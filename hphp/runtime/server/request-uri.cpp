/*
   +----------------------------------------------------------------------+
   | HipHop for PHP                                                       |
   +----------------------------------------------------------------------+
   | Copyright (c) 2010-present Facebook, Inc. (http://www.facebook.com)  |
   +----------------------------------------------------------------------+
   | This source file is subject to version 3.01 of the PHP license,      |
   | that is bundled with this package in the file LICENSE, and is        |
   | available through the world-wide-web at the following url:           |
   | http://www.php.net/license/3_01.txt                                  |
   | If you did not receive a copy of the PHP license and are unable to   |
   | obtain it through the world-wide-web, please send a note to          |
   | license@php.net so we can mail you a copy immediately.               |
   +----------------------------------------------------------------------+
*/
#include "hphp/runtime/server/request-uri.h"

#include <sys/stat.h>

#include <folly/Bits.h>
#include <folly/Hash.h>
#include <folly/Range.h>
#include <folly/portability/String.h>
#include <folly/portability/Unistd.h>

#include <algorithm>
#include <cstring>
#include <shared_mutex>
#include <vector>

#include "hphp/runtime/base/file-util.h"
#include "hphp/runtime/base/runtime-option.h"
#include "hphp/runtime/base/static-string-table.h"
#include "hphp/runtime/base/string-buffer.h"
#include "hphp/runtime/base/string-data.h"
#include "hphp/runtime/base/string-util.h"
#include "hphp/runtime/server/http-protocol.h"
#include "hphp/runtime/server/request-path-cache.h"
#include "hphp/runtime/server/static-content-cache.h"
#include "hphp/runtime/server/transport.h"
#include "hphp/runtime/server/virtual-host.h"
#include "hphp/util/assertions.h"
#include "hphp/util/ptr.h"

namespace HPHP {
///////////////////////////////////////////////////////////////////////////////

namespace {

struct RepoRequestPathCache {
  struct Entry {
    const VirtualHost* vhost{nullptr};
    PackedPtr<const StringData> sourceRoot;
    PackedPtr<const StringData> path;
    size_t sourceHash{0};
    size_t pathHash{0};
    uint8_t state{0};
  };

  static bool enabled() {
    return RuntimeOption::RepoAuthoritative &&
           RuntimeOption::RepoRequestPathCacheSize > 0 &&
           s_capacity > 0;
  }

  static void updateConfig() {
    std::unique_lock<std::shared_mutex> lock(s_mutex);
    s_size = 0;
    if (!RuntimeOption::RepoAuthoritative ||
        RuntimeOption::RepoRequestPathCacheSize <= 0) {
      s_entries.clear();
      s_capacity = 0;
      s_maxEntries = 0;
      return;
    }
    auto desired = static_cast<size_t>(RuntimeOption::RepoRequestPathCacheSize);
    if (desired < 1) desired = 1;
    desired = folly::nextPowTwo(desired * 2);
    s_entries.assign(desired, Entry{});
    s_capacity = desired;
    s_maxEntries = std::max<size_t>(1, desired * 3 / 4);
  }

  static void invalidateAll() {
    std::unique_lock<std::shared_mutex> lock(s_mutex);
    for (auto& entry : s_entries) entry = Entry{};
    s_size = 0;
  }

  static bool lookup(RequestURI& uri,
                     const VirtualHost* vhost,
                     folly::StringPiece sourceRoot,
                     folly::StringPiece canonicalPath) {
    if (!enabled() || canonicalPath.empty()) {
      return false;
    }
    auto const sourceHash = hashSlice(sourceRoot);
    auto const pathHash = hashSlice(canonicalPath);
    auto const combined = hashKey(vhost, sourceHash, pathHash);

    std::shared_lock<std::shared_mutex> lock(s_mutex);
    if (!s_capacity) return false;
    auto const mask = s_capacity - 1;
    auto idx = combined & mask;
    for (size_t i = 0; i < s_capacity; ++i) {
      auto const& entry = s_entries[idx];
      if (entry.state == 0) return false;
      if (entry.vhost == vhost &&
          entry.sourceHash == sourceHash &&
          entry.pathHash == pathHash &&
          equals(entry.sourceRoot.get(), sourceRoot) &&
          equals(entry.path.get(), canonicalPath)) {
        apply(uri, entry.sourceRoot.get(), entry.path.get());
        return true;
      }
      idx = (idx + 1) & mask;
    }
    return false;
  }

  static bool shouldStore(const RequestURI& uri,
                          folly::StringPiece canonicalPath) {
    if (!enabled() || canonicalPath.empty()) return false;
    if (uri.m_rewritten || uri.m_globalDoc || uri.m_defaultDoc ||
        uri.m_done || uri.m_forbidden ||
        !uri.m_origPathInfo.empty() || !uri.m_pathInfo.empty()) {
      return false;
    }
    if (!isPhpRequest(uri)) return false;
    auto const resolved = uri.m_path.slice();
    if (resolved.size() != canonicalPath.size() ||
        (resolved.size() &&
         memcmp(resolved.data(), canonicalPath.data(), resolved.size()) != 0)) {
      return false;
    }
    return true;
  }

  static void store(const VirtualHost* vhost,
                    folly::StringPiece sourceRootSlice,
                    folly::StringPiece canonicalSlice,
                    const StringData* sourceRootStatic,
                    const StringData* canonicalStatic) {
    if (!enabled() || canonicalSlice.empty() || canonicalStatic == nullptr ||
        sourceRootStatic == nullptr) {
      return;
    }
    std::unique_lock<std::shared_mutex> lock(s_mutex);
    if (s_size >= s_maxEntries || s_capacity == 0) return;

    auto const sourceHash = hashSlice(sourceRootSlice);
    auto const pathHash = hashSlice(canonicalSlice);
    auto const combined = hashKey(vhost, sourceHash, pathHash);

    auto const mask = s_capacity - 1;
    auto idx = combined & mask;
    for (;;) {
      auto& entry = s_entries[idx];
      if (entry.state == 0) {
        entry.vhost = vhost;
        entry.sourceRoot = PackedPtr<const StringData>(sourceRootStatic);
        entry.path = PackedPtr<const StringData>(canonicalStatic);
        entry.sourceHash = sourceHash;
        entry.pathHash = pathHash;
        entry.state = 1;
        ++s_size;
        return;
      }
      if (entry.vhost == vhost &&
          entry.sourceHash == sourceHash &&
          entry.pathHash == pathHash &&
          entry.sourceRoot.get() == sourceRootStatic &&
          entry.path.get() == canonicalStatic) {
        return;
      }
      idx = (idx + 1) & mask;
    }
  }

private:
  static size_t hashSlice(folly::StringPiece slice) {
    if (slice.empty()) return 0;
    return folly::hash::fnv64_buf(slice.data(), slice.size());
  }

  static size_t hashKey(const VirtualHost* vhost,
                        size_t sourceHash,
                        size_t pathHash) {
    auto hv = reinterpret_cast<uintptr_t>(vhost);
    auto combined = folly::hash::hash_128_to_64(hv, sourceHash);
    return folly::hash::hash_128_to_64(combined, pathHash);
  }

  static bool equals(const StringData* sd, folly::StringPiece slice) {
    if (!sd) return slice.empty();
    if (sd->size() != slice.size()) return false;
    if (slice.empty()) return true;
    return memcmp(sd->data(), slice.data(), slice.size()) == 0;
  }

  static void apply(RequestURI& uri,
                    const StringData* sourceRoot,
                    const StringData* canonicalPath) {
    auto pathStr = String(const_cast<StringData*>(canonicalPath));
    uri.m_path = pathStr;
    uri.m_resolvedURL = String("/") + pathStr;
    uri.m_origPathInfo.reset();
    uri.m_pathInfo.reset();
    if (sourceRoot && sourceRoot->size() != 0) {
      uri.m_absolutePath = String(const_cast<StringData*>(sourceRoot)) + pathStr;
    } else {
      uri.m_absolutePath = pathStr;
    }
    uri.m_rewritten = false;
    uri.m_defaultDoc = false;
    uri.m_globalDoc = false;
    uri.m_done = false;
    uri.m_forbidden = false;
    uri.processExt();
  }

  static bool isPhpRequest(const RequestURI& uri) {
    const char* ext = uri.m_ext;
    if (!ext) return true;

    auto matches = [&] (const char* target) {
      return strcasecmp(ext, target) == 0;
    };

    if (matches("php") || matches("hh") ||
        matches("hack") || matches("hackpartial")) {
      return true;
    }

    if (!RuntimeOption::PhpFileExtensions.empty()) {
      return RuntimeOption::PhpFileExtensions.count(ext);
    }

    return false;
  }

  static std::shared_mutex s_mutex;
  static std::vector<Entry> s_entries;
  static size_t s_capacity;
  static size_t s_maxEntries;
  static size_t s_size;
};

std::shared_mutex RepoRequestPathCache::s_mutex;
std::vector<RepoRequestPathCache::Entry> RepoRequestPathCache::s_entries;
size_t RepoRequestPathCache::s_capacity{0};
size_t RepoRequestPathCache::s_maxEntries{0};
size_t RepoRequestPathCache::s_size{0};

} // namespace

void repoRequestPathCacheInvalidate() {
  RepoRequestPathCache::invalidateAll();
}

void repoRequestPathCacheUpdateConfig() {
  RepoRequestPathCache::updateConfig();
}

RequestURI::RequestURI(const VirtualHost *vhost, Transport *transport,
                       const std::string &pathTranslation,
                       const std::string &sourceRoot)
  : m_rewritten(false)
  , m_defaultDoc(false)
  , m_globalDoc(false)
  , m_done(false)
  , m_forbidden(false)
  , m_ext(nullptr)
{
  if (!process(vhost, transport, sourceRoot, pathTranslation,
               transport->getServerObject()) ||
      (m_forbidden && Cfg::Server::ForbiddenAs404)) {
    m_forbidden = false; // put down forbidden flag since we are redirecting
    if (!Cfg::Server::ErrorDocument404.empty()) {
      String redirectURL(Cfg::Server::ErrorDocument404);
      if (!m_queryString.empty()) {
        if (redirectURL.find('?') == -1) {
          redirectURL += "?";
        } else {
          // has query in 404 string
          redirectURL += "&";
        }
        redirectURL += m_queryString;
      }
      if (process(vhost, transport, sourceRoot, pathTranslation,
                  redirectURL.data())) {
        // 404 redirection succeed
        return;
      }
    }
    transport->sendString(getDefault404(), 404);
    transport->onSendEnd();
    m_done = true;
  }
}

RequestURI::RequestURI(const std::string & rpcFunc)
  : m_rewritten(false)
  , m_defaultDoc(false)
  , m_globalDoc(false)
  , m_done(false)
{
  m_originalURL = m_rewrittenURL = m_resolvedURL = String(rpcFunc);
}

bool RequestURI::process(const VirtualHost *vhost, Transport *transport,
                         const std::string &sourceRoot,
                         const std::string &pathTranslation, const char *url) {
  splitURL(url, m_originalURL, m_queryString);
  m_originalURL = StringUtil::UrlDecode(m_originalURL, false);
  m_rewritten = false;

  auto scriptFilename = transport->getScriptFilename();
  const bool allowRepoCache =
    scriptFilename.empty() &&
    RuntimeOption::RepoAuthoritative &&
    RuntimeOption::RepoRequestPathCacheSize > 0 &&
    pathTranslation.empty();
  folly::StringPiece rootPiece{sourceRoot};

  String canonicalOriginal;
  String repoCanonical;
  folly::StringPiece lookupPiece;
  if (allowRepoCache) {
    canonicalOriginal = FileUtil::canonicalize(m_originalURL);
    if (!canonicalOriginal.isNull()) {
      repoCanonical = canonicalOriginal;
      while (!repoCanonical.empty() && repoCanonical.charAt(0) == '/') {
        repoCanonical = repoCanonical.substr(1);
      }
      if (!repoCanonical.empty()) {
        lookupPiece = repoCanonical.slice();
        if (RepoRequestPathCache::lookup(
              *this,
              vhost,
              rootPiece,
              lookupPiece)) {
          return true;
        }
      }
    }
  }

  if (!scriptFilename.empty()) {
    // The transport is overriding everything and just handing us the filename
    m_originalURL = scriptFilename;
    if (!resolveURL(vhost, pathTranslation, sourceRoot)) {
      return false;
    }
    if (m_origPathInfo.empty()) {
      // PATH_INFO wasn't filled by resolveURL() because m_originalURL
      // didn't contain it. We set it now, based on PATH_TRANSLATED.
      m_origPathInfo = transport->getPathTranslated();
      if (!m_origPathInfo.empty() &&
          m_origPathInfo.charAt(0) != '/') {
        m_origPathInfo = "/" + m_origPathInfo;
      }
    }
    if (transport->isPathInfoSet()) {
      m_pathInfo =transport->getPathInfo();
    } else {
      m_pathInfo = m_origPathInfo;
    }
    return true;
  }

  if (!Cfg::Server::GlobalDocument.empty()) {
    // GlobalDocument option in use - never resolveURL and 404 if GlobalDocument
    // does not exist. Still check for rewrites.

    if (!rewriteURLNoDirCheck(vhost, transport, pathTranslation, sourceRoot)) {
      // Redirection
      m_done = true;
      return true;
    }

    m_resolvedURL = String(Cfg::Server::GlobalDocument);
    if (virtualFileExists(vhost, sourceRoot, pathTranslation,
                          m_resolvedURL)) {
      m_globalDoc = true;
      return true;
    }
    return false;
  }

  // Fast path for files that exist
  if (vhost->checkExistenceBeforeRewrite()) {
    String canon = canonicalOriginal.isNull()
      ? FileUtil::canonicalize(m_originalURL)
      : canonicalOriginal;
    if (virtualFileExists(vhost, sourceRoot, pathTranslation, canon)) {
      m_rewrittenURL = canon;
      m_resolvedURL = canon;
      return true;
    }
  }

  if (!rewriteURL(vhost, transport, pathTranslation, sourceRoot)) {
    // Redirection
    m_done = true;
    return true;
  }
  if (!resolveURL(vhost, pathTranslation, sourceRoot)) {
    // Can't find
    return false;
  }
  if (allowRepoCache &&
      !lookupPiece.empty() &&
      RepoRequestPathCache::shouldStore(*this, lookupPiece)) {
    auto pathSd = makeStaticString(lookupPiece);
    auto rootSd = rootPiece.empty()
      ? staticEmptyString()
      : makeStaticString(rootPiece);
    RepoRequestPathCache::store(
      vhost,
      rootPiece,
      lookupPiece,
      rootSd,
      pathSd
    );
  }
  return true;
}

void RequestURI::splitURL(String surl, String &base, String &querys) {
  const char *url = surl.c_str();
  const char *query = strchr(url, '?');
  const char *fragment = strchr(url, '#');
  if (fragment) {
    // ignore everything after the #
    if (query && fragment > query) {
      base = String(url, query - url, CopyString);
      ++query; // skipping ?
      querys = String(query, fragment - query, CopyString);
    } else {
      base = String(url, fragment - url, CopyString);
      querys = "";
    }
  } else if (query) {
    base = String(url, query - url, CopyString);
    ++query; // skipping ?
    querys = String(query, CopyString);
  } else {
    base = String(url, CopyString);
    querys = "";
  }
}

const StaticString s_http("http://");
const StaticString s_https("https://");

/**
 * Precondition: m_originalURL and m_queryString are set
 * Postcondition: Output is false and we are redirecting OR
 *  m_rewrittenURL is set and m_queryString is updated if needed
 */
bool RequestURI::rewriteURL(
  const VirtualHost* vhost,
  Transport* transport,
  const std::string& pathTranslation,
  const std::string& sourceRoot
) {
  return rewriteURLNoDirCheck(vhost, transport, pathTranslation, sourceRoot) &&
         rewriteURLForDir(vhost, transport, pathTranslation, sourceRoot);
}

bool RequestURI::rewriteURLNoDirCheck(
  const VirtualHost* vhost,
  Transport* transport,
  const std::string& pathTranslation,
  const std::string& sourceRoot
) {
  bool qsa = false;
  int redirect = 0;
  std::string host = transport->getHeader("host");
  m_rewrittenURL = m_originalURL;
  if (vhost->rewriteURL(host, m_rewrittenURL, qsa, redirect)) {
    m_rewritten = true;
    if (qsa && !m_queryString.empty()) {
      m_rewrittenURL += (m_rewrittenURL.find('?') < 0) ? "?" : "&";
      m_rewrittenURL += m_queryString;
    }
    if (redirect) {
      if (m_rewrittenURL.substr(0, 7) != s_http &&
          m_rewrittenURL.substr(0, 8) != s_https) {
        PrependSlash(m_rewrittenURL);
      }
      if (redirect < 0) {
        std::string error;
        StringBuffer response;
        int code = 0;
        HttpProtocol::ProxyRequest(transport, true,
                                   m_rewrittenURL.toCppString(),
                                   code, error,
                                   response);
        if (!code) {
          transport->sendString(error, 500, false, false, "proxyRequest");
        } else {
          const char* respData = response.data();
          if (!respData) respData = "";
          transport->sendRaw(const_cast<char*>(respData),
                             response.size(), code);
        }
        transport->onSendEnd();
      } else {
        transport->redirect(m_rewrittenURL.c_str(), redirect);
      }
      return false;
    }
    splitURL(m_rewrittenURL, m_rewrittenURL, m_queryString);
  }
  m_rewrittenURL = FileUtil::canonicalize(m_rewrittenURL);
  if (!m_rewritten && m_rewrittenURL.charAt(0) == '/') {
    // A un-rewritten URL is always relative, so remove prepending /
    m_rewrittenURL = m_rewrittenURL.substr(1);
  }
  return true;
}

bool RequestURI::rewriteURLForDir(
  const VirtualHost* vhost,
  Transport* transport,
  const std::string& pathTranslation,
  const std::string& sourceRoot
) {
  // If the URL refers to a folder but does not end
  // with a slash, then we need to redictect
  String url = m_rewrittenURL;
  if (!url.empty() &&
      url.charAt(url.length() - 1) != '/') {
    if (virtualFolderExists(vhost, sourceRoot, pathTranslation, url)) {
      if (m_originalURL.find("..") != String::npos) {
        transport->sendString(getDefault404(), 404);
        transport->onSendEnd();
        return false;
      }
      url += "/";
      m_rewritten = true;
      String queryStr;
      m_rewrittenURL = m_originalURL;
      m_rewrittenURL += "/";
      if (!m_queryString.empty()) {
        m_rewrittenURL += "?";
        m_rewrittenURL += m_queryString;
      }
      if (m_rewrittenURL.substr(0, 7) != s_http &&
          m_rewrittenURL.substr(0, 8) != s_https) {
        PrependSlash(m_rewrittenURL);
      }
      transport->redirect(m_rewrittenURL.c_str(), 301);
      return false;
    }
  }
  return true;
}

/**
 * Precondition: m_rewrittenURL is set
 * Postcondition: Output is true and m_path and m_absolutePath are set OR
 *   output is false and no file was found
 */
bool RequestURI::resolveURL(const VirtualHost *vhost,
                            const std::string &pathTranslation,
                            const std::string &sourceRoot) {

  String startURL;
  if (m_rewritten) {
    startURL = m_rewrittenURL;
  } else {
    startURL = m_originalURL;
  }
  startURL = FileUtil::canonicalize(startURL.c_str(), startURL.size(), false);
  m_resolvedURL = startURL;

  while (!virtualFileExists(vhost, sourceRoot, pathTranslation,
                            m_resolvedURL)) {
    int pos = m_resolvedURL.rfind('/');
    if (pos <= 0) {
      // when none of the <subpath> exists, we give up, and try default doc
      m_resolvedURL = startURL;
      if (!m_resolvedURL.empty() &&
          m_resolvedURL.charAt(m_resolvedURL.length() - 1) != '/') {
        m_resolvedURL += "/";
      }
      m_resolvedURL += String(Cfg::Server::DefaultDocument);
      m_origPathInfo.reset();
      if (virtualFileExists(vhost, sourceRoot, pathTranslation,
                            m_resolvedURL)) {
        m_defaultDoc = true;
        return true;
      }
      return false;
    }
    m_resolvedURL = startURL.substr(0, pos);
    m_origPathInfo = startURL.substr(pos);
  }
  if (!m_resolvedURL.empty() &&
      m_resolvedURL.charAt(0) != '/') {
    m_resolvedURL = "/" + m_resolvedURL;
  }
  if (!m_originalURL.empty() &&
      m_originalURL.charAt(0) != '/') {
    m_originalURL = "/" + m_originalURL;
  }
  m_pathInfo = FileUtil::canonicalize(m_origPathInfo);
  return true;
}

bool RequestURI::virtualFileExists(const VirtualHost *vhost,
                                   const std::string &sourceRoot,
                                   const std::string &pathTranslation,
                                   const String& filename) {
  if (filename.empty() || filename.charAt(filename.length() - 1) == '/') {
    return false;
  }
  String canon = FileUtil::canonicalize(filename);
  if (!vhost->getDocumentRoot().empty()) {
    std::string fullname = canon.data();
    int i = 0;
    while (i < fullname.size() && fullname[i] == '/') ++i;
    if (i) {
      fullname = fullname.substr(i);
    }
    if (!i || !m_rewritten) {
      fullname = pathTranslation + fullname;
    }
    m_path = fullname;
    m_absolutePath = String(sourceRoot) + m_path;
    processExt();
    if (Cfg::Server::PathDebug) {
      m_triedURLs.push_back(m_absolutePath.toCppString());
    }

    if (StaticContentCache::TheFileCache && !fullname.empty() &&
        StaticContentCache::TheFileCache->fileExists(fullname.c_str())) {
      return true;
    }

    if (Cfg::Server::AllowedFiles.find(fullname.c_str()) !=
      Cfg::Server::AllowedFiles.end()) {
      return true;
    }
    if (Cfg::Repo::Authoritative &&
      !Cfg::Server::EnableStaticContentFromDisk) {
      return false;
    }
    struct stat st;
    if (stat(m_absolutePath.c_str(), &st) != 0) {
      return false;
    }
    return (st.st_mode & S_IFMT) == S_IFREG;
  }
  m_path = canon;
  m_absolutePath = String(sourceRoot) + canon;
  processExt();
  return true;
}

bool RequestURI::virtualFolderExists(const VirtualHost *vhost,
                                     const std::string &sourceRoot,
                                     const std::string &pathTranslation,
                                     const String& foldername) {
  if (!vhost->getDocumentRoot().empty()) {
    std::string fullname = foldername.data();
    // If there is a trailing slash, remove it
    if (fullname.size() > 0 && fullname[fullname.size()-1] == '/') {
      fullname = fullname.substr(fullname.size()-1);
    }
    if (fullname[0] == '/') {
      fullname = fullname.substr(1);
    } else {
      fullname = pathTranslation + fullname;
    }
    m_path = fullname;
    m_absolutePath = String(sourceRoot) + m_path;
    processExt();

    if (StaticContentCache::TheFileCache && !fullname.empty() &&
        StaticContentCache::TheFileCache->dirExists(fullname.c_str())) {
      return true;
    }

    const std::vector<std::string> &allowedDirectories =
      VirtualHost::GetAllowedDirectories();
    if (find(allowedDirectories.begin(),
             allowedDirectories.end(),
             fullname.c_str()) != allowedDirectories.end()) {
      return true;
    }
    struct stat st;
    return (stat(m_absolutePath.c_str(), &st) == 0 &&
            (st.st_mode & S_IFMT) == S_IFDIR);
  }
  m_path = foldername;
  m_absolutePath = String(sourceRoot) + foldername;
  processExt();
  return true;
}

void RequestURI::processExt() {
  m_ext = parseExt(m_path);
  if (Cfg::Server::ForbiddenFileExtensions.empty()) {
    return;
  }
  if (m_ext &&
      Cfg::Server::ForbiddenFileExtensions.find(m_ext) !=
      Cfg::Server::ForbiddenFileExtensions.end()) {
    m_forbidden = true;
  }
}

/*
 * Parse file extension from a path
 */
const char *RequestURI::parseExt(const String& s) {
  int pos = s.rfind('.');
  if (pos == -1) {
    return nullptr;
  }
  if (s.find('/', pos) != -1) {
    // '/' after '.' is not extension, e.g., "./foo" "../bar"
    return nullptr;
  }
  return s.data() + pos + 1;
}

void RequestURI::PrependSlash(String &s) {
  if (!s.empty() && s.charAt(0) != '/') {
    s = String("/") + s;
  }
}

void RequestURI::dump() {
  m_originalURL.dump();
  m_queryString.dump();
  m_rewrittenURL.dump();
  m_resolvedURL.dump();
  m_pathInfo.dump();
  m_origPathInfo.dump();
  m_absolutePath.dump();
  m_path.dump();
}

void RequestURI::clear() {
  m_originalURL.reset();
  m_queryString.reset();
  m_rewrittenURL.reset();
  m_resolvedURL.reset();
  m_pathInfo.reset();
  m_origPathInfo.reset();
  m_absolutePath.reset();
  m_path.reset();
}

const std::string RequestURI::getDefault404() {
  std::string ret = "404 File Not Found";
  if (Cfg::Server::PathDebug) {
    ret += "<br/>Paths examined:<ul>";
    for (auto& url : m_triedURLs) {
      ret += "<li>" + url + "</li>";
    }
    ret += "</ul>";
  }
  return ret;
}

///////////////////////////////////////////////////////////////////////////////
}
