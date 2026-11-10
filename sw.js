// 本棚のService Worker。組み立て時に REVISION が公開版の番号に置き換わる。
// - ?v=付きのCSS・JS(版ごとに不変)と、版付きのURLのCDN・フォントはキャッシュ優先
// - ページ(HTML)と books.json などのJSONは、保存分をすぐ返して裏で更新
// - PDF、Equashare、その他の外部サイトには手を出さない
const REVISION = "__REVISION__";
const STATIC = "bookshelf-static-" + REVISION;
const RUNTIME = "bookshelf-runtime";
const SHARED = "bookshelf-shared";
const SCOPE = new URL(self.registration.scope);
const PRECACHE = ["shell.css", "shell.js", "lib.js", "styles.css", "app.js", "book.js"]
  .map((name) => new URL(name + "?v=" + REVISION, SCOPE).href);

self.addEventListener("install", (event) => {
  event.waitUntil(caches.open(STATIC).then((cache) => cache.addAll(PRECACHE)).then(() => self.skipWaiting()));
});

self.addEventListener("activate", (event) => {
  event.waitUntil((async () => {
    // Keep the previous revision too, so a page served from cache can still load its assets.
    const statics = (await caches.keys()).filter((name) => name.startsWith("bookshelf-static-") && name !== STATIC);
    await Promise.all(statics.slice(0, -1).map((name) => caches.delete(name)));
    await self.clients.claim();
  })());
});

async function cacheFirst(request, cacheName) {
  const cache = await caches.open(cacheName);
  const hit = await cache.match(request);
  if (hit) return hit;
  const response = await fetch(request);
  if (response.ok) cache.put(request, response.clone());
  return response;
}

async function staleWhileRevalidate(event, cacheName) {
  const cache = await caches.open(cacheName);
  const hit = await cache.match(event.request, { ignoreVary: true });
  const network = fetch(event.request).then((response) => {
    if (response.ok) cache.put(event.request, response.clone());
    return response;
  });
  if (hit) {
    event.waitUntil(network.catch(() => {}));
    return hit;
  }
  return network;
}

self.addEventListener("fetch", (event) => {
  const { request } = event;
  if (request.method !== "GET") return;
  const url = new URL(request.url);
  if (url.origin === SCOPE.origin) {
    if (!url.pathname.startsWith(SCOPE.pathname)) return;
    if (url.pathname.startsWith(SCOPE.pathname + "equashare/")) return;
    if (/\.pdf$/i.test(url.pathname)) return;
    if (url.searchParams.has("v")) {
      event.respondWith(cacheFirst(request, STATIC));
    } else if (request.mode === "navigate" || /\.(json|js|css|svg|png|ico|webmanifest)$/i.test(url.pathname)) {
      event.respondWith(staleWhileRevalidate(event, RUNTIME));
    }
    return;
  }
  if (url.hostname === "fonts.gstatic.com" || (url.hostname === "cdn.jsdelivr.net" && /@\d+\.\d+\.\d+\//.test(url.pathname))) {
    event.respondWith(cacheFirst(request, SHARED));
  } else if (url.hostname === "fonts.googleapis.com") {
    event.respondWith(staleWhileRevalidate(event, SHARED));
  }
});
