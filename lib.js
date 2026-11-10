// 本棚の各ページで共通に使うデータの読み込みと整形。
// books.json の一覧と、各教科書の Pages が公開する catalog.json を扱う。

export const SITE_ROOT = new URL("./", import.meta.url);
const LAST_OPENED_KEY = "bookshelf:last-opened";
const SEMVER = /^v\d+\.\d+\.\d+$/;

export function siteUrl(path) {
  return new URL(path, SITE_ROOT).href;
}

// 組み立て後のサイトは books/<id>/、リポジトリ直下での確認時は book.html?id=<id> を使う。
export function bookUrl(book) {
  const pattern = document.querySelector('meta[name="bookshelf-book-path"]')?.content || "book.html?id={id}";
  return siteUrl(pattern.replace("{id}", encodeURIComponent(book.id)));
}

export function bookColor(index) {
  return `var(--book-${index % 6})`;
}

// 取得したデータはこの端末に保存し、次回からは保存分をすぐ使う(古ければ裏で取り直す)。
const CACHE_PREFIX = "bookshelf:cache:";
const FRESH_MS = 10 * 60 * 1000;
const KEEP_MS = 30 * 24 * 60 * 60 * 1000;
export const REVISION = document.querySelector('meta[name="bookshelf-revision"]')?.content || "dev";

function readCache(key) {
  try {
    const entry = JSON.parse(localStorage.getItem(CACHE_PREFIX + key) || "null");
    if (entry && Date.now() - entry.at < KEEP_MS) return entry;
  } catch {
    // Unreadable storage behaves like an empty cache.
  }
  return null;
}

function writeCache(key, data) {
  try {
    localStorage.setItem(CACHE_PREFIX + key, JSON.stringify({ at: Date.now(), data }));
  } catch {
    // Storage may be full or disabled; the data was still used for this page.
  }
}

// Stale-while-revalidate: a valid saved copy is returned at once; when it is older
// than FRESH_MS it is refreshed in the background for the next page.
function cachedJson(key, url, validate) {
  const refresh = async () => {
    const response = await fetch(url);
    if (!response.ok) throw new Error(new URL(url).pathname + ": " + response.status);
    const data = await response.json();
    const value = validate(data);
    writeCache(key, data);
    return value;
  };
  const hit = readCache(key);
  if (hit) {
    try {
      const value = validate(hit.data);
      if (Date.now() - hit.at > FRESH_MS) refresh().catch(() => {});
      return Promise.resolve(value);
    } catch {
      // A saved copy that no longer validates is ignored.
    }
  }
  return refresh();
}

function validateBooks(books) {
  if (!Array.isArray(books)) throw new Error("books.json must be an array");
  return books.map((book, index) => ({ ...book, index }));
}

let booksPromise;
export function loadBooks() {
  // The key includes the deployed revision so a new deploy reads the new list at once.
  booksPromise ??= cachedJson("books:" + REVISION, siteUrl("books.json"), validateBooks);
  try {
    for (const key of Object.keys(localStorage)) {
      if (key.startsWith(CACHE_PREFIX + "books:") && key !== CACHE_PREFIX + "books:" + REVISION) localStorage.removeItem(key);
    }
  } catch {
    // Nothing to clean up without storage.
  }
  return booksPromise;
}

const catalogPromises = new Map();
export function loadCatalog(book) {
  if (!catalogPromises.has(book.site)) {
    const site = new URL(book.site);
    catalogPromises.set(book.site, site.protocol !== "https:"
      ? Promise.reject(new Error("Pages URLはHTTPSで指定してください"))
      : cachedJson("catalog:" + book.site, new URL("catalog.json", site).href, validateCatalog));
  }
  return catalogPromises.get(book.site);
}

export function pdfUrl(book, info, development = false, page = 0) {
  // Encode the title as a filename, including characters such as # and %.
  const url = new URL(encodeURIComponent(info.pdf), book.site);
  if (development) url.searchParams.set("sha", info.sha256);
  if (page > 0) url.hash = "page=" + page;
  return url.href;
}

function cleanToc(entries, depth = 1) {
  if (!Array.isArray(entries)) return [];
  const result = [];
  for (const entry of entries) {
    if (!entry || typeof entry.title !== "string" || !entry.title.trim()) continue;
    const item = { title: entry.title.trim() };
    if (Number.isInteger(entry.page) && entry.page > 0) item.page = entry.page;
    if (depth < 2) {
      const sections = cleanToc(entry.sections, depth + 1);
      if (sections.length) item.sections = sections;
    }
    result.push(item);
  }
  return result;
}

function cleanHistory(rows) {
  if (!Array.isArray(rows)) return [];
  return rows.filter((row) => row && SEMVER.test(row.version) && Number.isFinite(Date.parse(row.published_at)));
}

export function validateCatalog(catalog) {
  if (catalog.schema_version !== 1 || typeof catalog.title !== "string" || !catalog.title) {
    throw new Error("公開PDF情報の形式が正しくありません");
  }
  if (!catalog.release) throw new Error("正式Release情報がありません");
  for (const [kind, info] of [["release", catalog.release], ["latest", catalog.latest]]) {
    if (!info) continue;
    if (!SEMVER.test(info.version)
      || !/^[a-f0-9]{64}$/.test(info.sha256)
      || !Number.isFinite(Date.parse(info.updated_at))) {
      throw new Error("公開PDFのバージョン・日時・SHA-256が正しくありません");
    }
    const expected = (kind === "latest" ? "latest-" : "") + catalog.title + "-" + info.version + ".pdf";
    if (info.pdf !== expected || /[\\/]/.test(info.pdf)) {
      throw new Error("公開PDFのファイル名が正しくありません");
    }
    if (info.mobile) {
      const mobileExpected = (kind === "latest" ? "latest-" : "")
        + catalog.title + "-スマホ版-" + info.version + ".pdf";
      if (info.mobile.pdf !== mobileExpected || !/^[a-f0-9]{64}$/.test(info.mobile.sha256)) {
        throw new Error("スマホ版PDFのファイル名・SHA-256が正しくありません");
      }
    }
  }
  // 目次と版の履歴は表示を補うだけなので、不正な項目は捨てて読み込みは続ける。
  return { ...catalog, toc: cleanToc(catalog.toc), history: cleanHistory(catalog.history) };
}

export function chapterCount(catalog) {
  return catalog.toc.filter((entry) => /^第\s*\d+\s*章/.test(entry.title)).length;
}

const dateFormat = new Intl.DateTimeFormat("ja-JP", {
  timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit", day: "2-digit",
});
const dateTimeFormat = new Intl.DateTimeFormat("ja-JP", {
  timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit", day: "2-digit",
  hour: "2-digit", minute: "2-digit", hourCycle: "h23",
});

export function formatDate(value) {
  return dateFormat.format(new Date(value));
}

export function timeElement(value) {
  const time = document.createElement("time");
  time.dateTime = value;
  time.textContent = formatDate(value);
  time.title = dateTimeFormat.format(new Date(value)) + " JST";
  return time;
}

export function el(tag, attributes = {}, ...children) {
  const node = document.createElement(tag);
  for (const [key, value] of Object.entries(attributes)) {
    if (value === undefined || value === null || value === false) continue;
    if (key === "class") node.className = value;
    else if (key === "style") node.style.cssText = value;
    else if (key === "dataset") Object.assign(node.dataset, value);
    else if (key.startsWith("on")) node.addEventListener(key.slice(2), value);
    else node.setAttribute(key, value === true ? "" : value);
  }
  node.append(...children.flat().filter((child) => child !== undefined && child !== null && child !== false));
  return node;
}

// PDFへのリンク。押したときに「この端末で前回開いた本」として記録する。
export function readingLink(book, href, label, kind, attributes = {}) {
  return el("a", {
    href,
    target: "_blank",
    rel: "noopener noreferrer",
    dataset: { bookId: book.id, kind },
    ...attributes,
  }, label);
}

export function disabledLink(label, attributes = {}) {
  return el("a", { "aria-disabled": "true", ...attributes }, label);
}

export function recordOpened(bookId, kind) {
  try {
    localStorage.setItem(LAST_OPENED_KEY, JSON.stringify({ id: bookId, kind, at: new Date().toISOString() }));
  } catch {
    // Storage can be unavailable (private browsing); the shelf still works without it.
  }
}

export function readLastOpened() {
  try {
    const value = JSON.parse(localStorage.getItem(LAST_OPENED_KEY) || "null");
    if (value && typeof value.id === "string" && Number.isFinite(Date.parse(value.at))) return value;
  } catch {
    // Ignore unreadable or malformed storage.
  }
  return null;
}

document.addEventListener("click", (event) => {
  const link = event.target.closest?.("a[data-book-id][data-kind][href]");
  if (link) recordOpened(link.dataset.bookId, link.dataset.kind);
});
