const grid = document.querySelector("#book-grid");
const count = document.querySelector("#catalog-count");
const loadError = document.querySelector("#load-error");
let books = [];

function createTextElement(tagName, className, text) {
  const element = document.createElement(tagName);
  if (className) element.className = className;
  element.textContent = text;
  return element;
}

function externalLink(href, label, className, ariaLabel) {
  const link = document.createElement("a");
  if (href) link.href = href;
  else link.setAttribute("aria-disabled", "true");
  link.target = "_blank";
  link.rel = "noopener noreferrer";
  link.textContent = label;
  if (className) link.className = className;
  if (ariaLabel) link.setAttribute("aria-label", ariaLabel);
  return link;
}

function bookCard(book, index) {
  const article = document.createElement("article");
  article.className = "book-card";
  const cardTop = createTextElement("div", "card-top", "");
  const dates = createTextElement("div", "update-dates", "");
  for (const [kind, label] of [["release", "正式版"], ["latest", "latest"]]) {
    const row = createTextElement("p", "update-date", label + " 最終更新: ");
    const time = createTextElement("time", "", "確認中…");
    time.id = kind + "-updated-" + index;
    row.append(time);
    dates.append(row);
  }
  const version = createTextElement("span", "release-label", "確認中…");
  version.id = "release-version-" + index;
  cardTop.append(dates, version);

  const title = createTextElement("h3", "", book.title || "書名未登録");
  title.id = "book-title-" + index;
  const description = createTextElement("p", "description", book.description || "");
  const tagList = createTextElement("ul", "tag-list", "");
  tagList.setAttribute("aria-label", "テーマ");
  (book.tags || []).forEach((tag) => tagList.append(createTextElement("li", "", tag)));
  const actions = createTextElement("div", "card-actions", "");
  const primaryLink = externalLink(null, "PDFを読む", "card-primary");
  primaryLink.id = "release-pdf-" + index;
  const arrow = createTextElement("span", "", "↗");
  arrow.setAttribute("aria-hidden", "true");
  primaryLink.append(document.createTextNode(" "), arrow);
  const secondaryLinks = createTextElement("div", "card-secondary", "");
  const latestLink = externalLink(null, "最新版PDF（開発中）");
  latestLink.id = "latest-pdf-" + index;
  secondaryLinks.append(latestLink, externalLink(book.releases, "版一覧"),
    externalLink(book.repository, "GitHub", "", (book.title || "書籍") + "のRepository"));
  actions.append(primaryLink, secondaryLinks);
  article.append(cardTop, title, description, tagList, actions);
  return article;
}

function render() {
  grid.replaceChildren(...books.map((book, index) => bookCard(book, index)));
  count.textContent = books.length + " 冊を掲載中";
  grid.hidden = books.length === 0;
}

function pdfUrl(site, info, development = false) {
  // Encode the title as a filename, including characters such as # and %.
  const url = new URL(encodeURIComponent(info.pdf), site);
  if (development) url.searchParams.set("sha", info.sha256);
  return url.href;
}

function validateCatalog(catalog) {
  if (catalog.schema_version !== 1 || typeof catalog.title !== "string" || !catalog.title) {
    throw new Error("公開PDF情報の形式が正しくありません");
  }
  if (!catalog.release) throw new Error("正式Release情報がありません");
  for (const [kind, info] of [["release", catalog.release], ["latest", catalog.latest]]) {
    if (!info) continue;
    if (!/^v\d+\.\d+\.\d+$/.test(info.version)
      || !/^[a-f0-9]{64}$/.test(info.sha256)
      || !Number.isFinite(Date.parse(info.updated_at))) {
      throw new Error("公開PDFのバージョン・日時・SHA-256が正しくありません");
    }
    const expected = (kind === "latest" ? "latest-" : "") + catalog.title + "-" + info.version + ".pdf";
    if (info.pdf !== expected || /[\\/]/.test(info.pdf)) {
      throw new Error("公開PDFのファイル名が正しくありません");
    }
  }
  return catalog;
}

function showUpdatedTime(element, value) {
  element.dateTime = value;
  element.textContent = new Intl.DateTimeFormat("ja-JP", {
    timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit", day: "2-digit",
    hour: "2-digit", minute: "2-digit", hourCycle: "h23",
  }).format(new Date(value)) + " JST";
}

async function updatePublications() {
  await Promise.all(books.map(async (book, index) => {
    const version = document.getElementById("release-version-" + index);
    try {
      const site = new URL(book.site);
      if (site.protocol !== "https:") throw new Error("Pages URLはHTTPSで指定してください");
      const response = await fetch(new URL("catalog.json", site), { cache: "no-store" });
      if (!response.ok) throw new Error("公開PDF情報: " + response.status);
      const catalog = validateCatalog(await response.json());
      document.getElementById("book-title-" + index).textContent = catalog.title;
      version.textContent = catalog.release.version;
      version.title = "Pagesで配信中の正式Release";
      for (const kind of ["release", "latest"]) {
        const time = document.getElementById(kind + "-updated-" + index);
        const link = document.getElementById(kind + "-pdf-" + index);
        const info = catalog[kind];
        if (info) {
          showUpdatedTime(time, info.updated_at);
          link.href = pdfUrl(site, info, kind === "latest");
          link.removeAttribute("aria-disabled");
        } else {
          time.textContent = "未公開";
          link.hidden = true;
        }
      }
    } catch (error) {
      version.textContent = "取得できません";
      for (const kind of ["release", "latest"]) {
        document.getElementById(kind + "-updated-" + index).textContent = "取得できません";
      }
      console.warn("公開PDF情報を取得できませんでした:", book.site, error);
    }
  }));
}

async function loadBooks() {
  try {
    const response = await fetch("books.json", { cache: "no-cache" });
    if (!response.ok) throw new Error("books.json: " + response.status);
    const data = await response.json();
    if (!Array.isArray(data)) throw new Error("books.json must contain an array");
    books = data;
    grid.setAttribute("aria-busy", "false");
    render();
    void updatePublications();
  } catch (error) {
    console.error(error);
    grid.hidden = true;
    count.textContent = "";
    loadError.hidden = false;
    grid.setAttribute("aria-busy", "false");
  }
}

loadBooks();
