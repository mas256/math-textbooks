const grid = document.querySelector("#book-grid");
const count = document.querySelector("#catalog-count");
const loadError = document.querySelector("#load-error");
// Cover colors, assigned in books.json order. Each passes 4.5:1 against the cover text color.
const COVER_COLORS = ["#245c54", "#2f3f6b", "#7a3f2a", "#4b3a63", "#4f5a2c", "#5b3a4a"];
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
  const name = book.title || "書籍";
  const article = document.createElement("article");
  article.className = "book-card";
  article.setAttribute("aria-labelledby", "book-title-" + index);

  const cover = createTextElement("div", "book-cover", "");
  cover.style.setProperty("--cover", COVER_COLORS[index % COVER_COLORS.length]);
  const title = createTextElement("h3", "", book.title || "書名未登録");
  title.id = "book-title-" + index;
  cover.append(createTextElement("p", "book-category", book.category || ""), title);

  const body = createTextElement("div", "book-body", "");
  const description = createTextElement("p", "description", book.description || "");

  const meta = createTextElement("p", "book-meta", "正式版 ");
  const version = createTextElement("span", "", "確認中…");
  version.id = "release-version-" + index;
  const dateWrap = createTextElement("span", "", " · ");
  dateWrap.id = "release-date-" + index;
  dateWrap.hidden = true;
  const releaseTime = createTextElement("time", "", "");
  releaseTime.id = "release-updated-" + index;
  dateWrap.append(releaseTime, document.createTextNode(" 更新"));
  meta.append(version, dateWrap);

  const actions = createTextElement("div", "book-actions", "");
  const primaryLink = externalLink(null, "PDFで読む", "button button-primary", name + "をPDFで読む");
  primaryLink.id = "release-pdf-" + index;
  const mobileLink = externalLink(null, "スマホ版で読む", "button button-secondary", name + "をスマホ版で読む");
  mobileLink.id = "release-mobile-pdf-" + index;
  mobileLink.hidden = true;
  actions.append(primaryLink, mobileLink);

  const links = createTextElement("div", "book-links", "");
  const dev = createTextElement("span", "dev-links", "");
  dev.id = "latest-links-" + index;
  dev.hidden = true;
  const latestLink = externalLink(null, "開発中の版", "", name + "の開発中の版（PDF）");
  latestLink.id = "latest-pdf-" + index;
  const latestMobileLink = externalLink(null, "スマホ版", "", name + "の開発中の版（スマホ版）");
  latestMobileLink.id = "latest-mobile-pdf-" + index;
  latestMobileLink.hidden = true;
  const latestTime = createTextElement("time", "", "");
  latestTime.id = "latest-updated-" + index;
  const latestDate = createTextElement("span", "", "");
  latestDate.append("· ", latestTime, " 更新");
  dev.append(latestLink, latestMobileLink, latestDate);
  links.append(dev,
    externalLink(book.releases, "過去の版", "", name + "の過去の版"),
    externalLink(book.repository, "GitHub", "", name + "のRepository"));

  body.append(description, meta, actions, links);
  article.append(cover, body);
  return article;
}

function render() {
  grid.replaceChildren(...books.map((book, index) => bookCard(book, index)));
  count.textContent = books.length + "冊 · すべて無料";
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
    if (info.mobile) {
      const mobileExpected = (kind === "latest" ? "latest-" : "")
        + catalog.title + "-スマホ版-" + info.version + ".pdf";
      if (info.mobile.pdf !== mobileExpected || !/^[a-f0-9]{64}$/.test(info.mobile.sha256)) {
        throw new Error("スマホ版PDFのファイル名・SHA-256が正しくありません");
      }
    }
  }
  return catalog;
}

function showUpdatedDate(element, value) {
  const date = new Date(value);
  element.dateTime = value;
  element.textContent = new Intl.DateTimeFormat("ja-JP", {
    timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit", day: "2-digit",
  }).format(date);
  element.title = new Intl.DateTimeFormat("ja-JP", {
    timeZone: "Asia/Tokyo", year: "numeric", month: "2-digit", day: "2-digit",
    hour: "2-digit", minute: "2-digit", hourCycle: "h23",
  }).format(date) + " JST";
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
        const info = catalog[kind];
        if (!info) continue;
        showUpdatedDate(document.getElementById(kind + "-updated-" + index), info.updated_at);
        const link = document.getElementById(kind + "-pdf-" + index);
        link.href = pdfUrl(site, info, kind === "latest");
        link.removeAttribute("aria-disabled");
        if (info.mobile) {
          const mobileLink = document.getElementById(kind + "-mobile-pdf-" + index);
          mobileLink.href = pdfUrl(site, info.mobile, kind === "latest");
          mobileLink.removeAttribute("aria-disabled");
          mobileLink.hidden = false;
        }
      }
      document.getElementById("release-date-" + index).hidden = false;
      document.getElementById("latest-links-" + index).hidden = !catalog.latest;
    } catch (error) {
      version.textContent = "取得できません";
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
