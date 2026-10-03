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
  link.href = href;
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

  const cardTop = document.createElement("div");
  cardTop.className = "card-top";
  const edition = createTextElement("span", "edition-label", "");
  edition.append(document.createTextNode((book.edition || "版未登録") + " · "));
  const version = createTextElement("span", "", "確認中…");
  version.id = "release-version-" + index;
  edition.append(version);
  cardTop.append(edition);

  const title = createTextElement("h3", "", book.title || "書名未登録");
  const description = createTextElement("p", "description", book.description || "");

  const tagList = document.createElement("ul");
  tagList.className = "tag-list";
  tagList.setAttribute("aria-label", "テーマ");
  (book.tags || []).forEach((tag) => {
    tagList.append(createTextElement("li", "", tag));
  });

  const actions = document.createElement("div");
  actions.className = "card-actions";

  const primaryLink = externalLink(book.pdf, "PDFを読む", "card-primary");
  const arrow = createTextElement("span", "", "↗");
  arrow.setAttribute("aria-hidden", "true");
  primaryLink.append(document.createTextNode(" "), arrow);

  const secondaryLinks = document.createElement("div");
  secondaryLinks.className = "card-secondary";
  if (book.latest_pdf) {
    secondaryLinks.append(externalLink(book.latest_pdf, "最新版PDF（開発中）"));
  }
  secondaryLinks.append(externalLink(book.releases, "版一覧"));
  secondaryLinks.append(externalLink(
    book.repository,
    "GitHub",
    "",
    (book.title || "書籍") + "のRepository",
  ));

  actions.append(primaryLink, secondaryLinks);
  article.append(cardTop, title, description, tagList, actions);
  return article;
}

function render() {
  grid.replaceChildren(...books.map((book, index) => bookCard(book, index)));
  count.textContent = books.length + " 冊を掲載中";
  grid.hidden = books.length === 0;
}

async function fetchLatestReleaseTag(repositoryUrl) {
  const repository = new URL(repositoryUrl);
  if (repository.protocol !== "https:" || repository.hostname.toLowerCase() !== "github.com") {
    throw new Error("書籍のRepository URLがGitHub URLではありません");
  }

  const pathParts = repository.pathname.split("/").filter(Boolean);
  if (pathParts.length !== 2) {
    throw new Error("GitHub Repository URLの形式が正しくありません");
  }

  const owner = pathParts[0];
  const repositoryName = pathParts[1].replace(/\.git$/i, "");
  const apiUrl = "https://api.github.com/repos/"
    + encodeURIComponent(owner) + "/"
    + encodeURIComponent(repositoryName)
    + "/releases/latest";
  const response = await fetch(apiUrl, {
    headers: { Accept: "application/vnd.github+json" },
    cache: "no-cache",
  });
  if (!response.ok) {
    throw new Error("GitHub Releases API: " + response.status);
  }

  const release = await response.json();
  if (typeof release.tag_name !== "string" || !release.tag_name.trim()) {
    throw new Error("最新Releaseにtag_nameがありません");
  }
  return release.tag_name.trim();
}

function showFallbackVersion(book, label) {
  const fallback = typeof book.version === "string" ? book.version.trim() : "";
  if (fallback) {
    label.textContent = fallback + "（最新情報を取得できず）";
  } else {
    label.textContent = "版数を取得できません";
  }
  label.setAttribute(
    "aria-label",
    fallback
      ? fallback + "。GitHubから最新のリリース番号を取得できませんでした。"
      : "GitHubから最新のリリース番号を取得できませんでした。",
  );
}

async function updateReleaseVersions() {
  await Promise.all(books.map(async (book, index) => {
    const label = document.getElementById("release-version-" + index);
    if (!label) return;

    try {
      label.textContent = await fetchLatestReleaseTag(book.repository);
      label.title = "GitHubの最新公開Releaseから取得";
      label.removeAttribute("aria-label");
    } catch (error) {
      showFallbackVersion(book, label);
      console.warn("最新Release番号を取得できませんでした:", book.repository, error);
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
    void updateReleaseVersions();
  } catch (error) {
    console.error(error);
    grid.hidden = true;
    count.textContent = "";
    loadError.hidden = false;
    grid.setAttribute("aria-busy", "false");
  }
}

loadBooks();
