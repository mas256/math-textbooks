// ホーム:前回開いた本、教科書の一覧、演習の入口、最近の更新。
import {
  bookColor, bookUrl, chapterCount, el, loadBooks, loadCatalog,
  pdfUrl, readLastOpened, readingLink, disabledLink, siteUrl, timeElement,
} from "./lib.js";

const grid = document.getElementById("book-grid");
const count = document.getElementById("catalog-count");
const loadError = document.getElementById("load-error");

const KIND_LABEL = {
  release: "PDF(A4版)で開いていました",
  mobile: "スマホ版で開いていました",
  latest: "作成中の版を開いていました",
  "latest-mobile": "作成中の版(スマホ版)を開いていました",
};

function bookCard(book) {
  const i = book.index;
  const titleLink = el("a", { href: bookUrl(book), id: "book-link-" + i }, book.title);
  const title = el("h3", { id: "book-title-" + i }, titleLink);
  const pdf = disabledLink("PDF", { class: "button button-solid", id: "release-pdf-" + i, "aria-label": book.title + "をPDFで読む" });
  const second = el("a", { class: "button", href: bookUrl(book), id: "book-detail-" + i, "aria-label": book.title + "の詳細" }, "詳細");
  const meta = el("p", { class: "book-meta" },
    el("span", { id: "book-chapters-" + i }),
    el("span", { id: "release-version-" + i }, "確認中…"),
    el("span", { id: "book-formats-" + i }));
  return el("article", { class: "book-card", id: "book-card-" + i, "aria-labelledby": "book-title-" + i },
    el("p", { class: "eyebrow book-category" },
      el("span", { class: "shell-dot", style: `--dot: ${bookColor(i)}`, "aria-hidden": "true" }), book.category || ""),
    title,
    el("p", { class: "description" }, book.description || ""),
    meta,
    el("div", { class: "card-actions", id: "book-actions-" + i }, pdf, second));
}

function fillCard(book, catalog) {
  const i = book.index;
  document.getElementById("book-link-" + i).textContent = catalog.title;
  document.getElementById("release-version-" + i).textContent = catalog.release.version;
  const chapters = chapterCount(catalog);
  document.getElementById("book-chapters-" + i).textContent = chapters ? chapters + "章 · " : "";
  document.getElementById("book-formats-" + i).textContent = catalog.release.mobile ? " · A4 / スマホ" : " · A4";
  const pdf = readingLink(book, pdfUrl(book, catalog.release), "PDF", "release", {
    class: "button button-solid", id: "release-pdf-" + i, "aria-label": catalog.title + "をPDFで読む",
  });
  const actions = document.getElementById("book-actions-" + i);
  if (catalog.release.mobile) {
    const mobile = readingLink(book, pdfUrl(book, catalog.release.mobile), "スマホ版", "mobile", {
      class: "button", id: "release-mobile-pdf-" + i, "aria-label": catalog.title + "をスマホ版で読む",
    });
    actions.replaceChildren(pdf, mobile);
  } else {
    actions.replaceChildren(pdf, document.getElementById("book-detail-" + i));
  }
}

function failCard(book, error) {
  document.getElementById("release-version-" + book.index).textContent = "取得できません";
  console.warn("公開PDF情報を取得できませんでした:", book.site, error);
}

function resumeLink(book, catalog, kind) {
  if (kind === "mobile" && catalog.release.mobile) return pdfUrl(book, catalog.release.mobile);
  if (kind === "latest" && catalog.latest) return pdfUrl(book, catalog.latest, true);
  if (kind === "latest-mobile" && catalog.latest?.mobile) return pdfUrl(book, catalog.latest.mobile, true);
  return pdfUrl(book, catalog.release);
}

async function showResume(books) {
  const last = readLastOpened();
  const book = last && books.find((candidate) => candidate.id === last.id);
  if (!book) return;
  const section = document.getElementById("resume");
  section.style.setProperty("--dot", bookColor(book.index));
  document.getElementById("resume-title").textContent = book.title;
  document.getElementById("resume-kind").textContent = KIND_LABEL[last.kind] || KIND_LABEL.release;
  document.getElementById("resume-meta").replaceChildren("この端末で前回開いた本 · ", timeElement(last.at));
  const detail = el("a", { class: "button", href: bookUrl(book) }, "本の詳細");
  const actions = document.getElementById("resume-actions");
  actions.replaceChildren(detail);
  section.hidden = false;
  try {
    const catalog = await loadCatalog(book);
    document.getElementById("resume-title").textContent = catalog.title;
    actions.replaceChildren(
      readingLink(book, resumeLink(book, catalog, last.kind), "続きを読む", last.kind, { class: "button button-accent", id: "resume-open" }),
      detail);
  } catch {
    // The detail link stays available when the catalog cannot be read.
  }
}

function renderUpdates(books, results) {
  const list = document.getElementById("update-list");
  const events = [];
  books.forEach((book, i) => {
    if (results[i].status !== "fulfilled") return;
    const catalog = results[i].value;
    const releases = catalog.history.length
      ? catalog.history
      : [{ version: catalog.release.version, published_at: catalog.release.updated_at }];
    for (const release of releases) {
      events.push({ book, at: release.published_at, text: `${catalog.title} ${release.version} を公開` });
    }
    if (catalog.latest) {
      events.push({ book, at: catalog.latest.updated_at, text: `${catalog.title} 作成中の版を更新` });
    }
  });
  events.sort((a, b) => Date.parse(b.at) - Date.parse(a.at));
  list.replaceChildren(...events.slice(0, 6).map((event) => el("li", {},
    timeElement(event.at),
    el("span", {},
      el("span", { class: "shell-dot", style: `--dot: ${bookColor(event.book.index)}`, "aria-hidden": "true" }),
      el("a", { href: bookUrl(event.book) }, event.text)))));
  if (!events.length) list.replaceChildren(el("li", { class: "muted" }, "更新情報を取得できませんでした。"));
  list.setAttribute("aria-busy", "false");
}

function setupDrill() {
  const start = document.getElementById("drill-start");
  const buttons = [...document.querySelectorAll(".level-grid button[data-level]")];
  for (const button of buttons) {
    button.addEventListener("click", () => {
      for (const other of buttons) other.setAttribute("aria-pressed", String(other === button));
      start.href = siteUrl("recurrence/?level=" + button.dataset.level);
    });
  }
}

async function main() {
  setupDrill();
  let books;
  try {
    books = await loadBooks();
  } catch (error) {
    loadError.hidden = false;
    count.textContent = "";
    grid.setAttribute("aria-busy", "false");
    console.error(error);
    renderUpdates([], []);
    return;
  }
  grid.replaceChildren(...books.map(bookCard));
  count.textContent = books.length + "冊 · すべて無料";
  showResume(books);
  const results = await Promise.allSettled(books.map(async (book) => {
    try {
      const catalog = await loadCatalog(book);
      fillCard(book, catalog);
      return catalog;
    } catch (error) {
      failCard(book, error);
      throw error;
    }
  }));
  grid.setAttribute("aria-busy", "false");
  renderUpdates(books, results);
}

main();
