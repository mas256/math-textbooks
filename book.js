// 教科書ページ:概要・目次・版の履歴のタブと、版の情報。
import {
  bookColor, chapterCount, disabledLink, el, loadBooks, loadCatalog, pdfUrl,
  readingLink, siteUrl, timeElement,
} from "./lib.js";

const TABS = ["about", "toc", "history"];
const bookId = document.querySelector('meta[name="book-id"]')?.content
  || new URLSearchParams(location.search).get("id");

const $ = (id) => document.getElementById(id);

function selectTab(name, { focus = false, updateHash = true } = {}) {
  if (!TABS.includes(name)) return;
  for (const tab of TABS) {
    const selected = tab === name;
    const button = $("tab-" + tab);
    button.setAttribute("aria-selected", String(selected));
    button.tabIndex = selected ? 0 : -1;
    $("panel-" + tab).hidden = !selected;
    if (selected && focus) button.focus();
  }
  if (updateHash) history.replaceState(null, "", location.pathname + location.search + "#" + name);
}

function setupTabs() {
  for (const tab of TABS) {
    $("tab-" + tab).addEventListener("click", () => selectTab(tab));
    $("tab-" + tab).addEventListener("keydown", (event) => {
      const current = TABS.indexOf(tab);
      const next = { ArrowRight: current + 1, ArrowLeft: current - 1, Home: 0, End: TABS.length - 1 }[event.key];
      if (next === undefined) return;
      event.preventDefault();
      selectTab(TABS[(next + TABS.length) % TABS.length], { focus: true });
    });
  }
}

function followHash() {
  const hash = decodeURIComponent(location.hash.slice(1));
  if (TABS.includes(hash)) {
    selectTab(hash, { updateHash: false });
    return;
  }
  const chapter = /^toc-(\d+)$/.exec(hash);
  if (!chapter) return;
  selectTab("toc", { updateHash: false });
  const target = $(hash);
  if (!target) return;
  target.querySelector("details")?.setAttribute("open", "");
  target.scrollIntoView({ block: "center" });
  target.querySelector("a, summary")?.focus({ preventScroll: true });
}

function renderHead(book) {
  document.title = book.title + " — 数学書の本棚";
  $("crumb-title").textContent = book.title;
  $("book-title").textContent = book.title;
  $("book-category").textContent = book.category || "";
  $("book-dot").style.setProperty("--dot", bookColor(book.index));
  $("book-description").textContent = book.description || "";
}

function renderAbout(book, catalog) {
  const blocks = [el("p", { class: "muted" }, book.description || "")];
  const facts = [];
  if (catalog) {
    facts.push(el("div", { class: "panel" },
      el("h3", {}, "読める形式"),
      el("p", { class: "muted" }, catalog.release.mobile
        ? "A4版のPDFと、画面の幅に合わせて組み直したスマホ版があります。"
        : "A4版のPDFで読めます。")));
    if (catalog.toc.length) {
      const chapters = chapterCount(catalog);
      facts.push(el("div", { class: "panel" },
        el("h3", {}, "構成"),
        el("p", { class: "muted" }, chapters
          ? `${chapters}章` + (catalog.toc.length > chapters ? `と、ほか${catalog.toc.length - chapters}項目` : "") + "。目次はPDFのしおりから作っています。"
          : `${catalog.toc.length}節。`)));
    }
  }
  for (const item of book.related || []) {
    facts.push(el("a", { class: "panel", href: siteUrl(item.href), style: "text-decoration: none" },
      el("p", { class: "eyebrow" }, "一緒に使う"),
      el("h3", {}, item.title + " →"),
      el("p", { class: "muted" }, item.description || "")));
  }
  if (facts.length) blocks.push(el("div", { class: "about-grid" }, facts));
  if (book.tags?.length) blocks.push(el("p", { class: "chips tags" }, book.tags.map((tag) => el("span", {}, tag))));
  $("panel-about").replaceChildren(el("div", { style: "display: flex; flex-direction: column; gap: 16px" }, blocks));
}

function pageLink(book, catalog, entry, className) {
  if (!entry.page) return el("span", { class: className }, entry.title);
  return el("span", { class: className },
    readingLink(book, pdfUrl(book, catalog.release, false, entry.page), entry.title, "release", {
      title: `PDFの${entry.page}ページ目を開く`,
    }));
}

function renderToc(book, catalog) {
  const panel = $("panel-toc");
  if (!catalog.toc.length) {
    panel.replaceChildren(el("p", { class: "empty-note" },
      "この本の目次はまだ公開されていません。教科書のPages公開時に、PDFのしおりから自動で作られます。"));
    return;
  }
  const items = catalog.toc.map((chapter, index) => {
    const row = el("div", { class: "toc-row" },
      el("span", { class: "toc-index", "aria-hidden": "true" }, String(index + 1).padStart(2, "0")),
      pageLink(book, catalog, chapter, "toc-title"),
      chapter.page ? el("span", { class: "toc-page" }, "p." + chapter.page) : null);
    const sections = chapter.sections?.length
      ? el("details", { class: "toc-more" },
        el("summary", {}, `節を表示(${chapter.sections.length})`),
        el("ul", { class: "toc-sections" }, chapter.sections.map((section) => el("li", {},
          pageLink(book, catalog, section, ""),
          section.page ? el("span", { class: "toc-page" }, "p." + section.page) : null))))
      : null;
    return el("li", { id: "toc-" + index }, row, sections);
  });
  const note = catalog.toc.some((entry) => entry.page)
    ? el("p", { class: "muted", style: "margin-top: 10px" }, "章・節の名前を押すと、正式版PDFのそのページが開きます。")
    : null;
  panel.replaceChildren(el("ol", { class: "list-panel", id: "toc-list" }, items), note);
}

function renderHistory(book, catalog) {
  const releases = catalog.history.length
    ? catalog.history
    : [{ version: catalog.release.version, published_at: catalog.release.updated_at }];
  const rows = releases.map((release) => el("li", { class: "history-row" },
    el("a", {
      class: "version",
      href: book.repository.replace(/\/$/, "") + "/releases/tag/" + encodeURIComponent(release.version),
      target: "_blank",
      rel: "noopener noreferrer",
    }, release.version),
    timeElement(release.published_at),
    release.version === catalog.release.version ? el("span", { class: "badge" }, "現在の正式版") : null));
  $("panel-history").replaceChildren(
    el("ol", { class: "list-panel", id: "history-list" }, rows),
    el("p", { class: "muted", style: "margin-top: 10px" },
      el("a", { href: book.releases, target: "_blank", rel: "noopener noreferrer" }, "すべての版をGitHubで見る ↗")));
}

function renderInfo(book, catalog) {
  const links = [];
  if (catalog?.latest) {
    links.push(readingLink(book, pdfUrl(book, catalog.latest, true), "作成中の版を読む ↗", "latest", { id: "latest-pdf" }));
    if (catalog.latest.mobile) {
      links.push(readingLink(book, pdfUrl(book, catalog.latest.mobile, true), "作成中の版(スマホ版) ↗", "latest-mobile", { id: "latest-mobile-pdf" }));
    }
  }
  links.push(el("a", { href: book.releases, target: "_blank", rel: "noopener noreferrer" }, "過去の版 ↗"));
  links.push(el("a", { href: book.repository, target: "_blank", rel: "noopener noreferrer" }, "原稿(GitHub) ↗"));
  $("info-links").replaceChildren(...links);
  if (!catalog) return;
  $("release-version").textContent = catalog.release.version;
  $("release-date").replaceChildren(timeElement(catalog.release.updated_at));
  $("latest-date").replaceChildren(catalog.latest ? timeElement(catalog.latest.updated_at) : "なし");
}

function renderReading(book, catalog) {
  const actions = [readingLink(book, pdfUrl(book, catalog.release), "PDFで読む", "release", {
    class: "button button-accent", id: "release-pdf",
  })];
  if (catalog.release.mobile) {
    actions.push(readingLink(book, pdfUrl(book, catalog.release.mobile), "スマホ版で読む", "mobile", {
      class: "button", id: "release-mobile-pdf",
    }));
  }
  $("read-actions").replaceChildren(...actions);
  const chips = [];
  const chapters = chapterCount(catalog);
  if (chapters) chips.push(chapters + "章");
  chips.push(catalog.release.mobile ? "A4 / スマホ" : "A4");
  chips.push(catalog.release.version);
  $("book-chips").replaceChildren(...chips.map((chip) => el("span", {}, chip)));
}

function notFound() {
  document.title = "教科書が見つかりません — 数学書の本棚";
  $("crumb-title").textContent = "見つかりません";
  $("book-layout").replaceChildren(el("div", { class: "book-head" },
    el("h1", {}, "教科書が見つかりません"),
    el("p", { class: "muted" }, "URLが変わったか、本棚から外れた可能性があります。"),
    el("div", { class: "button-row" }, el("a", { class: "button", href: siteUrl("./") }, "本棚に戻る"))));
}

async function main() {
  setupTabs();
  let books;
  try {
    books = await loadBooks();
  } catch (error) {
    console.error(error);
    notFound();
    return;
  }
  const book = books.find((candidate) => candidate.id === bookId);
  if (!book) {
    notFound();
    return;
  }
  renderHead(book);
  renderAbout(book, null);
  renderInfo(book, null);
  try {
    const catalog = await loadCatalog(book);
    $("book-title").textContent = catalog.title;
    $("crumb-title").textContent = catalog.title;
    document.title = catalog.title + " — 数学書の本棚";
    renderReading(book, catalog);
    renderAbout(book, catalog);
    renderToc(book, catalog);
    renderHistory(book, catalog);
    renderInfo(book, catalog);
  } catch (error) {
    console.warn("公開PDF情報を取得できませんでした:", book.site, error);
    $("release-version").textContent = "取得できません";
    $("read-actions").replaceChildren(disabledLink("PDFで読む", { class: "button button-accent", id: "release-pdf" }));
    $("panel-toc").replaceChildren(el("p", { class: "empty-note" }, "目次を取得できませんでした。時間をおいて再読み込みしてください。"));
    $("panel-history").replaceChildren(el("p", { class: "empty-note" }, "版の履歴を取得できませんでした。"));
  }
  followHash();
}

window.addEventListener("hashchange", followHash);
main();
