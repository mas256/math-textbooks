// 共通の外枠:サイドバー、メニュー(狭い画面)、明暗の切り替え、章・節の検索。
import { bookColor, bookUrl, el, loadBooks, loadCatalog, siteUrl } from "./lib.js";

const THEME_KEY = "bookshelf:theme";
const page = document.body.dataset.page || "";
const currentBookId = page === "book"
  ? document.querySelector('meta[name="book-id"]')?.content || new URLSearchParams(location.search).get("id")
  : null;

const icons = {
  sun: '<svg aria-hidden="true" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="12" cy="12" r="4"/><path d="M12 2v2M12 20v2M4.9 4.9l1.4 1.4M17.7 17.7l1.4 1.4M2 12h2M20 12h2M4.9 19.1l1.4-1.4M17.7 6.3l1.4-1.4"/></svg>',
  moon: '<svg aria-hidden="true" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><path d="M21 12.8A9 9 0 1 1 11.2 3a7 7 0 0 0 9.8 9.8z"/></svg>',
  search: '<svg aria-hidden="true" width="18" height="18" viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2" stroke-linecap="round" stroke-linejoin="round"><circle cx="11" cy="11" r="7"/><path d="m20 20-3.5-3.5"/></svg>',
};

function navLink(href, label, { current = false, dot, external = false } = {}) {
  return el("a", {
    href,
    "aria-current": current ? "page" : undefined,
    target: external ? "_blank" : undefined,
    rel: external ? "noopener noreferrer" : undefined,
  }, dot ? el("span", { class: "shell-dot", style: `--dot: ${dot}`, "aria-hidden": "true" }) : null, el("span", {}, label));
}

function renderSidebar(books) {
  const sidebar = document.getElementById("shell-sidebar");
  if (!sidebar) return;
  const bookLinks = books.map((book) => navLink(bookUrl(book), book.title, {
    current: book.id === currentBookId, dot: bookColor(book.index),
  }));
  bookLinks.forEach((link, index) => { link.dataset.bookNav = books[index].id; });
  sidebar.replaceChildren(
    el("a", { class: "shell-brand", href: siteUrl("./") },
      el("span", { class: "shell-brand-mark", "aria-hidden": "true" }, el("span"), el("span"), el("span")),
      "数学書の本棚"),
    el("button", { type: "button", class: "shell-search-button", "aria-haspopup": "dialog", onclick: openSearch },
      "章や節を検索", el("span", { class: "shell-kbd", "aria-hidden": "true" }, "/")),
    el("nav", { class: "shell-nav", "aria-label": "サイト内" },
      el("div", { class: "shell-nav-group" },
        navLink(siteUrl("./"), "ホーム", { current: page === "home" }),
        navLink(siteUrl("./#updates"), "更新履歴")),
      el("div", { class: "shell-nav-group" },
        el("p", { class: "shell-nav-label" }, "教科書"),
        bookLinks),
      el("div", { class: "shell-nav-group" },
        el("p", { class: "shell-nav-label" }, "演習と道具"),
        navLink(siteUrl("recurrence/"), "漸化式の問題生成", { current: page === "recurrence" }),
        navLink(siteUrl("equashare/"), "Equashare", { external: true }))),
    el("div", { class: "shell-sidebar-foot" },
      el("a", { href: "https://github.com/mas256/math-textbooks", target: "_blank", rel: "noopener noreferrer" }, "GitHub")),
  );
}

// 本の一覧を読み込む前にも、ホームや道具へは移動できるようにしておく。
renderSidebar([]);
loadBooks().then(renderSidebar).catch(() => {});

// 本文へ移動するリンク(教科書ページは <base> を使うため、ハッシュではなくフォーカスで移動する)
const skip = el("a", { class: "shell-skip", href: "#main" }, "本文へ移動");
skip.addEventListener("click", (event) => {
  const main = document.getElementById("main");
  if (!main) return;
  event.preventDefault();
  main.setAttribute("tabindex", "-1");
  main.focus();
});
document.body.prepend(skip);

// Narrow screens: the sidebar becomes a drawer.
const menuButton = document.getElementById("menu-toggle");
const backdrop = el("div", { class: "shell-backdrop" });
document.body.append(backdrop);
function setMenu(open) {
  document.body.classList.toggle("shell-open", open);
  menuButton?.setAttribute("aria-expanded", String(open));
  if (open) document.querySelector("#shell-sidebar a, #shell-sidebar button")?.focus();
}
menuButton?.addEventListener("click", () => setMenu(!document.body.classList.contains("shell-open")));
backdrop.addEventListener("click", () => setMenu(false));
document.addEventListener("keydown", (event) => {
  if (event.key === "Escape" && document.body.classList.contains("shell-open")) {
    setMenu(false);
    menuButton?.focus();
  }
});

// Theme
const themeButton = document.getElementById("theme-toggle");
function applyTheme(theme) {
  document.documentElement.dataset.theme = theme;
  if (!themeButton) return;
  const dark = theme !== "light";
  themeButton.innerHTML = dark ? icons.sun : icons.moon;
  themeButton.setAttribute("aria-label", dark ? "明るい表示に切り替え" : "暗い表示に切り替え");
  themeButton.title = themeButton.getAttribute("aria-label");
}
applyTheme(document.documentElement.dataset.theme === "light" ? "light" : "dark");
themeButton?.addEventListener("click", () => {
  const next = document.documentElement.dataset.theme === "light" ? "dark" : "light";
  applyTheme(next);
  try { localStorage.setItem(THEME_KEY, next); } catch { /* not persisted */ }
});

// Search across book titles, chapters and sections.
let dialog;
let index;
function normalize(text) {
  return text.normalize("NFKC").toLowerCase();
}

async function buildIndex() {
  const books = await loadBooks();
  const entries = [
    { label: "漸化式の問題生成", context: "演習", href: siteUrl("recurrence/") },
    { label: "Equashare", context: "道具 · LaTeXの数式を画像に", href: siteUrl("equashare/") },
  ];
  const catalogs = await Promise.allSettled(books.map((book) => loadCatalog(book)));
  books.forEach((book, bookIndex) => {
    const catalog = catalogs[bookIndex].status === "fulfilled" ? catalogs[bookIndex].value : null;
    const title = catalog?.title || book.title;
    const base = bookUrl(book);
    entries.push({ label: title, context: "教科書 · " + book.category, href: base });
    catalog?.toc.forEach((chapter, chapterIndex) => {
      entries.push({ label: chapter.title, context: title, href: base + "#toc-" + chapterIndex });
      chapter.sections?.forEach((section) => {
        entries.push({ label: section.title, context: title + " · " + chapter.title, href: base + "#toc-" + chapterIndex });
      });
    });
  });
  return entries.map((entry) => ({ ...entry, key: normalize(entry.label + " " + entry.context) }));
}

function highlight(label, query) {
  const position = normalize(label).indexOf(query);
  if (!query || position < 0) return [label];
  return [label.slice(0, position), el("mark", {}, label.slice(position, position + query.length)), label.slice(position + query.length)];
}

async function renderResults() {
  const input = dialog.querySelector("input");
  const list = dialog.querySelector(".shell-search-results");
  const status = dialog.querySelector(".shell-search-empty");
  const query = normalize(input.value.trim());
  if (!query) {
    list.replaceChildren();
    status.textContent = "教科書の書名・章・節、道具の名前で探せます。";
    status.hidden = false;
    return;
  }
  index ??= buildIndex();
  const entries = await index;
  if (normalize(input.value.trim()) !== query) return;
  const matches = entries.filter((entry) => entry.key.includes(query)).slice(0, 30);
  list.replaceChildren(...matches.map((entry) => el("li", {},
    el("a", { href: entry.href }, el("span", {}, highlight(entry.label, query)), el("small", {}, entry.context)))));
  status.textContent = matches.length ? "" : "見つかりませんでした。";
  status.hidden = matches.length > 0;
}

function ensureDialog() {
  if (dialog) return dialog;
  const input = el("input", {
    type: "search", "aria-label": "章や節を検索", placeholder: "章や節を検索", autocomplete: "off",
    oninput: renderResults,
  });
  const field = el("div", { class: "shell-search-field" });
  field.innerHTML = icons.search;
  field.append(input, el("span", { class: "shell-kbd", "aria-hidden": "true" }, "Esc"));
  dialog = el("dialog", { class: "shell-search", "aria-label": "検索" },
    el("div", { class: "shell-search-form" },
      field,
      el("p", { class: "shell-search-empty", role: "status" }),
      el("ul", { class: "shell-search-results" })));
  dialog.addEventListener("click", (event) => { if (event.target === dialog) dialog.close(); });
  dialog.addEventListener("keydown", (event) => {
    if (event.key !== "ArrowDown" && event.key !== "ArrowUp") return;
    const links = [...dialog.querySelectorAll(".shell-search-results a")];
    if (!links.length) return;
    event.preventDefault();
    const current = links.indexOf(document.activeElement);
    const next = event.key === "ArrowDown"
      ? (current + 1) % links.length
      : current <= 0 ? -1 : current - 1;
    (next < 0 ? input : links[next]).focus();
  });
  dialog.addEventListener("click", (event) => {
    if (event.target.closest("a")) dialog.close();
  });
  document.body.append(dialog);
  return dialog;
}

export function openSearch() {
  setMenu(false);
  const searchDialog = ensureDialog();
  if (!searchDialog.open) searchDialog.showModal();
  const input = searchDialog.querySelector("input");
  input.select();
  renderResults();
}

document.addEventListener("keydown", (event) => {
  const typing = event.target.closest?.("input, textarea, select, [contenteditable='true']");
  const shortcut = (event.key === "/" && !typing && !event.ctrlKey && !event.metaKey && !event.altKey)
    || (event.key.toLowerCase() === "k" && (event.ctrlKey || event.metaKey));
  if (!shortcut || dialog?.open) return;
  event.preventDefault();
  openSearch();
});
