const grid = document.querySelector("#book-grid");
const search = document.querySelector("#search");
const category = document.querySelector("#category");
const count = document.querySelector("#catalog-count");
const emptyState = document.querySelector("#empty-state");
const loadError = document.querySelector("#load-error");
let books = [];

function escapeHTML(value) {
  return String(value).replace(/[&<>"']/g, (character) => ({
    "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;",
  })[character]);
}

function bookCard(book) {
  const tags = (book.tags || []).map((tag) => `<li>${escapeHTML(tag)}</li>`).join("");
  return `
    <article class="book-card">
      <div class="card-top">
        <span class="category-label">${escapeHTML(book.category)}</span>
        <span class="edition-label">${escapeHTML(book.edition)} · ${escapeHTML(book.version)}</span>
      </div>
      <h3>${escapeHTML(book.title)}</h3>
      <p class="description">${escapeHTML(book.description)}</p>
      <ul class="tag-list" aria-label="テーマ">${tags}</ul>
      <div class="card-actions">
        <a class="card-primary" href="${escapeHTML(book.site)}" target="_blank" rel="noopener noreferrer">Web版を読む <span aria-hidden="true">↗</span></a>
        <div class="card-secondary">
          <a href="${escapeHTML(book.pdf)}" target="_blank" rel="noopener noreferrer">PDF</a>
          <a href="${escapeHTML(book.releases)}" target="_blank" rel="noopener noreferrer">版一覧</a>
          <a href="${escapeHTML(book.repository)}" target="_blank" rel="noopener noreferrer" aria-label="${escapeHTML(book.title)}のRepository">GitHub</a>
        </div>
      </div>
    </article>`;
}

function render() {
  const query = search.value.trim().toLocaleLowerCase("ja");
  const selectedCategory = category.value;
  const visibleBooks = books.filter((book) => {
    const searchable = [book.title, book.description, book.category, ...(book.tags || [])]
      .join(" ").toLocaleLowerCase("ja");
    return (!query || searchable.includes(query))
      && (!selectedCategory || book.category === selectedCategory);
  });

  grid.innerHTML = visibleBooks.map(bookCard).join("");
  count.textContent = `${visibleBooks.length} 冊を掲載中`;
  emptyState.hidden = visibleBooks.length !== 0;
  grid.hidden = visibleBooks.length === 0;
}

async function loadBooks() {
  try {
    const response = await fetch("books.json", { cache: "no-cache" });
    if (!response.ok) throw new Error(`books.json: ${response.status}`);
    const data = await response.json();
    if (!Array.isArray(data)) throw new Error("books.json must contain an array");
    books = data;
    [...new Set(books.map((book) => book.category).filter(Boolean))].sort()
      .forEach((name) => category.add(new Option(name, name)));
    grid.setAttribute("aria-busy", "false");
    render();
  } catch (error) {
    console.error(error);
    grid.hidden = true;
    count.textContent = "";
    loadError.hidden = false;
    grid.setAttribute("aria-busy", "false");
  }
}

search.addEventListener("input", render);
category.addEventListener("change", render);
document.addEventListener("keydown", (event) => {
  if (event.key === "/" && !["INPUT", "TEXTAREA", "SELECT"].includes(document.activeElement.tagName)) {
    event.preventDefault();
    search.focus();
  }
});

loadBooks();
