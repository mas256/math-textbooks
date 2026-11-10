// Browser checks for the bookshelf: home cards, book pages, search, theme,
// the "last opened" card, narrow-screen navigation and broken catalogs.
// Runs against the repository root (book.html?id=...) or an assembled site
// (books/<id>/) given by CATALOG_TEST_URL; links are followed from the home page.
const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const fs = require('node:fs');

const books = JSON.parse(fs.readFileSync('books.json', 'utf8'));
const base = process.env.CATALOG_TEST_URL || 'http://127.0.0.1:8787/';
let corrupt = false;

function catalogFor(book) {
  const pdf = book.title + '-v2.0.1.pdf';
  const release = {version: 'v2.0.1', updated_at: '2026-10-13T00:00:00Z', pdf, sha256: 'a'.repeat(64)};
  if (book === books[0]) release.mobile = {pdf: book.title + '-スマホ版-v2.0.1.pdf', sha256: 'b'.repeat(64)};
  const latest = {...release, pdf: 'latest-' + pdf, sha256: 'c'.repeat(64), updated_at: '2026-11-01T00:00:00Z'};
  if (release.mobile) latest.mobile = {...release.mobile, pdf: 'latest-' + release.mobile.pdf};
  if (corrupt && release.mobile) release.mobile.pdf = '../wrong.pdf';
  const catalog = {schema_version: 1, title: book.title, release, latest};
  if (book === books[0]) {
    catalog.toc = [
      {title: '第1章 はじめに', page: 9, sections: [{title: '1.1 本書について', page: 9}]},
      {title: '第2章 置換と部分', page: 11},
      {title: 42},
    ];
    catalog.history = [
      {version: 'v2.0.1', published_at: '2026-10-13T00:00:00Z'},
      {version: 'v1.0.0', published_at: '2026-09-01T00:00:00Z'},
    ];
  }
  return catalog;
}

const pdfHref = (book, name, extra = '') => new URL(encodeURIComponent(name), book.site).href + extra;
const noOverflow = async (page, label) => assert.ok(
  await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Horizontal overflow: ${label}`);

(async () => {
  const browser = await chromium.launch({executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH});
  // Service workers are checked separately below, so mocked responses are never served from their cache here.
  const context = await browser.newContext({serviceWorkers: 'block'});
  let catalogRequests = 0;
  const mockCatalog = route => {
    catalogRequests++;
    const book = books.find(candidate => new URL('catalog.json', candidate.site).href === route.request().url());
    return route.fulfill({json: catalogFor(book)});
  };
  await context.route('**/catalog.json', mockCatalog);
  await context.route(/^https:\/\/fonts\.(googleapis|gstatic)\.com\//, route => route.fulfill({body: ''}));
  await context.route(/\.pdf(\?|#|$)/, route => route.fulfill({contentType: 'application/pdf', body: '%PDF-test'}));
  const page = await context.newPage();
  const errors = [];
  page.on('pageerror', error => errors.push(String(error)));
  page.on('console', message => { if (message.type() === 'error') errors.push(message.text()); });

  // Home: cards, reading links and layout at three widths.
  for (const width of [1440, 390, 320]) {
    await page.setViewportSize({width, height: 900});
    await page.goto(base);
    await page.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
    await page.locator('#release-version-1').filter({hasText: 'v2.0.1'}).waitFor();
    const a4 = page.locator('#release-pdf-0');
    const mobile = page.locator('#release-mobile-pdf-0');
    assert.equal(await a4.getAttribute('href'), pdfHref(books[0], books[0].title + '-v2.0.1.pdf'));
    assert.equal(await a4.getAttribute('target'), '_blank');
    assert.ok((await a4.getAttribute('rel')).includes('noopener'));
    assert.equal(await mobile.textContent(), 'スマホ版');
    assert.equal(await mobile.getAttribute('href'), pdfHref(books[0], books[0].title + '-スマホ版-v2.0.1.pdf'));
    assert.equal(await page.locator('#release-mobile-pdf-1').count(), 0);
    assert.equal(await page.locator('#book-detail-1').isVisible(), true);
    assert.match(await page.locator('#book-card-0 .book-meta').textContent(), /2章 · v2\.0\.1 · A4 \/ スマホ/);
    const left = await a4.boundingBox(), right = await mobile.boundingBox();
    assert.ok(right.x >= left.x + left.width && Math.abs(left.y + left.height / 2 - right.y - right.height / 2) < 2,
      `Reading links are not adjacent at ${width}px`);
    await page.locator('#update-list li a').first().waitFor();
    assert.match(await page.locator('#update-list').textContent(), /作成中の版を更新/);
    await noOverflow(page, `home at ${width}px`);
    const sidebarLink = page.locator('#shell-sidebar a[data-book-nav]').first();
    await sidebarLink.waitFor({state: 'attached'});
    if (width < 960) {
      assert.equal(await sidebarLink.isVisible(), false, 'The drawer starts closed on narrow screens');
      await page.click('#menu-toggle');
      await sidebarLink.waitFor({state: 'visible'});
      assert.equal(await page.getAttribute('#menu-toggle', 'aria-expanded'), 'true');
      await page.keyboard.press('Escape');
      await sidebarLink.waitFor({state: 'hidden'});
    } else {
      assert.equal(await sidebarLink.isVisible(), true);
    }
  }

  // A reload within the freshness window reuses the saved data without asking the network.
  const requestsBefore = catalogRequests;
  await page.reload();
  await page.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
  assert.equal(catalogRequests, requestsBefore, 'Catalogs are read from the device cache on reload');

  // Drill entry keeps the chosen level.
  await page.setViewportSize({width: 1280, height: 900});
  await page.click('.level-grid button[data-level="4"]');
  assert.ok((await page.getAttribute('#drill-start', 'href')).endsWith('recurrence/?level=4'));

  // Opening a PDF is remembered on this device.
  assert.equal(await page.locator('#resume').isVisible(), false);
  const [popup] = await Promise.all([context.waitForEvent('page'), page.click('#release-mobile-pdf-0')]);
  await popup.close();
  await page.reload();
  await page.locator('#resume-open').waitFor();
  assert.equal(await page.locator('#resume-title').textContent(), books[0].title);
  assert.equal(await page.getAttribute('#resume-open', 'href'), pdfHref(books[0], books[0].title + '-スマホ版-v2.0.1.pdf'));

  // Theme switch persists.
  assert.equal(await page.evaluate(() => document.documentElement.dataset.theme), 'dark');
  await page.click('#theme-toggle');
  await page.reload();
  assert.equal(await page.evaluate(() => document.documentElement.dataset.theme), 'light');
  await page.click('#theme-toggle');

  // Book page reached from the home card.
  await page.click('#book-link-0');
  await page.locator('#release-version').filter({hasText: 'v2.0.1'}).waitFor();
  assert.equal(await page.getAttribute('#tab-toc', 'aria-selected'), 'true');
  assert.equal(await page.locator('#toc-list > li').count(), 2, 'Invalid toc entries are dropped');
  assert.equal(await page.locator('#toc-0 .toc-title a').getAttribute('href'), pdfHref(books[0], books[0].title + '-v2.0.1.pdf', '#page=9'));
  assert.equal(await page.locator('#release-mobile-pdf').textContent(), 'スマホ版で読む');
  assert.ok((await page.getAttribute('#latest-pdf', 'href')).includes('?sha='));
  assert.ok((await page.getAttribute('#latest-mobile-pdf', 'href')).includes('?sha='));
  assert.match(await page.locator('.book-info').textContent(), /作成中/);
  assert.equal(await page.locator('#shell-sidebar a[aria-current="page"]').textContent(), books[0].title);
  await page.click('#tab-history');
  assert.equal(await page.locator('#panel-history').isVisible(), true);
  assert.equal(await page.locator('#history-list > li').count(), 2);
  assert.match(await page.locator('#history-list > li').first().textContent(), /v2\.0\.1.*現在の正式版/);
  await page.focus('#tab-history');
  await page.keyboard.press('ArrowLeft');
  assert.equal(await page.getAttribute('#tab-toc', 'aria-selected'), 'true');
  for (const width of [1440, 320]) {
    await page.setViewportSize({width, height: 900});
    await noOverflow(page, `book page at ${width}px`);
  }
  await page.setViewportSize({width: 1280, height: 900});

  // Search finds a chapter and opens it on the book page.
  await page.goto(base);
  await page.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
  await page.keyboard.press('/');
  await page.locator('.shell-search input').fill('置換');
  const result = page.locator('.shell-search-results a', {hasText: '第2章 置換と部分'});
  await result.waitFor();
  await result.click();
  await page.locator('#toc-1').waitFor();
  assert.equal(await page.getAttribute('#tab-toc', 'aria-selected'), 'true');
  assert.ok(page.url().endsWith('#toc-1'));

  // A book without toc or history still shows its reading link and current release.
  await page.goto(base);
  await page.click('#book-link-1');
  await page.locator('#release-version').filter({hasText: 'v2.0.1'}).waitFor();
  assert.match(await page.locator('#panel-toc').textContent(), /目次はまだ公開されていません/);
  assert.equal(await page.locator('#release-mobile-pdf').count(), 0);
  await page.click('#tab-history');
  assert.equal(await page.locator('#history-list > li').count(), 1);

  // Broken metadata disables only that book (on a device without saved data).
  await page.evaluate(() => Object.keys(localStorage).filter(key => key.startsWith('bookshelf:cache:')).forEach(key => localStorage.removeItem(key)));
  corrupt = true;
  await page.goto(base);
  await page.locator('#release-version-0').filter({hasText: '取得できません'}).waitFor();
  assert.equal(await page.locator('#release-pdf-0').getAttribute('href'), null);
  assert.equal(await page.locator('#release-mobile-pdf-0').count(), 0);
  await page.locator('#release-version-1').filter({hasText: 'v2.0.1'}).waitFor();
  await page.click('#book-link-0');
  await page.locator('#release-version').filter({hasText: '取得できません'}).waitFor();
  assert.equal(await page.getAttribute('#release-pdf', 'href'), null);
  corrupt = false;

  if (!process.env.CATALOG_TEST_URL) {
    await page.goto(base + 'book.html?id=missing-book');
    await page.locator('h1', {hasText: '教科書が見つかりません'}).waitFor();
  }

  assert.deepEqual(errors, []);

  // The assembled site installs a service worker; afterwards pages open without the network.
  if (process.env.CATALOG_TEST_URL) {
    const swContext = await browser.newContext();
    await swContext.route('**/catalog.json', mockCatalog);
    await swContext.route(/^https:\/\/fonts\.(googleapis|gstatic)\.com\//, route => route.fulfill({body: ''}));
    const swPage = await swContext.newPage();
    await swPage.goto(base);
    await swPage.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
    await swPage.evaluate(() => navigator.serviceWorker.ready);
    await swPage.reload();
    assert.ok(await swPage.evaluate(() => Boolean(navigator.serviceWorker.controller)), 'The service worker controls the page');
    await swPage.click('#book-link-1');
    await swPage.locator('#release-version').filter({hasText: 'v2.0.1'}).waitFor();
    await swContext.setOffline(true);
    await swPage.goto(base);
    await swPage.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
    await swPage.click('#book-link-1');
    await swPage.locator('#release-version').filter({hasText: 'v2.0.1'}).waitFor();
    await swContext.close();
  }

  await browser.close();
  console.log('Bookshelf checked: home at 1440/390/320px, book pages, search, theme, last opened, drawer, broken catalog, device cache' + (process.env.CATALOG_TEST_URL ? ', service worker offline' : ''));
})().catch(error => { console.error(error); process.exit(1); });
