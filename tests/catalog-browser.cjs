const { chromium } = require('playwright');
const assert = require('node:assert/strict');
const fs = require('node:fs');

(async () => {
  const books = JSON.parse(fs.readFileSync('books.json', 'utf8'));
  const browser = await chromium.launch({executablePath: process.env.PLAYWRIGHT_CHROMIUM_EXECUTABLE_PATH});
  const page = await browser.newPage();
  let corrupt = false;
  await page.route('**/catalog.json', route => {
    const book = books.find(book => new URL('catalog.json', book.site).href === route.request().url());
    const pdf = book.title + '-v2.0.1.pdf';
    const release = {version: 'v2.0.1', updated_at: '2026-10-13T00:00:00Z', pdf, sha256: 'a'.repeat(64)};
    if (book === books[0]) release.mobile = {pdf: book.title + '-スマホ版-v2.0.1.pdf', sha256: 'b'.repeat(64)};
    const latest = {...release, pdf: 'latest-' + pdf, sha256: 'c'.repeat(64)};
    if (release.mobile) latest.mobile = {...release.mobile, pdf: 'latest-' + release.mobile.pdf};
    if (corrupt && release.mobile) release.mobile.pdf = '../wrong.pdf';
    return route.fulfill({json: {schema_version: 1, title: book.title, release, latest}});
  });
  await page.route('https://fonts.googleapis.com/**', route => route.fulfill({body: ''}));
  const base = process.env.CATALOG_TEST_URL || 'http://127.0.0.1:8787/';
  for (const width of [1440, 390, 320]) {
    await page.setViewportSize({width, height: 900});
    await page.goto(base);
    await page.locator('#release-version-0').filter({hasText: 'v2.0.1'}).waitFor();
    const mobile = page.locator('#release-mobile-pdf-0');
    const a4 = page.locator('#release-pdf-0');
    assert.equal(await mobile.textContent(), 'スマホ版で読む');
    assert.equal(await mobile.isVisible(), true);
    assert.equal(await mobile.getAttribute('href'), new URL(encodeURIComponent(books[0].title + '-スマホ版-v2.0.1.pdf'), books[0].site).href);
    assert.equal(await mobile.getAttribute('target'), '_blank');
    assert.ok((await mobile.getAttribute('rel')).includes('noopener'));
    assert.equal(await page.locator('#release-mobile-pdf-1').isVisible(), false);
    assert.equal(await page.locator('#latest-mobile-pdf-0').isVisible(), true);
    assert.equal(await page.locator('#latest-mobile-pdf-1').isVisible(), false);
    assert.ok((await page.locator('#latest-mobile-pdf-0').getAttribute('href')).includes('?sha='));
    const left = await a4.boundingBox(), right = await mobile.boundingBox();
    assert.ok(right.x >= left.x + left.width && Math.abs(left.y + left.height / 2 - right.y - right.height / 2) < 2, `Reading links are not adjacent at ${width}px`);
    assert.ok(await page.evaluate(() => document.documentElement.scrollWidth <= innerWidth), `Horizontal overflow at ${width}px`);
  }
  corrupt = true;
  await page.reload();
  await page.locator('#release-version-0').filter({hasText: '取得できません'}).waitFor();
  assert.equal(await page.locator('#release-pdf-0').getAttribute('href'), null);
  assert.equal(await page.locator('#release-mobile-pdf-0').isVisible(), false);
  assert.equal(await page.locator('#release-version-1').textContent(), 'v2.0.1');
  await browser.close();
  console.log('Catalog checked: adjacent reading links at 1440/390/320px, legacy book, invalid mobile metadata');
})().catch(error => { console.error(error); process.exit(1); });
