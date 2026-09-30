# 数学書の本棚

複数の数学教科書・解説書を探せる公開カタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)

## 掲載書籍を追加する

`books.json`に次の形式の要素を追加し、`main`へPushしてください。Pages Workflowが一覧データを検証して自動公開します。

```json
{
  "title": "書名",
  "category": "分野",
  "description": "本の短い紹介",
  "edition": "第1版",
  "version": "v1.0.0",
  "site": "https://example.github.io/book/",
  "pdf": "https://example.github.io/book/book.pdf",
  "repository": "https://github.com/owner/book",
  "releases": "https://github.com/owner/book/releases",
  "tags": ["テーマ1", "テーマ2"]
}
```

`title`は一覧内で一意にし、リンクはHTTPSで指定します。各教科書の書名・説明・公開URL・版番号を記入してください。

## ローカルで表示する

`index.html`を直接開くのではなく、RepositoryルートでローカルHTTPサーバーを起動します。

```bash
python -m http.server 8000
```

ブラウザーで <http://localhost:8000/> を開きます。
