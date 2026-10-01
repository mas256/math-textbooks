# 数学書の本棚

複数の数学教科書・解説書を探せる公開カタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)

## リポジトリの役割と版番号

このRepositoryは一覧カタログです。教科書の原稿・Tag・正式Release・PDFは、書籍ごとのRepositoryで管理します。各書籍の`books.json`項目には、公開が完了した最新の正式Releaseの版番号を記入し、`pdf`にはその書籍のPagesサイトにある正式版`book.pdf`を指定します。

`latest_pdf`は成功した開発ビルドを読むための別リンクです。Pre-release名や開発ビルド番号は正式版の`version`に入れません。正式Release・PDF・SHA-256の検査とPages公開が終わってから`books.json`を更新します。

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
  "latest_pdf": "https://owner.github.io/book/latest.pdf",
  "repository": "https://github.com/owner/book",
  "releases": "https://github.com/owner/book/releases",
  "tags": ["テーマ1", "テーマ2"]
}
```

`title`は一覧内で一意にし、リンクはHTTPSで指定します。各教科書の書名・説明・公開URL・正式版番号を記入してください。

## ローカルで表示する

`index.html`を直接開くのではなく、RepositoryルートでローカルHTTPサーバーを起動します。

```bash
python -m http.server 8000
```

ブラウザーで <http://localhost:8000/> を開きます。

## 正式版と最新版

「正式版PDF」は各教科書の正式Releaseに対応します。
「最新版PDF（開発中）」は、各教科書の`main`へのpush後にBuildが成功したPDFです。
失敗したpushでは更新せず、直前の成功ビルドを維持します。
最新版PDFは教科書のPagesサイトに`latest.pdf`として配信します。ビルドごとの成果物は固有のPre-releaseにも保存します。Actions Artifactの期限には左右されません。
`latest_pdf`は任意項目です。最新版の公開に未対応の書籍では省略できます。