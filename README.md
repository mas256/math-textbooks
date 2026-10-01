# 数学書の本棚

数学教科書・解説書とその他の公開中の著作物を探せるカタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)

その他の著作物は `index.html` の「その他の公開中の著作物」に掲載します。Equashare のインストーラは配布準備中のため、現在は配布元のRepositoryへ案内しています。インストーラ公開後は、ダウンロードリンクを実際の配布URLに更新してください。

## リポジトリの役割と版番号

このRepositoryは一覧カタログです。教科書の原稿・Tag・正式Release・PDFは、書籍ごとのRepositoryで管理します。各書籍の`books.json`項目には、公開が完了した最新の正式Releaseの版番号を記入し、`pdf`にはその書籍のPagesサイトにある正式版`book.pdf`を指定します。

`latest_pdf`は、正式版とは別に案内する開発中PDFへのリンクです。正式版の`version`には開発ビルドの番号を入れません。正式Release・PDF・SHA-256の検査とPages公開が終わってから、`books.json`の正式版番号を更新します。

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

`title`は一覧内で一意にし、リンクはHTTPSで指定します。各教科書の書名・説明・公開URL・正式版番号を記入してください。`latest_pdf`は任意項目です。開発中PDFの配信方法や更新条件は、各書籍のRepositoryにあるREADMEを正とします。

## ローカルで表示する

`index.html`を直接開くのではなく、RepositoryルートでローカルHTTPサーバーを起動します。

```bash
python -m http.server 8000
```

ブラウザーで <http://localhost:8000/> を開きます。

## 正式版と最新版

「正式版PDF」は各教科書の正式Releaseに対応します。「最新版PDF（開発中）」は成功した開発ビルドを別URLで配信し、失敗したビルドでは前回のPDFを維持します。

漸化式の超体系的解説では、Actionsの成功ビルド成果物からPagesの`latest.pdf`を更新します。新しい開発ビルドごとのTagやPre-releaseは作らず、過去に作られたものは履歴として残します。
