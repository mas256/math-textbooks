# 数学書の本棚

数学教科書・解説書とその他の公開中の著作物を探せるカタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)

トップページの案内欄にEquashare v5.0.2のWindows版ダウンロードとWeb版へのリンクを掲載しています。Equashareは教科書一覧には含めていません。Web版のビルドは [`equashare/`](equashare/) にあります。

## リポジトリの役割と版番号

このRepositoryは一覧カタログです。教科書の原稿・Tag・正式Release・PDFは、書籍ごとのRepositoryで管理します。各Pagesの `catalog.json` から、配信済みの正式Release番号、PDFファイル名、正式版とlatestの最終更新日時をまとめて取得します。`books.json` に版やバージョンを手動登録する必要はありません。

各カードの左上に更新日時を日本時間（JST）で縦に表示し、右上には `v1.5.0` のようにRelease番号だけを表示します。正式版の日付はReleaseの公開日時、latestの日付は配信する成功ビルドの `built_at` です。Pagesの再配信だけでは日付を変えません。

PDFは `タイトル-v1.5.0.pdf`、開発中PDFは `latest-タイトル-v1.5.0.pdf` の形式です。latestの版番号は現在の正式Release番号を使用します。同じ版番号の間にlatestが更新されても、SHA-256をクエリに付けて旧キャッシュを避けます。

公開情報を取得できない場合は「取得できません」と表示し、PDFリンクを有効にしません。版番号だけが先に進んで旧PDFを案内する状態を防ぎます。

## 掲載書籍を追加する

`books.json`に次の形式の要素を追加し、`main`へPushしてください。Pages Workflowが一覧データを検証して自動公開します。

```json
{
  "title": "書名",
  "category": "分野",
  "description": "本の短い紹介",
  "site": "https://example.github.io/book/",
  "repository": "https://github.com/owner/book",
  "releases": "https://github.com/owner/book/releases",
  "tags": ["テーマ1", "テーマ2"]
}
```

`title`は一覧内で一意にし、リンクはHTTPSで指定します。各教科書の書名・説明・公開URLを記入してください。各Pagesは配信PDFと同じ公開処理で `catalog.json` を生成してください。開発中PDFの配信方法や更新条件は、各書籍のRepositoryにあるREADMEを正とします。

## ローカルで表示する

`index.html`を直接開くのではなく、RepositoryルートでローカルHTTPサーバーを起動します。

```bash
python -m http.server 8000
```

ブラウザーで <http://localhost:8000/> を開きます。

## 正式版と最新版

「正式版PDF」は各教科書の正式Releaseに対応します。「最新版PDF（開発中）」は成功した開発ビルドを別URLで配信し、失敗したビルドでは前回のPDFを維持します。

漸化式の超体系的解説では、Actionsの成功ビルド成果物からPagesの`latest.pdf`を更新します。新しい開発ビルドごとのTagやPre-releaseは作らず、過去に作られたものは履歴として残します。
