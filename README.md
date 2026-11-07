# 数学書の本棚

数学教科書・解説書とその他の公開中の著作物を探せるカタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)
- 漸化式の問題生成: https://mas256.github.io/math-textbooks/recurrence/

漸化式生成ページの仕様・検証範囲・開発手順は [`recurrence/README.md`](recurrence/README.md) にあります。1つの画面で難易度1〜6を出題します。Lv1〜5は、版を固定したRust製の漸化式エンジンで、更新を依頼したときにまとめて生成した問題です。全問を有限項の厳密計算とLeanで検証してから公開します。Lv6は事前作成の固定問題です。問題の更新は Actions → **Regenerate recurrence problems** から依頼します。検証に失敗したビルドは公開しません。

トップページの「学習ツール」欄にEquashare v5.0.2のWindows版ダウンロードとWeb版へのリンクを掲載しています。Equashareは教科書一覧には含めていません。Web版のビルドは [`equashare/`](equashare/) にあります。

## リポジトリの役割と版番号

このRepositoryは一覧カタログです。教科書の原稿・Tag・正式Release・PDFは、書籍ごとのRepositoryで管理します。各Pagesの `catalog.json` から、配信済みの正式Release番号、PDFファイル名、正式版とlatestの最終更新日時をまとめて取得します。`books.json` に版やバージョンを手動登録する必要はありません。

各カードは、分野名と書名を載せた色付きの表紙の下に、紹介文、「正式版 v1.5.0 · 2026/10/28 更新」の版情報、読むためのボタン、補助リンク（開発中の版・過去の版・GitHub）を並べます。表紙の色は `books.json` の並び順で自動的に割り当てます（`app.js` の `COVER_COLORS`）。日付は日本時間（JST）の日付で表示し、時刻はマウスを重ねると表示されます。正式版の日付はReleaseの公開日時、latestの日付は配信する成功ビルドの `built_at` です。Pagesの再配信だけでは日付を変えません。

PDFは `タイトル-v1.5.0.pdf`、開発中PDFは `latest-タイトル-v1.5.0.pdf` の形式です。latestの版番号は現在の正式Release番号を使用します。同じ版番号の間にlatestが更新されても、SHA-256をクエリに付けて旧キャッシュを避けます。

スマホ版がある書籍は「PDFで読む」の隣に「スマホ版で読む」を表示します。各書籍の `catalog.json` の `release.mobile` から `タイトル-スマホ版-vMAJOR.MINOR.PATCH.pdf` とSHA-256を取得します。開発中のスマホ版は `latest.mobile` を使用します。スマホ版のない書籍ではリンクを表示しません。

公開情報を取得できない場合は版情報に「取得できません」と表示し、PDFボタンを無効にします。版番号だけが先に進んで旧PDFを案内する状態を防ぎます。

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

「PDFで読む」は各教科書の正式Releaseに対応します。補助リンクの「開発中の版」は成功した開発ビルドを別URLで配信し、失敗したビルドでは前回のPDFを維持します。

漸化式の超体系的解説では、Actionsの成功ビルド成果物からPagesの`latest.pdf`を更新します。新しい開発ビルドごとのTagやPre-releaseは作らず、過去に作られたものは履歴として残します。

## Pages のデプロイ

静的ファイルをそのまま成果物にまとめ、GitHub Pages へ配信します。Pages の Source は初回に Settings → Pages で「GitHub Actions」に設定してください。毎回の設定確認は省き、配信完了を1秒間隔で確認して待ち時間を減らしています。

公開処理の途中で中止しないよう、同時デプロイは引き続き1件ずつ実行します。連続した更新では GitHub Actions が待機中の古い実行を最新の実行に置き換えます。
