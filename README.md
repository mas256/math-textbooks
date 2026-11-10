# 数学書の本棚

数学教科書・解説書とその他の公開中の著作物を探せるカタログです。

- 公開サイト: https://mas256.github.io/math-textbooks/
- 教科書一覧データ: [`books.json`](books.json)
- 漸化式の問題生成: https://mas256.github.io/math-textbooks/recurrence/

漸化式生成ページの仕様・検証範囲・開発手順は [`recurrence/README.md`](recurrence/README.md) にあります。1つの画面で難易度1〜6を出題します。Lv1〜5は、版を固定したRust製の漸化式エンジンで、更新を依頼したときにまとめて生成した問題です。全問を有限項の厳密計算とLeanで検証してから公開します。Lv6は事前作成の固定問題です。問題の更新は Actions → **Regenerate recurrence problems** から依頼します。検証に失敗したビルドは公開しません。

ホームの下部にEquashare v5.0.2のWindows版ダウンロードとWeb版へのリンクを掲載しています。Equashareは教科書一覧には含めていません。Web版のビルドは [`equashare/`](equashare/) にあります。

## リポジトリの役割と版番号

このRepositoryは一覧カタログです。教科書の原稿・Tag・正式Release・PDFは、書籍ごとのRepositoryで管理します。各Pagesの `catalog.json` から、配信済みの正式Release番号、PDFファイル名、正式版とlatestの最終更新日時をまとめて取得します。`books.json` に版やバージョンを手動登録する必要はありません。

## サイトの構成

全ページが共通の外枠（左のサイドバー、上のバー、章・節の検索）を使います。外枠は `shell.css`・`shell.js`、データの読み込みは `lib.js` です。配色は暗い表示（墨と琥珀）が既定で、上のバーのボタンで明るい表示（白と朱）に切り替えられます。選択はブラウザーに保存します。幅960px未満ではサイドバーがメニューボタンで開く引き出しになります。

- ホーム（`index.html`・`app.js`）：この端末で前回開いた本、教科書の一覧、漸化式の問題生成の入口、最近の更新、Equashare。
- 教科書ページ（`book.html`・`book.js`）：概要・目次・版の履歴のタブと、版の情報。サイトの組み立て時に `books/<id>/` へ書籍ごとに生成します。目次の章・節を押すと、正式版PDFのそのページが開きます。
- 漸化式の問題生成（`recurrence/`）：同じ外枠の中で動きます。`?level=N` で難易度を指定して開けます。
- 検索：`/` キー（または Ctrl+K）で開き、書名・章・節・道具の名前から探せます。
- 前回開いた本：PDFへのリンクを押すと、その本と形式をこの端末のブラウザーにだけ記録します。

### 端末へのキャッシュ

再読み込みやページの移動を軽くするため、次のように端末側に保存します。

- `books.json` と各教科書の `catalog.json`：取得した内容をブラウザー（localStorage）に保存し、次回からは保存分ですぐ表示します。保存から10分を過ぎていれば裏で取り直し、次のページから新しい内容を使います。`books.json` は公開版ごとに保存し直すため、デプロイ直後から新しい一覧になります。
- サイトの部品：公開サイトでは Service Worker（`sw.js`）が、版番号付きのCSS・JS・問題データ、MathJax、フォントを保存して再利用します。ページ（HTML）とJSONは保存分をすぐ返し、裏で更新します。PDFとEquashareは対象外です。
- 先読み：リンクにカーソルを合わせると、同じサイト内の次のページを先に読み込みます（対応ブラウザーのみ）。

リポジトリ直下での確認時は Service Worker を登録しません。

日付は日本時間（JST）の日付で表示し、時刻はマウスを重ねると表示されます。正式版の日付はReleaseの公開日時、作成中の版の日付は配信する成功ビルドの `built_at` です。Pagesの再配信だけでは日付を変えません。

目次と版の履歴は、各教科書のPagesが `catalog.json` に出力する `toc`（PDFのしおりの章と節）と `history`（正式版の一覧）から表示します。まだ出力していない書籍では、目次を省き、版の履歴は現在の正式版だけを表示します。

PDFは `タイトル-v1.5.0.pdf`、作成中の版のPDFは `latest-タイトル-v1.5.0.pdf` の形式です。latestの版番号は現在の正式Release番号を使用します。同じ版番号の間にlatestが更新されても、SHA-256をクエリに付けて旧キャッシュを避けます。

スマホ版がある書籍は、PDFのボタンの隣にスマホ版のボタンを表示します。各書籍の `catalog.json` の `release.mobile` から `タイトル-スマホ版-vMAJOR.MINOR.PATCH.pdf` とSHA-256を取得します。作成中の版のスマホ版は `latest.mobile` を使用します。スマホ版のない書籍ではリンクを表示しません。

公開情報を取得できない場合は版情報に「取得できません」と表示し、PDFボタンを無効にします。版番号だけが先に進んで旧PDFを案内する状態を防ぎます。

## 掲載書籍を追加する

`books.json`に次の形式の要素を追加し、`main`へPushしてください。Pages Workflowが一覧データを検証して自動公開します。

```json
{
  "id": "book-id",
  "title": "書名",
  "category": "分野",
  "description": "本の短い紹介",
  "site": "https://example.github.io/book/",
  "repository": "https://github.com/owner/book",
  "releases": "https://github.com/owner/book/releases",
  "tags": ["テーマ1", "テーマ2"]
}
```

`id` は教科書ページのURL（`books/<id>/`）に使う英小文字・数字・ハイフンの名前で、一覧内で一意にします。`title`も一覧内で一意にし、リンクはHTTPSで指定します。各教科書の書名・説明・公開URLを記入してください。各Pagesは配信PDFと同じ公開処理で `catalog.json` を生成してください。任意の `related`（`title`・`description`・サイト内の `href` の配列）を書くと、教科書ページの概要に「一緒に使う」道具として表示します。作成中の版の配信方法や更新条件は、各書籍のRepositoryにあるREADMEを正とします。

## ローカルで表示する

`index.html`を直接開くのではなく、RepositoryルートでローカルHTTPサーバーを起動します。

```bash
python -m http.server 8000
```

ブラウザーで <http://localhost:8000/> を開きます。リポジトリ直下では、教科書ページは `book.html?id=<id>` で表示されます。公開時と同じ `books/<id>/` の形で確かめるときは、`python3 recurrence/scripts/assemble-site.py` で `site/` を組み立て、`site/` をHTTPサーバーで開きます。

## 正式版と最新版

「PDFで読む」は各教科書の正式Releaseに対応します。教科書ページの「作成中の版」は成功した開発ビルドを別URLで配信し、失敗したビルドでは前回のPDFを維持します。

漸化式の超体系的解説では、Actionsの成功ビルド成果物からPagesの`latest.pdf`を更新します。新しい開発ビルドごとのTagやPre-releaseは作らず、過去に作られたものは履歴として残します。

## Pages のデプロイ

静的ファイルをそのまま成果物にまとめ、GitHub Pages へ配信します。Pages の Source は初回に Settings → Pages で「GitHub Actions」に設定してください。毎回の設定確認は省き、配信完了を1秒間隔で確認して待ち時間を減らしています。

公開処理の途中で中止しないよう、同時デプロイは引き続き1件ずつ実行します。連続した更新では GitHub Actions が待機中の古い実行を最新の実行に置き換えます。
