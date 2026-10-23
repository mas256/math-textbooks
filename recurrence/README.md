# 漸化式の問題生成

公開ページ `/recurrence/` は、難易度1〜6の漸化式を1つの画面で出題します。

| 難易度 | 問題の出どころ | 検証 | 変わるとき |
| --- | --- | --- | --- |
| Lv1〜5 | [漸化式エンジン](https://github.com/mas256/recurrence-equation-generator)（Rust）が更新の依頼時にまとめて生成した問題 | 全問で有限項の厳密計算と、Leanによる原問題の証明 | 更新を依頼したときだけ（毎回新しい乱数の種で作り直す） |
| Lv6 | 事前作成した[固定問題60問](authored/level6-problems.md) | 解説と有限範囲の厳密計算による検算（Leanの対象外） | 変わらない |

1問出題、分野の絞り込み、ヒント、解答、別解、14問のまとめて出題、リンク共有、印刷、TeX出力、Equashare連携は、両方の問題で使えます。以前の `textbook.html` は `/recurrence/` へ転送します。`?problem=L6-N03` や `?batch=...` のリンクも、そのまま引き継ぎます。

## 問題の更新（再生成）

GitHubの **Actions → Regenerate recurrence problems → Run workflow** を、`main` を選んで実行します。各難易度の問題数（既定30問）を指定できます。Workflowは次の順に処理します。

1. `engine-lock.json` に固定したエンジンのコミットを取得し、`recurrence-bank` をビルドする。
2. Lean 4.19.0とmathlib v4.19.0を準備する。
3. 新しい乱数の種で、Lv1〜5の問題を難易度ごとに選ぶ。エンジンの出題配分（大分類、次に細分類の偏りを抑える）を使い、同じ問題は含めない。
4. 各問題について、次の2つを行う。
   - Recipeから問題・解法を再生成し、一般項と初期条件・漸化式・定義域条件の一致を n=20 まで厳密計算で確かめる。
   - Leanで、初期値、全ての添字での漸化式、一意性、分母や正値の条件を証明する。
5. 公理の監査で、`sorry` と独自の公理を拒否する。Leanで失敗した候補は除外し、別の候補で補う。除外が5件を超えたら失敗とする。
6. `recurrence-bank check` で全問を再照合し、Lv6・画面・ブラウザーの検査を通す。
7. `recurrence/bank/` を `main` へコミットし、そのコミットをPagesへ公開する。

途中で失敗した場合はコミットも公開もしません。生成中に `main` が進むとpushが失敗するため、もう一度実行してください。`main` にブランチ保護がある場合は、`github-actions[bot]` によるpushを許可してください。

更新すると、Lv1〜5の以前の問題IDと、それを含む共有リンクは使えなくなります。リンクを開くと「指定された問題がない」と表示し、別の問題を出題します。各問題のレシピJSONは、[漸化式ラボ](https://github.com/mas256/recurrence-equation-generator)の「保存したRecipeから問題を再現」で読み込めます。過去の問題バンクはGitの履歴に残ります。

## 問題バンクの形式と公開時の検査

`bank/problems.json` は、エンジンが書き出した問題ごとの表示用データです。主な内容は次のとおりです。

- 問題文・解法・別解・一般項のTeX
- 難易度スコア、Recipe、有限項の検査結果
- Leanの証明ソースと監査結果

`bank/manifest.json` には、次の記録を残します。

- 乱数の種、エンジンの版とコミット、生成日時、実行ID
- 難易度ごとの問題数、除外した候補
- `problems.json` のSHA-256

通常の公開（`main` へのpush）では問題を作り直しません。コミット済みのバンクをLeanなしで検査します。

- `recurrence-bank check` が、各RecipeからLeanの証明ソースまで再生成し、記録と完全に一致することを確かめる。
- 同時に、有限項の厳密計算をやり直す。
- エンジンのロックとバンクの生成元が一致しない場合は公開を止める。エンジンを更新したときは、再生成してください。

画面は `manifest.json` のSHA-256とバンクを照合してから出題します。日本語の解説文や、学習上の難しさそのものはLeanの検証対象ではありません。別解の途中式は有限項の検査で、Leanの証明は原問題についてのものです。難易度は登録解法の教育上のスコアで、学習者の実測による校正は今後の課題です。

## Lv6の固定問題

難易度6向けに、エンジンが生成しない分野の[固定問題60問](authored/level6-problems.md)と[方針・解答・解説](authored/level6-solutions.md)を事前作成しました。扱う分野は、ガウス型・隣接4項間・ニュートン法・対称式・三角関数・非隣接型・二重数列・母関数・畳み込み・ペル方程式などです。係数・初期値・小問は変更せずに表示します。データ形式と検算範囲は[固定問題集のREADME](authored/README.md)に記しています。

## 画面とTeX出力

難易度1〜6から選び、ボタンで1問ずつ出題します。同じ設定では、出題済みの問題を一巡するまで重複させません。ヒントは主解法の方針、解答は主解法の途中式と一般項です。登録された別解は2つまで折りたたんで表示します。Lv1〜5の解法スコア・検証情報と、Lv6の出典・検算情報は、それぞれ別の折りたたみに表示します。

「まとめて出題」はフィルターにかかわらず、Lv1・2・5・6を各2問、Lv3・4を各3問、計14問を難易度順に表示します。各問の直下の「ヒント」「答え」「Equashare」「TeX」は、その問だけが対象です。印刷とリンク共有は14問全体が対象です。

TeXは教科書と同じjsbook・A4・11pt・20mm余白・2段組（段間12pt、罫線0.4pt）です。pLaTeXとdvipdfmxで組版します。答えを開いているときは方針・解答・解法と別解を含み、閉じているときは問題のみを出力します。

「Equashare」は、その問題を入力済みのブラウザー版Equashareを新しいタブで開きます。問題文は `\text{…}` で、初期条件と漸化式は1行に1つの数式で渡します。

## 開発

```bash
git clone https://github.com/mas256/recurrence-equation-generator.git /tmp/recurrence-engine
git -C /tmp/recurrence-engine checkout "$(jq -r .revision recurrence/engine-lock.json)"
cargo build --release --locked --bin recurrence-bank --manifest-path /tmp/recurrence-engine/Cargo.toml

# コミット済みのバンクを検査する（Lean不要）
/tmp/recurrence-engine/target/release/recurrence-bank check --bank recurrence/bank

# 新しいバンクを生成する（Lean 4.19.0とmathlibを準備する）
bash /tmp/recurrence-engine/scripts/setup-lean.sh
python3 recurrence/scripts/regenerate-bank.py --engine-root /tmp/recurrence-engine \
  --bank-binary /tmp/recurrence-engine/target/release/recurrence-bank --per-level 30

# Lv6と画面の検査
python3 -m pip install -r recurrence/requirements-dev.txt
python3 recurrence/scripts/authored_workbook.py --check
python3 recurrence/tests/level6_check.py
node --test recurrence/tests/model.test.mjs recurrence/tests/batch-model.test.mjs
```

ブラウザー検査は、`recurrence/bank/` と `authored/level6.json` を `recurrence/data/` にコピーし、リポジトリのルートで `python3 -m http.server 8787` を起動してから `node recurrence/tests/browser.cjs` を実行します。

エンジンを更新するときは、`engine-lock.json` のコミットと版を変更し、同じPRで問題バンクを再生成してください。
