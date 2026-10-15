"""Render the hand-authored bank without creating or changing any problems."""
import argparse
from collections import Counter
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BANK = ROOT / 'authored/level6.json'


def render(bank):
    categories = {c['id']: c['label'] for c in bank['categories']}
    counts = Counter(p['category'] for p in bank['problems'])
    intro = (
        f"全{len(bank['problems'])}問。難易度6は、既存の自動生成で扱っていない分野から"
        "事前に作成した問題を出題するための区分である。\n\n"
        "特に断らない限り添字は整数で、各漸化式に記した範囲を用いる。"
        "$\\lfloor x\\rfloor$ は $x$ を超えない最大の整数を表す。\n\n"
    )
    table = '| 分野 | 問数 |\n| --- | ---: |\n' + ''.join(
        f'| {label} | {counts[key]} |\n' for key, label in categories.items())
    questions = ['# 難易度6 固定問題集：問題\n\n', intro, table,
                 '\n[方針・解答・解説](level6-solutions.md)\n']
    solutions = ['# 難易度6 固定問題集：方針・解答・解説\n\n',
                 '[問題一覧](level6-problems.md)\n\n',
                 '各解説は手作業で作成した。検算の方法と範囲は [README](README.md) を参照。\n']
    for category, label in categories.items():
        questions.append(f'\n## {label}\n')
        solutions.append(f'\n## {label}\n')
        for p in bank['problems']:
            if p['category'] != category:
                continue
            heading = f"\n### {p['id']}　{p['title']}\n\n"
            questions.extend([heading, p['statement'], '\n'])
            solutions.extend([heading, f"**方針**　{p['hint']}\n\n",
                              f"**解答**\n\n{p['answer']}\n\n", '**解説**\n\n',
                              '\n\n'.join(p['solution']), '\n\n'])
            source = p['source']
            solutions.append(f"出典：[{source['location']}]({source['url']})。"
                             f"{source['adaptation']}。\n")
    return {
        ROOT / 'authored/level6-problems.md': ''.join(questions),
        ROOT / 'authored/level6-solutions.md': ''.join(solutions),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true', help='Check committed documents are current')
    args = parser.parse_args()
    bank = json.loads(BANK.read_text(encoding='utf-8'))
    for path, content in render(bank).items():
        if args.check:
            if not path.exists() or path.read_text(encoding='utf-8') != content:
                raise SystemExit(f'Out of date: {path}; run python3 recurrence/scripts/authored_workbook.py')
        else:
            path.write_text(content, encoding='utf-8')
    print(f"{'Checked' if args.check else 'Rendered'} {len(bank['problems'])} fixed problems")


if __name__ == '__main__':
    main()
