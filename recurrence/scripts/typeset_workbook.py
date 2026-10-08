"""Typeset the regenerated batch with the source textbook's jsbook settings."""
import json,re,sys
from pathlib import Path
import sympy as sp
sys.path.insert(0,str(Path(__file__).resolve().parent))
ROOT=Path(sys.argv[1]).resolve().parent if len(sys.argv)>1 else Path(__file__).resolve().parents[1]/'build'
from expr import evaluate,latex,mul
batch=json.loads((ROOT/'workbook.json').read_text());qs=batch['problems']
n=sp.Symbol('n',integer=True,positive=True)
def symbolic(e):
 op=e['op'];a=e.get('args',[])
 if op=='rational':return sp.Rational(e['num'],e['den'])
 if op=='index':return n
 if op=='nat_index':return n-1+e['offset']
 if op=='nat_constant':return sp.Integer(e['value'])
 if op=='triangular':return n*(n-1)/2
 if op=='choose':return sp.expand_func(sp.binomial(symbolic(a[0]),symbolic(a[1])))
 if op=='add':return sum(map(symbolic,a))
 if op=='mul':return sp.prod(map(symbolic,a))
 if op=='div':return symbolic(a[0])/symbolic(a[1])
 if op=='pow':return symbolic(a[0])**symbolic(a[1])
 raise ValueError(op)
def clean(e):
 original=symbolic(e)
 z=sp.simplify(original)
 bases=[a for a in z.atoms(sp.Pow) if a.exp.has(n) and not a.base.has(n)]
 choices=[z,sp.factor(z),sp.factor_terms(sp.collect(sp.expand(z),bases))]
 z=min(choices,key=lambda x:len(sp.latex(x)))
 if z.is_Pow:z=z.func(z.base,sp.factor(z.exp))
 for k in range(24):assert z.subs(n,k+1)==sp.Rational(evaluate(e,k)),(e,k,z)
 return sp.latex(z,fold_frac_powers=False)
def mathfmt(s):
 # Fractions inside fractions use the taller continued-fraction form.
 return s.replace(r'\dfrac',r'\frac')
def display(s):return '\\[\\fitmath{'+mathfmt(s)+'}\\]\n'
def escaped(s):return s.replace('&',r'\&').replace('%',r'\%').replace('_',r'\_')
def paragraph(s):
 s=s.replace('+-','-').replace('--','+').replace('+0','').replace('=0+','=')
 s=s.replace('です。','である。').replace('とおけます。','とおける。').replace('を得ます。','を得る。').replace('となります。','となる。').replace('消えます。','消える。').replace('まとめられます。','まとめられる。').replace('定義できます。','定義できる。')
 parts=[];last=0
 for m in re.finditer(r'\\\((.*?)\\\)',s):
  parts.append(escaped(s[last:m.start()]));v=mathfmt(m.group(1))
  if '\\begin{aligned}' in v or len(v)>65:parts.append('\n'+display(v))
  else:parts.append(r'\('+v+r'\)')
  last=m.end()
 parts.append(escaped(s[last:]));return ''.join(parts)+'\\par\n'
# Use compact final expressions, independently checked against the original AST.
answers={q['id']:(clean(q['ir']['formula']),clean(q['ir']['b_formula']) if q['ir'].get('shape')=='system' else None) for q in qs}
# Display simplifications in the prose are confined to exact formula strings.
replacements={}
for q in qs:
 for e in [q['ir']['formula'],*([q['ir']['b_formula']] if q['ir'].get('shape')=='system' else []),*[d['formula'] for r in q['routes'] for d in r.get('derivation',[])]]:
  replacements[latex(e)]=clean(e)
  if e['op']=='pow':replacements[latex(e['args'][1])]=clean(e['args'][1])
def prose(s):
 def repl(m):
  v=m.group(1)
  if v.count('=')==1:
   left,right=v.split('=',1)
   if right in replacements:v=left+'='+replacements[right]
  return r'\('+v+r'\)'
 s=re.sub(r'\\\((.*?)\\\)',repl,s)
 return paragraph(s)
def statement(q):
 s=q['statement'];result=[]
 if s.get('definitions_tex'):result.append(paragraph(r'\('+s['definitions_tex']+r'\) とおく。'))
 result.append(paragraph(r'\('+r',\quad '.join(s['initials_tex'])+r'\) とし、'))
 rec=s['recurrence_tex']
 if q['ir'].get('shape')=='pure_sum' and q['ir']['second_order']:
  lhs=latex(mul(q['ir']['P2'],{'op':'sum_term','offset':2}));terms=[latex(mul(q['ir']['Q2'],{'op':'sum_term','offset':1})),latex(mul(q['ir']['R2'],{'op':'sum_term','offset':0}))];terms=[v for v in terms if v!='0']
  rec=r'\begin{aligned}'+lhs+'&='+terms[0]+''.join(r'\\&\quad{}'+('' if e.startswith('-') else '+')+e for e in terms[1:])+r'\end{aligned}'
 result.append(display(rec))
 condition='で定められる2つの数列の一般項をそれぞれ求めよ。' if q['ir'].get('shape')=='system' else 'を満たす数列の一般項を求めよ。'
 if q['ir'].get('shape')=='power_second':condition='を満たす正の数列の一般項を求めよ。'
 result.append(paragraph(condition));return ''.join(result)
preamble=r'''\documentclass[dvipdfmx,a4paper,11pt,fleqn,openany]{jsbook}
\usepackage{amsmath,amsthm,amssymb,amsfonts}
\everymath{\displaystyle}
\usepackage[margin=20truemm]{geometry}
\usepackage{multicol,enumitem,url,quotchap}
\usepackage[table]{xcolor}
\usepackage{tcolorbox,graphicx}
\tcbuselibrary{breakable}
\definecolor{shadecolor}{gray}{0.80}
\usepackage[dvipdfmx,hidelinks]{hyperref}
\usepackage{pxjahyper}
\raggedcolumns
\setlength{\columnsep}{12pt}
\setlength{\columnseprule}{0.4pt}
\setlength{\parskip}{0pt}
\setlength{\emergencystretch}{1em}
\setlength{\abovedisplayskip}{10pt plus 2pt minus 2pt}
\setlength{\belowdisplayskip}{10pt plus 2pt minus 2pt}
\setlength{\abovedisplayshortskip}{8pt plus 2pt minus 2pt}
\setlength{\belowdisplayshortskip}{8pt plus 2pt minus 2pt}
\setlist[enumerate,1]{label=(\arabic*),leftmargin=\leftmargini,parsep=3pt}
\newsavebox{\mathbox}
\newcommand{\fitmath}[1]{\sbox{\mathbox}{$\displaystyle #1$}%
\ifdim\wd\mathbox>\linewidth
\typeout{MATHWIDTH: \the\wd\mathbox; AVAILABLE: \the\linewidth}\typeout{FORMULA: \detokenize{#1}}%
\resizebox{\linewidth}{!}{\usebox{\mathbox}}%
\else\usebox{\mathbox}\fi}
\title{漸化式演習集}
\author{MAS256}
\date{2026年10月8日 改訂版}
\begin{document}
\maketitle
\tableofcontents
\chapter{問題演習}
\begin{multicols*}{2}
以下、\,$n$は正の整数とする。Lv1〜Lv4に各15問を収録した。
連立漸化式では両方の数列の一般項を求める。
部分和を使う問題では\,$S_0=0$,\,$S_n=\sum_{k=1}^n a_k$とする。
\par
'''
out=[preamble];names={1:'基本',2:'標準',3:'応用',4:'発展'}
for lv in range(1,5):
 group=[q for q in qs if q['scores']['level']==lv];assert len(group)==15
 out.append(r'\section{Lv'+str(lv)+' '+names[lv]+'}')
 out.append(r'\subsection{問題}')
 out.append(r'\begin{enumerate}[label=\textbf{問\arabic*.},leftmargin=3.8em]')
 for q in group:
  out.append(r'\item\label{問題：'+q['id']+'}'+statement(q))
 out.append(r'\end{enumerate}')
out.append(r'\end{multicols*}\chapter{方針・解答・解法}\begin{multicols*}{2}')
for lv in range(1,5):
 group=[q for q in qs if q['scores']['level']==lv]
 out.append(r'\section{Lv'+str(lv)+' '+names[lv]+'}')
 for section in ['方針','解答','解法']:
  out.append(r'\subsection{'+section+'}')
  out.append(r'\begin{enumerate}[label=\textbf{問\arabic*.},leftmargin=3.8em]')
  for q in group:
   out.append(r'\item\label{'+section+'：'+q['id']+'}')
   if section=='方針':out.append(prose(q['routes'][0]['hint']))
   else:
    if section=='解法':
     for s in q['routes'][0]['steps']:out.append(prose(s))
    a,b=answers[q['id']]
    if b:out.append(display(r'\begin{aligned}a_n&='+a+r'\\b_n&='+b+r'\end{aligned}'))
    else:out.append(display('a_n='+a))
    out.append('である。\n')
  out.append(r'\end{enumerate}')
out.append(r'\end{multicols*}\end{document}')
target=ROOT/'textbook-workbook.tex';target.write_text('\n'.join(out))
print(target)
