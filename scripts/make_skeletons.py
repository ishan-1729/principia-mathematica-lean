#!/usr/bin/env python3
"""Generate the Lean files of the formalization from data/principia.json (run once; refuses to
overwrite).

One file per Section of a Part (`PrincipiaMathematica/PartN/SectionX.lean`). Each file gets a header
naming the Section and its starred numbers, and for each number ✱N:
* a unit block `## [✱N] Title` quoting the opening of Whitehead and Russell's summary, with
  placeholders for the Lean reading and status;
* for each numbered proposition ✱N·M, a docstring with its number and its formula as printed
  (MathJax TeX), followed by a `-- TODO(pmN_M)` placeholder for the Lean declaration `pmN_M`.
"""
import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
ROMAN = {'I': 1, 'II': 2, 'III': 3, 'IV': 4, 'V': 5}


def decl_name(n: str) -> str:
    """'2·01' -> 'pm2_01'."""
    a, b = n.split('·')
    return f'pm{a}_{b}'


# Large Sections are split in two files: numbers from the given one on go to Section<X>2.
SPLIT = {(1, 'C'): 23, (1, 'D'): 36, (2, 'C'): 73, (2, 'E'): 94, (3, 'B'): 115, (3, 'C'): 122,
         (5, 'A'): 206, (5, 'B'): 213}


def module_of(num: dict) -> str:
    part = ROMAN[re.match(r'PART ([IVX]+)', num['part']).group(1)]
    sec = re.match(r'SECTION ([A-E])', num['section']).group(1)
    second = (part, sec) in SPLIT and num['number'] >= SPLIT[(part, sec)]
    return f'Part{part}/Section{sec}' + ('2' if second else '')


def doc_safe(t: str) -> str:
    return t.replace('-/', '- /').replace('/-', '/ -')


def quote(t: str, limit: int = 1200) -> str:
    paras = [p.strip() for p in t.split('\n\n') if p.strip()]
    paras = [p for p in paras if not re.fullmatch(r'\*?Summary\*? of \*?\*?\d+\.?', p)]
    out, n = [], 0
    for p in paras:
        p = re.sub(r'\s*\n\s*', ' ', p)
        if n + len(p) > limit and out:
            out.append('…')
            break
        out.append(p)
        n += len(p)
    return '\n>\n'.join('> ' + doc_safe(p) for p in out)


def title_case(s: str) -> str:
    s = s.strip(' .').lower()
    return s[:1].upper() + s[1:]


def main() -> int:
    data = json.loads((ROOT / 'data' / 'principia.json').read_text(encoding='utf-8'))
    files = {}
    for v in data['volumes']:
        for num in v['numbers']:
            files.setdefault(module_of(num), []).append((v['volume'], num))
    for mod, nums in files.items():
        path = ROOT / 'PrincipiaMathematica' / (mod + '.lean')
        if path.exists():
            print('exists, skipping', path.relative_to(ROOT)); continue
        path.parent.mkdir(parents=True, exist_ok=True)
        part = int(mod.split('/')[0][4:])
        vol, first = nums[0]
        sec_title = re.sub(r'\s+', ' ', first['section'].split('\n\n')[1] if '\n\n' in first['section'] else first['section'])
        sec_title = re.split(r'\*?Summary', sec_title)[0].strip()
        m = re.match(r"([A-Z][A-Z0-9 ,\-'’]+[A-Z])\.", sec_title)
        sec_title = m.group(1) if m else sec_title
        ns = 'PrincipiaMathematica'
        lines = [f'import PrincipiaMathematica.Defs.Part{part}', '', '/-!',
                 f'# Part {list(ROMAN)[part - 1]}, {first["section"].split(chr(10))[0].strip(" .").title()}: {title_case(sec_title)}', '',
                 f'Volume {vol}. Numbers: ' + ', '.join(f'✱{n["number"]}' for _, n in nums) + '.', '',
                 'Each number has a unit block; each proposition ✱N·M is the declaration `pmN_M`, whose docstring',
                 'gives the formula as printed (MathJax TeX). The full text is in `data/principia.json`.', '-/', '',
                 f'namespace {ns}', '']
        for _, n in nums:
            pg = n['page']
            lines += ['/-!', f'## [✱{n["number"]}] {title_case(n["title"])}', '', f'*(Vol. {vol}, p. {pg})*', '',
                      quote(n['summary']) or '> (no summary)', '', '**Lean reading.** TODO', '', '**Status.** TODO', '-/', '']
            for p in n['propositions']:
                lines += [f'/-- ✱{p["n"]}{" (" + p["kind"] + ")" if p["kind"] != "prop" else ""}. '
                          f'{doc_safe(p["formula"])} -/', f'-- TODO({decl_name(p["n"])})', '']
        lines += [f'end {ns}', '']
        path.write_text('\n'.join(lines), encoding='utf-8', newline='\n')
        print('wrote', path.relative_to(ROOT), sum(len(n['propositions']) for _, n in nums), 'propositions')
    return 0


if __name__ == '__main__':
    sys.exit(main())
