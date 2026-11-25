#!/usr/bin/env python3
"""Extract Whitehead & Russell, *Principia Mathematica*, Volumes I (1910) and II (1912), from the
Project Gutenberg MathJax HTML sources (eBooks #78050 and #78255, `*-src.htm`) into
`data/principia.json`.

Usage: python scripts/extract_source.py path/to/78050-src.htm path/to/78255-src.htm

The output records, for each volume:
* the front matter and the introduction (preface, Introduction chapters I–III, prefatory
  statements, summaries of parts and sections, notes), as text;
* each starred number ✱N: its part and section, its title, its summary (the prose before the first
  proposition), and every numbered proposition ✱N·M in the body: the formula (TeX, as printed,
  with the trailing reference list), its kind (Pp = primitive proposition, Df = definition,
  otherwise an asserted proposition), the original page, and the text that follows it up to the
  next proposition (the demonstration and any comment).

Clean-up: HTML tags are removed (italics become `*…*`), footnotes are inlined as `[Note: …]`,
mathematics stays as MathJax TeX between `\\( … \\)` / `\\[ … \\]`. Propositions that the summary of a
number repeats before the body are recorded once, from the body.
"""
import html, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PROP = re.compile(r'<p\s+class="nind">\s*<b>(?:<a id="[^"]*">)?\*?(\d+)·(\d+)(?:</a>)?\.?</b>\.?\s*(.*?)</p>', re.S)
PP = re.compile(r'\\text\{\s*Pp\s*\}|\bPp\b\.?\s*(?:\\\))?\s*\.?\s*$')
DF = re.compile(r'\\text\{\s*Df\s*\}|\bDf\b\.?\s*(?:\\\))?\s*\.?\s*$')


def text_of(h: str) -> str:
    h = re.sub(r'<span class="pagenum"[^>]*>.*?</span>', '', h, flags=re.S)
    h = re.sub(r'<a id="FNanchor[^>]*>\[(\d+)\]</a>', r'[^\1]', h)
    h = re.sub(r'</?(?:i|em)>', '*', h)
    h = re.sub(r'<br\s*/?>', '\n', h)
    h = re.sub(r'</p>|</div>|</h\d>|</tr>', '\n\n', h)
    h = re.sub(r'</td>', ' ', h)
    h = re.sub(r'<[^>]+>', '', h)
    h = html.unescape(h)
    h = re.sub(r'[ \t\r]+', ' ', h)
    h = re.sub(r' *\n *', '\n', h)
    h = re.sub(r'\n{3,}', '\n\n', h)
    return h.strip()


def footnotes(src: str) -> dict:
    notes = {}
    for m in re.finditer(r'<div class="footnote">\s*<p[^>]*>\s*<a id="Footnote_(\d+)"[^>]*>\[\d+\]</a>(.*?)</div>', src, re.S):
        notes[m.group(1)] = text_of(m.group(2))
    return notes


def inline_notes(t: str, notes: dict) -> str:
    return re.sub(r'\[\^(\d+)\]', lambda m: ' [Note: ' + notes.get(m.group(1), '?') + ']', t)


def page_at(src: str, pos: int) -> str:
    m = None
    for m in re.finditer(r'id="Page_([0-9ivxlc]+)"', src[:pos]):
        pass
    return m.group(1) if m else ''


def volume(path: Path, vol: int) -> dict:
    src = path.read_text(encoding='utf-8')
    src = src[:src.find('*** END OF THE PROJECT GUTENBERG')] if '*** END OF THE PROJECT GUTENBERG' in src else src
    notes = footnotes(src)
    src_body = re.sub(r'<div class="footnote">.*?</div>', '', src, flags=re.S)
    src_body = re.sub(r'<h3>FOOTNOTES:</h3>', '', src_body)
    heads = list(re.finditer(r'<h2[^>]*id="([^"]+)"[^>]*>(.*?)</h2>', src_body, re.S))
    out = {'volume': vol, 'front': [], 'numbers': []}
    part = section = ''
    for k, h in enumerate(heads):
        hid, title = h.group(1), text_of(h.group(2))
        end = heads[k + 1].start() if k + 1 < len(heads) else len(src_body)
        chunk = src_body[h.end():end]
        if hid.startswith('PART_'):
            part = (title + ' ' + text_of(chunk)[:200]).split('\n')[0].strip()
            out['front'].append({'id': hid, 'title': title, 'text': inline_notes(text_of(chunk), notes)})
            continue
        if hid.startswith('SECTION_'):
            section = text_of(chunk).split('\n\n')[0].strip()
            section = (title + ' ' + section).strip()
            out['front'].append({'id': hid, 'title': title, 'text': inline_notes(text_of(chunk), notes),
                                 'part': part})
            continue
        m = re.match(r'\*?(\d+)(?:_|$)', hid.lstrip('*'))
        if not (hid.startswith('*') or re.match(r'\d+_', hid)):
            out['front'].append({'id': hid, 'title': title, 'text': inline_notes(text_of(chunk), notes)})
            continue
        num = int(re.match(r'\*?(\d+)', hid).group(1))
        title = re.sub(r'^\*?\d+\.\s*', '', re.sub(r'\s+', ' ', title)).strip(' .')
        props = list(PROP.finditer(chunk))
        props = [p for p in props if int(p.group(1)) == num]
        # keep the last occurrence of each proposition number (the body, not the summary)
        last = {}
        for i, p in enumerate(props):
            last[p.group(2)] = i
        first_body = min(last.values()) if last else None
        summary_end = props[first_body].start() if props else len(chunk)
        # the summary ends at the first body proposition that is not also listed later
        recs = []
        for i, p in enumerate(props):
            if last[p.group(2)] != i:
                continue
            nxt = props[i + 1].start() if i + 1 < len(props) else len(chunk)
            formula = re.sub(r'\s+', ' ', inline_notes(text_of(p.group(3)), notes)).strip()
            kind_src = re.sub(r'\s*\[Note:.*?\]', '', formula)
            kind = 'Pp' if PP.search(kind_src) else ('Df' if DF.search(kind_src) else 'prop')
            recs.append({'n': f'{num}·{p.group(2)}', 'kind': kind, 'formula': formula,
                         'page': page_at(src_body, h.end() + p.start()),
                         'after': inline_notes(text_of(chunk[p.end():nxt]), notes)})
        # summary = the text before the first proposition kept from the body region
        body_start = min((props[i].start() for i in last.values()), default=len(chunk))
        out['numbers'].append({'number': num, 'title': title, 'part': part, 'section': section,
                               'page': page_at(src_body, h.end()),
                               'summary': inline_notes(text_of(chunk[:body_start]), notes),
                               'propositions': recs})
    return out


def main() -> int:
    sys.stdout.reconfigure(encoding='utf-8')
    vols = [volume(Path(sys.argv[1]), 1), volume(Path(sys.argv[2]), 2)]
    data = {'source': 'A. N. Whitehead and B. Russell, Principia Mathematica, Vol. I (Cambridge, 1910) and '
                      'Vol. II (1912). Project Gutenberg eBooks #78050 and #78255.',
            'volumes': vols}
    dst = ROOT / 'data' / 'principia.json'
    dst.parent.mkdir(exist_ok=True)
    dst.write_text(json.dumps(data, ensure_ascii=False, indent=1), encoding='utf-8', newline='\n')
    for v in vols:
        nums = v['numbers']
        n = sum(len(x['propositions']) for x in nums)
        kinds = {}
        for x in nums:
            for p in x['propositions']:
                kinds[p['kind']] = kinds.get(p['kind'], 0) + 1
        print(f"Vol {v['volume']}: {len(nums)} numbers, {n} propositions {kinds}; front parts: {len(v['front'])}")
        print('  numbers:', [x['number'] for x in nums])
        empty = [x['number'] for x in nums if not x['propositions']]
        if empty:
            print('  numbers without propositions:', empty)
    return 0


if __name__ == '__main__':
    sys.exit(main())
