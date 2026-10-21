#!/usr/bin/env python3
"""Render the `@[dlmf]` tag dump as a browsable pilot index page.

Usage (from the project root):

    python3 scripts/dlmf_index_page.py dlmf-tags.json OUT.html

Input is the JSON written by scripts/DumpDLMF.lean. Per-section denominators come from the
project's enumerations of DLMF chapters: the equation lines of the root acquisition ledgers
(every numbered equation of Chapters 6–9, 11, 12 and 14, with a note for equations that carry
no tagged declaration) and the "tagged / numbered" columns of the coverage tables for
Chapters 13 and 18. The page template is scripts/dlmf_index_template.html.
"""
import collections
import json
import os
import re
import sys

CHAPTERS = {
    1: 'Algebraic and Analytic Methods', 2: 'Asymptotic Approximations', 3: 'Numerical Methods',
    4: 'Elementary Functions', 5: 'Gamma Function',
    6: 'Exponential, Logarithmic, Sine, and Cosine Integrals',
    7: "Error Functions, Dawson's and Fresnel Integrals",
    8: 'Incomplete Gamma and Related Functions', 9: 'Airy and Related Functions',
    10: 'Bessel Functions', 11: 'Struve and Related Functions', 12: 'Parabolic Cylinder Functions',
    13: 'Confluent Hypergeometric Functions', 14: 'Legendre and Related Functions',
    15: 'Hypergeometric Function', 16: 'Generalized Hypergeometric Functions and Meijer G-Function',
    17: 'q-Hypergeometric and Related Functions', 18: 'Orthogonal Polynomials',
    19: 'Elliptic Integrals', 20: 'Theta Functions', 21: 'Multidimensional Theta Functions',
    22: 'Jacobian Elliptic Functions', 23: 'Weierstrass Elliptic and Modular Functions',
    24: 'Bernoulli and Euler Polynomials', 25: 'Zeta and Related Functions',
    26: 'Combinatorial Analysis', 27: 'Functions of Number Theory',
    28: "Mathieu Functions and Hill's Equation", 29: 'Lamé Functions',
    30: 'Spheroidal Wave Functions', 31: 'Heun Functions', 32: 'Painlevé Transcendents',
    33: 'Coulomb Functions', 34: '3j, 6j, 9j Symbols', 35: 'Functions of Matrix Argument',
    36: 'Integrals with Coalescing Saddles',
}
LEDGERS = ['AiryAcquisition.md', 'DLMF678Acquisition.md', 'DLMF111214Acquisition.md']
TABLES = ['DLMF/Confluent/DLMFCoverage.md', 'DLMF/OrthogonalPolynomials/DLMFCoverage.md']
STATUS = {'proved': 0, 'admitted': 1, 'proved from admissions': 2, 'nonstandard': 3}


def natkey(s):
    return [int(x) if x.isdigit() else x for x in re.split(r'(\d+)', s)]


def base_id(i):
    """The numbered equation a key belongs to (`13.6.E11_1` → `13.6.E11`)."""
    return re.sub(r'_\d+$', '', i)


def main():
    dump = json.load(open(sys.argv[1]))
    out = sys.argv[2]
    here = os.path.dirname(os.path.abspath(__file__))

    # Display order: upstream libraries first; open pull requests and other GitHub projects
    # are reserved for later layers; this project last.
    projects = ['Mathlib', 'TauCeti', 'lean-DLMF']
    files, file_idx = [], {}
    ids = collections.defaultdict(list)
    for e in dump['entries']:
        st = e['status']
        if st == 'admitted' and e.get('sorryDirect') is False:
            st = 'proved from admissions'
        path = ''
        if e['sourceUrl']:
            path = e['sourceUrl'].split('/blob/', 1)[1].split('/', 1)[1].split('#')[0]
        if path not in file_idx:
            file_idx[path] = len(files)
            files.append(path)
        ids[e['dlmf']].append([e['decl'], projects.index(e['project']) if e['project'] in projects
                               else projects.index('lean-DLMF'), STATUS[st], 0 if e['kind'] == 'theorem' else 1,
                               file_idx[path], e['line'] or 0,
                               1 if e.get('source') == 'pointer' else 0,
                               e['comment'], e.get('recordedIn') or ''])

    # Denominators, titles and notes for untagged equations from the project's enumerations.
    listed = collections.defaultdict(set)
    counts = {}
    titles = {}
    notes = {}
    eqline = re.compile(r'^- \[(\d+\.\d+\.[ETF]\d+(?:_\d+)?)\]\(https://dlmf\.nist\.gov/[^)]*\):(.*)$')
    for f in LEDGERS:
        for line in open(f):
            m = re.match(r'^#+ \[?§(\d+\.\d+)[: ]\s*([^\]()]+?)(?:\s*\(\d+ equations?\))?\]?(?:\(|$)', line)
            if m:
                titles[m.group(1)] = m.group(2).strip()
            m = eqline.match(line)
            if m:
                i, rest = m.group(1), m.group(2)
                if 'retired' in rest.lower():
                    continue
                listed['.'.join(i.split('.')[:2])].add(base_id(i))
                if i not in ids:
                    if 'refuted' in rest.lower():
                        notes[i] = 'printed statement refuted; counterexample proved'
                    elif 'excluded: numerical' in rest:
                        notes[i] = 'excluded: numerical'
                    elif 'Mathlib' in rest:
                        notes[i] = 'upstream pointer, untagged'
                    else:
                        notes[i] = 'no tagged declaration'
    for sec, s in listed.items():
        counts[sec] = len(s)
    for f in TABLES:
        for line in open(f):
            m = re.match(r'^\| \[(\d+\.\d+)\]\([^)]*\) \| (\d+) / (\d+) \|', line)
            if m:
                counts.setdefault(m.group(1), int(m.group(3)))

    sections = collections.defaultdict(set)
    for i in ids:
        sections['.'.join(i.split('.')[:2])].add(i)
    for i in notes:
        sections['.'.join(i.split('.')[:2])].add(i)
    for sec in counts:
        sections.setdefault(sec, set())

    chapters = []
    for n, title in CHAPTERS.items():
        secs = sorted((s for s in sections if s.split('.')[0] == str(n)), key=natkey)
        chapters.append({'n': n, 'title': title, 'sections': [
            {'key': s, 'title': titles.get(s, ''), 'count': counts.get(s),
             'ids': sorted(sections[s], key=natkey)} for s in secs]})

    projinfo = dump['projects']
    meta = {
        'format': dump['format'],
        'repos': {p: {'url': re.sub(r'\.git$', '', (projinfo.get(p) or {}).get('url') or ''),
                      'rev': (projinfo.get(p) or {}).get('rev') or ''} for p in projects},
        'summary': dump['summary'],
        'keys': len(ids),
        'byProject': collections.Counter(projects[r[1]] for v in ids.values() for r in v),
        'pointers': sum(r[6] for v in ids.values() for r in v),
    }
    data = {'meta': meta, 'projects': projects, 'files': files, 'chapters': chapters,
            'ids': ids, 'notes': notes}
    tpl = open(os.path.join(here, 'dlmf_index_template.html')).read()
    blob = json.dumps(data, separators=(',', ':'), ensure_ascii=False).replace('</', '<\\/')
    open(out, 'w').write(tpl.replace('/*DATA*/null', blob))
    print(f'{out}: {len(ids)} keys, {sum(len(v) for v in ids.values())} records, '
          f'{len(notes)} untagged listed equations, {os.path.getsize(out)} bytes')


if __name__ == '__main__':
    main()
