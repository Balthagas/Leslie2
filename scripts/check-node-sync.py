#!/usr/bin/env python3
"""Check that nodes-min/ carries the same formal frontmatter as nodes/.

The two node directories hold the same statements for the two editions of the
blueprint: nodes/ carries the full bodies and proofs, nodes-min/ carries a
one-sentence body pointing at the Lean source. Their formal frontmatter --- the
environment's \\label, its \\lean declaration lists, its \\leanok marks and its
\\uses dependencies --- must be identical, since that is what the dependency
graph and the declaration harvest are built from. Bodies differ by design and
are not compared: a min body cites declarations with \\leandecl instead.

Usage: python3 scripts/check-node-sync.py
Exits 0 and prints "N/N in sync" when every pair agrees, else lists the drifts
and exits 1.
"""
import os
import re
import sys

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAT = os.path.join(REPO, 'blueprint', 'src', 'nodes')
MIN = os.path.join(REPO, 'blueprint', 'src', 'nodes-min')

ENV_OPEN = re.compile(
    r'\s*\\begin\{(definition|theorem|lemma|proposition|corollary|proof)\}')
FM_TOKEN = re.compile(r'\\(label|lean|leanok|uses)(?![A-Za-z])')


def balanced(s, i):
    """Given s[i] == '{', return the index just past the matching '}'."""
    depth = 0
    while i < len(s):
        if s[i] == '{':
            depth += 1
        elif s[i] == '}':
            depth -= 1
            if depth == 0:
                return i + 1
        i += 1
    raise ValueError('unbalanced brace')


def is_frontmatter_line(line):
    """True when the line consists solely of \\label, \\lean, \\leanok, \\uses."""
    s = line.strip()
    if not s:
        return False
    i = 0
    while i < len(s):
        m = FM_TOKEN.match(s, i)
        if not m:
            return False
        name = m.group(1)
        i = m.end()
        if name == 'leanok':
            if s[i:i + 2] == '{}':
                i += 2
        else:
            while i < len(s) and s[i] == ' ':
                i += 1
            if i >= len(s) or s[i] != '{':
                return False
            try:
                i = balanced(s, i)
            except ValueError:
                return False
        while i < len(s) and s[i] == ' ':
            i += 1
    return True


def frontmatters(text):
    """Return the frontmatter block of each environment, in document order.

    An environment's frontmatter runs from its \\begin line up to the first line
    that is not made of frontmatter tokens alone; a \\uses spanning several
    lines is taken whole. Everything after it is the body, which this check
    ignores.
    """
    lines = text.split('\n')
    blocks = []
    i = 0
    while i < len(lines):
        m = ENV_OPEN.match(lines[i])
        if not m:
            i += 1
            continue
        env = m.group(1)
        end = i
        while not re.match(r'\s*\\end\{%s\}' % env, lines[end]):
            end += 1
        j = i + 1
        while j < end:
            if is_frontmatter_line(lines[j]):
                j += 1
                continue
            stripped = lines[j].strip()
            if stripped.startswith('\\uses{') and '}' not in stripped:
                buf = ''
                k = j
                while k < end:
                    buf += lines[k].strip()
                    if buf.count('{') == buf.count('}'):
                        break
                    k += 1
                j = k + 1
                continue
            break
        blocks.append((env, '\n'.join(lines[i:j])))
        i = end + 1
    return blocks


def tokens(block):
    """The formal token sequence of one frontmatter block."""
    labels, leans, uses = [], [], []
    leanok = 0
    i = 0
    while True:
        m = FM_TOKEN.search(block, i)
        if not m:
            break
        name = m.group(1)
        i = m.end()
        if name == 'leanok':
            leanok += 1
            continue
        while i < len(block) and block[i] in ' \n':
            i += 1
        if i >= len(block) or block[i] != '{':
            continue
        j = balanced(block, i)
        arg = ' '.join(block[i + 1:j - 1].split())
        {'label': labels, 'lean': leans, 'uses': uses}[name].append(arg)
        i = j
    return {'label': labels, 'lean': leans, 'leanok': leanok, 'uses': uses}


def main():
    if not os.path.isdir(MIN):
        print('missing directory: %s' % MIN)
        return 1
    names = sorted(n for n in os.listdir(FAT) if n.endswith('.tex'))
    drifts = []
    for name in names:
        minpath = os.path.join(MIN, name)
        if not os.path.isfile(minpath):
            drifts.append('%s: absent from nodes-min/' % name)
            continue
        fat = frontmatters(open(os.path.join(FAT, name)).read())
        mn = frontmatters(open(minpath).read())
        if len(fat) != len(mn):
            drifts.append('%s: %d environments in nodes/, %d in nodes-min/'
                          % (name, len(fat), len(mn)))
            continue
        for k, ((fenv, fblock), (menv, mblock)) in enumerate(zip(fat, mn)):
            if fenv != menv:
                drifts.append('%s: environment %d is %s in nodes/, %s in '
                              'nodes-min/' % (name, k + 1, fenv, menv))
                continue
            ft, mt = tokens(fblock), tokens(mblock)
            for key in ('label', 'lean', 'leanok', 'uses'):
                if ft[key] != mt[key]:
                    drifts.append('%s (%s): %s differs --- nodes/ %r, '
                                  'nodes-min/ %r'
                                  % (name, fenv, key, ft[key], mt[key]))
    extra = sorted(n for n in os.listdir(MIN)
                   if n.endswith('.tex') and n not in names)
    for name in extra:
        drifts.append('%s: present in nodes-min/ only' % name)
    if drifts:
        for d in drifts:
            print(d)
        return 1
    print('%d/%d in sync' % (len(names), len(names)))
    return 0


if __name__ == '__main__':
    sys.exit(main())
