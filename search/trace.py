"""Summarize relaxed_walk stderr traces: python3 trace.py <err files...>  -> one line per file with the latest and best values."""
import sys, re
for f in sys.argv[1:]:
    last=None; best=None; start=None; zero=None
    for line in open(f):
        if line.startswith('start:'): start=line.strip()
        m=re.match(r't=(\d+) T=([\d.]+) E=(\d+) missing=(\d+) dups=(\d+) best=(\d+) V=(\d+)', line)
        if m: last=tuple(float(x) if i in (1,) else int(float(x)) for i,x in enumerate(m.groups()))
        m2=re.match(r't=(\d+) best=(\d+)(?: lam=[\d.]+)? swaps (\d+)/(\d+).*?\[T=([\d.]+) E=(\d+) m=(\d+) d=(\d+)\]', line)
        if m2: g=m2.groups(); last=(int(g[0]),float(g[4]),int(g[5]),int(g[6]),int(g[7]),int(g[1]),0)
        if 'ENERGY ZERO' in line: zero=line.strip()
    if last: print(f"{f}: t={last[0]} T={last[1]} E={last[2]} missing={last[3]} dups={last[4]} best={last[5]} V={last[6]}" + (f"  {zero}" if zero else ''))
    else: print(f, 'no report yet', zero or '')
