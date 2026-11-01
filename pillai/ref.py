"""Reference model of the search: the tuples (x, y, a, b) in the machine's order and the
events of each (`B` a beep, `O` a boop)."""

def nexcom(r):
    """The next composition in NEXCOM order (same total, or total + 1 after the last one)."""
    r = list(r); k = len(r)
    h = next(i for i, v in enumerate(r) if v > 0)
    if h == k - 1:
        return [r[h] + 1] + [0] * (k - 1)
    t = r[h]; r[h] = 0; r[0] = t - 1; r[h + 1] += 1
    return r

def tuples():
    """(x, y, a, b) in the order tested: the NEXCOM successors of the seed (3, 2, 2, 2)."""
    cur = [1, 0, 0, 0]
    while True:
        cur = nexcom(cur)
        yield tuple(v + 2 for v in cur)

def ev(t):
    x, y, a, b = t
    d = a ** x - b ** y
    return 'B' * (d - 1) + 'O' if d > 0 else ''

def events(n):
    """The events of the first n tuples."""
    g = tuples()
    return ''.join(ev(next(g)) for _ in range(n))
