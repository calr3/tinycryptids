"""Reference model: Barker sequences and the machine's search order."""
from itertools import product

def is_barker(a):
    n = len(a)
    for k in range(1, n):
        c = sum((1 if a[i] == a[i + k] else -1) for i in range(n - k))
        if abs(c) > 1:
            return False
    return True

def first_barker(n0):
    """First candidate (in the machine's order) that is Barker: length n0 upward,
    a[0] = 1, the rest read as a binary number with the last element least significant."""
    n = n0
    while True:
        for m in range(2 ** (n - 1)):
            bits = [1] + [int(c) for c in format(m, f'0{n-1}b')] if n > 1 else [1]
            if is_barker(bits):
                return bits
        n += 1

if __name__ == '__main__':
    for n0 in range(2, 14):
        print(n0, first_barker(n0))
