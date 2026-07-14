#!/usr/bin/env python3
"""Exact-rational verifier for the binary32 roots used by the CUDA probe."""

from fractions import Fraction
import math
import struct
import sys


MAGIC = 0x45523132524F4F54
U32 = Fraction(1, 1 << 24)


def arctan_bracket(inv: int, pairs: int = 32):
    x = Fraction(1, inv)
    total = Fraction(0)
    partial = []
    for j in range(2 * pairs + 2):
        term = x ** (2 * j + 1) / (2 * j + 1)
        total += term if j % 2 == 0 else -term
        partial.append(total)
    # An alternating partial sum ending in a negative term is below the sum;
    # the preceding partial sum is above it.
    return partial[-1], partial[-2]


def pi_bracket():
    l5, u5 = arctan_bracket(5)
    l239, u239 = arctan_bracket(239)
    return 16 * l5 - 4 * u239, 16 * u5 - 4 * l239


def neg(x):
    return -x[1], -x[0]


def add(x, y):
    return x[0] + y[0], x[1] + y[1]


def mul(x, y):
    products = (x[0] * y[0], x[0] * y[1], x[1] * y[0], x[1] * y[1])
    return min(products), max(products)


def scale(x, q):
    return mul(x, (q, q))


def power(x, n):
    result = (Fraction(1), Fraction(1))
    base = x
    while n:
        if n & 1:
            result = mul(result, base)
        base = mul(base, base)
        n >>= 1
    return result


def trig_small(x, terms: int = 11):
    sin_poly = (Fraction(0), Fraction(0))
    cos_poly = (Fraction(0), Fraction(0))
    for j in range(terms):
        sign = Fraction(1 if j % 2 == 0 else -1)
        sin_poly = add(sin_poly, scale(power(x, 2 * j + 1),
                                      sign / math.factorial(2 * j + 1)))
        cos_poly = add(cos_poly, scale(power(x, 2 * j),
                                      sign / math.factorial(2 * j)))
    radius = max(abs(x[0]), abs(x[1]))
    sin_rem = radius ** (2 * terms + 1) / math.factorial(2 * terms + 1)
    cos_rem = radius ** (2 * terms) / math.factorial(2 * terms)
    return ((sin_poly[0] - sin_rem, sin_poly[1] + sin_rem),
            (cos_poly[0] - cos_rem, cos_poly[1] + cos_rem))


def root_bracket(exponent: int, prime: int, pi):
    # 2*pi*exponent/prime = quadrant*pi/2 + residual, with
    # |residual| < pi/4.  The nearest quadrant is exact integer arithmetic.
    quadrant = (8 * exponent + prime) // (2 * prime)
    residual = Fraction(2 * exponent, prime) - Fraction(quadrant, 2)
    if residual >= 0:
        x = residual * pi[0], residual * pi[1]
    else:
        x = residual * pi[1], residual * pi[0]
    sine, cosine = trig_small(x)
    q = quadrant % 4
    if q == 0:
        return cosine, sine
    if q == 1:
        return neg(sine), cosine
    if q == 2:
        return neg(cosine), neg(sine)
    return sine, neg(cosine)


def exact_float(value: float):
    numerator, denominator = value.as_integer_ratio()
    return Fraction(numerator, denominator)


def main(path: str, expected_primes=None):
    pi = pi_bracket()
    records = 0
    worst = Fraction(0)
    worst_record = None
    seen_primes = []
    with open(path, "rb") as source:
        magic_raw = source.read(8)
        if len(magic_raw) != 8 or struct.unpack("<Q", magic_raw)[0] != MAGIC:
            raise SystemExit("bad root-table magic")
        while True:
            raw_prime = source.read(4)
            if not raw_prime:
                break
            if len(raw_prime) != 4:
                raise SystemExit("truncated prime")
            prime = struct.unpack("<i", raw_prime)[0]
            if prime < 1 or prime > 59:
                raise SystemExit("bad prime")
            seen_primes.append(prime)
            raw = source.read(8 * prime)
            if len(raw) != 8 * prime:
                raise SystemExit("truncated root table")
            values = struct.unpack("<" + "ff" * prime, raw)
            for exponent in range(prime):
                cosine, sine = root_bracket(exponent, prime, pi)
                for component, bracket in ((values[2 * exponent], cosine),
                                           (values[2 * exponent + 1], sine)):
                    center = exact_float(component)
                    distance = max(abs(bracket[0] - center),
                                   abs(bracket[1] - center))
                    if distance > worst:
                        worst = distance
                        worst_record = (prime, exponent, component)
                    if bracket[0] < center - 4 * U32 or bracket[1] > center + 4 * U32:
                        raise SystemExit(
                            f"root enclosure failed at p={prime}, exponent={exponent}")
                    records += 1
        if source.read(1):
            raise SystemExit("trailing bytes")
    if expected_primes is not None and seen_primes != expected_primes:
        raise SystemExit(
            f"prime coverage mismatch: seen={seen_primes}, expected={expected_primes}")
    if len(seen_primes) != len(set(seen_primes)):
        raise SystemExit("duplicate prime table")
    print("primes=" + ",".join(map(str, seen_primes)))
    print(f"root_components={records}")
    print(f"pi_width_lt_2^-{int(-math.log2(float(pi[1] - pi[0])))}")
    print(f"worst_error_in_u32={float(worst / U32):.12g}")
    print(f"worst_record={worst_record}")
    print("root_component_error_lt_4u32=PASS")


if __name__ == "__main__":
    if len(sys.argv) not in (2, 3):
        raise SystemExit(
            "usage: verify_repeat_phase_roots.py ROOT_TABLE.bin [p1,p2,...]")
    expected = None if len(sys.argv) == 2 else [int(x) for x in sys.argv[2].split(",")]
    main(sys.argv[1], expected)
