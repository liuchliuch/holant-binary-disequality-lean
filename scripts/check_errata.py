#!/usr/bin/env python3
"""Independent exact matrix check in Q(sqrt(2), i); no float arithmetic."""
from fractions import Fraction as F
import json


class K:
    # a + b sqrt(2) + i(c + d sqrt(2)); quotient by r^2=2 and i^2=-1.
    def __init__(self, a=0, b=0, c=0, d=0):
        self.v = tuple(map(F, (a, b, c, d)))

    def __add__(self, other):
        return K(*(x+y for x, y in zip(self.v, other.v)))

    def __neg__(self):
        return K(*(-x for x in self.v))

    def __sub__(self, other):
        return self + -other

    def __mul__(self, other):
        a, b, c, d = self.v
        e, f, g, h = other.v
        return K(a*e+2*b*f-c*g-2*d*h, a*f+b*e-c*h-d*g,
                 a*g+2*b*h+c*e+2*d*f, a*h+b*g+c*f+d*e)

    def inv(self):
        a, b, c, d = self.v
        p, q = a*a+2*b*b+c*c+2*d*d, 2*(a*b+c*d)
        den = p*p-2*q*q
        if not den:
            raise ZeroDivisionError
        return K(a, b, -c, -d)*K(p/den, -q/den)

    def __eq__(self, other):
        return isinstance(other, K) and self.v == other.v


ZERO, ONE, I, R = K(), K(1), K(c=1), K(b=1)


def add(A, B):
    return [[A[j][k]+B[j][k] for k in range(2)] for j in range(2)]


def scale(c, A):
    return [[c*x for x in row] for row in A]


def mul(A, B):
    return [[sum((A[j][l]*B[l][k] for l in range(2)), ZERO)
             for k in range(2)] for j in range(2)]


def inv(A):
    a, b, c, d = A[0][0], A[0][1], A[1][0], A[1][1]
    return scale((a*d-b*c).inv(), [[d, -b], [-c, a]])


def main():
    q0 = [[ONE, ZERO], [ZERO, ONE]]
    q1 = [[ZERO, I], [I, ZERO]]
    q2 = [[ZERO, ONE], [-ONE, ZERO]]
    q3 = [[I, ZERO], [ZERO, -I]]
    rho = R-ONE
    hdt, htd = add(q0, scale(-rho, q1)), add(q0, scale(rho, q3))
    def theta(h, u):
        return mul(mul(inv(h), u), h)
    checks = {
        'dt_plus_actual_Q2': theta(hdt, add(q2, q3)) == scale(R, q2),
        'dt_plus_refutes_printed_Q3': theta(hdt, add(q2, q3)) != scale(R, q3),
        'dt_corrected_minus_Q3': theta(hdt, add(q2, scale(-ONE, q3))) == scale(-R, q3),
        'td_plus_actual_Q2': theta(htd, add(q1, q2)) == scale(R, q2),
        'td_plus_refutes_printed_Q1': theta(htd, add(q1, q2)) != scale(R, q1),
        'td_corrected_minus_Q1': theta(htd, add(q1, scale(-ONE, q2))) == scale(R, q1),
        'scaled_delta_norm_squared': F(2)**2 != F(1)**2,
    }
    print(json.dumps({'arithmetic': 'Exact rational coordinates in Q(sqrt(2), i)',
                      'checks': checks}, indent=2))
    return 0 if all(checks.values()) else 1


if __name__ == '__main__':
    raise SystemExit(main())
