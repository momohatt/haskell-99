#!/usr/bin/env python
# -*- coding: utf-8 -*-

def fix(f):
    return (lambda x: f(lambda y: (x(x))(y)))(lambda x: f(lambda y: (x(x))(y)))


def fact_body(f, n):
    if n == 0:
        return 1
    return n * f(n - 1)

fact = fix(lambda f: (lambda n: fact_body(f, n)))


if __name__ == '__main__':
    print(fact(4))
