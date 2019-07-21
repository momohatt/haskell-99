#!/usr/bin/env python
# -*- coding: utf-8 -*-

from __future__ import print_function

# instant calculator using python ast library

import ast
import sys

def walk(node, indent=0):
    print(' ' * indent, end='')
    print(node.__class__, end='')

    # 行数の情報があれば表示する
    if hasattr(node, 'lineno'):
        msg = ': {lineno}'.format(lineno=node.lineno)
        print(msg, end='')

    print()

    for child in ast.iter_child_nodes(node):
        walk(child, indent=indent+4)


def myeval(node, env):
    # print(ast.dump(node))

    if isinstance(node, ast.BinOp):
        children = [myeval(c, env) for c in ast.iter_child_nodes(node)]
        assert(len(children) == 3)
        left = children[0]
        op = children[1]
        right = children[2]

        if isinstance(op, ast.Add):
            return left + right
        if isinstance(op, ast.Mult):
            return left * right
        if isinstance(op, ast.Sub):
            return left - right
        if isinstance(op, ast.Div):
            return left / right
        if isinstance(op, ast.Pow):
            return left ** right

    if isinstance(node, ast.Compare):
        children = [myeval(c, env) for c in ast.iter_child_nodes(node)]
        assert(len(children) == 3)
        left = children[0]
        op = children[1]
        right = children[2]

        if isinstance(op, ast.Eq):
            return left == right
        if isinstance(op, ast.NotEq):
            return left != right
        if isinstance(op, ast.Lt):
            return left < right
        if isinstance(op, ast.Gt):
            return left > right
        if isinstance(op, ast.LtE):
            return left <= right
        if isinstance(op, ast.GtE):
            return left >= right

    if isinstance(node, ast.Num):
        return node.n

    if isinstance(node, ast.Name):
        return [v for (x, v) in env if x == node.id][0]

    return node


def main():
    env = []

    while True:
        print(">>> ", end="", flush=True)
        input_string = sys.stdin.readline()
        if input_string == "":
            print()
            return
        if input_string == "\n":
            continue
        tree = ast.parse(input_string)
        walk(tree)
        assert(isinstance(tree, ast.Module))
        tree = list(ast.iter_child_nodes(tree))[0]

        if isinstance(tree, ast.Expr):
            tree = list(ast.iter_child_nodes(tree))[0]
            print(myeval(tree, env))
            continue

        if isinstance(tree, ast.Assign):
            children = list(ast.iter_child_nodes(tree))
            var = children[0].id
            val = myeval(children[1], env)
            env = [(var, val)] + [(x, v) for (x, v) in env if x != var]
            continue


if __name__ == '__main__':
    main()
