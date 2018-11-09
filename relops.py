# -*- coding: utf-8 -*-
#!/usr/bin/env python

from functools import total_ordering

@total_ordering
class Relation(object):
    """
    Relation
    """

    def __init__(self, sym, arity):
        self.sym = sym
        self.arity = arity
        self.r = set()

    def add(self, t):
        self.r.add(t)

    def __repr__(self):
        return repr(self.r)

    def __call__(self, *args):
        return args in self.r

    def __len__(self):
        return len(self.r)

    def __iter__(self):
        return iter(self.r)

    def spectrum(self):
        result = set()
        for t in self:
            result.add(len(set(t)))
        return result

    def restrict(self, subuniverse):
        result = Relation(self.sym, self.arity)
        subuniverse = set(subuniverse)
        for t in self.r:
            if set(t) <= subuniverse:
                result.add(t)
        return result

    def __eq__(self, other):
        return (self.sym,self.r) == (other.sym,other.r)

    def __ne__(self, other):
        return not (self == other)

    def __lt__(self, other):
        return self.arity > other.arity or self.sym < self.sym # TODO no ordena bien los symbolos



class Operation(object):
    """
    Operation
    """

    def __init__(self, sym, arity):
        self.sym = sym
        self.arity = arity
        self.op = dict()

    def add(self, t):
        self.op[t[:-1]] = t[-1]

    def __repr__(self):
        return repr(self.op)

    def __call__(self, *args):
        return self.op[args]

    def __len__(self):
        return len(self.op)

    # def __iter__(self):
    #    return iter(self.r)

    # def spectrum(self):
    #    result = set()
    #    for t in self:
    #        result.add(len(set(t)))
    #    return result

    def restrict(self, subuniverse):
        result = Operation(self.sym, self.arity)
        subuniverse = set(subuniverse)
        for t in self.op:
            if set(t) <= subuniverse:
                result.add(t + (self.op[t],))
        return result
