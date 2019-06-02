# -*- coding: utf-8 -*-
# !/usr/bin/env python

"""
Modulo para calcular HIT de una tupla en un modelo
"""
import formulas
from itertools import product
from collections import defaultdict
from misc import indent
from first_order.isomorphisms import Isomorphism


class StepperTupleModelHash():
    """
    Clase de HIT, toma un modelo ambiente y la tupla generadora
    """

    def __init__(self, model, arity, partition=[],alphabet=[], syntax=[], news=[]):
        """
        Calcula HIT de a pasos de una aridad en un modelo.
        Si viene en th una tupla (T,H), se considera que son
        los datos para un hit parcial ya calculado
        """
        self.arity = arity
        self.model = model
        
        if not alphabet:
            alphabet = [[],list(range(arity))]
            syntax = [(None,i) for i in range(arity)]

        self.ops = defaultdict(set)
        for op in model.operations:
            self.ops[model.operations[op].arity].add(model.operations[op])


        self.H = [generator_tuple]
        i = len(generator_tuple)-1
        self.T = defaultdict(set, {a: {j}
                                   for j, a in enumerate(generator_tuple)})
        O = self.H[-1]
    def next_in_language(self,language,element):
        return language[language.index(element) + 1]
    def step(self):
        while O:
            flath = [item for sublist in self.H for item in sublist]
            self.H.append([])
            for ar in sorted(self.ops):
                for f in sorted(self.ops[ar], key=lambda f: f.sym):
                    for tup in product(flath, repeat=ar):
                        if any(t in O for t in tup):
                            i += 1
                            x = f(*tup)
                            self.T[x].add(i)
                            if self.debug:
                                self.V.append(x)
                            if all(x not in h for h in self.H):
                                self.H[-1].append(x)
            O = self.H[-1]
        self.T = {k: frozenset(self.T[k]) for k in self.T}
        self.H.pop(-1)

    def __eq__(self, other):
        return set(self.T.values()) == set(other.T.values()) and self.R == other.R

    def __hash__(self):
        return hash(frozenset(self.T.values()))

    def iso(self, other):
        if self == other:
            flat_h_self = [item for sublist in self.H for item in sublist]
            flat_h_other = [item for sublist in other.H for item in sublist]
            d = {(flat_h_self[i]): flat_h_other[i]
                 for i in range(len(flat_h_self))}
            return Isomorphism(d, self.model.restrict(self.universe()),
                               other.model.restrict(other.universe()), None)
        return None

    def tuple(self):
        return self.generator_tuple

    def universe(self):
        return {item for sublist in self.H for item in sublist}

    def structure(self):
        return self.model.restrict(self.universe())

    def __repr__(self):
        result = "TupleModelHash(\n"
        result += indent("Tuple=%s,\n" % self.generator_tuple)
        result += indent("History=%s,\n" % self.H)
        result += indent("Type=%s,\n" % {k: sorted(self.T[k]) for k in self.T})
        result += indent("Relations=%s,\n" % self.R)
        if self.debug:
            result += indent("V=%s,\n" % self.V)
        result += ")"
        return result


if __name__ == "__main__":
    """
    Para testeo
    """

    from parser.parser import parser
    MODEL = parser("./model_examples/posetrombo.model", preprocess=True)
    # print(MODEL)
    TA = [0, 3]
    TB = [1, 2]
    FA = TupleModelHash(MODEL, TA)
    FB = TupleModelHash(MODEL, TB)
    print(FA)
    print(FB)
    print(FA == FB)
