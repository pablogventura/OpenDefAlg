# -*- coding: utf-8 -*-
# !/usr/bin/env python
import sys

from first_order.models import Model
from first_order.relops import Relation, Operation
from parser import preprocessing


class ParserError(Exception):
    """
    Sintax error while parsing
    """
    
    def __init__(self, line, message):
        super(ParserError, self).__init__(("Line %s: " % line) + message)


def c_input(line):
    """
    Clean input
    """
    if "#" in line:
        line = line[:line.find("#")]
    return line.strip()


def parse_universe(line):
    # el universo puede estar hecho de strings, de tuplas,etc
    return [eval(i) for i in line.split()]


def parse_defrel(line):
    sym, ntuples, arity = line.split()
    ntuples, arity = int(ntuples), int(arity)
    return Relation(sym, arity), ntuples


def parse_defop(line):
    sym, arity = line.split()
    arity = int(arity)
    return Operation(sym, arity)


def parse_tuple(line):
    return tuple(map(eval, line.split()))


def parser(path=None, preprocess=True, verbose=True):
    """
    New parser
    """
    if path:
        try:
            f = open(path)
        except:
            raise ParserError(-1, "File missing")
    else:
        f = sys.stdin
    relations = {}
    operations = {}
    current_rel = None
    current_op = None
    rel_missing_tuples = 0
    op_missing_tuples = 0
    universe = None
    for linenumber, line in enumerate(f):
        assert (current_op is None or current_rel is None)
        try:
            line = c_input(line)
            if line:
                if universe is None:
                    # tiene que ser el universo!
                    universe = parse_universe(line)
                elif current_rel is None and current_op is None:
                    if line.count(" ") == 1:
                        # empieza una operacion
                        current_op = parse_defop(line)
                        op_missing_tuples = len(universe) ** current_op.arity
                        if verbose:
                            print("universe %s" % universe)
                            print("%s tuples: %s" %
                                  (current_op.sym, op_missing_tuples))
                    elif line.count(" ") == 2:
                        # empieza una relacion
                        current_rel, rel_missing_tuples = parse_defrel(line)
                        if verbose:
                            try:
                                print("%s density: %f" % (
                                current_rel.sym, float(rel_missing_tuples) / (len(universe) ** current_rel.arity)))
                            except:
                                print("WARNING: no pudo calcular la densidad")
                else:
                    if current_rel is not None:
                        # continua una relacion
                        try:
                            if rel_missing_tuples:
                                current_rel.add(parse_tuple(line))
                                rel_missing_tuples -= 1
                            if not rel_missing_tuples:
                                relations[current_rel.sym] = current_rel
                                current_rel = None
                        except ValueError:
                            print(line)
                            raise
                    elif current_op is not None:
                        # continua una operacion
                        if op_missing_tuples:
                            current_op.add(parse_tuple(line))
                            op_missing_tuples -= 1
                        if not op_missing_tuples:
                            operations[current_op.sym] = current_op
                            current_op = None
        except:
            raise ParserError(linenumber, "")
    if universe is None:
        raise ParserError(linenumber, "Universe not defined")
    if current_rel is not None and not rel_missing_tuples:
        raise ParserError(
            linenumber, "Missing tuples for relation %s" % current_rel.sym)
    if current_op is not None:
        raise ParserError(
            linenumber, "Missing tuples for operation %s" % current_op.sym)
    
    if preprocess:
        prep_relations = set()
        for sym in relations:
            if sym.startswith("T"):
                rel = relations[sym]
                prep_relations = prep_relations.union(preprocessing.preprocesamiento2(rel))
        relations = {sym: relations[sym] for sym in relations if not sym.startswith("T")}
        if verbose:
            print("Target thinning turned T into %s Ts" % len(prep_relations))
        for r in prep_relations:
            relations[r.sym] = r
    
    return Model(universe, relations, operations)


if __name__ == "__main__":
    MODEL = parser()
    # print(MODEL)
