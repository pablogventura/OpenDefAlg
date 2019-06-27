# -*- coding: utf-8 -*-
# !/usr/bin/env python

"""
Modulo para calcular HIT de una tupla en un modelo
"""
import formulas
from itertools import product, tee
from collections import defaultdict
from parser.parser import parser
from time import time

import sys

class Counterexample(Exception):
    def __init__(self, a,b):
        super(Counterexample, self).__init__("Tuples %s and %s have the same type, but polarities differ" % (a,b))

def product_forced(not_forced_elems,forced_elems, repeat):
    for j in range(repeat):
        for i in product(*([not_forced_elems]*(repeat-(j+1)) + [forced_elems] * (j+1))):
            yield i

class TupleHistory:
    """
    Clase de la tupla con su historia
    Recibe una tupla de indices desde el generador y hace crecer la historia
    """
    def __init__(self,t):
        self.t=t
        self.history = list(t)
        self.has_generated = False # TODO capaz si genero al arrancar
    
    def __eq__(self, other):
        return self.t == other.t and self.history == other.history
    
    def step(self,op,ti):
        """
        Toma la operacion y la tupla de indices
        Devuelve el indice devuelto
        """
        x = op(*[self.history[i] for i in ti]) # resultado de la operacion
        try:
            xi = self.history.index(x) # indice en la historia
            self.has_generated = False
            return xi
        except ValueError:
            self.history.append(x)
            self.has_generated = True
            return len(self.history)-1
    def __hash__(self):
        return hash((self.t,tuple(self.history)))
    def __repr__(self):
        return "TupleHistory(t=%s,h=%s)" % (self.t,self.history)
        
        

class IndicesTupleGenerator:
    """
    Clase de HIT pero de indices, toma un modelo ambiente y la tupla generadora
    """
    def __init__(self, operations,arity, generator, viejos, nuevos, sintactico = []):
        """
        Devuelve tuplas para hacer HIT parcial de indices
        En operaciones estan las operaciones del modelo de la aridad arity
        generator es el generador de tuplas heredado, si se tiene que volver a calcular viene None
        viejos son los elementos viejos
        nuevos son los elementos que se estan generando ahora
        """
        self.sintactico = sintactico
        self.viejos = viejos
        if generator is None:
            self.generator = iter([])
        else:
            self.generator = generator
        self.nuevos = nuevos
        self.arity = arity
        self.ops = sorted(operations, key=lambda f: f.sym)
        
        self.finished = False
        self.forked = False
        
        assert type(self.ops)==list

    def step(self):
        if self.forked:
            raise ValueError("This generator was forked!")
        while not self.finished:
            try:
                f,ti = next(self.generator)
                fsym = formulas.OpSym(f.sym,f.arity)
                term = fsym(*[self.sintactico[i] for i in ti])
                self.sintactico.append(term)
                return (f, ti) # devuelve la operacion y la tupla de indices
            except StopIteration:
                if self.nuevos:
                    self.generator = product(self.ops,product_forced(self.viejos,self.nuevos,self.arity))
                    self.viejos+=self.nuevos
                    self.nuevos=[] # todos se gastaron para hacer el nuevo generador
                    self.finished = False
                else:
                    self.finished = True
    
    def formula_diferenciadora(self, index):
        """Asumo que acaban de diferenciarse"""
        return formulas.eq(self.sintactico[-1],self.sintactico[index])
    
    def hubo_nuevo(self):
        if self.forked:
            raise ValueError("This generator was forked!")
        self.nuevos.append(len(self.viejos)+len(self.nuevos))
    
    def fork(self,quantity):
        if self.forked:
            raise ValueError("This generator was forked!")
        self.forked = True
        result=[]
        generators = tee(self.generator,quantity)
        for i in range(quantity):
            result.append(IndicesTupleGenerator(self.ops,self.arity,generators[i],list(self.viejos),list(self.nuevos),self.sintactico))
        return result
    
    
class Block():
    """
    Clase del bloque que va llevando el mismo hit
    """
    def __init__(self,operations,tuples_in_target,tuples_out_target,target,generator = None, formula=None):
        """
        :param tuples_in_targets: tuplas en el target
        :param tuples_out_targets: tuplas fuera del target
        :param targets: relacion target
        """
        self.target = target
        self.operations = operations
        self.tuples_in_target = tuples_in_target
        self.tuples_out_target = tuples_out_target
        self.arity = target.arity
        if formula is None:
            self.formula = formulas.true()
        else:
            self.formula = formula
        if generator is None:
            self.generator = IndicesTupleGenerator(self.operations,self.arity,None,[],list(range(self.arity)),formulas.variables(*range(self.arity)))
        else:
            self.generator = generator
    
    def finished(self):
        return self.generator.finished
    
    def is_all_in_target(self):
        return len(self.tuples_out_target) == 0
    
    def is_disjunt_to_target(self):
        return len(self.tuples_in_target) == 0
        
    def step(self):
        """
        Hace un paso en hit a todas las tuplas
        Devuelve una lista de nuevos bloques
        """
        result = defaultdict(lambda : ([],[]))
        try:
            op, ti = self.generator.step()
        except TypeError:
            # step devolvio none, asi que ya termino
            assert self.generator.finished
            return [self]
        
        
        for th in self.tuples_in_target:
            result[th.step(op,ti)][0].append(th)
        for th in self.tuples_out_target:
            result[th.step(op,ti)][1].append(th)
        if len(result.keys()) == 1:
            return [self]
        else:
            generators = self.generator.fork(len(result.keys()))
            results = []
            for i,index in enumerate(result.keys()):
                r = result[index]
                if (r[0] and r[0][0].has_generated) or (r[1] and r[1][0].has_generated): # TODO tomo r[0][0] por agarrar la primer th
                    generators[i].hubo_nuevo()
                    f = self.formula & -generators[i].formula_diferenciadora(index) # formula valida
                else:
                    f = self.formula & generators[i].formula_diferenciadora(index)  # formula valida
                for j in range(len(result)):
                    if j == index:
                        continue
                    f = f & -generators[i].formula_diferenciadora(j) # formula no valida
                results.append(Block(self.operations,r[0],r[1],self.target,generators[i],f))
            return results
            

def is_open_def_recursive(block):
    """
    Algoritmo "posta", es recursivo
        un bloque tiene tuplas acompañadas por su historia parcial y un hit parcial que etiqueta al bloque
    input: un bloque mixto
    output:
    """

    if block.finished():
        raise Counterexample(block.tuples_in_target[0].t,block.tuples_out_target[0].t)
        # como es un bloque mixto, no es defel hit parcial esta terminado, no definible y termino
        return False
    if block.is_all_in_target():
        return block.formula
    if block.is_disjunt_to_target():
        return formulas.false()

    blocks = block.step()
    formula = formulas.false()
    for b in blocks:
        recursive_call = is_open_def_recursive(b)
        formula = formula | recursive_call

    return formula

def is_open_def(A,Tgs):
    assert len(Tgs)==1
    assert not A.relations
    T=Tgs[0]
    tuples_in = set(TupleHistory(t) for t in T.r)
    tuples_out = set(TupleHistory(t) for t in product(A.universe,repeat=T.arity)) - tuples_in

    start_block = Block(A.operations.values(),tuples_in,tuples_out,T)
    return is_open_def_recursive(start_block)


def main():
    try:
        model = parser(sys.argv[1], preprocess=False)
    except IndexError:
        model = parser()
    print("*" * 20)
    targets_rels = tuple(model.relations[sym] for sym in model.relations.keys() if sym[0] == "T")
    for t in targets_rels:
        del model.relations[t.sym]
    
    if not targets_rels:
        print("ERROR: NO TARGET RELATIONS FOUND")
        return
    start_hit = time()

    try:
        f = is_open_def(model, targets_rels)
        print("DEFINABLE")
        print("\tT := %s" % f)
    except Counterexample as e:
        print("NOT DEFINABLE")
        print("\tCounterexample: %s" % e)
    time_hit = time() - start_hit
    print("Elapsed time: %s" % time_hit)
    
    
if __name__ == "__main__":
    main()