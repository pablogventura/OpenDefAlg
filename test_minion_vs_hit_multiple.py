from parser.parser import parser
from random import sample
import sys
from hit import TupleModelHash
from time import time
from interfaces.minion import is_isomorphic
from colorama import Fore, Style
from itertools import product


def main():
    model = parser(sys.argv[1], verbose=False)
    model.relations = {} # este test es sin relaciones
    
    tuples=[]
    for i in range(100):
        tuples.append(sample(model.universe, 3))
    # estan generadas las tuplas
        
    start_hit = time()
    hits = []
    for t in tuples:
        hits.append(TupleModelHash(model, t))
    return_hits=[]
    for h1,h2 in product(hits,hits):
        return_hits.append(h1==h2)
    time_hit = time() - start_hit
        
    start_minion = time()
    substructures = []
    for t in tuples:
        substructures.append(model.substructure(t).to_relational_model())
    subtype = sorted(model.relations.keys())
    return_minion=[]
    for s1, s2 in product(substructures, substructures):
        return_minion.append(bool(is_isomorphic(s1, s2, subtype)))
    time_minion = time() - start_minion

    return_hits=int("".join(str(int(i)) for i in return_hits), 2)
    return_minion = int("".join(str(int(i)) for i in return_minion), 2)
    
    
    print("*" * 80)
    if time_hit <= time_minion:
        print(Fore.GREEN + "Hit = %s, hit/minion= %s" % (return_hits, time_hit / time_minion) + Style.RESET_ALL)
        print(Fore.RED + "Minion = %s, minion/hit= %s" % (return_minion, time_minion / time_hit) + Style.RESET_ALL)
    else:
        print(Fore.RED + "Hit = %s, hit/minion= %s" % (return_hits, time_hit / time_minion) + Style.RESET_ALL)
        print(Fore.GREEN + "Minion = %s, minion/hit= %s" % (return_minion, time_minion / time_hit) + Style.RESET_ALL)


if __name__ == "__main__":
    main()