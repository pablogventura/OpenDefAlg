import datetime
import sys
from random import sample, choice
from itertools import product, permutations


def generador(tA, t, c, fs, fc, tarity,density):
    # tA es el tamaño de la estructura ambiente
    # t es la cantidad de subconjuntos
    # c es el tamaño de esos subconjuntos
    # fs es una lista de aridades de funciones
    # fc es una lista de booleanos para hacer a la funcion hiperconmutativa
    result = '# Generated {0:%Y-%m-%d %H:%M:%S}\n'.format(datetime.datetime.now())
    result += '# Parameters: |A| = %s, |MaxSubs| = %s, |ms| = %s with ms in MaxSubs, Arities = %s\n' % (
        tA, t, c, fs)

    # result += "# Random Seed: %s\n" % seed
    universe = set(range(tA))
    result += " ".join(str(e) for e in universe) + "\n"
    # TODO no hay que agregar al universo ambiente como subuniverso maximal?
    maxSubuniverses = [set(universe)]
    for i in range(t):
        maxSubuniverses.append(set(sample(universe, c)))
    # print(maxSubuniverses)
    # para calcular f(a,b) tomo los conjuntos que tengan a "a" y b y hago la interseccion y de ese conjunto elijo uno al azar
    # quiza conviene que f se pueda hacer conmutativa para tener una forma barata de generar mas rapdido y tener funciones que son mas rigidas
    # aca arriba se corre hit secuencial contra hit p
    for i, arity in enumerate(fs):
        result += "f%s %s\n" % (i, arity)
        if fc[i]:
            # debe ser conmutativa
            ff = set()
            for values in product(universe, repeat=arity):
                sets = [m for m in maxSubuniverses if set(values).issubset(m)]
                intersection = sets.pop()
                while sets:
                    intersection = intersection & sets.pop()
                fvalues = choice(list(intersection))
                for tup in permutations(values):
                    if tup not in ff:
                        result += " ".join(str(e) for e in tup) + " %s\n" % fvalues
                        ff.add(tup)
        else:
            for values in product(universe, repeat=arity):
                sets = [m for m in maxSubuniverses if set(values).issubset(m)]
                intersection = sets.pop()
                while sets:
                    intersection = intersection & sets.pop()
                fvalues = choice(list(intersection))
                result += " ".join(str(e) for e in values) + " %s\n" % fvalues
    result += "T0 %s %s\n" % (int((tA**tarity)*density), tarity)
    for i in sample(list(product(universe, repeat=tarity)),int((tA**tarity)*density)):
        result += " ".join(map(str, i))
        result += "\n"
    return result


def permutador(lista, permutacion):
    result = dict()
    for i, j in enumerate(permutacion):
        result[j] = lista[i]
    return tuple(result[i] for i in range(len(lista)))


def main():
    try:
        tA, t, c, fs, fc, tarity = sys.argv[1:7]
        try:
            density = float(sys.argv[7])
        except:
            density = 1
        tA = int(tA)
        t = int(t)
        c = int(c)
        fs = [int(i) for i in eval(fs)]
        assert all(i >= 0 for i in fs)
        fc = eval(fc)
        assert all(i is False or i is True for i in fc)
        tarity = int(tarity)
    except:
        raise
        print("""tA es el tamaño de la estructura ambiente
            t es la cantidad de subconjuntos
            c es el tamaño de esos subconjuntos
            fs es una lista de aridades de funciones
            fc es una lista de booleanos para hacer a la funcion hiperconmutativa""")
        sys.exit(1)
    print(generador(tA, t, c, fs, fc, tarity,density))


if __name__ == "__main__":
    main()
