# A lot of code
# very messy
# without any documentation
# and the logic of research draft notes
# At least I'm being honest...

from sage.misc.cachefunc import cached_function
from sage.matrix.constructor import Matrix
from sage.combinat.ordered_tree import LabelledOrderedTree
from sage.combinat.ordered_tree import LabelledOrderedTrees
from sage.geometry.polyhedron.all import Polyhedron
from sage.misc.misc_c import prod
from sage.rings.integer_ring import *
from sage.combinat.posets.lattices import LatticePoset
from sage.combinat.posets.posets import Poset
from sage.functions.other import sqrt
from sage.plot.line import line2d
from sage.plot.plot3d.shapes2 import line3d
from sage.combinat.combination import Combinations
from sage.misc.misc import subsets



### Useful documented function to use the messy ones

def sWeakOrderLattice(s):
    """
    Return the s-weak order lattice on decreasing trees

    INPUT:
        - s, the weak composition
    """
    return LatticePoset(sWeakOrderLatticeTrees(s))


def realization2d(s):
    """
    Shows the 2d realization of the s-Permutahedron
    INPUT :

        - s, the weak composition of length 3
    """
    assert len(s) == 3
    pols = proj3VerticesTree(s)
    plotPols(pols, axes=False, aspect_ratio = 1)

def realization2dSTam(s):
    """
    Shows the 2d realization of the s-Associahderon
    INPUT :

        - s, the weak composition of length 3
    """
    assert len(s) == 3
    pols = vtamari_pols_edges(s)
    return plotPols(proj3Pols(pols), axes=False, aspect_ratio = 1)

def realization2dBoth(s):
    """
    Shows the 2d realization of the s-Permutahedron and s-Associahedron together
    INPUT :

        - s, the weak composition of length 3
    """
    assert len(s) == 3
    pols1 = proj3VerticesTree(s, color='blue')
    pols2 = proj3Pols(vtamari_pols_edges(s), color='red')
    return plotPols(pols1+pols2, axes=False, aspect_ratio=1)

def realization3d(s):
    """
    Shows the 3d realization of the s-Permutahedron
    INPUT :

        - s, the weak composition of length 4
    """
    assert len(s) == 4
    pols = proj4VerticesTree(s)
    return plotPols(pols, viewer = "threejs", frame = False)

def realization3dSTam(s):
    """
    Shows the 2d realization of the s-Associahderon
    INPUT :

        - s, the weak composition of length 4
    """
    assert len(s) == 4
    pols = vtamari_pols_edges(s)
    return plotPols(proj4Pols(pols), viewer = "threejs", frame = False)

def realization3dBoth(s):
    """
    Shows the 2d realization of the s-Permutahedron and s-Associahedron together
    INPUT :

        - s, the weak composition of length 3
    """
    assert len(s) == 4
    pols1 = proj4VerticesTree(s, color='blue')
    pols2 = proj4Pols(vtamari_pols_edges(s), color='red')
    return plotPols(pols1+pols2, viewer = "threejs", frame = False)

############


class LatticePrinter():

    def __init__(self, s):
        self._s = s
        self._lattice = sWeakOrderLatticeTrees(s)
        # self._scale = .15
        self._scale = .2

    def _latex_(self):
        SCALE = self._scale
        st = "\\begin{tikzpicture}[every node/.style={inner sep = -.5pt}]\n"
        matrix = proj3Matrix()
        ids = {}
        i = 0
        for t in self._lattice:
            ids[t] = i
            p = get_tree_point(t)
            pp = Matrix(p) * matrix
            pp = [v.n() for v in pp[0]]
            st+= "\\node(tree" + str(i) + ") at (" + str(pp[0]) + "," + str(pp[1]) + ") {\\scalebox{" + str(SCALE) +"}{$\n"
            st+= self._object_printer(t)
            st+="\n$}};\n"
            i+=1
        st+="\n"
        for t1,t2 in self._lattice.cover_relations():
            st+="\draw (tree" + str(ids[t1]) +") -- (tree" + str(ids[t2]) + ");\n"
        st+="\\end{tikzpicture}"
        return st

    def _object_printer(self, t):
        return latex(t).replace("[auto]","[every node/.style={inner sep = 3pt}]")

class TamLatticePrinter(LatticePrinter):

    def __init__(self, s):
        #self._scale = .15
        self._scale = .2
        self._s = s
        self._lattice = getSCatalanLattice(s)

class NutreeLatticePrinter(TamLatticePrinter):

    def __init__(self, s):
        TamLatticePrinter.__init__(self,s)
        self._scale = .1

    def _object_printer(self, t):
        return latex(STreeToNuTree(t))

def getSPermutations(s):
    if len(s) == 0:
        yield tuple()
        return
    for p in getSPermutations(s[1:]):
        np = [l+1 for l in p]
        ones = [1 for i in range(s[0])]
        if len(ones)==0:
            ones = [1]
        for i in range(len(np)+1):
            if i >= len(np) or s[np[i]-1] != 0:
                yield tuple(np[:i] + ones + np[i:])

def getSDecreasingTrees(s):
    for sperm in getSPermutations(s):
        yield getSDecreasingTree(sperm, s)

def getSDecreasingTrees2(s, subset = None):
    def children(v, subset):
        if v == 1:
            for t in getSDecreasingTrees2(s, subset):
                yield [t]
        else:
            for ss in subsets(subset):
                for l in children(v-1, [w for w in subset if not w in ss]):
                    for t in getSDecreasingTrees2(s, ss):
                        yield l + [t]
    if subset is None:
        subset = [i for i in range(1, len(s)+1)]
    if len(subset) == 0:
        yield leaf()
    else:
        m = max(subset)
        subset = [w for w in subset if w!= m]
        for c in children(s[m-1]+1, subset):
            yield LabelledOrderedTree(c, label = m)



def getSFaceTrees(s):
    for t in getSDecreasingTrees(s):
        for sub in subsets(list(treeAscents(t))):
            yield get_face_tree(s, t, sub)

def getSTamFaceTrees(s):
    for t in getSCatalanTrees(s):
        for sub in subsets(list(treeAscentsTam(t))):
            yield get_face_tree(s,t,sub)

#~ def getSFaceTrees2(s, subset = None, axila = False):
    #~ def children(v, subset, axila):
        #~ if v == 1:
            #~ for t in getSFaceTrees2(s, subset, axila):
                #~ yield [t]
        #~ else:
            #~ for ss in subsets(subset):
                #~ for l in children(v-1, [w for w in subset if not w in ss], not axila):
                    #~ for t in getSFaceTrees2(s, ss, axila):
                        #~ yield l + [t]
    #~ if subset is None:
        #~ subset = [i for i in range(1, len(s)+1)]
    #~ if len(subset) == 0:
        #~ yield leaf()
    #~ else:
        #~ m = max(subset)
        #~ subset = [w for w in subset if w!= m]
        #~ v = s[m-1]
        #~ if v == 0:
            #~ for t in getSFaceTrees2(s, subset, axila):
                #~ yield LabelledOrderedTree([t], label = m)
        #~ else:
            #~ if axila:
                #~ for c in children(2*v-1, subset, True):
                    #~ l = leaf()
                    #~ yield LabelledOrderedTree([l] + c + [l], label = m)
            #~ else:
                #~ for c in children(2*v+1, subset, False):
                    #~ yield LabelledOrderedTree(c, label = m)

# tested
# 022
# 032
# 002
# 0001
# 0201
#~ def testGetSFaceTrees2(s):
    #~ L1 = list(getSFaceTrees(s))
    #~ L2 = list(getSFaceTrees2(s))
    #~ return len(L1) == len(L2) and set(L1) == set(L2)

def is_catalan_perm(sperm):
    perm = Word(sperm).standard_permutation()
    return perm.avoids([1,3,2])

def is_catalan_tree(tree):
    inv = tree_inversions_dict(tree)
    n = tree.label()
    for a in range(1,n):
        for b in range(a+1,n):
            for c in range(b+1,n+1):
                if inv.get((c,a),0) > inv.get((c,b),0):
                    return False
    return True

def leaf():
    return LabelledOrderedTree([], label=" ")

def getSDecreasingTree(sperm, s = None, zeros = None):
    if len(sperm) == 0:
        return leaf()
    if zeros is None:
        zeros = getZeros(s)
    v,children = decomp(sperm)
    if v in zeros:
        return LabelledOrderedTree([getSDecreasingTree(sum(children,[]), zeros = zeros)], label = v)
    else:
        return LabelledOrderedTree([getSDecreasingTree(c, zeros = zeros) for c in children], label = v)

def getSFromTree(tree):
    n = tree.label()
    s = [0 for i in range(n)]
    def sTraversal(tree):
        if len(tree) == 0:
            return
        s[tree.label() -1] = len(tree) - 1
        for child in tree:
            sTraversal(child)
    sTraversal(tree)
    return tuple(s)

def permFromTreeGenerator(tree):
    if len(tree) == 0:
        return
    if len(tree) == 1:
        yield tree.label()
    first = True
    for c in tree:
        if not first:
            yield tree.label()
        else:
            first = False
        for v in permFromTreeGenerator(c):
            yield v

def getSPerm(tree):
    return tuple(permFromTreeGenerator(tree))


def getInitialTree(s):
    n = len(s)
    if n == 0:
        return leaf()
    v = s[-1]
    C = [leaf() for i in range(v+1)]
    C[0] = getInitialTree(s[:-1])
    return LabelledOrderedTree(C, label = n)

def getMaximalTree(s):
    n = len(s)
    if n == 0:
        return leaf()
    v = s[-1]
    C = [leaf() for i in range(v+1)]
    C[-1] = getMaximalTree(s[:-1])
    return LabelledOrderedTree(C, label = n)

def getInitialSPerm(s):
    T = getInitialTree(s)
    return getSPerm(T)

def getMaximalSPerm(s):
    T = getMaximalTree(s)
    return getSPerm(T)

def getSCatalanPermutations(s):
    for p in getSPermutations(s):
        if is_catalan_perm(p):
            yield p

def getSCatalanTrees(s):
    for t in getSDecreasingTrees(s):
        if is_catalan_tree(t):
            yield t

def getSCatalanLattice(s):
    L = list(getSCatalanTrees(s))
    return Poset([L, sweak_lequal])

def cardinalitySDecreasingTrees(s):
    return prod(sum(s[i] for i in range(len(s)-1,j,-1))+1 for j in range(len(s)-2,-1,-1))

def getSCatalanCardinality(s):
    n = len(s)
    M = Matrix([[ZZ(binomial(sum(s[k] for k in range(j,n))+1, j-i +1)) for j in range(1,n)] for i in range(1,n)])
    return M.determinant()

# tested
# 111
# 1111
# 11111
# 222
# 2222
# 22222
# 333
# 3333
# 12121
# 001
# 0001
# 00001
# 002
# 0002
# 00002
# 010
# 01010
# 01011
# 01021
def testSCatalanCardinality(s):
    return getSCatalanCardinality(s) == len(list(getSCatalanPermutations(s)))

# tested
# 111
# 1111
# 11111
# 222
# 2222
# 22222
# 333
# 3333
# 12121
# 001
# 0001
# 00001
# 002
# 0002
# 00002
# 010
# 01010
# 01011
# 01021
def testSCatalanCardinalityTrees(s):
    return getSCatalanCardinality(s) == len(list(getSCatalanTrees(s)))

# tested
# 111
# 1111
# 11111
# 222
# 2222
# 22222
# 333
# 3333
# 12121
# 001
# 0001
# 00001
# 002
# 0002
# 00002
# 010
# 01010
# 01011
# 01021
def testCatalanIsomorphy(s):
    P1 = nu_tamari_poset(tuple(reversed(s)))
    P2 = getSCatalanLattice(s)
    return P1.is_isomorphic(P2)


# tested
# 101
# 222
# 232
# 1001
# 10101
# 11001
# 1100102
# 1100202
def testCardinalityGenerator(s):
    return cardinalitySDecreasingTrees(s) == len(list(getSPermutations(s)))

def getZeros(s):
    if s is None:
        return set()
    else:
        return {i+1 for i in range(len(s)) if s[i]==0}

def ascents(sperm, s = None):
    zeros = getZeros(s)
    for i in range(len(sperm)-1):
        if sperm[i] in zeros:
            for j in range(i+1,len(sperm)):
                if sperm[j] > sperm[i]:
                    yield (i,j)
                    break
        elif sperm[i] < sperm[i+1]:
            yield i,i+1

def hasStrictRightChild(tree):
    return len(tree) > 1 and len(tree[-1]) > 0

def hasStrictLeftChild(tree):
    return len(tree) > 1 and len(tree[0]) > 0

def hasRightChild(tree):
    return len(tree) > 0 and len(tree[-1]) > 0

def hasLeftChild(tree):
    return len(tree) > 0 and len(tree[0]) > 0

def rightExtractions(tree):
    if not hasStrictRightChild(tree):
        T1 = tree[0]
        T2 = tree.clone()
        T2[0] = leaf()
        T2.set_immutable()
        yield T1,T2
    if hasRightChild(tree):
        for t,T2 in rightExtractions(tree[-1]):
            T1 = tree.clone()
            T1[-1] = t
            T1.set_immutable()
            yield T1,T2

def leftExtractions(tree):
    if not hasStrictLeftChild(tree):
        T1 = tree[-1]
        T2 = tree.clone()
        T2[-1] = leaf()
        T2.set_immutable()
        yield T1,T2
    if hasLeftChild(tree):
        for t,T2 in leftExtractions(tree[0]):
            T1 = tree.clone()
            T1[0] = t
            T1.set_immutable()
            yield T1,T2

def leftInsertion(tree, inserted):
    if len(tree) == 0:
        return inserted
    if tree.label() > inserted.label():
        left = leftInsertion(tree[0],inserted)
        tree = tree.clone()
        tree[0] = left
        tree.set_immutable()
        return tree
    else:
        inserted = inserted.clone()
        inserted[-1] = tree
        inserted.set_immutable()
        return inserted

def rightInsertion(tree, inserted):
    if len(tree) == 0:
        return inserted
    if tree.label() > inserted.label():
        right = rightInsertion(tree[-1],inserted)
        tree = tree.clone()
        tree[-1] = right
        tree.set_immutable()
        return tree
    else:
        inserted = inserted.clone()
        inserted[0] = tree
        inserted.set_immutable()
        return inserted


def sweak_tree_succ(tree):
    for i in range(len(tree)-1):
        child0 = tree[i]
        child1 = tree[i+1]
        if len(child0) > 0:
            for T1, T2 in rightExtractions(child0):
                S = tree.clone()
                S[i] = T1
                S[i+1] = leftInsertion(child1,T2)
                S.set_immutable()
                yield S
    for i,child in enumerate(tree):
        for Schild in sweak_tree_succ(child):
            S = tree.clone()
            S[i] = Schild
            S.set_immutable()
            yield S

def sweak_tree_add_ascent(tree, ab):
    a,b = ab
    s = getSFromTree(tree)
    d = tree_inversions_dict(tree)
    d[(b,a)] = d.get((b,a),0) + 1
    d = transitive_closure(s,d)
    return tree_from_inversions(s,d)

def tree_moves_right(tree,a):
    n = tree.label()
    d = tree_inversions_dict(tree)
    s = getSFromTree(tree)
    possibles = [b for b in range(1,n+1) if b != a and a in sub_tree_set(tree,b) and d.get((b,a),0) < s[b-1]]
    if len(possibles) > 0:
        b = min(possibles)
        d[(b,a)] = d.get((b,a),0) + 1
        d = transitive_closure(s,d)
        return tree_from_inversions(s,d)
    return None

def tree_moves_left(tree,a):
    n = tree.label()
    d = tree_inversions_dict(tree)
    s = getSFromTree(tree)
    possibles = [b for b in range(1,n+1) if b != a and a in sub_tree_set(tree,b) and d.get((b,a),0) > 0]
    if len(possibles) > 0:
        b = min(possibles)
        for aa in sub_tree_set(tree,a):
            if d.get((a,aa)) != s[a-1]:
                d[(b,aa)] -= 1
        return tree_from_inversions(s,d)
    return None

def sweak_tree_remove_descent(tree,ba):
    b,a = ba
    for t in sweak_tree_prev(tree):
        A = set(treeAscents(t))
        if (a,b) in A and sweak_tree_add_ascent(t,(a,b)) == tree:
            return t

def sweak_tree_prev(tree):
    for i in range(len(tree)-1,0,-1):
        child0 = tree[i]
        child1 = tree[i-1]
        if len(child0) > 0:
            for T1, T2 in leftExtractions(child0):
                S = tree.clone()
                S[i] = T1
                S[i-1] = rightInsertion(child1,T2)
                S.set_immutable()
                yield S
    for i,child in enumerate(tree):
        for Schild in sweak_tree_prev(child):
            S = tree.clone()
            S[i] = Schild
            S.set_immutable()
            yield S

def rightExtremals(tree):
    if len(tree) > 0:
        if not hasStrictRightChild(tree):
            yield tree.label()
        if hasRightChild(tree):
            for v in rightExtremals(tree[-1]):
                yield v

def leftExtremals(tree):
    if len(tree) > 0:
        if not hasStrictLeftChild(tree):
            yield tree.label()
        if hasLeftChild(tree):
            for v in leftExtremals(tree[0]):
                yield v


def treeDirectAscents(tree):
    for i in range(len(tree)-1):
        for v in rightExtremals(tree[i]):
            yield v, tree.label()


def treeDirectDescents(tree):
    for i in range(len(tree)-1,0,-1):
        for v in leftExtremals(tree[i]):
            yield tree.label(), v


def treeAscents(tree):
    for vv in treeDirectAscents(tree):
        yield vv
    for child in tree:
        for vv in treeAscents(child):
            yield vv

def treeAscentsTam(tree):
    for i in range(len(tree)-1):
        c = tree[i]
        if len(c) > 0:
            yield c.label(), tree.label()
    for child in tree:
        for vv in treeAscentsTam(child):
            yield vv

# checked
# 002
# 003
# 011
# 022
# 033
# 0001
# 0002
# 0003
# 0103
# 0113
# 0223
# 0333
# 02233
def checkTreeAscentsTam(s):
    L = getSCatalanLattice(s)
    for tree in L:
        if not len(L.upper_covers(tree)) == len(list(treeAscentsTam(tree))):
            return False
    return True

def isTreeAscentCondi(s, inversions, asc):
    a,c = asc
    for d in range(c+1,len(s)+1):
        if inversions.get((d,c), 0) != inversions.get((d,a), 0):
            return False
    return True

def isTreeAscentCondii(s, inversions, asc):
    a,c = asc
    if inversions.get((c,a),0) == s[c-1]:
        return False
    return True

def isTreeAscentCondiii(s, inversions, asc):
    x,z = asc
    for y in range(x+1,z):
        if inversions.get((z,y),0) == inversions.get((z,x),0) and inversions.get((y,x),0) < s[y-1]:
            return False
    return True

def isTreeAscentCondiv(s, inversions, asc):
    x,z = asc
    if s[x-1] > 0:
        for w in range(1,x):
            if inversions.get((x,w),0) == s[x-1] and inversions.get((z,w),0) <= inversions.get((z,x),0):
                return False
    return True


def isTreeAscent(s, inversions, asc):
    x,z = asc
    return isTreeAscentCondi(s,inversions, asc) and isTreeAscentCondii(s, inversions, asc) and isTreeAscentCondiii(s, inversions, asc) and isTreeAscentCondiv(s, inversions, asc)


def treeAscentsFromInv(s, inversions):
    n = len(s)
    for x in range(1,n):
        for z in range(x+1,n+1):
            if isTreeAscent(s,inversions,(x,z)):
                yield (x,z)

def nbtreeAscentsInversions(s, inversions):
    return len(list(treeAscentsInversions(tree)))

# does not work !
def findTreeAscent(s, inversions1, inversions2):
    for c in range(len(s), 0, -1):
        for a in range(c-1, 0, -1):
            if inversions1.get((c,a),0) != inversions2.get((c,a),0):
                return (a,c)

def test_findTreeAscent(s):
    invs = [tree_inversions_dict(t) for t in getSDecreasingTrees(s)]
    for inv1 in invs:
        for inv2 in invs:
            if inv1 != inv2 and sweak_lequal_inversions(inv1, inv2):
                asc = findTreeAscent(s, inv1, inv2)
                print(inv1, inv2, asc)
                if not isTreeAscent(s, inv1, asc):
                    print(inv1, inv2, asc)
                    return False
    return True

def test_condi_nonempty(s, inversions1, inversions2):
    for c in range(len(s), 0, -1):
        for a in range(c-1, 0, -1):
            if inversions1.get((c,a),0) != inversions2.get((c,a),0):
                return isTreeAscentCondi(s,inversions1,(a,c))

def test_condi_condiii_nonempty(s, inversions1, inversions2):
    min_length = len(s)
    min_couple = None
    for (c,a) in inversions2:
        if inversions1.get((c,a),0) < inversions2[(c,a)]:
            if isTreeAscentCondi(s,inversions1,(a,c)):
                if c - a < min_length:
                    min_couple = (a,c)
                    min_length = c - a
    return isTreeAscentCondiii(s,inversions1,min_couple)

def test_condi_condiii_condiv_nonempty(s, inversions1, inversions2):
    max_length = 0
    max_couple = None
    for (c,a) in inversions2:
        if inversions1.get((c,a),0) < inversions2[(c,a)]:
            if isTreeAscentCondi(s,inversions1,(a,c)) and isTreeAscentCondiii(s,inversions1,(a,c)):
                if c - a > max_length:
                    max_couple = (a,c)
                    max_length = c - a
    return isTreeAscentCondiv(s,inversions1,max_couple)

# tested
# 111
# 222
# 233
# 203
# 2222
# 22222
# 22322
# 22302
def test_minmax_ascentconditions(s):
    invs = [tree_inversions_dict(t) for t in getSDecreasingTrees(s)]
    for inv1 in invs:
        for inv2 in invs:
            if inv1 != inv2 and sweak_lequal_inversions(inv1, inv2):
                if not test_condi_nonempty(s, inv1, inv2):
                    print("Cond i", inv1, inv2)
                    return False
                if not test_condi_condiii_nonempty(s, inv1, inv2):
                    print("Cond iii", inv1, inv2)
                    return False
                if not test_condi_condiii_condiv_nonempty(s, inv1, inv2):
                    print("Cond iv", inv1, inv2)
                    return False

    return True

# tested
# 11
# 111
# 101
# 222
# 1111
# 2222
# 2202
# 2022
def test_treeAscentsFromInv(s):
    for t in getSDecreasingTrees(s):
        inversions = tree_inversions_dict(t)
        S1 = set(treeAscents(t))
        S2 = set(treeAscentsFromInv(s,inversions))
        if S1 != S2:
            print(t)
            return False
    return True

def treeDescents(tree):
    for vv in treeDirectDescents(tree):
        yield vv
    for child in tree:
        for vv in treeDescents(child):
            yield vv


def descents(sperm, s= None):
    zeros = getZeros(s)
    for i in range(len(sperm)-1):
        if not sperm[i] in zeros:
            for j in range(i+1,len(sperm)):
                if sperm[j] >= sperm[i]:
                    break
                yield i,j
                if not sperm[j] in zeros:
                    break

def nbascent(sperm, s = None):
    return len(list(ascents(sperm,s)))

def nbtreeAscents(tree):
    return len(list(treeAscents(tree)))

def sweak_succ(sperm,s = None):
    fpos = {}
    asc = {i:j for i,j in ascents(sperm,s)}
    zeros = getZeros(s)
    for i in range(len(sperm)-1):
        v = sperm[i]
        if not fpos.has_key(v):
            fpos[v] = i
        if i in asc:
            a,b = fpos[v],asc[i]
            while b+1 < len(sperm) and sperm[b+1] > v and sperm[b+1] in zeros:
                b+=1
            yield sperm[:a] + sperm[i+1:b+1] + sperm[a:i+1] + sperm[b+1:]

def sweak_prev(sperm,s = None):
    fpos = {}
    desc = {j:i for i,j in descents(sperm,s)}
    zeros = getZeros(s)
    for j in range(len(sperm)-1,0,-1):
        v = sperm[j]
        if not fpos.has_key(v):
            fpos[v] = j
        if j in desc:
            a,b = fpos[v],desc[j]
            if v in zeros:
                while b > 0 and sperm[b-1] < v:
                    b-=1
            yield sperm[:b] + sperm[j:a+1] + sperm[b:j] + sperm[a+1:]

# 001
# 002
# 112
# 122
# 1222
# 1333
# 1033
# 1303
# 1003
def checkSWeakSuccGenerates(s):
    seed = getInitialSPerm(s)
    F = RecursivelyEnumeratedSet([seed], lambda x: sweak_succ(x,s))
    return set(F) == set(getSPermutations(s))

# 001
# 002
# 112
# 122
# 1222
# 1333
# 1033
# 1303
# 1003
def checkSWeakTreeSuccGenerates(s):
    seed = getInitialTree(s)
    F = RecursivelyEnumeratedSet([seed], sweak_tree_succ)
    return set(F) == set(getSDecreasingTrees(s))

# 001
# 002
# 112
# 122
# 1222
# 1333
# 1033
# 1303
# 1003
def checkSWeakPrevGenerates(s):
    seed = getMaximalSPerm(s)
    F = RecursivelyEnumeratedSet([seed], lambda x: sweak_prev(x,s))
    return set(F) == set(getSPermutations(s))

# 001
# 002
# 112
# 122
# 1222
# 1333
# 1033
# 1303
# 1003
def checkSWeakTreePrevGenerates(s):
    seed = getMaximalTree(s)
    F = RecursivelyEnumeratedSet([seed], sweak_tree_prev)
    return set(F) == set(getSDecreasingTrees(s))



def sWeakOrderLatticePerms(s):
    L = list(getSPermutations(s))
    return Poset([L, [(p1,p2) for p1 in L for p2 in sweak_succ(p1,s)]])

def sWeakOrderLatticeTrees(s):
    L = list(getSDecreasingTrees(s))
    return Poset([L, [(p1,p2) for p1 in L for p2 in sweak_tree_succ(p1)]])

def meetIrreducible(s):
    for t in getSDecreasingTrees(s):
        inv = tree_inversions_dict(t)
        if len(list(treeAscentsFromInv(s,inv)))==1:
            yield t

# n=3 -> 4*m
# n = 4 -> 11*m
# n = 5 -> 26*m
def nbIrreducibles(s):
    return len(list(meetIrreducible(s)))

# tested
# 001
# 0101
# 0101001
# 0102002
# 0100201
def checkIsLattice(s):
    L = sWeakOrderLatticePerms(s)
    return L.is_lattice()

# 001
# 0101
# 0222
def checkSameLattice(s):
    L1 = sWeakOrderLatticePerms(s)
    L2 = sWeakOrderLatticeTrees(s)
    return L1.is_isomorphic(L2)

# checked
# 111
# 122
# 133
# 101
# 102
# 103
# 1111
# 2222
# 2022
# 2202
# 2302
# 2312
# 2013
def checkSemiDistributive(s):
    L = sWeakOrderLatticeTrees(s)
    LL = LatticePoset(L)
    return LL.is_semidistributive()

def tree_inversions(tree):
    counts = {}
    def inversions_rec(tree):
        if len(tree) == 0:
            return
        b = tree.label()
        for c in counts:
            if c > b:
                yield (c,b),counts[c]
        for r in inversions_rec(tree[0]):
            yield r
        for i in range(1,len(tree)):
            counts[b] = counts.get(b,0) +1
            for r in inversions_rec(tree[i]):
                yield r
    for r in inversions_rec(tree):
        yield r

def tree_inversions_dict(tree):
    return {inv:c for inv,c in tree_inversions(tree)}

def tree_from_inversions(s, inversions, subset = None):
    if subset is None:
        n = len(s)
        subset = {i for i in range(1,n+1)}
    if len(subset) == 0:
        return leaf()
    c = max(subset)
    subsets = [set() for i in range(s[c-1]+1)]
    subset.remove(c)
    for a in subset:
        i = inversions.get((c,a),0)
        subsets[i].add(a)
    return LabelledOrderedTree([tree_from_inversions(s,inversions,Ci) for Ci in subsets], label = c)

def face_tree_from_inversions(s, inversions, subset = None):
    tree_invs = {}
    ascents = []
    for b,a in inversions:
        if not inversions[(b,a)] in NN:
            ascents.append((a,b))
            i = int(inversions[(b,a)])
            if i != 0:
                tree_invs[(b,a)] = i
        else:
            tree_invs[(b,a)] = inversions[(b,a)]
    return SWeakFace(tree_from_inversions(s,tree_invs), ascents)

def face_tree_inversions(ftree):
    return ftree.inversions()

COLSEP = .1

class SWeakFace():

    def __init__(self, t, ascents):
        self._t = t
        self._ascents = tuple(ascents)
        self._marked = {i for (i,j) in self._ascents}
        invs = tree_inversions_dict(t)
        max_invs = dict(invs)
        s = getSFromTree(t)
        self._s = s
        for a,b in ascents:
            invs[(b,a)] = invs.get((b,a),0) + ZZ(1)/ZZ(2)
            max_invs[(b,a)] = max_invs.get((b,a),0) + 1
        self._invs = transitive_closure(s, invs)
        self._max_invs = transitive_closure(s, max_invs)
        self._maxt = tree_from_inversions(s,self._max_invs)

    def s(self):
        return self._s

    def tree(self):
        return self._t

    def ascents(self):
        return self._ascents

    def inversions(self):
        return self._invs

    def varies(self,b,a):
        v = self._invs.get((b,a),0)
        return int(v) < v

    def variation_path(self, b,a):
        s = self.s()
        chain = [b]
        if (a,b) in self.ascents():
            chain.append(a)
            return chain
        vba = int(self.inversion(b,a))
        for bi in range(b-1,a,-1):
            v = int(self.inversion(b,bi))
            if v == vba and s[bi-1] > 0 and (bi,b) in self.ascents():
                chain.append(bi)
                vbia = int(self.inversion(bi,a))
                if vbia < s[bi-1] and (vbia > 0 or (a,bi) in self.ascents()):
                    chain.append(a)
                    return chain
                b = bi
                vba = 0
        return None

    def is_variation_path(self,p):
        s = self.s()
        b = p[0]
        a = p[-1]
        if self.tree_inversion(p[0],p[1]) != self.tree_inversion(b,a):
            return False
        for i in range(1,len(p)-2):
            if self.tree_inversion(p[i],p[i+1]) != 0 or (p[i+1],p[i]) not in self.ascents():
                return False
        if len(p) > 2:
            if not self.tree_inversion(p[-2],p[-1]) < s[p[-2]-1]:
                return False
            if self.tree_inversion(p[-2],p[-1]) == 0 and not (p[-1],p[-2]) in self.ascents():
                return False
        return True

    def inversion(self,b,a):
        return self._invs.get((b,a),0)

    def tree_inversion(self,b,a):
        return int(self._invs.get((b,a),0))

    def dimension(self):
        return len(self._ascents)

    def __repr__(self):
        return str((self._t, self._ascents))

    def _get_ascents_letters(self):
        self._n=0
        def r(t):
            if t.label() in self._marked:
                yield "".join((chr(ord(x) + 49) for x in str(self._n)))
            self._n+=1
            for c in t:
                for l in r(c):
                    yield l
        for l in r(self._t):
            yield l

    def __eq__(self, other):
        return isinstance(other, SWeakFace) and other.ascents() == self.ascents() and other.tree() == self.tree()

    def __hash__(self):
        return hash((self.ascents(), self.tree()))

    def _latex_(self):
        L = self._t._latex_()
        L = L.replace("column sep=.3cm","column sep="+str(COLSEP)+"cm")
        L = L.replace("[draw,circle]","[draw,circle,fill=white]")
        for l in self._get_ascents_letters():
            rfrom = "\\node" + l +"}{\\node[draw,circle,fill=white]"
            rto = "\\node" + l +"}{\\node[draw,circle,fill=red!50]"
            L = L.replace(rfrom, rto)
        return L

    def is_border_face(self):
        if len(self.tree()[-1]) >0:
            return True
        def unmarked_left(t):
            if len(t) == 0:
                return False
            if not t.label() in self._marked:
                return True
            return unmarked_left(t[0])
        return unmarked_left(self.tree()[0])

    def get_min_tree(self):
        return self._t

    def get_max_tree(self):
        return self._maxt

    def tree_intervals(self):
        t = self.get_min_tree()
        maxt = self.get_max_tree()
        L = [t]
        seen = set()
        while len(L) > 0:
            tt = L.pop()
            if not tt in seen:
                seen.add(tt)
                yield tt
                for v in sweak_tree_succ(tt):
                    if sweak_lequal(v,maxt):
                        L.append(v)

    def includes(self, other):
        n = len(self._s)
        for a in range(1,n+1):
            for b in range(a+1,n+1):
                i,j = other._invs.get((b,a),0), self._invs.get((b,a),0)
                if int(j) == j and i != j:
                    return False
                if not (i >= j - ZZ(1)/ZZ(2) and i <= j + ZZ(1)/ZZ(2)):
                    return False
        return True

    def sub_faces(self):
        for t in self.tree_intervals():
            A = list(treeAscents(t))
            for subs in subsets(A):
                F = SWeakFace(t,subs)
                if self.includes(F):
                    yield F

    def sub_facets(self):
        d = self.dimension() - 1
        for t in self.tree_intervals():
            A = list(treeAscents(t))
            if len(A) >= d:
                for subs in subsets(A):
                    if len(subs) == d:
                        F = SWeakFace(t,subs)
                        if self.includes(F):
                            yield F

    def sub_face_to_set_partition(self, f):
        def subset_compare(s1,s2):
            if s1 == s2:
                return 0
            if any(f._invs.get((b,a),0) > self._invs.get((b,a),0) for a in s1 for b in s2 if b > a):
                return 1
            return -1
        n = len(self._s)
        d = {i:{i} for i in range(1,n+1)}
        for i,j in f.ascents():
            d[i].update(d[j])
            for k in d[i]:
                d[k] = d[i]
        V = [d[i] for i in d if i == max(d[i])]
        L = []
        for v in V:
            L.append(v)
            k = len(L) - 1
            j = k - 1
            while j>=0 and subset_compare(L[j],v) == 1:
                L[j+1] = L[j]
                j-=1
            L[j+1] = v
        return OrderedSetPartition(L)

    def intersection(self, f):
        s = self._s
        t1 = self.get_min_tree()
        t2 = f.get_min_tree()
        t1_max = self.get_max_tree()
        inv1_max = tree_inversions_dict(t1_max)
        t2_max = f.get_max_tree()
        inv2_max = tree_inversions_dict(t2_max)
        tjoin = join_trees(s,t1,t2)
        if sweak_lequal(tjoin, t1_max) and sweak_lequal(tjoin, t2_max):
            B = []
            for (a,b) in treeAscents(tjoin):
                inv = tree_inversions_dict(tjoin)
                inv[(b,a)] = inv.get((b,a),0) + 1
                inv = transitive_closure(s,inv)
                if sweak_lequal_inversions(inv, inv1_max) and sweak_lequal_inversions(inv, inv2_max):
                    B.append((a,b))
            return SWeakFace(tjoin, B)
        else:
            return None


    def get_tree_set_partition(self, t, i):

        n = self.dimension() + 1
        T = self._t
        s = self._s
        dT = tree_inversions_dict(T)
        dt = tree_inversions_dict(t)
        dTmax = tree_inversions_dict(self.get_max_tree())
        possible_moves = {j for j in range(i+1,n+1) if dTmax.get((j,i),0) != dT.get((j,i),0)}
        moves = {j for j in possible_moves if dt.get((j,i),0) != dT.get((j,i),0)}
        parents = [j for j in possible_moves if i in sub_tree_set(t,j)]
        parent = min(parents)

        if not parent in moves:
            A = sub_tree_set(t,i).intersection(sub_tree_set(T,i))
            if dt.get((parent,i),0) == 0:
                t0 = tree_moves_left(t,i)
                if t0 != None and self.includes(SWeakFace(t0,[])):
                    moved_parents = [p for p in parents if any(dt.get((j,p),0) != dT.get((j,p),0) for j in range(p+1,n+1))]
                    moved_parent = min(moved_parents)
                    unmoved_parents = [p for p in parents if all(dt.get((j,p),0) == dT.get((j,p),0) for j in range(p+1,n+1))]
                    unmoved_parent = min(unmoved_parents)
                    A.update(j for j in sub_tree_set(t,unmoved_parent).intersection(sub_tree_set(T,unmoved_parent)) if j not in sub_tree_set(t,moved_parent).intersection(sub_tree_set(T,moved_parent)))
            B = {j for j in range(1,n+1) if not j in A}
        else:
            B = sub_tree_set(t,i).intersection(sub_tree_set(T,i))
            if dt.get((parent,i),0) == s[parent-1]:
                t0 = tree_moves_right(t,i)
                if t0 != None and self.includes(SWeakFace(t0,[])):
                    unmoved_parents = [p for p in parents if all(dt.get((j,p),0) == dT.get((j,p),0) for j in range(p+1,n+1))]
                    unmoved_parent = min(unmoved_parents)
                    B.update(j for j in range(1,n+1) if j not in sub_tree_set(t,unmoved_parent).intersection(sub_tree_set(T,unmoved_parent)))
            A = {j for j in range(1,n+1) if not j in B}
        return OrderedSetPartition([A,B])
        # ~ dTmax = tree_inversions_dict(self.get_max_tree())
        # ~ possible_moves = {j for j in range(i+1,n+1) if dTmax.get((j,i),0) != dT.get((j,i),0)}
        # ~ moves = {j for j in possible_moves if dt.get((j,i),0) != dT.get((j,i),0)}
        # ~ print(moves)
        # ~ print(possible_moves)

        # ~ if len(moves) == 0 or len(moves) == len(possible_moves):
            # ~ A = {ii for ii in range(1,i+1) if all(dt.get((j,ii),0) == dt.get((j,i),0) and dT.get((j,ii),0) == dT.get((j,i),0) for j in range(i+1, n+1))}
            # ~ B = {j for j in range(1,n+1) if not j in A}
            # ~ if len(moves) == 0:
                # ~ return OrderedSetPartition([A,B])
            # ~ else:
                # ~ return OrderedSetPartition([B,A])




    def f_vector(self):
        v = [0] * (self.dimension()+2)
        v[0] = 1
        for f in self.sub_faces():
            d = f.dimension()+1
            v[d]+=1
        return tuple(v)

    def generalized_permutohedron(self):
        ieqs = []
        n = len(self._s)
        for f in self.sub_facets():
            sp = self.sub_face_to_set_partition(f)
            A = sp[0]
            ieq = [0]*(n+1)
            ieq[0] = -len(A)*(len(A) +1)/2
            for i in A:
                ieq[i] = 1
            ieqs.append(ieq)
        eq = [1]*(n+1)
        eq[0] = -n*(n+1)/2
        return Polyhedron(ieqs = ieqs, eqns = [eq])

    def get_vertex(self,t):
        n = len(self._s)
        eqns = []
        for i in range(1,n):
            sp = self.get_tree_set_partition(t,i)
            A = sp[0]
            ieq = [0]*(n+1)
            ieq[0] = -len(A)*(len(A) +1)/2
            for i in A:
                ieq[i] = 1
            eqns.append(ieq)
        eq = [1]*(n+1)
        eq[0] = -n*(n+1)/2
        eqns.append(eq)
        return Polyhedron(eqns = eqns)

    def get_tree_facet_ordered_sets(self,t):
        f = SWeakFace(t,[])
        for ff in self.sub_facets():
            if ff.includes(f):
                yield self.sub_face_to_set_partition(ff)

    def variations(self):
        n = len(self._s)
        return set((b,a) for a in range(1,n) for b in range(a+1,n+1) if self.varies(b,a))

    def get_maximal_variations(self):
        s = self._s
        n = len(s)
        t1 = self.get_min_tree()
        t2 = self.get_max_tree()
        inv1 = tree_inversions_dict(t1)
        inv2 = tree_inversions_dict(t2)
        var = set()
        # get the variation
        for a in range(1,n):
            for b in range(a+1,n+1):
                v1 = inv1.get((b,a),0)
                v2 = inv2.get((b,a),0)
                if v2 - v1 == 1:
                    var.add((b,a))
        # get maximal variations
        maxvar = set()
        for c in range(2,n+1):
            for a in range(c-1,0,-1):
                if (c,a) in var:
                    ca = inv1.get((c,a),0)
                    for b in range(a+1,c):
                        if (c,b) in maxvar:
                            ba = inv1.get((b,a),0)
                            cb = inv1.get((c,b),0)
                            if ca == cb and ba > 0 and ba < s[b-1]:
                                break
                    else:
                        maxvar.add((c,a))
        return maxvar

    def right_variations(self):
        S = set()
        for c,b in self.get_maximal_variations():
            for a in range(1,b):
                ba = self.tree_inversion(b,a)
                if self.varies(b,a) and ba > 0 and ba < self._s[b-1]:
                    S.add((c,a))
        return S


def get_max_cells(s):
    n = len(s)
    for t in getSDecreasingTrees(s):
        A = list(treeAscents(t))
        if len(A) == n-1:
            yield SWeakFace(t,A)

def get_faces(s):
    for t in getSDecreasingTrees(s):
        A = list(treeAscents(t))
        for subs in subsets(A):
            yield SWeakFace(t,subs)

def test_gp_vertices(f):
    T = list(f.tree_intervals())
    P = f.generalized_permutohedron()
    return len(T) == P.n_vertices()


# tested
# 111, 222, 333, 303
# 1111, 2222, 3333, 3104
# 22222
# 0011
# failed :
# 00111
# 00011
# 00012
# 00112
# 00122 failed
# 00133 failed
# 001133 failed
def test_all_gp_vertices(s):
    for f in get_max_cells(s):
        if not test_gp_vertices(f):
            print(f)
            return f
    return True

# tested
# 111, 222, 333, 303
# 1111, 2222, 3333, 3104
# 22222, 01413
# 012123
def test_all_gp_f_vectors(s):
    for f in get_max_cells(s):
        if not f.f_vector() != f.generalized_permutohedron().f_vector():
            return f
    return True

# tested
# 111, 222, 333, 303
# 1111, 2222, 3333, 3104
# 22222, 01413
def test_all_gp_simple(s):
    for f in get_max_cells(s):
        if not f.generalized_permutohedron().is_simple():
            return f
    return True

def test_tree_set_partitions(F,t):
    return set(F.get_tree_facet_ordered_sets(t)) == set(F.get_tree_set_partition(t,i) for i in range(1,F.dimension()+1))

# tested on
"""
sage: s = (0,1,2,2,1,1,2,1,3,3)
sage: d = {}
sage: d[(10,9)] = 1
sage: d[(10,8)] = 1
sage: d[(10,4)] = 1
sage: d[(10,1)] = 1
sage: d[(10,5)] = 2
sage: d[(9,4)] = 2
sage: d[(9,1)] = 2
sage: d[(7,3)] = 1
sage: d[(7,2)] = 1
sage: d[(4,1)] = 1
sage: t = tree_from_inversions(s,d)
sage: F = SWeakFace(t, [(1,4),(2,3),(3,7),(4,9),(5,10),(6,7),(7,10),(8,9),(9,10)])
"""
# f vector (1, 2178, 9801, 19008, 20790, 14082, 6099, 1680, 282, 26, 1)
def test_all_tree_set_partitions(F):
    i =0
    facets = {f:F.sub_face_to_set_partition(f) for f in F.sub_facets()}
    for t in F.tree_intervals():
        try:
            ft = SWeakFace(t,[])
            S1 = set(facets[f] for f in facets if f.includes(ft))
            S2 = set(F.get_tree_set_partition(t,i) for i in range(1,F.dimension()+1))
            if S1 != S2:
                return t
            i+=1
            print(i)
        except:
            print("error")
            return t
    return True

def test_face_intersection(f1,f2):
    f = f1.intersection(f2)
    S1 = {t for t in f1.tree_intervals() if f2.includes(SWeakFace(t,[]))}
    if f is None:
        S2 = set()
    else:
        S2 = set(f.tree_intervals())
    return S1 == S2

# tested
# 111 222
# 1111 2222
def test_all_face_intersections(s):
    F = list(get_faces(s))
    for f1 in F:
        for f2 in F:
            if not test_face_intersection(f1,f2):
                return f1,f2
    return True

# tested
# 1111, 2222,
def test_all_max_face_intersections(s):
    F = list(get_max_cells(s))
    for f1 in F:
        for f2 in F:
            if not test_face_intersection(f1,f2):
                return f1,f2
    return True

def tree_parent(t, i):
    n = t.label()
    d = tree_inversions_dict(t)
    p1 = None
    p2 = n
    A = set(range(i,n))
    while p2 != i:
        A = {j for j in A if d.get((p2,j),0) == d.get((p2,i),0)}
        p1 = p2
        p2 = max(A)
        A.remove(p2)
    return p1

def sub_tree_set(t,j):
    n = t.label()
    d = tree_inversions_dict(t)
    return {i for i in range(1,j+1) if all(d.get((k,j),0) == d.get((k,i),0) for k in range(j+1,n+1))}

def get_face_tree(s, tree, ascents):
    return SWeakFace(tree, ascents)


## FALSE
def meet_ascent_lemma(t1,t2):
    def transitive_link(S,a,b):
        if (a,b) in S:
            return True
        for x,y in S:
            if x == a and y < b and transitive_link(S,y,b):
                return True
        return False
    s = getSFromTree(t1)
    n = t1.label()
    dt1 = tree_inversions_dict(t1)
    dt2 = tree_inversions_dict(t2)
    A1 = set(treeAscents(t1))
    A2 = set(treeAscents(t2))
    t = meet_trees(s,t1,t2)
    A = set(treeAscents(t))
    for a in range(1,n):
        for b in range(a+1,n+1):
            if dt1.get((b,a),0) == dt2.get((b,a),0):
                if transitive_link(A1,a,b) and transitive_link(A2, a,b):
                    if not transitive_link(A,a,b):
                        print((a,b))
                        return False
    return True

## FALSE
def intersection_ascent_lemma_false(f1,f2):
    def transitive_link(S,a,b):
        if (a,b) in S:
            return True
        for x,y in S:
            if x == a and y < b and transitive_link(S,y,b):
                return True
        return False
    fi = f1.intersection(f2)
    if fi is None:
        return True
    t1 = f1.get_min_tree()
    t2 = f2.get_min_tree()
    ti = fi.get_min_tree()
    dt1 = tree_inversions_dict(t1)
    dt2 = tree_inversions_dict(t2)
    A1 = set(f1.ascents())
    A2 = set(f2.ascents())
    Ai = set(fi.ascents())
    s = f1.s()
    n = len(s)
    for a in range(1,n):
        for b in range(a+1,n+1):
            if dt1.get((b,a),0) == dt2.get((b,a),0):
                if transitive_link(A1,a,b) and transitive_link(A2, a,b):
                    if not transitive_link(Ai,a,b):
                        print((a,b))
                        return False
                if transitive_link(Ai,a,b):
                    if not transitive_link(A1,a,b) or not transitive_link(A2,a,b):
                        print((a,b))
                        return False
    return True

## FALSE
def join_descendant_lemma(t1,t2):
    n = t1.label()
    s = getSFromTree(t1)
    t = join_trees(s,t1,t2)
    for b in range(2,n+1):
        D1 = sub_tree_set(t1,b)
        D2 = sub_tree_set(t2,b)
        Dt = sub_tree_set(t,b)
        if not all(a in Dt for a in D1.intersection(D2)):
            print(b)
            print([a for a in D1.intersection(D2) if not a in Dt])
            return False
    return True

def test_all_join_descendant_lemma(s):
    T = list(getSDecreasingTrees(s))
    for t1 in T:
        for t2 in T:
            if not join_descendant_lemma(t1,t2):
                return (t1,t2)
    return True

# True
def join_weak_descendant_lemma(t1,t2):
    n = t1.label()
    s = getSFromTree(t1)
    t = join_trees(s,t1,t2)
    dt1 = tree_inversions_dict(t1)
    dt2 = tree_inversions_dict(t2)
    dt = tree_inversions_dict(t)
    for b in range(2,n):
        for a in range(b):
            if all(dt1.get((d,b),0) == dt1.get((d,a),0) and dt2.get((d,b),0) == dt2.get((d,a),0) for d in range(b+1,n+1)):
            #if all(dt1.get((d,b),0) == dt1.get((d,a),0) for d in range(b+1,n+1)) or all(dt2.get((d,b),0) == dt2.get((d,a),0) for d in range(b+1,n+1)):
                if not all(dt.get((d,a),0) >= dt.get((d,b),0) for d in range(b+1,n+1)):
                    return False
    return True

# tested
# 111 222
# 1111 2222
def test_all_join_weak_descendant_lemma(s):
    T = list(getSDecreasingTrees(s))
    for t1 in T:
        for t2 in T:
            if not join_weak_descendant_lemma(t1,t2):
                return (t1,t2)
    return True

# true
def intersection_ascent_lemma(f1,f2):
    fi = f1.intersection(f2)
    if fi is None:
        return True
    s = f1.s()
    n = len(s)
    I = set()
    for b in range(2,n+1):
        for a in range(1,b):
            if f1.varies(b,a) and f2.varies(b,a) and f1.inversion(b,a) == f2.inversion(b,a):
                I.add((b,a))
    Imin = {(b,a) for (b,a) in I if all(aa <= a for (bb,aa) in I if bb == b)}
    return all((a,b) in fi.ascents() for (b,a) in Imin)

# tested
# 111 222
# 1111 2222
def test_intersection_ascent_lemma(s):
    F = list(get_faces(s))
    for f1 in F:
        for f2 in F:
            if not intersection_ascent_lemma(f1,f2):
                return f1,f2
    return True

# true
def intersection_stability_lemma(f1,f2):
    fi = f1.intersection(f2)
    if fi is None:
        return True
    s = f1.s()
    n = len(s)
    for b in range(2,n+1):
        for a in range(1,b):
            if f1.varies(b,a) and f2.varies(b,a) and f1.inversion(b,a) == f2.inversion(b,a):
                if not int(fi.inversion(b,a)) == int(f1.inversion(b,a)):
                    return False
    return True

# tested
# 111 222 333
# 1111 2222
def test_intersection_stability_lemma(s):
    F = list(get_faces(s))
    for f1 in F:
        for f2 in F:
            if not intersection_stability_lemma(f1,f2):
                return f1,f2
    return True

def variation_chain(f,b,a):
    s = f.s()
    if (a,b) in f.ascents():
        return True
    for aa in range(a+1,b):
        v = int(f.inversion(aa,a))
        if (a,aa) in f.ascents() and v == 0:
            if variation_chain(f,b,aa):
                return True
    return False
def should_vary(f,b,a):
    s = f.s()
    if variation_chain(f,b,a):
        return True
    for aa in range(a+1,b):
        v = int(f.inversion(aa,a))
        if v > 0 and v < s[aa-1]:
            if variation_chain(f,b,aa):
                return True
    return False

# true
def ascent_variation_lemma(f):
    n = len(f.s())
    for a in range(1,n):
        for b in range(a+1,n+1):
            t1, t2 = f.varies(b,a), should_vary(f,b,a)
            if t1 != t2:
                #print(b,a)
                #print(t1,t2)
                return False
    return True

def ascent_variation_lemma2(f):
    n = len(f.s())
    for a in range(1,n):
        for b in range(a+1,n+1):
            t1 = f.varies(b,a)
            t2 = f.variation_path(b,a) is not None
            if t1 != t2:
                #print(b,a)
                #print(t1,t2)
                return False
    return True

# tested
# 011 022 033
# 0111 02222 0333 0303 0033
# 03033 01113
def test_all_ascent_variation_lemma(s):
    for f in get_faces(s):
        if not ascent_variation_lemma(f):
            return f
    return True

# tested
# 011 022 033
# 0111 02222 0333 0303 0033
# 03033 01113
def test_all_ascent_variation_lemma2(s):
    for f in get_faces(s):
        if not ascent_variation_lemma2(f):
            return f
    return True

# true
def double_ascent_lemma(f):
    n = len(f.s())
    for a in range(1,n):
        b = None
        for c in range(a+1,n):
            if f.varies(c,a):
                if b is None:
                    b = c
                else:
                    if not f.varies(c,b):
                        return False
    return True

# tested
# 011 022 033
# 0111 0222 0333 0303
# 01323
def test_all_double_ascent_lemma(s):
    for f in get_faces(s):
        if not ascent_variation_lemma(f):
            return f
    return True

def middle_variation_lemma(f):
    n = len(f.s())
    s = f.s()
    for a in range(1,n):
        for c in range(a+1,n):
            if f.varies(c,a):
                for b in range(a,c):
                    v1 = int(f.inversion(c,b))
                    v2 = int(f.inversion(c,a))
                    v3 = int(f.inversion(b,a))
                    if v1 == v2 and not f.varies(c,b) and not v3 == s[b-1]:
                        return False
    return True

# tested
# 011 022 033
# 0111 0222 0333 0303
# 01323
def test_all_middle_variation_lemma(s):
    for f in get_faces(s):
        if not middle_variation_lemma(f):
            return f
    return True

#true
def right_variation_lemma(f):
    n = len(f.s())
    s = f.s()
    for b in range(1,n):
        for c in range(b+1,n):
            if f.varies(c,b):
                for a in range(1,b):
                    vcb = int(f.inversion(c,b))
                    vca = int(f.inversion(c,a))
                    vba = int(f.inversion(b,a))
                    if vcb == vca and vba == s[b-1] and f.varies(c,b) and not f.varies(c,a):
                        return False
    return True

# tested
# 011 022 033
# 0111 0222 0333 0303
# 01323
def test_all_right_variation_lemma(s):
    for f in get_faces(s):
        if not right_variation_lemma(f):
            return f
    return True

# FALSE (0, 1, 1, 2)
# def path_intersection_lemma(f1,f2):
    # fi = f1.intersection(f2)
    # if fi is None:
        # return True
    # n = len(f1.s())
    # for a in range(1,n):
        # for b in range(a+1,n+1):
            # if f1.inversion(b,a) == f2.inversion(b,a) and f1.varies(b,a):
                # p1 = f1.variation_path(b,a)
                # p2 = f2.variation_path(b,a)
                # if not all(x in p2 for x in p1) and not all(x in p1 for x in p2):
                    # return False
    # return True

def path_intersection_lemma(f1,f2):
    fi = f1.intersection(f2)
    if fi is None:
        return True
    n = len(f1.s())
    for a in range(1,n):
        for b in range(a+1,n+1):
            if f1.inversion(b,a) == f2.inversion(b,a) and f1.varies(b,a):
                p1 = f1.variation_path(b,a)
                p2 = f2.variation_path(b,a)
                p3 = tuple(x for x in p1 if x in p2)
                if not fi.is_variation_path(p3):
                    return False
    return True

# tested
# FALSE (0, 1, 1, 2)
# def test_all_path_intersection_lemma(s):
    # F = list(get_faces(s))
    # for f1 in F:
        # for f2 in F:
            # if not path_intersection_lemma(f1,f2):
                # return f1,f2
    # return True

# tested 0112, 0111, 0222 01112
def test_all_path_intersection_lemma(s):
    F = list(get_faces(s))
    for f1 in F:
        for f2 in F:
            if not path_intersection_lemma(f1,f2):
                return f1,f2
    return True

def get_variations(t1,t2):
    s = getSFromTree(t1)
    n = len(s)
    inv1 = tree_inversions_dict(t1)
    inv2 = tree_inversions_dict(t2)
    var = set()
    # get the variation
    for a in range(1,n):
        for b in range(a+1,n+1):
            v1 = inv1.get((b,a),0)
            v2 = inv2.get((b,a),0)
            if v2 - v1 >= 1:
                var.add((b,a))
    return var

def get_maximal_variations(t1,t2):
    s = getSFromTree(t1)
    n = len(s)
    inv1 = tree_inversions_dict(t1)
    inv2 = tree_inversions_dict(t2)
    var = set()
    # get the variation
    for a in range(1,n):
        for b in range(a+1,n+1):
            v1 = inv1.get((b,a),0)
            v2 = inv2.get((b,a),0)
            if v2 - v1 >= 1:
                var.add((b,a))
    # get maximal variations
    maxvar = set()
    for c in range(2,n+1):
        for a in range(c-1,0,-1):
            if (c,a) in var:
                ca = inv1.get((c,a),0)
                for b in range(a+1,c):
                    if (c,b) in maxvar:
                        ba = inv1.get((b,a),0)
                        cb = inv1.get((c,b),0)
                        if ca == cb and ba > 0 and ba < s[b-1]:
                            break
                else:
                    maxvar.add((c,a))
    return maxvar


def is_plusone_interval(t1,t2):
    s = getSFromTree(t1)
    n = len(s)
    inv1 = tree_inversions_dict(t1)
    inv2 = tree_inversions_dict(t2)
    # get the variation
    for a in range(1,n):
        for b in range(a+1,n+1):
            v1 = inv1.get((b,a),0)
            v2 = inv2.get((b,a),0)
            if v1 > v2 or v2 - v1 > 1:
                return False
    return True

# tested on bigexamples
def is_pure_interval(t1,t2):
    if not is_plusone_interval(t1,t2):
        return False
    inv1 = tree_inversions_dict(t1)
    s = getSFromTree(t1)
    var = get_maximal_variations(t1,t2)
    n = t1.label()
    for a in range(1,n):
        for b in range(a+1,n):
            for c in range(b+1,n+1):
                if (c,a) in var and (b,a) in var and not (c,b) in var:
                    return False
                if (c,a) in var and (c,b) in var and inv1.get((c,a),0) == inv1.get((c,b),0) and s[b-1] != 0 and not (b,a) in var:
                    return False
    return True


def pure_intervals(s):
    T = list(getSDecreasingTrees(s))
    for t1 in T:
        for t2 in T:
            if is_pure_interval(t1,t2):
                yield (t1,t2)

def is_extreme_descendant(t,b,a):
    inv = tree_inversions_dict(t)
    s = getSFromTree(t)
    n = t.label()
    if a > b:
        return False
    v = inv.get((b,a),0)
    if v != 0 and v != s[b-1]:
        return False
    for c in range(b+1,n+1):
        if inv.get((c,b),0) != inv.get((c,a),0):
            return False
    return True


# tested
# 111 1111 11111
# 222 2222 22222
# 333 3333
def test_pure_intervals_card(s):
    L1 = list(pure_intervals(s))
    L2 = list(get_faces(s))
    return len(L1) == len(L2)

# tested
# 111 1111 11111
# 222 2222
# 333
# 0113 0123
# 001 0103
def test_pure_intervals(s):
    L1 = set(pure_intervals(s))
    L2 = set((F.get_min_tree(), F.get_max_tree()) for F in get_faces(s))
    return L1 == L2

# tested on bigexamples
def ascents_from_variations(F):
    S = F.get_maximal_variations()
    d = {}
    for b,a in S:
        if a in d:
            d[a] = min(d[a],b)
        else:
            d[a] = b
    return set(d.items()) == set(F.ascents())

# not true
# def variations_from_ascents(F):
    # d = {(b,a):1 for a,b in F.ascents()}
    # d = transitive_closure(F._s,d)
    # return d

def variations_from_ascents(F):
    var = {(b,a) for a,b in F.ascents()}
    n = len(F.s())
    changed = True
    while changed:
        changed = False
        for c in range(3,n+1):
            for b in range(2,c):
                if (c,b) in var:
                    for a in range(1,b):
                        if (b,a) in var and F.tree_inversion(b,a) == 0 and (c,a) not in var:
                            changed = True
                            var.add((c,a))
    return var == F.get_maximal_variations()

# NOT TRUE
# def test_intersect_essential_variations_pure(s):
    # L = list(get_faces(s))
    # for f1 in L:
        # for f2 in L:
            # f3 = f1.intersection(f2)
            # s1 = f1.get_maximal_variations()
            # s2 = f2.get_maximal_variations()
            # s3 = s1.intersection(s2)
            # ss3 = set() if f3 is None else f3.get_maximal_variations()
            # if not s3 == ss3:
                # return f1,f2
    # return True

# tested
# 111 1111
# NOT TRUE 222
def test_intersect_essential_variations_pure(s):
    L = list(get_faces(s))
    for f1 in L:
        for f2 in L:
            f3 = f1.intersection(f2)
            if f3 is not None:
                s1 = f1.get_maximal_variations()
                s2 = f2.get_maximal_variations()
                s3 = set((b,a) for (b,a) in s1 if (b,a) in s2 and f1.inversion(b,a) == f2.inversion(b,a))
                if not s3 == f3.get_maximal_variations():
                    return f1,f2
    return True

# tested
# 111 1111
# 222 2222
# 002 0102
def test_weak_intersect_essential_variations_pure(s):
    L = list(get_faces(s))
    for f1 in L:
        for f2 in L:
            f3 = f1.intersection(f2)
            if f3 is not None:
                s1 = f1.get_maximal_variations()
                s2 = f2.get_maximal_variations()
                s3 = set((b,a) for (b,a) in s1 if (b,a) in s2 and f1.inversion(b,a) == f2.inversion(b,a))
                if not s3.issubset(f3.get_maximal_variations()):
                    return f1,f2
    return True

# not working
def test_intersect_essential_right_variations_pure(s):
    L = list(get_faces(s))
    for f1 in L:
        for f2 in L:
            f3 = f1.intersection(f2)
            if f3 is not None:
                s1 = f1.get_maximal_variations().union(f1.right_variations())
                s2 = f2.get_maximal_variations().union(f2.right_variations())
                s3 = set((b,a) for (b,a) in s1 if (b,a) in s2 and f1.inversion(b,a) == f2.inversion(b,a))
                if not s3 == f3.get_maximal_variations().union(f3.right_variations()):
                    return f1,f2
    return True

# tested 111 1111
# 222 2222
# 0102
def test_intersect_variations(s):
    L = list(get_faces(s))
    for f1 in L:
        for f2 in L:
            f3 = f1.intersection(f2)
            if f3 is not None:
                s1 = f1.variations()
                s2 = f2.variations()
                s3 = set((b,a) for (b,a) in s1 if (b,a) in s2 and f1.inversion(b,a) == f2.inversion(b,a))
                if not s3 == f3.variations():
                    return f1,f2
    return True

# tested
# 111 1111
# 222 2222 22222
# 0102
def test_caba_variations_pure(s):
    n = len(s)
    for f in get_faces(s):
        for a in range(1,n):
            for c in range(a+1,n+1):
                if f.varies(c,a):
                    for b in range(a+1,c):
                        if f.varies(b,a) and not f.varies(c,b):
                            return f
    return True

# not true
def test_caba_variations_all(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if sweak_lequal(t1,t2):
                var = get_variations(t1,t2)
                for a in range(1,n):
                    for c in range(a+1,n+1):
                        if (c,a) in var:
                            for b in range(a+1,c):
                                if (b,a) in var and not (c,b) in var:
                                    return t1,t2
    return True

# not true
def test_caba_variations_plusone(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_plusone_interval(t1,t2):
                var = get_variations(t1,t2)
                for a in range(1,n):
                    for c in range(a+1,n+1):
                        if (c,a) in var:
                            for b in range(a+1,c):
                                if (b,a) in var and not (c,b) in var:
                                    return t1,t2
    return True

# tested
# 111 1111
# 222 2222
# 333 3333
# 0102
def test_cbba_variations_plusone(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_plusone_interval(t1,t2):
                inv1 = tree_inversions_dict(t1)
                inv2 = tree_inversions_dict(t2)
                for c in range(3,n+1):
                    for b in range(2,c):
                        if inv2.get((c,b),0) > inv1.get((c,b),0):
                            for a in range(1,b):
                                if inv1.get((b,a),0) == 0:
                                    if inv2.get((b,a),0) > 0 and inv2.get((c,a),0) == inv1.get((c,a),0):
                                        return t1,t2
    return True

# tested
# 111 1111
# 222 2222
# 333 3333
# 0102
def test_cbba_variations_all(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if sweak_lequal(t1,t2):
                inv1 = tree_inversions_dict(t1)
                inv2 = tree_inversions_dict(t2)
                for c in range(3,n+1):
                    for b in range(2,c):
                        if inv2.get((c,b),0) > inv1.get((c,b),0):
                            for a in range(1,b):
                                if inv1.get((b,a),0) == 0:
                                    if inv2.get((b,a),0) > 0 and inv2.get((c,a),0) == inv1.get((c,a),0):
                                        return t1,t2
    return True

# not true 2222
def test_cbba_essential_variations_plusone(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_plusone_interval(t1,t2):
                inv1 = tree_inversions_dict(t1)
                #inv2 = tree_inversions_dict(t2)
                var = get_maximal_variations(t1,t2)
                for c in range(3,n+1):
                    for b in range(2,c):
                        if (c,b) in var:
                            for a in range(1,b):
                                if inv1.get((b,a),0) == 0:
                                    if (b,a) in var and not (c,a) in var:
                                        return t1,t2
    return True

# tested
# 111 1111
# 222 2222
# 333 3333
# 0102
def test_cbba_essential_variations_pure(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_pure_interval(t1,t2):
                inv1 = tree_inversions_dict(t1)
                #inv2 = tree_inversions_dict(t2)
                var = get_maximal_variations(t1,t2)
                for c in range(3,n+1):
                    for b in range(2,c):
                        if (c,b) in var:
                            for a in range(1,b):
                                if inv1.get((b,a),0) == 0:
                                    if (b,a) in var and not (c,a) in var:
                                        return t1,t2
    return True


# not true 2222
def test_cbba_essential_variations_all(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if sweak_lequal(t1,t2):
                inv1 = tree_inversions_dict(t1)
                #inv2 = tree_inversions_dict(t2)
                var = get_maximal_variations(t1,t2)
                for c in range(3,n+1):
                    for b in range(2,c):
                        if (c,b) in var:
                            for a in range(1,b):
                                if inv1.get((b,a),0) == 0:
                                    if (b,a) in var and not (c,a) in var:
                                        return t1,t2
    return True

# tested
# 111 1111
# 222 2222
# 333 3333
# 0203
def test_essential_variation_intermediate_pure(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_pure_interval(t1,t2):
                var = get_variations(t1,t2)
                evar = get_maximal_variations(t1,t2)
                for c,a in evar:
                    for b in range(a+1,c):
                        if (b,a) in var and not (b,a) in evar:
                            return t1,t2
    return True

# not true 2222
# (4[3[2[ [], 1[ [],  [],  []],  []],  [],  []],  [],  []],
# 4[3[ [], 2[ [],  [],  []],  []], 1[ [],  [],  []],  []])
def test_essential_variation_intermediate_all(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if sweak_lequal(t1,t2):
                var = get_variations(t1,t2)
                evar = get_maximal_variations(t1,t2)
                for c,a in evar:
                    for b in range(a+1,c):
                        if (b,a) in var and not (b,a) in evar:
                            return t1,t2
    return True

# not true
# (4[3[ [], 2[ [], 1[ [],  [],  []],  []],  []],  [],  []],
#  4[3[ [],  [], 2[ [],  [],  []]], 1[ [],  [],  []],  []])
def test_essential_variation_intermediate_plusone(s):
    T = list(getSDecreasingTrees(s))
    n = len(s)
    for t1 in T:
        for t2 in T:
            if is_plusone_interval(t1,t2):
                var = get_variations(t1,t2)
                evar = get_maximal_variations(t1,t2)
                for c,a in evar:
                    for b in range(a+1,c):
                        if (b,a) in var and not (b,a) in evar:
                            return t1,t2
    return True

def interval_to_face_tree(tree1, tree2):
    s = getSFromTree(tree1)
    inv1 = tree_inversions_dict(tree1)
    inv2 = tree_inversions_dict(tree2)
    invs = [ZZ(inv1.get((b,a),0) + inv2[(b,a)])/ZZ(2) for (b,a) in inv2]
    return face_tree_from_inversions(s,invs)

def belong_to_face(tree, ftree):
    tinvs = tree_inversions_dict(tree)
    finvs = face_tree_inversions(ftree)
    n = tree.label()
    for a in range(1,n+1):
        for b in range(a+1,n+1):
            i,j = tinvs.get((b,a),0), finvs.get((b,a),0)
            if not (i >= j - ZZ(1)/ZZ(2) and i <= j + ZZ(1)/ZZ(2)):
                return False
    return True

def included_in_face(ftree1, ftree2):
    tinvs = face_tree_inversions(ftree1)
    finvs = face_tree_inversions(ftree2)
    n = ftree1.tree().label()
    for a in range(1,n+1):
        for b in range(a+1,n+1):
            i,j = tinvs.get((b,a),0), finvs.get((b,a),0)
            if int(j) == j and i != j:
                return False
            if not (i >= j - ZZ(1)/ZZ(2) and i <= j + ZZ(1)/ZZ(2)):
                return False
    return True

def dimension_tree_face(ftree):
    return ftree.dimension()

def remove_face(s,ftree):
    n = ftree.tree().label()
    invs = face_tree_inversions(ftree)
    for c in range(3,n+1):
        for b in range(2,c):
            for a in range(1,b):
                if invs.get((c,b),0) < invs.get((c,a),0):
                    if invs.get((c,b),0) <= s[c-1]-1:
                        return True
    return False

def border_face(ftree):
    return ftree.is_border_face()

def tree_versions(tree):
    counts = {}
    def versions_rec(tree):
        if len(tree) == 0:
            return
        b = tree.label()
        for c in counts:
            if c > b:
                yield (b,c),counts[c]
        for r in versions_rec(tree[-1]):
            yield r
        for i in range(len(tree)-2,-1,-1):
            counts[b] = counts.get(b,0) +1
            for r in versions_rec(tree[i]):
                yield r
    for r in versions_rec(tree):
        yield r

def check_transitivity(s, inversions):
    n = len(s)
    for a in range(1,n-1):
        for b in range(a+1,n):
            for c in range(b+1,n+1):
                if inversions.has_key((c,b)) and inversions.has_key((b,a)):
                    if not inversions.get((c,a),0) >= inversions[(c,b)]:
                        return False
    return True

def check_planarity(s, inversions):
    for (c,a) in inversions:
        for b in range(a+1,c):
            if not inversions.get((c,b),0) >= i and not inversions.get((b,a),0) == s[b-1]:
                return False
    return True

def check_tree_inversion_set(s, inversions):
    return check_transitivity(s, inversions) and check_planarity(s, inversions)

def checkAllInversionSet(s):
    for tree in getSDecreasingTrees(s):
        inversions = tree_inversions_dict(tree)
        if not check_tree_inversion_set(s,inversions):
            print(tree)
            return False
    return True

def inverse_inversions(s, inversions):
    d = {}
    for c in range(len(s),1,-1):
        for a in range(c-1,0,-1):
            d[(c,a)] = s[c-1] - inversions.get((c,a),0)
    return d

def transitive_closure(s, inversions):
    new_inversions = dict(inversions)
    n = len(s)
    changed = True
    while changed:
        changed = False
        for a in range(1,n-1):
            for b in range(a+1,n):
                for c in range(b+1,n+1):
                    if new_inversions.has_key((c,b)) and new_inversions.has_key((b,a)):
                        if not new_inversions.get((c,a),0) >= new_inversions[(c,b)]:
                            new_inversions[(c,a)] = new_inversions[(c,b)]
                            changed = True
    return new_inversions

def join_inversions(s,inv1, inv2):
    inv3 = dict(inv1)
    for c,a in inv2:
        inv3[(c,a)] = max(inv1.get((c,a),0), inv2[(c,a)])
    return transitive_closure(s,inv3)

def join_trees(s,t1,t2):
    inv1 = tree_inversions_dict(t1)
    inv2 = tree_inversions_dict(t2)
    inv3 = join_inversions(s,inv1,inv2)
    return tree_from_inversions(s,inv3)


def meet_trees(s,t1,t2):
    inv1 = tree_inversions_dict(t1)
    inv2 = tree_inversions_dict(t2)
    inv1 = inverse_inversions(s,inv1)
    inv2 = inverse_inversions(s,inv2)
    inv3 = join_inversions(s,inv1,inv2)
    inv3 = inverse_inversions(s,inv3)
    return tree_from_inversions(s,inv3)

# tested
# 011
# 022
# 0202
# 0302
# 0312
# 03002
def test_join(s):
    seen = []
    for t in getSDecreasingTrees(s):
        inv1 = tree_inversions_dict(t)
        for t2 in seen:
            inv2 = tree_inversions_dict(t2)
            inv3 = join_inversions(s,inv1, inv2)
            if not check_planarity(s,inv3):
                print(inv1, inv2)
                return False
        seen.append(t)
    return True

def sweak_lequal(tree1,tree2):
    inv1 = dict(tree_inversions(tree1))
    inv2 = dict(tree_inversions(tree2))
    return sweak_lequal_inversions(inv1, inv2)

def sweak_lequal_inversions(inv1, inv2):
    return all(inv1[k] <= inv2.get(k,0) for k in inv1)


def latticeHasseDiagramTree(s):
    L = list(getSDecreasingTrees(s))
    edges = [(p1,p2) for p1 in L for p2 in sweak_tree_succ(p1)]
    return DiGraph(edges, format ="list_of_edges")

def sWeakOrderLatticeTrees2(s):
    L = list(getSDecreasingTrees(s))
    return Poset([L, sweak_lequal])


# 001
# 111
# 112
# 1001
# 1101
# 1011
# 1012
# 1022
# 1122
# 1222
# 12021
def checkLatticeTreeDefinition(s):
    L1 = sWeakOrderLatticeTrees(s)
    L2 = sWeakOrderLatticeTrees2(s)
    return L1.is_isomorphic(L2)

# 001
# 111
# 112
# 133
# 1001
# 1101
# 1011
# 1012
# 1022
# 1122
# 1222
# 1333
# 12021
def checkLatticeHasseDiagram(s):
    L = sWeakOrderLatticeTrees(s)
    H = latticeHasseDiagramTree(s)
    return L.hasse_diagram() == H

def inv_sperm(sperm):
    d = {}
    for i,v in enumerate(sperm):
        if v in d:
            d[v].append(i)
        else:
            d[v] = [i]
    return d

def decomp(sperm):
    if len(sperm) == 0:
        return 0, []
    n = max(sperm)
    d = [[]]
    for v in sperm:
        if v == n:
            d.append([])
        else:
            d[-1].append(v)
    return n,d

# not working, should include only ascends / descends

#def get_chambers(sperm):
    #"""
    #OUTPUT: big value, small value, prev wall, next wall
    #3,1,0,1 ==> x3 < x1 < x3 + 1
    #"""
    #n,d = decomp(sperm)
    #counts = {}
    #for i,branch in enumerate(d):
        #l_counts = {}
        #for v in branch:
            #l_counts[v] = l_counts.get(v,0) + 1
        #values = l_counts.keys()
        #for v in values:
            #prev = -1
            #if i != 0:
                #chamber1 = sum(c - 1 for v2,c in counts.iteritems() if v2 > v)
                #chamber1 += i - 1
                #prev = chamber1
            #else:
                #chamber1 = None
            #if i != len(d)-1:
                #chamber2 = prev + 1 + sum(c - 1 for v2,c in l_counts.iteritems() if v2 > v)
            #else:
                #chamber2 = None
            #yield n,v,chamber1, chamber2
        #counts.update(l_counts)
        #for r in get_chambers(branch):
            #yield r
def treeContains(tree,a):
    if tree.label() == a:
        return true
    if len(tree) == 0 or tree.label() < a:
        return false
    return any(treeContains(child,a) for child in tree)

def chambers(tree):
    invs = dict(tree_inversions(tree))
    s = getSFromTree(tree)
    n = tree.label()
    for a in range(1,n):
        for c in range(a+1,n+1):
            i = (c,a)
            v = invs.get(i,0)
            chamber1 = None
            chamber2 = None
            if v!= 0:
                chamber1 = v-1
            if v!=s[c-1]:
                chamber2 = v
            for b in range(a+1,c):
                if s[b-1] > 1:
                    if invs.get((c,b),0) < v:
                        if chamber1 != None:
                            chamber1+=s[b-1]-1
                        if chamber2 != None:
                            chamber2+=s[b-1]-1
                    if invs.get((c,b),0) == v:
                        if chamber2 !=None:
                            chamber2+=s[b-1]-1
            yield (c,a,chamber1,chamber2)

def ieqs_iter_chambers(tree):
    n = tree.label()
    for c,a,wall1,wall2 in chambers(tree):
        if wall1 != None:
            ieq = [0 for i in range(n+1)]
            ieq[0] = -wall1
            ieq[a] = 1
            ieq[c] = -1
            yield ieq
        if wall2 != None:
            ieq = [0 for i in range(n+1)]
            ieq[0] = wall2
            ieq[a] = -1
            ieq[c] = 1
            yield ieq

def ieqs_iter_tree(tree,n):
    if len(tree) == 0:
        return
    for a,b in treeAscents(tree):
        counts = {}
        cb = 0
        for v in permFromTreeGenerator(tree):
            if v == a:
                break
            if v > a and v < b:
                counts[v] = counts.get(v,0) + 1
            elif v==b:
                cb+=1
        chamber = sum(counts[key] -1 for key in counts)
        chamber += cb
        ieq = [0 for i in range(n+1)]
        ieq[0] = chamber
        ieq[a] = -1
        ieq[b] = 1
        yield ieq
    for b,a in treeDescents(tree):
        counts = {}
        cb = 0
        for v in permFromTreeGenerator(tree):
            if v == a:
                break
            if v > a and v < b:
                counts[v] = counts.get(v,0) + 1
            elif v==b:
                cb+=1
        chamber = sum(counts[key] -1 for key in counts)
        chamber += cb-1
        ieq = [0 for i in range(n+1)]
        ieq[0] = -chamber
        ieq[a] = 1
        ieq[b] = -1
        yield ieq




def ieqs_iter(sperm):
    n = max(sperm)
    counts = {}
    for i in range(len(sperm)-1):
        v1,v2 = sperm[i],sperm[i+1]
        if v1 < v2:
            chamber = sum(c - 1 for b,c in counts.iteritems() if b > v1 and b < v2)
            chamber += counts.get(v2,0)
            ieq = [0 for i in range(n+1)]
            ieq[0] = chamber
            ieq[v1] = -1
            ieq[v2] = 1
            yield ieq
        elif v1 > v2:
            chamber = sum(c - 1 for b,c in counts.iteritems() if b > v2 and b < v1)
            chamber += counts.get(v1,0)
            ieq = [0 for i in range(n+1)]
            ieq[0] = -chamber
            ieq[v2] = 1
            ieq[v1] = -1
            yield ieq
        counts[v1] = counts.get(v1,0) + 1


def get_ieqs(sperm):
    return list(ieqs_iter(sperm))

def get_ieqs_tree(tree):
    n = tree.label()
    return list(ieqs_iter_tree(tree,n))

def get_ieqs_chambers(tree):
    return list(ieqs_iter_chambers(tree))

def getspermPolyhedron(sperm):
    n = max(sperm)
    eq = [1 for i in range(n+1)]
    eq[0] = 0
    ieqs = get_ieqs(sperm)
    return Polyhedron(ieqs=ieqs, eqns=[eq])


def getTreePolyhedron(tree):
    n = tree.label()
    eq = [1 for i in range(n+1)]
    eq[0] = 0
    ieqs = get_ieqs_tree(tree)
    return Polyhedron(ieqs=ieqs, eqns=[eq])

def getChamberPolyhedron(tree):
    n = tree.label()
    eq = [1 for i in range(n+1)]
    eq[0] = 0
    ieqs = get_ieqs_chambers(tree)
    return Polyhedron(ieqs=ieqs, eqns=[eq])

# checked
# 001
# 111
# 222
# 0001
# 0002
# 0102
# 0012
# 0112
# 0212
# 0122
# 0222
# 0333
def checkChamberPolyhedra(s):
    for tree in getSDecreasingTrees(s):
        if getTreePolyhedron(tree) != getChamberPolyhedron(tree):
            print(tree)
            return False
    return True

def spermPolyhedra(s):
    #boundary = Polyhedron(ieqs = [(1,1,0,-1), (s[1]+s[2]-1,-1,0,1), (1,0,1,-1), (s[2],0,-1,1), (s[2],1,-1,0), (s[1]+s[2]-1,-1,1,0)], eqns=[[0,1,1,1]])
    #return [getspermPolyhedron(sperm).intersection(boundary) for sperm in getSPermutations(s)]
    return [getspermPolyhedron(sperm) for sperm in getSPermutations(s)]

def treePolyhedra(s):
    #boundary = Polyhedron(ieqs = [(1,1,0,-1), (s[1]+s[2]-1,-1,0,1), (1,0,1,-1), (s[2],0,-1,1), (s[2],1,-1,0), (s[1]+s[2]-1,-1,1,0)], eqns=[[0,1,1,1]])
    #return [getspermPolyhedron(sperm).intersection(boundary) for sperm in getSPermutations(s)]
    return [getTreePolyhedron(tree) for tree in getSDecreasingTrees(s)]

def spermPolyhedraDict(s):
    return {sperm:getspermPolyhedron(sperm) for sperm in getSPermutations(s)}

def treePolyhedraDict(s):
    return {tree:getTreePolyhedron(tree) for tree in getSDecreasingTrees(s)}


def spermPolyhedraProj3(s):
    pols = spermPolyhedra(s)
    matrix = Matrix([[1, 0], [0, 1], [-ZZ(1)/ZZ(2), -ZZ(1)/ZZ(2)]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def spermPolyhedraProj4(s):
    pols = spermPolyhedra(s)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def getProj4Polyhedron(s):
    pol = getspermPolyhedron(s)
    pol.projection() # ??
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    return pol.projection(proj)

#def plotPols(pols, **args):
    #plots = [p.plot(**args) for p in pols]
    #return sum(plots)

def plotPols(pols, **args):
    return sum(pols).show(**args)

def treePolyhedraProj3(s):
    pols = treePolyhedra(s)
    matrix = Matrix([[1, 0], [0, 1], [-ZZ(1)/ZZ(2), -ZZ(1)/ZZ(2)]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def treePolyhedraProj4(s):
    pols = treePolyhedra(s)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols


def getProj4TreePolyhedron(tree):
    pol = getspermPolyhedron(tree)
    pol.projection() # ??
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    return pol.projection(proj)


# 1,1,1
# 2,2,2
# 1,4,3
# 1,1,1,1
# 2,2,2,2
# 2,3,5,3
# 2,3,5,3,2
def checkLatticePolyhedra(s):
    polDict = spermPolyhedraDict(s)
    dimension = len(s)-1
    for sperm in getSPermutations(s):
        for sperm2 in metasylv_succ(sperm):
            print(sperm, sperm2)
            I = polDict[sperm].intersection(polDict[sperm2])
            print(I)
            if I.dimension() != dimension -1:
                print("No", sperm, sperm2)
                return False
    return True

# 1,1,1
# 2,2,2
# 1,4,3
# 1,1,1,1
# 2,2,2,2
# 2,3,5,3
# 2,3,5,3,2
# 001
# 0011
# 0101
# 0202
# 0303
# 0033
# 01202
def checkLatticeTreePolyhedra(s):
    polDict = treePolyhedraDict(s)
    dimension = len(s)-1
    for tree in getSDecreasingTrees(s):
        for tree2 in sweak_tree_succ(tree):
            print(tree, tree2)
            I = polDict[tree].intersection(polDict[tree2])
            print(I)
            if I.dimension() != dimension -1:
                print("No", tree, tree2)
                return False
    return True

### primal decomp

def get_sperm_point(sperm):
    n = max(sperm)
    P = [0 for i in range(n)]
    counts = {}
    for a in sperm:
        if not a in counts:
            for b in range(a+1,n+1):
                v = counts.get(b,0)
                P[a-1] += v
                P[b-1] -= v
        counts[a] = counts.get(a,0) +1
    return P

# the second fix idea for dim3
def fix_tree_point2_3d(tree, P):
    s = getSFromTree(tree)
    n = len(s)
    invs = tree_inversions_dict(tree)
    denominator = (s[3]+1)*2+1
    for (b,a) in invs:
        if b < len(s):
            if invs[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        if invs.get((b,aa),0) == 0:
                            numerator = -invs.get((c,b),0) + invs.get((c,aa),0) + s[c-1]
                            f = ZZ(numerator)/ZZ(denominator)
                            P[a-1]+=f
                            P[b-1]-=f
                        elif invs.get((b,aa),0) == s[b-1]:
                            numerator =  invs.get((c,aa),0) - invs.get((c,b),0) - s[c-1]
                            f = ZZ(numerator)/ZZ(denominator)
                            P[a-1]+=f
                            P[b-1]-=f
    return P

def fix_tree_point(tree, P):
    if len(tree) < 2 or tree.label() != 4:
        return
    s = getSFromTree(tree)
    dinvs = tree_inversions_dict(tree)
    #if dinvs.get((3,2),0) == s[2]:
        #P[1] +=3
        #P[2] -=3
    #elif dinvs.get((3,2),0) == 0:
        #P[1] -=3
        #P[2] +=3

    #if dinvs.get((3,1),0) == s[2]:
        #P[0] +=3
        #P[2] -=3
    #elif dinvs.get((3,1),0) == 0:
        #P[0] -=3
        #P[2] +=3

    for i in range(len(tree)):
        if tree[i].label() == 3:
            for j in range(len(tree)):
                if j!=i and len(tree[j])!= 0:
                    for k in range(1,len(tree[i])-1):
                        if len(tree[i][k]) != 0:
                            v = tree[i][k].label()
                            e = (j-i) * ZZ(1)/3
                            P[v-1]+= e
                            P[2]-= e
                            return

    #if len(tree[0]) == 0 or len(tree[1]) == 0:
        #return
    #if tree[0].label() == 3:
        #for i in range(1,len(tree[0])-1):
            #v = tree[0][i]
            #if len(v) != 0:
                #k = v.label()
                #P[k-1] += ZZ(1)/3
                #P[2] -= ZZ(1)/3
                #return
    #if tree[1].label() == 3:
        #for i in range(1,len(tree[1])-1):
            #v = tree[1][i]
            #if len(v) != 0:
                #k = v.label()
                #P[k-1] -= ZZ(1)/3
                #P[2] += ZZ(1)/3
                #return

def get_tree_point_nofix(tree):
    n = tree.label()
    P = [0 for i in range(n)]
    for (b,a), v in tree_inversions(tree):
        P[a-1] += v
        P[b-1] -= v
    return P

# the second fix
def get_tree_point_secondfix(tree):
    n = tree.label()
    P = [0 for i in range(n)]
    for (b,a), v in tree_inversions(tree):
        P[a-1] += v
        P[b-1] -= v
    #fix_tree_point(tree, P)
    if n >=4:
        fix_tree_point2_3d(tree,P)
    return P

# tentative for fixing al
def get_tree_pointt(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = factorial(n)/2
    #factor = 1
    scaling = [s[i+1]*(i-1) for i in range(len(s)-1)]
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b >= 3 and b < n and s[b-1] > 1:
            k+=scaling[b-1]
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= factor/b *(p1 - p3)
            else:
                k+=scaling[b-1]
                pass
        P[a-1] +=k
        P[b-1] -= k
    return P

# trying to fix 3 and 4
def get_tree_point34(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = 3
    #factor = ZZ(1)
    scaling = sum(s[3:])
    scaling = 0
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b == 3 and b < len(s):
            k+=scaling
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= factor /3 * (p1 - p3)
            else:
                k+=scaling
                pass
        P[a-1] +=k
        P[b-1] -= k
    return P

# fix without stetch
def get_tree_point_justfix(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = prod(i for i in range(3,len(s)))
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b >= 3 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(1,b):
                    p1 = inv.get((b+1,c),0)
                    p3 = inv.get((b+1,b),0)
                    k+= (p1 - p3)
            else:
                pass
        P[a-1] +=k
        P[b-1] -= k
    return P


# works for n = 4
def get_tree_point2(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = prod(i for i in range(3,len(s)))
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b >= 3 and b < len(s):
            k+=s[b]
            if inv[(b,a)] < s[b-1]:
                for c in range(1,b):
                    p1 = inv.get((b+1,c),0)
                    p3 = inv.get((b+1,b),0)
                    k+= (p1 - p3)
            else:
                k+=s[b]
        P[a-1] +=k
        P[b-1] -= k
    return P

# tentative partial fix for increasing s3
# 0**11...1*
# tested
# 00211
# 00212
# 00213
# 00214
# 00215
# 00314
# 00315
# 003113
def get_tree_pointttt(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = 3
    #factor = ZZ(1)
    scaling = sum(s[3:])
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b == 3 and b < len(s):
            k+=scaling
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= factor /3 * (p1 - p3)
            else:
                k+=scaling
                pass
        P[a-1] +=k
        P[b-1] -= k
    return P

# tentative partial fix to increase s4
# 00121
# 00131
# 01131
# 00122
# 00132
# 000211
# 00043
def get_tree_point4(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = 4
    scaling = sum(s[4:])
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b == 4 and b < len(s):
            k+=scaling
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= (p1 - p3)
            else:
                k+=scaling
        P[a-1] +=k
        P[b-1] -= k
    return P

# tentative partial fix to increase s5
# 000021
# 000031
# 000032
# 0000212
#
def get_tree_point5(tree):
    n = tree.label()
    s = getSFromTree(tree)
    P = [0 for i in range(n)]
    inv = tree_inversions_dict(tree)
    factor = 5
    scaling = sum(s[5:])*factor
    for (b,a) in inv:
        k = factor*inv[(b,a)]
        if b == 5 and b < len(s):
            k+=scaling
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= (p1 - p3)
            else:
                k+=scaling
        P[a-1] +=k
        P[b-1] -= k
    return P

get_tree_point = get_tree_point2


def getVertices(s):
    vertices = []
    for sperm in getSPermutations(s):
        for sperm2 in metasylv_succ(sperm):
            vertices.append(Polyhedron([get_sperm_point(sperm), get_sperm_point(sperm2)]))
    return vertices

def getVerticesTree(s):
    vertices = []
    for tree in getSDecreasingTrees(s):
        for tree2 in sweak_tree_succ(tree):
            vertices.append(Polyhedron([get_tree_point(tree), get_tree_point(tree2)]))
    return vertices

def getVerticesTreeCoord(s, coord):
    vertices = []
    for tree in getSDecreasingTrees(s):
        for tree2 in sweak_tree_succ(tree):
            vertices.append(Polyhedron([coord[tree], coord[tree2]]))
    return vertices

def getConvexHull(s):
    vertices = [get_tree_point(tree) for tree in getSDecreasingTrees(s)]
    return Polyhedron(vertices)

def proj3Vertices(s):
    pols = getVertices(s)
    matrix = Matrix([[1, 0], [0, 1], [-ZZ(1)/ZZ(2), -ZZ(1)/ZZ(2)]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def proj3VerticesTree(s, **options):
    pols = getVerticesTree(s)
    return proj3Pols(pols, **options)

def proj4Vertices(s):
    pols = getVertices(s)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def proj4VerticesTree(s, **options):
    pols = getVerticesTree(s)
    return proj4Pols(pols)

def proj4VerticesTreeCoord(s, coord):
    pols = getVerticesTreeCoord(s, coord)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

#def proj4VerticesFacetCoord(facet, coord):
    #pols = getVerticesTreeCoord(s, coord)
    #matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    #proj = lambda x: list(Matrix(x)*matrix)[0]
    #projs = [p.projection() for p in pols] # ??
    #pols = [p.projection(proj) for p in pols]
    #return pols

def proj4ConvexHull(s):
    pol = getConvexHull(s)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projpol = pol.projection()
    pol = pol.projection(proj)
    return pol


def get_facets_spermutations(s):
    d = {}
    n = len(s)
    import itertools
    for sperm in getSPermutations(s):
        inv = inv_sperm(sperm)
        for r in itertools.product(*(inv[i] for i in range(2,n+1))):
            key = tuple(v for i,v in enumerate(sperm) if i not in r)
            L = d.get(key,set())
            L.add(sperm)
            d[key] = L
    return d


def getFacetsNumber(s):
    ns = [v-1 for v in s]
    for i in range(len(s)):
        if ns[i]<0:
            ns[i] = 0
    return cardinalitySDecreasingTrees(ns)


def get_facet_tree_intervals(s):
    S = getSDecreasingTrees(s)
    maxascent = len(s) - 1
    for tree in S:
        inv = tree_inversions_dict(tree)
        ascents = list(treeAscentsFromInv(s,inv))
        if len(ascents) == maxascent:
            for a,c in ascents:
                inv[(c,a)] = inv.get((c,a),0) + 1
            inv = transitive_closure(s,inv)
            yield (tree, tree_from_inversions(s,inv))

def get_dimension_facet_tree_intervals(s, d):
    S = getSDecreasingTrees(s)
    for tree in S:
        inv = tree_inversions_dict(tree)
        ascents = list(treeAscentsFromInv(s,inv))
        for comb in Combinations(ascents, d):
            ninv = dict(inv)
            for a,c in comb:
                ninv[(c,a)] = ninv.get((c,a),0) + 1
            ninv = transitive_closure(s,ninv)
            yield (tree, tree_from_inversions(s,ninv))

def get_dimension_face_trees(s, d):
    S = getSDecreasingTrees(s)
    for tree in S:
        inv = tree_inversions_dict(tree)
        ascents = list(treeAscentsFromInv(s,inv))
        for comb in Combinations(ascents, d):
            yield get_face_tree(s, tree, comb)


def get_euler_chars(s):
    d = {ftree:0 for ftree in get_dimension_face_trees(s, len(s)-1)}
    for dim in range(len(s)):
        for ft in get_dimension_face_trees(s,dim):
            for ftree in d:
                if included_in_face(ft,ftree):
                    d[ftree]+=(-1)**dim
    return d

def get_facet_trees(s):
    S = list(getSDecreasingTrees(s))
    inversions = {t: tree_inversions_dict(t) for t in S}
    d = {interval:[] for interval in get_facet_tree_intervals(s)}
    for t in S:
        for t1,t2 in d:
            if sweak_lequal_inversions(inversions[t1],inversions[t]) and sweak_lequal_inversions(inversions[t],inversions[t2]):
                d[(t1,t2)].append(t)
    return d

def get_facet_tree_trees(s):
    S = list(getSDecreasingTrees(s))
    d = {ftree:[] for ftree in get_dimension_face_trees(s, len(s)-1)}
    for t in S:
        for ftree in d:
            if belong_to_face(t,ftree):
                d[ftree].append(t)
    return d

def get_facet_tree_faces(s):
    S = list(getSFaceTrees(s))
    d = {ftree:[] for ftree in get_dimension_face_trees(s, len(s)-1)}
    for ft in S:
        for ftree in d:
            if included_in_face(ft,ftree):
                d[ftree].append(ft)
    return d

def get_facet_border_inequalities(s, ftree, trees, faces):
    d = dimension_tree_face(ftree)
    L = [ft for ft in faces if border_face(ft) and dimension_tree_face(ft) == d - 1 and (not remove_face(s,ft)) ]
    border_ieqs = []
    if len(L) > 0:
        pol = Polyhedron([get_tree_point(t) for t in trees])
        ieqs = pol.inequalities()
        for face in L:
            trees_face = [t for t in trees if belong_to_face(t,face)]
            pol2 = Polyhedron([get_tree_point(t) for t in trees_face])
            border_ieqs.extend([i for i in ieqs if all(not i.interior_contains(v) for v in pol2.vertices())])
    return border_ieqs


def vtamari_pol_facet(s,ftree, trees, faces, borders):
    d = dimension_tree_face(ftree)
    facets = [ft for ft in faces if dimension_tree_face(ft) == d - 1 and (not remove_face(s,ft)) ]
    v_ieqs = []
    if len(facets) > 0:
        pol = Polyhedron([get_tree_point(t) for t in trees])
        ieqs = pol.inequalities()
        for face in facets:
            trees_face = [t for t in trees if belong_to_face(t,face)]
            pol2 = Polyhedron([get_tree_point(t) for t in trees_face])
            v_ieqs.extend([i for i in ieqs if all(not i.interior_contains(v) for v in pol2.vertices())])
        v_ieqs.extend(borders)
        return Polyhedron(ieqs = v_ieqs, eqns = pol.equations())
    return None

def vtamari_pols(s):
    TREES = get_facet_tree_trees(s)
    FACES = get_facet_tree_faces(s)
    border_ieqs = sum((get_facet_border_inequalities(s, ft, TREES[ft], FACES[ft]) for ft in TREES), [])
    pols = [vtamari_pol_facet(s,ftree, TREES[ftree], FACES[ftree], border_ieqs) for ftree in TREES]
    pols = [pol for pol in pols if not pol is None]
    return pols

def vtamari_pols_edges(s):
    pols = vtamari_pols(s)
    edges = set()
    for pol in pols:
        for f in pol.faces(1):
            edges.add(Polyhedron(f.vertices()))
    return list(edges)

def check_vtamari_remove_face(s):
    FACES = get_facet_tree_faces(s)
    d = len(s) - 1
    invalid1 = [ftree for ftree in FACES if dimension_tree_face(ftree) == d and all(remove_face(s,ft) for ft in FACES[ftree] if dimension_tree_face(ft) == d-1)]
    invalid2 = [ftree for ftree in FACES if dimension_tree_face(ftree) == d and remove_face(s,ftree)]
    return invalid1 == invalid2

def check_vtam_intersect(pols):
    for i in range(len(pols)):
        for j in range(i):
            pol1, pol2 = pols[i], pols[j]
            if pol1.intersection(pol2).dimension() == pol1.dimension():
                return False
    return True

def check_vtam_vertices(s, pols):
    V = set(v for pol in pols for v in pol.vertices())
    return len(V) == getSCatalanCardinality(s)

def check_vtam_graph(s, pols):
    G = Graph()
    for pol in pols:
        G = G.union(pol.vertex_graph())
    G2 = Graph(getSCatalanLattice(s).hasse_diagram())
    return G.is_isomorphic(G2)

# with fix_tree_point2_3D
# works for
# 022
# 0211
# 0222
# 0333
# 0112
# broken
# 0002
# with get_tree_point2
# works for
# 022
# 033
# 044
# 055
# 0222
# 0333
# 0444
# 0555
# 0115
# 0515
def check_vtamari_pols(s):
    pols = vtamari_pols(s)
    return check_vtam_intersect(pols) and check_vtam_vertices(s,pols) and check_vtam_graph(s,pols)

def get_trees_from_face_tree(s, ftree):
    return [t for t in getSDecreasingTrees(s) if belong_to_face(t,ftree)]

def get_dimention_facet_trees(s,dim):
    S = list(getSDecreasingTrees(s))
    inversions = {t: tree_inversions_dict(t) for t in S}
    d = {interval:[] for interval in get_dimension_facet_tree_intervals(s, dim)}
    for t in S:
        for t1,t2 in d:
            if sweak_lequal_inversions(inversions[t1],inversions[t]) and sweak_lequal_inversions(inversions[t],inversions[t2]):
                d[(t1,t2)].append(t)
    return d





#def getFacetsNumber(s):
    #ns = list(s)
    #i = 0
    #while i < len(s) and s[i] == 1:
        #i+=1
    #if i == len(s):
        #return 1



# checked
# 1,2,1
# 1,2,2
# 1,4,3
# 1,5,2
# 1,5,4
# 1,2,2,2
# 1,4,3,5
# 1,2,2,2,2
# 1,3,3,3,3
# 1,3,2,3,4
# 1,3,2,3,4,2
# 1,1,2
# 1,1,2,1
# 1,1,2,1,2
# 1,1,2,1,1,2
# 1,1,2,1,1,1,3
# 1,1,2,1,1,1,3,1,1,2
# 1,1,2,1,2,3
# 1,2,2,1,1,3
# 101
# 1001
# 1101
# 1101001
# 11010101
# 110120112
def checkFactetsNumber(s):
    V = f_vector(s)
    return getFacetsNumber(s) == V.coefficients()[-1]

def get_facets_vertices(facet):
    vertices = []
    for tree in facet:
        for tree2 in sweak_tree_succ(tree):
            if tree2 in facet:
                vertices.append(Polyhedron([get_tree_point(tree), get_tree_point(tree2)]))
    return vertices

def get_facet_convex_hull(facet):
    return Polyhedron([get_tree_point(tree) for tree in facet])

def get_facet_lattice(facet):
    return Poset((facet, sweak_lequal))


def proj3FacetVertices(facet):
    pols = get_facets_vertices(facet)
    matrix = Matrix([[1, 0], [0, 1], [-ZZ(1)/ZZ(2), -ZZ(1)/ZZ(2)]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def proj4FacetVertices(facet):
    pols = get_facets_vertices(facet)
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    projs = [p.projection() for p in pols] # ??
    pols = [p.projection(proj) for p in pols]
    return pols

def proj3Matrix():
    return  Matrix([[-ZZ(1),-ZZ(1)], [-(sqrt(3)/2+1), -ZZ(3)/ZZ(2)], [-ZZ(1), -ZZ(2)]])

def proj3Pol(pol, **options):
    #matrix = Matrix([[1, 0], [0, 1], [-ZZ(1)/ZZ(2), -ZZ(1)/ZZ(2)]])
    #matrix = Matrix([[ZZ(1),ZZ(1)], [ZZ(3)/ZZ(2), sqrt(3)/2+1], [ZZ(2), ZZ(1)]])
    matrix =proj3Matrix()
    proj = lambda x: list(Matrix(x)*matrix)[0]
    v = pol.vertices_list()
    v = [Matrix(x)*matrix for x in v]
    v = [list(p[0]) for p in v]
    return line2d(v, **options)

def proj4Pol(pol, **options):
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    proj = lambda x: list(Matrix(x)*matrix)[0]
    v = pol.vertices_list()
    v = [Matrix(x)*matrix for x in v]
    v = [list(p[0]) for p in v]
    if len(set(tuple(p) for p in v)) == 1:
        return point3d(v[0], **options)
    return line3d(v, **options)

def proj3Pols(pols, **options):
    return [proj3Pol(pol, **options) for pol in pols]

def proj4Pols(pols, **options):
    return [proj4Pol(pol, **options) for pol in pols]

def proj4FacetConvexHull(facet):
    matrix = Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
    pol = get_facet_convex_hull(facet)
    proj = lambda x: list(Matrix(x)*matrix)[0]
    pol.projection()
    pol = pol.projection(proj)
    return pol

def testFacet(facet):
    pol = get_facet_convex_hull(facet)
    vertices = pol.vertices()
    if len(vertices) != len(facet):
        print("wrong vertices")
        return False
    if set(tuple(get_tree_point(tree)) for tree in facet) != set(tuple(v) for v in vertices):
        print("wront vertices")
        return False
    lattice = get_facet_lattice(facet)
    G = lattice.hasse_diagram()
    if G.num_edges() != len(pol.faces(1)):
        print("wrong edges")
        return False
    G.relabel(lambda x:tuple(get_tree_point(x)))
    G = Graph(G) # remore orientation
    G2 = Graph()
    G2.add_vertices(tuple(p) for p in vertices)
    for e in pol.faces(1):
        v1,v2 = e.vertices()
        G2.add_edge(tuple(v1),tuple(v2))
    if G != G2:
        print("wrong structure")
        return False

    return True

def testFacetCoord(facet, coord):
    pol = Polyhedron([coord[t] for t in facet])
    vertices = pol.vertices()
    if len(vertices) != len(facet):
        print("wrong vertices")
        return False
    if set(tuple(coord[tree]) for tree in facet) != set(tuple(v) for v in vertices):
        print("wront vertices")
        return False
    lattice = get_facet_lattice(facet)
    G = lattice.hasse_diagram()
    if G.num_edges() != len(pol.faces(1)):
        print("wrong edges")
        return False
    G.relabel(lambda x:tuple(coord[x]))
    G = Graph(G) # remore orientation
    G2 = Graph()
    G2.add_vertices(tuple(p) for p in vertices)
    for e in pol.faces(1):
        v1,v2 = e.vertices()
        G2.add_edge(tuple(v1),tuple(v2))
    if G != G2:
        print("wrong structure")
        return False

    return True


def get_broken_tree_face(face, d):
    pol = get_facet_convex_hull(face)
    if pol.dimension() == d:
        print("This face is not broken")
        return None
    broken = []
    for i in range(len(face)):
        t = face[i]
        f2 = face[:i] + face[i+1:]
        pol2 = get_facet_convex_hull(f2)
        if pol2.dimension() == d:
            broken.append(t)
    return broken

def fix_broken_tree(face, d, invs):
    pol = get_facet_convex_hull(face)
    if pol.dimension() == d:
        print("This face is not broken")
        return None
    for i in range(len(face)):
        t = face[i]
        f2 = face[:i] + face[i+1:]
        pol2 = get_facet_convex_hull(f2)
        if pol2.dimension() == d:
            vt = get_tree_point(t)
            v = [get_tree_point(t2) for t2 in f2]
            line1 = tuple(v[1][i] - v[0][i] for i in range(len(v[0])))
            line2 = tuple(v[2][i] - v[0][i] for i in range(len(v[0])))
            Plane = Polyhedron(vertices = [v[0]], lines = [line1, line2])
            lines = []
            for b,a in invs:
                line = [0]*5
                line[b-1] = -1
                line[a-1] = 1
                lines.append(line)
            Plane2 = Polyhedron(vertices = [vt], lines = lines)
            I = Plane.intersection(Plane2)
            if I.dimension() == 0 and I.n_vertices() == 1:
                v = list(I.vertices()[0])
                return [v[i] - vt[i] for i in range(len(vt))]
            else:
                print("Nope")
                return I

def contain_broken_pattern4(tree):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b == 4 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            return True
    return False

def contain_broken_pattern3(tree):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b == 3 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            return True
    return False

def contain_broken_pattern(tree):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b >=3 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            return True
    return False

def contain_broken_patternk(tree,k):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b == k and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            return True
    return False

def broken_pattern_roots(tree):
    n = tree.label()
    r = []
    for v in range(3,n):
        if contain_broken_patternk(tree,v):
            r.append(v)
    return r

def broken_pattern_inversions4(tree):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b == 4 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            yield (b,a)

def broken_pattern_inversions3(tree):
    n = tree.label()
    s = getSFromTree(tree)
    inv = tree_inversions_dict(tree)
    for (b,a) in inv:
        if b == 3 and b < len(s):
            if inv[(b,a)] < s[b-1]:
                for c in range(b+1, n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        if p1 - p3 != 0:
                            yield (b,a)

def fix_pentagon(face, broken_tree, coordinates):
    n = broken_tree.label()
    invs = set(broken_pattern_inversions3(broken_tree))
    invs.update(broken_pattern_inversions4(broken_tree))
    v = [coordinates[t] for t in face if not t == broken_tree]
    line1 = [v[1][i] - v[0][i] for i in range(len(v[0]))]
    line2 = [v[2][i] - v[0][i] for i in range(len(v[0]))]
    Plane = Polyhedron(vertices = [v[0]], lines = [line1, line2], base_ring = QQ)
    #~ try:
        #~ Plane = Polyhedron(vertices = [v[0]], lines = [line1, line2])
    #~ except:
        #~ print v[0],v[1],v[2]
        #~ print line1, line2
        #~ raise ValueError()
    lines = []
    for b,a in invs:
        line = [0]*n
        line[b-1] = - 1
        line[a-1] = 1
        lines.append(line)
    Plane2 = Polyhedron(vertices = [coordinates[broken_tree]], lines = lines, base_ring = QQ)
    I = Plane.intersection(Plane2)
    if I.dimension() != 0 or len(I.vertices()) != 1:
        #print invs
        #print I
        #print face, broken_tree
        return False
    coordinates[broken_tree] = list(I.vertices()[0])
    return True

def fix_broken_tree_faces(faces, broken_tree, coordinates):
    I = None
    for f in faces:
        v = [coordinates[t] for t in f if t != broken_tree]
        line1 = [v[1][i] - v[0][i] for i in range(len(v[0]))]
        line2 = [v[2][i] - v[0][i] for i in range(len(v[0]))]
        Plane = Polyhedron(vertices = [v[0]], lines = [line1, line2], base_ring = QQ)
        if I is None:
            I = Plane
        else:
            I = I.intersection(Plane)
    if I.dimension() != 0 or len(I.vertices()) != 1:
        #print len(faces)
        #print I
        #print broken_tree
        return False
    coordinates[broken_tree] = list(I.vertices()[0])
    return True


def scale_coordinates(s,coords,k, scale):
    for t in coords:
        inv = tree_inversions_dict(t)
        for b,a in inv:
            if b == k:
                coords[t][a-1] +=scale
                coords[t][b-1] -=scale
                if inv[(b,a)] == s[b-1]:
                    coords[t][a-1] +=scale
                    coords[t][b-1] -=scale

def update_scales(coords, scales):
    for t in coords:
        for i in range(len(coords[t])):
            coords[t][i]+=scales[t][i]


def easy_fix(s, coordinates, scales):
    n = len(s)
    fixed_trees = set()
    for tree in coordinates:
        for v in range(3,n):
            if contain_broken_patternk(tree,v):
                if all(not contain_broken_patternk(tree,w) for w in range(v+1,n)):
                    inv = tree_inversions_dict(tree)
                    for (b,a) in inv:
                        if b == v and b < len(s):
                            k = 0
                            if inv[(b,a)] < s[b-1]:
                                for c in range(b+1, n+1):
                                    for aa in range(1,b):
                                        p1 = inv.get((c,aa),0)
                                        p3 = inv.get((c,b),0)
                                        k+= ZZ(1) /b * (p1 - p3)
                                        k+= ZZ(1)/b * (scales[c-3][tree][aa-1] - scales[c-3][tree][b-1])
                            coordinates[tree][a-1] +=k
                            coordinates[tree][b-1] -= k
                    fixed_trees.add(tree)
                break
    return fixed_trees

# no...
def get_denominators(s, inv):
    has_middle_children = set()
    for (b,a) in inv:
        if inv[(b,a)] < s[b-1]:
            has_middle_children.add(b)
    return {v:max([0] + [w for w in range(v) if w in has_middle_children]) for v in range(3,len(s)+1)}

# does not work
def general_fix(s, coordinates, scales):
    n = len(s)
    for tree in coordinates:
        inv = tree_inversions_dict(tree)
        denominators = get_denominators(s, inv)
        for (b,a) in inv:
            if inv[(b,a)] < s[b-1]:
                k = 0
                for c in range(b+1,n+1):
                    for aa in range(1,b):
                        p1 = inv.get((c,aa),0)
                        p3 = inv.get((c,b),0)
                        k+= ZZ(1)/ denominators[c] * (p1 - p3)
                        k+= ZZ(1)/denominators[c] * (scales[c-3][tree][aa-1] - scales[c-3][tree][b-1])
                coordinates[tree][a-1] +=k
                coordinates[tree][b-1] -=k

#def general_fix(s, coordinates, scales):
    #n = len(s)
    #for tree in coordinates:
        #inv = tree_inversions_dict(tree)
        #for (b,a) in inv:
            #if inv[(b,a)] < s[b-1]:
                #k = 0
                #for c in range(b+1,n+1):
                    #for aa in range(1,b):
                        #denominator = b

                        #p1 = inv.get((c,aa),0)
                        #p3 = inv.get((c,b),0)
                        #k+= ZZ(1)/ denominators[c] * (p1 - p3)
                        #k+= ZZ(1)/b * (scales[c-3][tree][aa-1] - scales[c-3][tree][b-1])
                #coordinates[tree][a-1] +=k
                #coordinates[tree][b-1] -=k

def get_tree_coordinates(s, scaling_values):
    S = list(getSDecreasingTrees(s))
    coordinates = {t: get_tree_point(t) for t in S}
    scales = [{t:[0]*len(s) for t in S} for i in range(3, len(s)+1)]
    for i in range(len(scales)):
        scale_coordinates(s, scales[i], i+3, scaling_values[i])
        update_scales(coordinates, scales[i])
    general_fix(s, coordinates, scales)
    return coordinates

# the good function!
# scaling which works
# (0,0,2,2) --> [0,0], [1,0], [1,1],[2,2]
# (0,0,2,2,2) --> [2,1,0], [3,2,1],
# (0,0,2,2,2,1) --> [3,2,1,0]
def fix_broken_pentagons(s, scaling_values, use_easy_fix = True):
    S = list(getSDecreasingTrees(s))
    broken_trees = set(t for t in S if contain_broken_pattern(t))
    r = get_dimention_facet_trees(s,2).values()
    broken_pentagons = [f for f in r if any(t in broken_trees for t in f)]
    coordinates = {t: get_tree_point(t) for t in S}
    orig = {t: list(coordinates[t]) for t in coordinates}
    scales = [{t:[0]*len(s) for t in S} for i in range(3, len(s)+1)]
    for i in range(len(scales)):
        scale_coordinates(s, scales[i], i+3, scaling_values[i])
        update_scales(coordinates, scales[i])

    scaled = {t: list(coordinates[t]) for t in coordinates}

    if use_easy_fix:
        fixed_trees = easy_fix(s, coordinates, scales)
        print("Easy fix")
        print(len(fixed_trees))
        broken_trees.difference_update(fixed_trees)
        broken_pentagons = [f for f in broken_pentagons if any(t in broken_trees for t in f)]

    while len(broken_trees) != 0:
        fixed_trees = set()
        for bt in broken_trees:
            bp = [p for p in broken_pentagons if bt in p]
            bp1 = [p for p in bp if sum(1 for t in p if t in broken_trees) == 1]
            if len(bp1) == 1:
                #print "TEST1"
                if fix_pentagon(bp1[0], bt, coordinates):
                    #print "TEST1"
                    fixed_trees.add(bt)
            elif len(bp1) > 1:
                #print "TEST2", len(bp1)
                if fix_broken_tree_faces(bp1, bt, coordinates):
                    #print "TEST2"
                    fixed_trees.add(bt)
                else:
                    for f in bp1:
                        pol = Polyhedron([coordinates[t] for t in f])
                        if pol.dimension() != 2:
                            if fix_pentagon(f, bt, coordinates):
                                #print "TEST3"
                                fixed_trees.add(bt)
                                break
        print(len(fixed_trees))
        if len(fixed_trees) == 0:
            print("has not fixed everything")
            break
        broken_trees.difference_update(fixed_trees)
        broken_pentagons = [f for f in broken_pentagons if any(t in broken_trees for t in f)]

    #~ while len(broken_trees) != 0:
        #~ fixed_trees = set()
        #~ for bt in broken_trees:
            #~ for p in broken_pentagons:
                #~ if bt in p:
                    #~ b = [t for t in p if t in broken_trees]
                    #~ pol = Polyhedron([coordinates[t] for t in p])
                    #~ if len(b) == 1 and pol.dimension() != 2:
                        #~ if fix_pentagon(p, bt, coordinates):
                            #~ fixed_trees.add(bt)
                            #~ #break
        #~ print len(fixed_trees)
        #~ if len(fixed_trees) == 0:
            #~ break
        #~ broken_trees.difference_update(fixed_trees)
        #~ broken_pentagons = [f for f in broken_pentagons if any(t in broken_trees for t in f)]


    #~ while len(broken_pentagons) > 0:
        #~ c = 0
        #~ for p in broken_pentagons:
            #~ b = [t for t in p if t in broken_trees]
            #~ pol = Polyhedron([coordinates[t] for t in p])
            #~ if len(b) == 0 and pol.dimension() == 2:
                #~ broken_pentagons.remove(p)
                #~ c+=1
            #~ if len(b) == 1:
                #~ if pol.dimension() != 2:
                    #~ fix_pentagon(p, b[0], coordinates)
                #~ c+=1
                #~ broken_pentagons.remove(p)
                #~ broken_trees.remove(b[0])
        #~ print c
        #~ if c == 0:
            #~ return broken_trees, broken_pentagons

    return orig, scaled, coordinates


def testFacetDimension(facet, d):
    pol = get_facet_convex_hull(facet)
    return pol.dimension() == d

def testFacetDimensionCoord(facet, d, coord):
    pol = Polyhedron([coord[t] for t in facet])
    return pol.dimension() == d



def testFacet2(facet):
    pol = get_facet_convex_hull(facet)
    vertices = pol.vertices()
    if len(vertices) != len(facet):
        print("wrong vertices")
        return False
    if set(tuple(get_tree_point(tree)) for tree in facet) != set(tuple(v) for v in vertices):
        print("wront vertices")
        return False
    lattice = get_facet_lattice(facet)
    G = lattice.hasse_diagram()
    G.relabel(lambda x:tuple(get_tree_point(x)))
    edges = set()
    for f in pol.faces(1):
        v1,v2 = f.vertices()
        L = [tuple(v1),tuple(v2)]
        L.sort()
        edges.add(tuple(L))
    for v1,v2,l in G.edges():
        L = [v1,v2]
        L.sort()
        if not tuple(L) in edges:
            print("Not included")
            return False
    return True

def testFacetOrderCompatible(facet):
    pol = get_facet_convex_hull(facet)
    d = {tuple(get_tree_point(t)):t for t in facet}
    lattice = get_facet_lattice(facet)
    for f in pol.faces(1):
        v1,v2 = f.vertices()
        t1 = d[tuple(v1)]
        t2 = d[tuple(v2)]
        if not sweak_lequal(t1,t2) and not sweak_lequal(t2,t1):
            print("Not compatible")
            return False
    return True

def testFacetIntervalSimple(s, facet):
    P = Poset([facet, [(p1,p2) for p1 in facet for p2 in sweak_tree_succ(p1) if p2 in facet]])
    D = P.hasse_diagram()
    L = [len(D.neighbors(v)) for v in D]
    return all(i == L[0] for i in L)


# passed
# 111
# 001
# 002
# 012
# 022
# 033
# 0111
# 0112
# 0202
# 0212
# 0313
# 02112
# passed with 1/3 fix
# 0121
# 0131
# 0331
# not passed (wrong edges)
# 0222
# 0022
# 0122
# 0221
# 02222

# with fix_point2_3d
# 0022
# 0121
# 0123
# 0333
# broken in higher dimensions
def testAllFacets(s):
    d = get_facet_trees(s)
    flag = True
    for k in d:
        facet = d[k]
        if not testFacet(facet):
            return k
            flag = False
    return flag

def testAllFacetsCoord(s, coord):
    d = get_facet_trees(s)
    flag = True
    for k in d:
        facet = d[k]
        if not testFacetCoord(facet, coord):
            return k
            flag = False
    return flag

def testAllFacetsSimpleCoord(s, coord):
    d = get_facet_trees(s)
    for k in d:
        facet = d[k]
        pol = Polyhedron([coord[t] for t in facet])
        if not pol.is_simple():
            return pol
    return True

# works when no 0 in s
# tested
# 0122
# 0222
# 0333
# 0323
# 0303
# 01222
# 01212
# 012222
# 0122222
# also true for
# 01202
# 01001
# not true for
# 0022
def testAllFacetsIntervalSimple(s):
    d = get_facet_trees(s)
    for k in d:
        facet = d[k]
        if not testFacetIntervalSimple(s, facet):
            print("Nope")
            return facet
    return True

def testFacetDimensions(s,d):
    facets = get_dimention_facet_trees(s, d).values()
    r = [f for f in facets if not testFacetDimension(f,d)]
    return r

def testFacetDimensionsCoord(s,d, coord):
    facets = get_dimention_facet_trees(s, d).values()
    r = [f for f in facets if not testFacetDimensionCoord(f,d, coord)]
    return r

def getDimensionBrokenTrees(s, d):
    faces = get_dimention_facet_trees(s,d).values()
    r = [f for f in faces if not testFacetDimension(f,d)]
    return [get_broken_tree_face(f, d) for f in r]

def getDimensionBrokenLattices(s,d):
    faces = get_dimention_facet_trees(s,d).values()
    r = [f for f in faces if not testFacetDimension(f,d)]
    L = [get_facet_lattice(f) for f in r]
    T = [get_broken_tree_face(f, d) for f in r]
    L = [L[i].relabel({t:t if t != T[i][0] else (t,"*") for t in L[i]}) for i in range(len(L))]
    return L

def getDimensionBrokenFaces(s,d):
    faces = get_dimention_facet_trees(s,d).values()
    r = [f for f in faces if not testFacetDimension(f,d)]
    return r

# passed
# 0222
# 0022
# 02222
def testAllFacets2(s):
    d = get_facet_trees(s)
    flag = True
    for k in d:
        facet = d[k]
        if not testFacet2(facet):
            return k
            flag = False
    return flag

# passed
# 111
# 001
# 002
# 012
# 022
# 033
# 0111
# 0112
# 0202
# 0212
# 0313
# 02112
# Not passed
# 0222
def testAllFacetsOrderCompatible(s):
    d = get_facet_trees(s)
    flag = True
    for k in d:
        facet = d[k]
        if not testFacetOrderCompatible(facet):
            print(k)
            flag = False
    return flag

###

def f_vector(s):
    K = PolynomialRing(QQ,'t')
    t = K.gen()
    S = 0
    for sperm in getSPermutations(s):
        S+=(1+t)**nbascent(sperm, s)
    return S

def f_vector_tree(s):
    K = PolynomialRing(QQ,'t')
    t = K.gen()
    S = 0
    for tree in getSDecreasingTrees(s):
        S+=(1+t)**nbtreeAscents(tree)
    return S

# tested
# 011
# 0111
# 022
# 0222
# 033
# 033
# 002
# 0303
@cached_function
def f_vector_rec(s):
    K = PolynomialRing(QQ,'t')
    t = K.gen()
    b = s[-1]
    a = s[-2]
    if len(s) == 2:
        return b+1+b*t
    if a == 0:
        return (b+1 + b*t) * f_vector_rec(s[:-2] + (b,))
    return (b+1) * f_vector_rec(s[:-2] + (a+b,)) + b*t*f_vector_rec(s[:-2] + (a+b-1,))


### Doubling construction

def find_tree(tree, value):
    if len(tree) == 0:
        return None
    if tree.label() == value:
        return tree
    if tree.label() < value:
        return None
    for child in tree:
        f = find_tree(child,value)
        if f != None:
            return f
    return None

def extract_tree(tree, value):
    if len(tree) == 0:
        return tree,None
    if tree.label() == value:
        tree = tree.clone()
        left = tree[0]
        tree[0] = leaf()
        tree.set_immutable()
        return left,tree
    if tree.label() < value:
        return tree,None
    for i,child in enumerate(tree):
        f1,f2 = extract_tree(child,value)
        if f2 != None:
            tree = tree.clone()
            tree[i] = f1
            tree.set_immutable()
            return tree, f2
    return tree,None

def update_tree(tree, new_tree):
    if len(tree) == 0:
        return tree
    if tree.label() == new_tree.label():
        return new_tree
    if tree.label() < new_tree.label():
        return tree
    new_children = []
    for child in tree:
        new_children.append(update_tree(child,new_tree))
    return LabelledOrderedTree(new_children, label = tree.label())

def select_for_doubling(tree, value1, value2):
    f = find_tree(tree,value1)
    def rec_select(tree, value):
        if len(tree) == 0:
            return False
        if tree.label() == value:
            return True
        return rec_select(tree[-1],value)
    tree = f[-2]
    return rec_select(tree,value2)

def arity_increase(tree, value):
    if len(tree) == 0:
        return tree
    if tree.label() == value:
        tree = tree.clone()
        tree.append(leaf())
        tree.set_immutable()
        return tree
    if tree.label() < value :
        return tree
    new_children = []
    for child in tree:
        new_children.append(arity_increase(child,value))
    return LabelledOrderedTree(new_children, label = tree.label())

def partial_arity_increase(L,value1,value2):
    doubling = set(t for t in L if select_for_doubling(t,value1,value2))
    Ld = poset_doubling(L, doubling)
    relabel = {}
    for t,d in Ld:
        if not t in doubling or d == 0:
            relabel[(t,d)] = t
        else:
            fn = find_tree(t,value1)
            fn,fi = extract_tree(fn, value2)
            fn = fn.clone()
            fn[-1] = leftInsertion(fn[-1], fi)
            fn.set_immutable()
            t2 = update_tree(t,fn)
            relabel[(t,d)] = t2
    return Ld.relabel(relabel)

def arity_increase_lattice(L, value):
    L = neutral_increase(L,value)
    for i in range(value-1,0,-1):
        L = partial_arity_increase(L,value,i)
    return L

def neutral_increase(L, value):
    return  L.relabel({t:arity_increase(t, value) for t in L})

def initial_lattice(n):
    return sWeakOrderLatticeTrees([0 for i in range(n)])

def constructLatticeDoubling(s):
    n = len(s)
    L = initial_lattice(n)
    for i in range(n):
        v = s[i]
        for j in range(v):
            L = arity_increase_lattice(L,i+1)
    return L

# checked
# 012
# 001
# 002
# 003
# 011
# 021
# 022
# 023
# 024
# 0001
# 0002
# 0003
# 0101
# 0201
# 0202
# 0302
# 0303
# 0011
# 0021
# 0031
# 0032
# 0033
# 0111
# 0112
# 0212
# 0222
# 0223
# 01111
# 01112
def checkLatticeDoubling(s):
    L1 = sWeakOrderLatticeTrees(s)
    L2 = constructLatticeDoubling(s)
    return L1 == L2

def partial_arity_increase_inversions(s,L,asc):
    a,c = asc
    doubling = set(t for t in L if isDoublingAscent(s,dict(t), asc))
    Ld = poset_doubling(L, doubling)
    relabel = {}
    for t,d in Ld:
        if not t in doubling or d == 0:
            relabel[(t,d)] = t
        else:
            t2 = dict(t)
            t2[(c,a)] = t2.get((c,a),0) +1
            t2 = transitive_closure(s, t2)
            relabel[(t,d)] = tuple((k,t2[k]) for k in t2)
    return Ld.relabel(relabel)

def arity_increase_lattice_inversions(s, L, c):
    s[c-1]+=1
    for a in range(c-1,0,-1):
        L = partial_arity_increase_inversions(s,L,(a,c))
    return L

def initial_lattice_inversions(n):
    return Poset(([tuple()], [] ))

def constructLatticeDoublingInversions(s):
    n = len(s)
    L = initial_lattice_inversions(n)
    news = [0 for i  in range(n)]
    for i in range(n):
        v = s[i]
        for j in range(v):
            L = arity_increase_lattice_inversions(news,L,i+1)
    L = L.relabel({t:tree_from_inversions(s,dict(t)) for t in L})
    return L

def isDoublingAscent(s, inversions, asc):
    a,c = asc
    return isTreeAscentCondi(s,inversions, asc) and inversions.get((c,a),0) == s[c-1]-1 and isTreeAscentCondiii(s, inversions, asc)

# checked
# 012
# 001
# 002
# 003
# 011
# 021
# 022
# 023
# 024
# 0001
# 0002
# 0003
# 0101
# 0201
# 0202
# 0302
# 0303
# 0011
# 0021
# 0031
# 0032
# 0033
# 0111
# 0112
# 0212
# 0222
# 0223
# 01111
# 01112
def checkLatticeDoublingInversions(s):
    L1 = sWeakOrderLatticeTrees(s)
    L2 = constructLatticeDoublingInversions(s)
    return L1 == L2


### NEW GEOMETRIC IDEA WITH PROJECTIONS

def get_edges_poly(d):
    P = Poset((d,  lambda x,y: x.permutohedron_lequal(y)))
    pols = []
    for p1, p2 in P.cover_relations():
        pols.append(Polyhedron([d[p1],d[p2]]))
    return pols

# example edge 34

def select_edge34(perm):
    perm = list(perm)
    return perm.index(3) < perm.index(4)

A34 = Matrix(
[[1,1,1,1],
 [0,0,1,-1],
 [-1,1,0,0],
 [-2,0,1,1]
 ])

def project_edge34():
    P = [p for p in Permutations(4) if select_edge34(p)]
    S = [Matrix(list(p.inverse())) for p in P]
    Ainv = A34.inverse()
    S = [v*Ainv for v in S]
    #S = [Matrix([0,0] + list(x[0][2:])) for x in S]
    S = [Matrix(list(x[0][2:])) for x in S]
    #S = [x*A34 for x in S]
    S = [list(x[0]) for x in S]
    return dict(zip(P,S))

# example edge 45

def select_edge45(perm):
    perm = list(perm)
    return perm.index(4) < perm.index(5)


A45 = Matrix(
[[1,1,1,1,1],
 [0,0,0,1,-1],
 [-1,1,0,0,0],
 [-1,0,1,0,0],
 [-2,0,0,1,1]]
)

def project_edge45():
    P = [p for p in Permutations(5) if select_edge45(p)]
    S = [Matrix(list(p.inverse())) for p in P]
    Ainv = A45.inverse()
    S = [v*Ainv for v in S]
    #S = [Matrix([0,0] + list(x[0][2:])) for x in S]
    S = [Matrix(list(x[0][2:])) for x in S]
    #S = [x*A34 for x in S]
    S = [list(x[0]) for x in S]
    return dict(zip(P,S))

def projection(perms, direction):
    pass

# example edge 456

def select_edge456(perm):
    perm = list(perm)
    return perm.index(4) < perm.index(5) and perm.index(5) < perm.index(6)


A456 = Matrix(
[[1,1,1,1,1,1],
 [0,0,0,1,-1,0],
 [0,0,0,0,1,-1],
 [-1,1,0,0,0,0],
 [-1,0,1,0,0,0],
 [-3,0,0,1,1,1]]
)

def project_edge456():
    P = [p for p in Permutations(6) if select_edge456(p)]
    S = [Matrix(list(p.inverse())) for p in P]
    Ainv = A456.inverse()
    S = [v*Ainv for v in S]
    #S = [Matrix([0,0] + list(x[0][2:])) for x in S]
    S = [Matrix(list(x[0][-3:])) for x in S]
    #S = [x*A34 for x in S]
    S = [list(x[0]) for x in S]
    return dict(zip(P,S))

# example edge 34 in size 5

def select_edge34_5(perm):
    perm = list(perm)
    s3 = perm.index(3)
    s4 = perm.index(4)
    s5 = perm.index(5)
    #return s3 < s4 and not (s3 < s5 and s5 < s4)
    return s3 < s4

A34_5 = Matrix(
[[1,1,1,1,1],
 [0,0,1,-1,0],
 [-1,1,0,0,0],
 [-2,0,1,1,0],
 [-1,0,0,0,1]
])

def project_edge34_5():
    P = [p for p in Permutations(5) if select_edge34_5(p)]
    S = [Matrix(list(p.inverse())) for p in P]
    Ainv = A34_5.inverse()
    S = [v*Ainv for v in S]
    #S = [Matrix([0,0] + list(x[0][2:])) for x in S]
    S = [Matrix(list(x[0][-3:])) for x in S]
    #S = [x*A34 for x in S]
    S = [list(x[0]) for x in S]
    return dict(zip(P,S))

# example edge 23 in size 4

def select_edge23_4(perm):
    perm = list(perm)
    s2 = perm.index(2)
    s3 = perm.index(3)
    s4 = perm.index(4)
    return s2 < s3 and not (s2 < s4 and s4 < s3)

A23_4 = Matrix(
[[1,1,1,1],
 [0,1,-1,0],
 [-2,1,1,0],
 [-1,0,0,1],
])

def project_edge23_4():
    P = [p for p in Permutations(4) if select_edge23_4(p)]
    S = [Matrix(list(p.inverse())) for p in P]
    Ainv = A23_4.inverse()
    S = [v*Ainv for v in S]
    #S = [Matrix([0,0] + list(x[0][2:])) for x in S]
    S = [Matrix(list(x[0][-2:])) for x in S]
    #S = [x*A34 for x in S]
    S = [list(x[0]) for x in S]
    return dict(zip(P,S))



######## nu trees ##########

def sToPath(s):
    p = []
    for a in reversed(s):
        p.append(1)
        p.extend([0]*a)
    return tuple(p)

def path_matrix(p):
    n = sum(1 for i in p if i == 0) + 1
    m = sum(p) + 1
    M = [[True]*n for i in range(m)]
    i,j = 0,0
    for v in p:
        if v == 1:
            for k in range(i+1,n):
                M[j][k] = False
            j+=1
        else:
            i+=1
    return M

def is_compatible(P,p,M):
    i1,j1 = p
    for i2,j2 in P:
        if i2 < i1 and j2 < j1 and M[j2][i1]:
            return False
    return True

def readNodes(t,L, c = 0):
    L[c]+=1
    if len(t) == 0:
        return c
    c+=1
    for child in reversed(t):
        c = readNodes(child,L,c)
    return c

def STreeToNuTree(t):
    s = getSFromTree(t)
    path = sToPath(s)
    mat = path_matrix(path)
    L = [0]*(len(s)+1)
    readNodes(t,L)
    n = len(mat[0])
    m = len(mat)
    P = []
    for j in range(len(L)):
        k = L[j]
        for i in range(n-1,-1,-1):
            if k == 0:
                break
            if M[j][i] and is_compatible(P,(i,j),mat):
                P.append((i,j))
                k-=1
    return NuTree(path,tuple(P))



class NuTree():

    def __init__(self, path, points):
        self._path = path
        self._points = points
        n = sum(1 for i in p if i == 0) + 1
        m = sum(p) + 1
        M = [[False]*n for i in range(m)]
        for i,j in points:
            M[j][i] = True
        self._point_matrix = M
        self._n = n
        self._m = m
        self._construct_point_graph()

    def _construct_point_graph(self):
        G = Graph()
        for i,j in self._points:
            for k in range(j-1,-1,-1):
                if self._point_matrix[k][i]:
                    G.add_edge(((i,j),(i,k)))
                    break
            for k in range(i+1,self._n):
                if self._point_matrix[j][k]:
                    G.add_edge(((i,j),(k,j)))
                    break
        self._point_graph = G

    def __repr__(self):
        return str((self._path,self._points))

    def __eq__(self, other):
        return isinstance(other,NuTree) and self._path == other._path and self._points == other._points

    def __hash__(self):
        return hash((self._path, self._points))

    def _latex_(self):
        off = .1
        st = "\\begin{tikzpicture}\n"
        point_str = ""
        x,y = 0,0
        for v in self._path:
            if v == 1:
                x1 = x
                y1 = y+1
            else:
                x1 = x+1
                y1 = y
            st += "\\draw[line width = 4] (" + str(x) + "," + str(y) + ") -- (" + str(x1) + "," + str(y1) + ");\n"
            point_str += "\\draw[fill, radius=0.15] (" + str(x) + "," + str(y) +") circle;\n"
            x,y = x1,y1
        point_str += "\\draw[fill, radius=0.15] (" + str(x) + "," + str(y) +") circle;\n"
        st += point_str
        st+="\n"

        for i,j in self._points:
            st+= "\\draw[red, fill, radius=0.15] (" + str(i-off) + "," + str(j+off) + ") circle;\n"
        st+="\n"
        for p1,p2,l in self._point_graph.edges():
            st+= "\\draw[red, line width = 4] ("+ str(p1[0]-off) + "," + str(p1[1]+off) + ") -- (" + str(p2[0]-off) + "," + str(p2[1]+off) + ");\n"
        st+="\\end{tikzpicture}"
        return st


### test permutahedra

def is_pure_perm_interval(p1,p2): # on the inverse
    n = len(p1)
    I1 = set(p1.inversions())
    I2 = set(p2.inversions())
    if not I1.issubset(I2):
        return False
    I = I2.symmetric_difference(I1)
    for a in range(1,n+1):
        for b in range(a+1,n+1):
            for c in range(b+1, n+1):
                if (a,c) in I and (a,b) in I and not (b,c) in I:
                    return False
                if (a,c) in I and (b,c) in I and not (a,b) in I:
                    return False
                #if (b,c) in I and (a,b) in I and not (a,c) in I:
                    #return False
    return True

def pure_perm_intervals(n):
    P = list(Permutations(n))
    for p1 in P:
        for p2 in P:
            if is_pure_perm_interval(p1,p2):
                yield (p1.inverse(),p2.inverse())
