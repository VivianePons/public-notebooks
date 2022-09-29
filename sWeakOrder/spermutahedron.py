
from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.combinat.composition import Compositions
from sage.combinat.ordered_tree import LabelledOrderedTree, LabelledOrderedTrees
from sage.combinat.posets.lattices import LatticePoset
from sage.combinat.posets.posets import Poset
from sage.functions.other import sqrt
from sage.geometry.polyhedron.constructor import Polyhedron
from sage.matrix.constructor import Matrix
from sage.misc.cachefunc import cached_method
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.latex import latex
from sage.misc.lazy_attribute import lazy_attribute
from sage.misc.misc import subsets
from sage.misc.misc_c import prod
from sage.plot.line import line
from sage.rings.all import NN, ZZ, QQ
from sage.rings.polynomial.polynomial_ring_constructor import PolynomialRing
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.structure.element import Element
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation

from sage.sets.family import Family
from six import add_metaclass


@add_metaclass(InheritComparisonClasscallMetaclass)
class SDecreasingTree(Element):
    """
    EXAMPLES::

        sage: SDecreasingTree()
        []
        sage: leaf = LabelledOrderedTree([], label = "")
        sage: t1 = LabelledOrderedTree([leaf], label = 1)
        sage: t2 = LabelledOrderedTree([leaf, t1, leaf], label = 2); t2
        2[[], 1[[]], []]
        sage: t = SDecreasingTree(t2)
        sage: t
        2[[], 1[[]], []]
        sage: t.s()
        (0, 2)
        sage: t.inversion(2,1)
        1
        sage: s = (0,2)
        sage: d = {(2,1):1}
        sage: t = SDecreasingTree((s,d))
        sage: t
        2[[], 1[[]], []]

    """

    @staticmethod
    def __classcall_private__(cls, *args, **opts):
        """
        TESTS::

            sage: type(SDecreasingTree())
            <class '__main__.SDecreasingTrees_all_with_category.element_class'>

        """
        P = SDecreasingTrees_all()
        return P.element_class(P, *args, **opts)

    def __init__(self, parent, data = None):
        Element.__init__(self, parent)
        if data is None:
            self._tree = LabelledOrderedTree([], label= "")
            self._s = tuple()
            self._invs = dict()
        elif data in LabelledOrderedTrees():
            self._tree = data
            self._s = SDecreasingTrees.getSFromTree(data)
            self._invs = SDecreasingTrees.tree_inversions(data)
        else:
            s,invs = data
            self._s = tuple(s)
            self._tree = SDecreasingTrees.tree_from_inversions(s, invs)
            self._invs = SDecreasingTrees.tree_inversions(self._tree)

    def pre_order_traversal(self):
        r"""
        EXAMPLES::

            sage: t = SDecreasingTree(((0,2,2),{(3,1):1}))
            sage: list(t.pre_order_traversal())
            [3, 2, 1]
        """
        for node in self._tree.pre_order_traversal_iter():
            if len(node) != 0:
                yield node.label()

    @lazy_attribute
    def _nodes(self):
        """
        EXAMPLES::

            sage: t = SDecreasingTree(((0,2),{(2,1):1}))
            sage: [(i,t._nodes[i]) for i in range(1,t.size()+1)]
            [(1, 1[[]]), (2, 2[[], 1[[]], []])]

        """
        nodes = {}
        n = self.size()
        nodes[n] = self._tree
        for i in range(n,1,-1):
            for c in nodes[i]:
                if len(c) > 0:
                    nodes[c.label()] = c
        return nodes

    @lazy_attribute
    def _parents(self):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1}))._parents
            {1: 2}
        """
        parents = {}
        for n in self._nodes:
            for c in self._nodes[n]:
                if len(c) > 0:
                    parents[c.label()] = n
        return parents

    def node_parent(self, i):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).node_parent(1)
            2

        """
        return self._parents[i]

    def node(self,i):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).node(1)
            1[[]]
        """
        return self._nodes[i]

    def descendants(self,v):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2),{(2,1):1})).descendants(1))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).descendants(3))
            [1, 2]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).descendants(3))
            [2, 1]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).descendants(2))
            [1]
        """
        node = self.node(v)
        for c in node:
            if len(c) > 0:
                yield c.label()
                yield from self.descendants(c.label())

    def ascendants(self, v):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).ascendants(2))
            []
            sage: list(SDecreasingTree(((0,2),{(2,1):1})).ascendants(1))
            [2]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).ascendants(3))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).ascendants(2))
            [3]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).ascendants(1))
            [3]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).ascendants(3))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).ascendants(2))
            [3]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).ascendants(1))
            [2, 3]

        """
        if v == self.size():
            return
        w = self.node_parent(v)
        yield w
        yield from self.ascendants(w)

    def sub_tree_set(self,v):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).sub_tree_set(2)
            {1, 2}
            sage: SDecreasingTree(((0,2),{(2,1):1})).sub_tree_set(1)
            {1}
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).sub_tree_set(3)
            {1, 2, 3}
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).sub_tree_set(2)
            {2}
            sage: SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).sub_tree_set(3)
            {1, 2, 3}
            sage: SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).sub_tree_set(2)
            {1, 2}
        """
        s = {v}
        s.update(self.descendants(v))
        return s


    def middle_descendants(self, v):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).middle_descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2),{(2,1):2})).middle_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).middle_descendants(3))
            [2]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).middle_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).middle_descendants(3))
            [2, 1]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).middle_descendants(2))
            []

        """
        node = self.node(v)
        for c in node[1:-1]:
            if len(c) > 0:
                yield c.label()
                yield from self.descendants(c.label())

    def non_left_descendants(self,v):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).non_left_descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2),{(2,1):2})).non_left_descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2),{})).non_left_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).non_left_descendants(3))
            [2]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).non_left_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).non_left_descendants(3))
            [2, 1]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).non_left_descendants(2))
            [1]

        """
        node = self.node(v)
        for c in node[1:]:
            if len(c) > 0:
                yield c.label()
                yield from self.descendants(c.label())

    def non_right_descendants(self,v):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).non_right_descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2),{(2,1):2})).non_right_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2),{})).non_right_descendants(2))
            [1]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).non_right_descendants(3))
            [1, 2]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).non_right_descendants(2))
            []
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).non_right_descendants(3))
            [2, 1]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})).non_right_descendants(2))
            []

        """
        node = self.node(v)
        for c in node[:-1]:
            if len(c) > 0:
                yield c.label()
                yield from self.descendants(c.label())

    def tree(self):
        return self._tree

    def s(self):
        return self._s

    def inversion(self, b, a):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).inversion(2,1)
            1
        """
        return self._invs.get((b,a), 0)

    def version(self, b, a):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).version(3,2)
            1
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).version(3,1)
            2
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).version(2,1)
            2
        """
        return self.s()[b-1] - self.inversion(b,a)

    def inversions(self):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).inversions())
            [(2, 1)]
        """
        yield from self._invs

    def versions(self):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).versions())
            [(2, 1), (3, 1), (3, 2)]
        """
        n = self.size()
        for b in range(2,n+1):
            for a in range(1,b):
                if self.version(b,a) > 0:
                    yield (b,a)

    def to_s_permutation(self):
        def r(node):
            l = node.label()
            if len(node) > 0:
                yield from r(node[0])
                for i in range(1,len(node)):
                    yield l
                    yield from r(node[i])
        return list(r(self._tree))

    def tree_ascents(self):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).tree_ascents())
            [(1, 2)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).tree_ascents())
            [(1, 3), (2, 3)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_ascents())
            [(1, 3)]
            sage: list(SDecreasingTree(((0,2),{(2,1):2})).tree_ascents())
            []

        """
        s = self.s()
        n = self.size()
        for a in range(1,n):
            asc = self.tree_ascent(a)
            if asc != None:
                yield asc

    def nb_ascents(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):0,(3,1):0,(2,1):1})).nb_ascents()
            2
        """
        return len(list(self.tree_ascents()))

    def tree_ascent(self, a, check_right = True):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).tree_ascent(1)
            (1, 2)
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).tree_ascent(1)
            (1, 3)
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).tree_ascent(2)
            (2, 3)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_ascent(1)
            (1, 3)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_ascent(2)
            sage: SDecreasingTree(((0,2),{(2,1):2})).tree_ascent(1)

        """
        s = self.s()
        node = self.node(a)
        n = self.size()
        if check_right and s[a-1] > 0 and len(node[-1]) > 0:
            return None
        c,b = self.node_parent(a),a
        while self.node(c)[-1].label() == b and c != n:
            c,b = self.node_parent(c),c
        if self.inversion(c,a) < s[c-1]:
            return (a,c)
        return None

    def tree_descents(self):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).tree_descents())
            [(2, 1)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).tree_descents())
            [(3, 2)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_descents())
            [(2, 1), (3, 2)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1})).tree_descents())
            [(3, 1)]
            sage: list(SDecreasingTree(((0,2),{})).tree_descents())
            []

        """
        s = self.s()
        n = self.size()
        for a in range(1,n):
            desc = self.tree_descent(a)
            if desc != None:
                yield desc

    def tree_descent(self, a, check_left = True):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).tree_descent(1)
            (2, 1)
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).tree_descent(2)
            (3, 2)
            sage: SDecreasingTree(((0,2,2),{(3,2):1})).tree_descent(1)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_descent(1)
            (2, 1)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tree_descent(2)
            (3, 2)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1})).tree_descent(1)
            (3, 1)
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1})).tree_descent(2)
            sage: SDecreasingTree(((0,2),{})).tree_descent(1)

        """
        s = self.s()
        n = self.size()
        node = self.node(a)
        if check_left and s[a-1] > 0 and len(node[0]) > 0:
            return None
        c,b = self.node_parent(a),a
        while self.node(c)[0].label() == b and c != n:
            c,b = self.node_parent(c),c
        if self.inversion(c,a) > 0:
            return (c,a)
        return None

    def rotate_ascent(self, asc):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).rotate_ascent((1,2))
            2[[], [], 1[[]]]
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).rotate_ascent((2,3))
            3[[], [], 2[[], 1[[]], []]]

        """
        a,b = asc
        d = self._invs.copy()
        d[(b,a)] = d.get((b,a),0)+1
        for aa in self.non_left_descendants(a):
            d[(b,aa)] = d.get((b,aa),0)+1
        return SDecreasingTree((self.s(),d))

    def rotate_descent(self, desc):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).rotate_descent((2,1))
            2[1[[]], [], []]
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).rotate_descent((3,2))
            3[2[[], 1[[]], []], [], []]

        """
        b,a = desc
        d = self._invs.copy()
        d[(b,a)] = d.get((b,a),0)-1
        for aa in self.non_right_descendants(a):
            d[(b,aa)] = d.get((b,aa),0)-1
        return SDecreasingTree((self.s(),d))

    def rotate_right(self, i, check_right = True):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).rotate_right(1)
            2[[], [], 1[[]]]
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).rotate_right(2)
            3[[], [], 2[[], 1[[]], []]]
            sage: SDecreasingTree(((0,2,2),{(3,2):2,(3,1):1})).rotate_right(2)

        """
        asc = self.tree_ascent(i, check_right)
        if asc != None:
            return self.rotate_ascent(asc)
        return None

    def rotate_left(self, i, check_left = True):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).rotate_left(1)
            2[1[[]], [], []]
            sage: SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).rotate_left(2)
            3[2[[], 1[[]], []], [], []]
            sage: SDecreasingTree(((0,2,2),{(3,2):0,(3,1):0,(2,1):1})).rotate_left(2)

        """
        desc = self.tree_descent(i, check_left)
        if desc != None:
            return self.rotate_descent(desc)
        return None

    def sweak_succ(self):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).sweak_succ())
            [2[[], [], 1[[]]]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).sweak_succ())
            [3[[], 2[[], [], 1[[]]], []], 3[[], [], 2[[], 1[[]], []]]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).sweak_succ())
            [3[[], 2[[], [], []], 1[[]]]]

        TESTS::

            sage: all(set((a,b) for a,b in SDecreasingTrees(s).lattice().cover_relations()) == set((a,b) for a in SDecreasingTrees(s) for b in a.sweak_succ()) for s in SDecreasingTrees.some_s())
            True

        """
        for asc in self.tree_ascents():
            yield self.rotate_ascent(asc)

    def sweak_prec(self):
        """
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).sweak_prec())
            [2[1[[]], [], []]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).sweak_prec())
            [3[[], 2[1[[]], [], []], []], 3[2[[], 1[[]], []], [], []]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).sweak_prec())
            [3[[], 2[[], 1[[]], []], []], 3[2[[], [], []], 1[[]], []]]

        TESTS::

            sage: all(set((a,b) for a,b in SDecreasingTrees(s).lattice().cover_relations()) == set((a,b) for a in SDecreasingTrees(s) for b in a.sweak_succ()) for s in SDecreasingTrees.some_s())
            True

        """
        for desc in self.tree_descents():
            yield self.rotate_descent(desc)


    def size(self):
        """
        EXAMPLES::

            sage: SDecreasingTree().size()
            0

        """
        return len(self._s)

    def _repr_(self):
        """
        EXAMPLES::

            sage: SDecreasingTree()
            []
        """
        return str(self._tree)

    def __eq__(self, other):
        """
        EXAMPLES::

            sage: leaf = LabelledOrderedTree([], label = "")
            sage: t1 = LabelledOrderedTree([leaf], label = 1)
            sage: t2 = LabelledOrderedTree([leaf, t1, leaf], label = 2); t2
            2[[], 1[[]], []]
            sage: s = (0,2)
            sage: d = {(2,1):1}
            sage: SDecreasingTree((s,d)) == SDecreasingTree(t2)
            True

        """
        if not isinstance(other, SDecreasingTree):
            return False
        return self._tree == other._tree

    def __cmp__(self,other):
        if self._tree < other._tree:
            return -1
        elif self._tree == other._tree:
            return 0
        else:
            return 1

    def __ne__(self, other):
        return not self == other

    def __hash__(self):
        return hash(self._tree)

    def _latex_(self):
        r"""
        EXAMPLES::

            sage: s = (0,2)
            sage: d = {(2,1):1}
            sage: t = SDecreasingTree((s,d))
            sage: latex(t)
            { \newcommand{\nodea}{\node[draw,circle] (a) {$2$}
            ;}\newcommand{\nodeb}{\node[draw,circle] (b) {$$}
            ;}\newcommand{\nodec}{\node[draw,circle] (c) {$1$}
            ;}\newcommand{\noded}{\node[draw,circle] (d) {$$}
            ;}\newcommand{\nodee}{\node[draw,circle] (e) {$$}
            ;}\begin{tikzpicture}[auto]
            \matrix[column sep=.3cm, row sep=.3cm,ampersand replacement=\&]{
                     \& \nodea  \&         \\
             \nodeb  \& \nodec  \& \nodee  \\
                     \& \noded  \&         \\
            };
            <BLANKLINE>
            \path[ultra thick, red] (c) edge (d)
                (a) edge (b) edge (c) edge (e);
            \end{tikzpicture}}

        """
        return latex(self._tree)



    def sweak_lequal(self, other):
        """
        EXAMPLES::

            sage: SDecreasingTree(((0,2),{(2,1):1})).sweak_lequal(SDecreasingTree(((0,2),{(2,1):2})))
            True
            sage: SDecreasingTree(((0,2),{(2,1):1})).sweak_lequal(SDecreasingTree(((0,2),{})))
            False

        """
        if self.s() != other.s():
            return False
        for b,a in self.inversions():
            if other.inversion(b,a) < self.inversion(b,a):
                return False
        return True

    def sweak_join(self, other):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).sweak_join(SDecreasingTree(((0,2,2),{(2,1):2})))
            3[[], 2[[], [], 1[[]]], []]

        TESTS::

            sage: S = SDecreasingTrees((0,2,2))
            sage: L = S.lattice()
            sage: all(t1.sweak_join(t2) == L.join(t1,t2) for t1 in S for t2 in S)
            True

        """
        invs = {(b,a):max(self.inversion(b,a), other.inversion(b,a)) for b,a in set(self.inversions()).union(other.inversions())}
        invs = SDecreasingTrees.transitive_closure_inversions(self.s(), invs)
        return SDecreasingTree((self.s(), invs))

    def sweak_meet(self, other):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).sweak_meet(SDecreasingTree(((0,2,2),{(2,1):2})))
            3[2[1[[]], [], []], [], []]

        TESTS::

            sage: S = SDecreasingTrees((0,2,2))
            sage: L = S.lattice()
            sage: all(t1.sweak_meet(t2) == L.meet(t1,t2) for t1 in S for t2 in S)
            True
        """
        n = self.size()
        s = self.s()
        vers = {(b,a):max(self.version(b,a),other.version(b,a)) for b in range(2,n+1) for a in range(1,b) if self.version(b,a) > 0 or other.version(b,a) >0}
        vers = SDecreasingTrees.transitive_closure_inversions(self.s(),vers)
        invs = {(b,a): s[b-1] - vers.get((b,a),0) for b in range(2,n+1) for a in range(1,b)}
        return SDecreasingTree((s,invs))

    def reverse_tree(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).reverse_tree()
            3[[], 2[[], [], []], 1[[]]]
        """
        return SDecreasingTree((self.s(), {(b,a):self.version(b,a) for b,a in self.versions()}))

    def pure_intervals_starting(self, dimension = None):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2,2),{})).pure_intervals_starting())
            [(3[2[1[[]], [], []], [], []], ()),
             (3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[2[1[[]], [], []], [], []], ((1, 2), (2, 3)))]
            sage: list(SDecreasingTree(((0,2,2),{})).pure_intervals_starting(1))
            [(3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),))]
        """
        A = list(self.tree_ascents())
        if dimension is None or len(A) >= dimension:
            for subs in subsets(A):
                if dimension is None or len(subs) == dimension:
                    yield SPureIntervalFace(self, subs)

    def variations(self, other):
        if not self.sweak_lequal(other):
            return None
        return {(c,a):self.inversion(c,a) for c,a in other.inversions() if other.inversion(c,a) > self.inversion(c,a)}

    def essential_variations(self, other):
        s = self.s()
        n = self.size()
        var = self.variations(other)
        evar = {}
        for c,a in var:
            for b in range(a+1,c):
                if (c,b) in var and self.inversion(b,a) > 0 and self.inversion(b,a) < s[b-1]:
                    break
            else:
                evar[(c,a)] = self.inversion(c,a)

        return evar

    def is_plusone(self,other):
        return all(other.inversion(c,a) == self.inversion(c,a) + 1 for c,a in self.variations(other))

    def is_pure(self, other):
        if not self.is_plusone(other):
            return False
        evar = self.essential_variations(other)
        var = self.variations(other)

        for c,a in var:
            for b in range(a+1,c):
                if (b,a) in var and (not (c,b) in var or var[(c,b)] != var[(c,a)]):
                    return False

        for c,a in evar:
            for b in range(a+1,c):
                if (c,b) in evar and evar[(c,b)] == evar[(c,a)] and self.s()[b-1] > 0 and (not (b,a) in var or var[(b,a)] != 0):
                    return False

        return True

    # def is_pure2(self, other):
        # evar = self.variations(other)

        # for c,a in evar:
            # for b in range(a+1,c):
                # if (b,a) in evar and (not (c,b) in evar or evar[(c,b)] != evar[(c,a)]):
                    # return False
                # if (c,b) in evar and evar[(c,b)] == evar[(c,a)] and self.s()[b-1] > 0 and (not (b,a) in evar or evar[(b,a)] != 0):
                    # return False

        # return True


    def increase_arity(self, value):
        s = list(self.s())
        s[value-1] +=1
        return SDecreasingTree((s,self._invs))

    def select_double(self, c, a):
        return self.inversion(c,a) == self.s()[c-1] - 1 and all(self.inversion(b,a) == self.s()[b-1] for b in range(a+1,c) if self.inversion(c,b) == self.inversion(c,a))

    def subtree(self, nodes):
        """
        Return the standardized subtree of `self` by keeping only the given nodes
        """
        nodes = sorted(nodes)
        d = {v:i+1 for i,v in enumerate(nodes)}
        new_s = tuple(self.s()[i] for i in range(len(self.s())) if i+1 in d)
        return SDecreasingTree((new_s, {(d[b],d[a]): self.inversion(b,a) for b,a in self.inversions() if b in d and a in d}))

    ## S Tamari

    def is_s_tamari(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).is_s_tamari()
            True
            sage: SDecreasingTree(((0,2,2),{(3,1):1})).is_s_tamari()
            False
        """
        n = self.size()
        for a in range(1,n):
            for b in range(a+1,n):
                for c in range(b+1,n+1):
                    if self.inversion(c,a) > self.inversion(c,b):
                        return False
        return True

    def tamari_ascents(self):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).tamari_ascents())
            [(1, 2)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1})).tamari_ascents())
            [(1, 3), (2, 3)]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).tamari_ascents())
            [(2, 3)]
            sage: list(SDecreasingTree(((0,2),{(2,1):2})).tamari_ascents())
            []

        """
        n = self.size()
        for i in range(1,n):
            p = self.node_parent(i)
            if self.inversion(p,i) < self.s()[p-1]:
                yield (i,p)

    def s_tamari_succ(self):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTree(((0,2),{(2,1):1})).s_tamari_succ())
            [2[[], [], 1[[]]]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):1})).s_tamari_succ())
            [3[[], 2[[], [], 1[[]]], []], 3[[], [], 2[[], 1[[]], []]]]
            sage: list(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})).s_tamari_succ())
            [3[[], [], 2[[], [], 1[[]]]]]

        TESTS::

            sage: all(set((a,b) for a,b in SDecreasingTrees(s).s_tamari_lattice().cover_relations()) == set((a,b) for a in SDecreasingTrees(s).s_tamari_trees() for b in a.s_tamari_succ()) for s in SDecreasingTrees.some_s())
            True

        """
        for asc in self.tamari_ascents():
            yield self.rotate_ascent(asc)

    def nu_tree_traversal(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{})).nu_tree_traversal()
            [0, 1, 1, 1, 2, 2, 2, 3]

        """
        def read(t):
            nonlocal x
            yield x
            if len(t) > 0:
                x+=1
            for c in reversed(t):
                yield from read(c)
        x = 0
        return list(read(self._tree))

    def to_nu_tree(self):
        s = self.s()
        nu = tuple(reversed(s))
        NT = NuTrees(nu)

        L = self.nu_tree_traversal()
        n = NT.n()
        m = NT.m()
        P = []
        for j in L:
            start = n-1 if len(P) == 0 or P[-1][1] != j else P[-1][0] -1
            for i in range(start,-1,-1):
                if NT.is_above((i,j)) and all(NT.is_compatible(p,(i,j)) for p in P):
                    P.append((i,j))
                    break
        return NuTree(nu,P)

    ## Realizations

    def inversion_coordinates(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).inversion_coordinates()
            [0, 1, -1]
        """
        n = self.size()
        P = [0 for i in range(n)]
        for (b,a) in self.inversions():
            v = self.inversion(b,a)
            P[a-1] += v
            P[b-1] -= v
        return P

    def fixed_3d_coordinates(self, stretch = True):
        r"""
        EXAMPLES::

            sage: SDecreasingTree(((0,2,2),{(3,2):1})).fixed_3d_coordinates()
            [0, 1, -1]
        """
        n = self.size()
        s = self.s()
        P = [0 for i in range(n)]
        factor = prod(i for i in range(3,len(s))) if stretch else 3
        for (b,a) in self.inversions():
            k = factor*self.inversion(b,a)
            if b >= 3 and b < len(s):
                k+=s[b] if stretch else 0
                if self.inversion(b,a) < s[b-1]:
                    for c in range(1,b):
                        p1 = self.inversion(b+1,c)
                        p3 = self.inversion(b+1,b)
                        k+= (p1 - p3)
                else:
                    k+=s[b] if stretch else 0
            P[a-1] +=k
            P[b-1] -= k
        return P

    def get_point_cavern(self):
        def r(t,l,cavern):
            if len(t) == 0:
                return cavern
            v = 0
            for i in range(len(t)):
                c = t[i]
                if i != 0:
                    v+= cavern
                    cavern+=1
                cavern = r(c,l,cavern)
            l[t.label() - 1] = v
            return cavern
        l = [0 for i in range(self.size())]
        r(self._tree,l,1)
        return l




class SDecreasingTrees(UniqueRepresentation, Parent):
    """
    EXAMPLES::

        sage: SDecreasingTrees()
        S-decreasing trees
        sage: SDecreasingTrees((0,2,2))
        S-decreasing trees of (0, 2, 2)

    TESTS::

        sage: TestSuite(SDecreasingTrees()).run()
    """

    def __call__(self, *args, **keywords):

        if isinstance(args[0], SDecreasingTree):
            return args[0]

        return super(SDecreasingTrees, self).__call__(*args, **keywords)

    @staticmethod
    def __classcall_private__(cls, s=None):

        if s is None:
            return SDecreasingTrees_all()

        return SDecreasingTrees_s(tuple(s))

    @staticmethod
    def getSFromTree(tree):
        if len(tree) == 0:
            return tuple()
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

    @staticmethod
    def tree_inversions(tree):
        counts = {}
        d = {}
        def inversions_rec(tree):
            if len(tree) == 0:
                return
            b = tree.label()
            for c in counts:
                if c > b:
                    d[(c,b)] = counts[c]
            inversions_rec(tree[0])
            for i in range(1,len(tree)):
                counts[b] = counts.get(b,0) +1
                inversions_rec(tree[i])
        inversions_rec(tree)
        return d

    @staticmethod
    def tree_from_inversions(s, inversions, subset = None):
        if subset is None:
            n = len(s)
            subset = {i for i in range(1,n+1)}
        if len(subset) == 0:
            return LabelledOrderedTree([], label = "")
        c = max(subset)
        subsets = [set() for i in range(s[c-1]+1)]
        subset.remove(c)
        for a in subset:
            i = inversions.get((c,a),0)
            subsets[i].add(a)
        return LabelledOrderedTree([SDecreasingTrees.tree_from_inversions(s,inversions,Ci) for Ci in subsets], label = c)

    @staticmethod
    def transitive_closure_inversions(s, inversions):
        new_inversions = dict(inversions)
        n = len(s)
        changed = True
        while changed:
            changed = False
            for a in range(1,n-1):
                for b in range(a+1,n):
                    for c in range(b+1,n+1):
                        if (c,b) in new_inversions and (b,a) in new_inversions:
                            if not new_inversions.get((c,a),0) >= new_inversions[(c,b)]:
                                new_inversions[(c,a)] = new_inversions[(c,b)]
                                changed = True
        return new_inversions

    @staticmethod
    def from_s_permutation(perm):
        def r(perm):
            if len(perm) ==0:
                return LabelledOrderedTree([], label="")
            m = max(perm)
            pos = [i for i in range(len(perm)) if perm[i] == m]
            L = []
            deb = 0
            for i in pos:
                L.append(r(perm[deb:i]))
                deb = i+1
            L.append(r(perm[deb:]))
            return LabelledOrderedTree(L, label = m)
        return SDecreasingTree(r(perm))

    @staticmethod
    def some_s():
        return [(),
        (0,),
        (1,),
        (0,1),
        (0,2),
        (0,1,1),
        (0,2,2),
        (0,0,2),
        (0,1,1,1),
        (0,2,2,2),
        (0,3,3,3),
        (0,1,0,2),
        (0,1,1,2,2),
        (0,0,1,0,0,2)]



class SDecreasingTrees_all(DisjointUnionEnumeratedSets, SDecreasingTrees):

    def __init__(self):
        DisjointUnionEnumeratedSets.__init__(
            self, Family(Compositions(), lambda c : SDecreasingTrees_s(tuple(v-1 for v in c))),
            facade=True, keepkey=False, category=EnumeratedSets())

    def _repr_(self):
        return "S-decreasing trees"

    def _element_constructor_(self, data = None):
        return self.element_class(self, data)

    def __contains__(self, t):
        """
        TESTS::

            sage: SDecreasingTrees().an_element() in SDecreasingTrees()
            True

        """
        return isinstance(t, self.element_class)

    Element = SDecreasingTree

class SDecreasingTrees_s(SDecreasingTrees):
    """
        TESTS::

            sage: for s in SDecreasingTrees.some_s():
            ....:     TestSuite(SDecreasingTrees(s)).run()
    """

    def __init__(self, s):
        Parent.__init__(self, category=FiniteEnumeratedSets())
        self._s = tuple(s)
        self._get_point_default = lambda t: t.fixed_3d_coordinates()

    def __contains__(self,t):
        """
        TESTS::

            sage: SD = SDecreasingTrees((0,2))
            sage: SD.an_element() in SD
            True
            sage: SDecreasingTrees((0,3)).an_element() in SD
            False
        """
        return isinstance(t, self.element_class) and t.s() == self.s()

    def _repr_(self):
        return "S-decreasing trees of {}".format(self._s)

    def s(self):
        return self._s

    def n(self):
        return len(self._s)

    def cardinality(self):
        """
        EXAMPLES::

            sage: S = SDecreasingTrees((1,1,1))
            sage: S.cardinality()
            6
            sage: SDecreasingTrees((2,2,2)).cardinality()
            15

        """
        return NN(prod(sum(self._s[i:]) + 1 for i in range(len(self._s),0,-1)))

    def __iter__(self):
        """
        TESTS::

            sage: list(SDecreasingTrees(tuple()))
            [[]]
            sage: list(SDecreasingTrees((1,)))
            [1[[], []]]
            sage: list(SDecreasingTrees((2,)))
            [1[[], [], []]]
            sage: list(SDecreasingTrees((0,2)))
            [2[1[[]], [], []], 2[[], 1[[]], []], 2[[], [], 1[[]]]]

        """
        leaf = LabelledOrderedTree([],label="")
        s = self._s
        if self.n() == 0:
            yield SDecreasingTree(leaf)
            return
        def immutable_copy(tree):
            if tree == leaf:
                return tree
            return LabelledOrderedTree([immutable_copy(c) for c in tree], label = tree.label())
        def iter_trees(nodes, v):
            if v == 0:
                yield SDecreasingTree(immutable_copy(nodes[0]))
                return
            node = LabelledOrderedTree([leaf]*(s[v-1]+1), label = v)
            node = node.clone()
            nodes.append(node)
            for root in nodes[:-1]:
                for i in range(len(root)):
                    if root[i] == leaf:
                        root[i] = node
                        yield from iter_trees(nodes,v-1)
                        root[i] = leaf
            nodes.pop()
        node = LabelledOrderedTree([leaf]*(s[-1]+1), label = self.n())
        node = node.clone()
        yield from iter_trees([node], self.n()-1)

    def border_trees(self):
        """
        EXAMPLES::

            sage: list(SDecreasingTrees(tuple()).border_trees())
            [[]]
            sage: list(SDecreasingTrees((1,)).border_trees())
            [1[[], []]]
            sage: list(SDecreasingTrees((2,)).border_trees())
            [1[[], [], []]]
            sage: list(SDecreasingTrees((0,2)).border_trees())
            [2[1[[]], [], []], 2[[], [], 1[[]]]]
            sage: list(SDecreasingTrees((0,2,2)).border_trees())
            [3[2[[], [], []], 1[[]], []],
             3[2[[], [], []], [], 1[[]]],
             3[2[1[[]], [], []], [], []],
             3[2[[], 1[[]], []], [], []],
             3[2[[], [], 1[[]]], [], []],
             3[1[[]], 2[[], [], []], []],
             3[[], 2[[], [], []], 1[[]]],
             3[1[[]], [], 2[[], [], []]],
             3[[], 1[[]], 2[[], [], []]],
             3[[], [], 2[1[[]], [], []]],
             3[[], [], 2[[], 1[[]], []]],
             3[[], [], 2[[], [], 1[[]]]]]
            sage: list(SDecreasingTrees((0,1,1)).border_trees())
            [3[2[[], []], 1[[]]],
             3[2[1[[]], []], []],
             3[2[[], 1[[]]], []],
             3[1[[]], 2[[], []]],
             3[[], 2[1[[]], []]],
             3[[], 2[[], 1[[]]]]]

        """
        leaf = LabelledOrderedTree([],label="")
        s = self._s
        if self.n() == 0:
            yield SDecreasingTree(leaf)
            return
        def immutable_copy(tree):
            if tree == leaf:
                return tree
            return LabelledOrderedTree([immutable_copy(c) for c in tree], label = tree.label())
        def iter_trees(nodes, v, is_border = False):
            if v == 0:
                yield SDecreasingTree(immutable_copy(nodes[0]))
                return
            node = LabelledOrderedTree([leaf]*(s[v-1]+1), label = v)
            node = node.clone()
            nodes.append(node)
            if v == 1 and not is_border:
                root = nodes[0]
                root[0] = node
                yield from iter_trees(nodes,v-1,True)
                root[0] = leaf
                root[-1] = node
                yield from iter_trees(nodes,v-1,True)
                root[-1] = leaf
            else:
                for root in nodes[:-1]:
                    for i in range(len(root)):
                        if root[i] == leaf:
                            root[i] = node
                            new_is_border = is_border or( True if (i == 0 or i == len(root)-1) and root.label() == self.n() else False)
                            yield from iter_trees(nodes,v-1, new_is_border)
                            root[i] = leaf
            nodes.pop()
        node = LabelledOrderedTree([leaf]*(s[-1]+1), label = self.n())
        node = node.clone()
        yield from iter_trees([node], self.n()-1)

    @lazy_attribute
    def _parent_for(self):
        r"""
        The parent of the element generated by ``self``.

        TESTS::

            sage: SDecreasingTrees((0,2))._parent_for
            S-decreasing trees
        """
        return SDecreasingTrees_all()

    # This is needed because this is a facade parent via DisjointUnionEnumeratedSets
    @lazy_attribute
    def element_class(self):
        r"""
        TESTS::

            sage: SDecreasingTrees((0,2)).element_class
            <class '__main__.SDecreasingTrees_all_with_category.element_class'>
        """
        return self._parent_for.element_class

    def minimal_tree(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).minimal_tree()
            3[2[1[[]], [], []], [], []]
        """
        return SDecreasingTree((self.s(), {}))

    def maximal_tree(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).maximal_tree()
            3[[], [], 2[[], [], 1[[]]]]
        """
        s = self.s()
        return SDecreasingTree((s, {(b,a):s[b-1] for b in range(1,self.n()+1) for a in range(1,b)}))

    def poset(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2)).poset()
            Finite poset containing 3 elements
        """
        return Poset([list(self), lambda x,y: x.sweak_lequal(y)])

    def lattice(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2)).lattice()
            Finite lattice containing 3 elements
        """
        return LatticePoset(self.poset())

    def lattice_printer(self,**args):
        r"""

        """
        if "poset" in args:
            poset = args["poset"]
            del args["poset"]
        else:
            poset = self.poset()

        matrix = self.proj_matrix()
        return LatticePrinter(poset, lambda t: (Matrix(t.fixed_3d_coordinates())*matrix)[0], object_printer = lambda t: latex(t).replace("[auto]","[every node/.style={inner sep = 3pt}]"), **args)

    def lattice_doublings(self):
        s = self.s()
        initial = [0] * len(s)
        E = {SDecreasingTree((initial, {}))}
        yield Poset([E, lambda x,y: x.sweak_lequal(y)])
        for i in range(len(s)):
            c =  i+1
            for v in range(s[i]):
                E = {dt.increase_arity(c) for dt in E}
                for a in range(c-1,0,-1):
                    select = {dt for dt in E if dt.select_double(c,a)}
                    E.update(dt.rotate_ascent((a,c)) for dt in select)
                    yield Poset([list(E), lambda x,y: x.sweak_lequal(y)])


    def intervals(self):
        r"""
        EXAMPLES::

            sage: SD = SDecreasingTrees((0,2))
            sage: list(SD.intervals())
            [(2[1[[]], [], []], 2[1[[]], [], []]),
             (2[1[[]], [], []], 2[[], 1[[]], []]),
             (2[1[[]], [], []], 2[[], [], 1[[]]]),
             (2[[], 1[[]], []], 2[[], 1[[]], []]),
             (2[[], 1[[]], []], 2[[], [], 1[[]]]),
             (2[[], [], 1[[]]], 2[[], [], 1[[]]])]
        """
        L = list(self)
        return ((x,y) for x in L for y in L if x.sweak_lequal(y))

    ## S-Tamari

    def s_tamari_trees(self):
        r"""
        EXAMPLES::

            sage: list(SDecreasingTrees((0,2,2)).s_tamari_trees())
            [3[2[1[[]], [], []], [], []],
             3[2[[], 1[[]], []], [], []],
             3[2[[], [], 1[[]]], [], []],
             3[1[[]], 2[[], [], []], []],
             3[[], 2[1[[]], [], []], []],
             3[[], 2[[], 1[[]], []], []],
             3[[], 2[[], [], 1[[]]], []],
             3[1[[]], [], 2[[], [], []]],
             3[[], 1[[]], 2[[], [], []]],
             3[[], [], 2[1[[]], [], []]],
             3[[], [], 2[[], 1[[]], []]],
             3[[], [], 2[[], [], 1[[]]]]]
        """
        for tree in self:
            if tree.is_s_tamari():
                yield tree

    def s_catalan_cardinality(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_catalan_cardinality()
            12
            sage: all(len(list(SDecreasingTrees(s).s_tamari_trees())) == SDecreasingTrees(s).s_catalan_cardinality() for s in SDecreasingTrees.some_s())
            True

        """
        n = self.n()
        s = self.s()
        M = Matrix([[ZZ(binomial(sum(s[k] for k in range(j,n))+1, j-i +1)) for j in range(1,n)] for i in range(1,n)])
        return M.determinant()

    def s_tamari_poset(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_poset()
            Finite poset containing 12 elements
        """
        return Poset([list(self.s_tamari_trees()), lambda x,y: x.sweak_lequal(y)])

    def s_tamari_lattice(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_lattice()
            Finite lattice containing 12 elements
            sage: SDecreasingTrees((0,2,2)).s_tamari_lattice().is_sublattice(SDecreasingTrees((0,2,2)).lattice())
            True
        """
        return LatticePoset(self.s_tamari_poset())

    def s_tamari_lattice_printer(self):
        r"""

        """
        matrix = self.proj_matrix()
        return LatticePrinter(self.s_tamari_poset(), lambda t: (Matrix(t.fixed_3d_coordinates())*matrix)[0], object_printer = lambda t: latex(t).replace("[auto]","[every node/.style={inner sep = 3pt}]"))

    def nu_trees(self):
        r"""

        """
        return NuTrees(reversed(self.s()))

    def nu_tamari_poset(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_poset()
            Finite poset containing 12 elements
        """
        return self.nu_trees().nu_tamari_poset()

    def nu_tamari_lattice(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_lattice()
            Finite lattice containing 12 elements
            sage: SDecreasingTrees((0,2,2)).s_tamari_lattice().is_sublattice(SDecreasingTrees((0,2,2)).lattice())
            True
        """
        return self.nu_trees().nu_tamari_lattice()

    def nu_tamari_lattice_printer(self):
        r"""

        """
        return self.nu_trees().nu_tamari_lattice_printer()

    ## Realizations


    def proj_matrix(self):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).proj_matrix()
            [              -1               -1]
            [-1/2*sqrt(3) - 1             -3/2]
            [              -1               -2]
            sage: SDecreasingTrees((0,2,2,2)).proj_matrix()
            [   1    0    0]
            [   0    1    0]
            [   0    0    1]
            [-1/3 -1/3 -1/3]
            sage: SDecreasingTrees((0,2,2,2,2)).proj_matrix()
            Traceback (most recent call last):
            ...
            NotImplementedError: No projection matrix for n > 4
        """
        if self.n() == 3:
            return Matrix([[-ZZ(1),-ZZ(1)], [-(sqrt(3)/2+1), -ZZ(3)/ZZ(2)], [-ZZ(1), -ZZ(2)]])
        elif self.n() == 4:
            return Matrix([[1, 0, 0], [0, 1, 0], [0, 0, 1], [-ZZ(1)/3, -ZZ(1)/3, -ZZ(1)/3]])
        raise NotImplementedError("No projection matrix for n > 4")

    def edges_polyhedrons(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,1,1)).edges_polyhedrons()
            [A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in ZZ^3 defined as the convex hull of 2 vertices]
        """
        if get_point is None:
            get_point = self._get_point_default
        edges = []
        for tree in self:
            for tree2 in tree.sweak_succ():
                edges.append(Polyhedron([get_point(tree), get_point(tree2)]))
        return edges

    def s_tamari_edges_polyhedrons(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_edges_polyhedrons()
            [A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices,
             A 1-dimensional polyhedron in QQ^3 defined as the convex hull of 2 vertices]

        """
        pols = self.s_tamari_facet_polyhedrons(get_point)
        edges = set()
        for pol in pols:
            for f in pol.faces(1):
                edges.add(Polyhedron(f.vertices()))
        return list(edges)

    def projected_edge_plot(self, edge, **options):
        r"""
        EXAMPLES::

            sage: S = SDecreasingTrees((0,1,1))
            sage: E = S.edges_polyhedrons()
            sage: p = S.projected_edge_plot(E[0]); p
            Launched png viewer for Graphics object consisting of 1 graphics primitive
        """
        matrix = self.proj_matrix()
        proj = lambda x: list(Matrix(x)*matrix)[0]
        v = edge.vertices_list()
        v = [Matrix(x)*matrix for x in v]
        v = [list(p[0]) for p in v]
        return line(v, **options)

    def projected_sweak_plot(self, get_point = None, **options):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).projected_sweak_plot()
            Launched png viewer for Graphics object consisting of 20 graphics primitives
            sage: SDecreasingTrees((0,2,2,2)).projected_sweak_plot()
            Launched html viewer for Graphics3d Object
            sage: SDecreasingTrees((0,2,2,2)).projected_sweak_plot(get_point = lambda t:t.inversion_coordinates()) # broken polytopes
            Launched html viewer for Graphics3d Object
            sage: SDecreasingTrees((0,2,2,2)).projected_sweak_plot(get_point = lambda t:t.fixed_3d_coordinates(False)) # no stretch
            Launched html viewer for Graphics3d Object
        """
        if not "axes" in options:
            options["axes"] = False
        if not "aspect_ratio" in options:
            options["aspect_ratio"] = 1
        edges = self.edges_polyhedrons(get_point)
        P = [self.projected_edge_plot(e, **options) for e in edges]
        return sum(P)

    def projected_s_tamari_plot(self, get_point = None, **options):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).projected_s_tamari_plot()
            Launched png viewer for Graphics object consisting of 16 graphics primitives
            sage: SDecreasingTrees((0,2,2,2)).projected_s_tamari_plot()
            Launched html viewer for Graphics3d Object
        """
        if not "axes" in options:
            options["axes"] = False
        if not "aspect_ratio" in options:
            options["aspect_ratio"] = 1
        edges = self.s_tamari_edges_polyhedrons(get_point)
        P = [self.projected_edge_plot(e, **options) for e in edges]
        return sum(P)

    def projected_both_plot(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).projected_both_plot()
            Launched png viewer for Graphics object consisting of 36 graphics primitives
            sage: SDecreasingTrees((0,2,2,2)).projected_both_plot()
            Launched html viewer for Graphics3d Object
        """
        p1 = self.projected_sweak_plot(color="blue", get_point = get_point)
        p2 = self.projected_s_tamari_plot(color = "red", get_point = get_point)
        return p1 + p2


    def convex_hull(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2)).convex_hull()
            A 1-dimensional polyhedron in ZZ^2 defined as the convex hull of 2 vertices
            sage: SDecreasingTrees((0,2,2)).convex_hull()
            A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 6 vertices
        """
        if get_point is None:
            get_point = self._get_point_default
        return Polyhedron([get_point(t) for t in self.border_trees()])

    @cached_method
    def filtered_facet_border_inequalities(self, validator = None, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).filtered_facet_border_inequalities()
            {An inequality (0, -1, -1) x + 0 >= 0,
             An inequality (0, 0, -1) x + 0 >= 0,
             An inequality (0, -1, 0) x + 2 >= 0,
             An inequality (0, 1, 0) x + 2 >= 0,
             An inequality (0, 0, 1) x + 4 >= 0,
             An inequality (0, 1, 1) x + 4 >= 0}
        """
        if self.n() < 3:
            return
        if get_point is None:
            get_point = self._get_point_default
        if validator is None:
            validator = lambda x: True
        L = [f for f in SPureIntervalFaces(self.s()).border_faces(self.n() - 2) if validator(f)]
        border_ieqs = set()
        ieqs = self.convex_hull(get_point).inequalities()
        for face in L:
            pol2 = Polyhedron([get_point(t) for t in face.interval_trees()])
            border_ieqs.update([i for i in ieqs if all(not i.interior_contains(v) for v in pol2.vertices())])
        return border_ieqs

    @cached_method
    def s_tamari_border_inequalities(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_border_inequalities()
            {An inequality (0, -1, -1) x + 0 >= 0,
             An inequality (0, 0, -1) x + 0 >= 0,
             An inequality (0, -1, 0) x + 2 >= 0,
             An inequality (0, 0, 1) x + 4 >= 0,
             An inequality (0, 1, 1) x + 4 >= 0}
        """
        return self.filtered_facet_border_inequalities(validator = lambda x: x.is_s_tamari_valid())

    def facet_polyhedrons(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).facet_polyhedrons()
            [A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 4 vertices,
             A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 5 vertices,
             A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 5 vertices,
             A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 4 vertices,
             A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 5 vertices,
             A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 5 vertices]

        """
        return [f.s_weak_polyhedron(get_point) for f in SPureIntervalFaces(self.s()).facets()]

    def s_tamari_facet_polyhedrons(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SDecreasingTrees((0,2,2)).s_tamari_facet_polyhedrons()
            [A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 5 vertices,
             A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 4 vertices,
             A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 4 vertices,
             A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 5 vertices,
             A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 4 vertices]
        """
        return [f.s_tamari_polyhedron(get_point) for f in SPureIntervalFaces(self.s()).facets() if f.is_s_tamari_valid()]

@add_metaclass(InheritComparisonClasscallMetaclass)
class SPureIntervalFace(Element):

    COLSEP = .1

    @staticmethod
    def __classcall_private__(cls, *args, **opts):
        """
        TESTS::

            sage: type(SPureIntervalFace(SDecreasingTree(),[]))
            <class '__main__.SPureIntervalFaces_all_with_category.element_class'>

        """
        P = SPureIntervalFaces()
        return P.element_class(P, *args, **opts)

    def __init__(self,parent, t, ascents):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)])
            (3[2[[], [], []], 1[[]], []], ((2, 3),))

        """
        Element.__init__(self, parent)
        self._tree_min = t
        self._ascents = tuple(ascents)
        self._marked = {i for (i,j) in self._ascents}
        invs = {(b,a):t.inversion(b,a) for (b,a) in t.inversions()}

        for a,b in ascents:
            invs[(b,a)] = invs.get((b,a),0) +1

        invs = SDecreasingTrees.transitive_closure_inversions(t.s(),invs)
        self._tree_max = SDecreasingTree((t.s(), invs))

    def s(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).s()
            (0, 2, 2)
        """
        return self._tree_min.s()

    def size(self):
        """
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).size()
            3

        """
        return self._tree_min.size()

    def tree_min(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).tree_min()
            3[2[[], [], []], 1[[]], []]
        """
        return self._tree_min

    def tree_max(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).tree_max()
            3[[], 2[[], [], 1[[]]], []]
        """
        return self._tree_max

    def ascents(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).ascents()
            ((2, 3),)
        """
        return self._ascents

    def inversions_min(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversions_min())
            [(2, 1), (3, 1)]
        """
        return self._tree_min.inversions()

    def inversions_max(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversions_max())
            [(3, 2), (3, 1), (2, 1)]
        """
        return self._tree_max.inversions()

    def varies(self,b,a):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).varies(3,1)
            False
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).varies(3,2)
            True

        """
        return self.inversion_min(b,a) < self.inversion_max(b,a)

    def variation_path(self, c,a):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).variation_path(3,2)
            [3, 2]
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3),(1,3)]).variation_path(3,1)
            [3, 1]
        """
        if not self.varies(c,a):
            return None
        chain = [c]
        ev = set(self.essential_variations().items())
        v = self.inversion_min(c,a)
        for b in range(c-1,a,-1):
            if ((c,b),v) in ev and self.inversion_min(b,a) < self.s()[b-1]:
                chain.append(b)
        if ((c,a),v) in ev:
            chain.append(a)
        return chain
        # s = self.s()
        # chain = [b]
        # if (a,b) in self.ascents():
            # chain.append(a)
            # return chain
        # vba = self.inversion_min(b,a)
        # for bi in range(b-1,a,-1):
            # v = self.inversion_min(b,bi)
            # if v == vba and s[bi-1] > 0 and (bi,b) in self.ascents():
                # chain.append(bi)
                # vbia = self.inversion_min(bi,a)
                # if vbia < s[bi-1] and (vbia > 0 or (a,bi) in self.ascents()):
                    # chain.append(a)
                    # return chain
                # b = bi
                # vba = 0
        # return None

    def is_variation_path(self,p):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).is_variation_path([3,2])
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).is_variation_path([3,1])
            False
        """
        s = self.s()
        b = p[0]
        a = p[-1]
        if not self.varies(b,a):
            return False
        if self.inversion_min(p[0],p[1]) != self.inversion_min(b,a):
            return False
        for i in range(1,len(p)-2):
            if self.inversion_min(p[i],p[i+1]) != 0 or (p[i+1],p[i]) not in self.ascents():
                return False
        if len(p) > 2:
            if not self.inversion_min(p[-2],p[-1]) < s[p[-2]-1]:
                return False
            if self.inversion_min(p[-2],p[-1]) == 0 and not (p[-1],p[-2]) in self.ascents():
                return False
        return True

    def inversion_min(self,b,a):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversion_min(3,1)
            1
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversion_min(3,2)
            0
        """
        return self._tree_min.inversion(b,a)

    def inversion_max(self,b,a):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversion_max(3,1)
            1
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).inversion_max(3,2)
            1

        """
        return self._tree_max.inversion(b,a)

    def dimension(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).dimension()
            1
        """
        return len(self._ascents)

    def is_full_dimensional(self):
        return self.dimension() == self.size() - 1

    def __repr__(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)])
            (3[2[[], [], []], 1[[]], []], ((2, 3),))
        """
        return str((self._tree_min, self._ascents))

    def _get_ascents_letters(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)])._get_ascents_letters())
            ['b']

        """
        n = 0
        for t in self.tree_min().tree().pre_order_traversal_iter():
            if t.label() in self._marked:
                yield "".join((chr(ord(x) + 49) for x in str(n)))
            n+=1


    def __eq__(self, other):
        r"""
        TESTS::

            EXAMPLES::

                sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]) == SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)])
                True
                sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]) == SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(1,3)])
                False
        """
        return isinstance(other, SPureIntervalFace) and other.ascents() == self.ascents() and other.tree_min() == self.tree_min()

    def __hash__(self):
        return hash((self.ascents(), self.tree_min()))

    def _latex_(self):
        r"""
        TESTS::

            sage: print(latex(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)])))
            { \newcommand{\nodea}{\node[draw,circle,fill=white] (a) {$3$}
            ;}\newcommand{\nodeb}{\node[draw,circle,fill=red!50] (b) {$2$}
            ;}\newcommand{\nodec}{\node[draw,circle,fill=white] (c) {$$}
            ;}\newcommand{\noded}{\node[draw,circle,fill=white] (d) {$$}
            ;}\newcommand{\nodee}{\node[draw,circle,fill=white] (e) {$$}
            ;}\newcommand{\nodef}{\node[draw,circle,fill=white] (f) {$1$}
            ;}\newcommand{\nodeg}{\node[draw,circle,fill=white] (g) {$$}
            ;}\newcommand{\nodeh}{\node[draw,circle,fill=white] (h) {$$}
            ;}\begin{tikzpicture}[auto]
            \matrix[column sep=0.1cm, row sep=.3cm,ampersand replacement=\&]{
                     \&         \&         \& \nodea  \&         \\
                     \& \nodeb  \&         \& \nodef  \& \nodeh  \\
             \nodec  \& \noded  \& \nodee  \& \nodeg  \&         \\
            };

            \path[ultra thick, red] (b) edge (c) edge (d) edge (e)
                (f) edge (g)
                (a) edge (b) edge (f) edge (h);
            \end{tikzpicture}}
        """
        L = self._tree_min._latex_()
        L = L.replace("column sep=.3cm","column sep="+str(self.COLSEP)+"cm")
        L = L.replace("[draw,circle]","[draw,circle,fill=white]")
        for l in self._get_ascents_letters():
            rfrom = "\\node" + l +"}{\\node[draw,circle,fill=white]"
            rto = "\\node" + l +"}{\\node[draw,circle,fill=red!50]"
            L = L.replace(rfrom, rto)
        return L

    def is_border_face(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})),[(2,3)]).is_border_face()
            False
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2)]).is_border_face()
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).is_border_face()
            False
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1})),[(2,3)]).is_border_face()
            True
        """
        if len(self.tree_min().tree()[-1]) >0:
            return True
        def unmarked_left(t):
            if len(t) == 0:
                return False
            if not t.label() in self._marked:
                return True
            return unmarked_left(t[0])
        return unmarked_left(self.tree_min().tree()[0])


    def interval_trees(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2)]).interval_trees())
            [3[2[1[[]], [], []], [], []], 3[2[[], 1[[]], []], [], []]]
            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).interval_trees())
            [3[2[1[[]], [], []], [], []],
             3[1[[]], 2[[], [], []], []],
             3[[], 2[1[[]], [], []], []],
             3[[], 2[[], 1[[]], []], []],
             3[2[[], 1[[]], []], [], []]]
        """
        t = self.tree_min()
        maxt = self.tree_max()
        L = [t]
        seen = set()
        while len(L) > 0:
            tt = L.pop()
            if not tt in seen:
                seen.add(tt)
                yield tt
                for v in tt.sweak_succ():
                    if v.sweak_lequal(maxt):
                        L.append(v)

    def interval_as_poset(self):
        return Poset((list(self.interval_trees()), lambda x,y : x.sweak_lequal(y)))

    def lattice_printer(self,**args):
        r"""

        """
        poset = self.interval_as_poset()

        nodes = set(v for a in self.ascents() for v in a)

        st = self.tree_min().subtree(nodes)

        matrix = SDecreasingTrees(st.s()).proj_matrix()
        return LatticePrinter(poset, lambda t: (Matrix(t.subtree(nodes).fixed_3d_coordinates())*matrix)[0], object_printer = lambda t: latex(t).replace("[auto]","[every node/.style={inner sep = 3pt}]"), **args)


    def include_face(self, other):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).include_face(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2)]))
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).include_face(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1})),[(1,3)]))
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).include_face(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1})),[(1,3),(2,3)]))
            False
        """
        return self.tree_min().sweak_lequal(other.tree_min()) and other.tree_max().sweak_lequal(self.tree_max())

    def include_tree(self, t):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).include_tree(SDecreasingTree(((0,2,2),{(3,2):1})))
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).include_tree(SDecreasingTree(((0,2,2),{(3,2):2})))
            False
        """
        return self.tree_min().sweak_lequal(t) and t.sweak_lequal(self.tree_max())

    def sub_faces(self, dimension = None):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).sub_faces())
            [(3[2[1[[]], [], []], [], []], ()),
             (3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[2[1[[]], [], []], [], []], ((1, 2), (2, 3))),
             (3[1[[]], 2[[], [], []], []], ()),
             (3[1[[]], 2[[], [], []], []], ((1, 3),)),
             (3[[], 2[1[[]], [], []], []], ()),
             (3[[], 2[1[[]], [], []], []], ((1, 2),)),
             (3[[], 2[[], 1[[]], []], []], ()),
             (3[2[[], 1[[]], []], [], []], ()),
             (3[2[[], 1[[]], []], [], []], ((2, 3),))]
            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).sub_faces(1))
            [(3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[1[[]], 2[[], [], []], []], ((1, 3),)),
             (3[[], 2[1[[]], [], []], []], ((1, 2),)),
             (3[2[[], 1[[]], []], [], []], ((2, 3),))]
            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).sub_faces(0))
            [(3[2[1[[]], [], []], [], []], ()),
             (3[1[[]], 2[[], [], []], []], ()),
             (3[[], 2[1[[]], [], []], []], ()),
             (3[[], 2[[], 1[[]], []], []], ()),
             (3[2[[], 1[[]], []], [], []], ())]
        """
        for t in self.interval_trees():
            for f in t.pure_intervals_starting(dimension):
                if self.include_face(f):
                    yield f

    def sub_facets(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)]).sub_facets())
            [(3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[1[[]], 2[[], [], []], []], ((1, 3),)),
             (3[[], 2[1[[]], [], []], []], ((1, 2),)),
             (3[2[[], 1[[]], []], [], []], ((2, 3),))]
        """
        yield from self.sub_faces(self.dimension() - 1)

    def sub_facets_ordered_partitions(self):
        nn = set(range(1,self.size()+1))

        # Type 0
        for a in range(1, self.size()):
            d = set(self.tree_min().descendants(a))
            d.add(a)
            yield OrderedSetPartition([d, nn.difference(d)])

        # Type 1
        for a in range(1, self.size()):
            for path in self.left_movable_paths(a):
                Tclosure = set(path)
                Tclosure.update(j for p in path for j in self.tree_min().middle_descendants(p))
                yield OrderedSetPartition([nn.difference(Tclosure),Tclosure])

        # Type 2
        for a in range(1,self.size()):
            for p1 in self.movable_descendants(a):
                if self.inversion_min(a,p1) == self.s()[a-1] - 1:
                    for path in self.left_movable_paths(p1):
                        d = set(self.tree_min().descendants(a))
                        d.add(a)
                        Tclosure = set(path)
                        Tclosure.update(j for p in path for j in self.tree_min().middle_descendants(p))
                        J = d.difference(Tclosure)
                        yield OrderedSetPartition([J, nn.difference(J)])


    def sub_face_to_set_partition(self, f):
        r"""
        EXAMPLES::

            sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{})),[(1,2),(2,3)])
            sage: [F.sub_face_to_set_partition(f) for f in F.sub_faces()]
            [[{1}, {2}, {3}],
             [{1, 2}, {3}],
             [{1}, {2, 3}],
             [{1, 2, 3}],
             [{1}, {3}, {2}],
             [{1, 3}, {2}],
             [{3}, {1}, {2}],
             [{3}, {1, 2}],
             [{3}, {2}, {1}],
             [{2}, {1}, {3}],
             [{2, 3}, {1}]]
        """
        def subset_compare(s1,s2):
            if s1 == s2:
                return 0
            if any(f.inversion_min(b,a) > self.inversion_min(b,a) for a in s1 for b in s2 if b > a):
                return 1
            return -1
        n = self.size()
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
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).intersection(SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1})), [(1,3),(2,3)]))
            (3[[], 2[[], [], 1[[]]], []], ((1, 3),))

        """
        tjoin = self.tree_min().sweak_join(f.tree_min())
        tmeet = self.tree_max().sweak_meet(f.tree_max())
        if tjoin.sweak_lequal(tmeet):
            return SPureIntervalFace(tjoin, [(a,b) for (a,b) in tjoin.tree_ascents() if tjoin.inversion(b,a) < tmeet.inversion(b,a)])
        else:
            return None


    def tree_set_partition(self, t, i):
        r"""
        EXAMPLES::

            sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
            sage: F.tree_set_partition(SDecreasingTree(((0,2,2),{(3,2):2, (3,1):2, (2,1):1})),2)
            [{3}, {1, 2}]

        """
        def started_moving(t,a):
            if a == self.size():
                return False
            a,b = self.tree_min().tree_ascent(a)
            return t.inversion(b,a) > self.tree_min().inversion(b,a)
        n = self.dimension() + 1
        T = self.tree_min()
        s = self.s()
        possible_moves = {j for j in range(i+1,n+1) if self.varies(j,i)}
        moves = {j for j in possible_moves if t.inversion(j,i) != self.inversion_min(j,i)}
        parents = [j for j in t.ascendants(i) if j in possible_moves]
        parent = min(parents)
        #parent = T.tree_ascent(i)

        #print(parent)

        if not parent in moves:
            A = t.sub_tree_set(i).intersection(T.sub_tree_set(i))
            if t.inversion(parent,i) == 0:
                t0 = t.rotate_left(i, False)
                if t0 != None and self.include_tree(t0):
                    #moved_parents = [p for p in parents if any(t.inversion(j,p) != T.inversion(j,p) for j in range(p+1,n+1))]
                    moved_parents = [p for p in parents if started_moving(t,p)]
                    #print(moved_parents)
                    moved_parent = min(moved_parents)
                    unmoved_parents = [p for p in parents if not p in moved_parents]
                    unmoved_parent = min(unmoved_parents)
                    A.update(j for j in t.sub_tree_set(unmoved_parent).intersection(T.sub_tree_set(unmoved_parent)) if j not in t.sub_tree_set(moved_parent).intersection(T.sub_tree_set(moved_parent)))
            B = {j for j in range(1,n+1) if not j in A}
        else:
            #print("test")
            B = t.sub_tree_set(i).intersection(T.sub_tree_set(i))
            if t.inversion(parent,i) == s[parent-1]:
                t0 = t.rotate_right(i, False)
                #print(t0)
                if t0 != None and self.include_tree(t0):
                    #unmoved_parents = [p for p in parents if all(t.inversion(j,p) == T.inversion(j,p) for j in range(p+1,n+1))]
                    unmoved_parents = [p for p in parents if not started_moving(t,p)]
                    unmoved_parent = min(unmoved_parents)
                    #print(unmoved_parent)
                    B.update(j for j in range(1,n+1) if j not in t.sub_tree_set(unmoved_parent).intersection(T.sub_tree_set(unmoved_parent)))
            A = {j for j in range(1,n+1) if not j in B}
        return OrderedSetPartition([A,B])

    def tree_facet_ordered_sets(self,t):
        r"""
        EXAMPLES::

            sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
            sage: list(F.tree_facet_ordered_sets(SDecreasingTree(((0,2,2),{(3,2):2, (3,1):2, (2,1):1}))))
            [[{1}, {2, 3}], [{3}, {1, 2}]]

        TESTS::

            sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
            sage: t = SDecreasingTree(((0,2,2),{(3,2):2, (3,1):2, (2,1):1}))
            sage: set(F.tree_facet_ordered_sets(t)) == set(F.tree_set_partition(t,i) for i in range(1,3))
            True

        """
        for ff in self.sub_facets():
            if ff.include_tree(t):
                yield self.sub_face_to_set_partition(ff)

    def f_vector(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).f_vector()
            (1, 5, 5, 1)
        """
        v = [0] * (self.dimension()+2)
        v[0] = 1
        for f in self.sub_faces():
            d = f.dimension()+1
            v[d]+=1
        return tuple(v)

    def ascentope(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).ascentope()
            A 2-dimensional polyhedron in RDF^3 defined as the convex hull of 5 vertices
        """
        ieqs = []
        n = self.size()
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
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).get_vertex(SDecreasingTree(((0,2,2),{(3,2):1,(3,1):1,(2,1):2})))
            A vertex at (2.0, 1.0, 3.0)

        TESTS::

            sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
            sage: Polyhedron([F.get_vertex(t) for t in F.interval_trees()]) == F.ascentope()
            True

        """
        n = self.size()
        eqns = []
        for i in range(1,n):
            sp = self.tree_set_partition(t,i)
            A = sp[0]
            ieq = [0]*(n+1)
            ieq[0] = -len(A)*(len(A) +1)/2
            for i in A:
                ieq[i] = 1
            eqns.append(ieq)
        eq = [1]*(n+1)
        eq[0] = -n*(n+1)/2
        eqns.append(eq)
        return Polyhedron(eqns = eqns).vertices()[0]


    def variations(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).variations()
            {(3, 2): 1, (3, 1): 1, (2, 1): 1}

        """
        return self.tree_min().variations(self.tree_max())

    def essential_variations(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).essential_variations()
            {(3, 2): 1, (2, 1): 1}

        """
        return self.tree_min().essential_variations(self.tree_max())
        # s = self.s()
        # n = self.size()
        # t1 = self.tree_min()
        # t2 = self.tree_max()
        # var = self.variations()

        # # get essential variations
        # maxvar = dict()
        # for c in range(2,n+1):
            # for a in range(c-1,0,-1):
                # if (c,a) in var:
                    # ca = var[(c,a)]
                    # for b in range(a+1,c):
                        # if (c,b) in maxvar:
                            # ba = t1.inversion(b,a)
                            # cb = maxvar[(c,b)]
                            # if ca == cb and ba > 0 and ba < s[b-1]:
                                # break
                    # else:
                        # maxvar[(c,a)] = ca
        # return maxvar

    def is_essential_variation(self, c, a):
        r"""
        EXAMPLES::

            sage: f = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
            sage: f.is_essential_variation(2,1)
            True
            sage: f.is_essential_variation(3,2)
            True
            sage: f.is_essential_variation(3,1)
            False
        """

        if not self.varies(c,a):
            return False

        for b in range(a+1,c):
            if self.varies(c,b) and self.inversion_min(b,a) > 0 and self.inversion_min(b,a) < self.s()[b-1]:
                return False
        return True

    def right_variations(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).right_variations()
            {(3, 1)}

        """
        S = set()
        for c,b in self.essential_variations():
            for a in range(1,b):
                ba = self.inversion_min(b,a)
                if self.varies(b,a) and ba > 0 and ba < self.s()[b-1]:
                    S.add((c,a))
        return S

    def is_s_tamari_valid(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)]).is_s_tamari_valid()
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):2, (2,1):2})),[(2,3)]).is_s_tamari_valid()
            True
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):2})),[(1,3)]).is_s_tamari_valid()
            False
            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1, (2,1):2})),[(2,3)]).is_s_tamari_valid()
            False

        """
        n = self.size()
        s = self.s()
        for c in range(3,n+1):
            for b in range(2,c):
                for a in range(1,b):
                    if self.inversion_max(c,b) < self.inversion_max(c,a) or self.inversion_min(c,b) < self.inversion_min(c,a):
                        if self.inversion_min(c,b) < s[c-1]-1 or self.inversion_max(c,b) < s[c-1]:
                            return False
        return True

    def s_weak_polyhedron(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1, (2,1):2})),[(2,3),(1,3)]).s_weak_polyhedron()
            A 2-dimensional polyhedron in ZZ^3 defined as the convex hull of 4 vertices
        """
        if get_point is None:
            get_point = SDecreasingTrees(self.s())._get_point_default
        return Polyhedron([get_point(t) for t  in self.interval_trees()])


    def s_tamari_polyhedron(self, get_point = None):
        r"""
        EXAMPLES::

            sage: SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,1):1, (2,1):1, (3,2):1})),[(2,3),(1,2)]).s_tamari_polyhedron()
            A 2-dimensional polyhedron in QQ^3 defined as the convex hull of 4 vertices

        """
        if get_point is None:
            get_point = SDecreasingTrees(self.s())._get_point_default
        facets = [ft for ft in self.sub_facets() if ft.is_s_tamari_valid()]
        borders = SDecreasingTrees(self.s()).s_tamari_border_inequalities()
        v_ieqs = []
        if len(facets) > 0:
            pol = self.s_weak_polyhedron(get_point)
            ieqs = pol.inequalities()
            for face in facets:
                pol2 = Polyhedron([get_point(t) for t in face.interval_trees()])
                v_ieqs.extend([i for i in ieqs if all(not i.interior_contains(v) for v in pol2.vertices())])
            v_ieqs.extend(borders)
            return Polyhedron(ieqs = v_ieqs, eqns = pol.equations())
        return None


    def movable_descendants(self, c):
        root = self.tree_min().node(c)
        L = root[:-1]
        while len(L) >0 :
            node = L.pop()
            if len(node) > 0:
                yield node.label()
                if len(node) > 1:
                    L.append(node[-2])

    def left_movable_descendants(self, c):
        root = self.tree_min().node(c)
        L = [root[0]]
        while len(L) >0 :
            node = L.pop()
            if len(node) > 0:
                yield node.label()
                if len(node) > 1:
                    L.append(node[-2])

    def left_movable_paths(self, i = None):
        if i is None:
            for i in range(1,F.size()):
                yield from self.left_movable_paths(i)
            return
        root = self.tree_min().node(i)
        p1 =  (root.label(),)
        yield p1
        for j in self.left_movable_descendants(i):
            for p in self.left_movable_paths(j):
                yield p1 + p



class SPureIntervalFaces(UniqueRepresentation, Parent):
    r"""
    EXAMPLES::

        sage: SPureIntervalFaces()
        Pure Interval Faces
        sage: SPureIntervalFaces((0,2,2))
        Pure Interval Faces of (0, 2, 2)

    TESTS::

        sage: TestSuite(SPureIntervalFaces()).run()

    """
    def __call__(self, *args, **keywords):

        if isinstance(args[0], SPureIntervalFace):
            return args[0]

        return super(SPureIntervalFaces, self).__call__(*args, **keywords)

    @staticmethod
    def __classcall_private__(cls, s=None):

        if s is None:
            return SPureIntervalFaces_all()

        return SPureIntervalFaces_s(tuple(s))

class SPureIntervalFaces_all(DisjointUnionEnumeratedSets, SPureIntervalFaces):

    def __init__(self):
        DisjointUnionEnumeratedSets.__init__(
            self, Family(Compositions(), lambda c : SPureIntervalFaces_s(tuple(v-1 for v in c))),
            facade=True, keepkey=False, category=EnumeratedSets())

    def _repr_(self):
        return "Pure Interval Faces"

    def _element_constructor_(self, t, ascents):
        return self.element_class(self, t, ascents)

    def __contains__(self, t):
        """
        TESTS::

            sage: SPureIntervalFaces().an_element() in SPureIntervalFaces()
            True

        """
        return isinstance(t, self.element_class)

    Element = SPureIntervalFace

class SPureIntervalFaces_s(SPureIntervalFaces):
    r"""
    TESTS::

        sage: for s in SDecreasingTrees.some_s():
        ....:     TestSuite(SDecreasingTrees(s)).run()

    """

    def __init__(self, s):
        Parent.__init__(self, category=FiniteEnumeratedSets())
        self._s = s

    def _repr_(self):
        return "Pure Interval Faces of {}".format(self._s)

    def s(self):
        return self._s

    def n(self):
        return len(self._s)

    @lazy_attribute
    def _parent_for(self):
        r"""
        The parent of the element generated by ``self``.

        TESTS::

            sage: SPureIntervalFaces((0,2))._parent_for
            Pure Interval Faces
        """
        return SPureIntervalFaces_all()

    # This is needed because this is a facade parent via DisjointUnionEnumeratedSets
    @lazy_attribute
    def element_class(self):
        r"""
        TESTS::

            sage: SPureIntervalFaces((0,2,2)).element_class
            <class '__main__.SPureIntervalFaces_all_with_category.element_class'>
        """
        return self._parent_for.element_class

    def __iter__(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFaces(tuple()))
            [([], ())]
            sage: list(SPureIntervalFaces((1,)))
            [(1[[], []], ())]
            sage: list(SPureIntervalFaces((2,)))
            [(1[[], [], []], ())]
            sage: list(SPureIntervalFaces((0,2)))
            [(2[1[[]], [], []], ()),
             (2[1[[]], [], []], ((1, 2),)),
             (2[[], 1[[]], []], ()),
             (2[[], 1[[]], []], ((1, 2),)),
             (2[[], [], 1[[]]], ())]
        """
        for t in SDecreasingTrees(self.s()):
            yield from t.pure_intervals_starting()

    def faces(self, dimension):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFaces(tuple()).faces(0))
            [([], ())]
            sage: list(SPureIntervalFaces(tuple()).faces(1))
            []
            sage: list(SPureIntervalFaces((1,)).faces(0))
            [(1[[], []], ())]
            sage: list(SPureIntervalFaces((1,)).faces(1))
            []
            sage: list(SPureIntervalFaces((2,)).faces(0))
            [(1[[], [], []], ())]
            sage: list(SPureIntervalFaces((2,)).faces(1))
            []
            sage: list(SPureIntervalFaces((0,2)).faces(0))
            [(2[1[[]], [], []], ()), (2[[], 1[[]], []], ()), (2[[], [], 1[[]]], ())]
            sage: list(SPureIntervalFaces((0,2)).faces(1))
            [(2[1[[]], [], []], ((1, 2),)), (2[[], 1[[]], []], ((1, 2),))]
            sage: list(SPureIntervalFaces((0,2)).faces(2))
            []
            sage: list(SPureIntervalFaces((0,2,2)).faces(0))
            [(3[2[[], [], []], 1[[]], []], ()),
             (3[2[[], [], []], [], 1[[]]], ()),
             (3[2[1[[]], [], []], [], []], ()),
             (3[2[[], 1[[]], []], [], []], ()),
             (3[2[[], [], 1[[]]], [], []], ()),
             (3[1[[]], 2[[], [], []], []], ()),
             (3[[], 2[[], [], []], 1[[]]], ()),
             (3[[], 2[1[[]], [], []], []], ()),
             (3[[], 2[[], 1[[]], []], []], ()),
             (3[[], 2[[], [], 1[[]]], []], ()),
             (3[1[[]], [], 2[[], [], []]], ()),
             (3[[], 1[[]], 2[[], [], []]], ()),
             (3[[], [], 2[1[[]], [], []]], ()),
             (3[[], [], 2[[], 1[[]], []]], ()),
             (3[[], [], 2[[], [], 1[[]]]], ())]
            sage: list(SPureIntervalFaces((0,2,2)).faces(1))
            [(3[2[[], [], []], 1[[]], []], ((1, 3),)),
             (3[2[[], [], []], 1[[]], []], ((2, 3),)),
             (3[2[[], [], []], [], 1[[]]], ((2, 3),)),
             (3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[2[[], 1[[]], []], [], []], ((1, 2),)),
             (3[2[[], 1[[]], []], [], []], ((2, 3),)),
             (3[2[[], [], 1[[]]], [], []], ((1, 3),)),
             (3[1[[]], 2[[], [], []], []], ((1, 3),)),
             (3[1[[]], 2[[], [], []], []], ((2, 3),)),
             (3[[], 2[[], [], []], 1[[]]], ((2, 3),)),
             (3[[], 2[1[[]], [], []], []], ((1, 2),)),
             (3[[], 2[1[[]], [], []], []], ((2, 3),)),
             (3[[], 2[[], 1[[]], []], []], ((1, 2),)),
             (3[[], 2[[], 1[[]], []], []], ((2, 3),)),
             (3[[], 2[[], [], 1[[]]], []], ((1, 3),)),
             (3[1[[]], [], 2[[], [], []]], ((1, 3),)),
             (3[[], 1[[]], 2[[], [], []]], ((1, 3),)),
             (3[[], [], 2[1[[]], [], []]], ((1, 2),)),
             (3[[], [], 2[[], 1[[]], []]], ((1, 2),))]
            sage: list(SPureIntervalFaces((0,2,2)).faces(2))
            [(3[2[[], [], []], 1[[]], []], ((1, 3), (2, 3))),
             (3[2[1[[]], [], []], [], []], ((1, 2), (2, 3))),
             (3[2[[], 1[[]], []], [], []], ((1, 2), (2, 3))),
             (3[1[[]], 2[[], [], []], []], ((1, 3), (2, 3))),
             (3[[], 2[1[[]], [], []], []], ((1, 2), (2, 3))),
             (3[[], 2[[], 1[[]], []], []], ((1, 2), (2, 3)))]
        """
        for t in SDecreasingTrees(self.s()):
            yield from t.pure_intervals_starting(dimension)

    def border_faces(self, dimension = None):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFaces((0,2)).border_faces())
            [(2[1[[]], [], []], ()), (2[[], [], 1[[]]], ())]
            sage: list(SPureIntervalFaces((0,2,2)).border_faces())
            [(3[2[[], [], []], 1[[]], []], ()),
             (3[2[[], [], []], 1[[]], []], ((1, 3),)),
             (3[2[[], [], []], [], 1[[]]], ()),
             (3[2[[], [], []], [], 1[[]]], ((2, 3),)),
             (3[2[1[[]], [], []], [], []], ()),
             (3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[2[[], 1[[]], []], [], []], ()),
             (3[2[[], 1[[]], []], [], []], ((1, 2),)),
             (3[2[[], [], 1[[]]], [], []], ()),
             (3[2[[], [], 1[[]]], [], []], ((1, 3),)),
             (3[1[[]], 2[[], [], []], []], ()),
             (3[1[[]], 2[[], [], []], []], ((2, 3),)),
             (3[[], 2[[], [], []], 1[[]]], ()),
             (3[[], 2[[], [], []], 1[[]]], ((2, 3),)),
             (3[1[[]], [], 2[[], [], []]], ()),
             (3[1[[]], [], 2[[], [], []]], ((1, 3),)),
             (3[[], 1[[]], 2[[], [], []]], ()),
             (3[[], 1[[]], 2[[], [], []]], ((1, 3),)),
             (3[[], [], 2[1[[]], [], []]], ()),
             (3[[], [], 2[1[[]], [], []]], ((1, 2),)),
             (3[[], [], 2[[], 1[[]], []]], ()),
             (3[[], [], 2[[], 1[[]], []]], ((1, 2),)),
             (3[[], [], 2[[], [], 1[[]]]], ())]
            sage: list(SPureIntervalFaces((0,2,2)).border_faces(1))
            [(3[2[[], [], []], 1[[]], []], ((1, 3),)),
             (3[2[[], [], []], [], 1[[]]], ((2, 3),)),
             (3[2[1[[]], [], []], [], []], ((1, 2),)),
             (3[2[1[[]], [], []], [], []], ((2, 3),)),
             (3[2[[], 1[[]], []], [], []], ((1, 2),)),
             (3[2[[], [], 1[[]]], [], []], ((1, 3),)),
             (3[1[[]], 2[[], [], []], []], ((2, 3),)),
             (3[[], 2[[], [], []], 1[[]]], ((2, 3),)),
             (3[1[[]], [], 2[[], [], []]], ((1, 3),)),
             (3[[], 1[[]], 2[[], [], []]], ((1, 3),)),
             (3[[], [], 2[1[[]], [], []]], ((1, 2),)),
             (3[[], [], 2[[], 1[[]], []]], ((1, 2),))]

        """
        for t in SDecreasingTrees(self.s()).border_trees():
            for f in t.pure_intervals_starting(dimension):
                if f.is_border_face():
                    yield f

    def facets(self):
        r"""
        EXAMPLES::

            sage: list(SPureIntervalFaces(tuple()).facets())
            []
            sage: list(SPureIntervalFaces((0,2,2)).facets())
            [(3[2[[], [], []], 1[[]], []], ((1, 3), (2, 3))),
             (3[2[1[[]], [], []], [], []], ((1, 2), (2, 3))),
             (3[2[[], 1[[]], []], [], []], ((1, 2), (2, 3))),
             (3[1[[]], 2[[], [], []], []], ((1, 3), (2, 3))),
             (3[[], 2[1[[]], [], []], []], ((1, 2), (2, 3))),
             (3[[], 2[[], 1[[]], []], []], ((1, 2), (2, 3)))]
            sage: list(SPureIntervalFaces((0,2)).facets())
            [(2[1[[]], [], []], ((1, 2),)), (2[[], 1[[]], []], ((1, 2),))]
        """
        yield from self.faces(self.n() - 1)

    @cached_method
    def f_vector(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFaces((0,2,2)).f_vector()
            6*t^2 + 20*t + 15

        """
        K = PolynomialRing(QQ,'t')
        t = K.gen()
        s = self.s()
        if len(s) < 2:
            return K(1)
        b = s[-1]
        a = s[-2]
        if len(s) == 2:
            return b+1+b*t
        if a == 0:
            return (b+1 + b*t) * SPureIntervalFaces(s[:-2] + (b,)).f_vector()
        return (b+1) * SPureIntervalFaces(s[:-2] + (a+b,)).f_vector() + b*t*SPureIntervalFaces(s[:-2]+(a+b-1,)).f_vector()

    def f_vector_explicit(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFaces((0,2,2)).f_vector_explicit()
            6*t^2 + 20*t + 15

        TESTS::

            sage: tested = [(0,1,1),(0,1,1,1),(0,2,2),(0,2,2,2),(0,3,3),(0,3,3,3),(0,0,2),(0,3,0,3)]
            sage: all(SPureIntervalFaces(s).f_vector() == SPureIntervalFaces(s).f_vector_explicit() for s in tested)
            True

        """
        s = self.s()
        K = PolynomialRing(QQ,'t')
        t = K.gen()
        S = 0
        for tree in SDecreasingTrees(s):
            S+=(1+t)**tree.nb_ascents()
        return S

    def cardinality(self):
        r"""
        EXAMPLES::

            sage: SPureIntervalFaces((0,2,2)).cardinality()
            41
            sage: SPureIntervalFaces((0,1,2,2,1,1,2,1,3,3)).cardinality()
            97027775945

        """
        return self.f_vector()(t=1)

@add_metaclass(InheritComparisonClasscallMetaclass)
class NuTree(Element):

    @staticmethod
    def __classcall_private__(cls, *args, **opts):
        """
        TESTS::

            sage: nut = NuTree((2,2,0),[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,2),(4,2)])
            sage: type(nut)
            <class '__main__.NuTrees_all_with_category.element_class'>


        """
        P = NuTrees_all()
        return P.element_class(P, *args, **opts)

    def __init__(self, parent, nu, points):
        r"""
        EXAMPLES::

            sage: NuTree((2,2,0),[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,2),(4,2)])
            ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (0, 1), (0, 2), (0, 3), (1, 1), (2, 1), (3, 2), (4, 2)))
        """
        Element.__init__(self, parent)
        self._nu = nu
        self._path = NuTrees(nu).path()
        self._points = tuple(points)
        n = NuTrees(nu).n()
        m = NuTrees(nu).m()
        M = [[False]*n for i in range(m)]
        for i,j in points:
            M[j][i] = True
        self._point_matrix = M
        self._n = n
        self._m = m
        self._construct_point_graph()

    def nu(self):
        return self._nu

    def path(self):
        return self._path

    def points(self):
        return self._points

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

    def _repr_(self):
        return str((self._path,self._points))

    def __eq__(self, other):
        return isinstance(other,NuTree) and self._hash_key() == other._hash_key()

    def _hash_key(self):
        return (self._path, self._points)

    def __hash__(self):
        return hash(self._hash_key())

    def __cmp__(self,other):
        if self._hash_key() < other._hash_key():
            return -1
        elif self._hash_key() == other._hash_key():
            return 0
        else:
            return 1

    def __ne__(self, other):
        return not self == other

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

    def to_s_decreasing_tree(self):
        r"""
        EXAMPLES::

            sage: nut = NuTree((2,2,0),[(0,0),(0,1),(0,2),(0,3),(1,1),(2,1),(3,2),(4,2)])
            sage: nut.to_s_decreasing_tree()
            3[2[1[[]], [], []], [], []]

        TESTS::

            sage: all(t.to_nu_tree().to_s_decreasing_tree() == t for t in SDecreasingTrees((0,2,2)).s_tamari_trees())
            True
            sage: all(t.to_nu_tree().to_s_decreasing_tree() == t for t in SDecreasingTrees((0,0,2)).s_tamari_trees())
            True
            sage: all(t.to_nu_tree().to_s_decreasing_tree() == t for t in SDecreasingTrees((0,2,0,2)).s_tamari_trees())
            True
        """
        n = len(self.nu())
        s = tuple(reversed(self.nu()))
        L = [sum(l) for l in self._point_matrix[1:]]
        read = []
        for i in range(len(L)):
            read.append(s[n-1-i]+1)
            read.extend([0] * (L[i]-1))
        leaf = LabelledOrderedTree([],label="")
        fifo = [leaf]
        label = 1
        for v in reversed(read):
            if v > 0:
                children = [fifo.pop() for i in range(v)]
                children.reverse()
                child = LabelledOrderedTree(children, label = label)
                label+=1
                fifo.append(child)
            else:
                fifo.append(leaf)
        return SDecreasingTree(fifo[0])



class NuTrees(UniqueRepresentation, Parent):

    def __call__(self, *args, **keywords):

        if isinstance(args[0], NuTree):
            return args[0]

        return super(NuTrees, self).__call__(*args, **keywords)

    @staticmethod
    def __classcall_private__(cls, nu=None):

        if nu is None:
            return NuTrees_all()

        return NuTrees_nu(tuple(nu))

    @staticmethod
    def nu_to_path(nu):
        p = []
        for a in nu:
            p.append(1)
            p.extend([0]*a)
        return tuple(p)

    @staticmethod
    def some_nu():
        return [tuple(reversed(s)) for s in SDecreasingTrees.some_s()]



class NuTrees_all(DisjointUnionEnumeratedSets, NuTrees):

    def __init__(self):
        DisjointUnionEnumeratedSets.__init__(
            self, Family(Compositions(), lambda c : NuTrees_s(tuple(v-1 for v in c))),
            facade=True, keepkey=False, category=EnumeratedSets())

    def _repr_(self):
        return "NuTrees"

    def _element_constructor_(self, data = None):
        return self.element_class(self, data)

    def __contains__(self, t):
        """
        TESTS::

            sage: SDecreasingTrees().an_element() in SDecreasingTrees()
            True

        """
        return isinstance(t, self.element_class)

    Element = NuTree

class NuTrees_nu(NuTrees):
    """
        TESTS::

            sage: for nu in NuTrees.some_nu():
            ....:     TestSuite(NuTrees(nu)).run()
    """

    def __init__(self, nu):
        Parent.__init__(self, category=FiniteEnumeratedSets())
        self._nu = tuple(nu)
        self._path = NuTrees.nu_to_path(nu)
        self._n = sum(1 for i in self._path if i == 0) + 1
        self._m = sum(self._path) + 1

    def __contains__(self,t):
        """
        TESTS::

            sage: NT = NuTrees((2,0))
            sage: NT.an_element() in NT
            True
            sage: NuTrees((3,0)).an_element() in NT
            False

        """
        return isinstance(t, self.element_class) and t.nu() == self.nu()

    def __iter__(self):
        r"""
        EXAMPLES::

            sage: list(NuTrees(tuple()))
            [((), ((0, 0),))]
            sage: list(NuTrees((1,)))
            [((1, 0), ((0, 0), (1, 1), (0, 1)))]
            sage: list(NuTrees((2,)))
            [((1, 0, 0), ((0, 0), (2, 1), (1, 1), (0, 1)))]
            sage: list(NuTrees((0,2)))
            [((1, 1, 0, 0), ((0, 0), (0, 1), (2, 2), (1, 2), (0, 2)))]
            sage: list(NuTrees((0,2,2)))
            [((1, 1, 0, 0, 1, 0, 0), ((0, 0), (0, 1), (2, 2), (1, 2), (0, 2), (4, 3), (3, 3), (0, 3))),
             ((1, 1, 0, 0, 1, 0, 0), ((0, 0), (0, 1), (2, 2), (1, 2), (4, 3), (3, 3), (1, 3), (0, 3))),
             ((1, 1, 0, 0, 1, 0, 0), ((0, 0), (0, 1), (2, 2), (4, 3), (3, 3), (2, 3), (1, 3), (0, 3)))]
            sage: list(NuTrees((2,2,0)))
            [((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (0, 1), (4, 2), (3, 2), (0, 2), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (0, 1), (4, 2), (3, 2), (3, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (0, 1), (4, 2), (4, 3), (3, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (4, 2), (3, 2), (1, 2), (0, 2), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (4, 2), (3, 2), (1, 2), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (4, 2), (3, 2), (3, 3), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (1, 1), (4, 2), (4, 3), (3, 3), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (4, 2), (3, 2), (2, 2), (1, 2), (0, 2), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (4, 2), (3, 2), (2, 2), (1, 2), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (4, 2), (3, 2), (2, 2), (2, 3), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (4, 2), (3, 2), (3, 3), (2, 3), (1, 3), (0, 3))),
             ((1, 0, 0, 1, 0, 0, 1), ((0, 0), (2, 1), (4, 2), (4, 3), (3, 3), (2, 3), (1, 3), (0, 3)))]
        """
        for t in self.s_decreasing_trees().s_tamari_trees():
            yield t.to_nu_tree()

    def _repr_(self):
        return "NuTrees of {}".format(self._nu)

    def nu(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).nu()
            (2, 2, 0)

        """
        return self._nu

    def path(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).path()
            (1, 0, 0, 1, 0, 0, 1)

        """
        return self._path

    def n(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).n()
            5

        """
        return self._n

    def m(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).m()
            4
        """
        return self._m

    def cardinality(self):
        """
        EXAMPLES::

            sage: NuTrees((1,1,1)).cardinality()
            5
            sage: NuTrees((2,2,2)).cardinality()
            12

        """
        return self.s_decreasing_trees().s_catalan_cardinality()

    def s_decreasing_trees(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).s_decreasing_trees()
            S-decreasing trees of (0, 2, 2)
        """
        return SDecreasingTrees(reversed(self.nu()))

    @lazy_attribute
    def _parent_for(self):
        r"""
        The parent of the element generated by ``self``.

        TESTS::

            sage: NuTrees((0,2,2))._parent_for
            NuTrees
        """
        return NuTrees_all()

    # This is needed because this is a facade parent via DisjointUnionEnumeratedSets
    @lazy_attribute
    def element_class(self):
        r"""
        TESTS::

            sage: NuTrees((0,2,2)).element_class
            <class '__main__.NuTrees_all_with_category.element_class'>
        """
        return self._parent_for.element_class

    @lazy_attribute
    def _path_matrix(self):
        r"""
        EXAMPLES::

            sage: NT = NuTrees((2,2,0))
            sage: NT._path_matrix
            [[True, False, False, False, False],
             [True, True, True, False, False],
             [True, True, True, True, True],
             [True, True, True, True, True]]
        """
        n = self._n
        m = self._m
        M = [[True]*n for i in range(m)]
        i,j = 0,0
        p = self._path
        for v in p:
            if v == 1:
                for k in range(i+1,n):
                    M[j][k] = False
                j+=1
            else:
                i+=1
        return M

    def is_above(self, point):
        r"""
        EXAMPLES::

            sage: NT = NuTrees((2,2,0))
            sage: NT.is_above((0,0))
            True
            sage: NT.is_above((1,0))
            False
            sage: NT.is_above((1,1))
            True
        """
        i,j = point
        return self._path_matrix[j][i]

    def is_compatible(self, p1, p2):
        r"""
        EXAMPLES::

            sage: NT = NuTrees((2,2,0))
            sage: NT.is_compatible((0,0),(0,0))
            True
            sage: NT.is_compatible((0,0),(0,1))
            True
            sage: NT.is_compatible((0,0),(1,1))
            True
            sage: NT.is_compatible((0,0),(2,1))
            True
            sage: NT.is_compatible((1,1),(2,2))
            False
        """
        if p1[0] > p2[0]:
            p1, p2 = p2, p1
        i1, j1 = p1
        i2, j2 = p2
        return not (i1 < i2 and j1 < j2 and self.is_above((i2,j1)))

    def nu_tamari_poset(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).nu_tamari_poset()
            Finite poset containing 12 elements
        """
        return Poset([list(self), lambda x,y: x.to_s_decreasing_tree().sweak_lequal(y.to_s_decreasing_tree())])

    def nu_tamari_lattice(self):
        r"""
        EXAMPLES::

            sage: NuTrees((2,2,0)).nu_tamari_lattice()
            Finite lattice containing 12 elements

        """
        return LatticePoset(self.nu_tamari_poset())

    def nu_tamari_lattice_printer(self):
        r"""

        """
        matrix = self.s_decreasing_trees().proj_matrix()
        return LatticePrinter(self.nu_tamari_poset(), lambda nut: (Matrix(nut.to_s_decreasing_tree().fixed_3d_coordinates())*matrix)[0], scale=.1, object_printer = lambda nut: latex(nut))

###

class LatticePrinter():

    def __init__(self, lattice, get_pos, scale = .2, object_printer = None):
        self._lattice = lattice
        self._scale = scale
        if object_printer is None:
            object_printer = lambda x: latex(x)
        self._object_printer = object_printer
        self._get_pos = get_pos


    def _latex_(self):
        SCALE = self._scale
        st = "\\begin{tikzpicture}[every node/.style={inner sep = -.5pt}]\n"
        ids = {}
        i = 0
        for t in self._lattice:
            ids[t] = i
            p = self._get_pos(t)
            p = [v.n() for v in p]
            st+= "\\node(tree" + str(i) + ") at (" + str(p[0]) + "," + str(p[1]) + ") {\\scalebox{" + str(SCALE) +"}{$\n"
            st+= self._object_printer(t)
            st+="\n$}};\n"
            i+=1
        st+="\n"
        for t1,t2 in self._lattice.cover_relations():
            st+="\\draw (tree" + str(ids[t1]) +") -- (tree" + str(ids[t2]) + ");\n"
        st+="\\end{tikzpicture}"
        return st




#### test functions ####

## intervals ##

"""
sage: transitity((0,2))
True
sage: transitity((0,2,2))
True
sage: transitity((0,2,2,2))
True
sage: transitity((0,3,3))
True
sage: transitity((0,2,2,2,2))
True
"""
def transitity(s):
    SD = SDecreasingTrees(s)
    n = SD.n()
    for t1, t2 in SD.intervals():
        for a in range(1,n):
            for b in range(a+1,n):
                for c in range(b+1,n+1):
                    if t2.inversion(c,b) > t1.inversion(c,b) and t2.inversion(b,a) > t1.inversion(b,a) and t2.inversion(c,a) == t1.inversion(c,a):
                        return t1,t2
    return True



### Ascentopes ###

def test_tree_set_partitions(F,t):
    r"""
    TESTS::

        sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
        sage: t = SDecreasingTree(((0,2,2),{(3,2):2, (3,1):2, (2,1):1}))
        sage: test_tree_set_partitions(F,t)
        True

    """
    return set(F.tree_facet_ordered_sets(t)) == set(F.tree_set_partition(t,i) for i in range(1,F.dimension()+1))

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
sage: t = SDecreasingTree((s,d))
sage: F = SPureIntervalFace(t, [(1,4),(2,3),(3,7),(4,9),(5,10),(6,7),(7,10),(8,9),(9,10)])
"""
# f vector (1, 2178, 9801, 19008, 20790, 14082, 6099, 1680, 282, 26, 1)
def test_all_tree_set_partitions(F):
    r"""
    TESTS::

        sage: F = SPureIntervalFace(SDecreasingTree(((0,2,2),{(3,2):1, (3,1):1, (2,1):1})),[(1,2),(2,3)])
        sage: test_all_tree_set_partitions(F)
        1
        2
        3
        4
        5
        True

    """
    i =0
    facets = {f:F.sub_face_to_set_partition(f) for f in F.sub_facets()}
    for t in F.interval_trees():
        try:
            S1 = set(facets[f] for f in facets if f.include_tree(t))
            S2 = set(F.tree_set_partition(t,i) for i in range(1,F.dimension()+1))
            if S1 != S2:
                return t
            i+=1
            print(i)
        except:
            print("error")
            return t
    return True

### Polytopal subdivision ###

# checked 0222 02222
def check_vtamari_remove_face(s):
    FACETS = list(SPureIntervalFaces(s).facets())
    invalid1 = [ftree for ftree in FACETS if all(not f.is_s_tamari_valid() for f in ftree.sub_facets())]
    invalid2 = [ftree for ftree in FACETS if not ftree.is_s_tamari_valid()]
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
    return len(V) == SDecreasingTrees(s).s_catalan_cardinality()

def check_vtam_graph(s, pols):
    G = Graph()
    for pol in pols:
        G = G.union(pol.vertex_graph())
    G2 = Graph(SDecreasingTrees(s).s_tamari_poset().hasse_diagram())
    return G.is_isomorphic(G2)

# with default fix point
# works for
# 022
# 0211
# 0222
# 0333
# 0112
# broken
# 0002
def check_vtamari_pols(s):
    pols = SDecreasingTrees(s).s_tamari_facet_polyhedrons()
    return check_vtam_intersect(pols) and check_vtam_vertices(s,pols) and check_vtam_graph(s,pols)

# False 2,2,2
def check_essential_variations_intersection(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = set(f3.essential_variations().items())
                ev12 = set(f2.essential_variations().items()).intersection(set(f1.essential_variations().items()))
                if ev12 != ev3:
                    return f1, f2
    return True

# no 2,2,2
def check_essential_variations_intersection_rule(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = set(f3.essential_variations().items())
                var12 = set(f2.variations().items()).intersection(set(f1.variations().items()))
                union12 = set(f2.essential_variations().items()).union(set(f1.essential_variations().items()))
                ev12 = var12.intersection(union12)
                if ev12 != ev3:
                    return f1, f2
    return True

# checked
# 222
# 2222
# 331
# 0202
def check_essential_variations_weak_intersection_rule(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = set(f3.essential_variations().items())
                var12 = set(f2.variations().items()).intersection(set(f1.variations().items()))
                union12 = set(f2.essential_variations().items()).union(set(f1.essential_variations().items()))
                ev12 = var12.intersection(union12)
                if not all(v in ev12 for v in ev3):
                    return f1, f2
    return True

# checked
# 222
# 2222
def check_essential_variations_last_rule(s):
    def potential(f,ev,c,a):
        if (c,a) in ev:
            return True
        p = f.variation_path(c,a)
        b = p[-1]
        return f.inversion_min(b,a) == f.s()[b-1] - 1 and f.varies(b,a)
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                ev1 = f1.essential_variations()
                ev2 = f2.essential_variations()
                for c,a in ev3:
                    if not potential(f1,ev1,c,a) or not potential(f2,ev2,c,a):
                        return f1,f2,c,a
    return True

# no
def check_essential_variations_last_rule_iif(s):
    def compatible_potential(f1, f2,ev1, ev2,c,a):
        if (c,a) not in ev1:
            if (c,a) not in ev2:
                return False
        else:
            if (c,a) in ev2:
                return True
            f1,f2 = f2,f1
            ev1, ev2 = ev2, ev1
        p = f1.variation_path(c,a)
        b = p[-1]
        return f1.inversion_min(b,a) == f1.s()[b-1] - 1 and f1.varies(b,a) and f2.inversion_min(b,a) == f2.s()[b-1]
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = set(f3.essential_variations().items())
                ev1 = f1.essential_variations()
                ev2 = f2.essential_variations()
                var12 = set(f2.variations().items()).intersection(set(f1.variations().items()))
                ev12 = {((c,a),v) for (c,a),v in var12 if compatible_potential(f1,f2,ev1,ev2,c,a)}
                if not ev12 == ev3:
                    return f1,f2
    return True

# checked 222
# 2222
def check_essential_variations_compatible(s):
    def compatible(f1,f2,c,a):
        if not f2.varies(c,a) or f2.inversion_min(c,a) != f1.inversion_min(c,a):
            return False
        if f2.is_essential_variation(c,a):
            return True

        for b in range(a+1,c):
            if f2.inversion_min(b,a) > 0 and f2.inversion_min(b,a) < s[b-1]:
                if not (f2.inversion_min(b,a) == s[b-1] -1 and f1.inversion_min(b,a) == s[b-1] and f2.varies(b,a)):
                    return False
        return True

    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                ev1 = f1.essential_variations()
                ev2 = f2.essential_variations()
                ev12 = {(c,a):ev1[(c,a)] for c,a in ev1 if compatible(f1,f2,c,a)}
                ev12.update({(c,a):ev2[(c,a)] for c,a in ev2 if compatible(f2,f1,c,a)})
                if not ev12 == ev3:
                    return f1,f2
    return True

# 222
# 2222
def check_essential_variations_compatible2(s):
    def compatible(f1,f2,c,a):
        if not f2.varies(c,a) or f2.inversion_min(c,a) != f1.inversion_min(c,a):
            return False
        if f2.is_essential_variation(c,a):
            return True

        for b in range(a+1,c):
            if f2.inversion_min(b,a) > 0 and f2.inversion_min(b,a) < s[b-1]:
                if not f1.inversion_min(b,a) == s[b-1]:
                    return False
        return True

    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                ev1 = f1.essential_variations()
                ev2 = f2.essential_variations()
                ev12 = {(c,a):ev1[(c,a)] for c,a in ev1 if compatible(f1,f2,c,a)}
                ev12.update({(c,a):ev2[(c,a)] for c,a in ev2 if compatible(f2,f1,c,a)})
                if not ev12 == ev3:
                    return f1,f2
    return True

# 222
# 2222
def check_essential_variations_compatible_intersection(s):
    def compatible(f1,f2,c,a):
        if not f2.varies(c,a) or f2.inversion_min(c,a) != f1.inversion_min(c,a):
            return False
        for b in range(a+1,c):
            if f2.inversion_min(b,a) > 0 and f2.inversion_min(b,a) < s[b-1]:
                if not f1.inversion_min(b,a) == s[b-1]:
                    return False
        return True

    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                v1 = f1.variations()
                v2 = f2.variations()
                c1 = {(c,a):v1[(c,a)] for c,a in v1 if compatible(f1,f2,c,a)}
                c2 = {(c,a):v2[(c,a)] for c,a in v2 if compatible(f2,f1,c,a)}
                ev12 = {(c,a):c1[(c,a)] for c,a in c1 if (c,a) in c2 and c2[(c,a)] == c1[(c,a)]}
                if not ev12 == ev3:
                    return f1,f2
    return True

# checked
# 222
# 2222
# 331
# 3330
# 0333
# 0202
def check_variations_intersection(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = set(f3.variations().items())
                ev12 = set(f2.variations().items()).intersection(set(f1.variations().items()))
                if ev12 != ev3:
                    return f1, f2
    return True

# no 222
def check_variations_none_intersection(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 is None:
                ev12 = set(f2.variations().items()).intersection(set(f1.variations().items()))
                if len(ev12)!=0:
                    return f1, f2
    return True

# no 222
def check_variation_path_intersection(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                for (c,a) in f3.variations():
                    path = f3.variation_path(c,a)
                    p1 = f1.variation_path(c,a)
                    p2 = set(f2.variation_path(c,a))
                    p12 = [ci for ci in p1 if ci in p2]
                    if path != p12:
                        return f1,f2,c,a
    return True

# no 2222
def test_ca_cb_essential_var(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for f2 in F:
            f3 = f1.intersection(f2)
            if f3 != None:
                for (c,a) in f3.essential_variations():
                    v = f3.inversion_min(c,a)
                    for b in range(a+1,c):
                        if f3.is_essential_variation(c,b) and f3.inversion_min(c,b) == v  and (not f1.is_essential_variation(c,b) or not f2.is_essential_variation(c,b)):
                            return f1,f2,c,b,a
    return True
# 222
# 2222
# 22222
# 11111
# 02022
# 02202
# 222222
def test_a_barrier(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for c,b in f1.variations():
            if s[b-1] > 0:
                for a in range(1,b):
                    if f1.inversion_min(b,a) == s[b-1] and f1.inversion_min(c,a) == f1.inversion_min(c,b):
                        for bb in range(b+1,c):
                            if f1.inversion_min(bb,a) > 0 and f1.inversion_min(bb,a) < s[bb-1]:
                                break
                        else:
                            return f1,c,b
    return True

# NO 22222
def test_a_barrier_strong(s):
    F = list(SPureIntervalFaces(s))
    for f1 in F:
        for c,b in f1.variations():
            if s[b-1] > 0:
                for a in range(1,b):
                    if f1.inversion_min(b,a) == s[b-1] and f1.inversion_min(c,a) == f1.inversion_min(c,b):
                        for bb in range(b+1,c):
                            if f1.inversion_min(c,bb) == f1.inversion_min(c,b) and f1.inversion_min(bb,a) == s[bb-1] and f1.inversion_min(bb,b) == 0:
                                return f1,c,b
    return True


# 222
# 2222
def test_ca_cb_intersection_ev(s):
    F = list(SPureIntervalFaces(s))
    n = len(s)
    for f1 in F:
        for f2 in F:
            ev1 = f1.essential_variations()
            ev2 = f2.essential_variations()
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                for c in range(1,n+1):
                    for b in range(1,c):
                        if (c,b) in ev3:
                            for a in range(1,b):
                                if (c,a) in ev3 and ev3[(c,a)] == ev3[(c,b)]:
                                    v = ev3[(c,b)]
                                    if not ((ev1.get((c,a),None) == v and ev1.get((c,b),None) == v) or (ev2.get((c,a),None) == v and ev2.get((c,b),None) == v)):
                                        return f1,f2,c,b,a
    return True

# no 2222
def test_ca_cb_intersection_ev_strong(s):
    F = list(SPureIntervalFaces(s))
    n = len(s)
    for f1 in F:
        for f2 in F:
            ev1 = f1.essential_variations()
            ev2 = f2.essential_variations()
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                for c in range(1,n+1):
                    for b in range(1,c):
                        if (c,b) in ev3:
                            for a in range(1,b):
                                if (c,a) in ev3 and ev3[(c,a)] == ev3[(c,b)]:
                                    v = ev3[(c,b)]
                                    if not ((ev1.get((c,a),None) == v and ev1.get((c,b),None) == v) and (ev2.get((c,a),None) == v and ev2.get((c,b),None) == v)):
                                        return f1,f2,c,b,a
    return True
# 222
# 2222
def test_ca_cb_intersection_ev_ca_impl_cb(s):
    F = list(SPureIntervalFaces(s))
    n = len(s)
    for f1 in F:
        for f2 in F:
            ev1 = f1.essential_variations()
            ev2 = f2.essential_variations()
            f3 = f1.intersection(f2)
            if f3 != None:
                ev3 = f3.essential_variations()
                for c in range(1,n+1):
                    for b in range(1,c):
                        if (c,b) in ev3:
                            for a in range(1,b):
                                if (c,a) in ev3 and ev3[(c,a)] == ev3[(c,b)]:
                                    v = ev3[(c,b)]
                                    if ev1.get((c,a),None) == v and not ev1.get((c,b),None) == v:
                                        return f1,f2,c,b,a
    return True

# No
# def test_ca_ba_variations(s):
    # F = list(SPureIntervalFaces(s))
    # for f in F:
        # vf = f.variations()
        # for c,a in vf:
            # for b in range(a+1,c):
                # if f.inversion_min(c,b) == f.inversion_min(c,a) and f.inversion_min(b,a) == 0:
                    # if not (b,a) in vf:
                        # return f,c,b,a
    # return True

# 222
# 2222
# 22222
# 02022
# 02202
def test_ca_ba_variations(s):
    F = list(SPureIntervalFaces(s))
    for f in F:
        vf = f.variations()
        for c,a in vf:
            for b in range(a+1,c):
                if s[b-1] > 0:
                    if f.inversion_min(c,b) == f.inversion_min(c,a) and f.inversion_min(b,a) == 0:
                        if not (b,a) in vf:
                            for bb in range(b+1,c):
                                if f.inversion_min(bb,b) > 0 and f.inversion_min(bb,b) < s[bb-1] and (c,bb) in vf:
                                    break
                            else:
                                return f,c,b,a
    return True


# tested
# 022
# 0222
# 02222
# 022222
# 0232
# 02332
# 0111
# 0112
# 0212
# 022332
def test_full_dimensional_facets(s):
    for F in SPureIntervalFaces(s).facets():
        L1 = set(F.sub_facets_ordered_partitions())
        L2 = set(F.sub_face_to_set_partition(f) for f in F.sub_facets())
        if L1 != L2:
            return F
    return True

# tested
# 022
# 0222
# 02222
# 022222
# 0232
# 02332
# 0111
# 0112
# 0212
# 022332
def test_full_dimensional_facets_unique(s):
    for F in SPureIntervalFaces(s).facets():
        L = list(F.sub_facets_ordered_partitions())
        if len(L) != len(set(L)):
            return F
    return True


### TEST CAVERN REALIZATION

# tested
# 122
# 1222
# 1333
# 1332
# 1232
# 12222
# 122222
def test_convex_hull_number(s):
    SPF = SPureIntervalFaces(s)

    for f in SPF.facets():
        pol = f.s_weak_polyhedron(get_point=lambda x:x.get_point_cavern())
        tr = list(f.interval_trees())
        if len(tr) != len(pol.vertices()):
            return f

    return True

def test_faces_dimensions(s):
    SPF = SPureIntervalFaces(s)

    for f in SPF:
        pol = f.s_weak_polyhedron(get_point=lambda x:x.get_point_cavern())
        if pol.dimension() != f.dimension():
            return f

    return True

