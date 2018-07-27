from sage.categories.enumerated_sets import EnumeratedSets
from sage.categories.finite_enumerated_sets import FiniteEnumeratedSets
from sage.categories.posets import Posets
from sage.combinat.posets.posets import Poset, FinitePoset
from sage.categories.finite_posets import FinitePosets
from sage.combinat.binary_tree import BinaryTrees
from sage.combinat.binary_tree import LabelledBinaryTrees
from sage.combinat.dyck_word import DyckWords
from sage.combinat.permutation import Permutation
from sage.misc.classcall_metaclass import ClasscallMetaclass
from sage.misc.inherit_comparison import InheritComparisonClasscallMetaclass
from sage.misc.cachefunc import cached_method
from sage.misc.latex import latex
from sage.misc.lazy_attribute import lazy_attribute
from sage.rings.integer import Integer
from sage.rings.all import NN
from sage.sets.non_negative_integers import NonNegativeIntegers
from sage.sets.disjoint_union_enumerated_sets import DisjointUnionEnumeratedSets
from sage.sets.family import Family
from sage.structure.element import Element
from sage.structure.global_options import GlobalOptions
from sage.structure.parent import Parent
from sage.structure.unique_representation import UniqueRepresentation


RelationOptions = GlobalOptions(name="Relations",
    doc=r"""
    Set and display the global options for Integer relations
    """,
    end_doc=r"""

    """,
    latex_tikz_scale=dict(default=1,
                          description='the default value for the tikz scale when latexed',
                          checker=lambda x: True),  # More trouble than it's worth to check
    latex_line_width_scalar=dict(default=0.5,
                                 description='the default value for the line width as a'
                                             'multiple of the tikz scale when latexed',
                                 checker=lambda x: True),  # More trouble than it's worth to check
    latex_color_decreasing=dict(default="red",
                                description='the default color of decreasing relations when latexed',
                                checker=lambda x: True),  # More trouble than it's worth to check
    latex_color_increasing=dict(default="blue",
                                description='the default color of increasing relations when latexed',
                                checker=lambda x: True),  # More trouble than it's worth to check

    latex_textcolor=dict(default=None,
                                description='the label text color',
                                checker=lambda x: True),  # More trouble than it's worth to check

    latex_hspace=dict(default=1,
                      description='the default difference between horizontal'
                                  ' coordinates of vertices when latexed',
                      checker=lambda x: True),  # More trouble than it's worth to check
    latex_bend=dict(default=70,
                      description='the default bend for arrows',
                      checker=lambda x: True),   # More trouble than it's worth to check

    latex_arrow=dict(default=True,
                      description='draw arrow',
                      checker=lambda x: True),   # More trouble than it's worth to check

    latex_number=dict(default=True,
                      description='draw numbers',
                      checker=lambda x: True)   # More trouble than it's worth to check
)


class Relation(Element):
    r"""
    An integer binary relation

    EXAMPLES::

        sage: Relation(3,[(1,2),(3,2)])
        The relation of size 3 given by relations ((1, 2), (3, 2))
    """
    __metaclass__ = InheritComparisonClasscallMetaclass

    @staticmethod
    def __classcall_private__(cls, *args, **opts):
        P = Relations_all()
        return P.element_class(P, *args, **opts)

    def __init__(self, parent, size, relations, sign = None):
        r"""
        TESTS::

            sage: Relation(3,[(1,2),(3,2)]).parent()
            Relations
        """
        self._size = size
        relset = set(tuple(r) for r in relations)
        relset.update((i,i) for i in xrange(1,size+1))
        self._relations_with_reflexive = frozenset(relset)
        self._relations = frozenset({r for r in relset if r[0]!=r[1]}) # without reflexive
        self._sign = None
        assert(sign is None or len(sign) == size)
        if not sign is None:
            self._sign = tuple(sign)

        Element.__init__(self, parent)

        self._latex_options = dict()

    def relations(self):
        r"""
        Return the frozen set of (x,y), x!=y, such that xRy

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.relations()
            frozenset({(1, 2), (3, 2)})
        """
        return self._relations

    def relations_with_reflexive(self):
        r"""
        Return the frozen set of (x,y), such that xRy, including xRx relations

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.relations_with_reflexive()
            frozenset({(1, 1), (1, 2), (2, 2), (3, 2), (3, 3)})
        """
        return self._relations_with_reflexive

    def sign(self):
        return self._sign

    def is_signed(self):
        return not self._sign is None

    def __hash__(self):
        return hash((self.relations(), self.sign()))

    @cached_method
    def increasing_relations(self):
        r"""
        Return the tuple of tuples (x,y), such that xRy, with x < y

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.increasing_relations()
            ((1, 2),)
        """
        return tuple((i,j) for (i,j) in self.relations() if i<j)

    @cached_method
    def decreasing_relations(self):
        r"""
        Return the tuple of tuples (y,x), such that yRx, with x < y

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.decreasing_relations()
            ((3, 2),)
        """
        return tuple((i,j) for (i,j) in self.relations() if i>j)


    def __cmp__(self,other):
        if self._relations < other._relations:
            return -1
        elif self._relations == other._relations:
            return 0
        else:
            return 1

    def set_latex_options(self, D):
        r"""
        Set the latex options for use in the ``_latex_`` function.  The
        default values are set in the ``__init__`` function.

        - ``tikz_scale`` -- (default: 1) scale for use with the tikz package

        - ``line_width`` -- (default: 1*``tikz_scale``) value representing the
          line width

        - ``color_decreasing`` -- (default: red) the color for decreasing
          relations

        - ``color_increasing`` -- (default: blue) the color for increasing
          relations

        - ``hspace`` -- (default: 1) the difference between horizontal
          coordinates of adjacent vertices

        - ``vspace`` -- (default: 1) the difference between vertical
          coordinates of adjacent vertices

        INPUT:

        - ``D`` -- a dictionary with a list of latex parameters to change

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.latex_options()["color_decreasing"]
            'red'
            sage: r.set_latex_options({"color_decreasing":'green'})
            sage: r.latex_options()["color_decreasing"]
            'green'
            sage: r.set_latex_options({"color_increasing":'black'})
            sage: r.latex_options()["color_increasing"]
            'black'


        To change the default options for all integer relations, use the
        parent's global latex options::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r2 = Relation(4,[(4,3),(1,2)])
            sage: r.latex_options()["color_decreasing"]
            'red'
            sage: r2.latex_options()["color_decreasing"]
            'red'
            sage: Relations.global_options(latex_color_decreasing='green')
            sage: r.latex_options()["color_decreasing"]
            'green'
            sage: r2.latex_options()["color_decreasing"]
            'green'

        Next we set a local latex option and show the global does not
        override it::

            sage: r.set_latex_options({"color_decreasing":'black'})
            sage: r.latex_options()["color_decreasing"]
            'black'
            sage: Relations.global_options(latex_color_decreasing='blue')
            sage: r.latex_options()["color_decreasing"]
            'black'
            sage: r2.latex_options()["color_decreasing"]
            'blue'
            sage: Relations.global_options._reset()

        """
        for opt in D:
            self._latex_options[opt] = D[opt]

    def latex_options(self):
        r"""
        Return the latex options for use in the ``_latex_`` function as a
        dictionary. The default values are set using the global options.

        - ``tikz_scale`` -- (default: 1) scale for use with the tikz package

        - ``line_width`` -- (default: 1) value representing the line width
          (additionally scaled by ``tikz_scale``)

        - ``color_decreasing`` -- (default: ``'red'``) the color for
          decreasing relations

        - ``color_increasing`` -- (default: ``'blue'``) the color for
          increasing relations

        - ``textcolor`` -- (default: None) the label textcolor

        - ``hspace`` -- (default: 1) the difference between horizontal
          coordinates of adjacent vertices

        - ``bend`` -- (default: 70) the arrow bend

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.latex_options()["color_decreasing"]
            'red'
            sage: r.latex_options()["hspace"]
            1
        """
        d = self._latex_options.copy()
        if "tikz_scale" not in d:
            d["tikz_scale"] = self.parent().global_options["latex_tikz_scale"]
        if "line_width" not in d:
            d["line_width"] = self.parent().global_options["latex_line_width_scalar"] * d["tikz_scale"]
        if "color_decreasing" not in d:
            d["color_decreasing"] = self.parent().global_options["latex_color_decreasing"]
        if "color_increasing" not in d:
            d["color_increasing"] = self.parent().global_options["latex_color_increasing"]
        if "textcolor" not in d:
            d["textcolor"] = self.parent().global_options["latex_textcolor"]
        if "hspace" not in d:
            d["hspace"] = self.parent().global_options["latex_hspace"]
        if "bend" not in d:
            d["bend"] = self.parent().global_options["latex_bend"]
        if "arrow" not in d:
            d["arrow"] = self.parent().global_options["latex_arrow"]
        if "number" not in d:
            d["number"] = self.parent().global_options["latex_number"]
        return d

    def _latex_(self):
        r"""

        """
        latex.add_package_to_preamble_if_available("tikz")
        latex_options = self.latex_options()
        start = "\\begin{tikzpicture}[scale=" + str(latex_options['tikz_scale']) + "]\n"
        end = "\\end{tikzpicture}"

        def draw_node(j, x, y):
            r"""
            Internal method to draw vertices
            """
            if latex_options["number"]:
                n = str(j)
                if latex_options["textcolor"] is not None:
                    n = "\\textcolor{" + latex_options["textcolor"] + "}{" + n + "}"
            else:
                n = "$\\cdot$"
            return "\\node(T" + str(j) + ") at (" + str(x) + "," + str(y) + ") {" + n + "};\n"

        def draw_increasing(i, j):
            r"""
            Internal method to draw increasing relations
            """
            if latex_options["arrow"]:
                a = "->, "
            else:
                a = ""
            return "\\draw[" + a + "line width = " + str(latex_options["line_width"]) + ", color=" + latex_options["color_increasing"] + "] (T" + str(i) + ") edge [bend left="+ str(latex_options["bend"])+"] (T" + str(j) + ");\n"

        def draw_decreasing(i, j):
            r"""
            Internal method to draw decreasing relations
            """
            if latex_options["arrow"]:
                a = "->, "
            else:
                a = ""
            return "\\draw["+ a + "line width = " + str(latex_options["line_width"]) + ", color=" + latex_options["color_decreasing"] + "] (T" + str(i) + ") edge [bend left="+ str(latex_options["bend"])+"] (T" + str(j) + ");\n"
        if self.size() == 0:
            nodes = "\\node(T0) at (0,0){$\emptyset$};"
            relations = ""
        else:
            nodes = ""  # latex for node decraltions
            relations = ""  # latex for drawing relations
            x = 0
            y = 0
            dx = latex_options["hspace"]
            for i in self:
                nodes+=draw_node(i,x,y)
                x+=dx

            for (i,j) in self.relations():
                if i < j:
                    relations += draw_increasing(i,j)
                else:
                    relations += draw_decreasing(i,j)

            # Latex drawing trick
            relations += "\\draw[->,line width = " + str(latex_options["line_width"]) + ", color=white, opacity=0] (T1) edge [bend left="+ str(latex_options["bend"])+"] (T" + str(self.size()) + ");\n"
            relations += "\\draw[->,line width = " + str(latex_options["line_width"]) + ", color=white, opacity=0] (T" + str(self.size()) + ") edge [bend left="+ str(latex_options["bend"])+"] (T1);\n"

        return start + nodes + relations + end


    def rel(self, e1, e2):
        r"""
        Return whether ``e1`` is in the relation with ``e2`` in ``self``.

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.rel(1,2)
            True
            sage: r.rel(1,3)
            False

        """
        return (e1,e2) in self.relations_with_reflexive()


    def size(self):
        r"""
        Return the size (number of vertices) of the relation.

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: r.size()
            3

        """
        return self._size

    def complement(self):
        r"""
        Return the relation ``C`` where increasing and decreasing relations are reversed, such that `a C b ` iif `(n-a+1) R (n-b+1)`.

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(1,3)])
            sage: r.complement()
            The relation of size 3 given by relations ((3, 2), (3, 1))

        """
        N = self._size + 1
        new_relations = [[N - i[0], N - i[1]] for i in self.relations()]
        return Relation(N - 1, new_relations, self._sign)

    def relation_extensions(self, forbiden = None):
        r"""
        Return all relations ``r``  such that if ``i`` is related to ``j``
        in ``self``, ``i`` is related to ``j`` in ``r2``

        INPUT:

            - ``forbiden`` (optional) a list of forbiden relations

        Proceeds by width exploration of the boolean lattice
        """
        level = {self}
        n = self.size()
        steps = n*(n-1) - len(self.relations())
        if forbiden is None:
            forbiden = set()
        else:
            forbiden = set(forbiden)

        for i in xrange(steps):
            next_level = set()
            for r in level:
                yield r
                rels = list(r.relations())
                for a in r:
                    for b in r:
                        if not r.rel(a,b) and (a,b) not in forbiden:
                            r2 = Relation(n, rels + [(a,b)], self.sign())
                            next_level.add(r2)
            level = next_level
        for r in level:
            yield r


    def _repr_(self):
        s = "The relation of size {} given by relations {}".format(self.size(),
                self.increasing_relations() + self.decreasing_relations())
        if self.is_signed():
            s+= " with orientation {}".format(self.sign())
        return s

    def __eq__(self, other):
        if (not isinstance(other, Relation)):
            return False
        return self.size() == other.size() and self._relations == other._relations and self._sign == other._sign and self._latex_options == other._latex_options
        # the latex_options is a weird one to check BUT otherwise it gets messy when drawing the posets with different latex options

    def __ne__(self, other):
        return not (self == other)

    def __iter__(self):
        return xrange(1,self.size()+1).__iter__()

    def maximal_antichains(self):
        r"""
        Return an iterator on the maximal subsets for inclusion `I` of `n` such that the elements of `I` are not related in ``self``.

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(3,2)])
            sage: list(r.maximal_antichains())
            [frozenset({1, 3}), frozenset({2})]

        """
        from collections import defaultdict
        def maximal_antichains_rec(rels_dict, current_antichain, comparables):
            potential_nodes = set([k for k in range(1, self.size() + 1) if not k in current_antichain and not k in comparables])
            res = []
            found = False
            for pot in potential_nodes:
                if not any((x in rels_dict[pot] for x in current_antichain)):
                    found = True
                    res.extend(maximal_antichains_rec(rels_dict,
                                                      current_antichain | {pot},
                                                      comparables | rels_dict[pot]))
            if not found:
                res.append(current_antichain)
            return res

        rels = set(self._relations)
        rels_dict = defaultdict(set)
        for a, b in rels:
            rels_dict[a].add(b)
        return set([frozenset(x) for x in maximal_antichains_rec(rels_dict, set(), set())])

    def transDelDec(self):
        r"""
        Return the relation after applying the transitive decreasing deletion

        EXAMPLES::

            sage: r = Relation(4,[(1,2),(2,3),(1,3),(4,3),(3,1),(4,1)]); r
            The relation of size 4 given by relations ((1, 2), (1, 3), (2, 3), (4, 3), (3, 1), (4, 1))
            sage: r.transDelDec()
            The relation of size 4 given by relations ((1, 2), (1, 3), (2, 3), (4, 3))

        """
        n = self.size()
        newS = set(self.relations())
        for (j,i) in self.relations():
            if j>i:
                for k in xrange(1,j+1):
                    if k==j or (k,j) in self.relations():
                        for l in xrange(i,n+1):
                            if i==l or (i,l) in self.relations():
                                if (k,l) not in self.relations() and (j,i) in newS:
                                    newS.remove((j,i))
        return Relation(self.size(), newS, self._sign)

    def asDelDec(self):
        r"""
        Return the relation after applying the assymmetric decreasing deletion

        EXAMPLES::

            sage: r = Relation(3,[(1,3),(3,2),(3,1)]); r
            The relation of size 3 given by relations ((1, 3), (3, 2), (3, 1))
            sage: r.asDelDec()
            The relation of size 3 given by relations ((1, 3), (3, 2))

        """
        newS = set(self.relations())
        for (i,j) in self.increasing_relations():
            if self.rel(j,i):
                newS.remove((j,i))
        return Relation(self.size(), newS, self._sign)

    def increasingClosure(self):
        r"""
        Return the relationa fter applying a transitive closure on the increasing relations

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(2,3),(3,2),(2,1)]); r
            The relation of size 3 given by relations ((1, 2), (2, 3), (3, 2), (2, 1))
            sage: r.increasingClosure()
            The relation of size 3 given by relations ((1, 2), (1, 3), (2, 3), (3, 2), (2, 1))
        """
        newS = set(self.relations())
        added = True
        while added:
            added = False
            for k in self:
                for j in xrange(1,k):
                    if (j,k) in newS:
                        for i in xrange(1,j):
                            if (i,j) in newS and not (i,k) in newS:
                                newS.add((i,k))
                                added = True
        return Relation(self.size(), newS, self._sign)


    def decreasingClosure(self):
        r"""
        Return the relationa fter applying a transitive closure on the decreasing relations

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(2,3),(3,2),(2,1)]); r
            The relation of size 3 given by relations ((1, 2), (2, 3), (3, 2), (2, 1))
            sage: r.decreasingClosure()
            The relation of size 3 given by relations ((1, 2), (2, 3), (3, 2), (3, 1), (2, 1))
        """
        newS = set(self.relations())
        added = True
        while added:
            added = False
            for k in self:
                for j in xrange(1,k):
                    if (k,j) in newS:
                        for i in xrange(1,j):
                            if (j,i) in newS and not (k,i) in newS:
                                newS.add((k,i))
        return Relation(self.size(), newS, self._sign)

    def semiTransitiveClosure(self):
        r"""
        Return the relation after applying a semi transitive closure, i.e. 2 independant transitive closures on
        both the increasing and decreasing relations.

        EXAMPLES::

            sage: r = Relation(3,[(1,2),(2,3),(3,2),(2,1)]); r
            The relation of size 3 given by relations ((1, 2), (2, 3), (3, 2), (2, 1))
            sage: r.semiTransitiveClosure()
            The relation of size 3 given by relations ((1, 2), (1, 3), (2, 3), (3, 2), (3, 1), (2, 1))

        """
        return self.increasingClosure().decreasingClosure()



    def is_increasing(self):
        r"""
        Return if ``self`` contains only increasing realtions.

        EXAMPLES::

            sage: Relation(3,[(1,2),(3,2)]).is_increasing()
            False
            sage: Relation(3,[(1,2),(2,3)]).is_increasing()
            True

        """
        return len(self.decreasing_relations()) == 0

    def is_decreasing(self):
        r"""
        Return if ``self`` contains only decreasing realtions.

        EXAMPLES::

            sage: Relation(3,[(1,2),(3,2)]).is_decreasing()
            False
            sage: Relation(3,[(2,1),(3,2)]).is_decreasing()
            True

        """
        return len(self.increasing_relations()) == 0

    def succ(self):
        r"""
        Return a generator on the successor of ``self`` in the integer relations
        weak order

        EXAMPLES::

            sage: r = Relation(2,[(1,2)]); r
            The relation of size 2 given by relations ((1, 2),)
            sage: list(r.succ())
            [The relation of size 2 given by relations (),
             The relation of size 2 given by relations ((1, 2), (2, 1))]
            sage: r = Relation(2,[(2,1)]); r
            The relation of size 2 given by relations ((2, 1),)
            sage: list(r.succ())
            []

        """
        incs = self.increasing_relations()
        decs = set(self.decreasing_relations())
        for (i,j) in incs:
            p2 = Relation(self.size(),[(a,b) for (a,b) in self.relations() if (a,b)!=(i,j)], self._sign)
            if p2!=self:
                yield p2

            if (j, i) not in decs:
                yield Relation(self.size(),self.relations().union(frozenset([(j,i)])), self._sign)

        for (i,j) in self.non_relations():
            yield Relation(self.size(),self.relations().union(frozenset([(j,i)])), self._sign)

    def non_relations(self):
        r"""
        Return the list of tuple (i,j) such that i is not in relation with j nor j with i

        EXAMPLES::

            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: r.non_relations()
            [(2, 3)]
        """
        return [(i,j) for i in self for j in xrange(i+1,self.size()+1) if not self.rel(i,j) and not self.rel(j,i)]

    def lequal(self,p2):
        r"""
        Return True if ``self`` is lower than or equal to ``p2`` in the weak order on
        integer relations

        EXAMPLES::

            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: r.lequal(Relation(3,[(1,3),(2,1),(3,1)]))
            True
            sage: r.lequal(Relation(3,[(2,1),(3,1)]))
            True
            sage: r.lequal(Relation(3,[(1,2),(2,1),(3,1)]))
            False
        """
        return all([self.rel(i,j) for (i,j) in p2.increasing_relations()]) and all([p2.rel(j,i) for (j,i) in self.decreasing_relations()])

    def grade(self):
        r"""
        Return the grade of ``self`` in the weak order lattice on integer
        relations.

        Grades range from -n(n-1)/2 to n(n-1)/2

        EXAMPLES::

            sage: Relation(3,[(2,1),(3,2)]).grade()
            -2
            sage: Relation(3,[(1,2),(3,2)]).grade()
            0
            sage: Relation(3,[(1,2),(1,3),(2,3)]).grade()
            3
            sage:
            sage: Relation(4,[(1,2),(2,3),(3,4),(1,3),(2,4),(1,4)]).grade()
            6

        """
        return len(self.increasing_relations()) - len(self.decreasing_relations())

    def add(self, r):
        r"""
        Return the relation where ``r`` has been added.

        INPUT:

            - ``r`` a tuple ``(i,j)``

        EXAMPLES::

            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: r.add((2,3))
            The relation of size 3 given by relations ((1, 3), (2, 3), (2, 1))
            sage: r.add((1,3))
            The relation of size 3 given by relations ((1, 3), (2, 1))
        """
        return Relation(self.size(), self._relations.union({r}), self._sign)

    def delete(self, r):
        r"""
        Return the relation where ``r`` has been deleted (if present)

        INPUT:

            - ``r`` a tuple ``(i,j)``

        EXAMPLES::

            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: r.delete((1,3))
            The relation of size 3 given by relations ((2, 1),)
            sage: r.delete((2,3))
            The relation of size 3 given by relations ((1, 3), (2, 1))

        """
        return Relation(self.size(), self._relations.difference({r}), self._sign)

    def is_inc_transitive(self):
        return self.parent().is_inc_transitive(self)

    def is_dec_transitive(self):
        return self.parent().is_dec_transitive(self)

    def is_semi_transitive(self):
        return self.parent().is_semi_transitive(self)

    def is_transitive(self):
        return self.parent().is_transitive(self)

    def is_poset(self):
        return self.parent().is_transitive(self) and self.parent().is_anti_symmetric(self)

    def is_symmetric(self):
        return self.parent().is_symmetric(self)

    def is_anti_symmetric(self):
        return self.parent().is_anti_symmetric(self)

    def is_primitive(self):
        for k in xrange(1, self.size()):
            cut = True
            for i in xrange(1,k+1):
                for j in xrange(k+1,self.size()+1):
                    if self.rel(j,i) or not self.rel(i,j):
                        cut = False
                        break
                if not cut:
                    break
            else:
                return False
        return True



    def union(self, other, sign = None):
        m = max(self.size(), other.size())
        if m == self.size() and sign is None:
            sign = self.sign()
        S = set(self.relations())
        S.update(other.relations())
        return self.parent()(m, S, sign)

    def shift(self, n, sign = None):
        return self.parent()(self.size() + n, [(a+n, b+n) for (a,b) in self.relations()], sign)

    def is_cut_old(self, I):
        """
        checks if the subset I of [n] is a cut:
        that there is no relation from [n] \ I to I
        """
        I = set(I)
        for a in self:
            if not a in I:
                for i in I:
                    if self.rel(a,i):
                        return False
        return True

    def is_cut(self, I):
        """
        checks if the subset I of [n] is a cut:
        that there is all relations from I to [n] \ I
        and there is no relation from [n] \ I to I
        """
        I = set(I)
        J = set(v for v in self if not v in I)
        for a in I:
            for b in J:
                if self.rel(b,a) or not self.rel(a,b):
                    return False
        return True

    def cuts(self):
        for I in subsets(self):
            if self.is_cut(I):
                yield I

    def cut(self, I):
        I.sort()
        sI = set(I)
        d = {I[ind]:ind+1 for ind in xrange(len(I))}
        sign = None
        if self.is_signed():
            sign = tuple(self.sign()[i-1] for i in self if i in sI)
        return Relation(len(I), [(d[a],d[b]) for (a,b) in self.relations() if a in sI and b in sI], sign)


class Relations(UniqueRepresentation, Parent):
    r"""
    The parent class for all integer relations.

    It allows bor recursive generation under some restrictions (symmetric,
    antisymmetric, transitive, etc).

    EXAMPLES::

        sage: Relations()
        Relations
        sage: Relations(3)
        Relations of size 3
        sage: Relations(3, anti_symmetric = True)
        Relations of size 3 with properties: anti_symmetric
        sage: Relations(3, anti_symmetric = True, transitive = True)
        Relations of size 3 with properties: transitive, anti_symmetric

    """

    @staticmethod
    def __classcall_private__(cls, n=None, **keywords):

        if n is None:
            return Relations_all(**keywords)

        if n not in NN:
            raise ValueError("n must be a non negative integer")
        return Relations_size(Integer(n), **keywords)

    def parameters_view(self):
        return {k:self._parameters[k] for k in self._parameters}

    def properties(self):
        return self._parameters.keys()

    def _print_property(self, p):
        if self._parameters[p] == True:
            return p
        else:
            return p+ ":" + str(self._parameters[p])

    def prop_string(self):
        if len(self._parameters)!=0:
            strings = [self._print_property(p) for p in self.properties()]
            return " with properties: " + ", ".join(strings)
        return ""

    def _initialise_properties(self,keywords):
        self._parameters = {k:keywords[k] for k in keywords if keywords[k]}
        self._sign = None
        for k in keywords:
            if type(keywords[k]) == tuple:
                self._sign = keywords[k]
                break

    def has_property(self, prop):
        return prop in self._parameters.keys()

    def parameter(self, prop):
        if self._parameters.has_key(prop):
            return self._parameters[prop]
        return None

    def check_property(self, x, prop):
        r"""
        Return true if a relation ``x`` satisfies a certain property ``prop``

        EXAMPLES::

            sage: R = Relations()
            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: R.check_property(r, "transitive")
            False
            sage: R.check_property(r, "inc_transitive")
            True

        """
        method_name = "is_" + prop
        if not hasattr(self,method_name):
            raise NotImplementedError("No method to check property: {}".format(prop))
        method = getattr(self,method_name)
        return method(x)

    def check_all_properties(self, x):
        r"""
        Return true if the relation ``x```satisfies all properties of ``self``

        EXAMPLES::

            sage: R = Relations(anti_symmetric = True, transitive = True)
            sage: r = Relation(3,[(1,3),(2,1)]); r
            The relation of size 3 given by relations ((1, 3), (2, 1))
            sage: R.check_all_properties(r)
            False
            sage: r = Relation(3,[(1,3),(2,1),(2,3)]); r
            The relation of size 3 given by relations ((1, 3), (2, 3), (2, 1))
            sage: R.check_all_properties(r)
            True
        """
        for prop in self.properties():
            if not self.check_property(x, prop):
                return False
        return True

    def is_inc_transitive(self, x):
        n = x.size()
        for i in xrange(1,n+1):
            for j in xrange(i+1,n+1):
                if (i,j) in x.relations():
                    for k in xrange(j+1,n+1):
                        if x.rel(j,k) and not x.rel(i,k):
                            return False
        return True

    def is_dec_transitive(self, x):
        n = x.size()
        for k in xrange(n,-1,-1):
            for j in xrange(k,-1,-1):
                if x.rel(k,j):
                    for i in xrange(j-1,-1,-1):
                        if x.rel(j,i) and not x.rel(k,i):
                            return False
        return True

    def is_semi_transitive(self,x):
        return self.is_inc_transitive(x) and self.is_dec_transitive(x)

    def is_transitive(self, x):
        n = x.size()
        for i in xrange(1,n+1):
            for j in xrange(1,n+1):
                if i!=j and x.rel(i,j):
                    for k in xrange(1,n+1):
                        if k!=j and x.rel(j,k) and not x.rel(i,k):
                            return False
        return True

    def is_symmetric(self, x):
        for (i,j) in x.relations():
            if not x.rel(j,i):
                return False
        return True

    def is_anti_symmetric(self, x):
        for (i,j) in x.relations():
            if x.rel(j,i):
                return False
        return True


    def __call__(self, *args, **keywords):

        if isinstance(args[0], Relation):
            return args[0]

        return super(Relations, self).__call__(*args, **keywords)

    def meet(self, r1, r2):
        r"""
        Return the meet of ``r1`` and ``r2```in the weak order lattice
        on integer relations
        """
        if r1.size() != r2.size():
            raise ValueError("Wrong size")
        inc = set(r1.increasing_relations())
        inc.update(r2.increasing_relations())
        dec = set(r1.decreasing_relations()).intersection(r2.decreasing_relations())
        inc.update(dec)
        return Relation(r1.size(), inc, r1.sign())

    def bipartite(self,n,k):
        """
        Enumerate all bipartite relations between 1...n and n+1...n+k
        """
        for i in xrange(2**(2*n*k)):
            R = []
            for a in xrange(n):
                for b in xrange(k):
                    if i%2 == 1:
                        R.append((a+1,n+b+1))
                    i = i >> 1
            for b in xrange(k):
                for a in xrange(n):
                    if i%2 == 1:
                        R.append((n+b+1,a+1))
                    i = i >> 1
            yield Relation(n+k, R)

    def restricted_extensions(self, r, forbiden = None):
        r"""
        Return the extenstions of ``r`` which belong to ``self``
        """
        for r2 in r.relation_extensions(forbiden):
            if self.check_all_properties(r2):
                yield self(r2)




    global_options = RelationOptions





class Relations_all(DisjointUnionEnumeratedSets, Relations):
    r"""
    The enumerated set of all integer relations.
    """
    def __init__(self, **keywords):
        DisjointUnionEnumeratedSets.__init__(
            self, Family(NonNegativeIntegers(), lambda i : Relations_size(i, **keywords)),
            facade=True, keepkey=False, category=(Posets(), EnumeratedSets()))
        self._sign = None
        self._initialise_properties(keywords)


    def _repr_(self):
        r"""
        TEST::

            sage: Relations()
            Relations
            sage: Relations(transitive = True)
            Relations with properties: transitive
        """
        return "Relations" + self.prop_string()

    def _element_constructor_(self, size, relations, sign = None):
        return self.element_class(self, size, relations, sign)

    def __contains__(self, x):
        r"""
        TESTS::

            sage: S = Relations()
            sage: 1 in S
            False
            sage: S(0,[]) in S
            True
        """
        if isinstance(x, self.element_class):
            return self.check_all_properties(x)
        return False

    def finite_set(self, size):
        return self._family[size]

    Element = Relation


class Relations_size(Relations):
    r"""
    The enumerated set of integer relations of a given size.

    """
    def __init__(self, size, **keywords):
        r"""

        """
        super(Relations_size, self).__init__(category=FiniteEnumeratedSets())
        self._size = size
        self._initialise_properties(keywords)

    def _initialise_properties(self,keywords):
        super(Relations_size, self)._initialise_properties(keywords)
        self._parameters = {k:keywords[k] for k in keywords if keywords[k]}
        self._sign = None
        for k in keywords:
            if type(keywords[k]) == tuple:
                self._sign = keywords[k][:self._size]
                break

    def _repr_(self):
        r"""

        """
        return "Relations of size {}".format(self._size) + self.prop_string()

    def size(self):
        return self._size

    def __contains__(self, x):
        if isinstance(x, self.element_class) and x.size() == self._size:
            return self.check_all_properties(x)

    def is_signed(self):
        return not self._sign is None

    def sign(self):
        return self._sign

    def __iter__(self):
        def next_rels(r, i):
            n = r.size()
            if i == n:
                if self.check_all_properties(r):
                    yield self(r)
            else:
                for nr in next_rels(r,i+1):
                    yield nr
                r1 = r.add((i,n)) # increasing rel
                if not self.has_property("symmetric"):
                    for nr in next_rels(r1,i+1):
                        yield nr
                    r2 = r.add((n,i)) # decreasing rel
                    for nr in next_rels(r2,i+1):
                        yield nr
                if not self.has_property("anti_symmetric"):
                    r1 = r1.add((n,i)) # both
                    for nr in next_rels(r1,i+1):
                        yield nr
        if self.size() == 0:
            yield self(Relation(0,[], self._sign))
        else:
            keywords = {p:self.parameter(p) for p in self.properties()}
            for pr in self.__class__(self.size()-1, **keywords):
                r = Relation(self.size(), pr.relations(), self._sign)
                for nr in next_rels(r, 1):
                    yield nr


    @lazy_attribute
    def _parent_for(self):
        r"""
        The parent of the element generated by ``self``.

        """
        return Relations_all()

    # This is needed because this is a facade parent via DisjointUnionEnumeratedSets
    @lazy_attribute
    def element_class(self):
        r"""

        """
        return self._parent_for.element_class

    def _element_constructor_(self, relations):
        r"""

        """
        return self.element_class(self, self._size, relations, self_sign)

    def minimal_element(self):
        r"""
        Return the minimal relation in the weak order lattice

        EXAMPLES::

            sage: Relations(3).minimal_element()
            The relation of size 3 given by relations ((1, 2), (1, 3), (2, 3))
        """
        return self._parent_for(self.size(), [(i,j) for i in xrange(1,self.size()) for j in xrange(i+1,self.size()+1)])

    def maximal_element(self):
        r"""
        Return the maximal relation in the weak order lattice

        EXAMPLES::

            sage: Relations(3).maximal_element()
            The relation of size 3 given by relations ((3, 2), (3, 1), (2, 1))
        """
        return self._parent_for(self.size(), [(j,i) for i in xrange(1,self.size()) for j in xrange(i+1,self.size()+1)])

    def get_poset(self):
        r"""
        Return the weak order poset on the relations of ``self``
        """
        E = list(self)
        return Poset((E,lambda x,y: x.lequal(y)))

    def isSubLattice(self):
        r"""
        Return True if ``self`` forms a sublattice of the weak order lattice
        on integer relations

        EXAMPLES::

            sage: Relations(3,anti_symmetric = True).isSubLattice()
            True
            sage: Relations(3, transitive = True).isSubLattice()
            The relation of size 3 given by relations ((2, 3),) The relation of size 3 given by relations ((1, 2),)
            False
        """
        L = list(self)
        for ip1 in L:
            for ip2 in L:
                m = self.meet(ip1,ip2)
                if not m in L:
                    print ip1, ip2
                    return False
        return True


def minimals(S):
    minimal = []
    for r in S:
        for r2 in minimal:
            if r2.lequal(r):
                break
            elif r.lequal(r2):
                minimal = [r3 for r3 in minimal if not r.lequal(r3)]
                minimal.append(r)
                break
        else:
            minimal.append(r)
    return minimal

def minimal_primitives(n):
    r = Relations(n).minimal_element()
    prims = []
    L = {r}
    while len(L) != 0:
        L2 = set()
        for r in L:
            if r.is_primitive():
                if all(not p.lequal(r) for p in prims):
                    prims.append(r)
            else:
                L2.update(r.succ())
        L = L2
        print len(prims)
        print len(L)
    return prims




def maximals(S):
    maximal = []
    for r in S:
        for r2 in maximal:
            if r.lequal(r2):
                break
            elif r2.lequal(r):
                maximal = [r3 for r3 in maximal if not r3.lequal(r)]
                maximal.append(r)
                break
        else:
            maximal.append(r)
    return maximal

def testOrderPreserving(E, f):
    for r1 in E:
        for r2 in E:
            if r1.lequal(r2):
                if not f(r1).lequal(f(r2)):
                    print r1, r2
                    return False
    return True

def relations_interval(rmin, rmax):
    if not rmin.lequal(rmax):
        return
    level0 = {rmin,}
    yield rmin
    while len(level0)>0:
        level1 = set()
        for r in level0:
            for r2 in r.succ():
                if not r2 in level1 and r2.lequal(rmax):
                    yield r2
                    level1.add(r2)
        level0 = level1

def test_maximal_antichains(size):
    relation_poset = [r for r in Relations(size) if r.is_poset()]
    for r in relation_poset:
        p = IntegerPoset(size, r.relations())
        if not r.maximal_antichains() == p.maximal_antichains():
            return r, p
    return True
