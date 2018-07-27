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
from sage.misc.cachefunc import cached_method, cached_function

from relations import Relation, Relations, Relations_all, Relations_size



class IntegerPoset(Relation):
    __metaclass__ = InheritComparisonClasscallMetaclass

    @staticmethod
    def __classcall_private__(cls, *args, **opts):
        P = IntegerPosets_all()
        return P.element_class(P, *args, **opts)

    def __init__(self, parent, size, relations, sign = None):
        r"""
        TESTS::

            sage: TamariIntervalPoset(3,[(1,2),(3,2)]).parent()
            Interval-posets
        """
        self._size = size
        self._poset = Poset((range(1, size + 1), relations))
        Relation.__init__(self, parent, size, self._poset.relations(), sign)
        if self._poset.cardinality() != size:
            # This can happen as the Poset constructor automatically adds
            # in elements from the relations.
            raise ValueError("The relations do not correspond to the size of the poset.")

        self._cover_relations = tuple(self._poset.cover_relations())
        self._latex_options = dict()

    def poset(self):
        return self._poset

    def __hash__(self):
        def cmp_relation(r1, r2):
            if r1[0] < r2[0]:
                return -1
            if r1[0] > r2[0]:
                return 1
            if r1[1] < r2[1]:
                return -1
            if r1[1] > r2[1]:
                return 1
            return 0

        relations = self._poset.relations()
        relations.sort(cmp=cmp_relation)
        rel_tuple = tuple([tuple(x) for x in relations])
        return hash(rel_tuple)

    @cached_method
    def increasing_cover_relations(self):
        relations = []
        n = self.size()
        for i in self:
            js = []
            for j in xrange(i+1,n+1):
                if self.le(i,j) and all([not self.le(k,j) for k in js]):
                    js.append(j)
                    relations.append((i,j))
        return tuple(relations)

    @cached_method
    def decreasing_cover_relations(self):
        relations = []
        for i in self:
            js = []
            for j in xrange(i-1,0,-1):
                if self.le(i,j) and all([not self.le(k,j) for k in js]):
                    js.append(j)
                    relations.append((i,j))
        return tuple(relations)


    def cover_relations(self):
        return self._poset.cover_relations()


    def le(self, e1, e2):
        r"""
        Return whether ``e1`` precedes or equals ``e2`` in ``self``.

        """
        return self._poset.le(e1, e2)

    def lt(self, e1, e2):
        r"""
        Return whether ``e1`` strictly precedes ``e2`` in ``self``.

        """
        return self._poset.lt(e1, e2)

    def ge(self, e1, e2):
        r"""
        Return whether ``e2`` precedes or equals ``e1`` in ``self``.

        """
        return self._poset.ge(e1, e2)

    def gt(self, e1, e2):
        r"""
        Return whether ``e2`` strictly precedes ``e1`` in ``self``.

        """
        return self._poset.gt(e1, e2)


    def meet(self, i2):
        return IntegerPosets(self.size()).meet(self,i2)

    def meet_woip(self, i2):
        return self.parent().meet_woip(self,i2)

    def meet_wof(self, i2):
        return self.parent().meet_wof(self,i2)


    def _repr_(self):
        s= "The integer poset of size {} induced by relations {}".format(self.size(),
            self.increasing_cover_relations() + self.decreasing_cover_relations())
        if self.is_signed():
            s+= " with orientation {}".format(self.sign())
        return s

    def __eq__(self, other):
        if (not isinstance(other, IntegerPoset)):
            return False
        return self.size() == other.size() and self._cover_relations == other._cover_relations and self._latex_options == other._latex_options
        # the latex_options is a weird one to check BUT otherwise it gets messy when drawing the posets with different latex options

    def __ne__(self, other):
        return not (self == other)

    def __iter__(self):
        return xrange(1,self.size()+1).__iter__()


    def is_linear_extension(self, perm):
        r"""
        Return whether the permutation ``perm`` is a linear extension
        of ``self``.

        INPUT:

        - ``perm`` -- a permutation of the size of ``self``

        """
        return self._poset.is_linear_extension(perm)



    def subposet(self, start, end):
        p = self._poset.subposet(range(start,end))
        p = p.relabel(lambda x: x-start+1)
        return IntegerPoset(len(p),p.relations())


    def linear_extensions(self):
        r"""
        Return an iterator on the permutations which are linear
        extensions of ``self``.
        """
        for ext in self._poset.linear_extensions():
            yield Permutation(ext)

    def minimal_permutation(self):
        p = []
        pos = self._poset
        can_add = set(pos.minimal_elements())
        while len(can_add) > 0:
            e = min(can_add)
            can_add.remove(e)
            p.append(e)
            can_add.update(v for v in pos.upper_covers_iterator(e) if all(not pos.le(w,v) for w in can_add))

        return Permutation(p)

    def maximal_permutation(self):
        p = []
        pos = self._poset
        can_add = set(pos.minimal_elements())
        while len(can_add) > 0:
            e = max(can_add)
            can_add.remove(e)
            p.append(e)
            can_add.update(v for v in pos.upper_covers_iterator(e) if all(not pos.le(w,v) for w in can_add))

        return Permutation(p)

    def minimal_linear_extension(self):
        p = self.minimal_permutation()
        return IntegerPoset(len(p), [(p[i],p[i+1]) for i in xrange(len(p)-1)])

    def maximal_linear_extension(self):
        p = self.maximal_permutation()
        return IntegerPoset(len(p), [(p[i],p[i+1]) for i in xrange(len(p)-1)])

    def deminimalize_fiber(self, over_set = None, created = None):
        if over_set is None:
            over_set = IntegerPosets(woip = True)
        if created is None:
            created = set()
        if not self in created and self in over_set:
            created.add(self)
            yield self
            D = self.decreasing_relations()
            I = self.increasing_relations()
            for i in self.increasing_cover_relations():
                p = IntegerPoset(self.size(), D + tuple(r for r in I if r!= i))
                for q in p.deminimalize_fiber(over_set, created):
                    yield q

    def succ(self):
        rels = self.increasing_cover_relations()
        for (i,j) in rels:
            p2 = IntegerPoset(self.size(),[(a,b) for (a,b) in self.relations() if (a,b)!=(i,j)])
            if p2!=self:
                yield p2

        for (i,j) in self.non_relations():
            if all([self.le(j,k) for k in self if self.le(i,k) and k!=i]) and all([self.le(k,i) for k in self if self.le(k,j) and k!=j]):
                yield IntegerPoset(self.size(),self.cover_relations() + [(j,i)])

    def greater(self):
        r"""
        Return an iterator on integer posets greater that ``self`` in integer poset lattice
        """
        R = RecursivelyEnumeratedSet([self], lambda x: list(x.succ()))
        for ip in R:
            yield ip

    @cached_method
    def antichain_inc(self,a,c):
        if not self.le(a,c):
            return True
        for b in xrange(a+1,c):
            if not self.le(a,b) and self.antichain_inc(b,c):
                return True
        return False

    @cached_method
    def antichain_dec(self,a,c):
        if not self.le(c,a):
            return True
        for b in xrange(c-1,a,-1):
            if not self.le(c,b) and self.antichain_dec(a,b):
                return True
        return False

    def woipize(self):
        nr = []
        for a in self:
            for c in xrange(a+1,self.size()+1):
                if self.le(a,c):
                    if not self.antichain_inc(a,c):
                        nr.append((a,c))
                elif self.le(c,a):
                    if not self.antichain_dec(a,c):
                        nr.append((c,a))
        return IntegerPoset(self.size(),nr)

    def iwoipize(self):
        nr = []
        for a in self:
            for c in xrange(a+1,self.size()+1):
                if self.le(a,c):
                    if not self.antichain_inc(a,c):
                        nr.append((a,c))
                elif self.le(c,a):
                    nr.append((c,a))
        return IntegerPoset(self.size(),nr)

    def increasing_pip_valid(self, sign, a, c):
        for n in xrange(a,c):
            if n == a or (sign[n-1] == -1 or sign[n-1] == 2):
                for p in xrange(n+1,c+1):
                        if p == c or (sign[p-1] == 1 or sign[p-1] == 2):
                            if (n!= a or p !=c) and  not self.le(n,p):
                                return False
        return True

    def decreasing_pip_valid(self, sign, a, c):
        for p in xrange(a,c):
            if p == a or (sign[p-1] == 1 or sign[p-1] == 2):
                for n in xrange(p+1,c+1):
                    if n == c or (sign[n-1] == -1 or sign[n-1] == 2):
                        if (p != a or n != c) and not self.le(n,p):
                            return False
        return True

    def pipize(self, sign = None):
        if sign is None:
            sign = self.sign()
        # takes a woip and make it a pip
        nrel = []
        for a in self:
            for c in xrange(a+1, self.size()+1):
                if self.le(a,c):
                    if self.increasing_pip_valid(sign, a, c):
                        nrel.append((a,c))
                if self.le(c,a):
                    if self.decreasing_pip_valid(sign, a, c):
                        nrel.append((c,a))
        return IntegerPoset(self.size(),nrel, sign)

    def depipize_extensions(self,  sign = None, over_set = None):
        if over_set is None:
            over_set = IntegerPosets(woip = True)
        if sign is None:
            sign = self.sign()
        n = self.size()
        forbiden = [(a,c) for a in self for c in xrange(a+1,n+1) if self.increasing_pip_valid(sign, a, c)]
        forbiden.extend((c,a) for c in self for a in xrange(c-1,0,-1) if self.decreasing_pip_valid(sign, a, c))
        return over_set.restricted_extensions(self, forbiden)

    def depipize_poset_extensions(self,  sign = None):
        return self.depipize_extensions(sign, IntegerPosets())

    def toipize(self):
        sign = tuple(-1 for i in xrange(self.size()))
        return self.pipize(sign)

    def detoipize_extensions(self):
        sign = tuple(-1 for i in xrange(self.size()))
        return self.depipize_extensions(sign)

    def detoipize_poset_extensions(self):
        sign = tuple(-1 for i in xrange(self.size()))
        return self.depipize_poset_extensions(sign)

    def dewoipize_extensions(self):
        # tmp implementation
        d = self.parent().finite_set(self.size()).dewoipize_dict()
        return d[self]

    def deiwoipize_extensions(self):
        # tmp implementation
        d = self.parent().finite_set(self.size()).deiwoipize_dict()
        return d[self]

    def wofaddinc(self):
        rel = self.relations()
        nrel = list(rel)
        n = self.size()
        ip = self
        for d in xrange(2, n):
            for a in xrange(1,n-d+1):
                c = a+d
                if not ip.le(a,c) and not ip.le(c,a):
                    for b in xrange(a+1,c):
                        if ip.le(a,b):
                            if not ip.le(c,b):
                                nrel.append((a,c))
                        elif ip.le(b,c):
                            if not ip.le(b,a):
                                nrel.append((a,c))
            ip = IntegerPoset(self.size(),nrel, self.sign())
        return ip


    def pfpaddinc(self, sign = None):
        if sign is None:
            sign = self.sign()
        rel = self.relations()
        nrel = list(rel)
        n = self.size()
        ip = self
        for d in xrange(2, n):
            for a in xrange(1,n-d+1):
                c = a+d
                if not ip.le(a,c) and not ip.le(c,a):
                    for b in xrange(a+1, c):
                        if sign[b-1] == -1 or sign[b-1] == 2:
                            if not ip.le(b,a) and not ip.le(b,c):
                                break
                        if sign[b-1] == 1 or sign[b-1] == 2:
                            if not ip.le(a,b) and not ip.le(c,b):
                                break
                    else:
                        for b in xrange(a+1,c):
                            if (sign[b-1] == 1 or sign[b-1] == 0) and ip.le(a,b):
                                if not ip.le(c,b):
                                    nrel.append((a,c))
                            elif (sign[b-1] == -1 or sign[b-1] == 0) and ip.le(b,c):
                                if not ip.le(b,a):
                                    nrel.append((a,c))
            ip = IntegerPoset(self.size(),nrel, sign)
        return ip

    def pfpaddinc2(self, sign):
        if sign is None:
            sign = self.sign()
        def pique(a, c):
            for b in xrange(a+1,c):
                if sign[b-1] == -1 or sign[b-1] == 2:
                    if not self.le(b,a) and not self.le(b,c):
                        return True
                if sign[b-1] == 1 or sign[b-1] == 2:
                    if not self.le(a,b) and not self.le(c,b):
                        return True
            return False
        rel = self.relations()
        nrel = list(rel)
        n = self.size()
        for a in self:
            for d in xrange(a+2,n+1):
                for b in xrange(a,d):
                    if sign[b-1] == -1 or sign[b-1] == 0:
                        if b == a or not self.le(b,a):
                            for c in xrange(b+1,d+1):
                                if sign[d-1] == 1 or sign[d-1] == 0:
                                    if c == d or not self.le(d,c):
                                        if self.le(b,c):
                                            if (a != b and not pique(a,c)) or ( c!= d and not pique(b,d)):
                                                nrel.append((a,d))
        return IntegerPoset(n, nrel, sign)

    def pfp_min_permutree(self, sign = None):
        if sign is None:
            sign = self.sign()
        addrel = []
        for a in self:
            for c in xrange(a+1,self.size()+1):
                if not self.rel(a,c) and not self.rel(c,a):
                    for b in xrange(a+1,c):
                        if sign[b-1] == -1 or sign[b-1] == 2:
                            if not self.rel(b,a) and not self.rel(b,c):
                                break
                        if sign[b-1] == 1 or sign[b-1] == 2:
                            if not self.rel(a,b) and not self.rel(c,b):
                                break
                    else:
                        addrel.append((a,c))
        L = list(self.relations()) + addrel
        return IntegerPoset(self.size(), L)



    def is_total(self):
        return self.parent().is_total(self)

    def is_woip(self):
        return self.parent().is_woip(self)

    def is_iwoip(self):
        return self.parent().is_iwoip(self)

    def is_pip(self,sign = None):
        if sign is None:
            sign = self.sign()
        return self.parent().is_pip(self, sign = sign)

    def is_pep(self,sign = None):
        if sign is None:
            sign = self.sign()
        return self.parent().is_pep(self, sign = sign)

    def is_pfp(self, sign = None):
        if sign is None:
            sign = self.sign()
        return self.parent().is_pfp(self, sign = sign)

    def is_toip(self):
        return self.parent().is_toip(self)

    def is_tof(self):
        return self.parent().is_tof(self)

    def cone(self):
        V = [[1]*self.size(),[-1]*self.size()]
        for i,j in self.relations():
            v = [0] * self.size()
            v[i-1] = 1
            v[j-1] = -1
            V.append(v)
        C = Cone(V)
        #return C
        return C.dual()



class IntegerPosets(Relations):

    @staticmethod
    def __classcall_private__(cls, n=None, **keywords):

        if n is None:
            return IntegerPosets_all(**keywords)

        if n not in NN:
            raise ValueError("n must be a non negative integer")
        return IntegerPosets_size(Integer(n), **keywords)



    def __call__(self, *args, **keywords):

        if isinstance(args[0], IntegerPoset):
            return args[0]
        if len(args) == 1 and isinstance(args[0], FinitePoset):
            return self.element_class(IntegerPosets(), args[0].cardinality(), args[0].cover_relations(), self._sign)
        if len(args) == 1 and isinstance(args[0], Relation):
            return self.element_class(IntegerPosets(), args[0].size(), args[0].relations(), args[0].sign())

        return super(IntegerPosets, self).__call__(*args, **keywords)

    def prop_string(self):
        props = set(self.properties())
        props.remove("transitive")
        props.remove("anti_symmetric")
        if len(props)!=0:
            strings = [self._print_property(p) for p in props]
            return " with properties: " + ", ".join(strings)
        return ""

    def _get_sign(self, param, x, sign):
        """
        Priority: ``sign``, ``x.sign()`` ``param`` ``self.sign()``
        """
        if not sign is None:
            return sign
        if x.is_signed():
            return x.sign()
        sign = self.parameter("pfp")
        if not sign is None:
            return sign
        if self.is_signed():
            return self.sign()
        raise ValueError("Must specify a sign parameter")


    def meet(self, i1, i2):
        r = Relations.meet(self, i1, i2)
        r = r.increasingClosure()
        r = r.transDelDec()
        return self(r)

    def meet_woip(self, i1, i2):
        return self.meet(i1,i2).woipize()

    def meet_wof(self,  i1, i2):
        woip = self.meet_woip(i1,i2)
        return woip.wofaddinc()

    def meet_pfp(self,  i1, i2, sign = None):
        sign = self._get_sign(self, "pfp", i1, sign)
        pip = self.meet_woip(i1,i2)
        return pip.pfpaddinc(sign)

    def meet_pfp2(self,  i1, i2, sign = None):
        sign = self._get_sign(self, "pfp", i1, sign)
        pip = self.meet_woip(i1,i2)
        return pip.pfpaddinc2(sign)

    def is_total(self, x):
        n = x.size()
        nbr = len(x.relations())
        return nbr == n*(n-1)/2

    def is_woip(self, x):
        # Weak order intervals
        r = x.relations()
        for u, v in r:
            if u < v:
                a, c = u, v
                for b in xrange(a+1, c):
                    if not (b,c) in r and not (a,b) in r:
                        return False
            else:
                a, c = v, u
                for b in xrange(a+1, c):
                    if not (c,b) in r and not (b,a) in r:
                        return False
        return True

    def is_iwoip(self, x):
        # Weak order intervals
        r = x.relations()
        for u, v in r:
            if u < v:
                a, c = u, v
                for b in xrange(a+1, c):
                    if not (b,c) in r and not (a,b) in r:
                        return False
        return True


    def is_wof(self, x): # faces of permutohedron: strict weak ordering
        for (i,j) in x.relations():
            for z in x:
                if not x.rel(i,z) and not x.rel(z,j):
                    return False
        return True

    def is_wof2(self, x):
        if not self.is_woip(x):
            return False
        for a in x:
            for c in xrange(a+2,x.size()+1):
                if not x.rel(a,c) and not x.rel(c,a):
                    for b in xrange(a+1,c):
                        if not (not x.rel(a,b) and not x.rel(b,a) and not x.rel(b,c) and not x.rel(c,b))  and not (x.rel(a,b) and x.rel(c,b)) and not (x.rel(b,a) and x.rel(b,c)):
                            return False
        return True


    def is_toip(self, x):
        # Tamari order intervals
        r = x.relations()
        # Is Tamari interval poset
        for u, v in r:
            if u < v:
                # a < c, aXc
                a = u
                c = v
                for b in range(a + 1, c):
                    if not (b, c) in r:
                        return False
            elif u > v:
                # a < c, cXa
                a = v
                c = u
                for b in range(a + 1, c):
                    if not (b, a) in r:
                        return False

        return True

    def is_tof(self, x):
        """
        The algorithm follows these steps:

        - If the poset is not a Tamari interval poset, it's not a face
        of the Tamari order.

        - for every couple of letter a, c such that a < c:
          - if a is not smaller that c in the poset and if we have (for
            every a < b < c, we have b smaller than c in the poset) and
            we do not have (for every a < b < c, b smaller than a in the
            poset) then the poset is not a face of the Tamari order.

          - if c is not smaller that a in the poset and if we have (for
            every a < b < c, we have b smaller than a in the poset) and
            we do not have (for every a < b < c, b smaller than c in the
            poset) then the poset is not a face of the Tamari order.
        """
        if not self.is_toip(x):
            return False

        r = x.relations()
        for a in range(1, x.size()):
            for c in range(a, x.size() + 1):
                if not (a, c) in r:
                    if all([(b, c) in r for b in range(a + 1, c)]) and \
                       not all([(b, a) in r for b in range(a + 1, c)]):
                        return False
                if not (c, a) in r:
                    if all([(b, a) in r for b in range(a + 1, c)]) and \
                       not all([(b, c) in r for b in range(a + 1, c)]):
                        return False

        return True

    def is_pip(self, x, sign = None):
        sign = self._get_sign("pip", x, sign)
        for a in x:
            for c in xrange(a+2,x.size()+1):
                if x.rel(a,c):
                    for b in xrange(a+1,c):
                        if sign[b-1] == -1:
                            if not x.rel(b,c):
                                return False
                        if sign[b-1] == 1:
                            if not x.rel(a,b):
                                return False
                        if sign[b-1] == 2:
                            if not x.rel(b,c) or not x.rel(a,b):
                                return False
                        if sign[b-1] == 0:
                            if not x.rel(a,b) and not x.rel(b,c):
                                return False
                if x.rel(c,a):
                    for b in xrange(a+1,c):
                        if sign[b-1] == -1:
                            if not x.rel(b,a):
                                return False
                        if sign[b-1] == 1:
                            if not x.rel(c,b):
                                return False
                        if sign[b-1] == 2:
                            if not x.rel(b,a) or not x.rel(c,b):
                                return False
                        if sign[b-1] == 0:
                            if not x.rel(b,a) and not x.rel(c,b):
                                return False
        return True

    def is_pipplus(self, x, sign = None):
        sign = self._get_sign("pipplus", x, sign)
        for a in x:
            for c in xrange(a+2,x.size()+1):
                if x.rel(a,c):
                    for b in xrange(a+1,c):
                        if sign[b-1] == 1 or sign[b-1] == 2:
                            if not x.rel(a,b):
                                return False
                if x.rel(c,a):
                    for b in xrange(a+1,c):
                        if sign[b-1] == 1 or sign[b-1] == 2:
                            if not x.rel(c,b):
                                return False
        return True

    def is_pipminus(self, x, sign = None):
        sign = self._get_sign("pipminus", x, sign)
        for a in x:
            for c in xrange(a+2,x.size()+1):
                if x.rel(a,c):
                    for b in xrange(a+1,c):
                        if sign[b-1] == -1 or sign[b-1] == 2:
                            if not x.rel(b,c):
                                return False
                if x.rel(c,a):
                    for b in xrange(a+1,c):
                        if sign[b-1] == -1 or sign[b-1] == 2:
                            if not x.rel(b,a):
                                return False
        return True

    @cached_method
    def pep_compatible_norel(self, x, a, c, sign = None):
        sign = self._get_sign("pep_compatible_norel", x, sign)
        if x.rel(a,c) or x.rel(c,a):
            return True
        for b in xrange(a+1,c):
            if sign[b-1] == -1 or sign[b-1] == 2: # incoming
                if x.rel(a,b) and self.pep_compatible_norel(x,b,c,sign):
                    return True
            if sign[b-1] == 1 or sign[b-1] == 2: #outgoing
                if x.rel(b,a) and self.pep_compatible_norel(x,b,c,sign):
                    return True
        return False


    def is_pep_norel(self, x, sign = None):
        sign = self._get_sign("pep_norel", x, sign)
        for a in x:
            for c in xrange(a+1,x.size()+1):
                if not self.pep_compatible_norel(x,a,c,sign):
                    return False
        return True


    def is_pfp_norel(self, x, sign = None):
        sign = self._get_sign("pfp_norel", x, sign)

        def compatible(a,c):
            if x.rel(a,c) or x.rel(c,a):
                return True
            for b in xrange(a+1,c):
                if sign[b-1] == -1 or sign[b-1] == 2:
                    if not x.rel(b,a) and not x.rel(b,c):
                        return True
                if sign[b-1] == 1 or sign[b-1] == 2:
                    if not x.rel(a,b) and not x.rel(c,b):
                        return True
            for b in xrange(a+1,c):
                if x.rel(b,a) and not x.rel(b,c):
                    return False
                if x.rel(b,c) and not x.rel(b,a):
                    return False
                if x.rel(a,b) and not x.rel(c,b):
                    return False
                if x.rel(c,b) and not x.rel(a,b):
                    return False
            return True

        for a in x:
            for c in xrange(a+2,x.size()+1):
                if not compatible(a,c):
                    return False
        return True

    def is_pep(self, x, sign = None):
        sign = self._get_sign("pep", x, sign)
        return self.is_pip(x,sign) and self.is_pep_norel(x,sign)

    def is_pfp(self, x, sign = None):
        sign = self._get_sign("pfp", x, sign)
        return self.is_pip(x,sign) and self.is_pfp_norel(x,sign)

    def is_boe(self,x):
        return self.is_pep(x,tuple(2 for i in x))

    def is_bof(self, x):
        return self.is_boip(x)

    def is_boip(self,x):
        return self.is_pip(x,tuple(2 for i in x))

    def is_snake_neg(self,x):
        return self.is_pep_norel(x, tuple(-1 for i in x))

    # checked toip + snage_neg give catalan up to size 5
    def is_tree(self, x):
        return self.is_toip(x) and self.is_snake_neg(x)


class IntegerPosets_all(IntegerPosets, Relations_all):
    r"""
    The enumerated set of all integer posets.
    """
    def __init__(self, **keywords):
        DisjointUnionEnumeratedSets.__init__(
            self, Family(NonNegativeIntegers(), lambda i : IntegerPosets_size(i, **keywords)),
            facade=True, keepkey=False, category=(Posets(), EnumeratedSets()))
        keywords["transitive"] = True
        keywords["anti_symmetric"] = True
        self._sign = None
        self._initialise_properties(keywords)


    def _repr_(self):
        r"""
        TEST::

            sage: TamariIntervalPosets()
            Interval-posets
        """
        return "Integer posets" + self.prop_string()

    def _element_constructor_(self, size, relations, sign = None):
        return self.element_class(self, size, relations, sign)

    Element = IntegerPoset


class IntegerPosets_size(IntegerPosets, Relations_size):
    r"""
    The enumerated set of integer posets of a given size.

    """
    def __init__(self, size, **keywords):
        r"""

        """
        Parent.__init__(self, category=FiniteEnumeratedSets())
        keywords["transitive"] = True
        keywords["anti_symmetric"] = True
        self._size = size
        self._initialise_properties(keywords)

    def _repr_(self):
        r"""

        """
        return "Integer posets of size {}".format(self._size) + self.prop_string()


    @lazy_attribute
    def _parent_for(self):
        r"""
        The parent of the element generated by ``self``.

        """
        return IntegerPosets_all()


    def indecomposables(self):
        for p in self:
            if p.is_indecomposable():
                yield p

    def indecomposables_ideal(self):
        n = self.size()
        P = IntegerPoset(n,[(i,j) for i in xrange(1,n+1) for j in xrange(i+1,n+1)])
        yield P
        level0 = {P,}
        while len(level0)>0:
            level1 = set()
            for p in level0:
                for p2 in p.succ():
                    if not p2 in level1 and p2.is_indecomposable():
                        yield p2
                        level1.add(p2)
            level0 = level1

    def indecomposable_generators(self):
        n = self.size()
        P = IntegerPoset(n,[(i,j) for i in xrange(1,n+1) for j in xrange(i+1,n+1)])
        level0 = {P,}
        while len(level0)>0:
            level1 = set()
            for p in level0:
                hassuccs = False
                for p2 in p.succ():
                    if p2.is_indecomposable():
                        hassuccs = True
                        level1.add(p2)

                if not hassuccs:
                    yield p
            level0 = level1

    @cached_method
    def dewoipize_dict(self):
        d = {}
        for ip in self:
            wip = ip.woipize()
            s = d.get(wip, set())
            s.add(ip)
            d[wip] = s
        return d

    @cached_method
    def deiwoipize_dict(self):
        d = {}
        for ip in self:
            wip = ip.iwoipize()
            s = d.get(wip, set())
            s.add(ip)
            d[wip] = s
        return d




def interval(pmin,pmax):
    if not pmin.lequal(pmax):
        return
    level0 = {pmin,}
    yield pmin
    while len(level0)>0:
        level1 = set()
        for p in level0:
            for p2 in p.succ():
                if not p2 in level1 and p2.lequal(pmax):
                    yield p2
                    level1.add(p2)
        level0 = level1

def interval_woip(pmin,pmax):
    if not pmin.lequal(pmax):
        return
    level0 = {pmin,}
    yield pmin
    while len(level0)>0:
        level1 = set()
        for p in level0:
            for p2 in p.succ():
                if p2.is_woip() and not p2 in level1 and p2.lequal(pmax):
                    yield p2
                    level1.add(p2)
        level0 = level1

#tested up to size 5
def test_squares(size):
    for p in IntegerPosets(size):
        ss = list(p.succ())
        if len(ss)!=1:
            for s1 in ss:
                s1s = list(s1.succ())
                for s2 in ss:
                    if s2!=s1:
                        s2s = list(s2.succ())
                        if len([e for e in s1s if e in s2s])!=0:
                            break
                else:
                    print "not a square"
                    print p, s1
                    return False
    return True

def count_squares(size):
    nb = 0
    for p in IntegerPosets(size):
        ss = list(p.succ())
        if len(ss)!=1:
            for s1 in ss:
                s1s = list(s1.succ())
                for s2 in ss:
                    if s2!=s1:
                        s2s = list(s2.succ())
                        if len([e for e in s1s if e in s2s])!=0:
                            nb+=1
    return nb/2

def get_grades(size):
    grd = {}
    for p in IntegerPosets(size):
        g = p.grade()
        e = grd.get(g,[])
        e.append(p)
        grd[g]=e
    return grd

def distri_stat(ens, f):
    distri = {}
    for el in ens:
        stat = f(el)
        if distri.has_key(stat):
            distri[stat]+=1
        else:
            distri[stat]=1
    return distri

def test_indecomposable_ideal(size):
    indec = set()
    dec = set()
    for p in IntegerPosets(size):
        if not p.is_indecomposable():
            if not all([not p.lequal(indp) for indp in indec]):
                print str(p) + " is smaller than the indec " + str(indp)
                return False
            dec.add(p)
        else:
            if not all([not decp.lequal(p) for decp in dec]):
                print str(decp) + " is smaller than the indec " + str(p)
                return False
            indec.add(p)
    return True


def test_join(size):

    IP = list(IntegerPosets(size))
    for i1 in IP:
        for i2 in IP:
            try:
                j = i1.join(i2)
            except:
                print i1, i2
                print "Cannot construct the join"
                return False
            if not (i1.lequal(j) and i2.lequal(j)):
                print "the join is not bigger"
                print i1, i2, j
                return False
            for i3 in IP:
                if i1.lequal(i3) and i2.lequal(i3):
                    if not j.lequal(i3):
                        print "the join is not the join"
                        print i1, i2, j, i3
                        return False
    return True

##############################
## Test Poset Sub lattices
##############################


# tested 3, 4, 5
def testPermutationSubLattice(n):
    return IntegerPosets(n, total = True).isSubLattice()

# False for 3
# The integer poset of size 3 induced by relations [(3, 2), (3, 1)] The integer poset of size 3 induced by relations [(2, 1), (3, 1)]
def testWoipSubLattice(n):
    return IntegerPosets(n, woip = True).isSubLattice()

# False for 3
# The integer poset of size 3 induced by relations [] The integer poset of size 3 induced by relations [(1, 2), (3, 2)]
def testWofSubLattice(n):
    return IntegerPosets(n, wof = True).isSubLattice()

# False for 3
# The integer poset of size 3 induced by relations [] The integer poset of size 3 induced by relations [(2, 3), (2, 1)]
def testTofSubLattice(n):
    return IntegerPosets(n, tof = True).isSubLattice()

# tested 3, 4, 5
def testToipSubLattice(n):
    return IntegerPosets(n, toip = True).isSubLattice()

# tested 3, ..., 6
def testTreesSubLattice(n):
    return IntegerPosets(n, tree = True).isSubLattice()

# tested ... 6
def testBoeSubLattice(n):
    return IntegerPosets(n, boe = True).isSubLattice()

# tested ... 6
def testBoipSubLattice(n):
    return IntegerPosets(n, boip = True).isSubLattice()

# tested ... 5
def testBofSubLattice(n):
    return IntegerPosets(n, bof = True).isSubLattice()

# tested 3,4
# cardinality 1,1,2,7,38,300,3304
def testSnakeSubLattice(n):
    return IntegerPosets(n, snake_neg = True).isSubLattice()

# tested up to 5 with
# sign = (-1,1,2,-2,1)
# sign = (-1,2,2,-1,1)
# sign = (0,0,0,0,0) (Perms)
# sign = (0,0,0,-1,0)
# sign = (0,0,-1,0,0)
def testPepNoRelSublattice(n, sign):
    return IntegerPosets(n, pep_norel = sign).isSubLattice()

# False on (0,1,0,-1,0)
# The integer poset of size 5 induced by relations ((2, 3), (2, 1), (4, 3), (4, 2), (5, 4)) The integer poset of size 5 induced by relations ((3, 4), (2, 1), (3, 2), (4, 2), (5, 4))
def testPepSublattice(sign):
    return IntegerPosets(len(sign),pep=sign).isSubLattice()


def testpipMinusSublattice(sign):
    return IntegerPosets(len(sign),pipminus=sign).isSubLattice()

################################################

def testTrees():
    return [IntegerPosets(n, tree= True).cardinality() for n in xrange(7)]


#########################################

# tester ... 6
def testWoipize(n):
    for ip in IntegerPosets(n):
        woip = ip.woipize()
        if ip.is_woip() and not ip == woip:
            print ip, woip
            return False
        if not woip.is_woip():
            print ip, woip
            return False
    return True

# tested 3,4,5
def testWoipizeTest(n):
    for ip in IntegerPosets(n):
        woip = ip.woipize_test()
        if ip.is_woip() and not ip == woip:
            print "not stable"
            print ip, woip
            return False
        if not woip.is_woip():
            print "don't make woip"
            print ip, woip
            return False
    return True

# tested 3,4,5
def testEqualWoipizeTestWoipize(n):
    for ip in IntegerPosets(n):
        woip = ip.woipize_test()
        woip2 = ip.woipize()
        if not woip == woip2:
            print ip, woip, woip2
            return False
    return True



# tested .. 5
def test_woip_meet(size):

    IP = list(IntegerPosets(size, woip = True))
    for i1 in IP:
        for i2 in IP:
            j = i1.meet_woip(i2)
            if not (j.lequal(i1) and j.lequal(i2)):
                print "the meet is not smaller"
                print i1, i2, j
                return False
            for i3 in IP:
                if i3.lequal(i1) and i3.lequal(i2):
                    if not i3.lequal(j):
                        print "the meet is not the meet"
                        print i1, i2, j, i3
                        return False
    return True



# false 3
# The integer poset of size 3 induced by relations () The integer poset of size 3 induced by relations ((2, 3), (2, 1))
def test_tof_woipsublattice(n):
        S = IntegerPosets(n,tof=True)
        L = list(S)
        for ip1 in L:
            for ip2 in L:
                m = S.meet_woip(ip1,ip2)
                if not m in S:
                    print ip1, ip2
                    return False
        return True

# false 3
# The integer poset of size 3 induced by relations () The integer poset of size 3 induced by relations ((1, 2), (3, 2))
def test_wof_woipsublattice(n):
        S = IntegerPosets(n,wof=True)
        L = list(S)
        for ip1 in L:
            for ip2 in L:
                m = S.meet_woip(ip1,ip2)
                if not m in S:
                    print ip1, ip2
                    return False
        return True

# tested 3,4,5
def testWofaddincStable(n):
    for ip in IntegerPosets(n, wof=True):
        wof = ip.wofaddinc()
        if ip != wof:
            print ip, wof
            return False
    return True


# tested 3,4,5
def test_wof_meet(size):
    S = IntegerPosets(size, wof = True)
    IP = list(S)
    for i1 in IP:
        for i2 in IP:
            j = i1.meet_wof(i2)
            if not j in S:
                print "the meet is not a face"
                print i1, i2, j
                return False
            if not (j.lequal(i1) and j.lequal(i2)):
                print "the meet is not smaller"
                print i1, i2, j
                return False
            for i3 in IP:
                if i3.lequal(i1) and i3.lequal(i2):
                    if not i3.lequal(j):
                        print "the meet is not the meet"
                        print i1, i2, j, i3
                        return False
    return True

# tested
# (0,0,0,0)
# (0,-1,-1,0)
# (0,-1,0,1,0)
# (0,2,0,1,0)
def testPfpaddincStable(sign):
    n = len(sign)
    for ip in IntegerPosets(n, pfp=sign):
        pfp = ip.pfpaddinc(sign)
        if ip != pfp:
            print ip, wof
            return False
    return True


# tested all 3: *0 *-1 *1 *2
# tested 4:
# (0,0,0,0)
# (0,-1,-1,0)
# (0,-1,1,0)
# (0,-1,2,0)
# (0,-1,0,0)
# (0,-1,1,0,0)
# (0,-1,0,1,0)
def test_pfp_meet(sign):
    size = len(sign)
    S = IntegerPosets(size, pfp = sign)
    IP = list(S)
    for i1 in IP:
        for i2 in IP:
            j = S.meet_pfp(i1,i2)
            if not j in S:
                print "the meet is not a face"
                print i1, i2, j
                return False
            if not (j.lequal(i1) and j.lequal(i2)):
                print "the meet is not smaller"
                print i1, i2, j
                return False
            for i3 in IP:
                if i3.lequal(i1) and i3.lequal(i2):
                    if not i3.lequal(j):
                        print "the meet is not the meet"
                        print i1, i2, j, i3
                        return False
    return True

# 0 -1 -1 -1 0
# 0 1 0 -1 0
# 0 2 0 -1 0
def test_pfp_meet_partial(sign):
    size = len(sign)
    S = IntegerPosets(size, pfp = sign)
    IP = list(S)
    for i1 in IP:
        for i2 in IP:
            j = S.meet_pfp(i1,i2)
            if not j in S:
                print "the meet is not a face"
                print i1, i2, j
                return False
    return True

def pfp_meet_example_woip(sign):
    size = len(sign)
    S = IntegerPosets(size, pfp = sign)
    IP = list(S)
    for ip1 in IP:
        for ip2 in IP:
            m1 = ip1.meet_woip(ip2)
            if not m1.is_pfp(sign):
                m2 = m1.pfpaddinc(sign)
                print ip1, ip2
                print m1,m2


# tested on 0,-1,0,1,0
def test_pip_woipsublattice(sign):
    n = len(sign)
    S = IntegerPosets(n,pip=sign)
    L = list(S)
    for ip1 in L:
        for ip2 in L:
            m = S.meet_woip(ip1,ip2)
            if not m in S:
                print ip1, ip2
                return False
    return True

# tested on
# (0,0,0,0)
# (0,-1,-1,0)
# (0,-1,0,0)
# (0,-1,0,1,0)
# (0,-1,1,0,0)
def test_pep_woipsublattice(sign):
    n = len(sign)
    S = IntegerPosets(n,pep=sign)
    L = list(S)
    for ip1 in L:
        for ip2 in L:
            m = S.meet_woip(ip1,ip2)
            if not m in S:
                print ip1, ip2
                return False
    return True

#####

# tested on multiple signatrues up to size 5
def test_element_interval(sign):
    size = len(sign)
    elements = IntegerPosets(size, pep = sign)
    intervals = IntegerPosets(size, pip = sign)
    return len(elements.get_poset().relations()) == intervals.cardinality()


def getSignCardinalities(sign):
    size = len(sign)
    elements = IntegerPosets(size, pep = sign)
    intervals = IntegerPosets(size, pip = sign)
    return elements.cardinality(), intervals.cardinality()

def all_signs(size):
    def rec_all_signs(size, L):
        if len(L) == size-1:
            L.append(1)
            yield tuple(L)
            L.pop()
            return
        for v in xrange(-1,3):
            L.append(v)
            for l in rec_all_signs(size, L):
                yield l
            L.pop()
    for s in rec_all_signs(size, [1]):
        yield s

def count_all_signs(size):
    c = 0
    for s in all_signs(size):
        E = IntegerPosets(size, pep = s)
        c+= E.cardinality()
    return c

@cached_function
def catalan_decomp(sign):
    v = 0
    if not 0 in sign:
        return catalan_number(len(sign))
    for i in xrange(len(sign)):
        if sign[i] == 1 or sign[i] == -1:
            v+= signedElementsCardinality(sign[:i])*signedElementsCardinality(sign[i+1:])
    return v

@cached_function
def signedElementsCardinality(sign):
    n = len(sign)
    if len(sign) == 0 or len(sign) == 1:
        return 1
    if len(sign) == 2:
        return 2
    s = list(sign)
    s[0] = 1
    s[-1] = 1
    if 2 in s:
        i = s.index(2)
        return signedElementsCardinality(sign[:i+1])* signedElementsCardinality(sign[i:])
    J = [i for i in xrange(n) if s[i] == 0]
    if len(J) == n - 2:
        return factorial(n)
    if len(J) == 0:
        return catalan_number(n)
    C = 0
    for JJ in subsets(J):
        v = tuple(s[i] for i in xrange(len(s)) if s[i] != 0 or i in JJ)
        C+= catalan_decomp(v) * factorial(len(J) - len(JJ))
    return C

def testSignCardinality(sign):
    E = IntegerPosets(len(sign), pep = sign)
    return E.cardinality() == signedElementsCardinality(sign)

# tested all 2 .. 5
def test_all_SignCardinality(size):
    for s in all_signs(size):
        print s
        if not testSignCardinality(s):
            return False
    return True

# tested 6
def test_all_usefull_SignCardinality(size):
    for s in all_signs(size):
        if not 2 in s and 0 in s:
            print s
            if not testSignCardinality(s):
                return False
    return True

@cached_function
def signedElementsCardinality2(sign):
    n = len(sign)
    if len(sign) == 0 or len(sign) == 1:
        return 1
    if len(sign) == 2:
        return 2
    for i in xrange(1,n-1):
        if sign[i] == 2:
            return signedElementsCardinality2(sign[:i+1]) * signedElementsCardinality2(sign[i:])
    s = 0
    for i in xrange(n):
        if sign[i] == 0:
            s+= signedElementsCardinality2(sign[:i] + sign[i+1:])
        else:
            s+= signedElementsCardinality2(sign[:i])*signedElementsCardinality2(sign[i+1:])
    return s

def testSignCardinality2(sign):
    return signedElementsCardinality2(sign) == signedElementsCardinality(sign)

# tested all 2 .. 5
def test_all_SignCardinality2(size):
    for s in all_signs(size):
        print s
        if not testSignCardinality2(s):
            return False
    return True

# tested 6, 7
def test_all_usefull_SignCardinality2(size):
    for s in all_signs(size):
        if not 2 in s and 0 in s:
            print s
            if not testSignCardinality2(s):
                return False
    return True

def getFan(sign):
    C = [ip.cone() for ip in IntegerPosets(len(sign),pep=sign)]
    return Fan(C)

def getPolytope(F):
    n = F.dim() + 1
    bb = binomial(n+1,2)
    ieqs = [[-bb] + [1] *n, [bb] + [-1]* n]
    for v in F.rays():
        ieq = [0]
        k = 0
        for a in v:
            if a > 0:
                ieq.append(1)
                k+=1
            else:
                ieq.append(0)
        ieq[0] = -binomial(k+1,2)
        ieqs.append(ieq)
    return Polyhedron(ieqs=ieqs)

def getSignedPolytope(sign):
    F = getFan(sign)
    return getPolytope(F)

def getCoordinates(sign):
    pol = getSignedPolytope(sign)
    return [list(v) for v in pol.vertices()]

def getAllCoordinates(size):
    d = {}
    for sign in all_signs(size):
        d[sign] = getCoordinates(sign)
    return d

def keyMap(sign): # transform an orientation into a boolean vector
    bv = []
    d = {
         0: [0,0],
        -1: [1,0],
         1: [0,1],
         2: [1,1]
    }
    for i in xrange(1,len(sign)-1):
        bv.extend(d[sign[i]])
    return tuple(bv)


def getAllCoordinatesBooleanLatice(size):
    d =getAllCoordinates(size)
    return {keyMap(k):d[k] for k in d}

def rightLeftIsometry(sign):
    sign = list(sign)
    sign.reverse()
    return tuple(sign)

def upDownIsometry(sign):
    sign = list(sign)
    for i,v in enumerate(sign):
        if v == -1:
            sign[i] = 1
        elif v == 1:
            sign[i] = -1
    sign[0] = 1
    sign[-1] = 1
    return tuple(sign)


def testIsometryOrientation(sign,sign2):
    if sign == sign2:
        return True
    sign2 = upDownIsometry(sign2)
    if sign == sign2:
        return True
    sign2 = rightLeftIsometry(sign2)
    if sign == sign2:
        return True
    sign2 = upDownIsometry(sign2)
    if sign == sign2:
        return True
    return False

def cmpLexOrientation(sign1,sign2):
    if len(sign1) != len(sign2):
        raise ValueError
    d = {2:0,-1:1,1:2,0:3}
    for i in xrange(len(sign1)):
        if d[sign1[i]] < d[sign2[i]]:
            return -1
        elif d[sign1[i]] > d[sign2[i]]:
            return 1
    return 0

def getRepIsometryOrientation(sign):
    rep = sign
    sign = upDownIsometry(sign)
    if cmpLexOrientation(rep, sign) > 0:
        rep = sign
    sign = rightLeftIsometry(sign)
    if cmpLexOrientation(rep, sign) > 0:
        rep = sign
    sign = upDownIsometry(sign)
    if cmpLexOrientation(rep, sign) > 0:
        rep = sign
    return rep

def isometryClassesRep(size):
    return set(getRepIsometryOrientation(sign) for sign in all_signs(size))

def nbIsometricClasses(size):
    return len(isometryClassesRep(size))

def nbIsometricClasses2(size):
    if size < 0:
        return
    if size <= 2:
        return 1
    a = 1
    b1 = 0
    b2 = 0
    b3 = 0
    c = 0
    i = 2
    while i+2 <= size:
        c = 2*a + 6*(b1 +b2 + b3) + 16*c
        b1 = 4*b1 + a
        b2 = 4*b2 + a
        b3 = 4*b3 + a
        a = 2*a
        i+=2
    if i == size:
        return a+b1+b2+b3+c
    else:
        return 3*a + 3*b1 + 3*b3 + 4*b2 + 4*c


# not working
#def isometryClassesRepGenerator(size):
    #if size < 0:
        #return
    #if size <=2:
        #yield tuple(1 for i in xrange(size))
        #return
    #if size%2 == 1:
        #for s in isometryClassesRepGenerator(size-1):
            #k = (size - 1)/2
            #s1 = s[:k]
            #s2 = s[k:]
            #for v in (2,-1,1,0):
                #ns = s1 + (v,) + s2
                #rep = getRepIsometryOrientation(ns)
                #if ns == rep:
                    #yield ns
    #else:
        #for s in isometryClassesRepGenerator(size-2):
            #k = (size - 2)/2
            #s1 = s[:k]
            #s2 = s[k:]
            #for v1 in (2,-1,1,0):
                #for v2 in (2, -1, 1,0):
                    #ns = s1 + (v1,v2) + s2
                    #rep = getRepIsometryOrientation(ns)
                    #if ns == rep:
                        #yield ns

##### Test PFP ####


# tested 3,4,5,6
def testPfpWof(size):
    sign = tuple(0 for i in xrange(size))
    PFP = IntegerPosets(size, pfp = sign)
    WOF = IntegerPosets(size, wof = True)
    return set(WOF) == set(PFP)

# tested 3,4,5,6
def testPfpTof(size):
    sign = tuple(-1 for i in xrange(size))
    PFP = IntegerPosets(size, pfp = sign)
    TOF = IntegerPosets(size, tof = True)
    return set(PFP) == set(TOF)

# tested 3,4,5,6
def testPfpPlus(size):
    signplus = tuple(1 for i in xrange(size))
    signmoins = tuple(-1 for i in xrange(size))
    PFPP = IntegerPosets(size, pfp = signplus)
    PFPM = IntegerPosets(size, pfp = signmoins)
    return PFPP.cardinality() == PFPM.cardinality()

def testPfpPolytope(sign):
    size = len(sign)
    P = getSignedPolytope(sign)
    PFP = IntegerPosets(size, pfp = sign)
    return sum(P.f_vector()) -1 == PFP.cardinality()


# tested all 2 .. 6
def test_all_SignPfpPolytope(size):
    for s in all_signs(size):
        print s
        if not testPfpPolytope(s):
            return False
    return True

def testPFP2(sign):
    size = len(sign)
    PFP = IntegerPosets(size, pfp = sign)
    PFP2 = IntegerPosets(size, pfp2 = sign)
    return set(PFP) == set(PFP2)

# tested 3, 4, 5
def test_all_signs_PFP2(size):
    for s in all_signs(size):
        print s
        if not testPFP2(s):
            return False
    return True

def test_min_permutree_pfp(sign):
    for pfp in IntegerPosets(len(sign), pfp2 = sign):
        p = pfp.pfp_min_permutree(sign)
        if not p.is_pep(sign):
            print pfp, p
            return False
    return True

# tested 3,4,5, 6
def test_all_signs_pfp_permutree(size):
    for s in all_signs(size):
        print s
        if not test_min_permutree_pfp(s):
            return False
    return True

@cached_function
def PFPCardinality(sign):
    n = len(sign)
    if n <= 1:
        return 1
    if n == 2:
        return 3
    for i in xrange(1,n-1):
        if sign[i] == 2:
            return PFPCardinality(sign[:i+1]) * PFPCardinality(sign[i:])
    C = 0
    for II in subsets(range(n)):
        if len(II)!=0:
            indices = set(II)
            v = 1
            subset = []
            for i in xrange(n):
                if not i in indices:
                    subset.append(sign[i])
                else:
                    if sign[i] != 0:
                        v *= PFPCardinality(tuple(subset))
                        subset = []
            if len(subset)!=0:
                v*= PFPCardinality(tuple(subset))
            C+=v
    return C

def testPFPCardinality(sign):
    E = IntegerPosets(len(sign), pfp = sign)
    return E.cardinality() == PFPCardinality(sign)

# tested all 2 .. 5
def test_all_PFPCardinality(size):
    for s in all_signs(size):
        print s
        if not testPFPCardinality(s):
            return False
    return True

# tested 6
def test_all_usefull_PFPCardinality(size):
    for s in all_signs(size):
        if not 2 in s and 0 in s:
            print s
            if not testPFPCardinality(s):
                return False
    return True


## Permutree insertion

def permutreeInsertion(perm, sign):
    n = len(sign)
    walls = set(i+1 for i in xrange(n) if sign[i] == -1 or sign[i] == 2)
    relations = []
    outgoings = set()
    outgoingsplus = set()
    outgoingsminus = set()
    for v in perm:
        s = sign[v-1]
        i = v - 1
        rels = 0
        while i > 0 and  not i in walls:
            if i in outgoings:
                relations.append((i,v))
                outgoings.remove(i)
                rels+=1
            i-=1
        if i in outgoingsplus:
            relations.append((i,v))
            outgoingsplus.remove(i)
            rels+=1
        i = v + 1
        while i < n+1 and not i in walls :
            if i in outgoings:
                relations.append((i,v))
                outgoings.remove(i)
                rels+=1
            i+=1
        if i in outgoingsminus:
            relations.append((i,v))
            outgoingsminus.remove(i)
            rels+=1
        assert ((s == 0 or s == 1) and rels <= 1) or ((s== -1 or s == 2) and rels <= 2)
        if s == 1:
            walls.add(v)
            outgoingsminus.add(v)
            outgoingsplus.add(v)
        if s == -1:
            walls.remove(v)
            outgoings.add(v)
        if s == 2:
            outgoingsminus.add(v)
            outgoingsplus.add(v)
        if s == 0:
            outgoings.add(v)
    return IntegerPoset(n,relations)

def PepsFromPerms(sign):
    n = len(sign)
    COE = set()
    for p in Permutations(n):
        COE.add(permutreeInsertion(p, sign))
    return COE

def testPepsFromPerms(sign):
    n = len(sign)
    COE1 = set(IntegerPosets(n, pep = sign))
    COE2 = PepsFromPerms(sign)
    return COE1 == COE2

# tested 3...6
def test_all_sign_PepsFromPerms(size):
    for s in all_signs(size):
        print s
        if not testPepsFromPerms(s):
            return False
    return True

# Permutrees

def cleanCut(G, v):
    a,b = v
    Gcut = Graph()
    Gcut.add_vertices(G.vertices())
    Gcut.add_edges(e for e in G.edges() if e[0] != a or e[1] != b)
    C = Gcut.connected_components()
    Cmin = C[0]
    if not a in Cmin:
        Cmin = C[1]
    return range(1,len(Cmin)+1) == Cmin

def indecPermutrees(sign):
    I = IntegerPosets(len(sign), pep = sign)
    for ip in I:
        pos = ip.poset()
        G = Graph(pos.hasse_diagram())
        for v in pos.cover_relations():
            if v[0] < v[1]:
                if cleanCut(G, v):
                    break
        else:
            yield ip

def allIndecSign(size):
    c = 0
    for sign in all_signs(size):
        c+= len(list(indecPermutrees(sign)))
    return c*4

def allIndecSign01(size):
    c = 0
    for sign in all_signs(size):
        if not -1 in sign and not 2 in sign:
            c+= len(list(indecPermutrees(sign)))
    return c

def allPermutrees(size):
    c = 0
    for sign in all_signs(size):
        c+= IntegerPosets(size, pep = sign).cardinality()
    return c

def allPermutrees01(size):
    c = 0
    for sign in all_signs(size):
        if not -1 in sign and not 2 in sign:
            c+= IntegerPosets(size, pep = sign).cardinality()
    return c

def minIndec(sign):
    mins = set()
    for ip in indecPermutrees(sign):
        for m in mins:
            if m.lequal(ip):
                break
            if ip.lequal(m):
                mins = set(m2 for m2 in mins if not ip.lequal(m2))
                mins.add(ip)
                break
        else:
            mins.add(ip)
    return mins

def inverseSign(sign):
    inv = []
    for v in sign:
        if v == 1 or v == -1:
            v*=-1
        inv.append(v)
    return tuple(inv)

def baxterSign(sign):
    inv = inverseSign(sign)
    n = len(sign)
    for ip1 in IntegerPosets(n,pep=sign):
        for ip2 in IntegerPosets(n, pep=inv):
            for p in ip1.linear_extensions():
                if ip2.is_linear_extension(p):
                    yield ip1,ip2
                    break

### TEST pipIZE

# tested 0 1 0 -1 2 1
def test_woip_pipize(sign):
    n = len(sign)
    for ip in IntegerPosets(n, woip = True):
        pip = ip.pipize(sign)
        if not pip.is_pip(sign):
            print ip, pip
            return False
    return True

# tested 3,4,5
def test_all_sign_woip_pipize(size):
    for s in all_signs(size):
        print s
        if not test_woip_pipize(s):
            return False
    return True

# tested 0 1 0 -1 2 1
def test_woe_pipize(sign):
    n = len(sign)
    for ip in IntegerPosets(n, total = True):
        pip = ip.pipize(sign)
        if not pip.is_pep(sign):
            print ip, pip
            return False
    return True

# tested 3,4,5
def test_all_sign_woe_pipize(size):
    for s in all_signs(size):
        print s
        if not test_woe_pipize(s):
            return False
    return True

# tested 0 1 0 -1 2 1
def test_wof_pipize(sign):
    n = len(sign)
    for ip in IntegerPosets(n, wof = True):
        pip = ip.pipize(sign)
        if not pip.is_pfp(sign):
            print ip, pip
            return False
    return True

# tested 3,4,5
def test_all_sign_wof_pipize(size):
    for s in all_signs(size):
        print s
        if not test_wof_pipize(s):
            return False
    return True

# tested 3,4,5
def test_all_detoipize_extension(size):
    d = {}
    for ip in IntegerPosets(size, woip = True):
        tip = ip.toipize()
        s = d.get(tip, set())
        s.add(ip)
        d[tip] = s
    for tip in IntegerPosets(size, toip = True):
        s2 = set(tip.detoipize_extensions())
        if not d[tip] == s2:
            print tip
            return False
    return True

# tested 3,4,5
def test_all_detoipize_poset_extension(size):
    d = {}
    for ip in IntegerPosets(size):
        tip = ip.toipize()
        s = d.get(tip, set())
        s.add(ip)
        d[tip] = s
    for tip in IntegerPosets(size, toip = True):
        s2 = set(tip.detoipize_poset_extensions())
        if not d[tip] == s2:
            print tip
            return False
    return True

def min_max_interval(s):
    for ip in s:
        pmin = ip
        pmax = ip
        break
    for ip in s:
        if ip.lequal(pmin):
            pmin = ip
        if pmax.lequal(ip):
            pmax = ip
    return pmin, pmax

def test_detoipize_woip_interval(tip):
    s = list(tip.detoipize_extensions())
    pmin, pmax = min_max_interval(s)
    I = set(interval_woip(pmin, pmax))
    return I == set(s)

# tested 3,4,5
def test_all_detoipize_woip_interval(size):
    for ip in IntegerPosets(size, toip = True):
        if not test_detoipize_woip_interval(ip):
            print ip
            return False
    return True

# tested 3,4,5
def test_all_detoipize_poset_interval(size):
    d = {}
    for ip in IntegerPosets(size):
        tip = ip.toipize()
        s = d.get(tip, set())
        s.add(ip)
        d[tip] = s
    for tip in d:
        pmin, pmax = min_max_interval(d[tip])
        I = set(interval(pmin, pmax))
        if I != d[tip]:
            print tip
            return False
    return True

# tested 3,4,5
def test_all_dewoipize_poset_interval(size):
    d = {}
    for ip in IntegerPosets(size):
        wip = ip.woipize()
        s = d.get(wip, set())
        s.add(ip)
        d[wip] = s
    for wip in d:
        pmin, pmax = min_max_interval(d[wip])
        I = set(interval(pmin, pmax))
        if I != d[wip]:
            print wip
            return False
    return True
