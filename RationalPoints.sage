###############################################################################
# licensed under GPL v2 or any later version
###############################################################################
from sage.schemes.generic.algebraic_scheme import AlgebraicScheme_subscheme
from sage.rings.number_field.bdd_height import bdd_height, bdd_height_iq
from sage.rings.rational_field import is_RationalField
from time import time
###############################################################################
# hacked-up `global_height`
#
def global_height(x):
    k = x[0].parent()
    finite = lcm([xi.norm().denominator() for xi in x]) / gcd([xi.norm().numerator() for xi in x])
    if is_RationalField(k):
        infinite = max(abs(xi) for xi in x)
        return finite*infinite
    else:
        d = k.degree()
        infinite = product(max(abs(xi.complex_embedding(53,i)) for xi in x) for i in range(d))
        return (finite*infinite)^(RR(1)/d)
###############################################################################
class MyAlgebraicScheme_subscheme(AlgebraicScheme_subscheme):
    def rational_points(self, F=None, bound=None, split=False):
        def base_change(k, F):
            ch = F.characteristic()
            if ch == 0:
                return k.embeddings(F)[0]
            else:
                return F
        def enum_proj_points(I):
            for i in range(n+1):
                R_ = PolynomialRing(k, 'x', n-i)
                v = [k(0)]*i+[k(1)]
                pr = R.hom(v+list(R_.gens()), R_)
                for rest in enum_points(pr(I)):
                    pt = v+rest
                    if bound == None or global_height(pt) <= bound:
                        yield pt
            return
        def enum_points(I):
            possibleValues = get_elements()
            R = I.ring()
            F = R.base()
            ch = F.characteristic()
            n = R.ngens()
            if n == 0:
                if I.is_zero():
                    yield []
                return
            if I.is_one():
                return
            # if I.degree() == 1 and (I.dim() == 1 or I.is_prime()):
            #     print('do something')
            # TODO this case can be solved using linear algebra
            if ch > 0 and  I.is_homogeneous():
                yield [0]*n
                for pt in enum_proj_points(I):
                    for sca in get_elements():
                        if sca != 0:
                            yield [x * sca for x in pt]
                return
            elim = I.elimination_ideal(I.ring().gens()[1:])
            g = elim.gens()[0]
            if g != 0:
                S.<u> = F[]
                pr1 = R.hom([u]+[0]*(n-1),S)
                possibleValues = (v[0] for v in pr1(g).roots())
                nonSplit = (f[0] for f in factor(pr1(g)) if f[0].degree() > 1)
                if split:
                    for f in nonSplit:
                        F_ = f.splitting_field('a')
                        if ch == 0:
                            # `polredbest` from PARI/GP, improves performance significantly
                            minp = str(gp.polredbest(F_.0.minpoly('a')))
                            F_ = NumberField(PolynomialRing(QQ,'a')(minp),'a')
                        R_ = PolynomialRing(F_, 'x', n)
                        I = R_.ideal([f.change_ring(base_change(F, F_)) for f in I.gens()])
                        for pt in enum_points(I):
                            yield pt
                        return
            R_ = PolynomialRing(F, 'x', n-1)
            for v in possibleValues:
                pr2 = R.hom([v]+list(R_.gens()), R_)
                for rest in enum_points(pr2(I)):
                    yield [v]+rest
            return
        #######################################################################
        # begin of main function
        I = self.defining_ideal()
        R = I.ring()
        k = R.base()
        n = R.ngens()-1
        P = self.ambient_space()
        if F: # specified coefficient field
            R_ = PolynomialRing(F, 'x', n+1)
            I = R_.ideal([f.change_ring(base_change(k, F)) for f in I.gens()])
            R = R_
            k = F
            P = P.change_ring(k)
            split = False
        # by default we want to use elimination only and no brute force
        get_elements = lambda : []
        ch = k.characteristic()
        if I.dimension() > 1: # positive dimension
            split = False
            if ch == 0:
                if bound == None:
                    raise ValueError("need to specify a valid bound")
                if is_RationalField(k):
                    get_elements = lambda : k.range_by_height(floor(bound)+1)
                else:
                    p = k.0.minpoly()
                    if p.degree() == 2 and p.disc() < 0:
                        get_elements = lambda : bdd_height_iq(k, bound^(k.degree()))
                    else:
                        get_elements = lambda : bdd_height(k, bound^(k.degree()))
            else:
                bound = None
                get_elements = lambda : k
        for pt in enum_proj_points(I):
            if split:
                # TODO construct homogeneous coordinates from a bunch of
                # elements from different fields
                yield pt
            else:
                yield P(pt)
        return

###############################################################################
# examples

def togliatti_quintic(split=True):
    q = QQ['q'].0
    F.<q> = NumberField(q^4-10*q^2+20)
    P.<x,y,z,w> = ProjectiveSpace(F,3)
    f = 64*(x-w)*(x^4-4*x^3*w-10*x^2*y^2-4*x^2*w^2+16*x*w^3-20*x*y^2*w+5*y^4+16*w^4-20*y^2*w^2)-5*q*(2*z-q*w)*(4*(x^2+y^2-z^2)+(1+3*(5-q^2))*w^2)^2
    X = MyAlgebraicScheme_subscheme(P, [f]+f.jacobian_ideal())
    return X.rational_points(split=split)

def labs_septic(split=True):
    c = QQ['c'].0
    F.<c> = NumberField(49*c^2+1)
    P.<x,y,z,w> = ProjectiveSpace(F,3)
    f = x*(x^6-21*x^4*y^2+35*x^2*y^4-7*y^6)+7*z*((x^2+y^2)^3-8*z^2*(x^2+y^2)^2+16*z^4*(x^2+y^2))-64*z^7-((z+c*w)*(56*c*z^3+(4/7)*z^2*w+(4/7)*c*z*w^2+(8/343)*w^3+(0*z+w)*(x^2+y^2))^2)
    X = MyAlgebraicScheme_subscheme(P, [f]+f.jacobian_ideal())
    return X.rational_points(split=split)

def magma_doc():
    F = GF(7823)
    P.<x,y,z,w> = ProjectiveSpace(F,3)
    X = MyAlgebraicScheme_subscheme(P, [4*x*z + 2*x*w + y^2 + 4*y*w + 7821*z^2 + 7820*w^2,
    4*x^2 + 4*x*y + 7821*x*w + 7822*y^2 + 7821*y*w + 7821*z^2 + 7819*z*w + 7820*w^2])
    return X.rational_points()

def P2_over_number_field(bound=RR(5^(1/3)+1e-10)):
    u = QQ['u'].0
    F.<u> = NumberField(u^3-5)
    P.<x,y,z> = ProjectiveSpace(F, 2)
    X = MyAlgebraicScheme_subscheme(P, [])
    return X.rational_points(bound=bound)


# 31 nodes on a Togliatti quintic over char. 0
# less than 1s
t = time()
print(len(list(togliatti_quintic(split=True))))
print(time()-t)

# # 99 nodes on a septic surface
# # only one is defined over QQ
# # needs ~8s
# t = time()
# print(len(list(labs_septic(split=True))))
# print(time()-t)

# # example from magma documentation
# # needs around 20s; unfeasible with the old methods
# t = time()
# print(len(list(magma_doc())))
# print(time()-t)

# P2 over the field QQ[u]/(u^3-5), with bound 5^(1/3)
# 49 is the correct answer
t = time()
print(len(list(P2_over_number_field())))
print(time()-t)
