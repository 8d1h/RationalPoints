###############################################################################
# licensed under GPL v2 or any later version
###############################################################################
r"""
Enumeration of rational points using elimination.
"""
from sage.all import factor, floor, gcd, lcm, matrix, pari, product, QQ, RR, vector
from sage.all import NumberField, PolynomialRing
from sage.rings.rational_field import is_RationalField
from sage.libs.pari.convert_sage import gen_to_sage
###############################################################################
def global_height(x, prec=53):
    r"""
    Return the (correct) global height of a homogeneous coordinate.

    EXAMPLES::
    
        sage: from rational_points import global_height
        sage: global_height([1/1,2/3,5/8])
        24
        sage: F.<u> = NumberField(x^3-5)
        sage: P = ProjectiveSpace(F, 2)
        sage: global_height(P(u,u^2/5,1))
        2.92401773821287
    """
    k = x[0].parent()
    # first get rid of the denominators
    denom = lcm([xi.denominator() for xi in x])
    x = [xi * denom for xi in x]
    if is_RationalField(k):
        return max(abs(xi) for xi in x) / gcd(x)
    else:
        finite = 1 / sum(k.ideal(xi) for xi in x).norm()
        d = k.degree()
        infinite = product(max(abs(xi.complex_embedding(prec,i)) for xi in x) for i in range(d))
        return (finite*infinite)**(RR(1)/d)
###############################################################################
def rational_points(X, F=None, split=False, bound=None, tolerance=0.01, prec=53):
    r"""
    Return an iterator of rational points on a scheme ``X``

    INPUT:

    - ``X`` - a scheme, affine or projective

    OPTIONS:
    
    - ``F`` - coefficient field
    
    - ``split`` - whether to compute the splitting field when the scheme is 0-dimensional

    - ``bound`` - a bound for multiplicative height

    - ``tolerance`` - tolerance used for computing height
    
    - ``prec`` - precision used for computing height

    OUTPUT:

    - an iterator of rational points on ``X``
    
    ALGORITHM:

    Use brute force plus some elimination. The complexity is approximately
    `O(n^d)`, where `n` is the size of the field (or the number of elements
    with bounded height when the field is infinite) and `d` is the dimension of
    the scheme ``X``. Significantly faster than the current available
    algorithms in Sage, especially for low dimension schemes in large
    ambient spaces.

    EXAMPLES::
    
        sage: from rational_points import rational_points

    A curve of genus 9 over `\mathbf F_{97}` with many rational points (from
    the website `<https://manypoints.org>`_)::
    
        sage: A.<x,y,z> = AffineSpace(GF(97),3)
        sage: C = A.subscheme([x^4+y^4+1+3*x^2*y^2+13*y^2+68*x^2,z^2+84*y^2+x^2+67])
        sage: len(list(rational_points(C)))
        228
    
    The following example is from the `documentation
    <http://magma.maths.usyd.edu.au/magma/handbook/text/1354>`_ of Magma: a
    space rational curve with one cusp. Unfeasible with the old methods::
    
        sage: F = GF(7823)
        sage: P.<x,y,z,w> = ProjectiveSpace(F,3)
        sage: C = P.subscheme([4*x*z+2*x*w+y^2+4*y*w+7821*z^2+7820*w^2,\
        ....: 4*x^2+4*x*y+7821*x*w+7822*y^2+7821*y*w+7821*z^2+7819*z*w+7820*w^2])
        sage: len(list(rational_points(C))) # long time
        7824
        
    31 nodes on a `Togliatti surface
    <https://en.wikipedia.org/wiki/Togliatti_surface>`_: only 7 of them are
    defined over the field of definition. Use ``split=True`` to automatically
    find the splitting field::
    
        sage: q = QQ['q'].0
        sage: F.<q> = NumberField(q^4-10*q^2+20)
        sage: P.<x,y,z,w> = ProjectiveSpace(F,3)
        sage: f = 5*q*(2*z-q*w)*(4*(x^2+y^2-z^2)+(1+3*(5-q^2))*w^2)^2-64*(x-w)*\
        ....: (x^4-4*x^3*w-10*x^2*y^2-4*x^2*w^2+16*x*w^3-20*x*y^2*w+5*y^4+16*w^4-20*y^2*w^2)
        sage: X = P.subscheme([f]+f.jacobian_ideal())
        sage: len(list(rational_points(X)))
        7
        sage: len(list(rational_points(X,split=True)))
        31

    Enumeration of points on a projective plane over a number field::
        
        sage: a = QQ['a'].0
        sage: F.<a> = NumberField(a^3-5)
        sage: P.<x,y,z> = ProjectiveSpace(F, 2)
        sage: len(list(rational_points(P, bound=RR(5^(1/3)))))
        49
    """
    def base_change(k, F):
        ch = F.characteristic()
        if ch == 0:
            return k.embeddings(F)[0]
        else:
            return F
    def enum_proj_points(I):
        R = I.ring()
        k = R.base()
        n = R.ngens()-1
        for i in range(n+1):
            R_ = PolynomialRing(k, 'x', n-i)
            v = [k(0)]*i+[k(1)]
            pr = R.hom(v+list(R_.gens()), R_)
            for rest in enum_points(pr(I)):
                pt = v+rest
                if bound == None or global_height(pt, prec=prec) <= bound+tolerance:
                    yield pt
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
        if all(map(lambda _:_.degree()==1, I.gens())) and (ch > 0 or I.dimension() == 0):
            # solve using linear algebra
            f = R.hom(n*[0],F)
            A = matrix([f(g.coefficient(xi)) for xi in R.gens()] for g in I.gens())
            b = vector(-g.constant_coefficient() for g in I.gens())
            v0 = A.solve_right(b)
            r = A.rank()
            if r == n:
                yield list(v0)
            else:
                K = A.right_kernel().matrix()
                for v in F**(n-r):
                    yield list(v*K+v0)
            return
        if ch > 0 and I.is_homogeneous():
            yield [F(0)]*n
            for pt in enum_proj_points(I):
                for sca in get_elements():
                    if sca != 0:
                        yield [x * sca for x in pt]
            return
        elim = I.elimination_ideal(I.ring().gens()[1:])
        g = elim.gens()[0]
        if g != 0:
            S = F['u']
            pr1 = R.hom([S.gen()]+[0]*(n-1),S)
            possibleValues = (v[0] for v in pr1(g).roots() if bound == None or global_height([v[0],F(1)]) <= bound+tolerance)
            if split:
                nonSplit = (f[0] for f in factor(pr1(g)) if f[0].degree() > 1)
                for f in nonSplit:
                    if ch == 0:
                        F_ = f.splitting_field('a')
                        # `polredbest` from PARI/GP, improves performance significantly
                        f = gen_to_sage(pari(F_.gen().minpoly('x')).polredbest(), {'x':S.gen()})
                    F_ = f.splitting_field('a')
                    R_ = PolynomialRing(F_, 'x', n)
                    I = R_.ideal([f.change_ring(base_change(F,F_)) for f in I.gens()])
                    for pt in enum_points(I):
                        yield pt
                    return
        R_ = PolynomialRing(F, 'x', n-1)
        if n == 1:
            for v in possibleValues:
                yield [v]
        else:
            for v in possibleValues:
                pr2 = R.hom([v]+list(R_.gens()), R_)
                for rest in enum_points(pr2(I)):
                    yield [v]+rest
    #######################################################################
    # begin of main function
    try:
        I = X.defining_ideal()
        R = I.ring()
    except: # when X has no defining ideal, i.e. when it's the whole space
        R = X.coordinate_ring()
        I = R.ideal([])
    k = R.base()
    n = R.ngens()
    ambient = X.ambient_space()
    if F: # specified coefficient field
        R_ = PolynomialRing(F, 'x', n)
        I = R_.ideal([f.change_ring(base_change(k, F)) for f in I.gens()])
        k = F
        ambient = ambient.change_ring(k)
        split = False
    ch = k.characteristic()
    if (X.is_projective() and I.dimension() == 1) or (not X.is_projective() and I.dimension() == 0): # 0-dimensional dimension
        # in 0-dim use elimination only
        bound = None
        get_elements = lambda : []
    else: # positive dimension
        split = False # splitting field does not work in positive dimension
        if ch == 0:
            if bound == None:
                raise ValueError("need to specify a valid bound")
            if is_RationalField(k):
                get_elements = lambda : k.range_by_height(floor(bound)+1)
            else:
                get_elements = lambda : k.elements_of_bounded_height(bound=bound**(k.degree()), tolerance=tolerance, precision=prec)
        else: # finite field
            bound = None
            get_elements = lambda : k
    if X.is_projective(): # projective case
        for pt in enum_proj_points(I):
            if split:
                # TODO construct homogeneous coordinates from a bunch of
                # elements from different fields
                yield pt
            else:
                yield ambient(pt)
    else: # affine case
        for pt in enum_points(I):
            if split:
                yield pt
            else:
                yield ambient(pt)
