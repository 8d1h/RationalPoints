using Oscar

# evaluate function for an ideal
function evaluate(I::Oscar.MPolyIdeal, v)
    R = base_ring(I)
    return ideal([R(Oscar.evaluate(f,v)) for f in gens(I)])
end

# convert to univariate
function to_univar(a, var::Int, Kx)
    r = zero(Kx)
    for (c, ev) in zip(coefficients(a), exponent_vectors(a))
        setcoeff!(r, ev[var], c)
    end
    return r
end

# enumeration of points; starts with a partial solution `part`
# unsafe: points are pushed into `ans`
# would be nice to have multithread
function enum!(I, part, els, ans)
    R = base_ring(I)
    char = characteristic(R)
    F = base_ring(R)
    n = nvars(R)
    i = length(part)
    if i == n
        if I == ideal([R(0)]) push!(ans, part) end
        return
    end
    rest = gens(R)[i+2:end]
    if i < n-1
        elim = gens(eliminate(I, rest))[1]
    else
        # eliminate an empty list doesn't work right now
        I = ideal(groebner_basis(I))
        elim = gens(I)[1]
    end
    if elim == 0
        values = els
    else
        values = roots(to_univar(elim, i+1, F["x"][1]))
    end
    for v in values
        vec = [R(u) for u in vcat(part, [v], rest)]
        enum!(evaluate(I, vec), vcat(part, [v]), els, ans)
    end
end

# enumeration of points for an affine scheme
function points(I::Oscar.MPolyIdeal)
    els = collect(base_ring(base_ring(I)))
    ans = []
    enum!(I, [], els, ans)
    ans
end

# enumeration of points for a projective scheme
function proj_points(I::Oscar.MPolyIdeal)
    R = base_ring(I)
    F = base_ring(R)
    n = nvars(R)
    els = collect(F)
    ans = []
    for i in 1:n
        rest = gens(R)[i+1:end]
        part = vcat(repeat([F(0)], i-1), [F(1)])
        vec = [R(u) for u in vcat(part, rest)]
        enum!(evaluate(I, vec), part, els, ans)
    end
    ans
end

# example taken from the documentation of Magma
function example(char=7823)
    R,(x,y,z,w) = PolynomialRing(GF(char),["x","y","z","w"])
    I = ideal([4*x*z+2*x*w+y^2+4*y*w+7821*z^2+7820*w^2,4*x^2+4*x*y+7821*x*w+7822*y^2+7821*y*w+7821*z^2+7819*z*w+7820*w^2])
    @time length(proj_points(I))
end
# over an extension field
function exampleGF()
    R,(x,y) = PolynomialRing(FiniteField(19,3,"a")[1],["x","y"])
    I = ideal([y^27-x^8*(1-x)])
    @time length(points(I))
end
