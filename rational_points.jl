# using Nemo
using Singular
# using GroebnerBasis

# get a vector consisting of distinct zeros of a polynomial
function get_zeros(f::spoly)
    R = parent(f)
    F = base_ring(R)
    if total_degree(f) == 1
        cs = [c for c in coeffs(f)]
        if length(cs) == 1
            return [F(0)]
        else
            return [F(-cs[2]//cs[1])]
        end
    else
        # if typeof(F) <: Union{Rationals, Integers, N_ZpField, N_FField}
        lin_fac = [fi[1] for fi in factor(f) if total_degree(fi[1]) == 1]
        return [z for fi in lin_fac for z in get_zeros(fi)]
    end
end

# evaluate function for an ideal
function evaluate(I::sideal, v)
    R = base_ring(I)
    Ideal(R, [R(Singular.evaluate(f,v)) for f in gens(I)]...)
end

# enumeration of points; starts with a partial solution `part`
# unsafe: points are pushed into `ans`
# would be nice to have multithread
function enum!(I::sideal, part, els, ans)
    R = base_ring(I)
    char = characteristic(R)
    F = base_ring(R)
    n = nvars(R)
    i = length(part)
    if i == n
        if iszero(I) push!(ans, part) end
        return
    end
    rest = gens(R)[i+2:end]
    elim = eliminate(I, rest...)[1]
    if elim == 0
        values = els
    else
        values = get_zeros(elim)
    end
    for v in values
        vec = [R(u) for u in vcat(part, [v], rest)]
        enum!(evaluate(I, vec), vcat(part, [v]), els, ans)
    end
end

# list the elements of a finite field
function get_elements(F)
    char = Int(characteristic(F))
    if typeof(F) == N_ZpField
        return [F(i) for i in 0:char-1]
    elseif typeof(F) == N_GField
        a = gen(F)
        d = degree(F)
        return vcat([F(0)], [a^i for i in 0:char^d-2])
    end
end

# enumeration of points for an affine scheme
function points(I::sideal)
    els = get_elements(base_ring(base_ring(I)))
    ans = []
    enum!(I, [], els, ans)
    ans
end

# enumeration of points for a projective scheme
function proj_points(I::sideal)
    R = base_ring(I)
    F = base_ring(R)
    n = nvars(R)
    els = get_elements(F)
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
    R,(x,y,z,w) = PolynomialRing(Fp(char),["x","y","z","w"])
    I = Ideal(R,4*x*z+2*x*w+y^2+4*y*w+7821*z^2+7820*w^2,4*x^2+4*x*y+7821*x*w+7822*y^2+7821*y*w+7821*z^2+7819*z*w+7820*w^2)
    @time length(proj_points(I))
end
# this doesn't work right now
function exampleGF()
    R,(x,y) = PolynomialRing(FiniteField(19,3,"a")[1],["x","y"])
    I = Ideal(R,y^27-x^8*(1-x))
    @time length(points(I))
end
