"""Exact finite differences shared by construction and forward recognition."""
from fractions import Fraction
from math import comb, factorial

from expr import add, evaluate, expand_polynomial, index, mul, nat, nat_const, num, polynomial, shift, sub


def newton_coefficients(expr):
    degree = max(polynomial(expr), default=0)
    row = [evaluate(expr,n) for n in range(degree+1)]
    result = []
    while row:
        result.append(row[0])
        row = [b-a for a,b in zip(row,row[1:])]
    return result


def prefix_polynomial(expr, initial):
    terms = [num(initial)]
    for k,c in enumerate(newton_coefficients(expr),1):
        if c:
            falling = mul(*(sub(index(),num(j+1)) for j in range(k)))
            terms.append(mul(num(c/Fraction(factorial(k))),falling))
    result = expand_polynomial(add(*terms))
    assert polynomial(sub(shift(result),result)) == polynomial(expr)
    return result


def natural_polynomial(expr):
    """Nonnegative integral Newton coefficients give natural exponents."""
    coefficients=newton_coefficients(expr)
    assert all(c.denominator==1 and c>=0 for c in coefficients), 'Unregistered natural exponent'
    offset=0
    if len(coefficients)>1 and coefficients[1]:
        offset=int(coefficients[0]//coefficients[1])
        coefficients[0]-=offset*coefficients[1]
    terms=[]
    for k,c in enumerate(coefficients):
        if not c: continue
        if k==0:
            terms.append(nat_const(c.numerator))
            continue
        basis = nat(offset) if k==1 else {'op':'choose','args':[nat(),nat_const(k)]}
        terms.append(basis if c==1 else mul(nat_const(c.numerator),basis))
    return add(*terms) if terms else nat_const(0)


def geometric_antidifference(forcing, ratio):
    """Find H with ratio*H(n+1)-H(n)=forcing(n), degree at most two."""
    assert ratio!=1
    p=polynomial(forcing)
    degree=max(p,default=0)
    assert degree<=2
    coefficients={}
    for k in range(degree,-1,-1):
        higher=sum(ratio*c*comb(j,k) for j,c in coefficients.items() if j>k)
        coefficients[k]=(p.get(k,Fraction(0))-higher)/(ratio-1)
    from expr import from_polynomial
    result=from_polynomial(coefficients)
    assert polynomial(sub(mul(num(ratio),shift(result)),result))==p
    return result


def integer_log(value, base):
    value,base=Fraction(value),Fraction(base)
    assert base.denominator==1 and base>1 and value>0
    sign=1
    if value<1:
        value=1/value
        sign=-1
    assert value.denominator==1, 'Not an integral power of the registered base'
    lo,hi=0,value.numerator.bit_length()
    while lo<hi:
        mid=(lo+hi)//2
        if base.numerator**mid<value.numerator: lo=mid+1
        else: hi=mid
    assert base.numerator**lo==value.numerator, 'Not a power of the registered base'
    return sign*lo
