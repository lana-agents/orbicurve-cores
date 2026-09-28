from sympy import *
x=symbols('x')
def jinv(a2,a4,a6):
    # y^2 = x^3+a2 x^2+a4 x+a6
    b2=4*a2; b4=2*a4; b6=4*a6; b8=4*a2*a6-a4**2
    c4=b2**2-24*b4
    D=-b2**2*b8-8*b4**3-27*b6**2+9*b2*b4*b6
    return nsimplify(c4**3/D) if D!=0 else None
def analyze(name,f,G):
    N,D=fraction(together(G))
    N=Poly(N,x); D=Poly(D,x)
    print("==",name,"f=",factor(f),"j=",jinv(*[Poly(f,x).coeff_monomial(x**k) for k in (2,1,0)]))
    print(" N=",factor(N.as_expr())," D=",factor(D.as_expr()))
    print(" N-1728D=",factor((N-1728*D).as_expr()))
    crit=factor((N.diff(x)*D-N*D.diff(x)).as_expr())
    print(" crit=",crit)
    print(" degN,degD",N.degree(),D.degree())
# Case I: C: y^2=x(x^2+44x-16); G = phi(x'), x'=(x^2+44x-16)/(4x), phi=-(t^2-10t+5)^3/t
f1=x*(x**2+44*x-16)
t=(x**2+44*x-16)/(4*x)
analyze("I",f1,-(t**2-10*t+5)**3/t)
# Case III: E': y^2 = x(4x^2+1) -> monic: X=4x? Let's use phi=256(t^2+1)^3/t^4 with t = x-coordinate on E': y^2=x(4x^2+1)
# write E' as y^2 = x(x^2+a x+b) via x=t: 4t^3+t = t(4t^2+1); scale: Y=2y? (2y)^2... use u=4t? Let E'': v^2=u(u^2+4) with u=4t? check: u(u^2+4)=4t(16t^2+4)=16 t(4t^2+1) = 16 y^2, v=4y ok.
# so E'': y^2=x(x^2+4) (a=0,b=4), t=x/4, phi=256((x/4)^2+1)^3/(x/4)^4
# C = E''/<(0,0)>: y^2 = x(x^2 - 16)  (a'=-2a=0, b'=a^2-4b=-16)
# dual iota': C -> E''' = y^2=x(x^2+64)  ~ E'' scaled by 4: x''' = 4 x''
f3=x*(x**2-16)
xp=(x**2-16)/x   # x''' = y^2/x^2 on C
t=(xp/4)/4
analyze("III",f3,256*(t**2+1)**3/t**4)
# Case IV: C: y^2 = x^3-1728, G = x([2]P)^3
f4=x**3-1728
x2=(x**4+8*1728*x)/(4*(x**3-1728))
analyze("IV",f4,x2**3)
H=x**4-384*x**2-3072*x
K=x**6-576*x**4-4608*x**3+55296*x**2+884736*x+3538944
D=(x+8)**3*(x+12)**2*(x-24)
q=cancel((H**3-K**2)/D); print("II mu:",q)
c=1728/q
f2=(x-24)*(x+8)*(x+12)
analyze("II",f2,c*H**3/D)
