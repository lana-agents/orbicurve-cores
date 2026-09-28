# coset enumeration for H = Gamma_i ∩ SL2(Z) in SL2(Z) via membership oracle (word reduction in Gamma_i)
import math, itertools, sys
from fractions import Fraction

def mul(a,b):
    return ((a[0][0]*b[0][0]+a[0][1]*b[1][0], a[0][0]*b[0][1]+a[0][1]*b[1][1]),
            (a[1][0]*b[0][0]+a[1][1]*b[1][0], a[1][0]*b[0][1]+a[1][1]*b[1][1]))
def inv(a):  # det-1 assumed (for scaled: we'll handle separately)
    return ((a[1][1], -a[0][1]), (-a[1][0], a[0][0]))
I=((1,0),(0,1))
S=((0,-1),(1,0)); T=((1,1),(0,1))

# represent elements of Gamma_i numerically as float matrices for reduction

class F:
    def __init__(self,m): self.m=m
    def __matmul__(self,o):
        a=self.m;b=o.m
        return F(((a[0][0]*b[0][0]+a[0][1]*b[1][0], a[0][0]*b[0][1]+a[0][1]*b[1][1]),
            (a[1][0]*b[0][0]+a[1][1]*b[1][0], a[1][0]*b[0][1]+a[1][1]*b[1][1])))
    def copy(self): return self
def fmat(m,s=1.0): return F(tuple(tuple(x*s for x in row) for row in m))
def finv(f):
    a=f.m; return F(((a[1][1],-a[0][1]),(-a[1][0],a[0][0])))
def close(f,sign):
    return all(abs(f.m[i][j]-sign*(1 if i==j else 0))<1e-7 for i in range(2) for j in range(2))


cases = {
 'I':   (((4,1),(-1,1)),5, ((3,2),(8,7)),5),
 'II':  (((5,1),(-1,1)),6, ((2,1),(5,4)),3),
 'III': (((3,1),(1,1)),2, ((1,1),(1,3)),2),
 'IV':  (((2,1),(1,1)),1, ((0,-1),(1,3)),1),
}
def gens(case):
    M,n,N,k = cases[case]
    A=fmat(M,1/math.sqrt(n)); B=fmat(N,1/math.sqrt(k))
    Ai=finv(A); Bi=finv(B)
    return {'a':A,'A':Ai,'b':B,'B':Bi}

Z0=complex(0.1234,1.3456)
def act(m,z):
    a,b=m.m[0]; c,d=m.m[1]
    return (a*z+b)/(c*z+d)
def dist_i(m):
    w=act(m,Z0)
    return 1+abs(w-Z0)**2/(2*Z0.imag*w.imag)
def dist_old(m):
    # hyperbolic "size": ||m||^2 = a^2+b^2+c^2+d^2 = 2cosh d(i, m i)
    return sum(x*x for row in m.m for x in row)

def reduce_word(g, G, maxlen=200):
    # try to write g (float matrix, in SL2R) as word in G (up to sign), greedy reduction of size
    word=[]; cur=g.copy()
    for _ in range(maxlen):
        s=dist_i(cur)
        if s < 1+1e-9:  # cur = ±1 or rotation fixing i
            return word, cur
        best=None
        for k,m in G.items():
            c2 = m @ cur
            s2=dist_i(c2)
            if best is None or s2<best[0]: best=(s2,k,c2)
        if best[0] >= s-1e-9:
            return word, cur
        word.append(best[1]); cur=best[2]
    return word, cur

case=sys.argv[1]
G=gens(case)
# add more generators for greedy robustness
G2=dict(G)
inv_letter={'a':'A','A':'a','b':'B','B':'b'}
frontier=[k for k in G]
L=int(sys.argv[2]) if len(sys.argv)>2 else 4
for length in range(2,L+1):
    new=[]
    for w in frontier:
        for x in 'aAbB':
            if inv_letter[x]==w[-1]: continue
            ww=w+x
            G2[ww]=G2[w]@G[x]
            new.append(ww)
    frontier=new
print("gens",len(G2))
def member(g):
    w,cur=reduce_word(fmat(g),G2)
    ok = close(cur,1) or close(cur,-1)
    return ok, w, cur
# coset enumeration (right cosets H g) via BFS
reps=[I]; 
def find(g):
    for j,r in enumerate(reps):
        ok,w,cur = member(mul(g, inv(r)))
        if ok: return j,w,cur
    return None
table={}
i=0
while i < len(reps):
    for gname,gm in (('S',S),('T',T),('Ti',inv(T))):
        g=mul(reps[i],gm)
        f=find(g)
        if f is None:
            reps.append(g); j=len(reps)-1; w=[]
        else:
            j,w,cur=f
        table[(i,gname)]=(j,w)
    i+=1
    if len(reps)>200: print("too many"); break
print(case, "index", len(reps))
print(max(len(v[1]) for v in table.values()))
