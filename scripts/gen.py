import sys, math
exec(open('ce.py').read().split("case=sys.argv[1]")[0])
from fractions import Fraction

def imul(a,b): return mul(a,b)
def adj(m): return ((m[1][1],-m[0][1]),(-m[1][0],m[0][0]))
letters_int = None

def run(case, L=4):
    global G2
    M,n,N,k = cases[case]
    LI = {'a':M,'A':adj(M),'b':N,'B':adj(N)}
    G=gens(case)
    G2=dict(G)
    inv_letter={'a':'A','A':'a','b':'B','B':'b'}
    frontier=[x for x in G]
    for length in range(2,L+1):
        new=[]
        for w in frontier:
            for x in 'aAbB':
                if inv_letter[x]==w[-1]: continue
                ww=w+x; G2[ww]=G2[w]@G[x]; new.append(ww)
        frontier=new
    def member(g):
        w,cur=reduce_word(fmat(g),G2)
        if close(cur,1): sign=1
        elif close(cur,-1): sign=-1
        else: return None
        # G2[w_m]...G2[w_1] g = sign  => g = sign * inverse
        full=''.join(w[::-1])  # product order: w_m ... w_1 ; as letters string left-to-right
        # full string represents product G[full[0]] G[full[1]] ...
        invw=''.join(inv_letter[c] for c in reversed(full))
        return invw, sign
    def evalint(w):
        P=I
        for c in w: P=imul(P,LI[c])
        return P
    def scale(w):
        a=sum(1 for c in w if c in 'aA'); b=len(w)-a
        sq=n**a*k**b; r=math.isqrt(sq)
        assert r*r==sq,(w,a,b)
        return r
    reps=[I]; table=[]
    Sinv=inv(S)
    gensS=[('S',S),('T',T),('Si',Sinv),('Ti',inv(T))]
    i=0
    while i<len(reps):
        row=[]
        for gname,gm in gensS:
            g=mul(reps[i],gm)
            found=None
            for j,r in enumerate(reps):
                m=member(mul(g,inv(r)))
                if m: found=(j,m[0],m[1]); break
            if found is None:
                reps.append(g); found=(len(reps)-1,'',1)
            j,w,sg=found
            # exact check: evalint(w) * reps[j] == sg*scale(w) * g
            lhs=imul(evalint(w),reps[j]); sc=scale(w)
            rhs=tuple(tuple(sg*sc*x for x in row_) for row_ in g)
            assert lhs==rhs,(case,i,gname)
            row.append((j,w,sg))
        table.append(row); i+=1
        assert len(reps)<100
    return reps, table

if __name__=='__main__':
    for case in sys.argv[1:]:
        reps,table=run(case)
        print(case,len(reps), max(len(w) for row in table for (_,w,_) in row))
