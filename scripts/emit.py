import sys, math
sys.argv=['x']
exec(open('gen.py').read().split("if __name__")[0])
L2I={'a':0,'A':1,'b':2,'B':3}
def neg(m): return tuple(tuple(-x for x in r) for r in m)
def im(m): return "⟨%d, %d, %d, %d⟩"%(m[0][0],m[0][1],m[1][0],m[1][1])
def word(w): return "[" + ", ".join(str(L2I[c]) for c in w) + "]"
def cover_cert(case):
    reps,table=run(case)
    R2=[]
    for r in reps: R2.append(r)
    for r in reps: R2.append(neg(r))
    idx={R2[i]:i for i in range(len(R2))}
    assert len(idx)==len(R2)
    rows=[]
    m=len(reps)
    for eps,base in ((1,0),(-1,m)):
        for i,r in enumerate(reps):
            ents=[]
            for (j,w,sg) in table[i]:
                # eps*r*g = w * (eps*sg*r_j)
                tgt = j if eps*sg==1 else j+m
                M,n,N,k=cases[case]
                a=sum(1 for c in w if c in 'aA'); b=len(w)-a
                sq=n**a*k**b; s=math.isqrt(sq); assert s*s==sq
                ents.append("(%d, %s, %d)"%(tgt,word(w),s))
            rows.append("(%s, %s)"%(im(R2[base+i]), ", ".join(ents)))
    return rows
def adj(m): return ((m[1][1],-m[0][1]),(-m[1][0],m[0][0]))
def trans_cert(case):
    M,n,N,k=cases[case]
    LI={'a':M,'A':adj(M),'b':N,'B':adj(N)}
    inv_letter={'a':'A','A':'a','b':'B','B':'b'}
    if case=='IV': U=['']
    elif case in ('I','III'): U=['','a']
    else: U=['','a','b','ab']
    def cls(w):
        a=sum(1 for c in w if c in 'aA')%2; b=sum(1 for c in w if c in 'bB')%2
        if case=='IV': return 0
        if case in ('I','III'): return (a+b)%2
        return [(0,0),(1,0),(0,1),(1,1)].index((a,b))
    rows=[]
    for u in U:
        ents=[]
        for x in 'aAbB':
            j=cls(u+x); up=U[j]
            w=u+x+''.join(inv_letter[c] for c in reversed(up))
            P=I
            for c in w: P=mul(P,LI[c])
            a=sum(1 for c in w if c in 'aA'); b=len(w)-a
            sq=n**a*k**b; s=math.isqrt(sq); assert s*s==sq,(case,w)
            assert all(v%s==0 for r in P for v in r),(case,w,P,s)
            Z=tuple(tuple(v//s for v in r) for r in P)
            assert Z[0][0]*Z[1][1]-Z[0][1]*Z[1][0]==1
            ents.append("(%d, %s, %d)"%(j,im(Z),s))
        rows.append("(%s, %s)"%(word(u), ", ".join(ents)))
    return rows
out=[]
for case in ['I','II','III','IV']:
    cc=cover_cert(case); tc=trans_cert(case)
    out.append((case,cc,tc))
    print(case,len(cc),len(tc),file=sys.stderr)
import json
json.dump(out,open('certs.json','w'))
