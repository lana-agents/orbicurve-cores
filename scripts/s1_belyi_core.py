import numpy as np, sys
from numpy.polynomial import polynomial as P
rng=np.random.default_rng(7)
m=[int(a) for a in sys.argv[1:4]]
def F(v):
    h=np.concatenate([v[0:4],[1]]); k=np.concatenate([v[4:10],[1]]); b=v[10]; c=v[11]
    D=P.polymul(P.polymul(P.polypow([0,1],m[0]),P.polypow([-b,1],m[1])),P.polypow([-c,1],m[2]))
    lhs=np.zeros(13,complex)
    t=P.polypow(h,3); lhs[:len(t)]+=t
    t=P.polymul(k,k); lhs[:len(t)]-=t
    lhs[:len(D)]-=D
    return lhs[:12]
def newton(v):
    for it in range(80):
        f=F(v)
        if np.linalg.norm(f)<1e-10: return v
        J=np.zeros((12,12),complex); eps=1e-7
        for i in range(12):
            e=np.zeros(12,complex); e[i]=eps
            J[:,i]=(F(v+e)-f)/eps
        try: dv=np.linalg.solve(J,-f)
        except: return None
        v=v+dv
        if np.linalg.norm(v)>1e9: return None
    return None
