import sys
exec(open(__file__.replace('s1_belyi_search','s1_belyi_core')).read().replace("rng=np.random.default_rng(7)","rng=np.random.default_rng(int(sys.argv[4]))").replace("m=[int(a) for a in sys.argv[1:4]]","m=[int(a) for a in sys.argv[1:4]]"))
def jl(r):
    return 256*(r*r-r+1)**3/(r*r*(r-1)**2)
found=[]
for trial in range(int(sys.argv[5])):
    v=rng.normal(size=12)*2+1j*rng.normal(size=12)*2
    s=newton(v)
    if s is None: continue
    b,c=s[10],s[11]
    if abs(b)<1e-4 or abs(c)<1e-4 or abs(b-c)<1e-4: continue
    h=np.concatenate([s[0:4],[1]]); k=np.concatenate([s[4:10],[1]])
    hr=np.roots(h[::-1]); kr=np.roots(k[::-1]); fr=np.array([0,b,c])
    sc=max(abs(b),abs(c))
    ok=True
    for R in (hr,kr):
        for i in range(len(R)):
            if min(abs(R[i]-fr))<1e-3*sc: ok=False
            for j2 in range(i+1,len(R)):
                if abs(R[i]-R[j2])<1e-3*sc: ok=False
    if not ok: continue
    jj=jl(b/c)
    key=(round(jj.real,2),round(jj.imag,2))
    if key not in found:
        found.append(key); print(sys.argv[1:4],"j=",key,flush=True)
