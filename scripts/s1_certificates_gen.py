from sympy import *
x=symbols('x')
def lean(p):
    p=Poly(expand(p),x)
    terms=[]
    for (k,),c in sorted(p.terms(),key=lambda t:-t[0][0]):
        c=Integer(c)
        mon = "" if k==0 else ("X" if k==1 else f"X ^ {k}")
        a=abs(c)
        if k==0: t=f"{a}"
        elif a==1: t=mon
        else: t=f"{a} * {mon}"
        terms.append(("-" if c<0 else "+",t))
    if not terms: return "0"
    toks=[("-" if terms[0][0]=="-" else "")+terms[0][1]]+[f"{sg} {t}" for sg,t in terms[1:]]
    lines=[]; cur="("
    for t in toks:
        piece=(t if cur=="(" else " "+t)
        if len(cur)+len(piece)>70:
            lines.append(cur); cur="      "+t
        else: cur+=piece
    lines.append(cur+")")
    return "\n".join(lines)
def clear(a,b,g):
    # a*P+b*Q=g (g const); scale to integers
    den=ilcm(*[Rational(c).q for c in Poly(a,x).all_coeffs()+Poly(b,x).all_coeffs()+[g]])
    return expand(a*den),expand(b*den),g*den
def bez(P,Q):
    a,b,g=gcdex(Poly(P,x),Poly(Q,x))
    assert g.degree()==0
    a,b,d=clear(a.as_expr(),b.as_expr(),g.as_expr())
    assert expand(a*P+b*Q-d)==0
    return a,b,d
def cert(name,f,N,D,H,K,c):
    assert expand(N-c*H**3)==0
    assert expand(N-1728*D-c*K**2)==0
    crit=expand(diff(N,x)*D-N*diff(D,x))
    R,rem=div(Poly(crit,x),Poly(H**2*K,x)); assert rem.is_zero; R=R.as_expr()
    qD,rem=div(Poly(D,x),Poly(f,x)); assert rem.is_zero
    # C d f^6 = D q
    def dvdf(P):
        q,rem=div(Poly(f**6,x),Poly(P,x)); assert rem.is_zero
        q=q.as_expr(); den=ilcm(*[Rational(cc).q for cc in Poly(q,x).all_coeffs()])
        return expand(q*den),den
    qDf,dD=dvdf(D); qRf,dR=dvdf(R)
    aH,bH,dH=bez(H,f); aK,bK,dK=bez(K,f)
    aH2,bH2,dH2=bez(diff(H,x),H); aK2,bK2,dK2=bez(diff(K,x),K)
    out={}
    out['f']=lean(f);out['H']=lean(H);out['K']=lean(K);out['D']=lean(D);out['R']=lean(R)
    out['qD']=lean(qD.as_expr());out['qDf']=lean(qDf);out['dD']=dD;out['qRf']=lean(qRf);out['dR']=dR
    out['aH']=lean(aH);out['bH']=lean(bH);out['dH']=dH
    out['aK']=lean(aK);out['bK']=lean(bK);out['dK']=dK
    out['aH2']=lean(aH2);out['bH2']=lean(bH2);out['dH2']=dH2
    out['aK2']=lean(aK2);out['bK2']=lean(bK2);out['dK2']=dK2
    out['c']=c
    return out
cases={}
f=x*(x**2+44*x-16); H=x**4+48*x**3+224*x**2-768*x+256; K=(x**2+16)*(x**4+72*x**3+1184*x**2-1152*x+256)
D=1024*x**5*(x**2+44*x-16)
cases['I']=cert('I',f,-H**3,D,H,K,-1)
f=(x-24)*(x+8)*(x+12); H=x*(x**3-384*x-3072); K=(x**2-192)*(x**4-384*x**2-4608*x-18432)
D=4096*(x-24)*(x+8)**3*(x+12)**2
cases['II']=cert('II',f,H**3,D,H,K,1)
f=x*(x**2-16); H=x**4+224*x**2+256; K=(x**2+16)*(x**2-24*x+16)*(x**2+24*x+16)
D=x**2*(x-4)**4*(x+4)**4
cases['III']=cert('III',f,H**3,D,H,K,1)
f=x**3-1728; H=x*(x+24)*(x**2-24*x+576); K=(x**2-24*x-288)*(x**4+24*x**3+864*x**2-6912*x+82944)
D=64*(x-12)**3*(x**2+12*x+144)**3
cases['IV']=cert('IV',f,H**3,D,H,K,1)
import json
json.dump(cases,open('/tmp/s1/certs.json','w'),indent=1,default=str)
for k,v in cases.items(): print(k, {kk:(len(str(vv)) ) for kk,vv in v.items()})
