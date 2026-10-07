"""Mirror of the constant formulas of the Lean proof (Corner/Budget.lean, Final.lean).

consts(b, hp, hq, Tmin) returns (K0, C2 + 2, N0): K0 per log_b n, the n^2 coefficient
of pair_bound_of before the depth correction, and the least n. The depth correction
of pair_bound subtracts K0 * (log_b(2 Tbig) - 1). Keep in sync with the Lean
definitions; std_C1 / std_C2 in Final.lean are the authority.

    uv run python research/constants/mirror.py
"""
import math
def cdiv(a,b): return -(-a//b)
def layered(rho, J, hq):
    """hq times the layered harmonic sum of weights rho over J spokes, rounded up (Ledger.layered)."""
    from fractions import Fraction
    H=lambda N: sum(Fraction(1,t) for t in range(1,N+1))
    m=max(rho(j) for j in range(J))
    tot=sum(H(sum(1 for j in range(J) if v<rho(j))) for v in range(m))
    return -(-tot.numerator*hq//tot.denominator)
def consts(b=3,hp=2829,hq=1000,Tmin=107,verbose=False):
    W=2*b; M0=2*b*b+4; Tbig=M0+W+12+b*Tmin
    cs0=26*(M0-2)+50; sv=24*(M0-b*b-1)+46+4*(b-1)-2*W
    csl=24*(M0-2)+2*M0+4*b+50; lam=cdiv(csl+1,Tbig)
    dk=16+cdiv(24*W+170,Tbig)
    wrapC=2*(12*W+34)+2*(W+1)
    dc=24*W+170+wrapC
    cb0=24*(M0-2*b*b)+54+2*M0+4*(b-1)
    wp1=layered(lambda j: j//b+j%b, b*b, hq); wp2=layered(lambda j: b*b-1-j, b*b, hq)
    Kr=cdiv(hp*b*cb0+48*b*wp2+4*b*hq+b*hq*dc+(2*wp1+16*b*hq)*Tbig, (hq*b-hp)*Tbig)
    cr=2*(M0+b-1)+(b-1)*W
    crc=max(0,(M0+b-1)*(M0+b-1+b*W)+6-6*b*b)
    Lc=b*b*(2*b*b+4*b+4)
    al=3*(b-1)+2*(M0-2)+W*(b-2)
    fl=cdiv(9*(b*(6*(b-1+M0)**2+2*M0*W*b+3*W**2*b+6*W*b+2*W)),b)+cdiv(9*((b-1+M0)**2*(2*(b-1+M0)+W)),Tbig)+216*b*b+28*cr+168
    kap=W+4+M0; smax=24*(M0-2)+46+4*(b-1)-2*W
    lq=cdiv(4*sum((j//b+j%b)**2 for j in range(b*b)),b*b)
    ll=2*(4*kap+smax)*(b*(b-1))+cdiv(2*b*b*(kap*(2*kap+smax)),Tbig)
    sw=lambda r: 4+2*b*(r+1)
    gq=sum(sw(r)*(16*b-12*r-6) for r in range(b))//(b*b)
    gl=sum(sw(r)*((16*b-12*r-6)*W+max(0,18*W+54-4*M0)) for r in range(b))+2*gq*(M0+b)
    linC=b*b*(2*M0+4)+8*b*b+cdiv(Kr*(b*b+Lc),b)+b*b*cs0+2*(W+M0)+fl+ll+gl
    parts=dict(sv=sv,lanes=lq,rates=2*(b-1)*Kr,wrap=wrapC,dx=dk*cr-gq,sort=18*al,lin=cdiv(max(0,linC-dk*crc),Tbig))
    K0=sum(parts.values())
    Kl=cdiv(280*Tbig+(288*W+2526),12)
    N0=2*(Tmin+W+12)+6
    Croot=394+374+33*(8+2*W+5)
    Clin=16*2*394+4*394+8*7+2+Kr*44+150+276*(8+2*W+5)+3*394+3*Kr+658
    C2=Kl+Croot+cdiv(Clin+922,N0)+108+2
    if verbose: print(parts, dict(lam=lam,dk=dk,gq=gq,gl=gl,Kr=Kr,wp1=wp1,wp2=wp2,cr=cr,crc=crc,Tbig=Tbig,Kl=Kl,Croot=Croot))
    return K0,C2,N0
def effective(Tmin=107):
    import math
    K0, C2, N0 = consts(Tmin=Tmin)
    Tbig = 22+6+12+3*Tmin
    return math.ceil(K0/1.098546), round(C2-K0*(math.log(2*Tbig)/math.log(3)-1)), N0

if __name__=="__main__":
    for T in [107, 140, 203, 300]:
        print(T, effective(T))
    K0,C2,N0=consts(verbose=True)
    print(K0, K0/1.098546, C2, N0)
