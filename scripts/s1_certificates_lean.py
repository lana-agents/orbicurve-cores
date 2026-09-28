import json
C=json.load(open('/tmp/s1/certs.json'))
def cnum(n):
    n=int(n)
    return f"({n})" if n<0 else f"{n}"
out=[]
for name,v in C.items():
    c=int(v['c'])
    N = f"-{name}H ^ 3" if c==-1 else f"{name}H ^ 3"
    cC = "C (-1)" if c==-1 else "C 1"
    out.append(f"""
/-! ### Case {name} -/

/-- The cubic of case {name}. -/
noncomputable def f{name} : ℂ[X] :=
  {v['f']}
/-- `H` for case {name}. -/
noncomputable def {name}H : ℂ[X] :=
  {v['H']}
/-- `K` for case {name}. -/
noncomputable def {name}K : ℂ[X] :=
  {v['K']}
/-- The denominator of `G` for case {name}. -/
noncomputable def {name}D : ℂ[X] :=
  {v['D']}
/-- The numerator of `G` for case {name}. -/
noncomputable def {name}N : ℂ[X] := {N}
/-- The critical cofactor for case {name}. -/
noncomputable def {name}R : ℂ[X] :=
  {v['R']}

theorem cert{name} : RatCert f{name} {name}N {name}D {name}H {name}K {name}R ({c}) where
  c_ne := by norm_num
  hN := by simp only [{name}N, map_neg, map_one]; ring
  hK := by simp only [{name}N, {name}D, {name}H, {name}K, map_neg, map_one]; ring
  hcrit := by
    simp only [{name}N, {name}D, {name}H, {name}K, {name}R, derivative_mul, derivative_pow,
      derivative_add, derivative_sub, derivative_neg, derivative_X, derivative_ofNat,
      map_natCast, Nat.cast_ofNat, map_ofNat]
    ring
  f_dvd_D := ⟨
    {v['qD']}, by simp only [{name}D, f{name}]; ring⟩
  D_dvd_f := ⟨
    {v['qDf']},
    {v['dD']}, by norm_num, by
    simp only [{name}D, f{name}, map_ofNat, map_one]; ring⟩
  R_dvd_f := ⟨
    {v['qRf']},
    {v['dR']}, by norm_num, by
    simp only [{name}R, f{name}, map_ofNat, map_one]; ring⟩
  H_cop := ⟨
    {v['aH']},
    {v['bH']},
    {cnum(v['dH'])}, by norm_num, by
    simp only [{name}H, f{name}, map_ofNat, map_neg]; ring⟩
  K_cop := ⟨
    {v['aK']},
    {v['bK']},
    {cnum(v['dK'])}, by norm_num, by
    simp only [{name}K, f{name}, map_ofNat, map_neg]; ring⟩
  H_sqf := ⟨
    {v['aH2']},
    {v['bH2']},
    {cnum(v['dH2'])}, by norm_num, by
    simp only [{name}H, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  K_sqf := ⟨
    {v['aK2']},
    {v['bK2']},
    {cnum(v['dK2'])}, by norm_num, by
    simp only [{name}K, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  deg := by
    have hH : natDegree {name}H = 4 := by unfold {name}H; compute_degree!
    have h1 : natDegree {name}D ≤ 11 := by unfold {name}D; compute_degree; all_goals norm_num
    have h2 : natDegree {name}N = 12 := by
      rw [{name}N, {"natDegree_neg, " if c==-1 else ""}natDegree_pow, hH]
    omega
  D_ne := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [{name}D, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_ofNat, eval_zero] at h1
    norm_num at h1
""")
hdr='''/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Rational

/-!
# The four Belyi certificates

For each of the four curves `y² = f(x)` of [Sijs] Table 4 (up to isomorphism over `ℚ`) the
rational function `G = N / D` of `Blueprint.md` §2.3c, with its certificate `RatCert`. The
witnesses (quotients, Bézout coefficients) were computed by `scripts/s1_certificates.py`; here
every identity is checked by `ring`.
-/

open Polynomial

set_option linter.unusedSimpArgs false

namespace OrbicurveCores.S1
'''
open('/tmp/s1/Certificates.lean','w').write(hdr+''.join(out)+'\nend OrbicurveCores.S1\n')
