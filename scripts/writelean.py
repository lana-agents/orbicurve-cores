import json
out=json.load(open('certs.json'))
names={'I':('pairIA','pairIB','⟨4, 1, -1, 1⟩','⟨3, 2, 8, 7⟩',5,5,0),
       'II':('pairIIA','pairIIB','⟨5, 1, -1, 1⟩','⟨2, 1, 5, 4⟩',6,3,1),
       'III':('pairIIIA','pairIIIB','⟨3, 1, 1, 1⟩','⟨1, 1, 1, 3⟩',2,2,2),
       'IV':('pairIVA','pairIVB','⟨2, 1, 1, 1⟩','⟨0, -1, 1, 3⟩',1,1,3)}
L=[]
L.append('''/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Sharpness

/-!
# Takeuchi's four groups are arithmetic (sharpness)

Certificates, found by computer and checked here by `decide`: coset enumeration of
`Γᵢ ∩ SL(2, ℤ)` in `SL(2, ℤ)`, and a transversal of `Γᵢ ∩ SL(2, ℤ)` in `Γᵢ`, for the four explicit
pairs of `OrbicurveCores.FourGroups`. The number of cosets agrees with [Sijs] Table 3: 12, 24, 12
and 6 cosets of `±(Γᵢ ∩ SL(2,ℤ))`, doubled here to absorb signs.

Consequently each `Γᵢ = ⟨Aᵢ, Bᵢ⟩` is arithmetic (`takeuchiPair_isArithmeticSL`) and admits no
core (`takeuchiPair_not_admitsCore`). This is the converse half of Takeuchi's theorem, so the list
of four in `takeuchi_one_infty_conj` and `canLift27_group_conj` is sharp.
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace OrbicurveCores.Sharp
''')
for case,cc,tc in out:
    A,B,M,N,n,k,i=names[case]
    L.append(f'''
/-- Cover certificate, case {case}. -/
def cover{case} : CoverCert := [
  ''' + ",\n  ".join(r.replace("), (", "),\n    (") if len(r)>98 else r for r in cc) + f''']

/-- Transversal certificate, case {case}. -/
def trans{case} : TransCert := [
  ''' + ",\n  ".join(r.replace("), (", "),\n    (") if len(r)>98 else r for r in tc) + f''']

lemma cover{case}_ok : coverOK {M} {N} {n} {k} cover{case} = true := by decide

lemma trans{case}_ok : transOK {M} {N} {n} {k} trans{case} = true := by decide
''')
for case,cc,tc in out:
    A,B,M,N,n,k,i=names[case]
    L.append(f"""
lemma {A}_eq :
    ({A} : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt ({n} : ℕ))⁻¹ • IM.toR {M} := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [{A}, scaledSL, IM.toR]

lemma {B}_eq :
    ({B} : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt ({k} : ℕ))⁻¹ • IM.toR {N} := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [{B}, scaledSL, IM.toR]
""")
L.append("""
/-- **Sharpness of Takeuchi's list**: each of the four explicit `(1;∞)`-groups is arithmetic. -/
theorem takeuchiPair_isArithmeticSL (i : Fin 4) :
    IsArithmeticSL (Subgroup.closure {(takeuchiPair i).1, (takeuchiPair i).2}) := by
  fin_cases i
""")
for case in ['I','II','III','IV']:
    A,B,M,N,n,k,i=names[case]
    L.append(f"""  · exact isArithmeticSL_of_certs (by norm_num) (by norm_num) {A}_eq {B}_eq
      cover{case}_ok trans{case}_ok
""")
L.append("""
/-- Each of the four explicit `(1;∞)`-groups admits **no core**. -/
theorem takeuchiPair_not_admitsCore (i : Fin 4) :
    ¬ AdmitsCore (Subgroup.closure {(takeuchiPair i).1, (takeuchiPair i).2}) :=
  (takeuchiPair_isArithmeticSL i).not_admitsCore
""")
L.append("\nend OrbicurveCores.Sharp\n")
open('/home/christian/orbicurve-cores/OrbicurveCores/SharpnessData.lean','w').write("".join(L))
