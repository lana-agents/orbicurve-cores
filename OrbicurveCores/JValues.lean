/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# The four exceptional `j`-invariants

[EstIUT] (Mochizuki–Fesenko–Hoshi–Minamide–Porowski, *Explicit estimates in inter-universal
Teichmüller theory*, Prop. 2.1): if `E ∖ {0}` fails to admit a core, then

  `j(E) ∈ {2¹⁴·31³/5³, 2²·73³/3⁴, 1728, 0}`.

The values come from J. Sijsling, *Canonical models of arithmetic (1;∞)-curves*
(arXiv:1707.01158), Table 4. It lists the canonical models over `ℚ` of the compactified quotients
`Γ \ ℍ` for Takeuchi's four arithmetic `(1;∞)`-groups:

| case | trace triple | model | LMFDB | `j` |
|---|---|---|---|---|
| I | `(√5, 2√5, 5)` | `y² = x³ - 44x² - 16x` | 20.a1 | `2¹⁴·31³/5³` |
| II | `(√6, 2√3, 3√2)` | `y² = x³ - 4x² - 384x - 2304` | 24.a3 | `2²·73³/3⁴` |
| III | `(2√2, 2√2, 4)` | `y² = x(x² - 256)` | 32.a4 | `1728` |
| IV | `(3, 3, 3)` | `y² = x³ - 1728` | 36.a3 | `0` |

This file defines the finite set `OrbicurveCores.exceptionalJ` of these values and checks, as a
consistency test, that the four Weierstrass models have these `j`-invariants.
-/

namespace OrbicurveCores

/-- The four exceptional `j`-invariants of [CanLift] Prop. 2.7 / [EstIUT] Prop. 2.1. -/
def exceptionalJ : Finset ℚ := {0, 1728, 2 ^ 14 * 31 ^ 3 / 5 ^ 3, 2 ^ 2 * 73 ^ 3 / 3 ^ 4}

lemma exceptionalJ_eq : exceptionalJ = {0, 1728, 488095744 / 125, 1556068 / 81} := by
  simp only [exceptionalJ]
  norm_num

/-- `j` belongs to the exceptional set, in any field of characteristic zero. -/
def IsExceptionalJ {K : Type*} [Field K] [CharZero K] (j : K) : Prop :=
  ∃ q ∈ exceptionalJ, (q : K) = j

/-- Case I: `y² = x³ - 44x² - 16x` (LMFDB 20.a1). -/
def curveI : WeierstrassCurve ℚ := ⟨0, -44, 0, -16, 0⟩
/-- Case II: `y² = x³ - 4x² - 384x - 2304` (LMFDB 24.a3). -/
def curveII : WeierstrassCurve ℚ := ⟨0, -4, 0, -384, -2304⟩
/-- Case III: `y² = x³ - 256x` (LMFDB 32.a4). -/
def curveIII : WeierstrassCurve ℚ := ⟨0, 0, 0, -256, 0⟩
/-- Case IV: `y² = x³ - 1728` (LMFDB 36.a3). -/
def curveIV : WeierstrassCurve ℚ := ⟨0, 0, 0, 0, -1728⟩

instance : curveI.IsElliptic := ⟨by
  rw [isUnit_iff_ne_zero]; simp [curveI, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]; norm_num⟩
instance : curveII.IsElliptic := ⟨by
  rw [isUnit_iff_ne_zero]; simp [curveII, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]; norm_num⟩
instance : curveIII.IsElliptic := ⟨by
  rw [isUnit_iff_ne_zero]; simp [curveIII, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩
instance : curveIV.IsElliptic := ⟨by
  rw [isUnit_iff_ne_zero]; simp [curveIV, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

lemma j_curveI : curveI.j = 2 ^ 14 * 31 ^ 3 / 5 ^ 3 := by
  simp [WeierstrassCurve.j, curveI, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma j_curveII : curveII.j = 2 ^ 2 * 73 ^ 3 / 3 ^ 4 := by
  simp [WeierstrassCurve.j, curveII, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma j_curveIII : curveIII.j = 1728 := by
  simp [WeierstrassCurve.j, curveIII, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

lemma j_curveIV : curveIV.j = 0 := by
  simp [WeierstrassCurve.j, curveIV, WeierstrassCurve.Δ, WeierstrassCurve.c₄,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

end OrbicurveCores
