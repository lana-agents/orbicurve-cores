/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# The Diophantine core of Takeuchi's classification of arithmetic `(1;∞)`-groups

Let `Γ = ⟨A, B⟩ ⊆ SL(2, ℝ)` with parabolic commutator, `tr [A, B] = -2`, and write
`x = tr A`, `y = tr B`, `z = tr AB`. Fricke's identity gives `x² + y² + z² = xyz`. If `Γ` is
arithmetic then `X = x²`, `Y = y²`, `Z = z²` are integers (see `OrbicurveCores.ArithTraces`),
and so is `W = xyz = X + Y + Z`. These integers satisfy

  `(X + Y + Z)² = X Y Z`.

The Vieta involution `z ↦ xy - z`, which comes from the Nielsen move `(A, B) ↦ (A⁻¹, B)`, acts by
`Z ↦ XY - 2(X + Y + Z) + Z`. A triple is *reduced* when no Vieta move decreases `X + Y + Z`.
This file shows that a reduced positive triple with `X ≤ Y ≤ Z` is one of

  `(9, 9, 9)`, `(8, 8, 16)`, `(5, 20, 25)`, `(6, 12, 18)`,

which are the squared trace triples `(3,3,3)`, `(2√2,2√2,4)`, `(√5,2√5,5)` and `(√6,2√3,3√2)` of
[Take2] (K. Takeuchi, *Arithmetic Fuchsian groups with signature (1;e)*, J. Math. Soc. Japan 35,
1983, Thm. 4.1(i); see also J. Sijsling, arXiv:1707.01158, Table 1).

## Main results

* `OrbicurveCores.Markov.reduced_classification`: the classification of reduced sorted triples.
* `OrbicurveCores.Markov.vieta_lt`: a non-reduced coordinate decreases under the Vieta move.
-/

namespace OrbicurveCores.Markov

/-- The four squared trace triples of the arithmetic `(1;∞)`-groups, sorted increasingly. -/
def IsTakeuchiTriple (X Y Z : ℤ) : Prop :=
  (X = 9 ∧ Y = 9 ∧ Z = 9) ∨ (X = 8 ∧ Y = 8 ∧ Z = 16) ∨ (X = 5 ∧ Y = 20 ∧ Z = 25) ∨
    (X = 6 ∧ Y = 12 ∧ Z = 18)

/-- Finite search behind `reduced_classification`. -/
private theorem search : ∀ X : Fin 10, ∀ Y : Fin 39, ∀ Z : Fin 48,
    ((X : ℕ) + Y + Z) ^ 2 = X * Y * Z → 2 * ((X : ℕ) + Y + Z) ≤ X * Y → (X : ℕ) ≤ Y →
    (Y : ℕ) ≤ Z → 5 ≤ (X : ℕ) →
    ((X : ℕ) = 9 ∧ (Y : ℕ) = 9 ∧ (Z : ℕ) = 9) ∨ ((X : ℕ) = 8 ∧ (Y : ℕ) = 8 ∧ (Z : ℕ) = 16) ∨
      ((X : ℕ) = 5 ∧ (Y : ℕ) = 20 ∧ (Z : ℕ) = 25) ∨
      ((X : ℕ) = 6 ∧ (Y : ℕ) = 12 ∧ (Z : ℕ) = 18) := by
  decide

/-- **Takeuchi's Diophantine lemma.** A positive solution of `(X + Y + Z)² = XYZ` with
`X ≤ Y ≤ Z` which is reduced (`2(X + Y + Z) ≤ XY`, i.e. the Vieta move in the largest coordinate
does not decrease it) is one of the four triples of `IsTakeuchiTriple`. -/
theorem reduced_classification {X Y Z : ℤ} (hX : 0 < X) (hXY : X ≤ Y) (hYZ : Y ≤ Z)
    (hrel : (X + Y + Z) ^ 2 = X * Y * Z) (hred : 2 * (X + Y + Z) ≤ X * Y) :
    IsTakeuchiTriple X Y Z := by
  have hY : 0 < Y := by lia
  have hZ : 0 < Z := by lia
  -- the other root of `t ↦ t² - (XY - 2(X+Y)) t + (X+Y)²` is `Z' = XY - 2(X+Y) - Z ≥ Z`
  have hroot : Z * (X * Y - 2 * (X + Y) - Z) = (X + Y) ^ 2 := by linear_combination -hrel
  have hZZ' : Z ≤ X * Y - 2 * (X + Y) - Z := by lia
  -- hence `Z ≤ X + Y`
  have hZle : Z ≤ X + Y := by nlinarith
  -- `X ≥ 5`
  have hX5 : 5 ≤ X := by
    by_contra h
    have : X * Y * Z ≤ 4 * Y * Z := by
      have : X ≤ 4 := by lia
      have := mul_pos hY hZ
      nlinarith
    nlinarith [sq_nonneg (Y - Z)]
  -- `Y` is at most the smaller root, so the quadratic is nonnegative at `Y`
  have hpY : 0 ≤ (Y - Z) * (Y - (X * Y - 2 * (X + Y) - Z)) := by
    apply mul_nonneg_of_nonpos_of_nonpos <;> lia
  have hpY' : Y ^ 2 * (X - 4) ≤ 4 * X * Y + X ^ 2 := by nlinarith
  have hX9 : X ≤ 9 := by
    by_contra h
    have h1 : 5 * Y ^ 2 < Y ^ 2 * (X - 4) := by
      have : 0 < Y ^ 2 := by positivity
      nlinarith
    nlinarith
  have hY38 : Y ≤ 38 := by
    by_contra h
    have : Y ^ 2 ≤ Y ^ 2 * (X - 4) := by nlinarith
    nlinarith
  have hZ47 : Z ≤ 47 := by lia
  -- finite search
  lift X to ℕ using hX.le
  lift Y to ℕ using hY.le
  lift Z to ℕ using hZ.le
  have := search ⟨X, by lia⟩ ⟨Y, by lia⟩ ⟨Z, by lia⟩ (by exact_mod_cast hrel)
    (by exact_mod_cast hred) (by exact_mod_cast hXY) (by exact_mod_cast hYZ)
    (by exact_mod_cast hX5)
  simp only at this
  rcases this with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ <;>
    subst h1 h2 h3 <;> simp [IsTakeuchiTriple]

/-- The Vieta move `z ↦ xy - z` on squared traces: if `Z' = XY - 2W + Z` with `W = X + Y + Z`,
then the new triple satisfies the same relation. -/
theorem vieta_rel {X Y Z : ℤ} (hrel : (X + Y + Z) ^ 2 = X * Y * Z) :
    (X + Y + (X * Y - 2 * (X + Y + Z) + Z)) ^ 2 = X * Y * (X * Y - 2 * (X + Y + Z) + Z) := by
  linear_combination hrel

/-- A non-reduced coordinate strictly decreases under the Vieta move. -/
theorem vieta_lt {X Y Z : ℤ} (h : X * Y < 2 * (X + Y + Z)) :
    X * Y - 2 * (X + Y + Z) + Z < Z := by
  lia

end OrbicurveCores.Markov
