/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Defs

/-!
# Rigidity, step 1: reduction to lattice curves

A uniformisation `Uniformizes W A B` of an elliptic curve `W` over `ℂ` transports along a change
of variables to a uniformisation of the lattice curve `E_τ` with `j(E_τ) = j(W)`.
-/

open UpperHalfPlane
open scoped MatrixGroups

namespace OrbicurveCores.S1.Rigidity

/-- The period pair `(τ, 1)`. -/
noncomputable abbrev Lt (τ : ℍ) : PeriodPair := Heights.periodPairOfUpperHalfPlane τ

/-- The derivative of the first coordinate of a curve in `ℂ × ℂ`. -/
lemma hasDerivAt_fst' {f : ℂ → ℂ × ℂ} {d : ℂ × ℂ} {z : ℂ} (h : HasDerivAt f d z) :
    HasDerivAt (fun w ↦ (f w).1) d.1 z :=
  (hasFDerivAt_fst (p := f z)).comp_hasDerivAt z h

/-- The derivative of the second coordinate of a curve in `ℂ × ℂ`. -/
lemma hasDerivAt_snd' {f : ℂ → ℂ × ℂ} {d : ℂ × ℂ} {z : ℂ} (h : HasDerivAt f d z) :
    HasDerivAt (fun w ↦ (f w).2) d.2 z :=
  (hasFDerivAt_snd (p := f z)).comp_hasDerivAt z h

/-- **Reduction to lattice curves.** A uniformisation of `W` gives one of a lattice curve `E_τ`
with the same `j`-invariant, by the same pair `A, B`. -/
theorem uniformizes_lattice {W : WeierstrassCurve ℂ} [W.IsElliptic] {A B : SL(2, ℝ)}
    (h : Uniformizes W A B) :
    ∃ τ : ℍ, W.j = Heights.modularJ τ ∧
      Uniformizes (Heights.latticeWeierstrassCurve τ) A B := by
  obtain ⟨π, hd, heq, hsurj, hfib⟩ := h
  obtain ⟨τ, hτ⟩ := Heights.modularJ_surjective W.j
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq
    (Heights.latticeWeierstrassCurve τ) W (by rw [Heights.latticeWeierstrassCurve_j, hτ])
  refine ⟨τ, hτ.symm, ?_⟩
  set u : ℂ := (C.u : ℂ)
  have hu : u ≠ 0 := C.u.ne_zero
  set F : ℂ × ℂ → ℂ × ℂ := fun P ↦
    (u ^ 2 * P.1 + C.r, u ^ 3 * P.2 + u ^ 2 * C.s * P.1 + C.t) with hFdef
  have hF : ∀ P : ℂ × ℂ, W.toAffine.Equation P.1 P.2 ↔
      (Heights.latticeWeierstrassCurve τ).toAffine.Equation (F P).1 (F P).2 := by
    intro P
    rw [← hC, WeierstrassCurve.variableChange_equation_iff]
  have hFinj : ∀ P Q, F P = F Q → P = Q := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ h
    simp only [hFdef, Prod.mk.injEq] at h
    have hx : x = x' := by
      have := h.1
      have h2 : u ^ 2 ≠ 0 := pow_ne_zero 2 hu
      exact mul_left_cancel₀ h2 (by linear_combination this)
    subst hx
    have h3 : u ^ 3 ≠ 0 := pow_ne_zero 3 hu
    exact Prod.ext rfl (mul_left_cancel₀ h3 (by linear_combination h.2))
  have hFsurj : ∀ Q : ℂ × ℂ, ∃ P, F P = Q := by
    rintro ⟨X, Y⟩
    refine ⟨(u⁻¹ ^ 2 * (X - C.r), u⁻¹ ^ 3 * (Y - C.s * (X - C.r) - C.t)), ?_⟩
    simp only [hFdef, Prod.mk.injEq]
    constructor <;> field_simp <;> ring
  refine ⟨F ∘ π, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨hdz, hnz⟩ := hd z
    have hπ := hdz.hasDerivAt
    set d := deriv π z
    have h1 := ((hasDerivAt_fst' hπ).const_mul (u ^ 2)).add_const C.r
    have h2 := ((((hasDerivAt_snd' hπ).const_mul (u ^ 3)).add
      ((hasDerivAt_fst' hπ).const_mul (u ^ 2 * C.s))).add_const C.t)
    have hFπ : HasDerivAt (F ∘ π) (u ^ 2 * d.1, u ^ 3 * d.2 + u ^ 2 * C.s * d.1) z :=
      h1.prodMk h2
    refine ⟨hFπ.differentiableAt, ?_⟩
    rw [hFπ.deriv]
    intro h0
    simp only [Prod.mk_eq_zero] at h0
    have hd1 : d.1 = 0 := by
      rcases mul_eq_zero.mp h0.1 with h | h
      · exact absurd h (pow_ne_zero 2 hu)
      · exact h
    have hd2 : d.2 = 0 := by
      have := h0.2
      rw [hd1, mul_zero, add_zero] at this
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h (pow_ne_zero 3 hu)
      · exact h
    exact hnz (Prod.ext hd1 hd2)
  · intro z
    exact (hF (π z)).mp (heq z)
  · intro X Y hXY
    obtain ⟨P, hP⟩ := hFsurj (X, Y)
    have hWP : W.toAffine.Equation P.1 P.2 := (hF P).mpr (by rw [hP]; exact hXY)
    obtain ⟨z, hz⟩ := hsurj P.1 P.2 hWP
    exact ⟨z, by simp only [Function.comp_apply, hz, hP]⟩
  · intro z w
    rw [← hfib z w]
    exact ⟨hFinj _ _, fun h ↦ by simp only [Function.comp_apply, h]⟩

end OrbicurveCores.S1.Rigidity
