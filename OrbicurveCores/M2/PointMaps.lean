/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.ErgodicUse
import OrbicurveCores.M2.CrossRatio

/-!
# M2: equivariant point maps to `ℙ¹(k)`

Setting: `Γ ≤ SL(2, ℝ)` acts on `Y = OnePoint k` through `a : SL(2, ℝ) → GL(2, k)`
(`ActsOn`: `a` is multiplicative on `Γ` as an action on `Y`). `NonElem Γ a`: no finite-index
subgroup of `Γ` has a common fixed point.

* `ae_ne_of_equivariant`: an equivariant measurable map `ψ : B → Y` is essentially
  non-constant: `ψ x₁ ≠ ψ x₂` for almost every pair.
-/

open MeasureTheory Filter Set
open scoped MatrixGroups

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

/-- `ψ` is almost everywhere `Γ`-equivariant for the action `a`. -/
def Equivariant (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k)
    (ψ : OnePoint ℝ → OnePoint k) : Prop :=
  ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, ψ (γ • x) = a γ • ψ x

/-- `a` is multiplicative on `Γ`, as an action on `ℙ¹(k)`. -/
def ActsOn (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k) : Prop :=
  ∀ g ∈ Γ, ∀ h ∈ Γ, ∀ y : OnePoint k, a (g * h) • y = a g • a h • y

/-- No finite-index subgroup of `Γ` fixes a point of `ℙ¹(k)`. -/
def NonElem (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k) : Prop :=
  ∀ Γ' : Subgroup SL(2, ℝ), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 →
    ∀ y : OnePoint k, ∃ γ ∈ Γ', a γ • y ≠ y

omit [ProperSpace k] in
lemma ActsOn.one {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    (y : OnePoint k) : a 1 • y = y := by
  have := h 1 (one_mem _) 1 (one_mem _) y
  rw [mul_one] at this
  exact ((smul_left_cancel_iff (a 1)).1 this).symm

omit [ProperSpace k] in
lemma ActsOn.inv {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Γ) (y : OnePoint k) : a γ⁻¹ • a γ • y = y := by
  rw [← h _ (inv_mem hγ) _ hγ, inv_mul_cancel, h.one]

/-- A.e. statements transport along the boundary action. -/
lemma ae_smul {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) (g : SL(2, ℝ)) :
    ∀ᵐ x ∂bdry, p (g • x) :=
  (quasiMeasurePreserving_smul g).ae h

lemma ae_fst {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) :
    ∀ᵐ q ∂(bdry.prod bdry), p q.1 :=
  Measure.quasiMeasurePreserving_fst.ae h

lemma ae_snd {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) :
    ∀ᵐ q ∂(bdry.prod bdry), p q.2 :=
  Measure.quasiMeasurePreserving_snd.ae h

lemma exists_of_ae {p : OnePoint ℝ → Prop} (h : ∀ᵐ x ∂bdry, p x) : ∃ x, p x := by
  by_contra hne
  push Not at hne
  have : bdry univ = 0 := by
    rw [← ae_iff.1 (h.mono fun x hx ↦ hx)]
    exact congrArg bdry (by ext x; simp [hne x])
  exact bdry_ne_zero (Measure.measure_univ_eq_zero.1 this)

omit [ProperSpace k] in
/-- A point fixed by the image of all of `Γ` contradicts `NonElem`. -/
lemma NonElem.not_fixed {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}
    (hne : NonElem Γ a) {y : OnePoint k} (hy : ∀ γ ∈ Γ, a γ • y = y) : False := by
  obtain ⟨γ, hγ, h⟩ := hne Γ le_rfl (by simp) y
  exact h (hy γ hγ)

/-- **Essential non-constancy.** -/
theorem ae_ne_of_equivariant {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (hΓ : IsDoublyErgodic Γ)
    {a : SL(2, ℝ) → GL (Fin 2) k} (hne : NonElem Γ a) {ψ : OnePoint ℝ → OnePoint k}
    (hψ : Measurable ψ) (heq : Equivariant Γ a ψ) :
    ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 ≠ ψ q.2 := by
  set E : Set (OnePoint ℝ × OnePoint ℝ) := {q | ψ q.1 = ψ q.2}
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (hψ.comp measurable_fst) (hψ.comp measurable_snd)
  have hinv : ∀ γ ∈ Γ, dact γ ⁻¹' E =ᵐ[bdry.prod bdry] E := by
    intro γ hγ
    filter_upwards [ae_fst (heq γ hγ), ae_snd (heq γ hγ)] with q h1 h2
    change (ψ (γ • q.1) = ψ (γ • q.2)) = (ψ q.1 = ψ q.2)
    rw [h1, h2, smul_left_cancel_iff]
  rcases hΓ.null_or_conull hE hinv with h0 | h0
  · exact measure_eq_zero_iff_ae_notMem.1 h0
  · exfalso
    have hae : ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 = ψ q.2 :=
      (measure_eq_zero_iff_ae_notMem.1 h0).mono fun q hq ↦ by simpa [E] using hq
    obtain ⟨x₁, hx₁⟩ := exists_of_ae (Measure.ae_ae_of_ae_prod hae)
    simp only at hx₁
    refine hne.not_fixed (y := ψ x₁) fun γ hγ ↦ ?_
    obtain ⟨x, h1, h2, h3⟩ := exists_of_ae ((heq γ hγ).and (hx₁.and (ae_smul hx₁ γ)))
    rw [h2, ← h1, ← h3, h2]

end OrbicurveCores.M2
