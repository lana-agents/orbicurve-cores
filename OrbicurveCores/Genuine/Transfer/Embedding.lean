/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Complex.Cardinality

/-!
# T1a: countable fields of characteristic `0` embed into `ℂ`

A transcendence basis of a countable field `k` of characteristic `0` over `ℚ` is countable, while
`ℂ` has an uncountable one; mapping the former injectively into the latter embeds the purely
transcendental subfield `ℚ(s)` (in fact the polynomial subring) into `ℂ`, and the algebraic
extension `k / ℚ[s]` then embeds into the algebraically closed `ℂ` (`IsAlgClosed.lift`).
-/

open Cardinal

namespace OrbicurveCores.Transfer

/-- **A countable field of characteristic `0` embeds into `ℂ`.** -/
theorem nonempty_ringHom_complex (k : Type*) [Field k] [CharZero k] [Countable k] :
    Nonempty (k →+* ℂ) := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ k
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ ℂ
  -- `t` is uncountable
  have hct : #ℚ ≤ ℵ₀ := (Cardinal.mk_le_aleph0)
  have hC : ℵ₀ < #ℂ := by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum
  have htc : #ℂ = #t :=
    IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hct hC
  have hsc : #s ≤ ℵ₀ := Cardinal.mk_le_aleph0
  obtain ⟨g⟩ : Nonempty (s ↪ t) := by
    apply Cardinal.lift_mk_le'.mp
    have h1 : Cardinal.lift.{0} #s ≤ ℵ₀ := by
      rw [← Cardinal.lift_aleph0.{0}]; exact Cardinal.lift_le.mpr hsc
    have h2 : ℵ₀ ≤ Cardinal.lift #t := by
      rw [← Cardinal.lift_aleph0]; exact Cardinal.lift_le.mpr (htc ▸ hC).le
    exact h1.trans h2
  -- `ℚ[s] → ℂ`
  have hind : AlgebraicIndependent ℚ ((↑) ∘ g : s → ℂ) := ht.1.comp g g.injective
  let φ₀ : Algebra.adjoin ℚ (Set.range ((↑) : s → k)) →ₐ[ℚ] ℂ :=
    (MvPolynomial.aeval ((↑) ∘ g : s → ℂ)).comp hs.1.aevalEquiv.symm.toAlgHom
  have hφ₀ : Function.Injective φ₀ := by
    have : Function.Injective (MvPolynomial.aeval ((↑) ∘ g : s → ℂ)) := hind
    exact this.comp hs.1.aevalEquiv.symm.injective
  letI : Algebra (Algebra.adjoin ℚ (Set.range ((↑) : s → k))) ℂ := φ₀.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree (Algebra.adjoin ℚ (Set.range ((↑) : s → k))) ℂ :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr hφ₀
  haveI : Module.IsTorsionFree (Algebra.adjoin ℚ (Set.range ((↑) : s → k))) k :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr Subtype.val_injective
  haveI := hs.isAlgebraic
  exact ⟨(IsAlgClosed.lift (M := ℂ) (R := Algebra.adjoin ℚ (Set.range ((↑) : s → k)))
    (S := k)).toRingHom⟩

end OrbicurveCores.Transfer
