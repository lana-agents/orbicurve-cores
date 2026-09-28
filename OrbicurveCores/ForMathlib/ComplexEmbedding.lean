/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# Non-rational reals are moved by some embedding `ℝ → ℂ`

We show that for a real number `x` which is not rational, there exists a ring homomorphism
`σ : ℝ →+* ℂ` with `σ x ≠ x`.

The main tool is `IsAlgClosed.exists_ringEquiv_comp_eq`: two injective ring homomorphisms
from a countable domain `R` into uncountable algebraically closed fields of the same
cardinality differ by a ring isomorphism of the targets.
-/

open Cardinal Polynomial

universe u

namespace IsAlgClosed

/-- Let `R` be a countable domain and `f : R → K`, `g : R → L` injective ring homomorphisms
into uncountable algebraically closed fields of the same cardinality. Then there exists a
ring isomorphism `e : K ≃+* L` with `e ∘ f = g`. -/
theorem exists_ringEquiv_comp_eq {R K L : Type u} [CommRing R] [IsDomain R] [Field K]
    [Field L] [IsAlgClosed K] [IsAlgClosed L] (f : R →+* K) (g : R →+* L)
    (hf : Function.Injective f) (hg : Function.Injective g) (hR : #R ≤ ℵ₀) (hK : ℵ₀ < #K)
    (hKL : #K = #L) : ∃ e : K ≃+* L, (e : K →+* L).comp f = g := by
  letI : Algebra R K := f.toAlgebra
  letI : Algebra R L := g.toAlgebra
  have : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective R K).mpr hf
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hg
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis R K
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis R L
  have hst : #s = #t := by
    rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ hs hR hK,
      ← cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt' _ ht hR (hKL ▸ hK), hKL]
  obtain ⟨e⟩ := Cardinal.eq.mp hst
  letI := isAlgClosure_of_transcendence_basis _ hs
  letI := isAlgClosure_of_transcendence_basis _ ht
  let eadj := hs.1.aevalEquiv.symm.trans ((MvPolynomial.renameEquiv R e).trans ht.1.aevalEquiv)
  refine ⟨IsAlgClosure.equivOfEquiv K L eadj.toRingEquiv, RingHom.ext fun r => ?_⟩
  change _ = algebraMap R L r
  simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
  change IsAlgClosure.equivOfEquiv K L eadj.toRingEquiv (algebraMap R K r) = _
  rw [IsScalarTower.algebraMap_apply R (Algebra.adjoin R (Set.range ((↑) : s → K))) K,
    IsAlgClosure.equivOfEquiv_algebraMap, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply]

end IsAlgClosed

/-- A complex number `z` which is not rational has a conjugate over `ℚ` different from `z`:
there is `y ≠ z` such that `z` and `y` satisfy the same rational polynomial equations. -/
theorem Complex.exists_ne_forall_aeval_eq_zero_iff {z : ℂ}
    (hz : z ∉ Set.range ((↑) : ℚ → ℂ)) :
    ∃ y : ℂ, y ≠ z ∧ ∀ p : ℚ[X], aeval z p = 0 ↔ aeval y p = 0 := by
  by_cases halg : IsAlgebraic ℚ z
  · have hint := halg.isIntegral
    have hdeg : 2 ≤ (minpoly ℚ z).natDegree := by
      rw [minpoly.two_le_natDegree_iff hint]
      simpa using hz
    have hcard : 1 < Fintype.card ((minpoly ℚ z).rootSet ℂ) := by
      rw [card_rootSet_eq_natDegree (minpoly.irreducible hint).separable
        (IsAlgClosed.splits _)]
      omega
    have hzmem : z ∈ (minpoly ℚ z).rootSet ℂ :=
      (mem_rootSet_of_ne (minpoly.ne_zero hint)).mpr (minpoly.aeval ℚ z)
    obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hcard ⟨z, hzmem⟩
    have hy0 : aeval y (minpoly ℚ z) = 0 := (mem_rootSet.mp hy).2
    have hmin : minpoly ℚ y = minpoly ℚ z :=
      (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) hy0
        (minpoly.monic hint)).symm
    refine ⟨y, fun h => hne (Subtype.ext h), fun p => ?_⟩
    rw [← minpoly.dvd_iff, ← minpoly.dvd_iff, hmin]
  · refine ⟨z + 1, by simp, fun p => ?_⟩
    have ht : Transcendental ℚ (z + 1) := fun h =>
      halg (by simpa using h.add (isAlgebraic_algebraMap (-1 : ℚ)))
    rw [(injective_iff_map_eq_zero' _).mp (transcendental_iff_injective.mp halg),
      (injective_iff_map_eq_zero' _).mp (transcendental_iff_injective.mp ht)]

/-- A real number which is not rational is moved by some ring homomorphism `ℝ →+* ℂ`. -/
theorem exists_ringHom_real_complex_ne {x : ℝ} (hx : x ∉ Set.range ((↑) : ℚ → ℝ)) :
    ∃ σ : ℝ →+* ℂ, σ x ≠ (x : ℂ) := by
  have hz : (x : ℂ) ∉ Set.range ((↑) : ℚ → ℂ) := by
    rintro ⟨q, hq⟩
    exact hx ⟨q, by exact_mod_cast hq⟩
  obtain ⟨y, hne, hy⟩ := Complex.exists_ne_forall_aeval_eq_zero_iff hz
  let I : Ideal ℚ[X] := RingHom.ker (aeval (x : ℂ)).toRingHom
  have : I.IsPrime := RingHom.ker_isPrime _
  have hI : ∀ p ∈ I, (aeval y).toRingHom p = 0 := fun p hp => (hy p).mp hp
  let f : ℚ[X] ⧸ I →+* ℂ := Ideal.Quotient.lift I (aeval (x : ℂ)).toRingHom fun _ h => h
  let g : ℚ[X] ⧸ I →+* ℂ := Ideal.Quotient.lift I (aeval y).toRingHom hI
  have hf : Function.Injective f := RingHom.lift_injective_of_ker_le_ideal _ _ le_rfl
  have hg : Function.Injective g :=
    RingHom.lift_injective_of_ker_le_ideal _ _ fun p hp => (hy p).mpr hp
  have hR : #(ℚ[X] ⧸ I) ≤ ℵ₀ :=
    (Cardinal.mk_le_of_surjective Ideal.Quotient.mk_surjective).trans
      (cardinalMk_le_max.trans (by simp))
  have hC : ℵ₀ < #ℂ := Cardinal.mk_complex ▸ Cardinal.aleph0_lt_continuum
  obtain ⟨e, he⟩ := IsAlgClosed.exists_ringEquiv_comp_eq f g hf hg hR hC rfl
  refine ⟨(e : ℂ →+* ℂ).comp Complex.ofRealHom, ?_⟩
  have h := RingHom.congr_fun he (Ideal.Quotient.mk I X)
  simp only [RingHom.coe_comp, Function.comp_apply, f, g, Ideal.Quotient.lift_mk] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X] at h
  simpa [h] using hne
