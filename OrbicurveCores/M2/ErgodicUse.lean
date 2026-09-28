/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.BoundaryMeasure

/-!
# M2: consequences of double ergodicity

For a countable `Γ ≤ SL(2, ℝ)` acting doubly ergodically on the boundary:

* `IsDoublyErgodic.null_or_conull`: almost invariant measurable subsets of `B × B` are null or
  conull;
* `IsDoublyErgodic.ae_const`: almost invariant measurable maps from `B × B` to a countably
  separated space are almost everywhere constant;
* the same on `B` itself (`null_or_conull_single`, `ae_const_single`).
-/

open MeasureTheory Filter Set
open scoped MatrixGroups

namespace OrbicurveCores.M2

/-- The diagonal action on pairs of boundary points. -/
noncomputable def dact (γ : SL(2, ℝ)) (p : OnePoint ℝ × OnePoint ℝ) : OnePoint ℝ × OnePoint ℝ :=
  (γ • p.1, γ • p.2)

instance : SFinite bdry := by unfold bdry; infer_instance

lemma quasiMeasurePreserving_dact (γ : SL(2, ℝ)) :
    Measure.QuasiMeasurePreserving (dact γ) (bdry.prod bdry) (bdry.prod bdry) := by
  have hq := quasiMeasurePreserving_smul γ
  refine ⟨hq.measurable.prodMap hq.measurable, ?_⟩
  rw [show dact γ = Prod.map (fun x ↦ γ • x) (fun x ↦ γ • x) from rfl,
    ← Measure.map_prod_map _ _ hq.measurable hq.measurable]
  exact hq.absolutelyContinuous.prod hq.absolutelyContinuous

lemma bdry_ne_zero : bdry ≠ 0 := by
  intro h
  have : bdry univ = 0 := by rw [h]; rfl
  rw [bdry, Measure.map_apply OnePoint.continuous_coe.measurable MeasurableSet.univ,
    preimage_univ, Real.volume_univ] at this
  exact ENNReal.top_ne_zero this

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ]

/-- Almost invariant sets are null or conull. -/
theorem IsDoublyErgodic.null_or_conull (h : IsDoublyErgodic Γ)
    {E : Set (OnePoint ℝ × OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ γ ∈ Γ, dact γ ⁻¹' E =ᵐ[bdry.prod bdry] E) :
    (bdry.prod bdry) E = 0 ∨ (bdry.prod bdry) Eᶜ = 0 := by
  set E' : Set (OnePoint ℝ × OnePoint ℝ) := ⋂ γ : Γ, dact γ ⁻¹' E
  have hmeas : MeasurableSet E' :=
    MeasurableSet.iInter fun γ ↦ (quasiMeasurePreserving_dact γ).measurable hE
  have hinv' : ∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹' E' = E' := by
    intro γ hγ
    ext p
    simp only [E', mem_preimage, mem_iInter, dact]
    constructor
    · intro hp δ
      have := hp ⟨δ * γ⁻¹, mul_mem δ.2 (inv_mem hγ)⟩
      simpa [mul_smul] using this
    · intro hp δ
      have := hp ⟨δ * γ, mul_mem δ.2 hγ⟩
      simpa [mul_smul] using this
  have hae : E' =ᵐ[bdry.prod bdry] E := by
    have h1 : E' ⊆ E := by
      intro p hp
      have := mem_iInter.1 hp ⟨1, one_mem _⟩
      simpa [dact] using this
    refine (ae_eq_set.2 ⟨?_, ?_⟩)
    · rw [sdiff_eq_empty.2 h1, measure_empty]
    · have : E \ E' ⊆ ⋃ γ : Γ, (E \ dact γ ⁻¹' E) := by
        intro p ⟨hpE, hpE'⟩
        simp only [E', mem_iInter, not_forall] at hpE'
        obtain ⟨γ, hγ⟩ := hpE'
        exact mem_iUnion.2 ⟨γ, hpE, hγ⟩
      refine measure_mono_null this (measure_iUnion_null fun γ ↦ ?_)
      have := (ae_eq_set.1 (hinv γ γ.2)).2
      exact this
  rcases h E' hmeas hinv' with h0 | h0
  · left; rwa [← measure_congr hae]
  · right; rwa [← measure_congr hae.compl]

/-- Almost invariant maps into a countably separated space are almost everywhere constant. -/
theorem IsDoublyErgodic.ae_const (h : IsDoublyErgodic Γ) {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace.CountablySeparated Z] [Nonempty Z] {f : OnePoint ℝ × OnePoint ℝ → Z}
    (hf : Measurable f) (hinv : ∀ γ ∈ Γ, f ∘ dact γ =ᵐ[bdry.prod bdry] f) :
    ∃ c : Z, ∀ᵐ p ∂(bdry.prod bdry), f p = c := by
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae (bdry.prod bdry))
    (f := f) MeasurableSet fun U hU ↦ by
      have hE : MeasurableSet (f ⁻¹' U) := hf hU
      have hinvE : ∀ γ ∈ Γ, dact γ ⁻¹' (f ⁻¹' U) =ᵐ[bdry.prod bdry] f ⁻¹' U := by
        intro γ hγ
        filter_upwards [hinv γ hγ] with p hp
        change (f (dact γ p) ∈ U) = (f p ∈ U)
        rw [show f (dact γ p) = f p from hp]
      rcases h.null_or_conull hE hinvE with h0 | h0
      · right; exact measure_eq_zero_iff_ae_notMem.1 h0
      · left
        exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp ↦ by simpa using hp
  exact ⟨c, hc⟩

/-- Single ergodicity: almost invariant subsets of `B` are null or conull. -/
theorem IsDoublyErgodic.null_or_conull_single (h : IsDoublyErgodic Γ)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ γ ∈ Γ, (fun x ↦ γ • x) ⁻¹' E =ᵐ[bdry] E) : bdry E = 0 ∨ bdry Eᶜ = 0 := by
  have hE2 : MeasurableSet (E ×ˢ (univ : Set (OnePoint ℝ))) := hE.prod MeasurableSet.univ
  have hinv2 : ∀ γ ∈ Γ, dact γ ⁻¹' (E ×ˢ univ) =ᵐ[bdry.prod bdry] E ×ˢ univ := by
    intro γ hγ
    have : dact γ ⁻¹' (E ×ˢ univ) = ((fun x ↦ γ • x) ⁻¹' E) ×ˢ univ := by
      ext p; simp [dact]
    rw [this]
    exact Measure.set_prod_ae_eq (hinv γ hγ) (ae_eq_refl _)
  have hne : bdry univ ≠ 0 := fun h0 ↦ bdry_ne_zero (Measure.measure_univ_eq_zero.1 h0)
  rcases h.null_or_conull hE2 hinv2 with h0 | h0
  · left
    rw [Measure.prod_prod] at h0
    exact (mul_eq_zero.1 h0).resolve_right hne
  · right
    rw [compl_prod_eq_union, compl_univ, prod_empty, union_empty,
      Measure.prod_prod] at h0
    exact (mul_eq_zero.1 h0).resolve_right hne

/-- Single ergodicity for maps into a countably separated space. -/
theorem IsDoublyErgodic.ae_const_single (h : IsDoublyErgodic Γ) {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace.CountablySeparated Z] [Nonempty Z] {f : OnePoint ℝ → Z}
    (hf : Measurable f) (hinv : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, f (γ • x) = f x) :
    ∃ c : Z, ∀ᵐ x ∂bdry, f x = c := by
  obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_forall_separating (l := ae bdry)
    (f := f) MeasurableSet fun U hU ↦ by
      have hE : MeasurableSet (f ⁻¹' U) := hf hU
      have hinvE : ∀ γ ∈ Γ, (fun x ↦ γ • x) ⁻¹' (f ⁻¹' U) =ᵐ[bdry] f ⁻¹' U := by
        intro γ hγ
        filter_upwards [hinv γ hγ] with p hp
        change (f (γ • p) ∈ U) = (f p ∈ U)
        rw [hp]
      rcases h.null_or_conull_single hE hinvE with h0 | h0
      · right; exact measure_eq_zero_iff_ae_notMem.1 h0
      · left
        exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp ↦ by simpa using hp
  exact ⟨c, hc⟩

end OrbicurveCores.M2
