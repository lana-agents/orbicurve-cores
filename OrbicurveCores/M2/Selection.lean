/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Mathlib

/-!
# Measurable selection of atoms

* `exists_measurable_dirac_selection`: if on a measurable set `S` a finite kernel `ρ` is a
  nonzero multiple of a Dirac mass `δ_{z(x)}`, then `z` can be chosen measurable.
* `exists_measurable_heavy_selection`: if on `S` a Markov kernel has an atom of mass `> 1/2`,
  that atom depends measurably on the point.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

variable {X Z : Type*} [MeasurableSpace X] [TopologicalSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  [Nonempty Z]

/-- **Dirac selection.** -/
theorem exists_measurable_dirac_selection (ρ : Kernel X Z) {S : Set X} (hS : MeasurableSet S)
    (hρ : ∀ x ∈ S, ∃ z, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ρ x = c • Measure.dirac z) :
    ∃ f : X → Z, Measurable f ∧ ∀ x ∈ S, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ρ x = c • Measure.dirac (f x) := by
  classical
  let f : X → Z := fun x ↦ if h : x ∈ S then (hρ x h).choose else Classical.arbitrary Z
  have hf : ∀ x (h : x ∈ S), ∃ c : ℝ≥0∞, c ≠ 0 ∧ ρ x = c • Measure.dirac (f x) := by
    intro x h
    simp only [f, dif_pos h]
    exact (hρ x h).choose_spec
  refine ⟨f, measurable_of_isOpen fun U hU ↦ ?_, hf⟩
  have e : f ⁻¹' U = (S ∩ {x | ρ x U ≠ 0}) ∪ (Sᶜ ∩ {_x | Classical.arbitrary Z ∈ U}) := by
    ext x
    by_cases h : x ∈ S
    · obtain ⟨c, hc, hx⟩ := hf x h
      simp only [mem_preimage, mem_union, mem_inter_iff, h, true_and, mem_compl_iff,
        not_true_eq_false, false_and, or_false, mem_setOf_eq, hx, Measure.smul_apply,
        smul_eq_mul, Measure.dirac_apply' _ hU.measurableSet]
      by_cases hU' : f x ∈ U <;> simp [hU', hc]
    · simp [f, h]
  rw [e]
  refine (hS.inter ?_).union (hS.compl.inter (MeasurableSet.const _))
  exact (Kernel.measurable_coe ρ hU.measurableSet) (measurableSet_singleton 0).compl

omit [TopologicalSpace Z] [BorelSpace Z] [Nonempty Z] in
/-- If a probability measure has an atom of mass `> 1/2`, then that atom lies in a set `U`
iff `U` has measure `> 1/2`. -/
lemma mem_iff_of_heavy [MeasurableSingletonClass Z] {μ : Measure Z} [IsProbabilityMeasure μ]
    {z : Z} (hz : 1 / 2 < μ {z}) (U : Set Z) : z ∈ U ↔ 1 / 2 < μ U := by
  constructor
  · intro h; exact hz.trans_le (measure_mono (singleton_subset_iff.2 h))
  · intro h
    by_contra hzU
    have h1 : μ U + μ {z} ≤ 1 := by
      rw [← measure_union (disjoint_singleton_right.2 hzU) (measurableSet_singleton z)]
      exact prob_le_one
    have : (1 : ℝ≥0∞) / 2 + 1 / 2 < 1 :=
      (ENNReal.add_lt_add h hz).trans_le h1
    rw [ENNReal.add_halves] at this
    exact lt_irrefl _ this

/-- **Heavy-atom selection.** -/
theorem exists_measurable_heavy_selection [MeasurableSingletonClass Z] (κ : Kernel X Z) [IsMarkovKernel κ] {S : Set X}
    (hS : MeasurableSet S) (hκ : ∀ x ∈ S, ∃ z, 1 / 2 < κ x {z}) :
    ∃ f : X → Z, Measurable f ∧ ∀ x ∈ S, 1 / 2 < κ x {f x} := by
  classical
  let f : X → Z := fun x ↦ if h : x ∈ S then (hκ x h).choose else Classical.arbitrary Z
  have hf : ∀ x (h : x ∈ S), 1 / 2 < κ x {f x} := by
    intro x h; simp only [f, dif_pos h]; exact (hκ x h).choose_spec
  refine ⟨f, measurable_of_isOpen fun U hU ↦ ?_, hf⟩
  have e : f ⁻¹' U = (S ∩ {x | 1 / 2 < κ x U}) ∪ (Sᶜ ∩ {_x | Classical.arbitrary Z ∈ U}) := by
    ext x
    by_cases h : x ∈ S
    · simp only [mem_preimage, mem_union, mem_inter_iff, h, true_and, mem_compl_iff,
        not_true_eq_false, false_and, or_false, mem_setOf_eq]
      exact mem_iff_of_heavy (hf x h) U
    · simp [f, h]
  rw [e]
  exact (hS.inter (measurableSet_lt measurable_const
    (Kernel.measurable_coe κ hU.measurableSet))).union (hS.compl.inter (MeasurableSet.const _))
