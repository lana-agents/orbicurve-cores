/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Local generators, elementwise

For a prime `P` of a ring `R`, an ideal `I` and `π ∈ I`, the statement `I R_P = π R_P` is
equivalent to the elementwise statement `∀ x ∈ I, ∃ s ∉ P, ∃ y, s x = π y`. The elementwise form
passes to quotients and along ring maps, which is how local generators are transported between
`K ⊗ A`, `K ⊗ B` and their components.

`ramificationIdx_eq_of_map_eq_span_pow`: if `R_P` is a DVR with uniformizer `ϖ` and
`(P ∩ D) R_P = ϖ ^ e R_P`, then `e(P | D) = e`.
-/

open IsLocalRing

namespace OrbicurveCores.Transfer

/-- Elementwise generation up to units implies generation of the image ideal. -/
lemma map_eq_span_of_forall_isUnit {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {I : Ideal R} {π : R} (hπ : π ∈ I) (h : ∀ x ∈ I, ∃ s, IsUnit (φ s) ∧ ∃ y, s * x = π * y) :
    I.map φ = Ideal.span {φ π} := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hu, y, hsy⟩ := h x hx
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul, hsy, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hπ

variable {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime]

/-- Elementwise local generation implies generation after localization. -/
lemma map_eq_span_of_forall {I : Ideal R} {π : R} (hπ : π ∈ I)
    (h : ∀ x ∈ I, ∃ s ∉ P, ∃ y, s * x = π * y) :
    I.map (algebraMap R (Localization.AtPrime P)) =
      Ideal.span {algebraMap R (Localization.AtPrime P) π} := by
  set S := Localization.AtPrime P
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    obtain ⟨s, hs, y, hsy⟩ := h x hx
    have hu : IsUnit (algebraMap R S s) := (IsLocalization.AtPrime.isUnit_to_map_iff S P s).mpr hs
    rw [Ideal.mem_comap, ← Ideal.unit_mul_mem_iff_mem _ hu, ← map_mul, hsy, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_map_of_mem _ hπ

/-- Generation after localization implies elementwise local generation. -/
lemma forall_of_map_eq_span {I : Ideal R} {π : R}
    (h : I.map (algebraMap R (Localization.AtPrime P)) =
      Ideal.span {algebraMap R (Localization.AtPrime P) π}) :
    ∀ x ∈ I, ∃ s ∉ P, ∃ y, s * x = π * y := by
  set S := Localization.AtPrime P
  intro x hx
  have : algebraMap R S x ∈ Ideal.span {algebraMap R S π} := h ▸ Ideal.mem_map_of_mem _ hx
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp this
  obtain ⟨⟨y, ⟨s, hs⟩⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl c
  dsimp only at hc
  have hsp := IsLocalization.mk'_spec' S y (⟨s, hs⟩ : P.primeCompl)
  have : algebraMap R S (s * x) = algebraMap R S (π * y) := by
    rw [map_mul, map_mul]
    linear_combination (-(algebraMap R S s)) * hc + (algebraMap R S π) * hsp
  obtain ⟨⟨t, ht⟩, htx⟩ := (IsLocalization.eq_iff_exists P.primeCompl S).mp this
  refine ⟨t * s, fun hts ↦ (‹P.IsPrime›.mem_or_mem hts).elim ht hs, t * y, ?_⟩
  dsimp only at htx
  calc t * s * x = t * (s * x) := by ring
    _ = t * (π * y) := htx
    _ = π * (t * y) := by ring

/-- Elementwise version for the maximal ideal. -/
lemma maximalIdeal_eq_span_of_forall {π : R} (hπ : π ∈ P)
    (h : ∀ x ∈ P, ∃ s ∉ P, ∃ y, s * x = π * y) :
    maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap R (Localization.AtPrime P) π} := by
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  exact map_eq_span_of_forall P hπ h

/-- The ramification index from local generators: if `R_P` is a DVR with uniformizer `ϖ` and
`(P ∩ D) R_P = ϖ ^ e R_P`, then `e(P | D) = e`. -/
lemma ramificationIdx_eq_of_map_eq_span_pow {D : Type*} [CommRing D] [Algebra D R]
    [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)]
    {ϖ : R} (hmax : maximalIdeal (Localization.AtPrime P) =
      Ideal.span {algebraMap R (Localization.AtPrime P) ϖ}) (e : ℕ)
    (hv : (P.under D).map (algebraMap D (Localization.AtPrime P)) =
      Ideal.span {algebraMap R (Localization.AtPrime P) ϖ ^ e}) :
    P.ramificationIdx D = e := by
  rw [Ideal.ramificationIdx_def, hv, ← Ideal.span_singleton_pow, ← hmax,
    IsDiscreteValuationRing.length_quotient_pow_maximalIdeal, ENat.toNat_coe]

end OrbicurveCores.Transfer
