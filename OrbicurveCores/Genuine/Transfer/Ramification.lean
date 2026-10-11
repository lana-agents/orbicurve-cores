/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Transfer.LocalGen
import OrbicurveCores.Genuine.Transfer.LocalGeneric
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# T2d: ramification indices under base change

Let `f : A → B` be an injective integral map of Dedekind domains of finite type over a field `k`
of characteristic `0`, and `K / k` a field extension. For a maximal ideal `W` of `K ⊗ B`, with
`w = W ∩ B` and `V = W ∩ (K ⊗ A)`:

* if `w ≠ 0`, uniformizers `π` of `A` at `v = w ∩ A` and `ϖ` of `B` at `w` generate `V` and `W`
  locally, and `f(π) = u ϖ ^ e(w | v)` with `u` a unit at `w` (`exists_mul_eq_mul_pow`);
* if `w = 0`, a single element of `V` generates both `V` and `W` locally (generic case).

These elementwise statements pass to the components of `K ⊗ A` and `K ⊗ B`.
-/

open IsLocalRing TensorProduct

namespace OrbicurveCores.Transfer

section Dedekind

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]

/-- In a Dedekind extension, the image of a local uniformizer `π` of `A` at `v = w ∩ A` is a
unit times `ϖ ^ e(w | v)`, `ϖ` a local uniformizer of `B` at `w`, elementwise. -/
lemma exists_mul_eq_mul_pow (f : A →+* B) (hf : Function.Injective f) (w : Ideal B) [w.IsPrime]
    (hw : w ≠ ⊥) {π : A} (hπ0 : π ≠ 0) (hπ : π ∈ w.comap f)
    (hπloc : ∀ a ∈ w.comap f, ∃ s ∉ w.comap f, ∃ y, s * a = π * y) {ϖ : B} (hϖ : ϖ ∈ w)
    (hϖloc : ∀ x ∈ w, ∃ s ∉ w, ∃ y, s * x = ϖ * y) :
    ∃ s ∉ w, ∃ b ∉ w, s * f π = b * ϖ ^ (letI := f.toAlgebra; w.ramificationIdx A) := by
  letI := f.toAlgebra
  set S := Localization.AtPrime w
  have : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hw S
  have hmax : maximalIdeal S = Ideal.span {algebraMap B S ϖ} :=
    maximalIdeal_eq_span_of_forall w hϖ hϖloc
  have hv : (w.under A).map (algebraMap A S) = Ideal.span {algebraMap B S (f π)} := by
    have := map_eq_span_of_forall_isUnit (algebraMap A S) (I := w.under A) hπ fun a ha ↦ by
      obtain ⟨s, hs, y, hsy⟩ := hπloc a ha
      refine ⟨s, ?_, y, hsy⟩
      rw [IsScalarTower.algebraMap_apply A B S]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff S w _).mpr hs
    rw [this, IsScalarTower.algebraMap_apply A B S]
    rfl
  have hne : algebraMap B S (f π) ≠ 0 := by
    rw [Ne, IsLocalization.to_map_eq_zero_iff S w.primeCompl_le_nonZeroDivisors]
    exact fun h ↦ hπ0 (hf (h.trans (map_zero f).symm))
  obtain ⟨n, u, hu⟩ := exists_unit_mul_pow_of_maximalIdeal_eq hmax hne
  have hspan : Ideal.span {algebraMap B S (f π)} = Ideal.span {algebraMap B S ϖ ^ n} := by
    rw [hu, Ideal.span_singleton_mul_left_unit u.isUnit]
  have he : w.ramificationIdx A = n :=
    ramificationIdx_eq_of_map_eq_span_pow w hmax n (hv.trans hspan)
  rw [he]
  obtain ⟨⟨b, ⟨s, hs⟩⟩, hbs⟩ := IsLocalization.mk'_surjective w.primeCompl (u : S)
  dsimp only at hbs
  have hb : b ∉ w := by
    intro hb
    have : (u : S) ∈ maximalIdeal S := by
      rw [← hbs, IsLocalization.AtPrime.mk'_mem_maximal_iff S w]; exact hb
    exact (maximalIdeal.isMaximal S).ne_top (Ideal.eq_top_of_isUnit_mem _ this u.isUnit)
  have hsp := IsLocalization.mk'_spec' S b (⟨s, hs⟩ : w.primeCompl)
  have heq : algebraMap B S (s * f π) = algebraMap B S (b * ϖ ^ n) := by
    rw [map_mul, map_mul, hu, map_pow, ← hbs]
    linear_combination (algebraMap B S ϖ ^ n) * hsp
  obtain ⟨⟨t, ht⟩, htx⟩ := (IsLocalization.eq_iff_exists w.primeCompl S).mp heq
  dsimp only at htx
  refine ⟨t * s, fun h ↦ (‹w.IsPrime›.mem_or_mem h).elim ht hs, t * b,
    fun h ↦ (‹w.IsPrime›.mem_or_mem h).elim ht hb, ?_⟩
  calc t * s * f π = t * (s * f π) := by ring
    _ = t * (b * ϖ ^ n) := htx
    _ = t * b * ϖ ^ n := by ring

end Dedekind

end OrbicurveCores.Transfer
