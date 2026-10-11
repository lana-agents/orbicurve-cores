/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Filtration

/-!
# Orders of elements at a maximal ideal of a Dedekind domain

Let `S` be a Dedekind domain, `w` a maximal ideal and `g ∈ w ∖ w²` a uniformiser.

* `exists_mul_eq_pow_mul`: if `b ∈ w^k ∖ w^(k+1)`, then `s b = g^k c` with `s, c ∉ w`;
* `exists_order`: a nonzero `b ∈ w` lies in `w^k ∖ w^(k+1)` for some `k ≥ 1`.
-/

namespace OrbicurveCores.Abhyankar

section Algebra

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

/-- **Factoring out a uniformiser.** -/
theorem exists_mul_eq_pow_mul {w : Ideal S} [hw : w.IsMaximal] {g : S} (hg : g ∈ w)
    (hg2 : g ∉ w ^ 2) {b : S} {k : ℕ} (hb : b ∈ w ^ k) (hb' : b ∉ w ^ (k + 1)) :
    ∃ s c : S, s ∉ w ∧ c ∉ w ∧ s * b = g ^ k * c := by
  have hw0 : w ≠ ⊥ := by
    rintro rfl
    exact hg2 (by simpa using hg)
  obtain ⟨J, hJ⟩ : w ∣ Ideal.span {g} := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem
    w).mpr hg)
  obtain ⟨s₁, hs₁J, hs₁w⟩ : ∃ s₁ ∈ J, s₁ ∉ w := by
    by_contra h
    push Not at h
    apply hg2
    have : Ideal.span {g} ≤ w ^ 2 := by rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self g)
  have key1 : ∀ c ∈ w, ∃ c', s₁ * c = g * c' := fun c hc ↦ by
    have : c * s₁ ∈ Ideal.span {g} := by rw [hJ]; exact Ideal.mul_mem_mul hc hs₁J
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp this
    exact ⟨a, by rw [mul_comm s₁, ← ha, mul_comm]⟩
  have key2 : ∀ (m : ℕ) (c : S), g * c ∈ w ^ (m + 1) → c ∈ w ^ m := by
    intro m c hc
    have h1 : w * (J * Ideal.span {c}) ≤ w * w ^ m := by
      rw [← mul_assoc, ← hJ, Ideal.span_singleton_mul_span_singleton, ← pow_succ']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hc
    have h2 : J * Ideal.span {c} ≤ w ^ m := by
      rw [← Ideal.dvd_iff_le] at h1 ⊢
      exact (mul_dvd_mul_iff_left hw0).mp h1
    have h3 : s₁ * c ∈ w ^ m := h2 (Ideal.mul_mem_mul hs₁J (Ideal.mem_span_singleton_self c))
    exact (Ideal.IsPrime.mul_mem_pow w h3).resolve_left hs₁w
  have hind : ∀ j ≤ k, ∃ c, s₁ ^ j * b = g ^ j * c ∧ c ∈ w ^ (k - j) := by
    intro j
    induction j with
    | zero => intro _; exact ⟨b, by simp, by simpa using hb⟩
    | succ j ih =>
      intro hj
      obtain ⟨c, hc, hcw⟩ := ih (by omega)
      have hcw1 : c ∈ w := by
        have : w ^ (k - j) ≤ w := Ideal.pow_le_self (by omega)
        exact this hcw
      obtain ⟨c', hc'⟩ := key1 c hcw1
      refine ⟨c', by rw [pow_succ, mul_assoc, mul_comm s₁ b, ← mul_assoc, hc, mul_assoc,
        mul_comm c, hc', pow_succ, mul_assoc], key2 _ c' ?_⟩
      rw [← hc', show k - (j + 1) + 1 = k - j by omega]
      exact Ideal.mul_mem_left _ _ hcw
  obtain ⟨c, hc, -⟩ := hind k le_rfl
  refine ⟨s₁ ^ k, c, fun h ↦ hs₁w (hw.isPrime.mem_of_pow_mem k h), fun hcw ↦ hb' ?_, hc⟩
  have : s₁ ^ k * b ∈ w ^ (k + 1) := by
    rw [hc, pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hg k) hcw
  exact (Ideal.IsPrime.mul_mem_pow w this).resolve_left
    fun h ↦ hs₁w (hw.isPrime.mem_of_pow_mem k h)

/-- **Order of an element**: a nonzero `b ∈ w` lies in `w^k ∖ w^(k+1)` for some `k ≥ 1`
(Krull's intersection theorem). -/
theorem exists_order {w : Ideal S} [hw : w.IsMaximal] {b : S} (hb0 : b ≠ 0) (hb : b ∈ w) :
    ∃ k, k ≠ 0 ∧ b ∈ w ^ k ∧ b ∉ w ^ (k + 1) := by
  classical
  have hex : ∃ j, b ∉ w ^ j := by
    by_contra h
    push Not at h
    have : b ∈ ⨅ j : ℕ, w ^ j := Submodule.mem_iInf _ |>.mpr h
    rw [Ideal.iInf_pow_eq_bot_of_isDomain w hw.ne_top] at this
    exact hb0 this
  set m := Nat.find hex
  have hm : b ∉ w ^ m := Nat.find_spec hex
  have hm0 : m ≠ 0 := fun h ↦ hm (by rw [h, pow_zero, Ideal.one_eq_top]; trivial)
  have hm1 : m ≠ 1 := fun h ↦ hm (by rw [h, pow_one]; exact hb)
  refine ⟨m - 1, by omega, ?_, by rwa [Nat.sub_add_cancel (by omega)]⟩
  exact not_not.mp (Nat.find_min hex (by omega : m - 1 < m))

end Algebra

end OrbicurveCores.Abhyankar
