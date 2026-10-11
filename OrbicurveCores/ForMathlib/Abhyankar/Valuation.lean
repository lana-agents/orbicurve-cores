/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.ForMathlib.Abhyankar.Order
import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Abhyankar's lemma: orders of elements at primes of Dedekind domains

* `pow_mul_notMem_pow_succ`: for a uniformiser `g ∈ P ∖ P²` and `c ∉ P`, `g^m c ∉ P^(m+1)`;
* `pow_mem_pow_notMem`: if `b ∈ P^k ∖ P^(k+1)` then `b^n ∈ P^(nk) ∖ P^(nk+1)`;
* `exists_uniformizer`: `P ∖ P²` is nonempty for a nonzero maximal `P`;
* `algebraMap_mem_pow_ramificationIdx`: a uniformiser `t ∈ y ∖ y²` of the base has order
  `e(w | y)` at every `w` over `y`.
-/

namespace OrbicurveCores.Abhyankar

section

variable {S : Type*} [CommRing S] [IsDedekindDomain S]

lemma pow_mul_notMem_pow_succ {P : Ideal S} [hP : P.IsMaximal] {g : S} (hg : g ∈ P)
    (hg2 : g ∉ P ^ 2) {c : S} (hc : c ∉ P) (m : ℕ) : g ^ m * c ∉ P ^ (m + 1) := by
  have hP0 : P ≠ ⊥ := by rintro rfl; exact hg2 (by simpa using hg)
  obtain ⟨J, hJ⟩ : P ∣ Ideal.span {g} := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem P).mpr hg)
  have hJP : ¬ J ≤ P := fun h ↦ hg2 (by
    have : Ideal.span {g} ≤ P ^ 2 := by rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self g))
  intro hmem
  have h1 : P ^ m * (J ^ m * Ideal.span {c}) ≤ P ^ m * P := by
    rw [← mul_assoc, ← mul_pow, ← hJ, Ideal.span_singleton_pow,
      Ideal.span_singleton_mul_span_singleton, ← pow_succ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have h2 : J ^ m * Ideal.span {c} ≤ P := by
    rw [← Ideal.dvd_iff_le] at h1 ⊢
    exact (mul_dvd_mul_iff_left (pow_ne_zero m hP0)).mp h1
  rcases hP.isPrime.mul_le.mp h2 with h | h
  · exact hJP (hP.isPrime.le_of_pow_le h)
  · exact hc ((Ideal.span_singleton_le_iff_mem P).mp h)

/-- A nonzero maximal ideal of a Dedekind domain contains an element not in its square. -/
lemma exists_uniformizer {P : Ideal S} [hP : P.IsMaximal] (hP0 : P ≠ ⊥) :
    ∃ g ∈ P, g ∉ P ^ 2 := by
  by_contra h
  push Not at h
  have hle : P ≤ P ^ 2 := h
  have h2 : P * P = P * ⊤ := by
    rw [Ideal.mul_top]
    exact le_antisymm Ideal.mul_le_left (by simpa [pow_two] using hle)
  exact hP.ne_top (mul_left_cancel₀ hP0 h2)

/-- Orders are multiplicative: `b ∈ P^k ∖ P^(k+1)` gives `b^n ∈ P^(nk) ∖ P^(nk+1)`. -/
lemma pow_mem_pow_notMem {P : Ideal S} [hP : P.IsMaximal] (hP0 : P ≠ ⊥) {b : S} {k : ℕ}
    (hb : b ∈ P ^ k) (hb' : b ∉ P ^ (k + 1)) (n : ℕ) :
    b ^ n ∈ P ^ (n * k) ∧ b ^ n ∉ P ^ (n * k + 1) := by
  refine ⟨by rw [mul_comm, pow_mul]; exact Ideal.pow_mem_pow hb n, fun h ↦ ?_⟩
  obtain ⟨g, hg, hg2⟩ := exists_uniformizer hP0
  obtain ⟨s, c, hs, hc, hsc⟩ := exists_mul_eq_pow_mul hg hg2 hb hb'
  have h1 : (s ^ n) * b ^ n ∈ P ^ (n * k + 1) := (P ^ (n * k + 1)).mul_mem_left _ h
  rw [← mul_pow, hsc, mul_pow, ← pow_mul, mul_comm k n] at h1
  exact pow_mul_notMem_pow_succ hg hg2 (fun h ↦ hc (hP.isPrime.mem_of_pow_mem n h)) (n * k) h1

end

section

variable {B C : Type*} [CommRing B] [CommRing C] [IsDedekindDomain B] [IsDedekindDomain C]
  [Algebra B C] [Module.IsTorsionFree B C]

/-- **A uniformiser of the base has order `e(w | y)` at `w`.** -/
theorem algebraMap_mem_pow_ramificationIdx {y : Ideal B} [y.IsMaximal] (hy0 : y ≠ ⊥)
    {t : B} (ht : t ∈ y) (ht2 : t ∉ y ^ 2) {w : Ideal C} [hw : w.IsMaximal] [w.LiesOver y] :
    algebraMap B C t ∈ w ^ w.ramificationIdx B ∧
      algebraMap B C t ∉ w ^ (w.ramificationIdx B + 1) := by
  have hmap0 : Ideal.map (algebraMap B C) y ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hy0
  have hw0 : w ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hy0 w
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx y w hy0]
  set e := Ideal.ramificationIdx' y w
  refine ⟨Ideal.le_pow_ramificationIdx' (Ideal.mem_map_of_mem _ ht), fun hmem ↦ ?_⟩
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hmap0 w
  rw [← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 hw.isPrime hw0]
    at hfac
  obtain ⟨J, hJ⟩ : y ∣ Ideal.span {t} := Ideal.dvd_iff_le.mpr
    ((Ideal.span_singleton_le_iff_mem y).mpr ht)
  have hJy : ¬ J ≤ y := fun h ↦ ht2 (by
    have : Ideal.span {t} ≤ y ^ 2 := by rw [hJ, pow_two]; exact Ideal.mul_mono_right h
    exact this (Ideal.mem_span_singleton_self t))
  have h1 : w ^ e * (Q * Ideal.map (algebraMap B C) J) ≤ w ^ e * w := by
    rw [← mul_assoc, ← hfac, ← Ideal.map_mul, ← hJ, Ideal.map_span, Set.image_singleton,
      ← pow_succ]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
  have h2 : Q * Ideal.map (algebraMap B C) J ≤ w := by
    rw [← Ideal.dvd_iff_le] at h1 ⊢
    exact (mul_dvd_mul_iff_left (pow_ne_zero e hw0)).mp h1
  rcases hw.isPrime.mul_le.mp h2 with h | h
  · exact hw.ne_top (by rw [← hQ]; exact (sup_eq_left.mpr h).symm)
  · apply hJy
    rw [Ideal.map_le_iff_le_comap] at h
    have hy' : y = w.under B := Ideal.LiesOver.over
    rw [hy']
    exact h

end

end OrbicurveCores.Abhyankar
