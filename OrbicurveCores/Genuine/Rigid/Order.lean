/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.LiftAlg
import OrbicurveCores.S1.LocalForm

/-!
# U2c5: algebraic orders are analytic orders

Let `S` be a Dedekind domain, `w` a maximal ideal and `g ∈ w ∖ w²` a uniformiser.

* `exists_mul_eq_pow_mul`: if `b ∈ w^k ∖ w^(k+1)`, then `s b = g^k c` with `s, c ∉ w`;
* `hasLocalForm_of_mem_pow`: for a holomorphic family of points `τ` of a `ℂ`-algebra `S` with
  `w = ker (τ z)` and `τ g` a local coordinate at `z`, the function `τ b` has a local normal form of
  order `k` at `z`;
* `ramificationIdx_eq_of_mem_pow`: for `X ↦ h`, the ramification index of `w` over `X - h(w)` is
  that `k`.
-/

open Polynomial Set Filter
open scoped Topology

namespace OrbicurveCores.Rigid

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

section Analytic

variable {S : Type*} [CommRing S] [Algebra ℂ S] {U : Set ℂ} {τ : ℂ → (S →ₐ[ℂ] ℂ)}

/-- Elements of `w²` have vanishing derivative. -/
lemma deriv_eq_zero_of_mem_sq (hU : IsOpen U) (hτ : ∀ a, DifferentiableOn ℂ (fun y ↦ τ y a) U)
    {z : ℂ} (hz : z ∈ U) {b : S} (hb : b ∈ (RingHom.ker (τ z)) ^ 2) :
    deriv (fun y ↦ τ y b) z = 0 := by
  have hd : ∀ a, DifferentiableAt ℂ (fun y ↦ τ y a) z := fun a ↦
    (hτ a).differentiableAt (hU.mem_nhds hz)
  rw [pow_two] at hb
  refine Submodule.mul_induction_on hb (fun a ha c hc ↦ ?_) fun x x' hx hx' ↦ ?_
  · have : (fun y ↦ τ y (a * c)) = fun y ↦ τ y a * τ y c := funext fun y ↦ map_mul _ _ _
    rw [this, deriv_fun_mul (hd a) (hd c), RingHom.mem_ker.mp ha, RingHom.mem_ker.mp hc]
    ring
  · have : (fun y ↦ τ y (x + x')) = fun y ↦ τ y x + τ y x' := funext fun y ↦ map_add _ _ _
    rw [this, deriv_fun_add (hd x) (hd x'), hx, hx', add_zero]

/-- **Algebraic order = analytic order.** If `τ g` is a local coordinate at `z` vanishing at `z`
and `b ∈ w^k ∖ w^(k+1)` (`w = ker (τ z)`, `k ≥ 1`), then `τ b` has a local normal form of order
`k` at `z`. -/
theorem hasLocalForm_of_mem_pow [IsDedekindDomain S] (hU : IsOpen U)
    (hτ : ∀ a, DifferentiableOn ℂ (fun y ↦ τ y a) U) {z : ℂ} (hz : z ∈ U) {g : S}
    (hg0 : τ z g = 0) (hgd : deriv (fun y ↦ τ y g) z ≠ 0) {b : S} {k : ℕ} (hk : k ≠ 0)
    (hb : b ∈ (RingHom.ker (τ z)) ^ k) (hb' : b ∉ (RingHom.ker (τ z)) ^ (k + 1)) :
    S1.HasLocalForm (fun y ↦ τ y b) z k := by
  haveI := ker_isMaximal (τ z)
  set w := RingHom.ker (τ z)
  have hg : g ∈ w := RingHom.mem_ker.mpr hg0
  have hg2 : g ∉ w ^ 2 := fun h ↦ hgd (deriv_eq_zero_of_mem_sq hU hτ hz h)
  obtain ⟨s, c, hs, hc, hsc⟩ := exists_mul_eq_pow_mul hg hg2 hb hb'
  have han : ∀ a, AnalyticAt ℂ (fun y ↦ τ y a) z := fun a ↦
    (hτ a).analyticAt (hU.mem_nhds hz)
  have hs0 : τ z s ≠ 0 := fun h ↦ hs (RingHom.mem_ker.mpr h)
  have hc0 : τ z c ≠ 0 := fun h ↦ hc (RingHom.mem_ker.mpr h)
  have hb0 : τ z b = 0 := by
    have : w ^ k ≤ w := Ideal.pow_le_self hk
    exact RingHom.mem_ker.mp (this hb)
  refine S1.hasLocalForm_of_eq_pow_mul hk (han g) hg0 hgd ((han c).div (han s) hs0)
    (div_ne_zero hc0 hs0) ?_
  filter_upwards [(han s).continuousAt.eventually_ne hs0] with y hy
  change τ y b = τ z b + τ y g ^ k * (τ y c / τ y s)
  rw [hb0, zero_add, mul_div_assoc', eq_div_iff hy, ← map_pow, ← map_mul, ← map_mul, mul_comm,
    hsc]

end Analytic

section Ramification

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra ℂ S]

/-- The ramification index of `w` over `X - t₀` along `X ↦ h` is the order of `h - t₀`. -/
theorem ramificationIdx_eq_of_mem_pow (f : ℂ[X] →ₐ[ℂ] S) (hf : Function.Injective f)
    {w : Ideal S} [w.IsMaximal] {t₀ : ℂ} (hw : w.comap f = Ideal.span {X - C t₀}) {k : ℕ}
    (hb : f X - algebraMap ℂ S t₀ ∈ w ^ k) (hb' : f X - algebraMap ℂ S t₀ ∉ w ^ (k + 1)) :
    (letI := f.toRingHom.toAlgebra; w.ramificationIdx ℂ[X]) = k := by
  letI := f.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree ℂ[X] S := (Module.isTorsionFree_iff_algebraMap_injective).mpr hf
  haveI : w.LiesOver (Ideal.span {X - C t₀}) := ⟨hw.symm⟩
  have hp : Ideal.span {X - C t₀} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero t₀
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp]
  have hmap : Ideal.map (algebraMap ℂ[X] S) (Ideal.span {X - C t₀}) =
      Ideal.span {f X - algebraMap ℂ S t₀} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change f (X - C t₀) = _
    rw [map_sub, ← algebraMap_eq (R := ℂ), AlgHom.commutes]
  refine Ideal.ramificationIdx'_spec ?_ ?_
  · rw [hmap, Ideal.span_singleton_le_iff_mem]; exact hb
  · rw [hmap, Ideal.span_singleton_le_iff_mem]; exact hb'

end Ramification

end OrbicurveCores.Rigid
