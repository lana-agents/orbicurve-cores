/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Rigid.LiftAlg
import OrbicurveCores.ForMathlib.Abhyankar.Order
import OrbicurveCores.S1.LocalForm

/-!
# U2c5: algebraic orders are analytic orders

Let `S` be a Dedekind domain, `w` a maximal ideal and `g ∈ w ∖ w²` a uniformiser.

* `exists_mul_eq_pow_mul` (`ForMathlib/Abhyankar/Order.lean`): if `b ∈ w^k ∖ w^(k+1)`, then
  `s b = g^k c` with `s, c ∉ w`;
* `hasLocalForm_of_mem_pow`: for a holomorphic family of points `τ` of a `ℂ`-algebra `S` with
  `w = ker (τ z)` and `τ g` a local coordinate at `z`, the function `τ b` has a local normal form of
  order `k` at `z`;
* `ramificationIdx_eq_of_mem_pow`: for `X ↦ h`, the ramification index of `w` over `X - h(w)` is
  that `k`.
-/

open Polynomial Set Filter
open scoped Topology

open OrbicurveCores.Abhyankar

namespace OrbicurveCores.Rigid

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
