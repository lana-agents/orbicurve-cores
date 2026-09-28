/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Defs

/-!
# Local normal forms

Elementary facts about `HasLocalForm`:

* `exists_analyticAt_pow_eq`: a function analytic and nonvanishing at `x₀` has an analytic `n`-th
  root near `x₀`;
* `hasLocalForm_one`: a nonzero derivative gives a local normal form of order `1`;
* `hasLocalForm_of_eq_pow_mul`: `f = f x₀ + P ^ n · φ` with `P x₀ = 0`, `P' x₀ ≠ 0`, `φ x₀ ≠ 0`;
* `HasLocalForm.comp`: precomposition with a local biholomorphism;
* `HasLocalForm.analyticAt`: `f` is analytic at the point.
-/

open Complex Metric Set Filter Topology

namespace OrbicurveCores.S1

/-- A function analytic and nonvanishing at `x₀` has an analytic `n`-th root near `x₀`. -/
lemma exists_analyticAt_pow_eq {φ : ℂ → ℂ} {x₀ : ℂ} (hφ : AnalyticAt ℂ φ x₀) (h0 : φ x₀ ≠ 0)
    {n : ℕ} (hn : n ≠ 0) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ x₀ ∧ ψ x₀ ≠ 0 ∧ ∀ᶠ x in 𝓝 x₀, ψ x ^ n = φ x := by
  set c := φ x₀
  set c₀ : ℂ := c ^ ((n : ℂ)⁻¹)
  have hc₀ : c₀ ^ n = c := Complex.cpow_nat_inv_pow c hn
  have hc₀0 : c₀ ≠ 0 := by
    intro h; rw [h, zero_pow hn] at hc₀; exact h0 hc₀.symm
  have hq : AnalyticAt ℂ (fun x ↦ φ x / c) x₀ := hφ.div_const
  have hq1 : (fun x ↦ φ x / c) x₀ ∈ slitPlane := by
    simp only [c, div_self h0]; exact one_mem_slitPlane
  refine ⟨fun x ↦ c₀ * exp (log (φ x / c) / n), ?_, ?_, ?_⟩
  · exact analyticAt_const.mul ((hq.clog hq1).div_const.cexp)
  · exact mul_ne_zero hc₀0 (exp_ne_zero _)
  · filter_upwards [hφ.continuousAt.eventually_ne h0] with x hx
    rw [mul_pow, ← exp_nat_mul, hc₀, mul_div_cancel₀ _ (by exact_mod_cast hn),
      exp_log (div_ne_zero hx h0), mul_div_cancel₀ _ h0]

/-- A local normal form gives analyticity. -/
lemma HasLocalForm.analyticAt {f : ℂ → ℂ} {z : ℂ} {n : ℕ} (h : HasLocalForm f z n) :
    AnalyticAt ℂ f z := by
  obtain ⟨g, hg, -, -, hf⟩ := h
  exact (analyticAt_const.add (hg.pow n)).congr (hf.mono fun _ h ↦ h.symm)

/-- A nonzero derivative gives a local normal form of order `1`. -/
lemma hasLocalForm_one {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (hd : deriv f z ≠ 0) :
    HasLocalForm f z 1 := by
  refine ⟨fun x ↦ f x - f z, hf.sub analyticAt_const, sub_self _, ?_, ?_⟩
  · rwa [deriv_sub_const]
  · exact Eventually.of_forall fun x ↦ by ring

/-- `f = f x₀ + P ^ n · φ` near `x₀`, with `P` a local coordinate at `x₀` and `φ x₀ ≠ 0`, is a
local normal form of order `n`. -/
lemma hasLocalForm_of_eq_pow_mul {f P φ : ℂ → ℂ} {x₀ : ℂ} {n : ℕ} (hn : n ≠ 0)
    (hP : AnalyticAt ℂ P x₀) (hP0 : P x₀ = 0) (hP' : deriv P x₀ ≠ 0)
    (hφ : AnalyticAt ℂ φ x₀) (hφ0 : φ x₀ ≠ 0)
    (hf : ∀ᶠ x in 𝓝 x₀, f x = f x₀ + P x ^ n * φ x) : HasLocalForm f x₀ n := by
  obtain ⟨ψ, hψ, hψ0, hψn⟩ := exists_analyticAt_pow_eq hφ hφ0 hn
  refine ⟨fun x ↦ P x * ψ x, hP.mul hψ, by simp [hP0], ?_, ?_⟩
  · have hd := hP.differentiableAt.hasDerivAt.mul hψ.differentiableAt.hasDerivAt
    rw [show (fun x ↦ P x * ψ x) = P * ψ from rfl, hd.deriv, hP0, zero_mul, add_zero]
    exact mul_ne_zero hP' hψ0
  · filter_upwards [hf, hψn] with x hx hx'
    rw [hx, mul_pow, hx']

/-- Precomposition with a local biholomorphism preserves local normal forms. -/
lemma HasLocalForm.comp {f q : ℂ → ℂ} {u : ℂ} {n : ℕ} (hf : HasLocalForm f (q u) n)
    (hq : AnalyticAt ℂ q u) (hq' : deriv q u ≠ 0) : HasLocalForm (f ∘ q) u n := by
  obtain ⟨g, hg, hg0, hg', hfg⟩ := hf
  refine ⟨g ∘ q, hg.comp hq, hg0, ?_, ?_⟩
  · rw [deriv_comp u hg.differentiableAt hq.differentiableAt]
    exact mul_ne_zero hg' hq'
  · exact hq.continuousAt.eventually hfg

end OrbicurveCores.S1
