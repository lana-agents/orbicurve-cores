/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Setup
import OrbicurveCores.M2.FurstenbergLimit

/-!
# M2, part F: the Furstenberg boundary map

For a lattice `Γ ≤ SL(2, ℝ)` with a good fundamental set (`GoodLattice`) acting on a compact
metrizable space `Y` through `α`, we construct a measurable `ψ : OnePoint ℝ → Prob(Y)` which is
`Γ`-equivariant almost everywhere (`GoodLattice.exists_boundaryMap`). See `Blueprint.md`, §2.3b,
part F.

1. `phiM z`: a `Γ`-equivariant measurable family of probability measures on `Y`, indexed by
   `z ∈ ℍ`: the average of the Dirac masses at `α γ y₀` over the finitely many `γ ∈ Γ` with
   `γ⁻¹ z ∈ F`.
2. `theta n g`: the average of `phiM (g a_s n_u • I)` over the left Følner set
   `(s, u) ∈ [0, n + 1] × [-(n + 1), n + 1]` of `P° = {a_s n_u}`. It is exactly `Γ`-equivariant
   and asymptotically right-`P`-invariant, uniformly in `g`.
3. The abstract limit theorem `exists_tailWeights_ae_tendsto` gives tail convex combinations
   converging at `σ x = !![x, -1; 1, 0]` for almost every `x ∈ ℝ`. The convergence set is exactly
   left-`Γ`- and right-`P`-invariant, and the limit descends to `ℝ ⊆ OnePoint ℝ` via `σ`.

No Haar measure on `SL(2, ℝ)` is needed, and the lattice property enters only through the
fundamental set.
-/

open MeasureTheory Filter Topology Matrix UpperHalfPlane OnePoint BoundedContinuousFunction Set
open scoped MatrixGroups ENNReal NNReal ProbabilityTheory

namespace OrbicurveCores.M2

/-! ### Matrices -/

/-- `a_s n_u = [[e^s, e^s u], [0, e^{-s}]]`. -/
noncomputable def an (s u : ℝ) : SL(2, ℝ) :=
  ⟨!![Real.exp s, Real.exp s * u; 0, Real.exp (-s)], by
    simp [det_fin_two, ← Real.exp_add]⟩

lemma an_mul_an_of_u_eq_zero (s₀ s u : ℝ) : an s₀ 0 * an s u = an (s + s₀) u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [an, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_add, Real.exp_neg] <;> ring

lemma an_mul_an_of_s_eq_zero (u₀ s u : ℝ) :
    an 0 u₀ * an s u = an s (u + u₀ * Real.exp (-s) ^ 2) := by
  have h : Real.exp s * Real.exp (-s) = 1 := by rw [← Real.exp_add]; simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [an, Matrix.mul_apply, Fin.sum_univ_two]
  linear_combination (-(u₀ * Real.exp (-s))) * h

lemma continuous_an : Continuous fun q : ℝ × ℝ ↦ an q.1 q.2 := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun q : ℝ × ℝ ↦ !![Real.exp q.1, Real.exp q.1 * q.2; 0, Real.exp (-q.1)]
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [of_apply, cons_val', empty_val', cons_val_fin_one] <;> fun_prop

/-- The section `σ x = [[x, -1], [1, 0]]` of `SL(2, ℝ) → OnePoint ℝ`, `σ x • ∞ = x`. -/
def sec (x : ℝ) : SL(2, ℝ) :=
  ⟨!![x, -1; 1, 0], by simp [det_fin_two]⟩

lemma continuous_sec : Continuous sec := by
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : ℝ ↦ !![x, -1; 1, (0 : ℝ)]
  refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp only [of_apply, cons_val', empty_val', cons_val_fin_one] <;> fun_prop

/-- The upper triangular matrix `[[t, v], [0, t⁻¹]]`. -/
noncomputable def ptri (t v : ℝ) (ht : t ≠ 0) : SL(2, ℝ) :=
  ⟨!![t, v; 0, t⁻¹], by simp [det_fin_two, ht]⟩

lemma mul_sec (γ : SL(2, ℝ)) (x : ℝ) (ht : γ 1 0 * x + γ 1 1 ≠ 0) :
    γ * sec x = sec ((γ 0 0 * x + γ 0 1) / (γ 1 0 * x + γ 1 1)) *
      ptri (γ 1 0 * x + γ 1 1) (-γ 1 0) ht := by
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe
    rwa [det_fin_two] at this
  have ht' : x * γ 1 0 + γ 1 1 ≠ 0 := by rwa [mul_comm]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sec, ptri, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp
    linear_combination (-1 : ℝ) * hdet

lemma ptri_of_pos {t : ℝ} (v : ℝ) (ht : 0 < t) :
    ptri t v ht.ne' = an (Real.log t) 0 * an 0 (v / t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ptri, an, Matrix.mul_apply, Fin.sum_univ_two, Real.exp_log ht, Real.exp_neg]
  field_simp

lemma ptri_of_neg {t : ℝ} (v : ℝ) (ht : t < 0) :
    ptri t v ht.ne = -(an (Real.log (-t)) 0 * an 0 (v / t)) := by
  have he : Real.exp (Real.log t) = -t := by
    rw [← Real.log_neg_eq_log]; exact Real.exp_log (neg_pos.2 ht)
  have ht0 := ht.ne
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ptri, an, he, Real.exp_neg]
  field_simp

/-! ### Averages over intervals -/

/-- The uniform probability measure on `[a, b]`. -/
noncomputable def unif (a b : ℝ) : Measure ℝ :=
  (ENNReal.ofReal (b - a))⁻¹ • volume.restrict (Icc a b)

lemma isProbabilityMeasure_unif {a b : ℝ} (hab : a < b) : IsProbabilityMeasure (unif a b) := by
  constructor
  rw [unif, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Icc, smul_eq_mul, ENNReal.inv_mul_cancel (by simpa using hab) (by simp)]

lemma integral_unif {a b : ℝ} (hab : a ≤ b) (h : ℝ → ℝ) :
    ∫ t, h t ∂unif a b = (b - a)⁻¹ * ∫ t in a..b, h t := by
  rw [unif, integral_smul_measure, intervalIntegral.integral_of_le hab,
    integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
    smul_eq_mul]

lemma ae_unif_mem {a b : ℝ} : ∀ᵐ t ∂unif a b, t ∈ Icc a b :=
  Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _

/-- Translating the integrand of a uniform average by `c` changes it by at most
`2 M |c| / (b - a)`. -/
lemma abs_integral_unif_comp_add_sub_le {a b : ℝ} (hab : a < b) {h : ℝ → ℝ} (hm : Measurable h)
    {M : ℝ} (hM : ∀ t, |h t| ≤ M) (c : ℝ) :
    |∫ t, h (t + c) ∂unif a b - ∫ t, h t ∂unif a b| ≤ 2 * M * |c| / (b - a) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hint : ∀ x y, IntervalIntegrable h volume x y := fun x y ↦
    (intervalIntegrable_const (c := M)).mono_fun hm.aestronglyMeasurable
      (ae_of_all _ fun t ↦ by simpa [Real.norm_eq_abs, abs_of_nonneg hM0] using hM t)
  have hb : ∀ x, |∫ t in x..x + c, h t| ≤ M * |c| := fun x ↦ by
    simpa using intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + c)
      (f := h) (C := M) (fun t _ ↦ by simpa [Real.norm_eq_abs] using hM t)
  rw [integral_unif hab.le, integral_unif hab.le, ← mul_sub,
    intervalIntegral.integral_comp_add_right,
    intervalIntegral.integral_interval_sub_interval_comm' (hint _ _) (hint _ _) (hint _ _),
    abs_mul, abs_inv, abs_of_pos (sub_pos.2 hab), inv_mul_eq_div]
  gcongr
  calc |(∫ t in b..b + c, h t) - ∫ t in a..a + c, h t|
      ≤ |∫ t in b..b + c, h t| + |∫ t in a..a + c, h t| := abs_sub _ _
    _ ≤ M * |c| + M * |c| := add_le_add (hb b) (hb a)
    _ = 2 * M * |c| := by ring

/-! ### The equivariant family `phiM` on `ℍ` -/

section Phi

variable (Γ : Subgroup SL(2, ℝ)) (F : Set ℍ)

/-- The number of `γ ∈ Γ` with `γ⁻¹ z ∈ F`. -/
noncomputable def cnt (z : ℍ) : ℝ≥0∞ :=
  ∑' γ : Γ, F.indicator 1 ((γ : SL(2, ℝ))⁻¹ • z)

/-- The weight of `γ` at `z`: `1 / cnt z` if `γ⁻¹ z ∈ F`, else `0`. -/
noncomputable def wt (γ : Γ) (z : ℍ) : ℝ≥0∞ :=
  F.indicator 1 ((γ : SL(2, ℝ))⁻¹ • z) / cnt Γ F z

lemma indicator_le_one (z : ℍ) : F.indicator (1 : ℍ → ℝ≥0∞) z ≤ 1 := by
  unfold Set.indicator; split_ifs <;> simp

lemma cnt_smul (γ₀ : Γ) (z : ℍ) : cnt Γ F ((γ₀ : SL(2, ℝ)) • z) = cnt Γ F z := by
  unfold cnt
  rw [← (Equiv.mulLeft γ₀).tsum_eq]
  congr 1
  funext γ
  simp [mul_smul]

lemma wt_smul (γ₀ γ : Γ) (z : ℍ) : wt Γ F (γ₀ * γ) ((γ₀ : SL(2, ℝ)) • z) = wt Γ F γ z := by
  simp [wt, cnt_smul, mul_smul]

variable {Γ F}

lemma cnt_ne_zero (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F) (z : ℍ) : cnt Γ F z ≠ 0 := by
  obtain ⟨γ, hγ, h⟩ := hcov z
  refine ne_of_gt (lt_of_lt_of_le ?_ (ENNReal.le_tsum (⟨γ⁻¹, inv_mem hγ⟩ : Γ)))
  simp [h]

lemma cnt_ne_top (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (z : ℍ) :
    cnt Γ F z ≠ ⊤ := by
  classical
  have hS : {γ : Γ | (γ : SL(2, ℝ))⁻¹ • z ∈ F}.Finite := by
    refine ((hfin z).preimage (f := fun γ : Γ ↦ (γ : SL(2, ℝ))⁻¹) ?_).subset ?_
    · intro a _ b _ hab
      exact Subtype.ext (inv_injective hab)
    · intro γ hγ
      exact ⟨inv_mem γ.2, hγ⟩
  rw [cnt, tsum_eq_sum (s := hS.toFinset) (fun γ hγ ↦ by
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hγ
    simp [hγ])]
  exact ENNReal.sum_ne_top.2 fun γ _ ↦ ne_top_of_le_ne_top ENNReal.one_ne_top
    (indicator_le_one F _)

lemma tsum_wt (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
    (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (z : ℍ) :
    ∑' γ : Γ, wt Γ F γ z = 1 := by
  simp only [wt, div_eq_mul_inv]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_inv_cancel (cnt_ne_zero hcov z) (cnt_ne_top hfin z)

variable (Γ F) {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

/-- The `Γ`-equivariant family of measures `z ↦ ∑_γ wt γ z • δ_{α γ y₀}`. -/
noncomputable def phiM (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (z : ℍ) : Measure Y :=
  Measure.sum fun γ : Γ ↦ wt Γ F γ z • Measure.dirac (α γ y₀)

variable {Γ F}

lemma phiM_apply (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (z : ℍ) {A : Set Y} (hA : MeasurableSet A) :
    phiM Γ F α y₀ z A = ∑' γ : Γ, wt Γ F γ z * Measure.dirac (α γ y₀) A := by
  simp [phiM, Measure.sum_apply _ hA]

lemma isProbabilityMeasure_phiM (hcov : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F)
    (hfin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite) (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y)
    (z : ℍ) : IsProbabilityMeasure (phiM Γ F α y₀ z) := by
  constructor
  rw [phiM_apply α y₀ z MeasurableSet.univ]
  simpa using tsum_wt hcov hfin z

lemma phiM_smul [BorelSpace Y] (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (γ₀ : Γ) (z : ℍ) :
    phiM Γ F α y₀ ((γ₀ : SL(2, ℝ)) • z) = (phiM Γ F α y₀ z).map (α γ₀) := by
  ext A hA
  rw [Measure.map_apply (α γ₀).continuous.measurable hA, phiM_apply α y₀ _ hA,
    phiM_apply α y₀ _ ((α γ₀).continuous.measurable hA), ← (Equiv.mulLeft γ₀).tsum_eq]
  congr 1
  funext γ
  rw [Equiv.coe_mulLeft, wt_smul, map_mul, Homeomorph.mul_apply,
    Measure.dirac_apply' _ hA, Measure.dirac_apply' _ ((α γ₀).continuous.measurable hA)]
  rfl

variable [Countable Γ]

lemma measurable_indicator_smul (hF : MeasurableSet F) (g : SL(2, ℝ)) :
    Measurable fun z : ℍ ↦ F.indicator (1 : ℍ → ℝ≥0∞) (g • z) :=
  (measurable_one.indicator hF).comp (Fuchsian.measurable_smul_SL g)

lemma measurable_cnt (hF : MeasurableSet F) : Measurable (cnt Γ F) :=
  Measurable.tsum fun _ ↦ measurable_indicator_smul hF _

lemma measurable_wt (hF : MeasurableSet F) (γ : Γ) : Measurable (wt Γ F γ) :=
  (measurable_indicator_smul hF _).div (measurable_cnt hF)

lemma measurable_phiM (hF : MeasurableSet F) (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) :
    Measurable (phiM Γ F α y₀) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA ↦ ?_
  simp_rw [phiM_apply α y₀ _ hA]
  exact Measurable.tsum fun γ ↦ (measurable_wt hF γ).mul_const _

end Phi

/-! ### Averaging over Følner sets of `P` -/

/-- A measurable fundamental set of finite multiplicity. -/
structure FundSet (Γ : Subgroup SL(2, ℝ)) where
  /-- The set. -/
  F : Set ℍ
  meas : MeasurableSet F
  cover : ∀ z : ℍ, ∃ γ ∈ Γ, γ • z ∈ F
  fin : ∀ z : ℍ, {γ : SL(2, ℝ) | γ ∈ Γ ∧ γ • z ∈ F}.Finite

instance (n : ℕ) : IsProbabilityMeasure (unif 0 (n + 1)) :=
  isProbabilityMeasure_unif (by positivity)

instance (n : ℕ) : IsProbabilityMeasure (unif (-(n + 1)) (n + 1)) :=
  isProbabilityMeasure_unif (by linarith)

/-- The normalised Haar measure of the left Følner set `[0, n + 1] × [-(n + 1), n + 1]` of `P°`,
in the coordinates `(s, u) ↦ a_s n_u`. -/
noncomputable def box (n : ℕ) : Measure (ℝ × ℝ) :=
  (unif 0 (n + 1)).prod (unif (-(n + 1)) (n + 1))

instance (n : ℕ) : IsProbabilityMeasure (box n) := by
  unfold box; infer_instance

/-- The point `g a_s n_u • I` of `ℍ`. -/
noncomputable def orbitPt (g : SL(2, ℝ)) (q : ℝ × ℝ) : ℍ := (g * an q.1 q.2) • I

lemma continuous_orbitPt : Continuous fun p : SL(2, ℝ) × (ℝ × ℝ) ↦ orbitPt p.1 p.2 :=
  (continuous_fst.mul (continuous_an.comp continuous_snd)).smul continuous_const

lemma measurable_orbitPt (g : SL(2, ℝ)) : Measurable (orbitPt g) :=
  (continuous_orbitPt.comp (Continuous.prodMk_right g)).measurable

lemma neg_smul_upperHalfPlane (g : SL(2, ℝ)) (z : ℍ) : (-g) • z = g • z := by
  change SpecialLinearGroup.mapGL ℝ (-g) • z = SpecialLinearGroup.mapGL ℝ g • z
  rw [show SpecialLinearGroup.mapGL ℝ (-g) = -SpecialLinearGroup.mapGL ℝ g by ext; simp,
    UpperHalfPlane.neg_smul]

lemma orbitPt_neg (g : SL(2, ℝ)) (q : ℝ × ℝ) : orbitPt (-g) q = orbitPt g q := by
  simp [orbitPt, neg_mul, neg_smul_upperHalfPlane]

section Theta

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y)

/-- `phiM` as a Markov kernel. -/
noncomputable def phiK : ProbabilityTheory.Kernel ℍ Y :=
  ⟨phiM Γ D.F α y₀, measurable_phiM D.meas α y₀⟩

instance : ProbabilityTheory.IsMarkovKernel (phiK D α y₀) :=
  ⟨fun z ↦ isProbabilityMeasure_phiM D.cover D.fin α y₀ z⟩

lemma phiK_apply (z : ℍ) : phiK D α y₀ z = phiM Γ D.F α y₀ z := rfl

/-- The average of `phiM (g a_s n_u • I)` over the Følner set `box n`. -/
noncomputable def thetaM (n : ℕ) (g : SL(2, ℝ)) : Measure Y :=
  (phiK D α y₀).comap (orbitPt g) (measurable_orbitPt g) ∘ₘ box n

/-- `thetaM` as a probability measure. -/
noncomputable def theta (n : ℕ) (g : SL(2, ℝ)) : ProbabilityMeasure Y :=
  ⟨thetaM D α y₀ n g, by unfold thetaM; infer_instance⟩

lemma theta_apply (n : ℕ) (g : SL(2, ℝ)) {A : Set Y} (hA : MeasurableSet A) :
    (theta D α y₀ n g : Measure Y) A = ∫⁻ q, phiM Γ D.F α y₀ (orbitPt g q) A ∂box n :=
  Measure.bind_apply hA (ProbabilityTheory.Kernel.aemeasurable _)

lemma integral_theta [OpensMeasurableSpace Y] (n : ℕ) (g : SL(2, ℝ)) (f : Y →ᵇ ℝ) :
    ∫ y, f y ∂(theta D α y₀ n g : Measure Y) =
      ∫ q, ∫ y, f y ∂(phiM Γ D.F α y₀ (orbitPt g q)) ∂box n := by
  change ∫ y, f y ∂thetaM D α y₀ n g = _
  rw [thetaM, Measure.comp_eq_comp_const_apply, ProbabilityTheory.Kernel.integral_comp]
  · simp [ProbabilityTheory.Kernel.comap_apply, phiK_apply]
  · rw [← Measure.comp_eq_comp_const_apply]
    exact f.integrable _

lemma theta_mul [BorelSpace Y] (n : ℕ) (γ₀ : Γ) (g : SL(2, ℝ)) :
    theta D α y₀ n ((γ₀ : SL(2, ℝ)) * g) =
      (theta D α y₀ n g).map (α γ₀).continuous.measurable.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply (α γ₀).continuous.measurable hA,
    theta_apply _ _ _ _ _ hA, theta_apply _ _ _ _ _ ((α γ₀).continuous.measurable hA)]
  congr 1
  funext q
  rw [show orbitPt ((γ₀ : SL(2, ℝ)) * g) q = (γ₀ : SL(2, ℝ)) • orbitPt g q by
    simp [orbitPt, mul_assoc, mul_smul], phiM_smul,
    Measure.map_apply (α γ₀).continuous.measurable hA]

lemma theta_neg (n : ℕ) (g : SL(2, ℝ)) : theta D α y₀ n (-g) = theta D α y₀ n g := by
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  simp only [theta_apply _ _ _ _ _ hA, orbitPt_neg]

end Theta

/-! ### Asymptotic `P`-invariance -/

/-- Elements of `P = {± a_s n_u}`. -/
def IsP (p : SL(2, ℝ)) : Prop :=
  ∃ s₀ u₀ : ℝ, p = an s₀ 0 * an 0 u₀ ∨ p = -(an s₀ 0 * an 0 u₀)

lemma isP_ptri {t : ℝ} (v : ℝ) (ht : t ≠ 0) : IsP (ptri t v ht) := by
  rcases ht.lt_or_gt with h | h
  · exact ⟨_, _, Or.inr (ptri_of_neg v h)⟩
  · exact ⟨_, _, Or.inl (ptri_of_pos v h)⟩

section Estimates

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (f : Y →ᵇ ℝ)

/-- The integral of `f` against `phiM z`. -/
noncomputable def phiInt (z : ℍ) : ℝ := ∫ y, f y ∂(phiM Γ D.F α y₀ z)

lemma measurable_phiInt : Measurable (phiInt D α y₀ f) :=
  (f.continuous.measurable.stronglyMeasurable.integral_kernel (κ := phiK D α y₀)).measurable

omit [Countable Γ] in
lemma abs_phiInt_le (z : ℍ) : |phiInt D α y₀ f z| ≤ ‖f‖ := by
  haveI := isProbabilityMeasure_phiM D.cover D.fin α y₀ z
  exact f.norm_integral_le_norm _

/-- The inner average `s ↦ ⨍_u phiInt (h (s, u))` over `u ∈ [-(n + 1), n + 1]`. -/
noncomputable def avgU (n : ℕ) (h : ℝ × ℝ → ℍ) (s : ℝ) : ℝ :=
  ∫ u, phiInt D α y₀ f (h (s, u)) ∂unif (-(n + 1)) (n + 1)

lemma integral_theta_eq (n : ℕ) (g : SL(2, ℝ)) :
    ∫ y, f y ∂(theta D α y₀ n g : Measure Y) =
      ∫ s, avgU D α y₀ f n (orbitPt g) s ∂unif 0 (n + 1) := by
  rw [integral_theta, box, integral_prod]
  · rfl
  · refine Integrable.of_bound ((measurable_phiInt D α y₀ f).comp
      (measurable_orbitPt g)).aestronglyMeasurable ‖f‖ (ae_of_all _ fun q ↦ ?_)
    exact abs_phiInt_le D α y₀ f _

variable {D α y₀ f} in
lemma measurable_avgU {h : ℝ × ℝ → ℍ} (hh : Measurable h) (n : ℕ) :
    Measurable (avgU D α y₀ f n h) :=
  (((measurable_phiInt D α y₀ f).comp hh).stronglyMeasurable.integral_prod_right').measurable

omit [Countable Γ] in
variable {D α y₀ f} in
lemma abs_integral_unif_le {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : ℝ → ℍ) :
    |∫ u, phiInt D α y₀ f (h u) ∂μ| ≤ ‖f‖ := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun u ↦ phiInt D α y₀ f (h u))
    (C := ‖f‖) (ae_of_all _ fun u ↦ abs_phiInt_le D α y₀ f _)
  simpa using this

omit [Countable Γ] in
lemma abs_avgU_le (n : ℕ) (h : ℝ × ℝ → ℍ) (s : ℝ) : |avgU D α y₀ f n h s| ≤ ‖f‖ :=
  abs_integral_unif_le _

/-- Right translation by `a_{s₀}` moves the averages by `O(1 / n)`. -/
lemma abs_integral_theta_mul_an_s_sub_le (n : ℕ) (g : SL(2, ℝ)) (s₀ : ℝ) :
    |∫ y, f y ∂(theta D α y₀ n (g * an s₀ 0) : Measure Y) -
      ∫ y, f y ∂(theta D α y₀ n g : Measure Y)| ≤ 2 * ‖f‖ * |s₀| / (n + 1) := by
  have hG : Measurable (avgU D α y₀ f n (orbitPt g)) := measurable_avgU (measurable_orbitPt g) n
  have h1 : ∫ y, f y ∂(theta D α y₀ n (g * an s₀ 0) : Measure Y) =
      ∫ s, avgU D α y₀ f n (orbitPt g) (s + s₀) ∂unif 0 (n + 1) := by
    rw [integral_theta_eq]
    simp only [avgU, orbitPt, mul_assoc, an_mul_an_of_u_eq_zero]
  rw [h1, integral_theta_eq]
  have := abs_integral_unif_comp_add_sub_le (by positivity : (0 : ℝ) < n + 1) hG
    (abs_avgU_le D α y₀ f n _) s₀
  simpa using this

/-- Right translation by `n_{u₀}` moves the averages by `O(1 / n)` (this uses `s ≥ 0` on the
Følner set). -/
lemma abs_integral_theta_mul_an_u_sub_le (n : ℕ) (g : SL(2, ℝ)) (u₀ : ℝ) :
    |∫ y, f y ∂(theta D α y₀ n (g * an 0 u₀) : Measure Y) -
      ∫ y, f y ∂(theta D α y₀ n g : Measure Y)| ≤ ‖f‖ * |u₀| / (n + 1) := by
  have hcont : Continuous fun q : ℝ × ℝ ↦ orbitPt g (q.1, q.2 + u₀ * Real.exp (-q.1) ^ 2) :=
    (continuous_orbitPt.comp (Continuous.prodMk_right g)).comp (by fun_prop)
  have hH := measurable_avgU (D := D) (α := α) (y₀ := y₀) (f := f) hcont.measurable n
  have hG := measurable_avgU (D := D) (α := α) (y₀ := y₀) (f := f) (measurable_orbitPt g) n
  have h1 : ∫ y, f y ∂(theta D α y₀ n (g * an 0 u₀) : Measure Y) =
      ∫ s, avgU D α y₀ f n (fun q ↦ orbitPt g (q.1, q.2 + u₀ * Real.exp (-q.1) ^ 2)) s
        ∂unif 0 (n + 1) := by
    rw [integral_theta_eq]
    simp only [avgU, orbitPt, mul_assoc, an_mul_an_of_s_eq_zero]
  have hint : ∀ {K : ℝ → ℝ}, Measurable K → (∀ s, |K s| ≤ ‖f‖) →
      Integrable K (unif 0 (n + 1)) := fun hK hKb ↦
    Integrable.of_bound hK.aestronglyMeasurable ‖f‖ (ae_of_all _ hKb)
  rw [h1, integral_theta_eq, ← integral_sub (hint hH (abs_avgU_le D α y₀ f n _))
    (hint hG (abs_avgU_le D α y₀ f n _))]
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (μ := unif 0 (n + 1))
    (C := ‖f‖ * |u₀| / (n + 1)) ?_).trans_eq ?_
  swap
  · rw [probReal_univ, mul_one]
  filter_upwards [ae_unif_mem] with s hs
  have hc : |u₀ * Real.exp (-s) ^ 2| ≤ |u₀| := by
    rw [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (Real.exp_pos _).le ?_)
    exact Real.exp_le_one_iff.2 (by linarith [hs.1])
  have := abs_integral_unif_comp_add_sub_le (by linarith : -((n : ℝ) + 1) < n + 1)
    (h := fun u ↦ phiInt D α y₀ f (orbitPt g (s, u)))
    ((measurable_phiInt D α y₀ f).comp ((measurable_orbitPt g).comp measurable_prodMk_left))
    (fun u ↦ abs_phiInt_le D α y₀ f _) (u₀ * Real.exp (-s) ^ 2)
  rw [Real.norm_eq_abs]
  calc _ ≤ 2 * ‖f‖ * |u₀ * Real.exp (-s) ^ 2| / (n + 1 - -(n + 1)) := this
    _ ≤ 2 * ‖f‖ * |u₀| / (n + 1 - -(n + 1)) := by gcongr; linarith
    _ = ‖f‖ * |u₀| / (n + 1) := by field_simp; ring

/-- Right translation by `p ∈ P` moves the averages by `O(1 / n)`, uniformly in `g`. -/
lemma exists_abs_integral_theta_mul_sub_le {p : SL(2, ℝ)} (hp : IsP p) :
    ∃ C, ∀ n g, |∫ y, f y ∂(theta D α y₀ n (g * p) : Measure Y) -
      ∫ y, f y ∂(theta D α y₀ n g : Measure Y)| ≤ C / (n + 1) := by
  obtain ⟨s₀, u₀, hp⟩ := hp
  refine ⟨‖f‖ * |u₀| + 2 * ‖f‖ * |s₀|, fun n g ↦ ?_⟩
  have key : |∫ y, f y ∂(theta D α y₀ n (g * (an s₀ 0 * an 0 u₀)) : Measure Y) -
      ∫ y, f y ∂(theta D α y₀ n g : Measure Y)| ≤
        (‖f‖ * |u₀| + 2 * ‖f‖ * |s₀|) / (n + 1) := by
    rw [← mul_assoc, add_div]
    refine (abs_sub_le _ (∫ y, f y ∂(theta D α y₀ n (g * an s₀ 0) : Measure Y)) _).trans
      (add_le_add ?_ ?_)
    · exact abs_integral_theta_mul_an_u_sub_le D α y₀ f n _ u₀
    · exact abs_integral_theta_mul_an_s_sub_le D α y₀ f n g s₀
  rcases hp with rfl | rfl
  · exact key
  · rwa [mul_neg, theta_neg]

end Estimates

/-! ### The limit and its descent to the boundary -/

section Limit

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (D : FundSet Γ)
  {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
  (α : Γ →* (Y ≃ₜ Y)) (y₀ : Y) (W : TailWeights)

/-- The convergence set is right-`P`-invariant, with the same limit. -/
lemma tendsto_comb_theta_mul_iff {p : SL(2, ℝ)} (hp : IsP p) (g : SL(2, ℝ))
    (ν : ProbabilityMeasure Y) :
    Tendsto (fun m ↦ W.comb m fun k ↦ theta D α y₀ k (g * p)) atTop (𝓝 ν) ↔
      Tendsto (fun m ↦ W.comb m fun k ↦ theta D α y₀ k g) atTop (𝓝 ν) := by
  simp only [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  refine forall_congr' fun f ↦ ?_
  obtain ⟨C, hC⟩ := exists_abs_integral_theta_mul_sub_le D α y₀ f hp
  have hd : Tendsto (fun m ↦
      ∫ y, f y ∂(W.comb m fun k ↦ theta D α y₀ k (g * p) : Measure Y) -
        ∫ y, f y ∂(W.comb m fun k ↦ theta D α y₀ k g : Measure Y)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun m ↦ ?_) (a := fun m : ℕ ↦ C / ((m : ℝ) + 1)) ?_
    · rw [Real.norm_eq_abs]
      exact W.abs_integral_comb_sub_le m _ _ f fun k ↦ hC k g
    · simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul C
  constructor
  · intro h
    simpa using h.sub hd
  · intro h
    simpa using h.add hd

lemma comb_theta_mul (γ₀ : Γ) (g : SL(2, ℝ)) (m : ℕ) :
    (W.comb m fun k ↦ theta D α y₀ k ((γ₀ : SL(2, ℝ)) * g)) =
      (W.comb m fun k ↦ theta D α y₀ k g).map (α γ₀).continuous.measurable.aemeasurable := by
  rw [W.comb_map _ _ (α γ₀).continuous.measurable]
  simp_rw [theta_mul]

/-- The convergence set is left-`Γ`-invariant, with equivariant limit. -/
lemma tendsto_comb_theta_mul {γ₀ : Γ} {g : SL(2, ℝ)} {ν : ProbabilityMeasure Y}
    (h : Tendsto (fun m ↦ W.comb m fun k ↦ theta D α y₀ k g) atTop (𝓝 ν)) :
    Tendsto (fun m ↦ W.comb m fun k ↦ theta D α y₀ k ((γ₀ : SL(2, ℝ)) * g)) atTop
      (𝓝 (ν.map (α γ₀).continuous.measurable.aemeasurable)) := by
  simp_rw [comb_theta_mul]
  exact ((ProbabilityMeasure.continuous_map (α γ₀).continuous).tendsto ν).comp h

lemma measurable_integral_theta_sec (n : ℕ) (f : Y →ᵇ ℝ) :
    Measurable fun x ↦ ∫ y, f y ∂(theta D α y₀ n (sec x) : Measure Y) := by
  have hs := continuous_sec
  have hc : Continuous fun p : (ℝ × ℝ) × ℝ ↦ orbitPt (sec p.1.1) (p.1.2, p.2) :=
    continuous_orbitPt.comp (f := fun p : (ℝ × ℝ) × ℝ ↦ (sec p.1.1, (p.1.2, p.2)))
      (by fun_prop)
  have h2 : Measurable fun p : ℝ × ℝ ↦ avgU D α y₀ f n (orbitPt (sec p.1)) p.2 :=
    (StronglyMeasurable.integral_prod_right'
      (f := fun p : (ℝ × ℝ) × ℝ ↦ phiInt D α y₀ f (orbitPt (sec p.1.1) (p.1.2, p.2)))
      ((measurable_phiInt D α y₀ f).comp hc.measurable).stronglyMeasurable).measurable
  have heq : (fun x ↦ ∫ y, f y ∂(theta D α y₀ n (sec x) : Measure Y)) =
      fun x ↦ ∫ s, avgU D α y₀ f n (orbitPt (sec x)) s ∂unif 0 (n + 1) :=
    funext fun x ↦ integral_theta_eq D α y₀ f n (sec x)
  rw [heq]
  exact (StronglyMeasurable.integral_prod_right'
    (f := fun p : ℝ × ℝ ↦ avgU D α y₀ f n (orbitPt (sec p.1)) p.2)
    h2.stronglyMeasurable).measurable

end Limit

lemma measurable_onePoint_elim {Z : Type*} [MeasurableSpace Z] {c : Z} {f : ℝ → Z}
    (hf : Measurable f) : Measurable fun p : OnePoint ℝ ↦ p.elim c f := by
  classical
  intro B hB
  have hemb : MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have : (fun p : OnePoint ℝ ↦ p.elim c f) ⁻¹' B =
      (((↑) : ℝ → OnePoint ℝ) '' (f ⁻¹' B)) ∪ ({(∞ : OnePoint ℝ)} ∩ {_p | c ∈ B}) := by
    ext p
    induction p using OnePoint.rec with
    | infty => simp
    | coe x => simp
  rw [this]
  exact (hemb.measurableSet_image.2 (hf hB)).union
    ((measurableSet_singleton _).inter (MeasurableSet.const _))

/-- **Furstenberg boundary map.** A lattice `Γ ≤ SL(2, ℝ)` with a good fundamental set, acting on
a nonempty compact metrizable space `Y`, admits a measurable map `ψ : OnePoint ℝ → Prob(Y)` which
is `Γ`-equivariant almost everywhere. -/
theorem GoodLattice.exists_boundaryMap {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ)
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y] (α : Γ →* (Y ≃ₜ Y)) :
    ∃ ψ : OnePoint ℝ → ProbabilityMeasure Y, Measurable ψ ∧
      ∀ γ : Γ, ∀ᵐ x ∂bdry, (ψ ((γ : SL(2, ℝ)) • x) : Measure Y) = (ψ x : Measure Y).map (α γ) := by
  haveI : SecondCountableTopology Y := by
    letI := TopologicalSpace.metrizableSpaceMetric Y
    infer_instance
  haveI : Countable Γ := by
    haveI := h.discrete
    exact TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨F, hF, -, hcov, hfin⟩ := h.exists_fund
  set D : FundSet Γ := ⟨F, hF, hcov, hfin⟩
  set y₀ : Y := Classical.arbitrary Y
  set ν₀ : ProbabilityMeasure Y := theta D α y₀ 0 1
  have hmeas := measurable_integral_theta_sec D α y₀
  obtain ⟨W, hW⟩ := exists_tailWeights_ae_tendsto (ProbabilityTheory.gaussianReal 0 1)
    (fun n x ↦ theta D α y₀ n (sec x)) hmeas
  set ψℝ := W.lim (fun n x ↦ theta D α y₀ n (sec x)) ν₀
  refine ⟨fun p ↦ p.elim ν₀ ψℝ, measurable_onePoint_elim (measurable_lim W hmeas ν₀),
    fun γ ↦ ?_⟩
  have hemb : MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  rw [bdry, hemb.ae_map_iff]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ W.convSet fun n x ↦ theta D α y₀ n (sec x) :=
    (ProbabilityTheory.gaussianReal_absolutelyContinuous' 0 one_ne_zero).ae_le hW
  have hdet : (γ : SL(2, ℝ)) 0 0 * (γ : SL(2, ℝ)) 1 1 - (γ : SL(2, ℝ)) 0 1 * (γ : SL(2, ℝ)) 1 0
      = 1 := by
    have := (γ : SL(2, ℝ)).det_coe
    rwa [det_fin_two] at this
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), (γ : SL(2, ℝ)) 1 0 * x + (γ : SL(2, ℝ)) 1 1 ≠ 0 := by
    by_cases hc : (γ : SL(2, ℝ)) 1 0 = 0
    · refine ae_of_all _ fun x ↦ ?_
      rw [hc, zero_mul, zero_add]
      rintro h0
      rw [h0, hc] at hdet
      simp at hdet
    · filter_upwards [Measure.ae_ne volume (-(γ : SL(2, ℝ)) 1 1 / (γ : SL(2, ℝ)) 1 0)]
        with x hx h0
      apply hx
      field_simp
      linarith
  filter_upwards [hae, hne] with x hx ht
  set t := (γ : SL(2, ℝ)) 1 0 * x + (γ : SL(2, ℝ)) 1 1
  set y := ((γ : SL(2, ℝ)) 0 0 * x + (γ : SL(2, ℝ)) 0 1) / t
  have hsmul : (γ : SL(2, ℝ)) • (x : OnePoint ℝ) = (y : OnePoint ℝ) := by
    rw [sl_smul_bdry, OnePoint.smul_some_eq_ite]
    simp [t, y, ht]
  have h1 := tendsto_comb_theta_mul D α y₀ W (γ₀ := γ) (W.tendsto_lim ν₀ hx)
  rw [mul_sec _ _ ht] at h1
  have h2 := (tendsto_comb_theta_mul_iff D α y₀ W (isP_ptri _ ht) _ _).1 h1
  have hy : y ∈ W.convSet fun n x ↦ theta D α y₀ n (sec x) := ⟨_, h2⟩
  have h3 := tendsto_nhds_unique (W.tendsto_lim ν₀ hy) h2
  rw [hsmul]
  change (ψℝ y : Measure Y) = (ψℝ x : Measure Y).map (α γ)
  have h4 : ψℝ y = (ψℝ x).map (α γ).continuous.measurable.aemeasurable := h3
  rw [h4, ProbabilityMeasure.toMeasure_map]

/-- `GoodLattice.exists_boundaryMap` with the boundary map packaged as a Markov kernel. -/
theorem GoodLattice.exists_boundaryKernel {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ)
    {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] [Nonempty Y] (α : Γ →* (Y ≃ₜ Y)) :
    ∃ κ : ProbabilityTheory.Kernel (OnePoint ℝ) Y, ProbabilityTheory.IsMarkovKernel κ ∧
      ∀ γ : Γ, ∀ᵐ x ∂bdry, κ ((γ : SL(2, ℝ)) • x) = (κ x).map (α γ) := by
  obtain ⟨ψ, hψ, heq⟩ := h.exists_boundaryMap α
  exact ⟨⟨fun x ↦ ψ x, measurable_subtype_coe.comp hψ⟩, ⟨fun x ↦ (ψ x).2⟩, heq⟩

end OrbicurveCores.M2
