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

end OrbicurveCores.M2
