/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.ForMathlib.TailConvex

/-!
# M2, part F: limits of tail convex combinations of probability measures

The abstract analytic core of the Furstenberg boundary map (`Blueprint.md`, §2.3b, part F).

* `TailWeights`: a sequence of finitely supported convex weights `w n` on `ℕ`, with `w n`
  supported in `[n, ∞)`, and `TailWeights.comb`, the corresponding convex combinations of
  probability measures.
* `exists_tendsto_of_forall_dense`: on a compact space, a sequence of probability measures
  converges as soon as the integrals of a dense sequence of test functions converge (Prokhorov).
* `measurable_of_forall_integral`: a map into `ProbabilityMeasure Y` (Giry structure) is
  measurable as soon as all its integrals of bounded continuous functions are.
* `exists_tailWeights_ae_tendsto`: for a measurable family `θ n x` of probability measures on a
  compact metrizable `Y`, parametrised by a finite measure space `X`, some tail convex
  combinations converge for almost every `x`. The proof applies the Hilbert-space lemma
  `exists_tail_convex_tendsto` in `L²(X × ℕ)` to the integrals against a dense sequence of test
  functions.
-/

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal

namespace OrbicurveCores.M2

variable {Y : Type*} [MeasurableSpace Y]

/-- Tail convex weights: `w n` is a finitely supported probability vector on `ℕ` supported in
`[n, ∞)`. -/
structure TailWeights where
  /-- The weights. -/
  w : ℕ → ℕ →₀ ℝ
  nonneg : ∀ n k, 0 ≤ w n k
  sum_eq_one : ∀ n, ((w n).sum fun _ c ↦ c) = 1
  le_of_mem : ∀ n, ∀ k ∈ (w n).support, n ≤ k

namespace TailWeights

variable (W : TailWeights)

lemma sum_support_eq_one (n : ℕ) : ∑ k ∈ (W.w n).support, W.w n k = 1 := W.sum_eq_one n

/-- The convex combination `∑ₖ w n k • θ k` of measures. -/
noncomputable def combMeasure (n : ℕ) (θ : ℕ → Measure Y) : Measure Y :=
  ∑ k ∈ (W.w n).support, ENNReal.ofReal (W.w n k) • θ k

lemma combMeasure_apply (n : ℕ) (θ : ℕ → Measure Y) (s : Set Y) :
    W.combMeasure n θ s = ∑ k ∈ (W.w n).support, ENNReal.ofReal (W.w n k) * θ k s := by
  simp [combMeasure]

instance (n : ℕ) (θ : ℕ → Measure Y) [∀ k, IsProbabilityMeasure (θ k)] :
    IsProbabilityMeasure (W.combMeasure n θ) := by
  constructor
  rw [combMeasure_apply]
  simp only [measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦ W.nonneg n k), W.sum_support_eq_one,
    ENNReal.ofReal_one]

/-- The convex combination `∑ₖ w n k • θ k` of probability measures. -/
noncomputable def comb (n : ℕ) (θ : ℕ → ProbabilityMeasure Y) : ProbabilityMeasure Y :=
  ⟨W.combMeasure n fun k ↦ θ k, inferInstance⟩

lemma coe_comb (n : ℕ) (θ : ℕ → ProbabilityMeasure Y) :
    (W.comb n θ : Measure Y) = W.combMeasure n fun k ↦ θ k := rfl

lemma integral_comb [TopologicalSpace Y] [OpensMeasurableSpace Y] (n : ℕ)
    (θ : ℕ → ProbabilityMeasure Y) (f : Y →ᵇ ℝ) :
    ∫ y, f y ∂(W.comb n θ : Measure Y) =
      ∑ k ∈ (W.w n).support, W.w n k * ∫ y, f y ∂(θ k : Measure Y) := by
  rw [coe_comb, combMeasure,
    integral_finsetSum_measure (fun k _ ↦ (f.integrable _).smul_measure (by simp))]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal (W.nonneg n k), smul_eq_mul]

lemma comb_map {Z : Type*} [MeasurableSpace Z] (n : ℕ) (θ : ℕ → ProbabilityMeasure Y)
    {h : Y → Z} (hh : Measurable h) :
    (W.comb n θ).map hh.aemeasurable = W.comb n fun k ↦ (θ k).map hh.aemeasurable := by
  apply ProbabilityMeasure.toMeasure_injective
  ext s hs
  simp only [ProbabilityMeasure.toMeasure_map, coe_comb, combMeasure_apply,
    Measure.map_apply hh hs]

/-- Passing to a subsequence of tail weights. -/
def subseq (ns : ℕ → ℕ) (hns : StrictMono ns) : TailWeights where
  w n := W.w (ns n)
  nonneg n := W.nonneg (ns n)
  sum_eq_one n := W.sum_eq_one (ns n)
  le_of_mem n k hk := (hns.id_le n).trans (W.le_of_mem _ k hk)

/-- A tail average of a sequence decaying like `C / (k + 1)` decays like `C / (n + 1)`. -/
lemma abs_sum_le (n : ℕ) (a : ℕ → ℝ) {C : ℝ} (ha : ∀ k, |a k| ≤ C / (k + 1)) :
    |∑ k ∈ (W.w n).support, W.w n k * a k| ≤ C / (n + 1) := by
  have hC : 0 ≤ C := by simpa using (abs_nonneg _).trans (ha 0)
  calc |∑ k ∈ (W.w n).support, W.w n k * a k|
      ≤ ∑ k ∈ (W.w n).support, |W.w n k * a k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ (W.w n).support, W.w n k * (C / (n + 1)) := by
        refine Finset.sum_le_sum fun k hk ↦ ?_
        rw [abs_mul, abs_of_nonneg (W.nonneg n k)]
        refine mul_le_mul_of_nonneg_left ((ha k).trans ?_) (W.nonneg n k)
        have : (n : ℝ) ≤ k := by exact_mod_cast W.le_of_mem n k hk
        gcongr
    _ = C / (n + 1) := by rw [← Finset.sum_mul, W.sum_support_eq_one, one_mul]

lemma abs_integral_comb_sub_le [TopologicalSpace Y] [OpensMeasurableSpace Y] (n : ℕ)
    (θ θ' : ℕ → ProbabilityMeasure Y) (f : Y →ᵇ ℝ) {C : ℝ}
    (h : ∀ k, |∫ y, f y ∂(θ k : Measure Y) - ∫ y, f y ∂(θ' k : Measure Y)| ≤ C / (k + 1)) :
    |∫ y, f y ∂(W.comb n θ : Measure Y) - ∫ y, f y ∂(W.comb n θ' : Measure Y)| ≤
      C / (n + 1) := by
  rw [integral_comb, integral_comb, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  exact W.abs_sum_le n _ h

end TailWeights

section Convergence

variable [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- On a compact space, a sequence of probability measures converges as soon as the integrals
of a dense sequence of test functions converge. -/
theorem exists_tendsto_of_forall_dense [CompactSpace Y] [T2Space Y] [BorelSpace Y]
    {f : ℕ → Y →ᵇ ℝ} (hf : DenseRange f) {θ : ℕ → ProbabilityMeasure Y}
    (h : ∀ j, ∃ l, Tendsto (fun m ↦ ∫ y, f j y ∂(θ m : Measure Y)) atTop (𝓝 l)) :
    ∃ ν, Tendsto θ atTop (𝓝 ν) := by
  have hall : ∀ g : Y →ᵇ ℝ, ∃ l, Tendsto (fun m ↦ ∫ y, g y ∂(θ m : Measure Y)) atTop (𝓝 l) := by
    intro g
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_)
    obtain ⟨j, hj⟩ := hf.exists_dist_lt g (by positivity : 0 < ε / 3)
    obtain ⟨l, hl⟩ := h j
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hl.cauchySeq (ε / 3) (by positivity)
    have key : ∀ m, dist (∫ y, g y ∂(θ m : Measure Y)) (∫ y, f j y ∂(θ m : Measure Y)) ≤
        dist g (f j) := by
      intro m
      rw [dist_eq_norm, ← integral_sub (g.integrable _) ((f j).integrable _), dist_eq_norm]
      exact (g - f j).norm_integral_le_norm _
    refine ⟨N, fun m hm ↦ ?_⟩
    calc dist (∫ y, g y ∂(θ m : Measure Y)) (∫ y, g y ∂(θ N : Measure Y))
        ≤ dist (∫ y, g y ∂(θ m : Measure Y)) (∫ y, f j y ∂(θ m : Measure Y)) +
          dist (∫ y, f j y ∂(θ m : Measure Y)) (∫ y, f j y ∂(θ N : Measure Y)) +
          dist (∫ y, f j y ∂(θ N : Measure Y)) (∫ y, g y ∂(θ N : Measure Y)) :=
          dist_triangle4 _ _ _ _
      _ < ε / 3 + ε / 3 + ε / 3 := by
          rw [dist_comm (∫ y, f j y ∂(θ N : Measure Y))]
          gcongr
          · exact (key m).trans_lt hj
          · exact hN m hm
          · exact (key N).trans_lt hj
      _ = ε := by ring
  obtain ⟨ν, hν⟩ := exists_clusterPt_of_compactSpace (map θ atTop)
  refine ⟨ν, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 fun g ↦ ?_⟩
  obtain ⟨l, hl⟩ := hall g
  have hc := hν.map
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction g).continuousAt tendsto_map
  rw [Filter.map_map] at hc
  have : ∫ y, g y ∂(ν : Measure Y) = l := eq_of_nhds_neBot (hc.mono hl)
  rwa [this]

/-- The converse direction of `exists_tendsto_of_forall_dense`. -/
lemma exists_tendsto_integral_of_tendsto {θ : ℕ → ProbabilityMeasure Y} {ν : ProbabilityMeasure Y}
    (h : Tendsto θ atTop (𝓝 ν)) (f : Y →ᵇ ℝ) :
    ∃ l, Tendsto (fun m ↦ ∫ y, f y ∂(θ m : Measure Y)) atTop (𝓝 l) :=
  ⟨_, ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h f⟩

/-- A map into `ProbabilityMeasure Y` (with the Giry structure) is measurable as soon as all its
integrals of bounded continuous functions are. -/
theorem measurable_of_forall_integral [TopologicalSpace.PseudoMetrizableSpace Y] [BorelSpace Y]
    {X : Type*} [MeasurableSpace X] {ψ : X → ProbabilityMeasure Y}
    (h : ∀ f : Y →ᵇ ℝ, Measurable fun x ↦ ∫ y, f y ∂(ψ x : Measure Y)) : Measurable ψ := by
  have : Measurable fun x ↦ (ψ x : Measure Y) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure (S := {s | IsClosed s})
      ((BorelSpace.measurable_eq).trans borel_eq_generateFrom_isClosed) isPiSystem_isClosed ?_
    intro s hs
    refine measurable_of_tendsto_metrizable
      (f := fun n x ↦ ∫⁻ y, (IsClosed.apprSeq hs n y : ℝ≥0∞) ∂(ψ x : Measure Y))
      (fun n ↦ ?_) (tendsto_pi_nhds.2 fun x ↦ HasOuterApproxClosed.tendsto_lintegral_apprSeq hs _)
    set g : Y →ᵇ ℝ≥0 := IsClosed.apprSeq hs n
    set g' : Y →ᵇ ℝ := ⟨⟨fun y ↦ (g y : ℝ), NNReal.continuous_coe.comp g.continuous⟩,
      g.map_bounded'⟩
    have : (fun x ↦ ∫⁻ y, (g y : ℝ≥0∞) ∂(ψ x : Measure Y)) =
        fun x ↦ ENNReal.ofReal (∫ y, g' y ∂(ψ x : Measure Y)) := by
      funext x
      rw [← ENNReal.ofReal_toReal (g.lintegral_lt_top_of_nnreal (ψ x : Measure Y)).ne,
        g.toReal_lintegral_coe_eq_integral]
      rfl
    rw [this]
    exact ENNReal.measurable_ofReal.comp (h g')
  exact this.subtype_mk

end Convergence

section Limit

variable [TopologicalSpace Y] [OpensMeasurableSpace Y]

/-- The set of parameters at which the tail convex combinations converge. -/
def TailWeights.convSet (W : TailWeights) {G : Type*} (Θ : ℕ → G → ProbabilityMeasure Y) :
    Set G :=
  {g | ∃ ν, Tendsto (fun m ↦ W.comb m fun k ↦ Θ k g) atTop (𝓝 ν)}

open Classical in
/-- The limit of the tail convex combinations (`ν₀` where they do not converge). -/
noncomputable def TailWeights.lim (W : TailWeights) {G : Type*}
    (Θ : ℕ → G → ProbabilityMeasure Y) (ν₀ : ProbabilityMeasure Y) (g : G) :
    ProbabilityMeasure Y :=
  if g ∈ W.convSet Θ then @limUnder _ _ _ ⟨ν₀⟩ atTop (fun m ↦ W.comb m fun k ↦ Θ k g) else ν₀

lemma TailWeights.tendsto_lim [T2Space (ProbabilityMeasure Y)] (W : TailWeights) {G : Type*}
    {Θ : ℕ → G → ProbabilityMeasure Y} (ν₀ : ProbabilityMeasure Y) {g : G}
    (hg : g ∈ W.convSet Θ) :
    Tendsto (fun m ↦ W.comb m fun k ↦ Θ k g) atTop (𝓝 (W.lim Θ ν₀ g)) := by
  haveI : Nonempty (ProbabilityMeasure Y) := ⟨ν₀⟩
  rw [TailWeights.lim, if_pos hg]
  exact tendsto_nhds_limUnder hg

end Limit

section Main

variable [TopologicalSpace Y] [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y]
  [SecondCountableTopology Y] [BorelSpace Y]

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma exists_denseRange_boundedContinuousFunction : ∃ f : ℕ → Y →ᵇ ℝ, DenseRange f := by
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq C(Y, ℝ)
  refine ⟨fun j ↦ mkOfCompact (u j), fun g ↦ Metric.mem_closure_iff.2 fun ε hε ↦ ?_⟩
  obtain ⟨j, hj⟩ := hu.exists_dist_lt g.toContinuousMap hε
  refine ⟨_, ⟨j, rfl⟩, ?_⟩
  have : g = mkOfCompact g.toContinuousMap := by ext; simp
  rw [this, dist_mkOfCompact]
  exact hj

omit [SecondCountableTopology Y] in
/-- Almost everywhere, the conclusion of `exists_tendsto_of_forall_dense` and its converse. -/
lemma mem_convSet_iff {f : ℕ → Y →ᵇ ℝ} (hf : DenseRange f) (W : TailWeights) {G : Type*}
    (Θ : ℕ → G → ProbabilityMeasure Y) (g : G) :
    g ∈ W.convSet Θ ↔ ∀ j, ∃ l, Tendsto
      (fun m ↦ ∫ y, f j y ∂(W.comb m fun k ↦ Θ k g : Measure Y)) atTop (𝓝 l) :=
  ⟨fun ⟨_, h⟩ j ↦ exists_tendsto_integral_of_tendsto h (f j),
    fun h ↦ by exact exists_tendsto_of_forall_dense hf h⟩

variable {X : Type*} [MeasurableSpace X]

omit [CompactSpace Y] [TopologicalSpace.MetrizableSpace Y] [SecondCountableTopology Y] in
lemma measurable_integral_comb (W : TailWeights) {Θ : ℕ → X → ProbabilityMeasure Y}
    (hΘ : ∀ n (f : Y →ᵇ ℝ), Measurable fun x ↦ ∫ y, f y ∂(Θ n x : Measure Y)) (m : ℕ)
    (f : Y →ᵇ ℝ) :
    Measurable fun x ↦ ∫ y, f y ∂(W.comb m fun k ↦ Θ k x : Measure Y) := by
  simp_rw [TailWeights.integral_comb]
  exact Finset.measurable_sum _ fun k _ ↦ (hΘ k f).const_mul _

lemma measurableSet_convSet (W : TailWeights) {Θ : ℕ → X → ProbabilityMeasure Y}
    (hΘ : ∀ n (f : Y →ᵇ ℝ), Measurable fun x ↦ ∫ y, f y ∂(Θ n x : Measure Y)) :
    MeasurableSet (W.convSet Θ) := by
  obtain ⟨f, hf⟩ := exists_denseRange_boundedContinuousFunction (Y := Y)
  have : W.convSet Θ = ⋂ j, {x | ∃ l, Tendsto
      (fun m ↦ ∫ y, f j y ∂(W.comb m fun k ↦ Θ k x : Measure Y)) atTop (𝓝 l)} := by
    ext x
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact mem_convSet_iff hf W Θ x
  rw [this]
  exact MeasurableSet.iInter fun j ↦
    measurableSet_exists_tendsto fun m ↦ measurable_integral_comb W hΘ m (f j)

lemma measurable_lim (W : TailWeights) {Θ : ℕ → X → ProbabilityMeasure Y}
    (hΘ : ∀ n (f : Y →ᵇ ℝ), Measurable fun x ↦ ∫ y, f y ∂(Θ n x : Measure Y))
    (ν₀ : ProbabilityMeasure Y) : Measurable (W.lim Θ ν₀) := by
  classical
  refine measurable_of_forall_integral fun f ↦ ?_
  have hS := measurableSet_convSet W hΘ
  refine measurable_of_tendsto_metrizable (f := fun m x ↦ if x ∈ W.convSet Θ then
      ∫ y, f y ∂(W.comb m fun k ↦ Θ k x : Measure Y) else ∫ y, f y ∂(ν₀ : Measure Y))
    (fun m ↦ Measurable.ite hS (measurable_integral_comb W hΘ m f) measurable_const)
    (tendsto_pi_nhds.2 fun x ↦ ?_)
  by_cases hx : x ∈ W.convSet Θ
  · simp only [if_pos hx]
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 (W.tendsto_lim ν₀ hx) f
  · simp only [if_neg hx, TailWeights.lim]
    exact tendsto_const_nhds

/-- The measure on `ℕ` with weights `2⁻ʲ`. -/
noncomputable def geomWeights : Measure ℕ :=
  Measure.sum fun j ↦ (2⁻¹ : ℝ≥0∞) ^ j • Measure.dirac j

instance : IsFiniteMeasure geomWeights := by
  constructor
  rw [geomWeights, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, ENNReal.tsum_geometric]
  exact ENNReal.inv_lt_top.2 (by norm_num)

lemma forall_of_ae_geomWeights {p : ℕ → Prop} (h : ∀ᵐ j ∂geomWeights, p j) (j : ℕ) : p j := by
  by_contra hj
  have h0 : geomWeights {j | ¬p j} = 0 := ae_iff.1 h
  have : (2⁻¹ : ℝ≥0∞) ^ j ≤ geomWeights {j | ¬p j} := by
    calc (2⁻¹ : ℝ≥0∞) ^ j = ((2⁻¹ : ℝ≥0∞) ^ j • Measure.dirac j) {j | ¬p j} := by
          simp [Measure.dirac_apply_of_mem (show j ∈ {j | ¬p j} from hj)]
      _ ≤ geomWeights {j | ¬p j} := Measure.le_sum (fun j ↦ (2⁻¹ : ℝ≥0∞) ^ j • Measure.dirac j) j _
  rw [h0] at this
  exact (pow_ne_zero j (by simp)) (le_antisymm this bot_le)

lemma Lp.coeFn_finset_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (g : ι → Lp ℝ 2 μ) :
    ⇑(∑ k ∈ s, c k • g k) =ᵐ[μ] fun p ↦ ∑ k ∈ s, c k * g k p := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ 2 μ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (c a • g a) (∑ k ∈ s, c k • g k), Lp.coeFn_smul (c a) (g a),
      ih] with p h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, smul_eq_mul]

/-- **Almost everywhere convergence of tail convex combinations.** For a measurable family of
probability measures on a compact metrizable space, parametrised by a finite measure space,
suitable tail convex combinations converge almost everywhere. -/
theorem exists_tailWeights_ae_tendsto (μ : Measure X) [IsFiniteMeasure μ]
    (Θ : ℕ → X → ProbabilityMeasure Y)
    (hΘ : ∀ n (f : Y →ᵇ ℝ), Measurable fun x ↦ ∫ y, f y ∂(Θ n x : Measure Y)) :
    ∃ W : TailWeights, ∀ᵐ x ∂μ, x ∈ W.convSet Θ := by
  obtain ⟨f, hf⟩ := exists_denseRange_boundedContinuousFunction (Y := Y)
  set ν := μ.prod geomWeights
  set Φ : ℕ → X × ℕ → ℝ := fun n p ↦ (∫ y, f p.2 y ∂(Θ n p.1 : Measure Y)) / (1 + ‖f p.2‖)
  have hΦb : ∀ n p, ‖Φ n p‖ ≤ 1 := by
    intro n p
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + ‖f p.2‖),
      div_le_one (by positivity)]
    exact ((f p.2).norm_integral_le_norm _).trans (by linarith)
  have hΦm : ∀ n, Measurable (Φ n) := fun n ↦
    measurable_from_prod_countable_left fun j ↦ by
      simpa only [Φ] using (hΘ n (f j)).div_const (1 + ‖f j‖)
  have hΦL : ∀ n, MemLp (Φ n) 2 ν := fun n ↦
    MemLp.of_bound (hΦm n).aestronglyMeasurable 1 (ae_of_all _ (hΦb n))
  set xs : ℕ → Lp ℝ 2 ν := fun n ↦ (hΦL n).toLp
  have hxs : ∀ n, ‖xs n‖ ≤ measureUnivNNReal ν ^ (2 : ℝ≥0∞).toReal⁻¹ * 1 := fun n ↦
    Lp.norm_le_of_ae_bound zero_le_one (by
      filter_upwards [(hΦL n).coeFn_toLp] with p hp
      rw [hp]; exact hΦb n p)
  obtain ⟨w, hw0, hw1, hws, z, hz⟩ := exists_tail_convex_tendsto xs hxs
  set W₀ : TailWeights := ⟨w, hw0, hw1, hws⟩
  set ys : ℕ → Lp ℝ 2 ν := fun m ↦ (w m).sum fun k c ↦ c • xs k
  have hys : ∀ m, ⇑(ys m) =ᵐ[ν] fun p ↦ ∑ k ∈ (w m).support, w m k * Φ k p := by
    intro m
    filter_upwards [Lp.coeFn_finset_sum (w m).support (fun k ↦ w m k) xs,
      ae_all_iff.2 fun k ↦ (hΦL k).coeFn_toLp] with p h1 h2
    simp only [ys, Finsupp.sum, h1]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [h2 k]
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hz).exists_seq_tendsto_ae
  refine ⟨W₀.subseq ns hns, ?_⟩
  have hae' : ∀ᵐ p ∂ν, Tendsto (fun i ↦ ∑ k ∈ (w (ns i)).support, w (ns i) k * Φ k p) atTop
      (𝓝 (z p)) := by
    filter_upwards [hae, ae_all_iff.2 hys] with p hp h2
    simpa only [h2] using hp
  filter_upwards [Measure.ae_ae_of_ae_prod hae'] with x hx
  rw [mem_convSet_iff hf]
  intro j
  refine ⟨(1 + ‖f j‖) * z (x, j), ?_⟩
  have := (forall_of_ae_geomWeights hx j).const_mul (1 + ‖f j‖)
  refine this.congr fun i ↦ ?_
  rw [TailWeights.integral_comb, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [Φ, W₀, TailWeights.subseq]
  field_simp

end Main

end OrbicurveCores.M2
