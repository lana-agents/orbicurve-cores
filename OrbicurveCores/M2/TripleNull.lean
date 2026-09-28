/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.FromProb

/-!
# M2: the Furstenberg measure does not charge distinct triples

If `ρ(Γ)` is unbounded, then `κ(x)³` gives zero mass to distinct triples for a.e. `x`.

Suppose the mass is a positive constant `c`. The relative-position measure
`(κ(x₁)³ ⊗ κ(x₂)³){rel(t₁, t₂) ∈ C}` is invariant, hence constant, by double ergodicity. An
exhaustion of the distinct triples by compacts then yields a compact set `E` of distinct triples
with `κ(x)³(E) > c/2` for a.e. `x`. So `ρ(γ)E ∩ E ≠ ∅` for every `γ ∈ Γ`. By sharp
3-transitivity, `ρ(γ)(0, 1, ∞)` then stays in a fixed compact set of distinct triples,
contradicting unboundedness.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology OnePoint.Proj
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

/-- `ρ(Γ)` is unbounded: some sequence moves `(0, 1, ∞)` to a degenerate triple in the limit. -/
def Unbounded (Γ : Subgroup SL(2, ℝ)) (a : SL(2, ℝ) → GL (Fin 2) k) : Prop :=
  ∃ γs : ℕ → SL(2, ℝ), (∀ n, γs n ∈ Γ) ∧ ∃ τ : Triple k, ¬ Distinct3 τ ∧
    Tendsto (fun n ↦ smul3 (a (γs n)) e₃) atTop (𝓝 τ)

omit [DecidableEq k] in
/-- A compact exhaustion of the distinct triples by open sets with compact closure. -/
lemma exists_exhaustion : ∃ K C : ℕ → Set (Triple k), (∀ n, IsCompact (K n)) ∧
    (∀ n, IsOpen (C n)) ∧ (∀ n, C n ⊆ K n) ∧ (∀ n, K n ⊆ D3set) ∧ Monotone C ∧
    ⋃ n, C n = D3set := by
  have hD : IsOpen (D3set (k := k)) := isOpen_distinct3
  haveI : LocallyCompactSpace (D3set (k := k)) := hD.locallyCompactSpace
  let E : CompactExhaustion (D3set (k := k)) := CompactExhaustion.choice _
  have hemb : IsOpenEmbedding ((↑) : D3set (k := k) → Triple k) := hD.isOpenEmbedding_subtypeVal
  refine ⟨fun n ↦ (↑) '' E n, fun n ↦ (↑) '' interior (E n), fun n ↦ (E.isCompact n).image
    continuous_subtype_val, fun n ↦ hemb.isOpenMap _ isOpen_interior,
    fun n ↦ image_mono interior_subset, fun n ↦ by rintro _ ⟨x, -, rfl⟩; exact x.2,
    fun m n hmn ↦ image_mono (interior_mono (E.subset hmn)), ?_⟩
  ext t
  simp only [mem_iUnion, mem_image]
  constructor
  · rintro ⟨n, x, -, rfl⟩; exact x.2
  · intro ht
    obtain ⟨n, hn⟩ := E.exists_mem ⟨t, ht⟩
    exact ⟨n + 1, ⟨t, ht⟩, E.subset_interior_succ n hn, rfl⟩


lemma measurable_smul3 (g : GL (Fin 2) k) : Measurable (smul3 g) := by
  have hm := (measurable_gl_smul (k := k) g)
  exact hm.prodMap (hm.prodMap hm)

omit [ProperSpace k] in
lemma distinct3_smul3_iff (g : GL (Fin 2) k) (t : Triple k) :
    Distinct3 (smul3 g t) ↔ Distinct3 t := by
  simp only [Distinct3, smul3, ne_eq, smul_left_cancel_iff]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma exists_of_ae_prod {p : OnePoint ℝ × OnePoint ℝ → Prop}
    (h : ∀ᵐ q ∂(bdry.prod bdry), p q) : ∃ q, p q := by
  obtain ⟨x, hx⟩ := exists_of_ae (Measure.ae_ae_of_ae_prod h)
  obtain ⟨y, hy⟩ := exists_of_ae hx
  exact ⟨(x, y), hy⟩

section

variable {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}
  (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ]

/-- `x ↦ κ(x)³` restricted to distinct triples. -/
noncomputable abbrev mk3 : Kernel (OnePoint ℝ) (Triple k) :=
  Kernel.restrict (kern3 κ) measurableSet_D3set

omit [DecidableEq k] in
lemma mk3_apply {x : OnePoint ℝ} {s : Set (Triple k)} (hs : MeasurableSet s) :
    mk3 κ x s = kern3 κ x (s ∩ D3set) :=
  Kernel.restrict_apply' _ _ _ hs

lemma mk3_map {x y : OnePoint ℝ} {g : GL (Fin 2) k} (h : κ y = (κ x).map (fun z ↦ g • z)) :
    mk3 κ y = (mk3 κ x).map (smul3 g) := by
  rw [Kernel.restrict_apply, Kernel.restrict_apply, (kern_map κ h).2,
    Measure.restrict_map (measurable_smul3 g) measurableSet_D3set, smul3_preimage_D3set]

omit [DecidableEq k] in
lemma mk3_univ (x : OnePoint ℝ) : mk3 κ x univ = kern3 κ x D3set := by
  rw [mk3_apply κ MeasurableSet.univ, univ_inter]

instance : IsFiniteKernel (mk3 κ) := by infer_instance

/-- The pair kernel `(x₁, x₂) ↦ mk3(x₁) ⊗ mk3(x₂)`. -/
noncomputable abbrev mk3pair : Kernel (OnePoint ℝ × OnePoint ℝ) (Triple k × Triple k) :=
  (Kernel.comap (mk3 κ) Prod.fst measurable_fst) ×ₖ (Kernel.comap (mk3 κ) Prod.snd measurable_snd)

omit [DecidableEq k] in
lemma mk3pair_apply (q : OnePoint ℝ × OnePoint ℝ) :
    mk3pair κ q = (mk3 κ q.1).prod (mk3 κ q.2) := by
  rw [Kernel.prod_apply, Kernel.comap_apply, Kernel.comap_apply]

variable [MeasurableSpace k] [BorelSpace k]

omit [MeasurableSpace k] [BorelSpace k] in
/-- **The Furstenberg measure does not charge distinct triples.** -/
theorem triple_null_of_unbounded [Countable Γ] (hΓ : IsDoublyErgodic Γ) (hunb : Unbounded Γ a)
    (heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, κ (γ • x) = (κ x).map (fun y ↦ a γ • y)) :
    ∀ᵐ x ∂bdry, kern3 κ x D3set = 0 := by
  classical
  set Tf : OnePoint ℝ → ℝ≥0∞ := fun x ↦ kern3 κ x D3set
  have hTf : Measurable Tf := Kernel.measurable_coe _ measurableSet_D3set
  have hTinv : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, Tf (γ • x) = Tf x := by
    intro γ hγ
    filter_upwards [heq γ hγ] with x hx
    simp only [Tf, (kern_map κ hx).2]
    rw [Measure.map_apply (measurable_smul3 _) measurableSet_D3set, smul3_preimage_D3set]
  obtain ⟨c, hc⟩ := hΓ.ae_const_single hTf hTinv
  by_cases hc0 : c = 0
  · exact hc.mono fun x hx ↦ hx.trans hc0
  exfalso
  have hcle : c ≤ 1 := by
    obtain ⟨x, hx⟩ := exists_of_ae hc
    rw [← hx]; exact prob_le_one
  have hct : c ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hcle
  obtain ⟨K, C, hK, hC, hCK, hKD, hCmono, hCU⟩ := exists_exhaustion (k := k)
  -- the sets of pairs in relative position `C n`
  set s2 : Set (Triple k × Triple k) := {p | Distinct3 p.1 ∧ Distinct3 p.2}
  have hs2 : IsOpen s2 :=
    (isOpen_distinct3.preimage continuous_fst).inter (isOpen_distinct3.preimage continuous_snd)
  have hs2' : s2 = D3set ×ˢ D3set := rfl
  set W : ℕ → Set (Triple k × Triple k) := fun n ↦ s2 ∩ (fun p ↦ rel p.1 p.2) ⁻¹' C n
  have hWo : ∀ n, IsOpen (W n) := fun n ↦
    (continuousOn_rel.mono fun p hp ↦ hp.1).isOpen_inter_preimage hs2 (hC n)
  have hWm : Monotone W := fun m n hmn ↦ inter_subset_inter_right _ (preimage_mono (hCmono hmn))
  have hWU : ⋃ n, W n = s2 := by
    ext p
    simp only [W, mem_iUnion, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨n, hp, -⟩; exact hp
    · intro hp
      have : rel p.1 p.2 ∈ ⋃ n, C n := by rw [hCU]; exact distinct3_rel hp.1 hp.2
      obtain ⟨n, hn⟩ := mem_iUnion.1 this
      exact ⟨n, hp, hn⟩
  have hWinv : ∀ (g : GL (Fin 2) k) n,
      Prod.map (smul3 g) (smul3 g) ⁻¹' W n = W n := by
    intro g n
    ext p
    simp only [W, s2, mem_preimage, mem_inter_iff, mem_setOf_eq, Prod.map_fst, Prod.map_snd,
      distinct3_smul3_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by rwa [rel_smul3 g h1] at h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, by rwa [rel_smul3 g h1]⟩
  -- the invariant functions
  set V : ℕ → OnePoint ℝ × OnePoint ℝ → ℝ≥0∞ := fun n q ↦ mk3pair κ q (W n)
  have hVm : ∀ n, Measurable (V n) := fun n ↦ Kernel.measurable_coe _ (hWo n).measurableSet
  have hVinv : ∀ n, ∀ γ ∈ Γ, V n ∘ dact γ =ᵐ[bdry.prod bdry] V n := by
    intro n γ hγ
    filter_upwards [ae_fst (heq γ hγ), ae_snd (heq γ hγ)] with q h1 h2
    simp only [Function.comp, V, dact, mk3pair_apply, mk3_map κ h1, mk3_map κ h2]
    rw [Measure.map_prod_map _ _ (measurable_smul3 _) (measurable_smul3 _),
      Measure.map_apply ((measurable_smul3 _).prodMap (measurable_smul3 _))
        (hWo n).measurableSet, hWinv]
  choose cn hcn using fun n ↦ hΓ.ae_const (hVm n) (hVinv n)
  -- `cn n → c²`
  have hTq : ∀ᵐ q ∂(bdry.prod bdry), Tf q.1 = c ∧ Tf q.2 = c := (ae_fst hc).and (ae_snd hc)
  have hlim : Tendsto cn atTop (𝓝 (c * c)) := by
    obtain ⟨q, hq1, hq2⟩ := exists_of_ae_prod ((ae_all_iff.2 hcn).and hTq)
    have h := tendsto_measure_iUnion_atTop (μ := mk3pair κ q) hWm
    rw [hWU, hs2', mk3pair_apply, Measure.prod_prod, mk3_apply κ measurableSet_D3set,
      mk3_apply κ measurableSet_D3set, inter_self] at h
    rw [show kern3 κ q.1 D3set = c from hq2.1, show kern3 κ q.2 D3set = c from hq2.2] at h
    refine h.congr fun n ↦ ?_
    simp only [Function.comp]
    rw [← mk3pair_apply]; exact hq1 n
  have hcc : c * c ≠ 0 := mul_ne_zero hc0 hc0
  have hcct : c * c ≠ ⊤ := ENNReal.mul_ne_top hct hct
  have h78 : (7 / 8 : ℝ≥0∞) * (c * c) < c * c := by
    conv_rhs => rw [← one_mul (c * c)]
    refine ENNReal.mul_lt_mul_left hcc hcct ?_
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num), one_mul]
    norm_num
  obtain ⟨n₀, hn₀⟩ := (hlim.eventually (lt_mem_nhds h78)).exists
  -- a generic second point
  have hswap : ∀ᵐ q ∂(bdry.prod bdry), V n₀ q.swap = cn n₀ :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae (hcn n₀)
  obtain ⟨x₂, hx₂V, hx₂T⟩ := exists_of_ae ((Measure.ae_ae_of_ae_prod hswap).and hc)
  -- a large compact piece of `mk3 x₂`
  have hcompl : Tendsto (fun n ↦ mk3 κ x₂ (C n)ᶜ) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := mk3 κ x₂) (s := fun n ↦ (C n)ᶜ)
      (fun n ↦ (hC n).measurableSet.compl.nullMeasurableSet)
      (fun m n hmn ↦ compl_subset_compl.2 (hCmono hmn)) ⟨0, measure_ne_top _ _⟩
    rwa [← compl_iUnion, hCU, mk3_apply κ measurableSet_D3set.compl, compl_inter_self,
      measure_empty] at h
  have hc8 : (0 : ℝ≥0∞) < c / 8 := ENNReal.div_pos hc0 (by norm_num)
  obtain ⟨N, hN⟩ := (hcompl.eventually (gt_mem_nhds hc8)).exists
  set E' : Set (Triple k) := (fun p : Triple k × Triple k ↦ G3 p.1 p.2) '' (K N ×ˢ K n₀)
  have hE'c : IsCompact E' :=
    ((hK N).prod (hK n₀)).image_of_continuousOn
      (continuousOn_G3.mono fun p hp ↦ ⟨hKD N hp.1, hKD n₀ hp.2⟩)
  have hE'D : E' ⊆ D3set := by
    rintro _ ⟨p, hp, rfl⟩; exact distinct3_G3 (hKD N hp.1) (hKD n₀ hp.2)
  -- the key estimate
  have hbig : ∀ᵐ x ∂bdry, c / 2 < mk3 κ x E' := by
    filter_upwards [hx₂V, hc] with x₁ hx₁ hTx₁
    set A := mk3 κ x₁ E'
    have hE'm : MeasurableSet E' := hE'c.isClosed.measurableSet
    have e1 : cn n₀ = ∫⁻ t', mk3 κ x₁ ((fun t ↦ (t, t')) ⁻¹' W n₀) ∂(mk3 κ x₂) := by
      rw [← hx₁, ← Measure.prod_apply_symm (hWo n₀).measurableSet]
      simp [V, mk3pair_apply]
    have hpt : ∀ t', mk3 κ x₁ ((fun t ↦ (t, t')) ⁻¹' W n₀) ≤
        (K N).indicator (fun _ ↦ A) t' + (K N)ᶜ.indicator (fun _ ↦ c) t' := by
      intro t'
      by_cases ht' : t' ∈ K N
      · rw [indicator_of_mem ht', indicator_of_notMem (by simpa using ht'), add_zero]
        refine measure_mono fun t ht ↦ ?_
        obtain ⟨⟨h1, h2⟩, h3⟩ := ht
        exact ⟨(t', rel t t'), ⟨ht', hCK n₀ h3⟩, G3_rel h1 h2⟩
      · rw [indicator_of_notMem ht', indicator_of_mem (by simpa using ht'), zero_add]
        calc mk3 κ x₁ _ ≤ mk3 κ x₁ univ := measure_mono (subset_univ _)
          _ = c := by rw [mk3_univ]; exact hTx₁
    have hKm : MeasurableSet (K N) := (hK N).isClosed.measurableSet
    have e2 : ∫⁻ t', ((K N).indicator (fun _ ↦ A) t' + (K N)ᶜ.indicator (fun _ ↦ c) t')
        ∂(mk3 κ x₂) = A * mk3 κ x₂ (K N) + c * mk3 κ x₂ (K N)ᶜ := by
      rw [lintegral_add_left (measurable_const.indicator hKm), lintegral_indicator_const hKm,
        lintegral_indicator_const hKm.compl]
    have hK2 : mk3 κ x₂ (K N) ≤ c := by
      calc mk3 κ x₂ (K N) ≤ mk3 κ x₂ univ := measure_mono (subset_univ _)
        _ = c := by rw [mk3_univ]; exact hx₂T
    have hK2c : mk3 κ x₂ (K N)ᶜ ≤ c / 8 :=
      (measure_mono (compl_subset_compl.2 (hCK N))).trans hN.le
    have hle : cn n₀ ≤ A * c + c * (c / 8) := by
      rw [e1]
      refine (lintegral_mono hpt).trans ?_
      rw [e2]
      gcongr
    have hAle : A ≤ c := by
      calc A ≤ mk3 κ x₁ univ := measure_mono (subset_univ _)
        _ = c := by rw [mk3_univ]; exact hTx₁
    have hAt : A ≠ ⊤ := ne_top_of_le_ne_top hct hAle
    -- real arithmetic
    have hr : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
    have hlt : (7 / 8 : ℝ≥0∞) * (c * c) < A * c + c * (c / 8) := hn₀.trans_le hle
    have hlt' := (ENNReal.toReal_lt_toReal (by
      exact ENNReal.mul_ne_top (ENNReal.div_ne_top (by norm_num) (by norm_num)) hcct) (by
        exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top hAt hct,
          ENNReal.mul_ne_top hct (ENNReal.div_ne_top hct (by norm_num))⟩)).2 hlt
    rw [ENNReal.toReal_add (ENNReal.mul_ne_top hAt hct)
      (ENNReal.mul_ne_top hct (ENNReal.div_ne_top hct (by norm_num))),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_div, ENNReal.toReal_div] at hlt'
    norm_num at hlt'
    rw [← ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hct (by norm_num)) hAt,
      ENNReal.toReal_div]
    norm_num
    nlinarith
  -- every element of `ρ(Γ)` moves `E'` onto itself somewhere
  have hE'm : MeasurableSet E' := hE'c.isClosed.measurableSet
  have hmeet : ∀ γ ∈ Γ, ∃ t ∈ E', smul3 (a γ) t ∈ E' := by
    intro γ hγ
    obtain ⟨x, h1, h2, h3, h4⟩ :=
      exists_of_ae (hbig.and ((ae_smul hbig γ).and ((heq γ hγ).and hc)))
    by_contra hno
    push Not at hno
    have hdisj : Disjoint E' (smul3 (a γ) ⁻¹' E') :=
      Set.disjoint_left.2 fun t ht ht' ↦ hno t ht ht'
    have hpre : mk3 κ x (smul3 (a γ) ⁻¹' E') = mk3 κ (γ • x) E' := by
      rw [mk3_map κ h3, Measure.map_apply (measurable_smul3 _) hE'm]
    have hsum : mk3 κ x E' + mk3 κ x (smul3 (a γ) ⁻¹' E') ≤ c := by
      rw [← measure_union hdisj ((measurable_smul3 _) hE'm)]
      calc _ ≤ mk3 κ x univ := measure_mono (subset_univ _)
        _ = c := by rw [mk3_univ]; exact h4
    rw [hpre] at hsum
    have := ENNReal.add_lt_add h1 h2
    rw [ENNReal.add_halves] at this
    exact absurd (this.trans_le hsum) (lt_irrefl _)
  -- hence `ρ(Γ)(0, 1, ∞)` stays in a compact set of distinct triples
  set Ks : Set (Triple k) := (fun p : Triple k × Triple k ↦ G3 p.1 p.2) '' (E' ×ˢ E')
  have hKs : IsCompact Ks := (hE'c.prod hE'c).image_of_continuousOn
    (continuousOn_G3.mono fun p hp ↦ ⟨hE'D hp.1, hE'D hp.2⟩)
  have hKsD : Ks ⊆ D3set := by
    rintro _ ⟨p, hp, rfl⟩; exact distinct3_G3 (hE'D hp.1) (hE'D hp.2)
  have hin : ∀ γ ∈ Γ, smul3 (a γ) e₃ ∈ Ks := by
    intro γ hγ
    obtain ⟨t, ht, hgt⟩ := hmeet γ hγ
    exact ⟨(smul3 (a γ) t, t), ⟨hgt, ht⟩, G3_smul3 (a γ) (hE'D ht)⟩
  obtain ⟨γs, hγs, τ, hτ, hlimτ⟩ := hunb
  have : τ ∈ Ks := hKs.isClosed.mem_of_tendsto hlimτ
    (Filter.Eventually.of_forall fun n ↦ hin _ (hγs n))
  exact hτ (hKsD this)

end

end OrbicurveCores.M2
