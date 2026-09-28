/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.Superrigid
import OrbicurveCores.M2.Selection
import OrbicurveCores.M2.ThreePoint

/-!
# M2: from the Furstenberg map to a point map

Let `κ : B → Prob(ℙ¹(k))` be a `Γ`-equivariant Markov kernel. The mass of `κ(x)³` on distinct
triples is `Γ`-invariant, hence constant.

* If it is positive, `ρ(Γ)` is bounded (`FromProb`, part S3); this contradicts unboundedness.
* If it vanishes, `κ(x)` is carried by at most two points. The diagonal mass of `κ(x)²` is
  invariant:
  * either `κ(x)` has an atom of mass `> 1/2`, which gives an equivariant measurable point map;
  * or `κ(x) = ½δ_a + ½δ_b`, which gives an equivariant pair map, excluded by `noPair`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology OnePoint.Proj
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

instance polishSpace_onePoint : PolishSpace (OnePoint k) := by
  letI := TopologicalSpace.metrizableSpaceMetric (OnePoint k)
  haveI : CompleteSpace (OnePoint k) := complete_of_compact
  infer_instance

/-- Distinct triples. -/
def D3set : Set (Triple k) := {t | Distinct3 t}

omit [DecidableEq k] in
lemma measurableSet_D3set : MeasurableSet (D3set (k := k)) := isOpen_distinct3.measurableSet

omit [ProperSpace k] in
lemma smul3_preimage_D3set (g : GL (Fin 2) k) : smul3 g ⁻¹' D3set = (D3set (k := k)) := by
  ext t
  simp only [D3set, mem_preimage, mem_setOf_eq, Distinct3, smul3, ne_eq, smul_left_cancel_iff]

omit [DecidableEq k] in
/-- A probability measure whose cube does not charge distinct triples is carried by two
points. -/
lemma exists_pair_of_triple_null {μ : Measure (OnePoint k)} [IsProbabilityMeasure μ]
    (h : (μ.prod (μ.prod μ)) D3set = 0) : ∃ a b : OnePoint k, μ ({a, b}ᶜ) = 0 := by
  by_contra hab
  push Not at hab
  obtain ⟨a, -, ha⟩ := Measure.nonempty_inter_support_of_pos (μ := μ) (s := univ)
    (by simp)
  obtain ⟨b, hb, hbs⟩ := Measure.nonempty_inter_support_of_pos (μ := μ)
    (s := ({a} : Set (OnePoint k))ᶜ) (pos_iff_ne_zero.2 (by simpa using hab a a))
  obtain ⟨c, hc, hcs⟩ := Measure.nonempty_inter_support_of_pos (μ := μ)
    (s := ({a, b} : Set (OnePoint k))ᶜ) (pos_iff_ne_zero.2 (hab a b))
  have hab' : a ≠ b := fun e ↦ hb (by simp [e])
  have hac : a ≠ c := fun e ↦ hc (by simp [e])
  have hbc : b ≠ c := fun e ↦ hc (by simp [e])
  obtain ⟨U₁, V₁, hU₁, hV₁, haU₁, hbV₁, d₁⟩ := t2_separation hab'
  obtain ⟨U₂, W₁, hU₂, hW₁, haU₂, hcW₁, d₂⟩ := t2_separation hac
  obtain ⟨V₂, W₂, hV₂, hW₂, hbV₂, hcW₂, d₃⟩ := t2_separation hbc
  set A := U₁ ∩ U₂; set B := V₁ ∩ V₂; set C := W₁ ∩ W₂
  have hA : 0 < μ A := (Measure.mem_support_iff_forall a).1 ha A
    ((hU₁.inter hU₂).mem_nhds ⟨haU₁, haU₂⟩)
  have hB : 0 < μ B := (Measure.mem_support_iff_forall b).1 hbs B
    ((hV₁.inter hV₂).mem_nhds ⟨hbV₁, hbV₂⟩)
  have hC : 0 < μ C := (Measure.mem_support_iff_forall c).1 hcs C
    ((hW₁.inter hW₂).mem_nhds ⟨hcW₁, hcW₂⟩)
  have hsub : A ×ˢ (B ×ˢ C) ⊆ D3set := by
    rintro ⟨x, y, z⟩ ⟨hx, hy, hz⟩
    refine ⟨fun e ↦ ?_, fun e ↦ ?_, fun e ↦ ?_⟩
    · exact d₁.le_bot ⟨hx.1, e ▸ hy.1⟩
    · exact d₂.le_bot ⟨hx.2, e ▸ hz.1⟩
    · exact d₃.le_bot ⟨hy.2, e ▸ hz.2⟩
  have := measure_mono (μ := μ.prod (μ.prod μ)) hsub
  rw [h, Measure.prod_prod, Measure.prod_prod, nonpos_iff_eq_zero] at this
  simp only [mul_eq_zero] at this
  rcases this with h0 | h0 | h0
  · exact hA.ne' h0
  · exact hB.ne' h0
  · exact hC.ne' h0

section twoPoint

variable {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma eq_two_point {μ : Measure Y} {a b : Y} (hab : a ≠ b) (h : μ ({a, b}ᶜ) = 0) :
    μ = μ {a} • Measure.dirac a + μ {b} • Measure.dirac b := by
  ext s hs
  rw [← measure_inter_conull (s := s) h, Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.dirac_apply' _ hs, Measure.dirac_apply' _ hs]
  by_cases ha : a ∈ s <;> by_cases hb : b ∈ s
  · rw [show s ∩ {a, b} = {a} ∪ {b} by ext; simp; grind,
      measure_union (disjoint_singleton.2 hab) (measurableSet_singleton b)]
    simp [ha, hb]
  · rw [show s ∩ {a, b} = {a} by ext; simp; grind]; simp [ha, hb]
  · rw [show s ∩ {a, b} = {b} by ext; simp; grind]; simp [ha, hb]
  · rw [show s ∩ {a, b} = ∅ by ext; simp; grind]; simp [ha, hb]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] [MeasurableSingletonClass Y] in
lemma prod_diagonal_eq [MeasurableEq Y] (μ : Measure Y) [SFinite μ] :
    (μ.prod μ) (diagonal Y) = ∫⁻ x, μ {x} ∂μ := by
  rw [Measure.prod_apply measurableSet_diagonal]
  congr 1; ext x
  congr 1; ext y; simp [eq_comm]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma two_point_diag [MeasurableEq Y] {μ : Measure Y}
    [IsProbabilityMeasure μ] {a b : Y} (hab : a ≠ b) (h : μ ({a, b}ᶜ) = 0) :
    (μ.prod μ) (diagonal Y) = μ {a} ^ 2 + μ {b} ^ 2 := by
  rw [prod_diagonal_eq, congrArg (fun ν ↦ ∫⁻ x, μ {x} ∂ν) (eq_two_point hab h)]
  rw [lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, lintegral_dirac,
    lintegral_dirac, smul_eq_mul, smul_eq_mul, sq, sq]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma two_point_sum {μ : Measure Y} [IsProbabilityMeasure μ] {a b : Y} (hab : a ≠ b)
    (h : μ ({a, b}ᶜ) = 0) : μ {a} + μ {b} = 1 := by
  rw [← measure_union (disjoint_singleton.2 hab) (measurableSet_singleton b),
    show ({a} : Set Y) ∪ {b} = {a, b} by ext; simp [or_comm]]
  exact (prob_compl_eq_zero_iff ((measurableSet_singleton a).insert a |> fun _ ↦
    (measurableSet_singleton b).insert a)).1 h

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
/-- Two-point measures with diagonal mass `> 1/2` have a heavy atom. -/
lemma two_point_heavy [MeasurableEq Y] {μ : Measure Y}
    [IsProbabilityMeasure μ] {a b : Y} (h : μ ({a, b}ᶜ) = 0)
    (hφ : 1 / 2 < (μ.prod μ) (diagonal Y)) : ∃ z, 1 / 2 < μ {z} := by
  by_cases hab : a = b
  · subst hab
    refine ⟨a, ?_⟩
    have : μ {a} = 1 := by
      rw [← prob_compl_eq_zero_iff (measurableSet_singleton a)]; simpa using h
    rw [this]; norm_num
  · rw [two_point_diag hab h] at hφ
    have hs := two_point_sum hab h
    by_contra hno
    push Not at hno
    have ha := hno a; have hb := hno b
    have hpa : μ {a} ≠ ⊤ := measure_ne_top _ _
    have hpb : μ {b} ≠ ⊤ := measure_ne_top _ _
    have e : μ {a} ^ 2 + μ {b} ^ 2 ≤ 1 / 2 := by
      have hs' : (μ {a}).toReal + (μ {b}).toReal = 1 := by
        rw [← ENNReal.toReal_add hpa hpb, hs, ENNReal.toReal_one]
      have ha' : (μ {a}).toReal ≤ 1 / 2 := by
        have := ENNReal.toReal_mono (by norm_num) ha; simpa using this
      have hb' : (μ {b}).toReal ≤ 1 / 2 := by
        have := ENNReal.toReal_mono (by norm_num) hb; simpa using this
      rw [← ENNReal.ofReal_toReal hpa, ← ENNReal.ofReal_toReal hpb,
        ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [show (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2) by simp]
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [ENNReal.toReal_nonneg (a := μ {a}), ENNReal.toReal_nonneg (a := μ {b})]
    exact absurd hφ (not_lt.2 e)

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
/-- Two-point measures with diagonal mass `≤ 1/2` are `½δ_a + ½δ_b` with `a ≠ b`. -/
lemma two_point_pair [MeasurableEq Y] {μ : Measure Y}
    [IsProbabilityMeasure μ] {a b : Y} (h : μ ({a, b}ᶜ) = 0)
    (hφ : (μ.prod μ) (diagonal Y) ≤ 1 / 2) : a ≠ b ∧ μ {a} = 1 / 2 ∧ μ {b} = 1 / 2 := by
  have hab : a ≠ b := by
    rintro rfl
    have h1 : μ {a} = 1 := by
      rw [← prob_compl_eq_zero_iff (measurableSet_singleton a)]; simpa using h
    have h2 : (μ.prod μ) ({a} ×ˢ {a}) ≤ (μ.prod μ) (diagonal Y) :=
      measure_mono (by rintro ⟨x, y⟩ ⟨hx, hy⟩; simp_all [diagonal])
    rw [Measure.prod_prod, h1, one_mul] at h2
    exact absurd (h2.trans hφ) (by norm_num)
  refine ⟨hab, ?_⟩
  rw [two_point_diag hab h] at hφ
  have hs := two_point_sum hab h
  have hpa : μ {a} ≠ ⊤ := measure_ne_top _ _
  have hpb : μ {b} ≠ ⊤ := measure_ne_top _ _
  have hs' : (μ {a}).toReal + (μ {b}).toReal = 1 := by
    rw [← ENNReal.toReal_add hpa hpb, hs, ENNReal.toReal_one]
  have hφ' : (μ {a}).toReal ^ 2 + (μ {b}).toReal ^ 2 ≤ 1 / 2 := by
    have := ENNReal.toReal_mono (by norm_num) hφ
    rwa [ENNReal.toReal_add (by simp [hpa]) (by simp [hpb]), ENNReal.toReal_pow,
      ENNReal.toReal_pow, show ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 by norm_num] at this
  have hA : (μ {a}).toReal = 1 / 2 := by nlinarith [sq_nonneg ((μ {a}).toReal - (μ {b}).toReal)]
  have hB : (μ {b}).toReal = 1 / 2 := by linarith
  refine ⟨?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hpa, hA, ENNReal.ofReal_div_of_pos two_pos]; simp
  · rw [← ENNReal.ofReal_toReal hpb, hB, ENNReal.ofReal_div_of_pos two_pos]; simp

end twoPoint

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma eq_smul_dirac_of_compl_null {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {ν : Measure Y} {z : Y} (h : ν ({z}ᶜ) = 0) : ν = ν {z} • Measure.dirac z := by
  ext s hs
  rw [← measure_inter_conull (s := s) h, Measure.smul_apply, Measure.dirac_apply' _ hs,
    smul_eq_mul]
  by_cases hz : z ∈ s
  · rw [show s ∩ {z} = {z} by ext; simp; grind]; simp [hz]
  · rw [show s ∩ {z} = ∅ by ext; simp; grind]; simp [hz]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma heavy_unique {Y : Type*} [MeasurableSpace Y] [MeasurableSingletonClass Y]
    {μ : Measure Y} [IsProbabilityMeasure μ] {p q : Y} (hp : 1 / 2 < μ {p})
    (hq : 1 / 2 < μ {q}) : p = q := by
  by_contra hpq
  have h1 : μ {p} + μ {q} ≤ 1 := by
    rw [← measure_union (disjoint_singleton.2 hpq) (measurableSet_singleton q)]
    exact prob_le_one
  have := ENNReal.add_lt_add hp hq
  rw [ENNReal.add_halves] at this
  exact absurd (this.trans_le h1) (lt_irrefl _)

section kernel

variable {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}

/-- The kernel `x ↦ κ(x)²`. -/
noncomputable abbrev kern2 (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] :
    Kernel (OnePoint ℝ) (OnePoint k × OnePoint k) := κ ×ₖ κ

/-- The kernel `x ↦ κ(x)³`. -/
noncomputable abbrev kern3 (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] :
    Kernel (OnePoint ℝ) (Triple k) := κ ×ₖ (κ ×ₖ κ)

lemma measurable_gl_smul (g : GL (Fin 2) k) : Measurable fun y : OnePoint k ↦ g • y :=
  (continuous_gl_smul g).measurable

lemma kern_map (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] {x y : OnePoint ℝ}
    {g : GL (Fin 2) k} (h : κ y = (κ x).map (fun z ↦ g • z)) :
    kern2 κ y = (kern2 κ x).map (Prod.map (fun z ↦ g • z) (fun z ↦ g • z)) ∧
      kern3 κ y = (kern3 κ x).map (smul3 g) := by
  have hm := measurable_gl_smul g
  constructor
  · rw [Kernel.prod_apply, Kernel.prod_apply, h, Measure.map_prod_map _ _ hm hm]
  · rw [Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply, Kernel.prod_apply, h,
      Measure.map_prod_map _ _ hm hm, Measure.map_prod_map _ _ hm (hm.prodMap hm)]
    rfl

omit [ProperSpace k] [DecidableEq k] in
lemma kern3_apply (κ : Kernel (OnePoint ℝ) (OnePoint k)) [IsMarkovKernel κ] (x : OnePoint ℝ) :
    kern3 κ x = (κ x).prod ((κ x).prod (κ x)) := by
  rw [Kernel.prod_apply, Kernel.prod_apply]

variable [MeasurableSpace k] [BorelSpace k]

/-- **From a two-point Furstenberg map to a point map.** If `κ(x)³` does not charge distinct
triples, there is an equivariant measurable point map. -/
theorem exists_pointMap_of_triple_null [Countable Γ] (hΓ : IsDoublyErgodic Γ)
    (hact : ActsOn Γ a) (hne : NonElem Γ a) (κ : Kernel (OnePoint ℝ) (OnePoint k))
    [IsMarkovKernel κ]
    (heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, κ (γ • x) = (κ x).map (fun y ↦ a γ • y))
    (hT : ∀ᵐ x ∂bdry, kern3 κ x D3set = 0) :
    ∃ ψ : OnePoint ℝ → OnePoint k, Measurable ψ ∧ Equivariant Γ a ψ := by
  classical
  have hsupp : ∀ x, kern3 κ x D3set = 0 → ∃ p q : OnePoint k, κ x ({p, q}ᶜ) = 0 := by
    intro x hx
    rw [kern3_apply] at hx
    exact exists_pair_of_triple_null hx
  set φ : OnePoint ℝ → ℝ≥0∞ := fun x ↦ kern2 κ x (diagonal (OnePoint k))
  have hφ : Measurable φ := Kernel.measurable_coe _ measurableSet_diagonal
  have hφinv : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, φ (γ • x) = φ x := by
    intro γ hγ
    filter_upwards [heq γ hγ] with x hx
    have hm := measurable_gl_smul (a γ)
    simp only [φ, (kern_map κ hx).1]
    rw [Measure.map_apply (hm.prodMap hm) measurableSet_diagonal]
    congr 1
    ext ⟨y, z⟩
    simp [diagonal]
  obtain ⟨d, hd⟩ := hΓ.ae_const_single hφ hφinv
  have hT3 : MeasurableSet {x | kern3 κ x D3set = 0} :=
    Kernel.measurable_coe _ measurableSet_D3set (measurableSet_singleton 0)
  by_cases hd' : 1 / 2 < d
  · -- heavy atoms
    set S := {x | 1 / 2 < φ x} ∩ {x | kern3 κ x D3set = 0}
    have hS : MeasurableSet S := (measurableSet_lt measurable_const hφ).inter hT3
    have hSae : ∀ᵐ x ∂bdry, x ∈ S := by
      filter_upwards [hd, hT] with x h1 h2
      exact ⟨by simpa [φ, h1] using hd', h2⟩
    obtain ⟨f, hf, hfS⟩ := exists_measurable_heavy_selection κ hS fun x hx ↦ by
      obtain ⟨p, q, hpq⟩ := hsupp x hx.2
      have := hx.1
      simp only [φ, Kernel.prod_apply] at this
      exact two_point_heavy hpq this
    refine ⟨f, hf, fun γ hγ ↦ ?_⟩
    filter_upwards [hSae, ae_smul hSae γ, heq γ hγ] with x hx hγx hκ
    refine heavy_unique (μ := κ (γ • x)) (hfS _ hγx) ?_
    rw [hκ, Measure.map_apply (measurable_gl_smul _) (measurableSet_singleton _)]
    have : (fun y ↦ a γ • y) ⁻¹' {a γ • f x} = {f x} := by
      ext y; simp
    rw [this]; exact hfS x hx
  · -- pairs of half atoms
    exfalso
    obtain ⟨e, he⟩ := exists_measurableEmbedding_real (α := OnePoint k)
    set L : Set (OnePoint k × OnePoint k) := {p | e p.1 < e p.2}
    have hL : MeasurableSet L :=
      measurableSet_lt (he.measurable.comp measurable_fst) (he.measurable.comp measurable_snd)
    set S := {x | φ x ≤ 1 / 2} ∩ {x | kern3 κ x D3set = 0}
    have hS : MeasurableSet S := (measurableSet_le hφ measurable_const).inter hT3
    have hSae : ∀ᵐ x ∂bdry, x ∈ S := by
      filter_upwards [hd, hT] with x h1 h2
      exact ⟨by simpa [φ, h1] using not_lt.1 hd', h2⟩
    set ρ := Kernel.restrict (kern2 κ) hL
    -- the structure of `κ x` on `S`
    have hstr : ∀ x ∈ S, ∃ p q : OnePoint k, p ≠ q ∧ κ x {p} = 1 / 2 ∧ κ x {q} = 1 / 2 ∧
        κ x ({p, q}ᶜ) = 0 := by
      intro x hx
      obtain ⟨p, q, hpq⟩ := hsupp x hx.2
      have h1 := hx.1
      simp only [φ, Kernel.prod_apply] at h1
      obtain ⟨h2, h3, h4⟩ := two_point_pair hpq h1
      exact ⟨p, q, h2, h3, h4, hpq⟩
    have hsupp' : ∀ x ∈ S, ∀ p q : OnePoint k, p ≠ q → κ x {p} = 1 / 2 → κ x {q} = 1 / 2 →
        κ x ({p, q}ᶜ) = 0 → {y | κ x {y} ≠ 0} = {p, q} := by
      intro x _ p q _ hp hq hc
      ext y
      simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
      constructor
      · intro hy
        by_contra hy'
        push Not at hy'
        exact hy (measure_mono_null (by simpa using hy') hc)
      · rintro (rfl | rfl) <;> simp [hp, hq]
    -- `ρ x` is a multiple of a Dirac mass at the ordered pair
    have hdirac : ∀ x ∈ S, ∃ z, ∃ c : ℝ≥0∞, c ≠ 0 ∧ ρ x = c • Measure.dirac z := by
      intro x hx
      obtain ⟨p, q, hpq, hp, hq, hc⟩ := hstr x hx
      have hepq : e p ≠ e q := fun h ↦ hpq (he.injective h)
      set z : OnePoint k × OnePoint k := if e p < e q then (p, q) else (q, p)
      have hzL : z ∈ L := by
        simp only [z, L, mem_setOf_eq]
        split_ifs with h
        · exact h
        · exact lt_of_le_of_ne (not_lt.1 h) (Ne.symm hepq)
      have hnull : ρ x ({z}ᶜ) = 0 := by
        rw [Kernel.restrict_apply' _ hL _ (measurableSet_singleton z).compl, Kernel.prod_apply]
        refine measure_mono_null (t := (({p, q} : Set (OnePoint k))ᶜ ×ˢ univ) ∪
          (univ ×ˢ ({p, q} : Set (OnePoint k))ᶜ)) ?_ (measure_union_null ?_ ?_)
        · rintro ⟨y₁, y₂⟩ ⟨hz, hyL⟩
          by_contra hno
          have h1 : y₁ ∈ ({p, q} : Set (OnePoint k)) := by
            by_contra h; exact hno (Or.inl ⟨h, mem_univ _⟩)
          have h2 : y₂ ∈ ({p, q} : Set (OnePoint k)) := by
            by_contra h; exact hno (Or.inr ⟨mem_univ _, h⟩)
          simp only [mem_insert_iff, mem_singleton_iff] at h1 h2
          simp only [L, mem_setOf_eq] at hyL
          apply hz
          simp only [mem_singleton_iff, z]
          rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
          · exact absurd hyL (lt_irrefl _)
          · simp [hyL]
          · simp [not_lt.2 hyL.le]
          · exact absurd hyL (lt_irrefl _)
        · rw [Measure.prod_prod, hc, zero_mul]
        · rw [Measure.prod_prod, hc, mul_zero]
      refine ⟨z, ρ x {z}, ?_, eq_smul_dirac_of_compl_null hnull⟩
      rw [Kernel.restrict_apply' _ hL _ (measurableSet_singleton z), Kernel.prod_apply,
        inter_eq_left.2 (singleton_subset_iff.2 hzL), show ({z} : Set _) = {z.1} ×ˢ {z.2} by
          ext; simp [Prod.ext_iff], Measure.prod_prod]
      have h1 : κ x {z.1} = 1 / 2 := by simp only [z]; split_ifs <;> assumption
      have h2 : κ x {z.2} = 1 / 2 := by simp only [z]; split_ifs <;> assumption
      rw [h1, h2]; simp
    obtain ⟨w, hw, hwS⟩ := exists_measurable_dirac_selection ρ hS hdirac
    set u := fun x ↦ (w x).1
    set v := fun x ↦ (w x).2
    -- on `S`, `{u x, v x}` is the support of `κ x`
    have hkey : ∀ x ∈ S, u x ≠ v x ∧ pairAt u v x = {y | κ x {y} ≠ 0} := by
      intro x hx
      obtain ⟨c, hc0, hcx⟩ := hwS x hx
      obtain ⟨p, q, hpq, hp, hq, hc⟩ := hstr x hx
      have hwL : w x ∈ L := by
        by_contra hno
        have : ρ x {w x} = 0 := by
          rw [Kernel.restrict_apply' _ hL _ (measurableSet_singleton _)]
          simp [singleton_inter_eq_empty.2 hno]
        rw [hcx] at this; simp [hc0] at this
      have hpos : ρ x {w x} ≠ 0 := by rw [hcx]; simp [hc0]
      rw [Kernel.restrict_apply' _ hL _ (measurableSet_singleton _), Kernel.prod_apply,
        show ({w x} : Set _) ∩ L = {(w x).1} ×ˢ {(w x).2} by
          rw [inter_eq_left.2 (singleton_subset_iff.2 hwL)]; ext; simp [Prod.ext_iff],
        Measure.prod_prod] at hpos
      have hu0 : κ x {u x} ≠ 0 := left_ne_zero_of_mul hpos
      have hv0 : κ x {v x} ≠ 0 := right_ne_zero_of_mul hpos
      have hs := hsupp' x hx p q hpq hp hq hc
      have huv : u x ≠ v x := fun h ↦ by
        have : e (w x).1 < e (w x).2 := hwL
        simp only [u, v] at h
        rw [h] at this; exact lt_irrefl _ this
      refine ⟨huv, ?_⟩
      rw [hs]
      have hu' : u x ∈ ({p, q} : Set (OnePoint k)) := hs ▸ hu0
      have hv' : v x ∈ ({p, q} : Set (OnePoint k)) := hs ▸ hv0
      simp only [mem_insert_iff, mem_singleton_iff] at hu' hv'
      simp only [pairAt]
      rcases hu' with h1 | h1 <;> rcases hv' with h2 | h2
      · exact absurd (h1.trans h2.symm) huv
      · rw [h1, h2]
      · rw [h1, h2, pair_comm]
      · exact absurd (h1.trans h2.symm) huv
    refine noPair hΓ hne hact hw.fst hw.snd (hSae.mono fun x hx ↦ (hkey x hx).1) ?_
    intro γ hγ
    filter_upwards [hSae, ae_smul hSae γ, heq γ hγ] with x hx hγx hκ
    rw [(hkey _ hγx).2, (hkey _ hx).2, hκ]
    ext y
    simp only [mem_setOf_eq, Set.mem_smul_set_iff_inv_smul_mem,
      Measure.map_apply (measurable_gl_smul _) (measurableSet_singleton _)]
    have : (fun z ↦ a γ • z) ⁻¹' {y} = {(a γ)⁻¹ • y} := by
      ext z; simp [eq_inv_smul_iff]
    rw [this]

end kernel

end OrbicurveCores.M2
