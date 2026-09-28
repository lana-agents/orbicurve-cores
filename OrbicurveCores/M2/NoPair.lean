/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.PointMaps

/-!
# M2: no equivariant maps to unordered pairs

`noPair`: let `Γ` be countable and doubly ergodic, acting on `ℙ¹(k)` through `a` with no
finite-index subgroup fixing a point. Then there are no measurable `u v : B → ℙ¹(k)` with
`u ≠ v` a.e. such that the unordered pair `{u, v}` is equivariant.

* If the pairs of two generic points meet, the weights `w(y) = ν{x : y ∈ {u x, v x}}` single out
  a finite set of points meeting every pair. Then B. H. Neumann's lemma produces a finite-index
  stabiliser.
* If they are generically disjoint, the invariant `wcr + wcr⁻¹` of two pairs is constant. Two
  generic reference pairs then confine `u` to a finite set, which contradicts disjointness.
-/

open MeasureTheory Filter Set
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]

/-- The unordered pair `{u x, v x}`. -/
def pairAt (u v : OnePoint ℝ → OnePoint k) (x : OnePoint ℝ) : Set (OnePoint k) := {u x, v x}

/-- The stabiliser of a point, as a subgroup of `Γ`. -/
def stab {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (hact : ActsOn Γ a)
    (y : OnePoint k) : Subgroup Γ where
  carrier := {g | a g • y = y}
  mul_mem' {g h} hg hh := by
    change a (g * h : SL(2, ℝ)) • y = y
    rw [hact _ g.2 _ h.2]
    rw [show a h • y = y from hh]; exact hg
  one_mem' := hact.one y
  inv_mem' {g} hg := by
    change a (g⁻¹ : SL(2, ℝ)) • y = y
    conv_lhs => rw [← show a g • y = y from hg]
    exact hact.inv g.2 y

omit [ProperSpace k] in
/-- A finite-index stabiliser contradicts `NonElem`. -/
lemma NonElem.not_finiteIndex_stab {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k}
    (hne : NonElem Γ a) (hact : ActsOn Γ a) (y : OnePoint k) (hfi : (stab hact y).FiniteIndex) :
    False := by
  set Γ' := (stab hact y).map Γ.subtype
  have hle : Γ' ≤ Γ := by
    rintro _ ⟨g, -, rfl⟩; exact g.2
  have hsub : Γ'.subgroupOf Γ = stab hact y := by
    ext g
    simp only [Subgroup.mem_subgroupOf, Γ', Subgroup.mem_map, Subgroup.coe_subtype]
    constructor
    · rintro ⟨h, hh, e⟩; rwa [Subtype.ext e] at hh
    · intro hg; exact ⟨g, hg, rfl⟩
  have hri : Γ'.relIndex Γ ≠ 0 := by
    rw [Subgroup.relIndex, hsub]; exact hfi.index_ne_zero
  obtain ⟨γ, hγ, hne'⟩ := hne Γ' hle hri y
  obtain ⟨g, hg, rfl⟩ := hγ
  exact hne' hg

section

variable {Γ : Subgroup SL(2, ℝ)} [Countable Γ] {a : SL(2, ℝ) → GL (Fin 2) k}
  {u v : OnePoint ℝ → OnePoint k}

lemma cauchy_ne_zero : cauchy ≠ 0 := fun h ↦
  bdry_ne_zero (Measure.measure_univ_eq_zero.1 (bdry_absolutelyContinuous_cauchy (by simp [h])))

omit [DecidableEq k] [ProperSpace k] in
lemma measurableSet_mem_pairAt (hu : Measurable u) (hv : Measurable v) (y : OnePoint k) :
    MeasurableSet {x | y ∈ pairAt u v x} := by
  have : {x | y ∈ pairAt u v x} = u ⁻¹' {y} ∪ v ⁻¹' {y} := by
    ext x; simp [pairAt, eq_comm]
  rw [this]
  exact (hu (measurableSet_singleton y)).union (hv (measurableSet_singleton y))

omit [DecidableEq k] [ProperSpace k] in
/-- At most two points meet any given pair: the weights sum to at most `2 ν(B)`. -/
lemma sum_weight_le (hu : Measurable u) (hv : Measurable v) (T : Finset (OnePoint k)) :
    ∑ y ∈ T, cauchy {x | y ∈ pairAt u v x} ≤ 2 * cauchy univ := by
  classical
  have e : ∀ y ∈ T, cauchy {x | y ∈ pairAt u v x} =
      ∫⁻ x, {x | y ∈ pairAt u v x}.indicator 1 x ∂cauchy := fun y _ ↦
    (lintegral_indicator_one (measurableSet_mem_pairAt hu hv y)).symm
  rw [Finset.sum_congr rfl e, ← lintegral_finsetSum' _ fun y _ ↦
    (measurable_one.indicator (measurableSet_mem_pairAt hu hv y)).aemeasurable]
  calc ∫⁻ x, ∑ y ∈ T, {x | y ∈ pairAt u v x}.indicator 1 x ∂cauchy
      ≤ ∫⁻ _, (2 : ℝ≥0∞) ∂cauchy := by
        refine lintegral_mono fun x ↦ ?_
        have : ∑ y ∈ T, {x | y ∈ pairAt u v x}.indicator (1 : OnePoint ℝ → ℝ≥0∞) x =
            ((T.filter fun y ↦ y ∈ pairAt u v x).card : ℝ≥0∞) := by
          rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun y _ ↦ ?_
          by_cases h : y ∈ pairAt u v x <;> simp [h]
        rw [this]
        have hc : (T.filter fun y ↦ y ∈ pairAt u v x).card ≤ 2 := by
          calc (T.filter fun y ↦ y ∈ pairAt u v x).card ≤ ({u x, v x} : Finset _).card := by
                refine Finset.card_le_card fun y hy ↦ ?_
                have := (Finset.mem_filter.1 hy).2
                simp only [pairAt, mem_insert_iff, mem_singleton_iff] at this
                simp [this]
            _ ≤ 2 := Finset.card_le_two
        exact (Nat.cast_le.2 hc).trans_eq (by norm_num)
    _ = 2 * cauchy univ := by rw [lintegral_const]

omit [ProperSpace k] in
/-- **NoPair, meeting case.** If the pairs of almost every two points meet, some finite-index
subgroup has a fixed point. -/
theorem noPair_meet (hne : NonElem Γ a) (hact : ActsOn Γ a) (hu : Measurable u)
    (hv : Measurable v)
    (heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, pairAt u v (γ • x) = a γ • pairAt u v x)
    (hmeet : ∀ᵐ q ∂(bdry.prod bdry), (pairAt u v q.1 ∩ pairAt u v q.2).Nonempty) : False := by
  classical
  set c := cauchy univ
  have hc0 : c ≠ 0 := fun h ↦ cauchy_ne_zero (Measure.measure_univ_eq_zero.1 h)
  have hct : c ≠ ⊤ := measure_ne_top _ _
  set w : OnePoint k → ℝ≥0∞ := fun y ↦ cauchy {x | y ∈ pairAt u v x}
  -- (iii) generic pairs carry weight at least `c`
  have h3 : ∀ᵐ x₁ ∂bdry, c ≤ w (u x₁) + w (v x₁) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hmeet] with x₁ hx₁
    have hx₁' : ∀ᵐ x₂ ∂cauchy, (pairAt u v x₁ ∩ pairAt u v x₂).Nonempty :=
      cauchy_absolutelyContinuous_bdry.ae_le hx₁
    calc c = cauchy univ := rfl
      _ ≤ cauchy ({x | u x₁ ∈ pairAt u v x} ∪ {x | v x₁ ∈ pairAt u v x}) := by
          refine measure_mono_ae (hx₁'.mono fun x₂ hx₂ _ ↦ ?_)
          obtain ⟨y, hy1, hy2⟩ := hx₂
          simp only [pairAt, mem_insert_iff, mem_singleton_iff] at hy1
          rcases hy1 with rfl | rfl
          · exact Or.inl hy2
          · exact Or.inr hy2
      _ ≤ w (u x₁) + w (v x₁) := measure_union_le _ _
  -- (iv) the heavy points form a finite set
  set F := {y : OnePoint k | c / 2 ≤ w y}
  have hF : F.Finite := by
    by_contra hinf
    obtain ⟨T, hTF, hT⟩ := Set.Infinite.exists_subset_card_eq hinf 5
    have hsum := sum_weight_le hu hv T
    have : (5 : ℝ≥0∞) * (c / 2) ≤ 2 * c := by
      calc (5 : ℝ≥0∞) * (c / 2) = ∑ _y ∈ T, c / 2 := by rw [Finset.sum_const, hT]; simp
        _ ≤ ∑ y ∈ T, w y := Finset.sum_le_sum fun y hy ↦ hTF hy
        _ ≤ 2 * c := hsum
    have h' : (5 : ℝ≥0∞) * (c / 2) = 5 / 2 * c := by
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]; ring
    rw [h'] at this
    have := (ENNReal.mul_le_mul_iff_left hc0 hct).1 this
    exact absurd this (by norm_num [ENNReal.div_le_iff])
  -- (v) generic pairs meet `F`
  have h5 : ∀ᵐ x ∂bdry, ∃ y ∈ F, y ∈ pairAt u v x := by
    filter_upwards [h3] with x hx
    by_contra hno
    push Not at hno
    have h1 : w (u x) < c / 2 := lt_of_not_ge fun h ↦ hno (u x) h (by simp [pairAt])
    have h2 : w (v x) < c / 2 := lt_of_not_ge fun h ↦ hno (v x) h (by simp [pairAt])
    have := ENNReal.add_lt_add h1 h2
    rw [ENNReal.add_halves] at this
    exact absurd hx (not_le.2 this)
  -- (vi) and (vii): a generic pair meets every translate `a γ F`
  have h6 : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, ∃ y ∈ F, a γ • y ∈ pairAt u v x := by
    intro γ hγ
    filter_upwards [ae_smul h5 γ⁻¹, ae_smul (heq γ hγ) γ⁻¹] with x hx1 hx2
    rw [smul_inv_smul] at hx2
    obtain ⟨y, hyF, hy⟩ := hx1
    exact ⟨y, hyF, hx2 ▸ Set.smul_mem_smul_set hy⟩
  have h7 : ∀ᵐ x ∂bdry, ∀ γ : Γ, ∃ y ∈ F, a γ • y ∈ pairAt u v x :=
    ae_all_iff.2 fun γ ↦ h6 γ γ.2
  obtain ⟨x₀, hx₀⟩ := exists_of_ae h7
  -- (ix) Neumann's lemma
  set T : Finset (OnePoint k × Bool) := hF.toFinset ×ˢ Finset.univ
  let tgt : Bool → OnePoint k := fun b ↦ if b then u x₀ else v x₀
  let g : OnePoint k × Bool → Γ := fun i ↦
    if h : ∃ γ : Γ, a γ • i.1 = tgt i.2 then h.choose else 1
  have hcov : ⋃ i ∈ T, g i • (stab hact i.1 : Set Γ) = Set.univ := by
    refine Set.eq_univ_of_forall fun γ ↦ ?_
    obtain ⟨y, hyF, hy⟩ := hx₀ γ
    have hb : ∃ b : Bool, a γ • y = tgt b := by
      simp only [pairAt, mem_insert_iff, mem_singleton_iff] at hy
      rcases hy with h | h
      · exact ⟨true, by simp [tgt, h]⟩
      · exact ⟨false, by simp [tgt, h]⟩
    obtain ⟨b, hb⟩ := hb
    have hex : ∃ γ' : Γ, a γ' • y = tgt b := ⟨γ, hb⟩
    refine mem_iUnion₂.2 ⟨(y, b), Finset.mem_product.2 ⟨hF.mem_toFinset.2 hyF,
      Finset.mem_univ _⟩, ?_⟩
    have hg : g (y, b) = hex.choose := by simp only [g, dif_pos hex]
    have hgy : a (g (y, b)) • y = tgt b := by rw [hg]; exact hex.choose_spec
    refine ⟨(g (y, b))⁻¹ * γ, ?_, by simp⟩
    change a ((g (y, b))⁻¹ * γ : SL(2, ℝ)) • y = y
    rw [InvMemClass.coe_inv, hact _ (inv_mem (g (y, b)).2) _ γ.2, hb, ← hgy]
    exact hact.inv (g (y, b)).2 y
  obtain ⟨i, -, hi⟩ := Subgroup.exists_finiteIndex_of_leftCoset_cover hcov
  exact hne.not_finiteIndex_stab hact i.1 hi

omit [ProperSpace k] [DecidableEq k] in
lemma eq_or_eq_inv_of_add_inv {w c : k} (hw : w ≠ 0) (hc : c ≠ 0) (h : w + w⁻¹ = c + c⁻¹) :
    w = c ∨ w = c⁻¹ := by
  have : (w - c) * (w - c⁻¹) = 0 := by
    have e : (w - c) * (w - c⁻¹) = w * (w + w⁻¹ - (c + c⁻¹)) := by field_simp; ring
    rw [e, h, sub_self, mul_zero]
  rcases mul_eq_zero.1 this with h1 | h1
  · exact Or.inl (sub_eq_zero.1 h1)
  · exact Or.inr (sub_eq_zero.1 h1)

/-- The symmetric invariant of two pairs. -/
def jcr (y₁ y₂ y₃ y₄ : OnePoint k) : k := wcr y₁ y₂ y₃ y₄ + (wcr y₁ y₂ y₃ y₄)⁻¹

omit [ProperSpace k] [DecidableEq k] in
lemma jcr_swap₁₂ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    jcr y₂ y₁ y₃ y₄ = jcr y₁ y₂ y₃ y₄ := by
  simp only [jcr, wcr_swap₁₂ h, inv_inv]; ring

omit [ProperSpace k] [DecidableEq k] in
lemma jcr_swap₃₄ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    jcr y₁ y₂ y₄ y₃ = jcr y₁ y₂ y₃ y₄ := by
  simp only [jcr, wcr_swap₃₄ h, inv_inv]; ring

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma Distinct4.swap₁₂ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    Distinct4 y₂ y₁ y₃ y₄ := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1.symm, h4, h5, h2, h3, h6⟩

omit [ProperSpace k] in
lemma Distinct4.smul {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) (g : GL (Fin 2) k) :
    Distinct4 (g • y₁) (g • y₂) (g • y₃) (g • y₄) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only [Distinct4, ne_eq, smul_left_cancel_iff]; exact ⟨h1, h2, h3, h4, h5, h6⟩

omit [ProperSpace k] in
/-- The invariant of two disjoint pairs depends only on the unordered pairs, and is
`GL(2, k)`-invariant. -/
lemma jcr_congr {y₁ y₂ y₃ y₄ z₁ z₂ z₃ z₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄)
    (g : GL (Fin 2) k) (h₁ : ({z₁, z₂} : Set (OnePoint k)) = {g • y₁, g • y₂})
    (h₂ : ({z₃, z₄} : Set (OnePoint k)) = {g • y₃, g • y₄}) :
    jcr z₁ z₂ z₃ z₄ = jcr y₁ y₂ y₃ y₄ := by
  have hg := h.smul g
  have base : jcr (g • y₁) (g • y₂) (g • y₃) (g • y₄) = jcr y₁ y₂ y₃ y₄ := by
    simp only [jcr, wcr_smul g h]
  have hne₁ : g • y₁ ≠ g • y₂ := hg.1
  have hne₂ : g • y₃ ≠ g • y₄ := hg.2.2.2.2.2
  rcases (Set.pair_eq_pair_iff.1 h₁) with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;>
    rcases (Set.pair_eq_pair_iff.1 h₂) with ⟨e3, e4⟩ | ⟨e3, e4⟩ <;>
    subst e1 e2 e3 e4
  · exact base
  · rw [jcr_swap₃₄ hg, base]
  · rw [jcr_swap₁₂ hg, base]
  · rw [jcr_swap₃₄ hg.swap₁₂, jcr_swap₁₂ hg, base]

omit [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k] in
lemma distinct4_of_disjoint {u₁ v₁ u₂ v₂ : OnePoint k} (h₁ : u₁ ≠ v₁) (h₂ : u₂ ≠ v₂)
    (hd : Disjoint ({u₁, v₁} : Set (OnePoint k)) {u₂, v₂}) : Distinct4 u₁ v₁ u₂ v₂ := by
  simp only [Set.disjoint_insert_left, Set.disjoint_insert_right, Set.disjoint_singleton_left,
    Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hd
  obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := hd
  exact ⟨h₁, Ne.symm a, c, Ne.symm b, d, h₂⟩

variable [MeasurableSpace k] [BorelSpace k]

/-- **NoPair, disjoint case.** -/
theorem noPair_disjoint (hΓ : IsDoublyErgodic Γ) (hu : Measurable u) (hv : Measurable v)
    (huv : ∀ᵐ x ∂bdry, u x ≠ v x)
    (heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, pairAt u v (γ • x) = a γ • pairAt u v x)
    (hdisj : ∀ᵐ q ∂(bdry.prod bdry), Disjoint (pairAt u v q.1) (pairAt u v q.2)) : False := by
  classical
  set J : OnePoint ℝ × OnePoint ℝ → k := fun q ↦ jcr (u q.1) (v q.1) (u q.2) (v q.2)
  have hJ : Measurable J := by
    have h4 : Measurable fun q : OnePoint ℝ × OnePoint ℝ ↦
        (u q.1, v q.1, u q.2, v q.2) :=
      (hu.comp measurable_fst).prodMk ((hv.comp measurable_fst).prodMk
        ((hu.comp measurable_snd).prodMk (hv.comp measurable_snd)))
    have hw := measurable_wcr.comp h4
    exact hw.add hw.inv
  -- the good set of pairs
  have hG : ∀ᵐ q ∂(bdry.prod bdry), Distinct4 (u q.1) (v q.1) (u q.2) (v q.2) := by
    filter_upwards [ae_fst huv, ae_snd huv, hdisj] with q h1 h2 h3
    exact distinct4_of_disjoint h1 h2 h3
  have hinv : ∀ γ ∈ Γ, J ∘ dact γ =ᵐ[bdry.prod bdry] J := by
    intro γ hγ
    filter_upwards [hG, ae_fst (heq γ hγ), ae_snd (heq γ hγ)] with q hq h1 h2
    simp only [Function.comp, J, dact]
    refine jcr_congr hq (a γ) ?_ ?_
    · rw [← Set.image_pair]; exact h1
    · rw [← Set.image_pair]; exact h2
  obtain ⟨c₀, hc₀⟩ := hΓ.ae_const hJ hinv
  -- choose two generic reference points
  set P : OnePoint ℝ × OnePoint ℝ → Prop := fun q ↦
    Distinct4 (u q.1) (v q.1) (u q.2) (v q.2) ∧ J q = c₀
  have hP : ∀ᵐ q ∂(bdry.prod bdry), P q := hG.and hc₀
  have hPs : ∀ᵐ q ∂(bdry.prod bdry), P q.swap :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hP
  have hA2 : ∀ᵐ x₂ ∂bdry, ∀ᵐ x₁ ∂bdry, P (x₁, x₂) := Measure.ae_ae_of_ae_prod hPs
  obtain ⟨x₂, hx₂⟩ := exists_of_ae hA2
  obtain ⟨x₃, hx₃, hx₃₂⟩ := exists_of_ae (hA2.and hx₂)
  have hx₁ := hx₂.and hx₃
  obtain ⟨x₁', hx₁'⟩ := exists_of_ae hx₁
  set c := wcr (u x₁') (v x₁') (u x₂) (v x₂)
  have hc0 : c ≠ 0 := wcr_ne_zero hx₁'.1.1
  have hc1 : c ≠ 1 := wcr_ne_one hx₁'.1.1
  have hJc : c₀ = c + c⁻¹ := hx₁'.1.2.symm
  have hcinv : ∀ c' ∈ ({c, c⁻¹} : Set k), c' ≠ 0 ∧ c' ≠ 1 := by
    intro c' hc'
    rcases hc' with rfl | hc'
    · exact ⟨hc0, hc1⟩
    · rw [Set.mem_singleton_iff] at hc'; subst hc'
      exact ⟨inv_ne_zero hc0, fun h ↦ hc1 (inv_eq_one.1 h)⟩
  set Fin : Set (OnePoint k) := ⋃ c₁ ∈ ({c, c⁻¹} : Set k), ⋃ c₂ ∈ ({c, c⁻¹} : Set k),
    {y | ∃ y', Distinct4 y y' (u x₂) (v x₂) ∧ Distinct4 y y' (u x₃) (v x₃) ∧
      wcr y y' (u x₂) (v x₂) = c₁ ∧ wcr y y' (u x₃) (v x₃) = c₂}
  have h32 := hx₃₂.1
  have hFin : Fin.Finite := by
    refine Set.Finite.biUnion (Set.toFinite _) fun c₁ hc₁ ↦
      Set.Finite.biUnion (Set.toFinite _) fun c₂ hc₂ ↦ ?_
    exact finite_of_two_refs h32.2.2.2.2.2 (Ne.symm h32.2.1) (Ne.symm h32.2.2.2.1)
      (hcinv c₁ hc₁).1 (hcinv c₂ hc₂).2
  have hmem : ∀ᵐ x₁ ∂bdry, u x₁ ∈ Fin := by
    filter_upwards [hx₁] with x₁ ⟨⟨h12, e12⟩, ⟨h13, e13⟩⟩
    have w12 := eq_or_eq_inv_of_add_inv (wcr_ne_zero h12) hc0 (e12.trans hJc)
    have w13 := eq_or_eq_inv_of_add_inv (wcr_ne_zero h13) hc0 (e13.trans hJc)
    refine mem_iUnion₂.2 ⟨_, ?_, mem_iUnion₂.2 ⟨_, ?_, v x₁, h12, h13, rfl, rfl⟩⟩
    · rcases w12 with h | h <;> rw [h] <;> simp
    · rcases w13 with h | h <;> rw [h] <;> simp
  obtain ⟨y, -, hy⟩ : ∃ y ∈ Fin, bdry (u ⁻¹' {y}) ≠ 0 := by
    by_contra hno
    push Not at hno
    have h0 : bdry (u ⁻¹' Fin) = 0 := by
      rw [← Set.biUnion_preimage_singleton]
      exact (measure_biUnion_null_iff hFin.countable).2 hno
    have : bdry univ = 0 := by
      refine measure_mono_null (fun x _ ↦ ?_) (measure_union_null h0
        ((measure_eq_zero_iff_ae_notMem (s := (u ⁻¹' Fin)ᶜ)).2
          (hmem.mono fun x hx hx' ↦ hx' hx)))
      by_cases hx : x ∈ u ⁻¹' Fin
      · exact Or.inl hx
      · exact Or.inr hx
    exact bdry_ne_zero (Measure.measure_univ_eq_zero.1 this)
  have hR : (bdry.prod bdry) ((u ⁻¹' {y}) ×ˢ (u ⁻¹' {y})) ≠ 0 := by
    rw [Measure.prod_prod]; exact mul_ne_zero hy hy
  apply hR
  refine measure_mono_null (fun q hq ↦ ?_) ((measure_eq_zero_iff_ae_notMem
    (s := {q | ¬ Disjoint (pairAt u v q.1) (pairAt u v q.2)})).2
    (hdisj.mono fun q hq h ↦ h hq))
  simp only [mem_prod, mem_preimage, mem_singleton_iff] at hq
  rw [mem_setOf_eq, Set.not_disjoint_iff]
  exact ⟨y, by simp [pairAt, hq.1], by simp [pairAt, hq.2]⟩

/-- **NoPair.** There is no equivariant measurable map to unordered pairs of distinct points. -/
theorem noPair (hΓ : IsDoublyErgodic Γ) (hne : NonElem Γ a) (hact : ActsOn Γ a)
    (hu : Measurable u) (hv : Measurable v) (huv : ∀ᵐ x ∂bdry, u x ≠ v x)
    (heq : ∀ γ ∈ Γ, ∀ᵐ x ∂bdry, pairAt u v (γ • x) = a γ • pairAt u v x) : False := by
  set E : Set (OnePoint ℝ × OnePoint ℝ) := {q | (pairAt u v q.1 ∩ pairAt u v q.2).Nonempty}
  have hE' : E = {q | u q.1 = u q.2} ∪ {q | u q.1 = v q.2} ∪ {q | v q.1 = u q.2} ∪
      {q | v q.1 = v q.2} := by
    ext q
    simp only [E, pairAt, mem_setOf_eq, mem_union, Set.Nonempty, mem_inter_iff, mem_insert_iff,
      mem_singleton_iff]
    constructor
    · rintro ⟨y, h1 | h1, h2 | h2⟩ <;> subst h1 <;> simp_all
    · rintro (((h | h) | h) | h)
      · exact ⟨u q.1, Or.inl rfl, Or.inl h⟩
      · exact ⟨u q.1, Or.inl rfl, Or.inr h⟩
      · exact ⟨v q.1, Or.inr rfl, Or.inl h⟩
      · exact ⟨v q.1, Or.inr rfl, Or.inr h⟩
  have hE : MeasurableSet E := by
    rw [hE']
    have m : ∀ {f g : OnePoint ℝ → OnePoint k}, Measurable f → Measurable g →
        MeasurableSet {q : OnePoint ℝ × OnePoint ℝ | f q.1 = g q.2} := fun hf hg ↦
      measurableSet_eq_fun (hf.comp measurable_fst) (hg.comp measurable_snd)
    exact (((m hu hu).union (m hu hv)).union (m hv hu)).union (m hv hv)
  have hinv : ∀ γ ∈ Γ, dact γ ⁻¹' E =ᵐ[bdry.prod bdry] E := by
    intro γ hγ
    filter_upwards [ae_fst (heq γ hγ), ae_snd (heq γ hγ)] with q h1 h2
    change ((pairAt u v (γ • q.1) ∩ pairAt u v (γ • q.2)).Nonempty) =
      (pairAt u v q.1 ∩ pairAt u v q.2).Nonempty
    rw [h1, h2, ← Set.smul_set_inter, Set.smul_set_nonempty]
  rcases hΓ.null_or_conull hE hinv with h0 | h0
  · refine noPair_disjoint hΓ hu hv huv heq ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    exact Set.disjoint_iff_inter_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hq)
  · refine noPair_meet hne hact hu hv heq ?_
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with q hq
    simpa [E] using hq

end

end OrbicurveCores.M2
