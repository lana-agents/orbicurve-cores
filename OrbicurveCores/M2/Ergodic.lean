/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.ErgodicMautner
import OrbicurveCores.M2.GoodLattice

/-!
# Double ergodicity of good lattices (Moore's theorem)

`GoodLattice.isDoublyErgodic`: a good lattice `Γ ≤ SL(2, ℝ)` acts ergodically on `B × B`,
`B = ℙ¹(ℝ)`.

Proof. Let `E ⊆ B × B` be `Γ`-invariant and put `Φ(g) = 1_E(g ∞, g 0)` on `SL(2, ℝ)`. It is left
`Γ`-invariant and right `A`-invariant, hence right `N`-invariant almost everywhere (Mautner,
`ae_mul_unip_eq`). In Hopf coordinates `(g ∞, g 0) = (x, x - 1/u)` and `N` shears `u`, so almost
every slice `E_x` is null or conull. The same holds for the slices `E^y` (apply this to the
flipped set, which is also invariant), and the two slice dichotomies together force `E` to be
null or conull.

Consequences: `IsDoublyErgodic.ergodic_bdry` (ergodicity on `B`) and
`IsDoublyErgodic.ae_eq_const` (a.e. invariant measurable functions are a.e. constant).
-/

open MeasureTheory Set Filter Topology Real UpperHalfPlane OnePoint
open scoped MatrixGroups

namespace OrbicurveCores.M2

/-! ### The boundary maps -/

lemma smul_coe_bdry (g : SL(2, ℝ)) (k : ℝ) :
    g • (k : OnePoint ℝ) =
      if g 1 0 * k + g 1 1 = 0 then ∞ else ↑((g 0 0 * k + g 0 1) / (g 1 0 * k + g 1 1)) := by
  rw [sl_smul_bdry, OnePoint.smul_some_eq_ite]
  simp

lemma smul_infty_bdry (g : SL(2, ℝ)) :
    g • (∞ : OnePoint ℝ) = if g 1 0 = 0 then ∞ else ↑(g 0 0 / g 1 0) := by
  rw [sl_smul_bdry, OnePoint.smul_infty_eq_ite]
  simp

lemma neg_one_smul_bdry (x : OnePoint ℝ) : (-1 : SL(2, ℝ)) • x = x := by
  induction x using OnePoint.rec with
  | infty => rw [smul_infty_bdry]; simp
  | coe k => rw [smul_coe_bdry]; simp

lemma neg_smul_bdry (g : SL(2, ℝ)) (x : OnePoint ℝ) : (-g) • x = g • x := by
  rw [← neg_one_mul, mul_smul, neg_one_smul_bdry]

@[fun_prop]
lemma measurable_entry (i j : Fin 2) : Measurable fun g : SL(2, ℝ) ↦ g i j :=
  (show Continuous fun g : SL(2, ℝ) ↦ g i j by fun_prop).measurable

/-- A function on `OnePoint ℝ` is measurable as soon as its restriction to `ℝ` is. -/
lemma measurable_of_comp_coe {Y : Type*} [MeasurableSpace Y] {f : OnePoint ℝ → Y}
    (hf : Measurable fun x : ℝ ↦ f x) : Measurable f := by
  intro T hT
  have hemb := (OnePoint.isOpenEmbedding_coe (X := ℝ)).measurableEmbedding
  have : f ⁻¹' T = (((↑) : ℝ → OnePoint ℝ) '' ((fun x : ℝ ↦ f x) ⁻¹' T)) ∪
      ({(∞ : OnePoint ℝ)} ∩ f ⁻¹' T) := by
    ext y
    induction y using OnePoint.rec with
    | infty => simp
    | coe k => simp
  rw [this]
  exact (hemb.measurableSet_image.mpr (hf hT)).union
    ((Set.subsingleton_singleton.anti Set.inter_subset_left).measurableSet)

lemma measurable_smul_bdry (g : SL(2, ℝ)) : Measurable fun x : OnePoint ℝ ↦ g • x := by
  refine measurable_of_comp_coe ?_
  simp only [smul_coe_bdry]
  refine Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const ?_
  exact continuous_coe.measurable.comp (by fun_prop)

lemma measurable_smul_infty : Measurable fun g : SL(2, ℝ) ↦ g • (∞ : OnePoint ℝ) := by
  simp only [smul_infty_bdry]
  refine Measurable.ite (measurableSet_eq_fun ?_ measurable_const) measurable_const ?_
  · fun_prop
  · exact continuous_coe.measurable.comp (by fun_prop)

lemma measurable_smul_zero : Measurable fun g : SL(2, ℝ) ↦ g • ((0 : ℝ) : OnePoint ℝ) := by
  simp only [smul_coe_bdry]
  refine Measurable.ite (measurableSet_eq_fun ?_ measurable_const) measurable_const ?_
  · fun_prop
  · exact continuous_coe.measurable.comp (by fun_prop)

/-- The second endpoint in Hopf coordinates. -/
noncomputable def yb (x u : ℝ) : OnePoint ℝ := if u = 0 then ∞ else ↑(x - 1 / u)

lemma measurable_yb : Measurable fun q : ℝ × ℝ ↦ yb q.1 q.2 := by
  simp only [yb]
  exact Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const) measurable_const
    (continuous_coe.measurable.comp (by fun_prop))

lemma hopf_smul_infty (p : ℝ × ℝ × ℝ) : hopf p • (∞ : OnePoint ℝ) = ↑p.1 := by
  rw [smul_infty_bdry]
  simp [coe_hopf, (exp_pos p.2.2).ne']

lemma hopf_smul_zero (p : ℝ × ℝ × ℝ) : hopf p • ((0 : ℝ) : OnePoint ℝ) = yb p.1 p.2.1 := by
  rw [smul_coe_bdry, yb]
  simp only [coe_hopf]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', mul_zero, zero_add, mul_eq_zero,
    (exp_pos _).ne', or_false]
  split_ifs with h
  · rfl
  · congr 1
    field_simp

lemma diagA_smul_infty (σ : ℝ) : diagA σ • (∞ : OnePoint ℝ) = ∞ := by
  rw [smul_infty_bdry]; simp [diagA]

lemma diagA_smul_zero (σ : ℝ) : diagA σ • ((0 : ℝ) : OnePoint ℝ) = ((0 : ℝ) : OnePoint ℝ) := by
  rw [smul_coe_bdry]; simp [diagA, (exp_pos _).ne']

lemma unip_smul_infty (t : ℝ) : unip t • (∞ : OnePoint ℝ) = ∞ := by
  rw [smul_infty_bdry]; simp [unip]

/-! ### Lifting an invariant set to `SL(2, ℝ)` -/

section lift

variable (E : Set (OnePoint ℝ × OnePoint ℝ))

/-- The lift `Φ(g) = 1_E(g ∞, g 0)`. -/
noncomputable def liftE (g : SL(2, ℝ)) : ℝ :=
  E.indicator 1 (g • (∞ : OnePoint ℝ), g • ((0 : ℝ) : OnePoint ℝ))

/-- The lift in Hopf coordinates (it does not depend on `s`). -/
noncomputable def sliceFun (q : ℝ × ℝ) : ℝ := E.indicator 1 (((q.1 : ℝ) : OnePoint ℝ), yb q.1 q.2)

variable {E}

lemma measurable_liftE (hE : MeasurableSet E) : Measurable (liftE E) :=
  (measurable_one.indicator hE).comp (measurable_smul_infty.prodMk measurable_smul_zero)

lemma measurable_sliceFun (hE : MeasurableSet E) : Measurable (sliceFun E) :=
  (measurable_one.indicator hE).comp ((OnePoint.continuous_coe.measurable.comp
    measurable_fst).prodMk measurable_yb)

lemma abs_liftE_le (g : SL(2, ℝ)) : |liftE E g| ≤ 1 := by
  unfold liftE Set.indicator; split_ifs <;> simp

lemma liftE_hopf (p : ℝ × ℝ × ℝ) : liftE E (hopf p) = sliceFun E (p.1, p.2.1) := by
  simp only [liftE, sliceFun, hopf_smul_infty, hopf_smul_zero]

lemma liftE_hopf_mul_unip (p : ℝ × ℝ × ℝ) (t : ℝ) :
    liftE E (hopf p * unip t) = sliceFun E (p.1, p.2.1 + exp (2 * p.2.2) * t) := by
  rw [hopf_mul_unip, liftE_hopf]; rfl

lemma liftE_mul_diagA (g : SL(2, ℝ)) (σ : ℝ) : liftE E (g * diagA σ) = liftE E g := by
  simp only [liftE, mul_smul, diagA_smul_infty, diagA_smul_zero]

lemma liftE_mul_left {γ : SL(2, ℝ)}
    (hγ : (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹' E = E) (g : SL(2, ℝ)) :
    liftE E (γ * g) = liftE E g := by
  simp only [liftE, mul_smul]
  have hiff : ∀ a b : OnePoint ℝ, (γ • a, γ • b) ∈ E ↔ (a, b) ∈ E := fun a b ↦ by
    conv_rhs => rw [← hγ]
    rfl
  by_cases h : (g • (∞ : OnePoint ℝ), g • ((0 : ℝ) : OnePoint ℝ)) ∈ E
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hiff _ _).mpr h)]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' ↦ h ((hiff _ _).mp h'))]

/-- **Mautner in Hopf coordinates**: the lift is invariant under the shear almost everywhere. -/
theorem ae_sliceFun_shear {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ) (hE : MeasurableSet E)
    (hinv : ∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹' E = E)
    (t : ℝ) :
    ∀ᵐ p : ℝ × ℝ × ℝ, sliceFun E (p.1, p.2.1 + exp (2 * p.2.2) * t) = sliceFun E (p.1, p.2.1) := by
  obtain ⟨F, hFm, hFv, hcov, hfin⟩ := h.exists_fund
  haveI := h.discrete
  haveI := Fuchsian.countable_of_discrete Γ
  have hM := ae_mul_unip_eq hcov hfin hFm hFv (measurable_liftE hE) abs_liftE_le
    (fun γ hγ g ↦ liftE_mul_left (hinv γ hγ) g) (fun σ g ↦ liftE_mul_diagA g σ) t
  set B := {g : SL(2, ℝ) | liftE E (g * unip t) ≠ liftE E g}
  have hB : MeasurableSet B :=
    (measurableSet_eq_fun ((measurable_liftE hE).comp (measurable_mul_right_SL _))
      (measurable_liftE hE)).compl
  have h0 : hopfMeasure B = 0 := ae_iff.mp hM
  have h1 : volume (hopf ⁻¹' B) = 0 := by
    refine le_antisymm (le_trans ?_ h0.le) bot_le
    rw [← Measure.map_apply measurable_hopf hB, hopfMeasure]
    exact Measure.le_add_right le_rfl B
  rw [ae_iff]
  convert h1 using 2
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_preimage, B, liftE_hopf_mul_unip, liftE_hopf]

end lift

/-! ### From the shear to slices -/

/-- A function on `ℝ²` whose shears are a.e. equal to it has a.e. constant slices. -/
theorem ae_slice_const {G : ℝ × ℝ → ℝ} (hG : Measurable G)
    (h : ∀ t, ∀ᵐ p : ℝ × ℝ × ℝ, G (p.1, p.2.1 + exp (2 * p.2.2) * t) = G (p.1, p.2.1)) :
    ∀ᵐ x : ℝ, ∃ c, ∀ᵐ v : ℝ, G (x, v) = c := by
  have hP : MeasurableSet {q : ℝ × (ℝ × ℝ × ℝ) |
      G (q.2.1, q.2.2.1 + exp (2 * q.2.2.2) * q.1) = G (q.2.1, q.2.2.1)} :=
    measurableSet_eq_fun (hG.comp (by fun_prop)) (hG.comp (by fun_prop))
  have h1 : ∀ᵐ p : ℝ × ℝ × ℝ, ∀ᵐ t : ℝ,
      G (p.1, p.2.1 + exp (2 * p.2.2) * t) = G (p.1, p.2.1) :=
    (Measure.ae_ae_comm hP).mp (Eventually.of_forall h)
  have h2 : ∀ᵐ p : ℝ × ℝ × ℝ, ∀ᵐ v : ℝ, G (p.1, v) = G (p.1, p.2.1) := by
    refine h1.mono fun p hp ↦ ?_
    set N := {v : ℝ | G (p.1, v) ≠ G (p.1, p.2.1)}
    have hN : MeasurableSet N :=
      (measurableSet_eq_fun (hG.comp (by fun_prop)) measurable_const).compl
    have hr := exp_pos (2 * p.2.2)
    have hpre : volume ((fun t ↦ exp (2 * p.2.2) * t + p.2.1) ⁻¹' N) = 0 := by
      rw [ae_iff] at hp
      convert hp using 2
      ext t
      simp [N, add_comm]
    have key := lintegral_comp_mul_add hr.ne' p.2.1 (N.indicator 1)
    rw [lintegral_indicator_one hN] at key
    have hleft : ∫⁻ t, N.indicator 1 (exp (2 * p.2.2) * t + p.2.1) =
        volume ((fun t ↦ exp (2 * p.2.2) * t + p.2.1) ⁻¹' N) := by
      rw [← lintegral_indicator_one (hN.preimage (by fun_prop))]
      rfl
    rw [hleft, hpre] at key
    rw [ae_iff]
    have hne : ENNReal.ofReal |(exp (2 * p.2.2))⁻¹| ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
    exact (mul_eq_zero.mp key.symm).resolve_left hne
  have h3 : ∀ᵐ x : ℝ, ∀ᵐ q : ℝ × ℝ, ∀ᵐ v : ℝ, G (x, v) = G (x, q.1) := by
    have := h2
    rw [Measure.volume_eq_prod] at this
    exact Measure.ae_ae_of_ae_prod this
  refine h3.mono fun x hx ↦ ?_
  rw [Measure.volume_eq_prod] at hx
  obtain ⟨u, hu⟩ := (Measure.ae_ae_of_ae_prod hx).exists
  obtain ⟨_, hs⟩ := hu.exists
  exact ⟨G (x, u), hs⟩

/-- A.e. constant Hopf slices give a.e. null-or-conull slices of `E`. -/
lemma ae_slice_dichotomy {E : Set (OnePoint ℝ × OnePoint ℝ)}
    (h : ∀ᵐ x : ℝ, ∃ c, ∀ᵐ v : ℝ, sliceFun E (x, v) = c) :
    ∀ᵐ x : ℝ, (∀ᵐ w : ℝ, ((x : OnePoint ℝ), (w : OnePoint ℝ)) ∈ E) ∨
      (∀ᵐ w : ℝ, ((x : OnePoint ℝ), (w : OnePoint ℝ)) ∉ E) := by
  refine h.mono fun x ⟨c, hc⟩ ↦ ?_
  set N := {v : ℝ | sliceFun E (x, v) ≠ c}
  have hN : volume N = 0 := ae_iff.mp hc
  -- the exceptional set of the slice is contained in `{x} ∪ φ(N \ {0})`, `φ v = x - 1 / v`
  have hsub : {w : ℝ | E.indicator (1 : OnePoint ℝ × OnePoint ℝ → ℝ)
      ((x : OnePoint ℝ), (w : OnePoint ℝ)) ≠ c} ⊆
      {x} ∪ (fun v ↦ x - 1 / v) '' (N ∩ {v | v ≠ 0}) := by
    intro w hw
    by_cases hwx : w = x
    · exact Or.inl hwx
    right
    have hxw : x - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hwx)
    refine ⟨1 / (x - w), ⟨?_, one_div_ne_zero hxw⟩, by field_simp; ring⟩
    simp only [N, Set.mem_setOf_eq, sliceFun, yb, one_div_ne_zero hxw, if_false]
    rw [show x - 1 / (1 / (x - w)) = w by field_simp; ring]
    exact hw
  have hnull : volume {w : ℝ | E.indicator (1 : OnePoint ℝ × OnePoint ℝ → ℝ)
      ((x : OnePoint ℝ), (w : OnePoint ℝ)) ≠ c} = 0 := by
    refine measure_mono_null hsub (measure_union_null (measure_singleton x) ?_)
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null Set.inter_subset_left hN)
    intro v hv
    have hv0 : v ≠ 0 := hv.2
    exact ((differentiableAt_const x).sub
      ((differentiableAt_const 1).div differentiableAt_id hv0)).differentiableWithinAt
  have hae : ∀ᵐ w : ℝ, E.indicator (1 : OnePoint ℝ × OnePoint ℝ → ℝ)
      ((x : OnePoint ℝ), (w : OnePoint ℝ)) = c := by
    rw [ae_iff]; exact hnull
  by_cases hc1 : c = 1
  · left
    refine hae.mono fun w hw ↦ ?_
    by_contra hmem
    rw [Set.indicator_of_notMem hmem, hc1] at hw
    exact zero_ne_one hw
  · right
    refine hae.mono fun w hw hmem ↦ ?_
    rw [Set.indicator_of_mem hmem] at hw
    exact hc1 hw.symm

/-- **Slice dichotomy.** For a `Γ`-invariant measurable `E ⊆ B × B`, almost every slice
`E_x` is null or conull. -/
theorem GoodLattice.ae_slice {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ)
    {E : Set (OnePoint ℝ × OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹' E = E) :
    ∀ᵐ x : ℝ, (∀ᵐ w : ℝ, ((x : OnePoint ℝ), (w : OnePoint ℝ)) ∈ E) ∨
      (∀ᵐ w : ℝ, ((x : OnePoint ℝ), (w : OnePoint ℝ)) ∉ E) :=
  ae_slice_dichotomy (ae_slice_const (measurable_sliceFun hE) (ae_sliceFun_shear h hE hinv))

/-! ### Two slice dichotomies force a trivial set -/

/-- One slice dichotomy: `S` is a.e. a cylinder `H × ℝ`. -/
lemma exists_ae_eq_prod_univ {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (h : ∀ᵐ x : ℝ, (∀ᵐ w : ℝ, (x, w) ∈ S) ∨ (∀ᵐ w : ℝ, (x, w) ∉ S)) :
    ∃ H : Set ℝ, MeasurableSet H ∧ S =ᵐ[volume] H ×ˢ (univ : Set ℝ) := by
  set H := {x : ℝ | volume (Prod.mk x ⁻¹' Sᶜ) = 0}
  have hH : MeasurableSet H :=
    measurable_measure_prodMk_left hS.compl (measurableSet_singleton 0)
  refine ⟨H, hH, ?_⟩
  refine Filter.eventuallyEq_set.mpr ?_
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae]
  · refine h.mono fun x hx ↦ ?_
    by_cases hxH : x ∈ H
    · have : ∀ᵐ w : ℝ, (x, w) ∈ S := by
        rw [ae_iff]; exact hxH
      refine this.mono fun w hw ↦ ?_
      simp only [Set.mem_prod, Set.mem_univ, and_true]
      exact ⟨fun _ ↦ hxH, fun _ ↦ hw⟩
    · have hx' : ∀ᵐ w : ℝ, (x, w) ∉ S := hx.resolve_left fun h' ↦ hxH (by
        rw [ae_iff] at h'; exact h')
      refine hx'.mono fun w hw ↦ ?_
      simp only [Set.mem_prod, Set.mem_univ, and_true]
      exact ⟨fun h'' ↦ absurd h'' hw, fun h'' ↦ absurd h'' hxH⟩
  · exact measurableSet_setOf.mpr (hS.mem.iff ((hH.prod MeasurableSet.univ).mem))

lemma volume_prod_prod (A B : Set ℝ) : volume (A ×ˢ B) = volume A * volume B := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]

/-- **Two slice dichotomies.** -/
theorem null_or_conull_of_slices {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (h1 : ∀ᵐ x : ℝ, (∀ᵐ w : ℝ, (x, w) ∈ S) ∨ (∀ᵐ w : ℝ, (x, w) ∉ S))
    (h2 : ∀ᵐ w : ℝ, (∀ᵐ x : ℝ, (x, w) ∈ S) ∨ (∀ᵐ x : ℝ, (x, w) ∉ S)) :
    volume S = 0 ∨ volume Sᶜ = 0 := by
  obtain ⟨H, hH, hSH⟩ := exists_ae_eq_prod_univ hS h1
  obtain ⟨K, hK, hSK'⟩ := exists_ae_eq_prod_univ (S := Prod.swap ⁻¹' S)
    (hS.preimage measurable_swap) h2
  have hSK : S =ᵐ[volume] (univ : Set ℝ) ×ˢ K := by
    have := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))).quasiMeasurePreserving.preimage_ae_eq hSK'
    rw [← Set.preimage_comp, show Prod.swap ∘ Prod.swap = (id : ℝ × ℝ → ℝ × ℝ) from
      funext fun p ↦ Prod.swap_swap p, Set.preimage_id, Set.preimage_swap_prod] at this
    simpa [Measure.volume_eq_prod] using this
  have hHK := hSH.symm.trans hSK
  have hd := ae_eq_set.mp hHK
  have e1 : volume H * volume Kᶜ = 0 := by
    rw [← volume_prod_prod]
    refine measure_mono_null (fun p hp ↦ ?_) hd.1
    exact ⟨⟨hp.1, trivial⟩, fun h ↦ hp.2 h.2⟩
  have e2 : volume Hᶜ * volume K = 0 := by
    rw [← volume_prod_prod]
    refine measure_mono_null (fun p hp ↦ ?_) hd.2
    exact ⟨⟨trivial, hp.2⟩, fun h ↦ hp.1 h.1⟩
  by_cases hH0 : volume H = 0
  · left
    rw [measure_congr hSH, volume_prod_prod, hH0, zero_mul]
  · right
    have hKc : volume Kᶜ = 0 := (mul_eq_zero.mp e1).resolve_left hH0
    have hK0 : volume K ≠ 0 := by
      intro hK0
      have := measure_union_le (μ := (volume : Measure ℝ)) K Kᶜ
      rw [Set.union_compl_self, Real.volume_univ, hK0, hKc, add_zero] at this
      exact ENNReal.top_ne_zero (le_antisymm this bot_le)
    have hHc : volume Hᶜ = 0 := (mul_eq_zero.mp e2).resolve_right hK0
    rw [measure_congr hSH.compl, show (H ×ˢ (univ : Set ℝ))ᶜ = Hᶜ ×ˢ univ by ext; simp,
      volume_prod_prod, hHc, zero_mul]

/-! ### Double ergodicity -/

instance : SFinite bdry := by unfold bdry; infer_instance

lemma bdry_prod_apply {T : Set (OnePoint ℝ × OnePoint ℝ)} (hT : MeasurableSet T) :
    (bdry.prod bdry) T =
      volume {q : ℝ × ℝ | (((q.1 : ℝ) : OnePoint ℝ), ((q.2 : ℝ) : OnePoint ℝ)) ∈ T} := by
  have hc : Measurable ((↑) : ℝ → OnePoint ℝ) := OnePoint.continuous_coe.measurable
  rw [bdry, Measure.map_prod_map _ _ hc hc, Measure.map_apply (hc.prodMap hc) hT,
    Measure.volume_eq_prod]
  rfl

/-- **Moore's ergodicity theorem** for good lattices: `Γ` acts ergodically on `B × B`. -/
theorem GoodLattice.isDoublyErgodic {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ) :
    IsDoublyErgodic Γ := by
  intro E hE hinv
  have hc : Measurable ((↑) : ℝ → OnePoint ℝ) := OnePoint.continuous_coe.measurable
  set S := {q : ℝ × ℝ | (((q.1 : ℝ) : OnePoint ℝ), ((q.2 : ℝ) : OnePoint ℝ)) ∈ E}
  have hS : MeasurableSet S := hE.preimage (hc.prodMap hc)
  rw [bdry_prod_apply hE, bdry_prod_apply hE.compl]
  -- the flipped set is invariant too
  have hE' : MeasurableSet (Prod.swap ⁻¹' E) := hE.preimage measurable_swap
  have hinv' : ∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹'
      (Prod.swap ⁻¹' E) = Prod.swap ⁻¹' E := by
    intro γ hγ
    ext p
    have := congrArg (fun T ↦ p.swap ∈ T) (hinv γ hγ)
    simpa using this
  exact null_or_conull_of_slices hS (h.ae_slice hE hinv) (h.ae_slice hE' hinv')

/-- **Ergodicity on the boundary.** -/
theorem IsDoublyErgodic.ergodic_bdry {Γ : Subgroup SL(2, ℝ)} (h : IsDoublyErgodic Γ)
    {E : Set (OnePoint ℝ)} (hE : MeasurableSet E)
    (hinv : ∀ γ ∈ Γ, (fun x : OnePoint ℝ ↦ γ • x) ⁻¹' E = E) : bdry E = 0 ∨ bdry Eᶜ = 0 := by
  have huniv : bdry univ ≠ 0 := by
    rw [bdry, Measure.map_apply OnePoint.continuous_coe.measurable MeasurableSet.univ,
      Set.preimage_univ, Real.volume_univ]
    exact ENNReal.top_ne_zero
  have hinv' : ∀ γ ∈ Γ, (fun p : OnePoint ℝ × OnePoint ℝ ↦ (γ • p.1, γ • p.2)) ⁻¹'
      (E ×ˢ univ) = E ×ˢ univ := by
    intro γ hγ
    ext p
    have := congrArg (fun T ↦ p.1 ∈ T) (hinv γ hγ)
    simpa using this
  rcases h _ (hE.prod MeasurableSet.univ) hinv' with h0 | h0
  · left
    rw [Measure.prod_prod] at h0
    exact (mul_eq_zero.mp h0).resolve_right huniv
  · right
    rw [show (E ×ˢ (univ : Set (OnePoint ℝ)))ᶜ = Eᶜ ×ˢ univ by ext; simp,
      Measure.prod_prod] at h0
    exact (mul_eq_zero.mp h0).resolve_right huniv

/-- **Invariant functions are constant.** If `Γ` is countable and doubly ergodic, a measurable
`f : B × B → Z` (with `Z` countably separated, e.g. second countable `T₀` with its Borel
σ-algebra, such as `ℝ`) that is a.e. invariant under every `γ ∈ Γ` is a.e. constant. -/
theorem IsDoublyErgodic.ae_eq_const {Γ : Subgroup SL(2, ℝ)} [Countable Γ]
    (h : IsDoublyErgodic Γ) {Z : Type*} [MeasurableSpace Z]
    [MeasurableSpace.CountablySeparated Z] {f : OnePoint ℝ × OnePoint ℝ → Z} (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ,
      (fun p : OnePoint ℝ × OnePoint ℝ ↦ f (γ • p.1, γ • p.2)) =ᵐ[bdry.prod bdry] f) :
    ∃ c, f =ᵐ[bdry.prod bdry] fun _ ↦ c := by
  haveI : Nonempty Z := ⟨f (∞, ∞)⟩
  set act : SL(2, ℝ) → OnePoint ℝ × OnePoint ℝ → OnePoint ℝ × OnePoint ℝ :=
    fun γ p ↦ (γ • p.1, γ • p.2)
  have hact : ∀ γ, Measurable (act γ) := fun γ ↦
    (measurable_smul_bdry γ).prodMap (measurable_smul_bdry γ)
  have hact_mul : ∀ γ δ p, act γ (act δ p) = act (γ * δ) p := fun γ δ p ↦ by
    simp only [act, mul_smul]
  refine exists_eventuallyEq_const_of_forall_separating MeasurableSet fun U hU ↦ ?_
  set S := f ⁻¹' U
  set S' := ⋂ γ : Γ, act γ ⁻¹' S
  have hS' : MeasurableSet S' := MeasurableSet.iInter fun γ ↦ (hf hU).preimage (hact γ)
  have hinvS' : ∀ δ ∈ Γ, act δ ⁻¹' S' = S' := by
    intro δ hδ
    ext p
    simp only [S', Set.mem_preimage, Set.mem_iInter, hact_mul]
    constructor
    · intro hp γ
      have := hp (γ * (⟨δ, hδ⟩ : Γ)⁻¹)
      have e : ((γ * (⟨δ, hδ⟩ : Γ)⁻¹ : Γ) : SL(2, ℝ)) * δ = γ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
      rwa [e] at this
    · intro hp γ
      have := hp (γ * ⟨δ, hδ⟩)
      rwa [Subgroup.coe_mul] at this
  have hae : ∀ᵐ p ∂(bdry.prod bdry), (p ∈ S' ↔ f p ∈ U) := by
    have hall : ∀ᵐ p ∂(bdry.prod bdry), ∀ γ : Γ, f (act γ p) = f p :=
      ae_all_iff.mpr fun γ ↦ hinv γ γ.2
    refine hall.mono fun p hp ↦ ?_
    simp only [S', S, Set.mem_iInter, Set.mem_preimage, hp]
    exact ⟨fun h ↦ h 1, fun h _ ↦ h⟩
  rcases h S' hS' hinvS' with h0 | h0
  · right
    refine (measure_eq_zero_iff_ae_notMem.mp h0).mp (hae.mono fun p hp hp' ↦ ?_)
    exact fun hU' ↦ hp' (hp.mpr hU')
  · left
    refine (measure_eq_zero_iff_ae_notMem.mp h0).mp (hae.mono fun p hp hp' ↦ ?_)
    exact hp.mp (not_not.mp hp')

/-- **Invariant functions are constant** (good lattice version): for a good lattice `Γ`, a
measurable `f : B × B → Z` into a second countable `T₀` space with its Borel σ-algebra that is
a.e. invariant under every `γ ∈ Γ` is a.e. constant. -/
theorem GoodLattice.ae_eq_const {Γ : Subgroup SL(2, ℝ)} (h : GoodLattice Γ) {Z : Type*}
    [TopologicalSpace Z] [SecondCountableTopology Z] [T0Space Z] [MeasurableSpace Z]
    [BorelSpace Z] {f : OnePoint ℝ × OnePoint ℝ → Z} (hf : Measurable f)
    (hinv : ∀ γ ∈ Γ,
      (fun p : OnePoint ℝ × OnePoint ℝ ↦ f (γ • p.1, γ • p.2)) =ᵐ[bdry.prod bdry] f) :
    ∃ c, f =ᵐ[bdry.prod bdry] fun _ ↦ c := by
  haveI := h.discrete
  haveI := Fuchsian.countable_of_discrete Γ
  exact h.isDoublyErgodic.ae_eq_const hf hinv

/-- Finite-index subgroups of the Fricke normal form group (under the triangle inequalities) act
ergodically on `B × B`. -/
theorem isDoublyErgodic_of_le_normal {x y z : ℝ} (hz : 0 < z)
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z)
    (h2 : y < x + z) (h3 : z < x + y) {Γ' : Subgroup SL(2, ℝ)}
    (hle : Γ' ≤ Subgroup.closure {Fuchsian.nA hz hrel, Fuchsian.nB hz hrel})
    (hidx : Γ'.relIndex (Subgroup.closure {Fuchsian.nA hz hrel, Fuchsian.nB hz hrel}) ≠ 0) :
    IsDoublyErgodic Γ' :=
  ((goodLattice_normal hz hrel hx hy h1 h2 h3).of_le hle hidx).isDoublyErgodic

end OrbicurveCores.M2
