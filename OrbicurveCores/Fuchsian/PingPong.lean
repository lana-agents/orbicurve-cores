/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.OneInftyLattice

/-!
# Once-punctured torus groups are free and discrete (ping-pong)

For the Fricke normal form `A₀, B₀` (`x, y, z > 0`, `x² + y² + z² = xyz`) the ideal quadrilateral
with vertices

  `v₁ = A₀⁻¹ ∞ = -y/(xz)`,  `0 = A₀⁻¹B₀⁻¹ ∞`,  `v₃ = B₀⁻¹ ∞ = x/(yz)`,  `∞`

has its opposite sides paired by `A₀` and `B₀`. Let `U₁, U₂` be the open half-discs over `[v₁, 0]`
and `[0, v₃]`, and `U₃ = {Re > v₃}`, `U₄ = {Re < v₁}`. Then `A₀` maps the outside of `U₁` into
`U₃`, `A₀⁻¹` maps the outside of `U₃` into `U₁`, and similarly `B₀` sends the outside of `U₂` into
`U₄` and `B₀⁻¹` sends the outside of `U₄` into `U₂`. By ping-pong, every nontrivial reduced word
moves the interior `Q°` of the quadrilateral off itself. Hence:

* `⟨A₀, B₀⟩` is free on `A₀, B₀` (`injective_lift_normal`);
* `⟨A₀, B₀⟩` is discrete (`discreteTopology_normal`).

The key computation (`normSq_mul_re_smul_sub`): if `g = [[a, b], [c, d]] ∈ SL(2, ℝ)` and
`b = v d`, then `|cw + d|² (Re(g w) - v) = c(a - vc)|w|² + Re w`.
-/

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set Filter Topology
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.Fuchsian

/-- The basic Möbius computation. -/
lemma normSq_mul_re_smul_sub (g : SL(2, ℝ)) (v : ℝ) (hv : g 0 1 = v * g 1 1) (w : ℍ) :
    Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) * ((g • w).re - v) =
      g 1 0 * (g 0 0 - v * g 1 0) * Complex.normSq (w : ℂ) + w.re := by
  have hdet := g.det_coe
  rw [det_fin_two] at hdet
  have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
    simpa [UpperHalfPlane.denom] using this
  have hN : Complex.normSq (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
    rwa [Ne, Complex.normSq_eq_zero]
  have hre : (g • w).re = ((g 0 0 * (w : ℂ) + g 0 1) / (g 1 0 * (w : ℂ) + g 1 1)).re := by
    rw [UpperHalfPlane.re, coe_specialLinearGroup_apply]; simp
  set N := Complex.normSq (g 1 0 * (w : ℂ) + g 1 1)
  have hNe : N = (g 1 0 * w.re + g 1 1) ^ 2 + (g 1 0 * w.im) ^ 2 := by
    simp only [N, Complex.normSq_apply]; simp; ring
  have key : (g • w).re = ((g 0 0 * w.re + g 0 1) * (g 1 0 * w.re + g 1 1) +
      (g 0 0 * w.im) * (g 1 0 * w.im)) / N := by
    rw [hre, Complex.div_re]
    simp only [N]
    simp [Complex.normSq_apply]
    ring
  rw [key, mul_sub, mul_div_cancel₀ _ hN, hNe, Complex.normSq_apply]
  simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  rw [hv]
  rw [hv] at hdet
  linear_combination (w.re) * hdet

/-- The sign form: with `κ = c(a - vc) ≠ 0` and `m = -1/(2κ)`, `Re(g w) - v` has the sign of
`κ (|w - m|² - m²)`. -/
lemma re_smul_sub_eq (g : SL(2, ℝ)) (v κ : ℝ) (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ ≠ 0) (w : ℍ) :
    ∃ N > 0, N * ((g • w).re - v) =
      κ * (Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) - (1 / (2 * κ)) ^ 2) := by
  refine ⟨Complex.normSq (g 1 0 * (w : ℂ) + g 1 1), ?_, ?_⟩
  · have hden : (g 1 0 * (w : ℂ) + g 1 1) ≠ 0 := by
      have := UpperHalfPlane.denom_ne_zero (SpecialLinearGroup.mapGL ℝ g) w
      simpa [UpperHalfPlane.denom] using this
    exact Complex.normSq_pos.mpr hden
  rw [normSq_mul_re_smul_sub g v hv w, hκ]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  field_simp
  ring

lemma re_gt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    v < (g • w).re := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' w
  have : 0 < N * ((g • w).re - v) := by rw [h]; exact mul_pos hκ0 (by linarith)
  have := (pos_iff_pos_of_mul_pos this).mp hN
  linarith

lemma re_lt_of_out {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ}
    (hw : (1 / (2 * κ)) ^ 2 < Complex.normSq ((w : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ))) :
    (g • w).re < v := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne w
  have : N * ((g • w).re - v) < 0 := by rw [h]; exact mul_neg_of_neg_of_pos hκ0 (by linarith)
  by_contra hc; push Not at hc; nlinarith

lemma in_of_re_lt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : 0 < κ) {w : ℍ} (hw : w.re < v) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne' (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : N * (w.re - v) < 0 := mul_neg_of_pos_of_neg hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

lemma in_of_re_gt {g : SL(2, ℝ)} {v κ : ℝ} (hv : g 0 1 = v * g 1 1)
    (hκ : g 1 0 * (g 0 0 - v * g 1 0) = κ) (hκ0 : κ < 0) {w : ℍ} (hw : v < w.re) :
    Complex.normSq (((g⁻¹ • w : ℍ) : ℂ) - ((-1 / (2 * κ) : ℝ) : ℂ)) < (1 / (2 * κ)) ^ 2 := by
  obtain ⟨N, hN, h⟩ := re_smul_sub_eq g v κ hv hκ hκ0.ne (g⁻¹ • w)
  rw [smul_inv_smul] at h
  have : 0 < N * (w.re - v) := mul_pos hN (by linarith)
  rw [h] at this
  by_contra hc; push Not at hc; nlinarith

/-- Points of a closed disc `|w - m|² ≤ m²` have real part between `0` and `2m`. -/
lemma re_mem_of_normSq_le {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) ≤ m ^ 2) :
    min 0 (2 * m) ≤ w.re ∧ w.re ≤ max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 ≤ m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

lemma re_mem_of_normSq_lt {w : ℍ} {m : ℝ} (h : Complex.normSq ((w : ℂ) - (m : ℂ)) < m ^ 2) :
    min 0 (2 * m) < w.re ∧ w.re < max 0 (2 * m) := by
  have h' : (w.re - m) ^ 2 < m ^ 2 := by
    have := w.im_pos
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h
    nlinarith
  constructor
  · rcases le_total 0 m with hm | hm
    · rw [min_eq_left (by linarith)]; nlinarith
    · rw [min_eq_right (by linarith)]; nlinarith
  · rcases le_total 0 m with hm | hm
    · rw [max_eq_right (by linarith)]; nlinarith
    · rw [max_eq_left (by linarith)]; nlinarith

section normal

variable {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
  (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The four ping-pong regions and the open quadrilateral. With `v₁ = -y/(xz)`, `v₃ = x/(yz)`:
`mA = v₁/2`, `mB = v₃/2`. -/
noncomputable def ppX (x y z : ℝ) : Fin 2 × Bool → Set ℍ
  | (0, true) => {w | x / (y * z) < w.re}
  | (0, false) => {w | Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) <
      (-y / (2 * x * z)) ^ 2}
  | (1, true) => {w | w.re < -y / (x * z)}
  | (1, false) => {w | Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) <
      (x / (2 * y * z)) ^ 2}

/-- The open fundamental quadrilateral. -/
def ppQ (x y z : ℝ) : Set ℍ :=
  {w | (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) ∧
    (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) ∧
    -y / (x * z) < w.re ∧ w.re < x / (y * z)}

/-- The generators as letters. -/
noncomputable def ppGen : Fin 2 × Bool → SL(2, ℝ)
  | (0, true) => nA hz hrel
  | (0, false) => (nA hz hrel)⁻¹
  | (1, true) => nB hz hrel
  | (1, false) => (nB hz hrel)⁻¹

include hx hy in
lemma nA_hv : (nA hz hrel : SL(2, ℝ)) 0 1 = x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
lemma nA_hκ : (nA hz hrel : SL(2, ℝ)) 1 0 * ((nA hz hrel : SL(2, ℝ)) 0 0 -
    x / (y * z) * (nA hz hrel : SL(2, ℝ)) 1 0) = x * z / y := by
  simp only [coe_nA, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp
  grind

include hx hy in
lemma nB_hv : (nB hz hrel : SL(2, ℝ)) 0 1 = -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 1 := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp

include hx hy in
lemma nB_hκ : (nB hz hrel : SL(2, ℝ)) 1 0 * ((nB hz hrel : SL(2, ℝ)) 0 0 -
    -y / (x * z) * (nB hz hrel : SL(2, ℝ)) 1 0) = -(y * z / x) := by
  simp only [coe_nB, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one]
  field_simp
  grind

include hx hy hz in
lemma pp_facts :
    (-y / (x * z) < 0) ∧ (0 < x / (y * z)) ∧ 2 * (-y / (2 * x * z)) = -y / (x * z) ∧
      2 * (x / (2 * y * z)) = x / (y * z) ∧
      -1 / (2 * (x * z / y)) = -y / (2 * x * z) ∧
      (1 / (2 * (x * z / y))) ^ 2 = (-y / (2 * x * z)) ^ 2 ∧
      -1 / (2 * -(y * z / x)) = x / (2 * y * z) ∧
      (1 / (2 * -(y * z / x))) ^ 2 = (x / (2 * y * z)) ^ 2 := by
  refine ⟨?_, by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [neg_div]; exact neg_neg_of_pos (by positivity)
  all_goals field_simp

include hx hy in
/-- **Ping-pong step.** -/
lemma pp_step (s t : Fin 2 × Bool) (hst : s.1 = t.1 → s.2 = t.2) :
    ppGen hz hrel s • ppX x y z t ⊆ ppX x y z s := by
  obtain ⟨hv1, hv3, e1, e3, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  -- domains
  have domA : ∀ w : ℍ, w.re < -y / (x * z) ∨ 0 < w.re →
      (-y / (2 * x * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := -y / (2 * x * z)) hc
    rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  have domB : ∀ w : ℍ, w.re < 0 ∨ x / (y * z) < w.re →
      (x / (2 * y * z)) ^ 2 < Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    intro w hre
    by_contra hc; push Not at hc
    have := re_mem_of_normSq_le (m := x / (2 * y * z)) hc
    rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
    rcases hre with h | h <;> linarith [this.1, this.2]
  -- facts about the regions
  have hX : ∀ w : ℍ, w ∈ ppX x y z t →
      (t = (0, true) ∧ x / (y * z) < w.re) ∨ (t = (1, true) ∧ w.re < -y / (x * z)) ∨
      (t = (0, false) ∧ -y / (x * z) < w.re ∧ w.re < 0) ∨
      (t = (1, false) ∧ 0 < w.re ∧ w.re < x / (y * z)) := by
    intro w hw
    obtain ⟨j, c⟩ := t
    fin_cases j <;> cases c
    · right; right; left
      have := re_mem_of_normSq_lt (m := -y / (2 * x * z)) hw
      rw [e1, min_eq_right hv1.le, max_eq_left hv1.le] at this
      exact ⟨rfl, this⟩
    · left; exact ⟨rfl, hw⟩
    · right; right; right
      have := re_mem_of_normSq_lt (m := x / (2 * y * z)) hw
      rw [e3, min_eq_left hv3.le, max_eq_right hv3.le] at this
      exact ⟨rfl, this⟩
    · right; left; exact ⟨rfl, hw⟩
  -- actions
  have actA : ∀ w : ℍ, (-y / (2 * x * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) →
        nA hz hrel • w ∈ ppX x y z (0, true) := by
    intro w hw
    exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  have actAi : ∀ w : ℍ, w.re < x / (y * z) → (nA hz hrel)⁻¹ • w ∈ ppX x y z (0, false) := by
    intro w hw
    have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hw
    rwa [emA, erA] at this
  have actB : ∀ w : ℍ, (x / (2 * y * z)) ^ 2 <
      Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) →
        nB hz hrel • w ∈ ppX x y z (1, true) := by
    intro w hw
    exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])
  have actBi : ∀ w : ℍ, -y / (x * z) < w.re → (nB hz hrel)⁻¹ • w ∈ ppX x y z (1, false) := by
    intro w hw
    have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hw
    rwa [emB, erB] at this
  rintro _ ⟨w, hw, rfl⟩
  obtain ⟨i, b⟩ := s
  rcases hX w hw with ⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
  fin_cases i <;> cases b <;> simp at hst <;> simp only [ppGen] <;>
  first
    | exact actA w (domA w (by first | (left; linarith) | (right; linarith)))
    | exact actAi w (by linarith)
    | exact actB w (domB w (by first | (left; linarith) | (right; linarith)))
    | exact actBi w (by linarith)

include hx hy in
lemma pp_stepQ (s : Fin 2 × Bool) : ppGen hz hrel s • ppQ x y z ⊆ ppX x y z s := by
  obtain ⟨hv1, hv3, e1, e3, emA, erA, emB, erB⟩ := pp_facts hx hy hz
  have hκA : 0 < x * z / y := by positivity
  have hκB : -(y * z / x) < 0 := by rw [neg_lt_zero]; positivity
  rintro _ ⟨w, ⟨hq1, hq2, hq3, hq4⟩, rfl⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppGen]
  · have := in_of_re_lt (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA hq4
    rwa [emA, erA] at this
  · exact re_gt_of_out (nA_hv hx hy hz hrel) (nA_hκ hx hy hz hrel) hκA (by rwa [emA, erA])
  · have := in_of_re_gt (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB hq3
    rwa [emB, erB] at this
  · exact re_lt_of_out (nB_hv hx hy hz hrel) (nB_hκ hx hy hz hrel) hκB (by rwa [emB, erB])

lemma ppX_disjoint_Q (s : Fin 2 × Bool) : Disjoint (ppX x y z s) (ppQ x y z) := by
  rw [Set.disjoint_left]
  rintro w hw ⟨hq1, hq2, hq3, hq4⟩
  obtain ⟨i, b⟩ := s
  fin_cases i <;> cases b <;> simp only [ppX, Set.mem_setOf_eq] at hw <;> linarith

include hx hy in
/-- **Ping-pong.** A reduced nonempty word maps `Q°` into the region of its first letter. -/
lemma pp_word : ∀ (L : List (Fin 2 × Bool)) (s : Fin 2 × Bool), FreeGroup.IsReduced (s :: L) →
    ((s :: L).map (ppGen hz hrel)).prod • ppQ x y z ⊆ ppX x y z s := by
  intro L
  induction L with
  | nil =>
    intro s _
    simpa using pp_stepQ hx hy hz hrel s
  | cons t L ih =>
    intro s hL
    rw [FreeGroup.isReduced_cons_cons] at hL
    rw [List.map_cons, List.prod_cons, mul_smul]
    exact (Set.smul_set_mono (ih t hL.2)).trans (pp_step hx hy hz hrel s t hL.1)

/-- The generator map `Fin 2 → SL(2, ℝ)`. -/
noncomputable def ppF : Fin 2 → SL(2, ℝ) := ![nA hz hrel, nB hz hrel]

lemma lift_mk_eq (L : List (Fin 2 × Bool)) :
    FreeGroup.lift (ppF hz hrel) (FreeGroup.mk L) = (L.map (ppGen hz hrel)).prod := by
  rw [FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  rintro ⟨i, b⟩ -
  fin_cases i <;> cases b <;> rfl

include hx hy in
/-- Every nontrivial element moves `Q°` off itself. -/
theorem pp_disjoint {g : FreeGroup (Fin 2)} (hg : g ≠ 1) :
    Disjoint (FreeGroup.lift (ppF hz hrel) g • ppQ x y z) (ppQ x y z) := by
  obtain ⟨s, L, hL⟩ : ∃ s L, g.toWord = s :: L := by
    rcases h : g.toWord with _ | ⟨s, L⟩
    · exact absurd (FreeGroup.toWord_eq_nil_iff.mp h) hg
    · exact ⟨s, L, rfl⟩
  have hred : FreeGroup.IsReduced (s :: L) := hL ▸ FreeGroup.isReduced_toWord
  rw [← FreeGroup.mk_toWord (x := g), hL, lift_mk_eq]
  exact Set.disjoint_of_subset_left (pp_word hx hy hz hrel L s hred)
    (ppX_disjoint_Q s)

include hx hy hz in
lemma ppQ_nonempty : (ppQ x y z).Nonempty := by
  obtain ⟨hv1, hv3, -⟩ := pp_facts hx hy hz
  have key : ∀ m : ℝ, m ^ 2 < Complex.normSq (Complex.I - (m : ℂ)) := by
    intro m; rw [Complex.normSq_apply]; simp; nlinarith
  have hre : (⟨Complex.I, by simp⟩ : ℍ).re = 0 := by simp [UpperHalfPlane.re]
  exact ⟨⟨Complex.I, by simp⟩, key _, key _, by rw [hre]; exact hv1, by rw [hre]; exact hv3⟩

lemma ppQ_isOpen : IsOpen (ppQ x y z) := by
  have h1 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((-y / (2 * x * z) : ℝ) : ℂ)) := by
    fun_prop
  have h2 : Continuous fun w : ℍ ↦ Complex.normSq ((w : ℂ) - ((x / (2 * y * z) : ℝ) : ℂ)) := by
    fun_prop
  simp only [ppQ, Set.setOf_and]
  exact (isOpen_lt continuous_const h1).inter ((isOpen_lt continuous_const h2).inter
    ((isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)))

include hx hy in
/-- **The normal form group is free on `A₀, B₀`.** -/
theorem injective_lift_normal : Function.Injective (FreeGroup.lift (ppF hz hrel)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  by_contra hne
  obtain ⟨w, hw⟩ := ppQ_nonempty hx hy hz
  have := pp_disjoint hx hy hz hrel hne
  rw [hg, one_smul, disjoint_self, Set.bot_eq_empty] at this
  rw [this] at hw; exact hw

lemma range_lift_normal :
    (FreeGroup.lift (ppF hz hrel)).range = Subgroup.closure {nA hz hrel, nB hz hrel} := by
  rw [FreeGroup.range_lift_eq_closure]
  congr 1
  ext g
  simp only [ppF, Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

include hx hy in
/-- **The normal form group is discrete.** -/
theorem discreteTopology_normal :
    DiscreteTopology (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  apply discreteTopology_of_nhdsWithin_eq_bot
  obtain ⟨w, hw⟩ := ppQ_nonempty hx hy hz
  have hcont : Continuous fun g : SL(2, ℝ) ↦ g • w := continuous_id.smul continuous_const
  have hU : (fun g : SL(2, ℝ) ↦ g • w) ⁻¹' ppQ x y z ∈ 𝓝 (1 : SL(2, ℝ)) :=
    hcont.continuousAt.preimage_mem_nhds ((ppQ_isOpen).mem_nhds (by simpa using hw))
  rw [← Filter.empty_mem_iff_bot, mem_nhdsWithin]
  refine ⟨interior ((fun g : SL(2, ℝ) ↦ g • w) ⁻¹' ppQ x y z), isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hU, ?_⟩
  rintro γ ⟨hγU, hγH, hγ1⟩
  rw [← range_lift_normal] at hγH
  obtain ⟨g, rfl⟩ := hγH
  have hg : g ≠ 1 := by rintro rfl; exact hγ1 (by simp)
  have hγw := interior_subset hγU
  exact Set.disjoint_left.mp (pp_disjoint hx hy hz hrel hg) (Set.smul_mem_smul_set hw) hγw

end normal

/-- A discrete subgroup has a neighbourhood of `1` meeting it only in `1`. -/
lemma exists_nhds_of_discrete (H : Subgroup SL(2, ℝ)) [DiscreteTopology H] :
    ∃ U ∈ 𝓝 (1 : SL(2, ℝ)), ∀ h ∈ H, h ∈ U → h = 1 := by
  have hopen : IsOpen ({1} : Set H) := isOpen_discrete _
  obtain ⟨t, ht, hte⟩ := isOpen_induced_iff.mp hopen
  refine ⟨t, ht.mem_nhds ?_, fun h hH hU ↦ ?_⟩
  · have : (1 : H) ∈ Subtype.val ⁻¹' t := by rw [hte]; rfl
    exact this
  · have : (⟨h, hH⟩ : H) ∈ Subtype.val ⁻¹' t := hU
    rw [hte] at this
    exact congrArg Subtype.val this

/-- Discreteness via an isolating neighbourhood. -/
lemma discreteTopology_of_nhds {H : Subgroup SL(2, ℝ)} {U : Set SL(2, ℝ)}
    (hU : U ∈ 𝓝 (1 : SL(2, ℝ))) (h : ∀ g ∈ H, g ∈ U → g = 1) : DiscreteTopology H := by
  apply discreteTopology_of_nhdsWithin_eq_bot
  rw [← Filter.empty_mem_iff_bot, mem_nhdsWithin]
  obtain ⟨V, hVU, hVo, hV1⟩ := mem_nhds_iff.mp hU
  exact ⟨V, hVo, hV1, fun g ⟨hgV, hgH, hg1⟩ ↦ hg1 (h g hgH (hVU hgV))⟩

/-- Discreteness is invariant under simultaneous `GL(2, ℝ)`-conjugation of generators. -/
theorem discreteTopology_of_conj {A B A₀ B₀ : SL(2, ℝ)} (g : GL (Fin 2) ℝ)
    (hA : g * toGL A * g⁻¹ = toGL A₀) (hB : g * toGL B * g⁻¹ = toGL B₀)
    [DiscreteTopology (Subgroup.closure {A₀, B₀})] :
    DiscreteTopology (Subgroup.closure {A, B}) := by
  have hg : IsUnit (g : Matrix (Fin 2) (Fin 2) ℝ).det := g.isUnit.map Matrix.detMonoidHom
  set ψ := SL2R.conjMat (g : Matrix (Fin 2) (Fin 2) ℝ) hg
  have hψ : ∀ γ : SL(2, ℝ), toGL (ψ γ) = g * toGL γ * g⁻¹ := by
    intro γ; ext1
    simp [ψ, SL2R.coe_conjMat, Matrix.coe_units_inv]
  have hψA : ψ A = A₀ := toGL_injective (by rw [hψ, hA])
  have hψB : ψ B = B₀ := toGL_injective (by rw [hψ, hB])
  have hmap : Subgroup.closure {A₀, B₀} = (Subgroup.closure {A, B}).map ψ := by
    rw [MonoidHom.map_closure, Set.image_pair, hψA, hψB]
  obtain ⟨U₀, hU₀, hU₀H⟩ := exists_nhds_of_discrete (Subgroup.closure {A₀, B₀})
  refine discreteTopology_of_nhds (U := ψ ⁻¹' U₀)
    ((SL2R.continuous_conjMat _ hg).continuousAt.preimage_mem_nhds (by rwa [map_one])) ?_
  intro h hH hU
  have := hU₀H (ψ h) (by rw [hmap]; exact ⟨h, hH, rfl⟩) hU
  exact (SL2R.conjHomeo _ hg).injective (by simpa [SL2R.conjHomeo] using this)

/-- Discreteness is insensitive to the signs of the generators. -/
theorem discreteTopology_of_signs {A B A' B' : SL(2, ℝ)} (hA : A' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) [DiscreteTopology (Subgroup.closure {A', B'})] :
    DiscreteTopology (Subgroup.closure {A, B}) := by
  set H := Subgroup.closure {A', B'}
  have hsign : ∀ h ∈ Subgroup.closure {A, B}, h ∈ H ∨ -h ∈ H := by
    let Hpm : Subgroup SL(2, ℝ) :=
      { carrier := {g | g ∈ H ∨ -g ∈ H}
        mul_mem' := fun {a b} ha hb ↦ by
          rcases ha with ha | ha <;> rcases hb with hb | hb
          · exact Or.inl (mul_mem ha hb)
          · exact Or.inr (by simpa using mul_mem ha hb)
          · exact Or.inr (by simpa using mul_mem ha hb)
          · exact Or.inl (by simpa using mul_mem ha hb)
        one_mem' := Or.inl (one_mem _)
        inv_mem' := fun {a} ha ↦ by
          rcases ha with ha | ha
          · exact Or.inl (inv_mem ha)
          · exact Or.inr (by simpa using inv_mem ha) }
    have hA' : A' ∈ H := Subgroup.subset_closure (by simp)
    have hB' : B' ∈ H := Subgroup.subset_closure (by simp)
    have hle : Subgroup.closure {A, B} ≤ Hpm := by
      rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
      constructor
      · rcases hA with rfl | rfl
        · exact Or.inl hA'
        · exact Or.inr (by simpa using hA')
      · rcases hB with rfl | rfl
        · exact Or.inl hB'
        · exact Or.inr (by simpa using hB')
    exact fun h hh ↦ hle hh
  obtain ⟨U, hU, hUH⟩ := exists_nhds_of_discrete H
  by_cases hm : (-1 : SL(2, ℝ)) ∈ H
  · refine discreteTopology_of_nhds hU fun h hh hhU ↦ hUH h ?_ hhU
    rcases hsign h hh with h1 | h1
    · exact h1
    · simpa using mul_mem hm h1
  · have hclosed : IsClosed (H : Set SL(2, ℝ)) := Subgroup.isClosed_of_discrete
    have hN : {h : SL(2, ℝ) | -h ∈ (H : Set SL(2, ℝ))ᶜ} ∈ 𝓝 (1 : SL(2, ℝ)) := by
      have hcont : Continuous fun h : SL(2, ℝ) ↦ -h := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.neg
      exact hcont.continuousAt.preimage_mem_nhds (hclosed.isOpen_compl.mem_nhds hm)
    refine discreteTopology_of_nhds (Filter.inter_mem hU hN) fun h hh ⟨hhU, hhN⟩ ↦ ?_
    rcases hsign h hh with h1 | h1
    · exact hUH h h1 hhU
    · exact absurd h1 hhN

/-- **Once-punctured torus groups are discrete.** -/
theorem oneInfty_discrete {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) : DiscreteTopology (Subgroup.closure {A, B}) := by
  obtain ⟨x, y, z, hx, hy, hz, hrel, -, A', B', hcl, A'', hA'', B'', hB'', g, hgA,
    hgB⟩ := exists_normal_form hcomm hA
  rw [← hcl]
  haveI := discreteTopology_normal hx hy hz hrel
  haveI := discreteTopology_of_conj g hgA hgB
  exact discreteTopology_of_signs hA'' hB''

end OrbicurveCores.Fuchsian
