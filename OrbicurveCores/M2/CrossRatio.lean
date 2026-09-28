/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.ForMathlib.ProjectiveLine
import OrbicurveCores.M2.Setup

/-!
# M2: cross ratios on `ℙ¹(k)`

The cross ratio `wcr y₁ y₂ y₃ y₄ = [y₁,y₃][y₂,y₄] / ([y₁,y₄][y₂,y₃])` of four points of
`OnePoint k`, in homogeneous coordinates. For four distinct points:

* it is invariant under `GL(2, k)` (`wcr_smul`);
* swapping `y₁ ↔ y₂` or `y₃ ↔ y₄` inverts it (`wcr_swap₁₂`, `wcr_swap₃₄`);
* it is neither `0` nor `1`.

`finite_of_two_refs`: given two different reference pairs `{p, q}`, `{p', q'}` and a value `c`,
only finitely many `y` admit a partner `y'` with `wcr y y' p q` and `wcr y y' p' q'` in
`{c, c⁻¹}`. This is the algebraic core of the `NoPair` step of M2.
-/

open OnePoint OnePoint.Proj

namespace OrbicurveCores.M2

variable {k : Type*} [Field k] [DecidableEq k]

/-- The cross ratio in homogeneous coordinates. -/
def wcr (y₁ y₂ y₃ y₄ : OnePoint k) : k :=
  br (lift y₁) (lift y₃) * br (lift y₂) (lift y₄) /
    (br (lift y₁) (lift y₄) * br (lift y₂) (lift y₃))

/-- Four pairwise distinct points. -/
def Distinct4 (y₁ y₂ y₃ y₄ : OnePoint k) : Prop :=
  y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₁ ≠ y₄ ∧ y₂ ≠ y₃ ∧ y₂ ≠ y₄ ∧ y₃ ≠ y₄

omit [DecidableEq k] in
lemma br_ne_zero_of_ne {x y : OnePoint k} (h : x ≠ y) : br (lift x) (lift y) ≠ 0 := by
  classical
  rw [Ne, br_lift_eq_zero_iff]; exact h

omit [DecidableEq k] in
lemma wcr_swap₁₂ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    wcr y₂ y₁ y₃ y₄ = (wcr y₁ y₂ y₃ y₄)⁻¹ := by
  obtain ⟨-, h13, h14, h23, h24, -⟩ := h
  have := br_ne_zero_of_ne h13; have := br_ne_zero_of_ne h14
  have := br_ne_zero_of_ne h23; have := br_ne_zero_of_ne h24
  simp only [wcr]; field_simp

omit [DecidableEq k] in
lemma wcr_swap₃₄ {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    wcr y₁ y₂ y₄ y₃ = (wcr y₁ y₂ y₃ y₄)⁻¹ := by
  obtain ⟨-, h13, h14, h23, h24, -⟩ := h
  have := br_ne_zero_of_ne h13; have := br_ne_zero_of_ne h14
  have := br_ne_zero_of_ne h23; have := br_ne_zero_of_ne h24
  simp only [wcr]; field_simp

omit [DecidableEq k] in
lemma wcr_ne_zero {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    wcr y₁ y₂ y₃ y₄ ≠ 0 := by
  obtain ⟨-, h13, h14, h23, h24, -⟩ := h
  simp only [wcr]
  exact div_ne_zero (mul_ne_zero (br_ne_zero_of_ne h13) (br_ne_zero_of_ne h24))
    (mul_ne_zero (br_ne_zero_of_ne h14) (br_ne_zero_of_ne h23))

omit [DecidableEq k] in
/-- The Plücker relation `[a,c][b,d] − [a,d][b,c] = [a,b][c,d]`. -/
lemma br_plucker (a b c d : k × k) :
    br a c * br b d - br a d * br b c = br a b * br c d := by
  simp only [br]; ring

omit [DecidableEq k] in
lemma wcr_ne_one {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    wcr y₁ y₂ y₃ y₄ ≠ 1 := by
  obtain ⟨h12, h13, h14, h23, h24, h34⟩ := h
  simp only [wcr]
  rw [Ne, div_eq_one_iff_eq (mul_ne_zero (br_ne_zero_of_ne h14) (br_ne_zero_of_ne h23)),
    ← sub_eq_zero, br_plucker]
  exact mul_ne_zero (br_ne_zero_of_ne h12) (br_ne_zero_of_ne h34)

/-- The homogeneous coordinates of `g • y` are proportional to `g (lift y)`. -/
lemma lift_gl_smul (g : GL (Fin 2) k) (y : OnePoint k) :
    ∃ c : k, c ≠ 0 ∧ lift (g • y) = c • mv (g : Matrix (Fin 2) (Fin 2) k) (lift y) := by
  have hg : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := g.det_ne_zero
  rw [gl_smul_eq_mob]
  exact lift_proj (mv_ne_zero hg (lift_ne_zero y))

omit [DecidableEq k] in
lemma br_mv (M : Matrix (Fin 2) (Fin 2) k) (v w : k × k) :
    br (mv M v) (mv M w) = M.det * br v w := by
  simp only [br, mv, Matrix.det_fin_two]; ring

lemma wcr_smul (g : GL (Fin 2) k) {y₁ y₂ y₃ y₄ : OnePoint k} (h : Distinct4 y₁ y₂ y₃ y₄) :
    wcr (g • y₁) (g • y₂) (g • y₃) (g • y₄) = wcr y₁ y₂ y₃ y₄ := by
  obtain ⟨-, h13, h14, h23, h24, -⟩ := h
  have hg : (g : Matrix (Fin 2) (Fin 2) k).det ≠ 0 := g.det_ne_zero
  obtain ⟨c₁, hc₁, e₁⟩ := lift_gl_smul g y₁
  obtain ⟨c₂, hc₂, e₂⟩ := lift_gl_smul g y₂
  obtain ⟨c₃, hc₃, e₃⟩ := lift_gl_smul g y₃
  obtain ⟨c₄, hc₄, e₄⟩ := lift_gl_smul g y₄
  have key : ∀ {a b : k × k} {ca cb : k}, br (ca • a) (cb • b) = ca * cb * br a b := by
    intro a b ca cb; simp only [br, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring
  have := br_ne_zero_of_ne h14; have := br_ne_zero_of_ne h23
  simp only [wcr, e₁, e₂, e₃, e₄, key, br_mv]
  field_simp

/-! ### Two reference pairs -/

/-- The linear map `y ↦ [y,p] q − c [y,q] p`, whose projectivisation sends `y` to the unique `y'`
with cross ratio `wcr y y' p q = c`. -/
def crMat (p q : k × k) (c : k) : Matrix (Fin 2) (Fin 2) k :=
  !![p.2 * q.1 - c * q.2 * p.1, -(p.1 * q.1) + c * q.1 * p.1;
    p.2 * q.2 - c * q.2 * p.2, -(p.1 * q.2) + c * q.1 * p.2]

omit [DecidableEq k] in
lemma mv_crMat (p q y : k × k) (c : k) :
    mv (crMat p q c) y = br y p • q - (c * br y q) • p := by
  ext <;> simp [mv, crMat, br] <;> ring

omit [DecidableEq k] in
/-- If `wcr y y' p q = c`, then `y'` is proportional to `[y,p] q − c [y,q] p`. -/
lemma br_crMat_eq_zero {y y' p q : OnePoint k} (h : Distinct4 y y' p q) {c : k}
    (hc : wcr y y' p q = c) : br (lift y') (mv (crMat (lift p) (lift q) c) (lift y)) = 0 := by
  classical
  obtain ⟨-, -, h14, h23, -, -⟩ := h
  have h1 := br_ne_zero_of_ne h14
  have h2 := br_ne_zero_of_ne h23
  simp only [wcr] at hc
  rw [div_eq_iff (mul_ne_zero h1 h2)] at hc
  rw [mv_crMat]
  simp only [br, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub] at hc ⊢
  linear_combination hc

omit [DecidableEq k] in
lemma br_mv_mv (P R : Matrix (Fin 2) (Fin 2) k) (v : k × k) :
    br (mv P v) (mv R v) = quad (P 0 0 * R 1 0 - P 1 0 * R 0 0)
      (P 0 0 * R 1 1 + P 0 1 * R 1 0 - P 1 0 * R 0 1 - P 1 1 * R 0 0)
      (P 0 1 * R 1 1 - P 1 1 * R 0 1) v := by
  simp only [br, mv, quad]; ring

omit [DecidableEq k] in
/-- The zeros of a binary quadratic form not vanishing at one given point are finite. -/
lemma finite_quad_zeros {A B C : k} {v₀ : k × k} (h : quad A B C v₀ ≠ 0) :
    {y : OnePoint k | quad A B C (lift y) = 0}.Finite := by
  by_contra hinf
  obtain ⟨x, hx, -⟩ := Set.Infinite.exists_notMem_finite hinf (Set.finite_empty (α := OnePoint k))
  obtain ⟨y, hy, hyx⟩ := Set.Infinite.exists_notMem_finite hinf (Set.finite_singleton x)
  obtain ⟨z, hz, hzxy⟩ := Set.Infinite.exists_notMem_finite hinf
    ((Set.finite_singleton x).insert y)
  simp only [Set.mem_singleton_iff, Set.mem_insert_iff, not_or] at hyx hzxy
  obtain ⟨hA, hB, hC⟩ := quad_eq_zero (Ne.symm hyx) (Ne.symm hzxy.2) (Ne.symm hzxy.1) hx hy hz
  exact h (by simp [quad, hA, hB, hC])

omit [DecidableEq k] in
lemma br_eq_zero_of_parallel {v a b : k × k} (hv : v ≠ 0) (ha : br v a = 0) (hb : br v b = 0) :
    br a b = 0 := by
  simp only [br] at ha hb ⊢
  by_cases h1 : v.1 = 0
  · have h2 : v.2 ≠ 0 := fun h2 ↦ hv (Prod.ext h1 h2)
    rw [h1] at ha hb
    have ha1 : a.1 = 0 := by
      have : v.2 * a.1 = 0 := by linear_combination -ha
      exact (mul_eq_zero.1 this).resolve_left h2
    have hb1 : b.1 = 0 := by
      have : v.2 * b.1 = 0 := by linear_combination -hb
      exact (mul_eq_zero.1 this).resolve_left h2
    rw [ha1, hb1]; ring
  · have : v.1 * (a.1 * b.2 - a.2 * b.1) = 0 := by
      linear_combination a.1 * hb - b.1 * ha
    exact (mul_eq_zero.1 this).resolve_left h1

omit [DecidableEq k] in
/-- **Two reference pairs.** Given `p ≠ q`, `p' ≠ q'` with `p ∉ {p', q'}`, a value `c ≠ 0` and
a value `c' ≠ 1`, only finitely many `y` admit some `y'` with `wcr y y' p q = c` and
`wcr y y' p' q' = c'`. -/
lemma finite_of_two_refs {p q p' q' : OnePoint k} (hpq : p ≠ q) (hpp' : p ≠ p') (hpq' : p ≠ q')
    {c c' : k} (hc : c ≠ 0) (hc' : c' ≠ 1) :
    {y : OnePoint k | ∃ y', Distinct4 y y' p q ∧ Distinct4 y y' p' q' ∧ wcr y y' p q = c ∧
      wcr y y' p' q' = c'}.Finite := by
  set P := crMat (lift p) (lift q) c
  set R := crMat (lift p') (lift q') c'
  refine Set.Finite.subset (finite_quad_zeros (A := P 0 0 * R 1 0 - P 1 0 * R 0 0)
    (B := P 0 0 * R 1 1 + P 0 1 * R 1 0 - P 1 0 * R 0 1 - P 1 1 * R 0 0)
    (C := P 0 1 * R 1 1 - P 1 1 * R 0 1) (v₀ := lift p) ?_) ?_
  · rw [← br_mv_mv]
    simp only [P, R, mv_crMat]
    have e1 := br_ne_zero_of_ne hpq
    have e2 := br_ne_zero_of_ne hpp'
    have e3 := br_ne_zero_of_ne hpq'
    have e4 : (1 : k) - c' ≠ 0 := sub_ne_zero.2 (Ne.symm hc')
    have : br (br (lift p) (lift p) • lift q - (c * br (lift p) (lift q)) • lift p)
        (br (lift p) (lift p') • lift q' - (c' * br (lift p) (lift q')) • lift p') =
        -c * br (lift p) (lift q) * br (lift p) (lift p') * br (lift p) (lift q') * (1 - c') := by
      simp only [br, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, Prod.fst_sub, Prod.snd_sub]
      ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (neg_ne_zero.2 hc) e1) e2) e3) e4
  · rintro y ⟨y', h1, h2, e1, e2⟩
    simp only [Set.mem_setOf_eq]
    rw [← br_mv_mv]
    exact br_eq_zero_of_parallel (lift_ne_zero y') (br_crMat_eq_zero h1 e1)
      (br_crMat_eq_zero h2 e2)

/-! ### Measurability -/

section measurability

open MeasureTheory

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]
  [MeasurableSpace k] [BorelSpace k]

omit [DecidableEq k] in
lemma measurable_lift : Measurable (lift : OnePoint k → k × k) := by
  intro T hT
  have hcoe : MeasurableEmbedding ((↑) : k → OnePoint k) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding
  have e : lift ⁻¹' T = ((↑) '' {a : k | (a, (1 : k)) ∈ T}) ∪
      {y : OnePoint k | y = ∞ ∧ ((1 : k), (0 : k)) ∈ T} := by
    ext y
    cases y with
    | infty => simp
    | coe a => simp
  rw [e]
  refine (hcoe.measurableSet_image.2 ?_).union ?_
  · exact measurable_prodMk_right hT
  · by_cases h : ((1 : k), (0 : k)) ∈ T
    · simp [h]
    · simp [h]

omit [DecidableEq k] in
lemma measurable_wcr : Measurable fun y : OnePoint k × OnePoint k × OnePoint k × OnePoint k ↦
    wcr y.1 y.2.1 y.2.2.1 y.2.2.2 := by
  have hl : ∀ {f : OnePoint k × OnePoint k × OnePoint k × OnePoint k → OnePoint k},
      Measurable f → Measurable fun y ↦ lift (f y) := fun hf ↦ measurable_lift.comp hf
  have hb : ∀ {f g : OnePoint k × OnePoint k × OnePoint k × OnePoint k → OnePoint k},
      Measurable f → Measurable g → Measurable fun y ↦ br (lift (f y)) (lift (g y)) := by
    intro f g hf hg
    simp only [br]
    have h1 := hl hf; have h2 := hl hg
    exact (h1.fst.mul h2.snd).sub (h1.snd.mul h2.fst)
  simp only [wcr]
  exact ((hb measurable_fst measurable_snd.snd.fst).mul
    (hb measurable_snd.fst measurable_snd.snd.snd)).div
    ((hb measurable_fst measurable_snd.snd.snd).mul (hb measurable_snd.fst measurable_snd.snd.fst))

end measurability

end OrbicurveCores.M2
