/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.FordCover
import OrbicurveCores.Fuchsian.Commensurator
import OrbicurveCores.FourGroups
import OrbicurveCores.Takeuchi

/-!
# Once-punctured torus groups have finite covolume

For `x, y, z > 0` with `x² + y² + z² = xyz`, the **Fricke normal form**

  `A₀ = [[x - y/z, x/z²], [x, y/z]]`,  `B₀ = [[y - x/z, -y/z²], [-y, x/z]]`

has trace triple `(x, y, z)` and commutator `[A₀, B₀] = [[-1, -2], [0, -1]]`, which acts as
`z ↦ z + 2`. If moreover `(x, y, z)` satisfies the triangle inequalities, the isometric discs of
seven explicit elements of `⟨A₀, B₀⟩` cover `[-1, 1]`. The Ford-type covering criterion then gives
finite covolume.

Every once-punctured torus group reduces to this case:

* Nielsen descent `z ↦ xy - z` reaches a triple satisfying the triangle inequalities, since each
  step decreases `|x| + |y| + |z|` by at least `2`;
* signs are normalised (this changes the group only by `±1`, which acts trivially);
* Fricke rigidity conjugates the pair to the normal form, and conjugation by `GL(2, ℝ)` preserves
  the hyperbolic measure.

Main result: `OrbicurveCores.oneInftyFiniteCovolume`, which discharges `OneInftyFiniteCovolume`.
-/

open MeasureTheory Matrix Matrix.SpecialLinearGroup UpperHalfPlane Set
open scoped MatrixGroups

namespace OrbicurveCores.Fuchsian

section normalForm

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

/-- The Fricke normal form `A₀`. -/
noncomputable def nA : SL(2, ℝ) :=
  ⟨!![x - y / z, x / z ^ 2; x, y / z], by
    rw [det_fin_two_of]; field_simp; linear_combination -hrel⟩

/-- The Fricke normal form `B₀`. -/
noncomputable def nB : SL(2, ℝ) :=
  ⟨!![y - x / z, -y / z ^ 2; -y, x / z], by
    rw [det_fin_two_of]; field_simp; linear_combination -hrel⟩

lemma coe_nA : ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![x - y / z, x / z ^ 2; x, y / z] := rfl

lemma coe_nB : ((nB hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
    !![y - x / z, -y / z ^ 2; -y, x / z] := rfl

lemma coe_nAnB : ((nA hz hrel * nB hz hrel : SL(2, ℝ)) :
    Matrix (Fin 2) (Fin 2) ℝ) = !![z, -1 / z; z, 0] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_nA, coe_nB, Matrix.mul_fin_two]
  have hz0 : z ≠ 0 := hz.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> grind

lemma tr_nA : tr (nA hz hrel) = x := by
  simp [tr, coe_nA, trace_fin_two]

lemma tr_nB : tr (nB hz hrel) = y := by
  simp [tr, coe_nB, trace_fin_two]

lemma tr_nAnB : tr (nA hz hrel * nB hz hrel) = z := by
  rw [tr, coe_nAnB]; simp [trace_fin_two]

lemma coe_commutator_n : ((nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ *
    (nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = !![-1, -2; 0, -1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_nAnB,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, coe_nA, coe_nB,
    adjugate_fin_two, adjugate_fin_two]
  have hz0 : z ≠ 0 := hz.ne'
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one,
    Matrix.mul_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp <;> grind

/-- The interval covering for the normal form (under the triangle inequalities). -/
lemma normal_interval_cover {x y z t : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) (h1 : x < y + z) (h2 : y < x + z) (h3 : z < x + y)
    (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |z * t + z| < 1 ∨ |y * t + (y - x / z)| < 1 ∨ |x * t + y / z| < 1 ∨ |z * t + 0| < 1 ∨
    |-y * t + x / z| < 1 ∨ |-x * t + (x - y / z)| < 1 ∨ |-z * t + z| < 1 := by
  obtain ⟨X, hX⟩ : ∃ X, X = x / z := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = y / z := ⟨_, rfl⟩
  rw [← hX, ← hY]
  have hXz : X * z = x := by rw [hX]; field_simp
  have hYz : Y * z = y := by rw [hY]; field_simp
  have b1 : 0 < Y - X + 1 := by
    have : (Y - X + 1) * z = y - x + z := by linear_combination hYz - hXz
    by_contra hc; push Not at hc; nlinarith
  have b2 : 0 < x + x * X - x * y + y * Y + y := by
    have : (x + x * X - x * y + y * Y + y) * z = (x + y - z) * z := by
      linear_combination x * hXz + y * hYz + hrel
    by_contra hc; push Not at hc; nlinarith
  obtain ⟨ht1, ht2⟩ := ht
  simp only [abs_lt]
  by_cases c1 : z * t + z < 1
  · left; constructor <;> nlinarith
  right
  by_cases c2 : y * t + (y - X) < 1
  · left; constructor <;> nlinarith
  right
  by_cases c3 : x * t + Y < 1
  · left; constructor <;> nlinarith
  right
  by_cases c4 : z * t + 0 < 1
  · left; constructor <;> nlinarith
  right
  by_cases c5 : -1 < -y * t + X
  · left; constructor <;> nlinarith
  right
  by_cases c6 : -1 < -x * t + (x - Y)
  · left; constructor <;> nlinarith
  right
  constructor <;> nlinarith

/-- The commutator acts as the translation `z ↦ z + 2`. -/
lemma commutator_n_smul (w : ℍ) : (((nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ *
    (nB hz hrel)⁻¹ : SL(2, ℝ)) • w : ℍ) : ℂ) = w + 2 := by
  rw [coe_specialLinearGroup_apply]
  have e := coe_commutator_n hz hrel
  have e00 := congrFun (congrFun e 0) 0
  have e01 := congrFun (congrFun e 0) 1
  have e10 := congrFun (congrFun e 1) 0
  have e11 := congrFun (congrFun e 1) 1
  simp only [of_apply, cons_val', cons_val_zero, cons_val_one, empty_val',
    cons_val_fin_one] at e00 e01 e10 e11
  simp only [Algebra.algebraMap_self, RingHom.id_apply, e00, e01, e10, e11]
  push_cast
  field_simp
  ring

/-- **Explicit fundamental strip of the normal form group** under the triangle inequalities:
every orbit meets `-1 ≤ Re z ≤ 1`, `Im z ≥ η`. -/
theorem exists_strip_cover_normal (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y) : ∃ η > 0, ∀ w : ℍ, ∃ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel},
      γ • w ∈ {z : ℍ | z.re ∈ Icc (-1) (-1 + 2) ∧ η ≤ z.im} := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hA : (nA hz hrel) ∈ Γ := Subgroup.subset_closure (by simp)
  have hB : (nB hz hrel) ∈ Γ := Subgroup.subset_closure (by simp)
  set K := (nA hz hrel) * (nB hz hrel) * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹
  have hK : K ∈ Γ := mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB)
  have hz0 : z ≠ 0 := hz.ne'
  let g : Fin 7 → SL(2, ℝ) :=
    ![((nA hz hrel) * (nB hz hrel))⁻¹ * K, (nB hz hrel)⁻¹, (nA hz hrel),
      (nA hz hrel) * (nB hz hrel), (nB hz hrel), (nA hz hrel)⁻¹, ((nA hz hrel) * (nB hz hrel))⁻¹]
  have hg : ∀ i, g i ∈ Γ := by
    intro i
    fin_cases i <;> simp only [g] <;>
      first
        | exact mul_mem (inv_mem (mul_mem hA hB)) hK
        | exact inv_mem hB
        | exact hA
        | exact mul_mem hA hB
        | exact hB
        | exact inv_mem hA
        | exact inv_mem (mul_mem hA hB)
  refine exists_strip_cover_of_cover (a := -1) (w := 2) (by norm_num) hK
    (commutator_n_smul hz hrel) g hg ?_
  intro t ht
  have ht' : t ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> linarith [ht.1, ht.2]
  have eAB := coe_nAnB hz hrel
  have eK := coe_commutator_n hz hrel
  have e6 : ((((nA hz hrel) * (nB hz hrel))⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, 1 / z; -z, z] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eAB, adjugate_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp
    ring
  have e0 : ((((nA hz hrel) * (nB hz hrel))⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![0, -1 / z; z, z] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, e6, eK, Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
  rcases normal_interval_cover hx hy hz hrel h1 h2 h3 ht' with h | h | h | h | h | h | h
  · refine ⟨0, ?_⟩
    change |((((nA hz hrel * nB hz hrel)⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 * t +
      ((((nA hz hrel * nB hz hrel)⁻¹ * K : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1| < 1
    rw [e0]; simpa using h
  · exact ⟨1, by simpa [g, coe_nB, adjugate_fin_two] using h⟩
  · exact ⟨2, by simpa [g, coe_nA] using h⟩
  · exact ⟨3, by simpa [g, eAB] using h⟩
  · exact ⟨4, by simpa [g, coe_nB] using h⟩
  · exact ⟨5, by simpa [g, coe_nA, adjugate_fin_two] using h⟩
  · refine ⟨6, ?_⟩
    change |((((nA hz hrel * nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 0 * t +
      ((((nA hz hrel * nB hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) 1 1| < 1
    rw [e6]; simpa using h

/-- **Finite covolume of the normal form group** under the triangle inequalities. -/
theorem hasFiniteCovolume_normal (hx : 0 < x) (hy : 0 < y) (h1 : x < y + z) (h2 : y < x + z)
    (h3 : z < x + y) : HasFiniteCovolume (Subgroup.closure {nA hz hrel, nB hz hrel}) := by
  obtain ⟨η, hη, h⟩ := exists_strip_cover_normal hz hrel hx hy h1 h2 h3
  refine ⟨{z : ℍ | z.re ∈ Icc (-1) (-1 + 2) ∧ η ≤ z.im}, ?_, volume_strip_lt_top _ _ _ hη, h⟩
  exact (measurableSet_Icc.preimage continuous_re.measurable).inter
    (measurableSet_Ici.preimage continuous_im.measurable)

end normalForm

/-! ### Real Nielsen descent to the triangle inequalities -/

/-- The descent step decreases the largest coordinate by at least `2`. -/
lemma descent_step_bound {x y z : ℝ} (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
    (hx : 4 < x ^ 2) (hy : 4 < y ^ 2) (hz0 : z ≠ 0) (hc : |x| + |y| ≤ |z|) :
    |x * y - z| + 2 ≤ |z| := by
  have ha : 2 < |x| := by
    have := sq_lt_sq.mp (show (2 : ℝ) ^ 2 < x ^ 2 by norm_num; linarith)
    simpa using this
  have hb : 2 < |y| := by
    have := sq_lt_sq.mp (show (2 : ℝ) ^ 2 < y ^ 2 by norm_num; linarith)
    simpa using this
  have hcz : 0 < |z| := abs_pos.mpr hz0
  have hdc : |x * y - z| * |z| = |x| ^ 2 + |y| ^ 2 := by
    rw [← abs_mul, sq_abs, sq_abs]
    have : (x * y - z) * z = x ^ 2 + y ^ 2 := by linear_combination -hrel
    rw [this, abs_of_nonneg (by positivity)]
  have hd0 : 0 ≤ |x * y - z| := abs_nonneg _
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)]

open Realizes in
/-- **Descent.** Every realised triple on the Fricke surface with nonzero first coordinate can be
moved by Nielsen moves to one whose absolute values satisfy the triangle inequalities. -/
theorem exists_triangle {Γ : Subgroup SL(2, ℝ)} (N : ℕ) :
    ∀ x y z : ℝ, Realizes Γ x y z → x ^ 2 + y ^ 2 + z ^ 2 = x * y * z → x ≠ 0 →
      |x| + |y| + |z| ≤ 2 * N →
      ∃ x' y' z', Realizes Γ x' y' z' ∧ x' ^ 2 + y' ^ 2 + z' ^ 2 = x' * y' * z' ∧ x' ≠ 0 ∧
        |z'| < |x'| + |y'| ∧ |x'| < |y'| + |z'| ∧ |y'| < |x'| + |z'| := by
  induction N with
  | zero =>
    intro x y z _ _ hx hS
    have : 0 < |x| := abs_pos.mpr hx
    have := abs_nonneg y; have := abs_nonneg z
    push_cast at hS; linarith
  | succ N ih =>
    intro x y z hr hrel hx hS
    have hy : y ≠ 0 := by
      intro h; rw [h] at hrel; apply hx; nlinarith [sq_nonneg x, sq_nonneg z]
    have hz : z ≠ 0 := by
      intro h; rw [h] at hrel; apply hx; nlinarith [sq_nonneg x, sq_nonneg y]
    have hx4 := four_lt_sq_of_fricke hrel hx
    have hy4 := four_lt_sq_of_fricke
      (by linear_combination hrel : y ^ 2 + z ^ 2 + x ^ 2 = y * z * x) hy
    have hz4 := four_lt_sq_of_fricke
      (by linear_combination hrel : z ^ 2 + x ^ 2 + y ^ 2 = z * x * y) hz
    by_cases t1 : |z| < |x| + |y|
    · by_cases t2 : |x| < |y| + |z|
      · by_cases t3 : |y| < |x| + |z|
        · exact ⟨x, y, z, hr, hrel, hx, t1, t2, t3⟩
        · -- flip `y`: triple `(z, x, y)` then flip the last coordinate
          push Not at t3
          have hb := descent_step_bound (x := z) (y := x) (z := y)
            (by linear_combination hrel) hz4 hx4 hy (by linarith)
          refine ih z x (z * x - y) hr.cycle.cycle.flip (by linear_combination hrel) hz ?_
          push_cast at hS ⊢; linarith
      · push Not at t2
        have hb := descent_step_bound (x := y) (y := z) (z := x)
          (by linear_combination hrel) hy4 hz4 hx (by linarith)
        refine ih y z (y * z - x) hr.cycle.flip (by linear_combination hrel) hy ?_
        push_cast at hS ⊢; linarith
    · push Not at t1
      have hb := descent_step_bound hrel hx4 hy4 hz t1
      refine ih x y (x * y - z) hr.flip (by linear_combination hrel) hx ?_
      push_cast at hS ⊢; linarith

/-! ### Transport of finite covolume -/

lemma mapGL_self (γ : SL(2, ℝ)) : SpecialLinearGroup.mapGL ℝ γ = toGL γ := by
  ext i j; simp

lemma smul_eq_toGL_smul (γ : SL(2, ℝ)) (z : ℍ) : γ • z = (toGL γ) • z := by
  rw [← mapGL_self]; rfl

lemma neg_smul_SL (γ : SL(2, ℝ)) (z : ℍ) : (-γ) • z = γ • z := by
  rw [smul_eq_toGL_smul, smul_eq_toGL_smul,
    show toGL (-γ) = -toGL γ by ext1; simp [Matrix.SpecialLinearGroup.coe_neg]]
  exact UpperHalfPlane.neg_smul _ _

/-- Finite covolume is invariant under simultaneous `GL(2, ℝ)`-conjugation of generators. -/
theorem hasFiniteCovolume_of_conj {A B A₀ B₀ : SL(2, ℝ)} (g : GL (Fin 2) ℝ)
    (hA : g * toGL A * g⁻¹ = toGL A₀) (hB : g * toGL B * g⁻¹ = toGL B₀)
    (h₀ : HasFiniteCovolume (Subgroup.closure {A₀, B₀})) :
    HasFiniteCovolume (Subgroup.closure {A, B}) := by
  obtain ⟨F₀, hF₀m, hF₀v, hcov⟩ := h₀
  have hg : IsUnit (g : Matrix (Fin 2) (Fin 2) ℝ).det := g.isUnit.map Matrix.detMonoidHom
  set ψ := SL2R.conjMat (g : Matrix (Fin 2) (Fin 2) ℝ) hg
  have hψ : ∀ γ : SL(2, ℝ), toGL (ψ γ) = g * toGL γ * g⁻¹ := by
    intro γ; ext1
    simp [ψ, SL2R.coe_conjMat, Matrix.coe_units_inv]
  have hψA : ψ A = A₀ := toGL_injective (by rw [hψ, hA])
  have hψB : ψ B = B₀ := toGL_injective (by rw [hψ, hB])
  have hmap : Subgroup.closure {A₀, B₀} = (Subgroup.closure {A, B}).map ψ := by
    rw [MonoidHom.map_closure, Set.image_pair, hψA, hψB]
  have hact : ∀ (γ : SL(2, ℝ)) (z : ℍ), (ψ γ) • (g • z) = g • (γ • z) := by
    intro γ z
    rw [smul_eq_toGL_smul, smul_eq_toGL_smul, hψ, mul_smul, mul_smul, inv_smul_smul]
  refine ⟨(fun z ↦ g • z) ⁻¹' F₀, hF₀m.preimage (continuous_const_smul g).measurable, ?_, ?_⟩
  · rw [measure_preimage_smul]; exact hF₀v
  · intro z
    obtain ⟨γ₀, hγ₀, hγ₀z⟩ := hcov (g • z)
    rw [hmap] at hγ₀
    obtain ⟨γ, hγ, rfl⟩ := hγ₀
    exact ⟨γ, hγ, by simpa [hact] using hγ₀z⟩

/-- Finite covolume is insensitive to the signs of the generators. -/
theorem hasFiniteCovolume_of_signs {A B A' B' : SL(2, ℝ)} (hA : A' ∈ ({A, -A} : Set SL(2, ℝ)))
    (hB : B' ∈ ({B, -B} : Set SL(2, ℝ))) (h : HasFiniteCovolume (Subgroup.closure {A', B'})) :
    HasFiniteCovolume (Subgroup.closure {A, B}) := by
  obtain ⟨F, hFm, hFv, hcov⟩ := h
  set Γ := Subgroup.closure {A, B}
  let Hpm : Subgroup SL(2, ℝ) :=
    { carrier := {g | g ∈ Γ ∨ -g ∈ Γ}
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
  have hmemA : A ∈ Γ := Subgroup.subset_closure (by simp)
  have hmemB : B ∈ Γ := Subgroup.subset_closure (by simp)
  have hle : Subgroup.closure {A', B'} ≤ Hpm := by
    rw [Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    constructor
    · rcases hA with rfl | rfl
      · exact Or.inl hmemA
      · exact Or.inr (by simpa using hmemA)
    · rcases hB with rfl | rfl
      · exact Or.inl hmemB
      · exact Or.inr (by simpa using hmemB)
  refine ⟨F, hFm, hFv, fun z ↦ ?_⟩
  obtain ⟨γ, hγ, hγz⟩ := hcov z
  rcases hle hγ with h1 | h1
  · exact ⟨γ, h1, hγz⟩
  · exact ⟨-γ, h1, by rwa [neg_smul_SL]⟩

open Realizes in
/-- **Reduction to the normal form.** Every once-punctured torus group is, after Nielsen moves,
sign changes and `GL(2, ℝ)`-conjugation, a Fricke normal form group with triangle inequalities. -/
theorem exists_normal_form {A B : SL(2, ℝ)} (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0) :
    ∃ (x y z : ℝ) (_ : 0 < x) (_ : 0 < y) (hz : 0 < z)
      (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z),
      (x < y + z ∧ y < x + z ∧ z < x + y) ∧
      ∃ A' B' : SL(2, ℝ), Subgroup.closure {A', B'} = Subgroup.closure {A, B} ∧
        ∃ A'' ∈ ({A', -A'} : Set SL(2, ℝ)), ∃ B'' ∈ ({B', -B'} : Set SL(2, ℝ)),
          ∃ g : GL (Fin 2) ℝ, g * toGL A'' * g⁻¹ = toGL (nA hz hrel) ∧
            g * toGL B'' * g⁻¹ = toGL (nB hz hrel) := by
  have hrel := (tr_commutator_eq_neg_two_iff A B).mp hcomm
  have hr : Realizes (Subgroup.closure {A, B}) (tr A) (tr B) (tr (A * B)) :=
    ⟨A, B, rfl, rfl, rfl, rfl⟩
  obtain ⟨N, hN⟩ := exists_nat_ge ((|tr A| + |tr B| + |tr (A * B)|) / 2)
  obtain ⟨_, _, _, ⟨A', B', hcl, rfl, rfl, rfl⟩, hrel', hx', t1, t2, t3⟩ :=
    exists_triangle N _ _ _ hr hrel hA (by linarith)
  have hpos : 0 < tr A' * tr B' * tr (A' * B') := by
    rw [← hrel']; have := pow_pos (abs_pos.mpr hx') 2; rw [sq_abs] at this; positivity
  obtain ⟨A'', hA'', B'', hB'', e1, e2, e3, e4⟩ := exists_sign_normalize hpos
  have hy' : tr B' ≠ 0 := by
    intro h; rw [h] at hrel'; apply hx'; nlinarith [sq_nonneg (tr A'), sq_nonneg (tr (A' * B'))]
  have hz' : tr (A' * B') ≠ 0 := by
    intro h; rw [h] at hrel'; apply hx'; nlinarith [sq_nonneg (tr A'), sq_nonneg (tr B')]
  have hx0 : 0 < |tr A'| := abs_pos.mpr hx'
  have hy0 : 0 < |tr B'| := abs_pos.mpr hy'
  have hz0 : 0 < |tr (A' * B')| := abs_pos.mpr hz'
  have hrelxyz : |tr A'| ^ 2 + |tr B'| ^ 2 + |tr (A' * B')| ^ 2 =
      |tr A'| * |tr B'| * |tr (A' * B')| := by
    simp only [sq_abs]
    rw [← abs_mul, ← abs_mul, ← hrel', abs_of_pos (by rw [hrel']; exact hpos)]
  have hx4 : 4 < tr A'' ^ 2 := by
    rw [e1, sq_abs]; exact four_lt_sq_of_fricke hrel' hx'
  have hc : tr (A'' * B'' * A''⁻¹ * B''⁻¹) ≠ 2 := by
    rw [e4, (tr_commutator_eq_neg_two_iff A' B').mpr hrel']; norm_num
  obtain ⟨g, hgA, hgB⟩ := exists_conj_of_tr_eq (A' := nA hz0 hrelxyz) (B' := nB hz0 hrelxyz)
    hx4 hc (by rw [e1, tr_nA]) (by rw [e2, tr_nB]) (by rw [e3, tr_nAnB])
  exact ⟨_, _, _, hx0, hy0, hz0, hrelxyz, ⟨t2, t3, t1⟩, A', B', hcl, A'', hA'', B'', hB'', g,
    hgA, hgB⟩

/-- **Once-punctured torus groups have finite covolume.** -/
theorem oneInftyFiniteCovolume : OneInftyFiniteCovolume := by
  intro A B hcomm hA
  obtain ⟨x, y, z, hx, hy, hz, hrel, ⟨t1, t2, t3⟩, A', B', hcl, A'', hA'', B'', hB'', g, hgA,
    hgB⟩ := exists_normal_form hcomm hA
  rw [← hcl]
  exact hasFiniteCovolume_of_signs hA'' hB''
    (hasFiniteCovolume_of_conj g hgA hgB (hasFiniteCovolume_normal hz hrel hx hy t1 t2 t3))

end OrbicurveCores.Fuchsian

namespace OrbicurveCores

/-- `MargulisOneInfty` follows from Margulis' theorem in its standard (dense-commensurator)
form alone: the finite covolume input is now proved. -/
theorem margulisOneInfty_of_margulisDense (hM : MargulisDenseOneInfty) : MargulisOneInfty :=
  margulisOneInfty_of_dense hM Fuchsian.oneInftyFiniteCovolume

end OrbicurveCores
