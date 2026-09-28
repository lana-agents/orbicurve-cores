/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.TraceField
import OrbicurveCores.ArithTraces

/-!
# M2: rationality of the group and its commensurator

Suppose the squared traces `x², y², z²` of a normal-form group are rational. Then:

* every element of `Γ = ⟨A₀, B₀⟩` is a real multiple of a rational matrix (`isRatMul_of_mem`),
  by the "Klein grading": `A₀ ∈ x·GL₂(ℚ)` and `B₀ ∈ xz·GL₂(ℚ)`;
* so is every element of the commensurator (`isRatMul_of_mem_commensurator`), by C7.1 over `ℚ`.
-/

open Matrix Matrix.SpecialLinearGroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups

namespace OrbicurveCores.M2

local notation "𝐐" => OrbicurveCores.ratSubfield

/-- `g` is a real multiple of a rational matrix. -/
def IsRatMul (g : SL(2, ℝ)) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧ ∃ R : Matrix (Fin 2) (Fin 2) ℚ,
    (g : Matrix (Fin 2) (Fin 2) ℝ) = c • R.map ((↑) : ℚ → ℝ)

lemma mem_rat_iff {r : ℝ} : r ∈ 𝐐 ↔ ∃ q : ℚ, (q : ℝ) = r := by
  simp [OrbicurveCores.ratSubfield]

lemma isRatMul_one : IsRatMul 1 := ⟨1, one_ne_zero, 1, by ext i j; simp [Matrix.one_apply]⟩

lemma IsRatMul.mul {g h : SL(2, ℝ)} (hg : IsRatMul g) (hh : IsRatMul h) : IsRatMul (g * h) := by
  obtain ⟨c, hc, R, hR⟩ := hg
  obtain ⟨d, hd, S, hS⟩ := hh
  refine ⟨c * d, mul_ne_zero hc hd, R * S, ?_⟩
  rw [coe_mul, hR, hS, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  exact (Matrix.map_mul (f := Rat.castHom ℝ)).symm

lemma IsRatMul.inv {g : SL(2, ℝ)} (hg : IsRatMul g) : IsRatMul g⁻¹ := by
  obtain ⟨c, hc, R, hR⟩ := hg
  refine ⟨c, hc, R.adjugate, ?_⟩
  rw [coe_inv, hR, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma isRatMul_of_mem_closure {A B : SL(2, ℝ)} (hA : IsRatMul A) (hB : IsRatMul B) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) : IsRatMul γ := by
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | hg
    · exact hA
    · rw [Set.mem_singleton_iff.mp hg]; exact hB
  | one => exact isRatMul_one
  | mul g h _ _ hg hh => exact hg.mul hh
  | inv g _ hg => exact hg.inv

/-- A real multiple of a rational matrix with nonzero rational trace ratio is rational. -/
lemma slIn_of_isRatMul {g : SL(2, ℝ)} (hg : IsRatMul g) (htr : trace (g : Matrix (Fin 2) (Fin 2) ℝ)
    ∈ 𝐐) (htr0 : trace (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0) : SLIn 𝐐 g := by
  obtain ⟨c, hc, R, hR⟩ := hg
  have htrR : trace (g : Matrix (Fin 2) (Fin 2) ℝ) = c * ((trace R : ℚ) : ℝ) := by
    rw [hR, trace_smul, smul_eq_mul]
    congr 1
    simp [trace, Fin.sum_univ_two]
  have hR0 : ((trace R : ℚ) : ℝ) ≠ 0 := by
    intro h; rw [htrR, h, mul_zero] at htr0; exact htr0 rfl
  have hcQ : c ∈ 𝐐 := by
    have : c = trace (g : Matrix (Fin 2) (Fin 2) ℝ) / ((trace R : ℚ) : ℝ) := by
      rw [htrR]; field_simp
    rw [this]
    exact div_mem htr (mem_rat_iff.2 ⟨_, rfl⟩)
  intro i j
  rw [hR, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  exact mul_mem hcQ (mem_rat_iff.2 ⟨_, rfl⟩)

/-- From `(g⁻¹)ᵢₚ g_qj ∈ ℚ` for all indices, `g` is a real multiple of a rational matrix. -/
lemma isRatMul_of_mul_mem {g : SL(2, ℝ)}
    (h : ∀ i p q j, ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p *
      (g : Matrix (Fin 2) (Fin 2) ℝ) q j ∈ 𝐐) : IsRatMul g := by
  classical
  have hne : ∃ i p, ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p ≠ 0 := by
    by_contra hno
    push Not at hno
    have : ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by ext i p; exact hno i p
    have hdet := (g⁻¹).2
    rw [this, Matrix.det_zero] at hdet
    exact zero_ne_one hdet
  obtain ⟨i, p, hip⟩ := hne
  choose R hR using fun q j ↦ mem_rat_iff.1 (h i p q j)
  refine ⟨(((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p)⁻¹, inv_ne_zero hip,
    Matrix.of fun q j ↦ R q j, ?_⟩
  ext q j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, hR]
  field_simp

section normalForm

open Fuchsian

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)
  {X Y Z : ℚ} (hX : x ^ 2 = X) (hY : y ^ 2 = Y) (hZ : z ^ 2 = Z)
include hz hrel

omit hrel in
lemma x_ne_zero' (h : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z) : x ≠ 0 := by
  rintro rfl
  nlinarith [sq_nonneg y, sq_nonneg z, hz]

include hX hY hZ

omit hz in
lemma xyz_eq : x * y * z = ((X + Y + Z : ℚ) : ℝ) := by
  rw [← hrel]; push_cast; rw [hX, hY, hZ]

lemma isRatMul_nA : IsRatMul (nA hz hrel) := by
  have hx := x_ne_zero' hz hrel
  set W : ℚ := X + Y + Z
  have hW : x * y * z = W := xyz_eq hrel hX hY hZ
  have hX0 : (X : ℝ) ≠ 0 := by rw [← hX]; positivity
  have hZ0 : (Z : ℝ) ≠ 0 := by rw [← hZ]; positivity
  refine ⟨x, hx, !![1 - W / (X * Z), 1 / Z; 1, W / (X * Z)], ?_⟩
  rw [coe_nA]
  have hz0 : z ≠ 0 := hz.ne'
  ext i j; fin_cases i <;> fin_cases j <;> simp [← hX, ← hZ, ← hW] <;> field_simp

lemma isRatMul_nB : IsRatMul (nB hz hrel) := by
  have hx := x_ne_zero' hz hrel
  set W : ℚ := X + Y + Z
  have hW : x * y * z = W := xyz_eq hrel hX hY hZ
  have hX0 : (X : ℝ) ≠ 0 := by rw [← hX]; positivity
  have hZ0 : (Z : ℝ) ≠ 0 := by rw [← hZ]; positivity
  have hz0 : z ≠ 0 := hz.ne'
  refine ⟨x * z, mul_ne_zero hx hz0,
    !![W / (X * Z) - 1 / Z, -(W / (X * Z ^ 2)); -(W / (X * Z)), 1 / Z], ?_⟩
  rw [coe_nB]
  ext i j; fin_cases i <;> fin_cases j <;> simp [← hX, ← hZ, ← hW] <;> field_simp

/-- **Klein grading.** Every element of the normal-form group is a real multiple of a rational
matrix. -/
theorem isRatMul_of_mem {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel}) :
    IsRatMul γ :=
  isRatMul_of_mem_closure (isRatMul_nA hz hrel hX hY hZ) (isRatMul_nB hz hrel hX hY hZ) hγ

/-- **C7 over `ℚ`.** Every element of the commensurator is a real multiple of a rational matrix. -/
theorem isRatMul_of_mem_commensurator {δ : SL(2, ℝ)}
    (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) : IsRatMul δ := by
  have hx := x_ne_zero' hz hrel
  set W : ℚ := X + Y + Z
  have hW : x * y * z = W := xyz_eq hrel hX hY hZ
  have hz0 : z ≠ 0 := hz.ne'
  have hZ0 : (Z : ℝ) ≠ 0 := by rw [← hZ]; positivity
  have hax : x * (x - y / z) ∈ 𝐐 := by
    refine mem_rat_iff.2 ⟨X - W / Z, ?_⟩
    push_cast; rw [← hX, ← hZ, ← hW]; field_simp
  have hbx : (x - y / z) ^ 2 ∈ 𝐐 := by
    refine mem_rat_iff.2 ⟨X - 2 * W / Z + Y / Z, ?_⟩
    push_cast; rw [← hX, ← hY, ← hZ, ← hW]; field_simp; ring
  have hcx : x ^ 2 ∈ 𝐐 := mem_rat_iff.2 ⟨X, hX.symm⟩
  refine isRatMul_of_mul_mem (mul_mem_of_mem_commensurator' 𝐐 hz hrel hax hbx hcx ?_ hδ)
  intro n γ hγ htr
  refine slIn_of_isRatMul (isRatMul_of_mem hz hrel hX hY hZ hγ) ?_ ?_ <;> rw [htr]
  · exact mem_rat_iff.2 ⟨2 * (-1) ^ n, by push_cast; ring⟩
  · exact mul_ne_zero two_ne_zero (pow_ne_zero _ (by norm_num))

end normalForm

end OrbicurveCores.M2
