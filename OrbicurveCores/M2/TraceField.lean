/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fuchsian.PingPong

/-!
# M2, part C7: the commensurator lives over the trace field

Let `F ⊆ ℝ` be a subfield and `g ∈ SL(2, ℝ)`. Suppose the conjugates `g E₁₂ g⁻¹` and `g N g⁻¹` of
two matrices with entries in `F` have entries in `F`, where `N = [[a, b], [c, -a]]`
(`c ≠ 0`) has a different kernel. Then `E₁₂` and `N` generate `M₂(F)` as an
algebra, so conjugation by `g` preserves `M₂(F)`, and all products `gᵢₐ (g⁻¹)ᵦⱼ` lie in `F`
(`mul_mem_of_conj_gens`).

For a once-punctured torus group in Fricke normal form (entries in `F = ℚ(x, y, z)`), every
element `δ` of the commensurator has this property. Suitable powers of the parabolic
`K = [A₀, B₀]` and of `A₀ K A₀⁻¹` lie in `Γ ∩ δ⁻¹ Γ δ` and are conjugated into `Γ`
(`mul_mem_of_mem_commensurator`). Hence `δ` is a real multiple of a matrix over `F`, which
defines `ρ : Comm(Γ) → PGL₂(F)`.
-/

open Matrix Matrix.SpecialLinearGroup
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores.M2

variable (F : Subfield ℝ)

/-- A real matrix has all entries in `F`. -/
def MatIn (X : Matrix (Fin 2) (Fin 2) ℝ) : Prop := ∀ i j, X i j ∈ F

/-- An element of `SL(2, ℝ)` has all entries in `F`. -/
def SLIn (g : SL(2, ℝ)) : Prop := MatIn F (g : Matrix (Fin 2) (Fin 2) ℝ)

/-- **Generation.** If conjugation by `g` maps `E₁₂` and a matrix `N` over `F` with
`N₁₀ ≠ 0` into `M₂(F)`, then `gᵢₐ (g⁻¹)ᵦⱼ ∈ F` for all indices. -/
theorem mul_mem_of_conj_gens (g : SL(2, ℝ)) {a b c : ℝ} (ha : a ∈ F) (hb : b ∈ F)
    (hc : c ∈ F) (hc0 : c ≠ 0)
    (h1 : MatIn F ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 0, 0] *
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)))
    (h2 : MatIn F ((g : Matrix (Fin 2) (Fin 2) ℝ) * !![a, b; c, -a] *
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)))
    (i p q j : Fin 2) :
    (g : Matrix (Fin 2) (Fin 2) ℝ) i p * ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) q j ∈ F := by
  set G : Matrix (Fin 2) (Fin 2) ℝ := g.1
  set H : Matrix (Fin 2) (Fin 2) ℝ := (g⁻¹).1
  have hHG : H * G = 1 := by
    simp only [H, G, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  -- the set of matrices over `F` whose conjugates are over `F` is an `F`-subalgebra
  let S : Set (Matrix (Fin 2) (Fin 2) ℝ) := {X | MatIn F X ∧ MatIn F (G * X * H)}
  have hmul : ∀ X Y, X ∈ S → Y ∈ S → X * Y ∈ S := by
    intro X Y hX hY
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simp only [Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem (mul_mem (hX.1 _ _) (hY.1 _ _)) (mul_mem (hX.1 _ _) (hY.1 _ _))
    · have : G * (X * Y) * H = (G * X * H) * (G * Y * H) := by
        rw [show (G * X * H) * (G * Y * H) = G * X * (H * G) * Y * H by
          simp only [Matrix.mul_assoc], hHG]
        simp only [Matrix.mul_one, Matrix.mul_assoc]
      rw [this, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem (mul_mem (hX.2 _ _) (hY.2 _ _)) (mul_mem (hX.2 _ _) (hY.2 _ _))
  have hlin : ∀ (s t : ℝ) X Y, s ∈ F → t ∈ F → X ∈ S → Y ∈ S → s • X + t • Y ∈ S := by
    intro s t X Y hs ht hX hY
    refine ⟨fun i j ↦ ?_, fun i j ↦ ?_⟩
    · simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact add_mem (mul_mem hs (hX.1 _ _)) (mul_mem ht (hY.1 _ _))
    · rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.smul_mul]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      exact add_mem (mul_mem hs (hX.2 _ _)) (mul_mem ht (hY.2 _ _))
  have hE12 : !![(0 : ℝ), 1; 0, 0] ∈ S := by
    refine ⟨fun i j ↦ ?_, h1⟩
    fin_cases i <;> fin_cases j <;> simp [zero_mem, one_mem]
  have hN2 : !![a, b; c, -a] ∈ S := by
    refine ⟨fun i j ↦ ?_, h2⟩
    fin_cases i <;> fin_cases j <;> simp [ha, hb, hc]
  have hc1 : c⁻¹ ∈ F := inv_mem hc
  -- the matrix units
  have hE11 : !![(1 : ℝ), 0; 0, 0] ∈ S := by
    have h := hlin c⁻¹ (c⁻¹ * a) _ _ hc1 (mul_mem hc1 ha)
      (hmul _ _ hE12 hN2) hE12
    convert h using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
    field_simp
  have hE22 : !![(0 : ℝ), 0; 0, 1] ∈ S := by
    have h := hlin c⁻¹ (-(c⁻¹ * a)) _ _ hc1 (neg_mem (mul_mem hc1 ha))
      (hmul _ _ hN2 hE12) hE12
    convert h using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
    field_simp
  have hE21 : !![(0 : ℝ), 0; 1, 0] ∈ S := by
    -- `E₂₁ = (N - a E₁₁ + a E₂₂ - b E₁₂) / c`
    have h3 := hlin (-a) a _ _ (neg_mem ha) ha hE11 hE22
    have h4 := hlin 1 1 _ _ (one_mem _) (one_mem _) hN2 h3
    have h5 := hlin c⁻¹ (-(c⁻¹ * b)) _ _ hc1 (neg_mem (mul_mem hc1 hb)) h4 hE12
    convert h5 using 1
    ext i j; fin_cases i <;> fin_cases j <;> simp
    field_simp
  -- read off the products
  fin_cases p <;> fin_cases q
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hE11.2 i j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hE12.2 i j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hE21.2 i j
  · simpa [Matrix.mul_apply, Fin.sum_univ_two] using hE22.2 i j

/-- Matrices over `F` with determinant one are closed under the group operations: every element of
`closure {A, B}` is over `F` if `A` and `B` are. -/
theorem slIn_of_mem_closure {A B : SL(2, ℝ)} (hA : SLIn F A) (hB : SLIn F B) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) : SLIn F γ := by
  have hmul : ∀ g h : SL(2, ℝ), SLIn F g → SLIn F h → SLIn F (g * h) := by
    intro g h hg hh i j
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem (mul_mem (hg _ _) (hh _ _)) (mul_mem (hg _ _) (hh _ _))
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | hg
    · exact hA
    · rw [Set.mem_singleton_iff.mp hg]; exact hB
  | one =>
    intro i j; simp only [Matrix.SpecialLinearGroup.coe_one]
    fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]
  | mul g h _ _ hg hh => exact hmul g h hg hh
  | inv g _ hg =>
    intro i j
    rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_fin_two]
    fin_cases i <;> fin_cases j <;> simp [hg _ _]

/-- A power of each element of `Γ` is conjugated into `Γ` by a commensurating element. -/
theorem exists_pow_conj_mem {Γ : Subgroup SL(2, ℝ)} {δ : SL(2, ℝ)} (hδ : δ ∈ commensurator Γ)
    {P : SL(2, ℝ)} (hP : P ∈ Γ) : ∃ n, 0 < n ∧ δ⁻¹ * P ^ n * δ ∈ Γ := by
  obtain ⟨n, hn, -, hmem⟩ := Subgroup.exists_pow_mem_of_relIndex_ne_zero hδ.1 hP
  refine ⟨n, hn, ?_⟩
  have h := (Subgroup.mem_inf.mp hmem).1
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at h
  simpa using h

/-- Powers of `P = -(1 + 2N)` with `N² = 0`. -/
lemma coe_pow_of_nilpotent {P : SL(2, ℝ)} {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = -(1 + (2 : ℝ) • N)) (hN : N * N = 0) (n : ℕ) :
    ((P ^ n : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (-1 : ℝ) ^ n • (1 + (2 * n : ℝ) • N) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih, hP]
    simp only [Matrix.smul_mul, Matrix.mul_neg, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hN, smul_zero, add_zero, pow_succ]
    push_cast
    ext i j
    simp only [Matrix.neg_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring

/-- If `g Pⁿ g⁻¹` is over `F` for some `n > 0`, where `P = -(1 + 2N)`, `N² = 0`, then `g N g⁻¹`
is over `F`. -/
lemma matIn_conj_of_pow {P g : SL(2, ℝ)} {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = -(1 + (2 : ℝ) • N)) (hN : N * N = 0) {n : ℕ}
    (hn : 0 < n) (h : SLIn F (g * P ^ n * g⁻¹)) :
    MatIn F ((g : Matrix (Fin 2) (Fin 2) ℝ) * N *
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) := by
  have hg : (g : Matrix (Fin 2) (Fin 2) ℝ) * ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have e : ((g * P ^ n * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (-1 : ℝ) ^ n • (1 + (2 * n : ℝ) • ((g : Matrix (Fin 2) (Fin 2) ℝ) * N *
        ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ))) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_pow_of_nilpotent hP hN, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, hg, Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  have hij : ((g * P ^ n * g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i j ∈ F := h i j
  rw [e] at hij
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at hij
  have hn' : (2 * n : ℝ) ≠ 0 := by positivity
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℝ) i j ∈ F := by
    rw [Matrix.one_apply]; split_ifs <;> simp [one_mem, zero_mem]
  have hpow : ((-1 : ℝ) ^ n) ∈ F := pow_mem (neg_mem (one_mem _)) n
  have hsq : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ n) = 1 := by rw [← mul_pow]; norm_num
  have key : ((g : Matrix (Fin 2) (Fin 2) ℝ) * N *
      ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) i j =
      (2 * n : ℝ)⁻¹ * ((-1 : ℝ) ^ n * ((-1 : ℝ) ^ n * ((1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
        2 * n * ((g : Matrix (Fin 2) (Fin 2) ℝ) * N *
          ((g⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ)) i j)) -
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) := by
    rw [← mul_assoc ((-1 : ℝ) ^ n), hsq]; field_simp; ring
  rw [key]
  have h2n : (2 * n : ℝ) ∈ F := mul_mem (ofNat_mem F 2) (natCast_mem F n)
  exact mul_mem (inv_mem h2n) (sub_mem (mul_mem hpow hij) h1)

section normalForm

open OrbicurveCores.Fuchsian

variable {x y z : ℝ} (hz : 0 < z) (hrel : x ^ 2 + y ^ 2 + z ^ 2 = x * y * z)

lemma E12_sq : !![(0 : ℝ), 1; 0, 0] * !![(0 : ℝ), 1; 0, 0] = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The conjugate `A₀ E₁₂ A₀⁻¹`. -/
lemma nA_E12_nA_inv :
    ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 0, 0] *
      (((nA hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![-x * (x - y / z), (x - y / z) ^ 2; -x ^ 2, -(-x * (x - y / z))] := by
  rw [Matrix.SpecialLinearGroup.coe_inv, coe_nA, adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

omit hz hrel in
lemma trace_conj_pow {δ P : SL(2, ℝ)} {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hP : (P : Matrix (Fin 2) (Fin 2) ℝ) = -(1 + (2 : ℝ) • N)) (hN : N * N = 0)
    (hNtr : N.trace = 0) (n : ℕ) :
    ((δ⁻¹ * P ^ n * δ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * (-1) ^ n := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, coe_pow_of_nilpotent hP hN,
    Matrix.trace_smul, Matrix.trace_add, Matrix.trace_smul, hNtr, Matrix.trace_one]
  simp; ring

/-- **C7.1, general form.** Let `F ⊆ ℝ` be a subfield with `x², x(x − y/z), (x − y/z)² ∈ F`, and
suppose every element of the normal-form group `Γ` with trace `±2` has entries in `F`. Then every
element `δ` of the commensurator satisfies `(δ⁻¹)ᵢₚ δ_qj ∈ F`. -/
theorem mul_mem_of_mem_commensurator' (hax : x * (x - y / z) ∈ F) (hbx : (x - y / z) ^ 2 ∈ F)
    (hcx : x ^ 2 ∈ F)
    (hF : ∀ n : ℕ, ∀ γ ∈ Subgroup.closure {nA hz hrel, nB hz hrel},
      (γ : Matrix (Fin 2) (Fin 2) ℝ).trace = 2 * (-1) ^ n → SLIn F γ)
    {δ : SL(2, ℝ)} (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel}))
    (i p q j : Fin 2) :
    ((δ⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p * (δ : Matrix (Fin 2) (Fin 2) ℝ) q j ∈ F := by
  set Γ := Subgroup.closure {nA hz hrel, nB hz hrel}
  have hx0 : x ≠ 0 := by
    rintro rfl; nlinarith [sq_nonneg y]
  have hAΓ : nA hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  have hBΓ : nB hz hrel ∈ Γ := Subgroup.subset_closure (by simp)
  set K := nA hz hrel * nB hz hrel * (nA hz hrel)⁻¹ * (nB hz hrel)⁻¹ with hK
  have hKΓ : K ∈ Γ := mul_mem (mul_mem (mul_mem hAΓ hBΓ) (inv_mem hAΓ)) (inv_mem hBΓ)
  have hKc : (K : Matrix (Fin 2) (Fin 2) ℝ) = -(1 + (2 : ℝ) • !![(0 : ℝ), 1; 0, 0]) := by
    rw [hK, coe_commutator_n]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  set N2 : Matrix (Fin 2) (Fin 2) ℝ := ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
      !![0, 1; 0, 0] * (((nA hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) with hN2
  have hAA : (((nA hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
      ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hAA' : ((nA hz hrel : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) *
      (((nA hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hN2sq : N2 * N2 = 0 := by
    rw [hN2]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (((nA hz hrel)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ), hAA,
      Matrix.one_mul, ← Matrix.mul_assoc !![(0 : ℝ), 1; 0, 0], E12_sq, Matrix.zero_mul,
      Matrix.mul_zero]
  have hN2tr : N2.trace = 0 := by
    rw [hN2, nA_E12_nA_inv]; simp [Matrix.trace_fin_two]
  set K2 := nA hz hrel * K * (nA hz hrel)⁻¹
  have hK2Γ : K2 ∈ Γ := mul_mem (mul_mem hAΓ hKΓ) (inv_mem hAΓ)
  have hK2c : (K2 : Matrix (Fin 2) (Fin 2) ℝ) = -(1 + (2 : ℝ) • N2) := by
    simp only [K2, Matrix.SpecialLinearGroup.coe_mul, hKc, hN2, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hAA', Matrix.mul_smul, Matrix.smul_mul]
  obtain ⟨n1, hn1, h1⟩ := exists_pow_conj_mem hδ hKΓ
  obtain ⟨n2, hn2, h2⟩ := exists_pow_conj_mem hδ hK2Γ
  have h1F : SLIn F (δ⁻¹ * K ^ n1 * δ⁻¹⁻¹) := by
    rw [inv_inv]
    exact hF n1 _ h1 (trace_conj_pow hKc E12_sq (by simp [Matrix.trace_fin_two]) n1)
  have h2F : SLIn F (δ⁻¹ * K2 ^ n2 * δ⁻¹⁻¹) := by
    rw [inv_inv]
    exact hF n2 _ h2 (trace_conj_pow hK2c hN2sq hN2tr n2)
  have e1 := matIn_conj_of_pow F hKc E12_sq hn1 h1F
  have e2 := matIn_conj_of_pow F hK2c hN2sq hn2 h2F
  rw [hN2, nA_E12_nA_inv] at e2
  have := mul_mem_of_conj_gens F δ⁻¹ (a := -x * (x - y / z)) (b := (x - y / z) ^ 2)
    (c := -x ^ 2) (by rw [neg_mul]; exact neg_mem hax) hbx (neg_mem hcx)
    (neg_ne_zero.mpr (pow_ne_zero 2 hx0)) e1 e2 i p q j
  rwa [inv_inv] at this

/-- **C7.1.** For a once-punctured torus group in Fricke normal form and a subfield `F`
containing `x, y, z`, every element `δ` of the commensurator satisfies `(δ⁻¹)ᵢₚ δ_qj ∈ F`. So
`δ` is a real multiple of a matrix over `F`. -/
theorem mul_mem_of_mem_commensurator (hxF : x ∈ F) (hyF : y ∈ F) (hzF : z ∈ F) {δ : SL(2, ℝ)}
    (hδ : δ ∈ commensurator (Subgroup.closure {nA hz hrel, nB hz hrel})) (i p q j : Fin 2) :
    ((δ⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) i p * (δ : Matrix (Fin 2) (Fin 2) ℝ) q j ∈ F := by
  have hYF : y / z ∈ F := div_mem hyF hzF
  have hAF : SLIn F (nA hz hrel) := by
    intro i j; rw [coe_nA]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one]
    exacts [sub_mem hxF hYF, div_mem hxF (pow_mem hzF 2), hxF, hYF]
  have hBF : SLIn F (nB hz hrel) := by
    intro i j; rw [coe_nB]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, of_apply, cons_val', cons_val_zero,
        cons_val_one, cons_val_fin_one]
    all_goals first
      | exact sub_mem hyF (div_mem hxF hzF) | exact div_mem hyF (pow_mem hzF 2)
      | exact neg_mem (div_mem hyF (pow_mem hzF 2)) | exact hyF | exact neg_mem hyF
      | exact div_mem hxF hzF | exact div_mem (neg_mem hyF) (pow_mem hzF 2)
  exact mul_mem_of_mem_commensurator' F hz hrel (mul_mem hxF (sub_mem hxF hYF))
    (pow_mem (sub_mem hxF hYF) 2) (pow_mem hxF 2)
    (fun _ γ hγ _ ↦ slIn_of_mem_closure F hAF hBF hγ) hδ i p q j

end normalForm

end OrbicurveCores.M2
