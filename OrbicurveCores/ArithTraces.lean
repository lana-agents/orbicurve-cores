/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fricke

/-!
# Traces in arithmetic subgroups of `SL(2, ℝ)`

A subgroup `Γ ⊆ SL(2, ℝ)` is *arithmetic* (in the non-cocompact sense) if some `GL(2, ℝ)`-conjugate
of it is commensurable with `SL(2, ℤ)`. We use Mathlib's `Subgroup.IsArithmetic` for subgroups of
`GL(2, ℝ)` (commensurable with the image `𝒮ℒ` of `SL(2, ℤ)`).

The non-cocompact arithmetic Fuchsian groups are exactly the groups commensurable (up to
conjugacy) with `SL(2, ℤ)`: the quaternion algebra of a non-cocompact arithmetic group is
`M₂(ℚ)`. So this is the notion of arithmeticity relevant for the `(1;∞)`-groups
([Take2]; [Corr], Def. 2.2–2.3).

## Main results

* `OrbicurveCores.mul_mem_rat_of_mem_commensurator`: every `g` in the commensurator of `SL(2, ℤ)`
  in `GL(2, ℝ)` is a real multiple of a rational matrix. Concretely, all products
  `(g⁻¹)ᵢₐ gᵦⱼ` are rational.
* `OrbicurveCores.tr_mul_tr_inv_mem_rat`: hence `tr g · tr g⁻¹ = (tr g)² / det g ∈ ℚ`.
* `OrbicurveCores.IsArithmeticSL.sq_tr_int`: if `Γ ⊆ SL(2, ℝ)` is arithmetic, then
  `(tr γ)² ∈ ℤ` for every `γ ∈ Γ`. It is rational by the above, and an algebraic integer because
  `γⁿ` is conjugate into `SL(2, ℤ)` for some `n ≥ 1` and `tr γⁿ = Vₙ(tr γ)`.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup Polynomial
open Subgroup.Commensurable (commensurator)
open scoped MatrixGroups Pointwise

namespace OrbicurveCores

/-- The rational numbers inside `ℝ`, as a subfield. -/
noncomputable def ratSubfield : Subfield ℝ := (Rat.castHom ℝ).fieldRange

local notation "𝐐" => ratSubfield

lemma intCast_mem_rat (n : ℤ) : (n : ℝ) ∈ 𝐐 := ⟨n, by simp⟩

/-- Elements of `𝒮ℒ` have integral entries. -/
lemma entry_int_of_mem_SL {M : GL (Fin 2) ℝ} (hM : M ∈ 𝒮ℒ) (i j : Fin 2) :
    ∃ n : ℤ, (M : Matrix (Fin 2) (Fin 2) ℝ) i j = n := by
  obtain ⟨γ, rfl⟩ := hM
  exact ⟨γ i j, by simp⟩

lemma trace_int_of_mem_SL {M : GL (Fin 2) ℝ} (hM : M ∈ 𝒮ℒ) :
    ∃ n : ℤ, trace (M : Matrix (Fin 2) (Fin 2) ℝ) = n := by
  obtain ⟨a, ha⟩ := entry_int_of_mem_SL hM 0 0
  obtain ⟨b, hb⟩ := entry_int_of_mem_SL hM 1 1
  exact ⟨a + b, by simp [trace_fin_two, ha, hb]⟩

/-- If `g` commensurates `𝒮ℒ` then for every `u ∈ 𝒮ℒ` some positive power of `u` is conjugated
into `𝒮ℒ` by `g`. -/
lemma exists_conj_pow_mem {g : GL (Fin 2) ℝ} (hg : g ∈ commensurator 𝒮ℒ) {u : GL (Fin 2) ℝ}
    (hu : u ∈ 𝒮ℒ) : ∃ n : ℕ, 0 < n ∧ g⁻¹ * u ^ n * g ∈ 𝒮ℒ := by
  obtain ⟨n, hn, -, hmem⟩ := exists_pow_mem_of_relIndex_ne_zero hg.1 hu
  refine ⟨n, hn, ?_⟩
  have h := (Subgroup.mem_inf.mp hmem).1
  rw [mem_pointwise_smul_iff_inv_smul_mem] at h
  simpa only [MulEquiv.coe_toMonoidHom, ← ConjAct.toConjAct_inv, ConjAct.toConjAct_smul,
    inv_inv] using h

/-- The lower unipotent generator of `SL(2, ℤ)`. -/
def lowerL : SL(2, ℤ) := ⟨!![1, 0; 1, 1], by simp [det_fin_two]⟩

lemma mapGL_T_pow (n : ℕ) :
    ((mapGL ℝ (ModularGroup.T ^ n) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, (n : ℝ); 0, 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, map_mul, Units.val_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.coe_T, mul_apply, Fin.sum_univ_two]
    ring

lemma mapGL_lowerL_pow (n : ℕ) :
    ((mapGL ℝ (lowerL ^ n) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      !![1, 0; (n : ℝ), 1] := by
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, map_mul, Units.val_mul, ih]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [lowerL, mul_apply, Fin.sum_univ_two]

/-- **The commensurator of `SL(2, ℤ)` in `GL(2, ℝ)` consists of real multiples of rational
matrices**: all products `(g⁻¹)ᵢₐ gᵦⱼ` are rational. -/
theorem mul_mem_rat_of_mem_commensurator {g : GL (Fin 2) ℝ} (hg : g ∈ commensurator 𝒮ℒ)
    (i a b j : Fin 2) :
    ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) i a * (g : Matrix (Fin 2) (Fin 2) ℝ) b j
      ∈ 𝐐 := by
  set h : Matrix (Fin 2) (Fin 2) ℝ := ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) with hh
  set G : Matrix (Fin 2) (Fin 2) ℝ := (g : Matrix (Fin 2) (Fin 2) ℝ) with hG
  have hhG : h * G = 1 := by simp [hh, hG]
  have hGh : G * h = 1 := by simp [hh, hG]
  have hhG' : ∀ i j, h i 0 * G 0 j + h i 1 * G 1 j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j; rw [← hhG]; simp [mul_apply, Fin.sum_univ_two]
  have hGh' : ∀ i j, G i 0 * h 0 j + G i 1 * h 1 j = (1 : Matrix (Fin 2) (Fin 2) ℝ) i j := by
    intro i j; rw [← hGh]; simp [mul_apply, Fin.sum_univ_two]
  have one_mem : ∀ i j, (1 : Matrix (Fin 2) (Fin 2) ℝ) i j ∈ 𝐐 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]
  -- the upper unipotent
  have h01 : ∀ i j, h i 0 * G 1 j ∈ 𝐐 := by
    obtain ⟨n, hn, hmem⟩ := exists_conj_pow_mem hg (u := mapGL ℝ ModularGroup.T) ⟨_, rfl⟩
    intro i j
    obtain ⟨m, hm⟩ := entry_int_of_mem_SL hmem i j
    rw [← map_pow] at hm
    have key : (g⁻¹ * mapGL ℝ (ModularGroup.T ^ n) * g : GL (Fin 2) ℝ) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + n * (h i 0 * G 1 j) := by
      rw [← hhG' i j]
      simp only [Units.val_mul, mapGL_T_pow, hh, hG]
      simp [mul_apply, Fin.sum_univ_two]
      ring
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : h i 0 * G 1 j = ((m : ℝ) - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) / n := by
      rw [← hm, key]; field_simp; ring
    rw [this]
    exact div_mem (sub_mem (intCast_mem_rat m) (one_mem i j)) (natCast_mem _ n)
  -- the lower unipotent
  have h10 : ∀ i j, h i 1 * G 0 j ∈ 𝐐 := by
    obtain ⟨n, hn, hmem⟩ := exists_conj_pow_mem hg (u := mapGL ℝ lowerL) ⟨_, rfl⟩
    intro i j
    obtain ⟨m, hm⟩ := entry_int_of_mem_SL hmem i j
    rw [← map_pow] at hm
    have key : (g⁻¹ * mapGL ℝ (lowerL ^ n) * g : GL (Fin 2) ℝ) i j =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) i j + n * (h i 1 * G 0 j) := by
      rw [← hhG' i j]
      simp only [Units.val_mul, mapGL_lowerL_pow, hh, hG]
      simp [mul_apply, Fin.sum_univ_two]
      ring
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have : h i 1 * G 0 j = ((m : ℝ) - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j) / n := by
      rw [← hm, key]; field_simp; ring
    rw [this]
    exact div_mem (sub_mem (intCast_mem_rat m) (one_mem i j)) (natCast_mem _ n)
  -- the diagonal patterns, via `E₀₁ E₁₀ = E₀₀` and `E₁₀ E₀₁ = E₁₁`
  have h00 : ∀ i j, h i 0 * G 0 j ∈ 𝐐 := by
    intro i j
    have : h i 0 * G 0 j =
        (h i 0 * G 1 0) * (h 0 1 * G 0 j) + (h i 0 * G 1 1) * (h 1 1 * G 0 j) := by
      have := hGh' 1 1
      simp at this
      linear_combination (-(h i 0 * G 0 j)) * this
    rw [this]
    exact add_mem (mul_mem (h01 _ _) (h10 _ _)) (mul_mem (h01 _ _) (h10 _ _))
  have h11 : ∀ i j, h i 1 * G 1 j ∈ 𝐐 := by
    intro i j
    have : h i 1 * G 1 j =
        (h i 1 * G 0 0) * (h 0 0 * G 1 j) + (h i 1 * G 0 1) * (h 1 0 * G 1 j) := by
      have := hGh' 0 0
      simp at this
      linear_combination (-(h i 1 * G 1 j)) * this
    rw [this]
    exact add_mem (mul_mem (h10 _ _) (h01 _ _)) (mul_mem (h10 _ _) (h01 _ _))
  fin_cases a <;> fin_cases b
  · exact h00 i j
  · exact h01 i j
  · exact h10 i j
  · exact h11 i j

/-- For `g` in the commensurator of `SL(2, ℤ)`, `tr g · tr g⁻¹` (which is `(tr g)² / det g`) is
rational. -/
theorem tr_mul_tr_inv_mem_rat {g : GL (Fin 2) ℝ} (hg : g ∈ commensurator 𝒮ℒ) :
    trace (g : Matrix (Fin 2) (Fin 2) ℝ) * trace ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      ∈ 𝐐 := by
  have e : trace (g : Matrix (Fin 2) (Fin 2) ℝ) *
      trace ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
      ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 +
      ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 +
      (((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 * (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 +
      ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 1 *
        (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1) := by
    simp [trace_fin_two]; ring
  rw [e]
  have := mul_mem_rat_of_mem_commensurator hg
  exact add_mem (add_mem (this _ _ _ _) (this _ _ _ _)) (add_mem (this _ _ _ _) (this _ _ _ _))

/-- A subgroup of `SL(2, ℝ)` is **arithmetic** (non-cocompact case) if some `GL(2, ℝ)`-conjugate
of its image in `GL(2, ℝ)` is commensurable with `SL(2, ℤ)`. -/
def IsArithmeticSL (Γ : Subgroup SL(2, ℝ)) : Prop :=
  ∃ g : GL (Fin 2) ℝ, (ConjAct.toConjAct g • Γ.map toGL).IsArithmetic

/-- If `x ∈ ℝ` is a root of `Vₙ - m` for some `n ≥ 1`, `m ∈ ℤ`, then `x` is an algebraic integer. -/
lemma isIntegral_of_lucas_eq {x : ℝ} {n : ℕ} (hn : 0 < n) {m : ℤ}
    (h : (lucas n).eval₂ (Int.castRingHom ℝ) x = m) : IsIntegral ℤ x := by
  refine ⟨lucas n - C m, ?_, ?_⟩
  · apply (lucas_monic hn).sub_of_left
    refine lt_of_le_of_lt degree_C_le ?_
    rw [degree_eq_natDegree (lucas_monic hn).ne_zero]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
    rw [zero_add, (lucas_monic_natDegree k).2]
    exact_mod_cast Nat.succ_pos k
  · rw [eval₂_sub, eval₂_C]
    rw [show algebraMap ℤ ℝ = Int.castRingHom ℝ from rfl, h]
    simp

/-- **Traces in arithmetic groups.** If `Γ ⊆ SL(2, ℝ)` is arithmetic then `(tr γ)² ∈ ℤ` for all
`γ ∈ Γ`. -/
theorem IsArithmeticSL.sq_tr_int {Γ : Subgroup SL(2, ℝ)} (hΓ : IsArithmeticSL Γ) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Γ) : ∃ m : ℤ, tr γ ^ 2 = m := by
  obtain ⟨g, hΓ'⟩ := hΓ
  set Γ' := ConjAct.toConjAct g • Γ.map toGL
  set γ' : GL (Fin 2) ℝ := g * toGL γ * g⁻¹ with hγ'def
  have hγ' : γ' ∈ Γ' := by
    have := smul_mem_pointwise_smul (toGL γ) (ConjAct.toConjAct g) (Γ.map toGL)
      (mem_map_of_mem _ hγ)
    rwa [ConjAct.toConjAct_smul] at this
  have hcomm : Commensurable Γ' 𝒮ℒ := hΓ'.is_commensurable
  -- `γ'` commensurates `𝒮ℒ`
  have hγ'comm : γ' ∈ commensurator 𝒮ℒ := by
    rw [← Commensurable.eq hcomm, Commensurable.commensurator_mem_iff,
      conjAct_pointwise_smul_eq_self (le_normalizer hγ')]
  -- traces
  have trγ' : trace (γ' : Matrix (Fin 2) (Fin 2) ℝ) = tr γ := by
    simp only [hγ'def, Units.val_mul, coe_GL_coe_matrix, tr]
    rw [trace_mul_cycle, Units.inv_mul, one_mul]
  have trγ'inv : trace ((γ'⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = tr γ := by
    have : (γ'⁻¹ : GL (Fin 2) ℝ) = g * toGL γ⁻¹ * g⁻¹ := by
      simp [hγ'def, mul_assoc]
    rw [this, Units.val_mul, Units.val_mul, trace_mul_cycle, Units.inv_mul, one_mul,
      coe_GL_coe_matrix, ← tr, tr_inv]
  have hrat : tr γ ^ 2 ∈ 𝐐 := by
    have := tr_mul_tr_inv_mem_rat hγ'comm
    rwa [trγ', trγ'inv, ← pow_two] at this
  -- integrality
  obtain ⟨n, hn, -, hpow⟩ := exists_pow_mem_of_relIndex_ne_zero hcomm.2 hγ'
  obtain ⟨m, hm⟩ := trace_int_of_mem_SL hpow.1
  have hpow' : γ' ^ n = g * toGL (γ ^ n) * g⁻¹ := by
    rw [hγ'def, conj_pow, map_pow]
  have htr : tr (γ ^ n) = m := by
    rw [← hm, hpow', Units.val_mul, Units.val_mul, trace_mul_cycle, Units.inv_mul, one_mul,
      coe_GL_coe_matrix]
  rw [tr_pow] at htr
  have hint : IsIntegral ℤ (tr γ ^ 2) := (isIntegral_of_lucas_eq hn htr).pow 2
  obtain ⟨q, hq⟩ := hrat
  have hq' : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (A := ℚ) (B := ℝ) (algebraMap ℚ ℝ).injective]
    simpa [← hq] using hint
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp hq'
  refine ⟨k, ?_⟩
  rw [← hq]
  simp [← hk]

end OrbicurveCores
