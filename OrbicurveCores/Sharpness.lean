/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.FourGroups

/-!
# Certified coset enumeration: finite index in `SL(2, ℤ)`

The framework used to show that Takeuchi's four explicit groups are arithmetic
(`OrbicurveCores.SharpnessData`). Let `Γ = ⟨A, B⟩ ⊆ SL(2, ℝ)` with `A = M/√n`, `B = N/√k` for
integral `M, N` of determinants `n, k`. A word `w` in `A^{±1}, B^{±1}` evaluates to
`(1/√n)^a (1/√k)^b · W` with `W` integral (`coe_evalSL`). Hence identities between words and
integral matrices can be checked in integer arithmetic.

* A **cover certificate** is a finite list `R` of integral matrices (containing `1`, all of
  determinant `1`). For each `r ∈ R` and each `g ∈ {S, T, S⁻¹, T⁻¹}` it gives `r' ∈ R` and a
  word `w` with `r g = w r'`. Then `SL(2, ℤ) = ⋃_{r ∈ R} (Γ ∩ SL(2, ℤ)) r`, so `Γ ∩ SL(2, ℤ)`
  has finite index in `SL(2, ℤ)` (`relIndex_ne_zero_of_coverOK`).
* A **transversal certificate** is a finite list of words `u` (containing the empty word). For
  each `u` and each letter `x` it gives `u'` with `u x u'⁻¹` integral. Then `Γ ∩ SL(2, ℤ)` has
  finite index in `Γ` (`relIndex_ne_zero_of_transOK`).

All checks are Boolean functions evaluated by `decide`.
-/

open Matrix Matrix.SpecialLinearGroup Subgroup
open scoped MatrixGroups

namespace OrbicurveCores.Sharp

/-- Integral `2 × 2` matrices as quadruples, for fast kernel evaluation. -/
structure IM where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
deriving DecidableEq, Repr

namespace IM

/-- Matrix product. -/
def mul (x y : IM) : IM :=
  ⟨x.a * y.a + x.b * y.c, x.a * y.b + x.b * y.d, x.c * y.a + x.d * y.c, x.c * y.b + x.d * y.d⟩

/-- The identity. -/
def one : IM := ⟨1, 0, 0, 1⟩

/-- Scalar multiple. -/
def smul (k : ℤ) (x : IM) : IM := ⟨k * x.a, k * x.b, k * x.c, k * x.d⟩

/-- The adjugate. -/
def adj (x : IM) : IM := ⟨x.d, -x.b, -x.c, x.a⟩

/-- The determinant. -/
def det (x : IM) : ℤ := x.a * x.d - x.b * x.c

/-- The negative. -/
def neg (x : IM) : IM := ⟨-x.a, -x.b, -x.c, -x.d⟩

/-- The real matrix. -/
def toR (x : IM) : Matrix (Fin 2) (Fin 2) ℝ := !![(x.a : ℝ), x.b; x.c, x.d]

lemma toR_mul (x y : IM) : (mul x y).toR = x.toR * y.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul, toR, Matrix.mul_apply, Fin.sum_univ_two]

lemma toR_one : one.toR = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [one, toR]

lemma toR_smul (k : ℤ) (x : IM) : (smul k x).toR = (k : ℝ) • x.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [smul, toR]

lemma toR_adj (x : IM) : (adj x).toR = adjugate x.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adj, toR, adjugate_fin_two]

lemma det_toR (x : IM) : x.toR.det = (x.det : ℝ) := by
  simp [toR, det, det_fin_two]

lemma toR_mul_adj {x : IM} (h : x.det = 1) : x.toR * (adj x).toR = 1 := by
  rw [toR_adj, mul_adjugate, det_toR, h]; simp

lemma toR_adj_mul {x : IM} (h : x.det = 1) : (adj x).toR * x.toR = 1 := by
  rw [toR_adj, adjugate_mul, det_toR, h]; simp

/-- The element of `SL(2, ℤ)` (or `1` if the determinant is not `1`). -/
def toSLZ (x : IM) : SL(2, ℤ) :=
  if h : x.det = 1 then ⟨!![x.a, x.b; x.c, x.d], by simpa [det_fin_two, det] using h⟩ else 1

lemma coe_map_toSLZ {x : IM} (h : x.det = 1) :
    ((SpecialLinearGroup.map (algebraMap ℤ ℝ) x.toSLZ : SL(2, ℝ)) :
      Matrix (Fin 2) (Fin 2) ℝ) = x.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toSLZ, h, toR]

end IM

/-- `S`, `T`, `S⁻¹`, `T⁻¹` as integral matrices. -/
def genS : IM := ⟨0, -1, 1, 0⟩
/-- `T`. -/
def genT : IM := ⟨1, 1, 0, 1⟩
/-- `S⁻¹`. -/
def genSi : IM := ⟨0, 1, -1, 0⟩
/-- `T⁻¹`. -/
def genTi : IM := ⟨1, -1, 0, 1⟩

/-- The real homomorphism `SL(2, ℤ) → SL(2, ℝ)`. -/
abbrev φ : SL(2, ℤ) →* SL(2, ℝ) := SpecialLinearGroup.map (algebraMap ℤ ℝ)

lemma coe_φ_S : ((φ ModularGroup.S : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = genS.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [genS, IM.toR, ModularGroup.S]

lemma coe_φ_T : ((φ ModularGroup.T : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = genT.toR := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [genT, IM.toR, ModularGroup.T]

lemma coe_φ_S_inv :
    ((φ ModularGroup.S⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = genSi.toR := by
  rw [map_inv, Matrix.SpecialLinearGroup.coe_inv, coe_φ_S, ← IM.toR_adj]
  rfl

lemma coe_φ_T_inv :
    ((φ ModularGroup.T⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = genTi.toR := by
  rw [map_inv, Matrix.SpecialLinearGroup.coe_inv, coe_φ_T, ← IM.toR_adj]
  rfl

/-! ### Words -/

section words

variable (M N : IM)

/-- The integral matrices of the letters `A, A⁻¹, B, B⁻¹` (up to the scalars `1/√n`, `1/√k`). -/
def letterInt : Fin 4 → IM
  | 0 => M
  | 1 => M.adj
  | 2 => N
  | 3 => N.adj

/-- The integral matrix of a word. -/
def evalInt : List (Fin 4) → IM
  | [] => IM.one
  | x :: w => (letterInt M N x).mul (evalInt w)

/-- Number of letters `A^{±1}` in a word. -/
def countA (w : List (Fin 4)) : ℕ := w.countP (fun x ↦ x.val < 2)

/-- Number of letters `B^{±1}` in a word. -/
def countB (w : List (Fin 4)) : ℕ := w.countP (fun x ↦ ¬ x.val < 2)

/-- The inverse word. -/
def invLetter : Fin 4 → Fin 4
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- The inverse of a word. -/
def invWord (w : List (Fin 4)) : List (Fin 4) := (w.map invLetter).reverse

end words

section evalSL

variable (A B : SL(2, ℝ))

/-- The letters `A, A⁻¹, B, B⁻¹`. -/
def letterSL : Fin 4 → SL(2, ℝ)
  | 0 => A
  | 1 => A⁻¹
  | 2 => B
  | 3 => B⁻¹

/-- The value of a word. -/
def evalSL : List (Fin 4) → SL(2, ℝ)
  | [] => 1
  | x :: w => letterSL A B x * evalSL w

lemma evalSL_mem (w : List (Fin 4)) : evalSL A B w ∈ Subgroup.closure {A, B} := by
  induction w with
  | nil => exact one_mem _
  | cons x w ih =>
    refine mul_mem ?_ ih
    have hA : A ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    have hB : B ∈ Subgroup.closure {A, B} := subset_closure (by simp)
    fin_cases x
    · exact hA
    · exact inv_mem hA
    · exact hB
    · exact inv_mem hB

lemma evalSL_append (u v : List (Fin 4)) :
    evalSL A B (u ++ v) = evalSL A B u * evalSL A B v := by
  induction u with
  | nil => simp [evalSL]
  | cons x u ih => simp [evalSL, ih, mul_assoc]

lemma letterSL_invLetter (x : Fin 4) : letterSL A B (invLetter x) = (letterSL A B x)⁻¹ := by
  fin_cases x <;> simp [letterSL, invLetter]

lemma evalSL_invWord (w : List (Fin 4)) : evalSL A B (invWord w) = (evalSL A B w)⁻¹ := by
  induction w with
  | nil => simp [evalSL, invWord]
  | cons x w ih =>
    simp only [invWord, List.map_cons, List.reverse_cons] at ih ⊢
    rw [evalSL_append, ih]
    simp [evalSL, letterSL_invLetter]

end evalSL

lemma scal_cons (cA cB : ℝ) (x : Fin 4) (w : List (Fin 4)) :
    cA ^ countA (x :: w) * cB ^ countB (x :: w) =
      (if x.val < 2 then cA else cB) * (cA ^ countA w * cB ^ countB w) := by
  fin_cases x <;> simp [countA, countB, pow_succ] <;> ring

/-- Words in `A = cA • M`, `B = cB • N` evaluate to `cA^a cB^b • W` with `W` integral. -/
lemma coe_evalSL {A B : SL(2, ℝ)} {M N : IM} {cA cB : ℝ}
    (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = cA • M.toR)
    (hB : (B : Matrix (Fin 2) (Fin 2) ℝ) = cB • N.toR) (w : List (Fin 4)) :
    (evalSL A B w : Matrix (Fin 2) (Fin 2) ℝ) =
      (cA ^ countA w * cB ^ countB w) • (evalInt M N w).toR := by
  have hAi : ((A⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = cA • M.adj.toR := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hA, IM.toR_adj]
    simp [adjugate_fin_two, IM.toR]
  have hBi : ((B⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = cB • N.adj.toR := by
    rw [Matrix.SpecialLinearGroup.coe_inv, hB, IM.toR_adj]
    simp [adjugate_fin_two, IM.toR]
  have hletter : ∀ x : Fin 4, ((letterSL A B x : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
      (if x.val < 2 then cA else cB) • (letterInt M N x).toR := by
    intro x; fin_cases x
    · exact hA
    · exact hAi
    · exact hB
    · exact hBi
  induction w with
  | nil => simp [evalSL, evalInt, countA, countB, IM.toR_one]
  | cons x w ih =>
    rw [evalSL, Matrix.SpecialLinearGroup.coe_mul, ih, hletter, evalInt, IM.toR_mul,
      scal_cons, smul_mul_smul_comm]

/-- The scalar `(1/√n)^a (1/√k)^b` is `1/s` when `s² = nᵃ kᵇ`. -/
lemma scalar_eq {n k a b s : ℕ} (hn : 0 < n) (hk : 0 < k) (hs : s ^ 2 = n ^ a * k ^ b) :
    ((Real.sqrt n)⁻¹ ^ a * (Real.sqrt k)⁻¹ ^ b) = (s : ℝ)⁻¹ := by
  have hs' : ((s : ℝ)) = Real.sqrt n ^ a * Real.sqrt k ^ b := by
    have h1 : (0 : ℝ) ≤ Real.sqrt n ^ a * Real.sqrt k ^ b := by positivity
    rw [← Real.sqrt_sq (Nat.cast_nonneg s), ← Real.sqrt_sq h1]
    congr 1
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm a 2, mul_comm b 2, pow_mul, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
    exact_mod_cast hs
  rw [hs', mul_inv, inv_pow, inv_pow]

/-! ### Cover certificates: finite index in `SL(2, ℤ)` -/

/-- An entry of a cover certificate: target index, word, scale. -/
abbrev Entry := ℕ × List (Fin 4) × ℕ

section cert

variable (M N : IM) (n k : ℕ)

/-- Check `r g = w r'` (up to the scale `s`, with `s² = nᵃkᵇ`). -/
def entryOK (R : List IM) (r g : IM) (e : Entry) : Bool :=
  decide (e.1 < R.length) &&
    ((evalInt M N e.2.1).mul (R.getD e.1 IM.one) == IM.smul e.2.2 (r.mul g)) &&
    (e.2.2 ^ 2 == n ^ countA e.2.1 * k ^ countB e.2.1)

/-- A cover certificate: rows `(r, e_S, e_T, e_{S⁻¹}, e_{T⁻¹})`. -/
abbrev CoverCert := List (IM × Entry × Entry × Entry × Entry)

/-- The Boolean check of a cover certificate. -/
def coverOK (C : CoverCert) : Bool :=
  (C.map (·.1)).contains IM.one &&
    C.all (fun row ↦ row.1.det == 1 &&
      entryOK M N n k (C.map (·.1)) row.1 genS row.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genT row.2.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genSi row.2.2.2.1 &&
      entryOK M N n k (C.map (·.1)) row.1 genTi row.2.2.2.2)

variable {M N n k}

lemma entryOK_sound {R : List IM} {r g : IM} {e : Entry} (h : entryOK M N n k R r g e = true) :
    ∃ r' ∈ R, ∃ w : List (Fin 4), ∃ s : ℕ, (evalInt M N w).mul r' = IM.smul s (r.mul g) ∧
      s ^ 2 = n ^ countA w * k ^ countB w := by
  simp only [entryOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hlt, heq⟩, hs⟩ := h
  refine ⟨R.getD e.1 IM.one, ?_, e.2.1, e.2.2, heq, hs⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

lemma coverOK_sound {C : CoverCert} (h : coverOK M N n k C = true) :
    IM.one ∈ C.map (·.1) ∧ ∀ r ∈ C.map (·.1), r.det = 1 ∧
      ∀ g ∈ ({genS, genT, genSi, genTi} : Set IM), ∃ r' ∈ C.map (·.1),
        ∃ w : List (Fin 4), ∃ s : ℕ, (evalInt M N w).mul r' = IM.smul s (r.mul g) ∧
          s ^ 2 = n ^ countA w * k ^ countB w := by
  simp only [coverOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true,
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  intro r hr
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hr
  obtain ⟨⟨⟨⟨hdet, hS⟩, hT⟩, hSi⟩, hTi⟩ := h2 row hrow
  refine ⟨hdet, ?_⟩
  rintro g (rfl | rfl | rfl | rfl)
  · exact entryOK_sound hS
  · exact entryOK_sound hT
  · exact entryOK_sound hSi
  · exact entryOK_sound hTi

end cert

section cover

variable {A B : SL(2, ℝ)} {M N : IM} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
  (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt n)⁻¹ • M.toR)
  (hB : (B : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt k)⁻¹ • N.toR)
include hn hk hA hB

/-- A word with integral matrix `W` and `s² = nᵃkᵇ` evaluates to `W / s`. -/
lemma coe_evalSL_eq {w : List (Fin 4)} {s : ℕ} (hs : s ^ 2 = n ^ countA w * k ^ countB w) :
    (evalSL A B w : Matrix (Fin 2) (Fin 2) ℝ) = (s : ℝ)⁻¹ • (evalInt M N w).toR := by
  rw [coe_evalSL hA hB, scalar_eq hn hk hs]

/-- From a certificate entry: `r g = (word) r'` as real matrices. -/
lemma entry_real {r g r' : IM} {w : List (Fin 4)} {s : ℕ}
    (he : (evalInt M N w).mul r' = IM.smul s (r.mul g))
    (hs : s ^ 2 = n ^ countA w * k ^ countB w) :
    r.toR * g.toR = (evalSL A B w : Matrix (Fin 2) (Fin 2) ℝ) * r'.toR := by
  have hs0 : (s : ℝ) ≠ 0 := by
    have : 0 < n ^ countA w * k ^ countB w := by positivity
    rw [← hs] at this
    exact_mod_cast (pos_of_ne_zero (by rintro rfl; simp at this)).ne'
  rw [coe_evalSL_eq hn hk hA hB hs, smul_mul_assoc, ← IM.toR_mul, ← IM.toR_mul, he,
    IM.toR_smul, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ hs0, one_smul]

/-- **Covering.** A valid cover certificate gives `SL(2, ℤ) = ⋃_{r ∈ R} (⟨A, B⟩ ∩ SL(2,ℤ)) r`. -/
theorem cover_of_coverOK {C : CoverCert} (hC : coverOK M N n k C = true) (γ : SL(2, ℤ)) :
    ∃ r ∈ C.map (·.1), ∃ h ∈ Subgroup.closure {A, B},
      ((φ γ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = (h : Matrix (Fin 2) (Fin 2) ℝ) * r.toR := by
  obtain ⟨hone, hrows⟩ := coverOK_sound hC
  have hγ : γ ∈ Subgroup.closure {ModularGroup.S, ModularGroup.T} := by
    rw [SpecialLinearGroup.SL2Z_generators]; trivial
  induction hγ using Subgroup.closure_induction_right with
  | one => exact ⟨IM.one, hone, 1, one_mem _, by simp [IM.toR_one]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨r, hr, h, hh, hx⟩ := ih
    obtain ⟨-, hgens⟩ := hrows r hr
    have key : ∀ g ∈ ({genS, genT, genSi, genTi} : Set IM),
        ((φ y : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = g.toR →
        ∃ r ∈ C.map (·.1), ∃ h ∈ Subgroup.closure {A, B},
          ((φ (x * y) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
            (h : Matrix (Fin 2) (Fin 2) ℝ) * r.toR := by
      intro g hg hy'
      obtain ⟨r', hr', w, s, he, hs⟩ := hgens g hg
      refine ⟨r', hr', h * evalSL A B w, mul_mem hh (evalSL_mem A B w), ?_⟩
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy', mul_assoc,
        entry_real hn hk hA hB he hs, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    rcases hy with rfl | rfl
    · exact key genS (by simp) coe_φ_S
    · exact key genT (by simp) coe_φ_T
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨r, hr, h, hh, hx⟩ := ih
    obtain ⟨-, hgens⟩ := hrows r hr
    have key : ∀ g ∈ ({genS, genT, genSi, genTi} : Set IM),
        ((φ y⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) = g.toR →
        ∃ r ∈ C.map (·.1), ∃ h ∈ Subgroup.closure {A, B},
          ((φ (x * y⁻¹) : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ) =
            (h : Matrix (Fin 2) (Fin 2) ℝ) * r.toR := by
      intro g hg hy'
      obtain ⟨r', hr', w, s, he, hs⟩ := hgens g hg
      refine ⟨r', hr', h * evalSL A B w, mul_mem hh (evalSL_mem A B w), ?_⟩
      rw [map_mul, Matrix.SpecialLinearGroup.coe_mul, hx, hy', mul_assoc,
        entry_real hn hk hA hB he hs, Matrix.SpecialLinearGroup.coe_mul, mul_assoc]
    rcases hy with rfl | rfl
    · exact key genSi (by simp) coe_φ_S_inv
    · exact key genTi (by simp) coe_φ_T_inv

/-- **Finite index in `SL(2, ℤ)`.** -/
theorem relIndex_ne_zero_of_coverOK {C : CoverCert} (hC : coverOK M N n k C = true) :
    ((Subgroup.closure {A, B}).map toGL).relIndex 𝒮ℒ ≠ 0 := by
  set Γ := Subgroup.closure {A, B}
  set K : Subgroup SL(2, ℤ) := Γ.comap φ
  have hK : ((Subgroup.closure {A, B}).map toGL).relIndex 𝒮ℒ = K.index := by
    rw [MonoidHom.range_eq_map, ← Subgroup.relIndex_comap, Subgroup.relIndex_top_right]
    congr 1
    ext γ
    simp only [Subgroup.mem_comap, K]
    exact Subgroup.mem_map_iff_mem toGL_injective
  rw [hK]
  obtain ⟨-, hrows⟩ := coverOK_sound hC
  -- every element is `h r` with `r` from the finite list
  have hc := fun γ : SL(2, ℤ) ↦ cover_of_coverOK hn hk hA hB hC γ⁻¹
  choose f hf h hh hfh using hc
  let F : SL(2, ℤ) ⧸ K → {r // r ∈ C.map (·.1)} := fun q ↦ ⟨f q.out, hf q.out⟩
  have hinj : Function.Injective F := by
    intro q q' hqq
    simp only [F, Subtype.mk.injEq] at hqq
    rw [← q.out_eq, ← q'.out_eq, QuotientGroup.eq]
    set γ := q.out
    set γ' := q'.out
    have hdet := (hrows (f γ) (hf γ)).1
    let rs : SL(2, ℝ) := ⟨(f γ).toR, by rw [IM.det_toR, hdet]; simp⟩
    have e1 : φ γ⁻¹ = h γ * rs := Subtype.ext (by rw [hfh]; rfl)
    have e2 : φ γ'⁻¹ = h γ' * rs := Subtype.ext (by rw [hfh, ← hqq]; rfl)
    change φ (γ⁻¹ * γ') ∈ Γ
    have : φ (γ⁻¹ * γ') = h γ * (h γ')⁻¹ := by
      have e2' : φ γ' = rs⁻¹ * (h γ')⁻¹ := by
        rw [← _root_.mul_inv_rev, ← e2, map_inv, inv_inv]
      rw [map_mul, e1, e2']
      group
    rw [this]
    exact mul_mem (hh γ) (inv_mem (hh γ'))
  haveI : Finite {r // r ∈ C.map (·.1)} := List.finite_toSet _ |>.to_subtype
  haveI : Finite (SL(2, ℤ) ⧸ K) := Finite.of_injective F hinj
  exact Subgroup.index_ne_zero_of_finite

end cover

/-! ### Transversal certificates: finite index in `Γ` -/

/-- An entry of a transversal certificate: target index, integral matrix, scale. -/
abbrev Entry2 := ℕ × IM × ℕ

section trans

variable (M N : IM) (n k : ℕ)

/-- The word `u x u'⁻¹` of a transversal entry. -/
def transWord (U : List (List (Fin 4))) (u : List (Fin 4)) (x : Fin 4) (j : ℕ) : List (Fin 4) :=
  u ++ [x] ++ invWord (U.getD j [])

/-- Check that `u x u'⁻¹` is the integral matrix `Z` of determinant `1` (up to the scale `s`). -/
def entry2OK (U : List (List (Fin 4))) (u : List (Fin 4)) (x : Fin 4) (e : Entry2) : Bool :=
  decide (e.1 < U.length) &&
    (evalInt M N (transWord U u x e.1) == IM.smul e.2.2 e.2.1) &&
    (e.2.1.det == 1) &&
    (e.2.2 ^ 2 == n ^ countA (transWord U u x e.1) * k ^ countB (transWord U u x e.1))

/-- A transversal certificate: rows `(u, e_A, e_{A⁻¹}, e_B, e_{B⁻¹})`. -/
abbrev TransCert := List (List (Fin 4) × Entry2 × Entry2 × Entry2 × Entry2)

/-- The Boolean check of a transversal certificate. -/
def transOK (C : TransCert) : Bool :=
  (C.map (·.1)).contains [] &&
    C.all (fun row ↦
      entry2OK M N n k (C.map (·.1)) row.1 0 row.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 1 row.2.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 2 row.2.2.2.1 &&
      entry2OK M N n k (C.map (·.1)) row.1 3 row.2.2.2.2)

variable {M N n k}

lemma entry2OK_sound {U : List (List (Fin 4))} {u : List (Fin 4)} {x : Fin 4} {e : Entry2}
    (h : entry2OK M N n k U u x e = true) :
    ∃ u' ∈ U, ∃ Z : IM, ∃ s : ℕ, evalInt M N (u ++ [x] ++ invWord u') = IM.smul s Z ∧
      Z.det = 1 ∧
        s ^ 2 = n ^ countA (u ++ [x] ++ invWord u') * k ^ countB (u ++ [x] ++ invWord u') := by
  simp only [entry2OK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨hlt, heq⟩, hdet⟩, hs⟩ := h
  refine ⟨U.getD e.1 [], ?_, e.2.1, e.2.2, heq, hdet, hs⟩
  rw [List.getD_eq_getElem _ _ hlt]
  exact List.getElem_mem hlt

lemma transOK_sound {C : TransCert} (h : transOK M N n k C = true) :
    [] ∈ C.map (·.1) ∧ ∀ u ∈ C.map (·.1), ∀ x : Fin 4, ∃ u' ∈ C.map (·.1), ∃ Z : IM, ∃ s : ℕ,
      evalInt M N (u ++ [x] ++ invWord u') = IM.smul s Z ∧ Z.det = 1 ∧
        s ^ 2 = n ^ countA (u ++ [x] ++ invWord u') * k ^ countB (u ++ [x] ++ invWord u') := by
  simp only [transOK, Bool.and_eq_true, List.contains_iff_mem, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  intro u hu x
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hu
  obtain ⟨⟨⟨h0, h1⟩, h2'⟩, h3⟩ := h2 row hrow
  fin_cases x
  · exact entry2OK_sound h0
  · exact entry2OK_sound h1
  · exact entry2OK_sound h2'
  · exact entry2OK_sound h3

end trans

section transversal

variable {A B : SL(2, ℝ)} {M N : IM} {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
  (hA : (A : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt n)⁻¹ • M.toR)
  (hB : (B : Matrix (Fin 2) (Fin 2) ℝ) = (Real.sqrt k)⁻¹ • N.toR)
include hn hk hA hB

/-- A word evaluating to an integral matrix of determinant one lies in the image of
`SL(2, ℤ)`. -/
lemma evalSL_mem_range {w : List (Fin 4)} {Z : IM} {s : ℕ} (he : evalInt M N w = IM.smul s Z)
    (hdet : Z.det = 1) (hs : s ^ 2 = n ^ countA w * k ^ countB w) :
    evalSL A B w ∈ φ.range := by
  have hs0 : (s : ℝ) ≠ 0 := by
    have : 0 < n ^ countA w * k ^ countB w := by positivity
    rw [← hs] at this
    exact_mod_cast (pos_of_ne_zero (by rintro rfl; simp at this)).ne'
  refine ⟨Z.toSLZ, Subtype.ext ?_⟩
  rw [IM.coe_map_toSLZ hdet, coe_evalSL_eq hn hk hA hB hs, he, IM.toR_smul, smul_smul]
  push_cast
  rw [inv_mul_cancel₀ hs0, one_smul]

/-- **Transversal.** A valid transversal certificate gives
`Γ = ⋃_{u ∈ U} (Γ ∩ SL(2,ℤ)) u`. -/
theorem trans_of_transOK {C : TransCert} (hC : transOK M N n k C = true) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) :
    ∃ u ∈ C.map (·.1), γ * (evalSL A B u)⁻¹ ∈ φ.range := by
  obtain ⟨hnil, hrows⟩ := transOK_sound hC
  have step : ∀ (x : SL(2, ℝ)) (u : List (Fin 4)), u ∈ C.map (·.1) →
      x * (evalSL A B u)⁻¹ ∈ φ.range → ∀ l : Fin 4,
      ∃ u' ∈ C.map (·.1), x * letterSL A B l * (evalSL A B u')⁻¹ ∈ φ.range := by
    intro x u hu hx l
    obtain ⟨u', hu', Z, s, he, hdet, hs⟩ := hrows u hu l
    refine ⟨u', hu', ?_⟩
    have hv := evalSL_mem_range hn hk hA hB he hdet hs
    rw [evalSL_append, evalSL_append, evalSL_invWord] at hv
    have : x * letterSL A B l * (evalSL A B u')⁻¹ =
        (x * (evalSL A B u)⁻¹) * (evalSL A B u * evalSL A B [l] * (evalSL A B u')⁻¹) := by
      simp [evalSL]; group
    rw [this]
    exact mul_mem hx hv
  induction hγ using Subgroup.closure_induction_right with
  | one => exact ⟨[], hnil, by simp [evalSL]⟩
  | mul_right x _ y hy ih =>
    obtain ⟨u, hu, hx⟩ := ih
    rcases hy with rfl | rfl
    · exact step x u hu hx 0
    · exact step x u hu hx 2
  | mul_inv_cancel x _ y hy ih =>
    obtain ⟨u, hu, hx⟩ := ih
    rcases hy with rfl | rfl
    · exact step x u hu hx 1
    · exact step x u hu hx 3

/-- **Finite index in `Γ`.** -/
theorem relIndex_ne_zero_of_transOK {C : TransCert} (hC : transOK M N n k C = true) :
    Subgroup.relIndex 𝒮ℒ ((Subgroup.closure {A, B}).map toGL) ≠ 0 := by
  set Γ := Subgroup.closure {A, B}
  have hrange : 𝒮ℒ = φ.range.map toGL := by
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  rw [hrange, Subgroup.relIndex_map_map_of_injective _ _ toGL_injective]
  have hc := fun q : Γ ↦ trans_of_transOK hn hk hA hB hC (inv_mem q.2)
  choose f hf hfr using hc
  let F : Γ ⧸ φ.range.subgroupOf Γ → {u // u ∈ C.map (·.1)} :=
    fun q ↦ ⟨f q.out, hf q.out⟩
  have hinj : Function.Injective F := by
    intro q q' hqq
    simp only [F, Subtype.mk.injEq] at hqq
    rw [← q.out_eq, ← q'.out_eq, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h1 := hfr q.out
    have h2 := hfr q'.out
    rw [hqq] at h1
    have := mul_mem h1 (inv_mem h2)
    simpa [mul_assoc] using this
  haveI : Finite {u // u ∈ C.map (·.1)} := List.finite_toSet _ |>.to_subtype
  haveI : Finite (Γ ⧸ φ.range.subgroupOf Γ) := Finite.of_injective F hinj
  exact Subgroup.index_ne_zero_of_finite

/-- **Arithmeticity from certificates.** -/
theorem isArithmeticSL_of_certs {C : CoverCert} {D : TransCert}
    (hC : coverOK M N n k C = true) (hD : transOK M N n k D = true) :
    IsArithmeticSL (Subgroup.closure {A, B}) :=
  ⟨1, ⟨by
    rw [map_one, one_smul]
    exact ⟨relIndex_ne_zero_of_coverOK hn hk hA hB hC,
      relIndex_ne_zero_of_transOK hn hk hA hB hD⟩⟩⟩

end transversal

end OrbicurveCores.Sharp
