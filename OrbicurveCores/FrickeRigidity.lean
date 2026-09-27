/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Fricke

/-!
# Fricke rigidity: a pair in `SL(2, ℝ)` is determined by its trace triple

If `A, B ∈ SL(2, ℝ)` with `|tr A| > 2` (so `A` is hyperbolic) and `tr [A, B] ≠ 2` (the pair is
irreducible), then the triple `(tr A, tr B, tr AB)` determines the pair `(A, B)` up to
simultaneous conjugation by `GL(2, ℝ)` (`OrbicurveCores.exists_conj_of_tr_eq`).

Proof: conjugate `A` to `D = diag(λ, λ⁻¹)` with `λ = (x + √(x² - 4))/2`. Then
`B ~ [[a, b], [c, d]]` where `a + d = y` and `λa + λ⁻¹d = z` determine `a, d`, and
`bc = ad - 1 ≠ 0` because `tr [A, B] = 2 - bc(λ - λ⁻¹)²`. Conjugating by `diag(t, 1)`, which
fixes `D`, rescales `b` and leaves `bc` unchanged.

This is the classical fact behind [Sijs] Lemma 1.1.1 ("these traces determine `Γ` up to
conjugacy").
-/

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace OrbicurveCores

/-- The larger eigenvalue `(x + √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigBig (x : ℝ) : ℝ := (x + Real.sqrt (x ^ 2 - 4)) / 2

/-- The smaller eigenvalue `(x - √(x² - 4))/2` of an element of trace `x`. -/
noncomputable def eigSmall (x : ℝ) : ℝ := (x - Real.sqrt (x ^ 2 - 4)) / 2

section eig

variable {x : ℝ} (hx : 4 < x ^ 2)
include hx

omit hx in
lemma eig_sum : eigBig x + eigSmall x = x := by unfold eigBig eigSmall; ring

lemma eig_prod : eigBig x * eigSmall x = 1 := by
  unfold eigBig eigSmall
  have := Real.sq_sqrt (show (0 : ℝ) ≤ x ^ 2 - 4 by linarith)
  linear_combination (-1 / 4 : ℝ) * this

lemma eig_sub_pos : 0 < eigBig x - eigSmall x := by
  unfold eigBig eigSmall
  have := Real.sqrt_pos.mpr (show (0 : ℝ) < x ^ 2 - 4 by linarith)
  linarith

lemma eig_ne : eigBig x ≠ eigSmall x := sub_ne_zero.mp (eig_sub_pos hx).ne'

end eig

/-- Diagonalisation, in coordinates: for `A = [[p, q], [r, s]]` with `ps - qr = 1` and roots
`l ≠ m` of `t² - (p + s) t + 1`, an explicit invertible `P` with `P A = diag(l, m) P`. -/
lemma exists_diagonalize_aux (p q r s l m : ℝ) (hd : p * s - q * r = 1)
    (hsum : l + m = p + s) (hprod : l * m = 1) (hne : l - m ≠ 0) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * !![p, q; r, s] = !![l, 0; 0, m] * P := by
  have hl : l ^ 2 - (p + s) * l + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  have hm : m ^ 2 - (p + s) * m + 1 = 0 := by rw [← hsum]; linear_combination -hprod
  by_cases hr : r = 0
  · subst hr
    have hp : (p - l) * (p - m) = 0 := by linear_combination -p * hsum - hd + hprod
    rcases mul_eq_zero.mp hp with hpl | hpm
    · have hpl' : p = l := by linarith
      have hsm : s = m := by linarith
      subst hpl' hsm
      refine ⟨!![p - s, q; 0, s - p], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
    · have hpm' : p = m := by linarith
      have hsl : s = l := by linarith
      subst hpm' hsl
      refine ⟨!![0, s - p; p - s, q], ?_, ?_⟩
      · rw [det_fin_two_of]
        have := mul_self_ne_zero.mpr hne
        intro h; apply this; linarith
      · ext i j
        fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two] <;> ring
  · refine ⟨!![r, l - p; r, m - p], ?_, ?_⟩
    · rw [det_fin_two_of]
      have : r * (m - p) - (l - p) * r = -(r * (l - m)) := by ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero hr hne
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
      · ring
      · linear_combination -hl - hd
      · ring
      · linear_combination -hm - hd

/-- **Diagonalisation of a hyperbolic element.** If `det A = 1` and `(tr A)² > 4`, there is an
invertible `P` with `P A = diag(λ, μ) P`, where `λ, μ` are the two eigenvalues. -/
lemma exists_diagonalize {A : Matrix (Fin 2) (Fin 2) ℝ} (hdet : A.det = 1)
    (hx : 4 < A.trace ^ 2) :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P.det ≠ 0 ∧
      P * A = !![eigBig A.trace, 0; 0, eigSmall A.trace] * P := by
  have hA := eta_fin_two A
  rw [det_fin_two] at hdet
  have hsum : eigBig A.trace + eigSmall A.trace = A 0 0 + A 1 1 := by
    rw [eig_sum, trace_fin_two]
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize_aux (A 0 0) (A 0 1) (A 1 0) (A 1 1) _ _ hdet hsum
    (eig_prod hx) (eig_sub_pos hx).ne'
  exact ⟨P, hP, by rw [hA]; exact hPA⟩

/-- The normal form of the second matrix: `[[a, 1], [ad - 1, d]]` with
`a = (z - μy)/(λ - μ)`, `d = (λy - z)/(λ - μ)`. -/
noncomputable def normalB (x y z : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  let a := (z - eigSmall x * y) / (eigBig x - eigSmall x)
  let d := (eigBig x * y - z) / (eigBig x - eigSmall x)
  !![a, 1; a * d - 1, d]

/-- The Fricke polynomial in normal form: for `D = diag(l, m)` with `lm = 1` and
`C = [[a, b], [c, d]]` with `det C = 1`, `x² + y² + z² - xyz - 4 = -bc (l - m)²` where
`x = l + m`, `y = a + d`, `z = la + md`. -/
lemma fricke_normal {l m a b c d : ℝ} (hprod : l * m = 1) (hdet : a * d - b * c = 1) :
    (l + m) ^ 2 + (a + d) ^ 2 + (l * a + m * d) ^ 2 - (l + m) * (a + d) * (l * a + m * d) - 4 =
      -(b * c) * (l - m) ^ 2 := by
  linear_combination (4 - (a + d) ^ 2) * hprod - (l - m) ^ 2 * hdet

/-- **Normal form of an irreducible pair with hyperbolic first element.** -/
theorem exists_conj_normal {A B : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) :
    ∃ g : GL (Fin 2) ℝ,
      ((g * toGL A * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        !![eigBig (tr A), 0; 0, eigSmall (tr A)] ∧
      ((g * toGL B * g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
        normalB (tr A) (tr B) (tr (A * B)) := by
  set x := tr A with hxdef
  set l := eigBig x
  set m := eigSmall x
  have hprod : l * m = 1 := eig_prod hx
  have hlm : l - m ≠ 0 := (eig_sub_pos hx).ne'
  set D : Matrix (Fin 2) (Fin 2) ℝ := !![l, 0; 0, m] with hD
  obtain ⟨P, hP, hPA⟩ := exists_diagonalize (A := (A : Matrix (Fin 2) (Fin 2) ℝ)) A.det_coe hx
  have hPu : IsUnit P.det := isUnit_iff_ne_zero.mpr hP
  have hPPi : P * P⁻¹ = 1 := mul_nonsing_inv P hPu
  have hPiP : P⁻¹ * P = 1 := nonsing_inv_mul P hPu
  set C : Matrix (Fin 2) (Fin 2) ℝ := P * (B : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ with hC
  have hDA : P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ = D := by
    rw [hPA, mul_assoc, hPPi, mul_one]
  -- invariants of `C`
  have htrC : C.trace = tr B := by
    rw [hC, trace_mul_cycle, hPiP, one_mul]
  have htrDC : (D * C).trace = tr (A * B) := by
    rw [← hDA, hC, show P * (A : Matrix (Fin 2) (Fin 2) ℝ) * P⁻¹ * (P * B * P⁻¹) =
      P * ((A : Matrix (Fin 2) (Fin 2) ℝ) * B) * P⁻¹ by
        simp only [mul_assoc]; rw [← mul_assoc P⁻¹ P, hPiP, one_mul],
      trace_mul_cycle, hPiP, one_mul]
    simp [tr]
  have hdetC : C.det = 1 := by
    rw [hC, det_mul, det_mul, B.det_coe, mul_one, ← det_mul, hPPi, det_one]
  set a := C 0 0
  set b := C 0 1
  set c := C 1 0
  set d := C 1 1
  have hCeta : C = !![a, b; c, d] := eta_fin_two C
  have hdet' : a * d - b * c = 1 := by rw [hCeta, det_fin_two_of] at hdetC; exact hdetC
  have hy : a + d = tr B := by rw [← htrC, hCeta, trace_fin_two_of]
  have hz : l * a + m * d = tr (A * B) := by
    rw [← htrDC, hCeta, hD]; simp [trace_fin_two]
  have hxlm : l + m = x := eig_sum
  -- `bc ≠ 0` by irreducibility
  have hbc : b * c ≠ 0 := by
    intro h0
    apply hc
    have hf := fricke_normal (b := b) (c := c) hprod hdet'
    rw [h0, hxlm, hy, hz] at hf
    rw [tr_commutator]
    linarith
  have hb : b ≠ 0 := left_ne_zero_of_mul hbc
  -- rescale by `diag(b⁻¹, 1)`
  set Q : Matrix (Fin 2) (Fin 2) ℝ := !![b⁻¹, 0; 0, 1] with hQ
  have hQdet : Q.det ≠ 0 := by rw [hQ, det_fin_two_of]; simpa using hb
  set Qi : Matrix (Fin 2) (Fin 2) ℝ := !![b, 0; 0, 1] with hQi
  have hQQi : Q * Qi = 1 := by
    rw [hQ, hQi]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
  have hQiQ : Qi * Q = 1 := by
    rw [hQ, hQi]; ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
  have hQinv : Q⁻¹ = Qi := inv_eq_right_inv hQQi
  let g : GL (Fin 2) ℝ := GeneralLinearGroup.mkOfDetNeZero (Q * P)
    (by rw [det_mul]; exact mul_ne_zero hQdet hP)
  have hgc : (g : Matrix (Fin 2) (Fin 2) ℝ) = Q * P := rfl
  have hginv : ((g⁻¹ : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = P⁻¹ * Qi := by
    rw [Matrix.coe_units_inv, hgc, Matrix.mul_inv_rev, hQinv]
  -- solve for `a`, `d`
  have ha : a = (tr (A * B) - m * tr B) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  have hd' : d = (l * tr B - tr (A * B)) / (l - m) := by
    rw [eq_div_iff hlm, ← hy, ← hz]; ring
  refine ⟨g, ?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (A : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * (P * A * P⁻¹) * Qi by simp only [mul_assoc], hDA, hQ, hQi, hD]
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply]
    field_simp
  · rw [Units.val_mul, Units.val_mul, hgc, hginv, coe_GL_coe_matrix]
    rw [show Q * P * (B : Matrix (Fin 2) (Fin 2) ℝ) * (P⁻¹ * Qi) =
      Q * C * Qi by simp only [hC, mul_assoc], hCeta, hQ, hQi, normalB]
    rw [← ha, ← hd']
    ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, hb]
    · field_simp
    · linear_combination -hdet'

/-- **Fricke rigidity.** Two pairs in `SL(2, ℝ)` with the same trace triple, whose first element
is hyperbolic and which are irreducible (`tr [A, B] ≠ 2`), are simultaneously conjugate by an
element of `GL(2, ℝ)`. -/
theorem exists_conj_of_tr_eq {A B A' B' : SL(2, ℝ)} (hx : 4 < tr A ^ 2)
    (hc : tr (A * B * A⁻¹ * B⁻¹) ≠ 2) (h1 : tr A = tr A') (h2 : tr B = tr B')
    (h3 : tr (A * B) = tr (A' * B')) :
    ∃ g : GL (Fin 2) ℝ, g * toGL A * g⁻¹ = toGL A' ∧ g * toGL B * g⁻¹ = toGL B' := by
  have hx' : 4 < tr A' ^ 2 := h1 ▸ hx
  have hc' : tr (A' * B' * A'⁻¹ * B'⁻¹) ≠ 2 := by
    rwa [tr_commutator, ← h1, ← h2, ← h3, ← tr_commutator]
  obtain ⟨g, hgA, hgB⟩ := exists_conj_normal hx hc
  obtain ⟨g', hgA', hgB'⟩ := exists_conj_normal hx' hc'
  refine ⟨g'⁻¹ * g, ?_, ?_⟩
  · have e : g * toGL A * g⁻¹ = g' * toGL A' * g'⁻¹ := by
      ext1; rw [hgA, hgA', h1]
    calc g'⁻¹ * g * toGL A * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL A * g⁻¹) * g' := by group
      _ = toGL A' := by rw [e]; group
  · have e : g * toGL B * g⁻¹ = g' * toGL B' * g'⁻¹ := by
      ext1; rw [hgB, hgB', h1, h2, h3]
    calc g'⁻¹ * g * toGL B * (g'⁻¹ * g)⁻¹ = g'⁻¹ * (g * toGL B * g⁻¹) * g' := by group
      _ = toGL B' := by rw [e]; group

end OrbicurveCores
