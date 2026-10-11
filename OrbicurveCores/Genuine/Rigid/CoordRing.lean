/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.Genuine.Hemi
import Mathlib.RingTheory.Localization.NumDen
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# U2c1: the coordinate ring of `E ∖ 0` is the Weierstrass coordinate ring

pi1's `AffOrbicurve.punctured E` has coordinate ring the integral closure of `ℂ[x]` in
`ℂ(E) = ℂ(x)[y]`. Since `E` is smooth, this is `ℂ[x, y] / (W)`: an element `f = α + β y`
(`α, β ∈ ℂ(x)`) integral over `ℂ[x]` has trace `2α - β s` and norm `α² - α β s - β² c` in `ℂ[x]`
(`s = a₁ x + a₃`, `c = x³ + a₂ x² + a₄ x + a₆`), so `β² Ψ ∈ ℂ[x]` for the squarefree
`Ψ = s² + 4 c` (a double root of `Ψ` would be a singular point of `E`), hence `β ∈ ℂ[x]` and
`α ∈ ℂ[x]`.

* `squarefree_psi`: `Ψ = s² + 4 c` is squarefree;
* `exists_eq_of_isIntegral`: an element of `ℂ(E)` integral over `ℂ[x]` lies in `ℂ[x, y] / (W)`;
* `coordEquiv`: the coordinate ring of `E ∖ 0` is `ℂ[x, y] / (W)`.
-/

open Polynomial WeierstrassCurve.Affine

namespace OrbicurveCores.Rigid

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

/-- `s = a₁ x + a₃`. -/
noncomputable abbrev sP : ℂ[X] := C E.a₁ * X + C E.a₃

/-- `c = x³ + a₂ x² + a₄ x + a₆`. -/
noncomputable abbrev cP : ℂ[X] := X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆

/-- `Ψ = s² + 4 c`, the discriminant of `y² + s y - c`. -/
noncomputable abbrev psiP : ℂ[X] := sP E ^ 2 + 4 * cP E

omit [E.IsElliptic] in
lemma psiP_ne_zero : psiP E ≠ 0 := by
  intro h
  have := congrArg (fun p ↦ p.coeff 3) h
  simp only [psiP, sP, cP, coeff_add, coeff_ofNat_mul, coeff_X_pow, coeff_C_mul, coeff_X,
    coeff_C, pow_two, coeff_zero] at this
  rw [coeff_mul] at this
  simp [Finset.Nat.antidiagonal_succ, coeff_X, coeff_C] at this

/-- **`Ψ` is squarefree**: a double root `ρ` of `Ψ` would give the singular point
`(ρ, -s(ρ)/2)` of `E`. -/
lemma squarefree_psi : Squarefree (psiP E) := by
  intro t ht
  by_contra hu
  have ht0 : t ≠ 0 := by
    rintro rfl; rw [zero_mul, zero_dvd_iff] at ht; exact psiP_ne_zero E ht
  have hdeg : t.degree ≠ 0 := fun h ↦ hu (isUnit_iff_degree_eq_zero.mpr h)
  obtain ⟨ρ, hρ⟩ := Complex.exists_root (degree_pos_of_ne_zero_of_nonunit ht0 hu)
  have hdvd : (X - C ρ) ^ 2 ∣ psiP E := by
    have h1 : X - C ρ ∣ t := dvd_iff_isRoot.mpr hρ
    exact (pow_two (X - C ρ) ▸ mul_dvd_mul h1 h1).trans ht
  obtain ⟨Q, hQ⟩ := hdvd
  have hev : (psiP E).eval ρ = 0 := by rw [hQ]; simp
  have hdev : (derivative (psiP E)).eval ρ = 0 := by
    rw [hQ, derivative_mul]; simp [derivative_pow]
  set η : ℂ := -(E.a₁ * ρ + E.a₃) / 2
  have hns := (equation_iff_nonsingular (W := E.toAffine) (x := ρ) (y := η)).mp ?_
  · rw [nonsingular_iff'] at hns
    rcases hns.2 with h | h
    · apply h
      simp only [psiP, sP, cP, derivative_add, derivative_mul, derivative_pow, derivative_C,
        derivative_X, derivative_ofNat, eval_add, eval_mul, eval_pow, eval_C, eval_X,
        eval_ofNat, zero_mul, zero_add, mul_one, add_zero] at hdev
      simp only [η]
      linear_combination (-1 / 4 : ℂ) * hdev
    · apply h
      simp only [η]
      ring
  · rw [equation_iff']
    simp only [psiP, sP, cP, eval_add, eval_mul, eval_pow, eval_C, eval_X, eval_ofNat] at hev
    simp only [η]
    linear_combination (-1 / 4 : ℂ) * hev

/-! ### The function field `ℂ(E)` over `ℂ(x)` -/

attribute [local instance] FractionRing.liftAlgebra

local notation "K" => FractionRing ℂ[X]
local notation "L" => E.toAffine.FunctionField
local notation "R" => E.toAffine.CoordinateRing

/-- The basis `{1, y}` of `ℂ(E)` over `ℂ(x)`. -/
noncomputable abbrev bL : Module.Basis (Fin 2) K L :=
  (CoordinateRing.basis E.toAffine).localizationLocalization K (nonZeroDivisors ℂ[X]) L

/-- `y ∈ ℂ(E)`. -/
noncomputable abbrev yL : L := algebraMap R L (CoordinateRing.mk E.toAffine Polynomial.X)

omit [E.IsElliptic] in
lemma bL_zero : bL E 0 = 1 := by simp

omit [E.IsElliptic] in
lemma bL_one : bL E 1 = yL E := by simp

omit [E.IsElliptic] in
lemma smul_yL (p : ℂ[X]) (v : L) : p • v = algebraMap ℂ[X] K p • v :=
  (algebraMap_smul K p v).symm

omit [E.IsElliptic] in
lemma yL_sq : yL E * yL E = algebraMap K L (algebraMap ℂ[X] K (cP E)) -
    algebraMap K L (algebraMap ℂ[X] K (sP E)) * yL E := by
  have h := CoordinateRing.smul_basis_mul_Y (W' := E.toAffine) 0 1
  simp only [zero_smul, one_smul, zero_add, one_mul, zero_sub] at h
  rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
  have h2 : CoordinateRing.mk E.toAffine Polynomial.X * CoordinateRing.mk E.toAffine Polynomial.X
      = algebraMap ℂ[X] R (cP E) + algebraMap ℂ[X] R (-(sP E)) *
        CoordinateRing.mk E.toAffine Polynomial.X := h
  simp only [yL]
  rw [← map_mul, h2, map_add, map_mul, ← IsScalarTower.algebraMap_apply ℂ[X] R L,
    ← IsScalarTower.algebraMap_apply ℂ[X] R L, IsScalarTower.algebraMap_apply ℂ[X] K L,
    IsScalarTower.algebraMap_apply ℂ[X] K L, map_neg, map_neg]
  ring

omit [E.IsElliptic] in
lemma mul_yL (α β : K) : (α • (1 : L) + β • yL E) * yL E =
    (β * algebraMap ℂ[X] K (cP E)) • (1 : L) + (α - β * algebraMap ℂ[X] K (sP E)) • yL E := by
  simp only [Algebra.smul_def, mul_one, map_mul, map_sub]
  linear_combination (algebraMap K L β) * yL_sq E

omit [E.IsElliptic] in
lemma repr_bL (u v : K) (i : Fin 2) :
    (bL E).repr (u • (1 : L) + v • yL E) i = ![u, v] i := by
  rw [← bL_zero, ← bL_one, map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, Module.Basis.repr_self_apply]
  fin_cases i <;> simp

omit [E.IsElliptic] in
lemma norm_L (α β : K) : Algebra.norm K (α • (1 : L) + β • yL E) =
    α ^ 2 - α * β * algebraMap ℂ[X] K (sP E) - β ^ 2 * algebraMap ℂ[X] K (cP E) := by
  rw [Algebra.norm_eq_matrix_det (bL E), Matrix.det_fin_two, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul, bL_zero, bL_one, mul_one, mul_yL, repr_bL, repr_bL,
    repr_bL, repr_bL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

omit [E.IsElliptic] in
lemma trace_L (α β : K) : Algebra.trace K L (α • (1 : L) + β • yL E) =
    2 * α - β * algebraMap ℂ[X] K (sP E) := by
  rw [Algebra.trace_eq_matrix_trace (bL E), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, bL_zero, bL_one,
    mul_one, mul_yL, repr_bL, repr_bL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **U2c1.** An element of `ℂ(E)` integral over `ℂ[x]` lies in `ℂ[x, y] / (W)`. -/
theorem exists_eq_of_isIntegral (f : L) (hf : IsIntegral ℂ[X] f) :
    ∃ g : R, algebraMap R L g = f := by
  obtain ⟨α, β, rfl⟩ : ∃ α β : K, α • (1 : L) + β • yL E = f := by
    have h := (bL E).sum_equivFun f
    rw [Fin.sum_univ_two, bL_zero, bL_one] at h
    exact ⟨_, _, h⟩
  set s := algebraMap ℂ[X] K (sP E)
  set c := algebraMap ℂ[X] K (cP E)
  have htr : IsIntegral ℂ[X] (Algebra.trace K L (α • (1 : L) + β • yL E)) :=
    Algebra.isIntegral_trace hf
  have hnm : IsIntegral ℂ[X] (Algebra.norm K (α • (1 : L) + β • yL E)) :=
    Algebra.isIntegral_norm K hf
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp htr
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp hnm
  rw [trace_L] at ht
  rw [norm_L] at hn
  -- `β² Ψ = T² - 4 N`
  have hβ2 : β ^ 2 * algebraMap ℂ[X] K (psiP E) = algebraMap ℂ[X] K (t ^ 2 - 4 * n) := by
    simp only [psiP, map_add, map_mul, map_pow, map_sub, map_ofNat, ht, hn]
    ring
  -- `β ∈ ℂ[x]`
  obtain ⟨b, hb⟩ : ∃ b : ℂ[X], algebraMap ℂ[X] K b = β := by
    obtain ⟨r, q, hrq, hβ⟩ := IsFractionRing.exists_reduced_fraction ℂ[X] β
    have hq0 : algebraMap ℂ[X] K q ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors q.2
    have hβq : β * algebraMap ℂ[X] K q = algebraMap ℂ[X] K r := by
      rw [← hβ, IsLocalization.mk'_spec]
    have hdvd : (q : ℂ[X]) ^ 2 ∣ r ^ 2 * psiP E := by
      refine ⟨t ^ 2 - 4 * n, IsFractionRing.injective ℂ[X] K ?_⟩
      rw [map_mul, map_mul, map_pow, map_pow, ← hβq, ← hβ2]
      ring
    have hcop : IsRelPrime ((q : ℂ[X]) ^ 2) (r ^ 2) := (hrq.symm.pow_left).pow_right
    have hq2 : (q : ℂ[X]) * q ∣ psiP E := by
      rw [← pow_two]; exact hcop.dvd_of_dvd_mul_left hdvd
    obtain ⟨u, hu⟩ := (squarefree_psi E) q hq2
    refine ⟨r * ↑u⁻¹, ?_⟩
    rw [← hβ, IsFractionRing.mk'_eq_div, map_mul, div_eq_mul_inv]
    congr 1
    rw [← hu]
    exact map_units_inv (algebraMap ℂ[X] K) u
  -- `α ∈ ℂ[x]`
  obtain ⟨a, ha⟩ : ∃ a : ℂ[X], algebraMap ℂ[X] K a = α := by
    refine ⟨C (1 / 2 : ℂ) * (t + b * sP E), ?_⟩
    have h2 : (C (1 / 2 : ℂ) * 2 : ℂ[X]) = 1 := by
      rw [← map_ofNat C 2, ← C_mul]; norm_num
    have : algebraMap ℂ[X] K (C (1 / 2 : ℂ)) * 2 = 1 := by
      rw [← map_ofNat (algebraMap ℂ[X] K) 2, ← map_mul, h2, map_one]
    rw [map_mul, map_add, map_mul, ht, hb]
    linear_combination α * this
  refine ⟨a • 1 + b • CoordinateRing.mk E.toAffine Polynomial.X, ?_⟩
  rw [map_add, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, map_one, mul_one,
    ← IsScalarTower.algebraMap_apply ℂ[X] R L, ← IsScalarTower.algebraMap_apply ℂ[X] R L,
    IsScalarTower.algebraMap_apply ℂ[X] K L, IsScalarTower.algebraMap_apply ℂ[X] K L, ha, hb,
    Algebra.smul_def, Algebra.smul_def, mul_one]

end OrbicurveCores.Rigid
