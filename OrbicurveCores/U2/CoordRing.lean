/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import Pi1.Orbicurve.Elliptic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The coordinate ring of `E ∖ {0}` is integrally closed

For an elliptic curve `E / ℂ`, every element of the function field `ℂ(E)` integral over `ℂ[x]`
lies in the coordinate ring `ℂ[E] = ℂ[x, y]` (`U2.mem_range_of_isIntegral`); hence pi1's
`puncturedRing E` (the integral closure of `ℂ[x]` in `ℂ(E)`) is `ℂ[E]`
(`U2.puncturedRingEquiv`).

Write `z = e / N` with `e = p + q y ∈ ℂ[E]` and `N ∈ ℂ[x]` (multiply by the conjugate of the
denominator). The trace `(2p - a q)/N` and the norm `(p² - a p q - b q²)/N²` of `z` are integral
over `ℂ[x]`, hence polynomials (`a = a₁x + a₃`, `b = x³ + a₂x² + a₄x + a₆`). Since
`4(p² - a p q - b q²) = (2p - a q)² - D q²` with `D = a² + 4b` squarefree (a double root of `D` is
a singular point of `E`), `N ∣ q` and `N ∣ p`.
-/

open Polynomial

namespace OrbicurveCores.U2

attribute [local instance] FractionRing.liftAlgebra

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]


/-- `a = a₁ x + a₃`. -/
noncomputable def aP : ℂ[X] := C E.a₁ * X + C E.a₃

/-- `b = x³ + a₂ x² + a₄ x + a₆`. -/
noncomputable def bP : ℂ[X] := X ^ 3 + C E.a₂ * X ^ 2 + C E.a₄ * X + C E.a₆

/-- The discriminant `D = a² + 4b` of the equation in `y`. -/
noncomputable def DP : ℂ[X] := aP E ^ 2 + C 4 * bP E

omit [E.IsElliptic] in
theorem DP_natDegree : (DP E).natDegree = 3 := by
  unfold DP aP bP; compute_degree!

omit [E.IsElliptic] in
theorem DP_ne_zero : DP E ≠ 0 := fun h ↦ by
  have := DP_natDegree E; rw [h, natDegree_zero] at this; exact absurd this (by norm_num)

/-- `D` has no square factors: a double root of `D` gives a singular point. -/
theorem isUnit_of_sq_dvd_DP {g : ℂ[X]} (h : g ^ 2 ∣ DP E) : IsUnit g := by
  by_contra hg
  have hD0 : DP E ≠ 0 := DP_ne_zero E
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hD0 (by simpa using h)
  have hdeg : g.degree ≠ 0 := fun hd ↦ hg (isUnit_iff_degree_eq_zero.mpr hd)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_root g hdeg
  obtain ⟨h₁, hh₁⟩ := dvd_iff_isRoot.mpr hr
  obtain ⟨k, hk⟩ := h
  have hD : DP E = (X - C r) ^ 2 * (h₁ ^ 2 * k) := by rw [hk, hh₁]; ring
  have hDr : (DP E).eval r = 0 := by rw [hD]; simp
  have hD'r : (derivative (DP E)).eval r = 0 := by
    rw [hD]; simp [derivative_mul, derivative_pow]
  set y₀ := -(E.a₁ * r + E.a₃) / 2
  have heq : E.toAffine.Equation r y₀ := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [DP, aP, bP, eval_add, eval_pow, eval_mul, eval_C, eval_X] at hDr
    simp only [y₀]
    linear_combination (-1 / 4 : ℂ) * hDr
  have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := E.toAffine)).mp heq
  rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
  rcases hns.2 with h1 | h1
  · apply h1
    simp [DP, aP, bP, derivative_mul, derivative_pow] at hD'r
    simp only [y₀]
    linear_combination (-1 / 4 : ℂ) * hD'r
  · apply h1
    simp only [y₀]
    ring

/-- `N² ∣ D Q²` implies `N ∣ Q`. -/
theorem dvd_of_sq_dvd_DP_mul {N Q : ℂ[X]} (h : N ^ 2 ∣ DP E * Q ^ 2) : N ∣ Q := by
  classical
  by_cases hN : N = 0
  · subst hN
    have : DP E * Q ^ 2 = 0 := by simpa using h
    have hD0 : DP E ≠ 0 := DP_ne_zero E
    rw [mul_eq_zero] at this
    rcases this with h | h
    · exact absurd h hD0
    · rw [pow_eq_zero_iff two_ne_zero] at h; rw [h]
  obtain ⟨d, Q₁, N₁, hcop, hQ, hNd⟩ : ∃ d Q₁ N₁ : ℂ[X], IsCoprime Q₁ N₁ ∧ Q = d * Q₁ ∧
      N = d * N₁ :=
    ⟨GCDMonoid.gcd Q N, Q / GCDMonoid.gcd Q N, N / GCDMonoid.gcd Q N,
      isCoprime_div_gcd_div_gcd hN,
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hN) (gcd_dvd_left Q N)).symm,
      (EuclideanDomain.mul_div_cancel' (gcd_ne_zero_of_right hN) (gcd_dvd_right Q N)).symm⟩
  have hd0 : d ≠ 0 := fun h0 ↦ hN (by rw [hNd, h0, zero_mul])
  have h2 : N₁ ^ 2 ∣ DP E * Q₁ ^ 2 := by
    rw [hNd, hQ, mul_pow, mul_pow, mul_left_comm] at h
    exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hd0)).mp h
  have h3 : N₁ ^ 2 ∣ DP E := (hcop.symm.pow).dvd_of_dvd_mul_right h2
  have hu := isUnit_of_sq_dvd_DP E h3
  rw [hNd, hQ]
  exact mul_dvd_mul_left d hu.dvd

local notation "R" => E.toAffine.CoordinateRing
local notation "Lf" => E.toAffine.FunctionField

/-- The coordinate `y`. -/
noncomputable abbrev yR : R := WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine X

omit [E.IsElliptic] in
theorem polynomial_eq : E.toAffine.polynomial = X ^ 2 + C (aP E) * X - C (bP E) := rfl

omit [E.IsElliptic] in
theorem yR_sq : yR E ^ 2 + algebraMap ℂ[X] R (aP E) * yR E = algebraMap ℂ[X] R (bP E) := by
  have h : AdjoinRoot.mk E.toAffine.polynomial (X ^ 2 + C (aP E) * X - C (bP E)) = 0 := by
    rw [← polynomial_eq]; exact AdjoinRoot.mk_self
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_C] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  linear_combination h

/-- The involution `y ↦ -y - a` of `ℂ[E]` over `ℂ[x]`. -/
noncomputable def conjR : R →ₐ[ℂ[X]] R :=
  AdjoinRoot.liftAlgHom E.toAffine.polynomial (Algebra.ofId ℂ[X] R)
    (-yR E - algebraMap ℂ[X] R (aP E)) (by
      change eval₂ _ _ (X ^ 2 + C (aP E) * X - C (bP E)) = 0
      simp only [eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C]
      have h := yR_sq E
      change _ = (0 : R)
      simp only [RingHom.coe_coe, Algebra.ofId_apply]
      linear_combination h)

omit [E.IsElliptic] in
theorem conjR_yR : conjR E (yR E) = -yR E - algebraMap ℂ[X] R (aP E) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

omit [E.IsElliptic] in
theorem conjR_basis (p q : ℂ[X]) :
    conjR E (p • (1 : R) + q • yR E) = (p - q * aP E) • (1 : R) - q • yR E := by
  simp only [map_add, map_one, conjR_yR, Algebra.smul_def, map_sub, map_mul, AlgHom.commutes]
  ring

omit [E.IsElliptic] in
theorem mul_conjR_basis (p q : ℂ[X]) :
    (p • (1 : R) + q • yR E) * conjR E (p • (1 : R) + q • yR E) =
      algebraMap ℂ[X] R (p ^ 2 - p * q * aP E - q ^ 2 * bP E) := by
  rw [conjR_basis]
  have h := yR_sq E
  simp only [Algebra.smul_def, map_sub, map_mul, map_pow, mul_one]
  linear_combination (-(algebraMap ℂ[X] R q) ^ 2) * h

omit [E.IsElliptic] in
theorem conjR_conjR (r : R) : conjR E (conjR E r) = r := by
  obtain ⟨p, q, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
  change conjR E (conjR E (p • (1 : R) + q • yR E)) = p • (1 : R) + q • yR E
  rw [conjR_basis, sub_eq_add_neg, ← neg_smul, conjR_basis]
  simp only [Algebra.smul_def, map_sub, map_neg, map_mul, mul_one]
  ring

omit [E.IsElliptic] in
/-- Integral quotients of polynomials are polynomials. -/
theorem dvd_of_isIntegral {f g : ℂ[X]} (hg : g ≠ 0)
    (h : IsIntegral ℂ[X] (algebraMap ℂ[X] Lf f / algebraMap ℂ[X] Lf g)) : g ∣ f := by
  set K := FractionRing ℂ[X]
  have hinjK : Function.Injective (algebraMap K Lf) := (algebraMap K Lf).injective
  set w : K := algebraMap ℂ[X] K f / algebraMap ℂ[X] K g
  have hw : algebraMap K Lf w = algebraMap ℂ[X] Lf f / algebraMap ℂ[X] Lf g := by
    simp only [w, map_div₀, ← IsScalarTower.algebraMap_apply]
  rw [← hw] at h
  have hwi : IsIntegral ℂ[X] w :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℂ[X] K Lf) hinjK).mp h
  obtain ⟨u, hu⟩ := IsIntegrallyClosed.isIntegral_iff.mp hwi
  refine ⟨u, IsFractionRing.injective ℂ[X] K ?_⟩
  have hg' : algebraMap ℂ[X] K g ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective ℂ[X] K)]
  rw [map_mul, hu]
  simp only [w]
  rw [mul_comm]; exact (div_mul_cancel₀ _ hg').symm

/-- **The coordinate ring is integrally closed**: integral elements of `ℂ(E)` lie in `ℂ[E]`. -/
theorem mem_range_of_isIntegral {z : Lf} (hzi : IsIntegral ℂ[X] z) :
    ∃ r : R, algebraMap R Lf r = z := by
  classical
  have hinjR : Function.Injective (algebraMap R Lf) := IsFractionRing.injective R Lf
  -- the involution on `ℂ(E)`
  have hconj_inj : Function.Injective ((IsScalarTower.toAlgHom ℂ[X] R Lf).comp (conjR E)) :=
    hinjR.comp (Function.LeftInverse.injective (conjR_conjR E))
  set σ : Lf →ₐ[ℂ[X]] Lf := IsFractionRing.liftAlgHom hconj_inj
  have hσ : ∀ r : R, σ (algebraMap R Lf r) = algebraMap R Lf (conjR E r) := fun r ↦ by
    simp [σ, IsFractionRing.lift_algebraMap]
  -- `z = e / N`
  obtain ⟨c, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := R) z
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨p, q, hpq⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq d
  set N := p ^ 2 - p * q * aP E - q ^ 2 * bP E
  have hdN : d * conjR E d = algebraMap ℂ[X] R N := by rw [← hpq]; exact mul_conjR_basis E p q
  have hN0 : N ≠ 0 := by
    intro h0
    have : d * conjR E d = 0 := by rw [hdN, h0, map_zero]
    rcases mul_eq_zero.mp this with h | h
    · exact hd0 h
    · exact hd0 (by rw [← conjR_conjR E d, h, map_zero])
  obtain ⟨p', q', he⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq
    (c * conjR E d)
  have hNL : algebraMap R Lf (algebraMap ℂ[X] R N) = algebraMap ℂ[X] Lf N :=
    (IsScalarTower.algebraMap_apply ℂ[X] R Lf N).symm
  have hdL : algebraMap R Lf d ≠ 0 := by rwa [ne_eq, map_eq_zero_iff _ hinjR]
  have hcdL : algebraMap R Lf (conjR E d) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ hinjR]
    intro h; exact hd0 (by rw [← conjR_conjR E d, h, map_zero])
  have hz : algebraMap R Lf c / algebraMap R Lf d =
      algebraMap R Lf (c * conjR E d) / algebraMap ℂ[X] Lf N := by
    rw [← hNL, ← hdN, map_mul, map_mul, mul_div_mul_right _ _ hcdL]
  have hz0 := hzi
  rw [hz]
  rw [hz] at hz0
  set e := c * conjR E d
  have hNL0 : algebraMap ℂ[X] Lf N ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective ℂ[X] Lf)]; exact hN0
  have hσN : σ (algebraMap ℂ[X] Lf N) = algebraMap ℂ[X] Lf N := σ.commutes N
  have hσz : σ (algebraMap R Lf e / algebraMap ℂ[X] Lf N) =
      algebraMap R Lf (conjR E e) / algebraMap ℂ[X] Lf N := by
    rw [map_div₀, hσ, hσN]
  -- the trace
  have htr : algebraMap R Lf e / algebraMap ℂ[X] Lf N +
      σ (algebraMap R Lf e / algebraMap ℂ[X] Lf N) =
      algebraMap ℂ[X] Lf (2 * p' - q' * aP E) / algebraMap ℂ[X] Lf N := by
    rw [hσz, ← add_div, ← map_add, ← he, conjR_basis]
    congr 1
    rw [IsScalarTower.algebraMap_apply ℂ[X] R Lf]
    congr 1
    simp only [Algebra.smul_def, mul_one, map_sub, map_mul, map_ofNat]
    ring
  have hdvd1 : N ∣ 2 * p' - q' * aP E := dvd_of_isIntegral E hN0 (htr ▸ hz0.add (hz0.map σ))
  -- the norm
  have hnm : algebraMap R Lf e / algebraMap ℂ[X] Lf N *
      σ (algebraMap R Lf e / algebraMap ℂ[X] Lf N) =
      algebraMap ℂ[X] Lf (p' ^ 2 - p' * q' * aP E - q' ^ 2 * bP E) /
        algebraMap ℂ[X] Lf (N ^ 2) := by
    rw [hσz, div_mul_div_comm, ← map_mul, ← he, mul_conjR_basis,
      ← IsScalarTower.algebraMap_apply ℂ[X] R Lf, map_pow, pow_two (algebraMap ℂ[X] Lf N)]
  have hN20 : N ^ 2 ≠ 0 := pow_ne_zero 2 hN0
  have hdvd2 : N ^ 2 ∣ p' ^ 2 - p' * q' * aP E - q' ^ 2 * bP E :=
    dvd_of_isIntegral E hN20 (hnm ▸ hz0.mul (hz0.map σ))
  -- `N ∣ q'` and `N ∣ p'`
  have hdvd3 : N ^ 2 ∣ DP E * q' ^ 2 := by
    have h1 : N ^ 2 ∣ (2 * p' - q' * aP E) ^ 2 := pow_dvd_pow_of_dvd hdvd1 2
    have h2 : N ^ 2 ∣ 4 * (p' ^ 2 - p' * q' * aP E - q' ^ 2 * bP E) := dvd_mul_of_dvd_right hdvd2 _
    have : DP E * q' ^ 2 =
        (2 * p' - q' * aP E) ^ 2 - 4 * (p' ^ 2 - p' * q' * aP E - q' ^ 2 * bP E) := by
      have h4 : (C 4 : ℂ[X]) = 4 := map_ofNat C 4
      rw [DP, h4]; ring
    rw [this]; exact dvd_sub h1 h2
  obtain ⟨v, hv⟩ := dvd_of_sq_dvd_DP_mul E hdvd3
  have hp2 : N ∣ 2 * p' := by
    have := dvd_add hdvd1 (dvd_mul_of_dvd_left (⟨v, hv⟩ : N ∣ q') (aP E))
    rwa [sub_add_cancel] at this
  have hu2 : IsUnit (2 : ℂ[X]) := by
    rw [show (2 : ℂ[X]) = C 2 from (map_ofNat C 2).symm]; exact isUnit_C.mpr (by norm_num)
  obtain ⟨u, hu⟩ := hu2.dvd_mul_left.mp hp2
  refine ⟨u • (1 : R) + v • yR E, ?_⟩
  rw [eq_div_iff hNL0, ← he, hu, hv, ← hNL, ← map_mul]
  congr 1
  simp only [Algebra.smul_def, map_mul, mul_one]
  ring


end OrbicurveCores.U2

namespace OrbicurveCores.U2

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

attribute [local instance] FractionRing.liftAlgebra

/-- `ℂ[E]` lands in the integral closure of `ℂ[x]` in `ℂ(E)`. -/
noncomputable def toPuncturedRing :
    E.toAffine.CoordinateRing →ₐ[ℂ[X]] AffOrbicurve.puncturedRing E :=
  AlgHom.codRestrict (IsScalarTower.toAlgHom ℂ[X] _ E.toAffine.FunctionField)
    (integralClosure ℂ[X] E.toAffine.FunctionField) fun r ↦
      (Algebra.IsIntegral.isIntegral (R := ℂ[X]) r).map
        (IsScalarTower.toAlgHom ℂ[X] _ E.toAffine.FunctionField)

theorem toPuncturedRing_bijective : Function.Bijective (toPuncturedRing E) := by
  refine ⟨fun r r' h ↦ IsFractionRing.injective E.toAffine.CoordinateRing
    E.toAffine.FunctionField (congrArg Subtype.val h), fun z ↦ ?_⟩
  obtain ⟨r, hr⟩ := mem_range_of_isIntegral E z.2
  exact ⟨r, Subtype.ext hr⟩

/-- **`puncturedRing E ≅ ℂ[E]`.** -/
noncomputable def puncturedRingEquiv :
    E.toAffine.CoordinateRing ≃ₐ[ℂ[X]] AffOrbicurve.puncturedRing E :=
  AlgEquiv.ofBijective (toPuncturedRing E) (toPuncturedRing_bijective E)

end OrbicurveCores.U2
