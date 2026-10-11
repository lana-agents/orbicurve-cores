/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Order
import OrbicurveCores.Genuine.Rigid.Eval
import OrbicurveCores.Genuine.Assembly

/-!
# U2c9: `U2Rigidity`

Let `(A, B)` uniformise `E ∖ 0` via `π`, with `[Comm(Γ) : Γ] = 4`. For a finite étale cover
`p : Z → X = E ∖ 0` and a finite étale `φ : Z → H = (E ∖ 0)/±1`:

1. `σ_X` lifts to a holomorphic family of points `τ` of `Z` (`exists_lift`);
2. `F = τ(φ^* x)` is invariant under the finite-index stabiliser `Γ_τ ≤ Γ` of `τ`, proper modulo
   `Γ_τ` (integrality of `A_Z` over `ℂ[φ^* x]`), and has local normal forms of the signature
   `m_H` of `H` (the étale condition and `hasLocalForm_of_mem_pow`); so does `u = x ∘ π`;
3. hence `F = u` (`UnifProps.eq_u_of`), i.e. `τ(φ^* x - p^* x) = 0`, and `φ^* x = p^* x`
   (`eq_zero_of_forall`).
-/

open Polynomial Set Filter UpperHalfPlane
open scoped Topology MatrixGroups
open OrbicurveCores.S1 (upper HasLocalForm)
open Subgroup.Commensurable (commensurator)

namespace OrbicurveCores.Rigid

/-- The signature of `(E ∖ 0)/±1`: the stabiliser order at `x = t`. -/
noncomputable def sigH (E : WeierstrassCurve ℂ) (t : ℂ) : ℕ :=
  (AffOrbicurve.hemi E).mult (Ideal.span {X - C t})

lemma hasLocalForm_of_sub_const {f : ℂ → ℂ} {z c : ℂ} {n : ℕ}
    (h : HasLocalForm (fun y ↦ f y - c) z n) : HasLocalForm f z n := by
  obtain ⟨g, hg, hg0, hgd, hev⟩ := h
  refine ⟨g, hg, hg0, hgd, ?_⟩
  filter_upwards [hev] with y hy
  linear_combination hy

section Generic

variable {S : Type*} [CommRing S] [IsDedekindDomain S] [Algebra ℂ S]
  {τ : ℂ → (S →ₐ[ℂ] ℂ)}

omit [IsDedekindDomain S] in
lemma comap_ker_eq (f : ℂ[X] →ₐ[ℂ] S) (y : ℂ) :
    (RingHom.ker (τ y)).comap f = Ideal.span {X - C (τ y (f X))} := by
  have h : (τ y).comp f = aeval (τ y (f X)) := Polynomial.algHom_ext (by simp)
  rw [← ker_evalRingHom]
  ext q
  simp only [Ideal.mem_comap, RingHom.mem_ker]
  change (τ y).comp f q = 0 ↔ _
  rw [h]
  exact Iff.rfl

/-- **Local normal forms from the étale condition.** -/
theorem hasLocalForm_of_ramificationIdx (hτ : ∀ a, DifferentiableOn ℂ (fun y ↦ τ y a) upper)
    {y : ℂ} (hy : y ∈ upper) {g : S} (hg0 : τ y g = 0) (hgd : deriv (fun y' ↦ τ y' g) y ≠ 0)
    (f : ℂ[X] →ₐ[ℂ] S) (hf : Function.Injective f) (m : Ideal ℂ[X] → ℕ)
    (het : ∀ w : Ideal S, w.IsMaximal →
      (letI := f.toRingHom.toAlgebra; w.ramificationIdx ℂ[X]) = m (w.comap f)) :
    HasLocalForm (fun y' ↦ τ y' (f X)) y (m (Ideal.span {X - C (τ y (f X))})) := by
  haveI := ker_isMaximal (τ y)
  set t₀ := τ y (f X)
  set w := RingHom.ker (τ y)
  set d := f X - algebraMap ℂ S t₀
  have hd : d = f (X - C t₀) := by
    rw [map_sub, ← algebraMap_eq (R := ℂ), AlgHom.commutes]
  have hdw : d ∈ w := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_self]
  have hd0 : d ≠ 0 := by
    rw [hd]; exact fun h ↦ X_sub_C_ne_zero t₀ (hf (h.trans (map_zero f).symm))
  obtain ⟨k, hk, hk1, hk2⟩ := exists_order hd0 hdw
  have hl := hasLocalForm_of_mem_pow S1.isOpen_upper hτ hy hg0 hgd hk hk1 hk2
  have hfun : (fun y' ↦ τ y' d) = fun y' ↦ τ y' (f X) - t₀ := by
    funext y'
    simp only [d, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
  rw [hfun] at hl
  have hram := ramificationIdx_eq_of_mem_pow f hf (comap_ker_eq f y) hk1 hk2
  have h2 := het w inferInstance
  rw [hram, comap_ker_eq] at h2
  rw [← h2]
  exact hasLocalForm_of_sub_const hl

/-- A function vanishing along a family of points with a local coordinate is zero. -/
theorem eq_zero_of_forall (hτ : ∀ a, DifferentiableOn ℂ (fun y ↦ τ y a) upper) {y : ℂ}
    (hy : y ∈ upper) {g : S} (hg0 : τ y g = 0) (hgd : deriv (fun y' ↦ τ y' g) y ≠ 0) {d : S}
    (hd : ∀ y' ∈ upper, τ y' d = 0) : d = 0 := by
  by_contra hd0
  haveI := ker_isMaximal (τ y)
  obtain ⟨k, hk, hk1, hk2⟩ := exists_order hd0 (RingHom.mem_ker.mpr (hd y hy))
  have hl := hasLocalForm_of_mem_pow S1.isOpen_upper hτ hy hg0 hgd hk hk1 hk2
  have h1 := ne_eventually_of_hasLocalForm (Nat.pos_of_ne_zero hk) hl
  have h2 : ∀ᶠ y' in 𝓝[≠] y, τ y' d = τ y d :=
    nhdsWithin_le_nhds (by
      filter_upwards [S1.isOpen_upper.mem_nhds hy] with y' hy'
      rw [hd y' hy', hd y hy])
  obtain ⟨y', h3, h4⟩ := (h1.and h2).exists
  exact h3 h4

end Generic

/-! ### Bounds from integrality -/

/-- A root of a monic polynomial is bounded by `1 +` the sum of the norms of the lower
coefficients. -/
lemma norm_le_of_isRoot_monic {q : ℂ[X]} (hq : q.Monic) {r : ℂ} (hr : q.IsRoot r) :
    ‖r‖ ≤ 1 + ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖ := by
  set Sm := ∑ i ∈ Finset.range q.natDegree, ‖q.coeff i‖
  have hS : 0 ≤ Sm := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  by_contra h
  push Not at h
  have hr1 : 1 < ‖r‖ := by linarith
  have heval := hr.eq_zero
  rw [eval_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, one_mul] at heval
  set n := q.natDegree
  have hn : n ≠ 0 := by
    intro h0
    rw [h0, Finset.sum_range_zero, pow_zero, zero_add] at heval
    exact one_ne_zero heval
  have h1 : ‖r‖ ^ n ≤ ∑ i ∈ Finset.range n, ‖q.coeff i‖ * ‖r‖ ^ i := by
    have : r ^ n = -∑ i ∈ Finset.range n, q.coeff i * r ^ i := by linear_combination heval
    rw [← norm_pow, this, norm_neg]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_mul, norm_pow]
  have h2 : ∑ i ∈ Finset.range n, ‖q.coeff i‖ * ‖r‖ ^ i ≤ Sm * ‖r‖ ^ (n - 1) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hr1.le (by rw [Finset.mem_range] at hi; omega)) (norm_nonneg _)
  have h3 : ‖r‖ ^ n = ‖r‖ * ‖r‖ ^ (n - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hn)]
  have h4 : 0 < ‖r‖ ^ (n - 1) := by positivity
  nlinarith

section Bound

variable {S : Type*} [CommRing S] [Algebra ℂ S] {τ : ℂ → (S →ₐ[ℂ] ℂ)}

/-- Elements integral over `ℂ[h]` are bounded where `h` is. -/
theorem exists_bound_of_isIntegral (f : ℂ[X] →ₐ[ℂ] S) {a : S}
    (ha : (f : ℂ[X] →+* S).IsIntegralElem a) (R : ℝ) :
    ∃ M : ℝ, ∀ y, ‖τ y (f X)‖ ≤ R → ‖τ y a‖ ≤ M := by
  obtain ⟨P, hPm, hP⟩ := ha
  have hcont : ∀ i, ∃ Mi : ℝ, ∀ t : ℂ, ‖t‖ ≤ R → ‖(P.coeff i).eval t‖ ≤ Mi := fun i ↦ by
    obtain ⟨Mi, hMi⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
      (P.coeff i).continuous.continuousOn
    exact ⟨Mi, fun t ht ↦ hMi t (by simpa using ht)⟩
  choose Mi hMi using hcont
  refine ⟨1 + ∑ i ∈ Finset.range P.natDegree, Mi i, fun y hy ↦ ?_⟩
  set t := τ y (f X)
  have hcomp : ∀ c : ℂ[X], τ y (f c) = c.eval t := fun c ↦ by
    have h : (τ y).comp f = aeval t := Polynomial.algHom_ext (by simp [t])
    exact AlgHom.congr_fun h c
  set Q := P.map (evalRingHom t)
  have hQm : Q.Monic := hPm.map _
  have hring : ((τ y : S →+* ℂ).comp (f : ℂ[X] →+* S)) = evalRingHom t :=
    RingHom.ext fun c ↦ hcomp c
  have hroot : Q.IsRoot (τ y a) := by
    rw [IsRoot, eval_map, ← hring]
    change eval₂ ((τ y : S →+* ℂ).comp (f : ℂ[X] →+* S)) ((τ y : S →+* ℂ) a) P = 0
    rw [← Polynomial.hom_eval₂, hP, map_zero]
  refine (norm_le_of_isRoot_monic hQm hroot).trans ?_
  rw [hPm.natDegree_map]
  gcongr with i hi
  simp only [Q, coeff_map, coe_evalRingHom]
  exact hMi i t hy

end Bound

/-! ### The uniformisation -/

section Curve

variable {E : WeierstrassCurve ℂ} [E.IsElliptic] {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

variable (E) in
/-- The function `y` on `E ∖ 0`. -/
noncomputable def yR : AffOrbicurve.puncturedRing E :=
  coordEquiv E (WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine Polynomial.X)

lemma sigmaX_yR (hπ : UnifProps E A B π) (y : ℂ) : sigmaX hπ (yR E) y = (piC π y).2 := by
  rw [sigmaX_apply, yR, AlgEquiv.symm_apply_apply, evP_mk, evalEval_X]

variable (E) in
/-- The function `x` on `E ∖ 0`. -/
noncomputable def xR : AffOrbicurve.puncturedRing E := algebraMap ℂ[X] _ Polynomial.X

omit [E.IsElliptic] in
lemma xR_eq : xR E = Genuine.hemiMap E Polynomial.X := rfl

lemma sigmaX_xR (hπ : UnifProps E A B π) (y : ℂ) : sigmaX hπ (xR E) y = (piC π y).1 :=
  sigmaX_hemiMap hπ y

/-- The points `z ↦ π z` of `E ∖ 0`. -/
noncomputable def evX (hπ : UnifProps E A B π) (z : ℂ) : AffOrbicurve.puncturedRing E →ₐ[ℂ] ℂ :=
  (Pi.evalAlgHom ℂ (fun _ ↦ ℂ) z).comp (sigmaX hπ)

lemma evX_apply (hπ : UnifProps E A B π) (z : ℂ) (r : AffOrbicurve.puncturedRing E) :
    evX hπ z r = sigmaX hπ r z := rfl

/-- **A local coordinate**: `x - x₀` or `y - y₀` pulled back along a family of points over
`z ↦ π z`. -/
lemma exists_uniformizer (hπ : UnifProps E A B π) {S : Type*} [CommRing S] [Algebra ℂ S]
    (f : AffOrbicurve.puncturedRing E →ₐ[ℂ] S) {τ : ℂ → (S →ₐ[ℂ] ℂ)}
    (hτ : ∀ y ∈ upper, (τ y).comp f = evX hπ y) {y : ℂ} (hy : y ∈ upper) :
    ∃ g : S, τ y g = 0 ∧ deriv (fun y' ↦ τ y' g) y ≠ 0 := by
  have hd0 := (hπ.diff ⟨y, hy⟩).2
  rw [hπ.deriv_eq ⟨y, hy⟩] at hd0
  have hval : ∀ r, ∀ y' ∈ upper, τ y' (f r) = sigmaX hπ r y' := fun r y' hy' ↦
    AlgHom.congr_fun (hτ y' hy') r
  have hnhds : upper ∈ 𝓝 y := S1.isOpen_upper.mem_nhds hy
  by_cases h1 : deriv (fun w ↦ (π w).1) y = 0
  · have h2 : deriv (fun w ↦ (π w).2) y ≠ 0 := fun h2 ↦ hd0 (Prod.ext h1 h2)
    refine ⟨f (yR E - algebraMap ℂ _ (π y).2), ?_, ?_⟩
    · rw [hval _ y hy]
      simp only [map_sub, Pi.sub_apply, AlgHom.commutes, Pi.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [sigmaX_yR, piC_of_mem hy, sub_self]
    · have : (fun y' ↦ τ y' (f (yR E - algebraMap ℂ _ (π y).2))) =ᶠ[𝓝 y]
          fun y' ↦ (π y').2 - (π y).2 := by
        filter_upwards [hnhds] with y' hy'
        rw [hval _ y' hy']
        simp only [map_sub, Pi.sub_apply, AlgHom.commutes, Pi.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [sigmaX_yR, piC_of_mem hy']
      rw [this.deriv_eq, deriv_sub_const]
      exact h2
  · refine ⟨f (xR E - algebraMap ℂ _ (π y).1), ?_, ?_⟩
    · rw [hval _ y hy]
      simp only [map_sub, Pi.sub_apply, AlgHom.commutes, Pi.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply]
      rw [sigmaX_xR, piC_of_mem hy, sub_self]
    · have : (fun y' ↦ τ y' (f (xR E - algebraMap ℂ _ (π y).1)))
          =ᶠ[𝓝 y] fun y' ↦ (π y').1 - (π y).1 := by
        filter_upwards [hnhds] with y' hy'
        rw [hval _ y' hy']
        simp only [map_sub, Pi.sub_apply, AlgHom.commutes, Pi.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply]
        rw [sigmaX_xR, piC_of_mem hy']
      rw [this.deriv_eq, deriv_sub_const]
      exact h1

lemma isMaximal_span_X_sub_C (t : ℂ) : (Ideal.span {X - C t} : Ideal ℂ[X]).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible (irreducible_X_sub_C t)

lemma sigH_pos (E : WeierstrassCurve ℂ) [E.IsElliptic] (t : ℂ) : 0 < sigH E t :=
  (AffOrbicurve.hemi E).mult_pos _ (isMaximal_span_X_sub_C t)

lemma finite_sigH (E : WeierstrassCurve ℂ) [E.IsElliptic] : {t | sigH E t ≠ 1}.Finite := by
  have h := (AffOrbicurve.hemi E).finite_mult
  set f : ℂ → Ideal (AffOrbicurve.hemi E).A := fun t ↦ Ideal.span {X - C t}
  have hinj : Set.InjOn f (f ⁻¹' {v | v.IsMaximal ∧ (AffOrbicurve.hemi E).mult v ≠ 1}) := by
    intro t _ t' _ htt
    have h1 : (X - C t : ℂ[X]) ∈ f t' := by
      rw [← htt]; exact Ideal.mem_span_singleton_self _
    have h2 : (X - C t' : ℂ[X]) ∣ X - C t := Ideal.mem_span_singleton.mp h1
    rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_X, eval_C, sub_eq_zero] at h2
    exact h2.symm
  refine (h.preimage hinj).subset fun t ht ↦ ⟨isMaximal_span_X_sub_C t, ht⟩

end Curve

end OrbicurveCores.Rigid
