/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Order
import OrbicurveCores.Genuine.Rigid.Eval
import OrbicurveCores.Genuine.Assembly
import OrbicurveCores.Genuine.Descent

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

lemma HasLocalForm.congr_eventually {f g : ℂ → ℂ} {z : ℂ} {n : ℕ} (h : HasLocalForm f z n)
    (hfg : f =ᶠ[𝓝 z] g) : HasLocalForm g z n := by
  obtain ⟨k, hk, hk0, hkd, hev⟩ := h
  refine ⟨k, hk, hk0, hkd, ?_⟩
  filter_upwards [hev, hfg] with y hy hy'
  rw [← hy', hy, hfg.self_of_nhds]

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

/-! ### The main theorem -/

open AffOrbicurve in
/-- **U2Rigidity (analytic core)**. -/
theorem hemiRigid_of_unif {E : WeierstrassCurve ℂ} [E.IsElliptic] {A B : SL(2, ℝ)}
    {π : ℂ → ℂ × ℂ} (hπ : UnifProps E A B π) (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2)
    (hA : tr A ≠ 0)
    (hidx : (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4) :
    Genuine.HemiRigid E := by
  intro Z p φ
  set R := puncturedRing E
  letI : Algebra R Z.A := p.f.toRingHom.toAlgebra
  haveI : IsScalarTower ℂ R Z.A := IsScalarTower.of_algebraMap_eq fun c ↦ (p.f.commutes c).symm
  haveI : Algebra.IsIntegral R Z.A := ⟨p.isIntegral⟩
  haveI : FaithfulSMul R Z.A := (faithfulSMul_iff_algebraMap_injective _ _).mpr p.injective
  haveI : Algebra.FiniteType R Z.A := Algebra.FiniteType.of_restrictScalars_finiteType ℂ _ _
  haveI : Module.Finite R Z.A := Algebra.IsIntegral.finite
  haveI : IsDedekindDomain R := (punctured E).isDedekindDomain
  have hunr : ∀ q : Ideal Z.A, q.IsMaximal → q.ramificationIdx R = 1 := fun q hq ↦ by
    have h := p.etale q hq
    rw [Genuine.punctured_mult] at h
    exact Nat.eq_one_of_mul_eq_one_right h
  have hmultZ : ∀ w : Ideal Z.A, w.IsMaximal → Z.mult w = 1 := Genuine.mult_eq_one_of_hom E p
  set ev := evX hπ
  have hev : ∀ r, DifferentiableOn ℂ (fun z ↦ ev z r) upper := fun r ↦ differentiableOn_sigmaX hπ r
  have hI : Complex.I ∈ upper := by simp [upper]
  haveI : (RingHom.ker (ev Complex.I)).IsMaximal := ker_isMaximal _
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := Z.A)
    (RingHom.ker (ev Complex.I))
  set ψ₀ := (fibEquiv (S := Z.A) (ev Complex.I)).symm ⟨P, hP.isPrime, hPl⟩
  obtain ⟨τ, hτF, -, hτd⟩ := exists_lift hunr S1.isOpen_upper (convex_halfSpace_im_gt 0) hev hI
    ψ₀.2
  have hτc : ∀ y ∈ upper, (τ y).comp (IsScalarTower.toAlgHom ℂ R Z.A) = ev y := hτF
  have hτR : ∀ r, ∀ y ∈ upper, τ y (p.f r) = sigmaX hπ r y := fun r y hy ↦
    AlgHom.congr_fun (hτc y hy) r
  have hunif : ∀ y ∈ upper, ∃ g, τ y g = 0 ∧ deriv (fun y' ↦ τ y' g) y ≠ 0 := fun y hy ↦
    exists_uniformizer hπ (IsScalarTower.toAlgHom ℂ R Z.A) hτc hy
  -- local normal forms of `F = τ (φ^* x)`
  set F : ℂ → ℂ := fun y ↦ τ y (φ.f X)
  have hF : DifferentiableOn ℂ F upper := hτd _
  have hloc : ∀ y ∈ upper, HasLocalForm F y (sigH E (F y)) := fun y hy ↦ by
    obtain ⟨g, hg0, hgd⟩ := hunif y hy
    exact hasLocalForm_of_ramificationIdx hτd hy hg0 hgd φ.f φ.injective (hemi E).mult
      fun w hw ↦ by have := φ.etale w hw; rwa [hmultZ w hw, mul_one] at this
  -- local normal forms of `u = x ∘ π`
  have hlocU : ∀ y ∈ upper, HasLocalForm (fun y' ↦ (π y').1) y (sigH E (π y).1) := fun y hy ↦ by
    obtain ⟨g, hg0, hgd⟩ := exists_uniformizer hπ (AlgHom.id ℂ R) (τ := ev)
      (fun y _ ↦ AlgHom.comp_id _) hy
    have h := hasLocalForm_of_ramificationIdx (τ := ev) hev hy hg0 hgd (Genuine.hemiMap E)
      (Genuine.hemiHom E).injective (hemi E).mult fun w hw ↦ by
        have := (Genuine.hemiHom E).etale w hw
        rwa [Genuine.punctured_mult, mul_one] at this
    have hxy : ∀ y' ∈ upper, ev y' (Genuine.hemiMap E X) = (π y').1 := fun y' hy' ↦ by
      rw [evX_apply, sigmaX_hemiMap, piC_of_mem hy']
    have hn : sigH E (π y).1 =
        (hemi E).mult (Ideal.span {X - C (ev y (Genuine.hemiMap E X))}) := by
      unfold sigH; rw [← hxy y hy]
    rw [hn]
    refine HasLocalForm.congr_eventually h ?_
    filter_upwards [S1.isOpen_upper.mem_nhds hy] with y' hy'
    exact hxy y' hy'
  -- the stabiliser `Γ_τ` of `τ` in `Γ`
  set Γ := Subgroup.closure {A, B}
  have hmobF : ∀ γ ∈ Γ, ∀ y ∈ upper, τ (mob γ y) ∈ Fib Z.A (ev y) := fun γ hγ y hy ↦ by
    have h := hτF (mob γ y) (mob_mem γ y)
    refine h.trans ?_
    ext r
    exact sigmaX_mob hπ hγ r y
  have hmobc : ∀ γ : SL(2, ℝ), ∀ a, ContinuousOn (fun y ↦ τ (mob γ y) a) upper := fun γ a ↦
    (hτd a).continuousOn.comp (continuousOn_mob γ) fun y _ ↦ mob_mem γ y
  let Γτ : Subgroup SL(2, ℝ) :=
    { carrier := {γ | γ ∈ Γ ∧ ∀ y ∈ upper, τ (mob γ y) = τ y}
      mul_mem' := fun {a b} ha hb ↦ ⟨mul_mem ha.1 hb.1, fun y hy ↦ by
        rw [mob_mul, ha.2 _ (mob_mem _ _), hb.2 y hy]⟩
      one_mem' := ⟨one_mem _, fun y hy ↦ by rw [mob_one hy]⟩
      inv_mem' := fun {a} ha ↦ ⟨inv_mem ha.1, fun y hy ↦ by
        rw [← ha.2 _ (mob_mem _ _), mob_mob_inv _ hy]⟩ }
  have hΓτ : Γτ ≤ Γ := fun γ hγ ↦ hγ.1
  have hinv : ∀ γ ∈ Γτ, ∀ y ∈ upper, F (mob γ y) = F y := fun γ hγ y hy ↦ by
    simp only [F, hγ.2 y hy]
  -- `Γ_τ` has finite index: the lifts `τ ∘ γ⁻¹` are determined by their value at `i`
  have hfi : Γτ.relIndex Γ ≠ 0 := by
    haveI : Finite (Fib Z.A (ev Complex.I)) := (finite_fib (S := Z.A) _).to_subtype
    let Φ₀ : Γ → Fib Z.A (ev Complex.I) := fun γ ↦
      ⟨τ (mob (γ : SL(2, ℝ))⁻¹ Complex.I), hmobF _ (inv_mem γ.2) _ hI⟩
    have hΦ₀ : ∀ γ γ' : Γ, (γ : SL(2, ℝ))⁻¹ * γ' ∈ Γτ → Φ₀ γ = Φ₀ γ' := by
      intro γ γ' h
      apply Subtype.ext
      change τ (mob (γ : SL(2, ℝ))⁻¹ Complex.I) = τ (mob (γ' : SL(2, ℝ))⁻¹ Complex.I)
      have h' := (inv_mem h).2 (mob (γ : SL(2, ℝ))⁻¹ Complex.I) (mob_mem _ _)
      rw [← mob_mul] at h'
      rw [← h']
      congr 1; congr 1; group
    let Φ : Γ ⧸ Γτ.subgroupOf Γ → Fib Z.A (ev Complex.I) :=
      Quotient.lift Φ₀ fun γ γ' h ↦ hΦ₀ γ γ'
        (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp h))
    have hΦ : Function.Injective Φ := by
      intro c c'
      induction c using QuotientGroup.induction_on with | H γ => ?_
      induction c' using QuotientGroup.induction_on with | H γ' => ?_
      intro h
      have h0 : τ (mob (γ : SL(2, ℝ))⁻¹ Complex.I) = τ (mob (γ' : SL(2, ℝ))⁻¹ Complex.I) :=
        congrArg Subtype.val h
      have heq := eqOn_of_lifts hunr S1.isOpen_upper (convex_halfSpace_im_gt 0).isPreconnected
        hev (hmobF _ (inv_mem γ.2)) (hmobF _ (inv_mem γ'.2)) (hmobc _) (hmobc _) hI h0
      refine QuotientGroup.eq.mpr ⟨mul_mem (inv_mem γ.2) γ'.2, fun y hy ↦ ?_⟩
      have := heq (mob (γ' : SL(2, ℝ)) y) (mob_mem _ _)
      rw [mob_inv_mob _ hy] at this
      change τ (mob ((γ : SL(2, ℝ))⁻¹ * γ') y) = τ y
      rw [mob_mul, this]
    haveI : Finite (Γ ⧸ Γτ.subgroupOf Γ) := Finite.of_injective Φ hΦ
    exact Subgroup.index_ne_zero_of_finite
  -- properness modulo `Γ_τ`
  have hprop : ∀ Rr : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖F z‖ ≤ Rr →
      ∃ γ ∈ Γτ, γ • z ∈ C := by
    intro Rr
    obtain ⟨M₁, hM₁⟩ := exists_bound_of_isIntegral (τ := τ) φ.f (φ.isIntegral (p.f (xR E))) Rr
    obtain ⟨M₂, hM₂⟩ := exists_bound_of_isIntegral (τ := τ) φ.f (φ.isIntegral (p.f (yR E))) Rr
    obtain ⟨C, hC, hCp⟩ := hπ.exists_isCompact (max M₁ M₂)
    refine exists_isCompact_of_relIndex hfi hC fun z hz ↦ hCp z ?_
    have h1 : (π z).1 = τ z (p.f (xR E)) := by
      rw [hτR _ _ z.im_pos, sigmaX_xR, piC_of_mem z.im_pos]
    have h2 : (π z).2 = τ z (p.f (yR E)) := by
      rw [hτR _ _ z.im_pos, sigmaX_yR, piC_of_mem z.im_pos]
    rw [Prod.norm_def]
    exact max_le_max (h1 ▸ hM₁ z hz) (h2 ▸ hM₂ z hz)
  -- `F = u`, hence `φ^* x = p^* x`
  have hFu := hπ.eq_u_of hcomm hA hidx (sigH_pos E) (finite_sigH E) hlocU hΓτ hfi hF hinv
    hloc hprop
  have hd : ∀ y ∈ upper, τ y (φ.f X - p.f (Genuine.hemiMap E X)) = 0 := fun y hy ↦ by
    rw [map_sub, sub_eq_zero]
    change F y = _
    rw [hFu y hy, hτR _ y hy, sigmaX_hemiMap, piC_of_mem hy]
  obtain ⟨g, hg0, hgd⟩ := hunif Complex.I hI
  exact sub_eq_zero.mp (eq_zero_of_forall hτd hI hg0 hgd hd)

end OrbicurveCores.Rigid

namespace OrbicurveCores

/-- **U2, rigidity half, over `ℂ`.** -/
theorem u2Rigidity : U2Rigidity := by
  intro E _ A B hcomm hA hU hidx
  obtain ⟨π, hπ⟩ := Rigid.uniformizes_iff.mp hU
  exact Rigid.hemiRigid_of_unif hπ hcomm hA hidx

end OrbicurveCores
