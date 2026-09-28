/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.U2.CoreMap
import OrbicurveCores.U2.HemiUnique

/-!
# U2: assembly of [CanLift] Prop. 2.7 over `ℂ`

* `Hom.descend`: a map of coordinate rings `C → Y` through which a finite étale `Z → C`
  factors via a finite étale `Z → Y` is finite étale.
* ramification of polynomial maps `A¹ → A¹` (`ramificationIdx_aeval`) and of the double cover
  `E ∖ {0} → A¹` (`ramificationIdx_punctured`);
* `canLift27C`: [CanLift] Prop. 2.7 over `ℂ`: the map `x : E ∖ {0} → A¹` (`toHemi`) is
  terminal in `\overline{Loc}(E ∖ {0})`. Existence: Theorem G (`theoremG`) descends `x` to `Y`,
  and `Hom.descend` makes it finite étale. Uniqueness: a second map `Y → hemi E` gives a
  polynomial `p` with `x = p(u)` étale for the hemi-elliptic multiplicities, so `p = X`
  (`hemi_poly_unique`).
-/

open Polynomial Ideal AffOrbicurve

namespace OrbicurveCores.U2

section Descend

variable {k : Type*} [Field k]

/-- **Descent of finite étale maps.** If `χ : Z → C` factors as `Z → Y → C` through a finite
étale `ψ : Z → Y`, the map `Y → C` is finite étale. -/
def Hom.descend {Z Y C : AffOrbicurve k} (ψ : Hom Z Y) (χ : Hom Z C) (g : C.A →ₐ[k] Y.A)
    (hg : ψ.f.comp g = χ.f) : Hom Y C where
  f := g
  injective a b h := χ.injective (by rw [← hg]; simp [h])
  isIntegral a := by
    obtain ⟨p, hpm, hp⟩ := χ.isIntegral (ψ.f a)
    refine ⟨p, hpm, ψ.injective ?_⟩
    rw [map_zero, ← hp]
    change ψ.f.toRingHom (eval₂ g.toRingHom a p) = _
    rw [Polynomial.hom_eval₂, ← hg]
    rfl
  etale w hw := by
    letI := ψ.f.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral Y.A Z.A := ⟨ψ.isIntegral⟩
    obtain ⟨w', hw', hww'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := Z.A) w (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      rw [ψ.injective (hx.trans (map_zero _).symm)]
      exact w.zero_mem)
    have hcomp : ψ.f.toRingHom.comp g.toRingHom = χ.f.toRingHom := by rw [← hg]; rfl
    have h1 := ramificationIdx_comp g.toRingHom ψ.f.toRingHom ψ.injective w'
    have h1' := (ramificationIdx_congr hcomp w').symm.trans h1
    have h2 := χ.etale w' hw'
    have h3 := ψ.etale w' hw'
    have hw'w : w'.comap ψ.f.toRingHom = w := hww'
    have hc : w'.comap χ.f.toRingHom = (w.comap g.toRingHom) := by
      rw [← hw'w, Ideal.comap_comap, hcomp]
    rw [h1', mul_assoc, h3] at h2
    change _ = C.mult (w'.comap χ.f.toRingHom) at h2
    rw [hc] at h2
    change _ * Y.mult (w'.comap ψ.f.toRingHom) = _ at h2
    rw [hw'w] at h2
    exact h2

@[simp] lemma Hom.descend_f {Z Y C : AffOrbicurve k} (ψ : Hom Z Y) (χ : Hom Z C)
    (g : C.A →ₐ[k] Y.A) (hg : ψ.f.comp g = χ.f) : (Hom.descend ψ χ g hg).f = g := rfl

end Descend

section Poly

/-- Ramification indices along an injective ring map, as the classical ramification index. -/
theorem ramificationIdx_toAlgebra {R S : Type*} [CommRing R] [IsDomain R] [CommRing S]
    [IsDedekindDomain S] (f : R →+* S) (hf : Function.Injective f) (q : Ideal S) [q.IsPrime]
    (hq : q.comap f ≠ ⊥) :
    (letI := f.toAlgebra; q.ramificationIdx R) =
      (letI := f.toAlgebra; (q.comap f).ramificationIdx' q) := by
  letI := f.toAlgebra
  haveI : Module.IsTorsionFree R S := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hf
  haveI : q.LiesOver (q.comap f) := ⟨rfl⟩
  exact (ramificationIdx'_eq_ramificationIdx _ _ hq).symm

theorem comap_aeval_span (p : ℂ[X]) (w : ℂ) :
    (span {X - C w} : Ideal ℂ[X]).comap (aeval (R := ℂ) p).toRingHom = span {X - C (p.eval w)} := by
  ext q
  simp only [mem_comap, mem_span_singleton, dvd_iff_isRoot, IsRoot.def]
  change eval w (aeval p q) = 0 ↔ _
  rw [← comp_eq_aeval, eval_comp]

theorem aeval_injective_of_natDegree_pos {p : ℂ[X]} (hp : 0 < p.natDegree) :
    Function.Injective (aeval (R := ℂ) p).toRingHom := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  change aeval p q = 0 at hq
  rw [← comp_eq_aeval, comp_eq_zero_iff] at hq
  rcases hq with hq | ⟨-, hq⟩
  · exact hq
  · exfalso
    have := congrArg natDegree hq
    rw [natDegree_C] at this
    omega

theorem sub_C_ne_zero_of_natDegree_pos {p : ℂ[X]} (hp : 0 < p.natDegree) (c : ℂ) : p - C c ≠ 0 :=
  fun h ↦ by
    have := congrArg natDegree h
    rw [natDegree_sub_C, natDegree_zero] at this
    omega

/-- **Ramification of a polynomial map `A¹ → A¹`**: `e(w) = ord_w (p - p(w))`. -/
theorem ramificationIdx_aeval {p : ℂ[X]} (hp : 0 < p.natDegree) (w : ℂ) :
    (letI := (aeval (R := ℂ) p).toRingHom.toAlgebra;
      (span {X - C w} : Ideal ℂ[X]).ramificationIdx ℂ[X]) =
        Uniformization.RatFuncPoly.ramIdx p w := by
  have hinj := aeval_injective_of_natDegree_pos hp
  haveI : (span {X - C w} : Ideal ℂ[X]).IsPrime :=
    (Ideal.span_singleton_prime (X_sub_C_ne_zero w)).mpr (prime_X_sub_C w)
  have hq : (span {X - C w} : Ideal ℂ[X]).comap (aeval (R := ℂ) p).toRingHom ≠ ⊥ := by
    rw [comap_aeval_span, Ne, Ideal.span_singleton_eq_bot]
    exact X_sub_C_ne_zero _
  rw [ramificationIdx_toAlgebra _ hinj _ hq, comap_aeval_span]
  letI := (aeval (R := ℂ) p).toRingHom.toAlgebra
  have hmap : (span {X - C (p.eval w)} : Ideal ℂ[X]).map (algebraMap ℂ[X] ℂ[X]) =
      span {p - C (p.eval w)} := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change aeval (R := ℂ) p (X - C (p.eval w)) = _
    simp
  have hne := sub_C_ne_zero_of_natDegree_pos hp (p.eval w)
  apply Ideal.ramificationIdx'_spec
  · rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_dvd _ _
  · rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton]
    exact pow_rootMultiplicity_not_dvd hne _

end Poly

section Quadratic

/-- `s² = D` has one solution for `D = 0` and two otherwise. -/
theorem card_sq_eq (D : ℂ) : Nat.card {s : ℂ // s ^ 2 = D} = if D = 0 then 1 else 2 := by
  classical
  obtain ⟨s₀, hs₀⟩ := IsAlgClosed.exists_pow_nat_eq D two_pos
  have e : {s : ℂ // s ^ 2 = D} ≃ {s : ℂ // s ∈ ({s₀, -s₀} : Finset ℂ)} :=
    Equiv.subtypeEquivRight fun s ↦ by
      rw [← hs₀, sq_eq_sq_iff_eq_or_eq_neg]
      simp
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  by_cases hD : D = 0
  · have : s₀ = 0 := by rw [hD] at hs₀; exact pow_eq_zero_iff (two_ne_zero) |>.mp hs₀
    simp [hD, this]
  · have h0 : s₀ ≠ 0 := by rintro rfl; apply hD; rw [← hs₀]; ring
    have hne : s₀ ≠ -s₀ := fun h ↦ h0 (by linear_combination h / 2)
    rw [Finset.card_pair hne, if_neg hD]

/-- Points of `E` over `x = c`. -/
theorem card_equation (E : WeierstrassCurve ℂ) [E.IsElliptic] (c : ℂ) :
    Nat.card {y : ℂ // E.toAffine.Equation c y} = if c ∈ E₂ E then 1 else 2 := by
  classical
  set D := (tq E).eval c
  have e : {y : ℂ // E.toAffine.Equation c y} ≃ {s : ℂ // s ^ 2 = D} := by
    let f : ℂ ≃ ℂ := ⟨fun y ↦ 2 * y + (E.a₁ * c + E.a₃), fun s ↦ (s - (E.a₁ * c + E.a₃)) / 2,
      fun y ↦ by ring, fun s ↦ by ring⟩
    refine Equiv.subtypeEquiv f fun y ↦ ?_
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [f, Equiv.coe_fn_mk, D, tq_eval, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆]
    constructor
    · intro h; linear_combination 4 * h
    · intro h; linear_combination h / 4
  rw [Nat.card_congr e, card_sq_eq]
  have hmem : c ∈ E₂ E ↔ D = 0 := by
    simp [E₂, D, Multiset.mem_toFinset, mem_roots (tq_ne_zero (W := E))]
  simp only [hmem]

end Quadratic

section Punctured

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

instance : Module.Free ℂ[X] (puncturedRing E) :=
  Module.Free.of_equiv (puncturedRingEquiv E).toLinearEquiv

instance : Module.Finite ℂ[X] (puncturedRing E) :=
  Module.Finite.equiv (puncturedRingEquiv E).toLinearEquiv

instance : Algebra.FiniteType ℂ (puncturedRing E) :=
  (inferInstance : Algebra.FiniteType ℂ (punctured E).A)

theorem finrank_puncturedRing : Module.finrank ℂ[X] (puncturedRing E) = 2 := by
  rw [← (puncturedRingEquiv E).toLinearEquiv.finrank_eq,
    Module.finrank_eq_card_basis (WeierstrassCurve.Affine.CoordinateRing.basis E.toAffine)]
  simp

theorem puncturedRingEquiv_xA :
    puncturedRingEquiv E (Uniformization.FEt.xA E) = algebraMap ℂ[X] (puncturedRing E) X :=
  (puncturedRingEquiv E).commutes X

/-- **Points of `E ∖ {0}` over `x = c`.** -/
theorem card_ptOver (c : ℂ) :
    Nat.card (PtOver (puncturedRing E) (aeval c : ℂ[X] →ₐ[ℂ] ℂ)) = if c ∈ E₂ E then 1 else 2 := by
  classical
  rw [← card_equation E c]
  set e := ((puncturedRingEquiv E).restrictScalars ℂ)
  have hχx : ∀ ψ : PtOver (puncturedRing E) (aeval c : ℂ[X] →ₐ[ℂ] ℂ),
      (ψ.1.comp e.toAlgHom) (Uniformization.FEt.xA E) = c := fun ψ ↦ by
    change ψ.1 (puncturedRingEquiv E (Uniformization.FEt.xA E)) = c
    rw [puncturedRingEquiv_xA, ψ.2, aeval_X]
  let Φ : PtOver (puncturedRing E) (aeval c : ℂ[X] →ₐ[ℂ] ℂ) → {y : ℂ // E.toAffine.Equation c y} :=
    fun ψ ↦ ⟨(ψ.1.comp e.toAlgHom) (Uniformization.FEt.yA E), by
      have := Uniformization.FEt.equation_coord (ψ.1.comp e.toAlgHom)
      rwa [hχx] at this⟩
  refine Nat.card_congr (Equiv.ofBijective Φ ⟨fun ψ ψ' h ↦ ?_, fun y ↦ ?_⟩)
  · have h1 : ψ.1.comp e.toAlgHom = ψ'.1.comp e.toAlgHom :=
      Uniformization.FEt.algHom_ext_coord (by rw [hχx, hχx]) (congrArg Subtype.val h)
    refine Subtype.ext (AlgHom.ext fun b ↦ ?_)
    have := congrArg (fun χ : E.toAffine.CoordinateRing →ₐ[ℂ] ℂ ↦ χ (e.symm b)) h1
    simpa using this
  · refine ⟨⟨(Uniformization.FEt.ptAlg E y.2).comp e.symm.toAlgHom, fun a ↦ ?_⟩, Subtype.ext ?_⟩
    · change Uniformization.FEt.ptAlg E y.2 ((puncturedRingEquiv E).symm (algebraMap ℂ[X] _ a)) = _
      rw [AlgEquiv.commutes]
      change Uniformization.FEt.ptAlg E y.2
        (WeierstrassCurve.Affine.CoordinateRing.mk E.toAffine (C a)) = _
      rw [Uniformization.FEt.ptAlg_mk, evalEval_C, coe_aeval_eq_eval]
    · change Uniformization.FEt.ptAlg E y.2 (e.symm (e (Uniformization.FEt.yA E))) = _
      rw [AlgEquiv.symm_apply_apply, Uniformization.FEt.ptAlg_mk, evalEval_X]

/-- **Ramification of `E ∖ {0} → A¹`**: `e = 2` over `E₂`, `e = 1` elsewhere. -/
theorem ramificationIdx_punctured (c : ℂ) {q : Ideal (puncturedRing E)}
    (hq : q ∈ (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)).primesOver (puncturedRing E)) :
    q.ramificationIdx ℂ[X] = Uniformization.RatFuncPoly.mult (E₂ E) c := by
  classical
  set χ : ℂ[X] →ₐ[ℂ] ℂ := aeval c
  haveI : Fintype ((RingHom.ker χ).primesOver (puncturedRing E)) :=
    (Algebra.QuasiFinite.finite_primesOver (RingHom.ker χ) (S := puncturedRing E)).fintype
  have hsum := sum_ramificationIdx (B := puncturedRing E) χ
  rw [finrank_puncturedRing] at hsum
  have hcard : Fintype.card ((RingHom.ker χ).primesOver (puncturedRing E)) =
      if c ∈ E₂ E then 1 else 2 := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (ptOverEquiv χ), card_ptOver]
  have hpos : ∀ q' : (RingHom.ker χ).primesOver (puncturedRing E),
      1 ≤ q'.1.ramificationIdx ℂ[X] := fun q' ↦ by
    haveI := q'.2.1
    exact Ideal.ramificationIdx_pos _ _
  set q₀ : (RingHom.ker χ).primesOver (puncturedRing E) := ⟨q, hq⟩
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ q₀)] at hsum
  have hrest : (Finset.univ.erase q₀).card ≤
      ∑ q' ∈ Finset.univ.erase q₀, q'.1.ramificationIdx ℂ[X] := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun q' _ ↦ hpos q'
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, hcard] at hrest
  have h0 := hpos q₀
  change q₀.1.ramificationIdx ℂ[X] = _
  simp only [Uniformization.RatFuncPoly.mult]
  by_cases hc : c ∈ E₂ E
  · have hempty : Finset.univ.erase q₀ = ∅ := by
      rw [← Finset.card_eq_zero, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        hcard, if_pos hc]
    rw [hempty, Finset.sum_empty] at hsum
    rw [if_pos hc]
    omega
  · rw [if_neg hc] at hrest ⊢
    omega

/-- The maximal ideals of `ℂ[X]` are the kernels of evaluations. -/
theorem exists_eq_ker_aeval (v : Ideal ℂ[X]) [v.IsMaximal] :
    ∃ c : ℂ, v = RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ) := by
  obtain ⟨ψ, hψ⟩ := exists_point_of_isMaximal v
  refine ⟨ψ X, ?_⟩
  rw [← hψ]
  congr 1
  exact Polynomial.algHom_ext (by simp)

theorem ker_aeval (c : ℂ) :
    RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ) = span {X - C c} := by
  rw [← ker_evalRingHom]
  rfl

/-- **The multiplicities of `hemi E`.** -/
theorem hemi_mult (c : ℂ) :
    (hemi E).mult (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)) =
      Uniformization.RatFuncPoly.mult (E₂ E) c := by
  classical
  change (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)).ramificationIdxIn (puncturedRing E) = _
  haveI : (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)).IsMaximal := ker_isMaximal _
  obtain ⟨P, hP, hPl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := puncturedRing E)
    (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ))
  have hex : ∃ P : Ideal (puncturedRing E), P.IsPrime ∧
      P.LiesOver (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)) := ⟨P, hP.isPrime, hPl⟩
  rw [Ideal.ramificationIdxIn, dif_pos hex]
  exact ramificationIdx_punctured E c ⟨hex.choose_spec.1, hex.choose_spec.2⟩

end Punctured

section Final

variable (E : WeierstrassCurve ℂ) [E.IsElliptic]

theorem toHemi_etale_aux (w : Ideal (puncturedRing E)) (hw : w.IsMaximal) :
    w.ramificationIdx ℂ[X] = (hemi E).mult (w.comap (algebraMap ℂ[X] (puncturedRing E))) := by
  haveI := hw
  have hv : (w.comap (algebraMap ℂ[X] (puncturedRing E))).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℂ[X]) w
  obtain ⟨c, hc⟩ := exists_eq_ker_aeval (w.comap (algebraMap ℂ[X] (puncturedRing E)))
  have hlies : w ∈ (RingHom.ker (aeval c : ℂ[X] →ₐ[ℂ] ℂ)).primesOver (puncturedRing E) :=
    ⟨hw.isPrime, ⟨hc.symm⟩⟩
  exact (ramificationIdx_punctured E c hlies).trans
    ((hemi_mult E c).symm.trans (congrArg (hemi E).mult hc.symm))

/-- **The quotient map `E ∖ {0} → (E ∖ {0}) / {±1}`.** -/
noncomputable def toHemi : Hom (punctured E) (hemi E) where
  f := IsScalarTower.toAlgHom ℂ ℂ[X] (puncturedRing E)
  injective := by
    intro a b h
    have h' : puncturedRingEquiv E (algebraMap ℂ[X] _ a) =
        puncturedRingEquiv E (algebraMap ℂ[X] _ b) := by
      rw [AlgEquiv.commutes, AlgEquiv.commutes]; exact h
    exact FaithfulSMul.algebraMap_injective ℂ[X] E.toAffine.CoordinateRing
      ((puncturedRingEquiv E).injective h')
  isIntegral := fun x ↦ (Algebra.IsIntegral.of_finite ℂ[X] (puncturedRing E)).isIntegral x
  etale w hw := by
    change Ideal (puncturedRing E) at w
    have halg : (IsScalarTower.toAlgHom ℂ ℂ[X] (puncturedRing E)).toRingHom.toAlgebra =
        (inferInstance : Algebra ℂ[X] (puncturedRing E)) :=
      Algebra.algebra_ext _ _ fun _ ↦ rfl
    exact (mul_one _).trans ((congrArg (fun inst ↦
      @Ideal.ramificationIdx (puncturedRing E) _ w ℂ[X] _ inst) halg).trans
        (toHemi_etale_aux E w hw))

@[simp] theorem toHemi_f_X : (toHemi E).f X = xP E := by
  change algebraMap ℂ[X] (puncturedRing E) X = puncturedRingEquiv E (Uniformization.FEt.xA E)
  rw [puncturedRingEquiv_xA]

variable {E}

theorem exc_zero (hj : ∀ c ∈ excJ, E.j ≠ (c : ℂ)) : E.j ≠ 0 := by
  simpa using hj 0 (by simp [excJ])

theorem exc_1728 (hj : ∀ c ∈ excJ, E.j ≠ (c : ℂ)) : E.j ≠ 1728 := by
  simpa using hj 1728 (by simp [excJ])

/-- **Uniqueness**: every map `Y → hemi E` sends `X` to the descended `x`. -/
theorem hom_hemi_f_X (hj : ∀ c ∈ excJ, E.j ≠ (c : ℂ)) {Y Z : AffOrbicurve ℂ}
    (φ : Hom Z (punctured E)) (ψ : Hom Z Y) (h : Hom Y (hemi E)) :
    ψ.f (h.f X) = φ.f (xP E) := by
  classical
  set χ := ψ.comp h
  obtain ⟨p, hp⟩ : ∃ p : ℂ[X], χ.f p = φ.f (xP E) := theoremG E hj φ χ
  have hg : χ.f.comp (aeval p : ℂ[X] →ₐ[ℂ] ℂ[X]) = (φ.comp (toHemi E)).f := by
    refine Polynomial.algHom_ext ?_
    change χ.f (aeval (R := ℂ) p X) = φ.f ((toHemi E).f X)
    rw [aeval_X, toHemi_f_X]
    exact hp
  set H := Hom.descend χ (φ.comp (toHemi E)) (aeval p) hg
  have hdeg : 0 < p.natDegree := by
    by_contra h0
    push Not at h0
    have hpC : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero h0
    have := H.injective (a₁ := X - C (p.coeff 0)) (a₂ := 0) (by
      change aeval (R := ℂ) p (X - C (p.coeff 0)) = aeval (R := ℂ) p 0
      rw [map_sub, aeval_X, aeval_C, map_zero, algebraMap_eq, ← hpC, sub_self])
    exact X_sub_C_ne_zero _ this
  have hcond : ∀ w : ℂ, Uniformization.RatFuncPoly.ramIdx p w *
      Uniformization.RatFuncPoly.mult (E₂ E) w =
        Uniformization.RatFuncPoly.mult (E₂ E) (p.eval w) := by
    intro w
    have h1 := H.etale (RingHom.ker (aeval w : ℂ[X] →ₐ[ℂ] ℂ)) (ker_isMaximal _)
    rw [← hemi_mult E w, ← hemi_mult E (p.eval w), ← ramificationIdx_aeval hdeg w,
      ← ker_aeval]
    refine h1.trans ?_
    congr 1
    change (RingHom.ker (aeval w : ℂ[X] →ₐ[ℂ] ℂ)).comap (aeval (R := ℂ) p).toRingHom = _
    rw [ker_aeval]
    exact (comap_aeval_span p w).trans (ker_aeval _).symm
  rcases hemi_poly_unique hdeg hcond with hX | h0 | h1728
  · have : χ.f p = ψ.f (h.f X) := by rw [hX]; rfl
    rw [← this, hp]
  · exact absurd h0 (exc_zero hj)
  · exact absurd h1728 (exc_1728 hj)

/-- **[CanLift] Prop. 2.7 over `ℂ`.** -/
theorem canLift27C : CanLift27C := by
  intro E _ hj
  refine ⟨⟨punctured E, ⟨Hom.id _⟩, ⟨toHemi E⟩⟩, fun Y hY ↦ ?_⟩
  obtain ⟨Z, ⟨φ⟩, ⟨ψ⟩⟩ := hY
  obtain ⟨y, hy⟩ := theoremG E hj φ ψ
  have hg : ψ.f.comp (aeval y : ℂ[X] →ₐ[ℂ] Y.A) = (φ.comp (toHemi E)).f := by
    refine Polynomial.algHom_ext ?_
    change ψ.f (aeval (R := ℂ) y X) = φ.f ((toHemi E).f X)
    rw [aeval_X, toHemi_f_X]
    exact hy
  refine ⟨⟨Hom.descend ψ (φ.comp (toHemi E)) (aeval y) hg⟩, ⟨fun h₁ h₂ ↦ Hom.ext ?_⟩⟩
  refine Polynomial.algHom_ext (ψ.injective ?_)
  exact (hom_hemi_f_X hj φ ψ h₁).trans (hom_hemi_f_X hj φ ψ h₂).symm

end Final

end OrbicurveCores.U2
