/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Rigid.Lift

/-!
# U2c8–U2c9: the deck group of `u = x ∘ π` and the analytic rigidity theorem

Let `π : ℍ → E(ℂ) ∖ 0` uniformise with group `Γ = ⟨A, B⟩` and `u = x ∘ π`. Fix a signature
`e : ℂ → ℕ` (in the application, the stabiliser orders of `(E ∖ 0)/±1`) such that `u` has local
normal forms of order `e (u z)`.

* `deck π`: the group `D` of `δ ∈ SL(2, ℝ)` with `u ∘ δ = u`; it contains `Γ`;
* `relIndex_ne_zero_of_orbits`: a counting criterion for finite index;
* `eq_u_of_orbCover` (**U2c9**): if `[Comm(Γ) : Γ] = 4`, then every holomorphic `F` on `ℍ`
  invariant under a finite-index `Γ' ≤ Γ`, proper modulo `Γ'`, with local normal forms of order
  `e (F z)`, equals `u`. Proof: `F` and `u` are orbifold coverings with the same signature, so
  `F = u ∘ m` for a Möbius `m` (`exists_mobius_of_orbCover`); `m Γ' m⁻¹ ≤ D`, and `D` contains
  `Γ` and `m Γ' m⁻¹` with finite index, so `m ∈ Comm(Γ)`; finally `Comm(Γ) = D`, since
  `D ≤ Comm(Γ)` and `[D : Γ] ≥ 4` (`D ∋ -1, g₀` with `π ∘ g₀ = [-1] ∘ π`).
-/

open Complex Metric Set Filter Function UpperHalfPlane
open scoped MatrixGroups Topology Pointwise
open OrbicurveCores.S1 (upper HasLocalForm IsOrbCover)
open Subgroup.Commensurable (commensurator)

namespace OrbicurveCores.Rigid

/-! ### Finite index from finitely many orbits -/

lemma neg_one_smul_H (z : ℍ) : (-1 : SL(2, ℝ)) • z = z := S1.neg_smul_H 1 z |>.trans (one_smul _ _)

/-- **Finite index from orbits.** If `H ≤ K ≤ SL(2, ℝ)`, `-1 ∈ K`, `-1 ∉ H`, the stabiliser of
`z₀` in `K` is `±1`, and `K z₀` lies in finitely many `H`-orbits, then `[K : H] < ∞`. -/
lemma relIndex_ne_zero_of_orbits {H K : Subgroup SL(2, ℝ)} (hHK : H ≤ K) (hK : -1 ∈ K)
    (hH : (-1 : SL(2, ℝ)) ∉ H) {z₀ : ℍ} (hstab : ∀ k ∈ K, k • z₀ = z₀ → k = 1 ∨ k = -1)
    (P : Finset ℍ) (hP : ∀ k ∈ K, ∃ p ∈ P, ∃ h ∈ H, k • z₀ = h • p) : H.relIndex K ≠ 0 := by
  classical
  set Hp := Fuchsian.pmGroup H
  have hHp : Hp ≤ K := by
    rintro g (hg | hg)
    · exact hHK hg
    · have := mul_mem hK (hHK hg); simpa using this
  have h1 : H.relIndex Hp ≠ 0 := by
    rw [Fuchsian.relIndex_pmGroup_eq_two hH]; exact two_ne_zero
  refine Subgroup.relIndex_ne_zero_trans h1 ?_
  -- `K / ±H` injects into the `H`-orbits of the points of `P`
  have hpm : ∀ s ∈ Hp, ∀ x : ℍ, ∃ h ∈ H, s • x = h • x := by
    rintro s (hs | hs) x
    · exact ⟨s, hs, rfl⟩
    · refine ⟨-s, hs, ?_⟩
      have := S1.neg_smul_H (-s) x
      rwa [neg_neg] at this
  set Φ : K → MulAction.orbitRel.Quotient H ℍ := fun k ↦ ⟦(k : SL(2, ℝ))⁻¹ • z₀⟧
  have hΦ : ∀ k k' : K, (k : SL(2, ℝ))⁻¹ * k' ∈ Hp → Φ k = Φ k' := by
    intro k k' hkk
    obtain ⟨h, hh, hh'⟩ := hpm _ (inv_mem hkk) ((k : SL(2, ℝ))⁻¹ • z₀)
    have hk' : (k' : SL(2, ℝ))⁻¹ • z₀ = h • (k : SL(2, ℝ))⁻¹ • z₀ := by
      rw [← hh', smul_smul]; congr 1; group
    refine Quotient.sound (?_ : (k : SL(2, ℝ))⁻¹ • z₀ ∈ MulAction.orbit H _)
    refine ⟨⟨h⁻¹, inv_mem hh⟩, ?_⟩
    change h⁻¹ • (k' : SL(2, ℝ))⁻¹ • z₀ = _
    rw [hk', inv_smul_smul]
  set Ψ : K ⧸ Hp.subgroupOf K → MulAction.orbitRel.Quotient H ℍ :=
    Quotient.lift Φ fun k k' hkk ↦ hΦ k k'
      (Subgroup.mem_subgroupOf.mp (QuotientGroup.leftRel_apply.mp hkk))
  have hΨinj : Injective Ψ := by
    intro c c'
    induction c using QuotientGroup.induction_on with | H k => ?_
    induction c' using QuotientGroup.induction_on with | H k' => ?_
    intro hkk
    change Φ k = Φ k' at hkk
    obtain ⟨⟨h, hh⟩, hhk⟩ := Quotient.exact hkk
    change h • (k' : SL(2, ℝ))⁻¹ • z₀ = (k : SL(2, ℝ))⁻¹ • z₀ at hhk
    have hfix : ((k : SL(2, ℝ)) * h * (k' : SL(2, ℝ))⁻¹) • z₀ = z₀ := by
      rw [mul_smul, mul_smul, hhk, smul_inv_smul]
    have hmem : (k : SL(2, ℝ)) * h * (k' : SL(2, ℝ))⁻¹ ∈ K :=
      mul_mem (mul_mem k.2 (hHK hh)) (inv_mem k'.2)
    refine QuotientGroup.eq.mpr ?_
    change (k : SL(2, ℝ))⁻¹ * k' ∈ Hp
    rcases hstab _ hmem hfix with h1 | h1
    · have : (k : SL(2, ℝ))⁻¹ * k' = h := by
        rw [mul_inv_eq_one] at h1
        rw [← h1]; group
      rw [this]; exact Or.inl hh
    · have : (k : SL(2, ℝ))⁻¹ * k' = -h := by
        have h2 : (k : SL(2, ℝ)) * h = -k' := by
          rw [mul_inv_eq_iff_eq_mul, neg_one_mul] at h1; exact h1
        rw [show (k' : SL(2, ℝ)) = -((k : SL(2, ℝ)) * h) by rw [h2, neg_neg], mul_neg,
          inv_mul_cancel_left]
      rw [this]; exact Or.inr (by simpa using hh)
  have hrange : ∀ c, Ψ c ∈ P.image (fun p ↦ (⟦p⟧ : MulAction.orbitRel.Quotient H ℍ)) := by
    intro c
    induction c using QuotientGroup.induction_on with | H k => ?_
    obtain ⟨p, hp, h, hh, hkp⟩ := hP _ (inv_mem k.2)
    refine Finset.mem_image.mpr ⟨p, hp, Quotient.sound
      (?_ : p ∈ MulAction.orbit H ((k : SL(2, ℝ))⁻¹ • z₀))⟩
    refine ⟨⟨h⁻¹, inv_mem hh⟩, ?_⟩
    change h⁻¹ • _ = p
    rw [hkp, inv_smul_smul]
  haveI : Finite (K ⧸ Hp.subgroupOf K) :=
    Finite.of_injective (fun c ↦ (⟨Ψ c, hrange c⟩ : ↥(P.image _)))
      fun c c' h ↦ hΨinj (congrArg Subtype.val h)
  exact Subgroup.index_ne_zero_of_finite

/-! ### The deck group of `u = x ∘ π` -/

variable {E : WeierstrassCurve ℂ} {A B : SL(2, ℝ)} {π : ℂ → ℂ × ℂ}

/-- The deck group `D = {δ | u ∘ δ = u}` of `u = x ∘ π`. -/
def deck (π : ℂ → ℂ × ℂ) : Subgroup SL(2, ℝ) where
  carrier := {δ | ∀ y ∈ upper, (π (mob δ y)).1 = (π y).1}
  one_mem' := fun y hy ↦ by rw [mob_one hy]
  mul_mem' := fun {a b} ha hb y hy ↦ by rw [mob_mul, ha _ (mob_mem _ _), hb y hy]
  inv_mem' := fun {a} ha y hy ↦ by rw [← ha _ (mob_mem _ _), mob_mob_inv _ hy]

lemma mem_deck {δ : SL(2, ℝ)} : δ ∈ deck π ↔ ∀ y ∈ upper, (π (mob δ y)).1 = (π y).1 := Iff.rfl

lemma neg_one_mem_deck : (-1 : SL(2, ℝ)) ∈ deck π := fun y hy ↦ by
  rw [mob, neg_one_smul_H, ofComplex_apply_of_im_pos hy]

lemma UnifProps.mob_eq (hπ : UnifProps E A B π) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) {y : ℂ} (hy : y ∈ upper) : π (mob γ y) = π y := by
  have := (hπ.fib ⟨y, hy⟩ (γ • ⟨y, hy⟩)).mpr ⟨γ, hγ, rfl⟩
  rw [mob, ofComplex_apply_of_im_pos hy]
  exact this.symm

lemma UnifProps.le_deck (hπ : UnifProps E A B π) : Subgroup.closure {A, B} ≤ deck π :=
  fun γ hγ y hy ↦ by rw [hπ.mob_eq hγ hy]

/-- On the curve, `|y|` is bounded in terms of `|x|`. -/
lemma UnifProps.exists_norm_le (hπ : UnifProps E A B π) (R : ℝ) :
    ∃ R' : ℝ, ∀ z : ℍ, ‖(π z).1‖ ≤ R → ‖π z‖ ≤ R' := by
  refine ⟨R + 1 + (‖E.a₁‖ * R + ‖E.a₃‖) + (R ^ 3 + ‖E.a₂‖ * R ^ 2 + ‖E.a₄‖ * R + ‖E.a₆‖),
    fun z hz ↦ ?_⟩
  set x := (π z).1
  set y := (π z).2
  have heq := hπ.eqn z
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hc : ‖x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆‖ ≤
      R ^ 3 + ‖E.a₂‖ * R ^ 2 + ‖E.a₄‖ * R + ‖E.a₆‖ := by
    refine (norm_add_le _ _).trans (add_le_add_left ((norm_add_le _ _).trans
      (add_le_add_left (norm_add_le _ _) _)) _) |>.trans ?_
    simp only [norm_pow, norm_mul]
    gcongr
  have hb : ‖E.a₁ * x + E.a₃‖ ≤ ‖E.a₁‖ * R + ‖E.a₃‖ :=
    (norm_add_le _ _).trans (by rw [norm_mul]; gcongr)
  have hy : ‖y‖ ≤ 1 + (‖E.a₁‖ * R + ‖E.a₃‖) +
      (R ^ 3 + ‖E.a₂‖ * R ^ 2 + ‖E.a₄‖ * R + ‖E.a₆‖) := by
    by_cases h1 : ‖y‖ ≤ 1
    · have := norm_nonneg (E.a₁ * x + E.a₃)
      have := norm_nonneg (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
      linarith
    · push Not at h1
      have hy2 : y * y = (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆) - (E.a₁ * x + E.a₃) * y := by
        linear_combination heq
      have h2 : ‖y‖ * ‖y‖ ≤ ‖x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆‖ +
          ‖E.a₁ * x + E.a₃‖ * ‖y‖ := by
        rw [← norm_mul, hy2]
        exact (norm_sub_le _ _).trans (by rw [norm_mul])
      have h3 : ‖y‖ ≤ ‖x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆‖ + ‖E.a₁ * x + E.a₃‖ := by
        by_contra h
        push Not at h
        have := mul_lt_mul_of_pos_right h (by linarith : (0 : ℝ) < ‖y‖)
        nlinarith [norm_nonneg (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)]
      linarith
  have h0 := norm_nonneg (E.a₁ * x + E.a₃)
  have h0' := norm_nonneg (x ^ 3 + E.a₂ * x ^ 2 + E.a₄ * x + E.a₆)
  rw [show π z = (x, y) from rfl, Prod.norm_def]
  exact max_le (by linarith) (by linarith)

/-- Properness modulo `Γ` passes to finite-index subgroups. -/
lemma exists_isCompact_of_relIndex {Γ Γ' : Subgroup SL(2, ℝ)} (hfi : Γ'.relIndex Γ ≠ 0)
    {P : ℍ → Prop} {C : Set ℍ} (hC : IsCompact C) (hP : ∀ z, P z → ∃ γ ∈ Γ, γ • z ∈ C) :
    ∃ C' : Set ℍ, IsCompact C' ∧ ∀ z, P z → ∃ γ ∈ Γ', γ • z ∈ C' := by
  haveI : (Γ'.subgroupOf Γ).FiniteIndex := ⟨hfi⟩
  set C' := ⋃ q : Γ ⧸ Γ'.subgroupOf Γ, (fun z ↦ ((q.out : Γ) : SL(2, ℝ))⁻¹ • z) '' C
  refine ⟨C', isCompact_iUnion fun q ↦ hC.image (continuous_smul_H _), fun z hz ↦ ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hP z hz
  set q : Γ ⧸ Γ'.subgroupOf Γ := QuotientGroup.mk ⟨γ, hγ⟩
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (Γ'.subgroupOf Γ) (⟨γ, hγ⟩ : Γ)
  have hh' : ((h : Γ) : SL(2, ℝ)) ∈ Γ' := h.2
  refine ⟨((h : Γ) : SL(2, ℝ))⁻¹, inv_mem hh', mem_iUnion.mpr ⟨q, γ • z, hγC, ?_⟩⟩
  change ((q.out : Γ) : SL(2, ℝ))⁻¹ • γ • z = _
  rw [hh]
  simp only [Subgroup.coe_mul, mul_inv_rev, smul_smul, inv_mul_cancel_right]

/-- The fibres of a proper function with local normal forms are finite modulo the group. -/
lemma exists_finset_fibre {F : ℂ → ℂ} (hF : ContinuousOn F upper) {e : ℂ → ℕ}
    (he : ∀ w, 0 < e w) (hloc : ∀ z ∈ upper, HasLocalForm F z (e (F z)))
    {Γ' : Subgroup SL(2, ℝ)} (hinv : ∀ γ ∈ Γ', ∀ y ∈ upper, F (mob γ y) = F y)
    (hprop : ∀ R : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖F z‖ ≤ R → ∃ γ ∈ Γ', γ • z ∈ C)
    (t : ℂ) : ∃ P : Finset ℍ, ∀ y : ℍ, F y = t → ∃ p ∈ P, ∃ γ ∈ Γ', γ • p = y := by
  have hFc : Continuous fun c : ℍ ↦ F c :=
    hF.comp_continuous UpperHalfPlane.continuous_coe fun c ↦ c.im_pos
  obtain ⟨C, hC, hCp⟩ := hprop ‖t‖
  set S : Set ℍ := {c | c ∈ C ∧ F c = t}
  have hSc : IsCompact S := hC.inter_right (isClosed_eq hFc continuous_const)
  have hSd : IsDiscrete S := by
    rw [isDiscrete_iff_forall_mem_exists_isOpen]
    rintro c ⟨hcC, hcw⟩
    have h1 := ne_eventually_of_hasLocalForm (he _) (hloc c c.im_pos)
    rw [hcw, eventually_nhdsWithin_iff] at h1
    obtain ⟨U, hU, hUo, hcU⟩ := _root_.eventually_nhds_iff.mp h1
    refine ⟨((↑) : ℍ → ℂ) ⁻¹' U, hUo.preimage UpperHalfPlane.continuous_coe, ?_⟩
    ext c'
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, S, mem_setOf_eq]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨h1, -, h3⟩ := h
      by_contra hne
      exact hU _ h1 (fun h ↦ hne (UpperHalfPlane.ext h)) h3
    · subst h; exact ⟨hcU, hcC, hcw⟩
  have hSf : S.Finite := hSc.finite hSd
  refine ⟨hSf.toFinset, fun y hy ↦ ?_⟩
  obtain ⟨γ, hγ, hγC⟩ := hCp y (by rw [hy])
  have hF1 : F ((γ • y : ℍ) : ℂ) = t := by rw [← mob_coe, hinv γ hγ y y.im_pos, hy]
  exact ⟨γ • y, hSf.mem_toFinset.mpr ⟨hγC, hF1⟩, γ⁻¹, inv_mem hγ, inv_smul_smul _ _⟩

/-- At a point where `u` has nonzero derivative, the stabiliser in `D` is `±1`. -/
lemma UnifProps.stab_deck (hπ : UnifProps E A B π) {z₀ : ℍ}
    (hd : deriv (fun y ↦ (π y).1) z₀ ≠ 0) {δ : SL(2, ℝ)} (hδ : δ ∈ deck π) (hfix : δ • z₀ = z₀) :
    δ = 1 ∨ δ = -1 := by
  have hud : DifferentiableOn ℂ (fun y ↦ (π y).1) upper := fun y hy ↦
    ((hπ.diff ⟨y, hy⟩).1.fst).differentiableWithinAt
  have hm : mob δ z₀ = z₀ := by rw [mob_coe, hfix]
  have h := eqOn_of_lift (p := fun y ↦ (π y).1) (differentiableOn_mob δ) differentiableOn_id
    (fun y hy ↦ hδ y hy) z₀.im_pos hm (by rw [hm]; exact hπ.analyticAt_fst z₀) (by rwa [hm])
  refine eq_one_or_neg_one_of_eqOn isOpen_univ ⟨z₀, trivial⟩ fun w _ ↦ ?_
  apply UpperHalfPlane.ext
  rw [← mob_coe]
  exact h w.im_pos

/-- **U2c8–U2c9. Analytic rigidity.** If `[Comm(Γ) : Γ] = 4`, every holomorphic function on `ℍ`
which is invariant under a finite-index subgroup of `Γ`, proper modulo it, and has local normal
forms of the signature of `u = x ∘ π`, is `u`. -/
theorem UnifProps.eq_u_of [E.IsElliptic] (hπ : UnifProps E A B π)
    (hcomm : tr (A * B * A⁻¹ * B⁻¹) = -2) (hA : tr A ≠ 0)
    (hidx : (Subgroup.closure {A, B}).relIndex (commensurator (Subgroup.closure {A, B})) = 4)
    {e : ℂ → ℕ} (he : ∀ w, 0 < e w) (hfin : {w | e w ≠ 1}.Finite)
    (hlocU : ∀ z ∈ upper, HasLocalForm (fun y ↦ (π y).1) z (e (π z).1))
    {Γ' : Subgroup SL(2, ℝ)} (hΓ' : Γ' ≤ Subgroup.closure {A, B})
    (hfi : Γ'.relIndex (Subgroup.closure {A, B}) ≠ 0) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F upper) (hinv : ∀ γ ∈ Γ', ∀ y ∈ upper, F (mob γ y) = F y)
    (hloc : ∀ z ∈ upper, HasLocalForm F z (e (F z)))
    (hprop : ∀ R : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖F z‖ ≤ R → ∃ γ ∈ Γ', γ • z ∈ C) :
    ∀ y ∈ upper, F y = (π y).1 := by
  set Γ := Subgroup.closure {A, B}
  set u : ℂ → ℂ := fun y ↦ (π y).1
  set D := deck π
  have hud : DifferentiableOn ℂ u upper := fun y hy ↦
    ((hπ.diff ⟨y, hy⟩).1.fst).differentiableWithinAt
  have huinv : ∀ γ ∈ Γ, ∀ y ∈ upper, u (mob γ y) = u y := fun γ hγ y hy ↦ hπ.le_deck hγ y hy
  have huprop : ∀ R : ℝ, ∃ C : Set ℍ, IsCompact C ∧ ∀ z : ℍ, ‖u z‖ ≤ R →
      ∃ γ ∈ Γ, γ • z ∈ C := fun R ↦ by
    obtain ⟨R', hR'⟩ := hπ.exists_norm_le R
    obtain ⟨C, hC, hCp⟩ := hπ.exists_isCompact R'
    exact ⟨C, hC, fun z hz ↦ hCp z (hR' z hz)⟩
  have hOCu := hπ.isOrbCover_of hcomm hA le_rfl hud he huinv hlocU huprop
  have hOCF := hπ.isOrbCover_of hcomm hA hΓ' hF he hinv hloc hprop
  -- a generic value `t₀`
  obtain ⟨t₀, ht₀⟩ := hfin.infinite_compl.nonempty
  have he₀ : e t₀ = 1 := not_not.mp ht₀
  obtain ⟨z₀, hz₀, hz₀t⟩ := (hOCu t₀).1
  obtain ⟨w₀, hw₀, hw₀t⟩ := (hOCF t₀).1
  have hdu : deriv u z₀ ≠ 0 := by
    have := hlocU z₀ hz₀
    change HasLocalForm u z₀ (e (u z₀)) at this
    rw [hz₀t, he₀] at this
    exact deriv_ne_zero_of_hasLocalForm_one this
  set Z₀ : ℍ := ⟨z₀, hz₀⟩
  -- `F = u ∘ m`
  obtain ⟨m, hm, -⟩ := exists_mobius_of_orbCover he hOCF hOCu hud hloc hlocU hw₀ hz₀
    (hz₀t.trans hw₀t.symm) (by rw [hw₀t, he₀])
  -- finite index of `Γ` in `D`
  have hstab : ∀ k ∈ D, k • Z₀ = Z₀ → k = 1 ∨ k = -1 := fun k hk hfix ↦
    hπ.stab_deck hdu hk hfix
  obtain ⟨Pu, hPu⟩ := exists_finset_fibre hud.continuousOn he hlocU huinv huprop t₀
  have hΓD : Γ.relIndex D ≠ 0 := by
    refine relIndex_ne_zero_of_orbits hπ.le_deck neg_one_mem_deck
      (neg_one_notMem_closure hcomm hA) hstab Pu fun k hk ↦ ?_
    have hk' : u ((k • Z₀ : ℍ) : ℂ) = t₀ := by rw [← mob_coe]; exact (hk z₀ hz₀).trans hz₀t
    obtain ⟨p, hp, γ, hγ, hγp⟩ := hPu (k • Z₀) hk'
    exact ⟨p, hp, γ, hγ, hγp.symm⟩
  -- `H₂ = m Γ' m⁻¹ ≤ D` with finite index
  set H₂ := ConjAct.toConjAct m • Γ'
  have hmemH₂ : ∀ g, g ∈ H₂ ↔ m⁻¹ * g * m ∈ Γ' := fun g ↦ by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv,
      ConjAct.toConjAct_smul, inv_inv]
  have hH₂D : H₂ ≤ D := by
    intro g hg y hy
    rw [hmemH₂] at hg
    have h1 : g = m * (m⁻¹ * g * m) * m⁻¹ := by group
    change u (mob g y) = u y
    rw [h1, mob_mul, mob_mul, hm _ (mob_mem _ _), hinv _ hg _ (mob_mem _ _), ← hm _ (mob_mem _ _),
      mob_mob_inv _ hy]
  have hnegH₂ : (-1 : SL(2, ℝ)) ∉ H₂ := by
    rw [hmemH₂]
    intro h
    have : m⁻¹ * -1 * m = -1 := by simp
    rw [this] at h
    exact neg_one_notMem_closure hcomm hA (hΓ' h)
  obtain ⟨PF, hPF⟩ := exists_finset_fibre hF.continuousOn he hloc hinv hprop t₀
  have hH₂Dfin : H₂.relIndex D ≠ 0 := by
    classical
    refine relIndex_ne_zero_of_orbits hH₂D neg_one_mem_deck hnegH₂ hstab
      (PF.image fun p ↦ m • p) fun k hk ↦ ?_
    have hk' : F (((m⁻¹ * k) • Z₀ : ℍ) : ℂ) = t₀ := by
      rw [← mob_coe, ← hm _ (mob_mem _ _), ← mob_mul, mul_inv_cancel_left]
      exact (hk z₀ hz₀).trans hz₀t
    obtain ⟨p, hp, γ, hγ, hγp⟩ := hPF _ hk'
    refine ⟨m • p, Finset.mem_image.mpr ⟨p, hp, rfl⟩, m * γ * m⁻¹,
      (hmemH₂ _).mpr (by simpa [mul_assoc] using hγ), ?_⟩
    rw [smul_smul, show m * γ * m⁻¹ * m = m * γ by group, mul_smul, hγp, smul_smul,
      mul_inv_cancel_left]
  -- commensurabilities
  have cΓD : Γ.Commensurable D := ⟨hΓD, by rw [Subgroup.relIndex_eq_one.mpr hπ.le_deck]; simp⟩
  have cH₂D : H₂.Commensurable D := ⟨hH₂Dfin, by rw [Subgroup.relIndex_eq_one.mpr hH₂D]; simp⟩
  have cΓ'Γ : Γ'.Commensurable Γ := ⟨hfi, by rw [Subgroup.relIndex_eq_one.mpr hΓ']; simp⟩
  have hmC : m ∈ commensurator Γ := by
    rw [Subgroup.Commensurable.commensurator_mem_iff]
    exact (cΓ'Γ.conj (ConjAct.toConjAct m)).symm.trans (cH₂D.trans cΓD.symm)
  -- `D ≤ Comm(Γ)`
  have hDC : D ≤ commensurator Γ := by
    intro δ hδ
    rw [Subgroup.Commensurable.commensurator_mem_iff]
    have h1 := cΓD.conj (ConjAct.toConjAct δ)
    rw [Subgroup.conjAct_pointwise_smul_eq_self (Subgroup.le_normalizer hδ)] at h1
    exact h1.trans cΓD.symm
  -- `[D : Γ] ≥ 4`: the elliptic involution
  obtain ⟨w₁, hw₁⟩ := hπ.surj (π z₀).1 (E.toAffine.negY (π z₀).1 (π z₀).2)
    ((E.toAffine.equation_neg _ _).mpr (hπ.eqn Z₀))
  obtain ⟨m₀, hm₀, hm₀z⟩ := exists_mobius_of_orbCover he hOCu hOCu hud hlocU hlocU hz₀ w₁.im_pos
    (by change (π w₁).1 = (π z₀).1; rw [hw₁]) (by rw [hz₀t, he₀])
  have hm₀D : m₀ ∈ D := hm₀
  have hm₀Γ : m₀ ∉ Fuchsian.pmGroup Γ := by
    intro h
    have hπeq : π (mob m₀ z₀) = π z₀ := by
      rcases h with h | h
      · exact hπ.mob_eq h hz₀
      · have := hπ.mob_eq h hz₀
        rwa [mob, S1.neg_smul_H, ← mob] at this
    rw [hm₀z, hw₁] at hπeq
    have hy : (2 * (π z₀).2 + E.a₁ * (π z₀).1 + E.a₃) = 0 := by
      have := congrArg Prod.snd hπeq
      change -(π z₀).2 - E.a₁ * (π z₀).1 - E.a₃ = (π z₀).2 at this
      linear_combination -this
    have hrel := hπ.deriv_relation Z₀
    have hns := (WeierstrassCurve.Affine.equation_iff_nonsingular (W := E.toAffine)).mp
      (hπ.eqn Z₀)
    rw [WeierstrassCurve.Affine.nonsingular_iff'] at hns
    change (2 * (π z₀).2 + E.a₁ * (π z₀).1 + E.a₃) * _ +
      (E.a₁ * (π z₀).2 - (3 * (π z₀).1 ^ 2 + 2 * E.a₂ * (π z₀).1 + E.a₄)) * deriv u z₀ = 0
      at hrel
    rw [hy, zero_mul, zero_add, mul_eq_zero] at hrel
    rcases hns.2 with h1 | h1
    · exact hdu (hrel.resolve_left h1)
    · exact h1 hy
  have hΓpm : Γ.relIndex (Fuchsian.pmGroup Γ) = 2 :=
    Fuchsian.relIndex_pmGroup_eq_two (neg_one_notMem_closure hcomm hA)
  have hpmD : Fuchsian.pmGroup Γ ≤ D := by
    rintro g (hg | hg)
    · exact hπ.le_deck hg
    · have := mul_mem neg_one_mem_deck (hπ.le_deck hg); simpa using this
  have hpmDidx : (Fuchsian.pmGroup Γ).relIndex D ≠ 0 :=
    fun h ↦ hΓD (by rw [← Subgroup.relIndex_mul_relIndex _ _ _ (Fuchsian.le_pmGroup Γ) hpmD, h,
      mul_zero])
  have hpmD1 : (Fuchsian.pmGroup Γ).relIndex D ≠ 1 := fun h ↦
    hm₀Γ (Subgroup.relIndex_eq_one.mp h hm₀D)
  have hΓD4 : 4 ≤ Γ.relIndex D := by
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ (Fuchsian.le_pmGroup Γ) hpmD, hΓpm]
    omega
  -- `Comm(Γ) = D`
  have hCD : commensurator Γ ≤ D := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ hπ.le_deck hDC
    rw [hidx] at h
    have h1 : D.relIndex (commensurator Γ) = 1 := by
      rcases Nat.lt_or_ge (D.relIndex (commensurator Γ)) 2 with h2 | h2
      · interval_cases hc : D.relIndex (commensurator Γ)
        · rw [mul_zero] at h; exact absurd h (by norm_num)
        · rfl
      · nlinarith
    exact Subgroup.relIndex_eq_one.mp h1
  -- conclusion
  intro y hy
  rw [← hm y hy]
  exact hCD hmC y hy

end OrbicurveCores.Rigid
