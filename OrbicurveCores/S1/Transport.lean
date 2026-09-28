/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Defs
import OrbicurveCores.Classification

/-!
# Transporting uniformisations

`Uniformizes W A B` depends only on the orbits of `⟨A, B⟩` on `ℍ`. So it is invariant under
Nielsen moves (`Uniformizes.of_closure_eq`) and under signs of the generators
(`Uniformizes.of_signs`). Conjugation by `g ∈ GL(2, ℝ)` transports it to the conjugate pair:
for `det g > 0` on the same curve (`Uniformizes.conj_pos`), and for `det g < 0` on the
complex-conjugate curve `W.map conj` (`Uniformizes.conj_neg`).

Consequently a curve uniformised by a Takeuchi group is uniformised, possibly after complex
conjugation, by one of the four explicit pairs `takeuchiPair i` (`Uniformizes.exists_takeuchiPair`).
-/

open Complex Metric Set Filter Topology Matrix Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ComplexConjugate

namespace OrbicurveCores.S1

variable {W : WeierstrassCurve ℂ}

lemma Uniformizes.of_orbits {A B A₁ B₁ : SL(2, ℝ)} (hU : Uniformizes W A B)
    (h : ∀ z w : ℍ, (∃ γ ∈ Subgroup.closure {A, B}, γ • z = w) ↔
      ∃ γ ∈ Subgroup.closure {A₁, B₁}, γ • z = w) : Uniformizes W A₁ B₁ := by
  obtain ⟨π, h1, h2, h3, h4⟩ := hU
  exact ⟨π, h1, h2, h3, fun z w ↦ (h4 z w).trans (h z w)⟩

lemma Uniformizes.of_closure_eq {A B A₁ B₁ : SL(2, ℝ)} (hU : Uniformizes W A B)
    (h : Subgroup.closure {A₁, B₁} = Subgroup.closure {A, B}) : Uniformizes W A₁ B₁ :=
  Uniformizes.of_orbits hU fun z w ↦ by rw [h]

lemma neg_smul_H (γ : SL(2, ℝ)) (z : ℍ) : (-γ) • z = γ • z := by
  rw [show -γ = (-1) * γ by simp, mul_smul, Uniformization.Generators.neg_one_smul']

lemma exists_sign_orbit {A B A₁ B₁ : SL(2, ℝ)} (hA : A₁ = A ∨ A₁ = -A) (hB : B₁ = B ∨ B₁ = -B)
    {γ : SL(2, ℝ)} (hγ : γ ∈ Subgroup.closure {A, B}) :
    ∃ γ₁ ∈ Subgroup.closure {A₁, B₁}, ∀ z : ℍ, γ₁ • z = γ • z := by
  induction hγ using Subgroup.closure_induction with
  | mem g hg =>
    simp only [mem_insert_iff, mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · refine ⟨A₁, Subgroup.subset_closure (by simp), fun z ↦ ?_⟩
      rcases hA with rfl | rfl
      · rfl
      · exact neg_smul_H _ z
    · refine ⟨B₁, Subgroup.subset_closure (by simp), fun z ↦ ?_⟩
      rcases hB with rfl | rfl
      · rfl
      · exact neg_smul_H _ z
  | one => exact ⟨1, one_mem _, fun z ↦ rfl⟩
  | mul g₁ g₂ _ _ ih₁ ih₂ =>
    obtain ⟨h₁, hh₁, e₁⟩ := ih₁
    obtain ⟨h₂, hh₂, e₂⟩ := ih₂
    exact ⟨h₁ * h₂, mul_mem hh₁ hh₂, fun z ↦ by rw [mul_smul, mul_smul, e₂, e₁]⟩
  | inv g _ ih =>
    obtain ⟨h, hh, e⟩ := ih
    refine ⟨h⁻¹, inv_mem hh, fun z ↦ ?_⟩
    have := e (g⁻¹ • z)
    rw [smul_inv_smul] at this
    rw [inv_smul_eq_iff, this]

lemma Uniformizes.of_signs {A B A₁ B₁ : SL(2, ℝ)} (hU : Uniformizes W A B)
    (hA : A₁ ∈ ({A, -A} : Set SL(2, ℝ))) (hB : B₁ ∈ ({B, -B} : Set SL(2, ℝ))) :
    Uniformizes W A₁ B₁ := by
  have hA' : A₁ = A ∨ A₁ = -A := hA
  have hB' : B₁ = B ∨ B₁ = -B := hB
  have hA'' : A = A₁ ∨ A = -A₁ := by rcases hA' with rfl | rfl <;> simp
  have hB'' : B = B₁ ∨ B = -B₁ := by rcases hB' with rfl | rfl <;> simp
  refine Uniformizes.of_orbits hU fun z w ↦ ⟨fun ⟨γ, hγ, e⟩ ↦ ?_, fun ⟨γ, hγ, e⟩ ↦ ?_⟩
  · obtain ⟨γ₁, h₁, e₁⟩ := exists_sign_orbit hA' hB' hγ
    exact ⟨γ₁, h₁, by rw [e₁, e]⟩
  · obtain ⟨γ₁, h₁, e₁⟩ := exists_sign_orbit hA'' hB'' hγ
    exact ⟨γ₁, h₁, by rw [e₁, e]⟩

/-! ### Conjugation by `GL(2, ℝ)` -/

lemma sl_smul_eq_toGL (γ : SL(2, ℝ)) (z : ℍ) : γ • z = toGL γ • z := by
  ext
  rw [coe_specialLinearGroup_apply, coe_smul_of_det_pos (by simp)]
  simp [num, denom]

lemma exists_conj_mem {g : GL (Fin 2) ℝ} {A B A₁ B₁ : SL(2, ℝ)}
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) {γ : SL(2, ℝ)}
    (hγ : γ ∈ Subgroup.closure {A, B}) :
    ∃ γ₁ ∈ Subgroup.closure {A₁, B₁}, toGL γ₁ = g * toGL γ * g⁻¹ := by
  induction hγ using Subgroup.closure_induction with
  | mem x hx =>
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨A₁, Subgroup.subset_closure (by simp), hA.symm⟩
    · exact ⟨B₁, Subgroup.subset_closure (by simp), hB.symm⟩
  | one => exact ⟨1, one_mem _, by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨x₁, hx₁, ex⟩ := ihx
    obtain ⟨y₁, hy₁, ey⟩ := ihy
    exact ⟨x₁ * y₁, mul_mem hx₁ hy₁, by rw [map_mul, map_mul, ex, ey]; group⟩
  | inv x _ ih =>
    obtain ⟨x₁, hx₁, ex⟩ := ih
    exact ⟨x₁⁻¹, inv_mem hx₁, by rw [map_inv, map_inv, ex]; group⟩

lemma orbits_conj {g : GL (Fin 2) ℝ} {A B A₁ B₁ : SL(2, ℝ)}
    (hA : g * toGL A * g⁻¹ = toGL A₁) (hB : g * toGL B * g⁻¹ = toGL B₁) (z w : ℍ) :
    (∃ γ ∈ Subgroup.closure {A, B}, γ • (g⁻¹ • z) = g⁻¹ • w) ↔
      ∃ γ₁ ∈ Subgroup.closure {A₁, B₁}, γ₁ • z = w := by
  have hA' : g⁻¹ * toGL A₁ * g⁻¹⁻¹ = toGL A := by rw [← hA]; group
  have hB' : g⁻¹ * toGL B₁ * g⁻¹⁻¹ = toGL B := by rw [← hB]; group
  constructor
  · rintro ⟨γ, hγ, e⟩
    obtain ⟨γ₁, h₁, e₁⟩ := exists_conj_mem hA hB hγ
    refine ⟨γ₁, h₁, ?_⟩
    rw [sl_smul_eq_toGL, e₁, mul_smul, mul_smul, ← sl_smul_eq_toGL, e, smul_inv_smul]
  · rintro ⟨γ₁, h₁, e⟩
    obtain ⟨γ, hγ, eγ⟩ := exists_conj_mem hA' hB' h₁
    refine ⟨γ, hγ, ?_⟩
    rw [sl_smul_eq_toGL, eγ, mul_smul, mul_smul, inv_inv, smul_inv_smul, ← sl_smul_eq_toGL, e]

/-- The Möbius map of `h ∈ GL(2, ℝ)` as a function on `ℂ`. -/
noncomputable def mobC (h : GL (Fin 2) ℝ) (u : ℂ) : ℂ := num h u / denom h u

lemma hasDerivAt_mobC (h : GL (Fin 2) ℝ) {u : ℂ} (hu : u.im ≠ 0) :
    HasDerivAt (mobC h) (h.det.val / denom h u ^ 2) u := by
  have hd := denom_ne_zero_of_im h hu
  have h1 : HasDerivAt (num h) (h 0 0) u := by
    have := ((hasDerivAt_id' u).const_mul ((h 0 0 : ℝ) : ℂ)).add_const ((h 0 1 : ℝ) : ℂ)
    rw [mul_one] at this
    exact this
  have h2 : HasDerivAt (denom h) (h 1 0) u := by
    have := ((hasDerivAt_id' u).const_mul ((h 1 0 : ℝ) : ℂ)).add_const ((h 1 1 : ℝ) : ℂ)
    rw [mul_one] at this
    exact this
  refine (h1.div h2 hd).congr_deriv ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  simp only [num, denom]; push_cast; ring

lemma mobC_ne (h : GL (Fin 2) ℝ) {u : ℂ} (hu : u.im ≠ 0) : h.det.val / denom h u ^ 2 ≠ 0 :=
  div_ne_zero (by exact_mod_cast h.det.ne_zero) (pow_ne_zero _ (denom_ne_zero_of_im h hu))

lemma coe_smul_ofComplex {h : GL (Fin 2) ℝ} {u : ℂ} (hu : 0 < u.im) :
    ((h • ofComplex u : ℍ) : ℂ) = σ h (mobC h u) := by
  rw [coe_smul, ofComplex_apply_of_im_pos hu]; rfl

/-- **Conjugation by `g` with `det g > 0`.** -/
theorem Uniformizes.conj_pos {A B A₁ B₁ : SL(2, ℝ)} (hU : Uniformizes W A B)
    {g : GL (Fin 2) ℝ} (hg : 0 < g.det.val) (hA : g * toGL A * g⁻¹ = toGL A₁)
    (hB : g * toGL B * g⁻¹ = toGL B₁) : Uniformizes W A₁ B₁ := by
  obtain ⟨π, h1, h2, h3, h4⟩ := hU
  have hgd : 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact hg
  have hσ : ∀ v, σ g⁻¹ v = v := fun v ↦ by simp [σ, hgd]
  refine ⟨fun u ↦ π ((g⁻¹ • ofComplex u : ℍ) : ℂ), ?_, ?_, ?_, ?_⟩
  · intro z
    have hz : (z : ℂ).im ≠ 0 := z.im_ne_zero
    have heq : (fun u ↦ π ((g⁻¹ • ofComplex u : ℍ) : ℂ)) =ᶠ[𝓝 (z : ℂ)] π ∘ mobC g⁻¹ := by
      filter_upwards [Uniformization.isOpen_upper.mem_nhds z.im_pos] with u hu
      simp only [Function.comp, coe_smul_ofComplex hu, hσ]
    have hm : mobC g⁻¹ z = ((g⁻¹ • z : ℍ) : ℂ) := by
      rw [← hσ (mobC g⁻¹ z), ← coe_smul_ofComplex z.im_pos, ofComplex_apply]
    have hπ := (h1 (g⁻¹ • z)).1.hasDerivAt
    rw [← hm] at hπ
    have hc := hπ.scomp (z : ℂ) (hasDerivAt_mobC g⁻¹ hz)
    refine ⟨(hc.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    rw [heq.deriv_eq, hc.deriv]
    refine smul_ne_zero (mobC_ne g⁻¹ hz) ?_
    have := (h1 (g⁻¹ • z)).2
    rwa [← hm] at this
  · intro z
    simp only [ofComplex_apply]
    exact h2 _
  · intro x y hxy
    obtain ⟨z₀, hz₀⟩ := h3 x y hxy
    exact ⟨g • z₀, by simp only [ofComplex_apply, inv_smul_smul, hz₀]⟩
  · intro z w
    simp only [ofComplex_apply]
    rw [h4, orbits_conj hA hB]

lemma hasDerivAt_conj_prod {π : ℂ → ℂ × ℂ} {p : ℂ × ℂ} {v : ℂ} (h : HasDerivAt π p (conj v)) :
    HasDerivAt (fun u ↦ (conj (π (conj u)).1, conj (π (conj u)).2)) (conj p.1, conj p.2) v := by
  have h1 : HasDerivAt (fun u ↦ (π u).1) p.1 (conj v) :=
    (hasFDerivAt_fst (p := π (conj v))).comp_hasDerivAt (conj v) h
  have h2 : HasDerivAt (fun u ↦ (π u).2) p.2 (conj v) :=
    (hasFDerivAt_snd (p := π (conj v))).comp_hasDerivAt (conj v) h
  have c1 := h1.conj_conj
  have c2 := h2.conj_conj
  rw [conj_conj] at c1 c2
  exact c1.prodMk c2

/-- **Conjugation by `g` with `det g < 0`**, onto the complex-conjugate curve. -/
theorem Uniformizes.conj_neg {A B A₁ B₁ : SL(2, ℝ)} (hU : Uniformizes W A B)
    {g : GL (Fin 2) ℝ} (hg : g.det.val < 0) (hA : g * toGL A * g⁻¹ = toGL A₁)
    (hB : g * toGL B * g⁻¹ = toGL B₁) : Uniformizes (W.map (starRingEnd ℂ)) A₁ B₁ := by
  obtain ⟨π, h1, h2, h3, h4⟩ := hU
  have hgd : ¬ 0 < (g : Matrix (Fin 2) (Fin 2) ℝ).det := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact not_lt.mpr hg.le
  have hσ : ∀ v, σ g⁻¹ v = conj v := fun v ↦ by simp [σ, hgd]
  set Pc : ℂ → ℂ × ℂ := fun u ↦ (conj (π (conj u)).1, conj (π (conj u)).2)
  refine ⟨fun u ↦ (conj (π ((g⁻¹ • ofComplex u : ℍ) : ℂ)).1,
    conj (π ((g⁻¹ • ofComplex u : ℍ) : ℂ)).2), ?_, ?_, ?_, ?_⟩
  · intro z
    have hz : (z : ℂ).im ≠ 0 := z.im_ne_zero
    have heq : (fun u ↦ (conj (π ((g⁻¹ • ofComplex u : ℍ) : ℂ)).1,
        conj (π ((g⁻¹ • ofComplex u : ℍ) : ℂ)).2)) =ᶠ[𝓝 (z : ℂ)] Pc ∘ mobC g⁻¹ := by
      filter_upwards [Uniformization.isOpen_upper.mem_nhds z.im_pos] with u hu
      simp only [Function.comp, coe_smul_ofComplex hu, hσ, Pc]
    have hm : conj (mobC g⁻¹ z) = ((g⁻¹ • z : ℍ) : ℂ) := by
      rw [← hσ, ← coe_smul_ofComplex z.im_pos, ofComplex_apply]
    have hπ := (h1 (g⁻¹ • z)).1.hasDerivAt
    rw [← hm] at hπ
    have hPc := hasDerivAt_conj_prod hπ
    have hc := hPc.scomp (z : ℂ) (hasDerivAt_mobC g⁻¹ hz)
    refine ⟨(hc.congr_of_eventuallyEq heq).differentiableAt, ?_⟩
    rw [heq.deriv_eq, hc.deriv]
    refine smul_ne_zero (mobC_ne g⁻¹ hz) ?_
    have := (h1 (g⁻¹ • z)).2
    rw [← hm] at this
    intro h0
    apply this
    simp only [Prod.mk_eq_zero, map_eq_zero] at h0
    exact Prod.ext h0.1 h0.2
  · intro z
    simp only [ofComplex_apply]
    exact (WeierstrassCurve.Affine.map_equation W.toAffine (f := starRingEnd ℂ)
      (RingHom.injective _) _ _).mpr (h2 _)
  · intro x y hxy
    have hxy' : W.toAffine.Equation (conj x) (conj y) := by
      rw [← WeierstrassCurve.Affine.map_equation W.toAffine (f := starRingEnd ℂ)
          (RingHom.injective _),
        conj_conj, conj_conj]
      exact hxy
    obtain ⟨z₀, hz₀⟩ := h3 _ _ hxy'
    refine ⟨g • z₀, ?_⟩
    simp only [ofComplex_apply, inv_smul_smul, hz₀, conj_conj]
  · intro z w
    simp only [ofComplex_apply]
    rw [← orbits_conj hA hB, ← h4]
    constructor
    · intro h
      simp only [Prod.mk.injEq, RingHom.injective _ |>.eq_iff] at h
      exact Prod.ext h.1 h.2
    · intro h; rw [h]

/-- **A Takeuchi-uniformised curve is uniformised by one of the four explicit pairs**, possibly
after complex conjugation. -/
theorem Uniformizes.exists_takeuchiPair {A B : SL(2, ℝ)} (hU : Uniformizes W A B)
    (hT : IsTakeuchiConj A B) : ∃ i : Fin 4,
      Uniformizes W (takeuchiPair i).1 (takeuchiPair i).2 ∨
        Uniformizes (W.map (starRingEnd ℂ)) (takeuchiPair i).1 (takeuchiPair i).2 := by
  obtain ⟨A', B', hcl, i, A'', hA'', B'', hB'', g, hgA, hgB⟩ := hT
  have hU'' := Uniformizes.of_signs (Uniformizes.of_closure_eq hU hcl) hA'' hB''
  refine ⟨i, ?_⟩
  rcases lt_or_gt_of_ne (show g.det.val ≠ 0 from g.det.ne_zero) with h | h
  · exact Or.inr (Uniformizes.conj_neg hU'' h hgA hgB)
  · exact Or.inl (Uniformizes.conj_pos hU'' h hgA hgB)

end OrbicurveCores.S1
