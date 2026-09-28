/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.M2.NoPair

/-!
# M2: uniqueness, commensurator equivariance, and extension

Let `Γ ≤ Δ ≤ Comm(Γ)` act on `ℙ¹(k)` through `a` (multiplicative on `Δ`).

* `ae_eq_of_equivariant`: two equivariant point maps agree a.e. (by `noPair`);
* `equivariant_commensurator`: an equivariant point map is automatically `Δ`-equivariant;
* `exists_extension`: if `Δ` is dense and the point map is essentially non-constant, the action
  of `Δ` extends to a homomorphism `Φ : SL(2, ℝ) → PGL(2, k)` with `g ↦ Φ(g) y` continuous.
  The proof uses sharp 3-transitivity at a generic triple of points and continuity of
  translation in measure.
-/

open MeasureTheory Filter Set Topology OnePoint.Proj
open scoped MatrixGroups ENNReal Pointwise

namespace OrbicurveCores.M2

variable {k : Type*} [NontriviallyNormedField k] [ProperSpace k] [DecidableEq k]
  [MeasurableSpace k] [BorelSpace k]

/-- **Uniqueness of equivariant point maps.** -/
theorem ae_eq_of_equivariant {Γ : Subgroup SL(2, ℝ)} [Countable Γ] (hΓ : IsDoublyErgodic Γ)
    {a : SL(2, ℝ) → GL (Fin 2) k} (hne : NonElem Γ a) (hact : ActsOn Γ a)
    {ψ₁ ψ₂ : OnePoint ℝ → OnePoint k} (h₁ : Measurable ψ₁) (h₂ : Measurable ψ₂)
    (e₁ : Equivariant Γ a ψ₁) (e₂ : Equivariant Γ a ψ₂) : ψ₁ =ᵐ[bdry] ψ₂ := by
  set E := {x | ψ₁ x = ψ₂ x}
  have hE : MeasurableSet E := measurableSet_eq_fun h₁ h₂
  have hinv : ∀ γ ∈ Γ, (fun x ↦ γ • x) ⁻¹' E =ᵐ[bdry] E := by
    intro γ hγ
    filter_upwards [e₁ γ hγ, e₂ γ hγ] with x hx1 hx2
    change (ψ₁ (γ • x) = ψ₂ (γ • x)) = (ψ₁ x = ψ₂ x)
    rw [hx1, hx2, smul_left_cancel_iff]
  rcases hΓ.null_or_conull_single hE hinv with h0 | h0
  · exfalso
    refine noPair hΓ hne hact h₁ h₂ (measure_eq_zero_iff_ae_notMem.1 h0) fun γ hγ ↦ ?_
    filter_upwards [e₁ γ hγ, e₂ γ hγ] with x hx1 hx2
    simp only [pairAt, hx1, hx2, Set.smul_set_insert, Set.smul_set_singleton]
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with x hx
    simpa [E] using hx

omit [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
lemma ActsOn.mono {Γ Γ' : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    (hle : Γ' ≤ Γ) : ActsOn Γ' a := fun g hg h' hh y ↦ h g (hle hg) h' (hle hh) y

omit [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
lemma NonElem.mono {Γ Γ' : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : NonElem Γ a)
    (hle : Γ' ≤ Γ) (hfi : Γ'.relIndex Γ ≠ 0) : NonElem Γ' a := by
  intro Γ'' hle' hfi' y
  refine h Γ'' (hle'.trans hle) ?_ y
  rw [← Subgroup.relIndex_mul_relIndex Γ'' Γ' Γ hle' hle]
  exact mul_ne_zero hfi' hfi

omit [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
lemma ActsOn.inv_smul {Γ : Subgroup SL(2, ℝ)} {a : SL(2, ℝ) → GL (Fin 2) k} (h : ActsOn Γ a)
    {δ : SL(2, ℝ)} (hδ : δ ∈ Γ) (z : OnePoint k) : a δ⁻¹ • z = (a δ)⁻¹ • z := by
  have := h.inv hδ ((a δ)⁻¹ • z)
  rwa [smul_inv_smul] at this

/-- **Equivariance under the commensurator.** -/
theorem equivariant_commensurator {Γ Δ : Subgroup SL(2, ℝ)} (hΓΔ : Γ ≤ Δ)
    (hΔ : Δ ≤ Subgroup.Commensurable.commensurator Γ) [Countable Γ]
    (hErg : ∀ Γ' : Subgroup SL(2, ℝ), Γ' ≤ Γ → Γ'.relIndex Γ ≠ 0 → IsDoublyErgodic Γ')
    {a : SL(2, ℝ) → GL (Fin 2) k} (hne : NonElem Γ a) (hact : ActsOn Δ a)
    {ψ : OnePoint ℝ → OnePoint k} (hψ : Measurable ψ) (heq : Equivariant Γ a ψ) :
    Equivariant Δ a ψ := by
  intro δ hδ
  set Γδ : Subgroup SL(2, ℝ) := (ConjAct.toConjAct δ⁻¹ • Γ) ⊓ Γ
  have hle : Γδ ≤ Γ := inf_le_right
  have hmem : ∀ γ ∈ Γδ, δ * γ * δ⁻¹ ∈ Γ := by
    intro γ hγ
    have := (Subgroup.mem_inf.1 hγ).1
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def] at this
    simpa using this
  have hfi : Γδ.relIndex Γ ≠ 0 := by
    rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.Commensurable.commensurator_mem_iff _ _).1 (inv_mem (hΔ hδ)) |>.1
  haveI : Countable Γδ := Set.Countable.to_subtype
    ((Set.countable_coe_iff.1 ‹Countable Γ›).mono hle)
  have hactδ : ActsOn Γδ a := hact.mono (hle.trans hΓΔ)
  set ψδ : OnePoint ℝ → OnePoint k := fun x ↦ (a δ)⁻¹ • ψ (δ • x)
  have hψδ : Measurable ψδ :=
    (OnePoint.Proj.continuous_gl_smul _).measurable.comp (hψ.comp (measurable_smul_bdry δ))
  have heqδ : Equivariant Γδ a ψδ := by
    intro γ hγ
    have hc := hmem γ hγ
    filter_upwards [ae_smul (heq _ hc) δ] with x hx
    simp only [ψδ]
    rw [← mul_smul, show δ * γ = δ * γ * δ⁻¹ * δ by group, mul_smul, hx]
    rw [hact _ (mul_mem hδ (hΓΔ (hle hγ))) _ (inv_mem hδ), hact _ hδ _ (hΓΔ (hle hγ)),
      hact.inv_smul hδ, inv_smul_smul]
  have hu := ae_eq_of_equivariant (hErg Γδ hle hfi) (hne.mono hle hfi) hactδ hψδ hψ heqδ
    (fun γ hγ ↦ heq γ (hle hγ))
  filter_upwards [hu] with x hx
  simp only [ψδ] at hx
  rw [← hx, smul_inv_smul]

/-! ### Extension to `SL(2, ℝ)` -/

omit [DecidableEq k] [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
/-- Three generic points. -/
lemma exists_generic_triple {S : OnePoint ℝ → Prop} (hS : ∀ᵐ x ∂bdry, S x)
    {R : OnePoint ℝ → OnePoint ℝ → Prop} (hR : ∀ᵐ q ∂(bdry.prod bdry), R q.1 q.2) :
    ∃ x₁ x₂ x₃, S x₁ ∧ S x₂ ∧ S x₃ ∧ R x₁ x₂ ∧ R x₁ x₃ ∧ R x₂ x₃ := by
  have h := Measure.ae_ae_of_ae_prod hR
  obtain ⟨x₁, hS₁, h₁⟩ := exists_of_ae (hS.and h)
  obtain ⟨x₂, hS₂, h₂, h₂'⟩ := exists_of_ae (hS.and (h₁.and h))
  obtain ⟨x₃, hS₃, h₃, h₃'⟩ := exists_of_ae (hS.and (h₁.and h₂'))
  exact ⟨x₁, x₂, x₃, hS₁, hS₂, hS₃, h₂, h₃, h₃'⟩

variable {ψ : OnePoint ℝ → OnePoint k}

omit [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
/-- An essentially non-constant point map determines Möbius maps: if `M ψ = N ψ` a.e. then
`M = N` on `ℙ¹(k)`. -/
lemma gl_smul_eq_of_ae (hψne : ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 ≠ ψ q.2) {M N : GL (Fin 2) k}
    (h : ∀ᵐ x ∂bdry, M • ψ x = N • ψ x) (y : OnePoint k) : M • y = N • y := by
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁₂, r₁₃, r₂₃⟩ :=
    exists_generic_triple (R := fun a b ↦ ψ a ≠ ψ b) h hψne
  rw [gl_smul_eq_mob, gl_smul_eq_mob]
  refine mob_eq_of_three M.det_ne_zero N.det_ne_zero r₁₂ r₁₃ r₂₃ ?_ ?_ ?_ y <;>
    rw [← gl_smul_eq_mob, ← gl_smul_eq_mob] <;> assumption

/-- The Möbius map `h(t') h(t)⁻¹` as an element of `GL(2, k)`. -/
noncomputable def triGL {t t' : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t)
    (ht' : Distinct3 t') : GL (Fin 2) k :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (tri t' * (tri t).adjugate) (by
    rw [Matrix.det_mul]; exact mul_ne_zero (det_tri_ne_zero ht') (det_adjugate_tri_ne_zero ht))

omit [ProperSpace k] [MeasurableSpace k] [BorelSpace k] in
lemma triGL_smul {t t' : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t)
    (ht' : Distinct3 t') (y : OnePoint k) :
    triGL ht ht' • y = mob (tri t') (mob (tri t).adjugate y) := by
  rw [gl_smul_eq_mob]
  change mob (tri t' * (tri t).adjugate) y = _
  rw [mob_mul (det_adjugate_tri_ne_zero ht)]

omit [MeasurableSpace k] [BorelSpace k] in
/-- **Limits of Möbius maps along a generic triple.** If `Mₙ t → t'` for a distinct triple `t`
and a distinct triple `t'`, then `Mₙ y → h(t') h(t)⁻¹ y` for every `y`. -/
lemma tendsto_smul_of_tendsto_triple {M : ℕ → GL (Fin 2) k}
    {t t' : OnePoint k × OnePoint k × OnePoint k} (ht : Distinct3 t) (ht' : Distinct3 t')
    (hlim : Tendsto (fun n ↦ smul3 (M n) t) atTop (𝓝 t')) (y : OnePoint k) :
    Tendsto (fun n ↦ M n • y) atTop (𝓝 (triGL ht ht' • y)) := by
  rw [triGL_smul]
  have e : ∀ n, M n • y = mob (tri (smul3 (M n) t)) (mob (tri t).adjugate y) := fun n ↦
    smul_eq_mob_tri _ ht y
  simp_rw [e]
  have hc := continuousAt_mobTri ht' (mob (tri t).adjugate y)
  have := hc.tendsto.comp (hlim.prodMk_nhds (tendsto_const_nhds (x := mob (tri t).adjugate y)))
  simp only [Function.comp_def, mobTri] at this
  exact this

omit [ProperSpace k] [DecidableEq k] [MeasurableSpace k] [BorelSpace k] in
lemma tendsto_smul3 {s : ℕ → OnePoint k × OnePoint k × OnePoint k}
    {t : OnePoint k × OnePoint k × OnePoint k}
    (h₁ : Tendsto (fun n ↦ (s n).1) atTop (𝓝 t.1))
    (h₂ : Tendsto (fun n ↦ (s n).2.1) atTop (𝓝 t.2.1))
    (h₃ : Tendsto (fun n ↦ (s n).2.2) atTop (𝓝 t.2.2)) : Tendsto s atTop (𝓝 t) :=
  h₁.prodMk_nhds (h₂.prodMk_nhds h₃)

omit [MeasurableSpace k] [BorelSpace k] in
/-- **Existence of the extension at a point.** -/
theorem exists_gl_of_dense {Δ : Subgroup SL(2, ℝ)} (hdense : Dense (Δ : Set SL(2, ℝ)))
    {a : SL(2, ℝ) → GL (Fin 2) k} (hψ : Measurable ψ) (heq : Equivariant Δ a ψ)
    (hψne : ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 ≠ ψ q.2) (g : SL(2, ℝ)) :
    ∃ M : GL (Fin 2) k, ∀ᵐ x ∂bdry, ψ (g • x) = M • ψ x := by
  obtain ⟨δ, hδΔ, hδ⟩ := mem_closure_iff_seq_limit.1 (hdense.closure_eq ▸ mem_univ g)
  obtain ⟨ns, -, hns⟩ := exists_subseq_ae_tendsto hψ hδ
  have hG : ∀ᵐ x ∂bdry, (∀ n, ψ (δ n • x) = a (δ n) • ψ x) ∧
      Tendsto (fun i ↦ ψ (δ (ns i) • x)) atTop (𝓝 (ψ (g • x))) :=
    (ae_all_iff.2 fun n ↦ heq _ (hδΔ n)).and hns
  have hR : ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 ≠ ψ q.2 ∧ ψ (g • q.1) ≠ ψ (g • q.2) :=
    hψne.and ((quasiMeasurePreserving_dact g).ae hψne)
  obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁₂, r₁₃, r₂₃⟩ :=
    exists_generic_triple (R := fun a b ↦ ψ a ≠ ψ b ∧ ψ (g • a) ≠ ψ (g • b)) hG hR
  set t := (ψ x₁, ψ x₂, ψ x₃)
  set t' := (ψ (g • x₁), ψ (g • x₂), ψ (g • x₃))
  have ht : Distinct3 t := ⟨r₁₂.1, r₁₃.1, r₂₃.1⟩
  have ht' : Distinct3 t' := ⟨r₁₂.2, r₁₃.2, r₂₃.2⟩
  refine ⟨triGL ht ht', ?_⟩
  have hlim : Tendsto (fun i ↦ smul3 (a (δ (ns i))) t) atTop (𝓝 t') := by
    refine tendsto_smul3 ?_ ?_ ?_ <;> simp only [smul3, t, t']
    · simp_rw [← h₁.1]; exact h₁.2
    · simp_rw [← h₂.1]; exact h₂.2
    · simp_rw [← h₃.1]; exact h₃.2
  filter_upwards [hG] with x hx
  refine tendsto_nhds_unique hx.2 ?_
  simp_rw [hx.1]
  exact tendsto_smul_of_tendsto_triple ht ht' hlim (ψ x)

omit [MeasurableSpace k] [BorelSpace k] in
/-- **Extension.** A `Δ`-equivariant, essentially non-constant point map, with `Δ` dense,
extends the action of `Δ` to a homomorphism `Φ : SL(2, ℝ) → PGL(2, k)` (represented in
`GL(2, k)`) with `g ↦ Φ(g) y` continuous for every `y`. -/
theorem exists_extension {Δ : Subgroup SL(2, ℝ)} (hdense : Dense (Δ : Set SL(2, ℝ)))
    {a : SL(2, ℝ) → GL (Fin 2) k} (hψ : Measurable ψ) (heq : Equivariant Δ a ψ)
    (hψne : ∀ᵐ q ∂(bdry.prod bdry), ψ q.1 ≠ ψ q.2) :
    ∃ Φ : SL(2, ℝ) → GL (Fin 2) k,
      (∀ g h : SL(2, ℝ), ∀ y : OnePoint k, Φ (g * h) • y = Φ g • Φ h • y) ∧
      (∀ δ ∈ Δ, ∀ y : OnePoint k, Φ δ • y = a δ • y) ∧
      (∀ y : OnePoint k, Continuous fun g ↦ Φ g • y) := by
  choose Φ hΦ using exists_gl_of_dense hdense hψ heq hψne
  refine ⟨Φ, fun g h y ↦ ?_, fun δ hδ y ↦ ?_, fun y ↦ ?_⟩
  · rw [← mul_smul]
    refine gl_smul_eq_of_ae hψne ?_ y
    filter_upwards [hΦ (g * h), ae_smul (hΦ g) h, hΦ h] with x h1 h2 h3
    rw [← h1, mul_smul, mul_smul, h2, h3]
  · refine gl_smul_eq_of_ae hψne ?_ y
    filter_upwards [hΦ δ, heq δ hδ] with x h1 h2
    rw [← h1, h2]
  · refine continuous_iff_seqContinuous.2 fun gs g₀ hg ↦ ?_
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨ms, -, hms⟩ := exists_subseq_ae_tendsto hψ (hg.comp hns)
    have hG : ∀ᵐ x ∂bdry, (∀ n, ψ (gs n • x) = Φ (gs n) • ψ x) ∧ ψ (g₀ • x) = Φ g₀ • ψ x ∧
        Tendsto (fun i ↦ ψ (gs (ns (ms i)) • x)) atTop (𝓝 (ψ (g₀ • x))) :=
      (ae_all_iff.2 fun n ↦ hΦ (gs n)).and ((hΦ g₀).and hms)
    obtain ⟨x₁, x₂, x₃, h₁, h₂, h₃, r₁₂, r₁₃, r₂₃⟩ :=
      exists_generic_triple (R := fun a b ↦ ψ a ≠ ψ b) hG hψne
    set t := (ψ x₁, ψ x₂, ψ x₃)
    have ht : Distinct3 t := ⟨r₁₂, r₁₃, r₂₃⟩
    have ht' := distinct3_smul3 (Φ g₀) ht
    have hlim : Tendsto (fun i ↦ smul3 (Φ (gs (ns (ms i)))) t) atTop (𝓝 (smul3 (Φ g₀) t)) := by
      refine tendsto_smul3 ?_ ?_ ?_ <;> simp only [smul3, t]
      · simp_rw [← h₁.1, ← h₁.2.1]; exact h₁.2.2
      · simp_rw [← h₂.1, ← h₂.2.1]; exact h₂.2.2
      · simp_rw [← h₃.1, ← h₃.2.1]; exact h₃.2.2
    refine ⟨ms, ?_⟩
    have := tendsto_smul_of_tendsto_triple ht ht' hlim y
    rwa [triGL_smul, ← smul_eq_mob_tri _ ht] at this

end OrbicurveCores.M2
