/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import OrbicurveCores.ForMathlib.Abhyankar.Compositum
import OrbicurveCores.ForMathlib.Abhyankar.Valuation

/-!
# Abhyankar's lemma: the Kummer steps

Let `y` be a maximal ideal of `B`, `t ∈ y ∖ y²`, and `s ∈ Ω` with `s^m = t`. Let `F` be a finite
extension of `K` all of whose primes over `y` have ramification index `m`.

* `kummer_step`: `F(s)` is unramified over `F` at all primes over `y`;
* `kummer_base`: every prime over `y` of an extension containing `s` has ramification index
  divisible by `m`;
* `abhyankar`: **Abhyankar's lemma**: if all primes of `F₁` and `F₂` over `y` have ramification
  index `m`, then `F₁ ⊔ F₂` is unramified over `F₁` at all primes over `y`.
-/

open Polynomial IntermediateField

namespace OrbicurveCores.Abhyankar

noncomputable section

variable {B : Type} [CommRing B] [IsDedekindDomain B] [Algebra ℂ B]

local notation "K" => FractionRing B
local notation "Ω" => AlgebraicClosure (FractionRing B)

/-- **Kummer step**: adjoining an `m`-th root of a uniformiser of `y` to an extension with
ramification index `m` over `y` gives an extension unramified over all primes above `y`. -/
theorem kummer_step {F : IntermediateField K Ω} [FiniteDimensional K F] {y : Ideal B}
    [y.IsMaximal] (hy0 : y ≠ ⊥) {m₀ : ℕ} (hm₀ : m₀ ≠ 0)
    (hF : ∀ w : Ideal (IC B F), w.IsMaximal → w.under B = y → w.ramificationIdx B = m₀)
    {t : B} (ht : t ∈ y) (ht2 : t ∉ y ^ 2) {s : Ω} (hs : s ^ m₀ = algebraMap B Ω t)
    [FiniteDimensional K ↥(F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω)]
    (Q : Ideal (IC B (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω)))
    [hQ : Q.IsMaximal]
    (hQy : Q.under B = y) : ramIC le_sup_left Q = 1 := by
  have h : F ≤ (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) := le_sup_left
  -- the prime `w` of `IC F` below `Q`
  set w := Q.comap (icMap (B := B) h)
  haveI hwm : w.IsMaximal := isMaximal_comap_icMap h Q
  have hwy : w.under B = y := (under_comap_icMap h Q).trans hQy
  haveI : w.LiesOver y := ⟨hwy.symm⟩
  have hwe := hF w hwm hwy
  obtain ⟨hte, hte'⟩ := algebraMap_mem_pow_ramificationIdx (C := IC B F) hy0 ht ht2 (w := w)
  rw [hwe] at hte hte'
  have hw0 : w ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hy0 w
  obtain ⟨ϖ, hϖ, hϖ2⟩ := exists_uniformizer hw0
  obtain ⟨s₀, c₀, hs₀, hc₀, hsc⟩ := exists_mul_eq_pow_mul hϖ hϖ2 hte hte'
  -- the Kummer generator `θ = s₀ s / ϖ`
  have hϖ0 : ϖ ≠ 0 := by rintro rfl; exact hϖ2 (Ideal.zero_mem _)
  have hs₀0 : s₀ ≠ 0 := by rintro rfl; exact hs₀ (Ideal.zero_mem _)
  set W := icVal (B := B) F ϖ
  set S₀ := icVal (B := B) F s₀
  have hW0 : W ≠ 0 := fun h0 ↦ hϖ0 (icVal_injective F (h0.trans (map_zero _).symm))
  have hS₀0 : S₀ ≠ 0 := fun h0 ↦ hs₀0 (icVal_injective F (h0.trans (map_zero _).symm))
  set c := s₀ ^ (m₀ - 1) * c₀
  have hcw : c ∉ w := by
    intro hc
    rcases hwm.isPrime.mem_or_mem hc with h1 | h1
    · rcases Nat.eq_zero_or_pos (m₀ - 1) with h0 | hpos
      · rw [h0, pow_zero] at h1; exact hwm.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
      · exact hs₀ (hwm.isPrime.mem_of_pow_mem _ h1)
    · exact hc₀ h1
  set θΩ : Ω := S₀ * s / W
  have hθpow : θΩ ^ m₀ = icVal F c := by
    have hsc' := congrArg (icVal (B := B) F) hsc
    simp only [map_mul, map_pow, icVal_algebraMap] at hsc'
    rw [← hs] at hsc'
    simp only [θΩ, c, map_mul, map_pow]
    rw [div_pow, mul_pow, div_eq_iff (pow_ne_zero _ hW0)]
    obtain ⟨k, rfl⟩ : ∃ k, m₀ = k + 1 := ⟨m₀ - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hsc' ⊢
    rw [pow_succ S₀ k, mul_assoc, hsc']
    ring
  have hFF : F ≤ (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) := le_sup_left
  have hsF' : s ∈ (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) :=
    (le_sup_right : IntermediateField.adjoin K {s} ≤ _)
      (IntermediateField.mem_adjoin_simple_self K s)
  have hθmem : θΩ ∈ (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) := by
    refine div_mem (mul_mem (hFF (s₀ : F).2) hsF') (hFF (ϖ : F).2)
  set θ' : (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) := ⟨θΩ, hθmem⟩
  have hθ'pow : θ' ^ m₀ = ((icMap (B := B) h c : IC B _) : _) := Subtype.ext hθpow
  have hθint : IsIntegral B θ' := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm₀) ?_
    rw [hθ'pow]
    exact (icMap (B := B) h c).2
  set θ : IC B (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) := ⟨θ', hθint⟩
  have hθ : θ ^ m₀ = icMap h c := Subtype.ext hθ'pow
  have hgen : (F ⊔ IntermediateField.adjoin K {s} : IntermediateField K Ω) ≤
      (IntermediateField.adjoin F {((θ : _) : Ω)}).restrictScalars K := by
    refine sup_le (fun x hx ↦ ?_) ?_
    · exact (IntermediateField.adjoin F {((θ : _) : Ω)}).algebraMap_mem ⟨x, hx⟩
    · rw [IntermediateField.adjoin_simple_le_iff]
      change s ∈ IntermediateField.adjoin F {θΩ}
      have hs_eq : s = W * θΩ / S₀ := by
        simp only [θΩ]; field_simp
      rw [hs_eq]
      have hW : W ∈ IntermediateField.adjoin F {θΩ} :=
        (IntermediateField.adjoin F {θΩ}).algebraMap_mem (ϖ : F)
      have hS : S₀ ∈ IntermediateField.adjoin F {θΩ} :=
        (IntermediateField.adjoin F {θΩ}).algebraMap_mem (s₀ : F)
      exact div_mem (mul_mem hW (IntermediateField.mem_adjoin_simple_self F θΩ)) hS
  have hc : icMap h c ∉ Q := fun hm ↦ hcw hm
  exact ramIC_eq_one_of_pow_eq h hgen hm₀ hθ hc

/-- **Ramification of a Kummer extension of the base**: if `s ∈ E` with `s^m = t`, `t` a
uniformiser of `y`, then `m ∣ e(Q | y)` for every prime `Q` of `IC E` over `y`. -/
theorem kummer_base {y : Ideal B} [y.IsMaximal] (hy0 : y ≠ ⊥) {m₀ : ℕ} (hm₀ : m₀ ≠ 0) {t : B}
    (ht : t ∈ y) (ht2 : t ∉ y ^ 2) {s : Ω} (hs : s ^ m₀ = algebraMap B Ω t)
    {E : IntermediateField K Ω} [FiniteDimensional K E] (hsE : s ∈ E) (Q : Ideal (IC B E))
    [hQ : Q.IsMaximal] (hQy : Q.under B = y) : m₀ ∣ Q.ramificationIdx B := by
  haveI : Q.LiesOver y := ⟨hQy.symm⟩
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hy0 Q
  set sE : E := ⟨s, hsE⟩
  have hsEpow : sE ^ m₀ = algebraMap B E t := Subtype.ext hs
  have hsint : IsIntegral B sE := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm₀) ?_
    rw [hsEpow]; exact isIntegral_algebraMap
  set σ : IC B E := ⟨sE, hsint⟩
  have hσpow : σ ^ m₀ = algebraMap B (IC B E) t := Subtype.ext hsEpow
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (Ideal.zero_mem _)
  have hσ0 : σ ≠ 0 := by
    intro h0
    rw [h0, zero_pow hm₀] at hσpow
    exact ht0 (algebraMap_IC_injective E (hσpow.symm.trans (map_zero _).symm))
  have htQ : algebraMap B (IC B E) t ∈ Q := by
    rw [← hQy] at ht; exact ht
  have hσQ : σ ∈ Q := hQ.isPrime.mem_of_pow_mem m₀ (hσpow ▸ htQ)
  obtain ⟨k, -, hk, hk'⟩ := exists_order hσ0 hσQ
  obtain ⟨h1, h2⟩ := pow_mem_pow_notMem hQ0 hk hk' m₀
  rw [hσpow] at h1 h2
  obtain ⟨h3, h4⟩ := algebraMap_mem_pow_ramificationIdx (C := IC B E) hy0 ht ht2 (w := Q)
  refine ⟨k, le_antisymm ?_ ?_⟩
  · by_contra hlt
    push Not at hlt
    exact h2 (Ideal.pow_le_pow_right (by omega) h3)
  · by_contra hlt
    push Not at hlt
    exact h4 (Ideal.pow_le_pow_right (by omega) h1)

/-- **Abhyankar's lemma.** If all primes of `F₁` and of `F₂` over `y` have ramification index
`m`, then the compositum `G = F₁ ⊔ F₂` is unramified over `F₁` at all primes over `y`. -/
theorem abhyankar [Algebra.FiniteType ℂ B] {F₁ F₂ G : IntermediateField K Ω}
    [FiniteDimensional K F₁] [FiniteDimensional K F₂] [FiniteDimensional K G] {y : Ideal B}
    [y.IsMaximal] (hy0 : y ≠ ⊥) {m₀ : ℕ} (hm₀ : m₀ ≠ 0)
    (hF₁ : ∀ w : Ideal (IC B F₁), w.IsMaximal → w.under B = y → w.ramificationIdx B = m₀)
    (hF₂ : ∀ w : Ideal (IC B F₂), w.IsMaximal → w.under B = y → w.ramificationIdx B = m₀)
    (hG₁ : F₁ ≤ G) (hG₂ : F₂ ≤ G) (hG : G ≤ F₁ ⊔ F₂) (Q : Ideal (IC B G)) [Q.IsMaximal]
    (hQy : Q.under B = y) : ramIC hG₁ Q = 1 := by
  obtain ⟨t, ht, ht2⟩ := exists_uniformizer hy0
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B Ω t) (Nat.pos_of_ne_zero hm₀)
  have hsint : IsIntegral K s := by
    refine IsIntegral.of_pow (Nat.pos_of_ne_zero hm₀) ?_
    rw [hs, IsScalarTower.algebraMap_apply B K Ω]
    exact isIntegral_algebraMap
  set K' := IntermediateField.adjoin K {s}
  haveI : FiniteDimensional K K' := IntermediateField.adjoin.finiteDimensional hsint
  have hsK' : s ∈ K' := IntermediateField.mem_adjoin_simple_self K s
  set L₁ := F₁ ⊔ K'
  set L₂ := F₂ ⊔ K'
  set N := G ⊔ K'
  have h₁ : K' ≤ L₁ := le_sup_right
  have h₂ : K' ≤ L₂ := le_sup_right
  have hN₁ : L₁ ≤ N := sup_le_sup_right hG₁ _
  have hN₂ : L₂ ≤ N := sup_le_sup_right hG₂ _
  have hN : N ≤ L₁ ⊔ L₂ := sup_le (hG.trans (sup_le_sup le_sup_left le_sup_left))
    (h₁.trans le_sup_left)
  have hGN : G ≤ N := le_sup_left
  obtain ⟨Q'', hQ''m, hQ''⟩ := exists_comap_icMap_eq (B := B) hGN Q
  haveI := hQ''m
  have hQ''y : Q''.under B = y := by rw [← under_comap_icMap hGN, hQ'']; exact hQy
  -- `L₂ / K'` is unramified over `y`
  have hunr : ∀ q : Ideal (IC B L₂), q.IsMaximal →
      q.comap (icMap h₂) = Q''.comap (icMap (h₂.trans hN₂)) → ramIC h₂ q = 1 := by
    intro q hq hqQ
    have hqy : q.under B = y := by
      rw [← under_comap_icMap h₂, hqQ, under_comap_icMap, hQ''y]
    have e₁ := ramificationIdx_B_eq (B := B) (le_sup_left : F₂ ≤ L₂) q
    have e₂ := ramificationIdx_B_eq (B := B) h₂ q
    haveI := isMaximal_comap_icMap (B := B) (le_sup_left : F₂ ≤ L₂) q
    rw [hF₂ _ inferInstance ((under_comap_icMap _ q).trans hqy),
      kummer_step hy0 hm₀ hF₂ ht ht2 hs q hqy, mul_one] at e₁
    haveI := isMaximal_comap_icMap (B := B) h₂ q
    obtain ⟨j, hj⟩ := kummer_base hy0 hm₀ ht ht2 hs hsK' (q.comap (icMap h₂))
      ((under_comap_icMap _ q).trans hqy)
    rw [hj, e₁, mul_assoc] at e₂
    have := Nat.eq_one_of_mul_eq_one_left (Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero hm₀) (e₂.symm.trans (mul_one m₀).symm))
    exact this
  have hc := ramIC_compositum h₁ h₂ hN₁ hN₂ hN Q'' hunr
  -- `L₁ / F₁` is unramified over `y`
  haveI := isMaximal_comap_icMap (B := B) hN₁ Q''
  have hk := kummer_step hy0 hm₀ hF₁ ht ht2 hs (Q''.comap (icMap hN₁))
    ((under_comap_icMap _ Q'').trans hQ''y)
  have t₁ := ramIC_trans (B := B) (le_sup_left : F₁ ≤ L₁) hN₁ Q''
  have t₂ := ramIC_trans (B := B) hG₁ hGN Q''
  rw [hk, hc, mul_one] at t₁
  rw [hQ''] at t₂
  exact Nat.eq_one_of_mul_eq_one_right (t₂.symm.trans t₁)

end

end OrbicurveCores.Abhyankar
