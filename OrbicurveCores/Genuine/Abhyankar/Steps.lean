/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.Genuine.Abhyankar.Tower
import OrbicurveCores.Genuine.Abhyankar.Valuation

/-!
# U2f (part): the Kummer steps of Abhyankar's lemma

Let `y` be a maximal ideal of `B`, `t ∈ y ∖ y²`, and `s ∈ Ω` with `s^m = t`. Let `F` be a finite
extension of `K` all of whose primes over `y` have ramification index `m`.

* `kummer_step`: `F(s)` is unramified over `F` at all primes over `y`;
* `kummer_base`: `K(s)` has ramification index `m` over `y`.
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
  obtain ⟨s₀, c₀, hs₀, hc₀, hsc⟩ := Rigid.exists_mul_eq_pow_mul hϖ hϖ2 hte hte'
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

end

end OrbicurveCores.Abhyankar
