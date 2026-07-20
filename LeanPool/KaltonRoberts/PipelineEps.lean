/-
Copyright (c) 2026 Ho Boon Suan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ho Boon Suan
-/

/-
# Epsilon pipeline: spine theorems and final C₂ bound

Uses `one_sided_recombination_core_eps` and `two_sided_recombination_core_eps`
from `EpsilonRecombination.lean` to prove the spine theorem with epsilon loss,
then concludes the exact `C₂` bound via `∀ ε > 0, M ≤ C₂ + ε ⟹ M ≤ C₂`.

**Reference**: Section 5 of the companion paper.
-/
import LeanPool.KaltonRoberts.Pipeline
import LeanPool.KaltonRoberts.EpsilonRecombination

/-!
# Epsilon pipeline

Spine theorems with epsilon-loss recombination and the final exact `C₂` bound.
-/

namespace KaltonRoberts

open Finset BigOperators

variable {U : Type*} [DecidableEq U] [Fintype U]

/-! ## Case 1 spine with epsilon recombination -/

/-- Case 1 spine with epsilon recombination.
Same as `spine_case1` but with epsilon one-sided recombination.
Proves `M ≤ C₂ + 2 * ε`. -/
lemma spine_case1_eps
    (g : Finset U → ℝ) (hg : IsApproxAdditive g 1) (M : ℝ) (hM_pos : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M)
    (cert : DualCertificate g M)
    (hq_le : cert.negMass ≤ ↑q₀)
    (hq_half : cert.negMass ≤ 1 / 2)
    -- Mixed intersection (same as spine_case1)
    (hmix : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (D : ℝ) (_ : 0 ≤ D)
      (_ : C.avgDeficit g M ≤ D)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgDeficit g M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2))
    -- Epsilon one-sided recombination
    (hrec1_eps : ∀ (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (_ : 0 < r_v) (_ : 0 < (α_v : ℝ))
      (C : WeightedCollection U) (_ : ∀ i, C.itemFreq i ≤ (α_v : ℝ))
      (D : ℝ) (_ : 0 ≤ D) (_ : C.avgDeficit g M ≤ D)
      (ε : ℝ) (_ : 0 < ε),
      ∃ (C' : WeightedCollection U) (D' : ℝ), 0 ≤ D' ∧
        (∀ i, C'.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'.avgDeficit g M ≤ D' ∧
        (1 - (θ_v : ℝ)) * M ≤ D + ε - (θ_v : ℝ) * D' +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    (hexp1 : StrongExpandersExist α₁ 4 (1 / 3))
    (hexp2 : StrongExpandersExist (3009 / 10000) 4 (4 / 7))
    (ε : ℝ) (hε : 0 < ε) :
    M ≤ ↑C₂ + 2 * ε := by
  -- Apply mixed intersection with C₀, t = q, D = q*(1-u), ℓ = 3, τ = τ₁
  have h_mixed : ∃ C₁ : WeightedCollection U,
      (∀ i : U, C₁.itemFreq i ≤ (1 - τ₁) * cert.negMass ^ 3 + τ₁ * cert.negMass ^ 4) ∧
      C₁.avgDeficit g M ≤ 3 * (cert.negMass * (1 - g Finset.univ)) + 4 +
        τ₁ * (cert.negMass * (1 - g Finset.univ) + 2) := by
    convert hmix ( cert.augPosCollection ) ( cert.negMass ) ( by
      exact cert.negMass_nonneg ) ( by
      exact le_trans hq_le (by simp [q₀]; norm_num) ) ( by
      exact fun i => le_of_eq ( DualCertificate.augPosCollection_itemFreq cert i ) )
      ( cert.negMass * ( 1 - g Finset.univ ) ) ( by
      exact mul_nonneg ( by linarith [ cert.negMass_nonneg ] )
        ( by linarith [ abs_le.mp ( g_univ_le_one cert hg hM_pos hM_bound ) ] ) ) ( by
      convert DualCertificate.augPosCollection_avgDeficit_le cert hg hM_bound using 1 ) 3 ( by
      norm_num ) ( τ₁ : ℝ ) ( by
      exact_mod_cast τ₁_nonneg ) ( by
      exact_mod_cast τ₁_le_one ) using 1;
    norm_num [ pow_succ ];
  -- Set D₁ = mixed intersection deficit bound
  set D₁ := 3 * (cert.negMass * (1 - g Finset.univ)) + 4 +
    τ₁ * (cert.negMass * (1 - g Finset.univ) + 2) with hD₁_def
  -- Apply hrec1_eps with α₁, 4, 1/3, hexp1
  obtain ⟨C₂_coll, D', hD'_nonneg, hC₂_freq, hC₂_deficit, hC₂_rec⟩ :=
    hrec1_eps α₁ 4 (1 / 3) (by norm_num) (by norm_num) hexp1
      (by norm_num) (by norm_num [α₁])
      h_mixed.choose (by
    intro i
    have := h_mixed.choose_spec.left i
    have h_freq_le : (1 - τ₁) * cert.negMass ^ 3 + τ₁ * cert.negMass ^ 4 ≤
        (1 - τ₁) * q₀ ^ 3 + τ₁ * q₀ ^ 4 := by
      gcongr
      · exact sub_nonneg_of_le ( mod_cast τ₁_le_one )
      · exact Finset.sum_nonneg fun _ _ => le_max_right _ _
      · exact_mod_cast τ₁_nonneg
      · exact Finset.sum_nonneg fun _ _ => le_max_right _ _
    exact this.trans (h_freq_le.trans (by
      rw [show (α₁ : ℝ) = (1 - τ₁) * q₀ ^ 3 + τ₁ * q₀ ^ 4 by
        exact mod_cast frequency_identity_case1.symm])))
      D₁ (by
    have h_negMass_nonneg : 0 ≤ cert.negMass :=
      Finset.sum_nonneg fun _ _ => le_max_right _ _
    have h_g_univ_le_one : |g Finset.univ| ≤ 1 :=
      g_univ_le_one cert hg hM_pos hM_bound
    exact add_nonneg ( add_nonneg ( mul_nonneg zero_le_three
      ( mul_nonneg h_negMass_nonneg
        ( by linarith [ abs_le.mp h_g_univ_le_one ] ) ) ) zero_le_four )
      ( mul_nonneg ( by exact_mod_cast τ₁_nonneg )
        ( by nlinarith [ abs_le.mp h_g_univ_le_one ] ) )) (by
    exact h_mixed.choose_spec.2) ε hε
  -- Apply hrec1_eps with 3009/10000, 4, 4/7, hexp2
  obtain ⟨C₃_coll, D'', hD''_nonneg, hC₃_freq, hC₃_deficit, hC₃_rec⟩ :=
    hrec1_eps (3009 / 10000) 4 (4 / 7) (by norm_num) (by norm_num) hexp2
      (by norm_num) (by norm_num)
      C₂_coll (by
    convert hC₂_freq using 1;
    norm_num [ α₁ ]) D' hD'_nonneg hC₂_deficit ε hε
  -- Bound D₁
  have hD₁_le : D₁ ≤ 6 * q₀ + 4 + τ₁ * (2 * q₀ + 2) := by
    have hD₁_le : cert.negMass * (1 - g Finset.univ) ≤ 2 * q₀ := by
      have h_g_univ_le_one : |g Finset.univ| ≤ 1 :=
        g_univ_le_one cert hg hM_pos hM_bound
      nlinarith [ abs_le.mp h_g_univ_le_one, show ( q₀ : ℝ ) ≥ 0 by norm_num [q₀] ]
    nlinarith [ show ( τ₁ : ℝ ) ≥ 0 by exact_mod_cast τ₁_nonneg ]
  -- Final arithmetic: M ≤ C₂ + 2*ε
  -- hC₂_rec: (2/3)*M ≤ D₁ + ε - (1/3)*D' + 20/3
  -- hC₃_rec: (3/7)*M ≤ D' + ε - (4/7)*D'' + 45/7
  -- From these + hD₁_le + hD'' ≥ 0: M ≤ C₁ + (28/17)*ε ≤ C₂ + 2*ε
  have hD₁_num : D₁ ≤ (1525933315253649686407 : ℝ) / 210499561655322750000 := by
    calc D₁ ≤ (6 : ℝ) * q₀ + 4 + τ₁ * (2 * q₀ + 2) := hD₁_le
      _ = _ := by simp only [q₀, τ₁, α₁]; norm_num
  have hC₂_num : (C₂ : ℝ) =
      (694198146664396294486127753 : ℝ) / 34994834677886019996000000 := by
    simp only [C₂]; norm_num
  rw [hC₂_num]
  linarith

/-! ## Case 2 spine with epsilon recombination -/

/-- Case 2 spine with epsilon recombination.
Same as `spine_case2` but with epsilon two-sided recombination.
Proves `M ≤ C₂ + 2 * ε`. -/
lemma spine_case2_eps
    (g : Finset U → ℝ) (hg : IsApproxAdditive g 1) (M : ℝ) (hM_pos : 0 < M)
    (hM_bound : ∀ S : Finset U, |g S| ≤ M)
    (cert : DualCertificate g M)
    (hq_gt : ↑q₀ < cert.negMass)
    (hq_half : cert.negMass ≤ 1 / 2)
    -- Mixed intersection (deficit and surplus)
    (hmix : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (D : ℝ) (_ : 0 ≤ D)
      (_ : C.avgDeficit g M ≤ D)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgDeficit g M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ * (D + 2))
    (hmix_sur : ∀ (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (S_val : ℝ) (_ : 0 ≤ S_val)
      (_ : C.avgSurplus g M ≤ S_val)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ : ℝ) (_ : 0 ≤ τ) (_ : τ ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ) * t ^ ℓ + τ * t ^ (ℓ + 1)) ∧
        C'.avgSurplus g M ≤ ℓ * S_val + 2 * ((ℓ : ℝ) - 1) + τ * (S_val + 2))
    -- Epsilon two-sided recombination
    (hrec2_eps : ∀ (C_def C_sur : WeightedCollection U)
      (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (_ : 0 < r_v) (_ : 0 < (α_v : ℝ))
      (_ : ∀ i, C_def.itemFreq i ≤ (α_v : ℝ))
      (_ : ∀ i, C_sur.itemFreq i ≤ (α_v : ℝ))
      (D S_val : ℝ) (_ : 0 ≤ D) (_ : 0 ≤ S_val)
      (_ : C_def.avgDeficit g M ≤ D)
      (_ : C_sur.avgSurplus g M ≤ S_val)
      (ε : ℝ) (_ : 0 < ε),
      ∃ (C'_def C'_sur : WeightedCollection U) (D' S' : ℝ), 0 ≤ D' ∧ 0 ≤ S' ∧
        (∀ i, C'_def.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        (∀ i, C'_sur.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'_def.avgDeficit g M ≤ D' ∧
        C'_sur.avgSurplus g M ≤ S' ∧
        (1 - (θ_v : ℝ)) * M ≤ (D + S_val) / 2 + ε - (θ_v : ℝ) * ((D' + S') / 2) +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    (hexp3 : StrongExpandersExist α₂ 4 (2 / 7))
    (hexp4 : StrongExpandersExist (329 / 1250) 5 (5 / 11))
    (ε : ℝ) (hε : 0 < ε) :
    M ≤ ↑C₂ + 2 * ε := by
  -- Apply hmix to the augmented collection to get the deficit
  obtain ⟨C_def, hC_def⟩ := hmix cert.augPosCollection cert.negMass (by
    grind +suggestions) (by
    linarith) (by
    exact fun i => DualCertificate.augPosCollection_itemFreq cert i |> le_of_eq)
    (cert.negMass * (1 - g Finset.univ)) (by
    exact mul_nonneg ( cert_negMass_pos cert hg hM_pos hM_bound |> le_of_lt )
      ( sub_nonneg.2 <| le_of_abs_le <| g_univ_le_one cert hg hM_pos hM_bound )) (by
    convert DualCertificate.augPosCollection_avgDeficit_le cert hg hM_bound using 1) 4 (by
    norm_num) 0 (by norm_num) (by norm_num);
  -- Apply hmix_sur to the augmented collection to get the surplus
  obtain ⟨C_sur, hC_sur⟩ := hmix_sur cert.augNegCollection cert.posMass (by
    exact Finset.sum_nonneg fun _ _ => le_max_right _ _) (by
    exact cert.posMass_le_one) (by
    exact fun i => DualCertificate.augNegCollection_itemFreq cert i ▸ le_rfl)
    (cert.posMass * (1 + g Finset.univ)) (by
    exact mul_nonneg ( le_of_lt ( cert_posMass_pos cert hg hM_pos hM_bound ) )
      ( by linarith [ abs_le.mp ( g_univ_le_one cert hg hM_pos hM_bound ) ] )) (by
    convert DualCertificate.augNegCollection_avgSurplus_le _ _ _ using 1;
    · exact hg;
    · exact hM_bound) 4 (by norm_num) τ₂ (by exact_mod_cast τ₂_nonneg)
    (by exact_mod_cast τ₂_le_one);
  -- Apply hrec2_eps to get the first two-sided recombination with E₃
  obtain ⟨C'_def, C'_sur, D1, S1, hD1_nn, hS1_nn, hC'_def, hC'_sur,
      hC'_def_avg, hC'_sur_avg, hineq1⟩ :=
    hrec2_eps C_def C_sur α₂ 4 (2 / 7) (by norm_num) (by norm_num) hexp3
      (by norm_num) (by norm_num [α₂])
      (by
    intro i
    specialize hC_def
    have hC_def_i : C_def.itemFreq i ≤ cert.negMass ^ 4 := by
      simpa using hC_def.1 i
    have hC_def_i_le : cert.negMass ^ 4 ≤ α₂ := by
      exact le_trans
        (pow_le_pow_left₀
          (by
            linarith [
              show (0 : ℝ) ≤ cert.negMass by
                exact le_trans (by norm_num [q₀]) hq_gt.le])
          hq_half 4)
        (by norm_num [α₂])
    exact le_trans hC_def_i hC_def_i_le)
      (by
    intro i
    have hp_le_p0 : cert.posMass ≤ (↑p₀ : ℝ) := by
      have h1 := cert.posMass_add_negMass
      have h2 : (↑p₀ : ℝ) = 1 - (↑q₀ : ℝ) := by exact_mod_cast p₀_eq
      linarith
    have hp_nn : 0 ≤ cert.posMass := cert.posMass_nonneg
    have h_freq_sur : C_sur.itemFreq i ≤ (1 - τ₂) * p₀^4 + τ₂ * p₀^5 := by
      refine le_trans (hC_sur.1 i) ?_
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_nn hp_le_p0 4)
        linarith [show (τ₂ : ℝ) ≤ 1 from by exact_mod_cast τ₂_le_one]
      · apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp_nn hp_le_p0 5)
        exact_mod_cast τ₂_nonneg
    exact h_freq_sur.trans (by
      rw [show (α₂ : ℝ) = (1 - τ₂) * p₀ ^ 4 + τ₂ * p₀ ^ 5 by
        exact mod_cast frequency_identity_case2.symm])
      )
      (4 * (cert.negMass * (1 - g Finset.univ)) + 2 * (4 - 1))
      (4 * (cert.posMass * (1 + g Finset.univ)) + 2 * (4 - 1) +
        τ₂ * (cert.posMass * (1 + g Finset.univ) + 2))
      (by
    have := g_univ_le_one cert hg hM_pos hM_bound;
    nlinarith [
      abs_le.mp this,
      show (0 : ℝ) ≤ cert.negMass by
        exact le_of_lt (cert_negMass_pos cert hg hM_pos hM_bound)])
      (by
    have h_pos : 0 ≤ cert.posMass :=
      Finset.sum_nonneg fun _ _ => le_max_right _ _
    have h_pos_g : -1 ≤ g univ :=
      neg_le_of_abs_le ( g_univ_le_one cert hg hM_pos hM_bound )
    have h_pos_g' : g univ ≤ 1 :=
      by linarith [ abs_le.mp ( g_univ_le_one cert hg hM_pos hM_bound ) ]
    norm_num at *;
    exact add_nonneg ( add_nonneg ( mul_nonneg zero_le_four
      ( mul_nonneg h_pos ( by linarith ) ) ) ( by norm_num ) )
      ( mul_nonneg ( by exact_mod_cast τ₂_nonneg )
        ( add_nonneg ( mul_nonneg h_pos ( by linarith ) ) ( by norm_num ) ) ))
      (by exact hC_def.2.trans ( by norm_num ))
      (by exact hC_sur.2.trans ( by norm_num )) ε hε;
  -- Apply hrec2_eps again with E₄
  obtain ⟨C''_def, C''_sur, D2, S2, hD2_nn, hS2_nn, hC''_def, hC''_sur,
      hC''_def_avg, hC''_sur_avg, hineq2⟩ :=
    hrec2_eps C'_def C'_sur (329 / 1250) 5 (5 / 11) (by norm_num) (by norm_num) hexp4
      (by norm_num) (by norm_num)
      (by convert hC'_def using 1; norm_num [ α₂ ])
      (by convert hC'_sur using 1; norm_num [ α₂ ])
      D1 S1 (by exact hD1_nn) (by exact hS1_nn)
      (by exact hC'_def_avg) (by exact hC'_sur_avg) ε hε;
  -- Set Y1 = (D1 + S1) / 2
  set Y1 := (D1 + S1) / 2 with hY1_def
  have hY1_nn : 0 ≤ Y1 := by linarith
  -- Final arithmetic
  norm_num [ show cert.posMass = 1 - cert.negMass by linarith [ cert.posMass_add_negMass ] ] at *;
  unfold τ₂ at *;
  unfold C₂ p₀ α₂ at *;
  unfold q₀ at *;
  have := g_univ_le_one cert hg hM_pos hM_bound;
  norm_num [ abs_le ] at *;
  nlinarith [ mul_le_mul_of_nonneg_left hq_half hY1_nn ]

/-! ## The Section 5 spine theorem (epsilon version) -/

omit [Fintype U] in
/-- **Spine theorem** (epsilon version): `distToAdditive f ≤ C₂`
assuming all pipeline components with epsilon recombination.

Uses the real-analysis principle: if ∀ ε > 0, x ≤ y + ε, then x ≤ y.

**Reference**: Section 5 of the companion paper. -/
theorem distToAdditive_le_C₂_from_pipeline
    [Finite U]
    -- The target function
    (f : Finset U → ℝ) (hf : IsApproxAdditive f 1)
    -- Normalization: the infimum distance is attained
    (hnorm : ∃ a : U → ℝ, ∀ S : Finset U,
      |f S - additiveFunction a S| ≤ distToAdditive f)
    -- Mixed intersection construction
    (hmix : ∀ (g : Finset U → ℝ) (_ : IsApproxAdditive g 1) (M : ℝ)
      (_ : ∀ S, |g S| ≤ M)
      (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (D : ℝ) (_ : 0 ≤ D)
      (_ : C.avgDeficit g M ≤ D)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ_mix : ℝ) (_ : 0 ≤ τ_mix) (_ : τ_mix ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ_mix) * t ^ ℓ + τ_mix * t ^ (ℓ + 1)) ∧
        C'.avgDeficit g M ≤ ℓ * D + 2 * ((ℓ : ℝ) - 1) + τ_mix * (D + 2))
    (hmix_sur : ∀ (g : Finset U → ℝ) (_ : IsApproxAdditive g 1) (M : ℝ)
      (_ : ∀ S, |g S| ≤ M)
      (C : WeightedCollection U) (t : ℝ) (_ : 0 ≤ t) (_ : t ≤ 1)
      (_ : ∀ i, C.itemFreq i ≤ t) (S_val : ℝ) (_ : 0 ≤ S_val)
      (_ : C.avgSurplus g M ≤ S_val)
      (ℓ : ℕ) (_ : 1 ≤ ℓ) (τ_mix : ℝ) (_ : 0 ≤ τ_mix) (_ : τ_mix ≤ 1),
      ∃ C' : WeightedCollection U,
        (∀ i, C'.itemFreq i ≤ (1 - τ_mix) * t ^ ℓ + τ_mix * t ^ (ℓ + 1)) ∧
        C'.avgSurplus g M ≤ ℓ * S_val + 2 * ((ℓ : ℝ) - 1) + τ_mix * (S_val + 2))
    -- Epsilon one-sided recombination
    (hrec1_eps : ∀ (g : Finset U → ℝ) (_ : IsApproxAdditive g 1) (M : ℝ)
      (_ : ∀ S, |g S| ≤ M)
      (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (_ : 0 < r_v) (_ : 0 < (α_v : ℝ))
      (C : WeightedCollection U) (_ : ∀ i, C.itemFreq i ≤ (α_v : ℝ))
      (D : ℝ) (_ : 0 ≤ D) (_ : C.avgDeficit g M ≤ D)
      (ε : ℝ) (_ : 0 < ε),
      ∃ (C' : WeightedCollection U) (D' : ℝ), 0 ≤ D' ∧
        (∀ i, C'.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'.avgDeficit g M ≤ D' ∧
        (1 - (θ_v : ℝ)) * M ≤ D + ε - (θ_v : ℝ) * D' +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    -- Epsilon two-sided recombination
    (hrec2_eps : ∀ (g : Finset U → ℝ) (_ : IsApproxAdditive g 1) (M : ℝ)
      (_ : ∀ S, |g S| ≤ M)
      (α_v : ℚ) (r_v : ℕ) (θ_v : ℚ)
      (_ : 0 < (θ_v : ℝ)) (_ : (θ_v : ℝ) < 1)
      (_ : StrongExpandersExist α_v r_v θ_v)
      (_ : 0 < r_v) (_ : 0 < (α_v : ℝ))
      (C_def C_sur : WeightedCollection U)
      (_ : ∀ i, C_def.itemFreq i ≤ (α_v : ℝ))
      (_ : ∀ i, C_sur.itemFreq i ≤ (α_v : ℝ))
      (D S_val : ℝ) (_ : 0 ≤ D) (_ : 0 ≤ S_val)
      (_ : C_def.avgDeficit g M ≤ D)
      (_ : C_sur.avgSurplus g M ≤ S_val)
      (ε : ℝ) (_ : 0 < ε),
      ∃ (C'_def C'_sur : WeightedCollection U) (D' S' : ℝ), 0 ≤ D' ∧ 0 ≤ S' ∧
        (∀ i, C'_def.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        (∀ i, C'_sur.itemFreq i ≤ (α_v : ℝ) / (θ_v : ℝ)) ∧
        C'_def.avgDeficit g M ≤ D' ∧
        C'_sur.avgSurplus g M ≤ S' ∧
        (1 - (θ_v : ℝ)) * M ≤ (D + S_val) / 2 + ε -
          (θ_v : ℝ) * ((D' + S') / 2) +
          2 * (r_v : ℝ) - 1 - (θ_v : ℝ))
    -- Expander existence
    (hexp1 : StrongExpandersExist α₁ 4 (1 / 3))
    (hexp2 : StrongExpandersExist (3009 / 10000) 4 (4 / 7))
    (hexp3 : StrongExpandersExist α₂ 4 (2 / 7))
    (hexp4 : StrongExpandersExist (329 / 1250) 5 (5 / 11)) :
    distToAdditive f ≤ ↑C₂ := by
  letI := Fintype.ofFinite U
  -- Handle M ≤ 0
  by_cases hM : distToAdditive f ≤ 0
  · exact le_trans hM (by exact_mod_cast (show (0 : ℚ) ≤ C₂ by unfold C₂; norm_num))
  push Not at hM
  -- Use the real-analysis principle: ∀ ε > 0, M ≤ C₂ + ε ⟹ M ≤ C₂
  apply le_of_forall_pos_le_add
  intro δ hδ
  -- Normalize: subtract best additive approximation
  obtain ⟨a, ha⟩ := hnorm
  set g := fun S => f S - additiveFunction a S with hg_def
  have hg_add : IsApproxAdditive g 1 := IsApproxAdditive_sub_additive f hf a
  have hg_dist : distToAdditive g = distToAdditive f := distToAdditive_sub_additive f a
  -- Get dual certificate
  have hg_best := best_approx_property g (distToAdditive f) ha hg_dist
  obtain ⟨cert⟩ := dual_certificate_exists g hg_add (hg_dist ▸ ha) (hg_dist ▸ hg_best)
  rw [hg_dist] at cert
  -- Factor out: given any h with |h| ≤ M and cert with q ≤ 1/2, conclude M ≤ C₂ + δ
  suffices key : ∀ (h : Finset U → ℝ), IsApproxAdditive h 1 →
    (∀ S : Finset U, |h S| ≤ distToAdditive f) →
    DualCertificate h (distToAdditive f) →
    ∀ (c : DualCertificate h (distToAdditive f)), c.negMass ≤ 1/2 →
    distToAdditive f ≤ ↑C₂ + δ by
    rcases cert.can_swap_to_small_q with hq | hp
    · exact key g hg_add ha cert cert hq
    · have hg'_add := IsApproxAdditive_neg g hg_add
      have hg'_bound : ∀ S : Finset U, |(fun S => -g S) S| ≤ distToAdditive f := by
        intro S
        simp only [abs_neg]
        exact ha S
      exact key _ hg'_add hg'_bound cert.neg cert.neg (by rw [cert.neg_negMass]; exact hp)
  -- Prove key: case split on q ≤ q₀ vs q₀ < q
  intro h hh_add hh_bound _ c hq_half
  -- Use internal ε = δ/2
  have hε : 0 < δ / 2 := by linarith
  rcases le_or_gt c.negMass ↑q₀ with hq_le | hq_gt
  · -- Case 1: q ≤ q₀
    have := spine_case1_eps h hh_add (distToAdditive f) hM hh_bound c hq_le hq_half
      (fun C t ht ht1 hfreq D hD hdeficit ℓ hℓ τ hτ hτ1 =>
        hmix h hh_add _ hh_bound C t ht ht1 hfreq D hD hdeficit ℓ hℓ τ hτ hτ1)
      (fun α_v r_v θ_v hθ hθ1 hexp hr hα C hfreq D hD hdeficit ε' hε' =>
        hrec1_eps h hh_add _ hh_bound α_v r_v θ_v hθ hθ1 hexp hr hα C hfreq D
          hD hdeficit ε' hε')
      hexp1 hexp2 (δ / 2) hε
    linarith
  · -- Case 2: q₀ < q
    have := spine_case2_eps h hh_add (distToAdditive f) hM hh_bound c hq_gt hq_half
      (fun C t ht ht1 hfreq D hD hdeficit ℓ hℓ τ hτ hτ1 =>
        hmix h hh_add _ hh_bound C t ht ht1 hfreq D hD hdeficit ℓ hℓ τ hτ hτ1)
      (fun C t ht ht1 hfreq S_val hS hsurplus ℓ hℓ τ hτ hτ1 =>
        hmix_sur h hh_add _ hh_bound C t ht ht1 hfreq S_val hS hsurplus ℓ hℓ τ hτ hτ1)
      (fun C_def C_sur α_v r_v θ_v hθ hθ1 hexp hr hα hfreq_def hfreq_sur D S_val hD hS
          hdeficit hsurplus ε' hε' =>
        hrec2_eps h hh_add _ hh_bound α_v r_v θ_v hθ hθ1 hexp hr hα C_def C_sur
          hfreq_def hfreq_sur D S_val hD hS hdeficit hsurplus ε' hε')
      hexp3 hexp4 (δ / 2) hε
    linarith

end KaltonRoberts
