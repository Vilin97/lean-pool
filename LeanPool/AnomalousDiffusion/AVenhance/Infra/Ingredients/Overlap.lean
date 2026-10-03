/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.CutoffConsequences
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Ingredients.LIdxConsequences

/-! Disjointness of the small `ζ` window from all but its assigned large window. -/

@[expose] public section

noncomputable section

namespace AVenhance.Infra.Ingredients

theorem Overlap.zetaMK_mem_outer_interval {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (k : ℤ) (t : ℝ) (hτ : 0 < AVenhance.tau β I.Λ m)
    (hne : I.zetaMK m k t ≠ 0) :
    t ∈ Set.Icc ((k : ℝ) * AVenhance.tau β I.Λ m -
        (2 / 3) * AVenhance.tau β I.Λ m)
      ((k : ℝ) * AVenhance.tau β I.Λ m +
        (2 / 3) * AVenhance.tau β I.Λ m) := by
  simp only [AVenhance.Ingredients.zetaMK, AVenhance.scaledCutoff] at hne
  have hnonneg := I.zeta_nonneg
      ((t - (k : ℝ) * AVenhance.tau β I.Λ m) / AVenhance.tau β I.Λ m)
  have hpos : 0 < I.zeta
      ((t - (k : ℝ) * AVenhance.tau β I.Λ m) / AVenhance.tau β I.Λ m) :=
    lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hmem : (t - (k : ℝ) * AVenhance.tau β I.Λ m) /
      AVenhance.tau β I.Λ m ∈ Set.Icc (-(2 / 3 : ℝ)) (2 / 3) := by
    by_contra hnot
    have hz : AVenhance.indIcc (-(2 / 3)) (2 / 3)
        ((t - (k : ℝ) * AVenhance.tau β I.Λ m) / AVenhance.tau β I.Λ m) = 0 := by
      unfold AVenhance.indIcc
      rw [Set.indicator_of_notMem hnot]
    have hle := I.zeta_le_ind
      ((t - (k : ℝ) * AVenhance.tau β I.Λ m) / AVenhance.tau β I.Λ m)
    rw [hz] at hle
    linarith
  have hlo := hmem.1
  have hhi := hmem.2
  rw [le_div_iff₀ hτ] at hlo
  rw [div_le_iff₀ hτ] at hhi
  constructor <;> nlinarith

theorem Overlap.hatZetaML_mem_core_interval {β : ℝ}
    (I : AVenhance.Ingredients β) {m : ℕ} (hm : 1 ≤ m) (l : ℤ) (t : ℝ)
    (hne : I.hatZetaML m l t ≠ 0) :
    t ∈ Set.Icc ((l - 1 / 2) * AVenhance.tauPP β I.Λ m +
        AVenhance.tauP β I.Λ m)
      ((l + 1 / 2) * AVenhance.tauPP β I.Λ m -
        AVenhance.tauP β I.Λ m) := by
  have hnonneg := hatZetaML_nonneg I hm l t
  have hpos : 0 < I.hatZetaML m l t := lt_of_le_of_ne hnonneg (Ne.symm hne)
  have hle := I.hatZeta_le m hm l t
  by_contra hnot
  have hz : AVenhance.indIcc
      ((l - 1 / 2) * AVenhance.tauPP β I.Λ m + AVenhance.tauP β I.Λ m)
      ((l + 1 / 2) * AVenhance.tauPP β I.Λ m - AVenhance.tauP β I.Λ m) t = 0 := by
    unfold AVenhance.indIcc
    rw [Set.indicator_of_notMem hnot]
  rw [hz] at hle
  change I.hatZetaML m l t ≤ 0 at hle
  linarith

/-- `e.cutoff.overlaps` (1363-1365), with the corrected floor index:
for `l ≠ l_k` the translated large cutoff and small cutoff have zero product. -/
theorem cutoff_overlaps {β : ℝ} (I : AVenhance.Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) (k l : ℤ) (hl : l ≠ AVenhance.lIdx β I.Λ m k) :
    ∀ t : ℝ, I.hatZetaML m l t * I.zetaMK m k t = 0 := by
  intro t
  by_cases hz : I.zetaMK m k t = 0
  · simp [hz]
  by_cases hh : I.hatZetaML m l t = 0
  · simp [hh]
  exfalso
  have hβ := I.one_lt_beta
  have hβ' := I.beta_lt
  have hΛ := I.two_pow_seven_le
  have hτ := tau_pos (β := β) (Λ := I.Λ) (m := m) hβ hβ' hΛ
  have hτP := AVenhance.Infra.Cutoff.tauP_pos (β := β) (Λ := I.Λ) (m := m) hβ hβ' hΛ
  have hτPP := AVenhance.Infra.Cutoff.tauPP_pos (β := β) (Λ := I.Λ) (m := m) hβ hβ' hΛ
  have hcell := taum_prime_supp k hβ hβ' hΛ hm
  have hsmall := Overlap.zetaMK_mem_outer_interval I k t hτ hz
  have hlarge := Overlap.hatZetaML_mem_core_interval I hm l t hh
  let L : ℤ := AVenhance.lIdx β I.Λ m k
  have hLleft : (L : ℝ) * AVenhance.tauPP β I.Λ m -
      AVenhance.tauPP β I.Λ m / 2 ≤ (k : ℝ) * AVenhance.tau β I.Λ m -
        AVenhance.tau β I.Λ m / 2 := by
    have hmem : ((k : ℝ) * AVenhance.tau β I.Λ m - AVenhance.tau β I.Λ m / 2) ∈
        Set.Icc ((k : ℝ) * AVenhance.tau β I.Λ m - AVenhance.tau β I.Λ m / 2)
          ((k : ℝ) * AVenhance.tau β I.Λ m + AVenhance.tau β I.Λ m / 2) := by
      simp only [Set.mem_Icc]
      constructor <;> linarith
    have h := hcell hmem
    simpa [L] using h.1
  have hLright : (k : ℝ) * AVenhance.tau β I.Λ m +
      AVenhance.tau β I.Λ m / 2 ≤ (L : ℝ) * AVenhance.tauPP β I.Λ m +
        AVenhance.tauPP β I.Λ m / 2 := by
    have hmem : ((k : ℝ) * AVenhance.tau β I.Λ m + AVenhance.tau β I.Λ m / 2) ∈
        Set.Icc ((k : ℝ) * AVenhance.tau β I.Λ m - AVenhance.tau β I.Λ m / 2)
          ((k : ℝ) * AVenhance.tau β I.Λ m + AVenhance.tau β I.Λ m / 2) := by
      simp only [Set.mem_Icc]
      constructor <;> linarith
    have h := hcell hmem
    simpa [L] using h.2
  have hfactor : 5 ≤ tauCellFactor β I.Λ m := by
    unfold tauCellFactor
    have hceilPos : 0 <
        ⌈AVenhance.epsilon β I.Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ := by
      apply Nat.ceil_pos.mpr
      exact Real.rpow_pos_of_pos
        (AVenhance.Infra.Cutoff.epsilon_pos hβ hβ' hΛ) _
    have hceil : 1 ≤
        (⌈AVenhance.epsilon β I.Λ (m - 1) ^ (-AVenhance.delta β)⌉₊ : ℝ) := by
      exact_mod_cast (Nat.succ_le_iff.mpr hceilPos)
    linarith
  have hτP_ge : 5 * AVenhance.tau β I.Λ m ≤ AVenhance.tauP β I.Λ m := by
    rw [tauP_eq_cellFactor_mul_tau hm]
    exact mul_le_mul_of_nonneg_right hfactor hτ.le
  have hltIndex : l ≤ L - 1 ∨ L + 1 ≤ l := by
    have hl' : l ≠ L := by simpa [L] using hl
    omega
  rcases hltIndex with hleft | hright
  · have hbound : (l : ℝ) ≤ (L : ℝ) - 1 := by exact_mod_cast hleft
    have hsep : (l + 1 / 2) * AVenhance.tauPP β I.Λ m -
          AVenhance.tauP β I.Λ m <
        (k : ℝ) * AVenhance.tau β I.Λ m -
          (2 / 3) * AVenhance.tau β I.Λ m := by
      nlinarith [hτPP, hτP_ge, hLleft]
    linarith [hsmall.1, hlarge.2]
  · have hbound : (L : ℝ) + 1 ≤ (l : ℝ) := by exact_mod_cast hright
    have hsep : (k : ℝ) * AVenhance.tau β I.Λ m +
          (2 / 3) * AVenhance.tau β I.Λ m <
        (l - 1 / 2) * AVenhance.tauPP β I.Λ m +
          AVenhance.tauP β I.Λ m := by
      nlinarith [hτPP, hτP_ge, hLright]
    linarith [hsmall.2, hlarge.1]

end AVenhance.Infra.Ingredients
