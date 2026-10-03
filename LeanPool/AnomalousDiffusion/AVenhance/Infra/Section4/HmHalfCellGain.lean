/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPositivePairingAssembly

/-! A positive half-cell endpoint can be chosen separately for each positive
time.  The resulting interval has refresh-scale length, and the source-rate
bound gains the square root of that refresh scale. -/

@[expose] public section

noncomputable section

open Set

namespace AVenhance.Infra.Section4

/-- For every point of `[0,1]`, some positive half-cell endpoint in `[0,1]`
is within one refresh length.  The endpoint at `τ/2` handles the initial
half-cell; otherwise the floor chooses the preceding half-cell endpoint. -/
theorem exists_positive_halfCell_endpoint_near
    {τ t : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∃ l : ℤ,
      0 < (l + 1 / 2) * τ ∧
      (l + 1 / 2) * τ ≤ 1 ∧
      max ((l + 1 / 2) * τ) t - min ((l + 1 / 2) * τ) t ≤ τ := by
  let u : ℝ := t / τ - 1 / 2
  by_cases hf : 0 ≤ Int.floor u
  · let l : ℤ := Int.floor u
    let c : ℝ := (l + 1 / 2) * τ
    have hfloorLo : (l : ℝ) ≤ u := by
      dsimp [l, u]
      exact Int.floor_le _
    have hfloorHi : u < (l : ℝ) + 1 := by
      dsimp [l, u]
      exact Int.lt_floor_add_one _
    have hl : 0 ≤ (l : ℝ) := by exact_mod_cast hf
    have hcPos : 0 < c := by
      dsimp [c]
      exact mul_pos (by nlinarith) hτ
    have hfloorLo' : (l : ℝ) + 1 / 2 ≤ t / τ := by
      dsimp [u] at hfloorLo
      linarith
    have hfloorHi' : t / τ < (l : ℝ) + 3 / 2 := by
      dsimp [u] at hfloorHi
      linarith
    have hcLeT : c ≤ t := by
      dsimp [c]
      exact (le_div_iff₀ hτ).mp hfloorLo'
    have htLt : t < c + τ := by
      have hscaled := (div_lt_iff₀ hτ).mp hfloorHi'
      dsimp [c]
      nlinarith
    have hdist : |t - c| ≤ τ := by
      rw [abs_le]
      constructor <;> linarith
    have hlen : max c t - min c t = |t - c| := by
      rcases le_total c t with hct | htc
      · rw [max_eq_right hct, min_eq_left hct,
          abs_of_nonneg (sub_nonneg.mpr hct)]
      · rw [max_eq_left htc, min_eq_right htc,
          abs_of_nonpos (sub_nonpos.mpr htc)]
        ring
    refine ⟨l, ?_, ?_, ?_⟩
    · exact hcPos
    · exact hcLeT.trans ht1
    · rw [show (l + 1 / 2) * τ = c from rfl, hlen]
      exact hdist
  · let l : ℤ := 0
    let c : ℝ := (l + 1 / 2) * τ
    have hfloorInt : Int.floor u ≤ -1 := by omega
    have hfloorNeg : (Int.floor u : ℝ) ≤ -1 := by exact_mod_cast hfloorInt
    have hu : u < 0 := by
      have hhi := Int.lt_floor_add_one u
      linarith [hfloorNeg]
    have htLt : t < τ / 2 := by
      have hdiv : t / τ < 1 / 2 := by
        dsimp [u] at hu
        linarith
      rw [div_lt_iff₀ hτ] at hdiv
      nlinarith
    have hcEq : c = τ / 2 := by norm_num [c, l]; ring
    have hcPos : 0 < c := by rw [hcEq]; positivity
    have hcLe : c ≤ 1 := by rw [hcEq]; linarith
    have hdist : |t - c| ≤ τ := by
      rw [hcEq, abs_le]
      constructor <;> nlinarith
    have hlen : max c t - min c t = |t - c| := by
      have htc : t ≤ c := le_of_lt (by rw [hcEq]; exact htLt)
      rw [max_eq_left htc, min_eq_right htc, abs_of_nonpos (sub_nonpos.mpr htc)]
      ring
    refine ⟨l, ?_, ?_, ?_⟩
    · exact hcPos
    · exact hcLe
    · rw [show (l + 1 / 2) * τ = c from rfl, hlen]
      exact hdist

/-- The actual Section 4 refresh time is at most one, so the geometric
selector applies to every positive time up to one. -/
theorem hm_tauPP_le_one {β : ℝ} (I : Ingredients β)
    {m : ℕ} (hm : 1 ≤ m) :
    tauPP β I.Λ m ≤ 1 := by
  have hE : 0 < epsilon β I.Λ (m - 1) :=
    Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hE1 : epsilon β I.Λ (m - 1) ≤ 1 :=
    Infra.Construction.epsilon_le_one I.one_lt_beta I.beta_lt I.two_pow_seven_le
  have hδ : 0 < delta β := Infra.Ingredients.delta_pos I.one_lt_beta I.beta_lt
  have hβgap : 0 < 2 - β := by linarith [I.beta_lt]
  have hexp : 0 ≤ 2 - β + 2 * delta β := by positivity
  have hpow : epsilon β I.Λ (m - 1) ^ (2 - β + 2 * delta β) ≤ 1 :=
    Real.rpow_le_one hE.le hE1 hexp
  have hupper := (Infra.Ingredients.tauPP_bounds I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hm).2
  have hconst : (2 : ℝ) ^ (-25 : ℤ) ≤ 1 := by norm_num
  calc
    tauPP β I.Λ m ≤ (2 : ℝ) ^ (-25 : ℤ) *
        epsilon β I.Λ (m - 1) ^ (2 - β + 2 * delta β) := hupper
    _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 1 := by simpa using hconst

/-- At every positive time, choose a positive zero endpoint of the `H_m` within one `τPP`
    interval.  The interval between the chosen endpoint
and `t` has length at most `τPP`, in the exact `min`/`max` form used by the
pairing FTC. -/
theorem hm_positive_time_halfCell_endpoint
    {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℤ,
        0 < (l + 1 / 2) * tauPP β I.Λ m ∧
        (l + 1 / 2) * tauPP β I.Λ m ≤ 1 ∧
        max ((l + 1 / 2) * tauPP β I.Λ m) t -
          min ((l + 1 / 2) * tauPP β I.Λ m) t ≤ tauPP β I.Λ m := by
  have hτ : 0 < tauPP β I.Λ m := I.tauPP_pos' m
  have hτ1 : tauPP β I.Λ m ≤ 1 := hm_tauPP_le_one I hm
  intro t ht
  exact exists_positive_halfCell_endpoint_near hτ hτ1 ht.1 ht.2

/-- The source rate from the Hm estimate gains `epsilon^(δ)` after multiplication
by `sqrt(τPP)`.  `hKprev` is the diffusivity-recursion κ comparison, `hProduct` is the
    diffusivity-recursion
product comparison, and `hTauPP` is the preceding-amplitude refresh-scale
comparison.  The scalar amplitude `Theta` is kept abstract. -/
theorem hm_regular_source_halfCell_gain_of_rates
    {β : ℝ} (I : Ingredients β) {m : ℕ}
    {κ κprev Creg Cprod Cκ Ctau Theta G : ℝ}
    (hκ : 0 < κ) (hκprev : 0 < κprev)
    (hCreg : 0 ≤ Creg) (hCprod : 0 ≤ Cprod)
    (hCκ : 0 ≤ Cκ) (hCtau : 0 ≤ Ctau) (hTheta : 0 ≤ Theta)
    (hKprev : κprev ≤ Cκ *
      (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hProduct : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ ≤ Cprod * κprev)
    (hTauPP : a β I.Λ (m - 1) * tauPP β I.Λ m ≤
      Ctau * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hSourceRate : G ≤ Creg * Theta *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
      (Real.sqrt κprev)⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) :
    Real.sqrt (tauPP β I.Λ m) * G ≤
      Creg * Cprod * Real.sqrt (Cκ * Ctau) *
        epsilon β I.Λ (m - 1) ^ delta β * Theta := by
  let E : ℝ := epsilon β I.Λ (m - 1)
  let ap : ℝ := a β I.Λ (m - 1)
  let τ : ℝ := tauPP β I.Λ m
  let R : ℝ := a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ
  let sκ : ℝ := Real.sqrt κprev
  have hE : 0 < E := by
    dsimp [E]
    exact Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt
      I.two_pow_seven_le (m := m - 1)
  have hap : 0 < ap := by
    dsimp [ap, a]
    exact Real.rpow_pos_of_pos hE _
  have hτ : 0 < τ := by dsimp [τ]; exact I.tauPP_pos' m
  have hsκ : 0 < sκ := by dsimp [sκ]; exact Real.sqrt_pos.2 hκprev
  have hsκinv : 0 ≤ sκ⁻¹ := inv_nonneg.mpr hsκ.le
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hfactor : 0 ≤ Creg * Theta * sκ⁻¹ *
      E ^ (-(1 + gamma β / 2)) := by positivity
  have hRcmp : R ≤ Cprod * κprev := by simpa [R] using hProduct
  have hGcmp : G ≤ Creg * Cprod * Theta * sκ *
      E ^ (-(1 + gamma β / 2)) := by
    calc
      G ≤ Creg * Theta * R * sκ⁻¹ *
          E ^ (-(1 + gamma β / 2)) := by simpa [R] using hSourceRate
      _ = (Creg * Theta * sκ⁻¹ * E ^ (-(1 + gamma β / 2))) * R := by ring
      _ ≤ (Creg * Theta * sκ⁻¹ * E ^ (-(1 + gamma β / 2))) *
          (Cprod * κprev) := mul_le_mul_of_nonneg_left hRcmp hfactor
      _ = Creg * Cprod * Theta * sκ *
          E ^ (-(1 + gamma β / 2)) := by
        have hcancel : κprev * sκ⁻¹ = sκ := by
          dsimp [sκ]
          field_simp [ne_of_gt (Real.sqrt_pos.2 hκprev)]
          rw [Real.sq_sqrt hκprev.le]
        calc
          _ = Creg * Cprod * Theta * (κprev * sκ⁻¹) *
              E ^ (-(1 + gamma β / 2)) := by ring
          _ = _ := by rw [hcancel]
  have hκτ : κprev * τ ≤ Cκ * Ctau *
      E ^ (2 + gamma β + 2 * delta β) := by
    have hKprev' : κprev ≤ Cκ * (ap * E ^ (2 + gamma β)) := by
      simpa [ap, E] using hKprev
    have hTauPP' : ap * τ ≤ Ctau * E ^ (2 * delta β) := by
      simpa [ap, τ, E] using hTauPP
    calc
      κprev * τ ≤ (Cκ * (ap * E ^ (2 + gamma β))) * τ :=
        mul_le_mul_of_nonneg_right hKprev' hτ.le
      _ = (Cκ * E ^ (2 + gamma β)) * (ap * τ) := by ring
      _ ≤ (Cκ * E ^ (2 + gamma β)) *
          (Ctau * E ^ (2 * delta β)) :=
        mul_le_mul_of_nonneg_left hTauPP'
          (mul_nonneg hCκ (Real.rpow_nonneg hE.le _))
      _ = Cκ * Ctau * (E ^ (2 + gamma β) * E ^ (2 * delta β)) := by ring
      _ = Cκ * Ctau * E ^ (2 + gamma β + 2 * delta β) := by
        rw [← Real.rpow_add hE]
  have hExpSq : E ^ (2 + gamma β + 2 * delta β) =
      (E ^ (1 + gamma β / 2 + delta β)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hE.le]
    congr 1
    ring
  have hroot : Real.sqrt (κprev * τ) ≤
      Real.sqrt (Cκ * Ctau) * E ^ (1 + gamma β / 2 + delta β) := by
    rw [hExpSq] at hκτ
    have hsquare : (Real.sqrt (Cκ * Ctau) *
        E ^ (1 + gamma β / 2 + delta β)) ^ 2 =
        Cκ * Ctau * (E ^ (1 + gamma β / 2 + delta β)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hCκ hCtau)]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    · calc
        κprev * τ ≤ Cκ * Ctau *
            (E ^ (1 + gamma β / 2 + delta β)) ^ 2 := hκτ
        _ = (Real.sqrt (Cκ * Ctau) *
            E ^ (1 + gamma β / 2 + delta β)) ^ 2 := hsquare.symm
  have hpow : E ^ (1 + gamma β / 2 + delta β) *
      E ^ (-(1 + gamma β / 2)) = E ^ delta β := by
    rw [← Real.rpow_add hE]
    congr 1
    ring
  have hrootWeighted :
      Creg * Cprod * Theta *
          (Real.sqrt (κprev * τ) * E ^ (-(1 + gamma β / 2))) ≤
        Creg * Cprod * Theta *
          (Real.sqrt (Cκ * Ctau) * E ^ (1 + gamma β / 2 + delta β) *
            E ^ (-(1 + gamma β / 2))) := by
    have hfactorE : 0 ≤ E ^ (-(1 + gamma β / 2)) :=
      Real.rpow_nonneg hE.le _
    have hmul : Real.sqrt (κprev * τ) * E ^ (-(1 + gamma β / 2)) ≤
        (Real.sqrt (Cκ * Ctau) * E ^ (1 + gamma β / 2 + delta β)) *
          E ^ (-(1 + gamma β / 2)) :=
      mul_le_mul_of_nonneg_right hroot hfactorE
    exact mul_le_mul_of_nonneg_left hmul (by positivity)
  calc
    Real.sqrt τ * G ≤ Real.sqrt τ *
        (Creg * Cprod * Theta * sκ * E ^ (-(1 + gamma β / 2))) :=
      mul_le_mul_of_nonneg_left hGcmp (Real.sqrt_nonneg _)
    _ = Creg * Cprod * Theta * Real.sqrt (κprev * τ) *
        E ^ (-(1 + gamma β / 2)) := by
      have hsqrtmul : Real.sqrt (κprev * τ) = sκ * Real.sqrt τ := by
        dsimp [sκ]
        rw [Real.sqrt_mul hκprev.le]
      rw [hsqrtmul]
      dsimp [sκ]
      ring
    _ ≤ Creg * Cprod * Theta *
        (Real.sqrt (Cκ * Ctau) * E ^ (1 + gamma β / 2 + delta β) *
          E ^ (-(1 + gamma β / 2))) := by
      calc
        _ = (Creg * Cprod * Theta) *
            (Real.sqrt (κprev * τ) * E ^ (-(1 + gamma β / 2))) := by ring
        _ ≤ Creg * Cprod * Theta *
            (Real.sqrt (Cκ * Ctau) * E ^ (1 + gamma β / 2 + delta β) *
              E ^ (-(1 + gamma β / 2))) := hrootWeighted
    _ = Creg * Cprod * Real.sqrt (Cκ * Ctau) * Theta *
        (E ^ (1 + gamma β / 2 + delta β) *
          E ^ (-(1 + gamma β / 2))) := by ring
        _ = Creg * Cprod * Real.sqrt (Cκ * Ctau) *
        E ^ delta β * Theta := by
      calc
        _ = Creg * Cprod * Real.sqrt (Cκ * Ctau) * Theta *
            (E ^ (1 + gamma β / 2 + delta β) *
              E ^ (-(1 + gamma β / 2))) := by rfl
        _ = _ := by rw [hpow]; dsimp [E]; ring

/-- The source-rate gain and endpoint choice together give the exact
coefficient bound needed in the regular-pairing Cauchy estimate on each
positive-time interval.  The returned interval length is in the same `min` /
`max` form as `frozen_hm_positive_time_bounds_of_pairings`. -/
theorem hm_positive_time_halfCell_source_gain
    {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    {κ κprev Creg Cprod Cκ Ctau Theta G : ℝ}
    (hκ : 0 < κ) (hκprev : 0 < κprev)
    (hCreg : 0 ≤ Creg) (hCprod : 0 ≤ Cprod)
    (hCκ : 0 ≤ Cκ) (hCtau : 0 ≤ Ctau) (hTheta : 0 ≤ Theta)
    (hGnonneg : 0 ≤ G)
    (hKprev : κprev ≤ Cκ *
      (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hProduct : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ ≤ Cprod * κprev)
    (hTauPP : a β I.Λ (m - 1) * tauPP β I.Λ m ≤
      Ctau * epsilon β I.Λ (m - 1) ^ (2 * delta β))
    (hSourceRate : G ≤ Creg * Theta *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
      (Real.sqrt κprev)⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℤ,
        let c := (l + 1 / 2) * tauPP β I.Λ m
        0 < c ∧ c ≤ 1 ∧
          max c t - min c t ≤ tauPP β I.Λ m ∧
          Real.sqrt (max c t - min c t) * G ≤
            Creg * Cprod * Real.sqrt (Cκ * Ctau) *
              epsilon β I.Λ (m - 1) ^ delta β * Theta := by
  have hGain := hm_regular_source_halfCell_gain_of_rates I hκ hκprev
    hCreg hCprod hCκ hCtau hTheta hKprev hProduct hTauPP hSourceRate
  intro t ht
  obtain ⟨l, hc, hc1, hlen⟩ := hm_positive_time_halfCell_endpoint I hm t ht
  let c : ℝ := (l + 1 / 2) * tauPP β I.Λ m
  have hscaled := calc
      Real.sqrt (max c t - min c t) * G ≤
          Real.sqrt (tauPP β I.Λ m) * G :=
        mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt hlen) hGnonneg
      _ ≤ Creg * Cprod * Real.sqrt (Cκ * Ctau) *
          epsilon β I.Λ (m - 1) ^ delta β * Theta := by
        simpa [c] using hGain
  exact ⟨l, hc, hc1, hlen, hscaled⟩

/-- Inputs in the form of the diffusivity-recursion estimate plus the unconditional `a_(m-1)
    τPP_m` bound give the
half-cell source gain.  This wrapper removes the scale comparison from the
caller: `amplitude_tauPP_bounds` supplies the coefficient `2⁻²⁵`. -/
theorem hm_positive_time_halfCell_source_gain_from_A5
    {β : ℝ} (I : Ingredients β) {m : ℕ} (hm : 1 ≤ m)
    {κ κprev Creg Cprod Cκ Theta G : ℝ}
    (hκ : 0 < κ) (hκprev : 0 < κprev)
    (hCreg : 0 ≤ Creg) (hCprod : 0 ≤ Cprod)
    (hCκ : 0 ≤ Cκ) (hTheta : 0 ≤ Theta) (hGnonneg : 0 ≤ G)
    (hKprev : κprev ≤ Cκ *
      (a β I.Λ (m - 1) * epsilon β I.Λ (m - 1) ^ (2 + gamma β)))
    (hProduct : a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ ≤ Cprod * κprev)
    (hSourceRate : G ≤ Creg * Theta *
      (a β I.Λ m ^ 2 * epsilon β I.Λ m ^ 4 / κ) *
      (Real.sqrt κprev)⁻¹ *
      epsilon β I.Λ (m - 1) ^ (-(1 + gamma β / 2))) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      ∃ l : ℤ,
        let c := (l + 1 / 2) * tauPP β I.Λ m
        0 < c ∧ c ≤ 1 ∧
          max c t - min c t ≤ tauPP β I.Λ m ∧
          Real.sqrt (max c t - min c t) * G ≤
            Creg * Cprod * Real.sqrt (Cκ * (2 : ℝ) ^ (-25 : ℤ)) *
              epsilon β I.Λ (m - 1) ^ delta β * Theta := by
  have hTauPP := (amplitude_tauPP_bounds I.one_lt_beta I.beta_lt
    I.two_pow_seven_le hm).2
  have hCtau : 0 ≤ (2 : ℝ) ^ (-25 : ℤ) := by positivity
  exact hm_positive_time_halfCell_source_gain I hm hκ hκprev
    hCreg hCprod hCκ hCtau hTheta hGnonneg hKprev hProduct hTauPP hSourceRate

end AVenhance.Infra.Section4
