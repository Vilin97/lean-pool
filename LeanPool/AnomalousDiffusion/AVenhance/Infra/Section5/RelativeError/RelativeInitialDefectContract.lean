/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectZeroData

/-! Exact relative initial-layer contract from the two separately proved
corrector and positive-time Hm estimates, including zero dissipation amplitude. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- Assembly of the literal relative initial-layer contract. The component
estimates remain explicit, distinct from the family-level producer. -/
theorem relative_initialLayer_from_estimates {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ ν : ℝ} (hκ : 0 < κ) (hν : 0 < ν)
    {g : Vec 2 → ℝ} {θm θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel (Φ m)) κ (fun _ _ => 0) g θm)
    (hp : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κ ν g θprev T) (hmean : MeanZeroOn unitCube g)
    {Ccorr CH : ℝ}
    (hCorrector : Real.sqrt (l2NormSq (fun x =>
      ∑' k : ℤ, ansatzSummand I hΦ m κ (T (Nstar β)) k 0 x)) ≤
      Ccorr * epsilon β I.Λ (m - 1) ^ delta β *
        (Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x))))
    (hHm : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤
      CH * epsilon β I.Λ (m - 1) ^ delta β *
        (Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x)))) :
    InitialLayerContract I hΦ m κ θm T (Ccorr + CH + 1)
      (Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x))) := by
  let S := Real.sqrt ν * Real.sqrt (spaceTimeGradNormSq (fun t x => spaceGrad (θprev t) x))
  have hS : 0 ≤ S := by dsimp [S]; positivity
  by_cases hSpos : 0 < S
  · have he := Infra.Cutoff.epsilon_pos I.one_lt_beta I.beta_lt I.two_pow_seven_le (m := m - 1)
    have hcorrector' : Real.sqrt (l2NormSq (fun x =>
        ∑' k : ℤ, ansatzSummand I hΦ m κ (T (Nstar β)) k 0 x)) ≤
        Ccorr * (epsilon β I.Λ (m - 1) ^ delta β * S) := by
      simpa only [S, mul_assoc] using hCorrector
    have hHm' : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤
          CH * (epsilon β I.Λ (m - 1) ^ delta β * S) := by
      simpa only [S, mul_assoc] using hHm
    have hpos : 0 < epsilon β I.Λ (m - 1) ^ delta β * S :=
      mul_pos (Real.rpow_pos_of_pos he _) hSpos
    simpa only [InitialLayerContract, S, mul_assoc] using
      relative_initialLayer_of_positive_amplitude I hΦ hm hκ hu hp hT hpos hcorrector' hHm'
  · have hSzero : S = 0 := le_antisymm (le_of_not_gt hSpos) hS
    have hg := relative_initial_datum_zero_of_amplitude_zero (hΦ.adm_pred m) hν hp hmean hSzero
    have hHmzero : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤ 0 := by
      change (∀ᶠ s in 𝓝[>] (0 : ℝ), _ ≤ CH * epsilon β I.Λ (m - 1) ^ delta β * S) at hHm
      simpa only [hSzero, mul_zero] using hHm
    have hzero := relative_initial_defect_zero_of_zero_data I hΦ hκ hν hu hp hT hg hHmzero
    change ∀ᶠ s in 𝓝[>] (0 : ℝ), _ ≤ (Ccorr + CH + 1) * epsilon β I.Λ (m - 1) ^ delta β * S
    filter_upwards [hzero] with s hs
    rw [hs, hSzero, mul_zero]

end AVenhance.Infra.Section5.RelativeError
