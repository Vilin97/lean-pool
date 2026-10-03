/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeInitialDefectRightAssembly
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! Exact right-limit initial error at positive abstract amplitude. The zero
amplitude branch is handled separately using actual zero-data solutions. -/

@[expose] public section

noncomputable section
open MeasureTheory Filter Topology Homogenization AVenhance
open AVenhance.Infra.Section5 AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

/-- The actual error, rather than the ansatz-to-datum norm, satisfies the exact
initial-layer contract after absorbing a positive right-limit slack. -/
theorem relative_initialLayer_of_positive_amplitude {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ)
    {m : ℕ} (hm : 1 ≤ m) {κ ν : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} {θm θprev : ℝ → Vec 2 → ℝ} {T : ℕ → ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel (Φ m)) κ (fun _ _ => 0) g θm)
    (hp : IsClassicalSol (streamVel (Φ (m - 1))) ν (fun _ _ => 0) g θprev)
    (hT : I.IsTIterates hΦ m κ ν g θprev T)
    {B D S : ℝ} (hS : 0 < S)
    (hCorrector : Real.sqrt (l2NormSq (fun x =>
      ∑' k : ℤ, ansatzSummand I hΦ m κ (T (Nstar β)) k 0 x)) ≤ B * S)
    (hHm : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (I.Hm hΦ m κ (T (Nstar β)) s)) ≤ D * S) :
    ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (fun x => θm s x - I.ansatz hΦ m κ (T (Nstar β)) s x)) ≤
        (B + D + 1) * S := by
  have hlim := relative_classical_initial_L2_tendsto hu
  have hsmall := hlim.eventually (eventually_lt_nhds (half_pos hS))
  have hansatz := relative_initial_defect_from_right_Hm_bound I hΦ hm hκ hp hT
    hCorrector hHm (S / 2) (half_pos hS)
  have hg : Continuous g := by
    have hzero : θm 0 = g := funext hu.2.2.1
    simpa only [← hzero] using
      (AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hu.1 (t := 0) le_rfl).continuous
  have hsol := tIterates_classicalSol hT
  filter_upwards [hsmall, hansatz, self_mem_nhdsWithin] with s hs ha hspos
  have hθcont := (AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hu.1 hspos.le).continuous
  have hUcont := AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hsol.1 hspos.le
  have hHcont := Hm_slice_contDiff_pos I hΦ hm hκ hp hT hspos
  have hAcont := (ansatz_slice_contDiff I hΦ m κ hUcont hHcont).continuous
  have htri := sqrt_l2NormSq_add_le
    (memL2On_unitCube_of_continuous (hθcont.sub hg))
    (memL2On_unitCube_of_continuous (hg.sub hAcont))
  have hfun : (fun x => (θm s x - g x) + (g x - I.ansatz hΦ m κ (T (Nstar β)) s x)) =
      fun x => θm s x - I.ansatz hΦ m κ (T (Nstar β)) s x := by funext x; ring
  have hnorm : l2NormSq (fun x => g x - I.ansatz hΦ m κ (T (Nstar β)) s x) =
      l2NormSq (fun x => I.ansatz hΦ m κ (T (Nstar β)) s x - g x) := by
    unfold l2NormSq
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by ring
  change Real.sqrt (l2NormSq (fun x => (θm s x - g x) +
    (g x - I.ansatz hΦ m κ (T (Nstar β)) s x))) ≤
      Real.sqrt (l2NormSq (fun x => θm s x - g x)) +
      Real.sqrt (l2NormSq (fun x => g x - I.ansatz hΦ m κ (T (Nstar β)) s x)) at htri
  rw [hfun, hnorm] at htri
  change Real.sqrt (l2NormSq (fun x => θm s x - g x)) < S / 2 at hs
  linarith only [htri, hs, ha]

end AVenhance.Infra.Section5.RelativeError
