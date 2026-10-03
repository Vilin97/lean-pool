/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.RelativeError.RelativeResidual
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.Estimate
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.Energy.AnsatzRegularity
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIEnergyIoi
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.PartIAnsatzRegularityIoi

/-! Forced classical energy with relative initial defect and residual, on open time.

The comparison field `v` (the ansatz) is only required to be regular for `t > 0`, and the
initial defect is taken from the right (`s → 0⁺`, `Integration.InitialLayerContract`): the
ansatz at `t = 0` reads the negative-time extension of `T` through the two-sided time derivative of
`Amnr`, so `v 0` is not a meaningful datum.  The energy estimate is
`Integration.forced_energy_estimate_Ioi`. -/

@[expose] public section

noncomputable section
open scoped ContDiff ENNReal
open Filter Topology
open Homogenization MeasureTheory AVenhance AVenhance.Infra.Section5
open AVenhance.Infra.Section5.Integration
namespace AVenhance.Infra.Section5.RelativeError

theorem relative_forced_energy_estimate {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) {κ : ℝ} (hκ : 0 < κ)
    {g : Vec 2 → ℝ} {u v : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel φ) κ (fun _ _ => 0) g u)
    (hv : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => v p.1 p.2) (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hvs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvp : ∀ t, 0 < t → IsZ2Periodic (v t))
    {Ci Cr ε δ S : ℝ} (hCr : 0 ≤ Cr) (hε : 0 < ε) (hS : 0 ≤ S)
    (hInitial : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (fun x => u s x - v s x)) ≤ Ci * ε ^ δ * S)
    (hResidual : timeHMinusOneNorm (fun s x => advDiffOp (streamVel φ) κ v s x) ≤
      ENNReal.ofReal (Cr * Real.sqrt κ * ε ^ δ * S)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => u t x - v t x)) +
        Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (u s) x - spaceGrad (v s) x)) ≤
      (2 * (Ci + Cr)) * ε ^ δ * S := by
  obtain ⟨hfin, hr⟩ := relative_residual_finite_and_normalized hκ hCr hε hS hResidual
  intro t ht
  have h := forced_energy_estimate_Ioi hφ hκ hu hv hvs hvp hfin hInitial t ht
  have hb := add_le_add (le_refl (Ci * ε ^ δ * S)) hr
  exact h.trans ((mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 2)).trans_eq
    (by ring))

/-- Actual ansatz specialization, with joint and slice regularity of the ansatz discharged on
`(0,∞) × ℝ²` by the existing ansatz lemmas from regularity of `T` (up to `t = 0`) and of `HTilde_m`
(for `t > 0` only). -/
theorem relative_ansatz_error {β : ℝ} (I : Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : IsStreamSeq I Φ) (m : ℕ)
    {κ : ℝ} (hκ : 0 < κ) {g : Vec 2 → ℝ} {u T : ℝ → Vec 2 → ℝ}
    (hu : IsClassicalSol (streamVel (Φ m)) κ (fun _ _ => 0) g u)
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hTs : ∀ t, 0 ≤ t → ContDiff ℝ (⊤ : ℕ∞) (T t))
    (hTp : ∀ t, 0 ≤ t → IsZ2Periodic (T t))
    (hH : ContDiffOn ℝ 2 (fun p : ℝ × Vec 2 => I.Hm hΦ m κ T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ))
    (hHs : ∀ t, 0 < t → ContDiff ℝ (⊤ : ℕ∞) (I.Hm hΦ m κ T t))
    (hHp : ∀ t, 0 < t → IsZ2Periodic (I.Hm hΦ m κ T t))
    {Ci Cr ε δ S : ℝ} (hCr : 0 ≤ Cr) (hε : 0 < ε) (hS : 0 ≤ S)
    (hInitial : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      Real.sqrt (l2NormSq (fun x => u s x - I.ansatz hΦ m κ T s x)) ≤ Ci * ε ^ δ * S)
    (hResidual : timeHMinusOneNorm
      (fun s x => advDiffOp (streamVel (Φ m)) κ (I.ansatz hΦ m κ T) s x) ≤
      ENNReal.ofReal (Cr * Real.sqrt κ * ε ^ δ * S)) :
    ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Real.sqrt (l2NormSq (fun x => u t x - I.ansatz hΦ m κ T t x)) +
        Real.sqrt κ * Real.sqrt (spaceTimeGradNormSq (fun s x =>
          spaceGrad (u s) x - spaceGrad (I.ansatz hΦ m κ T s) x)) ≤
      (2 * (Ci + Cr)) * ε ^ δ * S := by
  have hTo : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => T p.1 p.2)
      (Set.Ioi (0 : ℝ) ×ˢ Set.univ) :=
    hT.mono (Set.prod_mono Set.Ioi_subset_Ici_self le_rfl)
  exact relative_forced_energy_estimate (by simpa using hΦ.adm_pred (m + 1)) hκ hu
    (ansatz_contDiffOn_two_Ioi I hΦ m κ hTo hH)
    (fun t ht => ansatz_slice_contDiff I hΦ m κ (hTs t ht.le) (hHs t ht))
    (fun t ht => ansatz_periodic I hΦ m κ ((hTs t ht.le).of_le (by simp))
      (hTp t ht.le) (hHp t ht)) hCr hε hS hInitial hResidual

end AVenhance.Infra.Section5.RelativeError
