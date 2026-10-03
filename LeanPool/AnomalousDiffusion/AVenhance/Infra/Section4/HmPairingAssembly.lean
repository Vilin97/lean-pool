/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmPairingEstimates
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.HmSourcePairing
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.DmBounds

/-! Hm flux identities and source bridges used by the positive-time
pairing assembler. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Homogenization
open AVenhance.Infra.Ergodic AVenhance.Infra.Section5

namespace AVenhance.Infra.Section4

/-- The `sourceErrorD` vector field is definitionally the `d_m`
source split used by the Section 4 scale estimate. -/
theorem sourceErrorD_eq_dmFrozenSource {β : ℝ}
    (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) :
    (fun z : ℝ × Vec 2 => sourceErrorD I hΦ m κ T z.1 z.2) =
      dmFrozenSource I hΦ m κ T
        (fun z => hmFrozenDFirstFlux I hΦ m κ T z.1 z.2) := by
  funext z i
  simp [AVenhance.Infra.Section5.sourceErrorD, dmFrozenSource,
    hmFrozenDFirstFlux, dmFrozenTailTerm, Finset.sum_apply]

/-- Convert the finite source estimate into the exact `d_m` field used
by the moving-flow pairing FTC. -/
theorem sourceErrorD_eLpNorm_le_of_dmFrozenSource
    {β : ℝ} (I : AVenhance.Ingredients β)
    {Φ : ℕ → ℝ → Vec 2 → ℝ} (hΦ : AVenhance.IsStreamSeq I Φ)
    (m : ℕ) (κ : ℝ) (T : ℝ → Vec 2 → ℝ) {B : ℝ}
    (hsource : eLpNorm
      (dmFrozenSource I hΦ m κ T
        (fun z => hmFrozenDFirstFlux I hΦ m κ T z.1 z.2)) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal B) :
    eLpNorm (fun z : ℝ × Vec 2 =>
      sourceErrorD I hΦ m κ T z.1 z.2) 2
      (volume.restrict AVenhance.timeCube) ≤ ENNReal.ofReal B := by
  rw [sourceErrorD_eq_dmFrozenSource I hΦ m κ T]
  exact hsource

end AVenhance.Infra.Section4

end
