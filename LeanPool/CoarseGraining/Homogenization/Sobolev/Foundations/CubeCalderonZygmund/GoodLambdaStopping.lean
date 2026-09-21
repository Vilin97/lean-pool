/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.StoppingRadius
import Mathlib.MeasureTheory.Covering.DensityTheorem

/-! # Good Lambda Stopping -/

namespace Homogenization

open scoped ENNReal NNReal BigOperators Topology
open Filter MeasureTheory Set

noncomputable section

namespace CubeCalderonZygmund

/-!
# Step-1 stopping radii for the good-`λ` argument

This module packages the local energy whose exact stopping radii will feed the
Vitali selection in the cube Calderón--Zygmund argument.  It does not use a
comparison estimate, a tail estimate, or a final good-`λ` inequality.
-/

/-- The combined normalized local `L²` energy used in the good-`λ` stopping
construction.  The square root is taken after adding the two squared energies;
this is the form for which a stopping identity at level `lambda` gives the
exact weighted-mass identity used in the level-set split. -/
def goodLambdaCombinedEnergy {d : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ) (x : Vec d) (r : ℝ) : ℝ :=
  Real.sqrt (closedBallL2Energy f x r + (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r)

theorem goodLambdaCombinedEnergy_nonneg {d : ℕ} {F G : Type*}
    [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ) (x : Vec d) (r : ℝ) :
    0 ≤ goodLambdaCombinedEnergy f g ε x r := by
  unfold goodLambdaCombinedEnergy
  exact Real.sqrt_nonneg _

/-- The combined normalized local energy is continuous on positive radii when
both squared data fields are integrable. -/
theorem continuousOn_goodLambdaCombinedEnergy {d : ℕ} [NeZero d]
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ)
    (hf : Integrable (fun y => ‖f y‖ ^ 2) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ 2) volume) (x : Vec d) :
    ContinuousOn (fun r => goodLambdaCombinedEnergy f g ε x r) (Ioi 0) := by
  have hsum_cont : ContinuousOn
      (fun r => closedBallL2Energy f x r + (ε⁻¹) ^ (2 : ℕ) * closedBallL2Energy g x r)
        (Ioi 0) :=
    (continuousOn_closedBallL2Energy f hf x).add
      (continuousOn_const.mul (continuousOn_closedBallL2Energy g hg x))
  exact Real.continuous_sqrt.comp_continuousOn hsum_cont

/-- Lebesgue differentiation for the normalized sup-metric closed-ball
average.  This is the input that identifies the small-radius energy with its
pointwise value almost everywhere. -/
theorem ae_tendsto_closedBallAverage_nhdsGT {d : ℕ}
    (h : Vec d → ℝ) (hh : Integrable h volume) :
    ∀ᵐ x ∂volume, Tendsto (fun r => closedBallAverage x r h) (𝓝[>] 0) (𝓝 (h x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (μ := volume)
    hh.locallyIntegrable (0 : ℝ)] with x hx
  have hraw := hx (fun _ : ℝ => x) id tendsto_id (Eventually.of_forall fun r => by simp)
  apply hraw.congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (closedBallAverage_eq_setAverage x hr.le h).symm

/-- Integrable square data has the expected almost-everywhere small-radius
limit for the normalized local `L²` energy. -/
theorem ae_tendsto_closedBallL2Energy_nhdsGT {d : ℕ} {F : Type*}
    [NormedAddCommGroup F] (u : Vec d → F)
    (hu : Integrable (fun y => ‖u y‖ ^ 2) volume) :
    ∀ᵐ x ∂volume,
      Tendsto (fun r => closedBallL2Energy u x r) (𝓝[>] 0) (𝓝 (‖u x‖ ^ 2)) := by
  simpa only [closedBallL2Energy] using
    ae_tendsto_closedBallAverage_nhdsGT (fun y => ‖u y‖ ^ 2) hu

/-- The combined source energy converges almost everywhere at small radii to
the corresponding pointwise combined energy. -/
theorem ae_tendsto_goodLambdaCombinedEnergy_nhdsGT {d : ℕ}
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ)
    (hf : Integrable (fun y => ‖f y‖ ^ 2) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ 2) volume) :
    ∀ᵐ x ∂volume, Tendsto (fun r => goodLambdaCombinedEnergy f g ε x r) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖f x‖ ^ 2 + (ε⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2))) := by
  filter_upwards [ae_tendsto_closedBallL2Energy_nhdsGT f hf,
    ae_tendsto_closedBallL2Energy_nhdsGT g hg] with x hfx hgx
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (hfx.add (tendsto_const_nhds.mul hgx))

/-- A positive-radius limit above the level and one large radius below it
produce an exact last stopping radius.  The small positive starting radius is
obtained internally from the one-sided limit. -/
theorem exists_stoppingRadius_of_tendsto_nhdsGT {E : ℝ → ℝ} {pointEnergy level R : ℝ}
    (hR : 0 < R) (hE : ContinuousOn E (Ioi 0))
    (hlimit : Tendsto E (𝓝[>] 0) (𝓝 pointEnergy))
    (hpoint : level < pointEnergy) (hlarge : E R ≤ level) :
    ∃ r, 0 < r ∧ r ≤ R ∧ E r = level ∧ ∀ s ∈ Icc r R, E s ≤ level := by
  have heventual : ∀ᶠ a in 𝓝[>] (0 : ℝ), level < E a :=
    hlimit.eventually (eventually_gt_nhds hpoint)
  obtain ⟨a, ha, haIoo⟩ := (heventual.and (Ioo_mem_nhdsGT hR)).exists
  obtain ⟨r, hrIcc, hrEq, hrLast⟩ :=
    exists_last_crossing_of_continuousOn haIoo.2.le
      (hE.mono fun s hs => haIoo.1.trans_le hs.1) ha hlarge
  exact ⟨r, haIoo.1.trans_le hrIcc.1, hrIcc.2, hrEq, hrLast⟩

/-- The stopping-radius certificate specialized to the combined local energy.
For almost every centre, its limit hypothesis is supplied by
`ae_tendsto_goodLambdaCombinedEnergy_nhdsGT`. -/
theorem exists_stoppingRadius_goodLambdaCombinedEnergy {d : ℕ} [NeZero d]
    {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    (f : Vec d → F) (g : Vec d → G) (ε : ℝ)
    (hf : Integrable (fun y => ‖f y‖ ^ 2) volume)
    (hg : Integrable (fun y => ‖g y‖ ^ 2) volume) (x : Vec d)
    {level R : ℝ} (hR : 0 < R)
    (hlimit : Tendsto (fun r => goodLambdaCombinedEnergy f g ε x r) (𝓝[>] 0)
      (𝓝 (Real.sqrt (‖f x‖ ^ 2 + (ε⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2))))
    (hpoint : level < Real.sqrt (‖f x‖ ^ 2 + (ε⁻¹) ^ (2 : ℕ) * ‖g x‖ ^ 2))
    (hlarge : goodLambdaCombinedEnergy f g ε x R ≤ level) :
    ∃ r, 0 < r ∧ r ≤ R ∧ goodLambdaCombinedEnergy f g ε x r = level ∧
      ∀ s ∈ Icc r R, goodLambdaCombinedEnergy f g ε x s ≤ level :=
  exists_stoppingRadius_of_tendsto_nhdsGT hR
    (continuousOn_goodLambdaCombinedEnergy f g ε hf hg x) hlimit hpoint hlarge

end CubeCalderonZygmund

end

end Homogenization
