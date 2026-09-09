/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedPeriodicAssembly
public import LeanPool.NavierStokesAndEuler.NavierStokes.MixedDiagonalSchedule
import LeanPool.NavierStokesAndEuler.NavierStokes.SimilarityApproach

/-!
# Residual estimates for the mixed diagonal sum

The direct angular increments are summed as velocity fields, while the
potential increments are differentiated after cutoff.  Both use the same
scale sequence.  The actual mixed tail is estimated from these two different
operations; it is not identified with the curl of an unspecified potential.

The finite uncut background and residual estimates are explicit inputs from
the correction construction.  The infinite-tail estimates and the resulting
residual decay are proved here.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.MixedDiagonalResidual

open ProblemStatement Set Filter DiagonalResidual ResidualStability
open scoped Topology ContDiff BigOperators

/-- Velocity, defined pointwise by `SolenoidalDiagonal.velocitySum a q A z +
SolenoidalDiagonal.potentialSum a q B z`. -/
def velocity (a : ℕ → ℝ) (q : SpaceTime → ℝ) (A B : ℕ → VelocityField) :
    VelocityField :=
  fun z => SolenoidalDiagonal.velocitySum a q A z +
    SolenoidalDiagonal.potentialSum a q B z

/-- Stage zero remains in every nonempty uncut prefix. -/
def uncutVelocity (A B : ℕ → VelocityField) (J : ℕ) : VelocityField :=
  fun z => SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1)) z +
    DiagonalJetBounds.uncutPrefix B (J + 1) z

/-- Pressure, given by `SolenoidalDiagonal.potentialSum a q P`. -/
def pressure (a : ℕ → ℝ) (q : SpaceTime → ℝ) (P : ℕ → PressureField) :
    PressureField := SolenoidalDiagonal.potentialSum a q P

/-- Residual, defined pointwise by `navierStokesResidual (velocity a q A B) (pressure a q P) z.1
z.2`. -/
def residual (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A B : ℕ → VelocityField) (P : ℕ → PressureField) : VelocityField :=
  fun z => navierStokesResidual (velocity a q A B) (pressure a q P) z.1 z.2

/-- The residual is exactly the nonlinear residual used by the mixed
localization and force construction, including both cross interactions. -/
theorem residual_eq_originalResidual (a : ℕ → ℝ) (q : SpaceTime → ℝ)
    (A B : ℕ → VelocityField) (P : ℕ → PressureField) :
    residual a q A B P = MixedPeriodicAssembly.originalResidual
      (SolenoidalDiagonal.potentialSum a q A)
      (SolenoidalDiagonal.potentialSum a q B)
      (SolenoidalDiagonal.potentialSum a q P) := rfl

theorem velocity_smooth {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U) :
    ContDiffOn ℝ ∞ (velocity a q A B) U :=
  (SolenoidalDiagonal.velocitySum_contDiffOn ha hU hqpos hq hA).add
    (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hqpos hq hB)

/-- Smoothness of the full cut sums suffices. The raw stages need not
be smooth outside the positive-scale domain where they are constructed. -/
theorem velocity_smooth_of_sums {a : ℕ → ℕ} {h : ℝ}
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hs : MixedDiagonalSchedule.ThreeSmoothSums a h A B P) :
    ContDiffOn ℝ ∞ (velocity (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B)
      PhysicalWaveSum.preterminal := by
  intro z hz
  have hmem := PhysicalWaveSum.preterminal_open.mem_nhds hz
  exact ((SpatialCurl.contDiffAt_spatialCurl (hs.potential.contDiffAt hmem)
    (by simp)).add (hs.direct.contDiffAt hmem)).contDiffWithinAt

theorem uncutVelocity_smooth {A B : ℕ → VelocityField} {U : Set SpaceTime}
    (hU : IsOpen U) (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U)
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U) (J : ℕ) :
    ContDiffOn ℝ ∞ (uncutVelocity A B J) U := by
  have hpA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have hcurl : ContDiffOn ℝ ∞
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      (hpA.contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  exact hcurl.add (ContDiffOn.sum (fun j _ => hB j))

/-- One derivative is paid for the potential component only.  The loss
depends on the derivative order, never on the stage number. -/
noncomputable def velocityLoss (LA LB : ℕ → ℝ) (m : ℕ) : ℝ := max (LA (m + 1)) (LB m)

theorem velocity_tail_jetRate {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A B : ℕ → VelocityField} {g LA LB : ℕ → ℝ}
    {U : Set SpaceTime} {l : Filter SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hg : Monotone g)
    (hbA : DiagonalJetBounds.CutStageBounds a q A g LA U)
    (hbB : DiagonalJetBounds.CutStageBounds a q B g LB U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hlq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1)
    (hqzero : Tendsto q l (𝓝 0)) (J m : ℕ) (hm : m + 1 ≤ J + 3) :
    JetRate l q (fun z => velocity a q A B z - uncutVelocity A B J z)
      m (g (J + 1) - velocityLoss LA LB m) := by
  have hAt := (jetRate_diagonal_velocity_tail ha hU hqpos hq hA hg hbA
    hlU hlq hqzero J m hm).weaken hlq
      (sub_le_sub_left (le_max_left (LA (m + 1)) (LB m)) _)
  have hBt := (jetRate_diagonal_tail ha hU hq hB hg hbB
    hlU hlq hqzero J m (by omega)).weaken hlq
      (sub_le_sub_left (le_max_right (LA (m + 1)) (LB m)) _)
  have hpA : ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix A (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hA j)
  have hcurl : ContDiffOn ℝ ∞
      (SpatialCurl.spatialCurl (DiagonalJetBounds.uncutPrefix A (J + 1))) U := by
    intro z hz
    exact (SpatialCurl.contDiffAt_spatialCurl
      (hpA.contDiffAt (hU.mem_nhds hz)) (by simp)).contDiffWithinAt
  have hsum := hAt.add hBt hU hlU
    ((SolenoidalDiagonal.velocitySum_contDiffOn ha hU hqpos hq hA).sub hcurl)
    ((SolenoidalDiagonal.potentialSum_contDiffOn ha hU hqpos hq hB).sub
      (ContDiffOn.sum (fun j _ => hB j)))
  apply hsum.congr_on hU hlU
  intro z hz
  dsimp [velocity, uncutVelocity]
  abel

/-- Every positive power follows by selecting an adequately advanced
finite uncut stage. No one fixed tail is assumed to have all powers. -/
theorem residual_jetRate {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {q : SpaceTime → ℝ} {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LB LP Lbg Lres : ℕ → ℝ} {U : Set SpaceTime} {l : Filter SpaceTime}
    (hU : IsOpen U) (hqpos : ∀ z ∈ U, 0 < q z) (hq : ContDiffOn ℝ ∞ q U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) U)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbA : DiagonalJetBounds.CutStageBounds a q A g LA U)
    (hbB : DiagonalJetBounds.CutStageBounds a q B g LB U)
    (hbP : DiagonalJetBounds.CutStageBounds a q P g LP U)
    (hlU : ∀ᶠ z in l, z ∈ U) (hqzero : Tendsto q l (𝓝 0))
    (hbg : ∀ J m, JetRate l q (uncutVelocity A B J) m (-Lbg m))
    (hres : ∀ J m, JetRate l q
      (fun z => navierStokesResidual (uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (g J - Lres m))
    (m : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    JetRate l q (residual a q A B P) m r := by
  have hlq : ∀ᶠ z in l, 0 < q z ∧ q z ≤ 1 := by
    filter_upwards [hlU, hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with z hz hq1
    exact ⟨hqpos z hz, hq1.le⟩
  have hprefixP (J : ℕ) :
      ContDiffOn ℝ ∞ (DiagonalJetBounds.uncutPrefix P (J + 1)) U :=
    ContDiffOn.sum (fun j _ => hP j)
  apply DiagonalResidual.residual_jetRate_of_stages
    (uStage := uncutVelocity A B)
    (pStage := fun J => DiagonalJetBounds.uncutPrefix P (J + 1))
    (g := g) (Ltail := fun m => max (velocityLoss LA LB m) (LP m))
    hU hlU hlq (velocity_smooth ha hU hqpos hq hA hB)
    (SolenoidalDiagonal.potentialSum_contDiffOn ha hU hqpos hq hP)
    (uncutVelocity_smooth hU hA hB) hprefixP hgtop hbg ?_ ?_ hres m r hr
  · intro J m hm
    apply (velocity_tail_jetRate ha hU hqpos hq hA hB hgmono hbA hbB
      hlU hlq hqzero J m (by omega)).weaken hlq
    exact sub_le_sub (hgmono (Nat.le_succ J)) (le_max_left (velocityLoss LA LB m) (LP m))
  · intro J m hm
    apply (jetRate_diagonal_tail ha hU hq hP hgmono hbP hlU hlq hqzero J m
      (by omega)).weaken hlq
    exact sub_le_sub (hgmono (Nat.le_succ J)) (le_max_right (velocityLoss LA LB m) (LP m))

/-- The actual physical scale has its joint zero limit at the origin.
Thus the finite-stage construction inputs give the tensor limits needed
by `MixedPeriodicAssembly`, rather than postulating those limits. -/
theorem physical_vanishingJointJets {h : ℝ} (hh : 0 < h) (hh1 : h < 1 / 2)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    {g LA LB LP Lbg Lres : ℕ → ℝ} {U : Set SpaceTime}
    (hU : IsOpen U) (hUp : U ⊆ PhysicalWaveSum.preterminal)
    (hlU : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U)
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) U) (hB : ∀ j, ContDiffOn ℝ ∞ (B j) U)
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) U)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbA : DiagonalJetBounds.CutStageBounds a (PhysicalWaveSum.physicalQ h) A g LA U)
    (hbB : DiagonalJetBounds.CutStageBounds a (PhysicalWaveSum.physicalQ h) B g LB U)
    (hbP : DiagonalJetBounds.CutStageBounds a (PhysicalWaveSum.physicalQ h) P g LP U)
    (hbg : ∀ J m, JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h) (uncutVelocity A B J) m (-Lbg m))
    (hres : ∀ J m, JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h)
      (fun z => navierStokesResidual (uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (g J - Lres m)) :
    JointResidualLimits.VanishingJointJets (residual a (PhysicalWaveSum.physicalQ h) A B P) := by
  have hqpos : ∀ z ∈ U, 0 < PhysicalWaveSum.physicalQ h z :=
    fun z hz => PhysicalWaveSum.physicalQ_pos hh hh1 (hUp hz)
  have hq : ContDiffOn ℝ ∞ (PhysicalWaveSum.physicalQ h) U :=
    fun z hz => (PhysicalWaveSum.physicalQ_smoothAt hh hh1 (hUp hz)).contDiffWithinAt
  have hqzero := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  intro m
  exact SimilarityApproach.jet_tendsto_zero
    (residual_jetRate ha hU hqpos hq hA hB hP hgmono hgtop hbA hbB hbP
      hlU hqzero hbg hres m 1 zero_le_one) hqzero

/-- A single schedule is selected from the three genuine raw estimates.
The resulting mixed residual has joint zero jets. All raw fields are used
only on their stated positive-scale domain, and stage zero is retained. -/
theorem exists_physical_schedule_residual_zero {h qbig : ℝ}
    (hh : 0 < h) (hh1 : h < 1 / 2) (hqbig : 0 < qbig)
    {S : Set SpaceTime} (hSopen : IsOpen S) (hS : S ⊆ PhysicalWaveSum.preterminal)
    (hlS : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ S)
    {A B : ℕ → VelocityField} {P : ℕ → PressureField}
    (hA : ∀ j, ContDiffOn ℝ ∞ (A j) (CutStageEstimates.physicalSublevel h qbig))
    (hB : ∀ j, ContDiffOn ℝ ∞ (B j) (CutStageEstimates.physicalSublevel h qbig))
    (hP : ∀ j, ContDiffOn ℝ ∞ (P j) (CutStageEstimates.physicalSublevel h qbig))
    (g LA LB LP Lbg Lres : ℕ → ℝ) (CA CB CP pA pB pP : ℕ → ℕ → ℝ)
    (rawA : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) A g LA CA pA
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawB : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) B g LB CB pB
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (rawP : CutStageEstimates.RawStageBounds (PhysicalWaveSum.physicalQ h) P g LP CP pP
      (S ∩ CutStageEstimates.physicalSublevel h qbig))
    (hg0 : 0 ≤ g 0) (hg : ∀ j, 1 ≤ j → 0 < g j)
    (hgmono : Monotone g) (hgtop : Tendsto g atTop atTop)
    (hbg : ∀ J m, JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h) (uncutVelocity A B J) m (-Lbg m))
    (hres : ∀ J m, JetRate (𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)))
      (PhysicalWaveSum.physicalQ h)
      (fun z => navierStokesResidual (uncutVelocity A B J)
        (DiagonalJetBounds.uncutPrefix P (J + 1)) z.1 z.2) m (g J - Lres m))
    (lower : ℕ) :
    ∃ a : ℕ → ℕ, lower ≤ a 0 ∧ (∀ j, 0 < a j) ∧
      (∀ j, 2 * a j ≤ a (j + 1)) ∧ StrictMono a ∧
      Tendsto (fun j => (a j : ℝ)) atTop atTop ∧
      (∀ j, 1 / (a j : ℝ) < qbig) ∧
      MixedDiagonalSchedule.ThreeCutBounds a h A B P (fun j => g j / 2)
        (MixedDiagonalSchedule.commonLoss LA LB LP) S ∧
      MixedDiagonalSchedule.ThreeSmoothSums a h A B P ∧
      JointResidualLimits.VanishingJointJets
        (residual (fun j => (a j : ℝ)) (PhysicalWaveSum.physicalQ h) A B P) := by
  obtain ⟨a, hal, hap, had, ham, hat, hrecip, hb, hs⟩ :=
    MixedDiagonalSchedule.exists_three_component_local_schedule hh hh1 hqbig hS
      hA hB hP g LA LB LP CA CB CP pA pB pP rawA rawB rawP hg lower
  refine ⟨a, hal, hap, had, ham, hat, hrecip, hb, hs, ?_⟩
  let U := S ∩ CutStageEstimates.physicalSublevel h qbig
  have hU : IsOpen U := hSopen.inter (CutStageEstimates.physicalSublevel_open hh hh1 qbig)
  have hUp : U ⊆ PhysicalWaveSum.preterminal := fun _ hx => hS hx.1
  have hqzero := AnnularEndpoint.physicalQ_tendsto_zero hh hh1 (x := (0 : Space)) rfl
  have hlU : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)), z ∈ U := by
    filter_upwards [hlS, hqzero.eventually (gt_mem_nhds hqbig)] with z hz hqz
    exact ⟨hz, hS hz, hqz⟩
  have hlq : ∀ᶠ z in 𝓝[SpacetimeEndpoint.openPast 1] (1, (0 : Space)),
      0 < PhysicalWaveSum.physicalQ h z ∧ PhysicalWaveSum.physicalQ h z ≤ 1 := by
    filter_upwards [hlS, hqzero.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
      with z hz hqz
    exact ⟨PhysicalWaveSum.physicalQ_pos hh hh1 (hS hz), hqz.le⟩
  have hhalfmono : Monotone (fun j => g j / 2) := by
    intro i j hij
    exact div_le_div_of_nonneg_right (hgmono hij) (by norm_num)
  have hhalftop : Tendsto (fun j => g j / 2) atTop atTop := by
    apply tendsto_atTop.2
    intro r
    filter_upwards [hgtop.eventually (eventually_ge_atTop (2 * r))] with j hj
    linarith
  have hnonneg (J : ℕ) : 0 ≤ g J := hg0.trans (hgmono (Nat.zero_le J))
  apply physical_vanishingJointJets (Lbg := Lbg) (Lres := Lres) hh hh1 hat hU hUp hlU
    (fun j => (hA j).mono inter_subset_right)
    (fun j => (hB j).mono inter_subset_right)
    (fun j => (hP j).mono inter_subset_right) hhalfmono hhalftop
    (fun j hj m hm z hz => hb.potential j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.direct j hj m hm z hz.1)
    (fun j hj m hm z hz => hb.pressure j hj m hm z hz.1) hbg
  intro J m
  exact (hres J m).weaken hlq (by linarith [hnonneg J])

end NavierStokes.MixedDiagonalResidual
