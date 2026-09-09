/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualInitialization
public import LeanPool.NavierStokesAndEuler.NavierStokes.ActualCycleExcluded

@[expose] public section

/-!
# The actual fixed geometry for every correction cycle

The numerical data, strip, gauge, and operators below are the ones used by
`ActualInitialization`.  In particular, compatibility with the excluded-alias
estimates is proved independently of the particular and signed wave choices.
-/

noncomputable section

namespace NavierStokes.ActualCycleGeometry

open CorrectionInitialization CorrectionStep WeightedClasses

abbrev Point := ActualInitialization.Point

/-- Initialization supplies all numerical hypotheses of the similarity
estimates, including the actual finite-window common index. -/
noncomputable def similarityData : ActualCycleExcluded.SimilarityData where
  h := ActualPrimary.h
  h_pos := ActualPrimary.outgoing.data.h_pos
  inner := PrimaryTargetBounds.leftRadius ActualPrimary.nominal
  outer := PrimaryTargetBounds.rightRadius ActualPrimary.nominal
  inner_pos := PrimaryTargetBounds.leftRadius_pos ActualPrimary.nominal
  inner_lt_outer := PrimaryTargetBounds.radii_ordered ActualPrimary.nominal
  leftWeight := FinalSlowBase.edgeExponent ActualPrimary.nominal / 4
  rightWeight := 1
  left_pos := div_pos (FinalSlowBase.edgeExponent_pos ActualPrimary.nominal) (by norm_num)
  right_pos := zero_lt_one
  baseScale := 1
  baseScale_ne := one_ne_zero
  region := ActualPrimary.standardRegion
  index := CommonWindow.index ActualPrimary.h
  gap := CommonWindow.gap ActualPrimary.h
  index_lower := CommonWindow.native_le_index_add ActualPrimary.h
    ActualPrimary.outgoing.data.h_pos.le
  index_upper := fun n => (CommonWindow.index_le_native ActualPrimary.h n).trans (Nat.le_add_right
    _ _)
  slow := BaseContextAssembly.slowScale
  slow_one := BaseContextAssembly.one_le_slowScale
  slow_scale := fun _ => le_max_right _ _

theorem strip_eq : similarityData.strip = ActualInitialization.strip := rfl

theorem strip_eq_geometry : similarityData.strip = ActualInitialization.geometry.strip := rfl

/-- The normalization factor is exactly one, so the similarity gauge agrees
with the common reconstruction used by initialization. -/
theorem gauge_eq : similarityData.gauge = ActualPrimary.commonGauge :=
  ActualInitialCoherence.commonGauge_eq_similarity.symm

theorem gauge_eq_geometry : similarityData.gauge = ActualInitialization.geometry.gauge :=
  gauge_eq

theorem region_eq : similarityData.region = ActualInitialization.geometry.region := rfl

theorem inner_eq : similarityData.inner = ActualInitialization.geometry.patch.a := rfl

theorem outer_eq : similarityData.outer = ActualInitialization.geometry.patch.b := rfl

theorem index_eq : similarityData.index = CommonWindow.index ActualPrimary.h := rfl

theorem index_bounds : CommonBaseContext.IndexBounds similarityData.h
    similarityData.index similarityData.gap :=
  CommonWindow.indexBounds ActualPrimary.h ActualPrimary.outgoing.data.h_pos.le

theorem slow_eq : similarityData.slow = BaseContextAssembly.slowScale := rfl

theorem epsilon_eq : similarityData.strip.epsilon = ChartScales.epsilon ActualPrimary.h := rfl

theorem fast_eq (B : ℕ) : (ActualPrimary.commonContext B).operators.fastCoefficient =
    fun n => ChartScales.Tg ^ similarityData.index n *
      ChartScales.Q n ^ (1 + similarityData.h) := rfl

theorem temporal_eq (B : ℕ) : (ActualPrimary.commonContext B).operators.vT =
    (0, (0, TorusInverse.vector .temporal)) := rfl

/-- Changing either wave family leaves the entire similarity certificate
unchanged.  The rank stage is the actual reserved rank construction. -/
theorem compatible {ι : Type} (B : ℕ)
    (particular : ι → ParticularParameters CycleSlow)
    (signed : ι → PeriodizedSignedParameters CyclePoint TorusInverse.Frequency) :
    ActualCycleExcluded.Compatible similarityData
      (CycleParameters.ofGeometry ActualInitialization.geometry ActualPrimary.h
        (CommonWindow.index ActualPrimary.h) ActualInitialization.axial
        particular signed ActualPrimary.rankData)
      (ActualPrimary.commonContext B) where
  gauge := gauge_eq.symm
  strip := strip_eq_geometry.symm
  time := rfl
  index := rfl
  fast := fast_eq B
  temporal := temporal_eq B

/-- The actual operator bounds on precisely the strip in the certificate. -/
theorem operators (B : ℕ) :
    MeanIncrementBounds.OperatorBounds similarityData.strip
      (ActualPrimary.commonContext B).operators ChartScales.kappa :=
  ActualInitialization.operators B

/-- These bounds concern the actual same-profile base in the common context. -/
theorem base_bounds (B : ℕ) :
    MeanIncrementBounds.BaseBounds similarityData.strip (ActualPrimary.commonContext B).base :=
  ActualInitialization.base_bounds B

theorem radius_pos (B : ℕ) (x : Point) (hx : x ∈ similarityData.strip.domain) :
    0 < (ActualPrimary.commonContext B).operators.radius x :=
  ActualInitialization.radius_pos B x hx

theorem strip_time (x : Point) (hx : x ∈ similarityData.strip.domain) : 0 < x.2.1.1 :=
  ActualInitialization.strip_time x hx

end NavierStokes.ActualCycleGeometry
