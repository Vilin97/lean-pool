/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSmoothOrbit
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderPaths
import LeanPool.NavierStokesAndEuler.Euler.ClassicalPressureCurl

/-! The actual smooth representative retains the proved compact spatial support of its L² class. -/

@[expose] public section


noncomputable section

namespace EulerCylinderSmoothOrbit

open Set MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport
  EulerLpSupportedSubspace EulerLpCylinderTranslation EulerLpCylinderPaths

variable (period : ℝ) [Fact (0 < period)]

/-- Vanishing outside a closed support region passes from the actual L² class to its smooth
representative. -/
theorem representative_zero_outside (S : Set Space) (hS : MeasurableSet S) (hSc : IsClosed S)
    (u : LiftL2 period) (hu : SmoothOrbit period u) (hs : u ∈ Supported period Space S hS)
    (x : LiftDomain period) (hx : x.1 ∉ S) : representative period u hu x = 0 := by
  have hset : IsClosed (spatialSet period S) := hSc.preimage continuous_fst
  have hout : (representative period u hu) =ᵐ[(liftMeasure period).restrict (spatialSet period S)ᶜ]
      (fun _ => 0) := by
    apply (ae_restrict_iff' hset.measurableSet.compl).2
    filter_upwards [(mem_supportedSpace_ae _ _ _ u).1 hs,representative_ae period u hu] with y hy
        he hnot
    exact he.symm.trans (hy hnot)
  exact Measure.eqOn_open_of_ae_eq hout hset.isOpen_compl
    (smoothField_continuous period _ (representative_smooth period u hu)).continuousOn
    continuous_const.continuousOn hx

/-- The actual topological support is contained in the same closed spatial support. -/
theorem representative_tsupport_subset (S : Set Space) (hS : MeasurableSet S) (hSc : IsClosed S)
    (u : LiftL2 period) (hu : SmoothOrbit period u) (hs : u ∈ Supported period Space S hS) :
    tsupport (representative period u hu) ⊆ spatialSet period S := by
  apply closure_minimal _ (hSc.preimage continuous_fst)
  intro x hx
  by_contra hnot
  exact hx (representative_zero_outside period S hS hSc u hu hs x hnot)

/-- Compact spatial support remains compact after adjoining the periodic angle. -/
theorem representative_hasCompactSupport (S : Set Space) (hS : MeasurableSet S) (hSc : IsCompact S)
    (u : LiftL2 period) (hu : SmoothOrbit period u) (hs : u ∈ Supported period Space S hS) :
    HasCompactSupport (representative period u hu) := by
  have hcompact : IsCompact (spatialSet period S) := by
    have he : spatialSet period S = S ×ˢ (univ : Set (AddCircle period)) := by
      ext x
      simp only [spatialSet,mem_preimage,mem_prod,mem_univ,and_true]
    rw [he]
    exact hSc.prod isCompact_univ
  exact hcompact.of_isClosed_subset (isClosed_tsupport _)
    (representative_tsupport_subset period S hS hSc.isClosed u hu hs)

end EulerCylinderSmoothOrbit
