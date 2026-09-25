/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Continuity.DenseTimeContinuousExtension
public import Mathlib.Topology.ContinuousMap.CompactlySupported


/-!
# Integrals of finite dense-time marginals of a path measure

Integrating a compactly supported test against the finite dense-time marginal of a measure on
continuous-path space is integrating the composed test against the measure itself.  This is a
change-of-variables identity with no probabilistic content.
-/

@[expose] public section

open MeasureTheory
open scoped CompactlySupported

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [TopologicalSpace alpha] [SecondCountableTopology alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- A compactly supported test integrated against a finite dense-time marginal of a path measure
is the composed test integrated against the path measure. -/
theorem integral_map_denseRestriction_map_restrict
    (nu : Measure (ContinuousPath alpha)) (J : Finset DenseTime) (f : C_c(J → alpha, ℝ)) :
    ∫ z, f z ∂((nu.map denseRestriction).map J.restrict) =
      ∫ omega, f (J.restrict (denseRestriction omega)) ∂nu := by
  have hdense := measurable_denseRestriction (alpha := alpha)
  have hrestrict := Finset.measurable_restrict (X := fun _ ↦ alpha) J
  rw [Measure.map_map hrestrict hdense]
  exact integral_map (hrestrict.comp hdense).aemeasurable
    f.continuous.stronglyMeasurable.aestronglyMeasurable

end ContinuousPath
end MarkovProcess
