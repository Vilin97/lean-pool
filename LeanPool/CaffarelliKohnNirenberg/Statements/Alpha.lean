/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Scaling

/-!
# Alpha

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

/-- The velocity energy quantity α from the manuscript, `eq:alpha-beta`. -/
noncomputable def alpha (u : ParabolicPoint → Vec3) (z : ParabolicPoint) (r : ℝ) : ℝ :=
  (r⁻¹ * (timeSliceEnergyEssSup z.1 z.2 r
      (fun w => vec3EuclideanNorm (u w))).toReal) ^ (1 / 2 : ℝ)

end CKN
