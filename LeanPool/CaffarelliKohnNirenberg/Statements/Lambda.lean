/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Lambda

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- The force quantity λ from the manuscript, `eq:lambda`. -/
@[expose]
noncomputable def lambda (q : ℝ) (f : ParabolicPoint → Vec3)
    (z : ParabolicPoint) (r : ℝ) : ℝ :=
  r ^ (3 - 5 / q) *
    (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q).toReal ^ (1 / q : ℝ)

end CKN
