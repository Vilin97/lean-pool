/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Parabolic Holder Vec Norm LE

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open CKN.Foundation.Parabolic


namespace CKN

/-- A bounded vector-valued parabolic Hölder norm built from paper label `def:holder`. -/
def ParabolicHolderVecNormLE (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ C : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧ B + K ≤ C ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

end CKN
