/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Parabolic Holder Vec On

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open CKN.Foundation.Parabolic


namespace CKN

/-- Vector-valued parabolic Hölder control from paper label `def:holder`. -/
def ParabolicHolderVecOn (U : Set ParabolicPoint) (g : ParabolicPoint → Vec3)
    (γ : ℝ) : Prop :=
  ∃ B K : ℝ, 0 ≤ B ∧ 0 ≤ K ∧
    (∀ z ∈ U, vec3EuclideanNorm (g z) ≤ B) ∧
    (∀ z ∈ U, ∀ w ∈ U,
      vec3EuclideanNorm (g z - g w) ≤ K * parabolicDist z w ^ γ)

end CKN
