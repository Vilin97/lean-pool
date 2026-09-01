/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.PreparationUniqueness
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.PublicExistence

/-!
# Classical complex-analytic Weierstrass preparation

This module assembles the general analytic existence construction and its full
germ uniqueness theorem into the exact independently frozen public result.
-/

open Filter
open scoped BigOperators Topology


namespace ClassicalComplexWPT

/--
Classical complex-analytic Weierstrass preparation at the origin, including
existence and uniqueness of every coefficient germ and of the unit germ. The
statement includes `n = 0` and `d = 0`.
-/
theorem classicalComplexWeierstrassPreparation
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by
  obtain ⟨a, u, hprep⟩ := exists_isWeierstrassPreparation hf horder
  exact ⟨a, u, hprep, fun _ _ hprep' ↦
    isWeierstrassPreparation_unique hprep hprep'⟩

/--
Explicit-neighborhood form of preparation: the same witnesses factor `f`
pointwise on an open neighborhood of the origin, throughout which the unit is
nonzero.
-/
theorem exists_open_preparation_neighborhood
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ) (s : Set (Ambient n)),
      IsWeierstrassPreparation f d a u ∧
      IsOpen s ∧ (0 : Ambient n) ∈ s ∧
      (∀ x ∈ s, u x ≠ 0) ∧
      ∀ x ∈ s, f x = u x * preparedPolynomial d a x := by
  obtain ⟨a, u, hprep⟩ := exists_isWeierstrassPreparation hf horder
  have hunit : ∀ᶠ x : Ambient n in 𝓝 0, u x ≠ 0 :=
    hprep.2.2.1.continuousAt.eventually_ne hprep.2.2.2.1
  have hfactor : ∀ᶠ x : Ambient n in 𝓝 0,
      f x = u x * preparedPolynomial d a x := hprep.2.2.2.2
  obtain ⟨s, hs, hsOpen, hs0⟩ := mem_nhds_iff.mp (hunit.and hfactor)
  refine ⟨a, u, s, hprep, hsOpen, hs0, ?_, ?_⟩
  · intro x hx
    exact (hs hx).1
  · intro x hx
    exact (hs hx).2

end ClassicalComplexWPT
