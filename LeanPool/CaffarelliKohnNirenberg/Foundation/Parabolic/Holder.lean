/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory Set


noncomputable section

namespace CKN.Foundation.Parabolic

def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α

def HasParabolicHolderRepresentativeOn
    (U : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∃ g : ParabolicPoint → ℝ,
    g =ᵐ[volume.restrict U] f ∧
      ParabolicHolderSeminormLE U g α K

lemma parabolicDist_nonneg (x y : ParabolicPoint) :
    0 ≤ parabolicDist x y := by
  exact (vec3EuclideanNorm_nonneg _).trans (le_max_left _ _)

namespace ParabolicHolderSeminormLE

theorem mono_set {U V : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {α K : ℝ} (h : ParabolicHolderSeminormLE U g α K) (hVU : V ⊆ U) :
    ParabolicHolderSeminormLE V g α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)

end ParabolicHolderSeminormLE

theorem ParabolicHolderSeminormLE.hasRepresentative
    {U : Set ParabolicPoint} {f : ParabolicPoint → ℝ} {α K : ℝ}
    (h : ParabolicHolderSeminormLE U f α K) :
    HasParabolicHolderRepresentativeOn U f α K :=
  ⟨f, Filter.Eventually.of_forall fun _ => rfl, h⟩

end CKN.Foundation.Parabolic
