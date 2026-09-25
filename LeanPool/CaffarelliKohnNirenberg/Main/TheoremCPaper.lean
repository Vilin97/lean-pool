/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems

/-!
# Theorem CPaper

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Main

/-- The parabolic singular set of a suitable weak solution of `def:sws` has zero
one dimensional Hausdorff measure. -/
theorem caffarelliKohnNirenbergPaper (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
by
  exact CKN.caffarelliKohnNirenberg_paper q hq

end CKN.Main
