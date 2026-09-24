/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremC
public import LeanPool.CaffarelliKohnNirenberg.Main.TheoremCPaper
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolutionIntegrable
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.Statements.RegularPoint
public import LeanPool.CaffarelliKohnNirenberg.Statements.SingularSet

/-!
# Theorem C

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Theorem C, paper label `thm:C`; as explained in docs/DESIGN_NOTES.md, it uses Mathlib's
  parabolic Hausdorff measure. -/
theorem caffarelliKohnNirenberg (q : ℝ) (hq : 5 / 2 < q) :
    ∀ (Ω : Set Vec3) (I : Set ℝ) (u : ParabolicPoint → Vec3)
      (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolution Ω I q u Du p f →
      parabolicHausdorffMeasure 1 (SingularSet Ω I u) = 0 :=
by exact CKN.Main.caffarelliKohnNirenbergPaper q hq

end CKN
