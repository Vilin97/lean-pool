/-
Copyright (c) 2026 KT. Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: KT. Wu
-/
/-
  Bicausal Optimal Transport — Bellman Recursion (T=1)
  Formally verified in Lean 4 + Mathlib.

  Main result: bellman_value_eq (Value Representation Theorem)

  Structure:
    Defs.lean                              — definitions
    Proposition1.lean                      — bicausal ↔ kernel decomposition
    LowerBound.lean                        — Step 2: ∫V₀ ≤ totalCost
    UpperBound.lean                        — Step 3: ε-optimal construction
    ValueRepresentation.lean               — Step 4: equality (main theorem)
    Existence.lean                         — Step 5: optimal coupling exists
    DescriptiveSetTheory/
      Tree.lean                            — Jankov–von Neumann uniformization (Kechris 18.1)
      JankovVonNeumann.lean                — ε-optimal selection
      AnalyticSigmaAlgebra.lean            — σ(Σ₁¹), analytical measurability
      LowerSemianalytic.lean               — lower semianalytic functions (BS 7.21, 7.47)
      Capacitability.lean                  — Choquet capacitability (Kechris 30.13, BS 7.42)
      KernelIntegral.lean                  — kernel integration of l.s.a. functions (BS 7.48)
    AxiomsAudit.lean                       — #print axioms for every theorem

  Status: 0 error, 0 warning, 0 sorry, 0 custom axioms project-wide
          (machine-checked: every audited theorem depends only on
           [propext, Classical.choice, Quot.sound])
-/
import LeanPool.BicausalOT.BicausalOT.Defs
import LeanPool.BicausalOT.BicausalOT.Proposition1
import LeanPool.BicausalOT.BicausalOT.LowerBound
import LeanPool.BicausalOT.BicausalOT.UpperBound
import LeanPool.BicausalOT.BicausalOT.ValueRepresentation
import LeanPool.BicausalOT.BicausalOT.Existence

/-!
# BicausalOT

Supporting results for bicausal optimal transport and measurable selection.
-/
