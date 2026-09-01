/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
import LeanPool.Rado.Surface.Assembly

/-!
# Radó's theorem: Riemann surfaces are second countable

Target (lean-eval `rado_riemannSurface`, pure Mathlib): a connected Hausdorff
topological space with a 1-dimensional complex manifold structure has second
countable topology.

This is the exact statement of
<https://lean-lang.org/eval/problems/rado_riemannSurface/>
(submitter: Junyan Xu; source: Hubbard, *Teichmüller theory*, Vol. 1, §1.3).

The real-manifold analogue is false (Prüfer surface, long line), so the proof
must use the complex structure in an essential way.
-/

theorem rado_riemannSurface {X : Type*} [TopologicalSpace X] [T2Space X]
    [ConnectedSpace X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] :
    SecondCountableTopology X :=
  Rado.secondCountableTopology_of_riemannSurface
