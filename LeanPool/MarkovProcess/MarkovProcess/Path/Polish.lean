/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Path.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Polish structure of continuous-path space

For a complete separable metric state space, the compact-open topology on continuous paths is
Polish: it is second countable, and it is induced by the compact-convergence uniformity, which is
complete and countably generated because nonnegative time is locally compact and sigma-compact.
With the Borel sigma-algebra the path space is therefore a standard Borel space.

This is ordinary topological infrastructure.  It proves no probabilistic statement.
-/

namespace MarkovProcess
namespace ContinuousPath

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha] [SecondCountableTopology alpha]

/-- Continuous-path space over a complete separable metric space is Polish. -/
instance instPolishSpace : PolishSpace (ContinuousPath alpha) := inferInstance

/-- With the Borel sigma-algebra, continuous-path space is a standard Borel space. -/
theorem standardBorelSpace_borel :
    @StandardBorelSpace (ContinuousPath alpha) (borel (ContinuousPath alpha)) := by
  let : MeasurableSpace (ContinuousPath alpha) := borel (ContinuousPath alpha)
  have : BorelSpace (ContinuousPath alpha) := ⟨rfl⟩
  infer_instance

end ContinuousPath
end MarkovProcess
