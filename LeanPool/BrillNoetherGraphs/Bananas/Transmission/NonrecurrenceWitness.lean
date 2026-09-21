/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.Theta.ThetaNonrecurrence

/-!
# Explicit witnesses of recurrence

The paper's recurrence arguments repeatedly exhibit two distinct nonzero
torsion residues at which the same degree-one vertex twist is effective.
This small generic lemma packages that final finite-residue step.
-/

namespace Bananas

open Utilities

/-- Two distinct nonzero effective twists of one vertex disprove
nonrecurrence.  The residue `1` is singled out because it is the one that
arises from the other marked vertex in the vertex-wedge argument. -/
theorem not_nonRecurrent_of_rank_nonneg_one_and_period
    {M : TwiceMarked} {a k : ℕ} (w : M.graph.V)
    (haOne : 1 < a) (haK : a < k)
    (hOne : 0 ≤ rank M.graph
      (one_chip w + (1 : ℤ) • (one_chip M.u - one_chip M.v)))
    (hA : 0 ≤ rank M.graph
      (one_chip w + (a : ℤ) • (one_chip M.u - one_chip M.v))) :
    ¬ NonRecurrent M k := by
  intro hNonrec
  let n : Fin k := ⟨1, by omega⟩
  let m : Fin k := ⟨a, haK⟩
  have hEq := hNonrec w n m (by simp [n])
    (by simpa [m] using Nat.ne_of_gt (lt_trans (by omega) haOne))
    (by simpa [n] using hOne) (by simpa [m] using hA)
  have hVal : 1 = a := congrArg Fin.val hEq
  omega

end Bananas
