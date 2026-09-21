/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage3BelowTwoS3F.PrimalTrajectory

namespace V7.Stage3BelowTwoS3F

mutual
  noncomputable def dualQ (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => 0
    | k + 1 =>
        dualQ p n oracle k -
          increment n (n - 1 - k) • belowMirrorMap p (dualR p n oracle k)
    termination_by k => k

  noncomputable def dualR (p : ℝ) (n : ℕ) (oracle : PairOracle d) :
      ℕ → Point d
    | 0 => -(coeffB n n n) • oracle.gradient 0
    | k + 1 =>
        let qNext :=
          dualQ p n oracle k -
            increment n (n - 1 - k) • belowMirrorMap p (dualR p n oracle k)
        let G : VectorSeq d := fun i =>
          if hi : i < k + 1 then oracle.gradient (dualQ p n oracle i)
          else if i = k + 1 then oracle.gradient qNext else 0
        dualR p n oracle k -
          weightedSum (k + 2) (fun i => coeffB n (n - i) (n - 1 - k)) G
    termination_by k => k
end

end V7.Stage3BelowTwoS3F
