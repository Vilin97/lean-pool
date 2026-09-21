/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.Multiplicativity
import LeanPool.RegtsSevenster.RS.Novel.Skein.SkeinIdeal

/-!
# The scalar class

Every closed fragment's class in the arity-zero Hom space is its
parameter value times the class of the empty fragment: this is
how the parameter `f` enters the skein category numerically.
The proof is the rank-one argument of Lemma 3.2 read backwards:
both rows of the arity-zero pairing are multiples of the empty
row, with ratio `f(W)`.
-/

namespace RS

/-- The arity-zero pairing is the union value. -/
theorem connectionPairing_zero_union {R : ℕ}
    (f : EdgeRankParameter R) (W G : ClosedFragment) :
    connectionPairing f.val 0 W G =
      f.val (ClosedFragment.union W G) :=
  f.iso_invariant _ _
    ((Fragment.composeCongr (relabelZeroEquiv W _)
      (relabelZeroEquiv G _)).trans (composeZeroEquiv W G))

/-- **The scalar class**: the class of a closed fragment in the
arity-zero Hom space is its value times the empty class. -/
theorem ofFragment_eq_smul_empty {R : ℕ}
    (f : EdgeRankParameter R) (W : ClosedFragment) :
    HomSpace.ofFragment f.val W =
      f.val W • HomSpace.ofFragment f.val emptyClosedFragment := by
  have h : (Finsupp.single W (1 : ℂ)) -
      f.val W • Finsupp.single emptyClosedFragment 1 ∈
      LinearMap.ker (connectionMap f.val 0) := by
    rw [LinearMap.mem_ker, map_sub, map_smul]
    funext G
    show connectionMap f.val 0 (Finsupp.single W 1) G -
      f.val W • connectionMap f.val 0
        (Finsupp.single emptyClosedFragment 1) G = 0
    rw [connectionMap_single, connectionMap_single, one_mul,
      one_mul, smul_eq_mul, connectionPairing_zero_union f W G,
      connectionPairing_zero_union f emptyClosedFragment G,
      EdgeRankParameter.val_union,
      EdgeRankParameter.val_union, f.val_empty, one_mul]
    ring
  have h2 : (LinearMap.ker (connectionMap f.val 0)).mkQ
      (Finsupp.single W (1 : ℂ)) =
      (LinearMap.ker (connectionMap f.val 0)).mkQ
        (f.val W • Finsupp.single emptyClosedFragment 1) := by
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq]
    exact h
  exact h2.trans (map_smul
    (LinearMap.ker (connectionMap f.val 0)).mkQ (f.val W)
    (Finsupp.single emptyClosedFragment 1))

end RS
