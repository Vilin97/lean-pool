/-
Copyright (c) 2026 Keston Aquino-Michaels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Keston Aquino-Michaels
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Group.PUnit
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import LeanPool.CriticalPortraits.CycleLemma  -- the cycle lemma (Raney, sum=1), PROVED sorry-free

/-!
# Core definitions + the count numerator (Mathlib)

Positions are `ZMod N` (`N = d*m`); `level i = i.val / m`, `fiber i = i.val % m`. A `(d−1)`-subset
is **level-canonical** iff `#{i ∈ S : level i ≤ j} ≤ j` for all `j < d`.

Proved here (sorry-free): the count **numerator** `#{(d−1)-subsets of Z_N} = C(N, d−1)`, via
Mathlib's `Fintype.card_finset_len` + `ZMod.card`.
-/

@[expose] public section

namespace CriticalPortraits

open Finset

/-- The `k`-subsets of `Z_N` number `C(N, k)` (the count numerator). -/
theorem card_kSubsets (N k : ℕ) [NeZero N] :
    Fintype.card {S : Finset (ZMod N) // S.card = k} = N.choose k := by
  rw [Fintype.card_finset_len, ZMod.card]

/-- `level i = ⌊i / m⌋` for a position `i ∈ Z_N` (intended `N = d*m`). -/
def level {N : ℕ} (m : ℕ) (i : ZMod N) : ℕ := i.val / m

/-- `fiber i = i mod m`. -/
def fiber {N : ℕ} (m : ℕ) (i : ZMod N) : ℕ := i.val % m

/-- `S ⊆ Z_{d*m}` is **level-canonical** iff `#{i ∈ S : level i ≤ j} ≤ j` for every `j < d`. -/
def LevelCanonical (d m : ℕ) (S : Finset (ZMod (d * m))) : Prop :=
  ∀ j < d, (S.filter (fun i => i.val / m ≤ j)).card ≤ j

instance (d m : ℕ) (S : Finset (ZMod (d * m))) : Decidable (LevelCanonical d m S) := by
  unfold LevelCanonical; infer_instance

end CriticalPortraits
