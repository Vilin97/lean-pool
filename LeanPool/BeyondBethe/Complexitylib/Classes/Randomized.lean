/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanPool.BeyondBethe.Complexitylib.Classes.Time

/-!
# Randomized complexity classes

This file defines the randomized complexity classes **BPP**, **RP**, **coRP**,
**ZPP**, and **PP**, along with the time-parameterized classes `BPTIME`,
`RTIME`, and `PPTIME`, and the predicate `NTM.IsPPT`.

A PTM (probabilistic Turing machine) is an NTM where the two transition
functions are selected uniformly at random. Acceptance probability is defined
via `NTM.acceptProb`.

## Helper predicates

The acceptance-probability conditions shared across classes are factored into
`NTM.AcceptsWithProb` (lower-bounding acceptance on yes-instances) and
`NTM.RejectsWithProb` (upper-bounding acceptance on no-instances).
-/


@[expose] public section

namespace Complexity


namespace NTM

variable {n : ℕ}

/-- The PTM accepts every `x ∈ L` with probability at least `c` within
    `T(|x|)` steps. -/
def AcceptsWithProb (tm : NTM n) (L : Language) (T : ℕ → ℕ) (c : ℚ) : Prop :=
  ∀ x, x ∈ L → tm.acceptProb x (T x.length) ≥ c

/-- The PTM accepts every `x ∉ L` with probability at most `s` within
    `T(|x|)` steps. -/
def RejectsWithProb (tm : NTM n) (L : Language) (T : ℕ → ℕ) (s : ℚ) : Prop :=
  ∀ x, x ∉ L → tm.acceptProb x (T x.length) ≤ s

/-- An NTM is **probabilistic polynomial-time (PPT)** if there exist a time
    bound `f` and degree `d` such that every computation path halts within
    `f(|x|)` steps and `f(n) = O(n^d)`. This is the central notion in
    cryptographic security definitions. -/
def IsPPT (tm : NTM n) : Prop :=
  ∃ (f : ℕ → ℕ) (d : ℕ), tm.AllPathsHaltIn f ∧ f =O (· ^ d)

end NTM

/-- `BPTIME(T)` is the class of languages decidable by a PTM in time `O(T(n))`
    with two-sided bounded error (accept probability ≥ 2/3 on yes-instances,
    ≤ 1/3 on no-instances). -/
def BPTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.AllPathsHaltIn f ∧
    tm.AcceptsWithProb L f (2 / 3) ∧
    tm.RejectsWithProb L f (1 / 3) ∧
    f =O T}

/-- **BPP** is the class of languages decidable by a PTM in polynomial time
    with two-sided bounded error: `BPP = ⋃_k BPTIME(n^k)`. -/
def BPP : Set Language :=
  ⋃ k : ℕ, BPTIME (· ^ k)

/-- `RTIME(T)` is the class of languages decidable by a PTM in time `O(T(n))`
    with one-sided error: yes-instances accepted with probability ≥ 1/2,
    no-instances never accepted (accept probability 0). -/
def RTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.AllPathsHaltIn f ∧
    tm.AcceptsWithProb L f (1 / 2) ∧
    tm.RejectsWithProb L f 0 ∧
    f =O T}

/-- **RP** is the class of languages decidable by a PTM in polynomial time
    with one-sided error: `RP = ⋃_k RTIME(n^k)`. -/
def RP : Set Language :=
  ⋃ k : ℕ, RTIME (· ^ k)

/-- **coRP** is the class of languages whose complements are in RP.
    Equivalently: yes-instances always accepted (probability 1), no-instances
    accepted with probability ≤ 1/2. -/
def coRP : Set Language := complClass RP

/-- **ZPP** (zero-error probabilistic polynomial time) is RP ∩ coRP. A language
    is in ZPP iff it has a PTM with zero-error expected polynomial running
    time. -/
def ZPP : Set Language := RP ∩ coRP

/-- `PPTIME(T)` is the class of languages decidable by a PTM in time `O(T(n))`
    with unbounded error: `x ∈ L` iff the PTM accepts with probability
    strictly greater than 1/2. -/
def PPTIME (T : ℕ → ℕ) : Set Language :=
  {L | ∃ (k : ℕ) (tm : NTM k) (f : ℕ → ℕ),
    tm.AllPathsHaltIn f ∧
    (∀ x, x ∈ L ↔ tm.acceptProb x (f x.length) > 1 / 2) ∧
    f =O T}

/-- **PP** (probabilistic polynomial time) is the class of languages decidable
    by a PTM in polynomial time with unbounded error: `PP = ⋃_k PPTIME(n^k)`. -/
def PP : Set Language :=
  ⋃ k : ℕ, PPTIME (· ^ k)

end Complexity
