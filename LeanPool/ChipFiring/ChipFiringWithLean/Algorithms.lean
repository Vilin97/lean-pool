/-
Copyright (c) 2026 Dhyey Dharmendrakumar Mavani, Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyey Dharmendrakumar Mavani, Nathan Pflueger
-/
module

public import LeanPool.ChipFiring.ChipFiringWithLean.Orientation


/-!
## Experimental computational algorithms for chip-firing

This file contains an early executable implementation of several chip-firing algorithms,
including greedy dollar-game play, Dhar's burning algorithm, and $q$-reduction routines.

The formal proof of Riemann-Roch in this repository does not rely on this file. Some of
these definitions predate the current theorem-proving infrastructure and should be treated
as exploratory code rather than certified implementations of the textbook algorithms.
In particular, the core mathematical statements about $q$-reduced divisors, superstability,
and Dhar's algorithm are proved elsewhere in the library.
-/

@[expose] public section

namespace ChipFiring


namespace CF



open Finset BigOperators List

/-- Checks whether a divisor is effective, meaning that all vertex values are nonnegative. -/
@[simp]
def isEffective (D : CFDiv G) : Bool := decide (∀ v, D v ≥ 0)

/-- A small size measure used only to set conservative default loop fuel. -/
def divisorMagnitude (G : CFGraph) (D : CFDiv G) : Nat :=
  ∑ v : G.V, Int.natAbs (D v)

/-- Default fuel for greedy routines, scaled by the actual chip counts in the input. -/
def greedyFuel (G : CFGraph) (D : CFDiv G) : Nat :=
  (Fintype.card G.V + 1) * (divisorMagnitude G D + 1) ^ 2 + 1

/-- Number of chips away from the source, used for the q-reduction loop budget. -/
def nonSourceChipCount (G : CFGraph) (q : G.V) (D : CFDiv G) : Nat :=
  ∑ v ∈ Finset.univ.erase q, Int.toNat (D v)

/-- Fuel-bounded greedy borrowing loop, recording vertices visited and the accumulated
firing script. -/
noncomputable def greedyWinnableLoop (G : CFGraph) (current_D : CFDiv G) (M : Finset G.V)
    (script : CFDiv G) (fuel : Nat) : Bool × Option (CFDiv G) :=
  if _h_fuel_zero : fuel = 0 then (false, none) -- Fuel exhaustion implies failure
  else if isEffective current_D then (true, some script)
  else if M = Finset.univ then (false, none) -- All vertices borrowed, still not effective
  else
    -- Find any in-debt vertex. The marked set only records which vertices have
    -- borrowed at least once; it does not prevent a vertex from borrowing again.
    match Finset.univ.toList.find? (fun v => current_D v < 0) with
    | some v =>
        let next_D := borrowingMove G current_D v
        let next_M := insert v M
        -- Update script: decrement count for borrowing vertex v
        let next_script : CFDiv G := script - oneChip v
        greedyWinnableLoop G next_D next_M next_script (fuel - 1)
    | none => -- No vertex is in debt, but `D` is not effective.
        -- This state implies unwinnability because we can't make progress.
        (false, none)
termination_by fuel
decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof

/--
The greedy algorithm for the dollar game (Corry-Perkinson, Algorithm 1).

The algorithm repeatedly chooses an in-debt vertex $v$, performs a borrowing move
at $v$, and records in $M$ that $v$ has borrowed at least once. Vertices already
in $M$ may still need to borrow again.
Returns `(winnable, script)` where `winnable` is true if an effective divisor is reached,
and `script` is the net borrowing count for each vertex if winnable.
-/
@[simp]
noncomputable def greedyWinnable (G : CFGraph) (D : CFDiv G) : Bool × Option (CFDiv G) :=
  -- Initial call with generous fuel
  let max_fuel := greedyFuel G D
  greedyWinnableLoop G D ∅ (0 : CFDiv G) max_fuel -- Initialize script as (0 : CFDiv G)

/-- Finds a burnable vertex $v \in S$, meaning one satisfying
$c(v) < \operatorname{outdeg}_S(v)$.

Returns `some v` if found, `none` otherwise. -/
noncomputable def findBurnableVertex (G : CFGraph) (c : G.V → ℤ) (S : Finset G.V) : Option { v :
    G.V // v ∈ S } :=
  -- Iterate through the list representation and find the first match
  -- Need to get proof v ∈ S, which is guaranteed by iterating S.toList
  let p := fun v => decide (c v < outdegS G S v) -- Use decide
  match h : S.toList.find? p with -- Use find? directly now (List is open)
  | some v =>
    -- Prove v is in the original finset S
    have h_mem_list : v ∈ S.toList := List.mem_of_find?_eq_some h
    have h_mem_finset : v ∈ S := Finset.mem_toList.mp h_mem_list
    some ⟨v, h_mem_finset⟩
  | none => none

/-- Fuel-bounded deletion of burnable vertices, returning the remaining stable set. -/
noncomputable def dharBurningSetLoop (G : CFGraph) (c : G.V → ℤ) (S : Finset G.V) (fuel : Nat) :
    Finset G.V :=
  -- Check fuel for termination safety
  if _h_fuel_zero : fuel = 0 then S -- Name hypothesis
  else
    match findBurnableVertex G c S with
    -- If a burnable vertex v is found, remove it and recurse
    | some ⟨v, hv⟩ => dharBurningSetLoop G c (S.erase v) (fuel - 1)
    -- If no burnable vertex found in S, S is stable, return it
    | none        => S
termination_by fuel
decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof

/--
The core iterative burning process of Dhar's algorithm (Corry-Perkinson, Algorithm 2).

Given a configuration $c$ (represented here as a function $V(G) \to \mathbb{Z}$,
with nonnegativity away from $q$ handled externally) and a sink $q$, this returns the
set of unburnt vertices $S \subseteq V(G) \setminus \{q\}$. The set $S$ is empty if
and only if the restriction of $c$ to $V(G) \setminus \{q\}$ is superstable relative to $q$.

The implementation uses well-founded recursion on the size of $S$.
-/
@[simp]
noncomputable def dharBurningSet (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  let initial_S := Finset.univ.erase q
  dharBurningSetLoop G c initial_S (Fintype.card G.V + 1)

/-- Fires every vertex in $S$, starting from the divisor $D$. -/
@[simp]
noncomputable def fireSet (G : CFGraph) (D : CFDiv G) (S : Finset G.V) : CFDiv G :=
  -- Use foldl directly now (List is open)
  foldl (fun current_D v => firingMove G current_D v) D S.toList

/-- Fuel-bounded borrowing loop that seeks nonnegative wealth away from the distinguished
vertex. -/
noncomputable def makeNonNegativeExceptQLoop (G : CFGraph) (q : G.V) (current_D : CFDiv G) (fuel
    : Nat) : Option (CFDiv G) :=
  if _h_fuel_zero : fuel = 0 then none -- Name hypothesis
  else
    -- Check if any vertex v != q has D(v) < 0
    let non_q_vertices := Finset.univ.erase q
    -- Use `find?` to efficiently check for a negative vertex
    match non_q_vertices.toList.find? (fun v => current_D v < 0) with
    | none => some current_D -- Goal reached: all v != q are non-negative
    | some v => -- Found a vertex v != q with current_D v < 0
        -- Borrow at the in-debt non-source vertex and continue.
        makeNonNegativeExceptQLoop G q (borrowingMove G current_D v) (fuel - 1)
termination_by fuel
decreasing_by simp_wf; exact Nat.pos_of_ne_zero _h_fuel_zero -- Simpler explicit proof

/--
The preprocessing step for `findQReducedDivisor`.

This borrows greedily at in-debt non-source vertices until $D(v) \ge 0$ for all
$v \ne q$ (Corry-Perkinson, Algorithm 4).
Requires sufficient fuel for the termination guard.
Returns `none` if fuel runs out, implying potential unwinnability or insufficient fuel.
-/
noncomputable def makeNonNegativeExceptQ (G : CFGraph) (q : G.V) (D : CFDiv G) (max_fuel : Nat)
    : Option (CFDiv G) :=
  makeNonNegativeExceptQLoop G q D max_fuel

/-- Fuel-bounded reduction loop that fires the nonburning set.
Returns `none` if the fuel runs out before reduction completes. -/
noncomputable def findQReducedDivisorLoop (G : CFGraph) (q : G.V) (current_D : CFDiv G) (fuel :
    Nat) : Option (CFDiv G) :=
  if h_fuel_zero : fuel = 0 then
    none
  else
    -- Use current_D as the configuration function for dharBurningSet
    let S := dharBurningSet G q current_D
    -- If the set S is non-empty, fire it and continue looping
    if hs : S.Nonempty then
      findQReducedDivisorLoop G q (fireSet G current_D S) (fuel - 1)
    else
      -- S is empty, the divisor is q-reduced
      some current_D
termination_by fuel
decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel_zero -- Simpler explicit proof

/--
Finds the unique $q$-reduced divisor linearly equivalent to $D$ (Corry-Perkinson,
Algorithm 3).

Starting from $D$, the algorithm first preprocesses by borrowing greedily at
in-debt non-source vertices until all vertices other than $q$ are nonnegative.
It then repeatedly finds the maximal legal firing set
$S \subseteq V(G) \setminus \{q\}$ using `dharBurningSet`, and fires $S$ until
`dharBurningSet` returns the empty set.

Returns `none` if preprocessing or reduction exhausts its fuel.
-/
@[simp]
noncomputable def findQReducedDivisor (G : CFGraph) (q : G.V) (D : CFDiv G) : Option (CFDiv G) :=
  -- Preprocessing: borrow at in-debt non-source vertices until D(v) >= 0 for v != q.
  -- Use chip-size-aware fuel rather than a graph-size-only bound.
  let preprocess_fuel : Nat := greedyFuel G D
  match makeNonNegativeExceptQ G q D preprocess_fuel with
  | none => none -- Preprocessing failed
  | some D_preprocessed =>
          -- Estimate fuel for main findQReducedDivisorLoop G q from possible
          -- q-effective non-source chip vectors.
      let main_loop_fuel := (nonSourceChipCount G q D_preprocessed + 1) ^ Fintype.card G.V + 1
      findQReducedDivisorLoop G q D_preprocessed main_loop_fuel

/-- Simulates the fire spread from $q$ in Dhar's algorithm on a configuration $c$.

Returns the set of unburnt vertices $S \subseteq V(G) \setminus \{q\}$.
Equivalent to `dharBurningSet`. -/
@[simp]
noncomputable def burn (G : CFGraph) (q : G.V) (c : G.V → ℤ) : Finset G.V :=
  dharBurningSet G q c

/-- Finds the $v$-reduced divisor linearly equivalent to $D$.

This wraps `findQReducedDivisor`.
Returns `none` if the reduction process fails. -/
@[simp]
noncomputable def dhar (G : CFGraph) (D : CFDiv G) (v : G.V) : Option (CFDiv G) :=
  findQReducedDivisor G v D

/--
The efficient winnability determination algorithm.

This checks whether $D$ is winnable by finding the $q$-reduced representative $D_q$
and checking whether $D_q(q) \ge 0$ (see Corry-Perkinson, Corollary 3.7). It requires
a chosen source vertex $q$ and returns `false` if the reduction process fails.
-/
@[simp]
noncomputable def isWinnable (G : CFGraph) (q : G.V) (D : CFDiv G) : Bool :=
  match findQReducedDivisor G q D with
  | none => false -- Reduction process failed (preprocessing or main loop fuel)
  | some D_q => D_q q >= 0

/--
Calculates the incoming burning degree of a vertex $v$ from a set $B$.

This sums `numEdges` from each $u \in B$ to $v$.
-/
def burningIndeg (G : CFGraph) (B : Finset G.V) (v : G.V) : ℤ :=
  ∑ u ∈ B, (numEdges G u v : ℤ)

/-- Fuel-bounded burning loop that records the orientations created as vertices burn. -/
noncomputable def dharBurningSetWithOrientationLoop (G : CFGraph) (c : G.V → ℤ) (current_S :
    Finset G.V) (current_B : Finset G.V) (current_O : Multiset (G.V × G.V)) (fuel : Nat)
  : Finset G.V × Multiset (G.V × G.V) :=
  if h_fuel : fuel = 0 then (current_S, current_O) -- Fuel exhausted, return current state
  else
    -- Find vertices in S that burn in this step
    let newly_burned_list := current_S.toList.filter (fun v => burningIndeg G current_B v > c v)
    let newly_burned := newly_burned_list.toFinset -- Use List.toFinset

    -- If no new vertices burned, the process stabilizes
    if newly_burned.card = 0 then (current_S, current_O) -- Use card = 0 check
    else
      -- Update S and B
      let next_S := current_S.filter (fun v => v ∉ newly_burned) -- Manual set difference
      let next_B := current_B ∪ newly_burned
      -- Update Orientation: Add edges from current_B to newly_burned
      -- Use Finset.sum for clarity and potentially better type inference
      let edges_to_add : Multiset (G.V × G.V) :=
        Finset.sum newly_burned (fun v_new => -- Sum over newly burned vertices
          Finset.sum current_B (fun u => -- For each u in the burning set
            Multiset.replicate (numEdges G u v_new) (u, v_new) -- Create edges u -> v_new
          )
        )
      let next_O := current_O + edges_to_add
      -- Recurse
      dharBurningSetWithOrientationLoop G c next_S next_B next_O (fuel - 1)
termination_by fuel
decreasing_by simp_wf; exact Nat.pos_of_ne_zero h_fuel -- Use robust termination proof

/--
The orientation-based version of Dhar's algorithm (Corry-Perkinson, Algorithm 5).

This takes a nonnegative configuration $c$ relative to $q$, and returns the final stable set
$S \subseteq V(G) \setminus \{q\}$ (empty if and only if $c$ is superstable) together
with a multiset $O$ of directed edges $(u,v)$ where fire spread from $u$ to $v$.

Note: this assumes $c$ is nonnegative on $V(G) \setminus \{q\}$.
The returned multiset `O` represents the edges oriented *by* the burning process.
It may not form a complete `CFOrientation` structure directly if not all edges are involved.
-/
@[simp]
noncomputable def dharBurningSetWithOrientation (G : CFGraph) (q : G.V) (c : G.V → ℤ)
  : Finset G.V × Multiset (G.V × G.V) :=
  let initial_S := Finset.univ.erase q
  let initial_B := {q}
  let initial_O := (∅ : Multiset (G.V × G.V))
  -- Initial call with fuel based on number of vertices
  dharBurningSetWithOrientationLoop G c initial_S initial_B initial_O (Fintype.card G.V + 1)

end CF

end ChipFiring
