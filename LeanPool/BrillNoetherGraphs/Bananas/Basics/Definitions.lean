/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionSeparator
import LeanPool.BrillNoetherGraphs.Utilities.Foundations.Parameters

/-!
# Twice-marked banana graphs: definitions

This is the paper-specific vocabulary for the twice-marked banana paper.  A banana
of genus `g` is represented by the existing positive subdivision model with
two core vertices and `g + 1` distinct edge slots.  Thus parallel strands are
retained by construction, rather than identified as a simple graph.
-/

namespace Bananas

open Utilities

open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-- A genus-`g` banana graph: `g + 1` positive-length strands between two core
vertices. -/
abbrev Banana (g : ℕ) := Spec 2 (g + 1)

/-- A concrete banana with prescribed positive strand lengths: the two-vertex
core with `g + 1` parallel strands, none of which is a loop.  This is the
coordinate-first constructor behind the notation `B_{n₀,…,nₑ}` and, at
`g = 2`, `θ_{a,b,c}`. -/
def bananaOfLengths (g : ℕ) (length : Fin (g + 1) → ℕ)
    (hpos : ∀ i, 0 < length i) : Banana g where
  core := { tail := fun _ => 0, head := fun _ => 1 }
  length := length
  core_nonempty := by decide
  core_loopless := fun _ => (by decide : (0 : Fin 2) ≠ 1)
  length_pos := hpos

/-- The vertex at position `i` along strand `α`, measured from core vertex
`0`.  `SubdivisionGraph.Spec` allows an individual slot to be stored in either
orientation, so this deliberately reverses its coordinate when necessary. -/
def strandVertex {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) : B.graph.V :=
  B.pathVertex α
    (if B.core.tail α = 0 then i else
      ⟨B.length α - i.val, by
        have hi := i.isLt
        omega⟩)

/-- Reflection of a normalized strand coordinate about its midpoint. -/
def strandMirror {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i : B.PathPosition α) : B.PathPosition α :=
  ⟨B.length α - i.val, by
    have hi := i.isLt
    omega⟩

/-- The two multivalent vertices of a banana. -/
def leftEndpoint {g : ℕ} (B : Banana g) : B.graph.V := B.coreVertex 0
def rightEndpoint {g : ℕ} (B : Banana g) : B.graph.V := B.coreVertex 1

/-- A graph with an ordered pair of marked vertices. -/
structure TwiceMarked where
  graph : CFGraph
  u : graph.V
  v : graph.V

/-- Bundle a graph and an ordered pair of its vertices as a twice-marked graph. -/
def mark (G : CFGraph) (u v : G.V) : TwiceMarked := ⟨G, u, v⟩

/-- Paper source: `def-Delt` (Definition 2.8), the function `Δ(D)`.

The paper's second rank difference, relative to the two marks. -/
noncomputable def rankDelta (M : TwiceMarked) (D : CFDiv M.graph) : ℤ :=
  rank M.graph D - rank M.graph (D - one_chip M.u) -
    rank M.graph (D - one_chip M.v) +
      rank M.graph (D - one_chip M.u - one_chip M.v)

/-- Paper source: `def-Twist` (Definition 2.7). -/
def twist (M : TwiceMarked) (D : CFDiv M.graph) (a b : ℤ) : CFDiv M.graph :=
  D + a • one_chip M.u + b • one_chip M.v

/-- Paper source: `def-submod` (Definition 2.9).

Submodularity of a divisor, including all of its marked twists. -/
def Submodular (M : TwiceMarked) (D : CFDiv M.graph) : Prop :=
  ∀ a b : ℤ, 0 ≤ rankDelta M (twist M D a b)

/-- Every divisor is submodular for this marked graph. -/
def AllSubmodular (M : TwiceMarked) : Prop :=
  ∀ D : CFDiv M.graph, Submodular M D

/-- Paper source: the hypothesis `ku ∼ kv` of the `k`-general transmission
definition (Definition 1.10), *not* the torsion order of `def-TwMkGraph`.

A positive `k` kills the degree-zero class of the marked-point difference. -/
def TorsionWitness (M : TwiceMarked) (k : ℕ) : Prop :=
  0 < k ∧ linear_equiv M.graph
    ((k : ℤ) • (one_chip M.u - one_chip M.v)) 0

/-- Paper source: `def-TwMkGraph` (Definition 2.6), the torsion order.

The torsion order is the least positive `k` killing the marked difference. -/
def IsTorsionOrder (M : TwiceMarked) (k : ℕ) : Prop :=
  TorsionWitness M k ∧ ∀ m : ℕ, TorsionWitness M m → k ≤ m

/-- Paper source: `def-tauD` (Definition 2.11), the transmission permutation
`τ^{u,v}_D` characterised by `δ(τ(b) = a) = Δ(D + au - bv)`.

We keep the permutation as an integer function; bijectivity is stated here
instead of using a separate affine-permutation structure.  Note that the
main library models the same notion by `AspPerm` together with
`Utilities.SatisfiesTransmission`; the two presentations are not yet
connected by any lemma. -/
def IsTransmissionPermutation (M : TwiceMarked) (D : CFDiv M.graph)
    (τ : ℤ → ℤ) : Prop :=
  Function.Bijective τ ∧ ∀ a b : ℤ,
    (if τ b = a then (1 : ℤ) else 0) =
      rankDelta M (D + a • one_chip M.u - b • one_chip M.v)

/-- Paper source: `def-EA` (Definition 2.10), membership in the extended
affine symmetric group `Σ̃_k`. -/
def IsKAffine (k : ℕ) (τ : ℤ → ℤ) : Prop :=
  ∀ n : ℤ, τ (n + k) = τ n + k

/-- Paper source: `def-inv` (Definition 2.13), the set `Inv_k(τ)`.

The paper's `k`-inversions are `k`-equivalence classes of inversions, where
`(a,b) ∼ (a',b')` iff `a - a' = b - b'` and `a ≡ a' (mod k)`.  Each class has
a unique representative with `0 ≤ a < k`, and this set of representatives is
what is recorded here. -/
def kInversions (k : ℕ) (τ : ℤ → ℤ) : Set (ℤ × ℤ) :=
  { p | p.1 < p.2 ∧ τ p.1 > τ p.2 ∧ 0 ≤ p.1 ∧ p.1 < k }

/-- Paper source: `def-inv` (Definition 2.13), the number `inv_k(τ)`. -/
noncomputable def kInversionCount (k : ℕ) (τ : ℤ → ℤ) : ℕ :=
  (kInversions k τ).ncard

/-- Paper source: Definition 1.10, `k`-general transmission.

Stated directly in terms of transmission permutations and their
`k`-inversion counts.  The `(kInversions k τ).Finite` conjunct is not
redundant decoration: `Set.ncard` is `0` on an infinite set, so without it
the count bound would be satisfied vacuously by a permutation with
infinitely many `k`-inversions.  (Finiteness is in fact automatic here — see
`kInversions_finite_of_isKAffine` — but only because of the other
conjuncts.) -/
def KGeneralTransmission (M : TwiceMarked) (k : ℕ) : Prop :=
  TorsionWitness M k ∧ AllSubmodular M ∧
    ∀ D : CFDiv M.graph, ∃ τ : ℤ → ℤ,
      IsTransmissionPermutation M D τ ∧ IsKAffine k τ ∧
        (kInversions k τ).Finite ∧
          kInversionCount k τ ≤ Int.toNat (genus M.graph)

/-- Paper source: Definition 1.3, i.e. part 2 of Conjecture 1.2.  Every pair
in the divisor census satisfies `ρ(g,r,d) ≥ 0`.

This is deliberately an implication and not an equivalence.  The converse
inclusion (every pair with `ρ ≥ 0` occurs) is part 1 of Conjecture 1.2, which
the paper records as open outside small genus.  Building it into the
definition would silently strengthen every hypothesis `BrillNoetherGeneral G`
and, more importantly, weaken every conclusion of the form
`¬ BrillNoetherGeneral G`. -/
def BrillNoetherGeneral (G : CFGraph) : Prop :=
  ∀ r d : ℤ, 0 ≤ r → BNExists G r d → 0 ≤ bnNumber G r d

/-- Paper source: the set `N_(G,u,v)` of `thm-NonSubmodGenus2` (Theorem 3.4),
for two marks `u = v_{α,i}`, `v = v_{α,j}` on one strand:
`{ v_{α,q} : q ≠ n_α - i, q ≠ j, j - i ≤ q ≤ j - i + n_α }`.

The bounds are stated over `ℤ`.  The paper places no order relation on `i`
and `j`, and with truncated `ℕ` subtraction the constraint `j - i ≤ q` would
collapse to `0 ≤ q` whenever `j < i`; the `ℕ` reading therefore only agrees
with the paper's set when `i ≤ j`. -/
def thetaExceptionalPositions {g : ℕ} (B : Banana g) (α : Fin (g + 1))
    (i j : B.PathPosition α) : Set (B.PathPosition α) :=
  { q | (q.val : ℤ) ≠ (B.length α : ℤ) - (i.val : ℤ) ∧
      (q.val : ℤ) ≠ (j.val : ℤ) ∧
      (j.val : ℤ) - (i.val : ℤ) ≤ (q.val : ℤ) ∧
      (q.val : ℤ) ≤ (j.val : ℤ) - (i.val : ℤ) + (B.length α : ℤ) }

/-- Paper source: `defn:evenlyMarked` (Definition 4.14).

Two interior marks on distinct theta strands divide their strands in the
same rational ratio.  Cross multiplication avoids a division convention. -/
def EvenlyMarkedTheta (B : Banana 2) (α β : Fin 3)
    (i : B.PathPosition α) (j : B.PathPosition β) : Prop :=
  α ≠ β ∧ 0 < i.val ∧ i.val < B.length α ∧ 0 < j.val ∧ j.val < B.length β ∧
    i.val * B.length β = j.val * B.length α

end Bananas
