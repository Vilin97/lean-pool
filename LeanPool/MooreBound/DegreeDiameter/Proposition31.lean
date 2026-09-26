/-
Copyright (c) 2026 Wouter Cames van Batenburg, Samuel Korsky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wouter Cames van Batenburg, Samuel Korsky
-/

module

public import LeanPool.MooreBound.DegreeDiameter.ExactDiameter
public import LeanPool.MooreBound.DegreeDiameter.ExactOrder
public import LeanPool.MooreBound.DegreeDiameter.FiniteFieldModels
public import LeanPool.MooreBound.DegreeDiameter.Symmetry

/-!
# Proposition 3.1 over arbitrary finite fields

The definitions below name the concrete graph in the write-up: its vertices
are the even partial flags in the recursively split `(2k+1)`-dimensional
coordinate model `FlagSpace K k`, and
adjacency means sharing a compatible odd partial flag.  The degree is the
cardinality of the neighbor set of the standard coordinate flag; transitivity
then proves that this is the degree of every vertex.

`proposition_3_1_over_finite_field` packages the exact order formula, the
sharp degree cap, regularity, and exact diameter for this one graph.  The
prime-power theorem is a genuine instance obtained from a finite field of
the requested cardinality, rather than a separate prime-only construction.

Lean Pool port of wewantmoore commit d59bd80ea93fabb9faf769e790ab47692645e022.
The port adds a namespace and adapts proofs to the current Mathlib APIs and repository style.
-/

public section

namespace MooreBound

namespace DegreeDiameter

open Module

/-- The vertex type of the graph `H_{k,K}` in Proposition 3.1. -/
abbrev Proposition31Vertex (K : Type*) [Field K] (k : ℕ) :=
  EvenPartialFlag (K := K) (V := FlagSpace K k) (n := 2 * k + 1)

/-- The concrete halved flag graph `H_{k,K}`. -/
abbrev Proposition31Graph (K : Type*) [Field K] (k : ℕ) :
    SimpleGraph (Proposition31Vertex K k) :=
  halvedFlagGraph (K := K) (V := FlagSpace K k) (n := 2 * k + 1)

/-- A coordinate basis of the recursively split model. -/
noncomputable def proposition31Basis (K : Type*) [Field K] (k : ℕ) :
    Basis (Fin (2 * k + 1)) K (FlagSpace K k) :=
  Module.finBasisOfFinrankEq K (FlagSpace K k) (by
    simpa only [flagDim_eq] using finrank_flagSpace (K := K) k)

/-- The standard vertex used to name the actual common degree. -/
noncomputable def proposition31StandardEven (K : Type*) [Field K] (k : ℕ) :
    Proposition31Vertex K k :=
  PartialFlag.ofComplete 0 (CompleteFlag.ofBasis (proposition31Basis K k))

/-- The actual degree of `H_{k,K}`, measured at the standard coordinate
flag.  Regularity below proves that this is independent of the vertex. -/
noncomputable def proposition31Degree (K : Type*) [Field K]
    (k : ℕ) : ℕ :=
  Nat.card ((Proposition31Graph K k).neighborSet
    (proposition31StandardEven K k))

/-- All vertices of the concrete graph have its named actual degree. -/
theorem proposition31_regular (K : Type*) [Field K] (k : ℕ) :
    ∀ P : Proposition31Vertex K k,
      Nat.card ((Proposition31Graph K k).neighborSet P) =
        proposition31Degree K k := by
  intro P
  exact halvedFlagGraph_natCard_neighborSet_eq P (proposition31StandardEven K k)

/-- **Proposition 3.1 (finite-field form).**  For every finite field `K` and
positive `k`, the same concrete graph is regular, has the exact q-factorial
order in both multiplication and division form, obeys the paper's sharp
degree cap, and has extended diameter exactly `k`. -/
theorem proposition_3_1_over_finite_field
    (K : Type*) [Field K] [Finite K] (k : ℕ) (hk : 0 < k) :
    (∀ P : Proposition31Vertex K k,
        Nat.card ((Proposition31Graph K k).neighborSet P) =
          proposition31Degree K k) ∧
    Nat.card (Proposition31Vertex K k) * (Nat.card K + 1) ^ k =
      qFactorial (Nat.card K) (2 * k + 1) ∧
    Nat.card (Proposition31Vertex K k) =
      qFactorial (Nat.card K) (2 * k + 1) / (Nat.card K + 1) ^ k ∧
    proposition31Degree K k ≤
      (Nat.card K + 1) ^ k * ((Nat.card K + 1) ^ k - 1) ∧
    (Proposition31Graph K k).ediam = (k : ℕ∞) := by
  refine ⟨proposition31_regular K k, ?_, ?_, ?_, ?_⟩
  · exact natCard_evenPartialFlag_mul_completion_eq_qFactorial
      (K := K) (V := FlagSpace K k) k (by
        simpa only [flagDim_eq] using finrank_flagSpace (K := K) k)
  · exact natCard_flagSpaceEvenPartialFlag_eq_qFactorial_div (K := K) k
  · exact halvedFlagGraph_natCard_neighborSet_le_sharp
      (K := K) (V := FlagSpace K k) k
      (proposition31StandardEven K k)
  · exact halvedFlagGraph_ediam_eq_ofBasis
      (K := K) (V := FlagSpace K k) k hk (proposition31Basis K k)

/-- **Proposition 3.1 (prime-power form).**  Every prime power `q` supplies
a finite field of cardinality exactly `q`, and hence the graph with exactly
the numerical parameters stated in the write-up. -/
theorem proposition_3_1_for_prime_power (q : PrimePowerIndex)
    (k : ℕ) (hk : 0 < k) :
    (∀ P : Proposition31Vertex (PrimePowerField q) k,
        Nat.card ((Proposition31Graph (PrimePowerField q) k).neighborSet P) =
          proposition31Degree (PrimePowerField q) k) ∧
    Nat.card (Proposition31Vertex (PrimePowerField q) k) * (q.1 + 1) ^ k =
      qFactorial q.1 (2 * k + 1) ∧
    Nat.card (Proposition31Vertex (PrimePowerField q) k) =
      qFactorial q.1 (2 * k + 1) / (q.1 + 1) ^ k ∧
    proposition31Degree (PrimePowerField q) k ≤
      (q.1 + 1) ^ k * ((q.1 + 1) ^ k - 1) ∧
    (Proposition31Graph (PrimePowerField q) k).ediam = (k : ℕ∞) := by
  simpa only [natCard_primePowerField] using
    (proposition_3_1_over_finite_field (PrimePowerField q) k hk)

end DegreeDiameter

end MooreBound
