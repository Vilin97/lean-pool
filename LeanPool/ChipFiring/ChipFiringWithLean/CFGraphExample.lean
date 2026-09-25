/-
Copyright (c) 2026 Dhyey Dharmendrakumar Mavani, Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyey Dharmendrakumar Mavani, Nathan Pflueger
-/
module

public import LeanPool.ChipFiring.ChipFiringWithLean.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric


/-!
# CFGraphExample

Chip firing, graph divisors, and their combinatorial properties.
-/

@[expose] public section

namespace ChipFiring


open Multiset Finset

/-- Four vertices used in the concrete chip-firing examples. -/
inductive Person : Type
  | A | B | C | E
  deriving DecidableEq

instance : Fintype Person where
  elems := {Person.A, Person.B, Person.C, Person.E}
  complete := by
    intro x
    cases x <;> simp only [mem_insert, reduceCtorEq, Finset.mem_singleton, or_false, or_true,
        or_self]
instance : Nonempty Person := ⟨Person.A⟩

-- Example usage for `Person` in a loopless graph.
/-- Three-edge path on the example vertices. -/
def exampleEdges : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.B, Person.C),
    (Person.C, Person.E)
  ]
private theorem loopless_example_edges : ∀ v, (v, v) ∉ exampleEdges := by
  decide

-- Example usage for `Person` in a graph with a loop.
/-- Example edge multiset containing a loop at A. -/
def edgesWithLoop : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.A, Person.A),   -- This is a loop
    (Person.B, Person.C),
  ]
private theorem loopless_test_edges_with_loop : ¬ (∀ v, (v, v) ∉ edgesWithLoop) := by decide

/-- Four-vertex loopless multigraph used to test firing and borrowing operations. -/
def exampleGraph : CFGraph := {
  V := Person,
  edges := Multiset.ofList [
    (Person.A, Person.B), (Person.B, Person.C),
    (Person.A, Person.C), (Person.A, Person.E),
    (Person.A, Person.E), (Person.E, Person.C)
  ],
  loopless := by decide,
}

/-- Initial divisor with wealth 2, -3, 4, and -1 at A, B, C, and E. -/
def initialWealth : CFDiv exampleGraph :=
  fun v => match v with
  | Person.A => 2
  | Person.B => -3
  | Person.C => 4
  | Person.E => -1

-- Test vertex degrees
private theorem vertex_degree_A : vertexDegree exampleGraph Person.A = 4 := by rfl
private theorem vertex_degree_B : vertexDegree exampleGraph Person.B = 2 := by rfl
private theorem vertex_degree_C : vertexDegree exampleGraph Person.C = 3 := by rfl
private theorem vertex_degree_E : vertexDegree exampleGraph Person.E = 3 := by rfl

-- Test edge counts
private theorem edge_count_AB : numEdges exampleGraph Person.A Person.B = 1 := by rfl
private theorem edge_count_BA : numEdges exampleGraph Person.B Person.A = 1 := by rfl
private theorem edge_count_BC : numEdges exampleGraph Person.B Person.C = 1 := by rfl
private theorem edge_count_CB : numEdges exampleGraph Person.C Person.B = 1 := by rfl
private theorem edge_count_AC : numEdges exampleGraph Person.A Person.C = 1 := by rfl
private theorem edge_count_CA : numEdges exampleGraph Person.C Person.A = 1 := by rfl
private theorem edge_count_AE : numEdges exampleGraph Person.A Person.E = 2 := by rfl
private theorem edge_count_EA : numEdges exampleGraph Person.E Person.A = 2 := by rfl
private theorem edge_count_EC : numEdges exampleGraph Person.E Person.C = 1 := by rfl
private theorem edge_count_CE : numEdges exampleGraph Person.C Person.E = 1 := by rfl
private theorem edge_count_BE : numEdges exampleGraph Person.B Person.E = 0 := by rfl
private theorem edge_count_EB : numEdges exampleGraph Person.E Person.B = 0 := by rfl

-- Test No self-loops
private theorem edge_count_AA : numEdges exampleGraph Person.A Person.A = 0 := by rfl
private theorem edge_count_BB : numEdges exampleGraph Person.B Person.B = 0 := by rfl
private theorem edge_count_CC : numEdges exampleGraph Person.C Person.C = 0 := by rfl
private theorem edge_count_EE : numEdges exampleGraph Person.E Person.E = 0 := by rfl

-- Test Charlie lending through an individual firing move
/-- Divisor after C fires once from the initial configuration. -/
def afterCharlieLends := firingMove exampleGraph initialWealth Person.C
private theorem charlie_wealth_after_lending : afterCharlieLends Person.C = 1 := by rfl
private theorem bob_wealth_after_charlie_lends : afterCharlieLends Person.B = -2 := by rfl

-- Test set firing W₁ = {A,E,C}
/-- First set of vertices fired in the example sequence. -/
def W₁ : Finset exampleGraph.V := {Person.A, Person.E, Person.C}
/-- Divisor after firing A, E, and C from the initial configuration. -/
def afterW₁Firing := setFiring exampleGraph initialWealth W₁
private theorem alice_wealth_after_W₁ : afterW₁Firing Person.A = 1 := by rfl
private theorem bob_wealth_after_W₁ : afterW₁Firing Person.B = -1 := by rfl
private theorem charlie_wealth_after_W₁ : afterW₁Firing Person.C = 3 := by rfl
private theorem elise_wealth_after_W₁ : afterW₁Firing Person.E = -1 := by rfl

-- Test set firing W₂ = {A,E,C}
/-- Second firing set, repeating the first set of vertices. -/
def W₂ : Finset exampleGraph.V := W₁
/-- Divisor after the second firing of A, E, and C. -/
def afterW₂Firing := setFiring exampleGraph afterW₁Firing W₂
private theorem alice_wealth_after_W₂ : afterW₂Firing Person.A = 0 := by rfl
private theorem bob_wealth_after_W₂ : afterW₂Firing Person.B = 1 := by rfl
private theorem charlie_wealth_after_W₂ : afterW₂Firing Person.C = 2 := by rfl
private theorem elise_wealth_after_W₂ : afterW₂Firing Person.E = -1 := by rfl

-- Test set firing W₃ = {B,C}
/-- Final firing set consisting of B and C. -/
def W₃ : Finset exampleGraph.V := {Person.B, Person.C}
/-- Effective divisor obtained after the three set-firing steps. -/
def afterW₃Firing := setFiring exampleGraph afterW₂Firing W₃
private theorem alice_wealth_after_W₃ : afterW₃Firing Person.A = 2 := by rfl
private theorem bob_wealth_after_W₃ : afterW₃Firing Person.B = 0 := by rfl
private theorem charlie_wealth_after_W₃ : afterW₃Firing Person.C = 0 := by rfl
private theorem elise_wealth_after_W₃ : afterW₃Firing Person.E = 0 := by rfl

-- Test borrowing moves
/-- Divisor after B borrows once from the initial configuration. -/
def afterBobBorrows := borrowingMove exampleGraph initialWealth Person.B
private theorem bob_wealth_after_borrowing : afterBobBorrows Person.B = -1 := by rfl
private theorem alice_wealth_after_bob_borrows : afterBobBorrows Person.A = 1 := by rfl
private theorem charlie_wealth_after_bob_borrows : afterBobBorrows Person.C = 3 := by rfl

-- Test degree of divisors
private theorem initial_wealth_degree : deg initialWealth = 2 := by rfl
private theorem after_W₁_degree : deg afterW₁Firing = 2 := by rfl
private theorem after_W₂_degree : deg afterW₂Firing = 2 := by rfl
private theorem after_W₃_degree : deg afterW₃Firing = 2 := by rfl

-- Test effectiveness of divisors
private theorem initial_not_effective : ¬(effective initialWealth) := by unfold effective; decide
private theorem after_W₃_firing_effective : effective afterW₃Firing  := by unfold effective; decide

-- Test Laplacian matrix values and symmetricity
/-- Integer Laplacian matrix of the example multigraph. -/
def exampleLaplacian := laplacianMatrix exampleGraph
private theorem laplacian_diagonal_A : exampleLaplacian Person.A Person.A = 4 := by rfl
private theorem laplacian_diagonal_B : exampleLaplacian Person.B Person.B = 2 := by rfl
private theorem laplacian_diagonal_C : exampleLaplacian Person.C Person.C = 3 := by rfl
private theorem laplacian_diagonal_E : exampleLaplacian Person.E Person.E = 3 := by rfl
private theorem laplacian_off_diagonal_AB : exampleLaplacian Person.A Person.B = -1 := by rfl
private theorem laplacian_off_diagonal_AC : exampleLaplacian Person.A Person.C = -1 := by rfl
private theorem laplacian_off_diagonal_AE : exampleLaplacian Person.A Person.E = -2 := by rfl
private theorem laplacian_off_diagonal_BC : exampleLaplacian Person.B Person.C = -1 := by rfl
private theorem laplacian_off_diagonal_BE : exampleLaplacian Person.B Person.E = 0 := by rfl
private theorem laplacian_off_diagonal_CE : exampleLaplacian Person.C Person.E = -1 := by rfl
private theorem check_example_laplacian_symmetry : Matrix.IsSymm exampleLaplacian := by {
  apply Matrix.IsSymm.ext
  intro i j
  cases i <;> cases j <;> rfl
}

-- Test script firing through laplacians
/-- Firing script in which C fires once and B borrows once. -/
def firingScriptExample : firingScript exampleGraph := fun v => match v with
  | Person.A => 0
  | Person.B => -1
  | Person.C => 1
  | Person.E => 0
/-- Divisor obtained by applying the example firing script through the Laplacian. -/
def resDivPostLapBasedScriptFiring := applyLaplacian exampleGraph firingScriptExample initialWealth
private theorem lap_based_script_firing_preserves_degree : deg resDivPostLapBasedScriptFiring =
    2 := by rfl

-- Test divisor that is not q-reduced with respect to Person.A
/-- Example divisor that is not A-reduced because B has negative wealth. -/
def nonQReducedExample : CFDiv exampleGraph := fun v => match v with
  | Person.A => 1
  | Person.B => -1  -- violates non-negativity condition for non-q vertices
  | Person.C => 2
  | Person.E => 1

private theorem non_q_reduced_example_is_invalid : ¬qReduced exampleGraph Person.A
    nonQReducedExample := by {
  rintro ⟨h1, _⟩
  have h1' : ∀ v : Person, v ≠ Person.A → nonQReducedExample v ≥ 0 := h1
  simpa only [nonQReducedExample, Int.reduceNeg, Int.neg_nonneg, Int.reduceLE]
      using h1' Person.B (by decide)
}

end ChipFiring
