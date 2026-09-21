/-
Copyright (c) 2026 Dhyey Dharmendrakumar Mavani, Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhyey Dharmendrakumar Mavani, Nathan Pflueger
-/
import LeanPool.ChipFiring.ChipFiringWithLean.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric


open Multiset Finset

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
def exampleEdges : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.B, Person.C),
    (Person.C, Person.E)
  ]
private theorem loopless_example_edges : ∀ v, (v, v) ∉ exampleEdges := by
  decide

-- Example usage for `Person` in a graph with a loop.
def edgesWithLoop : Multiset (Person × Person) :=
  Multiset.ofList [
    (Person.A, Person.B),
    (Person.A, Person.A),   -- This is a loop
    (Person.B, Person.C),
  ]
private theorem loopless_test_edges_with_loop : ¬ (∀ v, (v, v) ∉ edgesWithLoop) := by decide

def example_graph : CFGraph := {
  V := Person,
  edges := Multiset.ofList [
    (Person.A, Person.B), (Person.B, Person.C),
    (Person.A, Person.C), (Person.A, Person.E),
    (Person.A, Person.E), (Person.E, Person.C)
  ],
  loopless := by decide,
}

def initial_wealth : CFDiv example_graph :=
  fun v => match v with
  | Person.A => 2
  | Person.B => -3
  | Person.C => 4
  | Person.E => -1

-- Test vertex degrees
private theorem vertex_degree_A : vertex_degree example_graph Person.A = 4 := by rfl
private theorem vertex_degree_B : vertex_degree example_graph Person.B = 2 := by rfl
private theorem vertex_degree_C : vertex_degree example_graph Person.C = 3 := by rfl
private theorem vertex_degree_E : vertex_degree example_graph Person.E = 3 := by rfl

-- Test edge counts
private theorem edge_count_AB : num_edges example_graph Person.A Person.B = 1 := by rfl
private theorem edge_count_BA : num_edges example_graph Person.B Person.A = 1 := by rfl
private theorem edge_count_BC : num_edges example_graph Person.B Person.C = 1 := by rfl
private theorem edge_count_CB : num_edges example_graph Person.C Person.B = 1 := by rfl
private theorem edge_count_AC : num_edges example_graph Person.A Person.C = 1 := by rfl
private theorem edge_count_CA : num_edges example_graph Person.C Person.A = 1 := by rfl
private theorem edge_count_AE : num_edges example_graph Person.A Person.E = 2 := by rfl
private theorem edge_count_EA : num_edges example_graph Person.E Person.A = 2 := by rfl
private theorem edge_count_EC : num_edges example_graph Person.E Person.C = 1 := by rfl
private theorem edge_count_CE : num_edges example_graph Person.C Person.E = 1 := by rfl
private theorem edge_count_BE : num_edges example_graph Person.B Person.E = 0 := by rfl
private theorem edge_count_EB : num_edges example_graph Person.E Person.B = 0 := by rfl

-- Test No self-loops
private theorem edge_count_AA : num_edges example_graph Person.A Person.A = 0 := by rfl
private theorem edge_count_BB : num_edges example_graph Person.B Person.B = 0 := by rfl
private theorem edge_count_CC : num_edges example_graph Person.C Person.C = 0 := by rfl
private theorem edge_count_EE : num_edges example_graph Person.E Person.E = 0 := by rfl

-- Test Charlie lending through an individual firing move
def after_charlie_lends := firing_move example_graph initial_wealth Person.C
private theorem charlie_wealth_after_lending : after_charlie_lends Person.C = 1 := by rfl
private theorem bob_wealth_after_charlie_lends : after_charlie_lends Person.B = -2 := by rfl

-- Test set firing W₁ = {A,E,C}
def W₁ : Finset example_graph.V := {Person.A, Person.E, Person.C}
def after_W₁_firing := set_firing example_graph initial_wealth W₁
private theorem alice_wealth_after_W₁ : after_W₁_firing Person.A = 1 := by rfl
private theorem bob_wealth_after_W₁ : after_W₁_firing Person.B = -1 := by rfl
private theorem charlie_wealth_after_W₁ : after_W₁_firing Person.C = 3 := by rfl
private theorem elise_wealth_after_W₁ : after_W₁_firing Person.E = -1 := by rfl

-- Test set firing W₂ = {A,E,C}
def W₂ : Finset example_graph.V := W₁
def after_W₂_firing := set_firing example_graph after_W₁_firing W₂
private theorem alice_wealth_after_W₂ : after_W₂_firing Person.A = 0 := by rfl
private theorem bob_wealth_after_W₂ : after_W₂_firing Person.B = 1 := by rfl
private theorem charlie_wealth_after_W₂ : after_W₂_firing Person.C = 2 := by rfl
private theorem elise_wealth_after_W₂ : after_W₂_firing Person.E = -1 := by rfl

-- Test set firing W₃ = {B,C}
def W₃ : Finset example_graph.V := {Person.B, Person.C}
def after_W₃_firing := set_firing example_graph after_W₂_firing W₃
private theorem alice_wealth_after_W₃ : after_W₃_firing Person.A = 2 := by rfl
private theorem bob_wealth_after_W₃ : after_W₃_firing Person.B = 0 := by rfl
private theorem charlie_wealth_after_W₃ : after_W₃_firing Person.C = 0 := by rfl
private theorem elise_wealth_after_W₃ : after_W₃_firing Person.E = 0 := by rfl

-- Test borrowing moves
def after_bob_borrows := borrowing_move example_graph initial_wealth Person.B
private theorem bob_wealth_after_borrowing : after_bob_borrows Person.B = -1 := by rfl
private theorem alice_wealth_after_bob_borrows : after_bob_borrows Person.A = 1 := by rfl
private theorem charlie_wealth_after_bob_borrows : after_bob_borrows Person.C = 3 := by rfl

-- Test degree of divisors
private theorem initial_wealth_degree : deg initial_wealth = 2 := by rfl
private theorem after_W₁_degree : deg after_W₁_firing = 2 := by rfl
private theorem after_W₂_degree : deg after_W₂_firing = 2 := by rfl
private theorem after_W₃_degree : deg after_W₃_firing = 2 := by rfl

-- Test effectiveness of divisors
private theorem initial_not_effective : ¬(effective initial_wealth) := by unfold effective; decide
private theorem after_W₃_firing_effective : effective after_W₃_firing  := by unfold effective; decide

-- Test Laplacian matrix values and symmetricity
def example_laplacian := laplacian_matrix example_graph
private theorem laplacian_diagonal_A : example_laplacian Person.A Person.A = 4 := by rfl
private theorem laplacian_diagonal_B : example_laplacian Person.B Person.B = 2 := by rfl
private theorem laplacian_diagonal_C : example_laplacian Person.C Person.C = 3 := by rfl
private theorem laplacian_diagonal_E : example_laplacian Person.E Person.E = 3 := by rfl
private theorem laplacian_off_diagonal_AB : example_laplacian Person.A Person.B = -1 := by rfl
private theorem laplacian_off_diagonal_AC : example_laplacian Person.A Person.C = -1 := by rfl
private theorem laplacian_off_diagonal_AE : example_laplacian Person.A Person.E = -2 := by rfl
private theorem laplacian_off_diagonal_BC : example_laplacian Person.B Person.C = -1 := by rfl
private theorem laplacian_off_diagonal_BE : example_laplacian Person.B Person.E = 0 := by rfl
private theorem laplacian_off_diagonal_CE : example_laplacian Person.C Person.E = -1 := by rfl
private theorem check_example_laplacian_symmetry : Matrix.IsSymm example_laplacian := by {
  apply Matrix.IsSymm.ext
  intro i j
  cases i <;> cases j <;> rfl
}

-- Test script firing through laplacians
def firing_script_example : firing_script example_graph := fun v => match v with
  | Person.A => 0
  | Person.B => -1
  | Person.C => 1
  | Person.E => 0
def res_div_post_lap_based_script_firing := apply_laplacian example_graph firing_script_example initial_wealth
private theorem lap_based_script_firing_preserves_degree : deg res_div_post_lap_based_script_firing = 2 := by rfl

-- Test divisor that is not q-reduced with respect to Person.A
def non_q_reduced_example : CFDiv example_graph := fun v => match v with
  | Person.A => 1
  | Person.B => -1  -- violates non-negativity condition for non-q vertices
  | Person.C => 2
  | Person.E => 1

private theorem non_q_reduced_example_is_invalid : ¬q_reduced example_graph Person.A non_q_reduced_example := by {
  rintro ⟨h1, _⟩
  have h1' : ∀ v : Person, v ≠ Person.A → non_q_reduced_example v ≥ 0 := h1
  simpa only [non_q_reduced_example, Int.reduceNeg, Int.neg_nonneg, Int.reduceLE]
      using h1' Person.B (by decide)
}
