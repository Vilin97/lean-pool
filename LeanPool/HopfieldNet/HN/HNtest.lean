/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.HN.Core

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

variable {R U : Type} [Zero R]

/-- Two neurons `u` and `v` are connected in the graph if `w u v` is not zero. -/
def Matrix.Adj (w : Matrix U U R) : U → U → Prop := fun u v => w u v ≠ 0

/-- `Matrix.w` returns the value of the matrix `w` at position `(u, v)` if `u` and `v` are connected. -/
def Matrix.w (w : Matrix U U R) : ∀ u v : U, w.Adj u v → R := fun u v _ => w u v


/-Hopfield Networks-/

/-- A 4x4 matrix of rational numbers. --/
def W1 : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.of ![![0,1,-1,-1], ![1,0,-1,-1], ![-1,-1,0,1], ![-1,-1,1,0]]

/--
`HebbianParamsTest` defines a Hopfield Network with 4 neurons and rational weights.
- `w`: The weight matrix `W1`.
- `hw`: Proof that the weights are symmetric.
- `hw'`: Proof that the weights are zero on the diagonal.
- `σ`: Always an empty vector.
- `θ`: Always returns a list with a single 0.
--/
def HebbianParamsTest : Params (HopfieldNetwork ℚ (Fin 4)) where
  w := W1
  hw u v huv := by
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ := fun u => Vector.emptyWithCapacity 0
  θ u := ⟨#[0],by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]⟩

/-- `extu` is the initial state for our `HebbianParamsTest` Hopfield network.
- `act`: `[1, -1, -1, 1]` - initial activations.

This initializes the state for a Hopfield network test.
--/
def extu : State' HebbianParamsTest where
  act := ![1,-1,-1,1]
  hp := by
    intros u
    unfold HopfieldNetwork
    simp only
    revert u
    decide

instance : Repr (HopfieldNetwork ℚ (Fin 4)).State where
  reprPrec state _ := ("acts: " ++ repr (state.act))

-- Computations

-- lemma zero_if_not_mem_Ui' : ∀ u : Fin 4,
--     ¬ u ∈ ({0,1,2,3} : Finset (Fin 4)) → extu.act u = 0 := by {decide}

-- def HN.hext : extu.onlyUi := by {intros u; tauto}

-- #eval NeuralNetwork.State.workPhase HebbianParamsTest extu HN.hext [2,0,1,2,0,1,2]


/--
`pattern_ofVec` converts a pattern vector from `Fin n` to `ℚ` into a `State`
for a `HopfieldNetwork` with `n` neurons.
It checks if all elements are either 1 or -1. If they are, it returns `some`
 pattern; otherwise, it returns `none`.
--/
def pattern_ofVec {n} [NeZero n] (pattern : Fin n → ℚ) :
    Option (HopfieldNetwork ℚ (Fin n)).State :=
  if hp : ∀ i, pattern i = 1 ∨ pattern i = -1 then
    some {act := pattern, hp := by {
      intros u
      unfold HopfieldNetwork
      simp only
      apply hp
      }}
  else
    none

/--
`obviousFunction` tries to convert a function `f` from `α` to `Option β` into a regular function
from `α` to `β`. If `f` returns `some` for every input, it returns `some` function that extracts
these values. Otherwise, it returns `none`.
--/
def obviousFunction [Fintype α] (f : α → Option β) : Option (α → β) :=
  if h : ∀ x, (f x).isSome then
    some (fun a => (f a).get (h a))
  else
    none


/--
Converts a matrix of patterns `V` into Hopfield network states.

Each row of `V` (a function `Fin m → Fin n → ℚ`) is mapped to a Hopfield network state
if all elements are either `1` or `-1`. Returns `some` mapping if successful, otherwise `none`.
-/
def patternsOfVecs (V : Fin m → Fin n → ℚ) [NeZero n] (hmn : m < n) :
  Option (Fin m → (HopfieldNetwork ℚ (Fin n)).State) :=
  obviousFunction (fun i => pattern_ofVec (V i))

/--
`ZeroParams_4` defines a simple Hopfield Network with 4 neurons.

- `w`: A 4x4 weight matrix filled with zeros.
- `hw`: Proof that the weight matrix is symmetric.
- `hw'`: Proof that the weight matrix has zeros on the diagonal.
- `σ`: An empty vector for each neuron.
- `θ`: A threshold of 0 for each neuron, with proof that the list has length 1.
--/
def ZeroParams_4 : Params (HopfieldNetwork ℚ (Fin 4)) where
  w :=  (Matrix.of ![![0,0,0,0], ![0,0,0,0], ![0,0,0,0], ![0,0,0,0]])
  hw u v huv := by {
    unfold HopfieldNetwork at huv
    simp only [ne_eq, Decidable.not_not] at huv
    rw [huv]
    revert v v
    simp only [forall_eq']
    revert u u
    decide}
  hw' := by {
    unfold HopfieldNetwork
    simp only
    decide}
  σ u := Vector.emptyWithCapacity 0
  θ u := ⟨#[0], by {simp only [List.size_toArray, List.length_cons,
    List.length_nil, zero_add]}⟩

/--
`ps` are two patterns represented by a 2x4 matrix of rational numbers.
--/
def ps : Fin 2 → Fin 4 → ℚ := ![![1,1,-1,-1], ![-1,1,-1,1]]

/--
`test_params` sets up a `HopfieldNetwork` with 4 neurons.
It converts the patterns `ps` into a network using Hebbian learning if possible.
If not, it defaults to `ZeroParams_4`.
--/
def test_params : Params (HopfieldNetwork ℚ (Fin 4)) :=
  match (patternsOfVecs ps (by simp only [Nat.reduceLT])) with
  | some patterns => Hebbian patterns
  | none => ZeroParams_4

/--
`useq_Fin n` maps a natural number `i` to an element of `Fin n` (a type with `n` elements).
It wraps `i` around using modulo `n`.

Arguments:
- `n`: The size of the finite type (must be non-zero).
- `i`: The natural number to convert.

Returns:
- An element of `Fin n`.
--/
def useq_Fin n [NeZero n] : ℕ → Fin n := fun i =>
  ⟨_, Nat.mod_lt i (Nat.pos_of_neZero n)⟩

lemma useq_Fin_cyclic n [NeZero n] : cyclic (useq_Fin n) := by
  unfold cyclic
  unfold useq_Fin
  simp only [Fintype.card_fin]
  apply And.intro
  · intros u
    use u.val
    cases' u with u hu
    simp only
    simp_all only [Fin.mk.injEq]
    exact Nat.mod_eq_of_lt hu
  · intros i j hij
    exact Fin.mk.inj_iff.mpr hij

lemma useq_Fin_fair n [NeZero n] : fair (useq_Fin n) :=
  cycl_Fair (useq_Fin n) (useq_Fin_cyclic n)

#eval HopfieldNet_stabilize test_params extu (useq_Fin 4) (useq_Fin_fair 4)

#eval HopfieldNet_conv_time_steps test_params extu (useq_Fin 4) (useq_Fin_cyclic 4)
