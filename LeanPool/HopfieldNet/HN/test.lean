/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.NN
import Mathlib.Analysis.Normed.Field.Lemmas

set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset

variable {R U : Type} [Zero R]

/-- Two neurons `u` and `v` are connected in the graph if `w u v` is not zero. -/
def Matrix.Adj (w : Matrix U U R) : U → U → Prop := fun u v => w u v ≠ 0

/-- `Matrix.w` returns the value of the matrix `w` at position `(u, v)` if `u` and `v` are connected. -/
def Matrix.w (w : Matrix U U R) : ∀ u v : U, w.Adj u v → R := fun u v _ => w u v

/-- A 3x3 matrix of rational numbers. --/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

def test : NeuralNetwork ℚ (Fin 3) where
  Adj := test.M.Adj
  Ui := {0,1}
  Uo := {2}
  hU := by
     ext x
     simp only [Set.mem_univ, Fin.isValue, Set.union_singleton,
       Set.union_empty, Set.mem_insert_iff,
       Set.mem_singleton_iff, true_iff]
     revert x
     decide
  Uh := ∅
  hUi := Ne.symm (Set.ne_insert_of_notMem {1} fun a ↦ a)
  hUo := Set.singleton_ne_empty 2
  hhio := by
    simp only [Fin.isValue, Set.union_singleton, Set.empty_inter]
  pw W := True
  κ1 u := 0
  κ2 u := 1
  fnet u w pred σ := ∑ v, w v * pred v
  fact u input θ := if input ≥ θ then 1 else 0
  fout u act := act
  pact u := True
  hpact w _ _ σ θ _ pact u := pact u

def wθ : Params test where
  w := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]
  θ u := ⟨#[1], by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    unfold test
    simp only⟩
  σ _ := Vector.emptyWithCapacity 0
  hw u v hv := by by_contra h; exact hv h
  hw' := by simp only [test]

instance : Repr (NeuralNetwork.State test) where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

/--
`test.extu` is the initial state for the `test` neural network with activations `[1, 0, 0]`.
-/
def test.extu : test.State := {act := ![1,0,0], hp := fun u => trivial}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

/--If `u` is not in the input neurons `Ui`, then `test.extu.act u` is zero.-/
lemma test.onlyUi : test.extu.onlyUi := by {
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu}

/-The workphase for the asynchronous update of the sequence of neurons u3 , u1 , u2 , u3 , u1 , u2 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,0,1,2,0,1,2]

/-The workphase for the asynchronous update of the sequence of neurons u3 , u2 , u1 , u3 , u2 , u1 , u3. -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,1,0,2,1,0,2]
