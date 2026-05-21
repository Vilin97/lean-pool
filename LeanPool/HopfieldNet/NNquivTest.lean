/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.NNquiv
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs


set_option linter.unusedVariables false
set_option maxHeartbeats 500000

open Mathlib Finset BigOperators

/-- 1. DEFINE THE DATA SOURCE
    We keep the Matrix as the source of truth for both weights and topology. -/
def test.M : Matrix (Fin 3) (Fin 3) ℚ := Matrix.of ![![0,0,4], ![1,0,0], ![-2,3,0]]

/-- 2. DEFINE THE NETWORK
    We construct the NeuralNetwork instance. Note that we define 'Hom' here
    to satisfy the Quiver extension. -/
def test : NeuralNetwork ℚ (Fin 3) := {
  -- A. Topology (Quiver)
  -- We define an arrow existing only if the matrix value is non-zero.
  Hom := fun u v => PLift (test.M u v ≠ 0)

  -- B. Architecture (Sets)
  Ui := {0,1}
  Uo := {2}
  Uh := ∅

  -- C. Proofs of Architecture (Same as original)
  hUi := Ne.symm (Set.ne_insert_of_notMem {1} fun a ↦ a)
  hUo := Set.singleton_ne_empty 2
  hU := by
     ext x
     simp only [Set.mem_univ, Fin.isValue, Set.union_singleton,
       Set.union_empty, Set.mem_insert_iff,
       Set.mem_singleton_iff, true_iff]
     revert x
     decide
  hhio := by
    simp only [Fin.isValue, Set.union_singleton, Set.empty_inter]

  -- D. Dimensions
  κ1 := fun _ => 0
  κ2 := fun _ => 1

  -- E. Computation Functions
  -- 'fnet' calculates the weighted sum. We access 'test.M' directly here.
  fnet := fun u preds _ _ => ∑ v, (test.M u v) * preds v

  fact := fun u input θ => if input ≥ θ then 1 else 0
  fout := fun u act => act

  -- F. Constraints / Predicates
  pact := fun _ => True
  pw := fun _ _ _ => True -- We accept any arrow defined by our Hom
  hpact := fun _ _ _ _ _ _ => True.intro
}

/-- 3. DEFINE PARAMETERS
    In NNquiv, 'Params' holds external parameters (σ, θ) and a proof that
    the arrows satisfy 'pw'. -/
def wθ : Params test where
  h_arrows := fun _ _ _ => True.intro

  -- Thresholds (Theta)
  θ u := ⟨#[1], by
    simp only [List.size_toArray, List.length_cons, List.length_nil, zero_add]
    unfold test
    simp only⟩

  -- External inputs (Sigma) - empty here
  σ := fun _ => Vector.emptyWithCapacity 0

/-- 4. INITIAL STATE & HELPERS -/

-- Helper for printing
instance : Repr (NeuralNetwork.State test) where
  reprPrec state _ :=
   ("acts: " ++ repr (state.act)) ++ ", outs: " ++
        repr (state.out) ++ ", nets: " ++ repr (state.net wθ)

-- Initial State
def test.extu : test.State := {
  act := ![1,0,0],
  hp := fun u => trivial
}

lemma zero_if_not_mem_Ui : ∀ u : Fin 3,
  ¬ u ∈ ({0,1} : Finset (Fin 3)) → test.extu.act u = 0 := by decide

-- Proof that initial state respects input neuron constraints
lemma test.onlyUi : test.extu.onlyUi := by {
  intros u hu
  apply zero_if_not_mem_Ui u
  simp only [Fin.isValue, mem_insert, mem_singleton, not_or]
  exact not_or.mp hu
}


/- Workphase: u3, u1, u2, u3, u1, u2, u3 -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,0,1,2,0,1,2]

/- Workphase: u3, u2, u1, u3, u2, u1, u3 -/
#eval NeuralNetwork.State.workPhase wθ test.extu test.onlyUi [2,1,0,2,1,0,2]
