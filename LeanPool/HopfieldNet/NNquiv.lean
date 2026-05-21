/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import Mathlib.Combinatorics.Quiver.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.List.Pairwise

open Mathlib

universe u

structure NeuralNetwork (R U : Type u) [Zero R] extends Quiver.{u+1} U where
  (Ui Uo Uh : Set U)
  (hUi : Ui ≠ ∅)
  (hUo : Uo ≠ ∅)
  (hU : Set.univ = (Ui ∪ Uo ∪ Uh))
  (hhio : Uh ∩ (Ui ∪ Uo) = ∅)
  (κ1 κ2 : U → ℕ)
  (fnet : ∀ u : U, (U → R) → (U → R) → Vector R (κ1 u) → R)
  (fact : ∀ u : U, R → R → Vector R (κ2 u) → R)
  (fout : ∀ _ : U, R → R)
  (pact : R → Prop)
  (pw : ∀ (u v : U), (u ⟶ v) → Prop)
  (hpact : (∀ u v (f : Hom u v), pw u v f) →
   ∀ (σ : (u : U) → Vector R (κ1 u)) (θ : (u : U) → Vector R (κ2 u)) (current_neuron_activations : U → R),
  (∀ u_idx : U, pact (current_neuron_activations u_idx)) → -- Precondition on all current activations
  (∀ u_target : U, pact (fact u_target (current_neuron_activations u_target) -- Pass current_act of target neuron
                               (fnet u_target (fun v => fout v (current_neuron_activations v)) current_neuron_activations (σ u_target))
                               (θ u_target))))

variable {R U : Type} [Zero R]

/--
`Params` is a structure that holds the external parameters for a given
neural network `NN`, along with a proof that the network's internal
parameters (its arrows) satisfy the required predicate `NN.pw`.
-/
structure Params (NN : NeuralNetwork R U) where
  /-- A proof that all arrows in the neural network satisfy its parameter predicate `pw`. -/
  (h_arrows : ∀ u v (f : NN.Hom u v), NN.pw u v f)
  (w : Matrix U U R)
  /-- External parameters for the `fnet` function (e.g., biases). -/
  (σ : ∀ u : U, Vector R (NN.κ1 u))
  /-- External parameters for the `fact` function (e.g., activation function parameters). -/
  (θ : ∀ u : U, Vector R (NN.κ2 u))

namespace NeuralNetwork

structure State (NN : NeuralNetwork R U) where
  act : U → R
  hp : ∀ u : U, NN.pact (act u)

/-- Extensionality lemma for neural network states -/
@[ext]
lemma ext {R U : Type} [Zero R] [Quiver U] {NN : NeuralNetwork R U}
    {s₁ s₂ : NN.State} : (∀ u, s₁.act u = s₂.act u) → s₁ = s₂ := by
  intro h
  cases s₁
  cases s₂
  simp only [NeuralNetwork.State.mk.injEq]
  apply funext
  exact h

namespace State

variable {NN : NeuralNetwork R U} (wσθ : Params NN) (s : NN.State)

def out (u : U) : R := NN.fout u (s.act u)

def net (u : U) : R := NN.fnet u (fun v => s.out v) s.act (wσθ.σ u)

def onlyUi : Prop := ∀ u : U, ¬ u ∈ NN.Ui → s.act u = 0

variable [DecidableEq U]

def Up {NN_local : NeuralNetwork R U} (s : NN_local.State) (wσθ : Params NN_local) (u_upd : U) : NN_local.State :=
  { act := fun v => if v = u_upd then
                      NN_local.fact u_upd (s.act u_upd)
                        (NN_local.fnet u_upd (fun n => s.out n) s.act (wσθ.σ u_upd))
                        (wσθ.θ u_upd)
                    else
                      s.act v,
    hp := by
      intro v_target
      rw [ite_eq_dite]
      split_ifs with h_eq_upd_neuron
      · exact NN_local.hpact wσθ.h_arrows wσθ.σ wσθ.θ s.act s.hp u_upd
      · exact s.hp v_target
  }

def workPhase (extu : NN.State) (_ : extu.onlyUi) (uOrder : List U) : NN.State :=
  uOrder.foldl (fun s_iter u_iter => s_iter.Up wσθ u_iter) extu

def seqStates (useq : ℕ → U) : ℕ → NeuralNetwork.State NN
  | 0 => s
  | n + 1 => .Up (seqStates useq n) wσθ (useq n)

def isStable : Prop :=  ∀ (u : U), (s.Up wσθ u).act u = s.act u

end State
end NeuralNetwork
