/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.Hopfield.Basic
import LeanPool.NeuralNetworks.Hopfield.Energy
import LeanPool.NeuralNetworks.Hopfield.Convergence

/-!
# Neural Networks

Source: John J. Hopfield, "Neural networks and physical systems with
  emergent collective computational abilities", Proceedings of the National
  Academy of Sciences 79 (1982), 2554-2558, for the Hopfield-network energy
  and convergence mechanism; formalization source:
  url:https://github.com/or4nge19/NeuralNetworks
Authors: Matteo Cipollina, Alok Singh
Status: verified
Main declarations: `HopfieldState.HopfieldNetwork`, `HopfieldState.convergence`
Tags: neural-networks, hopfield-networks, dynamical-systems
MSC: 68T07, 37N40
-/

/-!
## Mathematical overview

Lean 4 formalizations of concepts related to neural networks and associated
mathematical structures, vendored from
<https://github.com/or4nge19/NeuralNetworks>.

This entry imports the Hopfield-network core: basic state space, energy
function, and convergence theorems. The upstream GPT-2 and floating-point
scaffolding are not included because they do not culminate in a theorem.
-/
