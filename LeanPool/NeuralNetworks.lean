/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.Hopfield.Basic
import LeanPool.NeuralNetworks.Hopfield.Energy
import LeanPool.NeuralNetworks.Hopfield.Convergence

/-!
# Hopfield Network Energy Descent

Source: doi:10.1073/pnas.79.8.2554
Authors: Matteo Cipollina, Alok Singh
Status: verified
Main declarations: `HopfieldState.energy_monotonically_decreases`, `HopfieldState.convergence`
Tags: neural-networks, hopfield-networks, dynamical-systems
MSC: 68T07, 37N40
-/

/-!
## Mathematical overview

Lean 4 formalizations of concepts related to neural networks and associated
mathematical structures, vendored from
<https://github.com/or4nge19/NeuralNetworks>.

This entry imports the Hopfield-network core: finite spin states, symmetric
zero-diagonal weight matrices, the usual quadratic energy, energy descent under
zero-threshold updates, and existence of a finite single-neuron update path from
any initial state to a fixed point.

The Lean code is imported from <https://github.com/or4nge19/NeuralNetworks>.
The upstream GPT-2, floating-point, and constructive-real material is outside
this Hopfield-paper scope.
-/
