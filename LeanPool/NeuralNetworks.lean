/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.Float.Foundation.Basic
import LeanPool.NeuralNetworks.Hopfield.Basic
import LeanPool.NeuralNetworks.Hopfield.Energy
import LeanPool.NeuralNetworks.Hopfield.Convergence
import LeanPool.NeuralNetworks.LLM.GPT2.Core
import LeanPool.NeuralNetworks.LLM.GPT2.ByteArrayUtils
import LeanPool.NeuralNetworks.LLM.GPT2.Model
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Defs
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Lemmas
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.ComputeBounds

/-!
# Neural Networks

Source: url:https://github.com/or4nge19/NeuralNetworks
Authors: Matteo Cipollina, Alok Singh
Status: verified
Main declarations: `HopfieldNetwork`, `HopfieldState.convergence`, `LLM.GPT2.Model`
Tags: neural-networks, hopfield-networks, large-language-models, dynamical-systems
MSC: 68T07, 68T50, 37N40
-/

/-!
## Mathematical overview

Lean 4 formalizations of concepts related to neural networks and associated
mathematical structures, vendored from
<https://github.com/or4nge19/NeuralNetworks>.

This entry imports the Hopfield-network core (basic state space, energy
function, and convergence theorems), the GPT-2 LLM scaffolding
(core types, byte-array I/O, tensor views, and the high-level model
structure), and the floating-point foundation used by both. WIP modules and
files containing `sorry` from upstream are intentionally omitted.
-/
