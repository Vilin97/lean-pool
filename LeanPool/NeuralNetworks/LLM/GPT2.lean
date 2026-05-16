/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Alok Singh
-/

import LeanPool.NeuralNetworks.LLM.GPT2.Core
import LeanPool.NeuralNetworks.LLM.GPT2.ByteArrayUtils
import LeanPool.NeuralNetworks.LLM.GPT2.Model
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Defs
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Lemmas
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.ComputeBounds

/-!
# GPT-2

Formalization of aspects of the GPT-2 model: core constants and types,
byte-array I/O utilities, the `TensorView` library, and the top-level model
structure.
-/
