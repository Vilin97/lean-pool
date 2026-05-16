/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Defs
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.Lemmas
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.ComputeBounds

/-!
# TensorView

A safe view over arrays used as tensor storage: definitions, supporting
lemmas, and bounds for index-flattening computations.
-/
