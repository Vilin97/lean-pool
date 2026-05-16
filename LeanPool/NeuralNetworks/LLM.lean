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
# Large Language Models

Formalization of components of large language models, organized around the
GPT-2 architecture: core types, byte-array I/O, tensor views, and the model
structure itself.
-/
