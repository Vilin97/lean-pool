/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.LLM.GPT2.Core
import LeanPool.HopfieldNet.LLM.GPT2.TensorView.ComputeBounds

namespace LLM.GPT2

set_option linter.dupNamespace false

--  Section 4: GPT-2 Structures

structure Config where
  maxSeqLen : Nat       := 1024
  vocabSize : Nat       := 50257
  paddedVocabSize : Nat := 50304
  numLayers : Nat       := 12
  numHeads : Nat        := 12
  channels : Nat        := 768
  deriving Repr, Inhabited

/--
`ParameterTensors` is a structure that encapsulates all the parameter tensors required
for a GPT-2 style transformer model layer. Each field represents a specific learnable parameter
 tensor used in various components of the model, such as embeddings, layer normalizations,
 attention mechanisms, and feed-forward networks.

- `wte`: Token embedding weights.
- `wpe`: Positional embedding weights.
- `ln1w`: Layer normalization 1 weights.
- `ln1b`: Layer normalization 1 biases.
- `qkvw`: Query, key, and value projection weights for self-attention.
- `qkvb`: Query, key, and value projection biases for self-attention.
- `attprojw`: Output projection weights for the attention mechanism.
- `attprojb`: Output projection biases for the attention mechanism.
- `ln2w`: Layer normalization 2 weights.
- `ln2b`: Layer normalization 2 biases.
- `fcw`: Feed-forward network (intermediate) weights.
- `fcb`: Feed-forward network (intermediate) biases.
- `fcprojw`: Feed-forward network (output) projection weights.
- `fcprojb`: Feed-forward network (output) projection biases.
- `lnfw`: Final layer normalization weights.
- `lnfb`: Final layer normalization biases.

All fields are parameterized by the type `s`, which represents the underlying
 storage or data type of the tensors.
-/
structure ParameterTensors (s : Type) where
  wte : TensorView s
  wpe : TensorView s
  ln1w : TensorView s
  ln1b : TensorView s
  qkvw : TensorView s
  qkvb : TensorView s
  attprojw : TensorView s
  attprojb : TensorView s
  ln2w : TensorView s
  ln2b : TensorView s
  fcw : TensorView s
  fcb : TensorView s
  fcprojw : TensorView s
  fcprojb : TensorView s
  lnfw : TensorView s
  lnfb : TensorView s
  deriving Repr

/--
`ActivationTensors` is a structure that holds the intermediate activation tensors produced during the
forward pass of a GPT-2 model layer. Each field represents a specific tensor at a particular stage of
computation, such as encoded inputs, layer normalization statistics, attention weights, feedforward activations,
and output logits. This structure is parameterized by the type `s`, which typically represents the storage or data type of the tensors.

Fields:
- `encoded`: The input tensor after initial embedding or encoding.
- `ln1`: Output of the first layer normalization.
- `ln1Mean`: Mean value computed during the first layer normalization.
- `ln1Rstd`: Reciprocal standard deviation from the first layer normalization.
- `qkv`: Concatenated query, key, and value tensors for attention.
- `attWeights`: Attention weights computed from the attention mechanism.
- `attproj`: Output of the attention projection.
- `residual2`: Residual connection after attention.
- `ln2`: Output of the second layer normalization.
- `ln2Mean`: Mean value computed during the second layer normalization.
- `ln2Rstd`: Reciprocal standard deviation from the second layer normalization.
- `fch`: Output of the first feedforward (fully connected) layer.
- `fchGelu`: Output after applying the GELU activation to `fch`.
- `fcproj`: Output of the second feedforward (fully connected) projection.
- `residual3`: Residual connection after the feedforward block.
- `lnf`: Output of the final layer normalization.
- `lnfMean`: Mean value computed during the final layer normalization.
- `lnfRstd`: Reciprocal standard deviation from the final layer normalization.
- `logits`: Output logits before softmax.
- `probs`: Probabilities after applying softmax to the logits.
- `losses`: Computed losses for the current batch or sequence.

This structure is useful for debugging, visualization, or analysis of the model's internal computations.
-/
structure ActivationTensors (s : Type) where
  encoded : TensorView s
  ln1 : TensorView s
  ln1Mean : TensorView s
  ln1Rstd : TensorView s
  qkv : TensorView s
  attWeights : TensorView s
  attproj : TensorView s
  residual2 : TensorView s
  ln2 : TensorView s
  ln2Mean : TensorView s
  ln2Rstd : TensorView s
  fch : TensorView s
  fchGelu : TensorView s
  fcproj : TensorView s
  residual3 : TensorView s
  lnf : TensorView s
  lnfMean : TensorView s
  lnfRstd : TensorView s
  logits : TensorView s
  probs : TensorView s
  losses : TensorView s
  deriving Repr

/--
The `GPT2` structure encapsulates the state and parameters of a GPT-2 model instance.

Parameters:
- `s : Type` : The state thread type for Lean's `ST` monad, ensuring safe mutable state.

Fields:
- `config : Config` : The configuration settings for the GPT-2 model (e.g., layer sizes, hyperparameters).
- `paramsMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer holding model parameters.
- `gradsMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer holding gradients of the parameters.
- `actsMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer holding activations.
- `gradsActsMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer holding gradients of activations.
- `mMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer for the first moment estimates (e.g., for Adam optimizer).
- `vMemoryRef : ST.Ref s ByteArray` : Reference to the memory buffer for the second moment estimates (e.g., for Adam optimizer).
- `params : ParameterTensors s` : Structured representation of model parameters.
- `grads : ParameterTensors s` : Structured representation of parameter gradients.
- `acts : ActivationTensors s` : Structured representation of activations.
- `gradsActs : ActivationTensors s` : Structured representation of activation gradients.
- `numParameters : Nat` : Total number of model parameters.
- `numActivations : Nat` : Total number of activations in the model.
-/
structure GPT2 (s : Type) where
  config : Config
  paramsMemoryRef : ST.Ref s ByteArray
  gradsMemoryRef : ST.Ref s ByteArray
  actsMemoryRef : ST.Ref s ByteArray
  gradsActsMemoryRef : ST.Ref s ByteArray
  mMemoryRef : ST.Ref s ByteArray
  vMemoryRef : ST.Ref s ByteArray
  params : ParameterTensors s
  grads : ParameterTensors s
  acts : ActivationTensors s
  gradsActs : ActivationTensors s
  numParameters : Nat
  numActivations : Nat

end LLM.GPT2
