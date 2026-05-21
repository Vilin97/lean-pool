/-
Copyright (c) 2026 Matvei Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matvei Karatarakis
-/

import LeanPool.HopfieldNet.LLM.GPT2.Core
import LeanPool.HopfieldNet.LLM.GPT2.TensorView.Lemmas

namespace LLM.GPT2

set_option linter.dupNamespace false

-- = Section 4: GPT-2 Structures ==

/--
Configuration parameters for a GPT-2 style transformer model.

Fields:
- `maxSeqLen`: The maximum sequence length supported by the model (default: 1024).
- `vocabSize`: The size of the vocabulary (default: 50257).
- `paddedVocabSize`: The vocabulary size after padding, typically for efficient computation (default: 50304).
- `numLayers`: The number of transformer layers in the model (default: 12).
- `numHeads`: The number of attention heads in each transformer layer (default: 12).
- `channels`: The dimensionality of the model's hidden representations (default: 768).
-/
structure Config where
  maxSeqLen : Nat       := 1024
  vocabSize : Nat       := 50257
  paddedVocabSize : Nat := 50304
  numLayers : Nat       := 12
  numHeads : Nat        := 12
  channels : Nat        := 768
  deriving Repr, Inhabited

/--
  `ParameterTensors` is a structure that holds all the parameter tensors required for a GPT-2 style transformer model.

  Fields:
  - `wte`: Token embedding tensor.
  - `wpe`: Positional embedding tensor.
  - `ln1w`: Array of layer normalization weights for the first layer norm in each transformer block (size: numLayers).
  - `ln1b`: Array of layer normalization biases for the first layer norm in each transformer block (size: numLayers).
  - `qkvw`: Array of query/key/value projection weights for each transformer block (size: numLayers).
  - `qkvb`: Array of query/key/value projection biases for each transformer block (size: numLayers).
  - `attprojw`: Array of attention output projection weights for each transformer block (size: numLayers).
  - `attprojb`: Array of attention output projection biases for each transformer block (size: numLayers).
  - `ln2w`: Array of layer normalization weights for the second layer norm in each transformer block (size: numLayers).
  - `ln2b`: Array of layer normalization biases for the second layer norm in each transformer block (size: numLayers).
  - `fcw`: Array of feed-forward network weights for each transformer block (size: numLayers).
  - `fcb`: Array of feed-forward network biases for each transformer block (size: numLayers).
  - `fcprojw`: Array of feed-forward projection weights for each transformer block (size: numLayers).
  - `fcprojb`: Array of feed-forward projection biases for each transformer block (size: numLayers).
  - `lnfw`: Final layer normalization weight tensor.
  - `lnfb`: Final layer normalization bias tensor.

  Note: The arrays are expected to have length equal to the number of transformer layers (`numLayers`).
  The structure does not derive `Repr` by default due to the presence of arrays of `TensorView`s.
-/
structure ParameterTensors (s : Type) where
  wte : TensorView s
  wpe : TensorView s
  -- Repeating structure for each layer
  ln1w : Array (TensorView s) -- Size numLayers
  ln1b : Array (TensorView s)
  qkvw : Array (TensorView s)
  qkvb : Array (TensorView s)
  attprojw : Array (TensorView s)
  attprojb : Array (TensorView s)
  ln2w : Array (TensorView s)
  ln2b : Array (TensorView s)
  fcw : Array (TensorView s)
  fcb : Array (TensorView s)
  fcprojw : Array (TensorView s)
  fcprojb : Array (TensorView s)
  -- Final layer norm
  lnfw : TensorView s
  lnfb : TensorView s
  -- No deriving Repr for now due to Arrays of TensorViews, can be added later if needed.

/--
`ActivationTensors` is a structure that holds intermediate activation tensors for a GPT-2 model layer.
Each field represents the output of a specific computation or transformation step in the model's forward pass.

- `encoded`: The initial encoded input tensor.
- `ln1`: Output tensor after the first layer normalization.
- `ln1Mean`: Mean values computed during the first layer normalization.
- `ln1Rstd`: Reciprocal standard deviation from the first layer normalization.
- `qkv`: Concatenated query, key, and value tensors for attention.
- `attWeights`: Attention weights tensor.
- `attproj`: Output tensor after the attention projection.
- `residual2`: Residual connection tensor after attention.
- `ln2`: Output tensor after the second layer normalization.
- `ln2Mean`: Mean values computed during the second layer normalization.
- `ln2Rstd`: Reciprocal standard deviation from the second layer normalization.
- `fch`: Output tensor from the first feed-forward (fully connected) layer.
- `fchGelu`: Output tensor after GELU activation in the feed-forward layer.
- `fcproj`: Output tensor after the second feed-forward (projection) layer.
- `residual3`: Residual connection tensor after the feed-forward block.
- `lnf`: Output tensor after the final layer normalization.
- `lnfMean`: Mean values computed during the final layer normalization.
- `lnfRstd`: Reciprocal standard deviation from the final layer normalization.
- `logits`: Output logits tensor before softmax.
- `probs`: Probability tensor after softmax.
- `losses`: Loss values tensor.

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
- `config` : The configuration settings for the GPT-2 model.
- `paramsMemoryRef` : Reference to the mutable memory region storing model parameters.
- `gradsMemoryRef` : Reference to the mutable memory region storing parameter gradients.
- `actsMemoryRef` : Reference to the mutable memory region storing activations.
- `gradsActsMemoryRef` : Reference to the mutable memory region storing activation gradients.
- `mMemoryRef` : Reference to the mutable memory region for optimizer's first moment estimates (e.g., Adam's "m").
- `vMemoryRef` : Reference to the mutable memory region for optimizer's second moment estimates (e.g., Adam's "v").
- `params` : The structured tensors representing model parameters.
- `grads` : The structured tensors representing gradients of the parameters.
- `acts` : The structured tensors representing activations.
- `gradsActs` : The structured tensors representing gradients of the activations.
- `numParameters` : The total number of model parameters.
- `numActivations` : The total number of activation values.

Note:
- The `GPT2` structure does not derive `Repr` if `ParameterTensors` does not support it.
- This structure is designed for use in a mutable state context, such as training or inference with in-place updates.
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
  -- No deriving Repr for GPT2 if ParameterTensors doesn't have it.

end LLM.GPT2
