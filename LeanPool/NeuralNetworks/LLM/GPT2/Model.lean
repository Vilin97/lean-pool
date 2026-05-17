/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Alok Singh
-/

import LeanPool.NeuralNetworks.LLM.GPT2.Core
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.ComputeBounds

namespace LLM.GPT2

--  Section 4: GPT-2 Structures

/-- TODO. -/
structure Config where
  /-- TODO. -/
  maxSeqLen : Nat       := 1024
  /-- TODO. -/
  vocabSize : Nat       := 50257
  /-- TODO. -/
  paddedVocabSize : Nat := 50304
  /-- TODO. -/
  numLayers : Nat       := 12
  /-- TODO. -/
  numHeads : Nat        := 12
  /-- TODO. -/
  channels : Nat        := 768
  deriving Inhabited

/-- TODO. -/
structure ParameterTensors (s : Type) where
  /-- TODO. -/
  wte : TensorView s
  /-- TODO. -/
  wpe : TensorView s
  /-- TODO. -/
  ln1w : TensorView s
  /-- TODO. -/
  ln1b : TensorView s
  /-- TODO. -/
  qkvw : TensorView s
  /-- TODO. -/
  qkvb : TensorView s
  /-- TODO. -/
  attprojw : TensorView s
  /-- TODO. -/
  attprojb : TensorView s
  /-- TODO. -/
  ln2w : TensorView s
  /-- TODO. -/
  ln2b : TensorView s
  /-- TODO. -/
  fcw : TensorView s
  /-- TODO. -/
  fcb : TensorView s
  /-- TODO. -/
  fcprojw : TensorView s
  /-- TODO. -/
  fcprojb : TensorView s
  /-- TODO. -/
  lnfw : TensorView s
  /-- TODO. -/
  lnfb : TensorView s

/-- TODO. -/
structure ActivationTensors (s : Type) where
  /-- TODO. -/
  encoded : TensorView s
  /-- TODO. -/
  ln1 : TensorView s
  /-- TODO. -/
  ln1Mean : TensorView s
  /-- TODO. -/
  ln1Rstd : TensorView s
  /-- TODO. -/
  qkv : TensorView s
  /-- TODO. -/
  attWeights : TensorView s
  /-- TODO. -/
  attproj : TensorView s
  /-- TODO. -/
  residual2 : TensorView s
  /-- TODO. -/
  ln2 : TensorView s
  /-- TODO. -/
  ln2Mean : TensorView s
  /-- TODO. -/
  ln2Rstd : TensorView s
  /-- TODO. -/
  fch : TensorView s
  /-- TODO. -/
  fchGelu : TensorView s
  /-- TODO. -/
  fcproj : TensorView s
  /-- TODO. -/
  residual3 : TensorView s
  /-- TODO. -/
  lnf : TensorView s
  /-- TODO. -/
  lnfMean : TensorView s
  /-- TODO. -/
  lnfRstd : TensorView s
  /-- TODO. -/
  logits : TensorView s
  /-- TODO. -/
  probs : TensorView s
  /-- TODO. -/
  losses : TensorView s

/-- TODO. -/
structure Model (s : Type) where
  /-- TODO. -/
  config : Config
  /-- TODO. -/
  paramsMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  gradsMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  actsMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  gradsActsMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  mMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  vMemoryRef : ST.Ref s ByteArray
  /-- TODO. -/
  params : ParameterTensors s
  /-- TODO. -/
  grads : ParameterTensors s
  /-- TODO. -/
  acts : ActivationTensors s
  /-- TODO. -/
  gradsActs : ActivationTensors s
  /-- TODO. -/
  numParameters : Nat
  /-- TODO. -/
  numActivations : Nat

end LLM.GPT2
