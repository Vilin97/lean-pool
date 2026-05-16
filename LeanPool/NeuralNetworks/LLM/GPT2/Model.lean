/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Alok Singh
-/

import LeanPool.NeuralNetworks.LLM.GPT2.Core
import LeanPool.NeuralNetworks.LLM.GPT2.TensorView.ComputeBounds

namespace LLM.GPT2

--  Section 4: GPT-2 Structures

structure Config where
  maxSeqLen : Nat       := 1024
  vocabSize : Nat       := 50257
  paddedVocabSize : Nat := 50304
  numLayers : Nat       := 12
  numHeads : Nat        := 12
  channels : Nat        := 768
  deriving Repr, Inhabited

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

structure Model (s : Type) where
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
