/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

module

public import LeanPool.LowWeightPauliDynamics.BlockNorm
public import LeanPool.LowWeightPauliDynamics.Constants.C0
public import LeanPool.LowWeightPauliDynamics.Constants.AssemblyBound
public import LeanPool.LowWeightPauliDynamics.Constants.ChainWeights
public import LeanPool.LowWeightPauliDynamics.Constants.Threshold
public import LeanPool.LowWeightPauliDynamics.Constants.Entry
public import LeanPool.LowWeightPauliDynamics.Constants.PartFactor
public import LeanPool.LowWeightPauliDynamics.Constants.StepSum
public import LeanPool.LowWeightPauliDynamics.Constants.Total
public import LeanPool.LowWeightPauliDynamics.Ladder.Defs
public import LeanPool.LowWeightPauliDynamics.Ladder.Assembly
public import LeanPool.LowWeightPauliDynamics.Ladder.ChainBound
public import LeanPool.LowWeightPauliDynamics.Ladder.HockeyStick
public import LeanPool.LowWeightPauliDynamics.Ladder.MultiJump
public import LeanPool.LowWeightPauliDynamics.Ladder.Recursion
public import LeanPool.LowWeightPauliDynamics.Ladder.Weighted
public import LeanPool.LowWeightPauliDynamics.Pauli.Basic
public import LeanPool.LowWeightPauliDynamics.Pauli.Branch
public import LeanPool.LowWeightPauliDynamics.Pauli.Coeff
public import LeanPool.LowWeightPauliDynamics.Pauli.Count
public import LeanPool.LowWeightPauliDynamics.Pauli.Discard
public import LeanPool.LowWeightPauliDynamics.Pauli.DiscardWitness
public import LeanPool.LowWeightPauliDynamics.Pauli.Flow
public import LeanPool.LowWeightPauliDynamics.Pauli.LayerWitness
public import LeanPool.LowWeightPauliDynamics.Pauli.LayerFlow
public import LeanPool.LowWeightPauliDynamics.Pauli.LayerLadder
public import LeanPool.LowWeightPauliDynamics.Pauli.LayerError
public import LeanPool.LowWeightPauliDynamics.Pauli.LayerCounterexample
public import LeanPool.LowWeightPauliDynamics.Pauli.Matrix
public import LeanPool.LowWeightPauliDynamics.Pauli.Trace
public import LeanPool.LowWeightPauliDynamics.Pauli.Truncate
public import LeanPool.LowWeightPauliDynamics.Pauli.TrotterTruncate
public import LeanPool.LowWeightPauliDynamics.Pauli.TruncationError
public import LeanPool.LowWeightPauliDynamics.Pauli.Tensor
public import LeanPool.LowWeightPauliDynamics.Pauli.Weight
public import LeanPool.LowWeightPauliDynamics.Rotation
public import LeanPool.LowWeightPauliDynamics.RotationExp
public import LeanPool.LowWeightPauliDynamics.Schur

/-!
# Low-weight Pauli dynamics and truncation error

Source: arxiv:2601.15770, url:https://github.com/Jue-Xu/Lean4LPD/tree/ad0561661c46ca4c331d21104468e5dc65b2a028
Authors: Jue Xu
Status: verified
Main declarations: `Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model_of_source_regime`
Tags: quantum-information, pauli-operators, numerical-analysis, operator-norms, truncation-error
MSC: 81P68, 65L70, 47A30
-/
