/-
Copyright (c) 2026 Jue Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jue Xu
-/

import LeanPool.LowWeightPauliDynamics.BlockNorm
import LeanPool.LowWeightPauliDynamics.Constants.C0
import LeanPool.LowWeightPauliDynamics.Constants.AssemblyBound
import LeanPool.LowWeightPauliDynamics.Constants.ChainWeights
import LeanPool.LowWeightPauliDynamics.Constants.Threshold
import LeanPool.LowWeightPauliDynamics.Constants.Entry
import LeanPool.LowWeightPauliDynamics.Constants.PartFactor
import LeanPool.LowWeightPauliDynamics.Constants.StepSum
import LeanPool.LowWeightPauliDynamics.Constants.Total
import LeanPool.LowWeightPauliDynamics.Ladder.Defs
import LeanPool.LowWeightPauliDynamics.Ladder.Assembly
import LeanPool.LowWeightPauliDynamics.Ladder.ChainBound
import LeanPool.LowWeightPauliDynamics.Ladder.HockeyStick
import LeanPool.LowWeightPauliDynamics.Ladder.MultiJump
import LeanPool.LowWeightPauliDynamics.Ladder.Recursion
import LeanPool.LowWeightPauliDynamics.Ladder.Weighted
import LeanPool.LowWeightPauliDynamics.Pauli.Basic
import LeanPool.LowWeightPauliDynamics.Pauli.Branch
import LeanPool.LowWeightPauliDynamics.Pauli.Coeff
import LeanPool.LowWeightPauliDynamics.Pauli.Count
import LeanPool.LowWeightPauliDynamics.Pauli.Discard
import LeanPool.LowWeightPauliDynamics.Pauli.DiscardWitness
import LeanPool.LowWeightPauliDynamics.Pauli.Flow
import LeanPool.LowWeightPauliDynamics.Pauli.LayerWitness
import LeanPool.LowWeightPauliDynamics.Pauli.LayerFlow
import LeanPool.LowWeightPauliDynamics.Pauli.LayerLadder
import LeanPool.LowWeightPauliDynamics.Pauli.LayerError
import LeanPool.LowWeightPauliDynamics.Pauli.LayerCounterexample
import LeanPool.LowWeightPauliDynamics.Pauli.Matrix
import LeanPool.LowWeightPauliDynamics.Pauli.Trace
import LeanPool.LowWeightPauliDynamics.Pauli.Truncate
import LeanPool.LowWeightPauliDynamics.Pauli.TrotterTruncate
import LeanPool.LowWeightPauliDynamics.Pauli.TruncationError
import LeanPool.LowWeightPauliDynamics.Pauli.Tensor
import LeanPool.LowWeightPauliDynamics.Pauli.Weight
import LeanPool.LowWeightPauliDynamics.Rotation
import LeanPool.LowWeightPauliDynamics.RotationExp
import LeanPool.LowWeightPauliDynamics.Schur

/-!
# Low-weight Pauli dynamics and truncation error

Source: arxiv:2601.15770, url:https://github.com/Jue-Xu/Lean4LPD/tree/ad0561661c46ca4c331d21104468e5dc65b2a028
Authors: Jue Xu
Status: verified
Main declarations: `Lean4LPD.PauliString.pauliNorm_layerStep_error_le_model_of_source_regime`
Tags: quantum-information, pauli-operators, numerical-analysis, operator-norms, truncation-error
MSC: 81P68, 65L70, 47A30
-/
