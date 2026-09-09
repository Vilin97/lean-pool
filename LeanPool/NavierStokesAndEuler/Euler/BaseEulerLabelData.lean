/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.BaseEulerFlowL2
public import LeanPool.NavierStokesAndEuler.Euler.ParentPacketLabelData

@[expose] public section

/-! The three actual base-flow fields satisfy the source's fixed-H6
label bound with one explicit constant, independent of derivative order. -/

noncomputable section

namespace EulerBaseEulerParent.L2Data

open EulerParentPacketFrames EulerLpTranslation EulerParameterWordGevrey
  EulerPacketParentLabelBounds Set

variable {I : Input} (L : L2Data I)

def labelCost : ℝ :=
  1 + sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius (I.T*L.C) +
    sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius L.C +
    sobolevCoefficientAmplitude (Fin 3) 6 L.accelerationRadius L.accelerationAmplitude +
    sobolevCoefficientRadius (Fin 3) L.velocityRadius +
    sobolevCoefficientRadius (Fin 3) L.accelerationRadius

private theorem costs_nonneg :
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius (I.T*L.C) ∧
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.velocityRadius L.C ∧
    0 ≤ sobolevCoefficientAmplitude (Fin 3) 6 L.accelerationRadius L.accelerationAmplitude ∧
    0 ≤ sobolevCoefficientRadius (Fin 3) L.velocityRadius ∧
    0 ≤ sobolevCoefficientRadius (Fin 3) L.accelerationRadius :=
  ⟨sobolevCoefficientAmplitude_nonneg 6 L.velocityRadius (I.T*L.C)
      L.velocityRadius_nonneg (mul_nonneg I.T_pos.le L.C_nonneg),
    sobolevCoefficientAmplitude_nonneg 6 L.velocityRadius L.C L.velocityRadius_nonneg L.C_nonneg,
    sobolevCoefficientAmplitude_nonneg 6 L.accelerationRadius L.accelerationAmplitude
      L.accelerationRadius_nonneg L.accelerationAmplitude_nonneg,
    sobolevCoefficientRadius_nonneg L.velocityRadius L.velocityRadius_nonneg,
    sobolevCoefficientRadius_nonneg L.accelerationRadius L.accelerationRadius_nonneg⟩

theorem labelCost_one : 1 ≤ L.labelCost := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  dsimp [labelCost]
  linarith

theorem displacement_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.displacementField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.displacementField t)
    (I.T*L.C) L.velocityRadius L.labelCost (mul_nonneg I.T_pos.le L.C_nonneg)
    L.velocityRadius_nonneg (L.displacementField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith

theorem velocity_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.velocityField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.velocityField t)
    L.C L.velocityRadius L.labelCost L.C_nonneg L.velocityRadius_nonneg (L.velocityField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith

theorem acceleration_labelBound (t : Icc (0 : ℝ) I.T) :
    HasLabelBound L.labelCost (L.accelerationField t) := by
  obtain ⟨h1,h2,h3,h4,h5⟩ := L.costs_nonneg
  apply SmoothL2Field.hasLabelBound_of_jet_bound (L.accelerationField t)
    L.accelerationAmplitude L.accelerationRadius L.labelCost L.accelerationAmplitude_nonneg
    L.accelerationRadius_nonneg (L.accelerationField_bound t)
  · dsimp [labelCost]; linarith
  · dsimp [labelCost]; linarith

def labelData (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) :
    LabelData (I.parent ell hell hell1) where
  K := L.labelCost
  K_one := L.labelCost_one
  displacement := L.displacementField
  velocity := L.velocityField
  acceleration := L.accelerationField
  displacement_match _ _ := rfl
  velocity_match := L.velocityField_apply
  acceleration_match := L.accelerationField_apply
  displacement_bound := L.displacement_labelBound
  velocity_bound := L.velocity_labelBound
  acceleration_bound := L.acceleration_labelBound

end EulerBaseEulerParent.L2Data
