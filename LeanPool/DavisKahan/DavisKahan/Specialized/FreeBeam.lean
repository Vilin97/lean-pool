/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.All
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamClassicalReal
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamDoubleTangent
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenbasis
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenvalueSequence
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenvalueSequenceReal
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpace
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceReal
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamInPlaneAngle
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9Real
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrum
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrumReal
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTangent
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTrialReal
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamWeinberger

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/

@[expose] public section
