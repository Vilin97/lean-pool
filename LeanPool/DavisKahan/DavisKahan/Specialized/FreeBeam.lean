/-
Copyright (c) 2026 Jon Crall, Edward Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Edward Wang
-/

import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.All
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamClassicalReal
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamDoubleTangent
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenbasis
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenvalueSequence
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamEigenvalueSequenceReal
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpace
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceReal
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamFormSpaceScalar
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamInPlaneAngle
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSection9Real
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrum
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamSpectrumReal
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTangent
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTrialReal
import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamWeinberger

/-! Supporting modules for Davis–Kahan rotation of eigenvectors. -/
