/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/
module

public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.Basic
public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.SpectralFiniteness
public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.CutoffProjector
public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.OpNormEigenvalue
public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.Approximation
public import LeanPool.CompactSpectral.Analysis.InnerProductSpace.CompactSelfAdjoint.SpectralTheorem
import Mathlib.Tactic.Positivity.Finset

/-!
# Compact self-adjoint operators on Hilbert spaces

This module bundles the spectral theory of compact self-adjoint operators.
-/

@[expose] public section
