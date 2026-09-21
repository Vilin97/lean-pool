/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.SpectralTheory.Spectral
import LeanPool.SpectralTheory.Spectral.Cayley
import LeanPool.SpectralTheory.Spectral.Cayley.Basic
import LeanPool.SpectralTheory.Spectral.Cayley.Inverse
import LeanPool.SpectralTheory.Spectral.Cayley.Unitary
import LeanPool.SpectralTheory.Spectral.Helpers
import LeanPool.SpectralTheory.Spectral.PVM
import LeanPool.SpectralTheory.Spectral.PVM.Basic
import LeanPool.SpectralTheory.Spectral.PVM.Integral
import LeanPool.SpectralTheory.Spectral.PVM.Unbounded
import LeanPool.SpectralTheory.Spectral.Spectral
import LeanPool.SpectralTheory.Spectral.Spectral.CayleyCalculus
import LeanPool.SpectralTheory.Spectral.Spectral.Existence
import LeanPool.SpectralTheory.Spectral.Spectral.FuncCalc
import LeanPool.SpectralTheory.Spectral.Spectral.Intrinsic
import LeanPool.SpectralTheory.Spectral.Spectral.Polarization
import LeanPool.SpectralTheory.Spectral.Spectral.Uniqueness
import LeanPool.SpectralTheory.Spectral.Stone
import LeanPool.SpectralTheory.Spectral.Stone.Generator
import LeanPool.SpectralTheory.Spectral.Stone.Intrinsic
import LeanPool.SpectralTheory.Spectral.Stone.SelfAdjoint
import LeanPool.SpectralTheory.Spectral.Stone.Theorem
import LeanPool.SpectralTheory.SpectralStoneSolution

/-!
# lean-spectral-theory

Source: url:https://github.com/savarin/lean-spectral-theory
Authors: Ezzeri Esa
Status: verified
Main declarations: `PalomarSpectralStone.spectral_theorem_intrinsic`
Tags: functional-analysis
MSC: 47A10, 47B15
-/
