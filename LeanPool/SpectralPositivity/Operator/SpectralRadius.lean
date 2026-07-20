/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas
-/

import LeanPool.SpectralPositivity.Operator.JentzschProof
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Spectral Radius Equals Norm for Self-Adjoint Operators

For a self-adjoint operator T on a complex Hilbert space L²(Ω, μ),
the spectral radius satisfies r(T) = ‖T‖.

## Main result

`spectralRadius_eq_nnnorm_of_selfAdjoint` : For a self-adjoint bounded operator on
`Lp ℂ 2 μ`, the spectral radius (over ℂ) equals the operator norm.

## Implementation notes

The statement is formulated over ℂ (rather than ℝ) because:
1. The C⋆-algebra structure on `E →L[ℂ] E` is available in Mathlib, giving
   `IsSelfAdjoint.spectralRadius_eq_nnnorm` directly.
2. Over ℝ, `E →L[ℝ] E` lacks a `CStarAlgebra` instance (which requires
   `NormedAlgebra ℂ`), and the Gelfand formula for the spectral radius
   is only proved for complex Banach algebras in Mathlib.
3. The positivity-preserving hypothesis from JentzschProof.lean is orthogonal
   to this result — it is self-adjointness alone that implies r(T) = ‖T‖.

For the ℝ case, one can complexify (extend T to Lp ℂ 2 μ) and apply this result;
the complexified operator preserves self-adjointness and has the same norm and
spectral radius.

## References

- Reed–Simon I, Theorem VI.6
- Simon, *Trace Ideals*, Ch. 2
-/

noncomputable section

open MeasureTheory

/-- For a self-adjoint bounded operator T on a complex L² space,
the spectral radius equals the operator norm: r(T) = ‖T‖.

This is a direct consequence of the general C⋆-algebra result
`IsSelfAdjoint.spectralRadius_eq_nnnorm`, since `E →L[ℂ] E` is
a C⋆-algebra when `E` is a complex Hilbert space.

The `IsPositivityPreserving` hypothesis used elsewhere in the Jentzsch
proof is not needed here — self-adjointness suffices. -/
theorem spectralRadius_eq_nnnorm_of_selfAdjoint {Ω : Type*} [MeasureSpace Ω]
    (T : Lp ℂ 2 (volume : Measure Ω) →L[ℂ] Lp ℂ 2 (volume : Measure Ω))
    (hsa : IsSelfAdjoint T) :
    spectralRadius ℂ T = ‖T‖₊ :=
  hsa.spectralRadius_eq_nnnorm

end
