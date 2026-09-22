/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.SpectralMeasure
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.LinearPMap.YosidaApproximation

/-!
# Spectral projections commute with the unitary group

`E_A(B)` commutes with `exp(itA)` for every Borel set `B` and every `t`.

This is the fact a block-diagonal argument needs: cutting a vector into spectral
pieces has to commute with the flow, or the blocks are not preserved by it.

The route is the one the Yosida construction already lays out, and no new
analysis is required at any step:

* spectral projections commute with the resolvent at every non-real point
  (`specProjection_comm_resolvent'`);
* the symmetric Yosida approximant is a linear combination of two resolvents,
  so it commutes too;
* an exponential of a commuting operator commutes (`commute_expTime_of_commute`);
* and `expLimit` is the strong limit of those exponentials, so commutation
  survives — a projection is continuous, and limits are unique.

## Sources

*Follows nothing in particular*: the commutation a block-diagonal argument needs between
spectral projections and the flow.

## Provenance

*New.*  Every ingredient is already in `SpectralMeasure.lean`,
`YosidaApproximation.lean` and `SkewAdjointExponential.lean`; this is the
composition none of them performs.
-/

public section

open scoped InnerProductSpace
open Complex Filter Topology

namespace TauCeti
namespace LinearPMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (B : Set ℝ) (hB : MeasurableSet B)

/-- A spectral projection commutes with the symmetric Yosida approximant, which
is a linear combination of two resolvents. -/
theorem specProjection_comm_yosidaApproxSym (n : ℕ+) :
    Commute (specProjection hA B hB) (yosidaApproximantSym hA n) := by
  have h1 : Commute (specProjection hA B hB) (resolventAtIn hA n) :=
    specProjection_comm_resolvent' hA (I_mul_pnat_im_ne_zero n)
      (mem_resolventSet_of_im_ne_zero hA (I_mul_pnat_im_ne_zero n)) B hB
  have h2 : Commute (specProjection hA B hB) (resolventAtNegIn hA n) :=
    specProjection_comm_resolvent' hA (neg_I_mul_pnat_im_ne_zero n)
      (mem_resolventSet_of_im_ne_zero hA (neg_I_mul_pnat_im_ne_zero n)) B hB
  rw [yosidaApproximantSym]
  exact (h1.add_right h2).smul_right (-((n : ℂ) ^ 2 / 2))

/-- A spectral projection commutes with each bounded exponential approximant. -/
theorem specProjection_comm_expApprox (n : ℕ+) (t : ℝ) :
    Commute (specProjection hA B hB) (expApprox hA n t) := by
  rw [expApprox_eq_expTime]
  exact commute_expTime_of_commute
    ((specProjection_comm_yosidaApproxSym hA B hB n).smul_right (Complex.I)).symm t

/-- **Spectral projections commute with the unitary group.**  Commutation with
the bounded approximants survives the strong limit. -/
theorem specProjection_expLimit_apply (t : ℝ) (ψ : H) :
    specProjection hA B hB (expLimit hA t ψ) = expLimit hA t (specProjection hA B hB ψ) := by
  have hstep : ∀ n : ℕ+,
      specProjection hA B hB (expApprox hA n t ψ)
        = expApprox hA n t (specProjection hA B hB ψ) := by
    intro n
    have h := congrArg (fun T : H →L[ℂ] H => T ψ)
      (specProjection_comm_expApprox hA B hB n t)
    simpa only [_root_.mul_apply_eq_comp] using h
  have hleft : Tendsto (fun n : ℕ+ => specProjection hA B hB (expApprox hA n t ψ))
      atTop (𝓝 (specProjection hA B hB (expLimit hA t ψ))) :=
    ((specProjection hA B hB).continuous.tendsto _).comp (tendsto_expLimitFun hA t ψ)
  have hright : Tendsto (fun n : ℕ+ => expApprox hA n t (specProjection hA B hB ψ))
      atTop (𝓝 (expLimit hA t (specProjection hA B hB ψ))) :=
    tendsto_expLimitFun hA t (specProjection hA B hB ψ)
  exact tendsto_nhds_unique (by simpa only [hstep] using hleft) hright

end LinearPMap
end TauCeti
