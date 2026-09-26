/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.Family.Schatten
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramResolvent

/-!
# The nuclear norm of a Gram operator is the squared Hilbert--Schmidt norm

`aₙ(X⋆X) = aₙ(X)²` turns any gauge of the Gram operator into a gauge of `X` at twice the
exponent.  Two instances of that principle matter, because they are the two that see `‖X‖`
itself rather than some other Schatten exponent — the `p = ∞` and `p = 1` ends of
`‖X⋆X‖_p = ‖X‖_{2p}²`:

```
‖X⋆X‖    = ‖X‖²        (operator norm, Schatten ∞)
‖X⋆X‖₁   = ‖X‖_HS²     (nuclear norm, Schatten 1)
```

The first is the C⋆-identity and already lives upstream as
`TauCeti.ApproximationNumber.norm_gramOperator`.  This module supplies the second, which is
not formal: it needs `aₙ(X⋆X) = aₙ(X)²` (`approximationNumber_gramOperator_complex`) together with
the
agreement of the Schatten-2 gauge with the basis-defined Hilbert--Schmidt gauge
(`ContinuousLinearMap.schattenENorm_two`), and neither is arithmetic.

Together the pair is exactly what a statement about the *squared* displacement `(1−W)⋆(1−W)`
needs in order to become a statement about the displacement `1−W`.

That is not an incidental use.  Davis and Kahan prove their whole-space extremality result
(Proposition 4.3) for `(1−V)⋆(1−V)`, and then observe that it also minimizes `‖1−V‖` in any
norm which is the square root of a unitarily invariant norm of `(1−V)⋆(1−V)` — naming the
operator norm and the Hilbert--Schmidt norm as the two such norms.  The pair above is that
observation, isolated from the Davis--Kahan setting.

The statement is in `ℝ≥0∞`, so it carries no finiteness side condition: `X` may fail to be
Hilbert--Schmidt, in which case both sides are `∞`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`; it has had no prior home.
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

open scoped ENNReal InnerProductSpace

namespace TauCeti
namespace ApproximationNumber

universe v

variable {E0 E1 : Type v}
  [NormedAddCommGroup E0] [InnerProductSpace ℂ E0] [CompleteSpace E0]
  [NormedAddCommGroup E1] [InnerProductSpace ℂ E1] [CompleteSpace E1]

/-- **The nuclear norm of a Gram operator is the square of the Hilbert--Schmidt norm.**

`‖X⋆X‖₁ = ‖X‖_HS²`, in `ℝ≥0∞` and hence with no trace-class or Hilbert--Schmidt hypothesis:
`X` is Hilbert--Schmidt exactly when `X⋆X` is trace class, and otherwise both sides are `∞`.

The proof is the singular-value computation.  Both sides are the sum `∑ₙ aₙ(X)²`: the left
because `aₙ(X⋆X) = aₙ(X)²` and the nuclear norm sums the approximation numbers, the right
because the Hilbert--Schmidt norm is the Schatten-2 gauge of the same sequence. -/
theorem nuclearENorm_gramOperator (X : E0 →L[ℂ] E1) :
    (gramOperator X).nuclearENorm = X.hilbertSchmidtENorm ^ 2 := by
  have hsum : (gramOperator X).nuclearENorm =
      ∑' n : ℕ, ENNReal.ofReal (X.approximationNumber n) ^ (2 : ℝ) := by
    rw [ContinuousLinearMap.nuclearENorm]
    refine tsum_congr fun n => ?_
    rw [approximationNumber_gramOperator_complex X n,
      ← Real.rpow_natCast (X.approximationNumber n) 2,
      ← ENNReal.ofReal_rpow_of_nonneg (X.approximationNumber_nonneg n) (by norm_num)]
    norm_num
  rw [hsum, ← ContinuousLinearMap.schattenENorm_two X, ContinuousLinearMap.schattenENorm,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

end ApproximationNumber
end TauCeti
