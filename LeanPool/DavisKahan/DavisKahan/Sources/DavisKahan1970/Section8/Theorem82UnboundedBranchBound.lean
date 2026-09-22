/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82Unbounded
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.UnboundedDirectedGapBound
import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Polar.SelfAdjointCompletion

/-!
# The static branch bound for Theorem 8.2 at unbounded scope

Theorem 8.2's closed quarter branch is the paper's connectedness step, and
`Theorem82Unbounded.lean` carries it as a hypothesis.  This module discharges it
on the part of the printed range where a *static* argument reaches.

The `sin Θ` theorem at unbounded scope, read at the operator norm, gives

```text
(δ/2) · directedGap P Q ≤ ‖H‖
```

from Theorem 8.2's own printed hypotheses -- the separation between the
unperturbed block on `P`, whose spectrum the theorem places in
`[β − δ/2, α + δ/2]`, and the perturbed block on `Qᗮ`, whose spectrum it places
off `(β − δ, α + δ)`.  So `directedGap P Q ≤ 2‖H‖/δ`, and the closed branch is
free whenever `2‖H‖/δ ≤ √2/2`, that is `‖H‖ ≤ (√2/4) δ`.

The printed hypothesis is `‖H‖ < δ/2`, so this covers a strict sub-interval.
The module docstring of `Theorem82Unbounded.lean` records what the rest costs.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

/-- **Davis--Kahan 1970, Theorem 8.2's acute conclusion at unbounded ambient
scope, with the closed branch discharged.**

`Theta < pi/4` from Theorem 8.2's printed hypotheses alone on the sub-range
`2‖H‖ ≤ (sqrt 2 / 2) delta`, that is `‖H‖ ≤ (sqrt 2 / 4) delta`.  Nothing is
carried that the paper does not print except that inequality, which is stronger
than the printed `‖H‖ < delta / 2`.

Two separations appear, and both are printed.  `hgap` is the `sin 2Theta`
theorem's own gap on the perturbed blocks at `Q`, which gives
`delta ‖sin 2Theta‖ ≤ 2 ‖H‖`.  `hgapHalf` is Theorem 8.2's extra hypothesis
`spec(A_0) ⊆ [beta - delta/2, alpha + delta/2]`, in the form the unbounded
`sin Theta` theorem consumes: it separates the unperturbed block on `P` from the
perturbed block on `Q^perp` by `delta/2`, which is exactly the distance the
printed containments leave.

`hcross` is Section 3's standing assumption (3.5), which is what turns the
directed bound into the symmetric one; the module docstring records why the rest
of the printed range needs the paper's connectedness argument. -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_smallPerturbation_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]

    {A : Hc →ₗ.[ℂ] Hc} (hA : IsSelfAdjoint A)
    (Hop : Hc →L[ℂ] Hc) (hHop : Hop.IsSymmetric)
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hPred : TauCeti.LinearPMap.ReducesSubspace A P)
    (hQred : TauCeti.LinearPMap.ReducesSubspace
      (TauCeti.LinearPMap.addBounded A Hop) Q)
    {δ : ℝ} (hδ : 0 < δ)
    (hgap : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Q hQred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ)
    (hgapHalf : FormBoundedSylvesterGap
      (TauCeti.LinearPMap.reducingRestriction A P hPred)
      (TauCeti.LinearPMap.reducingRestriction
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) (δ / 2))
    (hcross : DavisKahan.CrossedDefectsEquivalent P Q)
    (hsmall : 2 * ‖Hop‖ ≤ Real.sqrt 2 / 2 * δ) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hroot : Real.sqrt 2 < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0), Real.sqrt_nonneg 2]
  have hrootpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hdir := directedGap_le_of_reducingGap_unbounded_complex hA Hop hHop hPred hQred
    (by positivity) hgapHalf
  have hsym : P.projectionGap Q = P.directedProjectionGap Q :=
    DavisKahan.subspaceGap_eq_directedGap_of_crossedDefectsEquivalent P Q hcross
  have hclosed : P.projectionGap Q ≤ Real.sqrt 2 / 2 := by
    rw [hsym]
    nlinarith [hdir, hsmall, hδ]
  have hbound := norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
    hA Hop hHop hPred hQred hδ hgap
  rw [norm_sinTwoAngleOperator_eq_norm_block] at hbound
  have hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1 := by
    nlinarith [hbound, hsmall, hδ, hroot,
      norm_nonneg (TauCeti.DavisKahanExt.sinTwoAngleOperator P Q)]
  exact theorem8_2_branch_maximalAngle_lt_unbounded_complex hclosed hcross.symm hblock

end

end Section8
end DavisKahan1970
end TauCeti
