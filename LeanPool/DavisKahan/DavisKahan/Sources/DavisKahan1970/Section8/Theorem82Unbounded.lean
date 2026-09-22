/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTwoTheta.QuarterAngleUnbounded
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Ideals.NormalizedUnitaryInvariantNormExamples
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.RealAngleIdentification
import LeanPool.DavisKahan.DavisKahan.Geometry.Angle.DoubleAngleGapBound

/-!
# Theorem 8.2's acute branch at unbounded scope

Davis--Kahan add to the `sin 2Θ` theorem's hypotheses a smallness condition --
`‖H‖ < δ/2` or `‖R‖ < δ/2` -- and a spectral containment `spec(A₀) ⊆
[β − δ/2, α + δ/2]`, and conclude both the double-angle estimate and `Θ < π/4`.

## What Theorem 8.1 does *not* give here

**Corrected 2026-09-05.**  An earlier version of this module claimed the acute
conclusion is Theorem 8.1's closed branch plus the double-angle bound, so that
`hclosed` below was one derivation away from being free.  That is wrong, and the
reason is a hypothesis difference in the source:

* Theorem 8.1 opens "assume the hypotheses of the `tan 2θ` theorem", and the
  `tan 2θ` theorem carries the **strong off-diagonal hypothesis** `H₀ = H₁ = 0`;
* Theorem 8.2 opens "add to the hypotheses of the `sin 2θ` theorem", and the
  `sin 2θ` theorem carries **no** off-diagonality.

So Theorem 8.1 is unavailable at Theorem 8.2's hypotheses, and the closed branch
has to come from somewhere else.

## What the double-angle estimate alone gives, and where it stops

Writing `γ = ‖H‖` and `κ = 2γ/δ < 1`, the printed estimate `δ‖sin 2Θ‖ ≤ 2‖H‖`
says `2g√(1 − g²) ≤ κ` for `g = subspaceGap P Q`, which is a *dichotomy*

```text
g ≤ σ₋(κ) = sin(½ arcsin κ)   or   g ≥ σ₊(κ) = cos(½ arcsin κ),
```

with `σ₋ < √2/2 ≤ σ₊`.  The printed conclusion is exactly the low branch, and
the paper's homotopy exists to exclude the high one.

Two elementary bounds are available at Theorem 8.2's hypotheses and both fall
short of excluding it:

* the `sin Θ` theorem between `A` on `P` (spectrum in `[β − δ/2, α + δ/2]`) and
  `A + H` on `Qᗮ` (spectrum off `(β − δ, α + δ)`) separates by `δ/2` and gives
  `g ≤ 2γ/δ = κ`;
* sharpening it through `Q₀ = E_A([β − γ, α + γ])` -- which contains `P`,
  because `spec(A) ⊆ [β − γ, α + γ] ∪ exterior` forces `spec(A₀)` into the
  band -- separates by `δ − γ` and gives `g ≤ γ/(δ − γ)`.

`κ < σ₊(κ)` holds exactly when `κ < √3/2`, and `γ/(δ − γ) < √2/2` exactly when
`γ < (2 − √2)δ/2 ≈ 0.414 δ`.  So the static route reaches `γ < (√3/4) δ` and the
printed hypothesis is `γ < δ/2`.  The gap is real, not an artefact of a lossy
step.

## The remaining step

The connectedness argument that closes the rest of the range does **not** need
Riesz integrals or a continuation framework: the bounded proof
`theorem8_2_perturbationHalfGap_complex` already has the right bootstrap, at the
*constant* threshold `√2/2`, and only its bounded Riesz continuity has to be
replaced.  With `γ = ‖H‖`, `l = β − γ`, `r = α + γ`, `d = δ − 2γ > 0`, and the
path `B_t = (A + H) − tH` carrying `R_t = specRange B_t (centralBand l r d)`:

* `centralBand l r d = Ioo (β − δ/2) (α + δ/2)` is exactly the extra interval
  Theorem 8.2 prints, so the band is not a second moving datum;
* `d · subspaceGap R_s R_t ≤ |s − t| γ`, from
  `directedGap_le_of_reducingGap_unbounded_complex` in each orientation, is the
  continuity — no Riesz projector appears;
* at each `t` the `sin 2Θ` estimate instantiated at `A := B_t`, `Hop := tH`
  keeps the *fixed printed gap* `δ` at `Q`, because `B_t + tH = A + H`, and gives
  `δ ‖sin 2Θ (R_t, Q)‖ ≤ 2tγ`, hence `f t < √2/2` whenever `f t ≤ √2/2`;
* `f 0 = 0`, `f` continuous, and `P ≤ R₁` finish it.

What is missing is one narrow lemma: the unbounded analogue of
`realSpectrum_add_subset_of_gap`, that `spectrum B_t ⊆ Icc l r ∪ gapExterior l r d`
for `t ∈ [0,1]`.  `GOAL.md` §10.4 carries the full plan.

## What this module does prove

* the `sin 2Θ` estimate at unbounded ambient scope, read at the operator norm --
  which is possible only because the operator norm is the first Ky Fan norm and
  therefore a member of the source norm class;
* that the two spellings of `sin 2Θ` have the same norm;
* the acute conclusion **from** the closed branch, which is where the branch
  selection above plugs in.

The closed branch is carried as an explicit hypothesis here, and it is the
paper's connectedness step, not a missing translation.
`Theorem82UnboundedBranchBound.lean` discharges it from the printed hypotheses
alone on `2‖H‖ ≤ (√2/2) δ`, using the first of the two static bounds above.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open DavisKahan
open DavisKahan.ExactSinTheta
open TauCeti.DavisKahan.Sylvester

noncomputable section

universe v

/-- **The `sin 2Θ` estimate at the operator norm, unbounded ambient scope.**

The operator norm is the first Ky Fan norm, hence a member of the source norm
class, so the printed universal-norm estimate specializes to it. -/
theorem norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
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
        (TauCeti.LinearPMap.addBounded A Hop) Qᗮ hQred.orthogonal) δ) :
    δ * ‖TauCeti.DavisKahan.Angle.sinTwoAngleOperator P Q‖ ≤ 2 * ‖Hop‖ := by
  set N : NormalizedUnitaryInvariantNorm.{0, v} ℂ :=
    kyFanNormalizedUnitaryInvariantNorm (𝕜 := ℂ) 1 one_pos with hN
  obtain ⟨-, hle⟩ := sinTwoTheta_ambient_unbounded_perturbedGap_normalizedUIN_complex
    N hA Hop hHop hPred hQred hδ hgap
    (mem_kyFanNormalizedUnitaryInvariantNorm 1 one_pos Hop)
  rw [hN] at hle
  rw [gauge_kyFanNormalizedUnitaryInvariantNorm 1 one_pos,
    gauge_kyFanNormalizedUnitaryInvariantNorm 1 one_pos,
    kyFanApproximationGauge_one, kyFanApproximationGauge_one] at hle
  exact hle

/-- **Davis--Kahan 1970, Theorem 8.2's acute conclusion at unbounded ambient
scope, perturbation branch.**

`Theta < pi/4` from the closed quarter branch and a strict contraction.

* The **closed branch** `‖P_P − P_Q‖ ≤ √2/2` is the paper's connectedness step.
  It is a hypothesis here, and the module docstring says exactly why: Theorem 8.1
  cannot supply it, because Theorem 8.1 inherits the `tan 2θ` theorem's
  off-diagonality `H₀ = H₁ = 0` and Theorem 8.2 inherits the `sin 2θ` theorem's
  hypotheses, which have none.
* The **strict contraction** is stated on the one-sided block
  `2 P_{P^perp} P_Q P_P`, which is what the bootstrap comparison consumes.
  `norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex` above supplies
  the same bound for the functional-calculus `sin 2Theta`, and
  `norm_sinTwoAngleOperator_eq_norm_block` identifies the two norms. -/
theorem theorem8_2_branch_maximalAngle_lt_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    {P Q : Submodule ℂ Hc} [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
    (hclosed : P.projectionGap Q ≤ Real.sqrt 2 / 2)
    (hcross : DavisKahan.CrossedDefectsEquivalent Q P)
    (hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 :=
  DavisKahan.maximalAngle_lt_pi_div_four_of_le_of_norm_sinTwoAngle_lt_one
    P Q hcross hclosed hblock

/-- **The two spellings of `sin 2Theta` have the same norm.**

The unbounded estimate is proved for the functional-calculus `sin 2Theta`; the
bootstrap comparison that turns the closed branch into the open one consumes the
one-sided block `2 P_{U^perp} P_V P_U`.  Both have the norm of the directed
double-angle sine, which is symmetric in the pair because the *doubled* sines
have the same complete approximation-number sequence even though the undoubled
ones do not. -/
theorem norm_sinTwoAngleOperator_eq_norm_block
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    (U V : Submodule ℂ Hc) [U.HasOrthogonalProjection] [V.HasOrthogonalProjection] :
    ‖TauCeti.DavisKahan.Angle.sinTwoAngleOperator U V‖ =
      ‖TauCeti.DavisKahanExt.sinTwoAngleOperator U V‖ := by
  rw [TauCeti.DavisKahan.Angle.sinTwoAngleOperator_complex,
    TauCeti.DavisKahanExt.norm_sinTwoAngleOperatorC_eq_norm_directedSinTwoAngleOperatorC,
    TauCeti.DavisKahan.Angle.norm_sinTwoAngleOperator_eq_norm_directedSinTwoAngleOperatorC_swap]
  exact (TauCeti.DavisKahan.Angle.directedSinTwoAngleOperator_hasSameApproximationNumbers_swap
    U V).norm_eq

/-- **The acute conclusion from the printed smallness hypothesis.**

`‖H‖ < delta/2` and the closed branch give `Theta < pi/4`.  This is the
perturbation branch of Theorem 8.2 at unbounded ambient scope, with the closed
branch -- the paper's connectedness step -- still carried as a hypothesis.  See
the module docstring for what it would take to discharge it, and for why
Theorem 8.1 is not what discharges it. -/
theorem theorem8_2_branch_maximalAngle_lt_of_small_perturbation_unbounded_complex
    {Hc : Type v} [NormedAddCommGroup Hc] [InnerProductSpace ℂ Hc] [CompleteSpace Hc]
    [TopologicalSpace.SeparableSpace Hc]
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
    (hclosed : P.projectionGap Q ≤ Real.sqrt 2 / 2)
    (hcross : DavisKahan.CrossedDefectsEquivalent Q P)
    (hsmall : ‖Hop‖ < δ / 2) :
    TauCeti.DavisKahanExt.maximalAngle P Q < Real.pi / 4 := by
  have hbound := norm_sinTwoAngleOperator_le_of_perturbedGap_unbounded_complex
    hA Hop hHop hPred hQred hδ hgap
  rw [norm_sinTwoAngleOperator_eq_norm_block] at hbound
  have hblock : ‖TauCeti.DavisKahanExt.sinTwoAngleOperator P Q‖ < 1 := by
    nlinarith [hbound, hsmall, hδ,
      norm_nonneg (TauCeti.DavisKahanExt.sinTwoAngleOperator P Q)]
  exact theorem8_2_branch_maximalAngle_lt_unbounded_complex hclosed hcross hblock

end

end Section8
end DavisKahan1970
end TauCeti
