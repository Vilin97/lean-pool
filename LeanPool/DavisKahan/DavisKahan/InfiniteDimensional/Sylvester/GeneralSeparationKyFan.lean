/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.Sylvester.Basic
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ComplexificationApproximation
import LeanPool.DavisKahan.DavisKahan.SpectralTheory.Complexification.Spectrum
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.KyFanBochner

/-! # General Separation Ky Fan -/

open TauCeti.DavisKahan.Angle


open TauCeti.DavisKahan.ExactSinTheta

/-!
# The separated Sylvester estimate in every finite Ky Fan gauge

`DavisKahan/InfiniteDimensional/Sylvester/Basic.lean` proves the universal
Bhatia--Davis--McIntosh bound

```
d ‖X‖ ≤ (π/2) ‖C‖    whenever    A X − X B = C
```

on an arbitrary complex Hilbert space, for bounded self-adjoint `A`, `B` whose spectra are
`d`-separated.  That is the operator-norm statement.  This file upgrades it to *every*
finite Ky Fan gauge, still in arbitrary dimension, and then descends to real scalars.

## Why the upgrade is not automatic

The proof in `Basic.lean` estimates the Haagerup--Zsido Fourier reconstruction

```
X = ∫ m(t) • (e^{itA} C e^{-itB}) dt
```

with `‖∫ f‖ ≤ ∫ ‖f‖` and the unitary invariance of the operator norm.  Replacing the norm
by `kyFanGauge k` needs both ingredients again, and neither is formal: the gauge is not the
norm of the space being integrated in, so Minkowski's inequality has to be proved for it,
and its two-sided unitary invariance is a genuine ideal statement.  Both are paper-independent
and live upstream, in
`ForTauCeti/Analysis/OperatorIdeal/ApproximationNumber/KyFanBochner.lean`.

`ForTauCeti/Analysis/InnerProductSpace/Sylvester/SpectralDistance.lean` has the `π/2` Ky Fan
and arbitrary-unitarily-invariant-norm results already, but its spaces carry
`FiniteDimensional` instances, so it does not cover the statements here and neither
supersedes the other.

## The real case

The Fourier representation is intrinsically complex: `exp (i t A)` has no same-space real
formula.  The real theorem therefore complexifies the equation, applies the complex theorem,
and descends -- which is exact, because complexification changes no approximation number
(`kyFanApproximationGauge_complexify`).  Spectral separation is carried across by
`spectraSeparated_top_complexify` and self-adjointness by `complexify_isSymmetric_iff`.
-/

namespace TauCeti

open TauCeti
namespace DavisKahan.Sylvester

open TauCeti.DavisKahanExt

open DavisKahan.Foundation
open DavisKahan.Foundation.RealComplexification
open DavisKahan
open DavisKahan.ExactSinTheta
open DavisKahan.ExactSinTheta.ComplexificationApproximation
open TauCeti.ApproximationNumber
open TauCeti.RealComplexification
open MeasureTheory Set Filter
open scoped InnerProductSpace BigOperators

noncomputable section

universe u v

section Complex

variable {Ec : Type u} [NormedAddCommGroup Ec] [InnerProductSpace ℂ Ec]
  [CompleteSpace Ec]
variable {Fc : Type v} [NormedAddCommGroup Fc] [InnerProductSpace ℂ Fc]
  [CompleteSpace Fc]

/-- The unitary orbit appearing in the Fourier inverse preserves every finite Ky Fan gauge.

Sylvester-specific glue: the general two-sided invariance is
`ContinuousLinearMap.kyFanGauge_unitary_comp_comp`, and all this adds is that the two Fourier
group elements are unitary.  It is the Ky Fan analogue of `norm_unitary_left_right`. -/
private theorem kyFanGauge_unitaryGroup_orbit
    (A : Fc →L[ℂ] Fc) (hA : A.IsSymmetric)
    (B : Ec →L[ℂ] Ec) (hB : B.IsSymmetric)
    (t : ℝ) (C : Ec →L[ℂ] Fc) (k : ℕ) :
    (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t)).kyFanGauge k = C.kyFanGauge k :=
  ContinuousLinearMap.kyFanGauge_unitary_comp_comp
    (unitaryGroup_mem_unitary A hA t) (unitaryGroup_mem_unitary B hB (-t)) C k

/-- **The universal `π/2` Sylvester estimate in every finite Ky Fan gauge**, on arbitrary
complex Hilbert spaces.

For bounded self-adjoint `A`, `B` with `d`-separated spectra and `A X − X B = C`,

```
d · kyFanGauge k X ≤ (π/2) · kyFanGauge k C    for every k.
```

`norm_sylvester_le_of_generalSeparation` is the case `k = 1`. -/
theorem kyFan_sylvester_le_of_generalSeparation_complex
    {A : Fc →L[ℂ] Fc} {B : Ec →L[ℂ] Ec}
    {X C : Ec →L[ℂ] Fc}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) (k : ℕ) :
    d * X.kyFanGauge k ≤ (Real.pi / 2) * C.kyFanGauge k := by
  rw [separatedSylvester_reconstruction hA hB hd hsep X C hEq]
  unfold separatedSylvesterSolution
  have hint := separatedSylvester_integrable hA hB hd C
  calc
    d * (∫ t : ℝ, separatedSylvesterMultiplier d hd t •
          (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))).kyFanGauge k
        ≤ d * ∫ t : ℝ,
          (separatedSylvesterMultiplier d hd t •
            (unitaryGroup A t ∘L C ∘L unitaryGroup B (-t))).kyFanGauge k := by
      gcongr
      exact ContinuousLinearMap.kyFanGauge_integral_le k hint
    _ = d * ∫ t : ℝ,
          ‖separatedSylvesterMultiplier d hd t‖ * C.kyFanGauge k := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      rw [ContinuousLinearMap.kyFanGauge_smul,
        kyFanGauge_unitaryGroup_orbit A hA B hB t C k]
    _ = d * ((∫ t : ℝ, ‖separatedSylvesterMultiplier d hd t‖) * C.kyFanGauge k) := by
      rw [integral_mul_const]
    _ = (Real.pi / 2) * C.kyFanGauge k := by
      rw [l1_norm_separatedSylvesterMultiplier d hd]
      field_simp [ne_of_gt hd]

end Complex

section Real

variable {Er : Type u} [NormedAddCommGroup Er] [InnerProductSpace ℝ Er]
  [CompleteSpace Er]
variable {Fr : Type v} [NormedAddCommGroup Fr] [InnerProductSpace ℝ Fr]
  [CompleteSpace Fr]

omit [CompleteSpace Er] [CompleteSpace Fr] in
/-- Complexification commutes with the bounded Sylvester operator. -/
private theorem complexify_sylvesterOperator
    (A : Fr →L[ℝ] Fr) (B : Er →L[ℝ] Er) (X : Er →L[ℝ] Fr) :
    complexify (ContinuousLinearMap.sylvesterOperator A B X) =
      ContinuousLinearMap.sylvesterOperator (complexify A) (complexify B) (complexify X) := by
  simp [ContinuousLinearMap.sylvesterOperator, complexify_comp, complexify_sub]

omit [CompleteSpace Er] [CompleteSpace Fr] in
/-- A bounded real Sylvester equation complexifies exactly. -/
private theorem complexify_sylvesterEquation
    {A : Fr →L[ℝ] Fr} {B : Er →L[ℝ] Er} {X C : Er →L[ℝ] Fr}
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) :
    ContinuousLinearMap.sylvesterOperator (complexify A) (complexify B) (complexify X) =
      complexify C := by
  rw [← complexify_sylvesterOperator, hEq]

/-- **The universal `π/2` Sylvester estimate in every finite Ky Fan gauge**, on arbitrary
*real* Hilbert spaces.

The complex theorem applied to the complexified equation, read back through the exact
preservation of approximation numbers.  Nothing is lost in either direction: the
complexification of a real operator has literally the same approximation-number sequence. -/
theorem kyFan_sylvester_le_of_generalSeparation_real
    {A : Fr →L[ℝ] Fr} {B : Er →L[ℝ] Er}
    {X C : Er →L[ℝ] Fr}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C) (k : ℕ) :
    d * X.kyFanGauge k ≤ (Real.pi / 2) * C.kyFanGauge k := by
  have hfan := kyFan_sylvester_le_of_generalSeparation_complex
    ((complexify_isSymmetric_iff A).2 hA) ((complexify_isSymmetric_iff B).2 hB) hd
    (spectraSeparated_top_complexify hsep) (complexify_sylvesterEquation hEq) k
  have hX := kyFanApproximationGauge_complexify X k
  have hC := kyFanApproximationGauge_complexify C k
  rw [TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge,
    TauCeti.ApproximationNumber.kyFanApproximationGauge_eq_kyFanGauge] at hX hC
  rwa [hX, hC] at hfan

end Real

section RealIdeal

-- The ideal families are indexed by a single space universe, so the corollary below states
-- its two real spaces there; the finite Ky Fan theorem it consumes has no such constraint.
variable {Er Fr : Type v}
  [NormedAddCommGroup Er] [InnerProductSpace ℝ Er] [CompleteSpace Er]
  [NormedAddCommGroup Fr] [InnerProductSpace ℝ Fr] [CompleteSpace Fr]

/-- **The universal `π/2` Sylvester estimate for an arbitrary Ky-Fan-dominant unitarily
invariant ideal gauge**, on arbitrary real Hilbert spaces.

A thin corollary of the finite Ky Fan theorem above, which is the only analytic content:
the family's own dominance axiom reconstructs the ideal statement from all of the finite
gauges.  Membership of `X` is concluded rather than assumed. -/
theorem idealGauge_sylvester_le_of_generalSeparation_real
    (N : KyFanDominantIdealFamily (𝕜 := ℝ))
    {A : Fr →L[ℝ] Fr} {B : Er →L[ℝ] Er}
    {X C : Er →L[ℝ] Fr}
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    {d : ℝ} (hd : 0 < d)
    (hsep : SpectraSeparated A ⊤ B ⊤ d)
    (hEq : ContinuousLinearMap.sylvesterOperator A B X = C)
    (hC : N.Mem C) :
    N.Mem X ∧ d * N.gauge X ≤ (Real.pi / 2) * N.gauge C := by
  have hc : (0 : ℝ) < Real.pi / 2 := by positivity
  have hCscaled : N.Mem ((Real.pi / 2 : ℝ) • C) :=
    N.toSymmetricOperatorIdealFamily.smul_mem (Real.pi / 2 : ℝ) hC
  have hfan : ∀ k, d * kyFanApproximationGauge k X ≤
      kyFanApproximationGauge k ((Real.pi / 2 : ℝ) • C) := by
    intro k
    rw [kyFanApproximationGauge_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact kyFan_sylvester_le_of_generalSeparation_real hA hB hd hsep hEq k
  obtain ⟨hX, hg⟩ :=
    mem_and_scaled_gauge_le_of_all_scaled_kyFan_le N.toFanDominantIdealFamily hd hCscaled hfan
  refine ⟨hX, ?_⟩
  have hhom : N.gauge ((Real.pi / 2 : ℝ) • C) = (Real.pi / 2) * N.gauge C := by
    have h := N.toSymmetricOperatorIdealFamily.gaugeReal_smul (Real.pi / 2 : ℝ) hC
    rwa [Real.norm_eq_abs, abs_of_pos hc] at h
  rwa [hhom] at hg

end RealIdeal

end

end DavisKahan.Sylvester
end TauCeti
