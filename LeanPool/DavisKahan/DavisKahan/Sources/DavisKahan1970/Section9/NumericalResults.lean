/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamWeinberger
public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamInPlaneAngle
public import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section9.BeamDoubleTangentKyFan

/-! # Numerical Results -/

@[expose] public section

open TauCeti.DavisKahan.Angle


/-!
# Davis--Kahan 1970, Section 9: paper-exact numerical result surface

This module exposes the numerical conclusions of the Section 9 free-beam example
at the paper-facing namespace.  Every premise of these wrappers is discharged by
the genuine beam realization: there are no `TheoremOutputCertificate` fields and
no assumed Weinberger/Lehmann angle estimates.

The historical route to equation (9.8) uses external comparison results.  The
wrapper below instead uses the unconditional beam theorem already proved from the
subsequent, sharper one-vector Davis--Kahan argument, so the printed conclusion is
proved rather than imported as a hypothesis.

The final individual-eigenvector `omega_k` estimates are exposed by
`freeBeam_individualEigenvectorAngle_bounds` below, on the genuine perturbed beam, at the two
distinct constants the source prints.  `BeamInPlaneAngle.beamLowEigenvector_ritz_pairing`
supplies the in-plane argument the source performs after (9.9)--(9.11): it pairs each Ritz
vector with the eigenvector of the matching eigenvalue, bounds the angle by the `sqrt 7 / 10`
envelope, and — this is what makes the two printed denominators differ — records that the
smaller eigenvalue sits at or below `ritzLow eps`.  `NumericalBounds` then converts each
envelope into its printed decimal form.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section9

noncomputable section

open TauCeti.DavisKahan.FreeBeam.Model

/-- **Davis--Kahan 1970, equation (9.1), on the genuine free-beam example.** -/
theorem equation_9_1_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTheta ε < (811 : ℝ) / 500000 * ε :=
  equation_9_1 ε (beamSinTheta ε) hε (beamSinTheta_le ε)

/-- **Davis--Kahan 1970, equation (9.2), on the genuine free-beam example.** -/
theorem equation_9_2_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTwoTheta ε < (1 : ℝ) / 250 * ε :=
  equation_9_2 ε (beamSinTwoTheta ε) (beamSinTwoTheta_lt ε hε)

/-- **Davis--Kahan 1970, equation (9.3), on the genuine free-beam example.** -/
theorem equation_9_3_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinThetaSum ε < (109 : ℝ) / 50000 * ε :=
  equation_9_3 ε (beamSinThetaSum ε) hε (beamSinThetaSum_le ε)

/-- **Davis--Kahan 1970, equation (9.4), on the genuine free-beam example.** -/
theorem equation_9_4_freeBeam (ε : ℝ) (hε : 0 < ε) (_hε100 : ε < 100) :
    beamSinTwoThetaSum ε < (1 : ℝ) / 125 * ε :=
  equation_9_4 ε (beamSinTwoThetaSum ε) (beamSinTwoThetaSum_lt ε hε)

/-- **Davis--Kahan 1970, equation (9.5).**  Both Rayleigh--Ritz values are exposed
in the same source-facing statement. -/
theorem equation_9_5_freeBeam (ε : ℝ) (_hε : 0 < ε) (_hε100 : ε < 100) :
    ritzLow ε = ε / 2 * (1 - (Real.sqrt 3)⁻¹) ∧
      ritzHigh ε = ε / 2 * (1 + (Real.sqrt 3)⁻¹) :=
  ⟨equation_9_5_low ε, equation_9_5_high ε⟩

/-- **Davis--Kahan 1970, equation (9.6), including its two-term Ky Fan sentence.**
Both conclusions are proved for the genuine perturbed beam from `0 < ε < 100`. -/
theorem equation_9_6_freeBeam (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTheta ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanThetaSum ε
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanTheta_lt_printed ε hε hε100,
    beamTanThetaSum_lt_printed ε hε hε100⟩

/-- **Davis--Kahan 1970, equation (9.7), including its two-term Ky Fan sentence.**
Both conclusions are proved for the genuine perturbed beam from `0 < ε < 100`. -/
theorem equation_9_7_freeBeam (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanTwoTheta ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) ∧
      beamTanTwoThetaSum ε
        < ((1291 : ℝ) / 1250000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanTwoTheta_lt_printed ε hε hε100,
    beamTanTwoThetaSum_lt_printed ε hε hε100⟩

/-- **Davis--Kahan 1970, equation (9.8), both displayed individual-vector bounds.**

The paper derives these numbers through Weinberger/Lehmann comparison results.
Here the same printed conclusions are proved unconditionally for the genuine beam
from the later, strictly sharper one-vector Davis--Kahan estimates; no external
comparison theorem is left as a caller-supplied hypothesis. -/
theorem equation_9_8_freeBeam (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  beam_equation_9_8 ε hε hε100

/-- Read an individual-angle bound at an eigenvalue against the exact envelope taken at a Ritz
value.  Monotonicity of `c / (500 - x)` in `x`, nothing more; the Ritz coefficient is a
parameter so that the lower and upper envelopes are the same lemma. -/
private theorem le_individualAngleExactBound {ε lam a c : ℝ} (hε : 0 < ε) (hε100 : ε < 100)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hlam : lam ≤ ε * c)
    (h : a ≤ Real.sqrt 7 / 10 * ε / (500 - lam)) :
    a ≤ ((Real.sqrt 7 / 10) / 500 * ε) / (1 - (c / 500) * ε) := by
  have hd : (0 : ℝ) < 500 - ε * c := by nlinarith
  have hd2 : (0 : ℝ) < 1 - c / 500 * ε := by nlinarith
  have hnum : (0 : ℝ) ≤ Real.sqrt 7 / 10 * ε := by positivity
  refine h.trans ?_
  have hmono : Real.sqrt 7 / 10 * ε / (500 - lam) ≤ Real.sqrt 7 / 10 * ε / (500 - ε * c) :=
    div_le_div_of_nonneg_left hnum hd (by linarith)
  refine hmono.trans (le_of_eq ?_)
  rw [div_eq_div_iff hd.ne' hd2.ne']
  ring

private theorem ritzLowCoefficient_mem : 0 ≤ ritzLowCoefficient ∧ ritzLowCoefficient ≤ 1 := by
  have h3 : Real.sqrt 3 / 3 ≤ 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
  have h0 : (0 : ℝ) ≤ Real.sqrt 3 / 3 := by positivity
  constructor <;> · unfold ritzLowCoefficient; linarith

private theorem ritzHighCoefficient_mem : 0 ≤ ritzHighCoefficient ∧ ritzHighCoefficient ≤ 1 := by
  have h3 : Real.sqrt 3 / 3 ≤ 1 := by
    nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0), Real.sqrt_nonneg 3]
  have h0 : (0 : ℝ) ≤ Real.sqrt 3 / 3 := by positivity
  constructor <;> · unfold ritzHighCoefficient; linarith

/-- **Davis--Kahan 1970, Section 9, the final individual-eigenvector `omega_k` bounds**, on
the genuine perturbed free beam, at the two distinct constants the source prints.

Each trial Ritz vector is paired with the eigenvector of the correspondingly ordered
eigenvalue, and the angle between them satisfies the printed decimal bound:

```
omega_1 < 0.00053 eps / (1 - 0.00043 eps),      omega_2 < 0.00053 eps / (1 - 0.0016 eps).
```

The two denominators differ because the two envelopes are read at different Ritz values.  The
lower one needs `lambda_j <= ritzLow eps` for the smaller eigenvalue, which is the eigenvalue
placement `beamLowEigenvector_ritz_pairing` carries; the upper one needs only
`lambda_k <= ritzHigh eps`, from `beam_eigenvalue_le_ritzHigh`. -/
theorem freeBeam_individualEigenvectorAngle_bounds (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100)
    {j k : Fin 2} (hjk : j ≠ k)
    (hle : beamLowEigenvalue ε hε.le hε100 j ≤ beamLowEigenvalue ε hε.le hε100 k) :
    Real.arccos ‖inner ℂ (centeredAffineLp trialOne) (beamLowEigenvector ε hε.le hε100 j)‖
        < ((53 : ℝ) / 100000 * ε) / (1 - (43 : ℝ) / 100000 * ε) ∧
      Real.arccos ‖inner ℂ (centeredAffineLp trialTwo) (beamLowEigenvector ε hε.le hε100 k)‖
        < ((53 : ℝ) / 100000 * ε) / (1 - (1 : ℝ) / 625 * ε) := by
  obtain ⟨hjlow, -, hj, hk⟩ := beamLowEigenvector_ritz_pairing ε hε hε100 hjk hle
  have hkhigh : beamLowEigenvalue ε hε.le hε100 k ≤ ritzHigh ε :=
    beam_eigenvalue_le_ritzHigh ε hε (beamLowEigenvector_mem_domain ε hε.le hε100 k)
      (beamPerturbed_apply_beamLowEigenvector ε hε.le hε100 k)
      (by linarith [beamLowEigenvalue_lt_five_hundred ε hε.le hε100 k])
      (norm_beamLowEigenvector ε hε.le hε100 k)
  refine ⟨final_lower_individual_angle_bound ε _ hε hε100 ?_,
    final_upper_individual_angle_bound ε _ hε hε100 ?_⟩
  · exact le_individualAngleExactBound hε hε100 ritzLowCoefficient_mem.1
      ritzLowCoefficient_mem.2 (by simpa [ritzLow] using hjlow) hj
  · exact le_individualAngleExactBound hε hε100 ritzHighCoefficient_mem.1
      ritzHighCoefficient_mem.2 (by simpa [ritzHigh] using hkhigh) hk

/-- **The sharper one-vector Davis--Kahan bounds immediately following (9.8).**
These are the paper's two displayed `0.0003652` estimates for the specific Ritz
vectors, proved directly for the genuine beam. -/
theorem freeBeam_trialVector_tanAngle_bounds
    (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((913 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beamTanPhi_low_lt_printed ε hε hε100,
    beamTanPhi_high_lt_printed ε hε hε100⟩

end

end Section9
end DavisKahan1970
end TauCeti
