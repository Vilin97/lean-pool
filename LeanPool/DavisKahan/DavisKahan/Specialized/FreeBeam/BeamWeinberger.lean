/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Sol
-/
module


public import LeanPool.DavisKahan.DavisKahan.Specialized.FreeBeam.BeamTangent

/-! # Beam Weinberger -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# Section 9, equation (9.8): unconditional beam statement

The historical route to (9.8) cites Weinberger and Lehmann.  The arrowhead
lower-root half is formalized in `WeinbergerComparison`; the angle half requires
coupled variational information and must not be reconstructed from independent
scalar eigenvalue lower bounds (see `secondScalarLowerBound_angleBound_counterexample`).

For the *statement actually printed in (9.8)*, no such external detour is
needed: the repository already proves the subsequent, sharper Davis--Kahan
one-vector estimates for the genuine perturbed beam.  Their numerator is `913`
where (9.8) uses `1291`, with the same denominators.  This file records the
unconditional consequence for the actual beam while keeping the historical
Weinberger-attribution question separate.
-/

namespace TauCeti
namespace DavisKahan
namespace FreeBeam
namespace Model

open DavisKahan1970.Section9

/-- **Equation (9.8), first line, for the genuine perturbed beam.**

This follows from the strictly sharper direct one-vector Davis--Kahan estimate,
not from replacing Weinberger's coupled angle hypotheses by an independent
scalar lower-eigenvalue bound. -/
theorem beam_equation_9_8_lower (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
      < ((1291 : ℝ) / 2500000 * ε) /
          (1 - (4227 : ℝ) / 10000000 * ε) := by
  have hdirect := beamTanPhi_low_lt_printed ε hε hε100
  have hden : 0 < 1 - (4227 : ℝ) / 10000000 * ε := by
    nlinarith
  apply hdirect.trans
  apply div_lt_div_of_pos_right _ hden
  nlinarith

/-- **Equation (9.8), second line, for the genuine perturbed beam.**

As for the first line, this is an unconditional consequence of the sharper
one-vector theorem.  It closes the numerical beam statement without asserting
the invalid implication that a scalar lower bound for the second eigenvalue by
itself supplies Weinberger's second-vector angle estimate. -/
theorem beam_equation_9_8_upper (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialTwo)
      < ((1291 : ℝ) / 2500000 * ε) /
          (1 - (7887 : ℝ) / 5000000 * ε) := by
  have hdirect := beamTanPhi_high_lt_printed ε hε hε100
  have hden : 0 < 1 - (7887 : ℝ) / 5000000 * ε := by
    nlinarith
  apply hdirect.trans
  apply div_lt_div_of_pos_right _ hden
  nlinarith

/-- Both lines of the printed equation (9.8), simultaneously, for the genuine
free-beam example. -/
theorem beam_equation_9_8 (ε : ℝ) (hε : 0 < ε) (hε100 : ε < 100) :
    beamTanPhi ε (centeredAffineLp trialOne)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (4227 : ℝ) / 10000000 * ε) ∧
      beamTanPhi ε (centeredAffineLp trialTwo)
        < ((1291 : ℝ) / 2500000 * ε) /
            (1 - (7887 : ℝ) / 5000000 * ε) :=
  ⟨beam_equation_9_8_lower ε hε hε100,
    beam_equation_9_8_upper ε hε hε100⟩

end Model
end FreeBeam
end DavisKahan
end TauCeti
