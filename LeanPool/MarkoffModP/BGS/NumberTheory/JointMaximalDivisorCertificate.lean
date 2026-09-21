/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.NumberTheory.MaximalDivisorBounds

/-!
# Exact certificate at the paper's terminal obstruction

The published maximal-divisor computation stops at the reduced integer

`(863#)(53#)(13#)(7#)(5#) 3^3 2^5`.

Its central divisor-lattice coefficient is the paper's exact value
`C₉₃(n)`. The paper treats the two neighboring maximal-divisor counts
independently and therefore uses the square envelope `4 C^2`. The joint
`p - 1`, `p + 1` moment instead supplies `C^2 + 3J`, where the displayed
integer `J` is an exact tenth-root upper certificate.

All comparisons below are closed integer computations checked by Lean.
-/

namespace BGS.NumberTheory

/-- The reduced integer responsible for the published cutoff. -/
def publishedTerminalReducedInteger : ℕ :=
  344804838267768169319048795913558858218204726396462226085672206158143793783042367351629064411158183411576729661579236952954769470091851501268371488892117339245604283407662126578103043374612406105548170775523572783919769072224460076452087116657499868482554599063664473247688943813839202042578341146702180498643671937922409423337669168695270728922856540751624236363557097567988640618308214400000

/-- The exact value `C₉₃(n)` reported in the paper. -/
def publishedTerminalCentralCoefficient : ℕ :=
  3013671869689423302959704266406116383317724743440

/-- A tenth-root upper certificate for the joint neighboring divisor count. -/
def publishedTerminalJointProductEnvelope : ℕ :=
  183901584895411967004110876962572064564281061869576148842985488012286272296193902480021778244

/-- The new squared-sum envelope `C^2 + 3J`. -/
def publishedTerminalJointSquareEnvelope : ℕ :=
  publishedTerminalCentralCoefficient ^ 2 +
    3 * publishedTerminalJointProductEnvelope

/-- The displayed `J` really dominates the joint tenth-moment radicand.
The slightly looser `(n + 1)^2` form avoids any hidden square-root rounding. -/
theorem publishedTerminalJointProductEnvelope_certificate :
    2 ^ 457 * (publishedTerminalReducedInteger + 1) ^ 2 ≤
      publishedTerminalJointProductEnvelope ^ 10 := by
  native_decide

/-- The new envelope makes the paper's first-interval obstruction empty at
the exact reduced integer that caused the published algorithm to stop. -/
theorem publishedTerminalJointSquareEnvelope_succeeds :
    3 ^ 8 * publishedTerminalJointSquareEnvelope ^ 4 ≤
      32 * (publishedTerminalReducedInteger + 2) := by
  native_decide

/-- In contrast, the paper's independent envelope `4C^2` fails at this same
integer. This records that the improvement is structural, not a re-rounding
of the published computation. -/
theorem publishedTerminalIndependentSquareEnvelope_fails :
    32 * (publishedTerminalReducedInteger + 2) <
      3 ^ 8 * (4 * publishedTerminalCentralCoefficient ^ 2) ^ 4 := by
  native_decide

end BGS.NumberTheory
