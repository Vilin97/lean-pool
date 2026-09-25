/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Transmission.Transmission

/-!
# Ordinary Brill--Noether witnesses from transmission rows

A transmission witness contains many ordinary rank witnesses: fixing one row
`(a,b)` gives a divisor of degree `g + χτ + a - b` whose rank is at least
`τ.s (a+1) b - 1`.  Any smaller target rank therefore yields `BNExists`.

This is the generic core needed later for the Grassmannian-transmission ⇒
`W^r_d` implication.
-/

namespace Utilities

/-- The marked twist attached to one transmission row. -/
def TransmissionTwist
    (G : CFGraph) (u v : G.V) (D : CFDiv G) (a b : ℤ) : CFDiv G :=
  D + a • oneChip u - b • oneChip v

/-- Exact degree of a transmission-row twist. -/
theorem degree_transmissionTwist
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    deg (TransmissionTwist G u v D a b) =
      (genus G : ℤ) + τ.χ + a - b := by
  simpa [TransmissionTwist] using degree_twist_of_satisfiesTransmission h a b

/-- Exact rank lower bound supplied by one transmission row. -/
theorem rank_transmissionTwist
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D) (a b : ℤ) :
    rank G (TransmissionTwist G u v D a b) ≥ τ.s (a + 1) b - 1 := by
  simpa [TransmissionTwist] using rank_twist_of_satisfiesTransmission h a b

/-- Any target rank below the row threshold gives an ordinary BN witness at the
affine row degree. -/
theorem BNExists_of_transmission_row
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D)
    (a b r : ℤ)
    (hTarget : r ≤ τ.s (a + 1) b - 1) :
    BNExists G r ((genus G : ℤ) + τ.χ + a - b) := by
  refine ⟨TransmissionTwist G u v D a b, ?_, ?_⟩
  · exact degree_transmissionTwist h a b
  · exact le_trans hTarget (rank_transmissionTwist h a b)

/-- At the exact row threshold, transmission directly supplies a BN witness. -/
theorem BNExists_at_transmission_threshold
    {G : CFGraph} {u v : G.V} {τ : AspPerm} {D : CFDiv G}
    (h : SatisfiesTransmission G u v τ D)
    (a b : ℤ) :
    BNExists G (τ.s (a + 1) b - 1)
      ((genus G : ℤ) + τ.χ + a - b) := by
  exact BNExists_of_transmission_row h a b (τ.s (a + 1) b - 1) le_rfl

/-- Existence-level version: a transmission locus witness yields every ordinary
BN witness forced by any one of its rows. -/
theorem BNExists_of_transmissionExists_row
    {G : CFGraph} {u v : G.V} {τ : AspPerm}
    (h : TransmissionExists G u v τ)
    (a b r : ℤ)
    (hTarget : r ≤ τ.s (a + 1) b - 1) :
    BNExists G r ((genus G : ℤ) + τ.χ + a - b) := by
  obtain ⟨D, hD⟩ := h
  exact BNExists_of_transmission_row hD a b r hTarget

end Utilities
