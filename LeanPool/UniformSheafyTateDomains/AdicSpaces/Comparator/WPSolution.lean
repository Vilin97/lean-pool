/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Main

/-!
# Comparator solution: [WP] Theorem 8.1 (the weighted-parity example)

Forwards each statement of `WPChallenge.lean` to the library's proof. This is the
module comparator rebuilds inside the sandbox, so it is deliberately tiny: the
project itself is already built, and only this file is treated as the untrusted
submission.

The binder block is identical to the challenge's, so the two elaborate to the same
type; the paper's weight `w = id` is spelled `fun k => k` exactly as there
(definitionally `WeightedParity.idWeight`).

Numbering: Theorem 8.1 of the current paper revision; the library's docstrings cite
it as `[WP] thm 6.2` (the revision they were written against).
-/

open WeightedParity ValuationSpectrum TopologicalRing FiniteJetOver
open scoped NormedField Valued

universe u

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable [IsDiscreteValuationRing 𝒪[K]]

/-- **[WP] Theorem 8.1 (uniform)**. -/
theorem wp_8_1_isUniform : IsUniform (WPA K (fun k => k)) :=
  weightedParity_isUniform_of_dvr K

/-- **[WP] Theorem 8.1 (domain)**. -/
theorem wp_8_1_isDomain : IsDomain (WPA K (fun k => k)) :=
  weightedParity_isDomain K

/-- **[WP] Theorem 8.1 (nonnoetherian)**. -/
theorem wp_8_1_not_isNoetherianRing : ¬ IsNoetherianRing (WPA K (fun k => k)) :=
  weightedParity_not_noetherian K

/-- **[WP] Theorem 8.1 (`𝒜° = 𝒜₀`)**. -/
theorem wp_8_1_powerBounded_eq_unitBall :
    powerBoundedSubring (WPA K (fun k => k)) =
      (FiniteJet.unitBall (WPA K (fun k => k)) : Set (WPA K (fun k => k))) :=
  weightedParity_powerBounded_eq_unitBall (Uniformizer.ofDVR K)

/-- **[WP] Theorem 8.1 (sheafy)**. -/
theorem wp_8_1_isSheafyComplete : IsSheafyComplete (WPA K (fun k => k)) :=
  weightedParity_isSheafyComplete_of_dvr K

/-- **[WP] Theorem 8.1 (strongly sheafy)**. -/
theorem wp_8_1_stronglySheafy (s : ℕ) :
    IsSheafyComplete (WPA K (shiftWeight (fun k => k) s)) :=
  weightedParity_stronglySheafy_of_dvr K s

/-- **[WP] Theorem 8.1 (not stably uniform)**. -/
theorem wp_8_1_not_isStablyUniform : ¬ IsStablyUniform (WPA K (fun k => k)) :=
  weightedParity_not_stablyUniform_of_dvr K

/-- **[WP] Theorem 8.1 (`𝒜°` is a ring of integral elements)**. -/
theorem wp_8_1_powerBounded_isRingOfIntegralElements :
    IsRingOfIntegralElements ((ringPlus (WPA K (fun k => k)) : Subring (WPA K (fun k => k)))) :=
  inferInstance

/-- **[WP] Theorem 8.1 (the shifted-weight algebras have a ring of integral elements)**. -/
theorem wp_8_1_shifted_powerBounded_isRingOfIntegralElements (s : ℕ) :
    IsRingOfIntegralElements
      ((ringPlus (WPA K (shiftWeight (fun k => k) s)) :
        Subring (WPA K (shiftWeight (fun k => k) s)))) := inferInstance
