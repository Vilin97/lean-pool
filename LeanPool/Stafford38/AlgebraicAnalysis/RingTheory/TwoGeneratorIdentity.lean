/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib.RingTheory.OreLocalization.Ring
import LeanPool.Stafford38.AlgebraicAnalysis.Ore.RightLocalization

/-!
# Two-generator identities and unit-denominator transport

This neutral module extracts the reusable algebraic kernel formerly declared as
`Stafford38.LocalizationCorollaries.S38`,
`Stafford38.LocalizationCorollaries.s38_of_rightClearing`, and
`Stafford38.LocalizationCorollaries.s38_of_leftUnitClearing`.

Source record: Stafford38 commit `1585e4c7`, originally
`Stafford38/LocalizationCorollaries.lean` and
`Stafford38/LeftDenominatorTransport.lean`.
The extracted declarations are application-independent; Stafford38-specific
names and imports are intentionally absent.  The written multiplication order
is preserved.
-/

namespace AlgebraicAnalysis

universe u v

/-- The two-generator identity in a ring, with the distinguished factor on
the left of the first product and in the middle of the second. -/
def TwoGeneratorIdentity (R : Type u) [Ring R] : Prop :=
  ∀ d : R, d ≠ 0 → ∃ F r s : R, (1 : R) = d * r + F * d * s

/-- Right-clearing transport of the two-generator identity. -/
theorem TwoGeneratorIdentity.of_rightUnitClearing
    {R : Type u} {L : Type v} [Ring R] [Ring L]
    {f : R →+* L} (hR : TwoGeneratorIdentity R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a s : R, IsUnit (f s) ∧ q * f s = f a) :
    TwoGeneratorIdentity L := by
  intro q hq
  rcases hclear q hq with ⟨a, s, hs, hqa⟩
  have ha : a ≠ 0 := by
    intro ha
    have hzero : q * f s = 0 := by simpa [ha] using hqa
    exact hq (hs.mul_right_cancel (by simpa using hzero))
  rcases hR a ha with ⟨F, r, t, hone⟩
  refine ⟨f F, f s * f r, f s * f t, ?_⟩
  have hm := congrArg f hone
  simp only [map_add, map_mul] at hm
  calc
    (1 : L) = f a * f r + f F * f a * f t := by simpa using hm
    _ = q * (f s * f r) + f F * q * (f s * f t) := by
      rw [← hqa]
      simp [mul_assoc]

/-- Left-clearing transport of the two-generator identity. -/
theorem TwoGeneratorIdentity.of_leftUnitClearing
    {R : Type u} {L : Type v} [Ring R] [Ring L]
    {f : R →+* L} (hR : TwoGeneratorIdentity R)
    (hclear : ∀ q : L, q ≠ 0 →
      ∃ a : R, ∃ u : L, IsUnit u ∧ u * q = f a) :
    TwoGeneratorIdentity L := by
  intro q hq
  rcases hclear q hq with ⟨a, u, hu, hqa⟩
  have ha : a ≠ 0 := by
    intro ha
    have hzero : u * q = 0 := by simpa [ha] using hqa
    exact hq (hu.mul_left_cancel (by simpa using hzero))
  rcases hR a ha with ⟨F, r, t, hone⟩
  let U : Lˣ := hu.unit
  let ui : L := U.inv
  have hui : ui * u = 1 := by
    dsimp [ui, U]
    exact U.inv_mul
  have hui' : u * ui = 1 := by
    dsimp [ui, U]
    exact U.val_inv
  refine ⟨ui * f F * u, f r * u, f t * u, ?_⟩
  have hm := congrArg f hone
  simp only [map_add, map_mul] at hm
  have hm' : (1 : L) = (u * q) * f r + f F * (u * q) * f t := by
    simpa [hqa] using hm
  have hm'' := congrArg (fun z : L => ui * z * u) hm'
  have hm''' : (1 : L) = ui * ((u * q) * f r + f F * (u * q) * f t) * u := by
    simpa [hui, mul_assoc] using hm''
  calc
    (1 : L) = ui * ((u * q) * f r + f F * (u * q) * f t) * u := hm'''
    _ = q * (f r * u) + (ui * f F * u) * q * (f t * u) := by
      simp only [mul_add, add_mul, ← mul_assoc, hui, one_mul]

/-- The two-generator identity is preserved by the right Ore localization
implemented through the opposite ring. -/
theorem TwoGeneratorIdentity.of_rightOreLocalization
    {R : Type u} [Ring R] {S : Submonoid R}
    [OreLocalization.OreSet
      (AlgebraicAnalysis.OreRightLocalization.oppositeSubmonoid S)]
    (hR : TwoGeneratorIdentity R) :
    TwoGeneratorIdentity
      (AlgebraicAnalysis.OreRightLocalization.RightOreLocalization R S) := by
  apply TwoGeneratorIdentity.of_rightUnitClearing hR
  intro q hq
  rcases AlgebraicAnalysis.OreRightLocalization.rightOre_clear (S := S) q with
    ⟨a, s, _, hs, hclear⟩
  exact ⟨a, s, hs, hclear⟩

end AlgebraicAnalysis
