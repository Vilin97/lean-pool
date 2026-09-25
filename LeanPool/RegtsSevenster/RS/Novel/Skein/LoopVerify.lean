/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TransposeLedger

/-!
# A repaired system carrying a path-canonical orientation

The worked one-vertex fragment `TransposeVerify` (internal flags
`0–3`, boundary flags `4–7`) has three perfect matchings of its
internal flags.  This module builds the second of them as a repair
of the first, `lvKappa₂R = cKappa.repair 0 1 2 3`, together with an
orientation `lvO₂flip` of it: the one obtained from `cO` by
flipping the boundary chain `5–1–3–6`.

Against the fixed functional `cFunctional`, supported on the colour
set `{0, 5, 2, 7}` adapted to `cO`, that orientation's constrained
summand is `0` (`lvSummand₂flip`): the flipped in-list carries the
colours `{0, 7, 1, 6}` instead.  The summand is computed through
`lvThroughSummand`, which is `cThroughSummand` with the functional
freed so that each orientation can be evaluated against its own
delta.

`ThroughIndCFalse` uses exactly this: `cKappa` and `lvKappa₂R` both
carry path-canonical orientations with trivial chord sign, yet the
summands are `−1` and `0`, so the canonical value depends on the
boundary pairing and independence can only be asserted within one.
-/

namespace RS

namespace TransposeVerify

open EdgeSubset

/-! ## The repaired system -/

/-- `cKappa` repaired along `cSquare` (`0 1 2 3`): the matching
`0 ↔ 2`, `1 ↔ 3`, with chords `(4,7)` and `(5,6)`. -/
def lvKappa₂R : cSubset.RelTransitionSystem :=
  cKappa.repair 0 1 2 3 cV cSquare

/-! ## The flipped orientation -/

/-- `cO` with the boundary chain `5–1–3–6` (flags `1, 3`)
reversed — the chain carrying the colour `3`. -/
def lvO₂flip : lvKappa₂R.Orientation where
  isOut := ![false, false, true, true, false, false, false, false]
  match_flip := fun f hf => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;> rfl
  pairing_flip := fun f hf hp => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;>
      · rcases cInternal_cases hp with h | h | h | h <;>
          exact absurd h (by decide)

/-! ## The generalized two-in-flag summand

`cThroughSummand`, restated for an arbitrary functional (the
original is pinned to `cFunctional`); the proof is identical. -/

open Classical in
/-- The summand over a two-element in-list at an arbitrary
functional: `cThroughSummand` with the functional freed, so each
stage can be evaluated against its own adapted delta. -/
theorem lvThroughSummand (hM : MixedFunctional 0 4)
    (κ : cSubset.RelTransitionSystem)
    (o : κ.Orientation) (g₁ g₂ : Fin 8)
    (hglist : cSubset.relInFlagsAt o cV = [g₁, g₂]) :
    cSubset.throughSummand hM cState cBnd o 0 =
      ((oddPartnerSign 4 (cColour (κ.match_ g₁)) *
          oddPartnerSign 4 (cColour (κ.match_ g₂)) : ℤ) : ℂ) *
        MixedFunctional.evalOdd hM
          (cSubset.evenColoursAt cPsi cV)
          [cColour g₁, oddPartner 4 (cColour (κ.match_ g₁)),
            cColour g₂, oddPartner 4 (cColour (κ.match_ g₂))] := by
  unfold EdgeSubset.throughSummand
  rw [cThroughProduct, pow_zero, one_mul, one_mul]
  rw [Fintype.sum_subsingleton _ cPsi]
  rw [ite_eq_left cEvenMatch]
  have hzero : ∀ φ : cSubset.CoreOddColouring 4, φ ≠ cPhi →
      (if cSubset.coreOddBoundaryMatch cState φ then
        ∏ v : cFragment.Vertex,
          ((cSubset.coreOddSignAt o φ v : ℂ) *
            MixedFunctional.evalOdd hM
              (cSubset.evenColoursAt cPsi v)
              (cSubset.coreOddListAt o φ v))
      else 0) = 0 := by
    intro φ hφ
    rcases Classical.em (cSubset.coreOddBoundaryMatch cState φ) with
      hb | hb
    · exact absurd (cPhi_unique φ hb) hφ
    · rw [ite_eq_right hb]
  rw [Fintype.sum_eq_single cPhi hzero]
  rw [ite_eq_left cOddMatch]
  rw [Fintype.prod_subsingleton _ cV]
  rw [cCoreOddSignAt κ o g₁ g₂ hglist, cCoreOddListAt κ o g₁ g₂
    hglist]

/-! ## The summand against the fixed functional -/

open Classical in
/-- The flip kills the summand: the in-list colour set is
`{0, 7, 1, 6}`, outside the support `{0, 5, 2, 7}` of
`cFunctional`. -/
theorem lvSummand₂flip :
    cSubset.throughSummand cFunctional cState cBnd lvO₂flip 0 =
      0 := by
  rcases cRelIn_pair (κ := lvKappa₂R) lvO₂flip rfl rfl rfl rfl 0 1
      (by decide) (by decide) with h | h
  · rw [lvThroughSummand cFunctional lvKappa₂R lvO₂flip 0 1 h,
      show lvKappa₂R.match_ 0 = 2 from by decide,
      show lvKappa₂R.match_ 1 = 3 from by decide,
      show [cColour 0, oddPartner 4 (cColour 2), cColour 1,
        oddPartner 4 (cColour 3)] =
        ([0, 7, 1, 6] : List (Fin (2 * 4))) from by decide,
      MixedFunctional.evalOdd,
      ite_eq_left (by decide : ([0, 7, 1, 6] : List (Fin (2 * 4))).Nodup),
      show ([0, 7, 1, 6] : List (Fin (2 * 4))).toFinset =
        ({0, 7, 1, 6} : Finset (Fin (2 * 4))) from by decide,
      cFunctional_apply,
      ite_eq_right (by decide : ¬ ({0, 7, 1, 6} : Finset (Fin (2 * 4))) =
        ({0, 5, 2, 7} : Finset (Fin (2 * 4)))),
      mul_zero, mul_zero]
  · rw [lvThroughSummand cFunctional lvKappa₂R lvO₂flip 1 0 h,
      show lvKappa₂R.match_ 0 = 2 from by decide,
      show lvKappa₂R.match_ 1 = 3 from by decide,
      show [cColour 1, oddPartner 4 (cColour 3), cColour 0,
        oddPartner 4 (cColour 2)] =
        ([1, 6, 0, 7] : List (Fin (2 * 4))) from by decide,
      MixedFunctional.evalOdd,
      ite_eq_left (by decide : ([1, 6, 0, 7] : List (Fin (2 * 4))).Nodup),
      show ([1, 6, 0, 7] : List (Fin (2 * 4))).toFinset =
        ({0, 7, 1, 6} : Finset (Fin (2 * 4))) from by decide,
      cFunctional_apply,
      ite_eq_right (by decide : ¬ ({0, 7, 1, 6} : Finset (Fin (2 * 4))) =
        ({0, 5, 2, 7} : Finset (Fin (2 * 4)))),
      mul_zero, mul_zero]

end TransposeVerify

end RS
