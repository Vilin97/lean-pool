/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.TheoremDimension
public import LeanPool.RegtsSevenster.RS.Novel.Skein.ColourPadding

/-!
# Prescribed parity dimensions

The free-circle value fixes the difference of the parity dimensions.
The total-dimension theorem therefore bounds both dimensions by any
prescribed compatible pair. Extension by zero then gives a model on
exactly that pair of colour spaces.
-/

@[expose] public section

namespace RS

/-- A disjoint union of free circles evaluates to the corresponding
power of the superdimension. -/
theorem mixedPartition_circlesClosed {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (c : ℕ) :
    mixedPartition h (circlesClosed c) = ((k : ℂ) - 2 * ℓ) ^ c := by
  let : IsEmpty (circlesClosed c).Flag := inferInstanceAs (IsEmpty Empty)
  let : IsEmpty (circlesClosed c).Vertex := inferInstanceAs (IsEmpty Empty)
  exact mixedPartition_of_flagless (circlesClosed c) h

/-- Every representing model has superdimension equal to the
parameter's free-circle value. -/
theorem MixedFunctional.Represents.circle_eq
    {f : ClosedFragment → ℂ} {k ℓ : ℕ} {h : MixedFunctional k ℓ}
    (hrep : h.Represents f) : f (circlesClosed 1) = (k : ℂ) - 2 * ℓ := by
  rw [hrep, mixedPartition_circlesClosed, pow_one]

/-- The minimum total dimension and free-circle value determine
the even dimension of every minimal model. -/
theorem TotalBoundedMixedModel.even_dimension_eq
    {f : ClosedFragment → ℂ}
    (M : TotalBoundedMixedModel f (minimumColourDimension f)) :
    (M.k : ℂ) = ((minimumColourDimension f : ℂ) + f (circlesClosed 1)) / 2 := by
  have hcircle := (show M.functional.Represents f from M.partition_eq).circle_eq
  have hdim : (minimumColourDimension f : ℂ) = (M.k : ℂ) + 2 * M.ℓ := by
    exact_mod_cast M.dimension_eq_minimum.symm
  rw [hcircle, hdim]
  ring

/-- The minimum total dimension and free-circle value determine
half the odd dimension of every minimal model. -/
theorem TotalBoundedMixedModel.half_odd_dimension_eq
    {f : ClosedFragment → ℂ}
    (M : TotalBoundedMixedModel f (minimumColourDimension f)) :
    (M.ℓ : ℂ) = ((minimumColourDimension f : ℂ) - f (circlesClosed 1)) / 4 := by
  have hcircle := (show M.functional.Represents f from M.partition_eq).circle_eq
  have hdim : (minimumColourDimension f : ℂ) = (M.k : ℂ) + 2 * M.ℓ := by
    exact_mod_cast M.dimension_eq_minimum.symm
  rw [hcircle, hdim]
  ring

/-- A normalized invariant parameter has a model with prescribed
parity dimensions exactly when its ranks and free-circle value
satisfy the corresponding bounds, conditional on Deligne alone. -/
theorem regts_sevenster_prescribed_deligne_only
    (hDeligne : DeligneTheoremStatement.{1, 1})
    (f : ClosedFragment → ℂ)
    (hempty : f emptyClosedFragment = 1)
    (hiso : ∀ W₁ W₂ : ClosedFragment, W₁.Equiv W₂ → f W₁ = f W₂)
    (K L : ℕ) :
    (∃ h : MixedFunctional K L, h.Represents f) ↔
      PrescribedColourBounds f K L := by
  constructor
  · rintro ⟨h, hrep⟩
    exact ⟨hrep.circle_eq, hrep.edgeRankBounded⟩
  · intro hbounds
    let g : EdgeRankParameter (K + 2 * L) :=
      ⟨f, hempty, hiso, hbounds.rank_bounded⟩
    obtain ⟨M⟩ := regts_sevenster_total_deligne_only hDeligne _ g
    have hrep : M.functional.Represents f := M.partition_eq
    have hcircle : (M.k : ℂ) - 2 * M.ℓ = (K : ℂ) - 2 * L :=
      hrep.circle_eq.symm.trans hbounds.circle_eq
    have hdim := M.dimension_le
    have hcircleInt : (M.k : ℤ) - 2 * M.ℓ = (K : ℤ) - 2 * L := by
      exact_mod_cast hcircle
    have hk : M.k ≤ K := by omega
    have hℓ : M.ℓ ≤ L := by omega
    exact ⟨M.functional.padColours hk hℓ,
      M.functional.padColours_represents hk hℓ hcircle.symm hrep⟩

end RS
