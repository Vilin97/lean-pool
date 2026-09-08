/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import LeanPool.RareDistanceFields.BinaryPalette
import LeanPool.RareDistanceFields.OctagonalNorm

/-!
# Logarithmically many rare distances in Z[zeta_8]

See the project entry module for the exact coordinate restrictions and source roles.
All binary descent hypotheses are discharged by the actual octagonal
embedding. There is no assumed rarity or assumed planar realization.
-/

namespace LeanPool.RareDistanceFields.OctagonalDescent

open OctagonalNorm
noncomputable section

open Classical in
/-- The binary descent model constructed from octagonal integer coordinates. -/
def model : BinaryDescent.Model Point where
  point := embed
  point_injective := embed_injective
  height := fun u v => height (u - v)
  height_nonneg := fun u v => height_nonneg (u - v)
  height_zero := fun u v => by rw [height_eq_zero, sub_eq_zero]
  distance_height := distance_height
  parity := parity
  parity_values := parity_zero_or_one
  even_iff := height_even_iff
  half := divide
  scale := ‖pi‖
  scale_pos := norm_pos_iff.mpr pi_ne_zero
  half_height := divide_height
  half_distance := divide_distance

open Classical in
/-- Occurring octagonal distances with unordered multiplicity at most the label count. -/
abbrev rareDistances {V : Type*} [Fintype V] (x : V → Point) : Finset ℝ :=
  BinaryPalette.rareDistances model x

open Classical in
theorem card_le_pow_rareDistances {V : Type*} [Fintype V] (x : V → Point)
    (hx : Function.Injective x) : Fintype.card V ≤ 2 ^ (rareDistances x).card :=
  BinaryPalette.card_le_pow_rareDistances model x hx

open Classical in
theorem rareDistances_spec {V : Type*} [Fintype V] (x : V → Point)
    (hx : Function.Injective x) (d : ℝ) :
    d ∈ rareDistances x ↔ 0 < d ∧ (∃ a b, a ≠ b ∧ dist (embed (x a)) (embed (x b)) = d) ∧
      (BinaryPalette.graph model x d).edgeFinset.card ≤ Fintype.card V :=
  BinaryPalette.rareDistances_spec model x hx d

end
end LeanPool.RareDistanceFields.OctagonalDescent
