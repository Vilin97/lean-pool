/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.NodeMassMap
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.LevelInjectivity

/-!
# Level comparison for mass-transport maps

For a minimal output decomposition, compatibility on cumulative support
extends to its whole represented affine space. Thus a node mass map already
contains all data needed for level monotonicity and equal-level coordinate
injectivity; no extra transport fields are required.
-/

@[expose] public section

namespace EGZ.FlagDecomposition.NodeMassMap

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ Ψ : FlagDecomposition p d f} {x : Φ.flag.Node} {y : Ψ.flag.Node}
    (M : NodeMassMap Φ Ψ x y) (hΨ : Ψ.IsMinimal)

include M hΨ

theorem space_le : Ψ.representation.space y ≤ Φ.representation.space x := by
  rw [(hΨ y).1]
  apply affineSpan_le.mpr
  intro v hv
  exact Φ.originalWeights.cumulative_supported x v
    (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (M.cumulative_le v)))

/-- Compatibility extends from the support to its full affine span. -/
theorem map_eq_on_space (v : FpCoord p d) (hv : v ∈ Ψ.representation.space y) :
    M.coord.modp p (Ψ.representation.map y v) = Φ.representation.map x v := by
  rw [(hΨ y).1] at hv
  exact AffineMap.eqOn_affineSpan
    (f := (M.coord.modp p).comp (Ψ.representation.map y))
    (g := Φ.representation.map x) M.map_eq hv

theorem level_le : Φ.level x ≤ Ψ.level y :=
  Φ.representation.level_le_of_space_le_of_factor Ψ.representation x y (M.coord.modp p)
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm)

theorem space_eq_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Ψ.representation.space y = Φ.representation.space x :=
  Φ.representation.space_eq_of_codimension_eq_of_le Ψ.representation x y (M.space_le hΨ)
    (Φ.representation.codimension_eq_and_rank_eq_of_level_eq Ψ.representation x y hlevel).1

theorem modp_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective (M.coord.modp p) :=
  Φ.representation.factor_modp_injective_of_level_eq Ψ.representation x y (M.coord.modp p)
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

theorem real_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective M.coord.real :=
  Φ.representation.factor_real_injective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

theorem integer_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective M.coord.integer :=
  Φ.representation.factor_integer_injective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

theorem real_bijective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Bijective M.coord.real :=
  Φ.representation.factor_real_bijective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

end EGZ.FlagDecomposition.NodeMassMap
