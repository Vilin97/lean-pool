/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionZeroFreeApproximation
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.CoordinateEquivariance
import LeanPool.NandakumarRamanaRao.NRR.PrimeModel.ChildTestMap
import Mathlib.Topology.Homotopy.Basic

/-!
# Equivariant zero-free coordinate homotopies

This file packages the continuous objects used by the unconditional S6 argument.  The target is the
full labelled coordinate representation `Fin p → ℝ`; prime symmetry acts simultaneously on the
Fox--Neuwirth realization and by coordinate permutation on the target.

The crucial distinction is between avoiding the origin in the full coordinate representation and
avoiding zero only in the deviation representation.  The projected simultaneous-child-zero set is
exactly the locus where the full coordinate map meets the origin.
-/

namespace NRR

open Geometry
open scoped BigOperators

namespace FoxNeuwirthOrderComplex
namespace EquivariantCoordinateHomotopy

variable {p : Nat}

/-- Continuous coordinate-valued maps on the order-complex realization. -/
abbrev CoordinateMap := RefinedAffineMap.ContinuousCoordinateMap (p := p)

/-- Prime-equivariance of a continuous coordinate map. -/
abbrev IsEquivariant (hp : Nat.Prime p) (F : CoordinateMap (p := p)) : Prop :=
  IsEquivariantCoordinateMap hp F

/-- A continuous prime-equivariant coordinate map avoiding the origin. -/
structure ZeroFreeMap (hp : Nat.Prime p) where
  /-- The underlying continuous coordinate map. -/
  map : CoordinateMap
  equivariant : IsEquivariant hp map
  zeroFree : ∀ x, map x ≠ 0

/-- A continuous equivariant homotopy through maps avoiding the origin. -/
structure ZeroFreeHomotopy
    (hp : Nat.Prime p) (F₀ F₁ : ZeroFreeMap hp) where
  /-- The continuous map on the realization times the unit interval defining the homotopy. -/
  map : C(Realization p × Set.Icc (0 : Real) 1, Fin p → Real)
  map_zero : ∀ x, map (x, ⟨0, by simp⟩) = F₀.map x
  map_one : ∀ x, map (x, ⟨1, by simp⟩) = F₁.map x
  equivariant : ∀ (g : PrimeSymmetry p) x t, map (g • x, t) = g • map (x, t)
  zeroFree : ∀ x t, map (x, t) ≠ 0

namespace ZeroFreeHomotopy

/-- The constant zero-free homotopy. -/
noncomputable def refl (hp : Nat.Prime p) (F : ZeroFreeMap hp) :
    ZeroFreeHomotopy hp F F where
  map := ⟨fun z => F.map z.1, F.map.continuous.comp continuous_fst⟩
  map_zero := by simp
  map_one := by simp
  equivariant := by intro g x t; exact F.equivariant g x
  zeroFree := by intro x t; exact F.zeroFree x

/-- Reverse a zero-free homotopy. -/
noncomputable def symm
    {hp : Nat.Prime p} {F₀ F₁ : ZeroFreeMap hp}
    (H : ZeroFreeHomotopy hp F₀ F₁) : ZeroFreeHomotopy hp F₁ F₀ where
  map := ⟨fun z => H.map (z.1, ⟨1 - z.2.1, by constructor <;> linarith [z.2.2.1, z.2.2.2]⟩), by
    fun_prop⟩
  map_zero := by intro x; simpa using H.map_one x
  map_one := by intro x; simpa using H.map_zero x
  equivariant := by intro g x t; exact H.equivariant g x _
  zeroFree := by intro x t; exact H.zeroFree x _

/-- Concatenate two zero-free homotopies. -/
noncomputable def trans
    {hp : Nat.Prime p} {F₀ F₁ F₂ : ZeroFreeMap hp}
    (H₀₁ : ZeroFreeHomotopy hp F₀ F₁)
    (H₁₂ : ZeroFreeHomotopy hp F₁ F₂) :
    ZeroFreeHomotopy hp F₀ F₂ where
  map := ⟨fun z => if z.2.1 ≤ 1 / 2 then
      H₀₁.map (z.1, ⟨min (2 * z.2.1) 1, by
        constructor
        · exact le_min (by nlinarith [z.2.2.1]) zero_le_one
        · exact min_le_right _ _⟩)
    else
      H₁₂.map (z.1, ⟨max (2 * z.2.1 - 1) 0, by
        constructor
        · exact le_max_right _ _
        · exact max_le (by nlinarith [z.2.2.2]) zero_le_one⟩), by
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · fun_prop
    · fun_prop
    · intro z hz
      have hleft : (⟨min (2 * z.2.1) 1, by
          constructor
          · exact le_min (by nlinarith [z.2.2.1]) zero_le_one
          · exact min_le_right _ _⟩ : Set.Icc (0 : Real) 1) = 1 := by
        apply Subtype.ext
        simp [hz]
      have hright : (⟨max (2 * z.2.1 - 1) 0, by
          constructor
          · exact le_max_right _ _
          · exact max_le (by nlinarith [z.2.2.2]) zero_le_one⟩ : Set.Icc (0 : Real) 1) = 0 := by
        apply Subtype.ext
        simp [hz]
      rw [hleft, hright]
      exact (H₀₁.map_one z.1).trans (H₁₂.map_zero z.1).symm⟩
  map_zero := by intro x; norm_num; exact H₀₁.map_zero x
  map_one := by intro x; norm_num; exact H₁₂.map_one x
  equivariant := by
    intro g x t
    change (if t.1 ≤ 1 / 2 then H₀₁.map (g • x, _) else H₁₂.map (g • x, _)) =
      g • (if t.1 ≤ 1 / 2 then H₀₁.map (x, _) else H₁₂.map (x, _))
    by_cases h : t.1 ≤ 1 / 2
    · simp only [if_pos h]
      exact H₀₁.equivariant g x _
    · simp only [if_neg h]
      exact H₁₂.equivariant g x _
  zeroFree := by
    intro x t
    change (if t.1 ≤ 1 / 2 then H₀₁.map (x, _) else H₁₂.map (x, _)) ≠ 0
    split_ifs <;> first | exact H₀₁.zeroFree x _ | exact H₁₂.zeroFree x _

/-- Straight-line homotopy, under a pointwise nonvanishing hypothesis. -/
noncomputable def segment
    {hp : Nat.Prime p} (F₀ F₁ : ZeroFreeMap hp)
    (hseg : ∀ x (t : Set.Icc (0 : Real) 1),
      (1 - t.1) • F₀.map x + t.1 • F₁.map x ≠ 0) :
    ZeroFreeHomotopy hp F₀ F₁ where
  map := ⟨fun z => (1 - z.2.1) • F₀.map z.1 + z.2.1 • F₁.map z.1, by fun_prop⟩
  map_zero := by intro x; simp
  map_one := by intro x; simp
  equivariant := by
    intro g x t
    change (1 - t.1) • F₀.map (g • x) + t.1 • F₁.map (g • x) =
      g • ((1 - t.1) • F₀.map x + t.1 • F₁.map x)
    rw [F₀.equivariant g x, F₁.equivariant g x]
    funext i
    simp only [PrimeSymmetry.smul_coordinate_apply, Pi.add_apply, Pi.smul_apply]
  zeroFree := hseg

end ZeroFreeHomotopy

/-- A coordinate map obtained by freezing the parent-body/interval parameter in the child test
map. -/
noncomputable def childMap
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval) : CoordinateMap (p := p) where
  toFun x := (orderComplexModel hp).childTestMap hA phi (((z.1, x), z.2))
  continuous_toFun := by
    exact ((orderComplexModel hp).continuous_childTestMap hA phi).comp
      ((continuous_const.prodMk continuous_id).prodMk continuous_const)

/-- The frozen child map is prime-equivariant. -/
theorem childMap_equivariant
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval) :
    IsEquivariant hp (childMap hp hA phi z) := by
  intro g x
  convert (orderComplexModel hp).childTestMap_smul hA phi g
    (((z.1, x), z.2)) using 1 <;>
    rfl

/-- Outside the projected zero set, the frozen child coordinate map avoids the origin. -/
theorem childMap_zeroFree
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) :
    ∀ x, childMap hp hA phi z x ≠ 0 := by
  intro x hx
  apply hz
  exact ⟨x, hx⟩

/-- The child map as a bundled zero-free equivariant map. -/
noncomputable def childZeroFreeMap
    {K : Geometry.ConvexBody Plane} {A : Real}
    (hp : Nat.Prime p) (hA : 0 < A)
    (phi : NiceMV (BodySpace K (A / (p : Real))))
    (z : BodySpace K A × SignedInterval)
    (hz : z ∈ ((orderComplexModel hp).projectedAllChildrenZeroSet hA phi)ᶜ) :
    ZeroFreeMap hp where
  map := childMap hp hA phi z
  equivariant := childMap_equivariant hp hA phi z
  zeroFree := childMap_zeroFree hp hA phi z hz

end EquivariantCoordinateHomotopy
end FoxNeuwirthOrderComplex
end NRR
