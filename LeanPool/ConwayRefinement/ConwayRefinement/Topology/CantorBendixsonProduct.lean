/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.Topology.CantorBendixson
public import LeanPool.ConwayRefinement.CombinatorialGames.NatOrdinal.Basic
public import Mathlib.Topology.Constructions.SumProd

/-!
# Natural-sum bounds for Cantor–Bendixson derivatives of products

Locally strictly decreasing ordinal labels on two closed sets give their natural sum as a
bound on the Cantor–Bendixson stages of the product. The addition is Hessenberg addition on
`NatOrdinal`, not ordinary ordinal addition. No countability or compactness is required.
-/

public noncomputable section

open Set Filter Topology TopologicalSpace

universe u v w

namespace TopologicalSpace.Closeds

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T1Space X] [T1Space Y]

/-- Natural addition of locally strictly decreasing ordinal labels bounds product derivatives. -/
theorem cantorBendixson_prod_subset_of_locally_lt (s : Closeds X) (t : Closeds Y)
    (r : X → NatOrdinal.{w}) (q : Y → NatOrdinal.{w})
    (hr : ∀ x ∈ s, ∀ᶠ z in 𝓝 x, z ∈ s → z ≠ x → r z < r x)
    (hq : ∀ y ∈ t, ∀ᶠ z in 𝓝 y, z ∈ t → z ≠ y → q z < q y) (o : Ordinal.{w}) :
    ((s ×ˢ t).cantorBendixson o : Set (X × Y)) ⊆ {p | o ≤ (r p.1 + q p.2).val} := by
  apply cantorBendixson_subset_of_locally_lt
  rintro ⟨x, y⟩ hxy
  obtain ⟨hx, hy⟩ := mem_prod.mp hxy
  rw [nhds_prod_eq]
  apply eventually_prod_iff.mpr
  refine ⟨_, hr x hx, _, hq y hy, ?_⟩
  intro z hz w hw hzw hne
  obtain ⟨hzs, hwt⟩ := mem_prod.mp hzw
  apply NatOrdinal.val.lt_iff_lt.mpr
  by_cases hzx : z = x
  · subst z
    have hwy : w ≠ y := fun heq ↦ hne (Prod.ext rfl heq)
    exact add_lt_add_right (hw hwt hwy) _
  · have hwle : q w ≤ q y := by
      by_cases hwy : w = y
      · exact hwy ▸ le_rfl
      · exact (hw hwt hwy).le
    exact add_lt_add_of_lt_of_le (hz hzs hzx) hwle

end TopologicalSpace.Closeds
