/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.MinimalLattice

/-!
# Supports in minimal lattice coordinates

The inverse coordinates of an integer lattice chart carry its generating
support to a support that generates the full new coordinate lattice. The
generation statement uses the finitely supported integer weights required by
`FlagDecomposition.IsMinimal`.
-/

open scoped BigOperators

namespace EGZ

/-- An integer point in an affine span admits finitely supported integer
coefficients with sum one on the given generating support. -/
theorem exists_finsupp_affineCombination_of_mem_affineSpan {n : ℕ}
    {S : Finset (IntCoord n)} {z : IntCoord n}
    (hz : z ∈ affineSpan ℤ (S : Set (IntCoord n))) :
    ∃ c : IntCoord n →₀ ℤ, c.support ⊆ S ∧
      (∑ q ∈ c.support, c q) = 1 ∧
      (∑ q ∈ c.support, c q • q) = z := by
  classical
  have hz' : z ∈ affineSpan ℤ (id '' (S : Set (IntCoord n))) := by simpa using hz
  obtain ⟨t, w, ht, hw, hzcomb⟩ :=
    eq_affineCombination_of_mem_affineSpan_image hz'
  let c : IntCoord n →₀ ℤ := Finsupp.onFinset t
    (fun q ↦ if q ∈ t then w q else 0) (by
      intro q hq
      by_contra hqt
      simp [hqt] at hq)
  have hc : c.support ⊆ t := Finsupp.support_onFinset_subset
  have hcoeff (q : IntCoord n) (hq : q ∈ t) : c q = w q := by simp [c, hq]
  have hsum : (∑ q ∈ c.support, c q) = ∑ q ∈ t, w q := by
    calc
      (∑ q ∈ c.support, c q) = ∑ q ∈ t, c q := by
        apply Finset.sum_subset hc
        intro q hqt hq
        exact Finsupp.notMem_support_iff.mp hq
      _ = ∑ q ∈ t, w q := Finset.sum_congr rfl hcoeff
  refine ⟨c, hc.trans ht, hsum.trans hw, ?_⟩
  calc
    (∑ q ∈ c.support, c q • q) = ∑ q ∈ t, c q • q := by
      apply Finset.sum_subset hc
      intro q hqt hq
      rw [Finsupp.notMem_support_iff.mp hq, zero_smul]
    _ = ∑ q ∈ t, w q • q := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [hcoeff q hq]
    _ = z := by
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw] at hzcomb
      exact hzcomb.symm

/-- The finitely supported coefficient definition of minimality is
equivalent to spanning the full integer affine space. -/
theorem FlagDecomposition.affineIntSpans_iff_affineSpan_eq_top {n : ℕ}
    (S : Finset (IntCoord n)) :
    FlagDecomposition.AffineIntSpans S ↔ affineSpan ℤ (S : Set (IntCoord n)) = ⊤ := by
  constructor
  · intro hS
    apply top_unique
    intro z _
    obtain ⟨c, hcS, hc, hcz⟩ := hS z
    have hmem := affineCombination_mem_affineSpan_image
      (s := c.support) hc (s' := (S : Set (IntCoord n)))
      (by intro q hq hqS; exact (hqS (hcS hq)).elim) (id : IntCoord n → IntCoord n)
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hc] at hmem
    rw [Set.image_id] at hmem
    change (∑ q ∈ c.support, c q • q) ∈ affineSpan ℤ (S : Set (IntCoord n)) at hmem
    rwa [hcz] at hmem
  · intro hS z
    apply exists_finsupp_affineCombination_of_mem_affineSpan
    rw [hS]
    exact AffineSubspace.mem_top ℤ (IntCoord n) z

namespace IntegerLatticeChart

variable {n : ℕ} {S : Finset (IntCoord n)} (C : IntegerLatticeChart S)

/-- Inverse integer coordinates. Its values outside the chart range are
irrelevant; the inverse laws below hold on the generated lattice. -/
noncomputable def coordinates : IntCoord n → IntCoord C.rank := Function.invFun C.map

@[simp]
theorem coordinates_map (q : IntCoord C.rank) : C.coordinates (C.map q) = q :=
  Function.leftInverse_invFun C.injective q

/-- The inverse coordinates recover each point in the support-generated
integer affine lattice. -/
theorem map_coordinates_of_mem_affineSpan {z : IntCoord n}
    (hz : z ∈ affineSpan ℤ (S : Set (IntCoord n))) : C.map (C.coordinates z) = z :=
  Function.invFun_eq (C.range_eq.symm.subset hz)

theorem map_coordinates_of_mem {z : IntCoord n} (hz : z ∈ S) :
    C.map (C.coordinates z) = z :=
  C.map_coordinates_of_mem_affineSpan (subset_affineSpan ℤ _ hz)

/-- The old generating support, expressed in the chart coordinates. -/
noncomputable def coordinateSupport : Finset (IntCoord C.rank) := by
  classical
  exact S.image C.coordinates

theorem coordinates_mem_coordinateSupport {z : IntCoord n} (hz : z ∈ S) :
    C.coordinates z ∈ C.coordinateSupport := by
  classical
  exact Finset.mem_image.mpr ⟨z, hz, rfl⟩

@[simp]
theorem mem_coordinateSupport {q : IntCoord C.rank} :
    q ∈ C.coordinateSupport ↔ C.map q ∈ S := by
  classical
  constructor
  · rintro hq
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hq
    rwa [C.map_coordinates_of_mem hz]
  · intro hq
    exact Finset.mem_image.mpr ⟨C.map q, hq, C.coordinates_map q⟩

@[simp]
theorem image_coordinateSupport : C.coordinateSupport.image C.map = S := by
  classical
  ext z
  constructor
  · rintro hz
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
    exact C.mem_coordinateSupport.mp hq
  · intro hz
    exact Finset.mem_image.mpr ⟨C.coordinates z,
      Finset.mem_image.mpr ⟨z, hz, rfl⟩, C.map_coordinates_of_mem hz⟩

theorem coordinateSupport_nonempty (hS : S.Nonempty) : C.coordinateSupport.Nonempty :=
  hS.image C.coordinates

@[simp]
theorem card_coordinateSupport : C.coordinateSupport.card = S.card := by
  classical
  calc
    C.coordinateSupport.card = (C.coordinateSupport.image C.map).card :=
      (Finset.card_image_of_injective _ C.injective).symm
    _ = S.card := congrArg Finset.card C.image_coordinateSupport

/-- The new support generates every integer coordinate point. -/
theorem affineSpan_coordinateSupport :
    affineSpan ℤ (C.coordinateSupport : Set (IntCoord C.rank)) = ⊤ := by
  have hmap : (affineSpan ℤ (C.coordinateSupport : Set (IntCoord C.rank))).map C.map =
      affineSpan ℤ (S : Set (IntCoord n)) := by
    rw [AffineSubspace.map_span, ← Finset.coe_image, C.image_coordinateSupport]
  apply top_unique
  intro q _
  have hq : C.map q ∈ affineSpan ℤ (S : Set (IntCoord n)) :=
    C.range_eq.subset ⟨q, rfl⟩
  rw [← hmap] at hq
  obtain ⟨r, hr, heq⟩ := hq
  rwa [C.injective heq] at hr

/-- The transformed support satisfies exactly the lattice-generation field
in the definition of a minimal flag decomposition. -/
theorem coordinateSupport_affineIntSpans :
    FlagDecomposition.AffineIntSpans C.coordinateSupport :=
  (FlagDecomposition.affineIntSpans_iff_affineSpan_eq_top _).mpr C.affineSpan_coordinateSupport

/-- An old support bound and a chart box bound give the new support bound. -/
theorem coordinateSupport_bound {K B : ℕ}
    (hS : ∀ z ∈ S, latticeSupNorm z ≤ K)
    (hC : ∀ q : IntCoord C.rank, latticeSupNorm (C.map q) ≤ K → latticeSupNorm q ≤ B) :
    ∀ q ∈ C.coordinateSupport, latticeSupNorm q ≤ B := by
  intro q hq
  exact hC q (hS _ (C.mem_coordinateSupport.mp hq))

end IntegerLatticeChart

end EGZ
