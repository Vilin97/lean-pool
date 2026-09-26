/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.FieldTheory.LatticeFactorCoefficients
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.FiniteSupportGCDProof
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupAlgebra

/-!
# Clearing a scalar out of a finite-support Hahn factor

Two finite-support series have finitely many exponents between them, so both lie in the group ring
of the subgroup those exponents generate, which is free of finite rank. Coefficient extension
commutes with the inclusion of that group ring into the series ring, so a factorisation whose
product has coefficients in the subfield transports to the group ring, where one scalar clears a
factor into the subfield.
-/

universe u v w

namespace HahnSeries

public section

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable {G : Type w} [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]

/-- Coefficient extension commutes with the subgroup-algebra inclusion. -/
theorem subgroupAlgebraHom_mapRingHom (H : AddSubgroup G) (P : AddMonoidAlgebra K H) :
    HahnSeries.subgroupAlgebraHom H (AddMonoidAlgebra.mapRingHom H (algebraMap K L) P) =
      (HahnSeries.subgroupAlgebraHom H P).map (algebraMap K L) := by
  classical
  refine HahnSeries.coeff_injective (funext fun g ↦ ?_)
  rw [HahnSeries.coeff_subgroupAlgebraHom, HahnSeries.map_coeff,
    HahnSeries.coeff_subgroupAlgebraHom]
  by_cases hg : g ∈ H
  · rw [dite_eq_left hg, dite_eq_left hg, AddMonoidAlgebra.mapRingHom_apply',
      Finsupp.mapRange_apply]
  · rw [dite_eq_right hg, dite_eq_right hg, map_zero]

/-- Hahn-series form of scalar clearing for finite-support factors. -/
theorem exists_scalar_of_hahn_mul_eq_map
    (hclosed : Algebra.IsRelativelyAlgebraicallyClosed K L)
    {p q : HahnSeries G L} {a : HahnSeries G K} (hp : p ≠ 0) (hq : q ≠ 0)
    (hpfin : p.support.Finite) (hqfin : q.support.Finite)
    (hrel : p * q = a.map (algebraMap K L)) :
    ∃ c : L, c ≠ 0 ∧ ∀ x, c * p.coeff x ∈ (algebraMap K L).range := by
  classical
  set S : Finset G := hpfin.toFinset ∪ hqfin.toFinset with hS
  set H : AddSubgroup G := AddSubgroup.closure (S : Set G) with hH
  have hpH : p.support ⊆ (H : Set G) := fun x hx ↦ AddSubgroup.subset_closure
    (Finset.mem_coe.mpr (Finset.mem_union_left _ (hpfin.mem_toFinset.mpr hx)))
  have hqH : q.support ⊆ (H : Set G) := fun x hx ↦ AddSubgroup.subset_closure
    (Finset.mem_coe.mpr (Finset.mem_union_right _ (hqfin.mem_toFinset.mpr hx)))
  have haH : a.support ⊆ (H : Set G) := by
    intro x hx
    have hxa : x ∈ (a.map (algebraMap K L)).support := by
      rw [HahnSeries.mem_support, HahnSeries.map_coeff]
      exact fun h0 ↦ (HahnSeries.mem_support _ _).mp hx
        ((algebraMap K L).injective (by rw [h0, map_zero]))
    rw [← hrel] at hxa
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_add.mp (HahnSeries.support_mul_subset hxa)
    exact AddSubgroup.add_mem H (hpH hu) (hqH hv)
  have hafin : a.support.Finite := by
    refine Set.Finite.subset (Set.Finite.add hpfin hqfin) ?_
    intro x hx
    have hxa : x ∈ (a.map (algebraMap K L)).support := by
      rw [HahnSeries.mem_support, HahnSeries.map_coeff]
      exact fun h0 ↦ (HahnSeries.mem_support _ _).mp hx
        ((algebraMap K L).injective (by rw [h0, map_zero]))
    rw [← hrel] at hxa
    exact HahnSeries.support_mul_subset hxa
  obtain ⟨p₁, hp₁⟩ := HahnSeries.exists_subgroupAlgebraHom_eq H hpfin hpH
  obtain ⟨q₁, hq₁⟩ := HahnSeries.exists_subgroupAlgebraHom_eq H hqfin hqH
  obtain ⟨a₁, ha₁⟩ := HahnSeries.exists_subgroupAlgebraHom_eq H hafin haH
  have hp₁0 : p₁ ≠ 0 := fun h0 ↦ hp (by rw [← hp₁, h0, map_zero])
  have hq₁0 : q₁ ≠ 0 := fun h0 ↦ hq (by rw [← hq₁, h0, map_zero])
  have hrel₁ : p₁ * q₁ = AddMonoidAlgebra.mapRingHom H (algebraMap K L) a₁ := by
    refine HahnSeries.subgroupAlgebraHom_injective H ?_
    rw [map_mul, hp₁, hq₁, hrel, subgroupAlgebraHom_mapRingHom, ha₁]
  obtain ⟨c, hc, hcoeff⟩ := AddMonoidAlgebra.exists_scalar_of_mul_eq_map_free
    (HahnSeries.exists_addEquiv_fin S) hclosed hp₁0 hq₁0 hrel₁
  refine ⟨c, hc, fun x ↦ ?_⟩
  by_cases hx : x ∈ H
  · have : p.coeff x = p₁.coeff ⟨x, hx⟩ := by
      rw [← hp₁, HahnSeries.coeff_subgroupAlgebraHom, dite_eq_left hx]
    rw [this]
    exact hcoeff _
  · have : p.coeff x = 0 := by
      rw [← hp₁, HahnSeries.coeff_subgroupAlgebraHom, dite_eq_right hx]
    rw [this, mul_zero]
    exact ⟨0, map_zero _⟩

end

end HahnSeries
