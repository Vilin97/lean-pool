/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.EPrimitive
public import Mathlib.Algebra.MonoidAlgebra.Basic

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SubgroupSupport

/-!
# Series supported in a subgroup as a group ring

The finite-support series supported in a subgroup `H` of the exponents are the group ring of `H`.
The identification is the algebra map sending a group element to its monomial, so multiplication
is matched by the monomial rule and no convolution computation is needed.

This is what carries unique factorisation, and with it least common multiples, from the group ring
of a free abelian group of finite rank into the series ring.
-/

open scoped HahnSeries

universe u v

public noncomputable section

namespace HahnSeries

variable {G : Type u} {K : Type v}
variable [LinearOrder G] [AddCommGroup G] [IsOrderedAddMonoid G]
variable [Field K]

/-- Monomials with exponent in a subgroup, as a monoid homomorphism. -/
def subgroupMonomialHom (H : AddSubgroup G) : Multiplicative H →* K⟦G⟧ where
  toFun h := single ((Multiplicative.toAdd h : H) : G) (1 : K)
  map_one' := by simp
  map_mul' a b := by
    rw [HahnSeries.single_mul_single, one_mul]
    rfl

/-- The group ring of a subgroup of the exponents, mapped into the series ring. -/
def subgroupAlgebraHom (H : AddSubgroup G) : AddMonoidAlgebra K H →ₐ[K] K⟦G⟧ :=
  AddMonoidAlgebra.lift K (K⟦G⟧) H (subgroupMonomialHom H)

@[simp]
theorem subgroupAlgebraHom_single (H : AddSubgroup G) (a : H) (b : K) :
    subgroupAlgebraHom H (Finsupp.single a b) = single (a : G) b := by
  rw [subgroupAlgebraHom, AddMonoidAlgebra.lift_single]
  ext g
  simp [subgroupMonomialHom, HahnSeries.coeff_single]

open Classical in
/-- The coefficients of a monomial image. -/
private theorem coeff_subgroupAlgebraHom_single (H : AddSubgroup G) (a : H) (b : K) (g : G) :
    (subgroupAlgebraHom H (Finsupp.single a b)).coeff g
      = if hg : g ∈ H then (Finsupp.single a b : H →₀ K) ⟨g, hg⟩ else 0 := by
  rw [subgroupAlgebraHom_single, HahnSeries.coeff_single]
  by_cases hg : g ∈ H
  · rw [dite_eq_left hg, Finsupp.single_apply]
    by_cases hga : g = (a : G)
    · rw [ite_eq_left hga, ite_eq_left (Subtype.ext hga.symm : a = ⟨g, hg⟩)]
    · rw [ite_eq_right hga, ite_eq_right (fun h : a = ⟨g, hg⟩ ↦ hga (congrArg Subtype.val h).symm)]
  · rw [dite_eq_right hg, ite_eq_right]
    rintro rfl
    exact hg a.2

open Classical in
/-- The coefficients of the image are the coefficients of the group-ring element. -/
theorem coeff_subgroupAlgebraHom (H : AddSubgroup G) (f : AddMonoidAlgebra K H) (g : G) :
    (subgroupAlgebraHom H f).coeff g = if hg : g ∈ H then f ⟨g, hg⟩ else 0 := by
  induction f using AddMonoidAlgebra.induction_on with
  | hM m =>
    have hof : (AddMonoidAlgebra.of K H (Multiplicative.ofAdd m) : AddMonoidAlgebra K H)
        = Finsupp.single m 1 := rfl
    rw [hof]
    exact coeff_subgroupAlgebraHom_single H m 1 g
  | hadd x y hx hy =>
    rw [map_add, HahnSeries.coeff_add, hx, hy]
    by_cases hg : g ∈ H <;> simp [hg]
  | hsmul r x hx =>
    rw [map_smul, HahnSeries.coeff_smul, hx]
    by_cases hg : g ∈ H <;> simp [hg]

open Classical in
theorem subgroupAlgebraHom_injective (H : AddSubgroup G) :
    Function.Injective (subgroupAlgebraHom H (K := K)) := by
  intro f₁ f₂ h
  ext a
  have hc := congrArg (fun x : K⟦G⟧ ↦ x.coeff (a : G)) h
  simp only [coeff_subgroupAlgebraHom, dite_eq_left a.2] at hc
  simpa using hc

open Classical in
theorem support_subgroupAlgebraHom_subset (H : AddSubgroup G) (f : AddMonoidAlgebra K H) :
    (subgroupAlgebraHom H f).support ⊆ (H : Set G) := by
  intro g hg
  rw [HahnSeries.mem_support, coeff_subgroupAlgebraHom] at hg
  by_cases hgH : g ∈ H
  · exact hgH
  · rw [dite_eq_right hgH] at hg
    exact absurd rfl hg

open Classical in
theorem support_subgroupAlgebraHom_finite (H : AddSubgroup G) (f : AddMonoidAlgebra K H) :
    (subgroupAlgebraHom H f).support.Finite := by
  refine Set.Finite.subset ((f.support : Finset H).finite_toSet.image ((↑) : H → G)) ?_
  intro g hg
  rw [HahnSeries.mem_support, coeff_subgroupAlgebraHom] at hg
  by_cases hgH : g ∈ H
  · rw [dite_eq_left hgH] at hg
    exact ⟨⟨g, hgH⟩, Finsupp.mem_support_iff.mpr hg, rfl⟩
  · rw [dite_eq_right hgH] at hg
    exact absurd rfl hg

open Classical in
/-- Every finite-support series supported in `H` comes from the group ring of `H`. -/
theorem exists_subgroupAlgebraHom_eq
    (H : AddSubgroup G) {x : K⟦G⟧} (hfin : x.support.Finite)
    (hsub : x.support ⊆ (H : Set G)) :
    ∃ f : AddMonoidAlgebra K H, subgroupAlgebraHom H f = x := by
  set xf : G →₀ K := Finsupp.onFinset hfin.toFinset x.coeff
    (fun a ha ↦ hfin.mem_toFinset.mpr ha) with hxf
  have hinj : Set.InjOn ((↑) : H → G) (((↑) : H → G) ⁻¹' xf.support) :=
    fun a _ b _ hab ↦ Subtype.ext hab
  refine ⟨Finsupp.comapDomain ((↑) : H → G) xf hinj, ?_⟩
  ext g
  rw [coeff_subgroupAlgebraHom]
  by_cases hgH : g ∈ H
  · rw [dite_eq_left hgH, Finsupp.comapDomain_apply, hxf, Finsupp.onFinset_apply]
  · rw [dite_eq_right hgH]
    by_contra hne
    exact hgH (hsub ((HahnSeries.mem_support _ _).mpr (Ne.symm hne)))

/-- Divisibility in the group ring of `H` matches divisibility of the images. -/
theorem dvd_iff_dvdFS_subgroupAlgebraHom (H : AddSubgroup G) (a b : AddMonoidAlgebra K H) :
    a ∣ b ↔ DvdFS (subgroupAlgebraHom H a) (subgroupAlgebraHom H b) := by
  constructor
  · rintro ⟨c, rfl⟩
    exact dvdFS_iff.mpr ⟨subgroupAlgebraHom H c, support_subgroupAlgebraHom_finite H c,
      by rw [map_mul]⟩
  · intro h
    obtain ⟨w, hwf, hw⟩ := dvdFS_iff.mp h
    rcases eq_or_ne (subgroupAlgebraHom H a) 0 with h0 | h0
    · have ha : a = 0 := subgroupAlgebraHom_injective H (by rw [h0, map_zero])
      refine ⟨0, ?_⟩
      refine subgroupAlgebraHom_injective H ?_
      rw [map_mul, map_zero, mul_zero, hw, h0, zero_mul]
    · have hwsub : w.support ⊆ (H : Set G) :=
        support_subset_of_mul_eq (support_subgroupAlgebraHom_subset H a) h0
          (support_subgroupAlgebraHom_subset H b) hw
      obtain ⟨c, hc⟩ := exists_subgroupAlgebraHom_eq H hwf hwsub
      refine ⟨c, subgroupAlgebraHom_injective H ?_⟩
      rw [map_mul, hc, hw]

end HahnSeries
