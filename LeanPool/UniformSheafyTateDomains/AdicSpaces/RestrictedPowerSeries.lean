/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization project
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.HuberRings
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Restricted Power Series

This file defines restricted power series `A⟨T₁, …, Tₖ⟩` and the notion of a strongly
noetherian ring, following Wedhorn's *Adic Spaces*: the convergent/restricted power series ring is
(5.6.1) in §5.6; strong noetherianity is Proposition & Definition 6.36 in §6.7.

## Main definitions

* `MvPowerSeries.IsRestricted`: A power series is **restricted** if its coefficients
  converge to `0` along the cofinite filter on multi-indices.
* `restrictedMvPowerSeriesSubring k A`: The subring of restricted power series in `k`
  variables over `A`, denoted `A⟨T₁, …, Tₖ⟩`.
* `IsStronglyNoetherian A`: A topological ring `A` is **strongly noetherian** if
  `restrictedMvPowerSeriesSubring k A` is noetherian for all `k ≥ 0`
  (Proposition & Definition 6.36 of Wedhorn, stated here with `A`-level restricted
  series; Definition 6.36(i) verbatim is the condition on the completion `Â` — see
  `SheafyRing.lean`'s scope notes).

## Implementation notes

The restricted power series ring is defined as a subring of `MvPowerSeries (Fin k) A`
(the formal power series ring), cut out by the condition that coefficients tend to `0`.
This is the canonical concrete definition; the opaque/axiom-based placeholders in the
Scottish Book problem files are replaced by imports from this module.

The closure of the restricted power series under multiplication (convolution) requires
that `A` is a topological ring. The proof that the convolution of two sequences tending
to `0` also tends to `0` uses the nonarchimedean property to ensure that
arbitrary finite sums of elements in an open additive subgroup remain in the subgroup.
-/

@[expose] public section

open Filter

universe u

/-! ### Nonarchimedean ring instance

`NonarchimedeanRing` extends `IsTopologicalRing` and requires the same `is_nonarchimedean`
condition as `NonarchimedeanAddGroup`. This instance combines the two. -/

/-- A topological ring whose underlying additive group is nonarchimedean is a nonarchimedean
ring. This bridges `IsTopologicalRing` + `NonarchimedeanAddGroup` to `NonarchimedeanRing`. -/
instance (priority := 100) NonarchimedeanRing.ofNonarchimedeanAddGroup
    (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] [NonarchimedeanAddGroup R] :
    NonarchimedeanRing R where
  is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-! ### Restricted power series -/

/-- An element `f` of the multivariate power series ring `A⦃X₁, …, Xₖ⦄` is **restricted**
if its coefficients converge to `0` along the cofinite filter on multi-indices. That is,
for every open neighborhood `U` of `0` in `A`, all but finitely many coefficients of `f`
lie in `U`. This is the defining property of elements of `A⟨T₁, …, Tₖ⟩`.

See Wedhorn, (5.6.1) and §6.7. -/
def MvPowerSeries.IsRestricted {k : ℕ} {A : Type*} [CommRing A] [TopologicalSpace A]
    (f : MvPowerSeries (Fin k) A) : Prop :=
  Tendsto (fun s : Fin k →₀ ℕ => MvPowerSeries.coeff s f) cofinite (nhds 0)

/-- The set of restricted power series forms a subring of `MvPowerSeries (Fin k) A`.

The closure under multiplication (convolution of tendsto-0 coefficient sequences)
requires that `A` is a nonarchimedean topological ring (so that finite sums of elements in an
open additive subgroup remain in the subgroup). This is the canonical definition of
`A⟨T₁, …, Tₖ⟩` (Wedhorn, (5.6.1)/§5.6). -/
def restrictedMvPowerSeriesSubring (k : ℕ) (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Subring (MvPowerSeries (Fin k) A) where
  carrier := {f | MvPowerSeries.IsRestricted f}
  zero_mem' := by
    change Tendsto _ cofinite (nhds 0)
    simp only [map_zero]
    exact tendsto_const_nhds
  one_mem' := by
    change Tendsto _ cofinite (nhds 0)
    apply tendsto_nhds.mpr
    intro U hU h0U
    rw [Filter.mem_cofinite]
    apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
    intro s hs
    simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
    simp only [Set.mem_singleton_iff]
    by_contra h
    exact hs (by rw [MvPowerSeries.coeff_one, ite_eq_right h]; exact h0U)
  add_mem' {f g} hf hg := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s => MvPowerSeries.coeff s f + MvPowerSeries.coeff s g)
        cofinite (nhds 0) := by
      rw [show (0 : A) = 0 + 0 from (add_zero 0).symm]
      exact hf.add hg
    exact this.congr (fun s => by simp [map_add])
  neg_mem' {f} hf := by
    change Tendsto _ cofinite (nhds 0)
    have : Tendsto (fun s => -(MvPowerSeries.coeff s f)) cofinite (nhds 0) := by
      rw [show (0 : A) = -0 from neg_zero.symm]
      exact hf.neg
    exact this.congr (fun s => by simp [map_neg])
  mul_mem' {f g} hf hg := by
    classical
    change Tendsto _ cofinite (nhds 0)
    rw [tendsto_nhds]
    intro U hU h0U
    rw [Filter.mem_cofinite]
    obtain ⟨V, hVU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U (hU.mem_nhds h0U)
    obtain ⟨W, hWV⟩ := NonarchimedeanRing.mul_subset V
    set Sf := {s | MvPowerSeries.coeff s f ∉ (W : Set A)}
    set Sg := {s | MvPowerSeries.coeff s g ∉ (W : Set A)}
    have hSf : Sf.Finite := by
      have := (tendsto_nhds.mp hf) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
      rwa [Filter.mem_cofinite] at this
    have hSg : Sg.Finite := by
      have := (tendsto_nhds.mp hg) _ W.isOpen (SetLike.mem_coe.mpr W.zero_mem)
      rwa [Filter.mem_cofinite] at this
    set T := (W : Set A) ∩
      (⋂ a ∈ hSf.toFinset,
        (fun x => MvPowerSeries.coeff a f * x) ⁻¹' (V : Set A)) ∩
      (⋂ b ∈ hSg.toFinset,
        (fun x => x * MvPowerSeries.coeff b g) ⁻¹' (V : Set A))
    have hT_nhds : T ∈ nhds (0 : A) := by
      refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
      · exact W.isOpen.mem_nhds W.zero_mem
      · apply (Filter.biInter_finset_mem _).mpr
        intro a _
        exact (continuous_const_mul _).continuousAt.preimage_mem_nhds
          (by simpa using V.isOpen.mem_nhds V.zero_mem)
      · apply (Filter.biInter_finset_mem _).mpr
        intro b _
        exact (continuous_mul_const _).continuousAt.preimage_mem_nhds
          (by simpa using V.isOpen.mem_nhds V.zero_mem)
    have hTW : T ⊆ (W : Set A) := fun x hx => hx.1.1
    have hT_left : ∀ a ∈ hSf.toFinset, ∀ y ∈ T,
        MvPowerSeries.coeff a f * y ∈ (V : Set A) := by
      intro a ha y hy
      exact (Set.mem_iInter₂.mp hy.1.2 a ha : _)
    have hT_right : ∀ b ∈ hSg.toFinset, ∀ x ∈ T,
        x * MvPowerSeries.coeff b g ∈ (V : Set A) := by
      intro b hb x hx
      exact (Set.mem_iInter₂.mp hx.2 b hb : _)
    have hgT : {s | MvPowerSeries.coeff s g ∉ T}.Finite :=
      (Filter.mem_cofinite.mp (hg hT_nhds)).subset (fun s hs => hs)
    have hfT : {s | MvPowerSeries.coeff s f ∉ T}.Finite :=
      (Filter.mem_cofinite.mp (hf hT_nhds)).subset (fun s hs => hs)
    set B := {n | ∃ a ∈ hSf.toFinset, a ≤ n ∧ MvPowerSeries.coeff (n - a) g ∉ T} ∪
             {n | ∃ b ∈ hSg.toFinset, b ≤ n ∧ MvPowerSeries.coeff (n - b) f ∉ T}
    have hB_finite : B.Finite := by
      apply Set.Finite.union
      · apply Set.Finite.subset (hSf.toFinset.finite_toSet.biUnion (fun a _ =>
            (hgT.image (· + a))))
        intro n ⟨a, ha, han, hng⟩
        simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
        exact ⟨a, ha, n - a, hng, tsub_add_cancel_of_le han⟩
      · apply Set.Finite.subset (hSg.toFinset.finite_toSet.biUnion (fun b _ =>
            (hfT.image (· + b))))
        intro n ⟨b, hb, hbn, hnf⟩
        simp only [Set.mem_iUnion, Set.mem_image, Finset.mem_coe]
        exact ⟨b, hb, n - b, hnf, tsub_add_cancel_of_le hbn⟩
    apply hB_finite.subset
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_preimage] at hn
    by_contra hnB
    apply hn; clear hn
    simp only [B, Set.mem_union, Set.mem_ofPred_eq, not_or, not_exists, not_and] at hnB
    obtain ⟨hnB1, hnB2⟩ := hnB
    apply hVU
    rw [SetLike.mem_coe]
    rw [show MvPowerSeries.coeff n (f * g) =
      ∑ p ∈ Finset.antidiagonal n,
        MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g
      from MvPowerSeries.coeff_mul (n := n) (φ := f) (ψ := g)]
    apply V.toAddSubgroup.sum_mem
    intro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    by_cases haS : a ∈ Sf
    · have hab_le : a ≤ n := hab ▸ le_add_right le_rfl
      have hb_eq : b = n - a := by rw [← hab]; exact (add_tsub_cancel_left a b).symm
      have hgT_b : MvPowerSeries.coeff b g ∈ T := by
        rw [hb_eq]; exact not_not.mp (hnB1 a (hSf.mem_toFinset.mpr haS) hab_le)
      exact SetLike.mem_coe.mp (hT_left a (hSf.mem_toFinset.mpr haS) _ hgT_b)
    · by_cases hbS : b ∈ Sg
      · have hb_le : b ≤ n := hab ▸ le_add_left le_rfl
        have ha_eq : a = n - b := by rw [← hab]; exact (add_tsub_cancel_right a b).symm
        have hfT_a : MvPowerSeries.coeff a f ∈ T := by
          rw [ha_eq]; exact not_not.mp (hnB2 b (hSg.mem_toFinset.mpr hbS) hb_le)
        exact SetLike.mem_coe.mp (hT_right b (hSg.mem_toFinset.mpr hbS) _ hfT_a)
      · have haW : MvPowerSeries.coeff a f ∈ (W : Set A) := by
          simp only [Sf, Set.mem_ofPred_eq, not_not] at haS; exact haS
        have hbW : MvPowerSeries.coeff b g ∈ (W : Set A) := by
          simp only [Sg, Set.mem_ofPred_eq, not_not] at hbS; exact hbS
        exact SetLike.mem_coe.mp (hWV ⟨_, haW, _, hbW, rfl⟩)

/-! ### Algebra instance -/

/-- Constant power series are restricted: the `algebraMap` image of any `a : A` has
coefficient `a` at multi-index `0` and `0` elsewhere, so it trivially tends to `0`. -/
theorem MvPowerSeries.IsRestricted_algebraMap {k : ℕ} {A : Type*} [CommRing A]
    [TopologicalSpace A] (a : A) :
    MvPowerSeries.IsRestricted (algebraMap A (MvPowerSeries (Fin k) A) a) := by
  change Tendsto _ cofinite (nhds 0)
  apply tendsto_nhds.mpr
  intro U hU h0U
  rw [Filter.mem_cofinite]
  apply (Set.finite_singleton (0 : Fin k →₀ ℕ)).subset
  intro s hs
  simp only [Set.mem_compl_iff, Set.mem_preimage] at hs
  simp only [Set.mem_singleton_iff]
  by_contra h
  exact hs (by
    rw [MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C, ite_eq_right h]; exact h0U)

/-- The restricted power series subring inherits an `A`-algebra structure from the
`MvPowerSeries` algebra instance, since constant power series are restricted. -/
noncomputable instance restrictedMvPowerSeriesSubring.instAlgebra (k : ℕ) (A : Type*)
    [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A] :
    Algebra A (restrictedMvPowerSeriesSubring k A) :=
  RingHom.toAlgebra
    { toFun := fun a => ⟨algebraMap A (MvPowerSeries (Fin k) A) a,
        MvPowerSeries.IsRestricted_algebraMap a⟩
      map_one' := by ext; simp only [map_one, OneMemClass.coe_one]
      map_mul' := by intros; ext; simp only [map_mul, Subring.coe_mul]
      map_zero' := by ext; simp only [map_zero, ZeroMemClass.coe_zero]
      map_add' := by intros; ext; simp only [map_add, Subring.coe_add] }

/-! ### Strongly noetherian rings -/

/-- A topological ring `A` is **strongly noetherian** if the ring of restricted power series
`A⟨T₁, …, Tₖ⟩` is noetherian for all `k ≥ 0` (Proposition & Definition 6.36 of Wedhorn, stated
  here with `A`-level restricted
  series; Definition 6.36(i) verbatim is the condition on the completion `Â` — see
  `SheafyRing.lean`'s scope notes).

This is a fundamental finiteness condition in nonarchimedean geometry, introduced by
Huber. For a noetherian Tate ring, being strongly noetherian is equivalent to saying
that the theory of formal models is well-behaved. -/
class IsStronglyNoetherian (A : Type*) [CommRing A] [TopologicalSpace A]
    [NonarchimedeanRing A] : Prop where
  /-- The restricted power series ring in `k` variables is noetherian for all `k`. -/
  isNoetherianRing_restricted : ∀ k : ℕ,
    IsNoetherianRing (restrictedMvPowerSeriesSubring k A)

/-- **Strongly noetherian implies noetherian** — the `k = 0` case: the index set
`Fin 0 →₀ ℕ` is a singleton, so its cofinite filter is `⊥` and every power series in
zero variables is restricted; `constantCoeff` is then a ring surjection
`A⟨⟩ = A⦃⦄ → A`. -/
theorem IsStronglyNoetherian.isNoetherianRing (A : Type*) [CommRing A]
    [TopologicalSpace A] [NonarchimedeanRing A] [IsStronglyNoetherian A] :
    IsNoetherianRing A := by
  let h0 : IsNoetherianRing (restrictedMvPowerSeriesSubring 0 A) :=
    IsStronglyNoetherian.isNoetherianRing_restricted 0
  refine isNoetherianRing_of_surjective (restrictedMvPowerSeriesSubring 0 A) A
    ((MvPowerSeries.constantCoeff (σ := Fin 0) (R := A)).comp
      (restrictedMvPowerSeriesSubring 0 A).subtype) ?_
  intro a
  refine ⟨⟨MvPowerSeries.C (σ := Fin 0) (R := A) a, ?_⟩, ?_⟩
  · change Filter.Tendsto _ _ _
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot
  · simp [MvPowerSeries.constantCoeff_C]
