/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Units.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Compactness.CountablyCompact

/-!
# The Wallace semigroup deduction

This file formalizes Section 9, the final deduction of the Wallace-semigroup corollary in the
current paper under `paper/`.

The paper constructs a Hausdorff group topology on the free Abelian group and proves a
free-ultrafilter subsequence limit property.  Here that output is named
`HasWallaceLimitProperty`.  We prove from it that the nonnegative cone is Hausdorff, countably
compact, cancellative on both sides, a topological semigroup, and not a group.

Every declaration in this file is proved from its explicitly stated hypotheses.
-/

open Filter Set Topology

universe u

namespace Wallace

/-- The precise additive form of a Hausdorff Wallace semigroup.

The final conjunct says that the additive monoid has a noninvertible element, hence is not a
group.  An additive monoid is used rather than a bare semigroup because the counterexample in the
paper is the nonnegative cone and contains zero. -/
def IsWallaceSemigroup (S : Type u) [TopologicalSpace S] [AddMonoid S] : Prop :=
  ContinuousAdd S ∧ IsCancelAdd S ∧ T2Space S ∧ CountablyCompactSpace S ∧
    ∃ x : S, ¬ IsAddUnit x

/-- A convenient unbundled form of the accumulation-point criterion used for countable
compactness. -/
def HasInfiniteSetAccumulationProperty
    (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ B : Set X, B.Infinite → ∃ x : X, AccPt x (Filter.principal B)

/-- In a T1 space, the accumulation-point property implies countable compactness.

This invokes mathlib's standard equivalence
`isCountablyCompact_iff_infinite_subset_has_accPt`; it is not a custom compactness notion. -/
theorem countablyCompact_of_infiniteSet_accumulation
    {X : Type u} [TopologicalSpace X] [T1Space X]
    (hacc : HasInfiniteSetAccumulationProperty X) :
    CountablyCompactSpace X := by
  rw [← isCountablyCompact_univ_iff]
  refine isCountablyCompact_iff_infinite_subset_has_accPt.2 ?_
  intro B _hB hBinf
  obtain ⟨x, hx⟩ := hacc B hBinf
  exact ⟨x, Set.mem_univ x, hx⟩

/-- An injective sequence converging along a free ultrafilter has its limit as an accumulation
point of its range. -/
theorem accPt_range_of_free_ultrafilter_limit
    {X : Type u} [TopologicalSpace X]
    {h : ℕ → X} {p : Ultrafilter ℕ} {x : X}
    (hinj : Function.Injective h)
    (hfree : (p : Filter ℕ) ≤ cofinite)
    (htendsto : Tendsto h p (𝓝 x)) :
    AccPt x (Filter.principal (Set.range h)) := by
  have hcluster : MapClusterPt x cofinite h := htendsto.mapClusterPt.mono hfree
  refine accPt_iff_clusterPt.2 <| ClusterPt.mono hcluster <| le_inf ?_ ?_
  · exact tendsto_principal.mpr
      ((Set.finite_singleton x).preimage hinj.injOn).compl_mem_cofinite
  · exact tendsto_principal.mpr <| Eventually.of_forall fun n => ⟨n, rfl⟩

/-- The exact part of the paper's construction used by the Wallace corollary.

Every injective sequence contained in `P` has a genuine subsequence (`StrictMono φ`) converging
to a point of `P` along a free ultrafilter. -/
def HasWallaceLimitProperty
    {F : Type u} [TopologicalSpace F] [AddZeroClass F]
    (P : AddSubmonoid F) : Prop :=
  ∀ s : ℕ → F, Function.Injective s → (∀ n, s n ∈ P) →
    ∃ (φ : ℕ → ℕ) (x : F) (p : Ultrafilter ℕ),
      StrictMono φ ∧ x ∈ P ∧ (p : Filter ℕ) ≤ cofinite ∧
        Tendsto (s ∘ φ) p (𝓝 x)

/-- A limit in the ambient space is also a limit in a subspace when the sequence and its limit
lie in that subspace. -/
theorem tendsto_subtype_of_tendsto
    {X : Type u} [TopologicalSpace X] {P : Set X} {p : Filter ℕ}
    {u : ℕ → X} {x : X}
    (hu : ∀ n, u n ∈ P) (hx : x ∈ P)
    (htendsto : Tendsto u p (𝓝 x)) :
    Tendsto (fun n => (⟨u n, hu n⟩ : P)) p (𝓝 (⟨x, hx⟩ : P)) := by
  rw [Topology.IsInducing.subtypeVal.tendsto_nhds_iff]
  exact htendsto

/-- The paper's free-ultrafilter limit property gives the accumulation-point property on the
subspace `P`. -/
theorem infiniteSet_accumulation_of_wallaceLimitProperty
    {F : Type u} [TopologicalSpace F] [AddZeroClass F]
    (P : AddSubmonoid F)
    (hlimits : HasWallaceLimitProperty (F := F) P) :
    HasInfiniteSetAccumulationProperty P := by
  intro B hBinf
  let e : ℕ ↪ B := hBinf.natEmbedding
  let eP : ℕ → P := fun n => (e n : P)
  let s : ℕ → F := fun n => eP n
  have ePinj : Function.Injective eP :=
    Subtype.val_injective.comp e.injective
  have sinj : Function.Injective s :=
    Subtype.val_injective.comp ePinj
  have hsmem : ∀ n, s n ∈ P := fun n => (eP n).property
  obtain ⟨φ, x, p, hφ, hx, hfree, htendsto⟩ := hlimits s sinj hsmem
  let u : ℕ → P := fun n => ⟨s (φ n), hsmem (φ n)⟩
  have uinj : Function.Injective u :=
    ePinj.comp hφ.injective
  have utendsto : Tendsto u p (𝓝 (⟨x, hx⟩ : P)) := by
    exact tendsto_subtype_of_tendsto (fun n => hsmem (φ n)) hx htendsto
  have hacc : AccPt (⟨x, hx⟩ : P) (Filter.principal (Set.range u)) :=
    accPt_range_of_free_ultrafilter_limit uinj hfree utendsto
  refine ⟨⟨x, hx⟩, hacc.mono <| Filter.principal_mono.2 ?_⟩
  intro y hy
  obtain ⟨n, rfl⟩ := hy
  change eP (φ n) ∈ B
  exact (e (φ n)).property

/-- The algebraic witness `a ∈ P`, `-a ∉ P` is not an additive unit of the cone. -/
theorem not_isAddUnit_of_neg_not_mem
    {F : Type u} [AddCommGroup F] (P : AddSubmonoid F)
    {a : F} (ha : a ∈ P) (hneg : -a ∉ P) :
    ¬ IsAddUnit (⟨a, ha⟩ : P) := by
  intro hunit
  obtain ⟨b, hab⟩ := hunit.exists_neg
  have habF : a + (b : F) = 0 := congrArg Subtype.val hab
  apply hneg
  rw [← eq_neg_of_add_eq_zero_right habF]
  exact b.property

/-- A countably compact additive submonoid `P` of a Hausdorff Abelian group with continuous
addition is a Wallace semigroup whenever `a ∈ P` and `-a ∉ P` for some `a`. -/
theorem addSubmonoid_isWallace
    {F : Type u} [TopologicalSpace F] [AddCommGroup F]
    [ContinuousAdd F] [T2Space F]
    (P : AddSubmonoid F)
    (hcompact : CountablyCompactSpace P)
    {a : F} (ha : a ∈ P) (hneg : -a ∉ P) :
    IsWallaceSemigroup P := by
  let : CountablyCompactSpace P := hcompact
  refine ⟨inferInstance, inferInstance, inferInstance, inferInstance, ?_⟩
  exact ⟨⟨a, ha⟩, not_isAddUnit_of_neg_not_mem P ha hneg⟩

/-- The Wallace conclusion from the exact accumulation-point hypothesis. -/
theorem addSubmonoid_isWallace_of_accumulation
    {F : Type u} [TopologicalSpace F] [AddCommGroup F]
    [ContinuousAdd F] [T2Space F]
    (P : AddSubmonoid F)
    (hacc : HasInfiniteSetAccumulationProperty P)
    {a : F} (ha : a ∈ P) (hneg : -a ∉ P) :
    IsWallaceSemigroup P :=
  addSubmonoid_isWallace P
    (countablyCompact_of_infiniteSet_accumulation hacc) ha hneg

/-- The Wallace conclusion from the free-ultrafilter limit property proved in the paper. -/
theorem addSubmonoid_isWallace_of_limitProperty
    {F : Type u} [TopologicalSpace F] [AddCommGroup F]
    [ContinuousAdd F] [T2Space F]
    (P : AddSubmonoid F)
    (hlimits : HasWallaceLimitProperty (F := F) P)
    {a : F} (ha : a ∈ P) (hneg : -a ∉ P) :
    IsWallaceSemigroup P :=
  addSubmonoid_isWallace_of_accumulation P
    (infiniteSet_accumulation_of_wallaceLimitProperty P hlimits) ha hneg

/-- The coordinatewise nonnegative cone in the free Abelian group `ι →₀ ℤ`. -/
def positiveCone (ι : Type u) : AddSubmonoid (ι →₀ ℤ) where
  carrier := {x | ∀ i, 0 ≤ x i}
  zero_mem' i := by simp
  add_mem' hx hy i := add_nonneg (hx i) (hy i)

theorem single_one_mem_positiveCone (ι : Type u) (i : ι) :
    Finsupp.single i (1 : ℤ) ∈ positiveCone ι := by
  classical
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Finsupp.single_eq_of_ne (Ne.symm hij)]

theorem neg_single_one_not_mem_positiveCone (ι : Type u) (i : ι) :
    -Finsupp.single i (1 : ℤ) ∉ positiveCone ι := by
  intro h
  have hi := h i
  simp at hi

/-- The formalized Wallace deduction for a free Abelian group: if the topology has the exact
free-ultrafilter limit property constructed by the paper, its nonnegative cone is a Wallace
semigroup. -/
theorem positiveCone_isWallace_of_limitProperty
    (ι : Type u) [TopologicalSpace (ι →₀ ℤ)]
    [IsTopologicalAddGroup (ι →₀ ℤ)] [T2Space (ι →₀ ℤ)]
    (i : ι)
    (hlimits : HasWallaceLimitProperty (F := ι →₀ ℤ) (positiveCone ι)) :
    IsWallaceSemigroup (positiveCone ι) :=
  addSubmonoid_isWallace_of_limitProperty (positiveCone ι) hlimits
    (single_one_mem_positiveCone ι i) (neg_single_one_not_mem_positiveCone ι i)

end Wallace
