/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftLocalization

/-!
# Finite forests in one translated Krause--Lacey grid

A finite collection of depth/address pairs may meet several depth-zero
ancestors.  This file enlarges it, without changing the grid, to the union of
the corresponding complete parent-closed trees.  Thus the concrete
three-shift localization can be fed root by root into the finite stopping
recursion.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open CalderonZygmundDyadicStopping


noncomputable section

local instance : DecidableEq RealInterval := Classical.decEq _

/-- The depth-zero ancestor address of a depth/address pair. -/
def finiteShiftGridRootAddress (p : ℕ × ℤ) : ℤ :=
  p.2 / (2 : ℤ) ^ p.1

/-- The finite set of depth-zero roots met by a finite address family. -/
noncomputable def finiteShiftGridRootAddresses (F : Finset (ℕ × ℤ)) : Finset ℤ := by
  classical
  exact F.image finiteShiftGridRootAddress

/-- The parent-closed forest obtained by completing every canonical root down
to `maxDepth`. -/
noncomputable def completeFiniteShiftGridForest
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (F : Finset (ℕ × ℤ)) :
    Finset RealInterval := by
  classical
  exact (finiteShiftGridRootAddresses F).biUnion fun q₀ ↦
    completeFiniteShiftGridTree topScale shift maxDepth q₀

theorem mem_finiteShiftGridRootAddresses
    {F : Finset (ℕ × ℤ)} {q₀ : ℤ} :
    q₀ ∈ finiteShiftGridRootAddresses F ↔
      ∃ p ∈ F, finiteShiftGridRootAddress p = q₀ := by
  classical
  simp only [finiteShiftGridRootAddresses, Finset.mem_image]

/-- Every prescribed address of depth at most `maxDepth` belongs to its
completed forest. -/
theorem finiteShiftGridInterval_mem_completeFiniteShiftGridForest
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    {F : Finset (ℕ × ℤ)} {depth : ℕ} {q : ℤ}
    (hp : (depth, q) ∈ F) (hdepth : depth ≤ maxDepth) :
    finiteShiftGridInterval topScale shift depth q ∈
      completeFiniteShiftGridForest topScale shift maxDepth F := by
  classical
  apply Finset.mem_biUnion.mpr
  refine ⟨finiteShiftGridRootAddress (depth, q), ?_, ?_⟩
  · apply Finset.mem_image.mpr
    exact ⟨(depth, q), hp, rfl⟩
  · exact finiteShiftGridInterval_mem_completeAncestorTree_of_le
      topScale shift maxDepth depth q hdepth

/-- Every complete component is literally contained in the forest whenever
its root occurs among the canonical roots. -/
theorem completeFiniteShiftGridTree_subset_forest
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ)
    {F : Finset (ℕ × ℤ)} {q₀ : ℤ}
    (hq₀ : q₀ ∈ finiteShiftGridRootAddresses F) :
    completeFiniteShiftGridTree topScale shift maxDepth q₀ ⊆
      completeFiniteShiftGridForest topScale shift maxDepth F := by
  intro I hI
  exact Finset.mem_biUnion.mpr ⟨q₀, hq₀, hI⟩

/-- Each forest member belongs to a concrete complete component and hence is
contained in that component's depth-zero root. -/
theorem completeFiniteShiftGridForest_subset_some_root
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (F : Finset (ℕ × ℤ))
    {I : RealInterval} (hI : I ∈ completeFiniteShiftGridForest topScale shift maxDepth F) :
    ∃ q₀ ∈ finiteShiftGridRootAddresses F,
      I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀ ∧
        I.carrier ⊆ (finiteShiftGridInterval topScale shift 0 q₀).carrier := by
  classical
  rcases Finset.mem_biUnion.mp hI with ⟨q₀, hq₀, hIroot⟩
  exact ⟨q₀, hq₀, hIroot,
    completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀ I hIroot⟩

/-- A finite completed forest remains laminar because all of its components
belong to one translated dyadic grid. -/
theorem completeFiniteShiftGridForest_laminar
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (F : Finset (ℕ × ℤ)) :
    Set.Pairwise
      (↑(completeFiniteShiftGridForest topScale shift maxDepth F) : Set RealInterval)
      fun I J ↦ I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier := by
  classical
  intro I hI J hJ _
  rcases Finset.mem_biUnion.mp hI with ⟨q₀, _, hIq₀⟩
  rcases Finset.mem_image.mp hIq₀ with ⟨⟨depth, q⟩, _, rfl⟩
  rcases Finset.mem_biUnion.mp hJ with ⟨q₁, _, hJq₁⟩
  rcases Finset.mem_image.mp hJq₁ with ⟨⟨depth', q'⟩, _, rfl⟩
  exact finiteShiftGridInterval_laminar topScale shift depth q depth' q'

/-- Every member of the forest has the exact kernel-scale/interval-length
relation required by the localized operator. -/
theorem completeFiniteShiftGridForest_length_eq_scale
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (F : Finset (ℕ × ℤ)) :
    ∀ I ∈ completeFiniteShiftGridForest topScale shift maxDepth F,
      I.length = (2 : ℝ) ^ (finiteShiftGridScale topScale shift I + 2) := by
  classical
  intro I hI
  rcases Finset.mem_biUnion.mp hI with ⟨q₀, _, hIq₀⟩
  exact completeFiniteShiftGridTree_length_eq_scale
    topScale shift maxDepth q₀ I hIq₀

/-- Distinct depth-zero cells of one translated grid are disjoint as actual
half-open sets. -/
theorem finiteShiftGridRootIntervals_pairwiseDisjoint
    (topScale : ℤ) (shift : Fin 3) :
    Pairwise fun q r : ℤ ↦ Disjoint
      (finiteShiftGridInterval topScale shift 0 q).carrier
      (finiteShiftGridInterval topScale shift 0 r).carrier := by
  intro q r hqr
  apply Set.disjoint_left.mpr
  intro x hxq hxr
  change
    (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 < x ∧
      x ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((q : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) 0 at hxq
  change
    (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (r : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 < x ∧
      x ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((r : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) 0 at hxr
  have hL : 0 < dyadicLength (shiftedGridRootLength topScale) 0 :=
    dyadicLength_pos (shiftedGridRootLength_pos topScale) 0
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hstep : q + 1 ≤ r := (Int.add_one_le_iff).mpr hlt
    have hcast : ((q : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) 0 ≤
        (r : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 := by
      apply mul_le_mul_of_nonneg_right _ hL.le
      exact_mod_cast hstep
    linarith
  · have hstep : r + 1 ≤ q := (Int.add_one_le_iff).mpr hgt
    have hcast : ((r : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) 0 ≤
        (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 := by
      apply mul_le_mul_of_nonneg_right _ hL.le
      exact_mod_cast hstep
    linarith

/-- Different root components of the completed forest are disjoint, not just
laminar. -/
theorem completeFiniteShiftGridTree_disjoint_of_ne_root
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) {q₀ q₁ : ℤ}
    (hne : q₀ ≠ q₁) {I J : RealInterval}
    (hI : I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀)
    (hJ : J ∈ completeFiniteShiftGridTree topScale shift maxDepth q₁) :
    Disjoint I.carrier J.carrier := by
  exact (finiteShiftGridRootIntervals_pairwiseDisjoint topScale shift hne).mono
    (completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀ I hI)
    (completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₁ J hJ)

/-- Addresses selected from finitely many depths in one of the three shifted
grids. -/
noncomputable def finiteOneShiftMultiscaleAddresses
    (depths : Finset ℕ) (E : ℕ → Finset ℤ) (shift : Fin 3) :
    Finset (ℕ × ℤ) := by
  classical
  exact depths.biUnion fun depth ↦
    ((E depth).filter fun n ↦ (finiteShiftGridAddress depth n).1 = shift).image
      fun n ↦ (depth, (finiteShiftGridAddress depth n).2)

/-- The corresponding finite multiscale interval family in one shifted
grid. -/
noncomputable def finiteOneShiftMultiscaleFamily
    (topScale : ℤ) (depths : Finset ℕ) (E : ℕ → Finset ℤ) (shift : Fin 3) :
    Finset RealInterval := by
  classical
  exact depths.biUnion fun depth ↦ finiteOneShiftFamily topScale depth (E depth) shift

/-- Every interval selected at one of the retained depths belongs to the
parent-closed forest generated by the corresponding addresses. -/
theorem finiteOneShiftMultiscaleFamily_subset_completeForest
    (topScale : ℤ) (depths : Finset ℕ) (E : ℕ → Finset ℤ) (shift : Fin 3)
    (maxDepth : ℕ) (hdepths : ∀ depth ∈ depths, depth ≤ maxDepth) :
    finiteOneShiftMultiscaleFamily topScale depths E shift ⊆
      completeFiniteShiftGridForest topScale shift maxDepth
        (finiteOneShiftMultiscaleAddresses depths E shift) := by
  classical
  intro I hI
  rcases Finset.mem_biUnion.mp hI with ⟨depth, hdepth, hIdepth⟩
  rcases mem_finiteOneShiftFamily hIdepth with ⟨n, hn, hshift, rfl⟩
  apply finiteShiftGridInterval_mem_completeFiniteShiftGridForest
    topScale shift maxDepth
  · apply Finset.mem_biUnion.mpr
    refine ⟨depth, hdepth, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨n, Finset.mem_filter.mpr ⟨hn, hshift⟩, rfl⟩
  · exact hdepths depth hdepth

/-- A simultaneous finite localization exists at every grid depth.  This
choice packages the fixed-scale theorem without changing any operator. -/
theorem exists_finiteThreeShiftFamily_localization_all_depths
    (f : L0Infinity) (topScale : ℤ) :
    ∃ E : ℕ → Finset ℤ, ∀ depth,
      (∀ I ∈ finiteThreeShiftFamily topScale depth (E depth),
        I.length = dyadicLength (shiftedGridRootLength topScale) depth) ∧
      Set.Pairwise
        (↑(finiteThreeShiftFamily topScale depth (E depth)) : Set RealInterval)
        (Disjoint on fun I : RealInterval ↦ I.centralThird) ∧
      krauseLaceyFixedScaleInput
        (finiteThreeShiftFamily topScale depth (E depth)) f = f := by
  choose E hE using fun depth ↦
    exists_finiteThreeShiftFamily_localization f topScale depth
  exact ⟨E, hE⟩


end

end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
