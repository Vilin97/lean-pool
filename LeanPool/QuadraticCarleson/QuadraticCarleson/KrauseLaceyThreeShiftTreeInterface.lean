/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyThreeShiftGrid
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyBadScaleInputs
import LeanPool.QuadraticCarleson.QuadraticCarleson.KrauseLaceyStoppingRecursion

/-!
# The finite three-shift grids satisfy the KL bad-scale tree interface

This file connects the concrete complete descendant trees in each of the
three translated dyadic grids with the abstract parent-closure hypothesis
used in the local Krause--Lacey bad-scale estimates.
-/

open Function MeasureTheory Set

namespace QuadraticCarleson
namespace KrauseLaceyThreeShiftGrid

open CalderonZygmundDyadicStopping
open KrauseLaceyStoppingExtraction KrauseLaceyStoppingRecursion


noncomputable section

/-- Every represented descendant interval lies inside the represented root. -/
theorem finiteShiftGridInterval_subset_root
    (topScale : ℤ) (shift : Fin 3) {depth : ℕ} {q q₀ : ℤ}
    (haddr : q₀ * (2 : ℤ) ^ depth ≤ q ∧
      q ≤ (q₀ + 1) * (2 : ℤ) ^ depth - 1) :
    (finiteShiftGridInterval topScale shift depth q).carrier ⊆
      (finiteShiftGridInterval topScale shift 0 q₀).carrier := by
  have hlen := dyadicLength_eq_pow_mul
    (L := shiftedGridRootLength topScale) (Nat.zero_le depth)
  have hd := dyadicLength_pos (shiftedGridRootLength_pos topScale) depth
  have hloZ : q₀ * (2 : ℤ) ^ depth ≤ q := haddr.1
  have hhiZ : q + 1 ≤ (q₀ + 1) * (2 : ℤ) ^ depth := by omega
  have hloR : ((q₀ * (2 : ℤ) ^ depth : ℤ) : ℝ) *
      dyadicLength (shiftedGridRootLength topScale) depth ≤
      (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) depth :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hloZ) hd.le
  have hhiR : ((q + 1 : ℤ) : ℝ) *
      dyadicLength (shiftedGridRootLength topScale) depth ≤
      (((q₀ + 1) * (2 : ℤ) ^ depth : ℤ) : ℝ) *
        dyadicLength (shiftedGridRootLength topScale) depth :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hhiZ) hd.le
  intro x hx
  change
    (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) depth < x ∧
      x ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((q : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) depth at hx
  change
    (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (q₀ : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 < x ∧
      x ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((q₀ : ℝ) + 1) * dyadicLength (shiftedGridRootLength topScale) 0
  simp only [Nat.sub_zero] at hlen
  push_cast at hloR hhiR
  constructor
  · calc
      (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (q₀ : ℝ) * dyadicLength (shiftedGridRootLength topScale) 0 =
          (shift : ℝ) * shiftedGridRootLength topScale / 3 +
            ((q₀ : ℝ) * (2 : ℝ) ^ depth) *
              dyadicLength (shiftedGridRootLength topScale) depth := by
                rw [hlen]
                ring
      _ ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) depth := by
            linarith
      _ < x := hx.1
  · calc
      x ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((q : ℝ) + 1) *
            dyadicLength (shiftedGridRootLength topScale) depth := hx.2
      _ ≤ (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          (((q₀ : ℝ) + 1) * (2 : ℝ) ^ depth) *
            dyadicLength (shiftedGridRootLength topScale) depth := by
              linarith
      _ = (shift : ℝ) * shiftedGridRootLength topScale / 3 +
          ((q₀ : ℝ) + 1) *
            dyadicLength (shiftedGridRootLength topScale) 0 := by
              rw [hlen]
              ring

/-- At fixed largest scale and shift, the depth/address representation of a
grid interval is unique. -/
theorem finiteShiftGridInterval_injective
    (topScale : ℤ) (shift : Fin 3) {depth depth' : ℕ} {q q' : ℤ}
    (h : finiteShiftGridInterval topScale shift depth q =
      finiteShiftGridInterval topScale shift depth' q') :
    depth = depth' ∧ q = q' := by
  have hlength := congrArg RealInterval.length h
  rw [finiteShiftGridInterval_length, finiteShiftGridInterval_length] at hlength
  unfold dyadicLength at hlength
  have hcross := (div_eq_div_iff (by positivity : (2 : ℝ) ^ depth ≠ 0)
    (by positivity : (2 : ℝ) ^ depth' ≠ 0)).mp hlength
  have hroot := shiftedGridRootLength_pos topScale
  have hpowR : (2 : ℝ) ^ depth = (2 : ℝ) ^ depth' := by
    nlinarith
  have hpowN : (2 : ℕ) ^ depth = (2 : ℕ) ^ depth' := by
    exact_mod_cast hpowR
  have hdepth : depth = depth' :=
    Nat.pow_right_injective (by norm_num) hpowN
  subst depth'
  have hleft := congrArg RealInterval.left h
  change
    (shift : ℝ) * shiftedGridRootLength topScale / 3 +
        (q : ℝ) * dyadicLength (shiftedGridRootLength topScale) depth =
      (shift : ℝ) * shiftedGridRootLength topScale / 3 +
        (q' : ℝ) * dyadicLength (shiftedGridRootLength topScale) depth at hleft
  have hlenpos := dyadicLength_pos (shiftedGridRootLength_pos topScale) depth
  have hqR : (q : ℝ) = (q' : ℝ) := by nlinarith
  exact ⟨rfl, by exact_mod_cast hqR⟩

/-- The grid label, depth, and address are jointly unique, even when the two
representations initially come from different members of the three-grid
family. -/
theorem finiteShiftGridInterval_global_injective
    (topScale : ℤ) {shift shift' : Fin 3} {depth depth' : ℕ} {q q' : ℤ}
    (h : finiteShiftGridInterval topScale shift depth q =
      finiteShiftGridInterval topScale shift' depth' q') :
    depth = depth' ∧ shift = shift' ∧ q = q' := by
  have hlength := congrArg RealInterval.length h
  rw [finiteShiftGridInterval_length, finiteShiftGridInterval_length] at hlength
  unfold dyadicLength at hlength
  have hcross := (div_eq_div_iff (by positivity : (2 : ℝ) ^ depth ≠ 0)
    (by positivity : (2 : ℝ) ^ depth' ≠ 0)).mp hlength
  have hroot := shiftedGridRootLength_pos topScale
  have hpowR : (2 : ℝ) ^ depth = (2 : ℝ) ^ depth' := by
    nlinarith
  have hpowN : (2 : ℕ) ^ depth = (2 : ℕ) ^ depth' := by
    exact_mod_cast hpowR
  have hdepth : depth = depth' :=
    Nat.pow_right_injective (by norm_num) hpowN
  subst depth'
  have hparent :
      KrauseLaceyShiftedLocalization.centralThirdTileParent
          (dyadicLength (shiftedGridRootLength topScale) depth)
          (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth)
          (finiteShiftGridTileIndex shift depth q) =
        KrauseLaceyShiftedLocalization.centralThirdTileParent
          (dyadicLength (shiftedGridRootLength topScale) depth)
          (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth)
          (finiteShiftGridTileIndex shift' depth q') := by
    rw [← finiteShiftGridInterval_eq_centralThirdTileParent,
      ← finiteShiftGridInterval_eq_centralThirdTileParent]
    exact h
  have hindex : finiteShiftGridTileIndex shift depth q =
      finiteShiftGridTileIndex shift' depth q' :=
    (KrauseLaceyShiftedLocalization.centralThirdTileParentEmbedding
      (dyadicLength (shiftedGridRootLength topScale) depth)
      (dyadicLength_pos (shiftedGridRootLength_pos topScale) depth)).injective hparent
  exact ⟨rfl, finiteShiftGridTileIndex_injective depth hindex⟩

/-- The uniquely recovered depth of an interval in a fixed shifted grid;
outside that grid it is set to zero. -/
noncomputable def finiteShiftGridDepth
    (topScale : ℤ) (shift : Fin 3) (I : RealInterval) : ℕ := by
  classical
  exact if h : ∃ p : ℕ × ℤ,
      finiteShiftGridInterval topScale shift p.1 p.2 = I then
    (Classical.choose h).1
  else 0

theorem finiteShiftGridDepth_interval
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    finiteShiftGridDepth topScale shift
      (finiteShiftGridInterval topScale shift depth q) = depth := by
  classical
  unfold finiteShiftGridDepth
  split
  · rename_i h
    exact (finiteShiftGridInterval_injective topScale shift
      (Classical.choose_spec h)).1
  · rename_i h
    exact (h ⟨(depth, q), rfl⟩).elim

/-- The kernel scale attached to an interval of a fixed finite shifted grid. -/
noncomputable def finiteShiftGridScale
    (topScale : ℤ) (shift : Fin 3) (I : RealInterval) : ℤ :=
  topScale - finiteShiftGridDepth topScale shift I

theorem finiteShiftGridInterval_length_eq_scale
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    (finiteShiftGridInterval topScale shift depth q).length =
      (2 : ℝ) ^
        (finiteShiftGridScale topScale shift
          (finiteShiftGridInterval topScale shift depth q) + 2) := by
  rw [finiteShiftGridInterval_length]
  unfold dyadicLength shiftedGridRootLength finiteShiftGridScale
  rw [finiteShiftGridDepth_interval]
  rw [show topScale - (depth : ℤ) + 2 =
    (topScale + 2) - (depth : ℤ) by omega]
  rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast]

/-- Every interval of a complete finite shifted-grid tree is contained in
its root interval. -/
theorem completeFiniteShiftGridTree_subset_root
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    ∀ I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀,
      I.carrier ⊆ (finiteShiftGridInterval topScale shift 0 q₀).carrier := by
  classical
  intro I hI
  obtain ⟨⟨depth, q⟩, haddr, rfl⟩ := Finset.mem_image.mp hI
  rw [mem_completeDescendantIndices_iff] at haddr
  exact finiteShiftGridInterval_subset_root topScale shift haddr.2

/-- Every interval belongs to the complete tree below its canonical
depth-zero ancestor whenever that tree is retained at least to the interval's
depth.  The ancestor address is Euclidean division by `2 ^ depth`; this is
valid for negative addresses as well. -/
theorem finiteShiftGridInterval_mem_completeAncestorTree_of_le
    (topScale : ℤ) (shift : Fin 3) (maxDepth depth : ℕ) (q : ℤ)
    (hdepth : depth ≤ maxDepth) :
    finiteShiftGridInterval topScale shift depth q ∈
      completeFiniteShiftGridTree topScale shift maxDepth
        (q / (2 : ℤ) ^ depth) := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨(depth, q), ?_, rfl⟩
  rw [mem_completeDescendantIndices_iff]
  let D : ℤ := (2 : ℤ) ^ depth
  have hDpos : 0 < D := by dsimp [D]; positivity
  have hrem0 : 0 ≤ q % D := Int.emod_nonneg q hDpos.ne'
  have hremD : q % D < D := Int.emod_lt_of_pos q hDpos
  have hdecomp : q % D + D * (q / D) = q := Int.emod_add_mul_ediv q D
  change depth ≤ maxDepth ∧
    (q / D) * D ≤ q ∧ q ≤ (q / D + 1) * D - 1
  constructor
  · exact hdepth
  constructor
  · calc
      (q / D) * D = D * (q / D) := by ring
      _ ≤ q := by omega
  · calc
      q = q % D + D * (q / D) := hdecomp.symm
      _ ≤ (D - 1) + D * (q / D) := by omega
      _ = (q / D + 1) * D - 1 := by ring

/-- Every interval has a canonical depth-zero ancestor, obtained by Euclidean
division of its address, and belongs to the corresponding complete tree. -/
theorem finiteShiftGridInterval_mem_completeAncestorTree
    (topScale : ℤ) (shift : Fin 3) (depth : ℕ) (q : ℤ) :
    finiteShiftGridInterval topScale shift depth q ∈
      completeFiniteShiftGridTree topScale shift depth
        (q / (2 : ℤ) ^ depth) :=
  finiteShiftGridInterval_mem_completeAncestorTree_of_le
    topScale shift depth depth q le_rfl

/-- A complete finite shifted-grid tree inherits the laminar geometry of
its ambient translated dyadic grid. -/
theorem completeFiniteShiftGridTree_laminar
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    Set.Pairwise
      (↑(completeFiniteShiftGridTree topScale shift maxDepth q₀) : Set RealInterval)
      fun I J ↦ I.carrier ⊆ J.carrier ∨ J.carrier ⊆ I.carrier ∨
        Disjoint I.carrier J.carrier := by
  classical
  intro I hI J hJ _
  obtain ⟨⟨depth, q⟩, _, rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨⟨depth', q'⟩, _, rfl⟩ := Finset.mem_image.mp hJ
  exact finiteShiftGridInterval_laminar topScale shift depth q depth' q'

/-- Every member of the concrete tree has exactly the source scale relation
for the recovered kernel label. -/
theorem completeFiniteShiftGridTree_length_eq_scale
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    ∀ I ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀,
      I.length = (2 : ℝ) ^ (finiteShiftGridScale topScale shift I + 2) := by
  classical
  intro I hI
  obtain ⟨⟨depth, q⟩, _, rfl⟩ := Finset.mem_image.mp hI
  exact finiteShiftGridInterval_length_eq_scale topScale shift depth q

/-- The complete finite shifted-grid tree has the literal dyadic parents
required by the actual bad-scale mass estimate. -/
theorem completeFiniteShiftGridTree_hasDyadicParents
    (topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ) :
    KrauseLaceyBadScale.HasDyadicParents
      (completeFiniteShiftGridTree topScale shift maxDepth q₀)
      (finiteShiftGridInterval topScale shift 0 q₀) := by
  classical
  intro I hI hIroot
  obtain ⟨⟨depth, q⟩, haddr, rfl⟩ := Finset.mem_image.mp hI
  have hdepth : 0 < depth := by
    by_contra hn
    have hd0 : depth = 0 := Nat.eq_zero_of_not_pos hn
    subst depth
    rw [mem_completeDescendantIndices_iff] at haddr
    norm_num at haddr
    have hq : q = q₀ := by omega
    subst q
    exact hIroot rfl
  obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hdepth)
  let K := finiteShiftGridInterval topScale shift d (q / 2)
  have hparentAddr : (d, q / 2) ∈ completeDescendantIndices maxDepth q₀ :=
    parent_mem_completeDescendantIndices haddr (by omega)
  have hKmem : K ∈ completeFiniteShiftGridTree topScale shift maxDepth q₀ := by
    apply Finset.mem_image.mpr
    exact ⟨(d, q / 2), hparentAddr, rfl⟩
  refine ⟨K, hKmem, finiteShiftGridInterval_parent_subset topScale shift d q, ?_, ?_⟩
  · have hpos := (finiteShiftGridInterval topScale shift (d + 1) q).length_pos
    rw [finiteShiftGridInterval_parent_length]
    linarith
  · rw [finiteShiftGridInterval_parent_length]

/-- The abstract one-step stopping theorem applies directly to every
concrete complete shifted-grid tree: none of its geometric hypotheses remain
to be supplied by a caller. -/
theorem completeFiniteShiftGridTree_stopping_step
    (ell₀ topScale : ℤ) (shift : Fin 3) (maxDepth : ℕ) (q₀ : ℤ)
    {f g : ℝ → ℂ} (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f) (hgi : Integrable g) :
    let S := completeFiniteShiftGridTree topScale shift maxDepth q₀
    let scale := finiteShiftGridScale topScale shift
    let I₀ := finiteShiftGridInterval topScale shift 0 q₀
    IsSparse (1 / 4) (↑(stoppingStepFamily S f g I₀) : Set RealInterval) ∧
      (∀ J ∈ goodCollection S f g I₀,
        intervalL1Average f J ≤ 10 * intervalL1Average f I₀ ∧
          intervalL1Average g J ≤ 10 * intervalL1Average g I₀) ∧
      (∀ K ∈ stoppingChildren S f g I₀, ∀ x, x ∉ K.carrier →
        localizedTailMaximal ell₀ scale (childCollection S K) f x = 0) ∧
      (∫⁻ x, localizedTailMaximal ell₀ scale S f x * ‖g x‖ₑ) ≤
        (∫⁻ x, localizedTailMaximal ell₀ scale
          (goodCollection S f g I₀) f x * ‖g x‖ₑ) +
          ∑ K ∈ stoppingChildren S f g I₀,
            ∫⁻ x, localizedTailMaximal ell₀ scale
              (childCollection S K) f x * ‖g x‖ₑ := by
  dsimp only
  exact finite_localized_stopping_step ell₀
    (finiteShiftGridScale topScale shift)
    (completeFiniteShiftGridTree topScale shift maxDepth q₀)
    hf hg hfi hgi (finiteShiftGridInterval topScale shift 0 q₀)
    (completeFiniteShiftGridTree_subset_root topScale shift maxDepth q₀)
    (completeFiniteShiftGridTree_length_eq_scale topScale shift maxDepth q₀)
    (completeFiniteShiftGridTree_laminar topScale shift maxDepth q₀)


end

end KrauseLaceyThreeShiftGrid
end QuadraticCarleson
