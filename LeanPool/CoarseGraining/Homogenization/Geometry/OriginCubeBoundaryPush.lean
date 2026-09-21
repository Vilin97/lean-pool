/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Compact

/-! # Origin Cube Boundary Push -/

namespace Homogenization

/--
The open realization of a triadic cube is open in `\R^d`.
-/
theorem isOpen_openCubeSet {d : ℕ} (Q : TriadicCube d) :
    IsOpen (openCubeSet Q) := by
  rw [openCubeSet_eq_pi_Ioo]
  exact isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)

/--
If a compact set `K` is contained in the half-open centered cube `\square_n`,
then every sufficiently small positive diagonal translation pushes `K` into the
open centered cube.

This is the geometric input behind later boundary-pushing arguments for smooth
test functions on `cubeSet (originCube d n)`.
-/
theorem IsCompact.exists_pos_forall_uniformTranslate_subset_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {K : Set (Vec d)} (hK : IsCompact K)
    (hKsub : K ⊆ cubeSet (originCube d n)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
        (fun x : Vec d => x + (fun _ => ε)) '' K ⊆ openCubeSet (originCube d n) := by
  by_cases hKempty : K = ∅
  · refine ⟨1, zero_lt_one, ?_⟩
    intro ε hε hεle
    simp [hKempty]
  · have hKne : K.Nonempty := by
      exact Set.nonempty_iff_ne_empty.mpr hKempty
    let R : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ n
    let coordImage : Fin d → Set ℝ := fun i => (fun x : Vec d => x i) '' K
    let m : Fin d → ℝ := fun i =>
      Classical.choose ((hK.image (continuous_apply i)).exists_isGreatest
        (by
          rcases hKne with ⟨x, hx⟩
          exact ⟨x i, ⟨x, hx, rfl⟩⟩))
    have hm_mem : ∀ i : Fin d, m i ∈ coordImage i := by
      intro i
      exact (Classical.choose_spec ((hK.image (continuous_apply i)).exists_isGreatest
        (by
          rcases hKne with ⟨x, hx⟩
          exact ⟨x i, ⟨x, hx, rfl⟩⟩))).1
    have hm_ge : ∀ i : Fin d, ∀ y ∈ coordImage i, y ≤ m i := by
      intro i
      exact (Classical.choose_spec ((hK.image (continuous_apply i)).exists_isGreatest
        (by
          rcases hKne with ⟨x, hx⟩
          exact ⟨x i, ⟨x, hx, rfl⟩⟩))).2
    let δ : Fin d → ℝ := fun i => R - m i
    have hδpos : ∀ i : Fin d, 0 < δ i := by
      intro i
      rcases hm_mem i with ⟨x, hx, hxeq⟩
      have hxR : x i < R := by
        have hxCube := (mem_cubeSet_originCube_iff.mp (hKsub hx)) i
        simpa [R] using hxCube.2
      have hmR : m i < R := by
        simpa [hxeq] using hxR
      dsimp [δ]
      linarith
    let values : Finset ℝ := Finset.univ.image δ
    have hvalues_nonempty : values.Nonempty := (Finset.univ_nonempty.image δ)
    let ε₀ : ℝ := values.min' hvalues_nonempty
    have hε₀pos : 0 < ε₀ := by
      rcases Finset.mem_image.mp (Finset.min'_mem values hvalues_nonempty) with ⟨i, _, hi_eq⟩
      have : 0 < values.min' hvalues_nonempty := by
        rw [← hi_eq]
        exact hδpos i
      simpa [ε₀] using this
    refine ⟨ε₀, hε₀pos, ?_⟩
    intro ε hεpos hεlt y hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_openCubeSet_originCube_iff]
    intro i
    have hxCube := (mem_cubeSet_originCube_iff.mp (hKsub hx)) i
    have hxle : x i ≤ m i := hm_ge i (x i) ⟨x, hx, rfl⟩
    have hε₀_le : ε₀ ≤ δ i := by
      exact Finset.min'_le values (δ i)
        (by
          refine Finset.mem_image.mpr ?_
          exact ⟨i, Finset.mem_univ i, rfl⟩)
    have hεδ : ε < δ i := lt_of_lt_of_le hεlt hε₀_le
    constructor
    · change (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n < x i + ε
      have hxlow : (-(1 / 2 : ℝ)) * (3 : ℝ) ^ n ≤ x i := hxCube.1
      have hlt : x i < x i + ε := by linarith
      exact lt_of_le_of_lt hxlow hlt
    · change x i + ε < (1 / 2 : ℝ) * (3 : ℝ) ^ n
      have hupper : x i + ε ≤ m i + ε := by
        simpa [add_comm] using add_le_add_right hxle ε
      have hmε : m i + ε < R := by
        dsimp [δ, R] at hεδ
        linarith
      exact lt_of_le_of_lt hupper hmε

/--
If a compact set `K` is contained in the half-open centered cube `\square_n`,
then some positive diagonal translation pushes `K` into the open centered cube.
-/
theorem IsCompact.exists_pos_uniformTranslate_subset_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {K : Set (Vec d)} (hK : IsCompact K)
    (hKsub : K ⊆ cubeSet (originCube d n)) :
    ∃ ε : ℝ, 0 < ε ∧ (fun x : Vec d => x + (fun _ => ε)) '' K ⊆ openCubeSet (originCube d n) := by
  rcases IsCompact.exists_pos_forall_uniformTranslate_subset_openCubeSet_originCube
      (d := d) (n := n) (K := K) hK hKsub with ⟨ε₀, hε₀pos, htranslate⟩
  exact ⟨ε₀ / 2, by linarith, htranslate (by linarith) (by linarith)⟩

/--
If a smooth test has compact support in the half-open centered cube, then every
sufficiently small positive precomposition by a negative diagonal translation
pushes its support into the open centered cube.
-/
theorem HasCompactSupport.exists_pos_forall_precomp_subRight_tsupport_subset_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (hφsub : tsupport φ ⊆ cubeSet (originCube d n)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {ε : ℝ}, 0 < ε → ε < ε₀ →
        tsupport (fun x : Vec d => φ (x - (fun _ => ε))) ⊆ openCubeSet (originCube d n) := by
  rcases IsCompact.exists_pos_forall_uniformTranslate_subset_openCubeSet_originCube
      (d := d) (n := n) (K := tsupport φ) hφ.isCompact hφsub with ⟨ε₀, hε₀pos, htranslate⟩
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεlt x hx
  have hts :
      tsupport (fun x : Vec d => φ (x - (fun _ => ε))) =
        (Homeomorph.subRight (fun _ => ε)) ⁻¹' tsupport φ := by
    simpa using! tsupport_comp_eq_preimage φ (Homeomorph.subRight (fun _ => ε))
  have hxmem : x - (fun _ => ε) ∈ tsupport φ := by
    rw [hts] at hx
    exact hx
  refine htranslate hεpos hεlt ?_
  exact ⟨x - (fun _ => ε), hxmem, by
    ext i
    simp⟩

/--
If a smooth test has compact support in the half-open centered cube, then after
precomposing with a small negative diagonal translation, its support lies in the
open centered cube.
-/
theorem HasCompactSupport.exists_pos_precomp_subRight_tsupport_subset_openCubeSet_originCube
    {d : ℕ} [NeZero d] {n : ℤ} {φ : Vec d → ℝ} (hφ : HasCompactSupport φ)
    (hφsub : tsupport φ ⊆ cubeSet (originCube d n)) :
    ∃ ε : ℝ, 0 < ε ∧
      tsupport (fun x : Vec d => φ (x - (fun _ => ε))) ⊆ openCubeSet (originCube d n) := by
  rcases HasCompactSupport.exists_pos_forall_precomp_subRight_tsupport_subset_openCubeSet_originCube
      (d := d) (n := n) (φ := φ) hφ hφsub with ⟨ε₀, hε₀pos, hpush⟩
  exact ⟨ε₀ / 2, by linarith, hpush (by linarith) (by linarith)⟩

end Homogenization
