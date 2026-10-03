/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.TriadicPartition
public import LeanPool.CoarseGraining.Homogenization.Geometry.CubeMeasure
public import LeanPool.CoarseGraining.Homogenization.Multiscale.CubeAverage

/-! # Projection -/

@[expose] public section

namespace Homogenization

open scoped BigOperators

@[simp] theorem cubeIncrement_zero {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeIncrement Q 0 f = cubeProjection Q 0 f := rfl

@[simp] theorem cubeIncrement_succ {d : ℕ} (Q : TriadicCube d) (n : ℕ) (f : Vec d → ℝ) :
    cubeIncrement Q (n + 1) f = fun x => cubeProjection Q (n + 1) f x - cubeProjection Q n f x := rfl

theorem existsUnique_descendantAtDepth_mem_cubeSet {d : ℕ} {Q : TriadicCube d} {x : Vec d}
    (n : ℕ) (hx : x ∈ cubeSet Q) :
    ∃! R : TriadicCube d, R ∈ descendantsAtDepth Q n ∧ x ∈ cubeSet R := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet n hx with ⟨R, hR, hxR⟩
  refine ⟨R, ⟨hR, hxR⟩, ?_⟩
  intro S hS
  rcases hS with ⟨hS, hxS⟩
  by_contra hRS
  have hdisj : Disjoint (cubeSet R) (cubeSet S) :=
    pairwiseDisjoint_descendantsAtDepth Q n hR hS fun h => hRS h.symm
  exact hdisj.le_bot ⟨hxR, hxS⟩

theorem existsUnique_descendantAtScale_mem_cubeSet {d : ℕ} {Q : TriadicCube d} {x : Vec d}
    {k : ℤ} (hk : k ≤ Q.scale) (hx : x ∈ cubeSet Q) :
    ∃! R : TriadicCube d, R ∈ descendantsAtScale Q k ∧ x ∈ cubeSet R := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk]
  exact existsUnique_descendantAtDepth_mem_cubeSet (Int.toNat (Q.scale - k)) hx

theorem cubeProjection_eq_zero_of_not_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) {x : Vec d} (hx : x ∉ cubeSet Q) :
    cubeProjection Q j f x = 0 := by
  classical
  unfold cubeProjection
  refine Finset.sum_eq_zero ?_
  intro R hR
  have hxR : x ∉ cubeSet R := by
    intro hxR
    exact hx (cubeSet_subset_of_mem_descendantsAtDepth hR hxR)
  simp [hxR]

theorem cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (f : Vec d → ℝ) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hxR : x ∈ cubeSet R) :
    cubeProjection Q j f x = cubeAverage R f := by
  classical
  unfold cubeProjection
  have hsum :
      Finset.sum (descendantsAtDepth Q j) (fun S => if x ∈ cubeSet S then cubeAverage S f else 0) =
        if x ∈ cubeSet R then cubeAverage R f else 0 :=
    Finset.sum_eq_single_of_mem R hR (fun S hS hSR => by
      have hdisj : Disjoint (cubeSet R) (cubeSet S) :=
        pairwiseDisjoint_descendantsAtDepth Q j hR hS fun h => hSR h.symm
      have hxS : x ∉ cubeSet S := by
        intro hxS
        exact hdisj.le_bot ⟨hxR, hxS⟩
      simp [hxS])
  simpa [hxR] using hsum

theorem cubeProjection_eq_cubeAverage_of_mem_descendantsAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (f : Vec d → ℝ) {x : Vec d}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k) (hxR : x ∈ cubeSet R) :
    cubeProjection Q (Int.toNat (Q.scale - k)) f x = cubeAverage R f := by
  rw [descendantsAtScale_eq_descendantsAtDepth Q hk] at hR
  exact cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR

theorem cubeProjection_eq_cubeProjection_of_mem_same_descendant {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (f : Vec d → ℝ) {x y : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hxR : x ∈ cubeSet R) (hyR : y ∈ cubeSet R) :
    cubeProjection Q j f x = cubeProjection Q j f y := by
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR]
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hyR]

theorem cubeProjection_eq_cubeProjection_of_mem_same_descendantAtScale {d : ℕ}
    {Q R : TriadicCube d} {k : ℤ} (f : Vec d → ℝ) {x y : Vec d}
    (hk : k ≤ Q.scale) (hR : R ∈ descendantsAtScale Q k)
    (hxR : x ∈ cubeSet R) (hyR : y ∈ cubeSet R) :
    cubeProjection Q (Int.toNat (Q.scale - k)) f x =
      cubeProjection Q (Int.toNat (Q.scale - k)) f y := by
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtScale f hk hR hxR]
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtScale f hk hR hyR]

theorem cubeProjection_eq_zero_of_not_mem_descendantsAtDepth_union {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ) {x : Vec d}
    (hx : x ∉ (⋃ R ∈ (descendantsAtDepth Q j : Set (TriadicCube d)), cubeSet R)) :
    cubeProjection Q j f x = 0 := by
  apply cubeProjection_eq_zero_of_not_mem_cubeSet Q j f
  intro hxQ
  exact hx ((cubeSet_eq_iUnion_descendantsAtDepth Q j).symm ▸ hxQ)

theorem cubeAverage_const {d : ℕ} (Q : TriadicCube d) (c : ℝ) :
    cubeAverage Q (fun _ => c) = c := by
  have hvol : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  have hreal : MeasureTheory.volume.real (cubeSet Q) = cubeVolume Q := by
    simp [MeasureTheory.measureReal_def, volume_cubeSet_toReal]
  calc
    cubeAverage Q (fun _ => c)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q, c ∂MeasureTheory.volume := rfl
    _ = (cubeVolume Q)⁻¹ * (MeasureTheory.volume.real (cubeSet Q) * c) := by
      simp [MeasureTheory.integral_const, smul_eq_mul]
    _ = (cubeVolume Q)⁻¹ * (cubeVolume Q * c) := by rw [hreal]
    _ = ((cubeVolume Q)⁻¹ * cubeVolume Q) * c := by ring
    _ = c := by rw [inv_mul_cancel₀ hvol, one_mul]

theorem cubeProjection_const_of_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    {x : Vec d} (hx : x ∈ cubeSet Q) :
    cubeProjection Q j (fun _ => c) x = c := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet j hx with ⟨R, hR, hxR⟩
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth (fun _ => c) hR hxR,
    cubeAverage_const]

theorem cubeProjection_const_of_not_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    {x : Vec d} (hx : x ∉ cubeSet Q) :
    cubeProjection Q j (fun _ => c) x = 0 :=
  cubeProjection_eq_zero_of_not_mem_cubeSet Q j (fun _ => c) hx

theorem cubeIncrement_eq_zero_of_not_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (f : Vec d → ℝ) {x : Vec d} (hx : x ∉ cubeSet Q) :
    cubeIncrement Q j f x = 0 := by
  cases j with
  | zero =>
      simpa [cubeIncrement] using cubeProjection_eq_zero_of_not_mem_cubeSet Q 0 f hx
  | succ n =>
      simp [cubeIncrement, cubeProjection_eq_zero_of_not_mem_cubeSet Q _ f hx]

theorem cubeIncrement_eq_sub_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (f : Vec d → ℝ) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q (j + 1)) (hxR : x ∈ cubeSet R) :
    cubeIncrement Q (j + 1) f x = cubeAverage R f - cubeProjection Q j f x := by
  rw [cubeIncrement_succ]
  change cubeProjection Q (j + 1) f x - cubeProjection Q j f x =
    cubeAverage R f - cubeProjection Q j f x
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hR hxR]

theorem cubeIncrement_eq_sub_cubeAverage_of_mem_descendantsAtDepth {d : ℕ}
    {Q R S : TriadicCube d} {j : ℕ} (f : Vec d → ℝ) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q (j + 1)) (hS : S ∈ descendantsAtDepth Q j)
    (hxR : x ∈ cubeSet R) (hxS : x ∈ cubeSet S) :
    cubeIncrement Q (j + 1) f x = cubeAverage R f - cubeAverage S f := by
  rw [cubeIncrement_eq_sub_cubeProjection_of_mem_descendantsAtDepth f hR hxR,
    cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth f hS hxS]

theorem cubeIncrement_telescope {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (x : Vec d)
    (n : ℕ) :
    Finset.sum (Finset.range (n + 1)) (fun j => cubeIncrement Q j f x) = cubeProjection Q n f x := by
  induction n with
  | zero =>
      simp [cubeIncrement]
  | succ n ih =>
      rw [Finset.sum_range_succ, cubeIncrement_succ, ih]
      ring

theorem cubeIncrement_zero_const_of_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (c : ℝ)
    {x : Vec d} (hx : x ∈ cubeSet Q) :
    cubeIncrement Q 0 (fun _ => c) x = c := by
  simpa [cubeIncrement] using cubeProjection_const_of_mem_cubeSet Q 0 c hx

theorem cubeIncrement_zero_const_of_not_mem_cubeSet {d : ℕ} (Q : TriadicCube d) (c : ℝ)
    {x : Vec d} (hx : x ∉ cubeSet Q) :
    cubeIncrement Q 0 (fun _ => c) x = 0 := by
  simpa [cubeIncrement] using cubeProjection_const_of_not_mem_cubeSet Q 0 c hx

theorem cubeIncrement_succ_const {d : ℕ} (Q : TriadicCube d) (j : ℕ) (c : ℝ) (x : Vec d) :
    cubeIncrement Q (j + 1) (fun _ => c) x = 0 := by
  by_cases hx : x ∈ cubeSet Q
  · rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (j + 1) hx with ⟨R, hR, hxR⟩
    rcases exists_mem_descendantsAtDepth_of_mem_cubeSet j hx with ⟨S, hS, hxS⟩
    rw [cubeIncrement_eq_sub_cubeAverage_of_mem_descendantsAtDepth (fun _ => c) hR hS hxR hxS,
      cubeAverage_const, cubeAverage_const]
    ring
  · exact cubeIncrement_eq_zero_of_not_mem_cubeSet Q (j + 1) (fun _ => c) hx

end Homogenization
