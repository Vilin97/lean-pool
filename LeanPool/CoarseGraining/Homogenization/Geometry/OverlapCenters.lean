/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Geometry.OverlapCube

/-! # Overlap Centers -/

@[expose] public section

namespace Homogenization

namespace ScalarOverlap

noncomputable section

open scoped BigOperators ENNReal

private theorem cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth' {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j := by
  rw [cubeScaleFactor, scale_eq_sub_of_mem_descendantsAtDepth hR, zpow_sub₀]
  · simp [cubeScaleFactor, div_eq_mul_inv]
  · norm_num

/-- Fine-grid centers used by the overlapping norm at depth `j`.

The centers are descendants one generation below the cube scale. We retain only
those centers whose overlapping cube lies inside the parent cube. -/
noncomputable def centersAtDepth {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) : Finset (TriadicCube d) := by
  classical
  exact (descendantsAtDepth Q (j + 1)).filter
    (fun S => cubeSet S ⊆ Homogenization.cubeSet Q)

theorem mem_centersAtDepth_iff {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} :
    S ∈ centersAtDepth Q j ↔
      S ∈ descendantsAtDepth Q (j + 1) ∧ cubeSet S ⊆ Homogenization.cubeSet Q := by
  classical
  simp [centersAtDepth]

theorem mem_descendantsAtDepth_of_mem_centersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    S ∈ descendantsAtDepth Q (j + 1) :=
  (mem_centersAtDepth_iff.mp hS).1

theorem cubeSet_subset_cubeSet_of_mem_centersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    cubeSet S ⊆ Homogenization.cubeSet Q :=
  (mem_centersAtDepth_iff.mp hS).2

theorem openCubeSet_subset_openCubeSet_of_mem_centersAtDepth {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    openCubeSet S ⊆ Homogenization.openCubeSet Q := by
  have hsub : openCubeSet S ⊆ Homogenization.cubeSet Q :=
    (openCubeSet_subset_cubeSet S).trans
      (cubeSet_subset_cubeSet_of_mem_centersAtDepth hS)
  have hsub_int : openCubeSet S ⊆ interior (Homogenization.cubeSet Q) :=
    (isOpen_openCubeSet S).subset_interior_iff.2 hsub
  simpa [interior_cubeSet_eq_openCubeSet Q] using hsub_int

theorem scaleFactor_eq_cubeScaleFactor_div_pow_of_mem_centersAtDepth
    {d : ℕ} {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    scaleFactor S = cubeScaleFactor Q / (3 : ℝ) ^ j := by
  have hdesc : S ∈ descendantsAtDepth Q (j + 1) :=
    mem_descendantsAtDepth_of_mem_centersAtDepth hS
  unfold scaleFactor
  rw [cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth' hdesc]
  have hpow_succ : (3 : ℝ) ^ (j + 1) = (3 : ℝ) ^ j * 3 := by
    rw [pow_succ]
  rw [hpow_succ]
  field_simp [pow_ne_zero j (show (3 : ℝ) ≠ 0 by norm_num)]

private theorem parent_center_coord_mem_overlap_child {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    let child : TriadicCube d :=
      { scale := Q.scale - 1
        index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 }
    ((((child.index i : ℤ) : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor child ≤
        (Q.index i : ℝ) * cubeScaleFactor Q) ∧
      ((Q.index i : ℝ) * cubeScaleFactor Q <
        ((((child.index i : ℤ) : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor child)) := by
  let child : TriadicCube d :=
    { scale := Q.scale - 1
      index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 }
  have hscale : cubeScaleFactor child = cubeScaleFactor Q / 3 := by
    simp [child]
  have hscale_pos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hd_nonneg : 0 ≤ ((digits i : ℤ) : ℝ) := by
    exact_mod_cast (Nat.zero_le (digits i).val)
  have hd_le_two : ((digits i : ℤ) : ℝ) ≤ 2 := by
    have hd_le_two_int : (digits i : ℤ) ≤ 2 := by
      exact_mod_cast (Nat.le_of_lt_succ (digits i).isLt)
    exact_mod_cast hd_le_two_int
  have hindex :
      (((child.index i : ℤ) : ℝ)) =
        3 * (Q.index i : ℝ) + ((digits i : ℤ) : ℝ) - 1 := by
    simp [child]
  constructor
  · rw [hscale, hindex]
    nlinarith
  · rw [hscale, hindex]
    nlinarith

theorem eq_middleChildCube_of_mem_childCubes_of_cubeSet_subset
    {d : ℕ} {Q S : TriadicCube d} (hS : S ∈ childCubes Q)
    (hsub : cubeSet S ⊆ Homogenization.cubeSet Q) :
    S = middleChildCube Q := by
  classical
  rcases mem_childCubes_iff.mp hS with ⟨digits, rfl⟩
  unfold middleChildCube
  apply congrArg₂ TriadicCube.mk
  · rfl
  · funext i
    have hscale_pos : 0 < cubeScaleFactor Q := by
      simpa [cubeScaleFactor] using
        (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
    by_cases h0 : digits i = (0 : Fin 3)
    · exfalso
      let child : TriadicCube d :=
        { scale := Q.scale - 1
          index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 }
      let center : Vec d := fun k => (Q.index k : ℝ) * cubeScaleFactor Q
      let x : Vec d :=
        Function.update center i (((Q.index i : ℝ) - (5 / 6 : ℝ)) * cubeScaleFactor Q)
      have hscale : cubeScaleFactor child = cubeScaleFactor Q / 3 := by
        simp [child]
      have hx_overlap : x ∈ cubeSet child := by
        intro k
        by_cases hk : k = i
        · subst k
          have hindex :
              (((child.index i : ℤ) : ℝ)) = 3 * (Q.index i : ℝ) - 1 := by
            simp [child, h0]
          have hxcoord :
              x i = ((Q.index i : ℝ) - (5 / 6 : ℝ)) * cubeScaleFactor Q := by
            simp [x]
          constructor
          · rw [hxcoord, hscale, hindex]
            nlinarith
          · rw [hxcoord, hscale, hindex]
            nlinarith
        · have hcenter := parent_center_coord_mem_overlap_child Q digits k
          have hxcoord : x k = center k := by
            simp [x, hk]
          simpa [child, center, hxcoord] using hcenter
      have hx_parent := hsub hx_overlap
      have hxcoord :
          x i = ((Q.index i : ℝ) - (5 / 6 : ℝ)) * cubeScaleFactor Q := by
        simp [x]
      have hparent_lower :
          ((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤
            ((Q.index i : ℝ) - (5 / 6 : ℝ)) * cubeScaleFactor Q := by
        simpa [Homogenization.cubeSet, hxcoord] using (hx_parent i).1
      nlinarith
    · by_cases h1 : digits i = (1 : Fin 3)
      · simp [h1]
      · have h2 : digits i = (2 : Fin 3) := by
          apply Fin.ext
          have hval_le : (digits i).val ≤ 2 :=
            Nat.le_of_lt_succ (digits i).isLt
          have hval_ne_zero : (digits i).val ≠ 0 := by
            intro hval
            exact h0 (Fin.ext hval)
          have hval_ne_one : (digits i).val ≠ 1 := by
            intro hval
            exact h1 (Fin.ext hval)
          omega
        exfalso
        let child : TriadicCube d :=
          { scale := Q.scale - 1
            index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 }
        let center : Vec d := fun k => (Q.index k : ℝ) * cubeScaleFactor Q
        let x : Vec d :=
          Function.update center i (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)
        have hscale : cubeScaleFactor child = cubeScaleFactor Q / 3 := by
          simp [child]
        have hx_overlap : x ∈ cubeSet child := by
          intro k
          by_cases hk : k = i
          · subst k
            have hindex :
                (((child.index i : ℤ) : ℝ)) = 3 * (Q.index i : ℝ) + 1 := by
              simp [child, h2]
              ring
            have hxcoord :
                x i = ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
              simp [x]
            constructor
            · rw [hxcoord, hscale, hindex]
              nlinarith
            · rw [hxcoord, hscale, hindex]
              nlinarith
          · have hcenter := parent_center_coord_mem_overlap_child Q digits k
            have hxcoord : x k = center k := by
              simp [x, hk]
            simpa [child, center, hxcoord] using hcenter
        have hx_parent := hsub hx_overlap
        have hxcoord :
            x i = ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
          simp [x]
        have hparent_upper :
            ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q <
              ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
          simpa [Homogenization.cubeSet, hxcoord] using (hx_parent i).2
        exact (lt_irrefl _ hparent_upper)

theorem middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth
    {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) :
    middleChildCube R ∈ centersAtDepth Q j := by
  rw [mem_centersAtDepth_iff]
  refine ⟨?_, ?_⟩
  · rw [descendantsAtDepth_succ]
    exact Finset.mem_biUnion.mpr
      ⟨R, hR, middleChildCube_mem_childCubes R⟩
  · intro x hx
    have hxR : x ∈ Homogenization.cubeSet R := by
      simpa [cubeSet_middleChildCube_eq_cubeSet R] using hx
    exact cubeSet_subset_of_mem_descendantsAtDepth hR hxR

@[simp] theorem centersAtDepth_zero {d : ℕ}
    (Q : TriadicCube d) :
    centersAtDepth Q 0 = {middleChildCube Q} := by
  classical
  ext S
  constructor
  · intro hS
    have hdesc : S ∈ descendantsAtDepth Q 1 :=
      mem_descendantsAtDepth_of_mem_centersAtDepth (j := 0) hS
    have hchild : S ∈ childCubes Q := by
      simpa using hdesc
    have hsub : cubeSet S ⊆ Homogenization.cubeSet Q :=
      cubeSet_subset_cubeSet_of_mem_centersAtDepth (j := 0) hS
    have hEq : S = middleChildCube Q :=
      eq_middleChildCube_of_mem_childCubes_of_cubeSet_subset hchild hsub
    simp [hEq]
  · intro hS
    have hEq : S = middleChildCube Q := by
      simpa using hS
    rw [hEq]
    exact middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth (by simp)

theorem exists_mem_centersAtDepth_of_mem_cubeSet {d : ℕ}
    {Q : TriadicCube d} {x : Vec d} (j : ℕ)
    (hx : x ∈ Homogenization.cubeSet Q) :
    ∃ S ∈ centersAtDepth Q j, x ∈ cubeSet S := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet j hx with ⟨R, hR, hxR⟩
  refine ⟨middleChildCube R,
    middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth hR, ?_⟩
  simpa [cubeSet_middleChildCube_eq_cubeSet R] using hxR

theorem centersAtDepth_nonempty {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (centersAtDepth Q j).Nonempty := by
  rcases descendantsAtDepth_nonempty Q j with ⟨R, hR⟩
  exact ⟨middleChildCube R,
    middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth hR⟩

theorem centersAtDepth_card_pos {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    0 < (centersAtDepth Q j).card :=
  Finset.card_pos.mpr (centersAtDepth_nonempty Q j)

theorem centersAtDepth_card_ne_zero {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (centersAtDepth Q j).card ≠ 0 :=
  ne_of_gt (centersAtDepth_card_pos Q j)

theorem centersAtDepth_card_le_descendantsAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (centersAtDepth Q j).card ≤
      (descendantsAtDepth Q (j + 1)).card := by
  classical
  unfold centersAtDepth
  exact Finset.card_filter_le _ _

theorem centersAtDepth_card_le_pow {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (centersAtDepth Q j).card ≤ (3 ^ d) ^ (j + 1) := by
  rw [← descendantsAtDepth_card Q (j + 1)]
  exact centersAtDepth_card_le_descendantsAtDepth_card Q j

theorem descendantsAtDepth_card_le_centersAtDepth_card {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) :
    (descendantsAtDepth Q j).card ≤ (centersAtDepth Q j).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun R => middleChildCube R) ?_ ?_
  · intro R hR
    exact middleChildCube_mem_centersAtDepth_of_mem_descendantsAtDepth hR
  · intro R _hR S _hS hRS
    exact middleChildCube_injective hRS

/-- Average over the overlapping centers at a fixed depth. -/
noncomputable def centersAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ) : ℝ :=
  let D := centersAtDepth Q j
  ((D.card : ℝ)⁻¹) * D.sum F

theorem centersAverage_le_centersAverage {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) {F G : TriadicCube d → ℝ}
    (hFG : ∀ S ∈ centersAtDepth Q j, F S ≤ G S) :
    centersAverage Q j F ≤ centersAverage Q j G := by
  classical
  unfold centersAverage
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum hFG)
    (inv_nonneg.mpr (by positivity))

theorem centersAverage_const_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ)
    (hD : (centersAtDepth Q j).Nonempty) :
    centersAverage Q j (fun _ => c) = c := by
  classical
  let D := centersAtDepth Q j
  change ((D.card : ℝ)⁻¹) * D.sum (fun _ => c) = c
  have hD' : D.Nonempty := by
    simpa [D] using hD
  have hcard : (((D.card : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast (Finset.card_ne_zero.mpr hD')
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

theorem centersAverage_const {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (c : ℝ) :
    centersAverage Q j (fun _ => c) = c :=
  centersAverage_const_eq Q j c (centersAtDepth_nonempty Q j)

theorem centersAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (F : TriadicCube d → ℝ)
    (hF : ∀ S ∈ centersAtDepth Q j, 0 ≤ F S) :
    0 ≤ centersAverage Q j F := by
  unfold centersAverage
  exact mul_nonneg (inv_nonneg.mpr (by positivity))
    (Finset.sum_nonneg hF)

end

end ScalarOverlap

end Homogenization
