/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ShellGeometry
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.BigOperators

/-!
# Bounded-overlap count (G2) for the depth-`j` overlapping center family

A point `x` can lie in at most `3 ^ d` of the overlapping cubes
`ScalarOverlap.cubeSet S` as `S` ranges over `ScalarOverlap.centersAtDepth Q j`.

The proof is purely arithmetic: all centers at depth `j` share the same scale,
hence the same side factor `c = 3 ^ (Q.scale - (j + 1))`.  Membership of `x` in
the overlapping cube of `S` pins each coordinate `S.index i` into the integer
window `(x i / c - 3/2, x i / c + 3/2]`, which contains at most `3` integers.
Since a center is determined by its index vector, at most `3 ^ d` centers can
capture `x`.
-/

@[expose] public section

namespace Homogenization
namespace Gagliardo

open ScalarOverlap

variable {d : ℕ}

/-- The half-open real window `(t - 3/2, t + 3/2]` contains at most three
integers: they all lie in `Finset.Icc (⌊t - 3/2⌋ + 1) ⌊t + 3/2⌋`, and this
interval has at most three elements. -/
theorem card_Icc_window_le_three (t : ℝ) :
    (Finset.Icc (⌊t - 3 / 2⌋ + 1) ⌊t + 3 / 2⌋).card ≤ 3 := by
  have hfloor_le : (⌊t + 3 / 2⌋ : ℝ) ≤ t + 3 / 2 := Int.floor_le _
  have hlt_floor : t - 3 / 2 < (⌊t - 3 / 2⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  have hreal : (⌊t + 3 / 2⌋ : ℝ) < (⌊t - 3 / 2⌋ : ℝ) + 4 := by linarith
  have hint : ⌊t + 3 / 2⌋ < ⌊t - 3 / 2⌋ + 4 := by exact_mod_cast hreal
  rw [Int.card_Icc]
  omega

/-- If `x` lies in the overlapping cube of `S`, then each coordinate of the
index of `S` lies in the integer window determined by `x i / cubeScaleFactor S`. -/
theorem index_mem_Icc_of_mem_overlapCubeSet {S : TriadicCube d} {x : Vec d}
    (hx : x ∈ ScalarOverlap.cubeSet S) (i : Fin d) :
    S.index i ∈
      Finset.Icc (⌊x i / cubeScaleFactor S - 3 / 2⌋ + 1)
        ⌊x i / cubeScaleFactor S + 3 / 2⌋ := by
  have hc : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
  obtain ⟨hlo, hhi⟩ := hx i
  have hlo' : (S.index i : ℝ) - 3 / 2 ≤ x i / cubeScaleFactor S :=
    (le_div_iff₀ hc).mpr hlo
  have hhi' : x i / cubeScaleFactor S < (S.index i : ℝ) + 3 / 2 :=
    (div_lt_iff₀ hc).mpr hhi
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · have hfl : (⌊x i / cubeScaleFactor S - 3 / 2⌋ : ℝ) ≤
        x i / cubeScaleFactor S - 3 / 2 := Int.floor_le _
    have hstrict : (⌊x i / cubeScaleFactor S - 3 / 2⌋ : ℝ) < (S.index i : ℝ) := by
      linarith
    have hint : ⌊x i / cubeScaleFactor S - 3 / 2⌋ < S.index i := by
      exact_mod_cast hstrict
    omega
  · exact Int.le_floor.mpr (by linarith)

/-- All cubes of the depth-`j` center family share the side factor
`3 ^ (Q.scale - (j + 1))`. -/
theorem cubeScaleFactor_eq_of_mem_centersAtDepth {Q S : TriadicCube d} {j : ℕ}
    (hS : S ∈ centersAtDepth Q j) :
    cubeScaleFactor S = (3 : ℝ) ^ (Q.scale - (j + 1 : ℕ)) := by
  rw [cubeScaleFactor, scale_of_mem_centersAtDepth hS]

open Classical in
/-- G2 (bounded overlap): a point lies in at most `3^d` overlapping cubes
of the depth-`j` center family. -/
theorem card_centersAtDepth_filter_mem_le {d : ℕ} (Q : TriadicCube d) (j : ℕ) (x : Vec d) :
    ((ScalarOverlap.centersAtDepth Q j).filter
      (fun S => x ∈ ScalarOverlap.cubeSet S)).card ≤ 3 ^ d := by
  classical
  set c : ℝ := (3 : ℝ) ^ (Q.scale - (j + 1 : ℕ)) with hc_def
  set T : Finset (TriadicCube d) :=
    (ScalarOverlap.centersAtDepth Q j).filter
      (fun S => x ∈ ScalarOverlap.cubeSet S) with hT_def
  set W : Finset (Fin d → ℤ) :=
    Fintype.piFinset
      (fun i => Finset.Icc (⌊x i / c - 3 / 2⌋ + 1) ⌊x i / c + 3 / 2⌋) with hW_def
  have hscale : ∀ S ∈ T, cubeScaleFactor S = c := by
    intro S hS
    exact cubeScaleFactor_eq_of_mem_centersAtDepth (Finset.mem_filter.mp hS).1
  have hmaps : ∀ S ∈ T, S.index ∈ W := by
    intro S hS
    have hx : x ∈ ScalarOverlap.cubeSet S := (Finset.mem_filter.mp hS).2
    refine Fintype.mem_piFinset.mpr fun i => ?_
    have hmem := index_mem_Icc_of_mem_overlapCubeSet hx i
    rwa [hscale S hS] at hmem
  have hinj : Set.InjOn (fun S : TriadicCube d => S.index) ↑T := by
    intro S hS R hR hSR
    have hS' : S ∈ centersAtDepth Q j :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hS)).1
    have hR' : R ∈ centersAtDepth Q j :=
      (Finset.mem_filter.mp (Finset.mem_coe.mp hR)).1
    exact eq_of_index_eq_of_mem_centersAtDepth hS' hR' hSR
  have hcard_le : T.card ≤ W.card :=
    Finset.card_le_card_of_injOn (fun S => S.index) hmaps hinj
  have hW_card : W.card ≤ 3 ^ d := by
    rw [hW_def, Fintype.card_piFinset]
    calc
      ∏ i : Fin d, (Finset.Icc (⌊x i / c - 3 / 2⌋ + 1) ⌊x i / c + 3 / 2⌋).card
          ≤ 3 ^ (Finset.univ : Finset (Fin d)).card :=
        Finset.prod_le_pow_card _ _ 3 fun i _ => card_Icc_window_le_three (x i / c)
      _ = 3 ^ d := by rw [Finset.card_univ, Fintype.card_fin]
  exact hcard_le.trans hW_card

end Gagliardo
end Homogenization
