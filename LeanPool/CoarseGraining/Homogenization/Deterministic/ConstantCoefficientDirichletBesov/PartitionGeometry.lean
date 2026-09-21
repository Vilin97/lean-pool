/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.ConstantCoefficientDirichletBesov.OverlapFluctuation

/-! # Partition Geometry -/

namespace Homogenization

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Pointwise

/-!
### Raw one-sided overlap weights

These are the planned Stage-7 building blocks for the uniform smooth overlap
partition.  Interior coordinates use a two-sided smooth transition across the
outer collar of an overlap cube.  If an overlap face coincides with a parent
face, the corresponding one-sided transition is suppressed; this keeps the raw
weight uniformly positive near `∂Q` when we work relative to `openCubeSet Q`.
-/

noncomputable def cubeCoordLower {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)

noncomputable def cubeCoordUpper {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) : ℝ :=
  (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)

noncomputable def overlapCoordLower {d : ℕ}
    (S : TriadicCube d) (i : Fin d) : ℝ :=
  (((S.index i : ℝ) - (3 / 2 : ℝ)) * cubeScaleFactor S)

noncomputable def overlapCoordUpper {d : ℕ}
    (S : TriadicCube d) (i : Fin d) : ℝ :=
  (((S.index i : ℝ) + (3 / 2 : ℝ)) * cubeScaleFactor S)

theorem mem_openCubeSet_iff_coord_bounds {d : ℕ}
    {Q : TriadicCube d} {x : Vec d} :
    x ∈ openCubeSet Q ↔
      ∀ i : Fin d, cubeCoordLower Q i < x i ∧ x i < cubeCoordUpper Q i := by
  constructor
  · intro hx i
    simpa [cubeCoordLower, cubeCoordUpper] using hx i
  · intro hx i
    simpa [cubeCoordLower, cubeCoordUpper] using hx i

theorem mem_cubeSet_iff_coord_bounds {d : ℕ}
    {Q : TriadicCube d} {x : Vec d} :
    x ∈ cubeSet Q ↔
      ∀ i : Fin d, cubeCoordLower Q i ≤ x i ∧ x i < cubeCoordUpper Q i := by
  constructor
  · intro hx i
    simpa [cubeCoordLower, cubeCoordUpper] using hx i
  · intro hx i
    simpa [cubeCoordLower, cubeCoordUpper] using hx i

theorem mem_openOverlapCubeSet_iff_coord_bounds {d : ℕ}
    {S : TriadicCube d} {x : Vec d} :
    x ∈ openOverlapCubeSet S ↔
      ∀ i : Fin d, overlapCoordLower S i < x i ∧ x i < overlapCoordUpper S i := by
  constructor
  · intro hx i
    simpa [overlapCoordLower, overlapCoordUpper] using hx i
  · intro hx i
    simpa [overlapCoordLower, overlapCoordUpper] using hx i

theorem mem_overlapCubeSet_iff_coord_bounds {d : ℕ}
    {S : TriadicCube d} {x : Vec d} :
    x ∈ overlapCubeSet S ↔
      ∀ i : Fin d, overlapCoordLower S i ≤ x i ∧ x i < overlapCoordUpper S i := by
  constructor
  · intro hx i
    simpa [overlapCoordLower, overlapCoordUpper] using hx i
  · intro hx i
    simpa [overlapCoordLower, overlapCoordUpper] using hx i

theorem cubeScaleFactor_pos' {d : ℕ} (Q : TriadicCube d) :
    0 < cubeScaleFactor Q := by
  simpa [cubeScaleFactor] using
    (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)

theorem cubeCoordUpper_eq_lower_add_scale {d : ℕ}
    (Q : TriadicCube d) (i : Fin d) :
    cubeCoordUpper Q i = cubeCoordLower Q i + cubeScaleFactor Q := by
  simp [cubeCoordLower, cubeCoordUpper]
  ring

theorem cubeCoordLower_child {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    cubeCoordLower
        ({ scale := Q.scale - 1
           index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordLower Q i +
        ((digits i : ℤ) : ℝ) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
              TriadicCube d) := by
  simp [cubeCoordLower, cubeScaleFactor_childCube]
  ring_nf

theorem cubeCoordUpper_child {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    cubeCoordUpper
        ({ scale := Q.scale - 1
           index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordUpper Q i -
        (((2 : ℤ) - (digits i : ℤ)) : ℝ) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
              TriadicCube d) := by
  simp [cubeCoordUpper, cubeScaleFactor_childCube]
  ring_nf

theorem cubeScaleFactor_child_eq_three_mul {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) :
    cubeScaleFactor Q =
      3 *
        cubeScaleFactor
          ({ scale := Q.scale - 1
             index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
            TriadicCube d) := by
  rw [cubeScaleFactor_childCube Q digits]
  ring

theorem overlapCoordLower_child {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    overlapCoordLower
        ({ scale := Q.scale - 1
           index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordLower Q i +
        ((((digits i : ℤ) : ℝ) - 1) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
              TriadicCube d)) := by
  simp [overlapCoordLower, cubeCoordLower, cubeScaleFactor_childCube]
  ring_nf

theorem overlapCoordUpper_child {d : ℕ}
    (Q : TriadicCube d) (digits : Fin d → Fin 3) (i : Fin d) :
    overlapCoordUpper
        ({ scale := Q.scale - 1
           index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) i =
      cubeCoordUpper Q i +
        ((((digits i : ℤ) : ℝ) - 1) *
          cubeScaleFactor
            ({ scale := Q.scale - 1
               index := fun k => 3 * Q.index k + (digits k : ℤ) - 1 } :
              TriadicCube d)) := by
  simp [overlapCoordUpper, cubeCoordUpper, cubeScaleFactor_childCube]
  ring_nf

theorem cubeCoordLower_descendant_eq_or_one_scale_le {d : ℕ} :
    ∀ {n : ℕ} {Q R : TriadicCube d},
      R ∈ descendantsAtDepth Q n →
        ∀ i : Fin d,
          cubeCoordLower R i = cubeCoordLower Q i ∨
            cubeCoordLower Q i + cubeScaleFactor R ≤ cubeCoordLower R i
  | 0, Q, R, hR => by
      rw [descendantsAtDepth_zero] at hR
      rcases Finset.mem_singleton.mp hR with rfl
      intro i
      exact Or.inl rfl
  | n + 1, Q, R, hR => by
      intro i
      rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨P, hP, hRchild⟩
      rcases mem_childCubes_iff.mp hRchild with ⟨digits, rfl⟩
      let C : TriadicCube d :=
        { scale := P.scale - 1
          index := fun k => 3 * P.index k + (digits k : ℤ) - 1 }
      have hlowerC :
          cubeCoordLower C i =
            cubeCoordLower P i + ((digits i : ℤ) : ℝ) * cubeScaleFactor C := by
        simpa [C] using cubeCoordLower_child P digits i
      have hscaleP : cubeScaleFactor P = 3 * cubeScaleFactor C := by
        simpa [C] using cubeScaleFactor_child_eq_three_mul P digits
      have hCpos : 0 < cubeScaleFactor C := cubeScaleFactor_pos' C
      rcases cubeCoordLower_descendant_eq_or_one_scale_le hP i with hPeq | hPle
      · by_cases hzero : (digits i).val = 0
        · have hdigit : (((digits i : ℤ) : ℝ)) = 0 := by
            exact_mod_cast hzero
          left
          change cubeCoordLower C i = cubeCoordLower Q i
          nlinarith [hlowerC, hPeq, hdigit]
        · have hdigit_one : 1 ≤ (((digits i : ℤ) : ℝ)) := by
            have hpos : 0 < (digits i).val := Nat.pos_of_ne_zero hzero
            have hcast : (1 : ℤ) ≤ (digits i : ℤ) := by
              exact_mod_cast hpos
            exact_mod_cast hcast
          right
          change cubeCoordLower Q i + cubeScaleFactor C ≤ cubeCoordLower C i
          nlinarith [hlowerC, hPeq, hCpos, hdigit_one]
      · right
        change cubeCoordLower Q i + cubeScaleFactor C ≤ cubeCoordLower C i
        have hdigit_nonneg : 0 ≤ (((digits i : ℤ) : ℝ)) := by
          exact_mod_cast (Nat.zero_le (digits i).val)
        nlinarith [hlowerC, hPle, hscaleP, hCpos, hdigit_nonneg]

theorem cubeCoordUpper_descendant_eq_or_one_scale_le {d : ℕ} :
    ∀ {n : ℕ} {Q R : TriadicCube d},
      R ∈ descendantsAtDepth Q n →
        ∀ i : Fin d,
          cubeCoordUpper R i = cubeCoordUpper Q i ∨
            cubeCoordUpper R i + cubeScaleFactor R ≤ cubeCoordUpper Q i
  | 0, Q, R, hR => by
      rw [descendantsAtDepth_zero] at hR
      rcases Finset.mem_singleton.mp hR with rfl
      intro i
      exact Or.inl rfl
  | n + 1, Q, R, hR => by
      intro i
      rcases mem_descendantsAtDepth_succ_iff.mp hR with ⟨P, hP, hRchild⟩
      rcases mem_childCubes_iff.mp hRchild with ⟨digits, rfl⟩
      let C : TriadicCube d :=
        { scale := P.scale - 1
          index := fun k => 3 * P.index k + (digits k : ℤ) - 1 }
      have hupperC :
          cubeCoordUpper C i =
            cubeCoordUpper P i -
              (((2 : ℤ) - (digits i : ℤ)) : ℝ) * cubeScaleFactor C := by
        simpa [C] using cubeCoordUpper_child P digits i
      have hscaleP : cubeScaleFactor P = 3 * cubeScaleFactor C := by
        simpa [C] using cubeScaleFactor_child_eq_three_mul P digits
      have hCpos : 0 < cubeScaleFactor C := cubeScaleFactor_pos' C
      rcases cubeCoordUpper_descendant_eq_or_one_scale_le hP i with hPeq | hPle
      · by_cases htwo : (digits i).val = 2
        · have hdiff : (2 : ℝ) - (((digits i : ℤ) : ℝ)) = 0 := by
            have hdigit : (((digits i : ℤ) : ℝ)) = 2 := by
              exact_mod_cast htwo
            nlinarith
          left
          change cubeCoordUpper C i = cubeCoordUpper Q i
          rw [hPeq] at hupperC
          let t : ℝ := (↑(2 : ℤ) : ℝ) - (((digits i : ℤ) : ℝ))
          have hupperC' :
              cubeCoordUpper C i = cubeCoordUpper Q i - t * cubeScaleFactor C := by
            simpa [t] using hupperC
          have ht : t = 0 := by
            simpa [t] using hdiff
          rw [hupperC', ht]
          ring
        · have hdiff_one :
              1 ≤ (2 : ℝ) - (((digits i : ℤ) : ℝ)) := by
            have hdle : (digits i).val ≤ 1 := by
              have hdle_two : (digits i).val ≤ 2 :=
                Nat.le_of_lt_succ (digits i).isLt
              omega
            have hdle_real : (((digits i : ℤ) : ℝ)) ≤ 1 := by
              exact_mod_cast hdle
            nlinarith
          right
          change cubeCoordUpper C i + cubeScaleFactor C ≤ cubeCoordUpper Q i
          rw [hPeq] at hupperC
          let t : ℝ := (↑(2 : ℤ) : ℝ) - (((digits i : ℤ) : ℝ))
          have hupperC' :
              cubeCoordUpper C i = cubeCoordUpper Q i - t * cubeScaleFactor C := by
            simpa [t] using hupperC
          have ht : 1 ≤ t := by
            simpa [t] using hdiff_one
          rw [hupperC']
          nlinarith [hCpos, ht]
      · right
        change cubeCoordUpper C i + cubeScaleFactor C ≤ cubeCoordUpper Q i
        have hPnonneg : 0 ≤ cubeScaleFactor P := (cubeScaleFactor_pos' P).le
        have hCnonneg : 0 ≤ cubeScaleFactor C := hCpos.le
        have hdiff_nonneg :
            0 ≤ (((2 : ℤ) - (digits i : ℤ)) : ℝ) := by
          have hd_le_two : (digits i : ℤ) ≤ 2 := by
            exact_mod_cast Nat.le_of_lt_succ (digits i).isLt
          exact_mod_cast sub_nonneg.mpr hd_le_two
        nlinarith [hupperC, hPle, hscaleP, hCpos, hCnonneg, hPnonneg,
          hdiff_nonneg]

theorem cubeCoordLower_le_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n) (i : Fin d) :
    cubeCoordLower Q i ≤ cubeCoordLower R i := by
  rcases cubeCoordLower_descendant_eq_or_one_scale_le hR i with hEq | hLe
  · exact le_of_eq hEq.symm
  · exact le_trans (by linarith [cubeScaleFactor_pos' R]) hLe

theorem cubeCoordUpper_le_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n) (i : Fin d) :
    cubeCoordUpper R i ≤ cubeCoordUpper Q i := by
  rcases cubeCoordUpper_descendant_eq_or_one_scale_le hR i with hEq | hLe
  · exact le_of_eq hEq
  · exact le_trans (by linarith [cubeScaleFactor_pos' R]) hLe

theorem overlapCubeSet_child_subset_cubeSet_of_digit_safe {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j)
    (digits : Fin d → Fin 3)
    (hlo_safe :
      ∀ i : Fin d, (digits i).val = 0 →
        cubeCoordLower Q i + cubeScaleFactor R ≤ cubeCoordLower R i)
    (hhi_safe :
      ∀ i : Fin d, (digits i).val = 2 →
        cubeCoordUpper R i + cubeScaleFactor R ≤ cubeCoordUpper Q i) :
    overlapCubeSet
        ({ scale := R.scale - 1
           index := fun k => 3 * R.index k + (digits k : ℤ) - 1 } :
          TriadicCube d) ⊆ cubeSet Q := by
  intro y hy i
  let S : TriadicCube d :=
    { scale := R.scale - 1
      index := fun k => 3 * R.index k + (digits k : ℤ) - 1 }
  have hyS : y ∈ overlapCubeSet S := by
    simpa [S] using hy
  have hyi := (mem_overlapCubeSet_iff_coord_bounds.mp hyS i)
  have hSscale : cubeScaleFactor S = cubeScaleFactor R / 3 := by
    simp [S, cubeScaleFactor_childCube R digits]
  have hSlower :
      overlapCoordLower S i =
        cubeCoordLower R i +
          ((((digits i : ℤ) : ℝ) - 1) * cubeScaleFactor S) := by
    simpa [S] using overlapCoordLower_child R digits i
  have hSupper :
      overlapCoordUpper S i =
        cubeCoordUpper R i +
          ((((digits i : ℤ) : ℝ) - 1) * cubeScaleFactor S) := by
    simpa [S] using overlapCoordUpper_child R digits i
  have hQlowerR : cubeCoordLower Q i ≤ cubeCoordLower R i :=
    cubeCoordLower_le_of_mem_descendantsAtDepth hR i
  have hRupperQ : cubeCoordUpper R i ≤ cubeCoordUpper Q i :=
    cubeCoordUpper_le_of_mem_descendantsAtDepth hR i
  have hRscale_pos : 0 < cubeScaleFactor R := cubeScaleFactor_pos' R
  have hSscale_pos : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
  constructor
  · have hlower_overlap : cubeCoordLower Q i ≤ overlapCoordLower S i := by
      by_cases hzero : (digits i).val = 0
      · have hsafe := hlo_safe i hzero
        have hdigit : (((digits i : ℤ) : ℝ)) = 0 := by
          exact_mod_cast hzero
        rw [hSlower, hSscale]
        nlinarith [hsafe, hRscale_pos, hdigit]
      · have hdigit_one : 1 ≤ (((digits i : ℤ) : ℝ)) := by
          have hpos : 0 < (digits i).val := Nat.pos_of_ne_zero hzero
          have hcast : (1 : ℤ) ≤ (digits i : ℤ) := by
            exact_mod_cast hpos
          exact_mod_cast hcast
        rw [hSlower]
        nlinarith [hQlowerR, hSscale_pos, hdigit_one]
    exact le_trans hlower_overlap hyi.1
  · have hupper_overlap : overlapCoordUpper S i ≤ cubeCoordUpper Q i := by
      by_cases htwo : (digits i).val = 2
      · have hsafe := hhi_safe i htwo
        have hdigit : (((digits i : ℤ) : ℝ)) = 2 := by
          exact_mod_cast htwo
        rw [hSupper, hSscale]
        nlinarith [hsafe, hRscale_pos, hdigit]
      · have hdigit_le_one : (((digits i : ℤ) : ℝ)) ≤ 1 := by
          have hdle : (digits i).val ≤ 1 := by
            have hdle_two : (digits i).val ≤ 2 :=
              Nat.le_of_lt_succ (digits i).isLt
            omega
          exact_mod_cast hdle
        rw [hSupper]
        nlinarith [hRupperQ, hSscale_pos, hdigit_le_one]
    exact lt_of_lt_of_le hyi.2 hupper_overlap

noncomputable def plateauChildDigit {d : ℕ}
    (Q R : TriadicCube d) (x : Vec d) (i : Fin d) : Fin 3 :=
  if x i < cubeCoordLower R i + cubeScaleFactor R / 3 then
    if cubeCoordLower R i = cubeCoordLower Q i then
      (1 : Fin 3)
    else
      (0 : Fin 3)
  else if x i < cubeCoordLower R i + 2 * cubeScaleFactor R / 3 then
    (1 : Fin 3)
  else if cubeCoordUpper R i = cubeCoordUpper Q i then
    (1 : Fin 3)
  else
    (2 : Fin 3)

theorem plateauChildDigit_zero_safe {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {x : Vec d} {i : Fin d}
    (hR : R ∈ descendantsAtDepth Q j)
    (hzero : (plateauChildDigit Q R x i).val = 0) :
    cubeCoordLower Q i + cubeScaleFactor R ≤ cubeCoordLower R i := by
  rcases cubeCoordLower_descendant_eq_or_one_scale_le hR i with hEq | hSep
  · exfalso
    by_cases hleft : x i < cubeCoordLower R i + cubeScaleFactor R / 3
    · have hval : (plateauChildDigit Q R x i).val = 1 := by
        have hleftQ : x i < cubeCoordLower Q i + cubeScaleFactor R / 3 := by
          simpa [hEq] using hleft
        simp [plateauChildDigit, hleftQ, hEq]
      omega
    · by_cases hmid : x i < cubeCoordLower R i + 2 * cubeScaleFactor R / 3
      · have hval : (plateauChildDigit Q R x i).val = 1 := by
          simp [plateauChildDigit, hleft, hmid]
        omega
      · by_cases hupper : cubeCoordUpper R i = cubeCoordUpper Q i
        · have hval : (plateauChildDigit Q R x i).val = 1 := by
            simp [plateauChildDigit, hleft, hmid, hupper]
          omega
        · have hval : (plateauChildDigit Q R x i).val = 2 := by
            simp [plateauChildDigit, hleft, hmid, hupper]
          omega
  · exact hSep

theorem plateauChildDigit_two_safe {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {x : Vec d} {i : Fin d}
    (hR : R ∈ descendantsAtDepth Q j)
    (htwo : (plateauChildDigit Q R x i).val = 2) :
    cubeCoordUpper R i + cubeScaleFactor R ≤ cubeCoordUpper Q i := by
  rcases cubeCoordUpper_descendant_eq_or_one_scale_le hR i with hEq | hSep
  · exfalso
    by_cases hleft : x i < cubeCoordLower R i + cubeScaleFactor R / 3
    · by_cases hlower : cubeCoordLower R i = cubeCoordLower Q i
      · have hval : (plateauChildDigit Q R x i).val = 1 := by
          have hleftQ : x i < cubeCoordLower Q i + cubeScaleFactor R / 3 := by
            simpa [hlower] using hleft
          simp [plateauChildDigit, hleftQ, hlower]
        omega
      · have hval : (plateauChildDigit Q R x i).val = 0 := by
          simp [plateauChildDigit, hleft, hlower]
        omega
    · by_cases hmid : x i < cubeCoordLower R i + 2 * cubeScaleFactor R / 3
      · have hval : (plateauChildDigit Q R x i).val = 1 := by
          simp [plateauChildDigit, hleft, hmid]
        omega
      · have hval : (plateauChildDigit Q R x i).val = 1 := by
          simp [plateauChildDigit, hleft, hmid, hEq]
        omega
  · exact hSep

noncomputable def plateauChildCube {d : ℕ}
    (Q R : TriadicCube d) (x : Vec d) : TriadicCube d :=
  { scale := R.scale - 1
    index := fun i => 3 * R.index i + (plateauChildDigit Q R x i : ℤ) - 1 }

theorem plateauChildCube_mem_childCubes {d : ℕ}
    (Q R : TriadicCube d) (x : Vec d) :
    plateauChildCube Q R x ∈ childCubes R := by
  rw [mem_childCubes_iff]
  exact ⟨plateauChildDigit Q R x, rfl⟩

theorem plateauChildCube_mem_overlapCentersAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) :
    plateauChildCube Q R x ∈ overlapCentersAtDepth Q j := by
  rw [mem_overlapCentersAtDepth_iff]
  refine ⟨?_, ?_⟩
  · rw [descendantsAtDepth_succ]
    exact Finset.mem_biUnion.mpr
      ⟨R, hR, plateauChildCube_mem_childCubes Q R x⟩
  · simpa [plateauChildCube] using
      overlapCubeSet_child_subset_cubeSet_of_digit_safe
        hR (plateauChildDigit Q R x)
        (fun i hzero => plateauChildDigit_zero_safe hR hzero)
        (fun i htwo => plateauChildDigit_two_safe hR htwo)

theorem contDiff_lowerOverlapArgument {d : ℕ}
    (S : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => (x i - overlapCoordLower S i) / cubeScaleFactor S) := by
  fun_prop

theorem contDiff_upperOverlapArgument {d : ℕ}
    (S : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec d => (overlapCoordUpper S i - x i) / cubeScaleFactor S) := by
  fun_prop

noncomputable def lowerOverlapTransition {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) : ℝ :=
  if overlapCoordLower S i ≤ cubeCoordLower Q i then
    1
  else
    smoothTransitionProfile ((x i - overlapCoordLower S i) / cubeScaleFactor S)

noncomputable def upperOverlapTransition {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) : ℝ :=
  if cubeCoordUpper Q i ≤ overlapCoordUpper S i then
    1
  else
    smoothTransitionProfile ((overlapCoordUpper S i - x i) / cubeScaleFactor S)

theorem contDiff_lowerOverlapTransition {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (lowerOverlapTransition Q S i) := by
  unfold lowerOverlapTransition
  split
  · exact contDiff_const
  · exact smoothTransitionProfile.smooth.comp
      (contDiff_lowerOverlapArgument S i)

theorem contDiff_upperOverlapTransition {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (upperOverlapTransition Q S i) := by
  unfold upperOverlapTransition
  split
  · exact contDiff_const
  · exact smoothTransitionProfile.smooth.comp
      (contDiff_upperOverlapArgument S i)

theorem lowerOverlapTransition_nonneg {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    0 ≤ lowerOverlapTransition Q S i x := by
  unfold lowerOverlapTransition
  split
  · norm_num
  · exact smoothTransitionProfile.nonneg _

theorem upperOverlapTransition_nonneg {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    0 ≤ upperOverlapTransition Q S i x := by
  unfold upperOverlapTransition
  split
  · norm_num
  · exact smoothTransitionProfile.nonneg _

theorem lowerOverlapTransition_le_one {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    lowerOverlapTransition Q S i x ≤ 1 := by
  unfold lowerOverlapTransition
  split
  · norm_num
  · exact smoothTransitionProfile.le_one _

theorem upperOverlapTransition_le_one {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    upperOverlapTransition Q S i x ≤ 1 := by
  unfold upperOverlapTransition
  split
  · norm_num
  · exact smoothTransitionProfile.le_one _

theorem fderiv_lowerOverlapTransition_eq_zero_of_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hx : x i ≤ overlapCoordLower S i) :
    fderiv ℝ (lowerOverlapTransition Q S i) x = 0 := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · have hfun : lowerOverlapTransition Q S i = fun _ : Vec d => (1 : ℝ) := by
      funext y
      simp [lowerOverlapTransition, hboundary]
    rw [hfun]
    simp
  · have harg :
        (x i - overlapCoordLower S i) / cubeScaleFactor S ≤ 0 := by
      have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    have harg_diff :
        DifferentiableAt ℝ
          (fun y : Vec d => (y i - overlapCoordLower S i) / cubeScaleFactor S) x := by
      fun_prop
    have hprofile_diff :
        DifferentiableAt ℝ smoothTransitionProfile
          ((x i - overlapCoordLower S i) / cubeScaleFactor S) :=
      smoothTransitionProfile.smooth.differentiable (by simp) _
    have hprofile_zero :
        fderiv ℝ smoothTransitionProfile
          ((x i - overlapCoordLower S i) / cubeScaleFactor S) = 0 := by
      rw [← toSpanSingleton_deriv,
        smoothTransitionProfile.deriv_zero_of_nonpos harg]
      apply ContinuousLinearMap.ext
      intro r
      simp
    have hfun :
        lowerOverlapTransition Q S i =
          fun y : Vec d =>
            smoothTransitionProfile ((y i - overlapCoordLower S i) / cubeScaleFactor S) := by
      funext y
      simp [lowerOverlapTransition, hboundary]
    rw [hfun]
    rw [fderiv_fun_comp (x := x) hprofile_diff harg_diff]
    simp [hprofile_zero]

theorem fderiv_upperOverlapTransition_eq_zero_of_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hx : overlapCoordUpper S i ≤ x i) :
    fderiv ℝ (upperOverlapTransition Q S i) x = 0 := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · have hfun : upperOverlapTransition Q S i = fun _ : Vec d => (1 : ℝ) := by
      funext y
      simp [upperOverlapTransition, hboundary]
    rw [hfun]
    simp
  · have harg :
        (overlapCoordUpper S i - x i) / cubeScaleFactor S ≤ 0 := by
      have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    have harg_diff :
        DifferentiableAt ℝ
          (fun y : Vec d => (overlapCoordUpper S i - y i) / cubeScaleFactor S) x := by
      fun_prop
    have hprofile_diff :
        DifferentiableAt ℝ smoothTransitionProfile
          ((overlapCoordUpper S i - x i) / cubeScaleFactor S) :=
      smoothTransitionProfile.smooth.differentiable (by simp) _
    have hprofile_zero :
        fderiv ℝ smoothTransitionProfile
          ((overlapCoordUpper S i - x i) / cubeScaleFactor S) = 0 := by
      rw [← toSpanSingleton_deriv,
        smoothTransitionProfile.deriv_zero_of_nonpos harg]
      apply ContinuousLinearMap.ext
      intro r
      simp
    have hfun :
        upperOverlapTransition Q S i =
          fun y : Vec d =>
            smoothTransitionProfile ((overlapCoordUpper S i - y i) / cubeScaleFactor S) := by
      funext y
      simp [upperOverlapTransition, hboundary]
    rw [hfun]
    rw [fderiv_fun_comp (x := x) hprofile_diff harg_diff]
    simp [hprofile_zero]

theorem lowerOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : x i ≤ overlapCoordLower S i) :
    lowerOverlapTransition Q S i x = 0 := by
  by_cases hboundary : overlapCoordLower S i ≤ cubeCoordLower Q i
  · have hxQ_i := (mem_openCubeSet_iff_coord_bounds.mp hxQ i).1
    exfalso
    linarith
  · have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
    have harg :
        (x i - overlapCoordLower S i) / cubeScaleFactor S ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    simpa [lowerOverlapTransition, hboundary] using
      smoothTransitionProfile.zero_of_nonpos harg

theorem upperOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : overlapCoordUpper S i ≤ x i) :
    upperOverlapTransition Q S i x = 0 := by
  by_cases hboundary : cubeCoordUpper Q i ≤ overlapCoordUpper S i
  · have hxQ_i := (mem_openCubeSet_iff_coord_bounds.mp hxQ i).2
    exfalso
    linarith
  · have hscale : 0 < cubeScaleFactor S := cubeScaleFactor_pos' S
    have harg :
        (overlapCoordUpper S i - x i) / cubeScaleFactor S ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hscale.le
    simpa [upperOverlapTransition, hboundary] using
      smoothTransitionProfile.zero_of_nonpos harg

theorem overlapTransitionFactor_eq_zero_of_lower_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : x i ≤ overlapCoordLower S i) :
    lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x = 0 := by
  rw [lowerOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le hxQ hx]
  ring

theorem overlapTransitionFactor_eq_zero_of_upper_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : overlapCoordUpper S i ≤ x i) :
    lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x = 0 := by
  rw [upperOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le hxQ hx]
  ring

theorem overlapTransitionFactor_nonneg {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    0 ≤ lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x :=
  mul_nonneg
    (lowerOverlapTransition_nonneg Q S i x)
    (upperOverlapTransition_nonneg Q S i x)

theorem overlapTransitionFactor_le_one {d : ℕ}
    (Q S : TriadicCube d) (i : Fin d) (x : Vec d) :
    lowerOverlapTransition Q S i x * upperOverlapTransition Q S i x ≤ 1 :=
  mul_le_one₀
    (lowerOverlapTransition_le_one Q S i x)
    (upperOverlapTransition_nonneg Q S i x)
    (upperOverlapTransition_le_one Q S i x)

theorem fderiv_overlapTransitionFactor_eq_zero_of_lower_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : x i ≤ overlapCoordLower S i) :
    fderiv ℝ
      (fun y : Vec d =>
        lowerOverlapTransition Q S i y * upperOverlapTransition Q S i y) x = 0 := by
  have hl_diff :
      DifferentiableAt ℝ (lowerOverlapTransition Q S i) x :=
    (contDiff_lowerOverlapTransition Q S i).differentiable (by simp) x
  have hu_diff :
      DifferentiableAt ℝ (upperOverlapTransition Q S i) x :=
    (contDiff_upperOverlapTransition Q S i).differentiable (by simp) x
  rw [fderiv_fun_mul hl_diff hu_diff]
  have hl_zero :
      lowerOverlapTransition Q S i x = 0 :=
    lowerOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le hxQ hx
  have hlderiv_zero :
      fderiv ℝ (lowerOverlapTransition Q S i) x = 0 :=
    fderiv_lowerOverlapTransition_eq_zero_of_coord_le hx
  simp [hl_zero, hlderiv_zero]

theorem fderiv_overlapTransitionFactor_eq_zero_of_upper_coord_le {d : ℕ}
    {Q S : TriadicCube d} {i : Fin d} {x : Vec d}
    (hxQ : x ∈ openCubeSet Q)
    (hx : overlapCoordUpper S i ≤ x i) :
    fderiv ℝ
      (fun y : Vec d =>
        lowerOverlapTransition Q S i y * upperOverlapTransition Q S i y) x = 0 := by
  have hl_diff :
      DifferentiableAt ℝ (lowerOverlapTransition Q S i) x :=
    (contDiff_lowerOverlapTransition Q S i).differentiable (by simp) x
  have hu_diff :
      DifferentiableAt ℝ (upperOverlapTransition Q S i) x :=
    (contDiff_upperOverlapTransition Q S i).differentiable (by simp) x
  rw [fderiv_fun_mul hl_diff hu_diff]
  have hu_zero :
      upperOverlapTransition Q S i x = 0 :=
    upperOverlapTransition_eq_zero_of_mem_openCubeSet_coord_le hxQ hx
  have huderiv_zero :
      fderiv ℝ (upperOverlapTransition Q S i) x = 0 :=
    fderiv_upperOverlapTransition_eq_zero_of_coord_le hx
  simp [hu_zero, huderiv_zero]


end

end Homogenization
