/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.TerminalBounds

/-! # Force Localization -/

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSLocalCoeff_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) {s : ℝ} (hs : 0 < s) :
    0 ≤ coarsePoincareRHSLocalCoeff Q a s := by
  unfold coarsePoincareRHSLocalCoeff
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hlambda_nonneg : 0 ≤ lambdaSq Q s (.finite 2) a := by
    exact multiscale_ellipticity_lambdaSq_finite_nonneg Q s 2 a
      (by norm_num) hs2.le
  exact mul_nonneg
    (inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2)))
    (inv_nonneg.mpr hlambda_nonneg)

theorem coarsePoincareRHSLocalCenteredForceSeminorm_eq_uncentered_of_mem
    {d : ℕ} {Q R : TriadicCube d} (g : Vec d → Vec d) (s : ℝ) {n : ℕ}
    (hR : R ∈ descendantsAtDepth Q n)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S)) :
    coarsePoincareRHSLocalCenteredForceSeminorm R g s =
      cubeBesovPositiveVectorSeminormTwo R s g := by
  unfold coarsePoincareRHSLocalCenteredForceSeminorm
  exact
    cubeBesovPositiveVectorSeminormTwo_sub_const R s g
      (cubeAverageVec R g)
      (fun j S hS => hmem (n + j) S (mem_descendantsAtDepth_add hR hS))

theorem descendantsAverage_sq_coarsePoincareRHSLocalCenteredForceSeminorm_eq_of_mem
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hmem :
      ∀ j : ℕ, ∀ S ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure S)) :
    descendantsAverage Q n
        (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) =
      descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
  unfold descendantsAverage
  apply congrArg (fun t : ℝ => ((descendantsAtDepth Q n).card : ℝ)⁻¹ * t)
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [coarsePoincareRHSLocalCenteredForceSeminorm_eq_uncentered_of_mem
    (Q := Q) (R := R) g s hR hmem]

theorem cubeBesovPositiveVectorPartialSeminormTwo_bddAbove_of_parent_bddAbove
    {d : ℕ} {Q R : TriadicCube d} {n : ℕ} (s : ℝ) (u : Vec d → Vec d)
    (hR : R ∈ descendantsAtDepth Q n)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u)) :
    BddAbove (Set.range fun N : ℕ =>
      cubeBesovPositiveVectorPartialSeminormTwo R s N u) := by
  classical
  rcases hGlobalBdd with ⟨B, hB⟩
  have hB_nonneg : 0 ≤ B := by
    have hB0 : cubeBesovPositiveVectorPartialSeminormTwo Q s 0 u ≤ B :=
      hB ⟨0, rfl⟩
    exact (cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s 0 u).trans hB0
  let D : Finset (TriadicCube d) := descendantsAtDepth Q n
  let c : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  have hD_nonempty : D.Nonempty := by
    simpa [D] using descendantsAtDepth_nonempty Q n
  have hcard_pos_nat : 0 < D.card := Finset.card_pos.mpr hD_nonempty
  have hcard_pos : 0 < (D.card : ℝ) := by
    exact_mod_cast hcard_pos_nat
  have hcard_nonneg : 0 ≤ (D.card : ℝ) := le_of_lt hcard_pos
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  refine ⟨c⁻¹ * Real.sqrt ((D.card : ℝ) * B ^ 2), ?_⟩
  rintro x ⟨N, rfl⟩
  have hparent_le :
      cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) u ≤ B :=
    hB ⟨n + N, rfl⟩
  have hparent_nonneg :
      0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) u :=
    cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s (n + N) u
  have hparent_sq_le :
      (cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) u) ^ 2 ≤ B ^ 2 := by
    nlinarith
  let F : TriadicCube d → ℝ := fun S =>
    (c * cubeBesovPositiveVectorPartialSeminormTwo S s N u) ^ 2
  have havg_le_parent :
      descendantsAverage Q n F ≤
        (cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) u) ^ 2 := by
    dsimp [F, c]
    exact descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_le
      Q s u n N
  have havg_le_Bsq : descendantsAverage Q n F ≤ B ^ 2 :=
    havg_le_parent.trans hparent_sq_le
  have hsum_le : (∑ S ∈ D, F S) ≤ (D.card : ℝ) * B ^ 2 := by
    have hmul :
        (D.card : ℝ) * descendantsAverage Q n F ≤ (D.card : ℝ) * B ^ 2 :=
      mul_le_mul_of_nonneg_left havg_le_Bsq hcard_nonneg
    have hdesc : (D.card : ℝ) * descendantsAverage Q n F = ∑ S ∈ D, F S := by
      dsimp [descendantsAverage, D]
      field_simp [ne_of_gt hcard_pos]
    rwa [hdesc] at hmul
  have hterm_le_sum : F R ≤ ∑ S ∈ D, F S := by
    exact Finset.single_le_sum
      (fun S hS => sq_nonneg (c * cubeBesovPositiveVectorPartialSeminormTwo S s N u))
      (by simpa [D] using hR)
  have hterm_sq_le :
      (c * cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2 ≤
        (D.card : ℝ) * B ^ 2 :=
    hterm_le_sum.trans hsum_le
  have hscaled_le :
      c * cubeBesovPositiveVectorPartialSeminormTwo R s N u ≤
        Real.sqrt ((D.card : ℝ) * B ^ 2) :=
    Real.le_sqrt_of_sq_le hterm_sq_le
  exact (le_inv_mul_iff₀ hc_pos).mpr hscaled_le

theorem tendsto_cubeBesovPositiveVectorPartialSeminormTwo_atTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u)) :
    Filter.Tendsto
      (fun N : ℕ => cubeBesovPositiveVectorPartialSeminormTwo Q s N u)
      Filter.atTop
      (nhds (cubeBesovPositiveVectorSeminormTwo Q s u)) := by
  unfold cubeBesovPositiveVectorSeminormTwo
  exact
    tendsto_atTop_ciSup
      (monotone_nat_of_le_succ
        (fun N => cubeBesovPositiveVectorPartialSeminormTwo_le_succ Q s u N))
      hBdd

theorem tendsto_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_atTop
    {d : ℕ} (Q : TriadicCube d) (s c : ℝ) (u : Vec d → Vec d)
    (hBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N u)) :
    Filter.Tendsto
      (fun N : ℕ => (c * cubeBesovPositiveVectorPartialSeminormTwo Q s N u) ^ 2)
      Filter.atTop
      (nhds ((c * cubeBesovPositiveVectorSeminormTwo Q s u) ^ 2)) := by
  exact
    ((Filter.Tendsto.const_mul c
      (tendsto_cubeBesovPositiveVectorPartialSeminormTwo_atTop Q s u hBdd)).pow 2)

theorem tendsto_descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_atTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → Vec d) (n : ℕ)
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N u)) :
    Filter.Tendsto
      (fun N : ℕ =>
        descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorPartialSeminormTwo R s N u) ^ 2))
      Filter.atTop
      (nhds
        (descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s u) ^ 2))) := by
  unfold descendantsAverage
  exact
    Filter.Tendsto.const_mul ((descendantsAtDepth Q n).card : ℝ)⁻¹
      (tendsto_finsetSum (descendantsAtDepth Q n)
        (fun R hR =>
          tendsto_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_atTop
            R s (Real.rpow (3 : ℝ) (s * (n : ℝ))) u (hLocalBdd R hR)))

theorem descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    descendantsAverage Q n
        (fun R =>
          (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
            cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hglobal_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have hbound :
      ∀ N : ℕ,
        descendantsAverage Q n
            (fun R =>
              (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
                cubeBesovPositiveVectorPartialSeminormTwo R s N g) ^ 2) ≤
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    intro N
    have hpartial :=
      descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_le
        Q s g n N
    have hpartial_le_full :
        cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) g ≤
          cubeBesovPositiveVectorSeminormTwo Q s g :=
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s g hGlobalBdd (n + N)
    have hpartial_nonneg :
        0 ≤ cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) g :=
      cubeBesovPositiveVectorPartialSeminormTwo_nonneg Q s (n + N) g
    have hpartial_sq :
        (cubeBesovPositiveVectorPartialSeminormTwo Q s (n + N) g) ^ 2 ≤
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
      nlinarith
    exact hpartial.trans hpartial_sq
  have hlim :=
    tendsto_descendantsAverage_sq_scaled_cubeBesovPositiveVectorPartialSeminormTwo_atTop
      Q s g n hLocalBdd
  exact le_of_tendsto' hlim hbound

/--
Unscaled parent-seminorm corollary of
`descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le`.
-/
theorem descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_parent_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) {s : ℝ} (n : ℕ)
    (hs : 0 ≤ s)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let c : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  have hscaled :=
    descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le
      Q g s n hGlobalBdd hLocalBdd
  have hscaled_eq :
      descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) =
        c ^ 2 *
          descendantsAverage Q n
            (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
    dsimp [c]
    calc
      descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)
          =
            descendantsAverage Q n
              (fun R =>
                (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
                  (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
              apply congrArg (descendantsAverage Q n)
              funext R
              ring
      _ =
          (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
            descendantsAverage Q n
              (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
          exact descendantsAverage_mul_left Q n
            ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2)
            (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)
  have hc_one : 1 ≤ c := by
    dsimp [c]
    simpa using
      (Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3)
        (mul_nonneg hs (by exact_mod_cast Nat.zero_le n)))
  have hc_sq_one : 1 ≤ c ^ 2 := by
    nlinarith [sq_nonneg c]
  have havg_nonneg :
      0 ≤ descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
    descendantsAverage_nonneg Q n _
      (fun R hR => sq_nonneg (cubeBesovPositiveVectorSeminormTwo R s g))
  have havg_le_scaled :
      descendantsAverage Q n
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        c ^ 2 *
          descendantsAverage Q n
            (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
    nlinarith
  calc
    descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)
        ≤
      c ^ 2 *
        descendantsAverage Q n
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
        havg_le_scaled
    _ =
      descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) :=
        hscaled_eq.symm
    _ ≤ (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := hscaled

theorem descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    descendantsAverage Q n
        (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
      coarsePoincareRHSGlobalForceBound Q g s n := by
  let c : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hc_sq_pos : 0 < c ^ 2 := sq_pos_of_pos hc_pos
  have hscaled :=
    descendantsAverage_sq_scaled_cubeBesovPositiveVectorSeminormTwo_le
      Q g s n hGlobalBdd hLocalBdd
  have hscaled_eq :
      descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) =
        c ^ 2 *
          descendantsAverage Q n
            (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
    dsimp [c]
    calc
      descendantsAverage Q n
          (fun R =>
            (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
              cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)
          =
            descendantsAverage Q n
              (fun R =>
                (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
                  (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
                refine congrArg (descendantsAverage Q n) ?_
                funext R
                ring
      _ =
            (Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2 *
              descendantsAverage Q n
                (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) := by
            rw [descendantsAverage_mul_left Q n
              ((Real.rpow (3 : ℝ) (s * (n : ℝ))) ^ 2)
              (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)]
  have hmul :
      c ^ 2 *
          descendantsAverage Q n
            (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
    rw [hscaled_eq] at hscaled
    exact hscaled
  exact (le_inv_mul_iff₀ hc_sq_pos).mpr hmul

/--
Localized descendant `L²` average of the positive forcing seminorm at a fixed
depth.  This is the quantity whose parent-cube control carries the small
factor `3^{-s n}`.
-/
noncomputable def localizedPositiveBesovForcingSeminormTwoAtDepth {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (n : ℕ) (g : Vec d → Vec d) : ℝ :=
  Real.sqrt
    (descendantsAverage Q n fun R =>
      (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2)

/--
The square root of the global force bound is the inverse depth weight times the
parent positive-Besov seminorm.
-/
theorem sqrt_coarsePoincareRHSGlobalForceBound_eq_depthWeight_inv_mul_parent_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    Real.sqrt (coarsePoincareRHSGlobalForceBound Q g s n) =
      (Real.rpow (3 : ℝ) (s * (n : ℝ)))⁻¹ *
        cubeBesovPositiveVectorSeminormTwo Q s g := by
  let c : ℝ := Real.rpow (3 : ℝ) (s * (n : ℝ))
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  have hc_pos : 0 < c := by
    dsimp [c]
    exact Real.rpow_pos_of_pos (by norm_num : 0 < (3 : ℝ)) _
  have hc_nonneg : 0 ≤ c := hc_pos.le
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have hprod_nonneg : 0 ≤ c⁻¹ * B :=
    mul_nonneg (inv_nonneg.mpr hc_nonneg) hB_nonneg
  have hinside :
      coarsePoincareRHSGlobalForceBound Q g s n = (c⁻¹ * B) ^ 2 := by
    unfold coarsePoincareRHSGlobalForceBound
    dsimp [c, B]
    ring
  rw [hinside, Real.sqrt_sq hprod_nonneg]

/--
Scale-sharp localization of the positive forcing seminorm: averaging the
descendant forcing seminorms costs the inverse positive depth weight, not the
positive depth weight.
-/
theorem localizedPositiveBesovForcingSeminormTwoAtDepth_le_depthWeight_inv_mul_parent_of_bddAbove
    {d : ℕ} (Q : TriadicCube d) (g : Vec d → Vec d) (s : ℝ) (n : ℕ)
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hLocalBdd :
      ∀ R ∈ descendantsAtDepth Q n,
        BddAbove (Set.range fun N : ℕ =>
          cubeBesovPositiveVectorPartialSeminormTwo R s N g)) :
    localizedPositiveBesovForcingSeminormTwoAtDepth Q s n g ≤
      (Real.rpow (3 : ℝ) (s * (n : ℝ)))⁻¹ *
        cubeBesovPositiveVectorSeminormTwo Q s g := by
  have hscaled :
      descendantsAverage Q n
          (fun R => (cubeBesovPositiveVectorSeminormTwo R s g) ^ 2) ≤
        coarsePoincareRHSGlobalForceBound Q g s n :=
    descendantsAverage_sq_cubeBesovPositiveVectorSeminormTwo_le_global_scaled
      Q g s n hGlobalBdd hLocalBdd
  calc
    localizedPositiveBesovForcingSeminormTwoAtDepth Q s n g
        ≤ Real.sqrt (coarsePoincareRHSGlobalForceBound Q g s n) := by
          exact Real.sqrt_le_sqrt hscaled
    _ =
      (Real.rpow (3 : ℝ) (s * (n : ℝ)))⁻¹ *
        cubeBesovPositiveVectorSeminormTwo Q s g :=
          sqrt_coarsePoincareRHSGlobalForceBound_eq_depthWeight_inv_mul_parent_of_bddAbove
            Q g s n hGlobalBdd

theorem coarsePoincareRHSIntrinsicLocalForceError_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d) (s : ℝ) :
    0 ≤ coarsePoincareRHSIntrinsicLocalForceError Q a g s := by
  unfold coarsePoincareRHSIntrinsicLocalForceError
  exact sq_nonneg _

theorem coarsePoincareRHSIntrinsicForceErrorAverage_nonneg {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) (n : ℕ) :
    0 ≤ coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n := by
  unfold coarsePoincareRHSIntrinsicForceErrorAverage
  exact descendantsAverage_nonneg Q n _
    fun R hR => coarsePoincareRHSIntrinsicLocalForceError_nonneg R a g s

theorem coarsePoincareRHSIntrinsicEnergyErrorAverage_le_of_localCoeffBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) (n : ℕ) {C : ℝ}
    (hcoeff :
      ∀ R ∈ descendantsAtDepth Q n,
        coarsePoincareRHSLocalCoeff R a s ≤ C)
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u)) :
    coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n ≤
      2 * C *
        descendantsAverage Q n (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
  unfold coarsePoincareRHSIntrinsicEnergyErrorAverage
  calc
    descendantsAverage Q n (fun R => coarsePoincareRHSIntrinsicLocalEnergyError R a u s)
        ≤
          descendantsAverage Q n
            (fun R => 2 * C * cubeAverage R (coefficientEnergyDensity a u)) := by
              refine descendantsAverage_le_descendantsAverage Q n ?_
              intro R hR
              unfold coarsePoincareRHSIntrinsicLocalEnergyError
              calc
                2 * coarsePoincareRHSLocalCoeff R a s *
                    cubeAverage R (coefficientEnergyDensity a u)
                    ≤ 2 * (C * cubeAverage R (coefficientEnergyDensity a u)) := by
                      simpa [mul_assoc] using mul_le_mul_of_nonneg_left
                        (mul_le_mul_of_nonneg_right (hcoeff R hR) (havg_nonneg R hR))
                        (show 0 ≤ (2 : ℝ) by norm_num)
                _ = 2 * C * cubeAverage R (coefficientEnergyDensity a u) := by
                      ring
    _ =
          2 * C *
            descendantsAverage Q n (fun R => cubeAverage R (coefficientEnergyDensity a u)) := by
              rw [descendantsAverage_smul Q n (2 * C)
                (fun R => cubeAverage R (coefficientEnergyDensity a u))]

theorem coarsePoincareRHSIntrinsicEnergyErrorAverage_le_globalAverage_of_localCoeffBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (u : Vec d → Vec d)
    (s : ℝ) (n : ℕ) {C : ℝ}
    (hcoeff :
      ∀ R ∈ descendantsAtDepth Q n,
        coarsePoincareRHSLocalCoeff R a s ≤ C)
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume) :
    coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n ≤
      2 * C * cubeAverage Q (coefficientEnergyDensity a u) := by
  have hbase :=
    coarsePoincareRHSIntrinsicEnergyErrorAverage_le_of_localCoeffBound
      Q a u s n hcoeff havg_nonneg
  have hpartition :
      cubeAverage Q (coefficientEnergyDensity a u) =
        descendantsAverage Q n
          (fun R => cubeAverage R (coefficientEnergyDensity a u)) :=
    cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q n
      (coefficientEnergyDensity a u) hint
  simpa [hpartition] using hbase

theorem coarsePoincareRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s lam Lam : ℝ} (n : ℕ) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q n)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1)) :
    coarsePoincareRHSLocalCoeff R a s ≤
      (geometricDiscount s 2)⁻¹ *
        (Real.rpow (3 : ℝ) (s * (n : ℝ)) *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) := by
  have hs2 : 0 < s * (2 : ℝ) := by nlinarith
  have hdisc_nonneg : 0 ≤ (geometricDiscount s 2)⁻¹ :=
    inv_nonneg.mpr (le_of_lt (geometricDiscount_pos hs2))
  have hRscale : R ∈ descendantsAtScale Q (Q.scale - (n : ℤ)) :=
    mem_descendantsAtScale_of_mem_descendantsAtDepth hR
  have hlambda :=
    multiscale_ellipticity_lambdaSq_two_inv_le_rpow_s_of_mem_descendantsAtScale_of_half_of_isEllipticFieldOn_of_isSigmaCoarse
      (Q := Q) (R := R) (k := Q.scale - (n : ℤ)) a hs hRscale hEll hData hsum_half
  have htoNat :
      Int.toNat (Q.scale - (Q.scale - (n : ℤ))) = n := by
    have hdiff : Q.scale - (Q.scale - (n : ℤ)) = (n : ℤ) := by
      omega
    rw [hdiff]
    simp
  unfold coarsePoincareRHSLocalCoeff
  refine mul_le_mul_of_nonneg_left ?_ hdisc_nonneg
  simpa [htoNat] using hlambda

theorem coarsePoincareRHSIntrinsicEnergyErrorAverage_le_parentHalfCoeff_globalAverage
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (u : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ) (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (havg_nonneg :
      ∀ R ∈ descendantsAtDepth Q n,
        0 ≤ cubeAverage R (coefficientEnergyDensity a u))
    (hint :
      MeasureTheory.IntegrableOn (coefficientEnergyDensity a u) (cubeSet Q)
        MeasureTheory.volume) :
    coarsePoincareRHSIntrinsicEnergyErrorAverage Q a u s n ≤
      2 * coarsePoincareRHSParentHalfCoeff Q a s n *
        cubeAverage Q (coefficientEnergyDensity a u) := by
  simpa [coarsePoincareRHSParentHalfCoeff, mul_assoc] using
    coarsePoincareRHSIntrinsicEnergyErrorAverage_le_globalAverage_of_localCoeffBound
      Q a u s n
      (fun R hR =>
        coarsePoincareRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
          (Q := Q) (R := R) a n hs hR hEll hData hsum_half)
      havg_nonneg hint

theorem coarsePoincareRHSIntrinsicForceErrorAverage_le_of_multiplierSqBound {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) (n : ℕ) {K2 : ℝ}
    (hmult :
      ∀ R ∈ descendantsAtDepth Q n,
        (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s) ^ 2 ≤ K2) :
    coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n ≤
      K2 *
        descendantsAverage Q n
          (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
  unfold coarsePoincareRHSIntrinsicForceErrorAverage
  calc
    descendantsAverage Q n (fun R => coarsePoincareRHSIntrinsicLocalForceError R a g s)
        ≤
          descendantsAverage Q n
            (fun R => K2 * (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
              refine descendantsAverage_le_descendantsAverage Q n ?_
              intro R hR
              unfold coarsePoincareRHSIntrinsicLocalForceError
              calc
                (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s *
                    coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2
                    =
                      (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s) ^ 2 *
                        (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2 := by
                          ring
                _ ≤
                      K2 * (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2 := by
                        exact mul_le_mul_of_nonneg_right (hmult R hR) (sq_nonneg _)
    _ =
          K2 *
            descendantsAverage Q n
              (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
              rw [descendantsAverage_smul Q n K2
                (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2)]

theorem coarsePoincareRHSIntrinsicLocalForceMultiplier_sq_le_of_localCoeffBound {d : ℕ}
    (R : TriadicCube d) (a : CoeffField d) {s C : ℝ}
    (hs : 0 < s)
    (hcoeff : coarsePoincareRHSLocalCoeff R a s ≤ C) :
    (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s) ^ 2 ≤
      (C * ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))) ^ 2 := by
  let P : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact mul_nonneg
      (by exact_mod_cast Nat.zero_le d)
      (mul_nonneg
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
        (Real.sqrt_nonneg 2))
  have hlocal_nonneg :
      0 ≤ coarsePoincareRHSIntrinsicLocalForceMultiplier R a s := by
    unfold coarsePoincareRHSIntrinsicLocalForceMultiplier
    exact mul_nonneg (coarsePoincareRHSLocalCoeff_nonneg R a hs) hP_nonneg
  have hle :
      coarsePoincareRHSIntrinsicLocalForceMultiplier R a s ≤ C * P := by
    unfold coarsePoincareRHSIntrinsicLocalForceMultiplier
    exact mul_le_mul_of_nonneg_right hcoeff hP_nonneg
  simpa [P] using pow_le_pow_left₀ hlocal_nonneg hle 2

theorem coarsePoincareRHSIntrinsicLocalForceMultiplier_sq_le_parentHalfLambda_of_mem_descendantsAtDepth
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} (a : CoeffField d)
    {s lam Lam : ℝ} (n : ℕ) (hs : 0 < s)
    (hR : R ∈ descendantsAtDepth Q n)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1)) :
    (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s) ^ 2 ≤
      (coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 := by
  simpa [coarsePoincareRHSParentHalfCoeff,
    coarsePoincareRHSIntrinsicParentHalfForceMultiplier] using
    coarsePoincareRHSIntrinsicLocalForceMultiplier_sq_le_of_localCoeffBound
      R a hs
      (coarsePoincareRHSLocalCoeff_le_parentHalfLambda_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a n hs hR hEll hData hsum_half)

theorem coarsePoincareRHSIntrinsicForceErrorAverage_le_of_multiplierSqBound_of_centeredForceAverageBound
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    (s : ℝ) (n : ℕ) {K2 B : ℝ}
    (hK2 : 0 ≤ K2)
    (hmult :
      ∀ R ∈ descendantsAtDepth Q n,
        (coarsePoincareRHSIntrinsicLocalForceMultiplier R a s) ^ 2 ≤ K2)
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B) :
    coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n ≤ K2 * B := by
  calc
    coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n
        ≤
          K2 *
            descendantsAverage Q n
              (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) := by
              exact
                coarsePoincareRHSIntrinsicForceErrorAverage_le_of_multiplierSqBound
                  Q a g s n hmult
    _ ≤ K2 * B := by
          exact mul_le_mul_of_nonneg_left hforceAvg hK2

theorem coarsePoincareRHSIntrinsicForceErrorAverage_le_parentHalfLambda_of_centeredForceAverageBound
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (g : Vec d → Vec d) {s lam Lam : ℝ} (n : ℕ) {B : ℝ}
    (hs : 0 < s)
    (hEll : IsEllipticFieldOn lam Lam (openCubeSet Q) a)
    (hData :
      ∀ j ≤ Q.scale, ∀ S ∈ descendantsAtScale Q j,
        ∃ sigmaS sigmaStarS kappaS,
          IsCoarseBlockMatrix (openCubeSet S) a
            (deterministicCoarseBlockMatrix (openCubeSet S) a) ∧
          IsSigmaStarCoarse (openCubeSet S) a sigmaStarS ∧
          IsKappaCoarse (openCubeSet S) a sigmaStarS kappaS ∧
          IsSigmaCoarse (openCubeSet S) a sigmaS sigmaStarS kappaS ∧
          IsUnit sigmaStarS.det)
    (hsum_half :
      Summable (fun m : ℕ =>
        geometricWeight (s / 2) 2 m *
          Real.rpow (maxDescendantSigmaStarInvNormAtScale Q (Q.scale - (m : ℤ)) a) 1))
    (hforceAvg :
      descendantsAverage Q n
        (fun R => (coarsePoincareRHSLocalCenteredForceSeminorm R g s) ^ 2) ≤ B) :
    coarsePoincareRHSIntrinsicForceErrorAverage Q a g s n ≤
      (coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2 * B := by
  refine
    coarsePoincareRHSIntrinsicForceErrorAverage_le_of_multiplierSqBound_of_centeredForceAverageBound
      Q a g s n (K2 :=
        (coarsePoincareRHSIntrinsicParentHalfForceMultiplier Q a s n) ^ 2)
      (B := B) ?_ ?_ hforceAvg
  · exact sq_nonneg _
  · intro R hR
    exact
      coarsePoincareRHSIntrinsicLocalForceMultiplier_sq_le_parentHalfLambda_of_mem_descendantsAtDepth
        (Q := Q) (R := R) a n hs hR hEll hData hsum_half

end

end Homogenization
