/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Besov.Poincare.Structures

/-! # Projection -/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

theorem geom_sum_range_le_of_lt_one {x : ℝ} {n : ℕ} (hx : 0 ≤ x) (hx1 : x < 1) :
    Finset.sum (Finset.range n) (fun i => x ^ i) ≤ (1 - x)⁻¹ := by
  rw [Finset.range_eq_Ico]
  simpa using
    (geom_sum_Ico_le_of_lt_one (x := x) (m := 0) (n := n) hx hx1)

theorem sum_mul_le_mul_sum_of_nonneg {ι : Type*} {s : Finset ι} {f g : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) (hg : ∀ i ∈ s, 0 ≤ g i) :
    Finset.sum s (fun i => f i * g i) ≤ (Finset.sum s f) * Finset.sum s g := by
  have hpoint : ∀ i ∈ s, f i * g i ≤ f i * Finset.sum s g := by
    intro i hi
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum hg hi) (hf i hi)
  have hsum : Finset.sum s (fun i => f i * g i) ≤ Finset.sum s (fun i => f i * Finset.sum s g) :=
    Finset.sum_le_sum hpoint
  simpa [Finset.sum_mul] using hsum

theorem descendantsAverage_add_eq_descendantsAverage_descendantsAverage {d : ℕ}
    (Q : TriadicCube d) (j n : ℕ) (F : TriadicCube d → ℝ) :
    descendantsAverage Q (j + n) F =
      descendantsAverage Q j (fun R => descendantsAverage R n F) := by
  induction n generalizing Q F with
  | zero =>
      simp [descendantsAverage]
  | succ n ih =>
      calc
        descendantsAverage Q (j + (n + 1)) F
            = descendantsAverage Q (j + n) (fun R => descendantsAverage R 1 F) := by
                simpa [Nat.add_assoc] using
                  descendantsAverage_succ_eq_descendantsAverage_descendantsAverage
                    Q (j + n) F
        _ = descendantsAverage Q j
              (fun R => descendantsAverage R n (fun S => descendantsAverage S 1 F)) := by
              simpa using ih Q (fun S => descendantsAverage S 1 F)
        _ = descendantsAverage Q j (fun R => descendantsAverage R (n + 1) F) := by
              refine congrArg (descendantsAverage Q j) ?_
              funext R
              symm
              exact descendantsAverage_succ_eq_descendantsAverage_descendantsAverage R n F

theorem mem_descendantsAtDepth_add {d : ℕ} {Q R S : TriadicCube d} {j n : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (hS : S ∈ descendantsAtDepth R n) :
    S ∈ descendantsAtDepth Q (j + n) := by
  induction n generalizing Q R S j with
  | zero =>
      have hSR : S = R := by simpa using hS
      subst hSR
      simpa
  | succ n ih =>
      rcases mem_descendantsAtDepth_succ_iff.mp hS with ⟨T, hT, hST⟩
      have hTQ : T ∈ descendantsAtDepth Q (j + n) := ih hR hT
      have hSQ : S ∈ descendantsAtDepth Q ((j + n) + 1) := by
        exact mem_descendantsAtDepth_succ_iff.mpr ⟨T, hTQ, hST⟩
      simpa [Nat.add_assoc] using hSQ

theorem cubeProjection_add_eq_cubeProjection_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j n : ℕ} (f : Vec d → ℝ) {x : Vec d}
    (hR : R ∈ descendantsAtDepth Q j) (hx : x ∈ cubeSet R) :
    cubeProjection Q (j + n) f x = cubeProjection R n f x := by
  rcases exists_mem_descendantsAtDepth_of_mem_cubeSet (Q := R) (n := n) hx with
    ⟨S, hS, hxS⟩
  have hSQ : S ∈ descendantsAtDepth Q (j + n) := mem_descendantsAtDepth_add hR hS
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := S) (j := j + n) f hSQ hxS]
  rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := R) (R := S) (j := n) f hS hxS]

theorem cubeAverage_cubeProjection_eq_cubeAverage_of_memLp {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage Q (cubeProjection Q j u) = cubeAverage Q u := by
  have hprojInt :
      MeasureTheory.IntegrableOn (cubeProjection Q j u) (cubeSet Q) MeasureTheory.volume :=
    integrableOn_cubeProjection_of_integrableOn Q j u
  have huInt :
      MeasureTheory.IntegrableOn u (cubeSet Q) MeasureTheory.volume :=
    integrableOn_of_integrable_normalizedCubeMeasure (Q := Q) (hu.integrable (by norm_num))
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := cubeProjection Q j u) hprojInt]
  rw [cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn
    (Q := Q) (j := j) (f := u) huInt]
  unfold descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  rw [cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
    (Q := Q) (R := R) (j := j) (g := u) hR]

theorem cubeAverage_cubeProjection_add_eq_cubeAverage_of_mem_descendantsAtDepth_of_memLp
    {d : ℕ} {Q R : TriadicCube d} {j n : ℕ} (u : Vec d → ℝ)
    (hR : R ∈ descendantsAtDepth Q j)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeAverage R (cubeProjection Q (j + n) u) = cubeAverage R u := by
  have hcongr :
      cubeAverage R (cubeProjection Q (j + n) u) =
        cubeAverage R (cubeProjection R n u) := by
    apply cubeAverage_congr_on_cubeSet
    intro x hx
    exact cubeProjection_add_eq_cubeProjection_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (n := n) (f := u) hR hx
  rw [hcongr]
  have huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hu
  exact cubeAverage_cubeProjection_eq_cubeAverage_of_memLp R n u huR

theorem cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth {d : ℕ} {Q R : TriadicCube d}
    {j : ℕ} (hR : R ∈ descendantsAtDepth Q j) :
    cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j := by
  rw [cubeScaleFactor, scale_eq_sub_of_mem_descendantsAtDepth hR, zpow_sub₀]
  · simp [cubeScaleFactor, div_eq_mul_inv]
  · norm_num

/-- Besov scale weights on a depth-`j` descendant differ from the parent
weight by the triadic factor `3^(s j)`. -/
theorem cubeBesovScaleWeight_eq_mul_rpow_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (s : ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovScaleWeight s R =
      cubeBesovScaleWeight s Q * Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
  have hQR : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_eq_div_pow_of_mem_descendantsAtDepth hR
  have hQpos : 0 < cubeScaleFactor Q := by
    simpa [cubeScaleFactor] using
      (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale)
  have hpow_pos : 0 < (3 : ℝ) ^ j := by positivity
  unfold cubeBesovScaleWeight
  rw [hQR]
  calc
    (cubeScaleFactor Q / (3 : ℝ) ^ j) ^ (-s)
        = (cubeScaleFactor Q) ^ (-s) / (((3 : ℝ) ^ j) ^ (-s)) := by
            rw [Real.div_rpow hQpos.le hpow_pos.le]
    _ = (cubeScaleFactor Q) ^ (-s) /
          Real.rpow (3 : ℝ) ((-s) * (j : ℝ)) := by
            have hpow :
                (((3 : ℝ) ^ j : ℝ) ^ (-s)) =
                  Real.rpow (3 : ℝ) ((-s) * (j : ℝ)) := by
              simpa [mul_comm] using
                (Real.rpow_natCast_mul (by positivity : 0 ≤ (3 : ℝ)) j (-s)).symm
            rw [hpow]
    _ = (cubeScaleFactor Q) ^ (-s) *
          Real.rpow (3 : ℝ) (s * (j : ℝ)) := by
            have hneg : (-s) * (j : ℝ) = -(s * (j : ℝ)) := by ring
            have hrpow_neg :
                Real.rpow (3 : ℝ) (-(s * (j : ℝ))) =
                  (Real.rpow (3 : ℝ) (s * (j : ℝ)))⁻¹ := by
              simpa using
                (Real.rpow_neg (x := (3 : ℝ))
                  (by norm_num : 0 ≤ (3 : ℝ)) (s * (j : ℝ)))
            rw [div_eq_mul_inv, hneg, hrpow_neg, inv_inv]

/-- Parent-weight form of the descendant Besov-weight identity.  For a
depth-`j` descendant, the parent scale weight times the triadic depth factor is
the descendant scale weight. -/
theorem cubeBesovScaleWeight_neg_parent_mul_rpow_eq_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (r : ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovScaleWeight (-r) Q * Real.rpow (3 : ℝ) (-r * (j : ℝ)) =
      cubeBesovScaleWeight (-r) R := by
  simpa [mul_comm] using
    (cubeBesovScaleWeight_eq_mul_rpow_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (-r) hR).symm

/-- Cancellation form of the descendant Besov-weight identity used in the
small-cube Caccioppoli summation. -/
theorem cubeBesovScaleWeight_neg_mul_rpow_eq_of_mem_descendantsAtDepth {d : ℕ}
    {Q R : TriadicCube d} {j : ℕ} (r : ℝ)
    (hR : R ∈ descendantsAtDepth Q j) :
    cubeBesovScaleWeight (-r) R * Real.rpow (3 : ℝ) (r * (j : ℝ)) =
      cubeBesovScaleWeight (-r) Q := by
  have hscale :=
    cubeBesovScaleWeight_eq_mul_rpow_of_mem_descendantsAtDepth
      (Q := Q) (R := R) (j := j) (-r) hR
  rw [hscale]
  have hsum : (-r) * (j : ℝ) + r * (j : ℝ) = 0 := by ring
  calc
    (cubeBesovScaleWeight (-r) Q *
          Real.rpow (3 : ℝ) ((-r) * (j : ℝ))) *
        Real.rpow (3 : ℝ) (r * (j : ℝ))
        =
      cubeBesovScaleWeight (-r) Q *
        (Real.rpow (3 : ℝ) ((-r) * (j : ℝ)) *
          Real.rpow (3 : ℝ) (r * (j : ℝ))) := by
          ring
    _ =
      cubeBesovScaleWeight (-r) Q *
        Real.rpow (3 : ℝ) (((-r) * (j : ℝ)) + r * (j : ℝ)) := by
          have hadd :
              Real.rpow (3 : ℝ) (((-r) * (j : ℝ)) + r * (j : ℝ)) =
                Real.rpow (3 : ℝ) ((-r) * (j : ℝ)) *
                  Real.rpow (3 : ℝ) (r * (j : ℝ)) := by
            simpa using
              (Real.rpow_add (by norm_num : 0 < (3 : ℝ))
                ((-r) * (j : ℝ)) (r * (j : ℝ)))
          rw [hadd]
    _ = cubeBesovScaleWeight (-r) Q := by
          rw [hsum]
          simp

theorem cubeBesovCircDepthAverage_add_eq_descendantsAverage_cubeBesovCircDepthAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (j n : ℕ) :
    cubeBesovCircDepthAverage Q p u (j + n) =
      descendantsAverage Q j (fun R => cubeBesovCircDepthAverage R p u n) := by
  unfold cubeBesovCircDepthAverage
  simpa using descendantsAverage_add_eq_descendantsAverage_descendantsAverage
    (Q := Q) (j := j) (n := n) (F := fun R => ‖cubeAverage R u‖ ^ p.toReal)

theorem cubeBesovCircDepthAverage_projection_eventually_constant {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N r : ℕ) :
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1 + r) =
      cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1) := by
  calc
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1 + r)
        = descendantsAverage Q (N + 1)
            (fun R => cubeBesovCircDepthAverage R (2 : ℝ≥0∞)
              (cubeProjection Q (N + 1) u) r) := by
              rw [cubeBesovCircDepthAverage_add_eq_descendantsAverage_cubeBesovCircDepthAverage]
    _ = descendantsAverage Q (N + 1)
          (fun R => ‖cubeAverage R u‖ ^ ((2 : ℝ≥0∞).toReal)) := by
          unfold descendantsAverage
          refine congrArg (fun t : ℝ => ((descendantsAtDepth Q (N + 1)).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          have havg :
              cubeBesovCircDepthAverage R (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) r =
                ‖cubeAverage R u‖ ^ ((2 : ℝ≥0∞).toReal) := by
            calc
              cubeBesovCircDepthAverage R (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) r
                  = descendantsAverage R r
                      (fun _ => ‖cubeAverage R u‖ ^ ((2 : ℝ≥0∞).toReal)) := by
                        unfold cubeBesovCircDepthAverage descendantsAverage
                        refine congrArg (fun t : ℝ => ((descendantsAtDepth R r).card : ℝ)⁻¹ * t) ?_
                        refine Finset.sum_congr rfl ?_
                        intro S hS
                        have hRS :
                            cubeAverage S (cubeProjection Q (N + 1) u) = cubeAverage R u := by
                          have hcongr :
                              cubeAverage S (cubeProjection Q (N + 1) u) =
                                cubeAverage S (fun _ => cubeAverage R u) := by
                            apply cubeAverage_congr_on_cubeSet
                            intro x hx
                            rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
                              (Q := Q) (R := R) (j := N + 1) u hR]
                            exact cubeSet_subset_of_mem_descendantsAtDepth hS hx
                          rw [hcongr, cubeAverage_const]
                        simp [hRS]
              _ = ‖cubeAverage R u‖ ^ ((2 : ℝ≥0∞).toReal) := by
                    simp [descendantsAverage_const]
          simp [havg]
    _ = cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1) := by
          unfold cubeBesovCircDepthAverage descendantsAverage
          refine congrArg (fun t : ℝ => ((descendantsAtDepth Q (N + 1)).card : ℝ)⁻¹ * t) ?_
          refine Finset.sum_congr rfl ?_
          intro R hR
          rw [cubeAverage_cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
            (Q := Q) (R := R) (j := N + 1) (g := u) hR]

theorem cubeBesovCircDepthSeminorm_projection_eventually_geometric {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N r : ℕ) :
    cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1 + r) =
      (1 / 3 : ℝ) ^ r *
        cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) (N + 1) := by
  unfold cubeBesovCircDepthSeminorm
  rw [cubeBesovCircDepthAverage_projection_eventually_constant]
  have hweight :
      cubeBesovCircDepthWeight Q 1 (N + 1 + r) =
        (1 / 3 : ℝ) ^ r * cubeBesovCircDepthWeight Q 1 (N + 1) := by
    unfold cubeBesovCircDepthWeight
    rw [Real.rpow_one, Real.rpow_one]
    calc
      cubeScaleFactor Q / (3 : ℝ) ^ (N + 1 + r)
          = cubeScaleFactor Q / ((3 : ℝ) ^ (N + 1) * (3 : ℝ) ^ r) := by
              rw [pow_add]
      _ = (1 / 3 : ℝ) ^ r * (cubeScaleFactor Q / (3 : ℝ) ^ (N + 1)) := by
            rw [show (1 / 3 : ℝ) ^ r = ((3 : ℝ) ^ r)⁻¹ by rw [one_div, inv_pow]]
            field_simp
  rw [hweight]
  ring_nf

theorem cubeBesovCircDepthAverage_projection_eq_of_le {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N j : ℕ)
    (hj : j ≤ N + 1)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) j =
      cubeBesovCircDepthAverage Q (2 : ℝ≥0∞) u j := by
  unfold cubeBesovCircDepthAverage descendantsAverage
  refine congrArg (fun t : ℝ => ((descendantsAtDepth Q j).card : ℝ)⁻¹ * t) ?_
  refine Finset.sum_congr rfl ?_
  intro R hR
  have havg :
      cubeAverage R (cubeProjection Q (N + 1) u) = cubeAverage R u := by
    simpa [Nat.add_sub_of_le hj] using
      cubeAverage_cubeProjection_add_eq_cubeAverage_of_mem_descendantsAtDepth_of_memLp
        (Q := Q) (R := R) (j := j) (n := N + 1 - j) (u := u) hR hu
  simp [havg]

theorem cubeBesovCircDepthSeminorm_projection_eq_of_le {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (s : ℝ) (N j : ℕ)
    (hj : j ≤ N + 1)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) (cubeProjection Q (N + 1) u) j =
      cubeBesovCircDepthSeminorm Q s (2 : ℝ≥0∞) u j := by
  unfold cubeBesovCircDepthSeminorm
  rw [cubeBesovCircDepthAverage_projection_eq_of_le Q u N j hj hu]

theorem cubeBesovCircPartialNorm_projection_eq {d : ℕ}
    (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) (cubeProjection Q (N + 1) u) =
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) u := by
  simp [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hj_le : j ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  simpa using cubeBesovCircDepthSeminorm_projection_eq_of_le Q u 1 N j hj_le hu

@[simp] theorem cubeBesovCircPartialNorm_one_eq_sum {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (N : ℕ) (u : Vec d → ℝ) :
    cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) N u =
      ∑ n ∈ Finset.range (N + 1), cubeBesovCircDepthSeminorm Q s p u n := by
  simp [cubeBesovCircPartialNorm, cubeBesovCircPartialSeminorm]

theorem cubeBesovCircPartialNorm_one_mono {d : ℕ}
    (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ) {M N : ℕ}
    (hMN : M ≤ N) :
    cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) M u ≤
      cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) N u := by
  rw [cubeBesovCircPartialNorm_one_eq_sum, cubeBesovCircPartialNorm_one_eq_sum]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro j hj
    exact Finset.mem_range.mpr <|
      lt_of_lt_of_le (Finset.mem_range.mp hj) (Nat.succ_le_succ hMN)
  · intro j _ _
    exact cubeBesovCircDepthSeminorm_nonneg Q s p u j

theorem cubeBesovCircPartialNorm_one_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (p : ℝ≥0∞) (u : Vec d → ℝ)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞) :
    cubeBesovCircPartialNorm Q s p (1 : ℝ≥0∞) 0 u =
      cubeBesovScaleWeight (-s) Q * ‖cubeAverage Q u‖ := by
  rw [cubeBesovCircPartialNorm_one_eq_sum]
  simp [cubeBesovCircDepthSeminorm_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage, hp0, hpTop]

theorem cubeLpNorm_projection_depth_zero_eq_norm_cubeAverage {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (u : Vec d → ℝ) (hp0 : p ≠ 0) :
    cubeLpNorm Q p (cubeProjection Q 0 u) = ‖cubeAverage Q u‖ := by
  calc
    cubeLpNorm Q p (cubeProjection Q 0 u)
        = cubeLpNorm Q p (fun _ => cubeAverage Q u) := by
            apply cubeLpNorm_congr_on_cubeSet (Q := Q) (p := p)
            intro x hx
            rw [cubeProjection_eq_cubeAverage_of_mem_descendantsAtDepth
              (Q := Q) (R := Q) (j := 0) u (by simp) hx]
    _ = ‖cubeAverage Q u‖ := by
          simpa using cubeLpNorm_const (Q := Q) (p := p) (c := cubeAverage Q u) hp0

theorem cubeBesovCircNorm_projection_zero_le_three_halves_mul_cubeBesovCircPartialNorm_zero_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) :
    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection Q 0 u) ≤
      (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 u := by
  have hprojMem :
      MeasureTheory.MemLp (cubeProjection Q 0 u) (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    cubeProjection_memLp Q 0 (2 : ℝ≥0∞) u
  have hgeom_const : (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ = (3 / 2 : ℝ) := by
    rw [Real.rpow_neg (by positivity), Real.rpow_one]
    norm_num
  have hbase_eq :
      cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q 0 u) =
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 u := by
    calc
      cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q 0 u)
          = cubeBesovScaleWeight (-1) Q * ‖cubeAverage Q u‖ := by
              rw [cubeLpNorm_projection_depth_zero_eq_norm_cubeAverage
                (Q := Q) (p := (2 : ℝ≥0∞)) (u := u) (by norm_num)]
      _ = cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 u := by
            symm
            exact cubeBesovCircPartialNorm_one_depth_zero_eq_scaleWeight_neg_mul_norm_cubeAverage
              (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (u := u) (by norm_num) (by norm_num)
  unfold cubeBesovCircNorm
  refine csSup_le
    (cubeBesovCircNormValueSet_nonempty Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection Q 0 u)) ?_
  intro r hr
  rcases hr with ⟨M, rfl⟩
  calc
    cubeBesovCircNormEntry Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M (cubeProjection Q 0 u)
        ≤ (cubeBesovScaleWeight (-1) Q *
            cubeLpNorm Q (2 : ℝ≥0∞) (cubeProjection Q 0 u)) * (1 - (3 : ℝ) ^ (-1 : ℝ))⁻¹ := by
            exact cubeBesovCircNormEntry_le_geometric_constant_of_memLp
              (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
              (N := M) (u := cubeProjection Q 0 u)
              (by norm_num) hprojMem (by norm_num) (by norm_num) (by norm_num)
    _ = (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) 0 u := by
          rw [hbase_eq, hgeom_const]
          ring

theorem cubeBesovCircNorm_projection_succ_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (N : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection Q (N + 1) u) ≤
      (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) u := by
  let uN : Vec d → ℝ := cubeProjection Q (N + 1) u
  let a : ℕ → ℝ := fun j => cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) uN j
  let P : ℝ := cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) uN
  have hP_eq :
      P = cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) u := by
    dsimp [P, uN]
    exact cubeBesovCircPartialNorm_projection_eq Q u N hu
  have hP_nonneg : 0 ≤ P := by
    dsimp [P]
    exact cubeBesovCircPartialNorm_nonneg Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) uN
  unfold cubeBesovCircNorm
  refine csSup_le
    (cubeBesovCircNormValueSet_nonempty Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) uN) ?_
  intro r hr
  rcases hr with ⟨M, rfl⟩
  simp only [cubeBesovCircNormEntry, if_neg ENNReal.one_ne_top]
  by_cases hMN : M ≤ N
  · calc
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M + 1) uN
          ≤ cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) uN := by
              exact cubeBesovCircPartialNorm_one_mono
                (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (u := uN)
                (Nat.succ_le_succ hMN)
      _ = P := by rfl
      _ ≤ (3 / 2 : ℝ) * P := by nlinarith
      _ = (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) u := by
            rw [hP_eq]
  · have hNM : N < M := lt_of_not_ge hMN
    have hsplit :
        cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M + 1) uN =
          P + ∑ j ∈ Finset.Ico (N + 2) (M + 2), a j := by
      rw [cubeBesovCircPartialNorm_one_eq_sum]
      dsimp [P, a]
      rw [← Finset.sum_range_add_sum_Ico
        (f := fun j => cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) uN j)
        (h := Nat.add_le_add_right hNM.le 2)]
      rw [cubeBesovCircPartialNorm_one_eq_sum]
    have htail_shift :
        ∑ j ∈ Finset.Ico (N + 2) (M + 2), a j =
          ∑ r ∈ Finset.range (M - N), a (N + 2 + r) := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_add_right]
    have htail_geom :
        ∑ r ∈ Finset.range (M - N), a (N + 2 + r) =
          ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ (r + 1) * a (N + 1) := by
      refine Finset.sum_congr rfl ?_
      intro r hr
      simpa [a, uN, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        cubeBesovCircDepthSeminorm_projection_eventually_geometric
          (Q := Q) (u := u) (N := N) (r := r + 1)
    have hgeom_half :
        ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ (r + 1) ≤ (1 / 2 : ℝ) := by
      calc
        ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ (r + 1)
            = ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) * (1 / 3 : ℝ) ^ r := by
                refine Finset.sum_congr rfl ?_
                intro r hr
                rw [pow_succ, mul_comm]
        _ = (1 / 3 : ℝ) * ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ r := by
              rw [Finset.mul_sum]
        _ ≤ (1 / 3 : ℝ) * (1 - (1 / 3 : ℝ))⁻¹ := by
              gcongr
              exact geom_sum_range_le_of_lt_one (show 0 ≤ (1 / 3 : ℝ) by norm_num)
                (show (1 / 3 : ℝ) < 1 by norm_num)
        _ = (1 / 2 : ℝ) := by norm_num
    have hdepth_le_P : a (N + 1) ≤ P := by
      dsimp [a, P]
      rw [cubeBesovCircPartialNorm_one_eq_sum]
      exact Finset.single_le_sum
        (fun j _ => cubeBesovCircDepthSeminorm_nonneg Q 1 (2 : ℝ≥0∞) uN j)
        (by simp)
    have htail_le : ∑ j ∈ Finset.Ico (N + 2) (M + 2), a j ≤ (1 / 2 : ℝ) * P := by
      calc
        ∑ j ∈ Finset.Ico (N + 2) (M + 2), a j
            = ∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ (r + 1) * a (N + 1) := by
                rw [htail_shift, htail_geom]
        _ = (∑ r ∈ Finset.range (M - N), (1 / 3 : ℝ) ^ (r + 1)) * a (N + 1) := by
              rw [← Finset.sum_mul]
        _ ≤ (1 / 2 : ℝ) * a (N + 1) := by
              exact mul_le_mul_of_nonneg_right hgeom_half
                (cubeBesovCircDepthSeminorm_nonneg Q 1 (2 : ℝ≥0∞) uN (N + 1))
        _ ≤ (1 / 2 : ℝ) * P := by
              exact mul_le_mul_of_nonneg_left hdepth_le_P (by norm_num)
    calc
      cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M + 1) uN
          = P + ∑ j ∈ Finset.Ico (N + 2) (M + 2), a j := hsplit
      _ ≤ P + (1 / 2 : ℝ) * P := by gcongr
      _ = (3 / 2 : ℝ) * P := by ring
      _ = (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (N + 1) u := by
            rw [hP_eq]

theorem cubeBesovCircNorm_projection_succ_le_three_halves_mul_cubeBesovCircPartialNorm_on_descendants_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (M : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection R (M - j + 1) u) ≤
        (3 / 2 : ℝ) *
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j + 1) u := by
  intro j hj R hR
  have huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hu
  exact cubeBesovCircNorm_projection_succ_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
    (Q := R) (u := u) (N := M - j) huR

theorem cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (M : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection Q M u) ≤
      (3 / 2 : ℝ) * cubeBesovCircPartialNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M u := by
  cases M with
  | zero =>
      exact cubeBesovCircNorm_projection_zero_le_three_halves_mul_cubeBesovCircPartialNorm_zero_of_memLp
        (Q := Q) (u := u)
  | succ N =>
      simpa using
        cubeBesovCircNorm_projection_succ_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
          (Q := Q) (u := u) (N := N) hu

theorem cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_on_descendants_of_memLp
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ) (M : ℕ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    ∀ j ∈ Finset.range (M + 1), ∀ R ∈ descendantsAtDepth Q j,
      cubeBesovCircNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (cubeProjection R (M - j) u) ≤
        (3 / 2 : ℝ) *
          cubeBesovCircPartialNorm R 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (M - j) u := by
  intro j hj R hR
  have huR : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure R) :=
    memLp_on_descendant_of_memLp (Q := Q) (R := R) (j := j) hR hu
  exact cubeBesovCircNorm_projection_le_three_halves_mul_cubeBesovCircPartialNorm_of_memLp
    (Q := R) (u := u) (M := M - j) huR

end Homogenization
