/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.AssemblyPieces
import LeanPool.CoarseGraining.Homogenization.Besov.Localization

/-! # Euclidean Wsp Localization -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- `ENNReal` average over the finite set of depth-`j` descendants. -/
noncomputable def descendantsENNAverage {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (F : TriadicCube d → ℝ≥0∞) : ℝ≥0∞ :=
  ((descendantsAtDepth Q j).card : ℝ≥0∞)⁻¹ *
    ∑ R ∈ descendantsAtDepth Q j, F R

private theorem lintegral_normalizedCubeMeasure_eq {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ≥0∞) :
    (∫⁻ x, f x ∂normalizedCubeMeasure Q) =
      ENNReal.ofReal (cubeVolume Q)⁻¹ *
        ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by
  rw [normalizedCubeMeasure, lintegral_smul_measure]
  rfl

/-- Exact descendant partition identity for a first-variable normalized
nonnegative integrand. -/
theorem descendantsENNAverage_lintegral_normalizedCubeMeasure_eq {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : Vec d → ℝ≥0∞) :
    descendantsENNAverage Q j
        (fun R => ∫⁻ x, f x ∂normalizedCubeMeasure R) =
      ∫⁻ x, f x ∂normalizedCubeMeasure Q := by
  classical
  let D : Finset (TriadicCube d) := descendantsAtDepth Q j
  have hD : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q j
  have hfactor : ∀ R ∈ D,
      ((D.card : ℝ≥0∞)⁻¹) * ENNReal.ofReal (cubeVolume R)⁻¹ =
        ENNReal.ofReal (cubeVolume Q)⁻¹ := by
    intro R hR
    have hvol : cubeVolume Q = (D.card : ℝ) * cubeVolume R :=
      cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth (Q := Q)
        (by simpa [D] using hR)
    have hcard_pos : 0 < (D.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hD
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hcard_pos,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hcard_pos.le)]
    congr 1
    rw [hvol, mul_inv]
  have hmeas : ∀ R ∈ D, MeasurableSet (cubeSet R) := fun R _ => measurableSet_cubeSet R
  have hdisj : (D : Set (TriadicCube d)).PairwiseDisjoint cubeSet := by
    simpa [D] using pairwiseDisjoint_descendantsAtDepth Q j
  have hsum : (∑ R ∈ D, ∫⁻ x in cubeSet R, f x ∂MeasureTheory.volume) =
      ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by
    rw [cubeSet_eq_iUnion_descendantsAtDepth Q j]
    symm
    exact lintegral_biUnion_finset hdisj (fun R hR => hmeas R hR) f
  rw [descendantsENNAverage, Finset.mul_sum]
  simp_rw [lintegral_normalizedCubeMeasure_eq]
  calc
    ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹) *
        (ENNReal.ofReal (cubeVolume R)⁻¹ *
          ∫⁻ x in cubeSet R, f x ∂MeasureTheory.volume)
      = ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∑ R ∈ D, ∫⁻ x in cubeSet R, f x ∂MeasureTheory.volume := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R hR => by rw [← mul_assoc, hfactor R hR]
    _ = ENNReal.ofReal (cubeVolume Q)⁻¹ *
          ∫⁻ x in cubeSet Q, f x ∂MeasureTheory.volume := by rw [hsum]

/-- The exact finite-exponent Euclidean normalized `Lᵖ` descendant partition. -/
theorem descendantsENNAverage_normalizedEuclideanLpENorm_rpow_eq {d n : ℕ}
    (Q : TriadicCube d) (j : ℕ) (p : ℝ≥0∞) (F : Vec d → Vec n)
    (hp0 : p ≠ 0) (hpt : p ≠ ∞) :
    descendantsENNAverage Q j (fun R =>
      ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p F) ^ p.toReal) =
      ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p F) ^ p.toReal := by
  let f : Vec d → ℝ≥0∞ := fun x => ‖euclideanNorm (F x)‖ₑ ^ p.toReal
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hpow (R : TriadicCube d) :
      ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p F) ^ p.toReal =
        ∫⁻ x, f x ∂normalizedCubeMeasure R := by
    unfold BoundedMeasurableDomain.normalizedEuclideanLpENorm
    unfold BoundedMeasurableDomain.normalizedLpENorm
    rw [cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure,
      MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt, ← ENNReal.rpow_mul]
    have hpr : (1 / p.toReal) * p.toReal = 1 := by field_simp
    rw [hpr, ENNReal.rpow_one]
  calc
    descendantsENNAverage Q j (fun R =>
      ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p F) ^ p.toReal)
      = descendantsENNAverage Q j (fun R => ∫⁻ x, f x ∂normalizedCubeMeasure R) := by
          congr 2
          funext R
          exact hpow R
    _ = ∫⁻ x, f x ∂normalizedCubeMeasure Q :=
      descendantsENNAverage_lintegral_normalizedCubeMeasure_eq Q j f
    _ = ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p F) ^ p.toReal :=
      (hpow Q).symm

/-- Exact change of the anchored `p`-power scale weight down `j` triadic
levels.  The factor is the manuscript's `3^(j*s*p)`. -/
theorem descendant_scale_weight_algebra {d : ℕ} {Q R : TriadicCube d} {j : ℕ}
    (hR : R ∈ descendantsAtDepth Q j) (s : ℝ) (p : ℝ≥0∞) (hs : 0 ≤ s) :
    (ENNReal.ofReal (cubeScaleFactor R)) ^ (-s * p.toReal) =
      ((ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s * p.toReal)) *
        (ENNReal.ofReal (cubeScaleFactor Q)) ^ (-s * p.toReal) := by
  have hscale : cubeScaleFactor R = cubeScaleFactor Q / (3 : ℝ) ^ j :=
    cubeScaleFactor_descendant_eq_div_pow hR
  have hc : 0 ≤ s * p.toReal := mul_nonneg hs ENNReal.toReal_nonneg
  have hthree : 0 < ((3 : ℝ) ^ j) := by positivity
  have hbpos : 0 < (ENNReal.ofReal ((3 : ℝ) ^ j)) ^ (s * p.toReal) :=
    ENNReal.rpow_pos (ENNReal.ofReal_pos.mpr hthree) ENNReal.ofReal_ne_top
  have hbtop : (ENNReal.ofReal ((3 : ℝ) ^ j)) ^ (s * p.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_ne_zero (ne_of_gt (ENNReal.ofReal_pos.mpr hthree))
      ENNReal.ofReal_ne_top
  rw [hscale, ENNReal.ofReal_div_of_pos hthree]
  have hneg : -s * p.toReal = -(s * p.toReal) := by ring
  rw [hneg, ENNReal.rpow_neg, ENNReal.div_rpow_of_nonneg _ _ hc,
    ENNReal.inv_div (Or.inl hbtop) (Or.inl (ne_of_gt hbpos)),
    ENNReal.div_eq_inv_mul, ← ENNReal.rpow_neg, mul_comm]
  congr 1
  rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3), ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  ring_nf

private theorem descendantsENNAverage_add {d : ℕ} (Q : TriadicCube d) (j : ℕ)
    (A B : TriadicCube d → ℝ≥0∞) :
    descendantsENNAverage Q j (fun R => A R + B R) =
      descendantsENNAverage Q j A + descendantsENNAverage Q j B := by
  unfold descendantsENNAverage
  rw [Finset.sum_add_distrib]
  ring

/-- Pure `ENNReal` assembly of the full-norm power localization.  The three
inputs are exactly: local physical-scale weights, normalized `Lᵖ` powers, and
fractional seminorm powers. -/
theorem descendantsENNAverage_full_power_le_of_partition {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (A : ℝ≥0∞)
    (w L S : TriadicCube d → ℝ≥0∞)
    (hA : 1 ≤ A)
    (hw : ∀ R ∈ descendantsAtDepth Q j, w R = A * w Q)
    (hL : descendantsENNAverage Q j L = L Q)
    (hS : descendantsENNAverage Q j S ≤ S Q) :
    descendantsENNAverage Q j (fun R => w R * L R + S R) ≤
      A * (w Q * L Q + S Q) := by
  have hmain : descendantsENNAverage Q j (fun R => w R * L R) =
      (A * w Q) * descendantsENNAverage Q j L := by
    unfold descendantsENNAverage
    have hsum : (∑ R ∈ descendantsAtDepth Q j, w R * L R) =
        (A * w Q) * ∑ R ∈ descendantsAtDepth Q j, L R := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun R hR => ?_
      rw [hw R hR]
    rw [hsum]
    ac_rfl
  calc
    descendantsENNAverage Q j (fun R => w R * L R + S R)
      = (A * w Q) * descendantsENNAverage Q j L + descendantsENNAverage Q j S := by
          rw [descendantsENNAverage_add, hmain]
    _ = (A * w Q) * L Q + descendantsENNAverage Q j S := by rw [hL]
    _ ≤ (A * w Q) * L Q + A * S Q := by
          gcongr
          exact hS.trans (le_mul_of_one_le_left bot_le hA)
    _ = A * (w Q * L Q + S Q) := by ring

private theorem lintegral_descendant_diagonals_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (f : Vec d × Vec d → ℝ≥0∞) :
    (∑ R ∈ descendantsAtDepth Q j,
      ∫⁻ z in cubeSet R ×ˢ cubeSet R, f z ∂(volume.prod volume)) ≤
      ∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z ∂(volume.prod volume) := by
  classical
  let D := descendantsAtDepth Q j
  have hm : ∀ R ∈ D, MeasurableSet (cubeSet R ×ˢ cubeSet R) :=
    fun R _ => (measurableSet_cubeSet R).prod (measurableSet_cubeSet R)
  have hd : (D : Set (TriadicCube d)).PairwiseDisjoint
      (fun R => cubeSet R ×ˢ cubeSet R) := by
    intro R hR S hS hRS
    exact Set.disjoint_prod.mpr (Or.inl
      (pairwiseDisjoint_descendantsAtDepth Q j (by simpa [D] using hR)
        (by simpa [D] using hS) hRS))
  have hsub : (⋃ R ∈ (D : Set (TriadicCube d)), cubeSet R ×ˢ cubeSet R) ⊆
      cubeSet Q ×ˢ cubeSet Q := by
    intro z hz
    rcases Set.mem_iUnion₂.mp hz with ⟨R, hR, hz⟩
    exact ⟨cubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR) hz.1,
      cubeSet_subset_of_mem_descendantsAtDepth (by simpa [D] using hR) hz.2⟩
  rw [← lintegral_biUnion_finset hd hm]
  exact lintegral_mono_set hsub

theorem descendantsENNAverage_cubeEuclideanWspESeminorm_rpow_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    descendantsENNAverage Q j
        (fun R => (cubeEuclideanWspESeminorm R s p F) ^ p.exponent.toReal) ≤
      (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal := by
  let f : Vec d × Vec d → ℝ≥0∞ := fun z =>
    ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hpow (R : TriadicCube d) :
      (cubeEuclideanWspESeminorm R s p F) ^ p.exponent.toReal =
        ENNReal.ofReal (cubeVolume R)⁻¹ * ∫⁻ z in cubeSet R ×ˢ cubeSet R, f z ∂(volume.prod volume) := by
    rw [cubeEuclideanWspESeminorm_eq_lintegral, ← ENNReal.rpow_mul]
    have h : (1 / p.exponent.toReal) * p.exponent.toReal = 1 := by field_simp
    rw [h, ENNReal.rpow_one]
    simpa [f] using Gagliardo.lintegral_gagliardoCubeMeasure_eq R f
  rw [show (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal =
    ENNReal.ofReal (cubeVolume Q)⁻¹ * ∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z ∂(volume.prod volume) by exact hpow Q]
  unfold descendantsENNAverage
  rw [Finset.mul_sum]
  simp_rw [hpow]
  let D := descendantsAtDepth Q j
  have hD : D.Nonempty := by simpa [D] using descendantsAtDepth_nonempty Q j
  have hf : ∀ R ∈ D, ((D.card : ℝ≥0∞)⁻¹) * ENNReal.ofReal (cubeVolume R)⁻¹ =
      ENNReal.ofReal (cubeVolume Q)⁻¹ := by
    intro R hR
    have hv := cubeVolume_eq_card_mul_cubeVolume_of_mem_descendantsAtDepth (Q := Q)
      (by simpa [D] using hR)
    have hc : 0 < (D.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hD
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos hc,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hc.le)]
    congr 1
    rw [hv, mul_inv]
  calc
    ∑ R ∈ D, ((D.card : ℝ≥0∞)⁻¹) *
        (ENNReal.ofReal (cubeVolume R)⁻¹ * ∫⁻ z in cubeSet R ×ˢ cubeSet R, f z ∂(volume.prod volume)) =
      ENNReal.ofReal (cubeVolume Q)⁻¹ * ∑ R ∈ D,
        ∫⁻ z in cubeSet R ×ˢ cubeSet R, f z ∂(volume.prod volume) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun R hR => by rw [← mul_assoc, hf R hR]
    _ ≤ ENNReal.ofReal (cubeVolume Q)⁻¹ * ∫⁻ z in cubeSet Q ×ˢ cubeSet Q, f z ∂(volume.prod volume) := by
      gcongr
      exact lintegral_descendant_diagonals_le Q j f

theorem descendantsENNAverage_cubeEuclideanWspFullENorm_rpow_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    descendantsENNAverage Q j
        (fun R => (cubeEuclideanWspFullENorm R s p F) ^ p.exponent.toReal) ≤
      (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1 * p.exponent.toReal) *
        (cubeEuclideanWspFullENorm Q s p F) ^ p.exponent.toReal := by
  let A : ℝ≥0∞ := (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1 * p.exponent.toReal)
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hA : 1 ≤ A := by
    simpa [A] using ENNReal.rpow_le_rpow (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal 3 by norm_num)
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) s.2.1.le) ENNReal.toReal_nonneg)
  have hpow (R : TriadicCube d) :
      (cubeEuclideanWspFullENorm R s p F) ^ p.exponent.toReal =
        cubeEuclideanWspScalePowerWeight R s p *
          ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p.exponent F) ^ p.exponent.toReal +
        (cubeEuclideanWspESeminorm R s p F) ^ p.exponent.toReal := by
    unfold cubeEuclideanWspFullENorm
    rw [← ENNReal.rpow_mul]
    have h : p.exponent.toReal⁻¹ * p.exponent.toReal = 1 := by field_simp
    rw [h, ENNReal.rpow_one]
  have hw : ∀ R ∈ descendantsAtDepth Q j,
      cubeEuclideanWspScalePowerWeight R s p = A * cubeEuclideanWspScalePowerWeight Q s p := by
    intro R hR
    exact descendant_scale_weight_algebra hR s.1 p.exponent s.2.1.le
  have hL := descendantsENNAverage_normalizedEuclideanLpENorm_rpow_eq
    Q j p.exponent F (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hS := descendantsENNAverage_cubeEuclideanWspESeminorm_rpow_le Q j s p F
  calc
    descendantsENNAverage Q j (fun R => (cubeEuclideanWspFullENorm R s p F) ^ p.exponent.toReal)
      = descendantsENNAverage Q j (fun R =>
          cubeEuclideanWspScalePowerWeight R s p *
            ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p.exponent F) ^ p.exponent.toReal +
          (cubeEuclideanWspESeminorm R s p F) ^ p.exponent.toReal) := by
            congr 2
            funext R
            exact hpow R
    _ ≤ A * (cubeEuclideanWspScalePowerWeight Q s p *
          ((cubeBoundedMeasurableDomain Q).normalizedEuclideanLpENorm p.exponent F) ^ p.exponent.toReal +
          (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal) :=
      descendantsENNAverage_full_power_le_of_partition Q j A
        (cubeEuclideanWspScalePowerWeight · s p)
        (fun R => ((cubeBoundedMeasurableDomain R).normalizedEuclideanLpENorm p.exponent F) ^ p.exponent.toReal)
        (fun R => (cubeEuclideanWspESeminorm R s p F) ^ p.exponent.toReal) hA hw hL hS
    _ = A * (cubeEuclideanWspFullENorm Q s p F) ^ p.exponent.toReal := by rw [hpow Q]

/-- Rooted form of positive Euclidean `W^{s,p}` descendant localization. -/
theorem descendantsENNAverage_cubeEuclideanWspFullENorm_root_le {d : ℕ}
    (Q : TriadicCube d) (j : ℕ) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (descendantsENNAverage Q j
        (fun R => (cubeEuclideanWspFullENorm R s p F) ^ p.exponent.toReal)) ^
          (p.exponent.toReal)⁻¹ ≤
      (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) *
        cubeEuclideanWspFullENorm Q s p F := by
  let A : ℝ≥0∞ := (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1 * p.exponent.toReal)
  let N : ℝ≥0∞ := cubeEuclideanWspFullENorm Q s p F
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hpower := descendantsENNAverage_cubeEuclideanWspFullENorm_rpow_le Q j s p F
  change _ ≤ (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) * N
  calc
    (descendantsENNAverage Q j
        (fun R => (cubeEuclideanWspFullENorm R s p F) ^ p.exponent.toReal)) ^
          (p.exponent.toReal)⁻¹
      ≤ (A * N ^ p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ := by
          exact ENNReal.rpow_le_rpow hpower (inv_nonneg.mpr hp.le)
    _ = A ^ (p.exponent.toReal)⁻¹ *
          (N ^ p.exponent.toReal) ^ (p.exponent.toReal)⁻¹ :=
      ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le)
    _ = (ENNReal.ofReal (3 : ℝ)) ^ ((j : ℝ) * s.1) * N := by
      congr 1
      · rw [show A = (ENNReal.ofReal (3 : ℝ)) ^
          ((j : ℝ) * s.1 * p.exponent.toReal) by rfl, ← ENNReal.rpow_mul]
        have h : ((j : ℝ) * s.1 * p.exponent.toReal) * p.exponent.toReal⁻¹ =
            (j : ℝ) * s.1 := by field_simp
        rw [h]
      · rw [← ENNReal.rpow_mul]
        have h : p.exponent.toReal * p.exponent.toReal⁻¹ = 1 := by field_simp
        rw [h, ENNReal.rpow_one]

end
end Homogenization
