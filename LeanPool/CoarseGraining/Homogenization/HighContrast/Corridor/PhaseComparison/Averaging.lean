/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Stability
public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.GridCoverage
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.AeBridge
public import LeanPool.CoarseGraining.Homogenization.CoarseGraining.CoarseBounds.Sandwich

/-!
# Grid averaging + choice

Statement of `p.phase.comparison`'s conclusions `e.phase.comparison.average` /
`e.phase.comparison.choice` in the discrete-grid setting, plus the C4-glue lemma.

## C4 glue

`ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw` turns the amended
`ThetaEllipticLaw Θ L` (whose measurability conjunct is exactly what makes this
possible) into the a.s. C1′ two-sided bound on the coarse observable, by routing
each realization through the C2 truncation bridge `exists_ellipticFieldOn_ae_eq`
to an everywhere-`(1,Θ)`-elliptic representative with the **same** coarse block
matrix, then applying the deterministic C1′ sandwich.

## The averaging argument

M2 pointwise-in-`a`; exchange `∫ ∂L` with the finite grid sum
(`integral_finset_sum`); M0 coverage `sum_indicator_gridPhase_corridor_le`
(constant `3d/ℓ`); the C4-glue `F ≤ 2M²`; `|F_σ − F|² ≤ 4M²·|F_σ − F|`; below-average
member of the nonempty grid (`N ≥ ℓ ≥ 4 > 0`).  `M² := Θ·|p|² + |q|²`.
-/

@[expose] public section

open Homogenization
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier)
open MeasureTheory

namespace Homogenization

variable {d : ℕ}

/-- **C4 glue.**  Under the amended `ThetaEllipticLaw Θ L`, the coarse block
observable a.s. satisfies the C1′ two-sided bound `0 ≤ F ≤ 2(Θ|p|² + |q|²)`.

The measurability conjunct of `ThetaEllipticLaw` supplies the entrywise
measurability that the C2 bridge `exists_ellipticFieldOn_ae_eq` needs; that
bridge produces, from each a.s. realization, an everywhere-`(1,Θ)`-elliptic
representative `a'` with `coarseBlockMatrix U a' = coarseBlockMatrix U a`, whence
the deterministic C1′ sandwich (`zero_le_blockVecDot_coarseBlockMatrix_cube`,
`blockVecDot_coarseBlockMatrix_cube_le`) transfers. -/
theorem ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw [NeZero d] {L : RestrictionCoeffLaw d}
    {Θ : ℝ} (hΘ : 1 ≤ Θ) (hell : ThetaEllipticLaw Θ L) (m : ℤ) (P : BlockVec d) :
    ∀ᵐ a ∂L,
      0 ≤ blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P) ∧
        blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P) ≤
          2 * (Θ * vecNormSq P.1 + vecNormSq P.2) := by
  classical
  filter_upwards [hell] with a haeEll
  have hU : MeasurableSet (cubeSet (originCube d m)) := measurableSet_cubeSet (originCube d m)
  have hmeasA :
      Measurable (fun x => fun i j =>
        if x ∈ cubeSet (originCube d m) then a x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Set.indicator] using! (a.entry_measurable i j).indicator hU
  have haeU : ∀ᵐ x ∂(volume.restrict (cubeSet (originCube d m))),
      IsEllipticMatrix 1 Θ (a x) := ae_restrict_of_ae haeEll
  obtain ⟨a', hEll', _, hcoarse, _⟩ := exists_ellipticFieldOn_ae_eq hU hΘ hmeasA haeU
  rw [← hcoarse]
  exact ⟨zero_le_blockVecDot_coarseBlockMatrix_cube hEll' P,
    blockVecDot_coarseBlockMatrix_cube_le hEll' P⟩

/-! ## Per-realization summed bound

For a single measurable, a.e.-`(1,Θ)`-elliptic realization `a`, pass it through
the C2 bridge to an everywhere-elliptic representative `a'` with the same coarse
block matrices, take the minimizer `Z` for `a'` (one `Z` serves every phase),
apply M2-core per phase, and sum with the M0 grid-coverage count `3d/ℓ` and the
C1′ energy bound `F ≤ 2M²`. -/

/-- The finite-grid summed square deviation, bounded pointwise-in-`a` by
`576 d Θ N^d (M²)² / ℓ`, together with the per-phase bound `≤ 2M²`, for any
measurable a.e.-`(1,Θ)`-elliptic realization. -/
theorem gridPhase_summed_sq_le_of_realization [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {m : ℤ} {ℓ : ℝ} (hℓ : 4 ≤ ℓ) {N : ℕ} (hN : (ℓ : ℝ) ≤ (N : ℝ)) (P : BlockVec d)
    {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, Measurable fun x : Vec d => a x i j)
    (haeEll : ∀ᵐ x ∂(volume : Measure (Vec d)), IsEllipticMatrix 1 Θ (a x)) :
    (∀ σ : Fin d → Fin N,
        |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
              (corridorField ℓ (gridPhase ℓ N σ) a)) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P)|
          ≤ 2 * (Θ * vecNormSq P.1 + vecNormSq P.2)) ∧
      ∑ σ : Fin d → Fin N,
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
                (corridorField ℓ (gridPhase ℓ N σ) a)) P) -
              blockVecDot P
                (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a) P)| ^ 2
        ≤ 576 * (d : ℝ) * Θ * (N : ℝ) ^ d * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 / ℓ := by
  classical
  set U := cubeSet (originCube d m) with hUdef
  have hU : MeasurableSet U := measurableSet_cubeSet (originCube d m)
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by rw [hUdef]; infer_instance
  have hΘpos : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  set Msq := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘpos.le (vecNormSq_nonneg P.1)) (vecNormSq_nonneg P.2)
  -- C2 bridge to an everywhere-elliptic representative
  have hmeasA : Measurable (fun x => fun i j => if x ∈ U then a x i j else 0) := by
    refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => ?_
    simpa only [Set.indicator] using! (hmeas i j).indicator hU
  have haeU : ∀ᵐ x ∂(volume.restrict U), IsEllipticMatrix 1 Θ (a x) := ae_restrict_of_ae haeEll
  obtain ⟨a', hEll', ha'ae, hcoarse, _hblockae⟩ := exists_ellipticFieldOn_ae_eq hU hΘ hmeasA haeU
  obtain ⟨Z, hZadm, hZeng, hZresp⟩ := exists_cubeBlockMinimizer hEll' P
  -- transport the corridor coarse matrices from `a` to `a'`
  have hcorreq : ∀ σ : Fin d → Fin N,
      coarseBlockMatrix U (corridorField ℓ (gridPhase ℓ N σ) a)
        = coarseBlockMatrix U (corridorField ℓ (gridPhase ℓ N σ) a') := by
    intro σ
    refine coarseBlockMatrix_congr_of_ae_eq ?_
    filter_upwards [ha'ae] with x hx
    by_cases hxc : x ∈ corridorSet ℓ (gridPhase ℓ N σ)
    · rw [corridorField_apply_of_mem hxc, corridorField_apply_of_mem hxc]
    · rw [corridorField_apply_of_not_mem hxc, corridorField_apply_of_not_mem hxc]; exact hx.symm
  simp_rw [hcorreq, ← hcoarse]
  -- per-phase `≤ 2 M²`
  have hle2 : ∀ σ : Fin d → Fin N,
      |blockVecDot P (blockMatVecMul (coarseBlockMatrix U (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
          blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| ≤ 2 * Msq := by
    intro σ
    have hEllφ : IsEllipticFieldOn 1 Θ U (corridorField ℓ (gridPhase ℓ N σ) a') :=
      isEllipticFieldOn_corridorField hU hΘ hEll'
    have hFa'0 : 0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P) :=
      zero_le_blockVecDot_coarseBlockMatrix_cube hEll' P
    have hFa'le : blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P) ≤ 2 * Msq :=
      blockVecDot_coarseBlockMatrix_cube_le hEll' P
    have hFφ0 : 0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix U
        (corridorField ℓ (gridPhase ℓ N σ) a')) P) :=
      zero_le_blockVecDot_coarseBlockMatrix_cube hEllφ P
    have hFφle : blockVecDot P (blockMatVecMul (coarseBlockMatrix U
        (corridorField ℓ (gridPhase ℓ N σ) a')) P) ≤ 2 * Msq :=
      blockVecDot_coarseBlockMatrix_cube_le hEllφ P
    rw [abs_le]; exact ⟨by linarith, by linarith⟩
  refine ⟨hle2, ?_⟩
  -- energy machinery for the second conjunct
  set c := (volume U).toReal⁻¹ with hcdef
  set G := fun x => blockVecDot (Z.eval x) (blockMatVecMul (blockCoeffField a' x) (Z.eval x))
    with hGdef
  have hc0 : (0 : ℝ) ≤ c := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hGint : IntegrableOn G U :=
    blockPairingIntegrand_integrableOn_of_memBlockL2_of_isEllipticFieldOn
      (X := Z) (Y := Z) hZadm.memBlockL2_eval hZadm.memBlockL2_eval hEll'
  have hG0 : ∀ x ∈ U, 0 ≤ G x :=
    fun x hx => blockMatrixOfCoeff_quadratic_nonneg (hEll'.2 x hx) (Z.eval x)
  have hFa'eq : blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P) = c * ∫ x in U, G x :=
    coarseBlockMatrix_quadratic_eq_energyIntegral P hEll' hZeng
  have hFa'le : blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P) ≤ 2 * Msq :=
    blockVecDot_coarseBlockMatrix_cube_le hEll' P
  -- M2-core per phase (single minimizer `Z` for `a'`)
  have hcore : ∀ σ : Fin d → Fin N,
      |blockVecDot P (blockMatVecMul (coarseBlockMatrix U (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
          blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)|
        ≤ 48 * Θ * c * ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x := fun σ =>
    abs_phaseObservable_sub_le_of_minimizer hΘ P hEll' hZadm hZresp hZeng
  -- coverage: Σ_σ ∫_{S_σ∩U} G ≤ (3d/ℓ) N^d ∫_U G
  have hcov : ∑ σ : Fin d → Fin N, ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x
      ≤ 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d * ∫ x in U, G x := by
    have hrw : ∀ σ : Fin d → Fin N,
        (∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x)
          = ∫ x in U, (corridorSet ℓ (gridPhase ℓ N σ)).indicator G x := by
      intro σ
      rw [setIntegral_indicator (measurableSet_corridorSet ℓ (gridPhase ℓ N σ)),
        Set.inter_comm U (corridorSet ℓ (gridPhase ℓ N σ))]
    simp_rw [hrw]
    rw [← integral_finsetSum _
        (fun σ _ => hGint.indicator (measurableSet_corridorSet ℓ (gridPhase ℓ N σ)))]
    rw [show 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d * ∫ x in U, G x
          = ∫ x in U, 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d * G x from (integral_const_mul _ _).symm]
    refine setIntegral_mono_on
      (integrable_finsetSum _
        (fun σ _ => hGint.indicator (measurableSet_corridorSet ℓ (gridPhase ℓ N σ))))
      (hGint.const_mul _) hU (fun x hx => ?_)
    have hGx : 0 ≤ G x := hG0 x hx
    have hfact : (∑ σ : Fin d → Fin N, (corridorSet ℓ (gridPhase ℓ N σ)).indicator G x)
        = G x * ∑ σ : Fin d → Fin N,
            (corridorSet ℓ (gridPhase ℓ N σ)).indicator (fun _ => (1 : ℝ)) x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      by_cases hxc : x ∈ corridorSet ℓ (gridPhase ℓ N σ)
      · simp [Set.indicator_of_mem hxc]
      · simp [Set.indicator_of_notMem hxc]
    rw [hfact]
    calc G x * ∑ σ : Fin d → Fin N,
            (corridorSet ℓ (gridPhase ℓ N σ)).indicator (fun _ => (1 : ℝ)) x
        ≤ G x * (3 * (d : ℝ) / ℓ * (N : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left (sum_indicator_gridPhase_corridor_le hℓ hN x) hGx
      _ = 3 * (d : ℝ) / ℓ * (N : ℝ) ^ d * G x := by ring
  -- combine
  have hcoef0 : (0 : ℝ) ≤ 2 * Msq * (48 * Θ * c) :=
    mul_nonneg (by linarith [hMsq0])
      (mul_nonneg (mul_nonneg (by norm_num) hΘpos.le) hc0)
  have hcoef2 : (0 : ℝ) ≤ 2 * Msq * 48 * Θ * (3 * (d : ℝ) / ℓ) * (N : ℝ) ^ d := by
    have h1 : (0 : ℝ) ≤ 2 * Msq := by linarith [hMsq0]
    have h2 : (0 : ℝ) ≤ 3 * (d : ℝ) / ℓ := div_nonneg (by positivity) hℓ0.le
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h1 (by norm_num)) hΘpos.le) h2)
      (by positivity)
  have hkey : ∀ σ : Fin d → Fin N,
      |blockVecDot P (blockMatVecMul (coarseBlockMatrix U (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
          blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| ^ 2
        ≤ 2 * Msq * (48 * Θ * c) * ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x := by
    intro σ
    have hd0 := abs_nonneg (blockVecDot P (blockMatVecMul (coarseBlockMatrix U
      (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
        blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P))
    calc |blockVecDot P (blockMatVecMul (coarseBlockMatrix U
              (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| ^ 2
        = |blockVecDot P (blockMatVecMul (coarseBlockMatrix U
              (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| *
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix U
              (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| := by ring
      _ ≤ (2 * Msq) *
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix U
              (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| :=
          mul_le_mul_of_nonneg_right (hle2 σ) hd0
      _ ≤ (2 * Msq) * (48 * Θ * c * ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x) :=
          mul_le_mul_of_nonneg_left (hcore σ) (by linarith [hMsq0])
      _ = 2 * Msq * (48 * Θ * c) * ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x := by ring
  calc ∑ σ : Fin d → Fin N,
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix U
                (corridorField ℓ (gridPhase ℓ N σ) a')) P) -
              blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P)| ^ 2
      ≤ ∑ σ : Fin d → Fin N,
          2 * Msq * (48 * Θ * c) * ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x :=
        Finset.sum_le_sum (fun σ _ => hkey σ)
    _ = 2 * Msq * (48 * Θ * c) *
          ∑ σ : Fin d → Fin N, ∫ x in corridorSet ℓ (gridPhase ℓ N σ) ∩ U, G x := by
        rw [Finset.mul_sum]
    _ ≤ 2 * Msq * (48 * Θ * c) * (3 * (d : ℝ) / ℓ * (N : ℝ) ^ d * ∫ x in U, G x) :=
        mul_le_mul_of_nonneg_left hcov hcoef0
    _ = 2 * Msq * 48 * Θ * (3 * (d : ℝ) / ℓ) * (N : ℝ) ^ d * (c * ∫ x in U, G x) := by ring
    _ = 2 * Msq * 48 * Θ * (3 * (d : ℝ) / ℓ) * (N : ℝ) ^ d *
          blockVecDot P (blockMatVecMul (coarseBlockMatrix U a') P) := by rw [← hFa'eq]
    _ ≤ 2 * Msq * 48 * Θ * (3 * (d : ℝ) / ℓ) * (N : ℝ) ^ d * (2 * Msq) :=
        mul_le_mul_of_nonneg_left hFa'le hcoef2
    _ = 576 * (d : ℝ) * Θ * (N : ℝ) ^ d * Msq ^ 2 / ℓ := by ring

/-- **M3 (averaging + choice).**  Under a `RestrictionLawCarrier` `Θ`-elliptic law and
`4 ≤ ℓ ≤ N`, there is a deterministic grid phase `σ_*` whose mean-square coarse
deviation is `O(ℓ⁻¹)`, with an explicit dimensional constant `Cd = 576 d`.  The
per-realization summed bound `gridPhase_summed_sq_le_of_realization` is averaged
over the probability law and a below-average phase is selected. -/
theorem exists_gridPhase_meanSq_le [NeZero d] {Θ : ℝ} (hΘ : 1 ≤ Θ)
    {L : RestrictionCoeffLaw d} (hP : RestrictionLawCarrier L) (hell : ThetaEllipticLaw Θ L)
    {m : ℤ} {ℓ : ℝ} (hℓ : 4 ≤ ℓ) {N : ℕ} (hN : (ℓ : ℝ) ≤ (N : ℝ))
    (P : BlockVec d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∃ σ ∈ (Finset.univ : Finset (Fin d → Fin N)),
        ∫ a,
            |blockVecDot P
                  (blockMatVecMul
                    (coarseBlockMatrix (cubeSet (originCube d m))
                      (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
                blockVecDot P
                  (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2 ∂L ≤
          Cd * Θ * ℓ⁻¹ * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2 := by
  classical
  have : IsProbabilityMeasure L := hP.isProbability
  set Msq := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hΘpos : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hℓ0 hN
  have hNpow0 : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  set B := 576 * (d : ℝ) * Θ * (N : ℝ) ^ d * Msq ^ 2 / ℓ with hBdef
  -- a.e. per-realization bounds
  have hAE : ∀ᵐ a ∂L,
      (∀ σ : Fin d → Fin N,
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
                (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
              blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)|
            ≤ 2 * Msq) ∧
      (∑ σ : Fin d → Fin N,
          |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
                (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
              blockVecDot P
                (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2 ≤ B) := by
    filter_upwards [hell] with a ha
    exact gridPhase_summed_sq_le_of_realization hΘ hℓ hN P
      (fun i j => a.entry_measurable i j) ha
  -- integrability of each squared deviation
  have hInt : ∀ σ : Fin d → Fin N,
      Integrable (fun a =>
        |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
              (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2)
        L := by
    intro σ
    have hFφ := aestronglyMeasurable_phaseObservable hP m ℓ (gridPhase ℓ N σ) P
    have hF := aestronglyMeasurable_coarseBlockQuadratic_cubeSet hP m P
    have hmeas : AEStronglyMeasurable (fun a =>
        |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
              (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2)
        L := by
      have h2 : AEStronglyMeasurable (fun a =>
          (blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
                (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
              blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)) ^ 2)
          L := by simpa [pow_two] using! (hFφ.sub hF).mul (hFφ.sub hF)
      simpa [sq_abs] using h2
    refine (integrable_const (4 * Msq ^ 2)).mono' hmeas ?_
    filter_upwards [hAE] with a ha
    have h1 := ha.1 σ
    have h0 := abs_nonneg (blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
      (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [h1, h0]
  -- exchange the finite sum with the integral, bound by the constant `B`
  have hsum : ∑ σ : Fin d → Fin N,
      ∫ a, |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
            (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
          blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2 ∂L
        ≤ B := by
    rw [← integral_finsetSum _ (fun σ _ => hInt σ)]
    calc ∫ a, ∑ σ : Fin d → Fin N,
            |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
                  (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
                blockVecDot P
                  (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2 ∂L
        ≤ ∫ _a, B ∂L :=
          integral_mono_ae (integrable_finsetSum _ (fun σ _ => hInt σ)) (integrable_const B)
            (by filter_upwards [hAE] with a ha; exact ha.2)
      _ = B := by rw [integral_const]; simp
  -- choose a below-average phase
  have hcard : (Finset.univ : Finset (Fin d → Fin N)).card = N ^ d := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hne : (Finset.univ : Finset (Fin d → Fin N)).Nonempty := by
    have hNpos : 0 < N := by exact_mod_cast hN0
    have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    exact Finset.univ_nonempty
  refine ⟨576 * (d : ℝ), by positivity, ?_⟩
  have hgsum : (∑ _σ : Fin d → Fin N, B / (N : ℝ) ^ d) = B := by
    rw [Finset.sum_const, hcard, nsmul_eq_mul]
    push_cast
    field_simp
  obtain ⟨σ, hσuniv, hσ⟩ := Finset.exists_le_of_sum_le hne
    (show (∑ σ : Fin d → Fin N,
        ∫ a, |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
              (corridorField ℓ (gridPhase ℓ N σ) a.toFun)) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)| ^ 2 ∂L)
        ≤ ∑ _σ : Fin d → Fin N, B / (N : ℝ) ^ d from by rw [hgsum]; exact hsum)
  refine ⟨σ, hσuniv, ?_⟩
  have hBdiv : B / (N : ℝ) ^ d = 576 * (d : ℝ) * Θ * ℓ⁻¹ * Msq ^ 2 := by
    rw [hBdef]; field_simp
  rw [← hBdiv]; exact hσ

end Homogenization
