/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.RpowOpt
import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.FixedPhaseUniform
import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.AveragingUniform
import LeanPool.CoarseGraining.Homogenization.HighContrast.Variance.Projection

/-!
# Scalar block variance (`e.scalar.block.variance`)

Assembly of the scalar estimate: for any origin cube `𝒰_m` and block
vector `P = (p, q)`,

  `Var[P · 𝐀(𝒰_m) P] ≤ C_d·(Θ|p|² + |q|²)²·min{1, Θ²·3^{-β_d·m}}`,
  `β_d = (d-2)/(d-1)`.

The three ingredients, each with a *uniform* dimensional constant:

* `fixed_phase_variance_uniform` — `Var[F_σ] ≤ C_fp·Θ³(ℓ/3^m)^{d-2}·Msq²`;
* `exists_gridPhase_meanSq_le_uniform` — a grid phase `σ` with
  `∫|F_σ − F|² ≤ C_av·Θ·ℓ⁻¹·Msq²`;
* the deterministic a.s. bound `0 ≤ F ≤ 2·Msq` (`t.coarse.block.ellipticity`).

Step (i) is the `L²`-projection split `var_le_two_integral_add_two_var`; step (ii)
combines the two errors at a free width `ℓ ∈ [4, 3^m]`; step (iii) is the rpow
optimization `scalar_opt`.  The constant is fixed *before* the field quantifiers.
-/

namespace Homogenization

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier)

variable {d : ℕ}

/-- **Scalar block variance.**  Dimensional constant `Cd`, uniform in the
scale `m`, contrast `Θ`, law `L`, and block vector `P`. -/
theorem scalar_block_variance [NeZero d] (hd : 3 ≤ d) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {m : ℤ} (_hm : 0 ≤ m) {Θ : ℝ} (_hΘ : 1 ≤ Θ) {L : RestrictionCoeffLaw d}
        [IsProbabilityMeasure L] (_hP : RestrictionLawCarrier L)
        (_hURD : IsRestrictionUnitRangeDependentR L)
        (_hLaw : ThetaEllipticLaw Θ L) (P : BlockVec d),
      Var[fun a => blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P); L]
        ≤ Cd * (Θ * vecNormSq P.1 + vecNormSq P.2) ^ 2
            * min 1 (Θ ^ 2 * ((3 : ℝ) ^ m) ^ (-((d : ℝ) - 2) / ((d : ℝ) - 1))) := by
  obtain ⟨Cfp, hCfp0, hfp⟩ := fixed_phase_variance_uniform (d := d) hd
  obtain ⟨Cav, hCav0, hav⟩ := exists_gridPhase_meanSq_le_uniform (d := d)
  refine ⟨16 + 2 * (2 * (Cfp + Cav)), by positivity, ?_⟩
  intro m hm Θ hΘ L _ hP hURD hLaw P
  have hΘ0 : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  set Msq : ℝ := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hMsq0 : (0 : ℝ) ≤ Msq :=
    add_nonneg (mul_nonneg hΘ0.le (vecNormSq_nonneg _)) (vecNormSq_nonneg _)
  have hMsq2 : (0 : ℝ) ≤ Msq ^ 2 := sq_nonneg _
  have hL1 : (1 : ℝ) ≤ (3 : ℝ) ^ m := one_le_zpow₀ (by norm_num) hm
  -- the coarse observable `F`, its a.s. bounds, `AESM`, and membership in `L²`
  have hFaesm : AEStronglyMeasurable
      (fun a => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)) L :=
    aestronglyMeasurable_coarseBlockQuadratic_cubeSet hP m P
  have hFbd : ∀ᵐ a ∂L,
      0 ≤ blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P) ∧
        blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P) ≤
          2 * Msq :=
    ae_coarseBlockQuadratic_bounds_of_thetaEllipticLaw hΘ hLaw m P
  have hFmem : MemLp
      (fun a => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)) 2 L := by
    refine MemLp.of_bound hFaesm (2 * Msq) ?_
    filter_upwards [hFbd] with a ha
    rw [Real.norm_eq_abs, abs_of_nonneg ha.1]; exact ha.2
  -- (deterministic) `Var[F] ≤ 4·Msq²`
  have hdet : Var[fun a => blockVecDot P
        (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P); L]
      ≤ 4 * Msq ^ 2 := by
    refine le_trans (variance_le_expectation_sq hFaesm) ?_
    have hbnd : ∀ᵐ a ∂L,
        (blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)) ^ 2
          ≤ 4 * Msq ^ 2 := by
      filter_upwards [hFbd] with a ha; nlinarith [ha.1, ha.2, hMsq0]
    refine le_trans (integral_mono_ae hFmem.integrable_sq (integrable_const _) hbnd) ?_
    rw [integral_const]; simp
  -- (two-error) `Var[F] ≤ 2(Cfp+Cav)·(Θ³(ℓ/3^m)^{d-2} + Θ/ℓ)·Msq²`
  have htwo : ∀ ℓ : ℝ, 4 ≤ ℓ → ℓ ≤ (3 : ℝ) ^ m →
      Var[fun a => blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P); L]
        ≤ 2 * (Cfp + Cav)
            * (Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2) + Θ * ℓ⁻¹) * Msq ^ 2 := by
    intro ℓ hℓ4 hℓL
    have hℓ0 : (0 : ℝ) < ℓ := by linarith
    set N : ℕ := ⌈ℓ⌉₊ with hNdef
    have hNle : (ℓ : ℝ) ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil ℓ
    obtain ⟨σ, -, havb⟩ := hav (m := m) hΘ hP hLaw hℓ4 hNle P
    set φ : Vec d := gridPhase ℓ N σ with hφdef
    -- the fixed-phase observable `G = F_σ`
    have hGaesm : AEStronglyMeasurable (fun a => phaseObservable ℓ φ m P a.toFun) L :=
      aestronglyMeasurable_phaseObservable hP m ℓ φ P
    have hGbd : ∀ᵐ a ∂L,
        0 ≤ phaseObservable ℓ φ m P a.toFun ∧ phaseObservable ℓ φ m P a.toFun ≤ 2 * Msq := by
      filter_upwards [hLaw] with a ha
      exact phaseObservable_mem_Icc hΘ P (fun i j => a.entry_measurable i j) ha
    have hGmem : MemLp (fun a => phaseObservable ℓ φ m P a.toFun) 2 L := by
      refine MemLp.of_bound hGaesm (2 * Msq) ?_
      filter_upwards [hGbd] with a ha
      rw [Real.norm_eq_abs, abs_of_nonneg ha.1]; exact ha.2
    -- projection split
    have hsplit := var_le_two_integral_add_two_var (μ := L) hFmem hGmem
    -- averaging error, rewritten to `∫(F − G)²`
    have hIeq : (∫ a, (blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)
            - phaseObservable ℓ φ m P a.toFun) ^ 2 ∂L)
        = ∫ a, |blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m))
              (corridorField ℓ φ a.toFun)) P) -
            blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)|
              ^ 2 ∂L := by
      refine integral_congr_ae ?_
      filter_upwards with a
      show (blockVecDot P (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)
          - phaseObservable ℓ φ m P a.toFun) ^ 2 = _
      rw [phaseObservable, sq_abs]; ring
    have h1 : (∫ a, (blockVecDot P
          (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)
            - phaseObservable ℓ φ m P a.toFun) ^ 2 ∂L)
        ≤ Cav * Θ * ℓ⁻¹ * Msq ^ 2 := by rw [hIeq]; exact havb
    have h2 : Var[fun a => phaseObservable ℓ φ m P a.toFun; L]
        ≤ Cfp * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2) * Msq ^ 2 :=
      hfp (m := m) (ℓ := ℓ) (Θ := Θ) (σ := φ) hℓ4 hℓL hΘ P hURD hLaw
    -- combine
    have hA0 : (0 : ℝ) ≤ Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2) := by positivity
    have hB0 : (0 : ℝ) ≤ Θ * ℓ⁻¹ := by positivity
    calc Var[fun a => blockVecDot P
            (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P); L]
        ≤ 2 * (∫ a, (blockVecDot P
              (blockMatVecMul (coarseBlockMatrix (cubeSet (originCube d m)) a.toFun) P)
                - phaseObservable ℓ φ m P a.toFun) ^ 2 ∂L)
            + 2 * Var[fun a => phaseObservable ℓ φ m P a.toFun; L] := hsplit
      _ ≤ 2 * (Cav * Θ * ℓ⁻¹ * Msq ^ 2)
            + 2 * (Cfp * Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2) * Msq ^ 2) := by
          gcongr
      _ ≤ 2 * (Cfp + Cav)
            * (Θ ^ 3 * (ℓ / (3 : ℝ) ^ m) ^ (d - 2) + Θ * ℓ⁻¹) * Msq ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg hCfp0 hB0) hMsq2,
            mul_nonneg (mul_nonneg hCav0 hA0) hMsq2]
  -- rpow optimization
  exact scalar_opt hd hΘ hL1 (by positivity) hdet htwo

end Homogenization
