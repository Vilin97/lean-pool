/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.HighContrast.Corridor.PhaseComparison.Averaging

/-!
# Uniform-constant grid-phase averaging

`exists_gridPhase_meanSq_le` proves the phase-comparison mean-square bound in
`∀ params, ∃ Cd, …` form.  Its witness is the explicit dimensional constant
`576·d`, so the same reproduction trick used in `FixedPhaseUniform` pulls it
outside the field quantifiers, giving `∃ Cd, ∀ params`.
-/

@[expose] public section

namespace Homogenization

open Homogenization MeasureTheory ProbabilityTheory
open Homogenization.Book.Ch04 (RestrictionCoeffLaw RestrictionLawCarrier)

variable {d : ℕ}

/-- **Uniform-constant grid-phase averaging.**  The constant `Cd = 576·d` is
independent of `Θ, L, m, ℓ, N, P`. -/
theorem exists_gridPhase_meanSq_le_uniform [NeZero d] :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ {Θ : ℝ} (_hΘ : 1 ≤ Θ) {L : RestrictionCoeffLaw d} (_hP : RestrictionLawCarrier L)
        (_hell : ThetaEllipticLaw Θ L) {m : ℤ} {ℓ : ℝ} (_hℓ : 4 ≤ ℓ) {N : ℕ}
        (_hN : (ℓ : ℝ) ≤ (N : ℝ)) (P : BlockVec d),
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
  refine ⟨576 * (d : ℝ), by positivity, ?_⟩
  intro Θ hΘ L hP hell m ℓ hℓ N hN P
  have : IsProbabilityMeasure L := hP.isProbability
  set Msq := Θ * vecNormSq P.1 + vecNormSq P.2 with hMsqdef
  have hΘpos : (0 : ℝ) < Θ := lt_of_lt_of_le one_pos hΘ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith
  have hN0 : (0 : ℝ) < (N : ℝ) := lt_of_lt_of_le hℓ0 hN
  have hNpow0 : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  set B := 576 * (d : ℝ) * Θ * (N : ℝ) ^ d * Msq ^ 2 / ℓ with hBdef
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
  have hcard : (Finset.univ : Finset (Fin d → Fin N)).card = N ^ d := by
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  have hne : (Finset.univ : Finset (Fin d → Fin N)).Nonempty := by
    have hNpos : 0 < N := by exact_mod_cast hN0
    have : Nonempty (Fin N) := ⟨⟨0, hNpos⟩⟩
    exact Finset.univ_nonempty
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
