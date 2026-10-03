/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch05.Theorems.Section56.SmallContrastAlgebraicDecay.ScalarRecursion

/-! # Recurrence -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch05
namespace Section56

open MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise Matrix.Norms.L2Operator

noncomputable section

namespace SmallContrastAlgebraicDecay

open SmallContrastAssembly
open Section53.JUpperBoundCoarseFluctuations

/-- Absorb the negative multiple of `F_m` in the manuscript scalar recursion. -/
theorem scalar_contraction_of_drop_bound
    {C Fm Fk S : ℝ} (hC : 0 < C) (hS : 0 ≤ S)
    (h : (1 / 4 : ℝ) * Fm ≤ C * ((Fk - Fm) + S)) :
    let θ : ℝ := (4 * C) / (1 + 4 * C)
    Fm ≤ θ * Fk + S := by
  dsimp only
  let θ : ℝ := (4 * C) / (1 + 4 * C)
  have hden_pos : 0 < 1 + 4 * C := by nlinarith
  have hmul :
      (1 + 4 * C) * Fm ≤ 4 * C * Fk + 4 * C * S := by
    nlinarith
  have hdiv :
      Fm ≤ (4 * C * Fk + 4 * C * S) / (1 + 4 * C) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
  have hdiv_eq :
      (4 * C * Fk + 4 * C * S) / (1 + 4 * C) =
        θ * Fk + θ * S := by
    dsimp [θ]
    field_simp [hden_pos.ne']
  have hθ_le_one : θ ≤ 1 := by
    dsimp [θ]
    rw [div_le_iff₀ hden_pos]
    nlinarith
  have hsource : θ * S ≤ S := by
    have hmulS := mul_le_mul_of_nonneg_right hθ_le_one hS
    simpa using hmulS
  calc
    Fm ≤ (4 * C * Fk + 4 * C * S) / (1 + 4 * C) := hdiv
    _ = θ * Fk + θ * S := hdiv_eq
    _ ≤ θ * Fk + S := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hsource (θ * Fk)

/-- The scalar recurrence obtained from Lemma `l.small.contrast.assembly`.

The constant is selected before the probability law; the only scale hypotheses
are the manuscript window `ell < k < m` and the required coarse gap. -/
theorem scalar_contraction_recursion_from_assembly
    {d : ℕ} [NeZero d]
    (params : QuantitativeCoarseGrainedEllipticityParams d) :
    ∃ C θ : ℝ, 0 < C ∧ 0 < θ ∧ θ < 1 ∧
      ∀ {P : Ch04.RestrictionCoeffLaw d}
      (hP : Ch04.RestrictionLawCarrier P)
      (hStruct : Ch04.RestrictionStructuralLaw P)
      (hP4 : QuantitativeCoarseGrainedEllipticity P),
      hP4.params = params →
      widetildeThetaAtScale P (0 : ℤ) hP4 ≤ 2 →
      ∀ e : Vec d, vecNormSq e = 1 →
      ∀ {ell k m : ℕ}, ell < k → k < m → C ≤ ((m - k : ℕ) : ℝ) →
        let β := section53CoarseFluctuationBeta hP4
        thetaAtScale hP hStruct (m : ℤ) - 1 ≤
          θ * (thetaAtScale hP hStruct (k : ℤ) - 1) +
            Real.rpow (3 : ℝ) (-β * (m : ℝ)) +
              Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ)) +
                (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ) := by
  rcases SmallContrastAssembly.smallContrastAssembly_homogenizationScale
      params with
    ⟨Casm, hCasm_pos, hAssembly⟩
  let θ : ℝ := (4 * Casm) / (1 + 4 * Casm)
  have hθ_pos : 0 < θ := by
    dsimp [θ]
    exact div_pos (by nlinarith) (by nlinarith : 0 < 1 + 4 * Casm)
  have hθ_lt_one : θ < 1 := by
    dsimp [θ]
    rw [div_lt_iff₀ (by nlinarith : 0 < 1 + 4 * Casm)]
    nlinarith
  refine ⟨Casm, θ, hCasm_pos, hθ_pos, hθ_lt_one, ?_⟩
  intro P hP hStruct hP4 hparams hsmall e he ell k m hellk hkm hgap
  dsimp only
  let β := section53CoarseFluctuationBeta hP4
  let p_e := specialPAtScale hP hStruct (m : ℤ) e
  let q_e := specialQAtScale hP hStruct (m : ℤ) e
  let J := Ch04.expectedResponseJCubeSet P (originCube d (m : ℤ)) p_e q_e
  let Fm := thetaAtScale hP hStruct (m : ℤ) - 1
  let Fk := thetaAtScale hP hStruct (k : ℤ) - 1
  let FellSq := (thetaAtScale hP hStruct (ell : ℤ) - 1) ^ (2 : ℕ)
  let tau := tauAtScale P (m : ℤ) (k : ℤ) p_e q_e
  let tail := Real.rpow (3 : ℝ) (-β * (m : ℝ))
  let geom := Real.rpow (3 : ℝ) (-(d : ℝ) * ((k - ell : ℕ) : ℝ))
  let S := tail + geom + FellSq
  have hJlower : (1 / 4 : ℝ) * Fm ≤ J := by
    simpa [J, Fm, p_e, q_e] using
      expectedResponseJCubeSet_special_ge_quarter_theta_sub_one
        hP hStruct hP4 hsmall m e he
  have hJupper_group : J ≤ Casm * (tau + S) := by
    have hJupper := hAssembly hP hStruct hP4 hparams hsmall e he hellk hkm hgap
    calc
      J ≤ Casm * tau + Casm * tail + Casm * geom + Casm * FellSq := by
        simpa [J, tau, tail, geom, FellSq, p_e, q_e, β,
          SmallContrastAssembly.smallContrastAssemblyRHSAtScale] using hJupper
      _ = Casm * (tau + S) := by
        dsimp [S]
        ring
  have htau_drop : tau ≤ Fk - Fm := by
    have h := tauAtScale_special_le_thetaAtScale_sub
      hP hStruct hP4 hkm.le e he
    simpa [tau, Fk, Fm, p_e, q_e] using h
  have hS_nonneg : 0 ≤ S := by
    have htail_nonneg : 0 ≤ tail := by
      dsimp [tail]
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hgeom_nonneg : 0 ≤ geom := by
      dsimp [geom]
      exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
    have hFellSq_nonneg : 0 ≤ FellSq := by
      dsimp [FellSq]
      exact sq_nonneg _
    dsimp [S]
    nlinarith
  have hdrop_bound : (1 / 4 : ℝ) * Fm ≤ Casm * ((Fk - Fm) + S) := by
    have hsum_le : tau + S ≤ (Fk - Fm) + S := by
      linarith
    have hmul_le :
        Casm * (tau + S) ≤ Casm * ((Fk - Fm) + S) :=
      mul_le_mul_of_nonneg_left hsum_le hCasm_pos.le
    exact hJlower.trans (hJupper_group.trans hmul_le)
  have hcontract :=
    scalar_contraction_of_drop_bound hCasm_pos hS_nonneg hdrop_bound
  dsimp [θ, Fm, Fk, S, tail, geom, FellSq, β] at hcontract ⊢
  linarith

end SmallContrastAlgebraicDecay

end

end Section56
end Ch05
end Book
end Homogenization
