/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ExpandedAndElliptic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.CorrectorEnergy

/-! # Corrector Energy Poincare -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Corrector energy from the RHS Poincare estimate

This leaf closes the manuscript Step 3.2.3 estimate for the local mean-zero
Neumann corrector: the centered energy identity gives `E <= C W G`, the
RHS Poincare estimate bounds `W`, and a scalar Young absorption returns a
forcing-square envelope with the expected `lambda_{s/2,2}^{-1}` factor.
-/

open scoped ENNReal

namespace MeanZeroNeumannCorrectorData

variable {d : ℕ} {Q : TriadicCube d} {a : CoeffField d} {g : Vec d → Vec d}

private theorem le_sq_mul_add_two_mul_sqrt_of_le_mul_sqrt_mul_add
    {E A F B : ℝ}
    (hE_nonneg : 0 ≤ E) (hA_nonneg : 0 ≤ A)
    (hF_nonneg : 0 ≤ F) (hB_nonneg : 0 ≤ B)
    (h : E ≤ B * Real.sqrt (A * E + F)) :
    E ≤ B ^ 2 * A + 2 * B * Real.sqrt F := by
  have hAE_nonneg : 0 ≤ A * E := mul_nonneg hA_nonneg hE_nonneg
  have hsqrt_split :
      Real.sqrt (A * E + F) ≤ Real.sqrt (A * E) + Real.sqrt F :=
    sqrt_add_le_add_sqrt_of_nonneg hAE_nonneg hF_nonneg
  have hsplit :
      E ≤ B * Real.sqrt (A * E) + B * Real.sqrt F := by
    calc
      E ≤ B * Real.sqrt (A * E + F) := h
      _ ≤ B * (Real.sqrt (A * E) + Real.sqrt F) := by
          exact mul_le_mul_of_nonneg_left hsqrt_split hB_nonneg
      _ = B * Real.sqrt (A * E) + B * Real.sqrt F := by ring
  have hyoung_left :
      B * Real.sqrt (A * E) ≤ E / 2 + (B ^ 2 * A) / 2 := by
    rw [Real.sqrt_mul hA_nonneg E]
    have htwo :=
      two_mul_le_add_sq (B * Real.sqrt A) (Real.sqrt E)
    have hsqA : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA_nonneg
    have hsqE : (Real.sqrt E) ^ 2 = E := Real.sq_sqrt hE_nonneg
    nlinarith
  calc
    E ≤ B * Real.sqrt (A * E) + B * Real.sqrt F := hsplit
    _ ≤ E / 2 + (B ^ 2 * A) / 2 + B * Real.sqrt F := by
        nlinarith
    _ ≤ B ^ 2 * A + 2 * B * Real.sqrt F := by
        nlinarith

/--
Pre-Young Neumann-corrector energy estimate.

The coefficient energy of the centered mean-zero Neumann corrector is bounded
by the centered positive-Besov forcing seminorm times the square root of the
RHS Poincare radicand for the same corrector gradient.
-/
theorem coefficientEnergy_average_le_centered_force_mul_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded
    [NeZero d]
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hCenteredBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ω.toH1MeanZero.toH1Function.grad x)) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s
                  (fun x => g x - cubeAverageVec Q g)) ^ 2) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  let gCentered : Vec d → Vec d := fun x => g x - cubeAverageVec Q g
  have hg_mem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  have hg_centered :
      MeasureTheory.MemLp gCentered (2 : ENNReal) (normalizedCubeMeasure Q) := by
    have hconst :
        MeasureTheory.MemLp (fun _ : Vec d => cubeAverageVec Q g)
          (2 : ENNReal) (normalizedCubeMeasure Q) :=
      MeasureTheory.memLp_const (cubeAverageVec Q g)
    simpa [gCentered] using! hg.sub hconst
  have hg_centered_mem : MemVectorL2 (cubeSet Q) gCentered :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg_centered
  have hgradω :
      MeasureTheory.MemLp ωgrad (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ω.toH1MeanZero.toH1Function.grad_memVectorL2
  have hω_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N ωgrad) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      ωgrad hgradω
  have hω_residual :
      IsSolenoidalOn (cubeSet Q)
        (fun x => matVecMul (a x) (ωgrad x) - gCentered x) := by
    simpa [ωgrad, gCentered] using
      (ω.residualFlux_zeroNormalTrace hEll hg_centered_mem).isSolenoidalOn
  have hω_poincare :
      cubeBesovNegativeVectorSeminormTwo Q s ωgrad ≤
        Real.sqrt
          (250 * (s⁻¹) ^ 2 *
              (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              cubeAverage Q
                (coefficientEnergyDensity a ωgrad) +
            15000 * (s⁻¹) ^ 4 *
              ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              ((d : ℝ) *
                ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s gCentered) ^ 2) := by
    exact
      cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
        (Q := Q) (a := a) (g := gCentered) (u := ωgrad)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEll ω.toH1MeanZero.toH1Function.isPotentialOn
        hω_residual hg_centered hCenteredBdd
  have hneg :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N ωgrad ≤
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a ωgrad) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s gCentered) ^ 2) := by
    intro N
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s ωgrad hω_bdd N).trans hω_poincare
  have hCentered_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s gCentered :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s
      gCentered hCenteredBdd
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N gCentered ≤
          cubeBesovPositiveVectorSeminormTwo Q s gCentered := by
    intro N
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s gCentered hCenteredBdd N
  simpa [ωgrad, gCentered] using
    ω.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
      (s := s) hs hg_mem hg hgradω hCentered_nonneg hneg hpos

/--
Young-absorbed Neumann-corrector energy estimate with the centered forcing
seminorm kept explicit.
-/
theorem coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded_centered
    [NeZero d]
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hCenteredBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      ((d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g))) ^ 2 *
        (250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
      2 *
        |(d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g))| *
        Real.sqrt
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
  let ωgrad : Vec d → Vec d := fun x => ω.toH1MeanZero.toH1Function.grad x
  let gCentered : Vec d → Vec d := fun x => g x - cubeAverageVec Q g
  let E : ℝ := cubeAverage Q (coefficientEnergyDensity a ωgrad)
  let A : ℝ :=
    250 * (s⁻¹) ^ 2 * (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let F : ℝ :=
    15000 * (s⁻¹) ^ 4 *
      ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s gCentered) ^ 2
  let B : ℝ :=
    (d : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + s) *
        cubeBesovPositiveVectorSeminormTwo Q s gCentered)
  have hpre_raw :=
    ω.coefficientEnergy_average_le_centered_force_mul_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hg hCenteredBdd
  have hpre : E ≤ B * Real.sqrt (A * E + F) := by
    dsimp [E, A, F, B, ωgrad, gCentered]
    calc
      cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ω.toH1MeanZero.toH1Function.grad x))
          ≤
        (d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            Real.sqrt
              (250 * (s⁻¹) ^ 2 *
                  (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage Q
                    (coefficientEnergyDensity a
                      (fun x => ω.toH1MeanZero.toH1Function.grad x)) +
                15000 * (s⁻¹) ^ 4 *
                  ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                  ((d : ℝ) *
                    ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                  (cubeBesovPositiveVectorSeminormTwo Q s
                    (fun x => g x - cubeAverageVec Q g)) ^ 2) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g)) := hpre_raw
      _ =
        (d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g)) *
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ω.toH1MeanZero.toH1Function.grad x)) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s
                  (fun x => g x - cubeAverageVec Q g)) ^ 2) := by
          ring
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, ωgrad]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        hEll (fun x => ω.toH1MeanZero.toH1Function.grad x))
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hlambda_inv_nonneg :
      0 ≤ (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ :=
    inv_nonneg.mpr hlambda_nonneg
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact
      mul_nonneg
        (mul_nonneg (by norm_num : 0 ≤ (250 : ℝ)) (sq_nonneg (s⁻¹)))
        hlambda_inv_nonneg
  have hG_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s gCentered :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s
      gCentered hCenteredBdd
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le d)
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
          hG_nonneg)
  have hF_nonneg : 0 ≤ F := by
    have hs_inv_pow_four_nonneg : 0 ≤ (s⁻¹) ^ 4 := by
      rw [show (s⁻¹) ^ 4 = ((s⁻¹) ^ 2) ^ 2 by ring]
      exact sq_nonneg _
    dsimp [F]
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (by norm_num : 0 ≤ (15000 : ℝ)) hs_inv_pow_four_nonneg)
            (sq_nonneg ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹)))
          (sq_nonneg ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2))))
        (sq_nonneg (cubeBesovPositiveVectorSeminormTwo Q s gCentered))
  have hmain : E ≤ B ^ 2 * A + 2 * B * Real.sqrt F :=
    le_sq_mul_add_two_mul_sqrt_of_le_mul_sqrt_mul_add
      hE_nonneg hA_nonneg hF_nonneg hB_nonneg hpre
  have hB_abs : |B| = B := abs_of_nonneg hB_nonneg
  simpa [E, A, F, B, ωgrad, gCentered, hB_abs] using hmain

/--
Young-absorbed Neumann-corrector energy estimate with the uncentered forcing
seminorm, using the standard invariance of the positive Besov seminorm under
subtracting the cube average.
-/
theorem coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded
    [NeZero d]
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      ((d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovPositiveVectorSeminormTwo Q s g)) ^ 2 *
        (250 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹) +
      2 *
        |(d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            cubeBesovPositiveVectorSeminormTwo Q s g)| *
        Real.sqrt
          (15000 * (s⁻¹) ^ 4 *
            ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
            ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
            (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
  have hmem_desc :
      ∀ j : ℕ, ∀ R ∈ descendantsAtDepth Q j,
        MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure R) := by
    intro j R hR
    exact memLp_on_descendant_of_memLp_generic (E := Vec d) hR hg
  have hCenteredBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g)) := by
    rcases hGlobalBdd with ⟨M, hM⟩
    refine ⟨M, ?_⟩
    rintro y ⟨N, rfl⟩
    change
      cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g) ≤
        M
    rw [cubeBesovPositiveVectorPartialSeminormTwo_sub_const
      Q s N g (cubeAverageVec Q g) (fun j _ R hR => hmem_desc j R hR)]
    exact hM ⟨N, rfl⟩
  have hcenter_eq :
      cubeBesovPositiveVectorSeminormTwo Q s
          (fun x => g x - cubeAverageVec Q g) =
        cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_sub_const
      Q s g (cubeAverageVec Q g) hmem_desc
  have hcentered :=
    ω.coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded_centered
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hCenteredBdd
  simpa [hcenter_eq] using hcentered

/--
Single-scale force-form consequence of the Young-absorbed Neumann-corrector
energy estimate.

This is the local scalar estimate needed before averaging the corrector-energy
component over descendants: the two terms in the Young envelope are both
absorbed into the same `s^{-2} lambda^{-1} N^2 [g]^2` scale.
-/
theorem coefficientEnergy_average_le_force_scale_noteConstants_expanded
    [NeZero d]
    (ω : MeanZeroNeumannCorrectorData Q a (fun x => g x - cubeAverageVec Q g))
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x)) ≤
      500 * (s⁻¹) ^ 2 *
        (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let G : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let L : ℝ := (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let M : ℝ := (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)
  let N : ℝ := M * Real.sqrt 2
  let A : ℝ := 250 * (s⁻¹) ^ 2 * L
  let F : ℝ :=
    15000 * (s⁻¹) ^ 4 *
      ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      G ^ 2
  let B : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * G)
  have hmain :=
    ω.coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd
  have hlambda_nonneg :
      0 ≤ lambdaSq Q (s / 2) (.finite 2) a :=
    multiscale_ellipticity_lambdaSq_finite_nonneg Q (s / 2) 2 a
      (by norm_num) (by nlinarith : 0 ≤ s / 2 * (2 : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact inv_nonneg.mpr hlambda_nonneg
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le d)
        (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hsqrt2_ge_one : 1 ≤ Real.sqrt 2 := by
    have hsqrt2_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
    have hsqrt2_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact mul_nonneg hM_nonneg (Real.sqrt_nonneg 2)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le d)
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
          hG_nonneg)
  have hB_abs : |B| = B := abs_of_nonneg hB_nonneg
  have hB_le_NG : B ≤ N * G := by
    dsimp [B, N, M]
    have hscale : M ≤ M * Real.sqrt 2 := by
      calc
        M = M * 1 := by ring
        _ ≤ M * Real.sqrt 2 :=
          mul_le_mul_of_nonneg_left hsqrt2_ge_one hM_nonneg
    calc
      (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * G)
          = ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) * G := by ring
      _ ≤ (((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s)) * Real.sqrt 2) * G :=
          mul_le_mul_of_nonneg_right hscale hG_nonneg
      _ =
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) * G := by ring
      _ = (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2 * G := by ring
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    positivity
  let K : ℝ := 125 * (s⁻¹) ^ 2 * L * N * G
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsqrtF :
      Real.sqrt F ≤ K := by
    have hF_le_K_sq : F ≤ K ^ 2 := by
      dsimp [F, K, L, N, M]
      have hs_inv_four : (s⁻¹) ^ 4 = ((s⁻¹) ^ 2) ^ 2 := by ring
      rw [hs_inv_four]
      have hnonneg :
          0 ≤
            ((s⁻¹) ^ 2) ^ 2 *
              ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              (((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2) *
              G ^ 2 := by
        positivity
      nlinarith [hnonneg]
    refine le_of_sq_le_sq ?_ hK_nonneg
    simpa [Real.sq_sqrt hF_nonneg] using hF_le_K_sq
  have hterm1 :
      B ^ 2 * A ≤ 250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    have hB_sq :
        B ^ 2 ≤ (N * G) ^ 2 := by
      exact pow_le_pow_left₀ hB_nonneg hB_le_NG 2
    calc
      B ^ 2 * A ≤ (N * G) ^ 2 * A :=
        mul_le_mul_of_nonneg_right hB_sq hA_nonneg
      _ = 250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
        dsimp [A]
        ring
  have hterm2 :
      2 * |B| * Real.sqrt F ≤
        250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
    calc
      2 * |B| * Real.sqrt F ≤ 2 * (N * G) * K := by
        rw [hB_abs]
        have hleft_nonneg : 0 ≤ 2 * B := by positivity
        have hBmul : 2 * B ≤ 2 * (N * G) := by nlinarith
        have hNG_nonneg : 0 ≤ N * G := mul_nonneg hN_nonneg hG_nonneg
        calc
          2 * B * Real.sqrt F ≤ 2 * B * K :=
            mul_le_mul_of_nonneg_left hsqrtF hleft_nonneg
          _ ≤ 2 * (N * G) * K :=
            mul_le_mul_of_nonneg_right hBmul hK_nonneg
      _ = 250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by
        dsimp [K]
        ring
  calc
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ω.toH1MeanZero.toH1Function.grad x))
        ≤ B ^ 2 * A + 2 * |B| * Real.sqrt F := by
          simpa [A, B, F, G, L] using hmain
    _ ≤
        250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 +
          250 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 :=
        add_le_add hterm1 hterm2
    _ =
        500 * (s⁻¹) ^ 2 * L * N ^ 2 * G ^ 2 := by ring
    _ =
        500 * (s⁻¹) ^ 2 *
          (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
        dsimp [L, N, M, G]
        ring

end MeanZeroNeumannCorrectorData

end

end Homogenization
