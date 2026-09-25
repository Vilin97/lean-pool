/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.FinalTheorems.ExpandedAndElliptic
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarsePoincareRHS.Regularity

/-! # Zero Dirichlet Energy -/

@[expose] public section

namespace Homogenization

noncomputable section

/-!
# Zero-Dirichlet RHS energy bridge

This leaf packages the note-facing bridge between the zero-trace energy
identity and the expanded coarse-Poincare-with-RHS estimate.  The final Young
absorption is intentionally left as a separate algebraic step.
-/

open scoped ENNReal

/--
The note-facing forcing-square envelope for the coefficient energy of a
zero-trace RHS corrector.
-/
noncomputable def zeroTraceDirichletEnergyEnvelope {d : ℕ}
    (Q : TriadicCube d) (a : CoeffField d) (s : ℝ)
    (g : Vec d → Vec d) : ℝ :=
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
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2)

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

namespace ZeroTraceDirichletCorrectorData

/--
Pre-Young zero-Dirichlet energy estimate.

The coefficient energy of the zero-trace corrector is bounded by the centered
positive-Besov forcing seminorm times the square-root coarse-Poincare RHS
bound for the same corrector gradient.  This is the faithful formal socket
immediately before the manuscript's Young absorption step.
-/
theorem coefficientEnergy_average_le_centered_force_mul_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g))
    (hCenteredBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
          (fun x => g x - cubeAverageVec Q g))) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
      (d : ℝ) *
        ((3 : ℝ) ^ ((d : ℝ) + s) *
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x)) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) *
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g)) := by
  have hg_mem : MemVectorL2 (cubeSet Q) g :=
    memVectorL2_cubeSet_of_memLp_normalizedCubeMeasure Q hg
  have hρ_lp :
      MeasureTheory.MemLp
        (fun x => ρ.toH10.toH1Function.grad x)
        (2 : ENNReal) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q
      ρ.toH10.toH1Function.grad_memVectorL2
  have hρ_bdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => ρ.toH10.toH1Function.grad x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp Q hs
      (fun x => ρ.toH10.toH1Function.grad x) hρ_lp
  have hρ_poincare :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => ρ.toH10.toH1Function.grad x) ≤
        Real.sqrt
          (250 * (s⁻¹) ^ 2 *
              (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
              cubeAverage Q
                (coefficientEnergyDensity a
                  (fun x => ρ.toH10.toH1Function.grad x)) +
            15000 * (s⁻¹) ^ 4 *
              ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
              ((d : ℝ) *
                ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
              (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
    exact
      cubeBesovNegativeVectorSeminormTwo_le_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded_of_parent_potential_solenoidal
        (Q := Q) (a := a) (g := g)
        (u := fun x => ρ.toH10.toH1Function.grad x)
        (s := s) (lam := lam) (Lam := Lam)
        hs hs_le hEll ρ.toH10.toH1Function.isPotentialOn
        (ρ.residualFlux_solenoidal hEll hg_mem) hg hGlobalBdd
  have hneg :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
            (fun x => ρ.toH10.toH1Function.grad x) ≤
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x)) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
    intro N
    exact
      (cubeBesovNegativeVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s (fun x => ρ.toH10.toH1Function.grad x) hρ_bdd N).trans
        hρ_poincare
  have hCentered_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s
        (fun x => g x - cubeAverageVec Q g) :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s
      (fun x => g x - cubeAverageVec Q g) hCenteredBdd
  have hpos :
      ∀ N : ℕ,
        cubeBesovPositiveVectorPartialSeminormTwo Q s N
            (fun x => g x - cubeAverageVec Q g) ≤
          cubeBesovPositiveVectorSeminormTwo Q s
            (fun x => g x - cubeAverageVec Q g) := by
    intro N
    exact
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s (fun x => g x - cubeAverageVec Q g) hCenteredBdd N
  exact
    ρ.coefficientEnergy_average_le_collapsed_note_term_centered_two_two
      (s := s) hs hg_mem hg hρ_lp hCentered_nonneg hneg hpos

/--
Zero-Dirichlet energy estimate after the sharp Young absorption.

This turns the pre-Young energy/Poincare bridge into the note-facing sharp
envelope.  The source term remains as `2 B sqrt(F)` instead of being
over-absorbed into the larger `B^2 + F` envelope.
-/
theorem coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
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
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity a
        (fun x => ρ.toH10.toH1Function.grad x))
  let A : ℝ :=
    250 * (s⁻¹) ^ 2 *
      (lambdaSq Q (s / 2) (.finite 2) a)⁻¹
  let F : ℝ :=
    15000 * (s⁻¹) ^ 4 *
      ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
      ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
      (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2
  let B : ℝ :=
    (d : ℝ) *
      ((3 : ℝ) ^ ((d : ℝ) + s) *
        cubeBesovPositiveVectorSeminormTwo Q s g)
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
        cubeBesovPositiveVectorSeminormTwo Q s g := by
    exact cubeBesovPositiveVectorSeminormTwo_sub_const
      Q s g (cubeAverageVec Q g) hmem_desc
  have hpre_raw :=
    ρ.coefficientEnergy_average_le_centered_force_mul_sqrt_intrinsicGlobalEnergyForce_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam)
      hs hs_le hEll hg hGlobalBdd hCenteredBdd
  have hpre : E ≤ B * Real.sqrt (A * E + F) := by
    dsimp [E, A, F, B]
    calc
      cubeAverage Q
          (coefficientEnergyDensity a
            (fun x => ρ.toH10.toH1Function.grad x))
          ≤
        (d : ℝ) *
          ((3 : ℝ) ^ ((d : ℝ) + s) *
            Real.sqrt
              (250 * (s⁻¹) ^ 2 *
                  (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                  cubeAverage Q
                    (coefficientEnergyDensity a
                      (fun x => ρ.toH10.toH1Function.grad x)) +
                15000 * (s⁻¹) ^ 4 *
                  ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                  ((d : ℝ) *
                    ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                  (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) *
            cubeBesovPositiveVectorSeminormTwo Q s
              (fun x => g x - cubeAverageVec Q g)) := hpre_raw
      _ =
        (d : ℝ) *
            ((3 : ℝ) ^ ((d : ℝ) + s) *
              cubeBesovPositiveVectorSeminormTwo Q s g) *
          Real.sqrt
            (250 * (s⁻¹) ^ 2 *
                (lambdaSq Q (s / 2) (.finite 2) a)⁻¹ *
                cubeAverage Q
                  (coefficientEnergyDensity a
                    (fun x => ρ.toH10.toH1Function.grad x)) +
              15000 * (s⁻¹) ^ 4 *
                ((lambdaSq Q (s / 2) (.finite 2) a)⁻¹) ^ 2 *
                ((d : ℝ) *
                  ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
                (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2) := by
          rw [hcenter_eq]
          ring
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        hEll (fun x => ρ.toH10.toH1Function.grad x))
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
  have hBseminorm_nonneg :
      0 ≤ cubeBesovPositiveVectorSeminormTwo Q s g :=
    cubeBesovPositiveVectorSeminormTwo_nonneg_of_bddAbove Q s g hGlobalBdd
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact
      mul_nonneg (by exact_mod_cast Nat.zero_le d)
        (mul_nonneg (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
          hBseminorm_nonneg)
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
        (sq_nonneg (cubeBesovPositiveVectorSeminormTwo Q s g))
  have hmain : E ≤ B ^ 2 * A + 2 * B * Real.sqrt F :=
    le_sq_mul_add_two_mul_sqrt_of_le_mul_sqrt_mul_add
      hE_nonneg hA_nonneg hF_nonneg hB_nonneg hpre
  have hB_abs : |B| = B := abs_of_nonneg hB_nonneg
  simpa [E, A, F, B, hB_abs] using hmain

/--
Bundled version of the Young-absorbed zero-Dirichlet energy estimate using the
named forcing-square envelope.
-/
theorem coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : MeasureTheory.MemLp g (2 : ENNReal) (normalizedCubeMeasure Q))
    (hGlobalBdd :
      BddAbove (Set.range fun N : ℕ =>
        cubeBesovPositiveVectorPartialSeminormTwo Q s N g)) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
      zeroTraceDirichletEnergyEnvelope Q a s g := by
  simpa [zeroTraceDirichletEnergyEnvelope] using
    ρ.coefficientEnergy_average_le_forcing_square_envelope_noteConstants_expanded
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg hGlobalBdd

/--
Zero-Dirichlet energy estimate with the manuscript `g ∈ H^s` regularity
package, rather than separate `L²` and positive-Besov boundedness hypotheses.
-/
theorem coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded_of_cubeVectorBesovHRegularity
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (ρ : ZeroTraceDirichletCorrectorData Q a g)
    {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hg : CubeVectorBesovHRegularity Q s g) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => ρ.toH10.toH1Function.grad x)) ≤
      zeroTraceDirichletEnergyEnvelope Q a s g :=
  ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded
    (s := s) (lam := lam) (Lam := Lam)
    hs hs_le hEll hg.memLp hg.partialSeminorms_bddAbove

end ZeroTraceDirichletCorrectorData

/--
PDE-facing zero-Dirichlet energy estimate for an explicit zero-trace weak
solution, with RHS regularity supplied by the single manuscript `H^s` package.
-/
theorem coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded_of_isZeroTraceDirichletRhsWeakSolution_of_cubeVectorBesovHRegularity
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffField d}
    {g : Vec d → Vec d} (v : H10Function (cubeSet Q)) {s lam Lam : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hEll : IsEllipticFieldOn lam Lam (cubeSet Q) a)
    (hweak : IsZeroTraceDirichletRhsWeakSolution a (cubeSet Q) v g)
    (hg : CubeVectorBesovHRegularity Q s g) :
    cubeAverage Q
        (coefficientEnergyDensity a
          (fun x => v.toH1Function.grad x)) ≤
      zeroTraceDirichletEnergyEnvelope Q a s g := by
  let ρ : ZeroTraceDirichletCorrectorData Q a g := ⟨v, hweak⟩
  simpa [ρ] using
    ρ.coefficientEnergy_average_le_zeroTraceDirichletEnergyEnvelope_noteConstants_expanded_of_cubeVectorBesovHRegularity
      (s := s) (lam := lam) (Lam := Lam) hs hs_le hEll hg

end

end Homogenization
