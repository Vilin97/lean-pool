/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.EnergyRHS.DirichletSplit

/-! # Harmonic Remainder -/

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Energy RHS: Harmonic remainder estimates
-/

noncomputable section

open scoped ENNReal

private theorem sqrt_two_mul_le_of_le_mul_sqrt {E K : ℝ}
    (hE : 0 ≤ E) (hK : 0 ≤ K) (h : E ≤ K * Real.sqrt E) :
    Real.sqrt (2 * E) ≤ Real.sqrt 2 * K := by
  let x : ℝ := Real.sqrt E
  have hx_nonneg : 0 ≤ x := by
    dsimp [x]
    exact Real.sqrt_nonneg E
  have hx_sq : x ^ 2 = E := by
    dsimp [x]
    exact Real.sq_sqrt hE
  have hx_le_K : x ≤ K := by
    by_cases hx_zero : x = 0
    · simpa [hx_zero] using hK
    · have hx_pos : 0 < x := lt_of_le_of_ne hx_nonneg (Ne.symm hx_zero)
      by_contra hx_not_le
      have hK_lt_x : K < x := lt_of_not_ge hx_not_le
      have hmul_lt : K * x < x * x :=
        mul_lt_mul_of_pos_right hK_lt_x hx_pos
      have hmul_le : x * x ≤ K * x := by
        have h' : x ^ 2 ≤ K * x := by
          rw [hx_sq]
          simpa [x] using h
        simpa [pow_two] using h'
      exact (not_lt_of_ge hmul_le) hmul_lt
  calc
    Real.sqrt (2 * E)
        = Real.sqrt 2 * x := by
          rw [show 2 * E = 2 * x ^ 2 by rw [hx_sq]]
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          rw [Real.sqrt_sq hx_nonneg]
    _ ≤ Real.sqrt 2 * K :=
        mul_le_mul_of_nonneg_left hx_le_K (Real.sqrt_nonneg 2)

private theorem sqrt_two_energy_le_scaled_rhs_of_pairing
    {E Cpair Cflux C S P B : ℝ}
    (hE_nonneg : 0 ≤ E) (hS_nonneg : 0 ≤ S) (hP_nonneg : 0 ≤ P)
    (hB_nonneg : 0 ≤ B) (hCpair_nonneg : 0 ≤ Cpair)
    (hCflux_nonneg : 0 ≤ Cflux)
    (hC_absorb : Real.sqrt 2 * Cpair * Cflux ≤ C)
    (hpairing :
      E ≤ (Cpair * (Cflux * S * P) * B) * Real.sqrt E) :
    Real.sqrt (2 * E) ≤ C * S * P * B := by
  let K : ℝ := Cpair * (Cflux * S * P) * B
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg
      (mul_nonneg hCpair_nonneg
        (mul_nonneg (mul_nonneg hCflux_nonneg hS_nonneg) hP_nonneg))
      hB_nonneg
  have hcancel : Real.sqrt (2 * E) ≤ Real.sqrt 2 * K :=
    sqrt_two_mul_le_of_le_mul_sqrt hE_nonneg hK_nonneg (by simpa [K] using hpairing)
  have hSPB_nonneg : 0 ≤ S * P * B :=
    mul_nonneg (mul_nonneg hS_nonneg hP_nonneg) hB_nonneg
  have habsorb_scaled :
      (Real.sqrt 2 * Cpair * Cflux) * (S * P * B) ≤
        C * (S * P * B) :=
    mul_le_mul_of_nonneg_right hC_absorb hSPB_nonneg
  calc
    Real.sqrt (2 * E) ≤ Real.sqrt 2 * K := hcancel
    _ = (Real.sqrt 2 * Cpair * Cflux) * (S * P * B) := by
        dsimp [K]
        ring
    _ ≤ C * (S * P * B) := habsorb_scaled
    _ = C * S * P * B := by
        ring

private theorem geometricDiscount_two_rpow_neg_half_le_sqrt_five_mul_rpow_neg_half
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) :
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) ≤
      Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ) := by
  have hgd_pos : 0 < geometricDiscount s 2 :=
    geometricDiscount_pos (by nlinarith)
  have hleft_sq :
      (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 =
        (geometricDiscount s 2)⁻¹ := by
    simpa using
      (sq_rpow_neg_half_eq_inv_of_nonneg (le_of_lt hgd_pos))
  have hright_sq :
      (Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ)) ^ 2 =
        5 * s⁻¹ := by
    calc
      (Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ)) ^ 2 =
          (Real.sqrt 5) ^ 2 * (Real.rpow s (-1 / 2 : ℝ)) ^ 2 := by
        ring
      _ = 5 * s⁻¹ := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
        rw [show (Real.rpow s (-1 / 2 : ℝ)) ^ 2 = s⁻¹ by
          simpa using sq_rpow_neg_half_eq_inv_of_nonneg hs.le]
  have hsq :
      (Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)) ^ 2 ≤
        (Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ)) ^ 2 := by
    rw [hleft_sq, hright_sq]
    exact inv_geometricDiscount_two_le_five_inv hs hs_le
  exact le_of_sq_le_sq hsq
    (mul_nonneg (Real.sqrt_nonneg 5) (Real.rpow_nonneg hs.le _))

private theorem geometricDiscount_two_mul_sqrt_LambdaSqFinite_public_le_dim_publicUpper
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s E : ℝ} (hs : 0 < s) :
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        Real.rpow (LambdaSqFinite Q s 2 (publicCoeffField Q a)) ((2 : ℝ)⁻¹) *
        Real.sqrt E ≤
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        ((d : ℝ) * poincareUpperEllipticityFactor Q a s (.finite 2)) *
        Real.sqrt E := by
  have hP_old_le :
      Real.rpow (LambdaSqFinite Q s 2 (publicCoeffField Q a)) ((2 : ℝ)⁻¹) ≤
        (d : ℝ) * poincareUpperEllipticityFactor Q a s (.finite 2) := by
    simpa [Real.sqrt_eq_rpow, one_div] using
      sqrt_LambdaSq_publicCoeffField_finite_two_le_dim_mul_poincareUpperEllipticityFactor
        Q a hs
  have hG_nonneg :
      0 ≤ Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) :=
    Real.rpow_nonneg (geometricDiscount_pos (by nlinarith)).le _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP_old_le hG_nonneg)
    (Real.sqrt_nonneg E)

private theorem geometricDiscount_two_scale_mul_publicUpper_le
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffFamily d)
    {s E : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) :
    Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) *
        ((d : ℝ) * poincareUpperEllipticityFactor Q a s (.finite 2)) *
        Real.sqrt E ≤
      (Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ)) *
        ((d : ℝ) * poincareUpperEllipticityFactor Q a s (.finite 2)) *
        Real.sqrt E := by
  have hG_le :
      Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ) ≤
        Real.sqrt 5 * Real.rpow s (-1 / 2 : ℝ) :=
    geometricDiscount_two_rpow_neg_half_le_sqrt_five_mul_rpow_neg_half hs hs_le
  have hP_nonneg : 0 ≤ poincareUpperEllipticityFactor Q a s (.finite 2) := by
    dsimp [poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 2)) _
  have htail_nonneg :
      0 ≤ ((d : ℝ) * poincareUpperEllipticityFactor Q a s (.finite 2)) *
          Real.sqrt E :=
    mul_nonneg
      (mul_nonneg (by exact_mod_cast Nat.zero_le d) hP_nonneg)
      (Real.sqrt_nonneg E)
  have h := mul_le_mul_of_nonneg_right hG_le htail_nonneg
  simpa [mul_assoc] using h

private theorem abs_vecDot_le_sqrt_vecNormSq_mul_sqrt_vecNormSq {d : ℕ}
    (x y : Vec d) :
    |vecDot x y| ≤ Real.sqrt (vecNormSq x) * Real.sqrt (vecNormSq y) := by
  let A : ℝ := vecNormSq x
  let B : ℝ := vecNormSq y
  have hA : 0 ≤ A := by
    simpa [A] using vecNormSq_nonneg x
  have hB : 0 ≤ B := by
    simpa [B] using vecNormSq_nonneg y
  have hsq : (vecDot x y) ^ 2 ≤ A * B := by
    simpa [A, B] using sq_vecDot_le_vecNormSq_mul_vecNormSq x y
  have habs_sq :
      |vecDot x y| ^ 2 ≤ (Real.sqrt A * Real.sqrt B) ^ 2 := by
    calc
      |vecDot x y| ^ 2 = (vecDot x y) ^ 2 := by
        simp [sq_abs]
      _ ≤ A * B := hsq
      _ = (Real.sqrt A * Real.sqrt B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA, Real.sq_sqrt hB]
  exact le_of_sq_le_sq habs_sq
    (mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B))

private theorem sqrt_vecNormSq_cubeAverageVec_le_negativePartial_zero
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (F : Vec d → Vec d) :
    Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤
      cubeBesovNegativeVectorPartialSeminormTwo Q s 0 F := by
  have hsq :
      (Real.sqrt (vecNormSq (cubeAverageVec Q F))) ^ 2 ≤
        (cubeBesovNegativeVectorPartialSeminormTwo Q s 0 F) ^ 2 := by
    rw [Real.sq_sqrt (vecNormSq_nonneg _)]
    rw [sq_cubeBesovNegativeVectorPartialSeminormTwo]
    simp [sq_cubeBesovNegativeVectorDepthSeminorm_depth_zero]
  exact le_of_sq_le_sq hsq
    (cubeBesovNegativeVectorPartialSeminormTwo_nonneg Q s 0 F)


/-- Boundary harmonic-remainder energy from the two quantitative inputs used
in the manuscript: the weak-testing/Besov-duality pairing and the homogeneous
coarse-grained flux estimate.  This deliberately keeps the route through
`poincareUpperEllipticityFactor` and contains no raw `Lam` absorption. -/
theorem dirichletHarmonicRemainder_sqrt_two_energy_le_of_boundary_pairing_and_flux_bound
    {d : ℕ} [NeZero d] {C Cpair Cflux : ℝ}
    (hCpair_nonneg : 0 ≤ Cpair) (hCflux_nonneg : 0 ≤ Cflux)
    (hC_absorb : Real.sqrt 2 * Cpair * Cflux ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hpairing :
      cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x)) ≤
        Cpair *
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v))
    (hflux :
      cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) ≤
        Cflux * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2) *
          Real.sqrt
            (cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (fun x => w.toH1.grad x)))) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => w.toH1.grad x))
  let N : ℝ :=
    cubeBesovNegativeVectorSeminormTwo Q s
      (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
  let S : ℝ := Real.rpow s (-(1 / 2 : ℝ))
  let P : ℝ := poincareUpperEllipticityFactor Q a s (.finite 2)
  let B : ℝ :=
    scaleNormalizedPositiveBesovVectorNormTwo Q s
      (dirichletBoundaryGradientField v)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => w.toH1.grad x))
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg hs.le _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 2)) _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := dirichletBoundaryGradientField v) hboundary)
  have hflux' : N ≤ Cflux * S * P * Real.sqrt E := by
    simpa [N, S, P, E] using hflux
  have hpairing_scaled :
      E ≤ (Cpair * (Cflux * S * P) * B) * Real.sqrt E := by
    have hstep :
        Cpair * N * B ≤ Cpair * (Cflux * S * P * Real.sqrt E) * B :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hflux' hCpair_nonneg) hB_nonneg
    calc
      E ≤ Cpair * N * B := by
        simpa [E, N, B] using hpairing
      _ ≤ Cpair * (Cflux * S * P * Real.sqrt E) * B := hstep
      _ = (Cpair * (Cflux * S * P) * B) * Real.sqrt E := by
        ring
  have hscaled : Real.sqrt (2 * E) ≤ C * S * P * B :=
    sqrt_two_energy_le_scaled_rhs_of_pairing hE_nonneg hS_nonneg hP_nonneg
      hB_nonneg hCpair_nonneg hCflux_nonneg hC_absorb hpairing_scaled
  calc
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x)))
        = Real.sqrt (2 * E) := by
          rfl
    _ ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
        simpa [S, P, B] using hscaled

/-- Public wrapper for the homogeneous flux half of the notes' Dirichlet
harmonic-remainder proof.  It applies the deterministic `q = 2` coarse
Poincare theorem to the public coefficient representative, rewrites
`Λ_{s,2}^{1/2}` into `poincareUpperEllipticityFactor`, and absorbs the
geometric discount into the displayed `s^(-1/2)` scale loss. -/
theorem dirichletHarmonicRemainder_fluxSeminorm_le_poincareUpperEllipticityFactor
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1) :
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) ≤
      ((d : ℝ) * Real.sqrt 5) * Real.rpow s (-1 / 2 : ℝ) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        Real.sqrt
          (cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) := by
  let A : CoeffField d := publicCoeffField Q a
  let N : ℝ :=
    cubeBesovNegativeVectorSeminormTwo Q s
      (fun x => matVecMul (A x) (w.toH1.grad x))
  let G : ℝ := Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)
  let S : ℝ := Real.rpow s (-1 / 2 : ℝ)
  let P : ℝ := poincareUpperEllipticityFactor Q a s (.finite 2)
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity A (fun x => w.toH1.grad x))
  have hdet :=
    (coarsePoincare_qtwo_note_bounds_of_aHarmonicFunction
      (Q := Q) (a := A) (s := s) hs
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) w).2
  have henergy_eq :
      cubeAverage Q (fun x => scalarVariationEnergyIntegrand A w x) = E := by
    change cubeAverage Q (coefficientEnergyDensity A (fun x => w.toH1.grad x)) = E
    rfl
  have hdet_finite :
      N ≤ G * Real.rpow (LambdaSqFinite Q s 2 A) ((2 : ℝ)⁻¹) *
        Real.sqrt E := by
    simpa [N, G, E, henergy_eq, LambdaSq, one_div] using hdet
  have hdet' : N ≤ G * ((d : ℝ) * P) * Real.sqrt E := by
    calc
      N ≤ G * Real.rpow (LambdaSqFinite Q s 2 A) ((2 : ℝ)⁻¹) *
          Real.sqrt E := hdet_finite
      _ ≤ G * ((d : ℝ) * P) * Real.sqrt E := by
        simpa [A, G, P] using
          geometricDiscount_two_mul_sqrt_LambdaSqFinite_public_le_dim_publicUpper
            (Q := Q) (a := a) (s := s) (E := E) hs
  have hscale :
      G * ((d : ℝ) * P) * Real.sqrt E ≤
        (Real.sqrt 5 * S) * ((d : ℝ) * P) * Real.sqrt E := by
    simpa [G, S, P] using
      geometricDiscount_two_scale_mul_publicUpper_le (Q := Q) (a := a)
        (s := s) (E := E) hs hs_le
  calc
    cubeBesovNegativeVectorSeminormTwo Q s
        (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
        = N := by
          rfl
    _ ≤ G * ((d : ℝ) * P) * Real.sqrt E := hdet'
    _ ≤ (Real.sqrt 5 * S) * ((d : ℝ) * P) * Real.sqrt E := hscale
    _ =
      ((d : ℝ) * Real.sqrt 5) * Real.rpow s (-1 / 2 : ℝ) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        Real.sqrt
          (cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) := by
        dsimp [S, P, E, A]
        ring

/-- Finite-depth public wrapper for the homogeneous flux half of the
Dirichlet harmonic-remainder proof.  This is the partial-norm version consumed
by the Besov-duality pairing theorem. -/
theorem dirichletHarmonicRemainder_fluxPartialSeminorm_le_poincareUpperEllipticityFactor
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (N : ℕ) (hs : 0 < s) (hs_le : s ≤ 1) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) ≤
      ((d : ℝ) * Real.sqrt 5) * Real.rpow s (-1 / 2 : ℝ) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        Real.sqrt
          (cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) := by
  let A : CoeffField d := publicCoeffField Q a
  let flux : Vec d → Vec d := fun x => matVecMul (A x) (w.toH1.grad x)
  let energy : Vec d → ℝ := fun x => scalarVariationEnergyIntegrand A w x
  let G : ℝ := Real.rpow (geometricDiscount s 2) (-1 / 2 : ℝ)
  let S : ℝ := Real.rpow s (-1 / 2 : ℝ)
  let P : ℝ := poincareUpperEllipticityFactor Q a s (.finite 2)
  let E : ℝ :=
    cubeAverage Q (coefficientEnergyDensity A (fun x => w.toH1.grad x))
  let hOrigin : OpenCubeOriginEllipticRecoveryExistence (d := d)
      (a.coeffOn Q).lam (a.coeffOn Q).Lam :=
    openCubeOriginEllipticRecoveryExistence (d := d)
      (lam := (a.coeffOn Q).lam) (Lam := (a.coeffOn Q).Lam)
  have hsum_flux :=
    summable_qtwo_maxDescendantBBlockNormAtScale_of_isEllipticFieldOn_of_openCubeOriginEllipticRecoveryExistence
      (Q := Q) (a := A) s hs (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
      hOrigin
  have hdet :=
    coarsePoincare_flux_qtwo_partial_of_cubeAverageEnergyControl
      (Q := Q) (a := A) (s := s) hs (flux := flux) (energy := energy) (N := N)
      (scalarVariationEnergyIntegrand_nonneg_of_isEllipticFieldOn (cubeSet Q) A
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a) w)
      (ResponseLinearIntegrabilityData.energy
        (ResponseLinearIntegrabilityData.of_isEllipticFieldOn
          (publicCoeffField_isEllipticFieldOn_cubeSet Q a)) w)
      (cubeAverageFluxEnergyControl_of_aHarmonicFunction_of_openCubeOriginEllipticRecoveryExistence
        (Q := Q) (a := A) (publicCoeffField_isEllipticFieldOn_cubeSet Q a) w hOrigin)
      hsum_flux
  have henergy_eq : cubeAverage Q energy = E := by
    change cubeAverage Q (coefficientEnergyDensity A (fun x => w.toH1.grad x)) = E
    rfl
  have hdet_finite :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤
        G * Real.rpow (LambdaSqFinite Q s 2 A) ((2 : ℝ)⁻¹) * Real.sqrt E := by
    simpa [flux, energy, G, E, henergy_eq, LambdaSq, one_div] using hdet
  have hdet' :
      cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤
        G * ((d : ℝ) * P) * Real.sqrt E := by
    calc
      cubeBesovNegativeVectorPartialSeminormTwo Q s N flux ≤
          G * Real.rpow (LambdaSqFinite Q s 2 A) ((2 : ℝ)⁻¹) * Real.sqrt E :=
            hdet_finite
      _ ≤ G * ((d : ℝ) * P) * Real.sqrt E := by
        simpa [A, G, P] using
          geometricDiscount_two_mul_sqrt_LambdaSqFinite_public_le_dim_publicUpper
            (Q := Q) (a := a) (s := s) (E := E) hs
  have hscale :
      G * ((d : ℝ) * P) * Real.sqrt E ≤
        (Real.sqrt 5 * S) * ((d : ℝ) * P) * Real.sqrt E := by
    simpa [G, S, P] using
      geometricDiscount_two_scale_mul_publicUpper_le (Q := Q) (a := a)
        (s := s) (E := E) hs hs_le
  calc
    cubeBesovNegativeVectorPartialSeminormTwo Q s N
        (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
        = cubeBesovNegativeVectorPartialSeminormTwo Q s N flux := by
          rfl
    _ ≤ G * ((d : ℝ) * P) * Real.sqrt E := hdet'
    _ ≤ (Real.sqrt 5 * S) * ((d : ℝ) * P) * Real.sqrt E := hscale
    _ =
      ((d : ℝ) * Real.sqrt 5) * Real.rpow s (-1 / 2 : ℝ) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        Real.sqrt
          (cubeAverage Q
            (coefficientEnergyDensity (publicCoeffField Q a)
              (fun x => w.toH1.grad x))) := by
        dsimp [S, P, E, A]
        ring

/-- Weak testing for the homogeneous Dirichlet remainder.  If the difference
between the homogeneous solution gradient and the prescribed boundary-extension
gradient is a zero-trace potential, then testing the homogeneous equation by
that difference identifies the energy with the boundary pairing. -/
theorem dirichletHarmonicRemainder_energy_le_abs_boundary_pairing_of_zeroTrace
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hzero : IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.toH1.grad x - dirichletBoundaryGradientField v x)) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => w.toH1.grad x)) ≤
      |cubeAverage Q
        (fun x =>
          vecDot
            (matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
            (dirichletBoundaryGradientField v x))| := by
  let A : CoeffField d := publicCoeffField Q a
  let flux : Vec d → Vec d := fun x => matVecMul (A x) (w.toH1.grad x)
  let hgrad : Vec d → Vec d := dirichletBoundaryGradientField v
  rcases hzero with ⟨φ, hφgrad⟩
  have hsol :
      ∫ x in cubeSet Q, vecDot (flux x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        0 := by
    simpa [A, flux] using w.isHarmonic.2 φ
  have hsol' :
      ∫ x in cubeSet Q, vecDot (flux x) (w.toH1.grad x - hgrad x) ∂MeasureTheory.volume =
        0 := by
    simpa [flux, hgrad, hφgrad] using hsol
  have hflux_mem : MemVectorL2 (cubeSet Q) flux := by
    dsimp [flux, A]
    exact memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) w.toH1.grad_memVectorL2
  have hh_mem : MemVectorL2 (cubeSet Q) hgrad := by
    simpa [hgrad, dirichletBoundaryGradientField, publicH1ToCubeSet_grad] using
      (publicH1ToCubeSet v.boundaryData).grad_memVectorL2
  have hww_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (w.toH1.grad x)) (cubeSet Q)
        MeasureTheory.volume :=
    integrableOn_vecDot_of_memVectorL2 hflux_mem w.toH1.grad_memVectorL2
  have hwh_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (flux x) (hgrad x)) (cubeSet Q)
        MeasureTheory.volume :=
    integrableOn_vecDot_of_memVectorL2 hflux_mem hh_mem
  have hsub_fun :
      (fun x => vecDot (flux x) (w.toH1.grad x - hgrad x)) =
        fun x => vecDot (flux x) (w.toH1.grad x) - vecDot (flux x) (hgrad x) := by
    funext x
    simp [vecDot, sub_eq_add_neg, Finset.sum_add_distrib, mul_add]
  have hint_eq :
      ∫ x in cubeSet Q, vecDot (flux x) (w.toH1.grad x) ∂MeasureTheory.volume =
        ∫ x in cubeSet Q, vecDot (flux x) (hgrad x) ∂MeasureTheory.volume := by
    have hsub_int :
        ∫ x in cubeSet Q, vecDot (flux x) (w.toH1.grad x - hgrad x)
            ∂MeasureTheory.volume =
          ∫ x in cubeSet Q, vecDot (flux x) (w.toH1.grad x)
              ∂MeasureTheory.volume -
            ∫ x in cubeSet Q, vecDot (flux x) (hgrad x) ∂MeasureTheory.volume := by
      rw [hsub_fun]
      exact MeasureTheory.integral_sub hww_int hwh_int
    linarith
  have henergy_avg_eq_pair :
      cubeAverage Q
        (coefficientEnergyDensity A (fun x => w.toH1.grad x)) =
      cubeAverage Q (fun x => vecDot (flux x) (hgrad x)) := by
    unfold cubeAverage
    have henergy_integral :
        ∫ x in cubeSet Q, coefficientEnergyDensity A (fun x => w.toH1.grad x) x
            ∂MeasureTheory.volume =
          ∫ x in cubeSet Q, vecDot (flux x) (w.toH1.grad x)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.integral_congr_ae
      exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
        Filter.Eventually.of_forall fun x hx => by
          simp [flux, coefficientEnergyDensity_eq_unsymmetrized, vecDot_comm]
    rw [henergy_integral, hint_eq]
  calc
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => w.toH1.grad x))
        = cubeAverage Q (fun x => vecDot (flux x) (hgrad x)) := by
          simpa [A, flux, hgrad] using henergy_avg_eq_pair
    _ ≤ |cubeAverage Q (fun x => vecDot (flux x) (hgrad x))| := le_abs_self _
    _ =
      |cubeAverage Q
        (fun x =>
          vecDot
            (matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
            (dirichletBoundaryGradientField v x))| := by
        rfl

/-- Public `q = 2` Besov-duality wrapper for the boundary pairing.  It combines
the depth-zero average term with the deterministic fluctuation duality estimate,
and absorbs the scale weights and `s ≤ 1` into the dimension-only constant
`1 + d * 3^(d+1)`. -/
theorem abs_cubeAverage_vecDot_le_public_negative_positive_besov_duality_of_partial_flux_bound
    {d : ℕ} {Q : TriadicCube d} {s Bflux : ℝ}
    {F H : Vec d → Vec d}
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hF : MeasureTheory.MemLp F (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (hH : ForceBesovRegularity Q s H)
    (hBflux : 0 ≤ Bflux)
    (hneg : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N F ≤ Bflux) :
    |cubeAverage Q (fun x => vecDot (F x) (H x))| ≤
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux *
        scaleNormalizedPositiveBesovVectorNormTwo Q s H := by
  let Bsemi : ℝ := cubeBesovPositiveVectorSeminormTwo Q s H
  let Bnorm : ℝ := scaleNormalizedPositiveBesovVectorNormTwo Q s H
  have hBsemi_nonneg : 0 ≤ Bsemi := by
    simpa [Bsemi, scaleNormalizedPositiveBesovVectorSeminormTwo] using
      scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := H) hH
  have hBsemi_le_norm : Bsemi ≤ Bnorm := by
    dsimp [Bnorm, scaleNormalizedPositiveBesovVectorNormTwo, Bsemi]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hpos :
      ∀ N : ℕ, cubeBesovPositiveVectorPartialSeminormTwo Q s N H ≤ Bsemi := by
    intro N
    simpa [Bsemi, scaleNormalizedPositiveBesovVectorSeminormTwo] using
      cubeBesovPositiveVectorPartialSeminormTwo_le_seminormTwo_of_bddAbove
        Q s H hH.partialSeminorms_bddAbove N
  have hdecomp :=
    cubeAverage_vecDot_eq_vecDot_cubeAverageVec_add_cubeAverage_vecDot_fluctuationVec
      Q F H hF hH.memLp
  have havg :
      |vecDot (cubeAverageVec Q F) (cubeAverageVec Q H)| ≤ Bflux * Bnorm := by
    have hF0 : Real.sqrt (vecNormSq (cubeAverageVec Q F)) ≤ Bflux :=
      (sqrt_vecNormSq_cubeAverageVec_le_negativePartial_zero Q s F).trans (hneg 0)
    have hH0 : Real.sqrt (vecNormSq (cubeAverageVec Q H)) ≤ Bnorm := by
      dsimp [Bnorm, scaleNormalizedPositiveBesovVectorNormTwo]
      exact le_add_of_nonneg_right hBsemi_nonneg
    calc
      |vecDot (cubeAverageVec Q F) (cubeAverageVec Q H)|
          ≤ Real.sqrt (vecNormSq (cubeAverageVec Q F)) *
              Real.sqrt (vecNormSq (cubeAverageVec Q H)) :=
            abs_vecDot_le_sqrt_vecNormSq_mul_sqrt_vecNormSq _ _
      _ ≤ Bflux * Bnorm :=
            mul_le_mul hF0 hH0 (Real.sqrt_nonneg _) hBflux
  have hfluct_raw :=
    abs_cubeAverage_vecDot_fluctuationVec_le_sum_sharp_note_terms_of_partialBounds_two_two
      Q s F H hs hF hH.memLp hBsemi_nonneg hneg hpos
  have hscale_cancel :
      (d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bflux) *
            (cubeBesovScaleWeight s Q * Bsemi)) =
        (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * Bflux * Bsemi := by
    rw [show
      Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          (cubeBesovScaleWeight (-s) Q * Bflux) *
            (cubeBesovScaleWeight s Q * Bsemi) =
        Real.rpow (3 : ℝ) ((d : ℝ) + s) *
          ((cubeBesovScaleWeight (-s) Q * cubeBesovScaleWeight s Q) *
            (Bflux * Bsemi)) by ring]
    rw [cubeBesovScaleWeight_neg_mul_cubeBesovScaleWeight]
    ring
  have hpow :
      Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
        Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
      (by linarith)
  have hfluct :
      |cubeAverage Q (fun x => vecDot (F x) (cubeFluctuationVec Q H x))| ≤
        (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux * Bnorm := by
    calc
      |cubeAverage Q (fun x => vecDot (F x) (cubeFluctuationVec Q H x))|
          ≤ (d : ℝ) * (Real.rpow (3 : ℝ) ((d : ℝ) + s) *
              (cubeBesovScaleWeight (-s) Q * Bflux) *
                (cubeBesovScaleWeight s Q * Bsemi)) := hfluct_raw
      _ = (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * Bflux * Bsemi :=
            hscale_cancel
      _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux * Bnorm := by
        have hd_nonneg : 0 ≤ (d : ℝ) := by
          exact_mod_cast Nat.zero_le d
        have hpow1_nonneg : 0 ≤ Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
          Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
        calc
          (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * Bflux * Bsemi
              ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux *
                    Bsemi := by
                have hbase :
                    (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) ≤
                      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) :=
                  mul_le_mul_of_nonneg_left hpow hd_nonneg
                have hbaseB :
                    (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + s) * Bflux ≤
                      (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux :=
                  mul_le_mul_of_nonneg_right hbase hBflux
                exact mul_le_mul_of_nonneg_right hbaseB hBsemi_nonneg
          _ ≤ (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux *
                  Bnorm := by
                exact mul_le_mul_of_nonneg_left hBsemi_le_norm
                  (mul_nonneg (mul_nonneg hd_nonneg hpow1_nonneg) hBflux)
  calc
    |cubeAverage Q (fun x => vecDot (F x) (H x))|
        = |vecDot (cubeAverageVec Q F) (cubeAverageVec Q H) +
            cubeAverage Q (fun x => vecDot (F x) (cubeFluctuationVec Q H x))| := by
          rw [hdecomp]
    _ ≤ |vecDot (cubeAverageVec Q F) (cubeAverageVec Q H)| +
          |cubeAverage Q (fun x => vecDot (F x) (cubeFluctuationVec Q H x))| :=
          abs_add_le _ _
    _ ≤ Bflux * Bnorm +
          (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1) * Bflux * Bnorm :=
          add_le_add havg hfluct
    _ =
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux * Bnorm := by
        ring

/-- Weak testing plus the public `q = 2` Besov-duality wrapper for the
Dirichlet harmonic remainder, with the flux side supplied as a uniform
finite-depth negative-Besov bound. -/
theorem dirichletHarmonicRemainder_boundary_pairing_le_of_zeroTrace_and_partial_flux_bound
    {d : ℕ} [NeZero d] {Q : TriadicCube d} {a : CoeffFamily d} {s Bflux : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hzero : IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.toH1.grad x - dirichletBoundaryGradientField v x))
    (hBflux : 0 ≤ Bflux)
    (hpartial :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) ≤ Bflux) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => w.toH1.grad x)) ≤
      (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
  let flux : Vec d → Vec d :=
    fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)
  have hflux_mem : MemVectorL2 (cubeSet Q) flux := by
    dsimp [flux]
    exact memVectorL2_matVecMul_of_isEllipticFieldOn
      (publicCoeffField_isEllipticFieldOn_cubeSet Q a) w.toH1.grad_memVectorL2
  have hflux_memLp :
      MeasureTheory.MemLp flux (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    memLp_normalizedCubeMeasure_of_memVectorL2_cubeSet Q hflux_mem
  have hweak :=
    dirichletHarmonicRemainder_energy_le_abs_boundary_pairing_of_zeroTrace
      (Q := Q) (a := a) (g := g) v w hzero
  have hdual :
      |cubeAverage Q (fun x => vecDot (flux x) (dirichletBoundaryGradientField v x))| ≤
        (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Bflux *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v) := by
    exact
      abs_cubeAverage_vecDot_le_public_negative_positive_besov_duality_of_partial_flux_bound
        (Q := Q) (s := s) (Bflux := Bflux)
        (F := flux) (H := dirichletBoundaryGradientField v)
        hs hs_le hflux_memLp hboundary hBflux (by
          intro N
          simpa [flux] using hpartial N)
  exact hweak.trans (by simpa [flux] using hdual)

/-- Harmonic-remainder energy from weak testing, public Besov duality, and a
uniform finite-depth flux bound.  This is the direct partial-norm form of the
notes' argument and keeps the quantitative coefficient dependence in
`poincareUpperEllipticityFactor`. -/
theorem dirichletHarmonicRemainder_sqrt_two_energy_le_of_zeroTrace_and_partial_flux_bound
    {d : ℕ} [NeZero d] {C Cflux : ℝ}
    (hCflux_nonneg : 0 ≤ Cflux)
    (hC_absorb :
      Real.sqrt 2 *
          (1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)) * Cflux ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hzero : IsPotentialZeroTraceOn (cubeSet Q)
      (fun x => w.toH1.grad x - dirichletBoundaryGradientField v x))
    (hpartial :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminormTwo Q s N
          (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) ≤
        Cflux * Real.rpow s (-(1 / 2 : ℝ)) *
          poincareUpperEllipticityFactor Q a s (.finite 2) *
          Real.sqrt
            (cubeAverage Q
              (coefficientEnergyDensity (publicCoeffField Q a)
                (fun x => w.toH1.grad x)))) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
  let Cpair : ℝ := 1 + (d : ℝ) * Real.rpow (3 : ℝ) ((d : ℝ) + 1)
  let E : ℝ :=
    cubeAverage Q
      (coefficientEnergyDensity (publicCoeffField Q a)
        (fun x => w.toH1.grad x))
  let S : ℝ := Real.rpow s (-(1 / 2 : ℝ))
  let P : ℝ := poincareUpperEllipticityFactor Q a s (.finite 2)
  let B : ℝ :=
    scaleNormalizedPositiveBesovVectorNormTwo Q s
      (dirichletBoundaryGradientField v)
  let Bflux : ℝ := Cflux * S * P * Real.sqrt E
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact cubeAverage_nonneg_of_nonneg_on
      (coefficientEnergyDensity_nonneg_of_isEllipticFieldOn
        (publicCoeffField_isEllipticFieldOn_cubeSet Q a)
        (fun x => w.toH1.grad x))
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    exact Real.rpow_nonneg hs.le _
  have hP_nonneg : 0 ≤ P := by
    dsimp [P, poincareUpperEllipticityFactor]
    exact Real.rpow_nonneg
      (Ch02.LambdaSq_finite_nonneg Q a hs (by norm_num : (1 : ℝ) ≤ 2)) _
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, scaleNormalizedPositiveBesovVectorNormTwo]
    exact add_nonneg (Real.sqrt_nonneg _)
      (scaleNormalizedPositiveBesovVectorSeminormTwo_nonneg_of_forceBesovRegularity
        (Q := Q) (s := s) (g := dirichletBoundaryGradientField v) hboundary)
  have hCpair_nonneg : 0 ≤ Cpair := by
    dsimp [Cpair]
    positivity
  have hBflux_nonneg : 0 ≤ Bflux := by
    dsimp [Bflux]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hCflux_nonneg hS_nonneg) hP_nonneg)
      (Real.sqrt_nonneg E)
  have hpairing : E ≤ Cpair * Bflux * B := by
    simpa [E, Cpair, Bflux, S, P, B] using
      dirichletHarmonicRemainder_boundary_pairing_le_of_zeroTrace_and_partial_flux_bound
        (Q := Q) (a := a) (s := s) (Bflux := Bflux) (g := g) v w
        hs hs_le hboundary hzero hBflux_nonneg (by
          intro N
          simpa [Bflux, S, P, E] using hpartial N)
  have hpairing_scaled :
      E ≤ (Cpair * (Cflux * S * P) * B) * Real.sqrt E := by
    calc
      E ≤ Cpair * Bflux * B := hpairing
      _ = (Cpair * (Cflux * S * P) * B) * Real.sqrt E := by
        dsimp [Bflux]
        ring
  have hscaled : Real.sqrt (2 * E) ≤ C * S * P * B :=
    sqrt_two_energy_le_scaled_rhs_of_pairing hE_nonneg hS_nonneg hP_nonneg
      hB_nonneg hCpair_nonneg hCflux_nonneg
      (by simpa [Cpair] using hC_absorb) hpairing_scaled
  calc
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x)))
        = Real.sqrt (2 * E) := by
          rfl
    _ ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) := by
        simpa [S, P, B] using hscaled


/-- Boundary-pairing interface for the harmonic-remainder proof.  The
mathematical content still sits in the two inputs: weak testing of the
homogeneous equation gives the energy-to-pairing inequality, and Besov duality
bounds that pairing by the negative flux seminorm times the positive boundary
norm. -/
theorem dirichletHarmonicRemainder_boundary_pairing_le_of_weak_testing_and_besov_duality
    {d : ℕ} [NeZero d] {Cpair : ℝ}
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hweak :
      cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x)) ≤
        |cubeAverage Q
          (fun x =>
            vecDot
              (matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
              (dirichletBoundaryGradientField v x))|)
    (hduality :
      |cubeAverage Q
          (fun x =>
            vecDot
              (matVecMul (publicCoeffField Q a x) (w.toH1.grad x))
              (dirichletBoundaryGradientField v x))| ≤
        Cpair *
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v)) :
    cubeAverage Q
        (coefficientEnergyDensity (publicCoeffField Q a)
          (fun x => w.toH1.grad x)) ≤
      Cpair *
        cubeBesovNegativeVectorSeminormTwo Q s
          (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
  hweak.trans hduality

/-- Harmonic-remainder energy after the boundary pairing input is known.  This
closes the homogeneous flux-Poincare half of the notes' proof; the remaining
analytic task is precisely to supply the weak-testing/Besov-duality pairing
bound. -/
theorem dirichletHarmonicRemainder_sqrt_two_energy_le_of_boundary_pairing
    {d : ℕ} [NeZero d] {C Cpair : ℝ}
    (hCpair_nonneg : 0 ≤ Cpair)
    (hC_absorb : Real.sqrt 2 * Cpair * ((d : ℝ) * Real.sqrt 5) ≤ C)
    {Q : TriadicCube d} {a : CoeffFamily d} {s : ℝ}
    {g : Vec d → Vec d} (v : DirichletForcedCubeSolution Q a g)
    (w : AHarmonicFunction (publicCoeffField Q a) (cubeSet Q))
    (hs : 0 < s) (hs_le : s ≤ 1)
    (hboundary : ForceBesovRegularity Q s (dirichletBoundaryGradientField v))
    (hpairing :
      cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x)) ≤
        Cpair *
          cubeBesovNegativeVectorSeminormTwo Q s
            (fun x => matVecMul (publicCoeffField Q a x) (w.toH1.grad x)) *
          scaleNormalizedPositiveBesovVectorNormTwo Q s
            (dirichletBoundaryGradientField v)) :
    Real.sqrt
        (2 * cubeAverage Q
          (coefficientEnergyDensity (publicCoeffField Q a)
            (fun x => w.toH1.grad x))) ≤
      C * Real.rpow s (-(1 / 2 : ℝ)) *
        poincareUpperEllipticityFactor Q a s (.finite 2) *
        scaleNormalizedPositiveBesovVectorNormTwo Q s
          (dirichletBoundaryGradientField v) :=
  dirichletHarmonicRemainder_sqrt_two_energy_le_of_boundary_pairing_and_flux_bound
    (C := C) (Cpair := Cpair) (Cflux := (d : ℝ) * Real.sqrt 5)
    hCpair_nonneg
    (mul_nonneg (by exact_mod_cast Nat.zero_le d) (Real.sqrt_nonneg 5)) hC_absorb
    (Q := Q) (a := a) (s := s) (g := g) v w hs hboundary hpairing
    (by
      simpa [neg_div] using
        dirichletHarmonicRemainder_fluxSeminorm_le_poincareUpperEllipticityFactor
          (Q := Q) (a := a) (s := s) w hs hs_le)

end

end Ch03
end Book
end Homogenization
