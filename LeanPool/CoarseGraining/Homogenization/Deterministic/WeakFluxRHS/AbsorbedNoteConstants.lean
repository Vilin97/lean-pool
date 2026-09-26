/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.WeakFluxRHS.AbsorbedApex

/-! # Absorbed Note Constants -/

@[expose] public section

namespace Homogenization

noncomputable section

theorem coarsePoincareRHSNoteEta_le_one {s : ℝ} (hs : 0 < s) :
    coarsePoincareRHSNoteEta s ≤ 1 := by
  have hη_lt_half := coarsePoincareRHSNoteEta_lt_half hs
  linarith

/-- Reciprocal bound for the note absorption parameter used by the weak-flux
forcing component. -/
theorem coarsePoincareRHSNoteEta_inv_le_ten_inv {s : ℝ}
    (hs : 0 < s) (hs_le : s ≤ 1) :
    (coarsePoincareRHSNoteEta s)⁻¹ ≤ 10 * s⁻¹ := by
  let r : ℝ := Real.rpow (3 : ℝ) (-s / 2)
  have hr_nonneg : 0 ≤ r := by
    dsimp [r]
    exact Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _
  have hr_lt_one : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by norm_num : 1 < (3 : ℝ)) (by linarith)
  have hnum_pos : 0 < 1 - r := by linarith
  have hden_pos : 0 < 2 - r := by linarith
  have hnum_ne :
      1 - Real.rpow (3 : ℝ) (-s / 2) ≠ 0 := by
    simpa [r] using hnum_pos.ne'
  have hden_ne :
      2 - Real.rpow (3 : ℝ) (-s / 2) ≠ 0 := by
    simpa [r] using hden_pos.ne'
  have hinv_eq :
      (coarsePoincareRHSNoteEta s)⁻¹ = (2 - r) * (1 - r)⁻¹ := by
    unfold coarsePoincareRHSNoteEta
    dsimp [r]
    field_simp [hnum_ne, hden_ne]
  have hinv_nonneg : 0 ≤ (1 - r)⁻¹ := inv_nonneg.mpr hnum_pos.le
  have htwo_sub_le : 2 - r ≤ 2 := by linarith
  have hmul_le :
      (2 - r) * (1 - r)⁻¹ ≤ 2 * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_right htwo_sub_le hinv_nonneg
  have htail :
      (1 - r)⁻¹ ≤ 5 * s⁻¹ := by
    simpa [r] using inv_one_sub_rpow_three_neg_half_le_five_inv hs hs_le
  calc
    (coarsePoincareRHSNoteEta s)⁻¹ = (2 - r) * (1 - r)⁻¹ := hinv_eq
    _ ≤ 2 * (1 - r)⁻¹ := hmul_le
    _ ≤ 2 * (5 * s⁻¹) := mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = 10 * s⁻¹ := by ring

/-- The note-eta scalar seminorm component is bounded by the weak-flux
geometric-tail constant. -/
theorem weakFluxRHSNoteEtaComponent_mul_inv_one_sub_step_le_five_inv_mul
    {s B : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (hB_nonneg : 0 ≤ B) :
    (coarsePoincareRHSNoteEta s * B) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      (5 * s⁻¹) * B := by
  let H : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let K : ℝ := 5 * s⁻¹
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    have hr_lt_one : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hH_le : H ≤ K := by
    dsimp [H, K]
    exact inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have hη_le_one : coarsePoincareRHSNoteEta s ≤ 1 :=
    coarsePoincareRHSNoteEta_le_one hs
  have hηH_le : coarsePoincareRHSNoteEta s * H ≤ K := by
    calc
      coarsePoincareRHSNoteEta s * H ≤ 1 * H :=
        mul_le_mul_of_nonneg_right hη_le_one hH_nonneg
      _ = H := by ring
      _ ≤ K := hH_le
  calc
    (coarsePoincareRHSNoteEta s * B) *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
        (coarsePoincareRHSNoteEta s * H) * B := by
          simp [H]
          ring
    _ ≤ K * B := mul_le_mul_of_nonneg_right hηH_le hB_nonneg
    _ = (5 * s⁻¹) * B := by
          simp [K]

/-- Note-constant expansion of the localized weak-flux base with the forcing
component left as a separately supplied bound. -/
theorem weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_noteEnergySeminorms_of_force
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (m : ℕ) {BU BV Bforce : ℝ}
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV)
    (hforce :
      weakFluxRHSWeightedGlobalForceBase Q a g s
          (coarsePoincareRHSNoteEta s) m *
          (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤ Bforce) :
    weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a u) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV + Bforce := by
  exact
    weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_of_components
      Q a u g s m BU BV
      (50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
        cubeAverage Q (coefficientEnergyDensity a u))
      ((5 * s⁻¹) * BU) ((5 * s⁻¹) * BV) Bforce
      (weakFluxRHSWeightedCoefficientEnergyBase_mul_inv_one_sub_step_le_noteEnergySquare
        Q a u hs hs_le havg_nonneg)
      (weakFluxRHSNoteEtaComponent_mul_inv_one_sub_step_le_five_inv_mul
        hs hs_le hBU_nonneg)
      (weakFluxRHSNoteEtaComponent_mul_inv_one_sub_step_le_five_inv_mul
        hs hs_le hBV_nonneg)
      hforce

/-- Note-constant square-envelope for the weighted global forcing component at
the parent depth. -/
theorem weakFluxRHSWeightedGlobalForceBase_noteEta_zero_mul_inv_one_sub_step_le_noteForceSquare
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) :
    weakFluxRHSWeightedGlobalForceBase Q a g s (coarsePoincareRHSNoteEta s) 0 *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  let E : ℝ := (coarsePoincareRHSNoteEta s)⁻¹
  let G : ℝ := (geometricDiscount s 2)⁻¹
  let H : ℝ := (1 - Real.rpow (3 : ℝ) (-s))⁻¹
  let K : ℝ := 5 * s⁻¹
  let L : ℝ := LambdaSq Q (s / 2) (.finite 2) a
  let M : ℝ := (d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)
  let B : ℝ := cubeBesovPositiveVectorSeminormTwo Q s g
  let F : ℝ := L ^ 2 * M ^ 2 * B ^ 2
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact inv_nonneg.mpr (coarsePoincareRHSNoteEta_pos hs).le
  have hE_le : E ≤ 10 * s⁻¹ := by
    dsimp [E]
    exact coarsePoincareRHSNoteEta_inv_le_ten_inv hs hs_le
  have hG_nonneg : 0 ≤ G := by
    dsimp [G]
    exact inv_nonneg.mpr
      (le_of_lt (geometricDiscount_pos (by nlinarith : 0 < s * 2)))
  have hG_le : G ≤ K := by
    dsimp [G, K]
    exact inv_geometricDiscount_two_le_five_inv hs hs_le
  have hG_sq : G ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ hG_nonneg hG_le 2
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    have hr_lt_one : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  have hH_le : H ≤ K := by
    dsimp [H, K]
    exact inv_one_sub_rpow_three_neg_le_five_inv hs hs_le
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  have hEbound_nonneg : 0 ≤ 10 * s⁻¹ := by positivity
  have hF_nonneg : 0 ≤ F := by
    dsimp [F]
    positivity
  have hcore_le :
      (G * L * M) ^ 2 * B ^ 2 ≤ K ^ 2 * F := by
    calc
      (G * L * M) ^ 2 * B ^ 2 = G ^ 2 * F := by
        simp [F]
        ring
      _ ≤ K ^ 2 * F := mul_le_mul_of_nonneg_right hG_sq hF_nonneg
  have hcore_nonneg : 0 ≤ (G * L * M) ^ 2 * B ^ 2 := by positivity
  have hcore_bound_nonneg : 0 ≤ K ^ 2 * F :=
    mul_nonneg (sq_nonneg K) hF_nonneg
  have hEcore_le :
      E * ((G * L * M) ^ 2 * B ^ 2) ≤
        (10 * s⁻¹) * (K ^ 2 * F) :=
    mul_le_mul hE_le hcore_le hcore_nonneg hEbound_nonneg
  have hinner_le :
      2 * E * ((G * L * M) ^ 2 * B ^ 2) ≤
        2 * (10 * s⁻¹) * (K ^ 2 * F) := by
    simpa [mul_assoc] using
      mul_le_mul_of_nonneg_left hEcore_le (by norm_num : 0 ≤ (2 : ℝ))
  have hinner_bound_nonneg :
      0 ≤ 2 * (10 * s⁻¹) * (K ^ 2 * F) := by
    positivity
  calc
    weakFluxRHSWeightedGlobalForceBase Q a g s (coarsePoincareRHSNoteEta s) 0 *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ =
        (2 * E * ((G * L * M) ^ 2 * B ^ 2)) * H := by
          simp [weakFluxRHSWeightedGlobalForceBase,
            weakFluxRHSParentHalfForceMultiplier, weakFluxRHSParentHalfCoeff,
            coarsePoincareRHSDepthWeight, coarsePoincareRHSGlobalForceBound,
            E, G, H, L, M, B]
    _ ≤ (2 * (10 * s⁻¹) * (K ^ 2 * F)) * H :=
          mul_le_mul_of_nonneg_right hinner_le hH_nonneg
    _ ≤ (2 * (10 * s⁻¹) * (K ^ 2 * F)) * K :=
          mul_le_mul_of_nonneg_left hH_le hinner_bound_nonneg
    _ =
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
          simp [K, F, L, M, B]
          ring

/-- Note-constant square-envelope for the weighted global forcing component at
any descendant depth. -/
theorem weakFluxRHSWeightedGlobalForceBase_noteEta_mul_inv_one_sub_step_le_noteForceSquare
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (m : ℕ) :
    weakFluxRHSWeightedGlobalForceBase Q a g s (coarsePoincareRHSNoteEta s) m *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  have hη_pos : 0 < coarsePoincareRHSNoteEta s :=
    coarsePoincareRHSNoteEta_pos hs
  have htail_nonneg : 0 ≤ (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
    have hr_lt_one : Real.rpow (3 : ℝ) (-s) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith)
    exact inv_nonneg.mpr (sub_nonneg.mpr hr_lt_one.le)
  calc
    weakFluxRHSWeightedGlobalForceBase Q a g s (coarsePoincareRHSNoteEta s) m *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      weakFluxRHSWeightedGlobalForceBase Q a g s (coarsePoincareRHSNoteEta s) 0 *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ := by
        have hdecay :
            weakFluxRHSWeightedGlobalForceBase Q a g s
                (coarsePoincareRHSNoteEta s) m ≤
              weakFluxRHSWeightedGlobalForceBase Q a g s
                (coarsePoincareRHSNoteEta s) 0 := by
          simpa using
            (weakFluxRHSWeightedGlobalForceBase_add_le_base
              (Q := Q) (a := a) (g := g) (s := s)
              (η := coarsePoincareRHSNoteEta s) 0 m hs hη_pos)
        exact mul_le_mul_of_nonneg_right hdecay htail_nonneg
    _ ≤
      2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
        ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
        (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 :=
        weakFluxRHSWeightedGlobalForceBase_noteEta_zero_mul_inv_one_sub_step_le_noteForceSquare
          Q a g hs hs_le

/-- Fully expanded note-constant bound for the localized weak-flux base, with
the `u` and harmonic-remainder tails left as caller-supplied square bounds. -/
theorem weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_noteEnergySeminormsForce
    {d : ℕ} (Q : TriadicCube d) (a : CoeffField d) (u g : Vec d → Vec d)
    {s : ℝ} (hs : 0 < s) (hs_le : s ≤ 1) (m : ℕ) {BU BV : ℝ}
    (havg_nonneg : 0 ≤ cubeAverage Q (coefficientEnergyDensity a u))
    (hBU_nonneg : 0 ≤ BU) (hBV_nonneg : 0 ≤ BV) :
    weakFluxRHSAbsorbedLocalizedNoteBase Q a u g s m BU BV *
        (1 - Real.rpow (3 : ℝ) (-s))⁻¹ ≤
      50 * (s⁻¹) ^ 2 * LambdaSq Q (s / 2) (.finite 2) a *
          cubeAverage Q (coefficientEnergyDensity a u) +
        (5 * s⁻¹) * BU + (5 * s⁻¹) * BV +
        2500 * (s⁻¹) ^ 4 * (LambdaSq Q (s / 2) (.finite 2) a) ^ 2 *
          ((d : ℝ) * ((3 : ℝ) ^ ((d : ℝ) + s) * Real.sqrt 2)) ^ 2 *
          (cubeBesovPositiveVectorSeminormTwo Q s g) ^ 2 := by
  exact
    weakFluxRHSAbsorbedLocalizedNoteBase_mul_inv_one_sub_step_le_noteEnergySeminorms_of_force
      Q a u g hs hs_le m havg_nonneg hBU_nonneg hBV_nonneg
      (weakFluxRHSWeightedGlobalForceBase_noteEta_mul_inv_one_sub_step_le_noteForceSquare
        Q a g hs hs_le m)

end

end Homogenization
