/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.InputSpecializations
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFronts
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.CenteredFactors
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.Constructor
public import LeanPool.CoarseGraining.Homogenization.Deterministic.CoarseCaccioppoli.SingleCubeToRaw.HarmonicFinal.ExactSmallCube.LocalPatchConstructor

/-! # Endpoints -/

@[expose] public section

namespace Homogenization

noncomputable section

open scoped ENNReal

/-!
# Theorem-facing Caccioppoli endpoint aliases

This file keeps the theorem-facing endpoint aliases separate from the internal
`InputSpecializations` bridge machinery.  It retains only the standard
beta-dependent split endpoint route and the scalar budgets needed to construct
that route internally.
-/

/-- Explicit local-patch cutoff budget for the buffered boundary route.

This is the cutoff-size term formerly hidden inside an existential choice of
`Clocal`.  Keeping it as a definition lets later public theorems bound the
resulting note constant without losing track of which max construction was
used. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCutoffBudget {d : ℕ}
    (Q : TriadicCube d) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
    (12 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) +
      6 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q))

/-- The local-patch cutoff budget on a scale-zero cube, written without cube
geometry parameters. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCutoffBudgetUnit
    (d : ℕ) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
    (48 * quantitativeCubeCutoffHessianConst d +
      12 * quantitativeCubeCutoffGradientConst d)

theorem coarseCaccioppoliLocalPatchBufferedCutoffBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} {Q : TriadicCube d} (hQ : Q.scale = 0) :
    coarseCaccioppoliLocalPatchBufferedCutoffBudget Q =
      coarseCaccioppoliLocalPatchBufferedCutoffBudgetUnit d := by
  unfold coarseCaccioppoliLocalPatchBufferedCutoffBudget
    coarseCaccioppoliLocalPatchBufferedCutoffBudgetUnit
  rw [cubeScaleFactor_eq_one_of_scale_eq_zero hQ,
    cubeRadius_eq_half_of_scale_eq_zero hQ]
  ring_nf

/-- Explicit `Clocal` used by the local-patch buffered boundary endpoint. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedLocalBudget {d : ℕ}
    (Q : TriadicCube d) (Csol : ℝ) : ℝ :=
  max 1 (max Csol (coarseCaccioppoliLocalPatchBufferedCutoffBudget Q))

/-- Effective local budget after summing over coordinate directions. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCeffLocalBudget {d : ℕ}
    (Q : TriadicCube d) (Csol : ℝ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) *
    coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol

/-- Centered-front budget used by the arbitrary-center local-patch route. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCenteredFrontBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  6 * coarseCaccioppoliCenteredAverageFront d s
        (coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q Csol) +
    12 * coarseCaccioppoliCenteredBesovHessianFront d s
        (coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q Csol) +
    6 * coarseCaccioppoliCenteredBesovGradientFront d s
        (coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q Csol)

/-- Split alpha/front budget used by the local-patch buffered boundary
endpoint. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedAlphaBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  let centeredFront : ℝ :=
    coarseCaccioppoliLocalPatchBufferedCenteredFrontBudget Q s Csol
  let frontWork : ℝ := ((81 : ℝ) * centeredFront) * (s * (1 - s))
  max 1 frontWork

/-- Split constant/cross budget used by the local-patch buffered boundary
endpoint. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCrossBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  let Clocal : ℝ := coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol
  let constantWork : ℝ := (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) * Clocal
  max 1 constantWork

/-- Unit-cube split alpha/front budget for the local-patch boundary route. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit
    (d : ℕ) [NeZero d] (s : ℝ) : ℝ :=
  coarseCaccioppoliLocalPatchBufferedAlphaBudget (originCube d 0) s
    (fullVectorPoincareCubeConstant (originCube d 0))

/-- Unit-cube split constant/cross budget for the local-patch boundary route. -/
noncomputable def coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit
    (d : ℕ) [NeZero d] (s : ℝ) : ℝ :=
  coarseCaccioppoliLocalPatchBufferedCrossBudget (originCube d 0) s
    (fullVectorPoincareCubeConstant (originCube d 0))

theorem
    coarseCaccioppoliLocalPatchBufferedAlphaBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (s : ℝ) (hQ : Q.scale = 0) :
    coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s
        (fullVectorPoincareCubeConstant Q) =
      coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit d s := by
  unfold coarseCaccioppoliLocalPatchBufferedAlphaBudgetUnit
    coarseCaccioppoliLocalPatchBufferedAlphaBudget
    coarseCaccioppoliLocalPatchBufferedCenteredFrontBudget
    coarseCaccioppoliLocalPatchBufferedCeffLocalBudget
    coarseCaccioppoliLocalPatchBufferedLocalBudget
  rw [fullVectorPoincareCubeConstant_eq_dimensionConstant Q,
    fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0),
    coarseCaccioppoliLocalPatchBufferedCutoffBudget_eq_unit_of_scale_eq_zero hQ,
    coarseCaccioppoliLocalPatchBufferedCutoffBudget_eq_unit_of_scale_eq_zero
      (Q := originCube d 0) rfl]

theorem
    coarseCaccioppoliLocalPatchBufferedCrossBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (s : ℝ) (hQ : Q.scale = 0) :
    coarseCaccioppoliLocalPatchBufferedCrossBudget Q s
        (fullVectorPoincareCubeConstant Q) =
      coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit d s := by
  unfold coarseCaccioppoliLocalPatchBufferedCrossBudgetUnit
    coarseCaccioppoliLocalPatchBufferedCrossBudget
    coarseCaccioppoliLocalPatchBufferedLocalBudget
  rw [fullVectorPoincareCubeConstant_eq_dimensionConstant Q,
    fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0),
    coarseCaccioppoliLocalPatchBufferedCutoffBudget_eq_unit_of_scale_eq_zero hQ,
    coarseCaccioppoliLocalPatchBufferedCutoffBudget_eq_unit_of_scale_eq_zero
      (Q := originCube d 0) rfl]

/-- The explicit split local-patch buffered budgets satisfy the scalar side
conditions needed by the split exact raw-coefficient package. -/
theorem coarseCaccioppoliLocalPatchBufferedBudgetSplit_spec
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s t Csol : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    Csol ≤ coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol ∧
    0 ≤ coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol ∧
    0 < coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol ∧
    0 ≤ coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol ∧
    (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) *
        ((Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol) ≤
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol ∧
    (81 : ℝ) *
        (6 * coarseCaccioppoliCenteredAverageFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol) +
          12 * coarseCaccioppoliCenteredBesovHessianFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol) +
          6 * coarseCaccioppoliCenteredBesovGradientFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol)) ≤
      ((Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol) / (s * (1 - s)) ∧
    coarseCaccioppoliLocalPatchBufferedCutoffBudget Q ≤
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol := by
  let card : ℝ := Fintype.card (Fin d)
  let cutoffBound : ℝ := coarseCaccioppoliLocalPatchBufferedCutoffBudget Q
  let Clocal : ℝ := coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol
  let CeffLocal : ℝ :=
    coarseCaccioppoliLocalPatchBufferedCeffLocalBudget Q Csol
  let centeredFront : ℝ :=
    coarseCaccioppoliLocalPatchBufferedCenteredFrontBudget Q s Csol
  let den : ℝ := s * (1 - s)
  let constantWork : ℝ := (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) * Clocal
  let frontWork : ℝ := ((81 : ℝ) * centeredFront) * den
  let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
  have hClocal_eq : Clocal = max 1 (max Csol cutoffBound) := by rfl
  have hCeffLocal_eq : CeffLocal = card * Clocal := by rfl
  have hcenteredFront_eq :
      centeredFront =
        6 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          12 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          6 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal := by
    rfl
  have hCalpha_eq : Calpha = max 1 frontWork := by rfl
  have hCcross_eq : Ccross = max 1 constantWork := by rfl
  have hcard_nat_pos : 0 < Fintype.card (Fin d) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hcard_nonneg : 0 ≤ card := by
    dsimp [card]
    exact_mod_cast (Nat.zero_le (Fintype.card (Fin d)))
  have hcard_ge_one : (1 : ℝ) ≤ card := by
    dsimp [card]
    exact_mod_cast (Nat.succ_le_of_lt hcard_nat_pos)
  have hs1 : s < 1 := by nlinarith
  have hden_pos : 0 < den := by
    have hs1_pos : 0 < 1 - s := by nlinarith
    exact mul_pos hs hs1_pos
  have hCsol_le_Clocal : Csol ≤ Clocal := by
    rw [hClocal_eq]
    exact (le_max_left Csol cutoffBound).trans
      (le_max_right (1 : ℝ) (max Csol cutoffBound))
  have hcutoff_le_Clocal : cutoffBound ≤ Clocal := by
    rw [hClocal_eq]
    exact (le_max_right Csol cutoffBound).trans
      (le_max_right (1 : ℝ) (max Csol cutoffBound))
  have hClocal_nonneg : 0 ≤ Clocal := by
    rw [hClocal_eq]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans
      (le_max_left (1 : ℝ) (max Csol cutoffBound))
  have hCalpha_pos : 0 < Calpha := by
    rw [hCalpha_eq]
    exact zero_lt_one.trans_le (le_max_left (1 : ℝ) frontWork)
  have hCcross_pos : 0 < Ccross := by
    rw [hCcross_eq]
    exact zero_lt_one.trans_le (le_max_left (1 : ℝ) constantWork)
  have hClocal_le_card_mul : Clocal ≤ card * Clocal := by
    nlinarith
  have hCalpha_le_card_mul : Calpha ≤ card * Calpha := by
    nlinarith
  have hCcross_le_card_mul : Ccross ≤ card * Ccross := by
    nlinarith
  have hconstantWork_le_Ccross : constantWork ≤ Ccross := by
    rw [hCcross_eq]
    exact le_max_right (1 : ℝ) constantWork
  have hfrontWork_le_Calpha : frontWork ≤ Calpha := by
    rw [hCalpha_eq]
    exact le_max_right (1 : ℝ) frontWork
  have hwork_constant :
      (81 : ℝ) * Real.rpow (3 : ℝ) (2 * s) * (card * Clocal) ≤
        card * Ccross := by
    have hscaled := mul_le_mul_of_nonneg_left hconstantWork_le_Ccross hcard_nonneg
    simpa [constantWork, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hwork_front :
      (81 : ℝ) * centeredFront ≤ card * Calpha / den := by
    refine (le_div_iff₀ hden_pos).2 ?_
    exact hfrontWork_le_Calpha.trans hCalpha_le_card_mul
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Clocal] using hCsol_le_Clocal
  · simpa [Clocal] using hClocal_nonneg
  · simpa [Calpha] using hCalpha_pos
  · simpa [Ccross] using hCcross_pos.le
  · simpa [card, Clocal, Ccross] using hwork_constant
  · simpa [card, Clocal, Calpha, CeffLocal, centeredFront, den,
      hCeffLocal_eq, hcenteredFront_eq] using hwork_front
  · simpa [card, Clocal, cutoffBound] using
      hcutoff_le_Clocal.trans hClocal_le_card_mul

/-- Explicit cutoff budget for the centered buffered route. -/
noncomputable def coarseCaccioppoliBufferedCutoffBudget {d : ℕ}
    (Q : TriadicCube d) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
    (4 * (quantitativeCubeCutoffHessianConst d * cubeScaleFactor Q /
          (cubeRadius Q) ^ (2 : ℕ)) +
      2 * (quantitativeCubeCutoffGradientConst d / cubeRadius Q))

/-- The centered buffered cutoff budget on a scale-zero cube, written without
cube geometry parameters. -/
noncomputable def coarseCaccioppoliBufferedCutoffBudgetUnit (d : ℕ) : ℝ :=
  (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + 1) *
      (geometricDiscount (1 : ℝ) 1)⁻¹ *
    (16 * quantitativeCubeCutoffHessianConst d +
      4 * quantitativeCubeCutoffGradientConst d)

theorem coarseCaccioppoliBufferedCutoffBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} {Q : TriadicCube d} (hQ : Q.scale = 0) :
    coarseCaccioppoliBufferedCutoffBudget Q =
      coarseCaccioppoliBufferedCutoffBudgetUnit d := by
  unfold coarseCaccioppoliBufferedCutoffBudget
    coarseCaccioppoliBufferedCutoffBudgetUnit
  rw [cubeScaleFactor_eq_one_of_scale_eq_zero hQ,
    cubeRadius_eq_half_of_scale_eq_zero hQ]
  ring_nf

/-- Explicit `Clocal` used by the centered buffered endpoint. -/
noncomputable def coarseCaccioppoliBufferedLocalBudget {d : ℕ}
    (Q : TriadicCube d) (Csol : ℝ) : ℝ :=
  max 1 (max Csol (coarseCaccioppoliBufferedCutoffBudget Q))

/-- Effective centered buffered local budget after summing directions. -/
noncomputable def coarseCaccioppoliBufferedCeffLocalBudget {d : ℕ}
    (Q : TriadicCube d) (Csol : ℝ) : ℝ :=
  (Fintype.card (Fin d) : ℝ) * coarseCaccioppoliBufferedLocalBudget Q Csol

/-- Centered-front budget used by the centered buffered route. -/
noncomputable def coarseCaccioppoliBufferedCenteredFrontBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  2 * coarseCaccioppoliCenteredAverageFront d s
        (coarseCaccioppoliBufferedCeffLocalBudget Q Csol) +
    4 * coarseCaccioppoliCenteredBesovHessianFront d s
        (coarseCaccioppoliBufferedCeffLocalBudget Q Csol) +
    2 * coarseCaccioppoliCenteredBesovGradientFront d s
        (coarseCaccioppoliBufferedCeffLocalBudget Q Csol)

/-- Split alpha/front budget used by the centered buffered endpoint. -/
noncomputable def coarseCaccioppoliBufferedAlphaBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  let centeredFront : ℝ := coarseCaccioppoliBufferedCenteredFrontBudget Q s Csol
  let den : ℝ := s * (1 - s)
  let frontWork : ℝ := ((81 : ℝ) * centeredFront) * den
  max 1 frontWork

/-- Split constant/cross budget used by the centered buffered endpoint. -/
noncomputable def coarseCaccioppoliBufferedCrossBudget {d : ℕ}
    (Q : TriadicCube d) (s Csol : ℝ) : ℝ :=
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q Csol
  let constantWork : ℝ := (81 : ℝ) * Real.rpow (3 : ℝ) s * Clocal
  max 1 constantWork

/-- Unit-cube centered buffered alpha/front budget, depending only on `d` and
`s`. -/
noncomputable def coarseCaccioppoliBufferedAlphaBudgetUnit
    (d : ℕ) [NeZero d] (s : ℝ) : ℝ :=
  coarseCaccioppoliBufferedAlphaBudget (originCube d 0) s
    (fullVectorPoincareCubeConstant (originCube d 0))

/-- Unit-cube centered buffered constant/cross budget, depending only on `d`
and `s`. -/
noncomputable def coarseCaccioppoliBufferedCrossBudgetUnit
    (d : ℕ) [NeZero d] (s : ℝ) : ℝ :=
  coarseCaccioppoliBufferedCrossBudget (originCube d 0) s
    (fullVectorPoincareCubeConstant (originCube d 0))

theorem coarseCaccioppoliBufferedAlphaBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (s : ℝ) (hQ : Q.scale = 0) :
    coarseCaccioppoliBufferedAlphaBudget Q s
        (fullVectorPoincareCubeConstant Q) =
      coarseCaccioppoliBufferedAlphaBudgetUnit d s := by
  unfold coarseCaccioppoliBufferedAlphaBudgetUnit
    coarseCaccioppoliBufferedAlphaBudget
    coarseCaccioppoliBufferedCenteredFrontBudget
    coarseCaccioppoliBufferedCeffLocalBudget
    coarseCaccioppoliBufferedLocalBudget
  rw [fullVectorPoincareCubeConstant_eq_dimensionConstant Q,
    fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0),
    coarseCaccioppoliBufferedCutoffBudget_eq_unit_of_scale_eq_zero hQ,
    coarseCaccioppoliBufferedCutoffBudget_eq_unit_of_scale_eq_zero
      (Q := originCube d 0) rfl]

theorem coarseCaccioppoliBufferedCrossBudget_eq_unit_of_scale_eq_zero
    {d : ℕ} [NeZero d] {Q : TriadicCube d} (s : ℝ) (hQ : Q.scale = 0) :
    coarseCaccioppoliBufferedCrossBudget Q s
        (fullVectorPoincareCubeConstant Q) =
      coarseCaccioppoliBufferedCrossBudgetUnit d s := by
  unfold coarseCaccioppoliBufferedCrossBudgetUnit
    coarseCaccioppoliBufferedCrossBudget
    coarseCaccioppoliBufferedLocalBudget
  rw [fullVectorPoincareCubeConstant_eq_dimensionConstant Q,
    fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d 0),
    coarseCaccioppoliBufferedCutoffBudget_eq_unit_of_scale_eq_zero hQ,
    coarseCaccioppoliBufferedCutoffBudget_eq_unit_of_scale_eq_zero
      (Q := originCube d 0) rfl]

/-- The explicit split centered buffered budgets satisfy the scalar side
conditions needed by the split exact raw-coefficient package. -/
theorem coarseCaccioppoliBufferedBudgetSplit_spec
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s t Csol : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1) :
    Csol ≤ coarseCaccioppoliBufferedLocalBudget Q Csol ∧
    0 ≤ coarseCaccioppoliBufferedLocalBudget Q Csol ∧
    0 < coarseCaccioppoliBufferedAlphaBudget Q s Csol ∧
    0 ≤ coarseCaccioppoliBufferedCrossBudget Q s Csol ∧
    (81 : ℝ) * Real.rpow (3 : ℝ) s *
        ((Fintype.card (Fin d) : ℝ) *
          coarseCaccioppoliBufferedLocalBudget Q Csol) ≤
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedCrossBudget Q s Csol ∧
    (81 : ℝ) *
        (2 * coarseCaccioppoliCenteredAverageFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliBufferedLocalBudget Q Csol) +
          4 * coarseCaccioppoliCenteredBesovHessianFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliBufferedLocalBudget Q Csol) +
          2 * coarseCaccioppoliCenteredBesovGradientFront d s
            ((Fintype.card (Fin d) : ℝ) *
              coarseCaccioppoliBufferedLocalBudget Q Csol)) ≤
      ((Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedAlphaBudget Q s Csol) / (s * (1 - s)) ∧
    coarseCaccioppoliBufferedCutoffBudget Q ≤
      (Fintype.card (Fin d) : ℝ) *
        coarseCaccioppoliBufferedLocalBudget Q Csol := by
  let card : ℝ := Fintype.card (Fin d)
  let cutoffBound : ℝ := coarseCaccioppoliBufferedCutoffBudget Q
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q Csol
  let CeffLocal : ℝ := coarseCaccioppoliBufferedCeffLocalBudget Q Csol
  let centeredFront : ℝ := coarseCaccioppoliBufferedCenteredFrontBudget Q s Csol
  let den : ℝ := s * (1 - s)
  let constantWork : ℝ := (81 : ℝ) * Real.rpow (3 : ℝ) s * Clocal
  let frontWork : ℝ := ((81 : ℝ) * centeredFront) * den
  let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
  have hClocal_eq : Clocal = max 1 (max Csol cutoffBound) := by rfl
  have hCeffLocal_eq : CeffLocal = card * Clocal := by rfl
  have hcenteredFront_eq :
      centeredFront =
        2 * coarseCaccioppoliCenteredAverageFront d s CeffLocal +
          4 * coarseCaccioppoliCenteredBesovHessianFront d s CeffLocal +
          2 * coarseCaccioppoliCenteredBesovGradientFront d s CeffLocal := by
    rfl
  have hCalpha_eq : Calpha = max 1 frontWork := by rfl
  have hCcross_eq : Ccross = max 1 constantWork := by rfl
  have hcard_nat_pos : 0 < Fintype.card (Fin d) := by
    simp [Fintype.card_fin, Nat.pos_iff_ne_zero, NeZero.ne d]
  have hcard_nonneg : 0 ≤ card := by
    dsimp [card]
    exact_mod_cast (Nat.zero_le (Fintype.card (Fin d)))
  have hcard_ge_one : (1 : ℝ) ≤ card := by
    dsimp [card]
    exact_mod_cast (Nat.succ_le_of_lt hcard_nat_pos)
  have hs1 : s < 1 := by nlinarith
  have hden_pos : 0 < den := by
    have hs1_pos : 0 < 1 - s := by nlinarith
    exact mul_pos hs hs1_pos
  have hCsol_le_Clocal : Csol ≤ Clocal := by
    rw [hClocal_eq]
    exact (le_max_left Csol cutoffBound).trans
      (le_max_right (1 : ℝ) (max Csol cutoffBound))
  have hcutoff_le_Clocal : cutoffBound ≤ Clocal := by
    rw [hClocal_eq]
    exact (le_max_right Csol cutoffBound).trans
      (le_max_right (1 : ℝ) (max Csol cutoffBound))
  have hClocal_nonneg : 0 ≤ Clocal := by
    rw [hClocal_eq]
    exact (show (0 : ℝ) ≤ 1 by norm_num).trans
      (le_max_left (1 : ℝ) (max Csol cutoffBound))
  have hCalpha_pos : 0 < Calpha := by
    rw [hCalpha_eq]
    exact zero_lt_one.trans_le (le_max_left (1 : ℝ) frontWork)
  have hCcross_pos : 0 < Ccross := by
    rw [hCcross_eq]
    exact zero_lt_one.trans_le (le_max_left (1 : ℝ) constantWork)
  have hClocal_le_card_mul : Clocal ≤ card * Clocal := by
    nlinarith
  have hCalpha_le_card_mul : Calpha ≤ card * Calpha := by
    nlinarith
  have hconstantWork_le_Ccross : constantWork ≤ Ccross := by
    rw [hCcross_eq]
    exact le_max_right (1 : ℝ) constantWork
  have hfrontWork_le_Calpha : frontWork ≤ Calpha := by
    rw [hCalpha_eq]
    exact le_max_right (1 : ℝ) frontWork
  have hwork_constant :
      (81 : ℝ) * Real.rpow (3 : ℝ) s * (card * Clocal) ≤
        card * Ccross := by
    have hscaled := mul_le_mul_of_nonneg_left hconstantWork_le_Ccross hcard_nonneg
    simpa [constantWork, mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hwork_front :
      (81 : ℝ) * centeredFront ≤ card * Calpha / den := by
    refine (le_div_iff₀ hden_pos).2 ?_
    exact hfrontWork_le_Calpha.trans hCalpha_le_card_mul
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Clocal] using hCsol_le_Clocal
  · simpa [Clocal] using hClocal_nonneg
  · simpa [Calpha] using hCalpha_pos
  · simpa [Ccross] using hCcross_pos.le
  · simpa [card, Clocal, Ccross] using hwork_constant
  · simpa [card, Clocal, Calpha, CeffLocal, centeredFront, den,
      hCeffLocal_eq, hcenteredFront_eq] using hwork_front
  · simpa [card, Clocal, cutoffBound] using
      hcutoff_le_Clocal.trans hClocal_le_card_mul

/-- Boundary local-patch Caccioppoli with explicit split max-chosen budgets,
using the standard beta-dependent radius iteration.

This is the repaired arbitrary-center boundary endpoint: the deterministic
bridge is all-radii, and the note constant is the standard split one. -/
theorem
    coarseCaccioppoli_boundary_qone_standard_note_of_closedCubeEllipticity_of_localPatchBuffered_constantFamily_of_localizedZeroTraceOnLocalOpenCube_explicitBudgetSplit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (center : Vec d) (a : CoeffField d)
    (s t : ℝ) {lam Lam : ℝ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hzero :
      LocalizedZeroTraceFunctionOn (openCubeSet Q)
        (coarseCaccioppoliLocalOpenCube Q center 1) u.toH1.toFun)
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
    0 ≤ Cnote ∧
      coarseCaccioppoliLocalEnergyRadiusProfile Q center
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u) := by
  let Csol : ℝ := fullVectorPoincareCubeConstant Q
  let Clocal : ℝ := coarseCaccioppoliLocalPatchBufferedLocalBudget Q Csol
  let Calpha : ℝ := coarseCaccioppoliLocalPatchBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliLocalPatchBufferedCrossBudget Q s Csol
  rcases coarseCaccioppoliLocalPatchBufferedBudgetSplit_spec
      (Q := Q) (s := s) (t := t) (Csol := Csol) hs ht hst with
    ⟨hCsol_le, hClocal, hCalpha, hCcross, hwork_constant_cross,
      hwork_centered_fronts_alpha, hlarge⟩
  let hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii
        Q center a s t Clocal Calpha Ccross :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeLocalPatchBufferedExactRawCoefficientBoundsSplitAllRadii.of_closedCubeEllipticity_of_localPatchBufferedCutoffRadiusConst_of_centeredFronts
      (Q := Q) (center := center) (a := a) (s := s) (t := t)
      (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross)
      hClocal hCalpha.le hwork_constant_cross hwork_centered_fronts_alpha
      hs ht hst hEllCube hlarge
  let Cnote : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
      ((Fintype.card (Fin d) : ℝ) * Calpha)
      ((Fintype.card (Fin d) : ℝ) * Ccross)
  change 0 ≤ Cnote ∧
      coarseCaccioppoliLocalEnergyRadiusProfile Q center
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u)
  refine ⟨?_, ?_⟩
  · dsimp [Cnote]
    exact
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_nonneg_of_thetaRatio_pos
        Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
        hs ht hst
        (thetaRatio_pos_of_closedCubeHarmonicFamily Q a s t (fun _ _ => u)
          hs ht hEllCube)
  · dsimp [Cnote]
    exact
      coarseCaccioppoli_boundary_localPatch_qone_standard_le_noteRhs_explicitSplit_of_constantFamily_localPatchBufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_localizedZeroTraceOnLocalOpenCube
        (Q := Q) (center := center) (a := a) (s := s) (t := t)
        (Clocal := Clocal) (Calpha := Calpha) (Ccross := Ccross) (u0 := u)
        hzero hClocal hCalpha hCcross hCsol_le hs ht hst hEllCube hrawcoeff

/-- Boundary centered Caccioppoli with explicit split budgets and the standard
beta-dependent radius iteration.

This is the `m = 0` centered note-RHS endpoint with all all-radii coefficient
and raw-bridge inputs constructed internally. -/
theorem
    coarseCaccioppoli_boundary_qone_standard_note_of_closedCubeEllipticity_of_buffered_constantFamily_explicitBudgetSplit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t : ℝ) {lam Lam : ℝ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
    0 ≤ Cnote ∧
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u) := by
  let Csol : ℝ := fullVectorPoincareCubeConstant Q
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q Csol
  let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
  rcases coarseCaccioppoliBufferedBudgetSplit_spec
      (Q := Q) (s := s) (t := t) (Csol := Csol) hs ht hst with
    ⟨hCsol_le, hClocal, hCalpha, hCcross, hwork_constant_cross,
      hwork_centered_fronts_alpha, hlarge⟩
  let hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii
        Q a s t Clocal Calpha Ccross :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii.of_closedCubeEllipticity_of_bufferedCutoffRadiusConst_of_centeredFronts
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross)
      hClocal hCalpha.le hCcross hwork_constant_cross hwork_centered_fronts_alpha
      hs ht hst hEllCube hlarge
  let hBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u)
        (fun x => scalarVariationEnergyIntegrand a u x) :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii.of_constantFamily_bufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_closedCubeEllipticity
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross) (u0 := u)
      hClocal hCalpha.le hCcross hCsol_le hs ht hst hEllCube hrawcoeff
  let Cnote : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
      ((Fintype.card (Fin d) : ℝ) * Calpha)
      ((Fintype.card (Fin d) : ℝ) * Ccross)
  change 0 ≤ Cnote ∧
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliBoundaryNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u)
  refine ⟨?_, ?_⟩
  · dsimp [Cnote]
    exact
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_nonneg_of_thetaRatio_pos
        Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
        hs ht hst
        (thetaRatio_pos_of_closedCubeHarmonicFamily Q a s t (fun _ _ => u)
          hs ht hEllCube)
  · dsimp [Cnote]
    exact
      coarseCaccioppoli_boundary_qone_standard_le_noteRhs_explicitSplit_of_profileInputs_of_noteRawBridgeSplitAllRadii
        (Q := Q) (a := a) (s := s) (t := t) (Calpha := Calpha)
        (Ccross := Ccross) (uL2Sq := coarseCaccioppoliHarmonicL2Sq Q a u)
        (baseEnergy := fun x => scalarVariationEnergyIntegrand a u x)
        (w := fun _ _ => u)
        hCalpha hCcross hs ht hst (coarseCaccioppoliHarmonicL2Sq_nonneg Q a u)
        hEllCube
        (CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs.of_constantFamily
          Q a u hEllCube)
        hBridge

/-- Interior centered Caccioppoli with explicit split budgets and the standard
beta-dependent radius iteration. -/
theorem
    coarseCaccioppoli_interior_qone_standard_note_of_closedCubeEllipticity_of_buffered_constantFamily_explicitBudgetSplit
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (a : CoeffField d)
    (s t : ℝ) {lam Lam : ℝ}
    (u : AHarmonicFunction a (openCubeSet Q))
    (hs : 0 < s) (ht : 0 < t) (hst : s + t < 1)
    (hEllCube : IsEllipticFieldOn lam Lam (cubeSet Q) a) :
    let Csol : ℝ := fullVectorPoincareCubeConstant Q
    let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
    let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
    let Cnote : ℝ :=
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
    0 ≤ Cnote ∧
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliInteriorNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u) := by
  let Csol : ℝ := fullVectorPoincareCubeConstant Q
  let Clocal : ℝ := coarseCaccioppoliBufferedLocalBudget Q Csol
  let Calpha : ℝ := coarseCaccioppoliBufferedAlphaBudget Q s Csol
  let Ccross : ℝ := coarseCaccioppoliBufferedCrossBudget Q s Csol
  rcases coarseCaccioppoliBufferedBudgetSplit_spec
      (Q := Q) (s := s) (t := t) (Csol := Csol) hs ht hst with
    ⟨hCsol_le, hClocal, hCalpha, hCcross, hwork_constant_cross,
      hwork_centered_fronts_alpha, hlarge⟩
  let hrawcoeff :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii
        Q a s t Clocal Calpha Ccross :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorFaithfulWorkSmallCubeBufferedExactRawCoefficientBoundsSplitAllRadii.of_closedCubeEllipticity_of_bufferedCutoffRadiusConst_of_centeredFronts
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross)
      hClocal hCalpha.le hCcross hwork_constant_cross hwork_centered_fronts_alpha
      hs ht hst hEllCube hlarge
  let hBoundaryBridge :
      CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u)
        (fun x => scalarVariationEnergyIntegrand a u x) :=
    CoarseCaccioppoliBoundaryCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii.of_constantFamily_bufferedFaithfulWorkSmallCubeExactRawCoefficientBoundsSplitAllRadii_of_closedCubeEllipticity
      (Q := Q) (a := a) (s := s) (t := t) (Clocal := Clocal)
      (Calpha := Calpha) (Ccross := Ccross) (u0 := u)
      hClocal hCalpha.le hCcross hCsol_le hs ht hst hEllCube hrawcoeff
  let hBridge :
      CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii
        Q a s t Calpha Ccross (coarseCaccioppoliHarmonicL2Sq Q a u)
        (fun x => scalarVariationEnergyIntegrand a u x) := by
    simpa [CoarseCaccioppoliInteriorCanonicalHarmonicVectorNoteRawBridgeSplitAllRadii]
      using hBoundaryBridge
  let Cnote : ℝ :=
    coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit Q a s t
      ((Fintype.card (Fin d) : ℝ) * Calpha)
      ((Fintype.card (Fin d) : ℝ) * Ccross)
  change 0 ≤ Cnote ∧
      coarseCaccioppoliLocalizedEnergyRadiusProfile Q
          (fun x => scalarVariationEnergyIntegrand a u x) (1 / 3 : ℝ) ≤
        coarseCaccioppoliInteriorNoteRhs Q a s t Cnote
          (coarseCaccioppoliHarmonicL2Sq Q a u)
  refine ⟨?_, ?_⟩
  · dsimp [Cnote]
    exact
      coarseCaccioppoliBoundaryStandardExplicitNoteConstantSplit_nonneg_of_thetaRatio_pos
        Q a s t
        ((Fintype.card (Fin d) : ℝ) * Calpha)
        ((Fintype.card (Fin d) : ℝ) * Ccross)
        hs ht hst
        (thetaRatio_pos_of_closedCubeHarmonicFamily Q a s t (fun _ _ => u)
          hs ht hEllCube)
  · dsimp [Cnote]
    exact
      coarseCaccioppoli_interior_qone_standard_le_noteRhs_explicitSplit_of_profileInputs_of_noteRawBridgeSplitAllRadii
        (Q := Q) (a := a) (s := s) (t := t) (Calpha := Calpha)
        (Ccross := Ccross) (uL2Sq := coarseCaccioppoliHarmonicL2Sq Q a u)
        (baseEnergy := fun x => scalarVariationEnergyIntegrand a u x)
        (w := fun _ _ => u)
        hCalpha hCcross hs ht hst (coarseCaccioppoliHarmonicL2Sq_nonneg Q a u)
        hEllCube
        (CoarseCaccioppoliBoundaryCanonicalHarmonicProfileInputs.of_constantFamily
          Q a u hEllCube)
        hBridge

end

end Homogenization
