/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.LaurentSeries.Basic

/-!
# Iterated Laurent coefficients

Fubini's theorem writes a torus integral with the first circle integrated first. Consequently
Laurent coefficients can be computed one coordinate at a time.

## Main results

`torusIntegral_succ_inner` is Fubini for the first circle of a coordinate torus.
`multivariableLaurentCoeff_succ` identifies the multivariable coefficient with an iterated
one-variable coefficient in the remaining coordinates.
-/

public noncomputable section

open Complex Set MeasureTheory Function
open scoped Real Topology

namespace SeveralComplexVariables

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- A torus integral can be evaluated by first integrating the first coordinate circle. -/
theorem torusIntegral_succ_inner {f : (Fin (n + 1) → ℂ) → F}
    {c : Fin (n + 1) → ℂ} {r : Fin (n + 1) → ℝ} (hf : TorusIntegrable f c r) :
    torusIntegral f c r = torusIntegral
      (fun y => ∮ x in C(c 0, r 0), f (Fin.cons x y)) (c ∘ Fin.succ) (r ∘ Fin.succ) := by
  let e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm _
  have heπ : e ⁻¹' Icc 0 (fun _ => 2 * π) =
      Icc 0 (2 * π) ×ˢ Icc (0 : Fin n → ℝ) (fun _ => 2 * π) :=
    ((Fin.insertNthOrderIso (fun _ => ℝ) 0).preimage_Icc _ _).trans (Icc_prod_eq _ _)
  rw [torusIntegral, ← hem.map_eq, setIntegral_map_equiv, heπ, Measure.volume_eq_prod,
    ← setIntegral_prod_swap, setIntegral_prod]
  · rw [torusIntegral]
    refine setIntegral_congr_fun measurableSet_Icc fun Θ _ => ?_
    simp only [circleIntegral_def_Icc, ← integral_smul]
    refine setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    simp only [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero,
      Fin.insertNthEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      Function.comp_apply, deriv_circleMap, smul_smul]
    congr 1
    · simp [circleMap, mul_assoc, mul_comm]
    · congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [torusMap, circleMap]
  · have h := hf.function_integrable
    rw [← hem.integrableOn_comp_preimage e.measurableEmbedding, heπ] at h
    exact h.swap

omit [CompleteSpace F] in
/-- A multivariable Laurent coefficient is obtained by taking a circle coefficient first. -/
theorem multivariableLaurentCoeff_succ {f : (Fin (n + 1) → ℂ) → F}
    {r : Fin (n + 1) → ℝ} (hr : ∀ i, 0 < r i)
    (hf : Continuous (fun θ => f (torusMap 0 r θ))) (m : Fin (n + 1) → ℤ) :
    multivariableLaurentCoeff f r m =
      multivariableLaurentCoeff
        (fun y => circleLaurentCoeff (fun x => f (Fin.cons x y)) (r 0) (m 0))
        (r ∘ Fin.succ) (m ∘ Fin.succ) := by
  let g (y : Fin n → ℂ) := ∮ x in C(0, r 0), x ^ (-m 0 - 1) • f (Fin.cons x y)
  let b (y : Fin n → ℂ) := ∏ i, y i ^ (-m i.succ - 1)
  have hcircle (y : Fin n → ℂ) :
      (∮ x in C(0, r 0), (∏ i, (Fin.cons x y : Fin (n + 1) → ℂ) i ^ (-m i - 1)) • f (Fin.cons x
        y)) =
        b y • g y := by
    rw [← circleIntegral.integral_smul]
    apply circleIntegral.integral_congr (hr 0).le
    intro x _
    dsimp only [b, g]
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, mul_smul]
    exact smul_comm _ _ _
  rw [multivariableLaurentCoeff, torusIntegral_succ_inner (torusIntegrable_laurentKernel hr hf m)]
  simp only [Pi.zero_apply]
  simp_rw [hcircle]
  change ((2 * π * I : ℂ) ^ (n + 1))⁻¹ • torusIntegral (fun y => b y • g y) 0 (r ∘ Fin.succ) = _
  have he : (fun y => b y • ((2 * π * I : ℂ)⁻¹ • g y)) =
      (fun y => (2 * π * I : ℂ)⁻¹ • (b y • g y)) := by
    funext y
    exact smul_comm _ _ _
  change _ = ((2 * π * I : ℂ) ^ n)⁻¹ • torusIntegral
    (fun y => b y • ((2 * π * I : ℂ)⁻¹ • g y)) 0 (r ∘ Fin.succ)
  rw [he, torusIntegral_smul, smul_smul, pow_succ, mul_inv]

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
