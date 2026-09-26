/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
module

public import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedCanonicalSolution

/-! # Bounded Stability -/

@[expose] public section

open TauCeti.DavisKahan.Sylvester

/-!
# A posteriori stability for bounded Riccati equations

This leaf module turns the interval/exterior Sylvester estimate into an
error bound for approximate bounded Riccati solutions.  The distance between
two angular operators is controlled by the difference of their Riccati
defects whenever the nonlinear Lipschitz coefficient remains below the
spectral gap.  Specializing one operator to an exact contractive solution
gives a residual certificate, and specializing further to the canonical local
solution gives a directly reusable a posteriori estimate.
-/

namespace TauCeti
namespace DavisKahanExt


open DavisKahan

open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Difference equation for arbitrary angular operators, with the difference
of their Riccati defects retained as an inhomogeneous residual. -/
theorem riccati_defect_sub_sylvester_equation
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X Y : E0 →L[ℂ] E1) :
    H.A1 ∘L (X - Y) - (X - Y) ∘L H.A0 =
      (X - Y) ∘L H.B01 ∘L X +
        Y ∘L H.B01 ∘L (X - Y) +
          (riccatiDefect H X - riccatiDefect H Y) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [riccatiDefect, sub_apply, add_apply,
    ContinuousLinearMap.comp_apply, map_sub]
  abel

/-- General local stability estimate for two approximate Riccati solutions.
The denominator is the spectral gap minus the nonlinear Lipschitz
coefficient on the pair `X`, `Y`. -/
theorem norm_sub_le_riccatiDefect_sub_div_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (X Y : E0 →L[ℂ] E1)
    (hcoef : ‖H.B01‖ * (‖X‖ + ‖Y‖) < d) :
    ‖X - Y‖ ≤
      ‖riccatiDefect H X - riccatiDefect H Y‖ /
        (d - ‖H.B01‖ * (‖X‖ + ‖Y‖)) := by
  have hA0sa : IsSelfAdjoint H.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
  have hA1sa : IsSelfAdjoint H.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
  let D : E0 →L[ℂ] E1 := X - Y
  let C : E0 →L[ℂ] E1 :=
    (X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y)
  let E : E0 →L[ℂ] E1 := riccatiDefect H X - riccatiDefect H Y
  have hEq : H.A1 ∘L D - D ∘L H.A0 = C + E := by
    exact riccati_defect_sub_sylvester_equation H X Y
  have hsyl : d * ‖D‖ ≤ ‖C + E‖ :=
    norm_sylvester_le_of_spectrum_intervalExterior
      hA1sa hA0sa hd hlr hA0spec hA1spec hEq
  have hCnorm : ‖C‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ := by
    exact norm_riccati_solution_sub_rhs_le H X Y
  have hrhs : ‖C + E‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ + ‖E‖ := by
    calc
      ‖C + E‖ ≤ ‖C‖ + ‖E‖ := norm_add_le _ _
      _ ≤ ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ + ‖E‖ :=
        add_le_add hCnorm le_rfl
  have hmain : d * ‖D‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ + ‖E‖ :=
    hsyl.trans hrhs
  have hden : 0 < d - ‖H.B01‖ * (‖X‖ + ‖Y‖) := sub_pos.mpr hcoef
  apply (le_div_iff₀ hden).2
  change ‖D‖ * (d - ‖H.B01‖ * (‖X‖ + ‖Y‖)) ≤ ‖E‖
  nlinarith [norm_nonneg D, norm_nonneg E]

/-- If `Y` is an exact solution and both `X` and `Y` are contractive, the
Riccati defect of `X` controls its distance from `Y` with the uniform
stability denominator `d - 2 ‖B01‖`. -/
theorem norm_sub_exact_riccati_solution_le_defect_div
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X Y : E0 →L[ℂ] E1}
    (hY : SolvesRiccati H Y) (hXc : ‖X‖ < 1) (hYc : ‖Y‖ < 1) :
    ‖X - Y‖ ≤ ‖riccatiDefect H X‖ / (d - 2 * ‖H.B01‖) := by
  have hA0sa : IsSelfAdjoint H.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
  have hA1sa : IsSelfAdjoint H.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
  let D : E0 →L[ℂ] E1 := X - Y
  let C : E0 →L[ℂ] E1 :=
    (X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y)
  have hEq : H.A1 ∘L D - D ∘L H.A0 = C + riccatiDefect H X := by
    have hraw := riccati_defect_sub_sylvester_equation H X Y
    rw [hY, sub_zero] at hraw
    exact hraw
  have hsyl : d * ‖D‖ ≤ ‖C + riccatiDefect H X‖ :=
    norm_sylvester_le_of_spectrum_intervalExterior
      hA1sa hA0sa hd hlr hA0spec hA1spec hEq
  have hCnorm : ‖C‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ := by
    exact norm_riccati_solution_sub_rhs_le H X Y
  have hsum : ‖X‖ + ‖Y‖ ≤ 2 := by
    linarith
  have hcoef : ‖H.B01‖ * (‖X‖ + ‖Y‖) ≤ 2 * ‖H.B01‖ := by
    calc
      ‖H.B01‖ * (‖X‖ + ‖Y‖) ≤ ‖H.B01‖ * 2 :=
        mul_le_mul_of_nonneg_left hsum (norm_nonneg H.B01)
      _ = 2 * ‖H.B01‖ := by ring
  have hrhs : ‖C + riccatiDefect H X‖ ≤
      2 * ‖H.B01‖ * ‖D‖ + ‖riccatiDefect H X‖ := by
    calc
      ‖C + riccatiDefect H X‖ ≤ ‖C‖ + ‖riccatiDefect H X‖ :=
        norm_add_le _ _
      _ ≤ ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ +
          ‖riccatiDefect H X‖ := add_le_add hCnorm le_rfl
      _ ≤ 2 * ‖H.B01‖ * ‖D‖ + ‖riccatiDefect H X‖ :=
        add_le_add
          (mul_le_mul_of_nonneg_right hcoef (norm_nonneg D)) le_rfl
  have hmain : d * ‖D‖ ≤
      2 * ‖H.B01‖ * ‖D‖ + ‖riccatiDefect H X‖ :=
    hsyl.trans hrhs
  have hden : 0 < d - 2 * ‖H.B01‖ := sub_pos.mpr hsmall
  apply (le_div_iff₀ hden).2
  change ‖D‖ * (d - 2 * ‖H.B01‖) ≤ ‖riccatiDefect H X‖
  nlinarith [norm_nonneg D, norm_nonneg (riccatiDefect H X)]

/-- A posteriori residual certificate for the canonical local contractive
Riccati solution. -/
theorem norm_sub_canonicalContractiveRiccatiSolution_le_defect_div
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X : E0 →L[ℂ] E1} (hXc : ‖X‖ < 1) :
    ‖X - canonicalContractiveRiccatiSolution
        H hd hlr hA0spec hA1spec hsmall‖ ≤
      ‖riccatiDefect H X‖ / (d - 2 * ‖H.B01‖) := by
  exact norm_sub_exact_riccati_solution_le_defect_div
    H hd hlr hA0spec hA1spec hsmall
    (canonicalContractiveRiccatiSolution_solves
      H hd hlr hA0spec hA1spec hsmall)
    hXc
    (canonicalContractiveRiccatiSolution_norm_lt_one
      H hd hlr hA0spec hA1spec hsmall)

end DavisKahanExt
end TauCeti
