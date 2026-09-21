/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 Thinking
-/
import LeanPool.DavisKahan.DavisKahan.Riccati.BoundedReduction
import LeanPool.DavisKahan.DavisKahan.Sylvester.Spectrum

/-! # Bounded Estimates -/

open TauCeti.DavisKahan.Sylvester

/-!
# Bounded Riccati estimates from an interval/exterior spectral gap

This leaf module applies the genuine-spectrum constant-one Sylvester estimate
to bounded Riccati solutions over a complex Hilbert space.  It isolates the
linear Sylvester equation hidden in the nonlinear Riccati equation, controls
its quadratic right-hand side, obtains a conservative contractive norm bound,
and proves uniqueness of a contractive solution under the standard local
small-coupling threshold.

The hypotheses use the spectra of the actual diagonal block operators.  This
avoids the provisional restricted-spectrum-on-top interface and gives the
analytic theorem in the representation consumed by the proved Sylvester
estimate.
-/

namespace TauCeti
namespace DavisKahanExt


open scoped InnerProductSpace

variable {E0 : Type*} [NormedAddCommGroup E0] [InnerProductSpace ℂ E0]
  [CompleteSpace E0]
variable {E1 : Type*} [NormedAddCommGroup E1] [InnerProductSpace ℂ E1]
  [CompleteSpace E1]

/-- The mutually adjoint off-diagonal blocks have the same operator norm. -/
theorem offDiagonalBlock_norm_eq
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1)) :
    ‖H.B10‖ = ‖H.B01‖ := by
  have hAdj : H.B01 = H.B10.adjoint := by
    apply (ContinuousLinearMap.eq_adjoint_iff H.B01 H.B10).2
    intro x y
    exact H.offDiagonalAdjoint y x
  calc
    ‖H.B10‖ = ‖H.B10.adjoint‖ := by
      symm
      exact ContinuousLinearMap.adjoint.norm_map _
    _ = ‖H.B01‖ := by rw [← hAdj]

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- A bounded Riccati solution satisfies a linear Sylvester equation whose
right-hand side contains the quadratic correction and the lower-left block. -/
theorem riccati_sylvester_equation
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    H.A1 ∘L X - X ∘L H.A0 = X ∘L H.B01 ∘L X - H.B10 := by
  apply ContinuousLinearMap.ext
  intro u
  have hu := (solvesRiccati_iff_pointwise H X).1 hX u
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  calc
    H.A1 (X u) - X (H.A0 u) =
        (H.B10 u + H.A1 (X u)) - (H.B10 u + X (H.A0 u)) := by
      abel
    _ = X (H.A0 u + H.B01 (X u)) - (H.B10 u + X (H.A0 u)) := by
      rw [hu]
    _ = X (H.B01 (X u)) - H.B10 u := by
      rw [map_add]
      abel

/-- Norm control for the nonlinear right-hand side of the Riccati Sylvester
equation. -/
theorem norm_riccati_sylvester_rhs_le
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X : E0 →L[ℂ] E1) :
    ‖X ∘L H.B01 ∘L X - H.B10‖ ≤
      ‖H.B01‖ * (1 + ‖X‖ ^ 2) := by
  have hquad : ‖X ∘L H.B01 ∘L X‖ ≤
      (‖X‖ * ‖H.B01‖) * ‖X‖ := by
    calc
      ‖X ∘L H.B01 ∘L X‖ ≤ ‖X‖ * ‖H.B01 ∘L X‖ :=
        ContinuousLinearMap.opNorm_comp_le X (H.B01 ∘L X)
      _ ≤ ‖X‖ * (‖H.B01‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le H.B01 X) (norm_nonneg X)
      _ = (‖X‖ * ‖H.B01‖) * ‖X‖ := by ring
  calc
    ‖X ∘L H.B01 ∘L X - H.B10‖ ≤
        ‖X ∘L H.B01 ∘L X‖ + ‖H.B10‖ := norm_sub_le _ _
    _ ≤ (‖X‖ * ‖H.B01‖) * ‖X‖ + ‖H.B10‖ :=
      add_le_add hquad le_rfl
    _ = ‖H.B01‖ * (1 + ‖X‖ ^ 2) := by
      rw [offDiagonalBlock_norm_eq H]
      ring

/-- The interval/exterior Sylvester estimate turns the Riccati equation into
the scalar quadratic majorant
`d * ‖X‖ ≤ ‖B01‖ * (1 + ‖X‖ ^ 2)`. -/
theorem norm_riccati_solution_quadratic_le_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X) :
    d * ‖X‖ ≤ ‖H.B01‖ * (1 + ‖X‖ ^ 2) := by
  have hA0sa : IsSelfAdjoint H.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
  have hA1sa : IsSelfAdjoint H.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
  have hsyl := norm_sylvester_le_of_spectrum_intervalExterior
    hA1sa hA0sa hd hlr hA0spec hA1spec
    (riccati_sylvester_equation H hX)
  exact hsyl.trans (norm_riccati_sylvester_rhs_le H X)

/-- A contractive solution obeys the elementary conservative estimate
`‖X‖ ≤ 2 ‖B01‖ / d`.  This follows directly from the quadratic majorant and
is enough, together with `2 ‖B01‖ < d`, to keep the fixed-point branch inside
the open unit ball. -/
theorem norm_riccati_solution_le_two_mul_div_of_contractive_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    {X : E0 →L[ℂ] E1} (hX : SolvesRiccati H X)
    (hXc : ‖X‖ < 1) :
    ‖X‖ ≤ 2 * ‖H.B01‖ / d := by
  have hquad := norm_riccati_solution_quadratic_le_of_spectrum_gap
    H hd hlr hA0spec hA1spec hX
  have hX0 : 0 ≤ ‖X‖ := norm_nonneg X
  have hXsq : ‖X‖ ^ 2 ≤ 1 := by nlinarith
  have hrhs : ‖H.B01‖ * (1 + ‖X‖ ^ 2) ≤ 2 * ‖H.B01‖ := by
    nlinarith [norm_nonneg H.B01]
  have hmul : ‖X‖ * d ≤ 2 * ‖H.B01‖ := by
    rw [mul_comm]
    exact hquad.trans hrhs
  exact (le_div_iff₀ hd).2 hmul

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Difference equation for two bounded Riccati solutions. -/
theorem riccati_solution_sub_sylvester_equation
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {X Y : E0 →L[ℂ] E1}
    (hX : SolvesRiccati H X) (hY : SolvesRiccati H Y) :
    H.A1 ∘L (X - Y) - (X - Y) ∘L H.A0 =
      (X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y) := by
  calc
    H.A1 ∘L (X - Y) - (X - Y) ∘L H.A0 =
        (H.A1 ∘L X - X ∘L H.A0) -
          (H.A1 ∘L Y - Y ∘L H.A0) := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [sub_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel
    _ = (X ∘L H.B01 ∘L X - H.B10) -
          (Y ∘L H.B01 ∘L Y - H.B10) := by
      rw [riccati_sylvester_equation H hX,
        riccati_sylvester_equation H hY]
    _ = (X - Y) ∘L H.B01 ∘L X +
          Y ∘L H.B01 ∘L (X - Y) := by
      apply ContinuousLinearMap.ext
      intro u
      simp only [sub_apply, add_apply, ContinuousLinearMap.comp_apply, map_sub]
      abel

omit [CompleteSpace E0] [CompleteSpace E1] in
/-- Norm control for the difference-equation right-hand side. -/
theorem norm_riccati_solution_sub_rhs_le
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    (X Y : E0 →L[ℂ] E1) :
    ‖(X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y)‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖X - Y‖ := by
  have hleft : ‖(X - Y) ∘L H.B01 ∘L X‖ ≤
      (‖X - Y‖ * ‖H.B01‖) * ‖X‖ := by
    calc
      ‖(X - Y) ∘L H.B01 ∘L X‖ ≤
          ‖X - Y‖ * ‖H.B01 ∘L X‖ :=
        ContinuousLinearMap.opNorm_comp_le (X - Y) (H.B01 ∘L X)
      _ ≤ ‖X - Y‖ * (‖H.B01‖ * ‖X‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le H.B01 X) (norm_nonneg (X - Y))
      _ = (‖X - Y‖ * ‖H.B01‖) * ‖X‖ := by ring
  have hright : ‖Y ∘L H.B01 ∘L (X - Y)‖ ≤
      (‖Y‖ * ‖H.B01‖) * ‖X - Y‖ := by
    calc
      ‖Y ∘L H.B01 ∘L (X - Y)‖ ≤
          ‖Y‖ * ‖H.B01 ∘L (X - Y)‖ :=
        ContinuousLinearMap.opNorm_comp_le Y (H.B01 ∘L (X - Y))
      _ ≤ ‖Y‖ * (‖H.B01‖ * ‖X - Y‖) :=
        mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.opNorm_comp_le H.B01 (X - Y)) (norm_nonneg Y)
      _ = (‖Y‖ * ‖H.B01‖) * ‖X - Y‖ := by ring
  calc
    ‖(X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y)‖ ≤
        ‖(X - Y) ∘L H.B01 ∘L X‖ +
          ‖Y ∘L H.B01 ∘L (X - Y)‖ := norm_add_le _ _
    _ ≤ (‖X - Y‖ * ‖H.B01‖) * ‖X‖ +
          (‖Y‖ * ‖H.B01‖) * ‖X - Y‖ := add_le_add hleft hright
    _ = ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖X - Y‖ := by ring

/-- Under an interval/exterior gap and the local threshold
`2 ‖B01‖ < d`, a contractive bounded Riccati solution is unique. -/
theorem unique_contractive_riccati_solution_of_spectrum_gap
    (H : BlockOperatorData (𝕜 := ℂ) (E0 := E0) (E1 := E1))
    {left right d : ℝ} (hd : 0 < d) (hlr : left ≤ right)
    (hA0spec : spectrum ℝ H.A0 ⊆ Set.Icc left right)
    (hA1spec : ∀ x ∈ spectrum ℝ H.A1,
      x ≤ left - d ∨ right + d ≤ x)
    (hsmall : 2 * ‖H.B01‖ < d)
    {X Y : E0 →L[ℂ] E1}
    (hX : SolvesRiccati H X) (hY : SolvesRiccati H Y)
    (hXc : ‖X‖ < 1) (hYc : ‖Y‖ < 1) :
    X = Y := by
  have hA0sa : IsSelfAdjoint H.A0 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint0
  have hA1sa : IsSelfAdjoint H.A1 :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr H.selfAdjoint1
  let D : E0 →L[ℂ] E1 := X - Y
  let C : E0 →L[ℂ] E1 :=
    (X - Y) ∘L H.B01 ∘L X + Y ∘L H.B01 ∘L (X - Y)
  have hEq : H.A1 ∘L D - D ∘L H.A0 = C := by
    exact riccati_solution_sub_sylvester_equation H hX hY
  have hsyl : d * ‖D‖ ≤ ‖C‖ :=
    norm_sylvester_le_of_spectrum_intervalExterior
      hA1sa hA0sa hd hlr hA0spec hA1spec hEq
  have hCnorm : ‖C‖ ≤
      ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ := by
    exact norm_riccati_solution_sub_rhs_le H X Y
  have hcoef : ‖H.B01‖ * (‖X‖ + ‖Y‖) < d := by
    have hB0 : 0 ≤ ‖H.B01‖ := norm_nonneg H.B01
    have hsum : ‖X‖ + ‖Y‖ < 2 := by linarith
    calc
      ‖H.B01‖ * (‖X‖ + ‖Y‖) ≤ ‖H.B01‖ * 2 :=
        mul_le_mul_of_nonneg_left (le_of_lt hsum) hB0
      _ = 2 * ‖H.B01‖ := by ring
      _ < d := hsmall
  have hzero : ‖D‖ = 0 := by
    have hbound : d * ‖D‖ ≤
        ‖H.B01‖ * (‖X‖ + ‖Y‖) * ‖D‖ := hsyl.trans hCnorm
    nlinarith [norm_nonneg D]
  have hD : D = 0 := norm_eq_zero.mp hzero
  change X - Y = 0 at hD
  exact sub_eq_zero.mp hD

end DavisKahanExt
end TauCeti
