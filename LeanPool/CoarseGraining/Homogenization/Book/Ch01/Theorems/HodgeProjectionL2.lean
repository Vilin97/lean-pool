/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Hodge Projection L2 -/

namespace Homogenization
namespace Book
namespace Ch01

noncomputable section

/-!
# Ch1 Hilbert `L²` Hodge projection input

This file proves the Hilbert-space core of the unit Dirichlet Hodge projection
estimate.  The concrete negative-Besov theorem still needs boundedness of the
same projection in the Besov scale; the orthogonality and energy estimate here
are unconditional.
-/

/-- A zero-trace potential field has the `L²` membership supplied by its
`H¹₀` primitive. -/
theorem IsPotentialZeroTraceOn.memVectorL2
    {d : ℕ} {U : Set (Vec d)} {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn U w) :
    MemVectorL2 U w := by
  rcases hw with ⟨u, hgrad⟩
  simpa [hgrad] using u.toH1Function.grad_memVectorL2

/-- Zero-trace potential fields are `L²`-orthogonal to solenoidal fields. -/
theorem inner_toHilbertVectorL2OfVecField_eq_zero_of_isPotentialZeroTraceOn_of_isSolenoidalOn
    {d : ℕ} (Q : TriadicCube d) {w z : Vec d → Vec d}
    (hwMem : MemVectorL2 (cubeSet Q) w)
    (hzMem : MemVectorL2 (cubeSet Q) z)
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hz : IsSolenoidalOn (cubeSet Q) z) :
    inner ℝ (toHilbertVectorL2OfVecField hwMem)
      (toHilbertVectorL2OfVecField hzMem) = 0 := by
  rcases hw with ⟨u, hgrad⟩
  calc
    inner ℝ (toHilbertVectorL2OfVecField hwMem)
        (toHilbertVectorL2OfVecField hzMem)
        = ∫ x in cubeSet Q, vecDot (w x) (z x) ∂MeasureTheory.volume := by
            exact inner_toHilbertVectorL2OfVecField_eq_integral
              (U := cubeSet Q) hwMem hzMem
    _ = ∫ x in cubeSet Q, vecDot (z x) (w x) ∂MeasureTheory.volume := by
            refine MeasureTheory.integral_congr_ae ?_
            exact Filter.Eventually.of_forall fun x => vecDot_comm (w x) (z x)
    _ = 0 := by
            simpa [hgrad] using hz u

/-- The zero-trace primitive of a Hodge potential component solves the
Dirichlet variational problem with right-hand side `-F`.

This is the PDE identity behind the unit Hodge projection: if `w` is
zero-trace potential and `w + F` is solenoidal, then the primitive of `w`
tests against every zero-trace gradient as `-F`. -/
theorem exists_h10Function_gradient_eq_and_firstVariation_eq_neg_of_isPotentialZeroTraceOn_of_isSolenoidalOn
    {d : ℕ} {U : Set (Vec d)} {w F : Vec d → Vec d}
    (hF : MemVectorL2 U F)
    (hw : IsPotentialZeroTraceOn U w)
    (hsol : IsSolenoidalOn U (fun x => w x + F x)) :
    ∃ u : H10Function U,
      u.toH1Function.grad = w ∧
        ∀ φ : H10Function U,
          ∫ x in U, vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume =
            -∫ x in U, vecDot (F x) (φ.toH1Function.grad x)
              ∂MeasureTheory.volume := by
  rcases hw with ⟨u, rfl⟩
  refine ⟨u, rfl, ?_⟩
  intro φ
  have hu_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2
      u.toH1Function.grad_memVectorL2 φ.toH1Function.grad_memVectorL2
  have hF_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hF φ.toH1Function.grad_memVectorL2
  have hsplit :
      ∫ x in U,
          vecDot (u.toH1Function.grad x + F x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume +
        ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume := by
    have hpoint :
        (fun x =>
            vecDot (u.toH1Function.grad x + F x) (φ.toH1Function.grad x)) =
          fun x =>
            vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x) +
              vecDot (F x) (φ.toH1Function.grad x) := by
      funext x
      simp [vecDot_add_left]
    rw [hpoint]
    exact MeasureTheory.integral_add hu_int.integrable hF_int.integrable
  have hzero :
      ∫ x in U, vecDot (u.toH1Function.grad x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume +
        ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume = 0 := by
    simpa [hsplit] using hsol φ
  linarith

/--
Unit Dirichlet Hodge projection estimate in the Hilbert `L²` norm.

If `w` is the zero-trace potential component and `w + F` is solenoidal, both
components are controlled by the forcing field `F`.
-/
theorem unitHodgeProjectionL2Estimate
    {d : ℕ} (Q : TriadicCube d) (w F : Vec d → Vec d)
    (hF : MemVectorL2 (cubeSet Q) F)
    (hw : IsPotentialZeroTraceOn (cubeSet Q) w)
    (hsol : IsSolenoidalOn (cubeSet Q) (fun x => w x + F x)) :
    ‖toHilbertVectorL2OfVecField (IsPotentialZeroTraceOn.memVectorL2 hw)‖ +
        ‖toHilbertVectorL2OfVecField ((IsPotentialZeroTraceOn.memVectorL2 hw).add hF)‖ ≤
      2 * ‖toHilbertVectorL2OfVecField hF‖ := by
  let hwMem : MemVectorL2 (cubeSet Q) w := IsPotentialZeroTraceOn.memVectorL2 hw
  let W : HilbertVectorL2 (cubeSet Q) := toHilbertVectorL2OfVecField hwMem
  let Z : HilbertVectorL2 (cubeSet Q) := toHilbertVectorL2OfVecField (hwMem.add hF)
  let FF : HilbertVectorL2 (cubeSet Q) := toHilbertVectorL2OfVecField hF
  have horth : inner ℝ W Z = 0 := by
    dsimp [W, Z, hwMem]
    exact
      inner_toHilbertVectorL2OfVecField_eq_zero_of_isPotentialZeroTraceOn_of_isSolenoidalOn
        Q (IsPotentialZeroTraceOn.memVectorL2 hw)
          ((IsPotentialZeroTraceOn.memVectorL2 hw).add hF) hw hsol
  have hZ_eq : Z = W + FF := by
    dsimp [Z, W, FF, hwMem]
    exact toHilbertVectorL2OfVecField_add (IsPotentialZeroTraceOn.memVectorL2 hw) hF
  have hF_eq : FF = Z - W := by
    rw [hZ_eq]
    abel
  have horthZW : inner ℝ Z W = 0 := by
    simpa [real_inner_comm] using horth
  have hnormF_mul : ‖FF‖ * ‖FF‖ = ‖Z‖ * ‖Z‖ + ‖W‖ * ‖W‖ := by
    rw [hF_eq]
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      norm_sub_sq_eq_norm_sq_add_norm_sq_real (x := Z) (y := W) horthZW
  have hW_sq_le : ‖W‖ ^ 2 ≤ ‖FF‖ ^ 2 := by
    have hnormF_sq : ‖FF‖ ^ 2 = ‖Z‖ ^ 2 + ‖W‖ ^ 2 := by
      nlinarith [hnormF_mul]
    nlinarith [sq_nonneg ‖Z‖]
  have hZ_sq_le : ‖Z‖ ^ 2 ≤ ‖FF‖ ^ 2 := by
    have hnormF_sq : ‖FF‖ ^ 2 = ‖Z‖ ^ 2 + ‖W‖ ^ 2 := by
      nlinarith [hnormF_mul]
    nlinarith [sq_nonneg ‖W‖]
  have hW_le : ‖W‖ ≤ ‖FF‖ := le_of_sq_le_sq hW_sq_le (norm_nonneg FF)
  have hZ_le : ‖Z‖ ≤ ‖FF‖ := le_of_sq_le_sq hZ_sq_le (norm_nonneg FF)
  change ‖W‖ + ‖Z‖ ≤ 2 * ‖FF‖
  nlinarith

end

end Ch01
end Book
end Homogenization
