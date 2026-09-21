/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.CoefficientFieldHilbert
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CoerciveH1
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.H1Graph
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2

/-! # Neumann RHS -/

namespace Homogenization

open MeasureTheory

/-!
# Mean-zero Neumann problems with right-hand side

This file starts the mean-zero Neumann-side RHS development. The current layer
packages the weak formulation, the coefficient-weighted Lax-Milgram solution,
the energy identity, the basic elliptic energy estimate, and the qualitative
uniqueness statement once a mean-zero coercive estimate is supplied.
-/

/-- Weak mean-zero Neumann formulation of `- div (a grad u) = div g` on `U`. -/
def IsMeanZeroNeumannRhsWeakSolution {d : ℕ}
    (a : CoeffField d) (U : Set (Vec d)) (u : H1MeanZeroFunction U)
    (g : Vec d → Vec d) : Prop :=
  ∀ φ : H1MeanZeroFunction U,
    ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
      ∂MeasureTheory.volume =
    ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume

theorem integrableOn_vecNormSq_meanZeroGrad
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (u : H1MeanZeroFunction U) :
    MeasureTheory.IntegrableOn (fun x => vecNormSq (u.toH1Function.grad x)) U := by
  simpa [vecNormSq] using
    (integrableOn_vecDot_of_memVectorL2
      u.toH1Function.grad_memVectorL2 u.toH1Function.grad_memVectorL2)

theorem integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn_meanZero
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U a) (u : H1MeanZeroFunction U) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (u.toH1Function.grad x)
        (matVecMul (a x) (u.toH1Function.grad x))) U := by
  have hflux : MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2
  exact integrableOn_vecDot_of_memVectorL2 u.toH1Function.grad_memVectorL2 hflux

namespace H1CoerciveHilbert

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
variable {a : CoeffField d} {lam Lam : ℝ}

/-- The coefficient-weighted gradient projection on the coercive Hilbert graph. -/
noncomputable def coeffGradientCLM (hEll : IsEllipticFieldOn lam Lam U a) :
    H1CoerciveHilbertSpace (U := U) →L[ℝ] HilbertVectorL2 U :=
  (hilbertCoeffOperator hEll).comp (gradientCLM (U := U))

/-- The coefficient-weighted gradient bilinear form on the coercive Hilbert
graph. -/
noncomputable def coeffGradientBilin (hEll : IsEllipticFieldOn lam Lam U a) :
    H1CoerciveHilbertSpace (U := U) →L[ℝ]
      H1CoerciveHilbertSpace (U := U) →L[ℝ] ℝ :=
  ContinuousLinearMap.bilinearComp (isBoundedBilinearMap_inner (𝕜 := ℝ)).toContinuousLinearMap
    (coeffGradientCLM (U := U) hEll) (gradientCLM (U := U))

@[simp] theorem coeffGradientBilin_apply (hEll : IsEllipticFieldOn lam Lam U a)
    (z w : H1CoerciveHilbertSpace (U := U)) :
    coeffGradientBilin (U := U) hEll z w =
      inner ℝ
        (hilbertCoeffOperator hEll (gradient (U := U) z))
        (gradient (U := U) w) := by
  simp [coeffGradientBilin, coeffGradientCLM, gradient, gradientCLM]; rfl

theorem coeffGradientBilin_apply_toH1CoerciveHilbertSpace
    (hEll : IsEllipticFieldOn lam Lam U a)
    (u v : H1MeanZeroFunction U) :
    coeffGradientBilin (U := U) hEll
        (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
        (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v) =
      ∫ x in U,
        vecDot (matVecMul (a x) (u.toH1Function.grad x)) (v.toH1Function.grad x)
          ∂MeasureTheory.volume := by
  have hAu :
      hilbertCoeffOperator hEll u.gradToHilbertVectorL2 =
        toHilbertVectorL2OfVecField
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2) := by
    simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
      hilbertCoeffOperator_toHilbertVectorL2OfVecField
        (U := U) (a := a) (lam := lam) (Lam := Lam) hEll u.toH1Function.grad_memVectorL2
  calc
    coeffGradientBilin (U := U) hEll
        (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
        (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
        =
          inner ℝ (hilbertCoeffOperator hEll u.gradToHilbertVectorL2) v.gradToHilbertVectorL2 := by
            simp [coeffGradientBilin_apply]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2))
          v.gradToHilbertVectorL2 := by
            rw [hAu]
    _ =
        ∫ x in U,
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (v.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
                inner_toHilbertVectorL2OfVecField_eq_integral
                  (U := U)
                  (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2)
                  v.toH1Function.grad_memVectorL2

theorem coeffGradientBilin_apply_eq_integral
    (hEll : IsEllipticFieldOn lam Lam U a)
    (z w : H1CoerciveHilbertSpace (U := U)) :
    coeffGradientBilin (U := U) hEll z w =
      ∫ x in U,
        vecDot
          (matVecMul (a x) ((toH1MeanZeroFunction (U := U) z).toH1Function.grad x))
          ((toH1MeanZeroFunction (U := U) w).toH1Function.grad x)
          ∂MeasureTheory.volume := by
  let u : H1MeanZeroFunction U := toH1MeanZeroFunction (U := U) z
  let v : H1MeanZeroFunction U := toH1MeanZeroFunction (U := U) w
  have huGrad : u.gradToHilbertVectorL2 = gradient (U := U) z := by
    simp [u]
  have hvGrad : v.gradToHilbertVectorL2 = gradient (U := U) w := by
    simp [v]
  have hAu :
      hilbertCoeffOperator hEll u.gradToHilbertVectorL2 =
        toHilbertVectorL2OfVecField
          (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2) := by
    simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
      hilbertCoeffOperator_toHilbertVectorL2OfVecField
        (U := U) (a := a) (lam := lam) (Lam := Lam) hEll u.toH1Function.grad_memVectorL2
  calc
    coeffGradientBilin (U := U) hEll z w
        = inner ℝ (hilbertCoeffOperator hEll (gradient (U := U) z)) (gradient (U := U) w) := by
            simp [coeffGradientBilin_apply]
    _ = inner ℝ (hilbertCoeffOperator hEll u.gradToHilbertVectorL2) v.gradToHilbertVectorL2 := by
          rw [← huGrad, ← hvGrad]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField
            (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2))
          v.gradToHilbertVectorL2 := by
            rw [hAu]
    _ =
        ∫ x in U,
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (v.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
                inner_toHilbertVectorL2OfVecField_eq_integral
                  (U := U)
                  (memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2)
                  v.toH1Function.grad_memVectorL2

theorem coeffGradientBilin_self_ge_lam_mul_norm_gradient_sq
    (hEll : IsEllipticFieldOn lam Lam U a)
    (z : H1CoerciveHilbertSpace (U := U)) :
    lam * ‖gradient (U := U) z‖ ^ 2 ≤ coeffGradientBilin (U := U) hEll z z := by
  let u : H1MeanZeroFunction U := toH1MeanZeroFunction (U := U) z
  have hsqInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)) U := by
    simpa [vecNormSq] using integrableOn_vecNormSq_meanZeroGrad u
  have henergyInt :
      MeasureTheory.IntegrableOn
        (fun x =>
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (u.toH1Function.grad x)) U :=
    by
      simpa [vecDot_comm] using
        integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn_meanZero hEll u
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint :
      ∀ᵐ x ∂ volumeMeasureOn U,
        lam * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ≤
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (u.toH1Function.grad x) := by
    filter_upwards [hmem] with x hx
    simpa [vecNormSq, vecDot_comm] using (hEll.2 x hx).2.2.1 (u.toH1Function.grad x)
  have hgradSq :
      ‖gradient (U := U) z‖ ^ 2 =
        ∫ x in U, vecDot (u.toH1Function.grad x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
    have huGrad : u.gradToHilbertVectorL2 = gradient (U := U) z := by
      simp [u]
    calc
      ‖gradient (U := U) z‖ ^ 2 = inner ℝ (gradient (U := U) z) (gradient (U := U) z) := by
            symm
            exact real_inner_self_eq_norm_sq (gradient (U := U) z)
      _ = inner ℝ u.gradToHilbertVectorL2 u.gradToHilbertVectorL2 := by
            rw [← huGrad]
      _ =
          ∫ x in U, vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              simpa [H1MeanZeroFunction.gradToHilbertVectorL2, H1Function.gradToHilbertVectorL2] using
                inner_toHilbertVectorL2OfVecField_eq_integral
                  (U := U) u.toH1Function.grad_memVectorL2 u.toH1Function.grad_memVectorL2
  calc
    lam * ‖gradient (U := U) z‖ ^ 2
        = lam *
            ∫ x in U, vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)
              ∂MeasureTheory.volume := by
                rw [hgradSq]
    _ =
        ∫ x in U, lam * vecDot (u.toH1Function.grad x) (u.toH1Function.grad x)
          ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
    _ ≤
        ∫ x in U,
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (u.toH1Function.grad x)
            ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae (hsqInt.const_mul lam) henergyInt hpoint
    _ = coeffGradientBilin (U := U) hEll z z := by
          symm
          simpa [u] using coeffGradientBilin_apply_eq_integral
            (U := U) (a := a) (lam := lam) (Lam := Lam) hEll z z

theorem isCoercive_coeffGradientBilin
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsCoercive (coeffGradientBilin (U := U) hEll) := by
  let M : ℝ := hC.fixedValue + 1
  rcases hne with ⟨x, hx⟩
  have hlam : 0 < lam := (hEll.2 x hx).1
  have hM_pos : 0 < M := by
    linarith [hC.constant_nonneg]
  refine ⟨lam * M⁻¹ * M⁻¹, by positivity, ?_⟩
  intro z
  have hbound : ‖z‖ ≤ M * ‖gradient (U := U) z‖ := by
    simpa [M] using norm_le_max_constant_one_mul_norm_gradient (d := d) (U := U) hC z
  have hscaled : M⁻¹ * ‖z‖ ≤ ‖gradient (U := U) z‖ := by
    calc
      M⁻¹ * ‖z‖ ≤ M⁻¹ * (M * ‖gradient (U := U) z‖) := by
            gcongr
      _ = ‖gradient (U := U) z‖ := by
            field_simp [hM_pos.ne']
  have hsq :
      (M⁻¹ * ‖z‖) ^ 2 ≤ ‖gradient (U := U) z‖ ^ 2 := by
    have hleft_nonneg : 0 ≤ M⁻¹ * ‖z‖ := by
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hM_pos)) (norm_nonneg _)
    have hright_nonneg : 0 ≤ ‖gradient (U := U) z‖ := norm_nonneg _
    have hM_abs : |M| = M := abs_of_nonneg (le_of_lt hM_pos)
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg, abs_inv, hM_abs] using
        hscaled
  calc
    (lam * M⁻¹ * M⁻¹) * ‖z‖ * ‖z‖ = lam * (M⁻¹ * ‖z‖) ^ 2 := by
          ring
    _ ≤ lam * ‖gradient (U := U) z‖ ^ 2 := by
          nlinarith [hsq, le_of_lt hlam]
    _ ≤ coeffGradientBilin (U := U) hEll z z :=
          coeffGradientBilin_self_ge_lam_mul_norm_gradient_sq (U := U) hEll z

/-- The unique coercive-Hilbert graph element solving the coefficient-weighted
gradient problem with forcing `f`. -/
noncomputable def coeffGradientProblemSolution {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    H1CoerciveHilbertSpace (U := U) := by
  let hB : IsCoercive (coeffGradientBilin (U := U) hEll) :=
    isCoercive_coeffGradientBilin (U := U) (a := a) (lam := lam) (Lam := Lam) hC hne hEll
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  exact e.symm (forcingRieszRep (U := U) hf)

theorem coeffGradientBilin_coeffGradientProblemSolution_apply {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (z : H1CoerciveHilbertSpace (U := U)) :
    coeffGradientBilin (U := U) hEll
        (coeffGradientProblemSolution (U := U) (a := a) (lam := lam) (Lam := Lam)
          hf hC hne hEll) z =
      forcingFunctionalCLM (U := U) hf z := by
  let hB : IsCoercive (coeffGradientBilin (U := U) hEll) :=
    isCoercive_coeffGradientBilin (U := U) (a := a) (lam := lam) (Lam := Lam) hC hne hEll
  let e : H1CoerciveHilbertSpace (U := U) ≃L[ℝ] H1CoerciveHilbertSpace (U := U) :=
    hB.continuousLinearEquivOfBilin
  calc
    coeffGradientBilin (U := U) hEll
        (coeffGradientProblemSolution (U := U) (a := a) (lam := lam) (Lam := Lam)
          hf hC hne hEll) z
        = inner ℝ (e (coeffGradientProblemSolution
            (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll)) z := by
            symm
            simpa [e, hB] using
              hB.continuousLinearEquivOfBilin_apply
                (coeffGradientProblemSolution
                  (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll)
                z
    _ = inner ℝ (forcingRieszRep (U := U) hf) z := by
          rw [coeffGradientProblemSolution, e.apply_symm_apply]
    _ = forcingFunctionalCLM (U := U) hf z := by
          exact inner_forcingRieszRep_apply (U := U) hf z

end H1CoerciveHilbert

namespace H1MeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
variable {a : CoeffField d} {lam Lam : ℝ}

/-- The mean-zero `H¹` weak solution represented by the coefficient-weighted
coercive Hilbert graph solution. -/
noncomputable def coeffGradientProblemSolution {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    H1MeanZeroFunction U :=
  H1CoerciveHilbert.toH1MeanZeroFunction
    (H1CoerciveHilbert.coeffGradientProblemSolution
      (d := d) (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll)

theorem coeffGradientProblemSolution_firstVariation_eq_integral {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (u : H1MeanZeroFunction U) :
    ∫ x in U,
        vecDot
          (matVecMul (a x)
            ((coeffGradientProblemSolution
              (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll).toH1Function.grad x))
          (u.toH1Function.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (f x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  let zsol : H1CoerciveHilbertSpace (U := U) :=
    H1CoerciveHilbert.coeffGradientProblemSolution
      (d := d) (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll
  let v : H1MeanZeroFunction U := coeffGradientProblemSolution
    (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll
  have hzEq :
      H1CoerciveHilbert.coeffGradientBilin (U := U) hEll
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
        =
      H1CoerciveHilbert.coeffGradientBilin (U := U) hEll zsol
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) := by
    have hvGrad :
        v.gradToHilbertVectorL2 = H1CoerciveHilbert.gradient (U := U) zsol := by
      unfold v zsol
      simp [coeffGradientProblemSolution]
    calc
      H1CoerciveHilbert.coeffGradientBilin (U := U) hEll
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
          =
            inner ℝ
              (hilbertCoeffOperator hEll v.gradToHilbertVectorL2)
              u.gradToHilbertVectorL2 := by
                simp [H1CoerciveHilbert.coeffGradientBilin_apply]
      _ =
            inner ℝ
              (hilbertCoeffOperator hEll (H1CoerciveHilbert.gradient (U := U) zsol))
              u.gradToHilbertVectorL2 := by
                rw [hvGrad]
      _ =
            H1CoerciveHilbert.coeffGradientBilin (U := U) hEll zsol
              (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) := by
                simp [H1CoerciveHilbert.coeffGradientBilin_apply]
  have hpair :
      H1CoerciveHilbert.coeffGradientBilin (U := U) hEll
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) =
        gradientPairing hf u := by
    calc
      H1CoerciveHilbert.coeffGradientBilin (U := U) hEll
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
          (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
          =
            H1CoerciveHilbert.coeffGradientBilin (U := U) hEll zsol
              (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) := hzEq
      _ = H1CoerciveHilbert.forcingFunctionalCLM (U := U) hf
            (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) :=
          H1CoerciveHilbert.coeffGradientBilin_coeffGradientProblemSolution_apply
            (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll
            (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u)
      _ = gradientPairing hf u := by
            simpa using
              H1MeanZeroFunction.H1CoerciveHilbert_forcingFunctionalCLM_apply_toH1CoerciveHilbertSpace
                (U := U) hf u
  calc
    ∫ x in U,
        vecDot
          (matVecMul (a x)
            ((coeffGradientProblemSolution
              (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll).toH1Function.grad x))
          (u.toH1Function.grad x) ∂MeasureTheory.volume
        =
          H1CoerciveHilbert.coeffGradientBilin (U := U) hEll
            (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) v)
            (H1MeanZeroFunction.toH1CoerciveHilbertSpace (U := U) u) := by
              symm
              simpa [v] using
                H1CoerciveHilbert.coeffGradientBilin_apply_toH1CoerciveHilbertSpace
                  (U := U) (a := a) (lam := lam) (Lam := Lam) hEll v u
    _ = gradientPairing hf u := hpair
    _ = ∫ x in U, vecDot (f x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
          exact gradientPairing_eq_integral (U := U) hf u

end H1MeanZeroFunction

namespace H1Function

variable {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
variable {a : CoeffField d} {lam Lam : ℝ}

theorem coeffGradientProblemSolution_firstVariation_eq_integral {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (u : H1Function U) :
    ∫ x in U,
        vecDot
          (matVecMul (a x)
            ((H1MeanZeroFunction.coeffGradientProblemSolution
              (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll).toH1Function.grad x))
          (u.grad x) ∂MeasureTheory.volume =
      ∫ x in U, vecDot (f x) (u.grad x) ∂MeasureTheory.volume := by
  simpa using
    (H1MeanZeroFunction.coeffGradientProblemSolution_firstVariation_eq_integral
      (d := d) (U := U) (a := a) (lam := lam) (Lam := Lam) hf hC hne hEll
      u.toMeanZero)

end H1Function

namespace IsMeanZeroNeumannRhsWeakSolution

variable {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
variable {u : H1MeanZeroFunction U} {g : Vec d → Vec d}

omit [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] in
theorem energy_identity
    (h : IsMeanZeroNeumannRhsWeakSolution a U u g) :
    ∫ x in U,
        vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
          ∂MeasureTheory.volume =
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  simpa [vecDot_comm] using h u

theorem energy_le_rhs_pairing_of_isEllipticFieldOn
    {lam Lam : ℝ} (h : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume ≤
      ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume := by
  have hsqInt :
      MeasureTheory.IntegrableOn (fun x => vecNormSq (u.toH1Function.grad x)) U :=
    integrableOn_vecNormSq_meanZeroGrad u
  have hlhsInt :
      MeasureTheory.IntegrableOn (fun x => lam * vecNormSq (u.toH1Function.grad x)) U :=
    hsqInt.const_mul lam
  have henergyInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (u.toH1Function.grad x)
          (matVecMul (a x) (u.toH1Function.grad x))) U :=
    integrableOn_dirichletEnergyDensity_of_isEllipticFieldOn_meanZero hEll u
  have hmem :
      ∀ᵐ x ∂ volumeMeasureOn U, x ∈ U := by
    exact
      (MeasureTheory.ae_restrict_iff' (measurableSet_of_isEllipticFieldOn hEll)).2
        (Filter.Eventually.of_forall fun x hx => hx)
  have hpoint :
      ∀ᵐ x ∂ volumeMeasureOn U,
        lam * vecNormSq (u.toH1Function.grad x) ≤
          vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x)) := by
    filter_upwards [hmem] with x hx
    exact (hEll.2 x hx).2.2.1 (u.toH1Function.grad x)
  calc
    lam * ∫ x in U, vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume
        = ∫ x in U, lam * vecNormSq (u.toH1Function.grad x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
    _ ≤
        ∫ x in U,
          vecDot (u.toH1Function.grad x) (matVecMul (a x) (u.toH1Function.grad x))
            ∂MeasureTheory.volume :=
      MeasureTheory.integral_mono_ae hlhsInt henergyInt hpoint
    _ = ∫ x in U, vecDot (g x) (u.toH1Function.grad x) ∂MeasureTheory.volume :=
      energy_identity h

/-- The residual flux of a mean-zero Neumann RHS weak solution is solenoidal
with zero normal trace.  This is the Neumann counterpart of the Dirichlet RHS
residual bridge, using the mean-zero normalization of an arbitrary `H¹` test
function. -/
theorem residual_zeroNormalTrace
    {lam Lam : ℝ} (h : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) (hg : MemVectorL2 U g) :
    IsSolenoidalZeroNormalTraceOn U
      (fun x => matVecMul (a x) (u.toH1Function.grad x) - g x) := by
  intro φ
  have hflux_mem :
      MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2
  have hflux_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hflux_mem φ.grad_memVectorL2
  have hg_int :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (g x) (φ.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hg φ.grad_memVectorL2
  have hfun :
      (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x) - g x) (φ.grad x)) =
        fun x =>
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.grad x) -
            vecDot (g x) (φ.grad x) := by
    funext x
    simp [sub_eq_add_neg, vecDot_add_left, vecDot_neg_left]
  have hweak :
      ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.grad x)
          ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (φ.grad x) ∂MeasureTheory.volume := by
    simpa using h φ.toMeanZero
  rw [hfun, MeasureTheory.integral_sub hflux_int hg_int, hweak]
  ring

theorem sub_zero
    {v : H1MeanZeroFunction U}
    {lam Lam : ℝ}
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    IsMeanZeroNeumannRhsWeakSolution a U (u - v) (0 : Vec d → Vec d) := by
  intro φ
  have huFlux : MemVectorL2 U (fun x => matVecMul (a x) (u.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.toH1Function.grad_memVectorL2
  have hvFlux : MemVectorL2 U (fun x => matVecMul (a x) (v.toH1Function.grad x)) :=
    memVectorL2_matVecMul_of_isEllipticFieldOn hEll v.toH1Function.grad_memVectorL2
  have huInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 huFlux φ.toH1Function.grad_memVectorL2
  have hvInt :
      MeasureTheory.IntegrableOn
        (fun x => vecDot (matVecMul (a x) (v.toH1Function.grad x))
          (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2 hvFlux φ.toH1Function.grad_memVectorL2
  have hfun :
      (fun x =>
        vecDot (matVecMul (a x) ((u - v).toH1Function.grad x)) (φ.toH1Function.grad x)) =
        (fun x =>
          vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) -
            vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)) := by
    funext x
    have hgradSubX :
        ((u - v).toH1Function.grad x) = u.toH1Function.grad x - v.toH1Function.grad x := by
      simp
    rw [hgradSubX]
    simp [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_left, vecDot_neg_left]
  calc
    ∫ x in U,
        vecDot (matVecMul (a x) ((u - v).toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume
        =
          ∫ x in U,
            (vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x) -
              vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x))
            ∂MeasureTheory.volume := by
              rw [hfun]
    _ =
        ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
          ∂MeasureTheory.volume -
          ∫ x in U, vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)
            ∂MeasureTheory.volume := by
              rw [MeasureTheory.integral_sub huInt hvInt]
    _ =
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume -
          ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
              rw [hu φ, hv φ]
    _ = ∫ x in U, vecDot (0 : Vec d) (φ.toH1Function.grad x) ∂MeasureTheory.volume := by
          symm
          simp [vecDot]

theorem gradToVectorL2_eq_of_isEllipticFieldOn
    {v : H1MeanZeroFunction U} {lam Lam : ℝ}
    (hne : Set.Nonempty U)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.gradToVectorL2 = v.gradToVectorL2 := by
  let w : H1MeanZeroFunction U := u - v
  have hw : IsMeanZeroNeumannRhsWeakSolution a U w (0 : Vec d → Vec d) :=
    sub_zero hu hv hEll
  have henergy :
      lam * ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume ≤ 0 := by
    calc
      lam * ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume
          ≤ ∫ y in U, vecDot (0 : Vec d) (w.toH1Function.grad y) ∂MeasureTheory.volume :=
        energy_le_rhs_pairing_of_isEllipticFieldOn
          (u := w) (g := (0 : Vec d → Vec d)) hw hEll
      _ = 0 := by
            simp [vecDot]
  have hsqInt :
      MeasureTheory.IntegrableOn (fun y => vecNormSq (w.toH1Function.grad y)) U :=
    integrableOn_vecNormSq_meanZeroGrad w
  have hsqNonneg :
      0 ≤ ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume :=
    MeasureTheory.integral_nonneg fun _ => vecNormSq_nonneg _
  rcases hne with ⟨x, hx⟩
  have hlam : 0 < lam := (hEll.2 x hx).1
  have hsqLeZero :
      ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume ≤ 0 := by
    nlinarith
  have hsqZero :
      ∫ y in U, vecNormSq (w.toH1Function.grad y) ∂MeasureTheory.volume = 0 :=
    le_antisymm hsqLeZero hsqNonneg
  have hsqAe :
      (fun y => vecNormSq (w.toH1Function.grad y)) =ᵐ[volumeMeasureOn U] 0 := by
    exact
      (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
        (Filter.Eventually.of_forall fun _ => vecNormSq_nonneg _)
        hsqInt.integrable).1 hsqZero
  have hgradAe :
      (fun y => w.toH1Function.grad y) =ᵐ[volumeMeasureOn U] 0 := by
    filter_upwards [hsqAe] with y hy
    exact vecNormSq_eq_zero hy
  have hgradZero : w.gradToVectorL2 = 0 := by
    apply MeasureTheory.Lp.ext
    let hzeroAe :=
      MeasureTheory.Lp.coeFn_zero (E := Vec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)
    filter_upwards
        [H1Function.coeFn_gradToVectorL2 w.toH1Function, hzeroAe, hgradAe]
      with y hwGrad hzero hy
    have hwGrad' : w.gradToVectorL2 y = w.toH1Function.grad y := by
      simpa [H1MeanZeroFunction.gradToVectorL2] using hwGrad
    calc
      w.gradToVectorL2 y = w.toH1Function.grad y := hwGrad'
      _ = 0 := hy
      _ = (0 : VectorL2 U) y := by
            symm
            simpa using hzero
  have hsub :
      u.gradToVectorL2 - v.gradToVectorL2 = 0 := by
    have hneg : (-v).gradToVectorL2 = -v.gradToVectorL2 := by
      simpa using H1MeanZeroFunction.gradToVectorL2_smul (-1 : ℝ) v
    have hgradSub :
        (u - v).gradToVectorL2 = u.gradToVectorL2 - v.gradToVectorL2 := by
      calc
        (u - v).gradToVectorL2 = u.gradToVectorL2 + (-v).gradToVectorL2 := by
          simpa [sub_eq_add_neg] using H1MeanZeroFunction.gradToVectorL2_add u (-v)
        _ = u.gradToVectorL2 - v.gradToVectorL2 := by
          rw [hneg, sub_eq_add_neg]
    calc
      u.gradToVectorL2 - v.gradToVectorL2 = (u - v).gradToVectorL2 := by
        symm
        exact hgradSub
      _ = 0 := hgradZero
  exact sub_eq_zero.mp hsub

theorem toScalarL2_eq_of_h1CoerciveEstimate
    {v : H1MeanZeroFunction U} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hv : IsMeanZeroNeumannRhsWeakSolution a U v g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toScalarL2 = v.toScalarL2 := by
  let w : H1MeanZeroFunction U := u - v
  have hgradEq : u.gradToVectorL2 = v.gradToVectorL2 :=
    gradToVectorL2_eq_of_isEllipticFieldOn hne hu hv hEll
  have hgradZero : w.gradToVectorL2 = 0 := by
    have hneg : (-v).gradToVectorL2 = -v.gradToVectorL2 := by
      simpa using H1MeanZeroFunction.gradToVectorL2_smul (-1 : ℝ) v
    have hgradSub :
        (u - v).gradToVectorL2 = u.gradToVectorL2 - v.gradToVectorL2 := by
      calc
        (u - v).gradToVectorL2 = u.gradToVectorL2 + (-v).gradToVectorL2 := by
          simpa [sub_eq_add_neg] using H1MeanZeroFunction.gradToVectorL2_add u (-v)
        _ = u.gradToVectorL2 - v.gradToVectorL2 := by
          rw [hneg, sub_eq_add_neg]
    calc
      w.gradToVectorL2 = u.gradToVectorL2 - v.gradToVectorL2 := by
        simpa [w] using hgradSub
      _ = 0 := sub_eq_zero.mpr hgradEq
  have hbound := hC.bound w
  have hvalZeroNorm :
      ‖w.toScalarL2‖ = 0 := by
    have hgradNorm : w.gradientL2Norm = 0 := by
      simp [H1MeanZeroFunction.gradientL2Norm, hgradZero]
    have hnonneg : 0 ≤ ‖w.toScalarL2‖ := norm_nonneg _
    have hle : ‖w.toScalarL2‖ ≤ 0 := by
      simpa [H1MeanZeroFunction.valueL2Norm, hgradNorm] using hbound
    exact le_antisymm hle hnonneg
  have hvalZero : w.toScalarL2 = 0 := norm_eq_zero.mp hvalZeroNorm
  have hsub :
      u.toScalarL2 - v.toScalarL2 = 0 := by
    have hneg : (-v).toScalarL2 = -v.toScalarL2 := by
      simpa using H1MeanZeroFunction.toScalarL2_smul (-1 : ℝ) v
    have hvalueSub :
        (u - v).toScalarL2 = u.toScalarL2 - v.toScalarL2 := by
      calc
        (u - v).toScalarL2 = u.toScalarL2 + (-v).toScalarL2 := by
          simpa [sub_eq_add_neg] using H1MeanZeroFunction.toScalarL2_add u (-v)
        _ = u.toScalarL2 - v.toScalarL2 := by
          rw [hneg, sub_eq_add_neg]
    calc
      u.toScalarL2 - v.toScalarL2 = (u - v).toScalarL2 := by
        symm
        exact hvalueSub
      _ = 0 := hvalZero
  exact sub_eq_zero.mp hsub

end IsMeanZeroNeumannRhsWeakSolution

theorem isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    IsMeanZeroNeumannRhsWeakSolution a U
      (H1MeanZeroFunction.coeffGradientProblemSolution
        (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll)
      g := by
  intro φ
  simpa using
    H1MeanZeroFunction.coeffGradientProblemSolution_firstVariation_eq_integral
      (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll φ

theorem gradToVectorL2_eq_coeffGradientProblemSolution_of_h1CoerciveEstimate
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H1MeanZeroFunction U} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.gradToVectorL2 =
      (H1MeanZeroFunction.coeffGradientProblemSolution
        (U := U) (a := a) (lam := lam) (Lam := Lam) hg
        hC hne hEll).gradToVectorL2 := by
  let v : H1MeanZeroFunction U :=
    H1MeanZeroFunction.coeffGradientProblemSolution
      (U := U) (a := a) (lam := lam) (Lam := Lam) (f := g) hg
      hC hne hEll
  have hv : IsMeanZeroNeumannRhsWeakSolution a U v g :=
    isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
      (U := U) (a := a) (lam := lam) (Lam := Lam) hg
      hC hne hEll
  simpa [v] using
    IsMeanZeroNeumannRhsWeakSolution.gradToVectorL2_eq_of_isEllipticFieldOn
      (U := U) (a := a) (u := u) (v := v) (g := g) hne hu hv hEll

theorem toScalarL2_eq_coeffGradientProblemSolution_of_h1CoerciveEstimate
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {u : H1MeanZeroFunction U} {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    u.toScalarL2 =
      (H1MeanZeroFunction.coeffGradientProblemSolution
        (U := U) (a := a) (lam := lam) (Lam := Lam) hg
        hC hne hEll).toScalarL2 := by
  let v : H1MeanZeroFunction U :=
    H1MeanZeroFunction.coeffGradientProblemSolution
      (U := U) (a := a) (lam := lam) (Lam := Lam) (f := g) hg
      hC hne hEll
  have hv : IsMeanZeroNeumannRhsWeakSolution a U v g :=
    isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
      (U := U) (a := a) (lam := lam) (Lam := Lam) hg
      hC hne hEll
  simpa [v] using
    IsMeanZeroNeumannRhsWeakSolution.toScalarL2_eq_of_h1CoerciveEstimate
      (U := U) (a := a) (u := u) (v := v) (g := g) hC hne hu hv hEll

theorem exists_isMeanZeroNeumannRhsWeakSolution_of_h1CoerciveEstimate
    {d : ℕ} {a : CoeffField d} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} {lam Lam : ℝ}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a) :
    ∃ u : H1MeanZeroFunction U, IsMeanZeroNeumannRhsWeakSolution a U u g := by
  refine ⟨H1MeanZeroFunction.coeffGradientProblemSolution
    (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll, ?_⟩
  exact isMeanZeroNeumannRhsWeakSolution_coeffGradientProblemSolution_of_h1CoerciveEstimate
    (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hEll

end Homogenization
