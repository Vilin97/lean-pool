/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

/-! # Weak Poisson Derivative -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Weak equation for a derivative of a Poisson solution

Differentiating `-Delta u = F` in one coordinate does not require a derivative
of `F`: the forcing is retained in divergence form as the vector field with
`F` in that coordinate and zero in the others.  This file establishes that
identity from the scalar weak equation and an internally constructed weak
Hessian witness.
-/

namespace CubeCalderonZygmund

/-- Inserting a scalar `L²` field into one coordinate gives a vector `L²`
field. -/
theorem memVectorL2_singleCoordinate {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → ℝ} (hF : MemScalarL2 U F) (i : Fin d) :
    MemVectorL2 U (fun x j => if j = i then F x else 0) := by
  classical
  apply MeasureTheory.MemLp.of_eval
  intro j
  by_cases hji : j = i
  · subst j
    simpa using hF
  · rw [show (fun x : Vec d => if j = i then F x else 0) =
        fun _ : Vec d => (0 : ℝ) by
          funext x
          simp [hji]]
    exact MeasureTheory.MemLp.zero'

/-- Weak Hessian coordinates commute when paired with a smooth compactly
supported test.  This is the distributional mixed-derivative argument needed
below; no pointwise Hessian representative is selected. -/
private theorem setIntegral_hess_comm {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} (hU : IsOpen U) (H : HasWeakHessianOn U u)
    (i j : Fin d) (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφs : HasCompactSupport φ) (hφ_sub : tsupport φ ⊆ U) :
    ∫ x in U, H.hess i j x * φ x ∂MeasureTheory.volume =
      ∫ x in U, H.hess j i x * φ x ∂MeasureTheory.volume := by
  have hweak_ij := H.weak_second i j φ hφ hφs hφ_sub
  have hweak_ji := H.weak_second j i φ hφ hφs hφ_sub
  have hu_ij := u.hasWeakPartialDerivOn i (euclideanCoordDeriv j φ)
    (contDiff_euclideanCoordDeriv hφ j)
    (hasCompactSupport_euclideanCoordDeriv hφs j)
    ((tsupport_euclideanCoordDeriv_subset_tsupport j φ).trans hφ_sub)
  have hu_ji := u.hasWeakPartialDerivOn j (euclideanCoordDeriv i φ)
    (contDiff_euclideanCoordDeriv hφ i)
    (hasCompactSupport_euclideanCoordDeriv hφs i)
    ((tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hφ_sub)
  have hweak_ij' :
      ∫ x in U, u.grad x i * euclideanCoordDeriv j φ x
          ∂MeasureTheory.volume =
        -∫ x in U, H.hess i j x * φ x ∂MeasureTheory.volume := by
    simpa [euclideanCoordDeriv] using hweak_ij
  have hweak_ji' :
      ∫ x in U, u.grad x j * euclideanCoordDeriv i φ x
          ∂MeasureTheory.volume =
        -∫ x in U, H.hess j i x * φ x ∂MeasureTheory.volume := by
    simpa [euclideanCoordDeriv] using hweak_ji
  have hu_ij' :
      ∫ x in U, u x * euclideanCoordSecondDeriv j i φ x
          ∂MeasureTheory.volume =
        -∫ x in U, u.grad x i * euclideanCoordDeriv j φ x
          ∂MeasureTheory.volume := by
    simpa [euclideanCoordSecondDeriv, euclideanCoordDeriv] using hu_ij
  have hu_ji' :
      ∫ x in U, u x * euclideanCoordSecondDeriv i j φ x
          ∂MeasureTheory.volume =
        -∫ x in U, u.grad x j * euclideanCoordDeriv i φ x
          ∂MeasureTheory.volume := by
    simpa [euclideanCoordSecondDeriv, euclideanCoordDeriv] using hu_ji
  calc
    ∫ x in U, H.hess i j x * φ x ∂MeasureTheory.volume =
        -∫ x in U, u.grad x i * euclideanCoordDeriv j φ x
          ∂MeasureTheory.volume := by
          linarith [hweak_ij']
    _ = ∫ x in U, u x * euclideanCoordSecondDeriv j i φ x
          ∂MeasureTheory.volume := by
          linarith [hu_ij']
    _ = ∫ x in U, u x * euclideanCoordSecondDeriv i j φ x
          ∂MeasureTheory.volume := by
          apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
          intro x hx
          change u x * euclideanCoordSecondDeriv j i φ x =
            u x * euclideanCoordSecondDeriv i j φ x
          rw [euclideanCoordSecondDeriv_comm hφ j i x]
    _ = -∫ x in U, u.grad x j * euclideanCoordDeriv i φ x
          ∂MeasureTheory.volume := by
          linarith [hu_ji']
    _ = ∫ x in U, H.hess j i x * φ x ∂MeasureTheory.volume := by
          linarith [hweak_ji']

end CubeCalderonZygmund

namespace WeakPoissonEquationOn

/-- A scalar weak Poisson equation yields the divergence-form weak equation
for every gradient coordinate.  The datum is `F` in the differentiated
coordinate and zero in all other coordinates; in particular, the conclusion
assumes neither a weak derivative of `F` nor a trace for `∂ᵢu`.

The `MemScalarL2` hypothesis records that this coordinate datum is admissible
as an `L²` vector field, via
`CubeCalderonZygmund.memVectorL2_singleCoordinate`. -/
theorem gradCoordH1Function_weakDivergence {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} {F : Vec d → ℝ} (hU : IsOpen U)
    (hF : MemScalarL2 U F) (h : WeakPoissonEquationOn U u F)
    (H : HasWeakHessianOn U u) (i : Fin d) :
    ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
        ∫ x in U,
            vecDot ((H.gradCoordH1Function i).grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume =
          -∫ x in U,
            vecDot (fun j => if j = i then F x else 0) (euclideanGradient φ x)
              ∂MeasureTheory.volume := by
  classical
  have _hdatum_memL2 :=
    CubeCalderonZygmund.memVectorL2_singleCoordinate hF i
  intro φ hφ hφs hφ_sub
  have hderiv_memL2 : ∀ k : Fin d, MemScalarL2 U (euclideanCoordDeriv k φ) := by
    intro k
    simpa [MemScalarL2, volumeMeasureOn] using
      ((contDiff_euclideanCoordDeriv hφ k).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordDeriv hφs k)).restrict U
  have hsecond_memL2 : ∀ k : Fin d,
      MemScalarL2 U (euclideanCoordSecondDeriv i k φ) := by
    intro k
    simpa [MemScalarL2, volumeMeasureOn] using
      ((contDiff_euclideanCoordSecondDeriv hφ i k).continuous.memLp_of_hasCompactSupport
        (hasCompactSupport_euclideanCoordSecondDeriv hφs i k)).restrict U
  have hhess_int : ∀ k : Fin d,
      MeasureTheory.Integrable (fun x => H.hess i k x * euclideanCoordDeriv k φ x)
        (MeasureTheory.volume.restrict U) := by
    intro k
    simpa [MemScalarL2, volumeMeasureOn, Pi.mul_apply] using!
      (H.hess_memL2 i k).integrable_mul (hderiv_memL2 k)
  have hgrad_int : ∀ k : Fin d,
      MeasureTheory.Integrable
        (fun x => u.grad x k * euclideanCoordSecondDeriv i k φ x)
        (MeasureTheory.volume.restrict U) := by
    intro k
    simpa [MemScalarL2, volumeMeasureOn, Pi.mul_apply] using!
      (u.grad_memL2 k).integrable_mul (hsecond_memL2 k)
  have htest := h.test (euclideanCoordDeriv i φ)
    (contDiff_euclideanCoordDeriv hφ i)
    (hasCompactSupport_euclideanCoordDeriv hφs i)
    ((tsupport_euclideanCoordDeriv_subset_tsupport i φ).trans hφ_sub)
  have hforcing_sum :
      ∑ k : Fin d,
        ∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
          ∂MeasureTheory.volume =
        ∫ x in U, F x * euclideanCoordDeriv i φ x ∂MeasureTheory.volume := by
    calc
      ∑ k : Fin d,
          ∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
            ∂MeasureTheory.volume =
          ∫ x in U,
            vecDot (u.grad x) (euclideanGradient (euclideanCoordDeriv i φ) x)
              ∂MeasureTheory.volume := by
            symm
            calc
              ∫ x in U,
                  vecDot (u.grad x) (euclideanGradient (euclideanCoordDeriv i φ) x)
                    ∂MeasureTheory.volume =
                  ∫ x in U, ∑ k : Fin d,
                    u.grad x k * euclideanCoordSecondDeriv i k φ x
                      ∂MeasureTheory.volume := by
                    apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
                    intro x hx
                    simp only [vecDot, euclideanGradient, euclideanCoordSecondDeriv,
                      euclideanCoordDeriv]
              _ = ∑ k : Fin d,
                  ∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
                    ∂MeasureTheory.volume := by
                    rw [MeasureTheory.integral_finsetSum]
                    intro k _
                    exact hgrad_int k
      _ = ∫ x in U, F x * euclideanCoordDeriv i φ x
            ∂MeasureTheory.volume := by
            simpa [euclideanCoordDeriv] using htest
  have htranspose : ∀ k : Fin d,
      ∫ x in U, H.hess k i x * euclideanCoordDeriv k φ x
        ∂MeasureTheory.volume =
        -∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
          ∂MeasureTheory.volume := by
    intro k
    have hweak := H.weak_second k i (euclideanCoordDeriv k φ)
      (contDiff_euclideanCoordDeriv hφ k)
      (hasCompactSupport_euclideanCoordDeriv hφs k)
      ((tsupport_euclideanCoordDeriv_subset_tsupport k φ).trans hφ_sub)
    have hweak' :
        ∫ x in U, u.grad x k * euclideanCoordSecondDeriv k i φ x
          ∂MeasureTheory.volume =
          -∫ x in U, H.hess k i x * euclideanCoordDeriv k φ x
            ∂MeasureTheory.volume := by
      simpa [euclideanCoordSecondDeriv, euclideanCoordDeriv] using hweak
    calc
      ∫ x in U, H.hess k i x * euclideanCoordDeriv k φ x
          ∂MeasureTheory.volume =
          -∫ x in U, u.grad x k * euclideanCoordSecondDeriv k i φ x
            ∂MeasureTheory.volume := by
            linarith [hweak']
      _ = -∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
            ∂MeasureTheory.volume := by
            apply congrArg Neg.neg
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            change u.grad x k * euclideanCoordSecondDeriv k i φ x =
              u.grad x k * euclideanCoordSecondDeriv i k φ x
            rw [euclideanCoordSecondDeriv_comm hφ k i x]
  have hswap : ∀ k : Fin d,
      ∫ x in U, H.hess i k x * euclideanCoordDeriv k φ x
        ∂MeasureTheory.volume =
        ∫ x in U, H.hess k i x * euclideanCoordDeriv k φ x
          ∂MeasureTheory.volume := by
    intro k
    exact CubeCalderonZygmund.setIntegral_hess_comm hU H i k
      (euclideanCoordDeriv k φ) (contDiff_euclideanCoordDeriv hφ k)
      (hasCompactSupport_euclideanCoordDeriv hφs k)
      ((tsupport_euclideanCoordDeriv_subset_tsupport k φ).trans hφ_sub)
  calc
    ∫ x in U,
        vecDot ((H.gradCoordH1Function i).grad x) (euclideanGradient φ x)
          ∂MeasureTheory.volume =
        ∑ k : Fin d,
          ∫ x in U, H.hess i k x * euclideanCoordDeriv k φ x
            ∂MeasureTheory.volume := by
          calc
            ∫ x in U,
                vecDot ((H.gradCoordH1Function i).grad x) (euclideanGradient φ x)
                  ∂MeasureTheory.volume =
                ∫ x in U, ∑ k : Fin d,
                  H.hess i k x * euclideanCoordDeriv k φ x
                    ∂MeasureTheory.volume := by
                  apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
                  intro x hx
                  simp only [vecDot, HasWeakHessianOn.gradCoordH1Function_grad_apply,
                    euclideanGradient, euclideanCoordDeriv]
            _ = ∑ k : Fin d,
                ∫ x in U, H.hess i k x * euclideanCoordDeriv k φ x
                  ∂MeasureTheory.volume := by
                rw [MeasureTheory.integral_finsetSum]
                intro k _
                exact hhess_int k
    _ = ∑ k : Fin d,
          ∫ x in U, H.hess k i x * euclideanCoordDeriv k φ x
            ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro k _
          exact hswap k
    _ = ∑ k : Fin d,
          -∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
            ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro k _
          exact htranspose k
    _ = -∑ k : Fin d,
          ∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
            ∂MeasureTheory.volume := by
          rw [Finset.sum_neg_distrib]
    _ = -∫ x in U, F x * euclideanCoordDeriv i φ x
          ∂MeasureTheory.volume := by
          rw [hforcing_sum]
    _ = -∫ x in U,
          vecDot (fun j => if j = i then F x else 0) (euclideanGradient φ x)
            ∂MeasureTheory.volume := by
          congr 1
          apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
          intro x hx
          simp [vecDot, euclideanGradient, euclideanCoordDeriv]

/-- Constant-coefficient form of
`WeakPoissonEquationOn.gradCoordH1Function_weakDivergence`.  If
`-sigma0 * Delta u = F`, then `∂ᵢu` has divergence datum `F eᵢ` with the
coefficient and sign left unchanged. -/
theorem gradCoordH1Function_weakDivergence_constCoeff
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U} {F : Vec d → ℝ}
    {sigma0 : ℝ} (hU : IsOpen U) (hsigma0 : sigma0 ≠ 0)
    (hF : MemScalarL2 U F)
    (h : ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
        sigma0 *
            ∫ x in U, vecDot (u.grad x) (euclideanGradient φ x)
              ∂MeasureTheory.volume =
          ∫ x in U, F x * φ x ∂MeasureTheory.volume)
    (H : HasWeakHessianOn U u) (i : Fin d) :
    ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
        sigma0 *
            ∫ x in U,
              vecDot ((H.gradCoordH1Function i).grad x) (euclideanGradient φ x)
                ∂MeasureTheory.volume =
          -∫ x in U,
            vecDot (fun j => if j = i then F x else 0) (euclideanGradient φ x)
              ∂MeasureTheory.volume := by
  classical
  let Fs : Vec d → ℝ := fun x => sigma0⁻¹ * F x
  have hFs : MemScalarL2 U Fs := by
    simpa only [Fs] using hF.const_mul sigma0⁻¹
  have hscaled : WeakPoissonEquationOn U u Fs := by
    intro ψ hψ hψs hψ_sub
    have htest := h ψ hψ hψs hψ_sub
    calc
      ∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x)
          ∂MeasureTheory.volume =
          sigma0⁻¹ *
            (sigma0 *
              ∫ x in U, vecDot (u.grad x) (euclideanGradient ψ x)
                ∂MeasureTheory.volume) := by
            field_simp
      _ = sigma0⁻¹ * ∫ x in U, F x * ψ x ∂MeasureTheory.volume := by
            rw [htest]
      _ = ∫ x in U, sigma0⁻¹ * (F x * ψ x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ x in U, Fs x * ψ x ∂MeasureTheory.volume := by
            apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
            intro x hx
            simp only [Fs]
            ring
  intro φ hφ hφs hφ_sub
  have hderivative := hscaled.gradCoordH1Function_weakDivergence
    hU hFs H i φ hφ hφs hφ_sub
  have hscale_integral :
      sigma0 *
          ∫ x in U,
            vecDot (fun j => if j = i then Fs x else 0) (euclideanGradient φ x)
              ∂MeasureTheory.volume =
        ∫ x in U,
          vecDot (fun j => if j = i then F x else 0) (euclideanGradient φ x)
            ∂MeasureTheory.volume := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
    intro x hx
    simp [Fs, vecDot, euclideanGradient]
    field_simp
  calc
    sigma0 *
        ∫ x in U,
          vecDot ((H.gradCoordH1Function i).grad x) (euclideanGradient φ x)
            ∂MeasureTheory.volume =
        sigma0 *
          (-∫ x in U,
            vecDot (fun j => if j = i then Fs x else 0) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
          rw [hderivative]
    _ = -(sigma0 *
          ∫ x in U,
            vecDot (fun j => if j = i then Fs x else 0) (euclideanGradient φ x)
              ∂MeasureTheory.volume) := by
          ring
    _ = -∫ x in U,
          vecDot (fun j => if j = i then F x else 0) (euclideanGradient φ x)
            ∂MeasureTheory.volume := by
          rw [hscale_integral]

end WeakPoissonEquationOn

end

end Homogenization
