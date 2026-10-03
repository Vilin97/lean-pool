/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.HessianGradientH1

/-! # Harmonic Derivative -/

@[expose] public section

namespace Homogenization

open scoped ENNReal

noncomputable section

/-!
# Harmonicity of weak derivatives

This is an internal closure lemma for the Calderon--Zygmund proof engine.
Starting with a homogeneous scalar weak Poisson equation and the locally
constructed weak-Hessian witness, it supplies the same homogeneous equation
for every gradient coordinate.  No regularity assumption is added to a
Calderon--Zygmund statement: the witness is the one produced by the interior
difference-quotient argument.
-/

namespace CubeCalderonZygmund

private theorem hess_swap_ae {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    (hU : IsOpen U) (H : HasWeakHessianOn U u) (i j : Fin d) :
    H.hess i j =ᵐ[MeasureTheory.volume.restrict U] H.hess j i := by
  have hij_loc : MeasureTheory.LocallyIntegrableOn (H.hess i j) U
      MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((H.hess_memL2 i j).locallyIntegrable (by norm_num))
  have hji_loc : MeasureTheory.LocallyIntegrableOn (H.hess j i) U
      MeasureTheory.volume :=
    MeasureTheory.locallyIntegrableOn_of_locallyIntegrable_restrict
      ((H.hess_memL2 j i).locallyIntegrable (by norm_num))
  rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hU.measurableSet]
  have hzero :
      ∀ᵐ x ∂MeasureTheory.volume, x ∈ U → H.hess i j x - H.hess j i x = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hij_loc.sub hji_loc) ?_
    intro φ hφ hφs hφ_sub
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
    have hφ_memL2 : MemScalarL2 U φ := by
      simpa [MemScalarL2, volumeMeasureOn] using
        (hφ.continuous.memLp_of_hasCompactSupport hφs).restrict U
    have hij_int : MeasureTheory.Integrable (fun x => H.hess i j x * φ x)
        (MeasureTheory.volume.restrict U) := by
      simpa [MemScalarL2, volumeMeasureOn, Pi.mul_apply] using!
        (H.hess_memL2 i j).integrable_mul hφ_memL2
    have hji_int : MeasureTheory.Integrable (fun x => H.hess j i x * φ x)
        (MeasureTheory.volume.restrict U) := by
      simpa [MemScalarL2, volumeMeasureOn, Pi.mul_apply] using!
        (H.hess_memL2 j i).integrable_mul hφ_memL2
    have hij_zero_out : ∀ x, x ∉ U → H.hess i j x * φ x = 0 := by
      intro x hx
      have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
      simp [image_eq_zero_of_notMem_tsupport hx_notin]
    have hji_zero_out : ∀ x, x ∉ U → H.hess j i x * φ x = 0 := by
      intro x hx
      have hx_notin : x ∉ tsupport φ := fun hx' => hx (hφ_sub hx')
      simp [image_eq_zero_of_notMem_tsupport hx_notin]
    have hij_global : MeasureTheory.Integrable (fun x => H.hess i j x * φ x)
        MeasureTheory.volume := by
      exact MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
        hij_int hij_zero_out
    have hji_global : MeasureTheory.Integrable (fun x => H.hess j i x * φ x)
        MeasureTheory.volume := by
      exact MeasureTheory.IntegrableOn.integrable_of_forall_notMem_eq_zero
        hji_int hji_zero_out
    have hweak_ij' :
        ∫ x in U, u.grad x i * euclideanCoordDeriv j φ x ∂MeasureTheory.volume =
          -∫ x in U, H.hess i j x * φ x ∂MeasureTheory.volume := by
      simpa [euclideanCoordDeriv] using hweak_ij
    have hweak_ji' :
        ∫ x in U, u.grad x j * euclideanCoordDeriv i φ x ∂MeasureTheory.volume =
          -∫ x in U, H.hess j i x * φ x ∂MeasureTheory.volume := by
      simpa [euclideanCoordDeriv] using hweak_ji
    have hu_ij' :
        ∫ x in U, u x * euclideanCoordSecondDeriv j i φ x ∂MeasureTheory.volume =
          -∫ x in U, u.grad x i * euclideanCoordDeriv j φ x
            ∂MeasureTheory.volume := by
      simpa [euclideanCoordSecondDeriv, euclideanCoordDeriv] using hu_ij
    have hu_ji' :
        ∫ x in U, u x * euclideanCoordSecondDeriv i j φ x ∂MeasureTheory.volume =
          -∫ x in U, u.grad x j * euclideanCoordDeriv i φ x
            ∂MeasureTheory.volume := by
      simpa [euclideanCoordSecondDeriv, euclideanCoordDeriv] using hu_ji
    simp only [smul_eq_mul]
    rw [show (fun x => φ x * (H.hess i j x - H.hess j i x)) =
        (fun x => H.hess i j x * φ x - H.hess j i x * φ x) by
          funext x; ring]
    rw [MeasureTheory.integral_sub]
    · apply sub_eq_zero.mpr
      calc
        ∫ x, H.hess i j x * φ x ∂MeasureTheory.volume =
            ∫ x in U, H.hess i j x * φ x ∂MeasureTheory.volume :=
          (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hij_zero_out).symm
        _ =
            -∫ x in U, u.grad x i * euclideanCoordDeriv j φ x
              ∂MeasureTheory.volume := by linarith [hweak_ij']
        _ = ∫ x in U, u x * euclideanCoordSecondDeriv j i φ x
              ∂MeasureTheory.volume := by linarith [hu_ij']
        _ = ∫ x in U, u x * euclideanCoordSecondDeriv i j φ x
              ∂MeasureTheory.volume := by
              apply MeasureTheory.setIntegral_congr_fun hU.measurableSet
              intro x hx
              change u x * euclideanCoordSecondDeriv j i φ x =
                u x * euclideanCoordSecondDeriv i j φ x
              rw [euclideanCoordSecondDeriv_comm hφ j i x]
        _ = -∫ x in U, u.grad x j * euclideanCoordDeriv i φ x
              ∂MeasureTheory.volume := by linarith [hu_ji']
        _ = ∫ x in U, H.hess j i x * φ x ∂MeasureTheory.volume := by
              linarith [hweak_ji']
        _ = ∫ x, H.hess j i x * φ x ∂MeasureTheory.volume :=
          MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hji_zero_out
    · exact hij_global
    · exact hji_global
  filter_upwards [hzero] with x hx
  intro hxU
  exact sub_eq_zero.mp (hx hxU)

end CubeCalderonZygmund

namespace WeakPoissonEquationOn

/-- A zero-forcing weak Poisson equation is inherited by each gradient
coordinate once the local weak Hessian has been constructed. -/
theorem gradCoordH1Function_harmonic {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} (hU : IsOpen U)
    (h : WeakPoissonEquationOn U u (fun _ => 0))
    (H : HasWeakHessianOn U u) (i : Fin d) :
    WeakPoissonEquationOn U (H.gradCoordH1Function i) (fun _ => 0) := by
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
  have hzero_sum :
      ∑ k : Fin d,
        ∫ x in U, u.grad x k * euclideanCoordSecondDeriv i k φ x
          ∂MeasureTheory.volume = 0 := by
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
      _ = 0 := by
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
            ∂MeasureTheory.volume := by linarith [hweak']
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
    apply MeasureTheory.integral_congr_ae
    filter_upwards [CubeCalderonZygmund.hess_swap_ae hU H i k] with x hx
    rw [hx]
  simp only [zero_mul, MeasureTheory.integral_zero]
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
    _ = 0 := by rw [hzero_sum, neg_zero]

/-- Strict-inner-domain form of `gradCoordH1Function_harmonic`.  The scalar
weak equation is restricted, while the local Hessian witness is consumed only
on the inner domain. -/
theorem gradCoordH1Function_harmonic_restrict {d : ℕ} {U : Set (Vec d)}
    {u : H1Function U} (h : WeakPoissonEquationOn U u (fun _ => 0))
    {V : Set (Vec d)} (hVopen : IsOpen V) (hVU : V ⊆ U)
    (H : HasWeakHessianOn V (u.restrict hVopen hVU)) (i : Fin d) :
    WeakPoissonEquationOn V (H.gradCoordH1Function i) (fun _ => 0) := by
  exact (h.restrict hVopen hVU).gradCoordH1Function_harmonic hVopen H i

end WeakPoissonEquationOn

end

end Homogenization
