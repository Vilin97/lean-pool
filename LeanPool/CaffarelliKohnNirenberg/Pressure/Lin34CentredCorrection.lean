/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.Equation
public import LeanPool.CaffarelliKohnNirenberg.Setting.DivergenceFreeSlice

/-!
# Lin34 Centred Correction

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-!
# Centring the nonlinearity against the Hessian of a test function

The paper's nonlinearity is introduced in singly centred form
`U_ij = -u_i (u_j - c_j)` and then rewritten in the doubly centred form
`Û_ij = -(u_i - c_i)(u_j - c_j)` of `eq:Uhat`.  The difference between the two
tensors is `U_ij - Û_ij = -c_i (u_j - c_j)`, and the point of the present file is
that this difference pairs to zero against the Hessian of every smooth compactly
supported test function.  This is purely a calculus fact: the Hessian of a test
function is a divergence, so its pairing with a constant vector field vanishes,
and its pairing with the weakly divergence-free field `u` vanishes by hypothesis.

The file records the two elementary integration-by-parts facts (the integral of a
spatial derivative, and of a mixed second derivative, of a compactly supported
smooth function) and then assembles the cancellation for the centred pairing.
-/

/-- The integral over all of `Vec3` of a spatial partial derivative of a smooth
compactly supported function vanishes.  This is integration by parts against the
constant test function `1`, whose derivative is zero. -/
theorem lin34_integral_spatialDeriv_eq_zero {G : Vec3 → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) (i : Fin 3) :
    ∫ x, spatialDeriv G i x = 0 := by
  have hf'g : Integrable (fun x : Vec3 =>
      (fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x) (basisVec i) * G x) volume := by
    have hz : Integrable (fun _ : Vec3 => (0 : ℝ)) volume := by fun_prop
    simpa only [fderiv_const_apply, zero_apply, zero_mul] using hz
  have hfg' : Integrable (fun x : Vec3 =>
      (1 : ℝ) * (fderiv ℝ G x) (basisVec i)) volume := by
    have h : Integrable (fun x : Vec3 => (fderiv ℝ G x) (basisVec i)) volume :=
      (contDiff_spatialDeriv_smooth hG i).continuous.integrable_of_hasCompactSupport
        (hGc.fderiv_apply (𝕜 := ℝ) (basisVec i))
    simpa only [one_mul] using h
  have hfg : Integrable (fun x : Vec3 => (1 : ℝ) * G x) volume := by
    simpa only [one_mul] using hG.continuous.integrable_of_hasCompactSupport hGc
  have hIBP := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : Vec3 => (1 : ℝ)) (g := G) (v := basisVec i) hf'g hfg' hfg
    (fun x _ => differentiableAt_const (c := (1 : ℝ)))
    (fun x _ => hG.differentiable (by simp) x)
  have hz : ∫ x : Vec3,
      (fderiv ℝ (fun _ : Vec3 => (1 : ℝ)) x) (basisVec i) * G x = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [] with x
    rw [fderiv_const_apply]
    simp
  rw [hz] at hIBP
  simpa only [one_mul, spatialDeriv, neg_zero] using hIBP

/-- The integral over all of `Vec3` of a mixed second derivative of a smooth
compactly supported function vanishes: it is the spatial derivative of the smooth
compactly supported function `∂_j G`, so the previous integration-by-parts fact
applies. -/
theorem lin34_integral_mixedSecond_eq_zero {G : Vec3 → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGc : HasCompactSupport G) (i j : Fin 3) :
    ∫ x, mixedSecond G i j x = 0 := by
  have hc : HasCompactSupport (spatialDeriv G j) :=
    hGc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  simpa only [mixedSecond] using
    lin34_integral_spatialDeriv_eq_zero (G := spatialDeriv G j)
      (contDiff_spatialDeriv_smooth hG j) hc i

/-- The correction `U_ij - Û_ij = -c_i (u_j - c_j)` relating the singly and doubly
centred nonlinearities of `eq:Uhat` of `paper/ckn.tex` pairs to zero against the
Hessian of every smooth compactly supported test function `F` supported in `Ω`.
Indeed the constant vector field `b` is divergence free, so the `b_i b_j` part of
the pairing vanishes termwise, while the `b_i u_j` part is the divergence-free
pairing `∫_Ω ∑_j u_j ∂_j ∂_i F` supplied by `hdiv`; the two groups are related by
the symmetry `∂_i ∂_j F = ∂_j ∂_i F` of the Hessian. -/
theorem lin34_constant_hessian_pairing_zero
    {u : ParabolicPoint → Vec3} {Ω : Set Vec3} {s : ℝ} {b : Vec3}
    {F : Vec3 → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFΩ : tsupport F ⊆ Ω)
    (hint : ∀ j : Fin 3,
      IntegrableOn (fun x : Vec3 => u (x, s) j) (tsupport F) volume)
    (hdiv : ∀ i : Fin 3,
      ∫ x in Ω, ∑ j, u (x, s) j * mixedSecond F j i x = 0) :
    (∑ i, ∑ j, ∫ x, b i * (u (x, s) j - b j) * mixedSecond F i j x) = 0 := by
  have hmixedCont (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond F i j) :=
    contDiff_mixedSecond_smooth hF i j
  have hmixedC (i j : Fin 3) : HasCompactSupport (mixedSecond F i j) :=
    (hFc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hmixedInt (i j : Fin 3) : Integrable (mixedSecond F i j) volume :=
    (hmixedCont i j).continuous.integrable_of_hasCompactSupport (hmixedC i j)
  have hmixedSupp (i j : Fin 3) : tsupport (mixedSecond F i j) ⊆ tsupport F := by
    have h1 : tsupport (mixedSecond F i j) ⊆ tsupport (spatialDeriv F j) :=
      tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := spatialDeriv F j) (basisVec i)
    have h2 : tsupport (spatialDeriv F j) ⊆ tsupport F :=
      tsupport_fderiv_apply_subset (𝕜 := ℝ) (f := F) (basisVec j)
    exact h1.trans h2
  have huScalar (j i : Fin 3) :
      Integrable (fun x : Vec3 => u (x, s) j * mixedSecond F j i x) volume := by
    obtain ⟨C, hC⟩ :=
      (hmixedC j i).exists_bound_of_continuous (hmixedCont j i).continuous
    have hgm : AEStronglyMeasurable (mixedSecond F j i)
        (volume.restrict (tsupport F)) :=
      (hmixedCont j i).continuous.measurable.aestronglyMeasurable
    have h' : IntegrableOn (fun x : Vec3 => u (x, s) j * mixedSecond F j i x)
        (tsupport F) volume :=
      (hint j).mul_bdd hgm (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
    exact h'.integrable_of_forall_notMem_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun hm => hx (hmixedSupp j i hm)),
        mul_zero])
  have hrow (i : Fin 3) :
      ∑ j, ∫ x, b i * (u (x, s) j - b j) * mixedSecond F i j x = 0 := by
    have hstep (j : Fin 3) :
        (∫ x, b i * (u (x, s) j - b j) * mixedSecond F i j x)
          = b i * (∫ x, u (x, s) j * mixedSecond F j i x)
            - (b i * b j) * (∫ x, mixedSecond F j i x) := by
      calc
        (∫ x, b i * (u (x, s) j - b j) * mixedSecond F i j x)
            = ∫ x, (b i * (u (x, s) j * mixedSecond F j i x)
                - b i * b j * mixedSecond F j i x) := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [mixedSecond_swap hF i j x]
              ring
        _ = (∫ x, b i * (u (x, s) j * mixedSecond F j i x))
              - ∫ x, b i * b j * mixedSecond F j i x := by
              rw [integral_sub ((huScalar j i).const_mul (b i))
                ((hmixedInt j i).const_mul (b i * b j))]
        _ = b i * (∫ x, u (x, s) j * mixedSecond F j i x)
              - (b i * b j) * (∫ x, mixedSecond F j i x) := by
              rw [integral_const_mul, integral_const_mul]
    have hset : (∫ x, ∑ j, u (x, s) j * mixedSecond F j i x)
        = ∫ x in Ω, ∑ j, u (x, s) j * mixedSecond F j i x :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Ω) (f := fun x => ∑ j, u (x, s) j * mixedSecond F j i x)
        (fun x hx => by
          apply Finset.sum_eq_zero
          intro j _
          rw [image_eq_zero_of_notMem_tsupport
              (fun hm => hx (hFΩ (hmixedSupp j i hm))), mul_zero])).symm
    calc
      (∑ j, ∫ x, b i * (u (x, s) j - b j) * mixedSecond F i j x)
          = ∑ j, (b i * (∫ x, u (x, s) j * mixedSecond F j i x)
              - (b i * b j) * (∫ x, mixedSecond F j i x)) :=
            Finset.sum_congr rfl (fun j _ => hstep j)
      _ = ∑ j, b i * (∫ x, u (x, s) j * mixedSecond F j i x) := by
            apply Finset.sum_congr rfl
            intro j _
            rw [lin34_integral_mixedSecond_eq_zero hF hFc j i, mul_zero, sub_zero]
      _ = b i * (∑ j, ∫ x, u (x, s) j * mixedSecond F j i x) := by
            rw [Finset.mul_sum]
      _ = b i * (∫ x, ∑ j, u (x, s) j * mixedSecond F j i x) := by
            rw [integral_finsetSum (Finset.univ) (fun j _ => huScalar j i)]
      _ = b i * (∫ x in Ω, ∑ j, u (x, s) j * mixedSecond F j i x) := by
            rw [hset]
      _ = 0 := by rw [hdiv i, mul_zero]
  exact Finset.sum_eq_zero (fun i _ => hrow i)

end CKN
