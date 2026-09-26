/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionPotentials
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWSBasic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.InteriorWeak
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville

/-!
# Force Cancellation

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- The test functions used for a distributional spatial divergence. -/
@[expose] def SmoothCompactTest (ψ : Vec3 → ℝ) : Prop :=
  (∀ n : ℕ, ContDiff ℝ (n : ℕ∞) ψ) ∧ HasCompactSupport ψ

/-- Distributional divergence-free data, with the spatial test class explicit. -/
@[expose] def DistributionalDivergenceFree (F : Vec3 → Vec3) : Prop :=
  ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
    ∫ x, ∑ i : Fin 3, F x i * spatialDeriv ψ i x = 0

private lemma smoothCompactTest_contDiff
    {ψ : Vec3 → ℝ} (hψ : SmoothCompactTest ψ) :
    ContDiff ℝ (⊤ : ℕ∞) ψ := by
  exact (contDiff_infty).2 hψ.1

private lemma smoothCompactTest_deriv_integrable
    {g ψ : Vec3 → ℝ} (hg : Integrable g volume)
    (_ : HasCompactSupport g) (hψ : SmoothCompactTest ψ) (i : Fin 3) :
    Integrable (fun x => g x * spatialDeriv ψ i x) volume := by
  have hψtop := smoothCompactTest_contDiff hψ
  have hψd := contDiff_spatialDeriv_smooth hψtop i
  have hψdc : HasCompactSupport (spatialDeriv ψ i) :=
    hψ.2.fderiv_apply (𝕜 := ℝ) (basisVec i)
  obtain ⟨C, hC⟩ := hψdc.exists_bound_of_continuous hψd.continuous
  exact hg.mul_bdd hψd.continuous.measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hC x)

private lemma smoothCompactTest_mul
    {η ψ : Vec3 → ℝ} (hη : SmoothCompactTest η) (hψ : SmoothCompactTest ψ) :
    SmoothCompactTest (fun x => η x * ψ x) := by
  have hηtop := smoothCompactTest_contDiff hη
  have hψtop := smoothCompactTest_contDiff hψ
  refine ⟨fun n => ?_, hη.2.mul_right (f' := ψ)⟩
  exact (hηtop.mul hψtop).of_le (by simp)

/-- The force potentials have zero Laplacian pairing under distributional
divergence cancellation. -/
theorem pressure_force_pairing_zero_of_distributionalDivergenceFree
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : DistributionalDivergenceFree (fun x : Vec3 => f (x, s)))
    (hInt7 : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport
      (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j)) :
    ∀ ψ : Vec3 → ℝ, SmoothCompactTest ψ →
      ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x = 0 := by
  intro ψ hψ
  have hηtop := smoothCompactTest_contDiff hη
  have hψtop := smoothCompactTest_contDiff hψ
  have hηψ := smoothCompactTest_mul hη hψ
  have hdivηψ := hdiv (fun x => η x * ψ x) hηψ
  have hterm7 (j : Fin 3) : Integrable
      (fun x => η x * f (x, s) j * spatialDeriv ψ j x) volume := by
    exact smoothCompactTest_deriv_integrable (hInt7 j) (hSupp7 j) hψ j
  have hterm8 (j : Fin 3) : Integrable
      (fun x => spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    have hψc : HasCompactSupport ψ := hψ.2
    have hψbound := hψc.exists_bound_of_continuous hψtop.continuous
    obtain ⟨C, hC⟩ := hψbound
    exact (hInt8 j).mul_bdd hψtop.continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hC x)
  have hsum7 : Integrable
      (fun x => ∑ j : Fin 3, η x * f (x, s) j * spatialDeriv ψ j x) volume := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm7 j)
  have hsum8 : Integrable
      (fun x => ∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) volume := by
    exact integrable_finsetSum (s := (Finset.univ : Finset (Fin 3)))
      (fun j _hj => hterm8 j)
  have hdiv' : ∫ x, (∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
        (∑ j : Fin 3, spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, ∑ i : Fin 3, f (x, s) i *
          spatialDeriv (fun y => η y * ψ y) i x := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [show (∑ i : Fin 3, f (x, s) i *
            spatialDeriv (fun y => η y * ψ y) i x) =
          ∑ i : Fin 3, (η x * f (x, s) i * spatialDeriv ψ i x +
            spatialDeriv η i x * f (x, s) i * ψ x) by
          apply Finset.sum_congr rfl
          intro i hi
          rw [spatialDeriv_mul
            (hηtop.differentiable (by simp) x)
            (hψtop.differentiable (by simp) x) i]
          ring]
        rw [← Finset.sum_add_distrib]
      _ = 0 := hdivηψ
  have hdiv'' : (∫ x, ∑ j : Fin 3,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∫ x, ∑ j : Fin 3,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    calc
      _ = ∫ x, (∑ j : Fin 3,
          η x * f (x, s) j * spatialDeriv ψ j x) +
          (∑ j : Fin 3,
            spatialDeriv η j x * f (x, s) j * ψ x) :=
        (integral_add hsum7 hsum8).symm
      _ = 0 := hdiv'
  have hdivsum : (∑ j : Fin 3, ∫ x,
      η x * f (x, s) j * spatialDeriv ψ j x) +
      (∑ j : Fin 3, ∫ x,
        spatialDeriv η j x * f (x, s) j * ψ x) = 0 := by
    rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
    · rw [integral_finsetSum (s := (Finset.univ : Finset (Fin 3)))] at hdiv''
      · exact hdiv''
      · intro j hj
        exact hterm8 j
    · intro j hj
      exact hterm7 j
  have hP7 := pressureP7_distributional_pairing hInt7 hSupp7 hψtop hψ.2
  have hP8 := pressureP8_distributional_pairing hInt8 hSupp8 hψtop hψ.2
  calc
    ∫ x, (pressureP7 η f s x + pressureP8 η f s x) *
        spatialLaplacian ψ x =
      (∫ x, pressureP7 η f s x * spatialLaplacian ψ x) +
        ∫ x, pressureP8 η f s x * spatialLaplacian ψ x := by
      rw [show (fun x => (pressureP7 η f s x + pressureP8 η f s x) *
          spatialLaplacian ψ x) =
        (fun x => pressureP7 η f s x * spatialLaplacian ψ x +
          pressureP8 η f s x * spatialLaplacian ψ x) by
          funext x
          ring]
      have hP7Int : Integrable (fun x => pressureP7 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP7_locallyIntegrable hInt7 hSupp7
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      have hP8Int : Integrable (fun x => pressureP8 η f s x *
          spatialLaplacian ψ x) volume := by
        have hlocal := pressureP8_locallyIntegrable hInt8 hSupp8
        simpa only [smul_eq_mul, mul_comm] using
          hlocal.integrable_smul_right_of_hasCompactSupport
            (contDiff_spatialLaplacian_smooth hψtop).continuous
            (decomposition_laplacian_hasCompactSupport_sws hψ.2)
      exact integral_add hP7Int hP8Int
    _ = 0 := by
      rw [hP7, hP8]
      have hsign : (∑ j : Fin 3, ∫ y,
          η y * f (y, s) j * spatialDeriv ψ j y) =
          ∑ j : Fin 3, ∫ y,
            η y * f (y, s) j * spatialDeriv ψ j y := rfl
      rw [hsign]
      linarith only [hdivsum]

/-- A global harmonic force potential vanishes once its local integrability and
linear growth are supplied. -/
theorem pressure_force_eq_zero_of_distributionalDivergenceFree
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {s : ℝ}
    (hη : SmoothCompactTest η)
    (hdiv : DistributionalDivergenceFree (fun x : Vec3 => f (x, s)))
    (hInt7 : ∀ j, Integrable
      (fun y => η y * f (y, s) j) volume)
    (hSupp7 : ∀ j, HasCompactSupport
      (fun y => η y * f (y, s) j))
    (hInt8 : ∀ j, Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume)
    (hSupp8 : ∀ j, HasCompactSupport
      (fun y => spatialDeriv η j y * f (y, s) j))
    (hmem : ∀ ρ : ℝ, 0 < ρ →
      MemLp (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)))
    (hgrowth : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : ℝ, 0 < ρ →
      lpNorm (pressureP7 η f s + pressureP8 η f s)
        (ENNReal.ofReal (3 / 2))
        (volume.restrict (euclideanBall (0 : Vec3) ρ)) ≤ C * (1 + ρ)) :
    pressureP7 η f s + pressureP8 η f s =ᵐ[volume] 0 := by
  have hweak : CKN.Foundation.Heat.WeaklyHarmonicOn Set.univ
      (pressureP7 η f s + pressureP8 η f s) := by
    intro ψ hψ hψc hψU
    have htest : SmoothCompactTest ψ := by
      refine ⟨fun n => ?_, hψc⟩
      exact hψ.of_le (by simp)
    have hzero := pressure_force_pairing_zero_of_distributionalDivergenceFree
      hη hdiv hInt7 hSupp7 hInt8 hSupp8 ψ htest
    simpa only [Measure.restrict_univ, Set.mem_univ, true_and, Pi.add_apply] using hzero
  obtain ⟨C, hC, hgrowth'⟩ := hgrowth
  exact CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    hC hmem hweak hgrowth'

end CKN
