/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.PeriodicCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinModeCalculus
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.ConcreteData
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-! Finite Fourier generator identities used in the classical Galerkin estimates. -/

@[expose] public section

noncomputable section

open MeasureTheory

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalGeneratorMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalGeneratorMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalGeneratorProbabilityUnitAddCircle :
    IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

open AVenhance.Infra.Parabolic.FourierGalerkin
open Homogenization

theorem GalerkinGenerator.integral_periodicToTorus_vecDot_mul_eq_unitCell
    {b g : Vec 2 → Vec 2} {f : Vec 2 → ℝ} :
    (∫ x : Torus,
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
        (AVenhance.Infra.Torus.periodicToTorus b x)
        (AVenhance.Infra.Torus.periodicToTorus g x) *
          AVenhance.Infra.Torus.periodicToTorus f x) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (b x) (g x) * f x := by
  have hfun : (fun x : Torus =>
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
        (AVenhance.Infra.Torus.periodicToTorus b x)
        (AVenhance.Infra.Torus.periodicToTorus g x) *
          AVenhance.Infra.Torus.periodicToTorus f x) =
      AVenhance.Infra.Torus.periodicToTorus
        (fun x => Homogenization.vecDot (b x) (g x) * f x) := by
    funext x
    rfl
  rw [hfun]
  exact AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
    (d := 2) (f := fun x : Vec 2 => Homogenization.vecDot (b x) (g x) * f x)

theorem GalerkinGenerator.integral_periodicToTorus_vecDot_eq_unitCell
    {b g : Vec 2 → Vec 2} :
    (∫ x : Torus,
      AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
        (AVenhance.Infra.Torus.periodicToTorus b x)
        (AVenhance.Infra.Torus.periodicToTorus g x)) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (b x) (g x) := by
  simpa [AVenhance.Infra.Torus.periodicToTorus, mul_one] using
    (GalerkinGenerator.integral_periodicToTorus_vecDot_mul_eq_unitCell
    (b := b) (g := g) (f := fun _ => (1 : ℝ)))

theorem GalerkinGenerator.integral_periodicToTorus_mul_eq_unitCell
    {f g : Vec 2 → ℝ} :
    (∫ x : Torus,
      AVenhance.Infra.Torus.periodicToTorus f x *
        AVenhance.Infra.Torus.periodicToTorus g x) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2, f x * g x := by
  have hfun : (fun x : Torus =>
      AVenhance.Infra.Torus.periodicToTorus f x *
        AVenhance.Infra.Torus.periodicToTorus g x) =
      AVenhance.Infra.Torus.periodicToTorus (fun x => f x * g x) := by
    funext x
    rfl
  rw [hfun]
  exact AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
    (d := 2) (f := fun x : Vec 2 => f x * g x)

/-- Closed spatial unit cell used for compactness and periodic integration. -/
def GalerkinGenerator.generatorClosedUnitCell : Set (Vec 2) :=
  Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem GalerkinGenerator.generator_unitCell_subset_closed :
    AVenhance.Infra.Torus.unitCell 2 ⊆ GalerkinGenerator.generatorClosedUnitCell := by
  intro x hx
  simp only [AVenhance.Infra.Torus.unitCell,
    AVenhance.Infra.Torus.unitCellAt, Set.mem_ofPred_eq, zero_add] at hx
  simp only [GalerkinGenerator.generatorClosedUnitCell, Set.mem_pi, Set.mem_univ,
    forall_true_left]
  intro i
  exact ⟨le_of_lt (hx i).1, hx i |>.2⟩

theorem GalerkinGenerator.generator_closedUnitCell_compact :
    IsCompact GalerkinGenerator.generatorClosedUnitCell := by
  simpa [GalerkinGenerator.generatorClosedUnitCell] using
    (isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc))

theorem GalerkinGenerator.generator_continuous_integrableOn_unitCell
    {f : Vec 2 → ℝ} (hf : Continuous f) :
    IntegrableOn f (AVenhance.Infra.Torus.unitCell 2) := by
  exact (hf.continuousOn.integrableOn_compact GalerkinGenerator.generator_closedUnitCell_compact)
    |>.mono_set GalerkinGenerator.generator_unitCell_subset_closed

/-- Real Fourier mode with the finite-dimensional Galerkin indexing. -/
def GalerkinGenerator.realFourierAmbientMode (N : ℕ)
    (j : Fin (RealFourierDimension N)) : Vec 2 → ℝ :=
  realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j)

/-- Spatial gradient of a real Fourier mode with Galerkin indexing. -/
def GalerkinGenerator.realFourierAmbientModeGrad (N : ℕ)
    (j : Fin (RealFourierDimension N)) : Vec 2 → Vec 2 :=
  realFourierModeAmbientGrad N ((realFourierIndexEquivFin N).symm j)

theorem GalerkinGenerator.generator_vecDot_continuous {f g : Vec 2 → Vec 2}
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x => Homogenization.vecDot (f x) (g x)) := by
  change Continuous (fun x => ∑ i : Fin 2, f x i * g x i)
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

theorem GalerkinGenerator.generator_vecDot_sum_smul_right {ι : Type*} [Fintype ι]
    (v : Vec 2) (a : ι → ℝ) (g : ι → Vec 2) :
  Homogenization.vecDot v (∑ i, a i • g i) =
      ∑ i, a i * Homogenization.vecDot v (g i) := by
  classical
  have hcoords (j : Fin 2) : (∑ i, a i • g i) j = ∑ i, a i * g i j := by
    simp
  simp only [Homogenization.vecDot, hcoords]
  calc
    (∑ j : Fin 2, v j * ∑ i, a i * g i j) =
        ∑ j : Fin 2, ∑ i, (v j * a i) * g i j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i, ∑ j : Fin 2, (v j * a i) * g i j := Finset.sum_comm
    _ = ∑ i, a i * ∑ j : Fin 2, v j * g i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

theorem GalerkinGenerator.generator_vecDot_sum_smul_left {ι : Type*} [Fintype ι]
    (v : Vec 2) (a : ι → ℝ) (g : ι → Vec 2) :
    Homogenization.vecDot (∑ i, a i • g i) v =
      ∑ i, a i * Homogenization.vecDot (g i) v := by
  calc
    Homogenization.vecDot (∑ i, a i • g i) v =
        Homogenization.vecDot v (∑ i, a i • g i) := by
          simp [Homogenization.vecDot, mul_comm]
    _ = ∑ i, a i * Homogenization.vecDot v (g i) :=
      GalerkinGenerator.generator_vecDot_sum_smul_right v a g
    _ = ∑ i, a i * Homogenization.vecDot (g i) v := by
      apply Finset.sum_congr rfl
      intro i hi
      congr 1
      simp [Homogenization.vecDot, mul_comm]

/-- The finite ambient real Fourier expansion is smooth and retains integer periodicity. -/
theorem realFourierModeAmbientExpansion_periodic (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    AVenhance.IsZ2Periodic (realFourierModeAmbientExpansion N c) := by
  intro k x
  simp only [realFourierModeAmbientExpansion]
  apply Finset.sum_congr rfl
  intro j hj
  rw [realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm j) k x]

/-- Coordinate derivatives of a finite real Fourier synthesis are the corresponding sums of
mode derivatives. -/
theorem spaceGrad_realFourierModeAmbientExpansion_sum (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (i : Fin 2) (x : Vec 2) :
    AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x i =
      ∑ j : Fin (RealFourierDimension N), c j *
        AVenhance.spaceGrad (realFourierModeAmbient N
          ((realFourierIndexEquivFin N).symm j)) x i := by
  change fderiv ℝ (realFourierModeAmbientExpansion N c) x (basisVec i) = _
  unfold realFourierModeAmbientExpansion
  rw [fderiv_fun_sum]
  · rw [sum_apply]
    apply Finset.sum_congr rfl
    intro j hj
    rw [fderiv_const_mul
      ((realFourierModeAmbient_contDiff N
        ((realFourierIndexEquivFin N).symm j)).differentiable (by simp) x) (c j)]
    simp [AVenhance.spaceGrad]
  · intro j hj
    exact ((realFourierModeAmbient_contDiff N
      ((realFourierIndexEquivFin N).symm j)).differentiable (by simp) x).const_mul
      (c j)

theorem GalerkinGenerator.classicalWordDerivative_smooth (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hf
  | cons i w ih =>
      have hgrad : ContDiff ℝ (⊤ : ℕ∞)
          (fun x => AVenhance.spaceGrad (classicalWordDerivative w f) x i) := by
        change ContDiff ℝ (⊤ : ℕ∞)
          (fun x => fderiv ℝ (classicalWordDerivative w f) x (basisVec i))
        exact (ih.fderiv_right (by simp)).clm_apply contDiff_const
      exact hgrad

theorem GalerkinGenerator.classicalWordDerivative_periodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

/-- The positive real Fourier coefficient derivative formula iterates to every ordered spatial
derivative: finite projection commutes with each such derivative. -/
theorem realFourierWordDerivativeCoefficients_projection (N : ℕ)
    (w : List (Fin 2)) (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f) :
    realFourierWordDerivativeCoefficients N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f)) w =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (classicalWordDerivative w f)) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [realFourierWordDerivativeCoefficients, ih]
      exact realFourierModeDerivativeCoefficients_projection N
        (classicalWordDerivative w f) (GalerkinGenerator.classicalWordDerivative_smooth w f hf)
        (GalerkinGenerator.classicalWordDerivative_periodic w f hper) i

/-- Finite real Fourier synthesis agrees with the ambient smooth periodic synthesis on the
quotient torus. -/
theorem realFourierModeFin_expansion_eq_periodicToTorus (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    modeExpansion (RealFourierDimension N) (realFourierModeFin N) c =
      AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientExpansion N c) := by
  funext x
  simp [modeExpansion, realFourierModeAmbientExpansion,
    AVenhance.Infra.Torus.periodicToTorus, realFourierModeFin_eq_periodicToTorus]

private theorem frozenWeakFormCoefficient_eq_projectedGenerator_diffExpand1 :
  ∀ (N : ℕ) (c : Coefficients (RealFourierDimension N)),
    let u := realFourierModeAmbientExpansion N c;
    let m := GalerkinGenerator.realFourierAmbientMode N;
    let gm := GalerkinGenerator.realFourierAmbientModeGrad N;
    ContDiff ℝ (⊤ : ℕ∞) u →
      IsZ2Periodic u →
        (∀ (j : Fin (RealFourierDimension N)), ContDiff ℝ (⊤ : ℕ∞) (m j)) →
          (∀ (j : Fin (RealFourierDimension N)), IsZ2Periodic (m j)) →
            (∀ (x : Vec 2), spaceGrad u x = ∑ j, c.ofLp j • gm j x) →
              (∀ (i j : Fin (RealFourierDimension N)),
                  IntegrableOn (fun x => Homogenization.vecDot (gm j x) (gm i x)) (Torus.unitCell
                      2) volume) →
                ∀ (i : Fin (RealFourierDimension N)),
                  ∫ (x : Vec 2) in Torus.unitCell 2, spaceLap u x * m i x =
                    -∑ j, c.ofLp j * ∫ (x : Vec 2) in Torus.unitCell 2, Homogenization.vecDot (gm
                        j x) (gm i x)
    := by
  intro N c u m gm hu huper hm hmper hgradUPointwise htermDiffInt i
  have hparts := integral_unitCell_lap_mul (hm i) hu (hmper i) huper
  have hpoint (x : Vec 2) :
      Homogenization.vecDot (AVenhance.spaceGrad (m i) x)
          (AVenhance.spaceGrad u x) =
        ∑ j : Fin (RealFourierDimension N), c j *
          Homogenization.vecDot (gm j x) (gm i x) := by
    calc
      _ = Homogenization.vecDot (AVenhance.spaceGrad u x)
          (AVenhance.spaceGrad (m i) x) := by
        simp [Homogenization.vecDot, mul_comm]
      _ = ∑ j : Fin (RealFourierDimension N), c j *
          Homogenization.vecDot (gm j x) (gm i x) := by
        rw [hgradUPointwise x]
        simpa [m, gm, GalerkinGenerator.realFourierAmbientMode,
            GalerkinGenerator.realFourierAmbientModeGrad,
          realFourierModeAmbientGrad] using
          GalerkinGenerator.generator_vecDot_sum_smul_left
            (AVenhance.spaceGrad (m i) x) c (fun j => gm j x)
  have hsum := integral_finsetSum (Finset.univ : Finset (Fin (RealFourierDimension N)))
    (μ := (volume : Measure (Vec 2)).restrict (AVenhance.Infra.Torus.unitCell 2))
    (f := fun j => fun x => c j * Homogenization.vecDot (gm j x) (gm i x))
    (fun j hj => (htermDiffInt i j).const_mul (c j))
  have hdotSymm (x : Vec 2) :
      Homogenization.vecDot (AVenhance.spaceGrad (m i) x)
          (AVenhance.spaceGrad u x) =
      Homogenization.vecDot (AVenhance.spaceGrad u x)
          (AVenhance.spaceGrad (m i) x) := by
    simp [Homogenization.vecDot, mul_comm]
  calc
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
        m i x * AVenhance.spaceLap u x := by
      apply setIntegral_congr_ae (AVenhance.Infra.Torus.measurableSet_unitCell 2)
      filter_upwards with x hx
      ring
    _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (AVenhance.spaceGrad (m i) x)
          (AVenhance.spaceGrad u x) := hparts
    _ = -∫ x in AVenhance.Infra.Torus.unitCell 2,
        ∑ j : Fin (RealFourierDimension N), c j *
          Homogenization.vecDot (gm j x) (gm i x) := by
      congr 1
      apply setIntegral_congr_ae (AVenhance.Infra.Torus.measurableSet_unitCell 2)
      filter_upwards with x hx
      exact hpoint x
    _ = -∑ j : Fin (RealFourierDimension N), c j *
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecDot (gm j x) (gm i x) := by
      rw [hsum]
      simp_rw [integral_const_mul]

private theorem frozenWeakFormCoefficient_eq_projectedGenerator_split2 :
  ∀ (N : ℕ) (b : ℝ → Vec 2 → Vec 2) (κ t : ℝ) (c : Coefficients (RealFourierDimension N)),
    let u := realFourierModeAmbientExpansion N c;
    let m := GalerkinGenerator.realFourierAmbientMode N;
    ContDiff ℝ (⊤ : ℕ∞) u →
      (∀ (j : Fin (RealFourierDimension N)), ContDiff ℝ (⊤ : ℕ∞) (m j)) →
        Continuous (b t) →
          ∀ (i : Fin (RealFourierDimension N)),
            ∫ (x : Vec 2) in Torus.unitCell 2,
                (κ * spaceLap u x - Homogenization.vecDot (b t x) (spaceGrad u x)) * m i x =
              (κ * ∫ (x : Vec 2) in Torus.unitCell 2, spaceLap u x * m i x) -
                ∫ (x : Vec 2) in Torus.unitCell 2, Homogenization.vecDot (b t x) (spaceGrad u x) *
                    m i x
    := by
  intro N b κ t c u m hu hm hbcont i
  have huGradCont : Continuous (AVenhance.spaceGrad u) := by
    apply continuous_pi
    intro j
    change Continuous (fun x => fderiv ℝ u x (Homogenization.basisVec j))
    exact (hu.continuous_fderiv (by simp)).clm_apply continuous_const
  have huLapCont : Continuous (AVenhance.spaceLap u) := by
    unfold AVenhance.spaceLap
    apply continuous_finsetSum
    intro j hj
    have hgradSmooth : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => AVenhance.spaceGrad u x j) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun x => fderiv ℝ u x (Homogenization.basisVec j))
      exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
    change Continuous (fun x => fderiv ℝ
      (fun y => AVenhance.spaceGrad u y j) x (Homogenization.basisVec j))
    exact (hgradSmooth.continuous_fderiv (by simp)).clm_apply continuous_const
  have hlapInt : IntegrableOn
      (fun x => AVenhance.spaceLap u x * m i x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    GalerkinGenerator.generator_continuous_integrableOn_unitCell (huLapCont.mul (hm i).continuous)
  have hdriftInt : IntegrableOn
      (fun x => Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x) * m i x)
      (AVenhance.Infra.Torus.unitCell 2) :=
    GalerkinGenerator.generator_continuous_integrableOn_unitCell
      ((GalerkinGenerator.generator_vecDot_continuous hbcont huGradCont).mul (hm i).continuous)
  have hfun : (fun x =>
      (κ * AVenhance.spaceLap u x -
        Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x)) * m i x) =
      fun x => κ * (AVenhance.spaceLap u x * m i x) -
        Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x) * m i x := by
    funext x
    ring
  rw [hfun, integral_sub, integral_const_mul]
  · exact hlapInt.const_mul κ
  · exact hdriftInt

/-- On a finite real Fourier span, the weak matrix is precisely the orthogonal projection of
`κ Δu - b · ∇u`. The diffusion part is identified by periodic integration by parts, while the
drift part is expanded directly in the finite Fourier synthesis. -/
theorem frozenWeakFormCoefficient_eq_projectedGenerator (N : ℕ)
    (b : ℝ → Vec 2 → Vec 2) (κ t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c : Coefficients (RealFourierDimension N))
    (hb : Continuous (b t)) :
    frozenWeakFormCoefficient b κ (realFourierModeFin N)
        (realFourierModeGradFin N) t c =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (fun x =>
          κ * AVenhance.spaceLap (realFourierModeAmbientExpansion N c) x -
            Homogenization.vecDot (b t x)
              (AVenhance.spaceGrad (realFourierModeAmbientExpansion N c) x))) := by
  classical
  let u := realFourierModeAmbientExpansion N c
  let m := GalerkinGenerator.realFourierAmbientMode N
  let gm := GalerkinGenerator.realFourierAmbientModeGrad N
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have huper : AVenhance.IsZ2Periodic u := realFourierModeAmbientExpansion_periodic N c
  have hm (j : Fin (RealFourierDimension N)) :
      ContDiff ℝ (⊤ : ℕ∞) (m j) := by
    have hm0 : ContDiff ℝ ⊤ (m j) := by
      simpa [m, GalerkinGenerator.realFourierAmbientMode] using
        realFourierModeAmbient_contDiff N ((realFourierIndexEquivFin N).symm j)
    exact hm0.of_le (by simp)
  have hmper (j : Fin (RealFourierDimension N)) : AVenhance.IsZ2Periodic (m j) :=
    realFourierModeAmbient_periodic N ((realFourierIndexEquivFin N).symm j)
  have hgmcont (j : Fin (RealFourierDimension N)) : Continuous (gm j) := by
    exact realFourierModeAmbientGrad_continuous N
      ((realFourierIndexEquivFin N).symm j)
  have hbcont : Continuous (b t) := hb
  have hmodeTor (i : Fin (RealFourierDimension N)) :
      realFourierModeFin N i = AVenhance.Infra.Torus.periodicToTorus (m i) := by
    exact realFourierModeFin_eq_periodicToTorus N i
  have hgradTor (i : Fin (RealFourierDimension N)) :
      realFourierModeGradFin N i = AVenhance.Infra.Torus.periodicToTorus (gm i) := by
    exact realFourierModeGradFin_eq_periodicToTorus N i
  have hgradU : (fun x => AVenhance.spaceGrad u x) =
      fun x => ∑ j : Fin (RealFourierDimension N), c j • gm j x := by
    funext x
    ext i
    simpa [u, gm, GalerkinGenerator.realFourierAmbientModeGrad, realFourierModeAmbientGrad] using
      (spaceGrad_realFourierModeAmbientExpansion_sum N c i x)
  have hgradUPointwise (x : Vec 2) : AVenhance.spaceGrad u x =
      ∑ j : Fin (RealFourierDimension N), c j • gm j x := congrFun hgradU x
  have hweakDrift (i j : Fin (RealFourierDimension N)) :
      (∫ x : Torus,
        AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (AVenhance.Infra.Torus.periodicToTorus (b t) x)
          (realFourierModeGradFin N j x) * realFourierModeFin N i x) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (b t x) (gm j x) * m i x := by
    rw [hgradTor j, hmodeTor i]
    exact GalerkinGenerator.integral_periodicToTorus_vecDot_mul_eq_unitCell
  have hweakDiff (i j : Fin (RealFourierDimension N)) :
      (∫ x : Torus,
        AVenhance.Infra.Parabolic.FourierGalerkin.vecDot
          (realFourierModeGradFin N j x) (realFourierModeGradFin N i x)) =
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (gm j x) (gm i x) := by
    rw [hgradTor j, hgradTor i]
    exact GalerkinGenerator.integral_periodicToTorus_vecDot_eq_unitCell
  have hproject (i : Fin (RealFourierDimension N)) :
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => κ * AVenhance.spaceLap u x -
            Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x)))) i =
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        (κ * AVenhance.spaceLap u x -
          Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x)) * m i x := by
    change (∫ x : Torus,
      AVenhance.Infra.Torus.periodicToTorus
        (fun x => κ * AVenhance.spaceLap u x -
          Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x)) x *
        realFourierModeFin N i x) = _
    rw [hmodeTor i]
    exact GalerkinGenerator.integral_periodicToTorus_mul_eq_unitCell
  have htermDriftInt (i j : Fin (RealFourierDimension N)) : IntegrableOn
      (fun x => Homogenization.vecDot (b t x) (gm j x) * m i x)
      (AVenhance.Infra.Torus.unitCell 2) := by
    exact GalerkinGenerator.generator_continuous_integrableOn_unitCell
      ((GalerkinGenerator.generator_vecDot_continuous hbcont (hgmcont j)).mul (hm i).continuous)
  have htermDiffInt (i j : Fin (RealFourierDimension N)) : IntegrableOn
      (fun x => Homogenization.vecDot (gm j x) (gm i x))
      (AVenhance.Infra.Torus.unitCell 2) := by
    exact GalerkinGenerator.generator_continuous_integrableOn_unitCell
      (GalerkinGenerator.generator_vecDot_continuous (hgmcont j) (hgmcont i))
  have hdriftExpand (i : Fin (RealFourierDimension N)) :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x) * m i x) =
      ∑ j : Fin (RealFourierDimension N), c j *
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecDot (b t x) (gm j x) * m i x := by
    have hpoint (x : Vec 2) :
        Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x) * m i x =
          ∑ j : Fin (RealFourierDimension N), c j *
            (Homogenization.vecDot (b t x) (gm j x) * m i x) := by
      calc
        _ = (∑ j : Fin (RealFourierDimension N),
              c j * Homogenization.vecDot (b t x) (gm j x)) * m i x := by
          rw [hgradUPointwise x, GalerkinGenerator.generator_vecDot_sum_smul_right]
        _ = _ := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    calc
      _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          ∑ j : Fin (RealFourierDimension N), c j *
            (Homogenization.vecDot (b t x) (gm j x) * m i x) := by
        apply setIntegral_congr_ae (AVenhance.Infra.Torus.measurableSet_unitCell 2)
        filter_upwards with x hx
        exact hpoint x
      _ = ∑ j : Fin (RealFourierDimension N), c j *
          ∫ x in AVenhance.Infra.Torus.unitCell 2,
            Homogenization.vecDot (b t x) (gm j x) * m i x := by
        rw [integral_finsetSum]
        · simp_rw [integral_const_mul]
        · intro j hj
          exact (htermDriftInt i j).const_mul (c j)
  have hdiffExpand (i : Fin (RealFourierDimension N)) :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        AVenhance.spaceLap u x * m i x) =
      -∑ j : Fin (RealFourierDimension N), c j *
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecDot (gm j x) (gm i x) := by
    apply frozenWeakFormCoefficient_eq_projectedGenerator_diffExpand1
    all_goals assumption
  have hsplit (i : Fin (RealFourierDimension N)) :
      (∫ x in AVenhance.Infra.Torus.unitCell 2,
        (κ * AVenhance.spaceLap u x -
          Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x)) * m i x) =
      κ * (∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.spaceLap u x * m i x) -
        ∫ x in AVenhance.Infra.Torus.unitCell 2,
          Homogenization.vecDot (b t x) (AVenhance.spaceGrad u x) * m i x := by
    apply frozenWeakFormCoefficient_eq_projectedGenerator_split2
    all_goals assumption
  have hsumIdentity (i : Fin (RealFourierDimension N)) :
      (∑ j : Fin (RealFourierDimension N),
        (-(∫ x in AVenhance.Infra.Torus.unitCell 2,
            Homogenization.vecDot (b t x) (gm j x) * m i x) -
          κ * ∫ x in AVenhance.Infra.Torus.unitCell 2,
            Homogenization.vecDot (gm j x) (gm i x)) * c j) =
      κ * (-(∑ j : Fin (RealFourierDimension N), c j *
          ∫ x in AVenhance.Infra.Torus.unitCell 2,
            Homogenization.vecDot (gm j x) (gm i x))) -
        ∑ j : Fin (RealFourierDimension N), c j *
          ∫ x in AVenhance.Infra.Torus.unitCell 2,
            Homogenization.vecDot (b t x) (gm j x) * m i x := by
    let d : Fin (RealFourierDimension N) → ℝ := fun j =>
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (b t x) (gm j x) * m i x
    let e : Fin (RealFourierDimension N) → ℝ := fun j =>
      ∫ x in AVenhance.Infra.Torus.unitCell 2,
        Homogenization.vecDot (gm j x) (gm i x)
    change (∑ j, (-d j - κ * e j) * c j) =
      κ * (-(∑ j, c j * e j)) - ∑ j, c j * d j
    calc
      (∑ j, (-d j - κ * e j) * c j) =
          ∑ j, (-(c j * d j) - κ * (c j * e j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j, -(c j * d j)) - ∑ j, κ * (c j * e j) :=
        by rw [Finset.sum_sub_distrib]
      _ = -(∑ j, c j * d j) - κ * (∑ j, c j * e j) := by
        rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      _ = κ * (-(∑ j, c j * e j)) - ∑ j, c j * d j := by ring
  ext i
  rw [show (frozenWeakFormCoefficient b κ (realFourierModeFin N)
      (realFourierModeGradFin N) t c) i =
        ∑ j : Fin (RealFourierDimension N),
          weakFormMatrixEntry
            (fun s x => AVenhance.Infra.Torus.periodicToTorus (b s) x)
            κ (realFourierModeFin N) (realFourierModeGradFin N) t i j * c j by
      simp [frozenWeakFormCoefficient, ht, matrixCoefficientCLM_apply]]
  rw [hproject i]
  simp_rw [weakFormMatrixEntry, hweakDrift i, hweakDiff i]
  rw [hsplit i, hdiffExpand i, hdriftExpand i]
  exact hsumIdentity i

/-- Multiplication by a bounded smooth periodic function followed by Fourier projection is
bounded by the multiplier's uniform norm. The finite Fourier synthesis has exactly the
coefficient-space `L²` norm. -/
theorem realFourierProjection_product_norm_le (N : ℕ)
    (c : Coefficients (RealFourierDimension N)) (f : Vec 2 → ℝ)
    (hf : Continuous f) {B : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ x, ‖f x‖ ≤ B) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus
        (fun x => f x * realFourierModeAmbientExpansion N c x))‖ ≤ B * ‖c‖ := by
  let g : Vec 2 → ℝ := realFourierModeAmbientExpansion N c
  let ft : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus f
  let gt : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus g
  let q : Torus → ℝ := AVenhance.Infra.Torus.periodicToTorus (fun x => f x * g x)
  have hg : Continuous g := (realFourierModeAmbientExpansion_contDiff N c).continuous
  have hft : Measurable ft := by
    exact hf.measurable.comp
      (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have hgt : Measurable gt := by
    exact hg.measurable.comp
      (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have hqeq : q = fun x => ft x * gt x := by
    funext x
    rfl
  have hqmeas : Measurable q := by
    rw [hqeq]
    exact hft.mul hgt
  have hboundT : ∀ᵐ x : Torus, ‖ft x‖ ≤ B := by
    filter_upwards with x
    exact hbound (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  have hgmem : MemLp gt 2 (volume : Measure Torus) := by
    have hfinite := realFourierScalarExpansion_memLp N c
    have hexp := realFourierModeFin_expansion_eq_periodicToTorus N c
    change MemLp (AVenhance.Infra.Torus.periodicToTorus g) 2 volume
    rw [← hexp]
    exact hfinite
  have hqpoint : ∀ᵐ x : Torus, ‖q x‖ ≤ B * ‖gt x‖ := by
    filter_upwards [hboundT] with x hx
    rw [hqeq, norm_mul]
    exact mul_le_mul_of_nonneg_right hx (norm_nonneg (gt x))
  have hqmem : MemLp q 2 (volume : Measure Torus) :=
    MemLp.of_le_mul hgmem hqmeas.aestronglyMeasurable hqpoint
  have hproj := realFourierModeFin_projectionCoefficients_norm_le N hqmem
  have hmul : ‖hqmem.toLp q‖ ≤ B * ‖hgmem.toLp gt‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hqmem.coeFn_toLp, hgmem.coeFn_toLp, hqpoint] with x hq hg h
    rw [hq, hg]
    exact h
  have hgtLp : hgmem.toLp gt = realFourierScalarMap N c := by
    apply Lp.ext
    filter_upwards [hgmem.coeFn_toLp,
      realFourierScalarMap_coeFn N c] with x hgt hmap
    have hexp := congrFun (realFourierModeFin_expansion_eq_periodicToTorus N c) x
    calc
      (hgmem.toLp gt) x = gt x := hgt
      _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x := hexp.symm
      _ = (realFourierScalarMap N c) x := hmap.symm
  calc
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) q‖ ≤
        ‖hqmem.toLp q‖ := hproj
    _ ≤ B * ‖hgmem.toLp gt‖ := hmul
    _ = B * ‖c‖ := by rw [hgtLp, realFourierScalarMap_norm]

/-- The real Fourier projection as a continuous linear map from torus `L²` to coefficients. -/
def realFourierProjectionCLM (N : ℕ) :
    ScalarTorusL2 →L[ℝ] Coefficients (RealFourierDimension N) := by
  let e : Coefficients (RealFourierDimension N) ≃L[ℝ]
      (Fin (RealFourierDimension N) → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (RealFourierDimension N) => ℝ)
  let p : ScalarTorusL2 →L[ℝ] (Fin (RealFourierDimension N) → ℝ) :=
    ContinuousLinearMap.pi (fun i => innerSL ℝ (realFourierModeL2 N i))
  exact e.symm.toContinuousLinearMap.comp p

@[simp]
theorem realFourierProjectionCLM_apply (N : ℕ) (f : ScalarTorusL2)
    (i : Fin (RealFourierDimension N)) :
    (realFourierProjectionCLM N f) i = inner ℝ f (realFourierModeL2 N i) := by
  rw [show (realFourierProjectionCLM N f) i =
      inner ℝ (realFourierModeL2 N i) f by simp [realFourierProjectionCLM]]
  exact real_inner_comm _ _

/-- Integral-defined projection coefficients agree with the continuous `L²` projection map. -/
theorem realFourierModeProjectionCoefficients_eq_CLM (N : ℕ)
    {f : Torus → ℝ} (hf : MemLp f 2 (volume : Measure Torus)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f =
      realFourierProjectionCLM N (hf.toLp f) := by
  ext i
  rw [realFourierProjectionCLM_apply, MeasureTheory.L2.inner_def]
  simp only [modeProjectionCoefficients, PiLp.toLp_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,
    realFourierModeFin_memLp N i |>.coeFn_toLp] with x h₁ h₂
  rw [realFourierModeL2, h₁, h₂]
  simp [mul_comm]

/-- Real Fourier projection is additive on square-integrable inputs. -/
theorem realFourierModeProjectionCoefficients_add (N : ℕ)
    {f g : Torus → ℝ}
    (hf : MemLp f 2 (volume : Measure Torus))
    (hg : MemLp g 2 (volume : Measure Torus)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) (f + g) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) g := by
  rw [realFourierModeProjectionCoefficients_eq_CLM N (hf.add hg),
    realFourierModeProjectionCoefficients_eq_CLM N hf,
    realFourierModeProjectionCoefficients_eq_CLM N hg]
  rw [MemLp.toLp_add hf hg, map_add]

/-- Real Fourier projection is homogeneous on square-integrable inputs. -/
theorem realFourierModeProjectionCoefficients_smul (N : ℕ)
    (a : ℝ) {f : Torus → ℝ}
    (hf : MemLp f 2 (volume : Measure Torus)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) (a • f) =
      a • modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f := by
  rw [realFourierModeProjectionCoefficients_eq_CLM N (hf.const_smul a),
    realFourierModeProjectionCoefficients_eq_CLM N hf,
    MemLp.toLp_const_smul a hf, map_smul]

/-- Real Fourier projection is subtractive on square-integrable inputs. -/
theorem realFourierModeProjectionCoefficients_sub (N : ℕ)
    {f g : Torus → ℝ}
    (hf : MemLp f 2 (volume : Measure Torus))
    (hg : MemLp g 2 (volume : Measure Torus)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) (f - g) =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f -
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) g := by
  rw [realFourierModeProjectionCoefficients_eq_CLM N (hf.sub hg),
    realFourierModeProjectionCoefficients_eq_CLM N hf,
    realFourierModeProjectionCoefficients_eq_CLM N hg,
    MemLp.toLp_sub hf hg, map_sub]

/-- A continuous integer-periodic scalar function is bounded on the whole space. -/
theorem exists_uniform_bound_of_continuous_periodic
    (f : Vec 2 → ℝ) (hf : Continuous f)
    (hper : AVenhance.IsZ2Periodic f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  let g : Vec 2 → ℝ := fun x => ‖f x‖
  have hcont : Continuous g := continuous_norm.comp hf
  have hupper : BddAbove (g '' GalerkinGenerator.generatorClosedUnitCell) :=
    GalerkinGenerator.generator_closedUnitCell_compact.bddAbove_image hcont.continuousOn
  let C₀ : ℝ := sSup (g '' GalerkinGenerator.generatorClosedUnitCell)
  have hcell_nonempty : (g '' GalerkinGenerator.generatorClosedUnitCell).Nonempty := by
    refine ⟨g (fun _ => (0 : ℝ)), (fun _ => (0 : ℝ)), ?_, rfl⟩
    simp only [GalerkinGenerator.generatorClosedUnitCell, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    intro i
    norm_num
  have hcell_bound (x : Vec 2) (hx : x ∈ GalerkinGenerator.generatorClosedUnitCell) :
      g x ≤ C₀ := le_csSup hupper ⟨x, hx, rfl⟩
  refine ⟨max C₀ 0, le_max_right _ _, ?_⟩
  intro x
  let k : Fin 2 → ℤ := fun i => -Int.floor (x i)
  let y : Vec 2 := x + AVenhance.latticeShift k
  have hyi (i : Fin 2) : y i = x i - (Int.floor (x i) : ℝ) := by
    dsimp [y, k, AVenhance.latticeShift]
    rw [Int.cast_neg]
    exact Int.self_sub_floor (a := (x i : ℝ))
  have hy : y ∈ GalerkinGenerator.generatorClosedUnitCell := by
    simp only [GalerkinGenerator.generatorClosedUnitCell, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    intro i
    rw [hyi]
    constructor
    · exact sub_nonneg.mpr (Int.floor_le (x i))
    · have hfloor := Int.lt_floor_add_one (x i)
      linarith
  have hperiod := hper k x
  have hbound := hcell_bound y hy
  change ‖f y‖ ≤ C₀ at hbound
  calc
    ‖f x‖ = ‖f y‖ := by rw [← hperiod]
    _ ≤ C₀ := hbound
    _ ≤ max C₀ 0 := le_max_left _ _

/-- The torus representative of a continuous periodic scalar is square-integrable. -/
theorem memLp_periodicToTorus_real {f : Vec 2 → ℝ}
    (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f) :
    MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2
      (volume : Measure Torus) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_of_continuous_periodic f hf hper
  have hmeas : Measurable (AVenhance.Infra.Torus.periodicToTorus f) :=
    hf.measurable.comp
      (AVenhance.Infra.Torus.measurable_unitTorusRepresentative 2)
  have hpoint : ∀ᵐ x : Torus, ‖AVenhance.Infra.Torus.periodicToTorus f x‖ ≤ C := by
    filter_upwards with x
    exact hbound (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  exact MemLp.of_bound hmeas.aestronglyMeasurable C hpoint

/-- Fourier projection of a smooth periodic scalar is bounded in coefficient norm by any global
uniform bound for the scalar. -/
theorem realFourierProjectionCoefficients_norm_le_uniform (N : ℕ)
    (f : Vec 2 → ℝ) (hf : Continuous f) (hper : AVenhance.IsZ2Periodic f)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus f)‖ ≤ B := by
  let mem := memLp_periodicToTorus_real hf hper
  have hproj := realFourierModeFin_projectionCoefficients_norm_le N mem
  have hmass : measureUnivNNReal (volume : Measure Torus) = 1 := by
    simp [measureUnivNNReal]
  have hpoint : ∀ᵐ x : Torus,
      ‖mem.toLp (AVenhance.Infra.Torus.periodicToTorus f) x‖ ≤ B := by
    filter_upwards [mem.coeFn_toLp] with x hx
    rw [hx]
    exact hbound (AVenhance.Infra.Torus.unitTorusRepresentative 2 x)
  have hLp := Lp.norm_le_of_ae_bound
    (f := mem.toLp (AVenhance.Infra.Torus.periodicToTorus f)) hB hpoint
  calc
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus f)‖ ≤
      ‖mem.toLp (AVenhance.Infra.Torus.periodicToTorus f)‖ := hproj
    _ ≤ B := by simpa [hmass] using hLp

theorem GalerkinGenerator.continuous_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, Continuous f) : Continuous L.sum := by
  induction L with
  | nil => exact continuous_const
  | cons f L ih =>
      have hf := hL f (by simp)
      have htail : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hL g (by simp [hg])
      change Continuous (fun x => f x + L.sum x)
      exact hf.add (ih htail)

theorem GalerkinGenerator.periodic_listSum (L : List (Vec 2 → ℝ))
    (hL : ∀ f ∈ L, AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic L.sum := by
  induction L with
  | nil => intro k x; rfl
  | cons f L ih =>
      have hf := hL f (by simp)
      have htail : ∀ g ∈ L, AVenhance.IsZ2Periodic g := by
        intro g hg
        exact hL g (by simp [hg])
      intro k x
      simp only [List.sum_cons]
      change f (x + AVenhance.latticeShift k) + L.sum (x + AVenhance.latticeShift k) = _
      rw [hf k x, ih htail k x]
      rfl

/-- Fourier projection commutes with finite sums of continuous periodic ambient functions. -/
theorem realFourierProjectionCoefficients_listSum (N : ℕ)
    (L : List (Vec 2 → ℝ))
    (hcont : ∀ f ∈ L, Continuous f)
    (hper : ∀ f ∈ L, AVenhance.IsZ2Periodic f) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus L.sum) =
      (L.map fun f => modeProjectionCoefficients (RealFourierDimension N)
        (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus f)).sum := by
  induction L with
  | nil =>
      simp only [List.sum_nil]
      have hzero : AVenhance.Infra.Torus.periodicToTorus
          (0 : Vec 2 → ℝ) = 0 := by
        funext x
        rfl
      rw [hzero]
      ext i
      simp [modeProjectionCoefficients]
  | cons f L ih =>
      have hfcont := hcont f (by simp)
      have hfper := hper f (by simp)
      have htailcont : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      have htailper : ∀ g ∈ L, AVenhance.IsZ2Periodic g := by
        intro g hg
        exact hper g (by simp [hg])
      have hcontSum := GalerkinGenerator.continuous_listSum L htailcont
      have hperSum := GalerkinGenerator.periodic_listSum L htailper
      have htorusAdd : AVenhance.Infra.Torus.periodicToTorus
          (fun x => f x + L.sum x) =
          AVenhance.Infra.Torus.periodicToTorus f +
            AVenhance.Infra.Torus.periodicToTorus L.sum := by
        funext x
        rfl
      rw [show (f :: L).sum = fun x => f x + L.sum x by rfl,
        htorusAdd, realFourierModeProjectionCoefficients_add N
        (memLp_periodicToTorus_real hfcont hfper)
        (memLp_periodicToTorus_real hcontSum hperSum), ih htailcont htailper]
      simp

/-- The norm of a projected finite list sum is bounded by the sum of the projected term norms. -/
theorem realFourierProjectionCoefficients_listSum_norm_le (N : ℕ)
    (L : List (Vec 2 → ℝ))
    (hcont : ∀ f ∈ L, Continuous f)
    (hper : ∀ f ∈ L, AVenhance.IsZ2Periodic f) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus L.sum)‖ ≤
      (L.map fun f => ‖modeProjectionCoefficients (RealFourierDimension N)
        (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus f)‖).sum := by
  rw [realFourierProjectionCoefficients_listSum N L hcont hper]
  induction L with
  | nil => simp
  | cons f L ih =>
      have htailcont : ∀ g ∈ L, Continuous g := by
        intro g hg
        exact hcont g (by simp [hg])
      have htailper : ∀ g ∈ L, AVenhance.IsZ2Periodic g := by
        intro g hg
        exact hper g (by simp [hg])
      simp only [List.map_cons, List.sum_cons]
      exact (norm_add_le _ _).trans
        (add_le_add_right (ih htailcont htailper) _)

/-- Ordered spatial derivatives distribute over a finite sum of smooth scalar functions. -/
theorem classicalWordDerivative_finsetSum {ι : Type*} (s : Finset ι)
    (f : ι → Vec 2 → ℝ) (hf : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (w : List (Fin 2)) :
    classicalWordDerivative w (fun x => ∑ i ∈ s, f i x) =
      fun x => ∑ i ∈ s, classicalWordDerivative w (f i) x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
      funext x
      change AVenhance.spaceGrad
          (classicalWordDerivative w (fun y => ∑ i ∈ s, f i y)) x j = _
      rw [ih]
      change AVenhance.spaceGrad (fun y => ∑ i ∈ s,
        classicalWordDerivative w (f i) y) x j = _
      have hsum : fderiv ℝ (fun y => ∑ i ∈ s,
          classicalWordDerivative w (f i) y) x =
          ∑ i ∈ s, fderiv ℝ (classicalWordDerivative w (f i)) x := by
        rw [fderiv_fun_sum]
        intro i hi
        exact (classicalWordDerivative_contDiff w (f i) (hf i hi)).differentiable
          (by simp) x
      change fderiv ℝ (fun y => ∑ i ∈ s,
        classicalWordDerivative w (f i) y) x (Homogenization.basisVec j) = _
      rw [hsum]
      simp [classicalWordDerivative, AVenhance.spaceGrad]

/-- Ordered spatial derivatives commute with subtraction. -/
theorem classicalWordDerivative_sub (w : List (Fin 2)) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x - g x) =
      fun x => classicalWordDerivative w f x - classicalWordDerivative w g x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y - g y)) x i = _
      rw [ih]
      exact classicalSpaceGrad_sub (classicalWordDerivative w f)
        (classicalWordDerivative w g)
        (classicalWordDerivative_contDiff w f hf)
        (classicalWordDerivative_contDiff w g hg) i x

/-- Ordered spatial derivatives commute with multiplication by a real constant. -/
theorem classicalWordDerivative_const_mul (w : List (Fin 2)) (a : ℝ)
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (fun x => a * f x) =
      fun x => a * classicalWordDerivative w f x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => a * f y)) x i = _
      rw [ih]
      change fderiv ℝ (fun y => a • classicalWordDerivative w f y) x
        (Homogenization.basisVec i) = _
      rw [show (fun y => a • classicalWordDerivative w f y) =
        a • classicalWordDerivative w f by rfl]
      rw [fderiv_const_smul
        ((classicalWordDerivative_contDiff w f hf).differentiable (by simp) x) a]
      rfl

/-- Spatial derivatives commute with the Laplacian on smooth functions. -/
theorem classicalWordDerivative_spaceLap (w : List (Fin 2)) (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    classicalWordDerivative w (fun x => AVenhance.spaceLap f x) =
      fun x => AVenhance.spaceLap (classicalWordDerivative w f) x := by
  rw [show (fun x => AVenhance.spaceLap f x) = fun x =>
      ∑ i : Fin 2, AVenhance.spaceGrad
        (fun y => AVenhance.spaceGrad f y i) x i by rfl]
  rw [classicalWordDerivative_finsetSum Finset.univ]
  · funext x
    change (∑ i : Fin 2, classicalWordDerivative w
        (fun y => AVenhance.spaceGrad
          (fun z => AVenhance.spaceGrad f z i) y i) x) = _
    unfold AVenhance.spaceLap
    apply Finset.sum_congr rfl
    intro i hi
    have hfGrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => AVenhance.spaceGrad f y i) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ f y (Homogenization.basisVec i))
      exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    have hfirst := classicalWordDerivative_commute_gradient w
      (fun y => AVenhance.spaceGrad f y i) hfGrad i
    have hsecond := classicalWordDerivative_commute_gradient w f hf i
    rw [hfirst, hsecond]
  · intro i hi
    have hfGrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun y => AVenhance.spaceGrad f y i) := by
      change ContDiff ℝ (⊤ : ℕ∞)
        (fun y => fderiv ℝ f y (Homogenization.basisVec i))
      exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad (fun y => AVenhance.spaceGrad f y i) x i)
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad f y i) x
        (Homogenization.basisVec i))
    exact (hfGrad.fderiv_right (by simp)).clm_apply contDiff_const

end AVenhance.Infra.Classical

end
