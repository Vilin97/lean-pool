/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinResidualBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinEvolution
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Parabolic.FourierGalerkin.GalerkinSequence

/-! Strong Cauchy convergence of nested smooth Fourier Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalCauchyMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalCauchyMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalCauchyProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

namespace LinearIntegralSolution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- A continuous linear map sends an integral solution to the target equation with the exact
cross-space operator commutator in its source. -/
theorem continuousLinearMap_transform_between
    {A : ℝ → E →L[ℝ] E} {B : ℝ → F →L[ℝ] F}
    {f y : ℝ → E} {y₀ : E} {a b : ℝ}
    (hab : a ≤ b)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution A f y₀ a b y)
    (hRhs : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs A f y) volume a b)
    (L : E →L[ℝ] F) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution B
      (fun t => L (f t) + L (A t (y t)) - B t (L (y t)))
      (L y₀) a b (fun t => L (y t)) := by
  intro t ht
  have hsubset : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hRhsT : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs A f y) volume a t := hRhs.mono_set hsubset
  have hsource (s : ℝ) :
      L (AVenhance.Infra.ODE.linearRhs A f y s) =
        AVenhance.Infra.ODE.linearRhs B
          (fun t => L (f t) + L (A t (y t)) - B t (L (y t)))
          (fun t => L (y t)) s := by
    simp only [AVenhance.Infra.ODE.linearRhs, map_add]
    abel
  calc
    L (y t) = L (y₀ +
        ∫ s in a..t, AVenhance.Infra.ODE.linearRhs A f y s) :=
      congrArg L (hy t ht)
    _ = L y₀ + ∫ s in a..t,
        L (AVenhance.Infra.ODE.linearRhs A f y s) := by
      rw [map_add]
      congr 1
      exact (L.intervalIntegral_comp_comm hRhsT).symm
    _ = L y₀ + ∫ s in a..t,
        AVenhance.Infra.ODE.linearRhs B
          (fun t => L (f t) + L (A t (y t)) - B t (L (y t)))
          (fun t => L (y t)) s := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      exact hsource s

/-- The difference of two solutions for one linear operator solves the same equation with the
difference source. -/
theorem sub
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {f g y z : ℝ → E} {y₀ z₀ : E} {a b : ℝ}
    (hab : a ≤ b)
    (hy : AVenhance.Infra.ODE.IsLinearIntegralSolution A f y₀ a b y)
    (hz : AVenhance.Infra.ODE.IsLinearIntegralSolution A g z₀ a b z)
    (hIy : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs A f y) volume a b)
    (hIz : IntervalIntegrable (AVenhance.Infra.ODE.linearRhs A g z) volume a b) :
    AVenhance.Infra.ODE.IsLinearIntegralSolution A (fun t => f t - g t)
      (y₀ - z₀) a b (fun t => y t - z t) := by
  intro t ht
  have hsubset : uIcc a t ⊆ uIcc a b := by
    rw [uIcc_of_le ht.1, uIcc_of_le hab]
    intro s hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  have hIyT := hIy.mono_set hsubset
  have hIzT := hIz.mono_set hsubset
  calc
    y t - z t = (y₀ + ∫ s in a..t,
          AVenhance.Infra.ODE.linearRhs A f y s) -
        (z₀ + ∫ s in a..t, AVenhance.Infra.ODE.linearRhs A g z s) := by
      rw [hy t ht, hz t ht]
    _ = (y₀ - z₀) + ∫ s in a..t,
          (AVenhance.Infra.ODE.linearRhs A f y s -
            AVenhance.Infra.ODE.linearRhs A g z s) := by
      rw [intervalIntegral.integral_sub hIyT hIzT]
      module
    _ = (y₀ - z₀) + ∫ s in a..t,
          AVenhance.Infra.ODE.linearRhs A (fun r => f r - g r)
            (fun r => y r - z r) s := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [AVenhance.Infra.ODE.linearRhs, map_sub]
      abel

end LinearIntegralSolution

/-- The zero-extension map on nested real Fourier coefficient spaces. -/
noncomputable def classicalGalerkinLiftLinearMap {M N : ℕ} (hMN : M ≤ N) :
    Coefficients (RealFourierDimension M) →ₗ[ℝ]
      Coefficients (RealFourierDimension N) where
  toFun := realFourierCoefficientsLift hMN
  map_add' := by
    intro c d
    ext j
    simp only [realFourierCoefficientsLift, PiLp.toLp_apply, PiLp.add_apply]
    change (∑ i : Fin (RealFourierDimension M),
        (if realFourierIndexLiftFin hMN i = j then c i + d i else 0)) = _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hij : realFourierIndexLiftFin hMN i = j <;> simp [hij]
  map_smul' := by
    intro a c
    ext j
    simp [realFourierCoefficientsLift, Finset.mul_sum, mul_ite]

/-- The continuous zero-extension between nested Fourier coefficient spaces. -/
noncomputable def classicalGalerkinLiftCLM {M N : ℕ} (hMN : M ≤ N) :
    Coefficients (RealFourierDimension M) →L[ℝ]
      Coefficients (RealFourierDimension N) :=
  (classicalGalerkinLiftLinearMap hMN).toContinuousLinearMap

@[simp]
theorem classicalGalerkinLiftCLM_apply {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    classicalGalerkinLiftCLM hMN c = realFourierCoefficientsLift hMN c := rfl

/-- Projecting a finite synthesis from a smaller cutoff into a larger one recovers its
zero-extended coefficient vector. -/
theorem classicalGalerkin_projection_lift_expansion {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (modeExpansion (RealFourierDimension M) (realFourierModeFin M) c) =
        realFourierCoefficientsLift hMN c := by
  have hfun : modeExpansion (RealFourierDimension M) (realFourierModeFin M) c =
      modeExpansion (RealFourierDimension N) (realFourierModeFin N)
        (realFourierCoefficientsLift hMN c) := by
    funext x
    exact (scalarExpansion_lift hMN c x).symm
  rw [hfun]
  exact realFourierModeFin_projectionCoefficients_expansion N
    (realFourierCoefficientsLift hMN c)

/-- The ambient finite Fourier synthesis is unchanged when its coefficients are zero-extended. -/
theorem classicalGalerkinAmbientExpansion_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    realFourierModeAmbientExpansion N (realFourierCoefficientsLift hMN c) =
      realFourierModeAmbientExpansion M c := by
  funext x
  classical
  change (∑ j : Fin (RealFourierDimension N),
      (∑ i : Fin (RealFourierDimension M),
        if realFourierIndexLiftFin hMN i = j then c i else 0) *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x) =
    ∑ i : Fin (RealFourierDimension M),
      c i * realFourierModeAmbient M ((realFourierIndexEquivFin M).symm i) x
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ j : Fin (RealFourierDimension N),
        (if realFourierIndexLiftFin hMN i = j then c i else 0) *
          realFourierModeAmbient N ((realFourierIndexEquivFin N).symm j) x =
      c i * realFourierModeAmbient N
        ((realFourierIndexEquivFin N).symm (realFourierIndexLiftFin hMN i)) x := by
      rw [Finset.sum_eq_single (realFourierIndexLiftFin hMN i)]
      · simp
      · intro j hj hne
        have hne' : realFourierIndexLiftFin hMN i ≠ j := Ne.symm hne
        simp [hne']
      · intro hj
        exact (hj (Finset.mem_univ _)).elim
    _ = c i * realFourierModeAmbient M ((realFourierIndexEquivFin M).symm i) x := by
      congr 1
      simpa [realFourierIndexLiftFin] using congrFun (realFourierModeAmbient_lift hMN
        ((realFourierIndexEquivFin M).symm i)) x

/-- The Laplacian preserves every finite Fourier synthesis range, so its Galerkin coefficient
vector is compatible with zero extension to a larger cutoff. -/
theorem classicalGalerkin_laplacian_projection_lift {M N : ℕ} (hMN : M ≤ N)
    (c : Coefficients (RealFourierDimension M)) :
    modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceLap (realFourierModeAmbientExpansion M c) x)) =
      realFourierCoefficientsLift hMN
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => AVenhance.spaceLap (realFourierModeAmbientExpansion M c) x))) := by
  let d₀ := realFourierWordDerivativeMap M [0, 0] c
  let d₁ := realFourierWordDerivativeMap M [1, 1] c
  let d := d₀ + d₁
  let u := realFourierModeAmbientExpansion M c
  have hlapWords : (fun x => AVenhance.spaceLap u x) =
      fun x => classicalWordDerivative [0, 0] u x +
        classicalWordDerivative [1, 1] u x := by
    funext x
    simp [u, AVenhance.spaceLap, classicalWordDerivative, Fin.sum_univ_two]
  have hword₀ : classicalWordDerivative [0, 0] u =
      realFourierModeAmbientExpansion M d₀ := by
    simpa [d₀] using classicalWordDerivative_realFourierModeAmbientExpansion M [0, 0] c
  have hword₁ : classicalWordDerivative [1, 1] u =
      realFourierModeAmbientExpansion M d₁ := by
    simpa [d₁] using classicalWordDerivative_realFourierModeAmbientExpansion M [1, 1] c
  have hexpAdd : realFourierModeAmbientExpansion M d₀ +
      realFourierModeAmbientExpansion M d₁ =
        realFourierModeAmbientExpansion M d := by
    funext x
    simp only [Pi.add_apply, realFourierModeAmbientExpansion, d, PiLp.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hlapExpansion : (fun x => AVenhance.spaceLap u x) =
      realFourierModeAmbientExpansion M d := by
    rw [hlapWords, hword₀, hword₁]
    funext x
    exact congrFun hexpAdd x
  have hlow : modeProjectionCoefficients (RealFourierDimension M)
      (realFourierModeFin M) (AVenhance.Infra.Torus.periodicToTorus
        (fun x => AVenhance.spaceLap u x)) = d := by
    rw [hlapExpansion, ← realFourierModeFin_expansion_eq_periodicToTorus M d]
    exact realFourierModeFin_projectionCoefficients_expansion M d
  have hhigh : modeProjectionCoefficients (RealFourierDimension N)
      (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus
        (fun x => AVenhance.spaceLap u x)) = realFourierCoefficientsLift hMN d := by
    rw [hlapExpansion, ← realFourierModeFin_expansion_eq_periodicToTorus M d]
    exact classicalGalerkin_projection_lift_expansion hMN d
  rw [hhigh, hlow]

/-- The coefficient tail between two nested real Fourier cutoffs. -/
def classicalGalerkinProjectionTail {M N : ℕ} (hMN : M ≤ N)
    (f : Vec 2 → ℝ) : Coefficients (RealFourierDimension N) :=
  modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus f) -
    realFourierCoefficientsLift hMN
      (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
        (AVenhance.Infra.Torus.periodicToTorus f))

theorem classicalGalerkinProjectionTail_add {M N : ℕ} (hMN : M ≤ N)
    {f g : Vec 2 → ℝ}
    (hf : MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2 (volume : Measure Torus))
    (hg : MemLp (AVenhance.Infra.Torus.periodicToTorus g) 2 (volume : Measure Torus)) :
    classicalGalerkinProjectionTail hMN (fun x => f x + g x) =
      classicalGalerkinProjectionTail hMN f + classicalGalerkinProjectionTail hMN g := by
  have htorus : AVenhance.Infra.Torus.periodicToTorus (fun x => f x + g x) =
      AVenhance.Infra.Torus.periodicToTorus f + AVenhance.Infra.Torus.periodicToTorus g := by
    funext x
    rfl
  rw [classicalGalerkinProjectionTail, htorus,
    realFourierModeProjectionCoefficients_add N hf hg,
    realFourierModeProjectionCoefficients_add M hf hg]
  rw [← classicalGalerkinLiftCLM_apply hMN
      (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
        (AVenhance.Infra.Torus.periodicToTorus f) +
       modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
        (AVenhance.Infra.Torus.periodicToTorus g)),
      map_add]
  simp [classicalGalerkinProjectionTail]
  abel

theorem classicalGalerkinProjectionTail_smul {M N : ℕ} (hMN : M ≤ N)
    (a : ℝ) {f : Vec 2 → ℝ}
    (hf : MemLp (AVenhance.Infra.Torus.periodicToTorus f) 2 (volume : Measure Torus)) :
    classicalGalerkinProjectionTail hMN (fun x => a * f x) =
      a • classicalGalerkinProjectionTail hMN f := by
  have htorus : AVenhance.Infra.Torus.periodicToTorus (fun x => a * f x) =
      a • AVenhance.Infra.Torus.periodicToTorus f := by
    funext x
    rfl
  rw [classicalGalerkinProjectionTail, htorus,
    realFourierModeProjectionCoefficients_smul N a hf,
    realFourierModeProjectionCoefficients_smul M a hf]
  rw [← classicalGalerkinLiftCLM_apply hMN
      (a • modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
        (AVenhance.Infra.Torus.periodicToTorus f)), map_smul]
  simp [classicalGalerkinProjectionTail, smul_sub]

theorem GalerkinCauchy.classicalCauchyTransport_contDiff (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  exact ((contDiff_pi.1 hb) j).mul
    ((hu.fderiv_right (by simp)).clm_apply contDiff_const)

theorem GalerkinCauchy.classicalCauchyTransport_periodic (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : AVenhance.IsZ2Periodic b)
    (hu : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (classicalTransport b u) := by
  intro k x
  simp only [classicalTransport, Homogenization.vecDot]
  apply Finset.sum_congr rfl
  intro j hj
  have hp : AVenhance.spaceGrad u (x + AVenhance.latticeShift k) j =
      AVenhance.spaceGrad u x j :=
    AVenhance.Infra.Classical.periodic_spaceGrad_component hu j k x
  rw [congrFun (hb k x) j, hp]

theorem GalerkinCauchy.classicalCauchySpaceLap_contDiff {u : Vec 2 → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap u) := by
  have hgrad (j : Fin 2) : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad u x j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2,
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j) x j)
  apply ContDiff.sum
  intro j hj
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad u y j) x
      (Homogenization.basisVec j))
  exact ((hgrad j).fderiv_right (by simp)).clm_apply contDiff_const

theorem GalerkinCauchy.classicalCauchySpaceLap_periodic {u : Vec 2 → ℝ}
    (hup : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (AVenhance.spaceLap u) := by
  intro k x
  change (∑ j : Fin 2,
      AVenhance.spaceGrad (fun y => AVenhance.spaceGrad u y j)
        (x + AVenhance.latticeShift k) j) = _
  apply Finset.sum_congr rfl
  intro j hj
  exact AVenhance.Infra.Classical.periodic_spaceGrad_component
    (AVenhance.Infra.Classical.periodic_spaceGrad_component hup j) j k x

/-- The concrete coefficient ODE right-hand side is the Fourier projection of the classical
generator plus the forcing. -/
theorem classicalGalerkinCoefficient_rhs_eq_projectedGenerator
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (N : ℕ)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (c : Coefficients (RealFourierDimension N)) :
    (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t c +
        (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (fun x =>
          F t x + (κ * AVenhance.spaceLap (realFourierModeAmbientExpansion N c) x -
            classicalTransport (AVenhance.streamVel φ t)
              (realFourierModeAmbientExpansion N c) x))) := by
  let b : Vec 2 → Vec 2 := AVenhance.streamVel φ t
  let u : Vec 2 → ℝ := realFourierModeAmbientExpansion N c
  have hb0 := (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).smooth
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hsection : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
      hb0.comp (contDiff_const.prodMk contDiff_id)
    simpa [b, Function.uncurry] using hsection
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    have hu0 : ContDiff ℝ ⊤ u := by
      simpa [u] using realFourierModeAmbientExpansion_contDiff N c
    exact hu0.of_le (by simp)
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa using (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (AVenhance.spaceLap u) :=
    GalerkinCauchy.classicalCauchySpaceLap_contDiff hu
  have hlapPer : AVenhance.IsZ2Periodic (AVenhance.spaceLap u) :=
    GalerkinCauchy.classicalCauchySpaceLap_periodic hup
  have hgenSmooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x) := by
    exact (contDiff_const.mul hlapSmooth).sub (GalerkinCauchy.classicalCauchyTransport_contDiff b
        u hb hu)
  have hgenPer : AVenhance.IsZ2Periodic
      (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x) := by
    intro k x
    have hlap := hlapPer k x
    have htransport := GalerkinCauchy.classicalCauchyTransport_periodic b u hbp hup k x
    change κ * AVenhance.spaceLap u (x + AVenhance.latticeShift k) -
      classicalTransport b u (x + AVenhance.latticeShift k) = _
    rw [hlap, htransport]
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht.1
  have hFtPer : AVenhance.IsZ2Periodic (F t) := hFper t ht.1
  have hmemF := memLp_periodicToTorus_real hFslice.continuous hFtPer
  have hmemGen := memLp_periodicToTorus_real hgenSmooth.continuous hgenPer
  have htorusAdd : AVenhance.Infra.Torus.periodicToTorus (fun x =>
      F t x + (κ * AVenhance.spaceLap u x - classicalTransport b u x)) =
      AVenhance.Infra.Torus.periodicToTorus (F t) +
        AVenhance.Infra.Torus.periodicToTorus
          (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x) := by
    funext x
    rfl
  have hprojectionAdd := realFourierModeProjectionCoefficients_add N hmemF hmemGen
  have hcoefficient :
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t c =
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x)) := by
    change frozenWeakFormCoefficient (AVenhance.streamVel φ) κ
      (realFourierModeFin N) (realFourierModeGradFin N) t c = _
    exact frozenWeakFormCoefficient_eq_projectedGenerator N
      (AVenhance.streamVel φ) κ t ht c (by simpa [b] using hb.continuous)
  have hforcing :
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (F t)) := by
    simp [classicalForcedGalerkinData, ForcedGalerkinData.ofWeak,
      classicalForcingCoefficients, max_eq_left ht.1]
  rw [hcoefficient, hforcing]
  rw [htorusAdd]
  calc
    _ = modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (F t)) +
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => κ * AVenhance.spaceLap u x - classicalTransport b u x)) := by abel
    _ = _ := hprojectionAdd.symm

/-- The nested-cutoff defect in the Galerkin vector fields is exactly the projected Fourier tail
of the forcing minus transport. The diffusion part cancels because the Laplacian preserves the
lower Fourier span. -/
theorem classicalGalerkinNestedResidual_identity
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (M N : ℕ) (hMN : M ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (c : Coefficients (RealFourierDimension M)) :
    (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
        (realFourierCoefficientsLift hMN c) +
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t -
      realFourierCoefficientsLift hMN
        ((classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).weak.coefficient t c +
          (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).forcing t) =
    classicalGalerkinProjectionTail hMN
      (fun x => F t x - classicalTransport (AVenhance.streamVel φ t)
        (realFourierModeAmbientExpansion M c) x) := by
  let u := realFourierModeAmbientExpansion M c
  let b : Vec 2 → Vec 2 := AVenhance.streamVel φ t
  let lap : Vec 2 → ℝ := fun x => AVenhance.spaceLap u x
  let tr : Vec 2 → ℝ := classicalTransport b u
  let src : Vec 2 → ℝ := fun x => F t x - tr x
  let lapMem := memLp_periodicToTorus_real
    (GalerkinCauchy.classicalCauchySpaceLap_contDiff (by
      have hu0 : ContDiff ℝ ⊤ u := by
        simpa [u] using realFourierModeAmbientExpansion_contDiff M c
      exact hu0.of_le (by simp))).continuous
    (GalerkinCauchy.classicalCauchySpaceLap_periodic (by
      simpa [u] using realFourierModeAmbientExpansion_periodic M c))
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht.1
  have hFp : AVenhance.IsZ2Periodic (F t) := hFper t ht.1
  have hb0 := (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).smooth
  have hsection : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
    hb0.comp (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    simpa [b, Function.uncurry] using hsection
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa [b] using
      (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff M c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic M c
  have htrSmooth : ContDiff ℝ (⊤ : ℕ∞) tr := by
    simpa [tr, b] using GalerkinCauchy.classicalCauchyTransport_contDiff b u hb hu
  have htrPer : AVenhance.IsZ2Periodic tr := by
    simpa [tr, b] using GalerkinCauchy.classicalCauchyTransport_periodic b u hbp hup
  have hsrcSmooth : ContDiff ℝ (⊤ : ℕ∞) src := by
    exact hFslice.sub htrSmooth
  have hsrcPer : AVenhance.IsZ2Periodic src := by
    intro k x
    simp only [src]
    rw [hFp k x, htrPer k x]
  have hsrcMem := memLp_periodicToTorus_real hsrcSmooth.continuous hsrcPer
  have hLapSmooth : ContDiff ℝ (⊤ : ℕ∞) lap := by
    simpa [lap, u] using GalerkinCauchy.classicalCauchySpaceLap_contDiff hu
  have hLapPer : AVenhance.IsZ2Periodic lap := by
    simpa [lap, u] using GalerkinCauchy.classicalCauchySpaceLap_periodic hup
  have hscaledLapMem := memLp_periodicToTorus_real
    ((contDiff_const.mul hLapSmooth).continuous) (by
      intro k x
      change κ * lap (x + AVenhance.latticeShift k) = κ * lap x
      rw [hLapPer k x])
  have htailLap : classicalGalerkinProjectionTail hMN (fun x => κ * lap x) = 0 := by
    rw [classicalGalerkinProjectionTail_smul hMN κ lapMem]
    have hzero : classicalGalerkinProjectionTail hMN lap = 0 := by
      rw [classicalGalerkinProjectionTail]
      have hcoeff := classicalGalerkin_laplacian_projection_lift hMN c
      have hcoeff' : modeProjectionCoefficients (RealFourierDimension N)
          (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus lap) =
          realFourierCoefficientsLift hMN
            (modeProjectionCoefficients (RealFourierDimension M)
              (realFourierModeFin M)
              (AVenhance.Infra.Torus.periodicToTorus lap)) := by
        simpa [lap, u] using hcoeff
      rw [hcoeff']
      exact sub_self _
    rw [hzero]
    simp
  have hsourceSplit : (fun x => F t x + (κ * lap x - tr x)) =
      fun x => src x + κ * lap x := by
    funext x
    change F t x + (κ * AVenhance.spaceLap u x - classicalTransport b u x) =
      (F t x - classicalTransport b u x) + κ * AVenhance.spaceLap u x
    ring
  have htailSplit : classicalGalerkinProjectionTail hMN
      (fun x => F t x + (κ * lap x - tr x)) =
        classicalGalerkinProjectionTail hMN src := by
    rw [hsourceSplit, classicalGalerkinProjectionTail_add hMN hsrcMem hscaledLapMem,
      htailLap]
    simp
  have hhigh := classicalGalerkinCoefficient_rhs_eq_projectedGenerator
    φ hφ κ hκ F hF hFper θ₀ hθ₀ N t ht
      (realFourierCoefficientsLift hMN c)
  have hlow := classicalGalerkinCoefficient_rhs_eq_projectedGenerator
    φ hφ κ hκ F hF hFper θ₀ hθ₀ M t ht c
  have huLift : realFourierModeAmbientExpansion N
      (realFourierCoefficientsLift hMN c) = u := by
    simpa [u] using classicalGalerkinAmbientExpansion_lift hMN c
  have hhigh' :
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
          (realFourierCoefficientsLift hMN c) +
        (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t =
        modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => F t x + (κ * lap x - tr x))) := by
    have hhighLift := hhigh
    rw [huLift] at hhighLift
    simpa [b, u, lap, tr] using hhighLift
  have hlow' :
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).weak.coefficient t c +
        (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).forcing t =
        modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus
            (fun x => F t x + (κ * lap x - tr x))) := by
    simpa [b, u, lap, tr] using hlow
  have hdifference :
      (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).weak.coefficient t
          (realFourierCoefficientsLift hMN c) +
        (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N).forcing t -
        realFourierCoefficientsLift hMN
          ((classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).weak.coefficient t c +
            (classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M).forcing t) =
      classicalGalerkinProjectionTail hMN
        (fun x => F t x + (κ * lap x - tr x)) := by
    rw [classicalGalerkinProjectionTail]
    rw [hhigh', hlow']
  rw [hdifference, htailSplit]

/-- The nested real Fourier projection tail of a difference is controlled by the two separate
smooth projection tails. -/
theorem classicalSmoothDifferenceProjection_tail_norm_le
    (M N : ℕ) (hMN : M ≤ N) (f g : Vec 2 → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : AVenhance.IsZ2Periodic f) (hgp : AVenhance.IsZ2Periodic g)
    (Ef Eg : ℝ) (hEf : AVenhance.gradNormSq (AVenhance.spaceGrad f) ≤ Ef)
    (hEg : AVenhance.gradNormSq (AVenhance.spaceGrad g) ≤ Eg) :
    ‖modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus (fun x => f x - g x)) -
      realFourierCoefficientsLift hMN
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus (fun x => f x - g x)) )‖ ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * Ef) +
        Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * Eg) := by
  let hmemF := memLp_periodicToTorus_real hf.continuous hfp
  let hmemG := memLp_periodicToTorus_real hg.continuous hgp
  have hsubN := realFourierModeProjectionCoefficients_sub N hmemF hmemG
  have hsubM := realFourierModeProjectionCoefficients_sub M hmemF hmemG
  have hliftSub : realFourierCoefficientsLift hMN
      (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus f) -
        modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus g)) =
      realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus f)) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus g)) := by
    simpa only [classicalGalerkinLiftCLM_apply] using
      (map_sub (classicalGalerkinLiftCLM hMN)
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus f))
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus g)))
  have hexact :
      modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus (fun x => f x - g x)) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus (fun x => f x - g x))) =
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus f))) -
      (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus g) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus g))) := by
    have htorusSub : AVenhance.Infra.Torus.periodicToTorus
        (fun x => f x - g x) =
        AVenhance.Infra.Torus.periodicToTorus f -
          AVenhance.Infra.Torus.periodicToTorus g := by
      funext x
      rfl
    rw [htorusSub, hsubN, hsubM, hliftSub]
    abel
  have htailF := classicalSmoothProjection_tail_norm_le M N hMN f hf hfp
  have htailG := classicalSmoothProjection_tail_norm_le M N hMN g hg hgp
  let scale : ℝ := (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have htailF' : ‖modeProjectionCoefficients (RealFourierDimension N)
      (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus f) -
      realFourierCoefficientsLift hMN (modeProjectionCoefficients
        (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus f))‖ ≤ Real.sqrt (scale * Ef) := by
    calc
      _ ≤ Real.sqrt (scale * AVenhance.gradNormSq (AVenhance.spaceGrad f)) := by
        simpa [scale] using htailF
      _ ≤ Real.sqrt (scale * Ef) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hEf hscale)
  have htailG' : ‖modeProjectionCoefficients (RealFourierDimension N)
      (realFourierModeFin N) (AVenhance.Infra.Torus.periodicToTorus g) -
      realFourierCoefficientsLift hMN (modeProjectionCoefficients
        (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus g))‖ ≤ Real.sqrt (scale * Eg) := by
    calc
      _ ≤ Real.sqrt (scale * AVenhance.gradNormSq (AVenhance.spaceGrad g)) := by
        simpa [scale] using htailG
      _ ≤ Real.sqrt (scale * Eg) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hEg hscale)
  calc
    _ = ‖(modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus f) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus f)) -
       (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
          (AVenhance.Infra.Torus.periodicToTorus g) -
        realFourierCoefficientsLift hMN
          (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
            (AVenhance.Infra.Torus.periodicToTorus g))))‖ := by rw [hexact]
    _ ≤ _ := by
      simpa [scale] using (norm_sub_le _ _).trans (add_le_add htailF' htailG')

/-- The smooth forcing has a cutoff-independent Dirichlet-energy bound on the time interval. -/
theorem classicalForcing_gradient_energy_uniform_bound
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t)) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t, t ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq (AVenhance.spaceGrad (F t)) ≤ E := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_classicalForcing_allWordDerivative_uniform_bound F hF hFper 1
  refine ⟨2 * B ^ 2, by positivity, ?_⟩
  intro t ht
  have hFt := AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht.1
  have hFone : ContDiff ℝ 1 (F t) := hFt.of_le (by simp)
  have hprojection : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad (F t) x i))‖ ≤ B := by
    intro i K
    have hgrad : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => AVenhance.spaceGrad (F t) x i) :=
      classicalWordDerivative_contDiff [i] (F t) hFt
    apply realFourierProjectionCoefficients_norm_le_uniform K
      (fun x => AVenhance.spaceGrad (F t) x i)
      hgrad.continuous
      (AVenhance.Infra.Classical.periodic_spaceGrad_component (hFper t ht.1) i)
      hB
    intro x
    have h := hbound [i] (by simp) t ht x
    simpa only [classicalWordDerivative, Real.norm_eq_abs] using h
  exact classicalSmoothSource_gradient_energy_le_of_projection_bounds
    (F t) hFone (hFper t ht.1) hB hprojection

/-- The finite Fourier coefficient path viewed in scalar torus `L²`. -/
noncomputable def classicalGalerkinScalarPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (N : ℕ) :
    C(Icc (0 : ℝ) 1, ScalarTorusL2) :=
  ⟨fun t => realFourierScalarMap N
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t),
    (realFourierScalarMap N).continuous.comp
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N).continuous⟩

@[simp]
theorem classicalGalerkinScalarPath_apply
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (N : ℕ)
    (t : Icc (0 : ℝ) 1) :
    classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N t =
      realFourierScalarMap N
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) := rfl

/-- The residual forcing in the nested-cutoff difference equation is uniformly small in its
coefficient norm, with its size controlled by the smooth forcing and transport Dirichlet energies.
-/
theorem classicalGalerkinNestedResidual_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (E_F E_T : ℝ)
    (hFenergy : ∀ t, t ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq (AVenhance.spaceGrad (F t)) ≤ E_F)
    (hTenergy : ∀ K s, s ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq
        (AVenhance.spaceGrad
          (classicalTransport (AVenhance.streamVel φ s)
            (realFourierModeAmbientExpansion K
              (AVenhance.Infra.ODE.extendCurve (by norm_num)
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ K) s)))) ≤ E_T)
    (M N : ℕ) (hMN : M ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖classicalGalerkinProjectionTail hMN
      (fun x => F t x - classicalTransport (AVenhance.streamVel φ t)
        (realFourierModeAmbientExpansion M
          (AVenhance.Infra.ODE.extendCurve (by norm_num)
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ M) t)) x)‖ ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E_F) +
        Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E_T) := by
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num)
    (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ M) t
  let u := realFourierModeAmbientExpansion M c
  let b : Vec 2 → Vec 2 := fun x => AVenhance.streamVel φ t x
  let g : Vec 2 → ℝ := classicalTransport b u
  have hFslice : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF ht.1
  have hFone : ContDiff ℝ 1 (F t) := hFslice.of_le (by simp)
  have hFp : AVenhance.IsZ2Periodic (F t) := hFper t ht.1
  have hb0 := (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).smooth
  have hsection : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
    hb0.comp (contDiff_const.prodMk contDiff_id)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    simpa [b, Function.uncurry] using hsection
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa [b] using
      (AVenhance.Infra.Classical.streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff M c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic M c
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    simpa [g, b] using GalerkinCauchy.classicalCauchyTransport_contDiff b u hb hu
  have hgp : AVenhance.IsZ2Periodic g := by
    simpa [g, b] using GalerkinCauchy.classicalCauchyTransport_periodic b u hbp hup
  have hEg : AVenhance.gradNormSq (AVenhance.spaceGrad g) ≤ E_T := by
    simpa [g, b, u, c] using hTenergy M t ht
  have htail := classicalSmoothDifferenceProjection_tail_norm_le M N hMN
    (F t) g hFone (hg.of_le (by simp)) hFp hgp E_F E_T
    (hFenergy t ht) hEg
  simpa [g, classicalGalerkinProjectionTail, u, b, c] using htail

private theorem galerkin_nested_difference_residual :
  ∀ (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) (Ici 0 ×ˢ univ)),
    (∀ (t : ℝ), 0 ≤ t → IsZ2Periodic (F t)) →
      ∀ (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (E_F E_T : ℝ),
        (∀ t ∈ Icc 0 1, gradNormSq (spaceGrad (F t)) ≤ E_F) →
          (∀ (K : ℕ),
              ∀ s ∈ Icc 0 1,
                gradNormSq
                    (spaceGrad
                      (classicalTransport (streamVel φ s)
                        (realFourierModeAmbientExpansion K
                          (ODE.extendCurve (by norm_num)
                            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ K) s)))) ≤
                  E_T) →
            ∀ (M N : ℕ) (hMN : M ≤ N),
              let DN := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N;
              let DM := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M;
              let uM := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ M;
              let yM := AVenhance.Infra.ODE.extendCurve (by norm_num) uM;
              let L : Coefficients (RealFourierDimension M) →L[ℝ]
                  Coefficients (RealFourierDimension N) := classicalGalerkinLiftCLM hMN;
              let uML : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)) :=
                ⟨fun q => L (uM q), L.continuous.comp uM.continuous⟩;
              ∀ (hextLift : ∀ (s : ℝ), ODE.extendCurve (by norm_num) uML s = L (yM s)),
                let g : ℝ → Coefficients (RealFourierDimension N) := fun s =>
                  L (DM.forcing s) + L (DM.weak.coefficient s (yM s)) -
                    DN.weak.coefficient s (L (yM s));
                let Ddiff : ForcedGalerkinData (Coefficients (RealFourierDimension N))
                    SpatialGradientL2 :=
                  { weak := DN.weak
                    initial := DN.initial - L DM.initial
                    forcing := DN.forcing - g
                    forcing_integrable := DN.forcing_integrable.sub (by
                      have hRhsM := DM.ode.rhs_intervalIntegrable uM
                      change IntervalIntegrable
                        (AVenhance.Infra.ODE.linearRhs DM.weak.coefficient DM.forcing yM) volume 0
                            1 at hRhsM
                      have hAym : IntervalIntegrable
                          (fun s => DM.weak.coefficient s (yM s)) volume 0 1 := by
                        have h := hRhsM.sub DM.forcing_integrable
                        simpa [AVenhance.Infra.ODE.linearRhs] using h
                      have hLforce : IntervalIntegrable (fun s => L (DM.forcing s)) volume 0 1 := by
                        rw [intervalIntegrable_iff]
                        exact L.integrable_comp (intervalIntegrable_iff.mp DM.forcing_integrable)
                      have hLAym : IntervalIntegrable
                          (fun s => L (DM.weak.coefficient s (yM s))) volume 0 1 := by
                        rw [intervalIntegrable_iff]
                        exact L.integrable_comp (intervalIntegrable_iff.mp hAym)
                      have hRhsLift := DN.ode.rhs_intervalIntegrable uML
                      change IntervalIntegrable
                        (AVenhance.Infra.ODE.linearRhs DN.weak.coefficient DN.forcing
                          (AVenhance.Infra.ODE.extendCurve (by norm_num) uML)) volume 0 1
                              at hRhsLift
                      have hAymLift : IntervalIntegrable
                          (fun s => DN.weak.coefficient s (L (yM s))) volume 0 1 := by
                        have h := hRhsLift.sub DN.forcing_integrable
                        simpa [AVenhance.Infra.ODE.linearRhs, hextLift] using h
                      have hsum := (hLforce.add hLAym).sub hAymLift
                      simpa [g] using hsum) };
                let scale : ℝ := (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹;
                let ε : ℝ := Real.sqrt (scale * E_F) + Real.sqrt (scale * E_T);
                ∀ s ∈ Icc 0 1, ‖Ddiff.forcing s‖ ≤ ε
    := by
  intro φ hφ κ hκ F hF hFper θ₀ hθ₀ E_F E_T hFenergy hTenergy M N hMN DN DM uM yM L uML hextLift g
      Ddiff scale ε s hs
  have htail := classicalGalerkinNestedResidual_norm_le
    φ hφ κ hκ F hF hFper θ₀ hθ₀ E_F E_T hFenergy hTenergy M N hMN s hs
  have hforceEq : Ddiff.forcing s = classicalGalerkinProjectionTail hMN
      (fun x => F s x - classicalTransport (AVenhance.streamVel φ s)
        (realFourierModeAmbientExpansion M (yM s)) x) := by
    have hidentity := classicalGalerkinNestedResidual_identity
      φ hφ κ hκ F hF hFper θ₀ hθ₀ M N hMN s hs (yM s)
    change DN.forcing s -
      (L (DM.forcing s) + L (DM.weak.coefficient s (yM s)) -
        DN.weak.coefficient s (L (yM s))) = _
    have hsum : L (DM.forcing s) + L (DM.weak.coefficient s (yM s)) =
        L (DM.weak.coefficient s (yM s) + DM.forcing s) := by
      rw [map_add]
      abel
    have hforceAsTail : DN.forcing s -
        (L (DM.forcing s) + L (DM.weak.coefficient s (yM s)) -
          DN.weak.coefficient s (L (yM s))) =
        (DN.weak.coefficient s (L (yM s)) + DN.forcing s) -
          L (DM.weak.coefficient s (yM s) + DM.forcing s) := by
      rw [hsum]
      abel
    rw [hforceAsTail]
    have hidentity' := hidentity
    simpa [DN, DM, L, classicalGalerkinLiftCLM_apply] using hidentity'
  rw [hforceEq]
  simpa [ε, scale] using htail

private theorem galerkin_nested_difference_right_hand_side :
  ∀ (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ) (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ) (hF
    : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) (Ici 0 ×ˢ univ)) (θ₀ : Vec 2 → ℝ) (hθ₀ :
    ContDiff ℝ (⊤ : ℕ∞) θ₀) (M N : ℕ) (hMN : M ≤ N),
  let DN := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N;
  let DM := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M;
  let uM := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ M;
  let yM := AVenhance.Infra.ODE.extendCurve (by norm_num) uM;
  let L : Coefficients (RealFourierDimension M) →L[ℝ] Coefficients (RealFourierDimension N) :=
    classicalGalerkinLiftCLM hMN;
  let uML : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)) := ⟨fun q => L (uM q),
    L.continuous.comp uM.continuous⟩;
  (∀ (s : ℝ), ODE.extendCurve (by norm_num) uML s = L (yM s)) →
  let g : ℝ → Coefficients (RealFourierDimension N) := fun s => L (DM.forcing s) + L
    (DM.weak.coefficient s (yM s)) - DN.weak.coefficient s (L (yM s));
  IntervalIntegrable (ODE.linearRhs DM.weak.coefficient DM.forcing yM) volume 0 1 →
    IntervalIntegrable (ODE.linearRhs DN.weak.coefficient g fun s => L (yM s)) volume 0 1
    := by
  intro φ hφ κ hκ F hF θ₀ hθ₀ M N hMN DN DM uM yM L uML hextLift g hMrhs'
  have hAymLift : IntervalIntegrable
      (fun s => DN.weak.coefficient s (L (yM s))) volume 0 1 := by
    have hRhsLift := DN.ode.rhs_intervalIntegrable uML
    simpa [DN, ForcedGalerkinData.ode, AVenhance.Infra.ODE.LinearODEData.rhs,
      AVenhance.Infra.ODE.linearRhs, hextLift] using
      (hRhsLift.sub DN.forcing_integrable)
  have hAym : IntervalIntegrable
      (fun s => DM.weak.coefficient s (yM s)) volume 0 1 := by
    have h := hMrhs'.sub DM.forcing_integrable
    simpa [AVenhance.Infra.ODE.linearRhs] using h
  have hLforce : IntervalIntegrable (fun s => L (DM.forcing s)) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact L.integrable_comp (intervalIntegrable_iff.mp DM.forcing_integrable)
  have hLAym : IntervalIntegrable
      (fun s => L (DM.weak.coefficient s (yM s))) volume 0 1 := by
    rw [intervalIntegrable_iff]
    exact L.integrable_comp (intervalIntegrable_iff.mp hAym)
  have hG : IntervalIntegrable g volume 0 1 := by
    have h := (hLforce.add hLAym).sub hAymLift
    simpa [g] using h
  have hsum := hAymLift.add hG
  change IntervalIntegrable
    (fun s => DN.weak.coefficient s (L (yM s)) + g s) volume 0 1
  exact hsum

/-- The lifted difference of two nested classical Galerkin paths obeys the upper-cutoff energy
estimate, with forcing given by the residual Fourier tail. -/
theorem classicalGalerkinScalarPath_nested_difference_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (E_F E_T : ℝ)
    (hFenergy : ∀ t, t ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq (AVenhance.spaceGrad (F t)) ≤ E_F)
    (hTenergy : ∀ K s, s ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq
        (AVenhance.spaceGrad
          (classicalTransport (AVenhance.streamVel φ s)
            (realFourierModeAmbientExpansion K
              (AVenhance.Infra.ODE.extendCurve (by norm_num)
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ K) s)))) ≤ E_T)
    (M N : ℕ) (hMN : M ≤ N) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N) ⟨t, ht⟩ -
      (classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ M) ⟨t, ht⟩‖ ≤
      Real.sqrt (((Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
          AVenhance.gradNormSq (AVenhance.spaceGrad θ₀))) ^ 2 +
        (Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E_F) +
          Real.sqrt ((4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E_T)) ^ 2) *
        Real.exp ((positiveCutoffDriftConstant (AVenhance.streamVel φ)
          (classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀).drift_bounded ^ 2 / κ + 1))) := by
  let DN := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ N
  let DM := classicalForcedGalerkinData φ hφ κ hκ F hF θ₀ hθ₀ M
  let uN := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
  let uM := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ M
  let yN := AVenhance.Infra.ODE.extendCurve (by norm_num) uN
  let yM := AVenhance.Infra.ODE.extendCurve (by norm_num) uM
  let L : Coefficients (RealFourierDimension M) →L[ℝ]
      Coefficients (RealFourierDimension N) := classicalGalerkinLiftCLM hMN
  let uML : C(Icc (0 : ℝ) 1, Coefficients (RealFourierDimension N)) :=
    ⟨fun q => L (uM q), L.continuous.comp uM.continuous⟩
  have hextLift (s : ℝ) :
      AVenhance.Infra.ODE.extendCurve (by norm_num) uML s = L (yM s) := by
    rfl
  let v := uN - uML
  let g : ℝ → Coefficients (RealFourierDimension N) := fun s =>
    L (DM.forcing s) + L (DM.weak.coefficient s (yM s)) -
      DN.weak.coefficient s (L (yM s))
  let Ddiff : ForcedGalerkinData (Coefficients (RealFourierDimension N)) SpatialGradientL2 :=
    { weak := DN.weak
      initial := DN.initial - L DM.initial
      forcing := DN.forcing - g
      forcing_integrable := DN.forcing_integrable.sub (by
        have hRhsM := DM.ode.rhs_intervalIntegrable uM
        change IntervalIntegrable
          (AVenhance.Infra.ODE.linearRhs DM.weak.coefficient DM.forcing yM) volume 0 1 at hRhsM
        have hAym : IntervalIntegrable
            (fun s => DM.weak.coefficient s (yM s)) volume 0 1 := by
          have h := hRhsM.sub DM.forcing_integrable
          simpa [AVenhance.Infra.ODE.linearRhs] using h
        have hLforce : IntervalIntegrable (fun s => L (DM.forcing s)) volume 0 1 := by
          rw [intervalIntegrable_iff]
          exact L.integrable_comp (intervalIntegrable_iff.mp DM.forcing_integrable)
        have hLAym : IntervalIntegrable
            (fun s => L (DM.weak.coefficient s (yM s))) volume 0 1 := by
          rw [intervalIntegrable_iff]
          exact L.integrable_comp (intervalIntegrable_iff.mp hAym)
        have hRhsLift := DN.ode.rhs_intervalIntegrable uML
        change IntervalIntegrable
          (AVenhance.Infra.ODE.linearRhs DN.weak.coefficient DN.forcing
            (AVenhance.Infra.ODE.extendCurve (by norm_num) uML)) volume 0 1 at hRhsLift
        have hAymLift : IntervalIntegrable
            (fun s => DN.weak.coefficient s (L (yM s))) volume 0 1 := by
          have h := hRhsLift.sub DN.forcing_integrable
          simpa [AVenhance.Infra.ODE.linearRhs, hextLift] using h
        have hsum := (hLforce.add hLAym).sub hAymLift
        simpa [g] using hsum) }
  have huNsol : DN.ode.IsSolution uN := by
    simpa [DN, uN] using classicalGalerkinCoefficientPath_isSolution
      φ hφ κ hκ F hF θ₀ hθ₀ N
  have huMsol : DM.ode.IsSolution uM := by
    simpa [DM, uM] using classicalGalerkinCoefficientPath_isSolution
      φ hφ κ hκ F hF θ₀ hθ₀ M
  have hMIntegral := huMsol.integralSolution DM.ode
  have hMrhs := DM.ode.rhs_intervalIntegrable uM
  have hMIntegral' : AVenhance.Infra.ODE.IsLinearIntegralSolution
      DM.weak.coefficient DM.forcing DM.initial 0 1 yM := by
    simpa [DM, ForcedGalerkinData.ode,
      AVenhance.Infra.ODE.linearRhs] using hMIntegral
  have hMrhs' : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs DM.weak.coefficient DM.forcing yM) volume 0 1 := by
    change IntervalIntegrable (DM.ode.rhs uM) volume 0 1
    exact hMrhs
  have hMappedIntegral : AVenhance.Infra.ODE.IsLinearIntegralSolution
      DN.weak.coefficient g (L DM.initial) 0 1 (fun s => L (yM s)) :=
    LinearIntegralSolution.continuousLinearMap_transform_between
      (A := DM.weak.coefficient) (B := DN.weak.coefficient)
      (f := DM.forcing) (y := yM) (y₀ := DM.initial)
      (a := 0) (b := 1) (show (0 : ℝ) ≤ 1 by norm_num)
      hMIntegral' hMrhs' L
  have hNIntegral := huNsol.integralSolution DN.ode
  have hNrhs := DN.ode.rhs_intervalIntegrable uN
  have hMappedRhs : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs DN.weak.coefficient g
        (fun s => L (yM s))) volume 0 1 := by
    apply galerkin_nested_difference_right_hand_side
    all_goals assumption
  have hDiffIntegral := LinearIntegralSolution.sub
    (show (0 : ℝ) ≤ 1 by norm_num) hNIntegral hMappedIntegral hNrhs hMappedRhs
  have hextDiff : AVenhance.Infra.ODE.extendCurve (by norm_num) v =
      fun s => yN s - L (yM s) := by
    funext s
    rfl
  have hDiffIntegral' := hextDiff ▸ hDiffIntegral
  have hDdiffSolution : Ddiff.ode.IsSolution v := by
    apply (Ddiff.ode.isSolution_iff_integralSolution v).2
    have hDiffIntegral'' : AVenhance.Infra.ODE.IsLinearIntegralSolution
        DN.weak.coefficient (fun s => DN.forcing s - g s)
        (DN.initial - L DM.initial) 0 1
        (AVenhance.Infra.ODE.extendCurve (by norm_num) v) := by
      change AVenhance.Infra.ODE.IsLinearIntegralSolution DN.weak.coefficient
        (fun s => DN.forcing s - g s) (DN.initial - L DM.initial) 0 1
        (AVenhance.Infra.ODE.extendCurve (by norm_num) v) at hDiffIntegral'
      exact hDiffIntegral'
    change AVenhance.Infra.ODE.IsLinearIntegralSolution
      Ddiff.weak.coefficient Ddiff.forcing Ddiff.initial 0 1
      (AVenhance.Infra.ODE.extendCurve (by norm_num) v)
    exact hDiffIntegral''
  let scale : ℝ := (4 * Real.pi ^ 2 * ((M + 1 : ℕ) : ℝ) ^ 2)⁻¹
  let ε : ℝ := Real.sqrt (scale * E_F) + Real.sqrt (scale * E_T)
  let δ : ℝ := Real.sqrt (scale * AVenhance.gradNormSq (AVenhance.spaceGrad θ₀))
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hε : 0 ≤ ε := by dsimp [ε]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hResidual (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
      ‖Ddiff.forcing s‖ ≤ ε := by
    apply galerkin_nested_difference_residual
    all_goals assumption
  have hDinitial : Ddiff.initial = classicalGalerkinProjectionTail hMN θ₀ := by
    change (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus θ₀) -
      realFourierCoefficientsLift hMN
        (modeProjectionCoefficients (RealFourierDimension M) (realFourierModeFin M)
          (AVenhance.Infra.Torus.periodicToTorus θ₀))) = _
    rfl
  have hθ₀one : ContDiff ℝ 1 θ₀ := hθ₀.of_le (by simp)
  have hinitialTail := classicalSmoothProjection_tail_norm_le M N hMN θ₀ hθ₀one hθ₀per
  have hDinitialBound : ‖Ddiff.initial‖ ≤ δ := by
    rw [hDinitial]
    simpa [δ, scale, classicalGalerkinProjectionTail] using hinitialTail
  have henergy := Ddiff.uniformEnergyEstimateOfLinearGrowth v hDdiffSolution
    (A := 0) (by norm_num) hε (by
      intro s hs
      simpa using hResidual s hs)
  let P := classicalFrozenDriftProblem φ hφ κ hκ θ₀ hθ₀
  let H := positiveCutoffDriftConstant (AVenhance.streamVel φ) P.drift_bounded
  have hH : 0 ≤ H :=
    positiveCutoffDriftForm_bound N (AVenhance.streamVel φ)
      P.drift_measurable P.drift_bounded |>.1
  have hdrift : Ddiff.weak.driftBound = H := by
    change (P.galerkinData N).driftBound = H
    rfl
  have hdiffusivity : Ddiff.weak.diffusivity = κ := rfl
  have hrate : max Ddiff.weak.driftBound 0 ^ 2 / Ddiff.weak.diffusivity + 2 * 0 + 1 =
      H ^ 2 / κ + 1 := by
    rw [hdrift, hdiffusivity, max_eq_left hH]
    ring
  have hrateNonneg : 0 ≤ H ^ 2 / κ + 1 := by positivity
  have htime : (H ^ 2 / κ + 1) * t ≤ H ^ 2 / κ + 1 :=
    mul_le_of_le_one_right hrateNonneg ht.2
  have hexp := Real.exp_le_exp.mpr htime
  have hfactor : 0 ≤ Real.exp ((H ^ 2 / κ + 1) * t) := (Real.exp_pos _).le
  have hinitSq : ‖Ddiff.initial‖ ^ 2 ≤ δ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hδ).2 hDinitialBound
  have hsum : ‖Ddiff.initial‖ ^ 2 + ε ^ 2 ≤ δ ^ 2 + ε ^ 2 := by linarith
  have hsq : ‖AVenhance.Infra.ODE.extendCurve (by norm_num) v t‖ ^ 2 ≤
      (δ ^ 2 + ε ^ 2) * Real.exp (H ^ 2 / κ + 1) := by
    have hfirst := (henergy t ht).1
    rw [hrate] at hfirst
    calc
      _ ≤ (‖Ddiff.initial‖ ^ 2 + ε ^ 2) *
          Real.exp ((H ^ 2 / κ + 1) * t) := hfirst
      _ ≤ (δ ^ 2 + ε ^ 2) * Real.exp (H ^ 2 / κ + 1) :=
        mul_le_mul hsum hexp (Real.exp_nonneg _) (by positivity)
  have hnorm : ‖AVenhance.Infra.ODE.extendCurve (by norm_num) v t‖ ≤
      Real.sqrt ((δ ^ 2 + ε ^ 2) * Real.exp (H ^ 2 / κ + 1)) := by
    calc
      _ = Real.sqrt (‖AVenhance.Infra.ODE.extendCurve (by norm_num) v t‖ ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      _ ≤ _ := Real.sqrt_le_sqrt hsq
  have hpath : AVenhance.Infra.ODE.extendCurve (by norm_num) v t =
      yN t - L (yM t) := congrFun hextDiff t
  have hmap : realFourierScalarMap N (L (yM t)) =
      realFourierScalarMap M (yM t) := by
    simpa [L] using realFourierScalarMap_lift hMN (yM t)
  have hnormScalar :
      ‖(classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N) ⟨t, ht⟩ -
        (classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ M) ⟨t, ht⟩‖ =
      ‖AVenhance.Infra.ODE.extendCurve (by norm_num) v t‖ := by
    rw [classicalGalerkinScalarPath_apply, classicalGalerkinScalarPath_apply]
    have hyN : yN t = uN ⟨t, ht⟩ :=
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) uN ht
    have hyM : yM t = uM ⟨t, ht⟩ :=
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) uM ht
    rw [← hyN, ← hyM]
    calc
      _ = ‖realFourierScalarMap N (yN t) -
          realFourierScalarMap N (L (yM t))‖ := by rw [← hmap]
      _ = ‖realFourierScalarMap N (yN t - L (yM t))‖ := by rw [map_sub]
      _ = ‖yN t - L (yM t)‖ := by rw [realFourierScalarMap_norm]
      _ = ‖AVenhance.Infra.ODE.extendCurve (by norm_num) v t‖ := by rw [← hpath]
  rw [hnormScalar]
  simpa [δ, ε, scale, H, P] using hnorm

end AVenhance.Infra.Classical

end
