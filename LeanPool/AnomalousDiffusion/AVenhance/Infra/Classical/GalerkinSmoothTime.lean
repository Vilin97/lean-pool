/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothFourier
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.ForcedGalerkin

/-! Joint time continuity of the smooth Fourier representatives. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothTimeMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothTimeMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothTimeProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

namespace ForcedGalerkinData

/-- The integral equation gives a classical time derivative in the open slab when the operator and
forcing are continuous on the slab. This version accommodates the zero extension in the measurable
ODE interface, whose coefficient need not be continuous outside `[0,1]`. -/
theorem hasDerivAt_on_Ioo_of_continuousOn {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (D : ForcedGalerkinData E G)
    (u : C(Icc (0 : ℝ) 1, E)) (hu : D.ode.IsSolution u)
    (hA : ContinuousOn D.weak.coefficient (Icc (0 : ℝ) 1))
    (hf : ContinuousOn D.forcing (Icc (0 : ℝ) 1))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (AVenhance.Infra.ODE.extendCurve (by norm_num) u)
      (D.weak.coefficient t (AVenhance.Infra.ODE.extendCurve (by norm_num) u t) +
        D.forcing t) t := by
  let y : ℝ → E := AVenhance.Infra.ODE.extendCurve (by norm_num) u
  let rhs : ℝ → E := AVenhance.Infra.ODE.linearRhs D.weak.coefficient D.forcing y
  have hycont : Continuous y := AVenhance.Infra.ODE.continuous_extendCurve (by norm_num) u
  have hIcc (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) : Icc (0 : ℝ) 1 ∈ 𝓝 s :=
    Filter.mem_of_superset (Ioo_mem_nhds hs.1 hs.2) Ioo_subset_Icc_self
  have heval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) := by fun_prop
  have hAat (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      ContinuousAt D.weak.coefficient s := hA.continuousAt (hIcc s hs)
  have hfat (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      ContinuousAt D.forcing s := hf.continuousAt (hIcc s hs)
  have hAyAt (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) 1) :
      ContinuousAt (fun r => D.weak.coefficient r (y r)) s := by
    exact heval.continuousAt.comp ((hAat s hs).prodMk hycont.continuousAt)
  have hRhsOn : ContinuousOn rhs (Ioo (0 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro s hs
    change ContinuousAt (fun r => D.weak.coefficient r (y r) + D.forcing r) s
    exact (hAyAt s hs).add (hfat s hs)
  have hrhsInt : IntervalIntegrable rhs volume 0 1 := by
    change IntervalIntegrable (D.ode.rhs u) volume 0 1
    exact D.ode.rhs_intervalIntegrable u
  have hsol := hu.integralSolution D.ode
  have hsubset : uIcc 0 t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le (le_of_lt ht.1), uIcc_of_le (by norm_num)]
    intro s hs
    exact ⟨hs.1, hs.2.trans (le_of_lt ht.2)⟩
  have hrhsIntT : IntervalIntegrable rhs volume 0 t := hrhsInt.mono_set hsubset
  have hprimitive : HasDerivAt
      (fun s => D.initial + (∫ r in 0..s, rhs r)) (rhs t) t := by
    have hprimitive' := intervalIntegral.integral_hasDerivAt_right hrhsIntT
      ((ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioo hRhsOn) t ht)
      (hRhsOn.continuousAt (Ioo_mem_nhds ht.1 ht.2))
    exact hprimitive'.const_add D.initial
  have hlocal : y =ᶠ[𝓝 t]
      (fun s => D.initial + (∫ r in 0..s, rhs r)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    exact hsol s (Ioo_subset_Icc_self hs)
  have hresult := hprimitive.congr_of_eventuallyEq hlocal
  simpa [y, rhs, AVenhance.Infra.ODE.linearRhs] using hresult

end ForcedGalerkinData

theorem GalerkinSmoothTime.classicalSummable_of_norm_le_majorant
    {ι E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ι → E) (g : ι → ℝ) (hg : Summable g)
    (hfg : ∀ i, ‖f i‖ ≤ g i) (_hg0 : ∀ i, 0 ≤ g i) : Summable f := by
  apply Summable.of_norm_bounded hg
  intro i
  simpa only [Real.norm_of_nonneg (_hg0 i)] using hfg i

/-- One Fourier mode as a continuous function jointly in time and torus position. -/
@[irreducible] noncomputable def classicalGalerkinFourierJointTerm
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let a := classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per k
  exact ⟨fun p => a p.1 * UnitAddTorus.mFourier k p.2,
    (a.continuous.comp continuous_fst).mul
      ((UnitAddTorus.mFourier k).continuous.comp continuous_snd)⟩

theorem GalerkinSmoothTime.classicalGalerkinFourierJointTerm_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∀ k : Fin 2 → ℤ,
      ‖classicalGalerkinFourierJointTerm φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k‖ ≤
      classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per 0 * classicalScaledTorusFrequencyWeight k := by
  intro k
  let C := classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per 0
  have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0
  have hCw : 0 ≤ C * classicalScaledTorusFrequencyWeight k := by
    dsimp [classicalScaledTorusFrequencyWeight]
    positivity
  apply (ContinuousMap.norm_le
    (f := classicalGalerkinFourierJointTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per k) hCw).2
  intro p
  unfold classicalGalerkinFourierJointTerm
  change ‖(classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per k p.1) * UnitAddTorus.mFourier k p.2‖ ≤ _
  rw [norm_mul]
  have hmode : ‖UnitAddTorus.mFourier k p.2‖ ≤ 1 := by
    exact (ContinuousMap.norm_coe_le_norm (UnitAddTorus.mFourier k) p.2).trans_eq
      (by simp [UnitAddTorus.mFourier_norm])
  have hcoeff := classicalGalerkinFourierCoefficientBound_spec
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0 k p.1
  let x : ℝ := 2 * Real.pi * |(k 0 : ℝ)|
  let y : ℝ := 2 * Real.pi * |(k 1 : ℝ)|
  let a := ‖classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per [] k p.1‖
  have hcoeffBound := classicalWeightedCoeff_frequencyPower_le 0 x y a C
    (by positivity) (by positivity) (norm_nonneg _) (by
      simpa [x, y, a] using hcoeff)
  have hcoeffEq : classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per k p.1 =
    classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per [] k p.1 := rfl
  calc
    ‖classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k p.1‖ * ‖UnitAddTorus.mFourier k p.2‖ ≤
        ‖classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per k p.1‖ * 1 :=
      mul_le_mul_of_nonneg_left hmode (norm_nonneg _)
    _ = ‖classicalGalerkinLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k p.1‖ := by ring
    _ ≤ C * classicalScaledTorusFrequencyWeight k := by
      simpa [C, x, y, a, classicalScaledTorusFrequencyWeight, hcoeffEq] using hcoeffBound

theorem GalerkinSmoothTime.classicalGalerkinFourierJointTerm_summable
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    Summable (classicalGalerkinFourierJointTerm φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per) := by
  let C := classicalGalerkinFourierCoefficientBound φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per 0
  have hC : 0 ≤ C := classicalGalerkinFourierCoefficientBound_nonneg
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per 0
  have hweight : Summable (fun k : Fin 2 → ℤ =>
      C * classicalScaledTorusFrequencyWeight k) :=
    classicalScaledTorusFrequencyWeight_summable.mul_left C
  have hbound : ∀ k : Fin 2 → ℤ,
      ‖classicalGalerkinFourierJointTerm φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per k‖ ≤ C * classicalScaledTorusFrequencyWeight k := by
    intro k
    simpa [C] using GalerkinSmoothTime.classicalGalerkinFourierJointTerm_norm_le
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per k
  have hnonneg : ∀ k : Fin 2 → ℤ, 0 ≤ C * classicalScaledTorusFrequencyWeight k := by
    intro k
    dsimp [classicalScaledTorusFrequencyWeight]
    positivity
  exact GalerkinSmoothTime.classicalSummable_of_norm_le_majorant _ _ hweight hbound hnonneg

end AVenhance.Infra.Classical

end
