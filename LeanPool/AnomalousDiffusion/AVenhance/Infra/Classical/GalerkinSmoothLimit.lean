/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinLimit
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinConvergence
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinResidualBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinDerivative

/-! Uniform Sobolev energy bounds for all spatial derivatives of the Galerkin paths. -/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter Topology Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalSmoothLimitMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalSmoothLimitMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalSmoothLimitProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalSmoothLimitOneLeTwoFact : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothLimit.classicalSmoothLimitWord_periodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinSmoothLimit.classicalSmoothLimitWord_contDiff (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w f) := by
  exact classicalWordDerivative_contDiff w f (hf.of_le (by simp))

theorem GalerkinSmoothLimit.classicalSmoothLimitWord_memLp_eq_synthesis (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N)) :
    let f := classicalWordDerivative w (realFourierModeAmbientExpansion N c)
    let hmem := memLp_periodicToTorus_real
      (GalerkinSmoothLimit.classicalSmoothLimitWord_contDiff w (realFourierModeAmbientExpansion N c)
        (realFourierModeAmbientExpansion_contDiff N c)).continuous
      (GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w (realFourierModeAmbientExpansion N c)
        (realFourierModeAmbientExpansion_periodic N c))
    hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f) =
      realFourierScalarMap N (realFourierWordDerivativeMap N w c) := by
  dsimp
  let f := classicalWordDerivative w (realFourierModeAmbientExpansion N c)
  let d := realFourierWordDerivativeMap N w c
  have hu0 : ContDiff ℝ ⊤ (realFourierModeAmbientExpansion N c) :=
    realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) (realFourierModeAmbientExpansion N c) :=
    hu0.of_le (by simp)
  let hmem := memLp_periodicToTorus_real
    (classicalWordDerivative_contDiff w (realFourierModeAmbientExpansion N c)
      hu).continuous
    (GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w (realFourierModeAmbientExpansion N c)
      (realFourierModeAmbientExpansion_periodic N c))
  have hword : f = realFourierModeAmbientExpansion N d := by
    simpa [f, d, realFourierWordDerivativeMap_apply] using
      classicalWordDerivative_realFourierModeAmbientExpansion N w c
  apply Lp.ext
  filter_upwards [hmem.coeFn_toLp, realFourierScalarMap_coeFn N d] with x hleft hright
  calc
    (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f)) x =
        AVenhance.Infra.Torus.periodicToTorus f x := hleft
    _ = modeExpansion (RealFourierDimension N) (realFourierModeFin N) d x := by
      rw [hword]
      exact congrFun (realFourierModeFin_expansion_eq_periodicToTorus N d).symm x
    _ = (realFourierScalarMap N d) x := hright.symm

theorem classicalGalerkinWordDerivative_gradient_energy_uniform_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (s : ℕ) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      ∀ w, w.length ≤ s →
        AVenhance.gradNormSq (AVenhance.spaceGrad
          (classicalWordDerivative w
            (realFourierModeAmbientExpansion N
              (AVenhance.Infra.ODE.extendCurve (by norm_num)
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)))) ≤ E := by
  obtain ⟨C, hC, hcoeff⟩ := classicalGalerkin_wordDerivative_coeff_uniform_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (s + 1)
  refine ⟨2 * C ^ 2, by positivity, ?_⟩
  intro N t ht w hw
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num)
    (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t
  let u := realFourierModeAmbientExpansion N c
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  let f := classicalWordDerivative w u
  have hf0 : ContDiff ℝ (⊤ : ℕ∞) f := by
    exact classicalWordDerivative_contDiff w u hu
  have hf : ContDiff ℝ 1 f := hf0.of_le (by simp)
  have hfp : AVenhance.IsZ2Periodic f := by
    simpa [f, u] using GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w
      (realFourierModeAmbientExpansion N c) (realFourierModeAmbientExpansion_periodic N c)
  have hprojection : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad f x i))‖ ≤ C := by
    intro i K
    let wi := i :: w
    let gi := classicalWordDerivative wi u
    have hgi : (fun x => AVenhance.spaceGrad f x i) = gi := by
      funext x
      rfl
    have hgi0 : ContDiff ℝ (⊤ : ℕ∞) gi :=
      classicalWordDerivative_contDiff wi u hu
    have hgiP : AVenhance.IsZ2Periodic gi :=
      GalerkinSmoothLimit.classicalSmoothLimitWord_periodic wi u
          (realFourierModeAmbientExpansion_periodic N c)
    let hmem := memLp_periodicToTorus_real hgi0.continuous hgiP
    have hproj := realFourierModeFin_projectionCoefficients_norm_le K hmem
    have hcoeffi : ‖realFourierWordDerivativeMap N wi c‖ ≤ C := by
      exact hcoeff N t ht wi (by simp [wi, hw])
    have hmemEq : hmem.toLp (AVenhance.Infra.Torus.periodicToTorus gi) =
        realFourierScalarMap N (realFourierWordDerivativeMap N wi c) := by
      simpa [hmem, gi, u] using
        GalerkinSmoothLimit.classicalSmoothLimitWord_memLp_eq_synthesis N wi c
    have hbound := hproj
    rw [hmemEq, realFourierScalarMap_norm] at hbound
    rw [hgi]
    exact hbound.trans hcoeffi
  exact classicalSmoothSource_gradient_energy_le_of_projection_bounds f hf hfp hC
    hprojection

/-- Applying an ordered derivative word costs at most the corresponding cutoff frequency to that
word's length in coefficient `L²`. -/
theorem classicalGalerkinWordDerivativeMap_norm_le (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N)) :
    ‖realFourierWordDerivativeMap N w c‖ ≤
      (2 * Real.pi * N) ^ w.length * ‖c‖ := by
  induction w with
  | nil => simp [realFourierWordDerivativeMap]
  | cons i w ih =>
      change ‖realFourierModeDerivativeMap N i
          (realFourierWordDerivativeMap N w c)‖ ≤ _
      calc
        _ ≤ (2 * Real.pi * N) *
            ‖realFourierWordDerivativeMap N w c‖ := by
          simpa only [realFourierModeDerivativeMap_apply] using
            realFourierModeDerivativeCoefficients_norm_le N
              (realFourierWordDerivativeMap N w c) i
        _ ≤ (2 * Real.pi * N) *
            ((2 * Real.pi * N) ^ w.length * ‖c‖) :=
          mul_le_mul_of_nonneg_left ih (by positivity)
        _ = (2 * Real.pi * N) ^ (w.length + 1) * ‖c‖ := by
          rw [pow_succ]
          ring

/-- The finite Fourier coefficient projection is contractive on torus `L²`. -/
theorem classicalGalerkinProjectionCLM_norm_le (N : ℕ) (v : ScalarTorusL2) :
    ‖realFourierProjectionCLM N v‖ ≤ ‖v‖ := by
  have hcoeff : realFourierProjectionCLM N v =
      orthonormalProjectionCoefficients (realFourierModeL2 N) v := by
    ext i
    simp [orthonormalProjectionCoefficients, realFourierProjectionCLM_apply]
  rw [hcoeff]
  exact orthonormalProjectionCoefficients_norm_le (realFourierModeL2 N)
    (realFourierModeL2_inner N) v

/-- The `L²` coefficient projection of a finite ambient expansion is its continuous Fourier
projection. -/
theorem classicalGalerkinProjectionCLM_expansion (N K : ℕ)
    (c : Coefficients (RealFourierDimension N)) :
    modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus (realFourierModeAmbientExpansion N c)) =
      realFourierProjectionCLM K (realFourierScalarMap N c) := by
  let f := realFourierModeAmbientExpansion N c
  have hf0 : ContDiff ℝ ⊤ f := by simpa [f] using realFourierModeAmbientExpansion_contDiff N c
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := hf0.of_le (by simp)
  have hfp : AVenhance.IsZ2Periodic f := by
    simpa [f] using realFourierModeAmbientExpansion_periodic N c
  let hmem := memLp_periodicToTorus_real hf.continuous hfp
  have hmemEq : hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f) =
      realFourierScalarMap N c := by
    simpa [f, hmem, classicalWordDerivative, realFourierWordDerivativeMap,
      realFourierWordDerivativeCoefficients] using
      GalerkinSmoothLimit.classicalSmoothLimitWord_memLp_eq_synthesis N [] c
  rw [← hmemEq]
  exact realFourierModeProjectionCoefficients_eq_CLM K hmem

/-- Differentiating a finite Galerkin path and then projecting to cutoff `K` agrees with
differentiating its cutoff-`K` projection. -/
theorem classicalGalerkinWordDerivative_projectionCLM (N K : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N)) :
    realFourierScalarMap K (realFourierWordDerivativeMap K w
        (realFourierProjectionCLM K (realFourierScalarMap N c))) =
      realFourierScalarMap K
        (modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
          (AVenhance.Infra.Torus.periodicToTorus
            (classicalWordDerivative w (realFourierModeAmbientExpansion N c)))) := by
  have hu0 : ContDiff ℝ ⊤ (realFourierModeAmbientExpansion N c) :=
    realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) (realFourierModeAmbientExpansion N c) :=
    hu0.of_le (by simp)
  have hup := realFourierModeAmbientExpansion_periodic N c
  rw [← classicalGalerkinProjectionCLM_expansion N K c]
  congr 1
  exact realFourierWordDerivativeMap_projection K w
    (realFourierModeAmbientExpansion N c) hu hup

/-- The scalar `L²` path of one ordered spatial derivative of the finite Galerkin solutions. -/
noncomputable def classicalGalerkinWordScalarPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (w : List (Fin 2)) (N : ℕ) : C(Icc (0 : ℝ) 1, ScalarTorusL2) :=
  let L := (realFourierScalarMap N).comp (realFourierWordDerivativeMap N w)
  ⟨fun t => L (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t),
    L.continuous.comp (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N).continuous⟩

@[simp]
theorem classicalGalerkinWordScalarPath_apply
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (w : List (Fin 2)) (N : ℕ) (t : Icc (0 : ℝ) 1) :
    classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t =
      realFourierScalarMap N (realFourierWordDerivativeMap N w
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t)) := rfl

/-- Project the base Galerkin path to a fixed cutoff, then apply one derivative word. -/
noncomputable def classicalGalerkinLowDerivativeCLM (K : ℕ) (w : List (Fin 2)) :
    ScalarTorusL2 →L[ℝ] ScalarTorusL2 :=
  (realFourierScalarMap K).comp
    ((realFourierWordDerivativeMap K w).comp (realFourierProjectionCLM K))

theorem classicalGalerkinLowDerivativeCLM_norm_apply_le (K : ℕ)
    (w : List (Fin 2)) (v : ScalarTorusL2) :
    ‖classicalGalerkinLowDerivativeCLM K w v‖ ≤
      (2 * Real.pi * K) ^ w.length * ‖v‖ := by
  rw [classicalGalerkinLowDerivativeCLM, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, realFourierScalarMap_norm]
  calc
    ‖realFourierWordDerivativeMap K w (realFourierProjectionCLM K v)‖ ≤
        (2 * Real.pi * K) ^ w.length * ‖realFourierProjectionCLM K v‖ :=
      classicalGalerkinWordDerivativeMap_norm_le K w _
    _ ≤ (2 * Real.pi * K) ^ w.length * ‖v‖ :=
      mul_le_mul_of_nonneg_left (classicalGalerkinProjectionCLM_norm_le K v) (by positivity)

/-- Above a fixed cutoff, the derivative path differs from its low-mode projection by a tail
controlled by the uniform energy of one more derivative. -/
theorem classicalGalerkinWordScalarPath_tail_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (w : List (Fin 2)) (E : ℝ)
    (henergy : ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq (AVenhance.spaceGrad
        (classicalWordDerivative w
          (realFourierModeAmbientExpansion N
            (AVenhance.Infra.ODE.extendCurve (by norm_num)
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)))) ≤ E)
    (K N : ℕ) (hKN : K ≤ N) (t : Icc (0 : ℝ) 1) :
    ‖classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t -
      classicalGalerkinLowDerivativeCLM K w
        (classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N t)‖ ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E) := by
  let c := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t
  let u := realFourierModeAmbientExpansion N c
  let f := classicalWordDerivative w u
  let d := realFourierWordDerivativeMap N w c
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u, c] using realFourierModeAmbientExpansion_contDiff N
      (AVenhance.Infra.ODE.extendCurve (by norm_num)
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u, c] using realFourierModeAmbientExpansion_periodic N
      (AVenhance.Infra.ODE.extendCurve (by norm_num)
        (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)
  have hf0 : ContDiff ℝ (⊤ : ℕ∞) f := classicalWordDerivative_contDiff w u hu
  have hf : ContDiff ℝ 1 f := hf0.of_le (by simp)
  have hfp := GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w u hup
  let pK := modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
    (AVenhance.Infra.Torus.periodicToTorus f)
  let pN := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
    (AVenhance.Infra.Torus.periodicToTorus f)
  have hbase : modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
      (AVenhance.Infra.Torus.periodicToTorus u) = c := by
    rw [← realFourierModeFin_expansion_eq_periodicToTorus N c]
    exact realFourierModeFin_projectionCoefficients_expansion N c
  have hpN : pN = d := by
    change modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordDerivative w u)) = realFourierWordDerivativeMap N w c
    calc
      _ = realFourierWordDerivativeMap N w
          (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N)
            (AVenhance.Infra.Torus.periodicToTorus u)) :=
        (realFourierWordDerivativeMap_projection N w u hu hup).symm
      _ = realFourierWordDerivativeMap N w c := by rw [hbase]
      _ = d := rfl
  have hprojTail := classicalSmoothProjection_tail_norm_le K N hKN f hf hfp
  have hscale : 0 ≤ (4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
  have hprojTail' : ‖d - realFourierCoefficientsLift hKN pK‖ ≤
      Real.sqrt ((4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E) := by
    rw [← hpN]
    calc
      _ ≤ Real.sqrt ((4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ *
          AVenhance.gradNormSq (AVenhance.spaceGrad f)) := by
        simpa [pK] using hprojTail
      _ ≤ _ := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (by simpa [f, u, c] using henergy N t t.property) hscale)
  have hlow := classicalGalerkinWordDerivative_projectionCLM N K w c
  have hlow' : classicalGalerkinLowDerivativeCLM K w
      (classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N t) =
      realFourierScalarMap K pK := by
    simpa [classicalGalerkinLowDerivativeCLM, classicalGalerkinScalarPath_apply,
      pK, c, u, f] using hlow
  have hdiff : classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t -
      classicalGalerkinLowDerivativeCLM K w
        (classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ N t) =
      realFourierScalarMap N (d - realFourierCoefficientsLift hKN pK) := by
    rw [classicalGalerkinWordScalarPath_apply, hlow']
    rw [← realFourierScalarMap_lift hKN pK]
    change realFourierScalarMap N d - realFourierScalarMap N
        (realFourierCoefficientsLift hKN pK) =
      realFourierScalarMap N (d - realFourierCoefficientsLift hKN pK)
    rw [map_sub]
  rw [hdiff, realFourierScalarMap_norm]
  exact hprojTail'

/-- The derivative Fourier tail tends to zero as its lower cutoff increases. -/
theorem classicalGalerkinWordScalarPathTailError_tendsto_zero (E : ℝ) :
    Tendsto (fun K : ℕ => Real.sqrt
      ((4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E)) atTop (𝓝 0) := by
  let scale : ℕ → ℝ := fun K =>
    (4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹
  have hshift0 : Tendsto (fun K : ℕ => (K : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hshift : Tendsto (fun K : ℕ => ((K + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.cast_add] using hshift0
  have hpow : Tendsto (fun x : ℝ => x ^ 2) atTop atTop :=
    tendsto_pow_atTop (n := 2) (by norm_num)
  have hden : Tendsto (fun K : ℕ => 4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)
      atTop atTop := by
    simpa [scale] using (hpow.comp hshift).const_mul_atTop
      (show 0 < 4 * Real.pi ^ 2 by positivity)
  have hscale : Tendsto scale atTop (𝓝 0) := by
    change Tendsto (fun K => (4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹)
      atTop (𝓝 0)
    exact tendsto_inv_atTop_zero.comp hden
  have hinside : Tendsto (fun K => scale K * E) atTop (𝓝 0) := by
    simpa using hscale.mul_const E
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hinside
  simpa [scale, Function.comp_def, Real.sqrt_zero] using hroot

/-- Every fixed ordered spatial derivative of the Galerkin paths is Cauchy in
`C([0,1];L²(T²))`. -/
theorem classicalGalerkinWordScalarPath_cauchy
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    CauchySeq (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N) := by
  obtain ⟨E, -, henergy⟩ := classicalGalerkinWordDerivative_gradient_energy_uniform_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w.length
  have hwordEnergy (N : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      AVenhance.gradNormSq (AVenhance.spaceGrad
        (classicalWordDerivative w
          (realFourierModeAmbientExpansion N
            (AVenhance.Infra.ODE.extendCurve (by norm_num)
              (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)))) ≤ E :=
    henergy N t ht w (by simp)
  have hbase := classicalGalerkinScalarPath_cauchy φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per
  let error : ℕ → ℝ := fun K => Real.sqrt
    ((4 * Real.pi ^ 2 * ((K + 1 : ℕ) : ℝ) ^ 2)⁻¹ * E)
  have herr := classicalGalerkinWordScalarPathTailError_tendsto_zero E
  let A : ℕ → ℝ := fun K => (2 * Real.pi * K) ^ w.length + 1
  have hA (K : ℕ) : 0 < A K := by
    dsimp [A]
    positivity
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hsmallNear : Set.Iio (ε / 4) ∈ 𝓝 (0 : ℝ) := by
    apply Iio_mem_nhds
    linarith
  obtain ⟨K₀, hK₀⟩ := (eventually_atTop.1 (herr.eventually hsmallNear))
  let K := K₀
  have hKsmall : error K < ε / 4 := by
    simpa [K, error] using hK₀ K le_rfl
  have hbaseSmall : 0 < ε / (2 * A K) := by positivity
  obtain ⟨N₀, hN₀⟩ :=
    (Metric.cauchySeq_iff.mp hbase) (ε / (2 * A K)) hbaseSmall
  refine ⟨max K N₀, ?_⟩
  intro m hm n hn
  let U := fun j => classicalGalerkinScalarPath φ hφ κ hκ F hF θ₀ hθ₀ j
  let V := fun j => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w j
  have hKm : K ≤ m := le_trans (le_max_left _ _) hm
  have hKn : K ≤ n := le_trans (le_max_left _ _) hn
  have hN₀m : N₀ ≤ m := le_trans (le_max_right _ _) hm
  have hN₀n : N₀ ≤ n := le_trans (le_max_right _ _) hn
  have hbaseDist : dist (U m) (U n) < ε / (2 * A K) := hN₀ m hN₀m n hN₀n
  have hpath : dist (V m) (V n) ≤
      2 * error K + A K * dist (U m) (U n) := by
    rw [ContinuousMap.dist_le (by
      dsimp [error]
      positivity)]
    intro t
    have htailm := classicalGalerkinWordScalarPath_tail_le φ hφ κ hκ F hF
      θ₀ hθ₀ w E hwordEnergy K m hKm t
    have htailn := classicalGalerkinWordScalarPath_tail_le φ hφ κ hκ F hF
      θ₀ hθ₀ w E hwordEnergy K n hKn t
    have hlow := classicalGalerkinLowDerivativeCLM_norm_apply_le K w
      (U m t - U n t)
    rw [map_sub] at hlow
    have hpoint : dist (U m t) (U n t) ≤ dist (U m) (U n) :=
      ContinuousMap.dist_apply_le_dist (f := U m) (g := U n) t
    have hlowNorm : ‖classicalGalerkinLowDerivativeCLM K w (U m t) -
        classicalGalerkinLowDerivativeCLM K w (U n t)‖ ≤
        A K * dist (U m) (U n) := by
      calc
        _ ≤ (2 * Real.pi * K) ^ w.length * ‖U m t - U n t‖ := hlow
        _ = (2 * Real.pi * K) ^ w.length * dist (U m t) (U n t) := by
          rw [← dist_eq_norm]
        _ ≤ (2 * Real.pi * K) ^ w.length * dist (U m) (U n) :=
          mul_le_mul_of_nonneg_left hpoint (by positivity)
        _ ≤ A K * dist (U m) (U n) := by
          dsimp [A]
          have hnonneg : 0 ≤ dist (U m) (U n) := dist_nonneg
          have hpow : 0 ≤ (2 * Real.pi * K) ^ w.length := by positivity
          nlinarith
    have hlow' : dist (classicalGalerkinLowDerivativeCLM K w (U m t))
        (classicalGalerkinLowDerivativeCLM K w (U n t)) ≤
        A K * dist (U m) (U n) := by
      simpa only [dist_eq_norm] using hlowNorm
    have htailm' : dist (V m t) (classicalGalerkinLowDerivativeCLM K w (U m t)) ≤
        error K := by
      rw [dist_eq_norm]
      simpa only [V, U, error] using htailm
    have htailn' : dist (classicalGalerkinLowDerivativeCLM K w (U n t)) (V n t) ≤
        error K := by
      rw [dist_eq_norm]
      simpa only [V, U, error, norm_sub_rev] using htailn
    have htri : dist (V m t) (V n t) ≤
        dist (V m t) (classicalGalerkinLowDerivativeCLM K w (U m t)) +
          dist (classicalGalerkinLowDerivativeCLM K w (U m t))
            (classicalGalerkinLowDerivativeCLM K w (U n t)) +
          dist (classicalGalerkinLowDerivativeCLM K w (U n t)) (V n t) := by
      calc
        _ ≤ dist (V m t) (classicalGalerkinLowDerivativeCLM K w (U m t)) +
            dist (classicalGalerkinLowDerivativeCLM K w (U m t)) (V n t) :=
          dist_triangle _ _ _
        _ ≤ dist (V m t) (classicalGalerkinLowDerivativeCLM K w (U m t)) +
            (dist (classicalGalerkinLowDerivativeCLM K w (U m t))
                (classicalGalerkinLowDerivativeCLM K w (U n t)) +
              dist (classicalGalerkinLowDerivativeCLM K w (U n t)) (V n t)) :=
          add_le_add (le_rfl) (dist_triangle _ _ _)
        _ = _ := by ring
    exact htri.trans (by linarith [htailm', htailn', hlow'])
  have hprod : A K * dist (U m) (U n) < ε / 2 := by
    calc
      _ < A K * (ε / (2 * A K)) := mul_lt_mul_of_pos_left hbaseDist (hA K)
      _ = ε / 2 := by field_simp [ne_of_gt (hA K)]
  have hsumsmall : 2 * error K + A K * dist (U m) (U n) < ε := by
    linarith [hKsmall, hprod]
  exact hpath.trans_lt hsumsmall

theorem classicalGalerkinWordScalarPath_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    ∃ u : C(Icc (0 : ℝ) 1, ScalarTorusL2),
      Tendsto (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N)
        atTop (𝓝 u) := by
  exact cauchySeq_tendsto_of_complete
    (classicalGalerkinWordScalarPath_cauchy φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w)

/-- Limit path for a spatial derivative word of the Galerkin solution. -/
noncomputable def classicalGalerkinWordScalarPathLimit
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    C(Icc (0 : ℝ) 1, ScalarTorusL2) :=
  Classical.choose (classicalGalerkinWordScalarPath_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w)

theorem classicalGalerkinWordScalarPathLimit_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    Tendsto (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N)
      atTop (𝓝 (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w)) :=
  (Classical.choose_spec (classicalGalerkinWordScalarPath_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w))

theorem classicalGalerkinWordScalarPathLimit_norm_le
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : Icc (0 : ℝ) 1,
      ‖classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w t‖ ≤ C := by
  obtain ⟨C, hC, hcoeff⟩ := classicalGalerkin_wordDerivative_coeff_uniform_bound
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w.length
  refine ⟨C, hC, ?_⟩
  intro t
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w
  have hconv := classicalGalerkinWordScalarPathLimit_tendsto φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w
  have heval : Tendsto (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF
      θ₀ hθ₀ w N t) atTop (𝓝 (U t)) := by
    exact ((continuous_eval_const t).tendsto _).comp hconv
  have hnorm := (continuous_norm.continuousAt.tendsto).comp heval
  apply le_of_tendsto hnorm
  filter_upwards with N
  change ‖classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t‖ ≤ C
  rw [classicalGalerkinWordScalarPath_apply, realFourierScalarMap_norm]
  have hcoefft := hcoeff N (t : ℝ) t.property w (by simp)
  have htime : AVenhance.Infra.ODE.extendCurve (by norm_num)
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) (t : ℝ) =
      classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t :=
    AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num)
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t.property
  rw [htime] at hcoefft
  exact hcoefft

theorem classicalComplexFourierCoeff_norm_le (f : ComplexScalarTorusL2)
    (k : Fin 2 → ℤ) :
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤ ‖f‖ := by
  have h := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (UnitAddTorus.mFourierBasis.repr f) k
  have hcoeff : (UnitAddTorus.mFourierBasis.repr f) k =
      UnitAddTorus.mFourierCoeff f k := UnitAddTorus.mFourierBasis_repr f k
  rw [hcoeff] at h
  calc
    ‖UnitAddTorus.mFourierCoeff f k‖ ≤
        ‖UnitAddTorus.mFourierBasis.repr f‖ := h
    _ = ‖f‖ := UnitAddTorus.mFourierBasis.repr.norm_map f

/-- Embed real torus square-integrable functions into the complex space. -/
noncomputable def classicalRealToComplexTorusCLM :
    ScalarTorusL2 →L[ℝ] ComplexScalarTorusL2 :=
  Complex.ofRealCLM.compLpL (2 : ENNReal) volume

/-- Extract a complex Fourier coefficient continuously from a real torus function. -/
noncomputable def classicalComplexFourierCoeffCLM (k : Fin 2 → ℤ) :
    ScalarTorusL2 →L[ℝ] ℂ := by
  let B : ComplexScalarTorusL2 →L[ℂ]
      lp (fun _ : Fin 2 → ℤ => ℂ) 2 :=
    UnitAddTorus.mFourierBasis.repr.toContinuousLinearEquiv.toContinuousLinearMap
  let E : lp (fun _ : Fin 2 → ℤ => ℂ) 2 →L[ℂ] ℂ :=
    lp.evalCLM ℂ (fun _ : Fin 2 → ℤ => ℂ) (2 : ENNReal) k
  exact ((E.comp B).restrictScalars ℝ).comp classicalRealToComplexTorusCLM

@[simp]
theorem classicalComplexFourierCoeffCLM_apply (k : Fin 2 → ℤ) (v : ScalarTorusL2) :
    classicalComplexFourierCoeffCLM k v =
      UnitAddTorus.mFourierCoeff (classicalRealToComplexTorusCLM v) k := by
  change (UnitAddTorus.mFourierBasis.repr
    (classicalRealToComplexTorusCLM v)) k = _
  exact UnitAddTorus.mFourierBasis_repr _ k

/-- Fourier coefficient path of the Galerkin limit. -/
noncomputable def classicalGalerkinLimitFourierCoeffPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (k : Fin 2 → ℤ) :
    C(Icc (0 : ℝ) 1, ℂ) :=
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per []
  ⟨fun t => classicalComplexFourierCoeffCLM k (U t),
    (classicalComplexFourierCoeffCLM k).continuous.comp U.continuous⟩

theorem classicalRealToComplexTorusCLM_norm_le (v : ScalarTorusL2) :
    ‖classicalRealToComplexTorusCLM v‖ ≤ ‖v‖ := by
  have hL : ‖classicalRealToComplexTorusCLM‖ ≤ ‖Complex.ofRealCLM‖ := by
    simpa [classicalRealToComplexTorusCLM] using
      (ContinuousLinearMap.norm_compLpL_le (p := (2 : ENNReal)) Complex.ofRealCLM)
  calc
    ‖classicalRealToComplexTorusCLM v‖ ≤
        ‖classicalRealToComplexTorusCLM‖ * ‖v‖ :=
      classicalRealToComplexTorusCLM.le_opNorm v
    _ ≤ ‖Complex.ofRealCLM‖ * ‖v‖ :=
      mul_le_mul_of_nonneg_right hL (norm_nonneg v)
    _ = ‖v‖ := by simp [Complex.ofRealCLM]

theorem GalerkinSmoothLimit.classicalPeriodicToTorusL2_fourierCoeff_eq
    {f : Vec 2 → ℂ} (hf : Continuous f) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
        (AVenhance.Infra.Torus.periodicToTorusL2 f hf) k =
      AVenhance.Infra.Torus.smoothFourierCoeff f k := by
  let hmem := AVenhance.Infra.Torus.memLp_periodicToTorus hf
  calc
    UnitAddTorus.mFourierCoeff
        (AVenhance.Infra.Torus.periodicToTorusL2 f hf) k =
        ∫ y : UnitAddTorus (Fin 2),
          UnitAddTorus.mFourier (-k) y * AVenhance.Infra.Torus.periodicToTorus f y := by
      apply integral_congr_ae
      filter_upwards [hmem.coeFn_toLp] with y hy
      exact congrArg (fun z : ℂ => UnitAddTorus.mFourier (-k) y * z) hy
    _ = ∫ x in AVenhance.Infra.Torus.unitCell 2,
          AVenhance.Infra.Torus.torusCharacter k x * f x := by
      rw [← AVenhance.Infra.Torus.integral_periodicToTorus_eq_unitCell
        (fun x : Vec 2 => AVenhance.Infra.Torus.torusCharacter k x * f x)]
      apply integral_congr_ae
      filter_upwards with y
      change UnitAddTorus.mFourier (-k) y * f
          (AVenhance.Infra.Torus.unitTorusRepresentative 2 y) =
        UnitAddTorus.mFourier (-k)
          (AVenhance.Infra.Torus.toUnitTorus 2
            (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)) *
          f (AVenhance.Infra.Torus.unitTorusRepresentative 2 y)
      rw [AVenhance.Infra.Torus.toUnitTorus_unitTorusRepresentative]

/-- Fourier coefficients in a finite real Galerkin projection agree with those of the projected
datum at every frequency contained in the cutoff. -/
theorem classicalComplexFourierCoeffCLM_projection (N : ℕ)
    {f : Torus → ℝ} (hf : Integrable f (volume : Measure Torus))
    (k : Fin 2 → ℤ) (hk : frequencyPair k ∈ symmetricFrequencyBox N) :
    classicalComplexFourierCoeffCLM k
      (realFourierScalarMap N
        (modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f)) =
      UnitAddTorus.mFourierCoeff (fun x : Torus => (f x : ℂ)) k := by
  let c := modeProjectionCoefficients (RealFourierDimension N) (realFourierModeFin N) f
  let u := realFourierModeAmbientExpansion N c
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u, c] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup := realFourierModeAmbientExpansion_periodic N c
  have hmem := memLp_periodicToTorus_real hu.continuous hup
  have hsynthesis : hmem.toLp (AVenhance.Infra.Torus.periodicToTorus u) =
      realFourierScalarMap N c := by
    simpa [hmem, u, c, classicalWordDerivative,
      realFourierWordDerivativeMap, realFourierWordDerivativeCoefficients] using
      GalerkinSmoothLimit.classicalSmoothLimitWord_memLp_eq_synthesis N [] c
  have hcomplex : classicalRealToComplexTorusCLM
      (realFourierScalarMap N c) =
      AVenhance.Infra.Torus.periodicToTorusL2 (AVenhance.Infra.Torus.realToComplex u)
        (Complex.ofRealCLM.continuous.comp hu.continuous) := by
    have hmap := congrArg classicalRealToComplexTorusCLM hsynthesis
    have hcomplex' : classicalRealToComplexTorusCLM
        (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus u)) =
        AVenhance.Infra.Torus.periodicToTorusL2 (AVenhance.Infra.Torus.realToComplex u)
          (Complex.ofRealCLM.continuous.comp hu.continuous) := by
      apply Lp.ext
      filter_upwards [Complex.ofRealCLM.coeFn_compLp
          (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus u)),
        hmem.coeFn_toLp,
        AVenhance.Infra.Torus.memLp_periodicToTorus
          (Complex.ofRealCLM.continuous.comp hu.continuous) |>.coeFn_toLp] with
        x hcast hreal hcomplex
      calc
        (classicalRealToComplexTorusCLM
            (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus u))) x =
            Complex.ofRealCLM
              ((hmem.toLp (AVenhance.Infra.Torus.periodicToTorus u)) x) := hcast
        _ = Complex.ofRealCLM (AVenhance.Infra.Torus.periodicToTorus u x) := by rw [hreal]
        _ = AVenhance.Infra.Torus.periodicToTorus
            (AVenhance.Infra.Torus.realToComplex u) x := rfl
        _ = (AVenhance.Infra.Torus.periodicToTorusL2
            (AVenhance.Infra.Torus.realToComplex u)
            (Complex.ofRealCLM.continuous.comp hu.continuous)) x := hcomplex.symm
    rw [← hmap]
    exact hcomplex'
  have hrealComplex : Continuous (AVenhance.Infra.Torus.realToComplex u) := by
    simpa [AVenhance.Infra.Torus.realToComplex] using
      (Complex.ofRealCLM.continuous.comp hu.continuous)
  have hcoeff := GalerkinSmoothLimit.classicalPeriodicToTorusL2_fourierCoeff_eq
    (f := AVenhance.Infra.Torus.realToComplex u) hrealComplex k
  have hexpansion := realFourierModeFin_expansion_eq_periodicToTorus N c
  have hproj := realFourierModeFin_projectionExpansion_fourierCoeff N hf k hk
  have hcoeffToFun : UnitAddTorus.mFourierCoeff
      (AVenhance.Infra.Torus.periodicToTorusL2
        (AVenhance.Infra.Torus.realToComplex u) hrealComplex) k =
      UnitAddTorus.mFourierCoeff
        (fun x : Torus => AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.Infra.Torus.realToComplex u) x) k := by
    unfold UnitAddTorus.mFourierCoeff
    apply integral_congr_ae
    filter_upwards [AVenhance.Infra.Torus.memLp_periodicToTorus hrealComplex |>.coeFn_toLp]
      with x hx
    have hx' : AVenhance.Infra.Torus.periodicToTorusL2
        (AVenhance.Infra.Torus.realToComplex u) hrealComplex x =
        AVenhance.Infra.Torus.periodicToTorus
          (AVenhance.Infra.Torus.realToComplex u) x := by
      simpa [AVenhance.Infra.Torus.periodicToTorusL2] using hx
    rw [hx']
  have hfourier : AVenhance.Infra.Torus.smoothFourierCoeff
      (AVenhance.Infra.Torus.realToComplex u) k =
      UnitAddTorus.mFourierCoeff (fun x : Torus => (f x : ℂ)) k := by
    have hexp (x : Torus) : modeExpansion (RealFourierDimension N)
        (realFourierModeFin N) c x =
          AVenhance.Infra.Torus.periodicToTorus (f := u) x :=
      congrFun hexpansion x
    have hfun : (fun x : Torus => AVenhance.Infra.Torus.periodicToTorus
        (f := AVenhance.Infra.Torus.realToComplex u) x) =
      fun x => (modeExpansion (RealFourierDimension N)
        (realFourierModeFin N) c x : ℂ) := by
      funext x
      change Complex.ofReal (AVenhance.Infra.Torus.periodicToTorus (f := u) x) = _
      exact congrArg Complex.ofReal (hexp x).symm
    calc
      AVenhance.Infra.Torus.smoothFourierCoeff
          (AVenhance.Infra.Torus.realToComplex u) k =
        UnitAddTorus.mFourierCoeff
          (AVenhance.Infra.Torus.periodicToTorusL2
            (AVenhance.Infra.Torus.realToComplex u) hrealComplex) k := hcoeff.symm
      _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus => AVenhance.Infra.Torus.periodicToTorus
            (f := AVenhance.Infra.Torus.realToComplex u) x) k := hcoeffToFun
      _ = UnitAddTorus.mFourierCoeff
          (fun x : Torus =>
            (modeExpansion (RealFourierDimension N) (realFourierModeFin N) c x : ℂ)) k := by
          rw [hfun]
      _ = _ := by simpa [c] using hproj
  rw [classicalComplexFourierCoeffCLM_apply, hcomplex, hcoeff]
  exact hfourier

theorem GalerkinSmoothLimit.classicalGalerkinWordFourierCoeff_eq_smooth (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N))
    (k : Fin 2 → ℤ) :
    classicalComplexFourierCoeffCLM k
        (realFourierScalarMap N (realFourierWordDerivativeMap N w c)) =
      AVenhance.Infra.Torus.smoothFourierCoeff
        (AVenhance.Infra.Torus.realToComplex
          (classicalWordDerivative w (realFourierModeAmbientExpansion N c))) k := by
  let f := classicalWordDerivative w (realFourierModeAmbientExpansion N c)
  let hf : ContDiff ℝ (⊤ : ℕ∞) f := GalerkinSmoothLimit.classicalSmoothLimitWord_contDiff w
    (realFourierModeAmbientExpansion N c) (realFourierModeAmbientExpansion_contDiff N c)
  let hper := GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w
    (realFourierModeAmbientExpansion N c) (realFourierModeAmbientExpansion_periodic N c)
  let hmem := memLp_periodicToTorus_real hf.continuous hper
  have hmemEq : hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f) =
      realFourierScalarMap N (realFourierWordDerivativeMap N w c) := by
    simpa [hmem, f] using GalerkinSmoothLimit.classicalSmoothLimitWord_memLp_eq_synthesis N w c
  have hcomplexEq : classicalRealToComplexTorusCLM
      (realFourierScalarMap N (realFourierWordDerivativeMap N w c)) =
      AVenhance.Infra.Torus.periodicToTorusL2 (AVenhance.Infra.Torus.realToComplex f)
        (Complex.ofRealCLM.continuous.comp hf.continuous) := by
    have hmap := congrArg classicalRealToComplexTorusCLM hmemEq
    have hcomplex : classicalRealToComplexTorusCLM
        (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f)) =
        AVenhance.Infra.Torus.periodicToTorusL2 (AVenhance.Infra.Torus.realToComplex f)
          (Complex.ofRealCLM.continuous.comp hf.continuous) := by
      apply Lp.ext
      filter_upwards [Complex.ofRealCLM.coeFn_compLp
          (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f)),
        hmem.coeFn_toLp,
        AVenhance.Infra.Torus.memLp_periodicToTorus
          (Complex.ofRealCLM.continuous.comp hf.continuous) |>.coeFn_toLp] with x hcast hreal
              hcomplex
      calc
        (classicalRealToComplexTorusCLM
            (hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f))) x =
            Complex.ofRealCLM
              ((hmem.toLp (AVenhance.Infra.Torus.periodicToTorus f)) x) := hcast
        _ = Complex.ofRealCLM (AVenhance.Infra.Torus.periodicToTorus f x) := by rw [hreal]
        _ = AVenhance.Infra.Torus.periodicToTorus (AVenhance.Infra.Torus.realToComplex f) x := rfl
        _ = (AVenhance.Infra.Torus.periodicToTorusL2
            (AVenhance.Infra.Torus.realToComplex f)
            (Complex.ofRealCLM.continuous.comp hf.continuous)) x := hcomplex.symm
    rw [← hmap]
    exact hcomplex
  rw [classicalComplexFourierCoeffCLM_apply, hcomplexEq]
  exact GalerkinSmoothLimit.classicalPeriodicToTorusL2_fourierCoeff_eq
    (Complex.ofRealCLM.continuous.comp hf.continuous) k

theorem classicalGalerkinWordFourierCoeff_derivative (N : ℕ)
    (w : List (Fin 2)) (c : Coefficients (RealFourierDimension N))
    (i : Fin 2) (k : Fin 2 → ℤ) :
    classicalComplexFourierCoeffCLM k
        (realFourierScalarMap N (realFourierWordDerivativeMap N (i :: w) c)) =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        classicalComplexFourierCoeffCLM k
          (realFourierScalarMap N (realFourierWordDerivativeMap N w c)) := by
  let u := realFourierModeAmbientExpansion N c
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hw : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative w u) :=
    classicalWordDerivative_contDiff w u hu
  have hwordPer := GalerkinSmoothLimit.classicalSmoothLimitWord_periodic w u
    (realFourierModeAmbientExpansion_periodic N c)
  have hformula := AVenhance.Infra.Torus.smoothFourierCoeff_spaceGrad
    (hw.of_le (by simp)) hwordPer i k
  rw [GalerkinSmoothLimit.classicalGalerkinWordFourierCoeff_eq_smooth N (i :: w) c k,
    GalerkinSmoothLimit.classicalGalerkinWordFourierCoeff_eq_smooth N w c k]
  convert hformula using 1
  congr 1

/-- Fourier coefficient path of a spatial derivative word of the Galerkin limit. -/
noncomputable def classicalGalerkinWordLimitFourierCoeffPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) (k : Fin 2 → ℤ) :
    C(Icc (0 : ℝ) 1, ℂ) :=
  let U := classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w
  ⟨fun t => classicalComplexFourierCoeffCLM k (U t),
    (classicalComplexFourierCoeffCLM k).continuous.comp U.continuous⟩

theorem classicalGalerkinWordFourierCoeff_eval_tendsto
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (k : Fin 2 → ℤ) (t : Icc (0 : ℝ) 1) :
    Tendsto (fun N => classicalComplexFourierCoeffCLM k
      (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t))
      atTop (𝓝 (classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k t)) := by
  have hconv := classicalGalerkinWordScalarPathLimit_tendsto φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w
  have heval : Tendsto (fun N => classicalGalerkinWordScalarPath φ hφ κ hκ F hF
      θ₀ hθ₀ w N t) atTop
      (𝓝 (classicalGalerkinWordScalarPathLimit φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w t)) := by
    exact ((continuous_eval_const t).tendsto _).comp hconv
  exact (classicalComplexFourierCoeffCLM k).continuous.continuousAt.tendsto.comp heval

theorem classicalGalerkinWordLimitFourierCoeff_derivative
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀)
    (w : List (Fin 2)) (i : Fin 2) (k : Fin 2 → ℤ) (t : Icc (0 : ℝ) 1) :
    classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (i :: w) k t =
      (2 * Real.pi * Complex.I * (k i : ℂ)) *
        classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w k t := by
  let multiplier : ℂ := 2 * Real.pi * Complex.I * (k i : ℂ)
  have hderiv := classicalGalerkinWordFourierCoeff_eval_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (i :: w) k t
  have hbase := classicalGalerkinWordFourierCoeff_eval_tendsto
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w k t
  have hfinite : ∀ N,
      classicalComplexFourierCoeffCLM k
        (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ (i :: w) N t) =
      multiplier * classicalComplexFourierCoeffCLM k
        (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t) := by
    intro N
    rw [classicalGalerkinWordScalarPath_apply, classicalGalerkinWordScalarPath_apply]
    exact classicalGalerkinWordFourierCoeff_derivative N w
      (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N t) i k
  have hmul : Tendsto (fun N => multiplier * classicalComplexFourierCoeffCLM k
      (classicalGalerkinWordScalarPath φ hφ κ hκ F hF θ₀ hθ₀ w N t)) atTop
      (𝓝 (multiplier * classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k t)) := by
    simpa [multiplier] using (tendsto_const_nhds.mul hbase)
  have hderiv' := hderiv.congr' (Filter.Eventually.of_forall hfinite)
  have hlim := tendsto_nhds_unique hderiv' hmul
  simpa [multiplier] using hlim

end AVenhance.Infra.Classical

end
