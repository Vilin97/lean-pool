/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinResidual
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinExistence

/-! Uniform coefficient bounds for the residual-tail argument. -/

@[expose] public section

noncomputable section

open MeasureTheory Set
open Homogenization
open AVenhance.Infra.Parabolic.FourierGalerkin

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalResidualBoundsMeasureSpaceUnitAddCircle : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalResidualBoundsMeasureIsAddHaarUnitAddCircle :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalResidualBoundsProbabilityUnitAddCircle : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

namespace AVenhance.Infra.Classical

/-- The all-order derivative-family estimate bounds every fixed ordered derivative coefficient
vector, uniformly in cutoff and time. -/
theorem classicalGalerkin_wordDerivative_coeff_uniform_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      ∀ w, w.length ≤ s →
        ‖realFourierWordDerivativeMap N w
          (AVenhance.Infra.ODE.extendCurve (by norm_num)
            (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)‖ ≤ C := by
  obtain ⟨C, hC, hfamily⟩ :=
    classicalGalerkin_derivativeFamily_uniform_bound φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per s
  refine ⟨C, hC, ?_⟩
  intro N t ht w hw
  let word : ClassicalDerivativeWordIndex s → List (Fin 2) :=
    classicalDerivativeWordOfIndex
  let u := classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N
  let V := energyFamilyPath (fun a : ClassicalDerivativeWordIndex s =>
    ForcedGalerkinData.mapPath (realFourierWordDerivativeMap N (word a)) u)
  let Y := AVenhance.Infra.ODE.extendCurve (by norm_num) V
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num) u t
  have hstate : Y t = WithLp.toLp 2 (fun a : ClassicalDerivativeWordIndex s =>
      realFourierWordDerivativeMap N (word a) c) := by
    rw [show Y t = V ⟨t, ht⟩ from
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) V ht]
    ext a
    simp [V, energyFamilyPath, ForcedGalerkinData.mapPath, c,
      AVenhance.Infra.ODE.extendCurve_eq_of_mem (by norm_num) u ht]
  let a := classicalDerivativeWordIndexOfList w hw
  have hcoord : ‖(Y t).ofLp a‖ ≤ ‖Y t‖ := PiLp.norm_apply_le (x := Y t) a
  have hcoordEq : (Y t).ofLp a = realFourierWordDerivativeMap N w c := by
    rw [hstate]
    have hword : word a = w := by
      simpa [word, a] using classicalDerivativeWordOfIndexOfList w hw
    change realFourierWordDerivativeMap N (word a) c =
      realFourierWordDerivativeMap N w c
    rw [hword]
  have hfamily' : ‖Y t‖ ≤ C := by
    simpa [Y, V, u, word] using hfamily N t ht
  calc
    ‖realFourierWordDerivativeMap N w c‖ = ‖(Y t).ofLp a‖ := by rw [hcoordEq]
    _ ≤ ‖Y t‖ := hcoord
    _ ≤ C := hfamily'

theorem GalerkinResidualBounds.classicalResidualTransport_smooth (b : Vec 2 → Vec 2)
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

theorem GalerkinResidualBounds.classicalResidualTransport_periodic (b : Vec 2 → Vec 2)
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

/-- The transport term built from any forced Galerkin path has uniformly bounded spatial
Dirichlet energy on [0,1]. -/
theorem classicalGalerkinTransport_gradient_energy_uniform_bound
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ N t, t ∈ Icc (0 : ℝ) 1 →
      AVenhance.gradNormSq
        (AVenhance.spaceGrad
          (classicalTransport (AVenhance.streamVel φ t)
            (realFourierModeAmbientExpansion N
              (AVenhance.Infra.ODE.extendCurve (by norm_num)
                (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t)))) ≤ E := by
  obtain ⟨C, hC, hcoeff⟩ :=
    classicalGalerkin_wordDerivative_coeff_uniform_bound φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per 2
  obtain ⟨B, hB, hBderiv⟩ := exists_streamVel_allWordDerivative_uniform_bound φ hφ 1
  let Q : ℝ := 4 * B * C
  let E : ℝ := 2 * Q ^ 2
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E, hE, ?_⟩
  intro N t ht
  let c := AVenhance.Infra.ODE.extendCurve (by norm_num)
    (classicalGalerkinCoefficientPath φ hφ κ hκ F hF θ₀ hθ₀ N) t
  let u := realFourierModeAmbientExpansion N c
  let b : Vec 2 → Vec 2 := fun x => AVenhance.streamVel φ t x
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hjoint := (streamVel_smoothPeriodic φ hφ).smooth
    have hsection : ContDiff ℝ (⊤ : ℕ∞)
        (fun x : Vec 2 => Function.uncurry (AVenhance.streamVel φ) (t, x)) :=
      hjoint.comp (contDiff_const.prodMk contDiff_id)
    simpa [b, Function.uncurry] using hsection
  have hbp : AVenhance.IsZ2Periodic b := by
    intro k x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift k) =
      AVenhance.streamVel φ t x
    simpa using (streamVel_smoothPeriodic φ hφ).periodic 0 k t x
  have hu0 : ContDiff ℝ ⊤ u := by
    simpa [u] using realFourierModeAmbientExpansion_contDiff N c
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := hu0.of_le (by simp)
  have hup : AVenhance.IsZ2Periodic u := by
    simpa [u] using realFourierModeAmbientExpansion_periodic N c
  have hDb : ∀ w, w.length ≤ 1 → ∀ j x,
      ‖classicalWordDerivative w (fun y => b y j) x‖ ≤ B := by
    intro w hw j x
    simpa [b] using hBderiv w hw j t ht x
  let g := classicalTransport b u
  have hg : ContDiff ℝ (⊤ : ℕ∞) g :=
    GalerkinResidualBounds.classicalResidualTransport_smooth b u hb hu
  have hgp : AVenhance.IsZ2Periodic g :=
    GalerkinResidualBounds.classicalResidualTransport_periodic b u hbp hup
  have hprojection : ∀ i K,
      ‖modeProjectionCoefficients (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (fun x => AVenhance.spaceGrad g x i))‖ ≤ Q := by
    intro i K
    have htransport := classicalTransportDerivative_projection_norm_le K N b c i
      hB hb hbp hDb
    have hwords : ∀ w, w.length ≤ 2 →
        ‖realFourierWordDerivativeMap N w c‖ ≤ C := by
      intro w hw
      exact hcoeff N t ht w hw
    have hsum :
        ‖realFourierWordDerivativeMap N [0, i] c‖ +
          ‖realFourierWordDerivativeMap N [1, i] c‖ +
          ‖realFourierWordDerivativeMap N [0] c‖ +
          ‖realFourierWordDerivativeMap N [1] c‖ ≤ 4 * C := by
      have h0 := hwords [0, i] (by simp)
      have h1 := hwords [1, i] (by simp)
      have h2 := hwords [0] (by simp)
      have h3 := hwords [1] (by simp)
      linarith
    have hbound : B *
        (‖realFourierWordDerivativeMap N [0, i] c‖ +
          ‖realFourierWordDerivativeMap N [1, i] c‖ +
          ‖realFourierWordDerivativeMap N [0] c‖ +
          ‖realFourierWordDerivativeMap N [1] c‖) ≤ Q := by
      dsimp [Q]
      calc
        _ ≤ B * (4 * C) := mul_le_mul_of_nonneg_left hsum hB
        _ = 4 * B * C := by ring
    have htransport' : ‖modeProjectionCoefficients
        (RealFourierDimension K) (realFourierModeFin K)
        (AVenhance.Infra.Torus.periodicToTorus
          (classicalWordDerivative [i] (classicalTransport b u)))‖ ≤ Q :=
      htransport.trans (by simpa [Q] using hbound)
    simpa [g, classicalWordDerivative] using htransport'
  have henergy := classicalSmoothSource_gradient_energy_le_of_projection_bounds
    g (hg.of_le (by simp)) hgp hQ hprojection
  simpa [E, Q] using henergy

end AVenhance.Infra.Classical

end
