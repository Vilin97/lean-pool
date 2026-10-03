/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinSmoothJointEquation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinBounds
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.Commutator

/-! Continuous right-hand-side paths for every ordered spatial derivative of the limit equation. -/

@[expose] public section

noncomputable section

open Set
open Filter
open MeasureTheory
open Homogenization
open Topology
open AVenhance.Infra.Torus

/-- Use normalized Haar measure on the unit circle for periodic integrals. -/
local instance classicalWordEquationMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance classicalWordEquationMeasureIsAddHaar :
    Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance classicalWordEquationProbability : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
local instance classicalWordEquationTorusProbability : IsProbabilityMeasure
    (volume : Measure (UnitAddTorus (Fin 2))) := inferInstance
local instance classicalWordEquationOneLeTwo : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩

namespace AVenhance.Infra.Classical

theorem GalerkinSmoothWordEquation.classicalSmoothWordPeriodic (w : List (Fin 2))
    (f : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic f) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w f) := by
  induction w with
  | nil => exact hper
  | cons i w ih =>
      exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

theorem GalerkinSmoothWordEquation.classicalWordDerivative_append (v w : List (Fin 2))
    (f : Vec 2 → ℝ) :
    classicalWordDerivative v (classicalWordDerivative w f) =
      classicalWordDerivative (v ++ w) f := by
  induction v with
  | nil => rfl
  | cons i v ih =>
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative v (classicalWordDerivative w f)) x i = _
      rw [ih]
      rfl

theorem GalerkinSmoothWordEquation.classicalWordDerivative_add (w : List (Fin 2))
    (f g : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    classicalWordDerivative w (fun x => f x + g x) =
      fun x => classicalWordDerivative w f x + classicalWordDerivative w g x := by
  induction w generalizing f g with
  | nil => rfl
  | cons i w ih =>
      have hfw := classicalWordDerivative_contDiff w f hf
      have hgw := classicalWordDerivative_contDiff w g hg
      funext x
      change AVenhance.spaceGrad
        (classicalWordDerivative w (fun y => f y + g y)) x i = _
      rw [ih f g hf hg]
      exact classicalSpaceGrad_add _ _ hfw hgw i x

theorem GalerkinSmoothWordEquation.classicalSpaceLap_contDiff_word (f : Vec 2 → ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => AVenhance.spaceLap f x) := by
  unfold AVenhance.spaceLap
  apply ContDiff.sum
  intro i hi
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (fun y => AVenhance.spaceGrad f y i) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun y => fderiv ℝ f y (Homogenization.basisVec i))
    exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => fderiv ℝ (fun y => AVenhance.spaceGrad f y i) x
      (Homogenization.basisVec i))
  exact (hgrad.fderiv_right (by simp)).clm_apply contDiff_const

theorem GalerkinSmoothWordEquation.classicalTransport_contDiff_word (b : Vec 2 → Vec 2)
    (u : Vec 2 → ℝ) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) := by
  unfold classicalTransport
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => ∑ j : Fin 2, b x j * AVenhance.spaceGrad u x j)
  apply ContDiff.sum
  intro j hj
  have hbcomp : ContDiff ℝ (⊤ : ℕ∞) (fun x => b x j) := (contDiff_pi.1 hb) j
  have hgrad : ContDiff ℝ (⊤ : ℕ∞)
      (fun x => AVenhance.spaceGrad u x j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun x => fderiv ℝ u x (Homogenization.basisVec j))
    exact (hu.fderiv_right (by simp)).clm_apply contDiff_const
  exact hbcomp.mul hgrad

/-- Descend the spatial derivative of a jointly smooth, spatially periodic scalar family. -/
noncomputable def classicalSmoothWordJointPath
    (g : ℝ × Vec 2 → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g classicalHalfSpace)
    (hper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (fun x => g (t, x)))
    (w : List (Fin 2)) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let D := classicalJointWordDerivative w g
  let f : Icc (0 : ℝ) 1 → Vec 2 → ℂ := fun t x => (D (t, x) : ℂ)
  have hmap : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 => ((p.1 : ℝ), p.2)) :=
    continuous_subtype_val.prodMap continuous_id
  have hmem (p : Icc (0 : ℝ) 1 × Vec 2) :
      ((p.1 : ℝ), p.2) ∈ classicalHalfSpace := ⟨p.1.property.1, trivial⟩
  have hf : Continuous (Function.uncurry f) := by
    change Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      (D ((p.1 : ℝ), p.2) : ℂ))
    exact Complex.ofRealCLM.continuous.comp
      ((classicalJointWordDerivative_contDiffOn w g hg).continuousOn
        |>.comp_continuous hmap hmem)
  have hfamily : ∀ t, IsZdPeriodic (f t) := by
    intro t z x
    have hw := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w (fun y => g (t, y)) (hper
        t t.property.1)
    change (D (t, x + AVenhance.latticeShift z) : ℂ) = (D (t, x) : ℂ)
    change (classicalJointWordDerivative w g (t, x + AVenhance.latticeShift z) : ℂ) =
      (classicalJointWordDerivative w g (t, x) : ℂ)
    rw [classicalJointWordDerivative_eq_slice w g hg t.property.1]
    rw [classicalJointWordDerivative_eq_slice w g hg t.property.1]
    exact congrArg (fun r : ℝ => (r : ℂ)) (hw z x)
  exact classicalPeriodicFamilyJointPath f hf hfamily

theorem classicalSmoothWordJointPath_apply
    (g : ℝ × Vec 2 → ℝ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g classicalHalfSpace)
    (hper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (fun x => g (t, x)))
    (w : List (Fin 2)) (t : Icc (0 : ℝ) 1) (x : UnitAddTorus (Fin 2)) :
    classicalSmoothWordJointPath g hg hper w (t, x) =
      (classicalWordDerivative w (fun y => g (t, y))
        (unitTorusRepresentative 2 x) : ℂ) := by
  change (classicalJointWordDerivative w g
    ((t : ℝ), unitTorusRepresentative 2 x) : ℂ) = _
  rw [classicalJointWordDerivative_eq_slice w g hg t.property.1]

/-- The forcing after an arbitrary ordered spatial derivative, on the time-space torus slab. -/
noncomputable def classicalGalerkinForcingWordJointPath
    (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (w : List (Fin 2)) : C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) :=
  classicalSmoothWordJointPath (Function.uncurry F)
    (by simpa [classicalHalfSpace] using hF)
    (by
      intro t ht
      simpa [Function.uncurry] using hFper t ht) w

/-- A spatial derivative of a drift coordinate, descended to the time-space torus slab. -/
noncomputable def classicalGalerkinDriftWordJointPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (w : List (Fin 2)) (j : Fin 2) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let g : ℝ × Vec 2 → ℝ := fun p => AVenhance.streamVel φ p.1 p.2 j
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g classicalHalfSpace := by
    have hb := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (p.1, p.2)) classicalHalfSpace :=
      contDiffOn_fst.prodMk contDiffOn_snd
    have hfull : ContDiffOn ℝ (⊤ : ℕ∞)
        (Function.uncurry (AVenhance.streamVel φ) ∘ fun p : ℝ × Vec 2 => (p.1, p.2))
        classicalHalfSpace := by
      exact hb.contDiffOn.comp hpair (fun _ _ => Set.mem_univ _)
    have hcoord : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => AVenhance.streamVel φ p.1 p.2 j) classicalHalfSpace := by
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (Function.uncurry (AVenhance.streamVel φ)
          (p.1, p.2)) j) classicalHalfSpace
      exact (contDiffOn_pi.1 hfull) j
    simpa [g, Function.uncurry] using hcoord
  have hper (t : ℝ) (ht : 0 ≤ t) :
      AVenhance.IsZ2Periodic (fun x => g (t, x)) := by
    intro z x
    change AVenhance.streamVel φ t (x + AVenhance.latticeShift z) j = _
    simpa using congrFun ((streamVel_smoothPeriodic φ hφ).periodic 0 z t x) j
  exact classicalSmoothWordJointPath g hg hper w

theorem classicalGalerkinDriftWordJointPath_apply
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (w : List (Fin 2)) (j : Fin 2) (t : Icc (0 : ℝ) 1)
    (x : UnitAddTorus (Fin 2)) :
    classicalGalerkinDriftWordJointPath φ hφ w j (t, x) =
      (classicalWordDerivative w (fun y => AVenhance.streamVel φ t y j)
        (unitTorusRepresentative 2 x) : ℂ) := by
  let g : ℝ × Vec 2 → ℝ := fun p => AVenhance.streamVel φ p.1 p.2 j
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g classicalHalfSpace := by
    have hb := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (p.1, p.2)) classicalHalfSpace :=
      contDiffOn_fst.prodMk contDiffOn_snd
    have hfull : ContDiffOn ℝ (⊤ : ℕ∞)
        (Function.uncurry (AVenhance.streamVel φ) ∘ fun p : ℝ × Vec 2 => (p.1, p.2))
        classicalHalfSpace := by
      exact hb.contDiffOn.comp hpair (fun _ _ => Set.mem_univ _)
    have hcoord : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => AVenhance.streamVel φ p.1 p.2 j) classicalHalfSpace := by
      change ContDiffOn ℝ (⊤ : ℕ∞)
        (fun p : ℝ × Vec 2 => (Function.uncurry (AVenhance.streamVel φ)
          (p.1, p.2)) j) classicalHalfSpace
      exact (contDiffOn_pi.1 hfull) j
    simpa [g, Function.uncurry] using hcoord
  have hper (s : ℝ) (hs : 0 ≤ s) :
      AVenhance.IsZ2Periodic (fun y => g (s, y)) := by
    intro z y
    change AVenhance.streamVel φ s (y + AVenhance.latticeShift z) j = _
    simpa using congrFun ((streamVel_smoothPeriodic φ hφ).periodic 0 z s y) j
  change classicalSmoothWordJointPath g hg hper w (t, x) = _
  exact classicalSmoothWordJointPath_apply g hg hper w t x

/-- All spatial derivatives of the limiting physical right-hand side, represented continuously on
the closed unit time slab and the spatial torus. -/
noncomputable def classicalGalerkinSmoothWordRhsJointPath
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    C(Icc (0 : ℝ) 1 × UnitAddTorus (Fin 2), ℂ) := by
  let U (v : List (Fin 2)) := classicalGalerkinWordFourierContinuousPath
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per v
  let lap := ∑ i : Fin 2, U ([i, i] ++ w)
  let drift := ∑ j : Fin 2,
    ((classicalWordSplits w).map fun p =>
      classicalGalerkinDriftWordJointPath φ hφ p.1 j * U (p.2 ++ [j])).sum
  exact classicalGalerkinForcingWordJointPath F hF hFper w +
    ContinuousMap.const _ (κ : ℂ) * lap - drift

theorem classicalGalerkinSmoothWordRhsJointPath_apply
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) (x : UnitAddTorus (Fin 2)) :
    classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (t, x) =
      ((classicalWordDerivative w (fun y => F t y + κ * AVenhance.spaceLap
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t) y -
        classicalTransport (AVenhance.streamVel φ t)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t) y))
        (unitTorusRepresentative 2 x) : ℂ) := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  let b := AVenhance.streamVel φ t
  let U (v : List (Fin 2)) := classicalGalerkinWordFourierContinuousPath
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per v
  let y := unitTorusRepresentative 2 x
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have h := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec 2 => ((t : ℝ), x)) :=
      contDiff_const.prodMk contDiff_id
    simpa [b, Function.uncurry, Function.comp_def] using h.comp hpair
  have hwordU (v : List (Fin 2)) :
      U v (t, x) = (classicalWordDerivative v u y : ℂ) := by
    dsimp [U, y]
    exact classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per v t x
  have hFc : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F) classicalHalfSpace := by
    simpa [classicalHalfSpace] using hF
  have hforce := classicalSmoothWordJointPath_apply
    (Function.uncurry F) hFc (by
      intro s hs
      simpa [Function.uncurry] using hFper s hs) w t x
  have hforcePath : classicalGalerkinForcingWordJointPath F hF hFper w (t, x) =
      (classicalWordDerivative w (F t) y : ℂ) := by
    unfold classicalGalerkinForcingWordJointPath
    exact hforce
  have hdriftPath (v : List (Fin 2)) (j : Fin 2) :
      classicalGalerkinDriftWordJointPath φ hφ v j (t, x) =
        (classicalWordDerivative v (fun z => b z j) y : ℂ) := by
    simpa [b] using classicalGalerkinDriftWordJointPath_apply φ hφ v j t x
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) (F t) :=
    AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF t.property.1
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z => AVenhance.spaceLap u z) :=
    GalerkinSmoothWordEquation.classicalSpaceLap_contDiff_word u hu
  have htransportSmooth : ContDiff ℝ (⊤ : ℕ∞) (classicalTransport b u) :=
    GalerkinSmoothWordEquation.classicalTransport_contDiff_word b u hb hu
  have hsplit (j : Fin 2) (p : List (Fin 2) × List (Fin 2)) :
      classicalWordDerivative p.2 (fun z => AVenhance.spaceGrad u z j) =
        classicalWordDerivative (p.2 ++ [j]) u := by
    change classicalWordDerivative p.2 (classicalWordDerivative [j] u) = _
    exact GalerkinSmoothWordEquation.classicalWordDerivative_append p.2 [j] u
  have hlinear : classicalWordDerivative w (fun z =>
      F t z + κ * AVenhance.spaceLap u z - classicalTransport b u z) =
      fun z => classicalWordDerivative w (F t) z +
        κ * classicalWordDerivative w (fun q => AVenhance.spaceLap u q) z -
        classicalWordDerivative w (classicalTransport b u) z := by
    rw [classicalWordDerivative_sub w _ _
      (hFsmooth.add (contDiff_const.mul hlapSmooth)) htransportSmooth]
    rw [GalerkinSmoothWordEquation.classicalWordDerivative_add w (F t) (fun z => κ *
        AVenhance.spaceLap u z)
      hFsmooth (contDiff_const.mul hlapSmooth)]
    rw [classicalWordDerivative_const_mul w κ (fun z => AVenhance.spaceLap u z) hlapSmooth]
  have hLapExpansion : (fun z => AVenhance.spaceLap
      (classicalWordDerivative w u) z) =
      fun z => classicalWordDerivative [0, 0] (classicalWordDerivative w u) z +
        classicalWordDerivative [1, 1] (classicalWordDerivative w u) z := by
    funext z
    simp [AVenhance.spaceLap, classicalWordDerivative, Fin.sum_univ_two]
  have hLapWords : (fun z => AVenhance.spaceLap
      (classicalWordDerivative w u) z) =
      fun z => classicalWordDerivative ([0, 0] ++ w) u z +
        classicalWordDerivative ([1, 1] ++ w) u z := by
    rw [hLapExpansion]
    funext z
    rw [GalerkinSmoothWordEquation.classicalWordDerivative_append [0, 0] w u,
      GalerkinSmoothWordEquation.classicalWordDerivative_append [1, 1] w u]
  have hLapPath : (∑ i : Fin 2, U ([i, i] ++ w)) (t, x) =
      (AVenhance.spaceLap (classicalWordDerivative w u) y : ℂ) := by
    calc
      _ = (classicalWordDerivative ([0, 0] ++ w) u y : ℂ) +
          (classicalWordDerivative ([1, 1] ++ w) u y : ℂ) := by
        simp only [Fin.sum_univ_two]
        simp only [ContinuousMap.add_apply]
        rw [hwordU, hwordU]
      _ = _ := by
        rw [← Complex.ofReal_add]
        exact congrArg Complex.ofReal (congrFun hLapWords y).symm
  have hLapPath' :
      (∑ i : Fin 2, classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per ([i, i] ++ w)) (t, x) =
      (AVenhance.spaceLap (classicalWordDerivative w u) y : ℂ) := by
    simpa [U] using hLapPath
  have hLapPathEval :
      ∑ i : Fin 2, classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per ([i, i] ++ w) (t, x) =
      (AVenhance.spaceLap (classicalWordDerivative w u) y : ℂ) := by
    simpa only [ContinuousMap.sum_apply] using hLapPath'
  have htransport := classicalWordDerivative_transport w b u hb hu
  have hcomponent (j : Fin 2) :
      ((classicalWordSplits w).map (fun p =>
        classicalGalerkinDriftWordJointPath φ hφ p.1 j * U (p.2 ++ [j]))).sum (t, x) =
      (classicalWordProductExpansion w (fun z => b z j)
        (fun z => AVenhance.spaceGrad u z j) y : ℂ) := by
    have hlist (L : List (List (Fin 2) × List (Fin 2))) :
        (L.map (fun p => classicalGalerkinDriftWordJointPath φ hφ p.1 j *
          U (p.2 ++ [j]))).sum (t, x) =
        ((L.map (fun p => classicalWordProductTerm p (fun z => b z j)
          (fun z => AVenhance.spaceGrad u z j))).sum y : ℂ) := by
      induction L with
      | nil => simp
      | cons p L ih =>
        simp only [List.map_cons, List.sum_cons, ContinuousMap.add_apply,
          ContinuousMap.mul_apply]
        rw [hdriftPath p.1 j, hwordU (p.2 ++ [j]), ih]
        simp [classicalWordProductTerm, hsplit, Complex.ofReal_add,
          Complex.ofReal_mul]
    simpa [classicalWordProductExpansion] using hlist (classicalWordSplits w)
  have htransportPath :
      (∑ j : Fin 2, ((classicalWordSplits w).map (fun p =>
        classicalGalerkinDriftWordJointPath φ hφ p.1 j * U (p.2 ++ [j]))).sum) (t, x) =
      (classicalWordDerivative w (classicalTransport b u) y : ℂ) := by
    calc
      _ = ∑ j : Fin 2, (classicalWordProductExpansion w (fun z => b z j)
          (fun z => AVenhance.spaceGrad u z j) y : ℂ) := by
        simp only [ContinuousMap.sum_apply]
        apply Finset.sum_congr rfl
        intro j hj
        exact hcomponent j
      _ = _ := by
        rw [htransport]
        simp only [Complex.ofReal_sum]
  have htransportPath' :
      (∑ j : Fin 2, ((classicalWordSplits w).map (fun p =>
        classicalGalerkinDriftWordJointPath φ hφ p.1 j *
          classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per (p.2 ++ [j]))).sum) (t, x) =
      (classicalWordDerivative w (classicalTransport b u) y : ℂ) := by
    simpa [U] using htransportPath
  have htransportPathEval :
      ∑ j : Fin 2, ((classicalWordSplits w).map (fun p =>
        classicalGalerkinDriftWordJointPath φ hφ p.1 j *
          classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per (p.2 ++ [j]))).sum (t, x) =
      (classicalWordDerivative w (classicalTransport b u) y : ℂ) := by
    simpa only [ContinuousMap.sum_apply] using htransportPath'
  have hlap : classicalWordDerivative w (fun z => AVenhance.spaceLap u z) =
      fun z => AVenhance.spaceLap (classicalWordDerivative w u) z :=
    classicalWordDerivative_spaceLap w u hu
  simp only [classicalGalerkinSmoothWordRhsJointPath]
  simp only [ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.sum_apply]
  simp only [ContinuousMap.const_apply]
  rw [hforcePath, hLapPathEval, htransportPathEval]
  have hpoint := congrArg (fun f : Vec 2 → ℝ => (f y : ℂ)) hlinear
  rw [hlap] at hpoint
  rw [hpoint]
  simp only [Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul]

theorem GalerkinSmoothWordEquation.classicalSmoothWordFourierCoeff_multiplier
    (f : Vec 2 → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : AVenhance.IsZ2Periodic f) (w : List (Fin 2)) (k : Fin 2 → ℤ) :
    smoothFourierCoeff (realToComplex (classicalWordDerivative w f)) k =
      classicalGalerkinWordFourierMultiplier k w *
        smoothFourierCoeff (realToComplex f) k := by
  have hword (v : List (Fin 2)) :
      smoothFourierCoeff (realToComplex (classicalWordDerivative v f)) k =
        classicalGalerkinWordFourierMultiplier k v *
          smoothFourierCoeff (realToComplex f) k := by
    induction v with
    | nil => simp [classicalGalerkinWordFourierMultiplier, classicalWordDerivative]
    | cons i v ih =>
        have hv : ContDiff ℝ (⊤ : ℕ∞) (classicalWordDerivative v f) :=
          classicalWordDerivative_contDiff v f hf
        have hvper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic v f hper
        have hformula := smoothFourierCoeff_spaceGrad (hv.of_le (by simp)) hvper i k
        rw [show classicalWordDerivative (i :: v) f =
          fun y => AVenhance.spaceGrad (classicalWordDerivative v f) y i by rfl]
        change smoothFourierCoeff
          (fun y => (AVenhance.spaceGrad (classicalWordDerivative v f) y i : ℂ)) k = _
        rw [hformula, ih]
        simp [classicalGalerkinWordFourierMultiplier, List.map_cons, List.prod_cons]
        ring
  exact hword w

theorem GalerkinSmoothWordEquation.classicalWordEquation_continuousUnitSlabClamp :
    Continuous classicalGalerkinUnitSlabClamp := by
  exact Continuous.subtype_mk
    (continuous_const.max (continuous_const.min continuous_id))
    (fun s => ⟨le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩)

theorem classicalGalerkinSmoothWordRhsJointPath_fourierCoeff
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) (k : Fin 2 → ℤ) :
    UnitAddTorus.mFourierCoeff
      ((classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry t) k =
      classicalGalerkinWordFourierMultiplier k w *
        UnitAddTorus.mFourierCoeff
          ((classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per).curry t) k := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  let b := AVenhance.streamVel φ t
  let R : Vec 2 → ℝ := fun y => F t y + κ * AVenhance.spaceLap u y -
    classicalTransport b u y
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    simpa [u] using classicalGalerkinRealSmoothLift_contDiff
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have huper : AVenhance.IsZ2Periodic u := by
    simpa [u] using classicalGalerkinRealSmoothLift_periodic
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have h := (streamVel_smoothPeriodic φ hφ).smooth
    have hpair : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec 2 => ((t : ℝ), y)) :=
      contDiff_const.prodMk contDiff_id
    simpa [b, Function.uncurry, Function.comp_def] using h.comp hpair
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z y
    change AVenhance.streamVel φ t (y + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z t y
  have hFslice := AVenhance.Infra.Classical.classicalSmooth_slice_nonneg hF t.property.1
  have hLapsmooth := GalerkinSmoothWordEquation.classicalSpaceLap_contDiff_word u hu
  have hTransportsmooth := GalerkinSmoothWordEquation.classicalTransport_contDiff_word b u hb hu
  have hRsmooth : ContDiff ℝ (⊤ : ℕ∞) R := by
    dsimp [R]
    exact (hFslice.add (contDiff_const.mul hLapsmooth)).sub hTransportsmooth
  have hLapper : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceLap u y) := by
    intro z y
    simp only [AVenhance.spaceLap]
    apply Finset.sum_congr rfl
    intro i hi
    exact AVenhance.Infra.Classical.periodic_spaceGrad_component
      (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i) i z y
  have hTransportper : AVenhance.IsZ2Periodic (classicalTransport b u) := by
    intro z y
    simp only [classicalTransport, Homogenization.vecDot]
    apply Finset.sum_congr rfl
    intro i hi
    have hbcomp := congrFun (hbper z y) i
    have hgrad := AVenhance.Infra.Classical.periodic_spaceGrad_component huper i z y
    change AVenhance.spaceGrad u (y + AVenhance.latticeShift z) i =
      AVenhance.spaceGrad u y i at hgrad
    rw [hbcomp, hgrad]
  have hRper : AVenhance.IsZ2Periodic R := by
    intro z y
    simp only [R]
    have hlap := hLapper z y
    have htransport := hTransportper z y
    change AVenhance.spaceLap u (y + AVenhance.latticeShift z) =
      AVenhance.spaceLap u y at hlap
    rw [hFper t t.property.1 z y, hlap, htransport]
  have hDper (v : List (Fin 2)) :
      AVenhance.IsZ2Periodic (classicalWordDerivative v R) :=
    GalerkinSmoothWordEquation.classicalSmoothWordPeriodic v R hRper
  have hDcont (v : List (Fin 2)) :
      Continuous (classicalWordDerivative v R) :=
    (classicalWordDerivative_contDiff v R hRsmooth).continuous
  have hcomplexPer (v : List (Fin 2)) :
      IsZdPeriodic (realToComplex (classicalWordDerivative v R)) := by
    intro z y
    change (classicalWordDerivative v R (y + AVenhance.latticeShift z) : ℂ) = _
    exact congrArg (fun q : ℝ => (q : ℂ)) (hDper v z y)
  have hcomplexCont (v : List (Fin 2)) :
      Continuous (realToComplex (classicalWordDerivative v R)) := by
    change Continuous (fun y => (classicalWordDerivative v R y : ℂ))
    exact Complex.ofRealCLM.continuous.comp (hDcont v)
  have hwordMap (v : List (Fin 2)) :
      (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per v).curry t =
      ⟨periodicToTorus (realToComplex (classicalWordDerivative v R)),
        AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
          (hcomplexCont v) (hcomplexPer v)⟩ := by
    ext x
    change classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per v (t, x) = _
    rw [classicalGalerkinSmoothWordRhsJointPath_apply]
    rfl
  have hcomplexBaseCont : Continuous (realToComplex R) := by
    simpa [classicalWordDerivative] using hcomplexCont []
  have hcomplexBasePer : IsZdPeriodic (realToComplex R) := by
    simpa [classicalWordDerivative] using hcomplexPer []
  have hbaseMap : (classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per).curry t =
      ⟨periodicToTorus (realToComplex R),
        AVenhance.Infra.Ergodic.periodicToTorus_continuous_of_periodic
          hcomplexBaseCont hcomplexBasePer⟩ := by
    ext x
    change classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per (t, x) = _
    rw [classicalGalerkinSmoothRhsJointPath_apply]
    simp [R, b, classicalTransport, Homogenization.vecDot,
      periodicToTorus, realToComplex, Fin.sum_univ_two]
    ring
  have hwordCoeff := GalerkinSmoothWordEquation.classicalSmoothWordFourierCoeff_multiplier R
      hRsmooth hRper w k
  have hwordTorus := classicalJoint_mFourierCoeff_eq_smoothFourierCoeff
    (hcomplexPer w) (hcomplexCont w) k
  have hbaseTorus := classicalJoint_mFourierCoeff_eq_smoothFourierCoeff
    hcomplexBasePer hcomplexBaseCont k
  rw [hwordMap, hbaseMap]
  rw [hwordTorus, hbaseTorus]
  exact hwordCoeff

/-- Each spatial derivative path satisfies the limiting equation in time-integrated form. -/
theorem classicalGalerkinWordPath_integral_eq
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) :
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry t =
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry 0 +
      ∫ s in (0 : ℝ)..(t : ℝ),
        (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per w).curry (classicalGalerkinUnitSlabClamp s) := by
  let U := (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let R := (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  have hcl : Continuous cl :=
      GalerkinSmoothWordEquation.classicalWordEquation_continuousUnitSlabClamp
  let coeffPath (k : Fin 2 → ℤ) : ℝ → ℂ := fun s =>
    classicalTorusFourierCoeffCLM k (U (cl s))
  let rhsCoeffPath (k : Fin 2 → ℤ) : ℝ → ℂ := fun s =>
    classicalTorusFourierCoeffCLM k (R (cl s))
  have hcoeffCont (k : Fin 2 → ℤ) : Continuous (coeffPath k) := by
    exact (classicalTorusFourierCoeffCLM k).continuous.comp (U.continuous.comp hcl)
  have hrhsCoeffCont (k : Fin 2 → ℤ) : Continuous (rhsCoeffPath k) := by
    exact (classicalTorusFourierCoeffCLM k).continuous.comp (R.continuous.comp hcl)
  have hcoeffEq (k : Fin 2 → ℤ) (s : ℝ) :
      coeffPath k s = classicalGalerkinWordLimitFourierCoeffPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w k (cl s) := by
    simpa [coeffPath, U, cl, classicalTorusFourierCoeffCLM_apply] using
      classicalGalerkinWordFourierPath_fourierCoeff_eq_limit
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w (cl s) k
  have hderiv (k : Fin 2 → ℤ) {s : ℝ}
      (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivAt (coeffPath k) (rhsCoeffPath k s) s := by
    have hs01 : s ∈ Ioo (0 : ℝ) 1 :=
      ⟨hs.1, lt_of_lt_of_le hs.2 t.property.2⟩
    have hs01' : 0 < s ∧ s < 1 := by
      simpa only [Set.mem_Ioo] using hs01
    have hformula := classicalGalerkinWordFourierPath_fourierCoeff_hasDerivAt
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w k hs01
    have hlocal :
        (coeffPath k) =ᶠ[𝓝 s]
          (fun r => UnitAddTorus.mFourierCoeff (U (cl r)) k) := by
      filter_upwards with r
      change classicalTorusFourierCoeffCLM k (U (cl r)) =
        UnitAddTorus.mFourierCoeff (U (cl r)) k
      exact classicalTorusFourierCoeffCLM_apply k (U (cl r))
    have hderivLocal := hformula.congr_of_eventuallyEq hlocal
    have hvalue : rhsCoeffPath k s =
        classicalGalerkinWordFourierMultiplier k w *
          UnitAddTorus.mFourierCoeff
            ((classicalGalerkinSmoothRhsJointPath φ hφ κ hκ F hF hFper
              θ₀ hθ₀ hθ₀per).curry ⟨s, le_of_lt hs01.1, le_of_lt hs01.2⟩) k := by
      dsimp [rhsCoeffPath, R, cl]
      rw [classicalGalerkinUnitSlabClamp_eq_of_mem hs01',
        classicalTorusFourierCoeffCLM_apply]
      exact classicalGalerkinSmoothWordRhsJointPath_fourierCoeff
        φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
          ⟨s, le_of_lt hs01.1, le_of_lt hs01.2⟩ k
    exact hderivLocal.congr_deriv hvalue.symm
  have hftc (k : Fin 2 → ℤ) :
      (∫ s in (0 : ℝ)..(t : ℝ), rhsCoeffPath k s) =
        coeffPath k (t : ℝ) - coeffPath k 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
    · exact (hcoeffCont k).continuousOn
    · intro s hs
      exact hderiv k hs
    · exact (hrhsCoeffCont k).intervalIntegrable 0 (t : ℝ)
  have hcommute (k : Fin 2 → ℤ) :
      (∫ s in (0 : ℝ)..(t : ℝ), rhsCoeffPath k s) =
        classicalTorusFourierCoeffCLM k
          (∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) := by
    rw [show rhsCoeffPath k = fun s => classicalTorusFourierCoeffCLM k (R (cl s)) by rfl]
    exact ContinuousLinearMap.intervalIntegral_comp_comm
      (classicalTorusFourierCoeffCLM k)
      ((R.continuous.comp hcl).intervalIntegrable 0 (t : ℝ))
  have hfourier (k : Fin 2 → ℤ) :
      classicalTorusFourierCoeffCLM k
          (U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) = 0 := by
    have h := hftc k
    rw [hcommute k] at h
    dsimp [coeffPath, rhsCoeffPath] at h
    have hclt : cl (t : ℝ) = t := by
      apply Subtype.ext
      simp [cl, classicalGalerkinUnitSlabClamp, t.property.1, t.property.2]
    have hcl0 : cl 0 = (0 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [cl, classicalGalerkinUnitSlabClamp]
    rw [hclt, hcl0] at h
    change classicalTorusFourierCoeffCLM k
      (U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) = 0
    rw [map_sub, map_sub]
    exact sub_eq_zero.mpr h.symm
  have hLp : ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ
      (U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) = 0 := by
    apply UnitAddTorus.mFourierBasis.repr.injective
    ext k
    calc
      (UnitAddTorus.mFourierBasis.repr
        (ContinuousMap.toLp 2 (volume : Measure (UnitAddTorus (Fin 2))) ℂ
          (U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)))) k =
          classicalTorusFourierCoeffCLM k
            (U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) := by
        rw [UnitAddTorus.mFourierBasis_repr, UnitAddTorus.mFourierCoeff_toLp,
          ← classicalTorusFourierCoeffCLM_apply]
      _ = 0 := hfourier k
      _ = (UnitAddTorus.mFourierBasis.repr 0) k := by simp
  have hzero : U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s) = 0 :=
    ContinuousMap.toLp_injective (p := (2 : ENNReal))
      (μ := (volume : Measure (UnitAddTorus (Fin 2)))) hLp
  have hpath : U t = U 0 + ∫ s in (0 : ℝ)..(t : ℝ), R (cl s) := by
    apply sub_eq_zero.mp
    calc
      U t - (U 0 + ∫ s in (0 : ℝ)..(t : ℝ), R (cl s)) =
          U t - U 0 - ∫ s in (0 : ℝ)..(t : ℝ), R (cl s) := by abel
      _ = 0 := hzero
  simpa [U, R, classicalGalerkinWordFourierContinuousPath,
    classicalGalerkinSmoothWordRhsJointPath, cl] using hpath

/-- Interior time differentiability of every spatial word, with derivative given by its continuous
right-hand-side path. -/
theorem classicalGalerkinWordPath_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry (classicalGalerkinUnitSlabClamp s))
      ((classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) t := by
  let U := (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let R := (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  have hcl : Continuous cl :=
      GalerkinSmoothWordEquation.classicalWordEquation_continuousUnitSlabClamp
  have hRcont : Continuous (fun s => R (cl s)) := R.continuous.comp hcl
  have hRint : IntervalIntegrable (fun s => R (cl s)) volume 0 t :=
    hRcont.intervalIntegrable 0 t
  have hprimitive : HasDerivAt
      (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r)) (R (cl t)) t := by
    have hprimitive' := intervalIntegral.integral_hasDerivAt_right hRint
      hRcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hRcont.continuousAt
    exact hprimitive'.const_add (U 0)
  have hlocal : (fun s => U (cl s)) =ᶠ[𝓝 t]
      (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r)) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hslab : s ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    have hclamp : cl s = ⟨s, hslab⟩ := by
      simpa [cl] using classicalGalerkinUnitSlabClamp_eq_of_mem hs
    rw [hclamp]
    exact classicalGalerkinWordPath_integral_eq φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w ⟨s, hslab⟩
  have hresult := hprimitive.congr_of_eventuallyEq hlocal
  have hclt : cl t = ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ := by
    simpa [cl] using classicalGalerkinUnitSlabClamp_eq_of_mem ht
  have hvalue : R ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ = R (cl t) :=
    congrArg R hclt.symm
  have hfinal := hresult.congr_deriv hvalue.symm
  simpa [U, R, cl] using hfinal

/-- Every spatial word of the smooth Galerkin lift is jointly continuous on the closed unit slab. -/
theorem classicalGalerkinWordLift_jointContinuous
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per p.1) p.2) := by
  let P := classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w
  have htorus : Continuous (toUnitTorus 2) := by
    apply continuous_pi
    intro i
    exact (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)
  have hmap : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      (p.1, toUnitTorus 2 p.2)) :=
    continuous_fst.prodMk (htorus.comp continuous_snd)
  have hP : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 => P (p.1, toUnitTorus 2 p.2)) :=
    P.continuous.comp hmap
  have hreal : Continuous (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      (P (p.1, toUnitTorus 2 p.2)).re) :=
    Complex.reCLM.continuous.comp hP
  have heq : (fun p : Icc (0 : ℝ) 1 × Vec 2 =>
      (P (p.1, toUnitTorus 2 p.2)).re) =
      (fun p => classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per p.1) p.2) := by
    funext p
    have hpoint := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w p.1 (toUnitTorus 2 p.2)
    have hwordper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per p.1)
      (classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per p.1)
    have hrep := congrFun (fromUnitTorus_periodicToTorus
      (isZdPeriodic_iff_frozen _ |>.2 hwordper)) p.2
    have hrep' : classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per p.1)
        (unitTorusRepresentative 2 (toUnitTorus 2 p.2)) =
      classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per p.1) p.2 := by
      simpa [fromUnitTorus, periodicToTorus] using hrep
    have hpoint' := congrArg Complex.re hpoint
    rw [hrep'] at hpoint'
    simpa [P] using hpoint'
  exact hreal.congr (fun p => congrFun heq p)

/-- Pointwise interior time differentiability of every spatial derivative of the smooth lift. -/
theorem classicalGalerkinWordPointwise_hasDerivAt
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) (x : Vec 2)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun s => classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp s)) x)
      (classicalWordDerivative w (fun y => F t y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y -
        classicalTransport (AVenhance.streamVel φ t)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y) x) t := by
  let xT := toUnitTorus 2 x
  let U : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let R : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  let ev : C(UnitAddTorus (Fin 2), ℂ) →L[ℝ] ℂ := ContinuousMap.evalCLM ℝ xT
  have hpath := classicalGalerkinWordPath_hasDerivAt
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w ht
  have heval := (hasDerivAt_const t ev).clm_apply hpath
  have hreal := (hasDerivAt_const t Complex.reCLM).clm_apply heval
  have hreal' : HasDerivAt (fun s => (ev (U (cl s))).re)
      ((ev (R ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩)).re) t := by
    simpa [ev, U, R, ContinuousMap.evalCLM_apply] using hreal
  have hlocal : (fun s => classicalWordDerivative w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s)) x) =ᶠ[𝓝 t]
      (fun s => (ev (U (cl s))).re) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
    have hpoint := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w (cl s) xT
    have hper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (cl s))
      (classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s))
    have hrep := congrFun (fromUnitTorus_periodicToTorus
      (isZdPeriodic_iff_frozen _ |>.2 hper)) x
    have hrep' : classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (cl s)) (unitTorusRepresentative 2 xT) =
        classicalWordDerivative w
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per (cl s)) x := by
      simpa [fromUnitTorus, periodicToTorus, xT] using hrep
    have hpoint' := congrArg Complex.re hpoint
    rw [hrep'] at hpoint'
    simpa [U, ev, ContinuousMap.evalCLM_apply] using hpoint'.symm
  have htransfer := hreal'.congr_of_eventuallyEq hlocal
  have hvalue := classicalGalerkinSmoothWordRhsJointPath_apply
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
      ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩ xT
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩
  let b := AVenhance.streamVel φ t
  let q : Vec 2 → ℝ := fun y => F t y + κ * AVenhance.spaceLap u y -
    classicalTransport b u y
  have huper : AVenhance.IsZ2Periodic u :=
    classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z y
    change AVenhance.streamVel φ t (y + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z t y
  have hlapper : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceLap u y) := by
    intro z y
    simp only [AVenhance.spaceLap]
    apply Finset.sum_congr rfl
    intro i hi
    exact AVenhance.Infra.Classical.periodic_spaceGrad_component
      (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i) i z y
  have htransportper : AVenhance.IsZ2Periodic (classicalTransport b u) := by
    intro z y
    unfold classicalTransport
    simp only [Homogenization.vecDot]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      b (y + AVenhance.latticeShift z) i * AVenhance.spaceGrad u
          (y + AVenhance.latticeShift z) i =
          b y i * AVenhance.spaceGrad u (y + AVenhance.latticeShift z) i := by
            rw [congrFun (hbper z y) i]
      _ = b y i * AVenhance.spaceGrad u y i := by
            exact congrArg (fun a : ℝ => b y i * a)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i z y)
  have hqper : AVenhance.IsZ2Periodic q := by
    intro z y
    dsimp [q]
    rw [hFper t (le_of_lt ht.1) z y]
    have hlap := hlapper z y
    have htr := htransportper z y
    change AVenhance.spaceLap u (y + AVenhance.latticeShift z) =
      AVenhance.spaceLap u y at hlap
    change classicalTransport b u (y + AVenhance.latticeShift z) =
      classicalTransport b u y at htr
    rw [hlap, htr]
  have hqwordper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w q hqper
  have hqrep := congrFun (fromUnitTorus_periodicToTorus
    (isZdPeriodic_iff_frozen _ |>.2 hqwordper)) x
  have hqrep' : classicalWordDerivative w q (unitTorusRepresentative 2 xT) =
      classicalWordDerivative w q x := by
    simpa [fromUnitTorus, periodicToTorus, xT] using hqrep
  have hderivValue : (ev (R ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩)).re =
      classicalWordDerivative w (fun y => F t y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y -
        classicalTransport (AVenhance.streamVel φ t)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨t, le_of_lt ht.1, le_of_lt ht.2⟩) y) x := by
    change (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (⟨t, le_of_lt ht.1, le_of_lt ht.2⟩, xT)).re = _
    rw [hvalue]
    simpa [q, u, b] using hqrep'
  have hfinal := htransfer.congr_deriv hderivValue
  simpa [U, R, cl, ev] using hfinal

/-- Right time differentiability at the initial boundary for every spatial word, as a torus-valued
path. -/
theorem classicalGalerkinWordPath_hasDerivWithinAt_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) :
    HasDerivWithinAt
      (fun s => (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry (classicalGalerkinUnitSlabClamp s))
      ((classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per w).curry ⟨0, by norm_num, by norm_num⟩) (Ici 0) 0 := by
  let U := (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let R := (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  have hcl : Continuous cl :=
      GalerkinSmoothWordEquation.classicalWordEquation_continuousUnitSlabClamp
  have hRcont : Continuous (fun s => R (cl s)) := R.continuous.comp hcl
  have hRint : IntervalIntegrable (fun s => R (cl s)) volume 0 0 :=
    hRcont.intervalIntegrable 0 0
  have hprimitive : HasDerivWithinAt
    (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r))
      (R (cl 0)) (Ici 0) 0 := by
    have hprimitive' := intervalIntegral.integral_hasDerivWithinAt_right
      (s := Ici (0 : ℝ)) (t := Ioi (0 : ℝ)) hRint
      hRcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hRcont.continuousAt.continuousWithinAt
    exact hprimitive'.const_add (U 0)
  have hsmall : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < 1 := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlocal : (fun s => U (cl s)) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
      (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r)) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs1
    have hs : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨hs0, le_of_lt hs1⟩
    have hs0' : (0 : ℝ) ≤ s := hs0
    have hclamp : cl s = ⟨s, hs⟩ := by
      apply Subtype.ext
      simp [cl, classicalGalerkinUnitSlabClamp, max_eq_right hs0',
        min_eq_right (le_of_lt hs1)]
    rw [hclamp]
    simpa [U, R, cl] using classicalGalerkinWordPath_integral_eq
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w ⟨s, hs⟩
  have hpoint : U (cl 0) = U 0 + ∫ r in (0 : ℝ)..(0 : ℝ), R (cl r) := by
    simp [cl, classicalGalerkinUnitSlabClamp]
  have hresult := hprimitive.congr_of_eventuallyEq hlocal hpoint
  have hcl0 : cl 0 = ⟨0, by norm_num, by norm_num⟩ := by
    apply Subtype.ext
    simp [cl, classicalGalerkinUnitSlabClamp]
  have hfinal := hresult.congr_deriv (congrArg R hcl0)
  simpa [U, R, cl] using hfinal

/-- Pointwise right time differentiability at the initial boundary, with the derivative given by
the physical right-hand side. -/
theorem classicalGalerkinWordPointwise_hasDerivWithinAt_zero
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2)) (x : Vec 2) :
    HasDerivWithinAt
      (fun s => classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (classicalGalerkinUnitSlabClamp s)) x)
      (classicalWordDerivative w (fun y => F 0 y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y -
        classicalTransport (AVenhance.streamVel φ 0)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y) x) (Ici 0) 0 := by
  let xT := toUnitTorus 2 x
  let U : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let R : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  let ev : C(UnitAddTorus (Fin 2), ℂ) →L[ℝ] ℂ := ContinuousMap.evalCLM ℝ xT
  have hpath := classicalGalerkinWordPath_hasDerivWithinAt_zero
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
  have hconstEv : HasDerivWithinAt (fun _ : ℝ => ev) 0 (Ici 0) 0 :=
    hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ici (0 : ℝ)) (c := ev)
  have hconstRe : HasDerivWithinAt (fun _ : ℝ => Complex.reCLM) 0 (Ici 0) 0 :=
    hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ici (0 : ℝ)) (c := Complex.reCLM)
  have heval := hconstEv.clm_apply hpath
  have hreal := hconstRe.clm_apply heval
  have hreal' : HasDerivWithinAt (fun s => (ev (U (cl s))).re)
      ((ev (R ⟨0, by norm_num, by norm_num⟩)).re) (Ici 0) 0 := by
    simpa [ev, U, R, ContinuousMap.evalCLM_apply] using hreal
  have hsmall : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < 1 := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlocal : (fun s => classicalWordDerivative w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s)) x) =ᶠ[𝓝[Ici (0 : ℝ)] 0]
      (fun s => (ev (U (cl s))).re) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs1
    have hpoint := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w (cl s) xT
    have hper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per (cl s))
      (classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s))
    have hrep := congrFun (fromUnitTorus_periodicToTorus
      (isZdPeriodic_iff_frozen _ |>.2 hper)) x
    have hrep' : classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (cl s)) (unitTorusRepresentative 2 xT) =
        classicalWordDerivative w
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per (cl s)) x := by
      simpa [fromUnitTorus, periodicToTorus, xT] using hrep
    have hpoint' := congrArg Complex.re hpoint
    rw [hrep'] at hpoint'
    simpa [U, ev, ContinuousMap.evalCLM_apply] using hpoint'.symm
  have hpoint :
      classicalWordDerivative w
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per (cl 0)) x = (ev (U (cl 0))).re := by
    obtain ⟨s, hs, hEq⟩ := hlocal.exists_mem
    rcases mem_nhdsWithin.mp hs with ⟨u, hu, h0u, hus⟩
    have h0s : (0 : ℝ) ∈ s := hus ⟨h0u, self_mem_Ici⟩
    exact hEq h0s
  have htransfer := hreal'.congr_of_eventuallyEq hlocal hpoint
  have hvalue := classicalGalerkinSmoothWordRhsJointPath_apply
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
      ⟨0, by norm_num, by norm_num⟩ xT
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩
  let b := AVenhance.streamVel φ 0
  let q : Vec 2 → ℝ := fun y => F 0 y + κ * AVenhance.spaceLap u y -
    classicalTransport b u y
  have huper : AVenhance.IsZ2Periodic u :=
    classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z y
    change AVenhance.streamVel φ 0 (y + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z 0 y
  have hlapper : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceLap u y) := by
    intro z y
    simp only [AVenhance.spaceLap]
    apply Finset.sum_congr rfl
    intro i hi
    exact AVenhance.Infra.Classical.periodic_spaceGrad_component
      (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i) i z y
  have htransportper : AVenhance.IsZ2Periodic (classicalTransport b u) := by
    intro z y
    unfold classicalTransport
    simp only [Homogenization.vecDot]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      b (y + AVenhance.latticeShift z) i * AVenhance.spaceGrad u
          (y + AVenhance.latticeShift z) i =
          b y i * AVenhance.spaceGrad u (y + AVenhance.latticeShift z) i := by
            rw [congrFun (hbper z y) i]
      _ = b y i * AVenhance.spaceGrad u y i := by
            exact congrArg (fun a : ℝ => b y i * a)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i z y)
  have hqper : AVenhance.IsZ2Periodic q := by
    intro z y
    dsimp [q]
    rw [hFper 0 (by norm_num) z y]
    have hlap := hlapper z y
    have htr := htransportper z y
    change AVenhance.spaceLap u (y + AVenhance.latticeShift z) =
      AVenhance.spaceLap u y at hlap
    change classicalTransport b u (y + AVenhance.latticeShift z) =
      classicalTransport b u y at htr
    rw [hlap, htr]
  have hqwordper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w q hqper
  have hqrep := congrFun (fromUnitTorus_periodicToTorus
    (isZdPeriodic_iff_frozen _ |>.2 hqwordper)) x
  have hqrep' : classicalWordDerivative w q (unitTorusRepresentative 2 xT) =
      classicalWordDerivative w q x := by
    simpa [fromUnitTorus, periodicToTorus, xT] using hqrep
  have hderivValue : (ev (R ⟨0, by norm_num, by norm_num⟩)).re =
      classicalWordDerivative w (fun y => F 0 y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y -
        classicalTransport (AVenhance.streamVel φ 0)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨0, by norm_num, by norm_num⟩) y) x := by
    change (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (⟨0, by norm_num, by norm_num⟩, xT)).re = _
    rw [hvalue]
    simpa [q, u, b] using hqrep'
  have hfinal := htransfer.congr_deriv hderivValue
  simpa [U, R, cl, ev] using hfinal

/-- The torus right-hand-side path agrees with the Euclidean periodic formula at every spatial
point, including the canonical representative boundary. -/
theorem classicalGalerkinSmoothWordRhsJointPath_apply_toEuclidean
    (φ : ℝ → Vec 2 → ℝ) (hφ : AVenhance.IsAdmissibleStream φ)
    (κ : ℝ) (hκ : 0 < κ) (F : ℝ → Vec 2 → ℝ)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (Function.uncurry F)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ))
    (hFper : ∀ t, 0 ≤ t → AVenhance.IsZ2Periodic (F t))
    (θ₀ : Vec 2 → ℝ) (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀)
    (hθ₀per : AVenhance.IsZ2Periodic θ₀) (w : List (Fin 2))
    (t : Icc (0 : ℝ) 1) (x : Vec 2) :
    classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (t, toUnitTorus 2 x) =
      (classicalWordDerivative w (fun y => F t y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t) y -
        classicalTransport (AVenhance.streamVel φ t)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per t) y) x : ℂ) := by
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per t
  let b := AVenhance.streamVel φ t
  let q : Vec 2 → ℝ := fun y => F t y + κ * AVenhance.spaceLap u y -
    classicalTransport b u y
  have huper : AVenhance.IsZ2Periodic u :=
    classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per t
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z y
    change AVenhance.streamVel φ t (y + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z t y
  have hlapper : AVenhance.IsZ2Periodic (fun y => AVenhance.spaceLap u y) := by
    intro z y
    simp only [AVenhance.spaceLap]
    apply Finset.sum_congr rfl
    intro i hi
    exact AVenhance.Infra.Classical.periodic_spaceGrad_component
      (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i) i z y
  have htransportper : AVenhance.IsZ2Periodic (classicalTransport b u) := by
    intro z y
    unfold classicalTransport
    simp only [Homogenization.vecDot]
    apply Finset.sum_congr rfl
    intro i hi
    calc
      b (y + AVenhance.latticeShift z) i * AVenhance.spaceGrad u
          (y + AVenhance.latticeShift z) i =
          b y i * AVenhance.spaceGrad u (y + AVenhance.latticeShift z) i := by
            rw [congrFun (hbper z y) i]
      _ = b y i * AVenhance.spaceGrad u y i := by
            exact congrArg (fun a : ℝ => b y i * a)
              (AVenhance.Infra.Classical.periodic_spaceGrad_component huper i z y)
  have hqper : AVenhance.IsZ2Periodic q := by
    intro z y
    dsimp [q]
    rw [hFper t t.property.1 z y]
    have hlap := hlapper z y
    have htr := htransportper z y
    change AVenhance.spaceLap u (y + AVenhance.latticeShift z) =
      AVenhance.spaceLap u y at hlap
    change classicalTransport b u (y + AVenhance.latticeShift z) =
      classicalTransport b u y at htr
    rw [hlap, htr]
  have hqwordper := GalerkinSmoothWordEquation.classicalSmoothWordPeriodic w q hqper
  have hqrep := congrFun (fromUnitTorus_periodicToTorus
    (isZdPeriodic_iff_frozen _ |>.2 hqwordper)) x
  have hqrep' : classicalWordDerivative w q
      (unitTorusRepresentative 2 (toUnitTorus 2 x)) =
    classicalWordDerivative w q x := by
    simpa [fromUnitTorus, periodicToTorus] using hqrep
  have hvalue := classicalGalerkinSmoothWordRhsJointPath_apply
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w t (toUnitTorus 2 x)
  rw [hvalue]
  simpa [q, u, b] using hqrep'

end AVenhance.Infra.Classical

end
