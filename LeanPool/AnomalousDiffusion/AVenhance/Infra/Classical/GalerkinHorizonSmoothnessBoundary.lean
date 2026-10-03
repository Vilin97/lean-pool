/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Partial

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Classical.GalerkinHorizonSmoothness

/-! # Galerkin Horizon Smoothness Boundary

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

noncomputable section
open MeasureTheory Set Filter Topology Homogenization AVenhance.Infra.Torus

namespace AVenhance.Infra.Classical

theorem GalerkinHorizonSmoothnessBoundary.classicalBoundaryWordPeriodic (w : List (Fin 2))
    (u : Vec 2 → ℝ) (hper : AVenhance.IsZ2Periodic u) :
    AVenhance.IsZ2Periodic (classicalWordDerivative w u) := by
  induction w with
  | nil => exact hper
  | cons i w ih => exact AVenhance.Infra.Classical.periodic_spaceGrad_component ih i

/-- The integrated word equation also gives the left time derivative at the terminal edge of the
unit slab. -/
theorem classicalGalerkinWordPath_hasDerivWithinAt_one
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
        θ₀ hθ₀ hθ₀per w).curry ⟨1, by norm_num, by norm_num⟩) (Iic 1) 1 := by
  let U := (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let R := (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per w).curry
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  have hcl : Continuous cl := by
    exact Continuous.subtype_mk
      (continuous_const.max (continuous_const.min continuous_id))
      (fun s => ⟨le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩)
  have hRcont : Continuous (fun s => R (cl s)) := R.continuous.comp hcl
  have hRint : IntervalIntegrable (fun s => R (cl s)) volume 0 1 :=
    hRcont.intervalIntegrable 0 1
  have hprimitive : HasDerivWithinAt
      (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r))
      (R (cl 1)) (Iic 1) 1 := by
    have hprimitive' := intervalIntegral.integral_hasDerivWithinAt_right
      (s := Iic (1 : ℝ)) (t := Iic (1 : ℝ)) hRint
      hRcont.aestronglyMeasurable.stronglyMeasurableAtFilter
      hRcont.continuousAt.continuousWithinAt
    exact hprimitive'.const_add (U 0)
  have hsmall : ∀ᶠ s in 𝓝[Iic (1 : ℝ)] 1, 0 < s := by
    exact Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlocal : (fun s => U (cl s)) =ᶠ[𝓝[Iic (1 : ℝ)] 1]
      (fun s => U 0 + ∫ r in (0 : ℝ)..s, R (cl r)) := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with s hs1 hs0
    change s ≤ 1 at hs1
    change 0 < s at hs0
    have hs : (s : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_of_lt hs0, hs1⟩
    have hclamp : cl s = ⟨s, hs⟩ := by
      apply Subtype.ext
      simp [cl, classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hs0),
        min_eq_right hs1]
    rw [hclamp]
    simpa [U, R, cl] using classicalGalerkinWordPath_integral_eq
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w ⟨s, hs⟩
  have hpoint : U (cl 1) = U 0 + ∫ r in (0 : ℝ)..(1 : ℝ), R (cl r) := by
    have hclamp : cl 1 = (1 : Icc (0 : ℝ) 1) := by
      apply Subtype.ext
      simp [cl, classicalGalerkinUnitSlabClamp]
    rw [hclamp]
    simpa [U, R, cl] using classicalGalerkinWordPath_integral_eq
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w (1 : Icc (0 : ℝ) 1)
  have hresult := hprimitive.congr_of_eventuallyEq hlocal hpoint
  have hcl1 : cl 1 = ⟨1, by norm_num, by norm_num⟩ := by
    apply Subtype.ext
    simp [cl, classicalGalerkinUnitSlabClamp]
  have hfinal := hresult.congr_deriv (congrArg R hcl1)
  simpa [U, R, cl] using hfinal

/-- Pointwise form of the terminal-edge derivative for the real periodic representative. -/
theorem classicalGalerkinWordPointwise_hasDerivWithinAt_one
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
      (classicalWordDerivative w (fun y => F 1 y + κ * AVenhance.spaceLap
        (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
          θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩) y -
        classicalTransport (AVenhance.streamVel φ 1)
          (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
            θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩) y) x)
      (Iic 1) 1 := by
  let xT := toUnitTorus 2 x
  let U : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinWordFourierContinuousPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let R : Icc (0 : ℝ) 1 → C(UnitAddTorus (Fin 2), ℂ) := fun s =>
    (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w).curry s
  let cl : ℝ → Icc (0 : ℝ) 1 := classicalGalerkinUnitSlabClamp
  let ev : C(UnitAddTorus (Fin 2), ℂ) →L[ℝ] ℂ := ContinuousMap.evalCLM ℝ xT
  have hpath := classicalGalerkinWordPath_hasDerivWithinAt_one
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
  have hconstEv : HasDerivWithinAt (fun _ : ℝ => ev) 0 (Iic 1) 1 :=
    hasDerivWithinAt_const (x := (1 : ℝ)) (s := Iic 1) (c := ev)
  have hconstRe : HasDerivWithinAt (fun _ : ℝ => Complex.reCLM) 0 (Iic 1) 1 :=
    hasDerivWithinAt_const (x := (1 : ℝ)) (s := Iic 1) (c := Complex.reCLM)
  have heval := hconstEv.clm_apply hpath
  have hreal := hconstRe.clm_apply heval
  have hreal' : HasDerivWithinAt (fun s => (ev (U (cl s))).re)
      ((ev (R ⟨1, by norm_num, by norm_num⟩)).re) (Iic 1) 1 := by
    simpa [ev, U, R, cl, ContinuousMap.evalCLM_apply] using hreal
  have hlocal : (fun s => classicalWordDerivative w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s)) x) =ᶠ[𝓝[Iic (1 : ℝ)] 1]
      (fun s => (ev (U (cl s))).re) := by
    filter_upwards [] with s
    have hpoint := classicalGalerkinWordFourierContinuousPath_eq_smoothDerivative
      φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w (cl s) xT
    have hper := GalerkinHorizonSmoothnessBoundary.classicalBoundaryWordPeriodic w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl s))
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
  have hpoint : classicalWordDerivative w
      (classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
        θ₀ hθ₀ hθ₀per (cl 1)) x = (ev (U (cl 1))).re := by
    obtain ⟨s, hs, hEq⟩ := hlocal.exists_mem
    rcases mem_nhdsWithin.mp hs with ⟨u, hu, h1u, hus⟩
    have h1s : (1 : ℝ) ∈ s := hus ⟨h1u, self_mem_Iic⟩
    exact hEq h1s
  have htransfer := hreal'.congr_of_eventuallyEq hlocal hpoint
  have hvalue := classicalGalerkinSmoothWordRhsJointPath_apply
    φ hφ κ hκ F hF hFper θ₀ hθ₀ hθ₀per w
      ⟨1, by norm_num, by norm_num⟩ xT
  let u := classicalGalerkinRealSmoothLift φ hφ κ hκ F hF hFper
    θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩
  let b := AVenhance.streamVel φ 1
  let q : Vec 2 → ℝ := fun y => F 1 y + κ * AVenhance.spaceLap u y -
    classicalTransport b u y
  have huper : AVenhance.IsZ2Periodic u :=
    classicalGalerkinRealSmoothLift_periodic φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per ⟨1, by norm_num, by norm_num⟩
  have hbper : AVenhance.IsZ2Periodic b := by
    intro z y
    change AVenhance.streamVel φ 1 (y + AVenhance.latticeShift z) = _
    simpa [b] using (streamVel_smoothPeriodic φ hφ).periodic 0 z 1 y
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
    rw [hFper 1 (by norm_num) z y]
    have hlap := hlapper z y
    have htr := htransportper z y
    change AVenhance.spaceLap u (y + AVenhance.latticeShift z) =
      AVenhance.spaceLap u y at hlap
    change classicalTransport b u (y + AVenhance.latticeShift z) =
      classicalTransport b u y at htr
    rw [hlap, htr]
  have hqwordper := GalerkinHorizonSmoothnessBoundary.classicalBoundaryWordPeriodic w q hqper
  have hqrep := congrFun (fromUnitTorus_periodicToTorus
    (isZdPeriodic_iff_frozen _ |>.2 hqwordper)) x
  have hqrep' : classicalWordDerivative w q (unitTorusRepresentative 2 xT) =
      classicalWordDerivative w q x := by
    simpa [fromUnitTorus, periodicToTorus, xT] using hqrep
  have hderivValue : (ev (R ⟨1, by norm_num, by norm_num⟩)).re =
      classicalWordDerivative w (fun y => F 1 y + κ * AVenhance.spaceLap u y -
        classicalTransport b u y) x := by
    change (classicalGalerkinSmoothWordRhsJointPath φ hφ κ hκ F hF hFper
      θ₀ hθ₀ hθ₀per w (⟨1, by norm_num, by norm_num⟩, xT)).re = _
    rw [hvalue]
    simpa [q, u, b] using hqrep'
  have hfinal := htransfer.congr_deriv hderivValue
  simpa [U, R, cl, ev, u, b] using hfinal

/-- Continue a unit-slab solution linearly using its endpoint equation values. -/
def classicalClosedSlabWordExtension
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : ℝ :=
  f w (classicalGalerkinUnitSlabClamp p.1, p.2) +
    q w (0, p.2) * min p.1 0 + q w (1, p.2) * max (p.1 - 1) 0

/-- Differentiate the endpoint extension along its time slices. -/
theorem classicalClosedSlabWordExtension_hasDerivAt
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (hinterior : ∀ w x t, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s => f w (s, x)) (q w (t, x)) t)
    (hzero : ∀ w x, HasDerivWithinAt (fun s => f w (s, x))
      (q w (0, x)) (Ici 0) 0)
    (hone : ∀ w x, HasDerivWithinAt (fun s => f w (s, x))
      (q w (1, x)) (Iic 1) 1) :
    ∀ w x t, HasDerivAt
      (fun s => classicalClosedSlabWordExtension f q w (s, x))
      (q w (classicalGalerkinUnitSlabClamp t, x)) t := by
  intro w x t
  by_cases hneg : t < 0
  · have hlocal : (fun s => classicalClosedSlabWordExtension f q w (s, x)) =ᶠ[𝓝 t]
        (fun s => f w (0, x) + q w (0, x) * s) := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      change s < 0 at hs
      simp [classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp,
        max_eq_left (le_of_lt hs), min_eq_right (le_of_lt (by linarith : s < 1)),
        min_eq_left (le_of_lt hs), max_eq_right (by linarith : s - 1 ≤ 0)]
    have hlin : HasDerivAt (fun s : ℝ => f w (0, x) + q w (0, x) * s)
        (q w (0, x)) t := by
      exact (hasDerivAt_const_mul (q w (0, x)) (x := t)).const_add
        (f w (0, x))
    have hderiv := hlin.congr_of_eventuallyEq hlocal
    have hcl : classicalGalerkinUnitSlabClamp t = ⟨0, by norm_num, by norm_num⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, max_eq_left (le_of_lt hneg),
        min_eq_right (le_of_lt (lt_trans hneg (by norm_num : (0 : ℝ) < 1)))]
    simpa [hcl] using hderiv
  · by_cases hzeroTime : t = 0
    · subst t
      let g : ℝ → ℝ := fun s => classicalClosedSlabWordExtension f q w (s, x)
      have hleft : HasDerivWithinAt g (q w (0, x)) (Iic 0) 0 := by
        have hlin : HasDerivWithinAt
            (fun s => f w (0, x) + q w (0, x) * s)
            (q w (0, x)) (Iic 0) 0 :=
          ((hasDerivAt_const_mul (q w (0, x))).const_add (f w (0, x))).hasDerivWithinAt
        apply hlin.congr
        · intro s hs
          change s ≤ 0 at hs
          simp [g, classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp,
            max_eq_left hs, min_eq_right (le_trans hs (by norm_num : (0 : ℝ) ≤ 1)),
            min_eq_left hs, max_eq_right (by linarith : s - 1 ≤ 0)]
        · simp [g, classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp]
      have hsmall : ∀ᶠ s in 𝓝[Ici (0 : ℝ)] 0, s < 1 := by
        exact Filter.Eventually.filter_mono inf_le_left
          (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
      have hlocal : g =ᶠ[𝓝[Ici (0 : ℝ)] 0] (fun s => f w (s, x)) := by
        filter_upwards [self_mem_nhdsWithin, hsmall] with s hs0 hs1
        change 0 ≤ s at hs0
        have hcl : classicalGalerkinUnitSlabClamp s = ⟨s, hs0, le_of_lt hs1⟩ := by
          apply Subtype.ext
          simp [classicalGalerkinUnitSlabClamp, max_eq_right hs0,
            min_eq_right (le_of_lt hs1)]
        simp [g, classicalClosedSlabWordExtension, hcl,
          min_eq_right hs0, max_eq_right (by linarith : s - 1 ≤ 0)]
      have hright := (hzero w x).congr_of_eventuallyEq hlocal (by
        simp [g, classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp])
      have hderiv := classicalHasDerivAt_of_within_Iic_Ici hleft hright
      have hcl : (classicalGalerkinUnitSlabClamp 0 : ℝ) = 0 := by
        simp [classicalGalerkinUnitSlabClamp]
      simpa [g, hcl] using hderiv
    · have hpos : 0 < t := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzeroTime)
      by_cases hgt : 1 < t
      · have hlocal : (fun s => classicalClosedSlabWordExtension f q w (s, x)) =ᶠ[𝓝 t]
            (fun s => f w (1, x) + q w (1, x) * (s - 1)) := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          change 1 < s at hs
          have hcl : classicalGalerkinUnitSlabClamp s = ⟨1, by norm_num, by norm_num⟩ := by
            apply Subtype.ext
            simp [classicalGalerkinUnitSlabClamp, min_eq_left (le_of_lt hs)]
          simp [classicalClosedSlabWordExtension, hcl,
            min_eq_right (le_of_lt (by linarith : (0 : ℝ) < s)),
            max_eq_left (by linarith : 0 ≤ s - 1)]
        have hid := (hasDerivAt_id t).sub_const 1
        have hlin := (hid.const_mul (q w (1, x))).const_add (f w (1, x))
        have hderiv := hlin.congr_of_eventuallyEq hlocal
        have hcl : classicalGalerkinUnitSlabClamp t = ⟨1, by norm_num, by norm_num⟩ := by
          apply Subtype.ext
          simp [classicalGalerkinUnitSlabClamp, le_of_lt hgt]
        simpa [hcl] using hderiv
      · by_cases honeTime : t = 1
        · subst t
          let g : ℝ → ℝ := fun s => classicalClosedSlabWordExtension f q w (s, x)
          have hsmall : ∀ᶠ s in 𝓝[Iic (1 : ℝ)] 1, 0 < s := by
            exact Filter.Eventually.filter_mono inf_le_left
              (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
          have hlocal : g =ᶠ[𝓝[Iic (1 : ℝ)] 1] (fun s => f w (s, x)) := by
            filter_upwards [self_mem_nhdsWithin, hsmall] with s hs1 hs0
            change s ≤ 1 at hs1
            change 0 < s at hs0
            have hcl : classicalGalerkinUnitSlabClamp s = ⟨s, le_of_lt hs0, hs1⟩ := by
              apply Subtype.ext
              simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hs0),
                min_eq_right hs1]
            simp [g, classicalClosedSlabWordExtension, hcl,
              min_eq_right (le_of_lt hs0), max_eq_right (sub_nonpos.mpr hs1)]
          have hleft := (hone w x).congr_of_eventuallyEq hlocal (by
            simp [g, classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp])
          have hright : HasDerivWithinAt g (q w (1, x)) (Ici 1) 1 := by
            have hid := (hasDerivAt_id (1 : ℝ)).sub_const 1
            have hlin : HasDerivWithinAt
                (fun s => f w (1, x) + q w (1, x) * (s - 1))
                (q w (1, x)) (Ici 1) 1 := by
              simpa using ((hid.const_mul (q w (1, x))).const_add
                (f w (1, x))).hasDerivWithinAt
            apply hlin.congr
            · intro s hs
              change 1 ≤ s at hs
              have hcl : classicalGalerkinUnitSlabClamp s = ⟨1, by norm_num, by norm_num⟩ := by
                apply Subtype.ext
                simp [classicalGalerkinUnitSlabClamp, min_eq_left hs]
              simp [g, classicalClosedSlabWordExtension, hcl,
                min_eq_right (le_trans (by norm_num : (0 : ℝ) ≤ 1) hs),
                max_eq_left (by linarith : 0 ≤ s - 1)]
            · simp [g, classicalClosedSlabWordExtension, classicalGalerkinUnitSlabClamp]
          have hderiv := classicalHasDerivAt_of_within_Iic_Ici hleft hright
          have hcl : (classicalGalerkinUnitSlabClamp 1 : ℝ) = 1 := by
            simp [classicalGalerkinUnitSlabClamp]
          simpa [g, hcl] using hderiv
        · have hlt1 : t < 1 := lt_of_le_of_ne (le_of_not_gt hgt) honeTime
          have hmid : t ∈ Ioo (0 : ℝ) 1 := ⟨hpos, hlt1⟩
          have hlocal : (fun s => classicalClosedSlabWordExtension f q w (s, x)) =ᶠ[𝓝 t]
              (fun s => f w (s, x)) := by
            filter_upwards [Ioo_mem_nhds hmid.1 hmid.2] with s hs
            change 0 < s ∧ s < 1 at hs
            rcases hs with ⟨hs0, hs1⟩
            have hcl : classicalGalerkinUnitSlabClamp s = ⟨s, le_of_lt hs0, le_of_lt hs1⟩ := by
              apply Subtype.ext
              simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hs0),
                min_eq_right (le_of_lt hs1)]
            simp [classicalClosedSlabWordExtension, hcl,
              min_eq_right (le_of_lt hs0), max_eq_right (by linarith : s - 1 ≤ 0)]
          have hderiv := (hinterior w x t hmid).congr_of_eventuallyEq hlocal
          have hcl : classicalGalerkinUnitSlabClamp t = ⟨t, le_of_lt hpos, le_of_lt hlt1⟩ := by
            apply Subtype.ext
            simp [classicalGalerkinUnitSlabClamp, max_eq_right (le_of_lt hpos),
              min_eq_right (le_of_lt hlt1)]
          simpa [hcl] using hderiv

/-- The spatial coefficient of the derivative of the linearly extended word. -/
def classicalClosedSlabWordExtensionSpaceCoeff
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (w : List (Fin 2)) (i : Fin 2) (p : ℝ × Vec 2) : ℝ :=
  f (i :: w) (classicalGalerkinUnitSlabClamp p.1, p.2) +
    q (i :: w) (0, p.2) * min p.1 0 +
    q (i :: w) (1, p.2) * max (p.1 - 1) 0

/-- Spatial differential assembled from the coordinate derivatives of a word extension. -/
def GalerkinHorizonSmoothnessBoundary.classicalClosedSlabWordExtensionSpaceCLM
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (w : List (Fin 2)) (p : ℝ × Vec 2) : Vec 2 →L[ℝ] ℝ :=
  ∑ i : Fin 2, classicalClosedSlabWordExtensionSpaceCoeff f q w i p •
    (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)

/-- Assemble the equation derivative and all coordinate derivatives into the full derivative
within the closed unit slab. -/
theorem classicalSpatialWordFamily_hasFDerivWithinAt
    (S : Set (ℝ × Vec 2)) (hS : S = Icc (0 : ℝ) 1 ×ˢ univ)
    (f q : List (Fin 2) → ℝ × Vec 2 → ℝ)
    (hcontinuousF : ∀ w, Continuous (f w))
    (hcontinuousQ : ∀ w, Continuous (q w))
    (hinterior : ∀ w x t, t ∈ Ioo (0 : ℝ) 1 →
      HasDerivAt (fun s => f w (s, x)) (q w (t, x)) t)
    (hzero : ∀ w x, HasDerivWithinAt (fun s => f w (s, x))
      (q w (0, x)) (Ici 0) 0)
    (hone : ∀ w x, HasDerivWithinAt (fun s => f w (s, x))
      (q w (1, x)) (Iic 1) 1)
    (hspaceF : ∀ w t x, HasFDerivAt (fun y => f w (t, y))
      (∑ i : Fin 2, f (i :: w) (t, x) •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x)
    (hspaceQ : ∀ w t x, HasFDerivAt (fun y => q w (t, y))
      (∑ i : Fin 2, q (i :: w) (t, x) •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) x) :
    ∀ w p, p ∈ S → HasFDerivWithinAt (f w)
      (classicalSpatialWordDerivativeLinearMap f q w p) S p := by
  intro w p hp
  rcases p with ⟨t, x⟩
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    rw [hS] at hp
    exact hp.1
  let E : ℝ × Vec 2 → ℝ := classicalClosedSlabWordExtension f q w
  let Dt : ℝ × Vec 2 → ℝ →L[ℝ] ℝ := fun z =>
    ContinuousLinearMap.toSpanSingleton ℝ (q w (classicalGalerkinUnitSlabClamp z.1, z.2))
  let Dx : ℝ × Vec 2 → Vec 2 →L[ℝ] ℝ :=
    GalerkinHorizonSmoothnessBoundary.classicalClosedSlabWordExtensionSpaceCLM f q w
  have hc : Continuous classicalGalerkinUnitSlabClamp := by
    exact Continuous.subtype_mk
      (continuous_const.max (continuous_const.min continuous_id))
      (fun s => ⟨le_max_left _ _, (max_le_iff).2 ⟨by norm_num, min_le_left _ _⟩⟩)
  have hclMap : Continuous (fun z : ℝ × Vec 2 =>
      ((classicalGalerkinUnitSlabClamp z.1 : ℝ), z.2)) :=
    ((continuous_subtype_val.comp (hc.comp continuous_fst)).prodMk continuous_snd)
  have hDt : Continuous Dt := by
    exact (ContinuousLinearMap.toSpanSingletonCLE (𝕜 := ℝ) (E := ℝ)).continuous.comp
      ((hcontinuousQ w).comp hclMap)
  have hDx : Continuous Dx := by
    change Continuous (fun z => ∑ i : Fin 2,
      classicalClosedSlabWordExtensionSpaceCoeff f q w i z •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ))
    apply continuous_finsetSum Finset.univ
    intro i hi
    have hcoeff : Continuous (fun z : ℝ × Vec 2 =>
        f (i :: w) (classicalGalerkinUnitSlabClamp z.1, z.2) +
          q (i :: w) (0, z.2) * min z.1 0 +
          q (i :: w) (1, z.2) * max (z.1 - 1) 0) := by
      fun_prop
    exact hcoeff.smul continuous_const
  have htime : ∀ᶠ z : ℝ × Vec 2 in 𝓝 (t, x),
      HasFDerivAt (fun s => E (s, z.2)) (Dt z) z.1 := by
    filter_upwards [] with z
    have h := classicalClosedSlabWordExtension_hasDerivAt f q
      hinterior hzero hone w z.2 z.1
    simpa [E, Dt] using h.hasFDerivAt
  have hspace : ∀ᶠ z : ℝ × Vec 2 in 𝓝 (t, x),
      HasFDerivAt (fun y => E (z.1, y)) (Dx z) z.2 := by
    filter_upwards [] with z
    let cl := classicalGalerkinUnitSlabClamp z.1
    have hbase := hspaceF w cl z.2
    have hleft := hspaceQ w (0 : ℝ) z.2
    have hright := hspaceQ w (1 : ℝ) z.2
    have hsum := hbase.add (hleft.const_smul (min z.1 0))
      |>.add (hright.const_smul (max (z.1 - 1) 0))
    have hD : Dx z =
        (∑ i : Fin 2, f (i :: w) (cl, z.2) •
          (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) +
          (min z.1 0) • (∑ i : Fin 2, q (i :: w) (0, z.2) •
            (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) +
          (max (z.1 - 1) 0) • (∑ i : Fin 2, q (i :: w) (1, z.2) •
            (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ)) := by
      apply ContinuousLinearMap.ext
      intro v
      simp [Dx, GalerkinHorizonSmoothnessBoundary.classicalClosedSlabWordExtensionSpaceCLM,
        classicalClosedSlabWordExtensionSpaceCoeff, smul_eq_mul, mul_comm]; ring
    have hsum' := hsum.congr_fderiv hD.symm
    have hfunc : (fun y => E (z.1, y)) =
        (fun y => f w (cl, y) + (min z.1 0) • q w (0, y) +
          (max (z.1 - 1) 0) • q w (1, y)) := by
      funext y
      simp [E, cl, classicalClosedSlabWordExtension, smul_eq_mul, mul_comm]
    rw [hfunc]
    exact hsum'
  have hstrict := hasStrictFDerivAt_uncurry_coprod (𝕜 := ℝ)
    (f := fun s y => E (s, y))
    (f₁ := fun s y => Dt (s, y)) (f₂ := fun s y => Dx (s, y)) htime hspace
    (by convert hDt.continuousAt using 1; rfl)
    (by convert hDx.continuousAt using 1; rfl)
  have hglobal := hstrict.hasFDerivAt
  have hEq : Set.EqOn E (f w) S := by
    intro z hz
    rw [hS] at hz
    have hcl : classicalGalerkinUnitSlabClamp z.1 = ⟨z.1, hz.1.1, hz.1.2⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, max_eq_right hz.1.1,
        min_eq_right hz.1.2]
    simp [E, classicalClosedSlabWordExtension, hcl, min_eq_right hz.1.1,
      max_eq_right (by linarith [hz.1.2] : z.1 - 1 ≤ 0)]
  have hpoint : f w (t, x) = E (t, x) := (hEq hp).symm
  have hDtValue : Dt (t, x) = ContinuousLinearMap.toSpanSingleton ℝ (q w (t, x)) := by
    have hcl : classicalGalerkinUnitSlabClamp t = ⟨t, ht.1, ht.2⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, max_eq_right ht.1, min_eq_right ht.2]
    simp [Dt, hcl]
  have hDxValue : Dx (t, x) =
      ∑ i : Fin 2, f (i :: w) (t, x) •
        (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ) := by
    have hcl : classicalGalerkinUnitSlabClamp t = ⟨t, ht.1, ht.2⟩ := by
      apply Subtype.ext
      simp [classicalGalerkinUnitSlabClamp, max_eq_right ht.1, min_eq_right ht.2]
    simp [Dx, GalerkinHorizonSmoothnessBoundary.classicalClosedSlabWordExtensionSpaceCLM,
      classicalClosedSlabWordExtensionSpaceCoeff, hcl,
      min_eq_right ht.1, max_eq_right (by linarith [ht.2] : t - 1 ≤ 0)]
  have hmap : (Dt (t, x)).coprod (Dx (t, x)) =
      classicalSpatialWordDerivativeLinearMap f q w (t, x) := by
    apply ContinuousLinearMap.ext
    intro v
    rcases v with ⟨a, b⟩
    simp [classicalSpatialWordDerivativeLinearMap, hDtValue, hDxValue,
      ContinuousLinearMap.coprod_apply]
  have hwithin : HasFDerivWithinAt E
      ((Dt (t, x)).coprod (Dx (t, x))) S (t, x) :=
    hglobal.hasFDerivWithinAt
  have hsource := hwithin.congr hEq.symm hpoint
  exact hsource.congr_fderiv hmap

end AVenhance.Infra.Classical

end
