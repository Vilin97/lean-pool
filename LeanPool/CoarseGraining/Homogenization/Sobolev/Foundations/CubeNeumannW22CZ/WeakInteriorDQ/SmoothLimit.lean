/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.LimitPairing

/-! # Smooth Limit -/

namespace Homogenization

open scoped ENNReal Manifold

noncomputable section

/-- Pairing representatives in scalar `L²` agrees with the set integral of
the pointwise product. -/
theorem inner_toScalarL2_eq_integral_mul
    {d : ℕ} {U : Set (Vec d)} {F G : Vec d → ℝ}
    (hF : MemScalarL2 U F) (hG : MemScalarL2 U G) :
    inner ℝ (toScalarL2 hF) (toScalarL2 hG) =
      ∫ x in U, F x * G x ∂MeasureTheory.volume := by
  rw [scalarInner_eq_integral]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [coeFn_toScalarL2 hF, coeFn_toScalarL2 hG] with x hFx hGx
  rw [hFx, hGx]

/-- A fixed `L²` factor defines a continuous functional against convergent
scalar `L²` representatives. -/
theorem tendsto_integral_mul_of_tendsto_toScalarL2
    {d : ℕ} {U : Set (Vec d)} {ι : Type*} {l : Filter ι}
    {u : Vec d → ℝ} {F : ι → Vec d → ℝ} {G : Vec d → ℝ}
    (hu : MemScalarL2 U u) (hF : ∀ n, MemScalarL2 U (F n))
    (hG : MemScalarL2 U G)
    (hconv : Filter.Tendsto (fun n => toScalarL2 (hF n)) l (nhds (toScalarL2 hG))) :
    Filter.Tendsto
      (fun n => ∫ x in U, u x * F n x ∂MeasureTheory.volume) l
      (nhds (∫ x in U, u x * G x ∂MeasureTheory.volume)) := by
  have hinner :
      Filter.Tendsto
        (fun n => inner ℝ (toScalarL2 hu) (toScalarL2 (hF n))) l
        (nhds (inner ℝ (toScalarL2 hu) (toScalarL2 hG))) :=
    Filter.Tendsto.inner tendsto_const_nhds hconv
  simpa [inner_toScalarL2_eq_integral_mul] using hinner

/-- Raw `eLpNorm` convergence of representatives implies convergence of
their scalar `L²` classes. -/
theorem tendsto_toScalarL2_of_tendsto_eLpNorm
    {d : ℕ} {U : Set (Vec d)} {ι : Type*} {l : Filter ι}
    {F : ι → Vec d → ℝ} {G : Vec d → ℝ}
    (hF : ∀ n, MemScalarL2 U (F n)) (hG : MemScalarL2 U G)
    (hlim : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - G x) 2 (volumeMeasureOn U))
      l (nhds 0)) :
    Filter.Tendsto (fun n => toScalarL2 (hF n)) l (nhds (toScalarL2 hG)) := by
  have hlim_coe :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          (fun x => (toScalarL2 (hF n) : Vec d → ℝ) x - G x)
          2 (volumeMeasureOn U))
        l (nhds 0) := by
    have hEq :
        (fun n => MeasureTheory.eLpNorm
          (fun x => (toScalarL2 (hF n) : Vec d → ℝ) x - G x)
          2 (volumeMeasureOn U)) =
        fun n =>
          MeasureTheory.eLpNorm (fun x => F n x - G x) 2 (volumeMeasureOn U) := by
      funext n
      apply MeasureTheory.eLpNorm_congr_ae
      filter_upwards [coeFn_toScalarL2 (hF n)] with x hx
      rw [hx]
    rw [hEq]
    exact hlim
  simpa [toScalarL2] using
    (MeasureTheory.Lp.tendsto_Lp_of_tendsto_eLpNorm
      (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      (f := fun n => toScalarL2 (hF n)) (f_lim := G) (f_lim_ℒp := hG)
      hlim_coe)

/-- Convergence in scalar `L²` of explicit representatives implies raw
`eLpNorm` convergence of their pointwise differences. -/
theorem tendsto_eLpNorm_of_tendsto_toScalarL2
    {d : ℕ} {U : Set (Vec d)} {ι : Type*} {l : Filter ι}
    {F : ι → Vec d → ℝ} {G : Vec d → ℝ}
    (hF : ∀ n, MemScalarL2 U (F n)) (hG : MemScalarL2 U G)
    (hconv :
      Filter.Tendsto (fun n => toScalarL2 (hF n)) l (nhds (toScalarL2 hG))) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - G x) 2 (volumeMeasureOn U))
      l (nhds 0) := by
  have hed :
      Filter.Tendsto
        (fun n => edist (toScalarL2 (hF n)) (toScalarL2 hG)) l (nhds 0) :=
    tendsto_iff_edist_tendsto_0.mp hconv
  have hEq :
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - G x) 2 (volumeMeasureOn U)) =
        fun n => edist (toScalarL2 (hF n)) (toScalarL2 hG) := by
    funext n
    exact (MeasureTheory.Lp.edist_toLp_toLp (F n) G (hF n) hG).symm
  simpa [hEq] using hed

/-- On a finite-measure set, an `O(|h_n|)` pointwise bound forces the `L²`
seminorm to vanish when `h_n -> 0`. -/
theorem tendsto_eLpNorm_zero_of_ae_norm_le_mul_norm
    {d : ℕ} {U : Set (Vec d)} {F : ℕ → Vec d → ℝ}
    {stepSeq : ℕ → ℝ} {C : ℝ}
    (hUfinite : (volumeMeasureOn U) Set.univ ≠ ⊤)
    (hstep : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    (hbound : ∀ n, ∀ᵐ x ∂volumeMeasureOn U, ‖F n x‖ ≤ C * ‖stepSeq n‖) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F n) 2 (volumeMeasureOn U))
      Filter.atTop (nhds 0) := by
  let A : ℝ≥0∞ := (volumeMeasureOn U) Set.univ ^ ((2 : ℝ≥0∞).toReal⁻¹)
  have hA_ne_top : A ≠ ⊤ := by
    dsimp [A]
    refine (ENNReal.rpow_lt_top_of_nonneg (by positivity) ?_).ne
    exact hUfinite
  have hreal : Filter.Tendsto (fun n => C * ‖stepSeq n‖) Filter.atTop (nhds 0) := by
    simpa using hstep.norm.const_mul C
  have hOf :
      Filter.Tendsto (fun n => ENNReal.ofReal (C * ‖stepSeq n‖))
        Filter.atTop (nhds 0) := by
    simpa using ENNReal.tendsto_ofReal hreal
  have hupper :
      Filter.Tendsto (fun n => A * ENNReal.ofReal (C * ‖stepSeq n‖))
        Filter.atTop (nhds 0) := by
    simpa using
      (ENNReal.Tendsto.mul tendsto_const_nhds (Or.inr ENNReal.zero_ne_top) hOf
        (Or.inr hA_ne_top))
  refine Filter.Tendsto.squeeze tendsto_const_nhds hupper (fun n => ?_) (fun n => ?_)
  · exact bot_le
  · dsimp [A]
    exact MeasureTheory.eLpNorm_le_of_ae_bound (μ := volumeMeasureOn U)
      (p := (2 : ℝ≥0∞)) (hbound n)

namespace WeakPoissonEquationOn

variable {d : ℕ} {V : Set (Vec d)}

private theorem support_h1WeakTest_deriv_subset
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    Function.support (fun x => φ.deriv j x) ⊆ U := by
  intro x hx
  exact φ.support_subset <|
    (support_fderiv_subset (𝕜 := ℝ) (f := (φ : Vec d → ℝ))) <| by
      change fderiv ℝ (φ : Vec d → ℝ) x ≠ 0
      intro hzero
      apply hx
      simp [H1WeakTestFunction.deriv, hzero]

private theorem contDiff_h1WeakTest_deriv
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv, euclideanCoordDeriv] using!
    contDiff_euclideanCoordDeriv φ.smooth j

private theorem hasCompactSupport_h1WeakTest_deriv
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    HasCompactSupport (fun x => φ.deriv j x) := by
  simpa [H1WeakTestFunction.deriv] using
    φ.compactSupport.fderiv_apply (𝕜 := ℝ) (basisVec j)

private theorem tsupport_h1WeakTest_deriv_subset
    {U : Set (Vec d)} (φ : H1WeakTestFunction U) (j : Fin d) :
    tsupport (fun x => φ.deriv j x) ⊆ U := by
  have hsub :
      tsupport (euclideanCoordDeriv j (φ : Vec d → ℝ)) ⊆
        tsupport (φ : Vec d → ℝ) :=
    tsupport_euclideanCoordDeriv_subset_tsupport j (φ : Vec d → ℝ)
  simpa [H1WeakTestFunction.deriv, euclideanCoordDeriv] using!
    hsub.trans φ.support_subset

/-- Smooth test derivatives have `L²` backward difference quotients on any
restricted ambient set. -/
theorem memScalarL2_euclideanBackwardDifferenceQuotient_h1WeakTest_deriv
    {S U : Set (Vec d)} {step : ℝ}
    (φ : H1WeakTestFunction S) (i j : Fin d) :
    MemScalarL2 U
      (euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y)) := by
  have hcont :
      Continuous
        (euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y)) :=
    (contDiff_euclideanBackwardDifferenceQuotient
      (contDiff_h1WeakTest_deriv φ j) step i).continuous
  have hcompact :
      HasCompactSupport
        (euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y)) :=
    hasCompactSupport_euclideanBackwardDifferenceQuotient
      (hasCompactSupport_h1WeakTest_deriv φ j) step i
  simpa [MemScalarL2, volumeMeasureOn] using
    (hcont.memLp_of_hasCompactSupport hcompact).restrict U

/-- The classical second derivative of a smooth weak test is scalar `L²` on
any restricted ambient set. -/
theorem memScalarL2_fderiv_h1WeakTest_deriv_apply
    {S U : Set (Vec d)}
    (φ : H1WeakTestFunction S) (i j : Fin d) :
    MemScalarL2 U
      (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) := by
  have hcont :
      Continuous
        (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) :=
    ((contDiff_h1WeakTest_deriv φ j).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hcompact :
      HasCompactSupport
        (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) :=
    (hasCompactSupport_h1WeakTest_deriv φ j).fderiv_apply (𝕜 := ℝ) (basisVec i)
  simpa [MemScalarL2, volumeMeasureOn] using
    (hcont.memLp_of_hasCompactSupport hcompact).restrict U

private theorem support_backwardDifferenceQuotient_h1WeakTest_deriv_subset
    {S U V : Set (Vec d)} {step : ℝ} (i j : Fin d)
    (φ : H1WeakTestFunction S) (hSV : S ⊆ V) (hVU : V ⊆ U)
    (hVshift : ∀ x ∈ V, euclideanCoordShift step i x ∈ U) :
    Function.support
        (euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y))
        ⊆ U := by
  intro x hx
  by_cases hxderiv : φ.deriv j x = 0
  · have hpre_ne : φ.deriv j (euclideanCoordShift (-step) i x) ≠ 0 := by
      intro hpre_zero
      apply hx
      have hnum :
          φ.deriv j x - φ.deriv j (euclideanCoordShift (-step) i x) = 0 := by
        rw [hxderiv, hpre_zero, sub_self]
      rw [euclideanBackwardDifferenceQuotient_apply, hnum]
      simp
    have hpreS :
        euclideanCoordShift (-step) i x ∈ S :=
      support_h1WeakTest_deriv_subset φ j hpre_ne
    have hxU :
        euclideanCoordShift step i (euclideanCoordShift (-step) i x) ∈ U :=
      hVshift (euclideanCoordShift (-step) i x) (hSV hpreS)
    simpa using hxU
  · exact hVU (hSV (support_h1WeakTest_deriv_subset φ j hxderiv))

private theorem support_mul_backwardDifferenceQuotient_h1WeakTest_deriv_subset
    {S U V : Set (Vec d)} {u : Vec d → ℝ} {step : ℝ} (i j : Fin d)
    (φ : H1WeakTestFunction S) (hSV : S ⊆ V) (hVU : V ⊆ U)
    (hVshift : ∀ x ∈ V, euclideanCoordShift step i x ∈ U) :
    Function.support
        (fun x =>
          u x *
            euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y) x)
        ⊆ U :=
  (Function.support_mul_subset_right u
    (euclideanBackwardDifferenceQuotient step i (fun y => φ.deriv j y))).trans
    (support_backwardDifferenceQuotient_h1WeakTest_deriv_subset
      i j φ hSV hVU hVshift)

private theorem support_fderiv_h1WeakTest_deriv_apply_subset
    {S U : Set (Vec d)} (φ : H1WeakTestFunction S) (i j : Fin d)
    (hSU : S ⊆ U) :
    Function.support
        (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) ⊆ U := by
  intro x hx
  exact hSU <| tsupport_h1WeakTest_deriv_subset φ j <|
    (support_fderiv_subset (𝕜 := ℝ) (f := fun y => φ.deriv j y)) <| by
      change fderiv ℝ (fun y => φ.deriv j y) x ≠ 0
      intro hzero
      apply hx
      simp [hzero]

private theorem support_mul_fderiv_h1WeakTest_deriv_apply_subset
    {S U : Set (Vec d)} {u : Vec d → ℝ}
    (φ : H1WeakTestFunction S) (i j : Fin d) (hSU : S ⊆ U) :
    Function.support
        (fun x =>
          u x * (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)) ⊆ U :=
  (Function.support_mul_subset_right u
    (fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))).trans
    (support_fderiv_h1WeakTest_deriv_apply_subset φ i j hSU)

/-- `L²` convergence of the smooth backward quotients is enough to close the
open-inner Hessian pairing limit.  The remaining analytic input is now exactly
the classical statement that, for smooth compactly supported `φ`,
`D_i^- (∂_j φ) → ∂_i∂_j φ` in `L²(openCubeSet Q)`. -/
theorem openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_toScalarL2_tendsto
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q)
    (hback_l2 :
      ∀ φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁),
        Filter.Tendsto
          (fun n : ℕ =>
            toScalarL2
              (memScalarL2_euclideanBackwardDifferenceQuotient_h1WeakTest_deriv
                (U := openCubeSet Q) (step := stepSeq n) φ i j))
          Filter.atTop
          (nhds
            (toScalarL2
              (memScalarL2_fderiv_h1WeakTest_deriv_apply
                (U := openCubeSet Q) φ i j)))) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  refine
    openCubeInnerHessianPairingTendsto_of_integral_backwardDifferenceQuotient_deriv_tendsto
      uQ stepSeq i j hSV hVU hVshift ?_
  intro φ
  let U : Set (Vec d) := openCubeSet Q
  let F : ℕ → Vec d → ℝ := fun n =>
    euclideanBackwardDifferenceQuotient (stepSeq n) i (fun y => φ.deriv j y)
  let G : Vec d → ℝ := fun x =>
    (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
  have hu : MemScalarL2 U uQ.toFun := by
    simpa [U, MemScalarL2, volumeMeasureOn] using uQ.memL2
  have hF : ∀ n, MemScalarL2 U (F n) := by
    intro n
    simpa [F, U] using
      memScalarL2_euclideanBackwardDifferenceQuotient_h1WeakTest_deriv
        (U := openCubeSet Q) (step := stepSeq n) φ i j
  have hG : MemScalarL2 U G := by
    simpa [G, U] using
      memScalarL2_fderiv_h1WeakTest_deriv_apply (U := openCubeSet Q) φ i j
  have hset_lim :
      Filter.Tendsto
        (fun n => ∫ x in U, uQ.toFun x * F n x ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, uQ.toFun x * G x ∂MeasureTheory.volume)) := by
    exact tendsto_integral_mul_of_tendsto_toScalarL2 hu hF hG (by
      simpa [F, G, U] using hback_l2 φ)
  have hseq :
      (fun n : ℕ =>
          ∫ x, uQ.toFun x *
            euclideanBackwardDifferenceQuotient (stepSeq n) i
              (fun y => φ.deriv j y) x
            ∂MeasureTheory.volume) =
        fun n : ℕ =>
          ∫ x in U, uQ.toFun x * F n x ∂MeasureTheory.volume := by
    funext n
    have hsupport :
        Function.support (fun x => uQ.toFun x * F n x) ⊆ U := by
      simpa [F, U] using
        support_mul_backwardDifferenceQuotient_h1WeakTest_deriv_subset
          (U := openCubeSet Q) (V := V) (u := uQ.toFun)
          (step := stepSeq n) i j φ hSV hVU (hVshift n)
    have hsubset :=
      integral_subset_of_support_subset
        (U := (Set.univ : Set (Vec d))) (V := U)
        (Set.subset_univ U) hsupport
    simpa [F, U] using hsubset
  have htarget :
      ∫ x,
          uQ.toFun x *
            (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)
          ∂MeasureTheory.volume =
        ∫ x in U, uQ.toFun x * G x ∂MeasureTheory.volume := by
    have hsupport :
        Function.support (fun x => uQ.toFun x * G x) ⊆ U := by
      simpa [G, U] using
        support_mul_fderiv_h1WeakTest_deriv_apply_subset
          (u := uQ.toFun) φ i j (hSV.trans hVU)
    have hsubset :=
      integral_subset_of_support_subset
        (U := (Set.univ : Set (Vec d))) (V := U)
        (Set.subset_univ U) hsupport
    simpa [G, U] using hsubset
  rw [hseq, htarget]
  exact hset_lim

/-- Raw `L²` seminorm convergence of the smooth backward quotients is enough
to close the open-inner Hessian pairing limit. -/
theorem openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_eLpNorm_tendsto
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q)
    (hback_eLp :
      ∀ φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁),
        Filter.Tendsto
          (fun n : ℕ =>
            MeasureTheory.eLpNorm
              (fun x =>
                euclideanBackwardDifferenceQuotient (stepSeq n) i
                    (fun y => φ.deriv j y) x -
                  (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))
              2 (volumeMeasureOn (openCubeSet Q)))
          Filter.atTop (nhds 0)) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  refine
    openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_toScalarL2_tendsto
      uQ stepSeq i j hSV hVU hVshift ?_
  intro φ
  exact
    tendsto_toScalarL2_of_tendsto_eLpNorm
      (F := fun n =>
        euclideanBackwardDifferenceQuotient (stepSeq n) i (fun y => φ.deriv j y))
      (G := fun x => (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))
      (fun n =>
        memScalarL2_euclideanBackwardDifferenceQuotient_h1WeakTest_deriv
          (U := openCubeSet Q) (step := stepSeq n) φ i j)
      (memScalarL2_fderiv_h1WeakTest_deriv_apply (U := openCubeSet Q) φ i j)
      (hback_eLp φ)

/-- A pointwise mean-value type bound for the smooth quotient error closes the
open-inner Hessian pairing limit.  This is the intended consumer of the
remaining smooth calculus estimate. -/
theorem openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_pointwise_bound
    {Q : TriadicCube d} (uQ : H1Function (openCubeSet Q))
    (stepSeq : ℕ → ℝ) (i j : Fin d) {ρ₁ : ℝ}
    (hSV : scaledOpenCubeSet Q ρ₁ ⊆ V)
    (hVU : V ⊆ openCubeSet Q)
    (hVshift : ∀ n, ∀ x ∈ V,
      euclideanCoordShift (stepSeq n) i x ∈ openCubeSet Q)
    (hstep : Filter.Tendsto stepSeq Filter.atTop (nhds 0))
    (hpoint :
      ∀ φ : H1WeakTestFunction (scaledOpenCubeSet Q ρ₁),
        ∃ C : ℝ,
          ∀ n : ℕ,
            ∀ᵐ x ∂volumeMeasureOn (openCubeSet Q),
              ‖euclideanBackwardDifferenceQuotient (stepSeq n) i
                    (fun y => φ.deriv j y) x -
                  (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i)‖ ≤
                C * ‖stepSeq n‖) :
    OpenCubeInnerHessianPairingTendsto (ρ₁ := ρ₁) uQ V stepSeq i j := by
  refine
    openCubeInnerHessianPairingTendsto_of_backwardDifferenceQuotient_deriv_eLpNorm_tendsto
      uQ stepSeq i j hSV hVU hVshift ?_
  intro φ
  rcases hpoint φ with ⟨C, hC⟩
  have hfinite : (volumeMeasureOn (openCubeSet Q)) Set.univ ≠ ⊤ := by
    simpa [volumeMeasureOn] using (volume_openCubeSet_lt_top Q).ne
  exact
    tendsto_eLpNorm_zero_of_ae_norm_le_mul_norm
      (U := openCubeSet Q)
      (F := fun n x =>
        euclideanBackwardDifferenceQuotient (stepSeq n) i (fun y => φ.deriv j y) x -
          (fderiv ℝ (fun y => φ.deriv j y) x) (basisVec i))
      (stepSeq := stepSeq) hfinite hstep hC

end WeakPoissonEquationOn

end

end Homogenization
