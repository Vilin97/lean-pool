/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.PoincareW1p.ConvexApproxTendsto

/-! # Core -/

namespace Homogenization

open scoped ENNReal

namespace W1pFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}
private theorem subAverageLpSeminorm_le_smoothPoincareLpConst_mul_gradientCoordLpSeminormSum
    [NeZero d] (hU : IsOpenBoundedConvexDomain U)
    {q : ℝ} (hq : 1 < q) (hvol : 0 < (MeasureTheory.volume U).toReal)
    (u : W1pFunction U (ENNReal.ofReal q)) :
    u.subAverageLpSeminorm ≤
      smoothPoincareLpConst (d := d) (U := U) hU * u.gradientCoordLpSeminormSum := by
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  let pE : ENNReal := ENNReal.ofReal q
  let hp1 : 1 ≤ pE := by
    dsimp [pE]
    rw [ENNReal.one_le_ofReal]
    exact hq.le
  have hp_top : pE ≠ ⊤ := by
    dsimp [pE]
    exact ENNReal.ofReal_ne_top
  have hnonempty : U.Nonempty := by
    by_contra hne
    have hUempty : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    subst U
    simp at hvol
  rcases hnonempty with ⟨x0, hx0⟩
  rcases Metric.mem_nhds_iff.1 (hU.isOpen.mem_nhds hx0) with ⟨δ, hδpos, hδsub⟩
  let r : ℝ := δ / 2
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hball : Metric.closedBall x0 r ⊆ U := by
    intro y hy
    apply hδsub
    have hy' : dist y x0 ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    have hlt : dist y x0 < δ := by
      have hrδ : r < δ := by
        dsimp [r]
        linarith
      exact lt_of_le_of_lt hy' hrδ
    simpa [Metric.mem_ball] using hlt
  let ψ : ℕ → W1pFunction U pE := fun n => convexApproxSmoothW1p (U := U) hU hp1 u x0 hr n
  have hψ_bound :
      ∀ n, (ψ n).subAverageLpSeminorm ≤
        smoothPoincareLpConst (d := d) (U := U) hU * (ψ n).gradientCoordLpSeminormSum := by
    intro n
    let f : Vec d → ℝ :=
      convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) u.toFun x0 r
        (unitConvexApproxScale n)
    have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
      contDiff_convexApproxSmoothRepresentative
        (U := U) (ρ := unitConvexApproxKernel (d := d)) (u := u.toFun)
        (p := pE) (x0 := x0) (r := r) (ε := unitConvexApproxScale n)
        hU.isOpen.measurableSet (isConvexApproxKernel_unitConvexApproxKernel (d := d))
        hp1 u.memLp hr (unitConvexApproxScale_pos n)
    simpa [ψ, convexApproxSmoothW1p, f, pE] using
      (subAverageLpSeminorm_le_smoothPoincareLpConst_mul_gradientCoordLpSeminormSum_ofContDiff
        (U := U) hU (q := q) hq (f := f) hf hvol)
  have hleft :
      Filter.Tendsto (fun n => (ψ n).subAverageLpSeminorm)
        Filter.atTop (nhds u.subAverageLpSeminorm) := by
    simpa [ψ, pE, hp1] using
      (tendsto_convexApproxSmoothW1p_subAverageLpSeminorm_ofReal
        (U := U) hU hq u hball hr)
  have hright_grad :
      Filter.Tendsto (fun n => (ψ n).gradientCoordLpSeminormSum)
        Filter.atTop (nhds u.gradientCoordLpSeminormSum) := by
    simpa [ψ, pE] using
      (tendsto_convexApproxSmoothW1p_gradientCoordLpSeminormSum
        (U := U) hU hp1 hp_top u hball hr)
  have hright :
      Filter.Tendsto
        (fun n =>
          smoothPoincareLpConst (d := d) (U := U) hU * (ψ n).gradientCoordLpSeminormSum)
        Filter.atTop
        (nhds (smoothPoincareLpConst (d := d) (U := U) hU *
          u.gradientCoordLpSeminormSum)) :=
    tendsto_const_nhds.mul hright_grad
  exact le_of_tendsto_of_tendsto' hleft hright hψ_bound

theorem exists_subAverage_poincare_constant_of_isOpenBoundedConvexDomain
    [NeZero d] (hU : IsOpenBoundedConvexDomain U) {q : ℝ} (hq : 1 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ u : W1pFunction U (ENNReal.ofReal q),
        u.subAverageLpSeminorm ≤ C * u.gradientCoordLpSeminormSum := by
  classical
  let : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  by_cases hvol0 : (MeasureTheory.volume U).toReal = 0
  · refine ⟨0, le_rfl, ?_⟩
    intro u
    have hfinite : MeasureTheory.volume U < ⊤ := by
      simpa [volumeMeasureOn] using
        (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ)
    have hvol0' : MeasureTheory.volume U = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff (MeasureTheory.volume U)).mp hvol0 with hzero | htop
      · exact hzero
      · exact (hfinite.ne htop).elim
    have hμ0 : volumeMeasureOn U = 0 := by
      simpa [volumeMeasureOn] using
        (MeasureTheory.Measure.restrict_eq_zero.2 hvol0' :
          MeasureTheory.volume.restrict U = 0)
    simp [W1pFunction.subAverageLpSeminorm, hμ0, MeasureTheory.eLpNorm_measure_zero]
  · refine ⟨smoothPoincareLpConst (d := d) (U := U) hU,
      smoothPoincareLpConst_nonneg (d := d) (U := U) hU, ?_⟩
    intro u
    have hvol : 0 < (MeasureTheory.volume U).toReal :=
      lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hvol0)
    exact subAverageLpSeminorm_le_smoothPoincareLpConst_mul_gradientCoordLpSeminormSum
      (U := U) hU hq hvol u

theorem integralAverage_eq_zero_of_meanZero
    (u : W1pFunction U p) (hmean : MeanZeroOn U u.toFun) :
    integralAverage U u.toFun = 0 := by
  unfold integralAverage
  rw [hmean]
  simp

theorem subAverageLpSeminorm_eq_valueLpSeminorm_of_meanZero
    (u : W1pFunction U p) (hmean : MeanZeroOn U u.toFun) :
    u.subAverageLpSeminorm = u.valueLpSeminorm := by
  have havg : integralAverage U u.toFun = 0 :=
    u.integralAverage_eq_zero_of_meanZero hmean
  apply congrArg ENNReal.toReal
  apply MeasureTheory.eLpNorm_congr_ae
  filter_upwards with x
  simp [havg]

private theorem valueLpSeminorm_eq_zero_of_volume_toReal_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : (MeasureTheory.volume U).toReal = 0) (u : W1pFunction U p) :
    u.valueLpSeminorm = 0 := by
  have hfinite : MeasureTheory.volume U < ⊤ := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.measure_lt_top (volumeMeasureOn U) Set.univ)
  have hvol0 : MeasureTheory.volume U = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (MeasureTheory.volume U)).mp hvol with hzero | htop
    · exact hzero
    · exact (hfinite.ne htop).elim
  have hμ0 : volumeMeasureOn U = 0 := by
    simpa [volumeMeasureOn] using
      (MeasureTheory.Measure.restrict_eq_zero.2 hvol0 :
        MeasureTheory.volume.restrict U = 0)
  dsimp [W1pFunction.valueLpSeminorm]
  rw [hμ0, MeasureTheory.eLpNorm_measure_zero]
  rfl

end W1pFunction

/-- Mean-zero `W^{1,p}(U)` functions, represented by a chosen witness together
with the zero-average condition. -/
structure W1pMeanZeroFunction {d : ℕ} (U : Set (Vec d)) (p : ENNReal) where
  toW1pFunction : W1pFunction U p
  meanZero : MeanZeroOn U toW1pFunction.toFun

namespace W1pMeanZeroFunction

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

instance : Coe (W1pMeanZeroFunction U p) (W1pFunction U p) where
  coe u := u.toW1pFunction

instance : CoeFun (W1pMeanZeroFunction U p) (fun _ => Vec d → ℝ) where
  coe u := u.toW1pFunction.toFun

@[simp] theorem coe_mk (u : W1pFunction U p) (hmean : MeanZeroOn U u.toFun) :
    ((⟨u, hmean⟩ : W1pMeanZeroFunction U p) : W1pFunction U p) = u :=
  rfl

@[ext] theorem ext {u v : W1pMeanZeroFunction U p}
    (htoW1p : u.toW1pFunction = v.toW1pFunction) : u = v := by
  cases u
  cases v
  cases htoW1p
  rfl

/-- The scalar `L^p(U)` seminorm of a mean-zero `W^{1,p}` function. -/
noncomputable def valueLpSeminorm (u : W1pMeanZeroFunction U p) : ℝ :=
  u.toW1pFunction.valueLpSeminorm

/-- Coordinate-sum gradient seminorm of a mean-zero `W^{1,p}` function. -/
noncomputable def gradientCoordLpSeminormSum (u : W1pMeanZeroFunction U p) : ℝ :=
  u.toW1pFunction.gradientCoordLpSeminormSum

theorem valueLpSeminorm_nonneg (u : W1pMeanZeroFunction U p) :
    0 ≤ u.valueLpSeminorm :=
  u.toW1pFunction.valueLpSeminorm_nonneg

theorem gradientCoordLpSeminormSum_nonneg (u : W1pMeanZeroFunction U p) :
    0 ≤ u.gradientCoordLpSeminormSum :=
  u.toW1pFunction.gradientCoordLpSeminormSum_nonneg

theorem subAverageLpSeminorm_eq_valueLpSeminorm
    (u : W1pMeanZeroFunction U p) :
    u.toW1pFunction.subAverageLpSeminorm = u.valueLpSeminorm := by
  simpa [W1pMeanZeroFunction.valueLpSeminorm] using
    u.toW1pFunction.subAverageLpSeminorm_eq_valueLpSeminorm_of_meanZero u.meanZero

private theorem valueLpSeminorm_eq_zero_of_dim_zero
    {U : Set (Vec 0)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hvol : 0 < (MeasureTheory.volume U).toReal) (u : W1pMeanZeroFunction U p) :
    u.valueLpSeminorm = 0 := by
  let c : ℝ := u.toW1pFunction.toFun 0
  have hconst : u.toW1pFunction.toFun = fun _ : Vec 0 => c := by
    funext x
    exact congrArg u.toW1pFunction.toFun (Subsingleton.elim x (0 : Vec 0))
  have hmean_const : ∫ x in U, (fun _ : Vec 0 => c) x ∂MeasureTheory.volume = 0 := by
    change MeanZeroOn U (fun _ : Vec 0 => c)
    rw [← hconst]
    exact u.meanZero
  have hμ :
      (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
    exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
  have hmean_mul : (MeasureTheory.volume U).toReal * c = 0 := by
    rw [MeasureTheory.integral_const] at hmean_const
    rw [hμ, smul_eq_mul] at hmean_const
    exact hmean_const
  have hc0 : c = 0 := by
    nlinarith
  have hzeroFun : u.toW1pFunction.toFun = 0 := by
    rw [hconst]
    funext x
    simp [hc0]
  simp [W1pMeanZeroFunction.valueLpSeminorm, W1pFunction.valueLpSeminorm, hzeroFun]

end W1pMeanZeroFunction

/-- A bundled finite-`p` mean-zero Poincare estimate for the `W^{1,p}` layer. -/
structure W1pPoincareEstimate {d : ℕ} (U : Set (Vec d)) (p : ENNReal) where
  fixedValue : ℝ
  constant_nonneg : 0 ≤ fixedValue
  bound :
    ∀ u : W1pMeanZeroFunction U p,
      u.valueLpSeminorm ≤ fixedValue * u.gradientCoordLpSeminormSum

namespace W1pPoincareEstimate

variable {d : ℕ} {U : Set (Vec d)} {p : ENNReal}

theorem bound_subAverage (hC : W1pPoincareEstimate U p) (u : W1pFunction U p)
    (hmean : MeanZeroOn U u.toFun) :
    u.subAverageLpSeminorm ≤ hC.fixedValue * u.gradientCoordLpSeminormSum := by
  rw [u.subAverageLpSeminorm_eq_valueLpSeminorm_of_meanZero hmean]
  let v : W1pMeanZeroFunction U p := ⟨u, hmean⟩
  simpa [v, W1pMeanZeroFunction.valueLpSeminorm,
    W1pMeanZeroFunction.gradientCoordLpSeminormSum] using hC.bound v

end W1pPoincareEstimate

/-- Bounded open convex domains satisfy the mean-zero finite-`p` Poincare
estimate for every real exponent `1 < p < ∞`, packaged on the witness-based
`W1pFunction` API. -/
noncomputable def w1pPoincareEstimate_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} {q : ℝ}
    (hU : IsOpenBoundedConvexDomain U) (hq : 1 < q) :
    W1pPoincareEstimate U (ENNReal.ofReal q) := by
  classical
  letI : MeasureTheory.IsFiniteMeasure (volumeMeasureOn U) := by
    simpa [volumeMeasureOn] using hU.isFiniteMeasure_restrict_volume
  by_cases hvol0 : (MeasureTheory.volume U).toReal = 0
  · exact
      { fixedValue := 0
        constant_nonneg := le_rfl
        bound := by
          intro u
          have hzero :=
            W1pFunction.valueLpSeminorm_eq_zero_of_volume_toReal_eq_zero
              (U := U) (p := ENNReal.ofReal q) hvol0 u.toW1pFunction
          simp [W1pMeanZeroFunction.valueLpSeminorm, hzero] }
  · have hvol : 0 < (MeasureTheory.volume U).toReal := by
      exact lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hvol0)
    by_cases hd0 : d = 0
    · subst d
      exact
        { fixedValue := 0
          constant_nonneg := le_rfl
          bound := by
            intro u
            have hzero :=
              W1pMeanZeroFunction.valueLpSeminorm_eq_zero_of_dim_zero
                (U := U) (p := ENNReal.ofReal q) hvol u
            simp [hzero] }
    · letI : NeZero d := ⟨hd0⟩
      exact
        { fixedValue := W1pFunction.smoothPoincareLpConst (d := d) (U := U) hU
          constant_nonneg :=
            W1pFunction.smoothPoincareLpConst_nonneg (d := d) (U := U) hU
          bound := by
            intro u
            have hsub :=
              W1pFunction.subAverageLpSeminorm_le_smoothPoincareLpConst_mul_gradientCoordLpSeminormSum
                (U := U) hU hq hvol u.toW1pFunction
            simpa [W1pMeanZeroFunction.valueLpSeminorm,
              W1pMeanZeroFunction.gradientCoordLpSeminormSum,
              u.subAverageLpSeminorm_eq_valueLpSeminorm] using hsub }


end Homogenization
