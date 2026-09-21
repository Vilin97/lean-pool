/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Killed.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Kernel.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Path.Exhaustion

/-!
# Potential measures

The resolvent of a transition family at a shift `lam` integrates an observable against the
exponentially weighted time average of its transition kernels.  This file realises that average
as a genuine measure, the `lam`-potential measure

  `laplacePotential lam mu = ∫_0^∞ e^{-lam t} (mu t) dt`,

so that both the kernel resolvent of a sub-Markov kernel semigroup and the killed resolvent of an
open set are integrals against a measure on the state space:
`SubMarkovKernelSemigroup.lintegral_resolventPotential` and
`IsConservative.lintegral_killedPotential`.  Potential measures of sub-Markov families are finite
at every positive shift, with total mass at most `1 / lam`.

Two consequences of the measure form are proved here: the killed resolvent is monotone in the
open set and in the observable (`IsConservative.killedResolvent_mono`), and the kernel resolvent
is measurable in the starting point and continuous along monotone limits of observables
(`SubMarkovKernelSemigroup.measurable_kernelResolvent`,
`SubMarkovKernelSemigroup.kernelResolvent_iSup`).  The kernel resolvent is also additive and
homogeneous on measurable observables (`SubMarkovKernelSemigroup.kernelResolvent_add`,
`SubMarkovKernelSemigroup.kernelResolvent_const_mul`).

No resolvent identity and no topology on the state space are used here.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace MarkovProcess

/-- The exponentially weighted measure on positive times at the shift `lam`. -/
noncomputable def laplaceWeight (lam : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity fun t ↦ ENNReal.ofReal (Real.exp (-lam * t))

/-- The exponential weight is measurable in time. -/
theorem measurable_laplaceDensity (lam : ℝ) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (Real.exp (-lam * t)) :=
  ENNReal.measurable_ofReal.comp
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable

/-- Integration against the exponentially weighted time measure. -/
theorem lintegral_laplaceWeight (lam : ℝ) {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, g t ∂laplaceWeight lam =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * g t := by
  rw [laplaceWeight,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_laplaceDensity lam) hg]
  rfl

/-- At a positive shift the exponentially weighted time measure has total mass `1 / lam`. -/
theorem laplaceWeight_univ {lam : ℝ} (hlam : 0 < lam) :
    laplaceWeight lam univ = ENNReal.ofReal lam⁻¹ := by
  have hmass : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  rw [← hmass, lintegral_laplaceWeight lam measurable_const]
  simp only [mul_one]
  rw [← ofReal_integral_eq_lintegral_ofReal (exp_neg_integrableOn_Ioi 0 hlam)
    (Eventually.of_forall fun t ↦ (Real.exp_pos _).le)]
  congr 1
  rw [integral_exp_mul_Ioi (neg_neg_of_pos hlam) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

/-- At a positive shift the exponentially weighted time measure is finite. -/
theorem isFiniteMeasure_laplaceWeight {lam : ℝ} (hlam : 0 < lam) :
    IsFiniteMeasure (laplaceWeight lam) :=
  ⟨by rw [laplaceWeight_univ hlam]; exact ENNReal.ofReal_lt_top⟩

variable {alpha : Type*} [MeasurableSpace alpha]

/-- The `lam`-potential measure of a measurable family of transition measures: the exponentially
weighted time average of the family. -/
noncomputable def laplacePotential (lam : ℝ) (mu : ℝ → Measure alpha) : Measure alpha :=
  (laplaceWeight lam).bind mu

/-- Integration against a potential measure is the Laplace transform in time of the integrals
against the family. -/
theorem lintegral_laplacePotential (lam : ℝ) {mu : ℝ → Measure alpha} (hmu : Measurable mu)
    {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y ∂laplacePotential lam mu =
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂mu t := by
  have hinner : Measurable fun t : ℝ ↦ ∫⁻ y, f y ∂mu t :=
    (Measure.measurable_lintegral hf).comp hmu
  rw [laplacePotential, Measure.lintegral_bind hmu.aemeasurable hf.aemeasurable,
    lintegral_laplaceWeight lam hinner]

/-- A potential measure of a family of sub-probability measures has mass at most `1 / lam`. -/
theorem laplacePotential_univ_le {lam : ℝ} (hlam : 0 < lam) {mu : ℝ → Measure alpha}
    (hmu : Measurable mu) (hmass : ∀ t, mu t univ ≤ 1) :
    laplacePotential lam mu univ ≤ ENNReal.ofReal lam⁻¹ := by
  have hone : ∫⁻ _y : alpha, (1 : ℝ≥0∞) ∂laplacePotential lam mu =
      laplacePotential lam mu univ := lintegral_one
  have hweight : ∫⁻ _t : ℝ, (1 : ℝ≥0∞) ∂laplaceWeight lam = laplaceWeight lam univ :=
    lintegral_one
  rw [← hone, lintegral_laplacePotential lam hmu measurable_const, ← laplaceWeight_univ hlam,
    ← hweight, lintegral_laplaceWeight lam measurable_const]
  refine setLIntegral_mono' measurableSet_Ioi fun t _ht ↦ ?_
  rw [lintegral_one]
  gcongr
  exact hmass t

/-- A potential measure of a family of sub-probability measures is finite at a positive shift. -/
theorem isFiniteMeasure_laplacePotential {lam : ℝ} (hlam : 0 < lam) {mu : ℝ → Measure alpha}
    (hmu : Measurable mu) (hmass : ∀ t, mu t univ ≤ 1) :
    IsFiniteMeasure (laplacePotential lam mu) :=
  ⟨lt_of_le_of_lt (laplacePotential_univ_le hlam hmu hmass) ENNReal.ofReal_lt_top⟩

namespace SubMarkovKernelSemigroup

variable (P : SubMarkovKernelSemigroup alpha)

/-- The transition measures of a sub-Markov kernel semigroup are measurable in time. -/
theorem measurable_toMeasure_toNNReal (x : alpha) :
    Measurable fun t : ℝ ↦ P (Real.toNNReal t) x :=
  P.measurable_toMeasure.comp (measurable_real_toNNReal.prodMk measurable_const)

/-- The `lam`-potential measure of a sub-Markov kernel semigroup started at `x`. -/
noncomputable def resolventPotential (lam : ℝ) (x : alpha) : Measure alpha :=
  laplacePotential lam fun t ↦ P (Real.toNNReal t) x

/-- The kernel resolvent is integration against the potential measure. -/
theorem lintegral_resolventPotential (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    ∫⁻ y, f y ∂P.resolventPotential lam x = P.kernelResolvent lam f x :=
  lintegral_laplacePotential lam (P.measurable_toMeasure_toNNReal x) hf

/-- The potential measure of a sub-Markov kernel semigroup is finite at a positive shift. -/
theorem isFiniteMeasure_resolventPotential {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (P.resolventPotential lam x) :=
  isFiniteMeasure_laplacePotential hlam (P.measurable_toMeasure_toNNReal x)
    fun _t ↦ P.measure_univ_le_one _ x

/-- At a positive shift the kernel resolvent of the constant observable one is at most
`1 / lam`. -/
theorem kernelResolvent_one_le {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    P.kernelResolvent lam (fun _ ↦ 1) x ≤ ENNReal.ofReal lam⁻¹ := by
  rw [← P.lintegral_resolventPotential lam measurable_const x, lintegral_one]
  exact laplacePotential_univ_le hlam (P.measurable_toMeasure_toNNReal x)
    fun _t ↦ P.measure_univ_le_one _ x

/-- **The normalized potential mass of any set is at most one.**  At a positive shift the
`lam`-potential measure of a sub-Markov kernel semigroup has total mass at most `1 / lam`, so
the normalization by `lam` used in the resolvent tail estimates is a sub-probability. -/
theorem ofReal_mul_resolventPotential_le_one {lam : ℝ} (hlam : 0 < lam) (x : alpha)
    (s : Set alpha) :
    ENNReal.ofReal lam * P.resolventPotential lam x s ≤ 1 := by
  have hmass : P.resolventPotential lam x s ≤ ENNReal.ofReal lam⁻¹ :=
    le_trans (measure_mono (Set.subset_univ s))
      (laplacePotential_univ_le hlam (P.measurable_toMeasure_toNNReal x)
        fun _t ↦ P.measure_univ_le_one _ x)
  calc ENNReal.ofReal lam * P.resolventPotential lam x s
      ≤ ENNReal.ofReal lam * ENNReal.ofReal lam⁻¹ := by gcongr
    _ = 1 := by
        rw [← ENNReal.ofReal_mul hlam.le, mul_inv_cancel₀ hlam.ne', ENNReal.ofReal_one]

/-- The kernel resolvent is monotone in the observable. -/
theorem kernelResolvent_mono (lam : ℝ) {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    P.kernelResolvent lam f x ≤ P.kernelResolvent lam g x := by
  refine setLIntegral_mono' measurableSet_Ioi fun _t _ht ↦ ?_
  exact mul_le_mul' le_rfl (lintegral_mono hfg)

/-- The kernel resolvent is additive on measurable observables. -/
theorem kernelResolvent_add (lam : ℝ) {f g : alpha → ℝ≥0∞} (hf : Measurable f) (x : alpha) :
    P.kernelResolvent lam (fun y ↦ f y + g y) x =
      P.kernelResolvent lam f x + P.kernelResolvent lam g x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, (f y + g y) ∂P (Real.toNNReal t) x =
      ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂P (Real.toNNReal t) x +
        ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, g y ∂P (Real.toNNReal t) x := by
    intro t
    rw [lintegral_add_left hf, mul_add]
  simp_rw [hinner]
  exact lintegral_add_left ((measurable_laplaceDensity lam).mul
    ((Measure.measurable_lintegral hf).comp (P.measurable_toMeasure_toNNReal x))) _

/-- The kernel resolvent is homogeneous under multiplication by an extended-real constant. -/
theorem kernelResolvent_const_mul (lam : ℝ) (c : ℝ≥0∞) {f : alpha → ℝ≥0∞} (hf : Measurable f)
    (x : alpha) :
    P.kernelResolvent lam (fun y ↦ c * f y) x = c * P.kernelResolvent lam f x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, c * f y ∂P (Real.toNNReal t) x =
      c * (ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f y ∂P (Real.toNNReal t) x) := by
    intro t
    rw [lintegral_const_mul c hf]
    ring
  simp_rw [hinner]
  exact lintegral_const_mul c ((measurable_laplaceDensity lam).mul
    ((Measure.measurable_lintegral hf).comp (P.measurable_toMeasure_toNNReal x)))

/-- The kernel resolvent is measurable in the starting point. -/
theorem measurable_kernelResolvent (lam : ℝ) {f : alpha → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x ↦ P.kernelResolvent lam f x := by
  have hjoint : Measurable fun q : alpha × ℝ ↦
      ENNReal.ofReal (Real.exp (-lam * q.2)) * ∫⁻ y, f y ∂P (Real.toNNReal q.2) q.1 := by
    refine Measurable.mul ((measurable_laplaceDensity lam).comp measurable_snd) ?_
    exact (Measure.measurable_lintegral hf).comp
      (P.measurable_toMeasure.comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
        measurable_fst))
  exact hjoint.lintegral_prod_right'

/-- The kernel resolvent is continuous along monotone limits of observables. -/
theorem kernelResolvent_iSup (lam : ℝ) {f : ℕ → alpha → ℝ≥0∞} (hf : ∀ n, Measurable (f n))
    (hmono : Monotone f) (x : alpha) :
    P.kernelResolvent lam (fun y ↦ ⨆ n, f n y) x = ⨆ n, P.kernelResolvent lam (f n) x := by
  unfold kernelResolvent
  have hinner : ∀ t : ℝ, ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, (⨆ n, f n y) ∂P (Real.toNNReal t) x =
      ⨆ n, ENNReal.ofReal (Real.exp (-lam * t)) * ∫⁻ y, f n y ∂P (Real.toNNReal t) x := by
    intro t
    rw [lintegral_iSup hf fun m n hmn ↦ hmono hmn, ENNReal.mul_iSup]
  simp_rw [hinner]
  refine lintegral_iSup (fun n ↦ ?_) fun m n hmn ↦ ?_
  · exact (measurable_laplaceDensity lam).mul
      ((Measure.measurable_lintegral (hf n)).comp (P.measurable_toMeasure_toNNReal x))
  · intro _t
    exact mul_le_mul' le_rfl (lintegral_mono (hmono hmn))

section Killed

variable [MetricSpace alpha] [CompleteSpace alpha] [BorelSpace alpha]
  [SecondCountableTopology alpha] [Nonempty alpha]

variable (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
variable (U : Set alpha) (hU : IsOpen U)

/-- The killed transition kernels are measurable in time. -/
theorem IsConservative.measurable_killedKernel_toNNReal (x : alpha) :
    Measurable fun t : ℝ ↦ IsConservative.killedKernel P hP U hU (Real.toNNReal t) x :=
  (IsConservative.measurable_killedKernel P hP U hU).comp
    (measurable_real_toNNReal.prodMk measurable_const)

/-- The `lam`-potential measure of the process killed at the exit of `U`, started at `x`. -/
noncomputable def IsConservative.killedPotential (lam : ℝ) (x : alpha) : Measure alpha :=
  laplacePotential lam fun t ↦ IsConservative.killedKernel P hP U hU (Real.toNNReal t) x

/-- The killed resolvent is integration against the killed potential measure. -/
theorem IsConservative.lintegral_killedPotential (lam : ℝ) {f : alpha → ℝ≥0∞}
    (hf : Measurable f) (x : alpha) :
    ∫⁻ y, f y ∂IsConservative.killedPotential P hP U hU lam x =
      IsConservative.killedResolvent P hP U hU lam f x :=
  lintegral_laplacePotential lam (IsConservative.measurable_killedKernel_toNNReal P hP U hU x) hf

/-- The killed potential measure is finite at a positive shift. -/
theorem IsConservative.isFiniteMeasure_killedPotential {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    IsFiniteMeasure (IsConservative.killedPotential P hP U hU lam x) :=
  isFiniteMeasure_laplacePotential hlam
    (IsConservative.measurable_killedKernel_toNNReal P hP U hU x)
    fun _t ↦ (IsConservative.isSubMarkovKernel_killedKernel P hP U hU _) x

/-- **The killed resolvent is monotone in the open set and in the observable.**  A path leaves a
larger set no earlier, so the killed transition kernels increase with the set. -/
theorem IsConservative.killedResolvent_mono {V : Set alpha} (hV : IsOpen V) (hUV : U ⊆ V)
    (lam : ℝ) {f g : alpha → ℝ≥0∞} (hfg : f ≤ g) (x : alpha) :
    IsConservative.killedResolvent P hP U hU lam f x ≤
      IsConservative.killedResolvent P hP V hV lam g x := by
  refine setLIntegral_mono' measurableSet_Ioi fun t _ht ↦ ?_
  refine mul_le_mul' le_rfl (lintegral_mono' ?_ hfg)
  refine Measure.le_iff.mpr fun B hB ↦ ?_
  rw [IsConservative.killedKernel_apply P hP U hU _ x hB,
    IsConservative.killedKernel_apply P hP V hV _ x hB]
  refine measure_mono fun omega homega ↦ ?_
  exact ⟨lt_of_lt_of_le homega.1 (ContinuousPath.exitTime_mono hUV omega), homega.2⟩

end Killed

end SubMarkovKernelSemigroup

end MarkovProcess
