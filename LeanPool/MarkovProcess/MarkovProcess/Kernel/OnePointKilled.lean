/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.MarkovProcess.MarkovProcess.Kernel.OnePointKolmogorov
import LeanPool.MarkovProcess.MarkovProcess.Killed.Semigroup
import LeanPool.MarkovProcess.MarkovProcess.Feller.Resolvent
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitLaw
import LeanPool.MarkovProcess.MarkovProcess.Trajectory.ExitTimeLaplace
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Killing the one-point process at infinity

This file identifies the continuous process of the one-point extension of a positive
`C₀`-contractive resolvent with the process killed on leaving its live part.
-/

noncomputable section PortComputability

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal NNReal ZeroAtInfty

section

namespace MarkovProcess.SubMarkovKernelSemigroup

variable {alpha : Type*} [MetricSpace alpha] [CompleteSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha] [SecondCountableTopology alpha]
  [Nonempty alpha]

/-- If a state is absorbing for every transition kernel, then the continuous-path process
started there is almost surely the constant path. -/
theorem IsConservative.ae_eq_const_of_absorbing
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hK : P.KolmogorovRegular hP) (a : alpha)
    (hAbsorb : ∀ t, P t a = Measure.dirac a) :
    (fun omega : ContinuousPath alpha ↦ omega) =ᵐ[IsConservative.continuousProcess P hP a]
      fun _ ↦ ContinuousMap.const NNReal a := by
  let mu := IsConservative.continuousProcess P hP a
  have hcoord : ∀ q : DenseTime, ∀ᵐ omega ∂mu,
      omega (DenseTime.castOrderEmbedding q) = a := by
    intro q
    have hmeas : Measurable
        (fun omega : ContinuousPath alpha ↦ omega (DenseTime.castOrderEmbedding q)) :=
      ContinuousPath.measurable_coordinateProcess (alpha := alpha) _
    have hmap := IsConservative.continuousProcess_map_eval P hP hK q
    have hmapa : Measure.map (fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) mu = Measure.dirac a := by
      rw [show mu = IsConservative.continuousProcess P hP a by rfl,
        ← Kernel.map_apply _ hmeas, hmap, hAbsorb]
    have hsingleton : MeasurableSet ({a}ᶜ : Set alpha) :=
      (isClosed_singleton (x := a)).measurableSet.compl
    have hzero : mu ((fun omega : ContinuousPath alpha ↦
        omega (DenseTime.castOrderEmbedding q)) ⁻¹' ({a}ᶜ : Set alpha)) = 0 := by
      rw [← Measure.map_apply hmeas hsingleton, hmapa, Measure.dirac_apply' a hsingleton,
        Set.indicator_of_notMem (by simp)]
    exact hzero
  have hall : ∀ᵐ omega ∂mu, ∀ q : DenseTime,
      omega (DenseTime.castOrderEmbedding q) = a := ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega
  apply ContinuousPath.denseRestriction_injective
  funext q
  rw [ContinuousPath.denseRestriction_apply, ContinuousPath.denseRestriction_apply, homega q]
  rfl

/-- At an absorbing state the entire continuous-path law is the Dirac mass at the constant
path. -/
theorem IsConservative.continuousProcess_eq_dirac_of_absorbing
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hK : P.KolmogorovRegular hP) (a : alpha)
    (hAbsorb : ∀ t, P t a = Measure.dirac a) :
    IsConservative.continuousProcess P hP a =
      Measure.dirac (ContinuousMap.const NNReal a) := by
  let mu := IsConservative.continuousProcess P hP a
  have hprob : IsProbabilityMeasure mu := by
    dsimp only [mu]
    infer_instance
  calc
    mu = mu.map id := (Measure.map_id).symm
    _ = mu.map (fun _ ↦ ContinuousMap.const NNReal a) :=
      Measure.map_congr (hP.ae_eq_const_of_absorbing P hK a hAbsorb)
    _ = mu Set.univ • Measure.dirac (ContinuousMap.const NNReal a) := Measure.map_const _ _
    _ = Measure.dirac (ContinuousMap.const NNReal a) := by rw [measure_univ, one_smul]

variable [LocallyCompactSpace alpha]

/-- If the complement of an open set is a single absorbing state, then, on every path which
leaves the open set in finite time, the path shifted to its exit time is almost surely the
constant path at that state. -/
theorem IsFellerKernelSemigroup.ae_shift_exitTime_eq_const_of_compl_eq_singleton
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (a : alpha) (hcompl : Uᶜ = {a})
    (hAbsorb : ∀ t, P t a = Measure.dirac a) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂IsConservative.continuousProcess P hP x,
      ContinuousPath.exitTime U omega < ⊤ →
        ContinuousPath.shift (ContinuousPath.exitTime U omega).toNNReal omega =
          ContinuousMap.const NNReal a := by
  let Q := IsConservative.continuousProcess P hP
  let tau := ContinuousPath.exitTimeTop U
  let S : Set (ContinuousPath alpha) := {omega | tau omega < ⊤}
  let Y : ContinuousPath alpha → ContinuousPath alpha := fun omega ↦
    ContinuousPath.shift ((tau omega).untopD 0) omega
  have htau := ContinuousPath.isStoppingTime_exitTime U hU
  have hS : MeasurableSet S := by
    simpa only [S, tau, ContinuousPath.exitTimeTop_apply] using!
      ContinuousPath.measurableSet_exitTime_lt_top U hU
  have hY : Measurable Y := ContinuousPath.measurable_shift_untopD_stoppingTime tau htau
  have heval0 : ∀ᵐ omega ∂Q x, omega 0 = x := IsConservative.ae_eval_zero_eq hP hK x
  have hevalExit : ∀ᵐ omega ∂(Q x).restrict S,
      omega ((tau omega).untopD 0) = a := by
    rw [ae_restrict_iff' hS]
    filter_upwards [heval0] with omega hzero homega
    have hfin : ContinuousPath.exitTime U omega ≠ ⊤ := by
      exact ne_of_lt (by simpa only [S, tau, ContinuousPath.exitTimeTop_apply] using! homega)
    rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega hfin]
    have hfront := ContinuousPath.coordinate_exitTime_mem_frontier U hU omega
      (hzero.symm ▸ hx) hfin
    have hout : omega (ContinuousPath.exitTime U omega).toNNReal ∈ Uᶜ := by
      exact (hU.frontier_eq ▸ hfront).2
    rw [hcompl] at hout
    exact Set.mem_singleton_iff.mp hout
  have hRestart : ((Q x).restrict S).map Y =
      Kernel.comap Q (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        ((Q x).restrict S) := by
    simpa only [Q, S, Y, Set.univ_inter] using
      hFeller.continuousProcess_restrict_map_shift_stoppingTime_lt_top
        P hP hK x tau htau Set.univ MeasurableSet.univ
  have hrhs : ∀ᵐ eta ∂Kernel.comap Q
        (fun omega ↦ omega ((tau omega).untopD 0))
          (ContinuousPath.measurable_eval_untopD_stoppingTime tau htau) ∘ₘ
        ((Q x).restrict S),
      eta = ContinuousMap.const NNReal a := by
    apply Measure.ae_comp_of_ae_ae
      (show MeasurableSet ({eta : ContinuousPath alpha |
        eta = ContinuousMap.const NNReal a}) by
          simpa only [Set.ofPred_eq_eq_singleton] using
            (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)
    filter_upwards [hevalExit] with omega homega
    rw [Kernel.comap_apply, homega,
      hP.continuousProcess_eq_dirac_of_absorbing P hK a hAbsorb]
    exact (ae_dirac_iff (show MeasurableSet ({eta : ContinuousPath alpha |
      eta = ContinuousMap.const NNReal a}) by
        simpa only [Set.ofPred_eq_eq_singleton] using
          (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)).mpr rfl
  rw [← hRestart] at hrhs
  have hshift : ∀ᵐ omega ∂(Q x).restrict S,
      Y omega = ContinuousMap.const NNReal a :=
    (ae_map_iff hY.aemeasurable
      (show MeasurableSet ({eta : ContinuousPath alpha |
        eta = ContinuousMap.const NNReal a}) by
          simpa only [Set.ofPred_eq_eq_singleton] using
            (isClosed_singleton (x := ContinuousMap.const NNReal a)).measurableSet)).mp hrhs
  rw [ae_restrict_iff' hS] at hshift
  filter_upwards [hshift] with omega homega hfin
  have hs : omega ∈ S := by
    change tau omega < ⊤
    rw [show tau omega = ContinuousPath.exitTime U omega by
      exact ContinuousPath.exitTimeTop_apply U omega]
    exact hfin
  have h := homega hs
  dsimp only [Y] at h
  rw [show (tau omega).untopD 0 = (ContinuousPath.exitTime U omega).toNNReal by
      exact ContinuousPath.untopD_exitTimeTop_eq_toNNReal U omega (ne_of_lt hfin)] at h
  exact h

/-- Pathwise absorption after the finite exit time from an open set whose complement is a
single absorbing state. -/
theorem IsFellerKernelSemigroup.ae_absorbed_after_exitTime_of_compl_eq_singleton
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (a : alpha) (hcompl : Uᶜ = {a})
    (hAbsorb : ∀ t, P t a = Measure.dirac a) {x : alpha} (hx : x ∈ U) :
    ∀ᵐ omega ∂IsConservative.continuousProcess P hP x,
      ContinuousPath.exitTime U omega < ⊤ →
        ∀ t : NNReal, (ContinuousPath.exitTime U omega).toNNReal ≤ t → omega t = a := by
  filter_upwards [hFeller.ae_shift_exitTime_eq_const_of_compl_eq_singleton
      P hP hK U hU a hcompl hAbsorb hx] with omega homega hfin t ht
  let s := t - (ContinuousPath.exitTime U omega).toNNReal
  have hadd : (ContinuousPath.exitTime U omega).toNNReal + s = t := by
    exact add_tsub_cancel_of_le ht
  have h := congrArg (fun eta : ContinuousPath alpha ↦ eta s) (homega hfin)
  simpa only [ContinuousPath.shift_apply, ContinuousMap.const_apply, hadd] using h

/-- Under pathwise absorption, survival to a deterministic time is equivalent almost surely to
being in the open live set at that time. -/
theorem IsFellerKernelSemigroup.ae_lt_exitTime_iff_mem_of_compl_eq_singleton
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    (U : Set alpha) (hU : IsOpen U) (a : alpha) (hcompl : Uᶜ = {a})
    (hAbsorb : ∀ t, P t a = Measure.dirac a) {x : alpha} (hx : x ∈ U) (t : NNReal) :
    ∀ᵐ omega ∂IsConservative.continuousProcess P hP x,
      ((t : ℝ≥0∞) < ContinuousPath.exitTime U omega ↔ omega t ∈ U) := by
  filter_upwards [hFeller.ae_absorbed_after_exitTime_of_compl_eq_singleton
      P hP hK U hU a hcompl hAbsorb hx] with omega habs
  constructor
  · exact fun ht ↦ ContinuousPath.mem_of_lt_exitTime U omega t ht
  · intro htU
    by_contra hsurv
    have hle : ContinuousPath.exitTime U omega ≤ (t : ℝ≥0∞) := le_of_not_gt hsurv
    have hfin : ContinuousPath.exitTime U omega < ⊤ :=
      hle.trans_lt ENNReal.coe_lt_top
    have htime : (ContinuousPath.exitTime U omega).toNNReal ≤ t := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_of_lt hfin)]
      exact hle
    have heq : omega t = a := habs hfin t htime
    have haU : a ∉ U := by
      intro ha
      have : a ∈ Uᶜ := by rw [hcompl]; exact Set.mem_singleton a
      exact this ha
    exact haU (heq ▸ htU)

end MarkovProcess.SubMarkovKernelSemigroup

namespace MarkovProcess.PositiveC0ContractiveResolvent

open MarkovProcess.SubMarkovKernelSemigroup

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The one-point compactification is compact under the exhaustion metric's topology, since that
topology coincides with the canonical one-point topology (which is always compact). This is a
typeclass-search cache in the same spirit as `OnePoint.instCompleteSpaceOnePointExhaustion`: it
lets the `isCompact_univ` calls that build `CompleteSpace (OnePoint X)` (via
`completeSpace_of_isComplete_univ`) inside this file's `letI` chains resolve automatically. -/
private instance instCompactSpaceOnePointExhaustion
    (rho : X → ℝ) (hrho_cont : Continuous rho) (hrho_pos : ∀ x, 0 < rho x)
    (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x}) :
    @CompactSpace (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
  rw [OnePoint.exhaustionMetricSpace_toTopologicalSpace]
  infer_instance

/-- The original space is homeomorphic to the live part of its one-point compactification. -/
noncomputable def onePointLiveHomeomorph :
    X ≃ₜ Set.range ((↑) : X → OnePoint X) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph

omit [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X]
  [BorelSpace X] in
/-- The homeomorphism onto the live part is the coercion into the compactification. -/
@[simp] theorem onePointLiveHomeomorph_apply (x : X) :
    (onePointLiveHomeomorph x : OnePoint X) = (x : OnePoint X) := rfl

/-- At a live starting point, the compactified transition law is the original transition law,
pushed into the live part, plus the missing mass at infinity. -/
theorem onePointKernelSemigroup_apply_coe
    (R : PositiveC0ContractiveResolvent X) (t : NNReal) (x : X) :
    R.onePointKernelSemigroup t (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty := by
  let : (R.kernelSemigroup t x).Regular := by
    rw [PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  let : IsFiniteMeasure (R.kernelSemigroup t x) :=
    ⟨lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top⟩
  let : Measure.InnerRegularCompactLTTop
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) :=
    Measure.InnerRegularCompactLTTop.map_of_continuous OnePoint.continuous_coe
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X)) := inferInstance
  have hmissing_ne_top : 1 - R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  let : IsFiniteMeasure
      ((1 - R.kernelSemigroup t x Set.univ) •
        Measure.dirac (OnePoint.infty : OnePoint X)) :=
    Measure.smul_finite _ hmissing_ne_top
  let : IsFiniteMeasure
      ((R.kernelSemigroup t x).map ((↑) : X → OnePoint X) +
        (1 - R.kernelSemigroup t x Set.univ) • Measure.dirac OnePoint.infty) :=
    ⟨(ENNReal.add_lt_top).2 ⟨measure_lt_top _ _, measure_lt_top _ _⟩⟩
  let : (R.onePointKernelSemigroup t (x : OnePoint X)).Regular := by
    rw [onePointKernelSemigroup, PositiveC0ContractiveResolvent.kernelSemigroup,
      PositiveC0SemigroupKernel.kernelSemigroup_apply,
      PositiveC0OperatorKernel.kernel_apply]
    infer_instance
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  let g : C₀(OnePoint X, ℝ) :=
    PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap f
  have hmain := R.integral_onePointKernelSemigroup t g (x : OnePoint X)
  rw [onePointSemigroup_apply, R.onePointSemigroupAction_coe] at hmain
  have hmap :
      ∫ z, f z ∂(R.kernelSemigroup t x).map ((↑) : X → OnePoint X) =
        ∫ y, f (y : OnePoint X) ∂R.kernelSemigroup t x := by
    simpa only using! integral_map OnePoint.continuous_coe.aemeasurable
      f.continuous.aestronglyMeasurable
  have hmass : R.kernelSemigroup t x Set.univ ≠ ⊤ :=
    (lt_of_le_of_lt (R.kernelSemigroup.measure_univ_le_one t x) ENNReal.one_lt_top).ne
  have hmissing :
      (1 - R.kernelSemigroup t x Set.univ).toReal =
        1 - (R.kernelSemigroup t x).real Set.univ := by
    rw [ENNReal.toReal_sub_of_le (R.kernelSemigroup.measure_univ_le_one t x)
        ENNReal.one_ne_top,
      ENNReal.toReal_one, measureReal_def]
  have hleft : ∫ z, f z ∂R.onePointKernelSemigroup t (x : OnePoint X) =
      ∫ z, g z ∂R.onePointKernelSemigroup t (x : OnePoint X) := by
    apply integral_congr_ae
    filter_upwards with z
    exact (PositiveC0OperatorMeasure.compactlySupportedToC0LinearMap_apply f z).symm
  rw [integral_add_measure]
  · rw [hleft, hmain, hmap, integral_smul_measure, integral_dirac, hmissing, smul_eq_mul]
    congr 2
  · exact f.integrable
  · exact f.integrable

/-- A tail estimate in the original metric and the explicit cemetery-mass identity give a
whole-space tail estimate for the one-point extension. -/
theorem onePointKernelSemigroup_tail_le_of_tail_le
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (h : NNReal) (x : X) (r : ℝ) (a : ℝ≥0∞)
    (hlive : R.kernelSemigroup h x {y | r < dist y x} ≤ a)
    (hcemetery : R.onePointKernelSemigroup h (x : OnePoint X) {OnePoint.infty} =
      1 - R.kernelSemigroup h x Set.univ) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    R.onePointKernelSemigroup h (x : OnePoint X)
        {z | r < dist z (x : OnePoint X)} ≤
      a + (1 - R.kernelSemigroup h x Set.univ) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let tail : Set (OnePoint X) := {z | r < dist z (x : OnePoint X)}
  let live : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X)
  have htail : MeasurableSet tail :=
    measurableSet_lt measurable_const
      (measurable_dist.comp (measurable_id.prodMk measurable_const))
  have hliveSet : MeasurableSet live := OnePoint.isOpen_range_coe.measurableSet
  have hliveBound :
      R.onePointKernelSemigroup h (x : OnePoint X) (tail ∩ live) ≤ a := by
    rw [R.onePointKernelSemigroup_apply_coe h x, Measure.add_apply,
      Measure.map_apply OnePoint.continuous_coe.measurable (htail.inter hliveSet),
      Measure.smul_apply, Measure.dirac_apply' OnePoint.infty (htail.inter hliveSet)]
    have hinfty : OnePoint.infty ∉ tail ∩ live :=
      fun hz ↦ OnePoint.infty_notMem_range_coe hz.2
    rw [Set.indicator_of_notMem hinfty, smul_zero, add_zero]
    apply (measure_mono ?_).trans hlive
    intro y hy
    exact OnePoint.exhaustionMetricSpace_live_tail_subset rho hrho_cont hrho_pos
      hrho_lipschitz hrho_compact x r hy.1
  have hcover : tail ⊆ (tail ∩ live) ∪ {OnePoint.infty} := by
    intro z hz
    induction z using OnePoint.rec with
    | infty => exact Set.mem_union_right _ (Set.mem_singleton _)
    | coe y => exact Set.mem_union_left _ ⟨hz, ⟨y, rfl⟩⟩
  calc
    R.onePointKernelSemigroup h (x : OnePoint X) tail ≤
        R.onePointKernelSemigroup h (x : OnePoint X)
          ((tail ∩ live) ∪ {OnePoint.infty}) := measure_mono hcover
    _ ≤ R.onePointKernelSemigroup h (x : OnePoint X) (tail ∩ live) +
        R.onePointKernelSemigroup h (x : OnePoint X) {OnePoint.infty} := measure_union_le _ _
    _ ≤ a + (1 - R.kernelSemigroup h x Set.univ) :=
      add_le_add hliveBound hcemetery.le

/-- The process furnished by the one-point resolvent is absorbed at infinity after its finite
exit time from the live part. -/
theorem ae_absorbed_after_onePoint_exitTime
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega < ⊤ →
        ∀ t : NNReal,
          (ContinuousPath.exitTime (Set.range ((↑) : X → OnePoint X)) omega).toNNReal ≤ t →
            omega t = OnePoint.infty := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  exact R.isFellerKernelSemigroup_onePointKernelSemigroup
    |>.ae_absorbed_after_exitTime_of_compl_eq_singleton R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      hK
      (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe OnePoint.infty
      OnePoint.compl_range_coe R.onePointKernelSemigroup_absorbing
      ⟨x, rfl⟩

/-- For the one-point process, survival to a deterministic time is almost surely equivalent to
the time-`t` coordinate still being a live point. -/
theorem ae_lt_onePoint_exitTime_iff_mem
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (x : X) (t : NNReal) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      ((t : ℝ≥0∞) < ContinuousPath.exitTime
          (Set.range ((↑) : X → OnePoint X)) omega ↔
        omega t ∈ Set.range ((↑) : X → OnePoint X)) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  exact R.isFellerKernelSemigroup_onePointKernelSemigroup
    |>.ae_lt_exitTime_iff_mem_of_compl_eq_singleton R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup
      hK
      (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe OnePoint.infty
      OnePoint.compl_range_coe R.onePointKernelSemigroup_absorbing
      ⟨x, rfl⟩ t

/-- In the canonical live coordinates, every transition kernel of the killed one-point process
is exactly the kernel generated by the original resolvent. -/
theorem killedSemigroup_onePointLive_image
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (t : NNReal) (x : X) {B : Set X} (hB : MeasurableSet B) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedSemigroup R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe
        R.isFellerKernelSemigroup_onePointKernelSemigroup
        hK t
        (onePointLiveHomeomorph x) (onePointLiveHomeomorph '' B) =
      R.kernelSemigroup t x B := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  let live : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X)
  let e := onePointLiveHomeomorph (X := X)
  have heB : MeasurableSet (e '' B) :=
    e.toMeasurableEquiv.measurableEmbedding.measurableSet_image.mpr hB
  have hcoeB : MeasurableSet (((↑) : X → OnePoint X) '' B) :=
    OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr hB
  have himage : Subtype.val '' (e '' B) = ((↑) : X → OnePoint X) '' B := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨e y, ⟨y, hy, rfl⟩, rfl⟩
  rw [IsConservative.killedSemigroup_apply_apply
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe
    R.isFellerKernelSemigroup_onePointKernelSemigroup
    hK t
    (onePointLiveHomeomorph x) heB]
  change IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X)
        (ContinuousPath.killedEvent live t (Subtype.val '' (e '' B))) = _
  rw [himage]
  have hae := R.ae_lt_onePoint_exitTime_iff_mem rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact hK x t
  have hevent : ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      (omega ∈ ContinuousPath.killedEvent live t
          (((↑) : X → OnePoint X) '' B) ↔
        omega t ∈ ((↑) : X → OnePoint X) '' B) := by
    filter_upwards [hae] with omega homega
    have homega' : ((t : ℝ≥0∞) < ContinuousPath.exitTime
        (Set.range ((↑) : X → OnePoint X)) omega ↔
      omega t ∈ Set.range ((↑) : X → OnePoint X)) := homega
    rw [ContinuousPath.mem_killedEvent_iff, homega']
    exact and_iff_right_of_imp fun h ↦ Set.mem_of_mem_of_subset h (Set.image_subset_range _ _)
  have hmeasure :
      IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            (ContinuousPath.killedEvent live t (((↑) : X → OnePoint X) '' B)) =
        IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            ((fun omega : ContinuousPath (OnePoint X) ↦ omega t) ⁻¹'
              (((↑) : X → OnePoint X) '' B)) := by
    apply measure_congr
    filter_upwards [hevent] with omega homega
    exact propext homega
  rw [hmeasure]
  change (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X))
      (ContinuousPath.coordinateProcess t ⁻¹' (((↑) : X → OnePoint X) '' B)) =
    R.kernelSemigroup t x B
  rw [← Kernel.map_apply'
    (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup) (hf :=
          ContinuousPath.measurable_coordinateProcess t)
    (x : OnePoint X) hcoeB]
  change ((IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup).map (fun omega => omega t) (x : OnePoint X))
      (((↑) : X → OnePoint X) '' B) =
    R.kernelSemigroup t x B
  rw [R.isFellerKernelSemigroup_onePointKernelSemigroup.continuousProcess_map_eval_nnreal
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      hK t,
    R.onePointKernelSemigroup_apply_coe, Measure.add_apply,
    Measure.map_apply OnePoint.continuous_coe.measurable hcoeB,
    Measure.smul_apply, Measure.dirac_apply' OnePoint.infty hcoeB]
  simp only [Set.preimage_image_eq B OnePoint.coe_injective,
    Set.indicator_of_notMem (OnePoint.infty_notMem_image_coe (s := B)), smul_zero, add_zero]

/-- The ambient killed kernel of the one-point process is the pushforward of the original
sub-Markov transition law. -/
theorem killedKernel_onePointLive_eq_map
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (t : NNReal) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedKernel R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe t
        (x : OnePoint X) =
      (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  let live : Set (OnePoint X) := Set.range ((↑) : X → OnePoint X)
  apply Measure.ext
  intro A hA
  have hAlive : MeasurableSet (A ∩ live) := hA.inter OnePoint.isOpen_range_coe.measurableSet
  have hae := R.ae_lt_onePoint_exitTime_iff_mem rho hrho_cont hrho_pos hrho_lipschitz
    hrho_compact hK x t
  rw [IsConservative.killedKernel_apply R.onePointKernelSemigroup
    R.isConservative_onePointKernelSemigroup live OnePoint.isOpen_range_coe t
    (x : OnePoint X) hA]
  have hevent : ∀ᵐ omega ∂IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X),
      (omega ∈ ContinuousPath.killedEvent live t A ↔ omega t ∈ A ∩ live) := by
    filter_upwards [hae] with omega homega
    have homega' : ((t : ℝ≥0∞) < ContinuousPath.exitTime
        (Set.range ((↑) : X → OnePoint X)) omega ↔
      omega t ∈ Set.range ((↑) : X → OnePoint X)) := homega
    rw [ContinuousPath.mem_killedEvent_iff, homega']
    exact and_comm
  have hmeasure :
      IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            (ContinuousPath.killedEvent live t A) =
        IsConservative.continuousProcess R.onePointKernelSemigroup
          R.isConservative_onePointKernelSemigroup (x : OnePoint X)
            ((fun omega : ContinuousPath (OnePoint X) ↦ omega t) ⁻¹' (A ∩ live)) := by
    apply measure_congr
    filter_upwards [hevent] with omega homega
    exact propext homega
  rw [hmeasure]
  change (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup (x : OnePoint X))
      (ContinuousPath.coordinateProcess t ⁻¹' (A ∩ live)) =
    (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) A
  rw [← Kernel.map_apply'
    (IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup) (hf :=
          ContinuousPath.measurable_coordinateProcess t)
    (x : OnePoint X) hAlive]
  change ((IsConservative.continuousProcess R.onePointKernelSemigroup
      R.isConservative_onePointKernelSemigroup).map (fun omega => omega t) (x : OnePoint X))
      (A ∩ live) =
    (R.kernelSemigroup t x).map ((↑) : X → OnePoint X) A
  rw [R.isFellerKernelSemigroup_onePointKernelSemigroup.continuousProcess_map_eval_nnreal
      R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
      hK t,
    R.onePointKernelSemigroup_apply_coe, Measure.add_apply,
    Measure.map_apply OnePoint.continuous_coe.measurable hAlive,
    Measure.smul_apply, Measure.dirac_apply' OnePoint.infty hAlive,
    Measure.map_apply OnePoint.continuous_coe.measurable hA]
  have hinf : OnePoint.infty ∉ A ∩ live := fun h ↦ OnePoint.infty_notMem_range_coe h.2
  rw [Set.indicator_of_notMem hinf, smul_zero, add_zero]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_inter_iff]
  exact and_iff_left ⟨y, rfl⟩

/-- Extend a nonnegative observable on the live space by zero at infinity. -/
def onePointLiveExtension (f : X → ℝ≥0∞) : OnePoint X → ℝ≥0∞ :=
  OnePoint.rec 0 f

omit [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The zero extension of a function on the live space agrees with it at live points. -/
@[simp] theorem onePointLiveExtension_coe (f : X → ℝ≥0∞) (x : X) :
    onePointLiveExtension f (x : OnePoint X) = f x := rfl

omit [MetricSpace X] [LocallyCompactSpace X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- The zero extension vanishes at the added point. -/
@[simp] theorem onePointLiveExtension_infty (f : X → ℝ≥0∞) :
    onePointLiveExtension f OnePoint.infty = 0 := rfl

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- Zero extension from the live space is measurable. -/
theorem measurable_onePointLiveExtension {f : X → ℝ≥0∞} (hf : Measurable f) :
    Measurable (onePointLiveExtension f) := by
  intro A hA
  by_cases hzero : (0 : ℝ≥0∞) ∈ A
  · have hpre : onePointLiveExtension f ⁻¹' A =
        ((↑) : X → OnePoint X) '' (f ⁻¹' A) ∪ {OnePoint.infty} := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointLiveExtension_infty, hzero,
          Set.mem_union, OnePoint.infty_notMem_image_coe, Set.mem_singleton_iff, or_true]
      | coe x => simp only [Set.mem_preimage, onePointLiveExtension_coe, Set.mem_union,
          Set.mem_image, OnePoint.coe_eq_coe, exists_eq_right, OnePoint.coe_ne_infty,
          Set.mem_singleton_iff, or_false]
    rw [hpre]
    exact (OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr
      (hf hA)).union OnePoint.isClosed_infty.measurableSet
  · have hpre : onePointLiveExtension f ⁻¹' A =
        ((↑) : X → OnePoint X) '' (f ⁻¹' A) := by
      ext z
      induction z using OnePoint.rec with
      | infty => simp only [Set.mem_preimage, onePointLiveExtension_infty, hzero,
          OnePoint.infty_notMem_image_coe]
      | coe x => simp only [Set.mem_preimage, onePointLiveExtension_coe, Set.mem_image,
          OnePoint.coe_eq_coe, exists_eq_right]
    rw [hpre]
    exact OnePoint.isOpenEmbedding_coe.measurableEmbedding.measurableSet_image.mpr (hf hA)

/-- The killed resolvent of the one-point process, on an observable extended by zero at
infinity, is the kernel resolvent of the original sub-Markov semigroup. -/
theorem killedResolvent_onePointLive_eq_kernelResolvent
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (lam : ℝ) {f : X → ℝ≥0∞} (hf : Measurable f) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe lam
        (onePointLiveExtension f) (x : OnePoint X) =
      R.kernelSemigroup.kernelResolvent lam f x := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  unfold IsConservative.killedResolvent SubMarkovKernelSemigroup.kernelResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  change ENNReal.ofReal (Real.exp (-lam * t)) *
      (∫⁻ y, onePointLiveExtension f y ∂IsConservative.killedKernel
        R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe
        (Real.toNNReal t) (x : OnePoint X)) =
    ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ y, f y ∂R.kernelSemigroup (Real.toNNReal t) x
  congr 1
  rw [R.killedKernel_onePointLive_eq_map rho hrho_cont hrho_pos hrho_lipschitz hrho_compact hK,
    lintegral_map
    (measurable_onePointLiveExtension hf) OnePoint.continuous_coe.measurable]
  rfl

/-- For a nonnegative `C₀` observable, the killed resolvent is the originally supplied analytic
resolvent, evaluated at the starting point. -/
theorem killedResolvent_onePointLive_ofReal_eq_operator
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (mu : Semigroup.PositiveShift) (f : C₀(X, ℝ)) (hf0 : ∀ y, 0 ≤ f y) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe (mu : ℝ)
        (onePointLiveExtension fun y ↦ ENNReal.ofReal (f y)) (x : OnePoint X) =
      ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  calc
    IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe (mu : ℝ)
        (onePointLiveExtension fun y ↦ ENNReal.ofReal (f y)) (x : OnePoint X) =
      R.kernelSemigroup.kernelResolvent (mu : ℝ) (fun y ↦ ENNReal.ofReal (f y)) x :=
        R.killedResolvent_onePointLive_eq_kernelResolvent rho hrho_cont hrho_pos
          hrho_lipschitz hrho_compact hK mu
          (ENNReal.measurable_ofReal.comp f.continuous.measurable) x
    _ = ENNReal.ofReal
        (R.isFellerKernelSemigroup_kernelSemigroup.c0Semigroup.resolvent mu f x) :=
      R.isFellerKernelSemigroup_kernelSemigroup.kernelResolvent_ofReal_eq_resolvent
        mu f hf0 x
    _ = ENNReal.ofReal (R.toContractiveResolvent.operator mu f x) := by
      rw [R.resolvent_c0Semigroup_kernelSemigroup]

/-- The Laplace transform of the finite exit time from the live part is one minus the shift
times the original kernel resolvent of one. -/
theorem lintegral_exp_neg_onePoint_exitTime
    (R : PositiveC0ContractiveResolvent X) (rho : X → ℝ) (hrho_cont : Continuous rho)
    (hrho_pos : ∀ x, 0 < rho x) (hrho_lipschitz : LipschitzWith 1 rho)
    (hrho_compact : ∀ epsilon > 0, IsCompact {x | epsilon ≤ rho x})
    (hK : letI :=
        OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
      letI : CompleteSpace (OnePoint X) :=
        completeSpace_of_isComplete_univ isCompact_univ.isComplete
      R.onePointKernelSemigroup.KolmogorovRegular
      R.isConservative_onePointKernelSemigroup)
    (lam : ℝ) (hlam : 0 < lam) (x : X) :
    letI := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
    letI : CompleteSpace (OnePoint X) :=
      completeSpace_of_isComplete_univ isCompact_univ.isComplete
    ∫⁻ omega, ({omega | ContinuousPath.exitTime
        (Set.range ((↑) : X → OnePoint X)) omega < ⊤} : Set _).indicator
        (fun omega ↦ ENNReal.ofReal (Real.exp (-lam *
          (ContinuousPath.exitTime
            (Set.range ((↑) : X → OnePoint X)) omega).toReal))) omega
      ∂IsConservative.continuousProcess R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup (x : OnePoint X) =
      1 - ENNReal.ofReal lam *
        R.kernelSemigroup.kernelResolvent lam (fun _ : X ↦ 1) x := by
  let := OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact
  let : CompleteSpace (OnePoint X) :=
    completeSpace_of_isComplete_univ isCompact_univ.isComplete
  have hUexh : @IsOpen (OnePoint X)
      (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz
        hrho_compact).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
      (Set.range ((↑) : X → OnePoint X)) :=
    OnePoint.isOpen_range_coe
  have hlem := @IsConservative.lintegral_exp_neg_exitTime (OnePoint X)
    (OnePoint.exhaustionMetricSpace rho hrho_cont hrho_pos hrho_lipschitz hrho_compact)
    inferInstance OnePoint.instMeasurableSpace inferInstance inferInstance inferInstance
    R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
    (Set.range ((↑) : X → OnePoint X)) hUexh lam hlam
    (x : OnePoint X)
  trans (1 - ENNReal.ofReal lam *
      IsConservative.killedResolvent R.onePointKernelSemigroup
        R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) hUexh lam (fun _ : OnePoint X ↦ 1) x)
  · exact hlem
  congr 2
  unfold IsConservative.killedResolvent SubMarkovKernelSemigroup.kernelResolvent
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t _ht
  change ENNReal.ofReal (Real.exp (-lam * t)) *
      (∫⁻ _y, 1 ∂IsConservative.killedKernel
        R.onePointKernelSemigroup R.isConservative_onePointKernelSemigroup
        (Set.range ((↑) : X → OnePoint X)) OnePoint.isOpen_range_coe
        (Real.toNNReal t) (x : OnePoint X)) =
    ENNReal.ofReal (Real.exp (-lam * t)) *
      ∫⁻ _y, 1 ∂R.kernelSemigroup (Real.toNNReal t) x
  congr 1
  rw [R.killedKernel_onePointLive_eq_map rho hrho_cont hrho_pos hrho_lipschitz hrho_compact hK,
    lintegral_map measurable_const OnePoint.continuous_coe.measurable]

end MarkovProcess.PositiveC0ContractiveResolvent

end

end PortComputability
