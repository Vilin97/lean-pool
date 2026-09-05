/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.Foundations
public import Mathlib.Analysis.Complex.Exponential
import all LeanPool.EhrhartVolumeInequality.Foundations
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.RegularityCompacts

/-!
# Ehrhart volume inequality: Variation

Variational envelopes and torus analytic estimates.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace MomentTargetDanskin

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentExistence MomentPotentialExistence MomentFunctionalCoercivity
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentTargetGeodesicVariation
open scoped BigOperators ENNReal NNReal Topology

private theorem finiteEnergySourceGradient_eq_of_phase_maximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (p x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (hmax : ∀ z : Space n,
      phase p F.potential z ≤ phase p F.potential x) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x = p := by
  classical
  ext i
  let w : Space n := Pi.single i (1 : ℝ)
  have hline : HasDerivAt
      (fun t : ℝ => x + t • w) w 0 := by
    simpa only [hasDerivAt_const_add_iff, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add x
  have hpair : HasDerivAt
      (fun t : ℝ =>
        SupportFunction.pairing p (x + t • w))
      (SupportFunction.pairing p w) 0 := by
    simpa only [MonomialDivergence.pairing_add_right, MonomialDivergence.pairing_smul_right,
      hasDerivAt_const_add_iff, id_eq, one_mul] using
      ((hasDerivAt_id (0 : ℝ)).mul_const
        (SupportFunction.pairing p w)).const_add
          (SupportFunction.pairing p x)
  have hpot : HasDerivAt
      (fun t : ℝ => F.potential (x + t • w))
      ((fderiv ℝ F.potential x) w) 0 := by
    have hzero : x = (fun t : ℝ => x + t • w) 0 := by
      simp only [zero_smul, add_zero]
    simpa only [comp_def] using
      hx.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline hzero
  have hphase : HasDerivAt
      (fun t : ℝ => phase p F.potential (x + t • w))
      (SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w) 0 := by
    change HasDerivAt
      (fun t : ℝ =>
        SupportFunction.pairing p (x + t • w) -
          F.potential (x + t • w))
      (SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w) 0
    exact hpair.fun_sub hpot
  have hlocal : IsLocalMax
      (fun t : ℝ => phase p F.potential (x + t • w)) 0 :=
    Filter.Eventually.of_forall
      (fun t => by simpa only [zero_smul, add_zero] using hmax (x + t • w))
  have hzero :
      SupportFunction.pairing p w -
        (fderiv ℝ F.potential x) w = 0 := by
    have hd := hphase.deriv
    rw [hlocal.deriv_eq_zero] at hd
    linarith
  have hpairing :
      SupportFunction.pairing
        (SpatialBergmanFatouScheffe.actualGradient
          F.potential x) w =
        SupportFunction.pairing p w := by
    rw [SpatialBergmanFatouScheffe.pairing_actualGradient_eq_fderiv]
    linarith
  simpa [w, SupportFunction.pairing, Pi.single_apply]
    using hpairing

private theorem exists_finiteEnergyTargetGeodesic_approximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t ε : ℝ) (hε : 0 < ε) :
    ∃ p ∈ finiteEnergyFiniteTargetSet F,
      finiteEnergyTargetGeodesic F v t x - ε <
        finiteEnergyTargetDualPhase F v t p x := by
  have hlt :
      finiteEnergyTargetGeodesic F v t x - ε <
        finiteEnergyTargetGeodesic F v t x :=
    sub_lt_self _ hε
  change
    finiteEnergyTargetGeodesic F v t x - ε <
      sSup
        ((fun p : Space n =>
          finiteEnergyTargetDualPhase F v t p x) ''
            finiteEnergyFiniteTargetSet F) at hlt
  obtain ⟨_, ⟨p, hp, rfl⟩, happrox⟩ :=
    exists_lt_of_lt_csSup
      ((finiteEnergyFiniteTargetSet_nonempty F).image _) hlt
  exact ⟨p, hp, happrox⟩

private def finiteEnergyTargetQuadraticApproximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t : ℝ) : Space n :=
  if ht : t = 0 then 0 else
    (exists_finiteEnergyTargetGeodesic_approximateMaximizer
      F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose

private theorem finiteEnergyTargetQuadraticApproximateMaximizer_mem
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (t : ℝ) :
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t ∈
      finiteEnergyFiniteTargetSet F := by
  classical
  unfold finiteEnergyTargetQuadraticApproximateMaximizer
  split_ifs with ht
  · exact zero_mem_finiteEnergyFiniteTargetSet F
  · exact
      (exists_finiteEnergyTargetGeodesic_approximateMaximizer
        F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose_spec.1

private theorem finiteEnergyTargetQuadraticApproximateMaximizer_phase
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      finiteEnergyTargetDualPhase F v t
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t) x := by
  classical
  unfold finiteEnergyTargetQuadraticApproximateMaximizer
  simp only [dite_eq_right ht]
  exact
    (exists_finiteEnergyTargetGeodesic_approximateMaximizer
      F v x t (t ^ 2) (sq_pos_of_ne_zero ht)).choose_spec.2

private theorem finiteEnergyTargetQuadraticApproximateMaximizer_phase_defect
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x z : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    phase
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t)
        F.potential z -
      phase
        (finiteEnergyTargetQuadraticApproximateMaximizer
          F v x t)
        F.potential x ≤
      2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2 := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  have hp := finiteEnergyTargetQuadraticApproximateMaximizer_mem
    F v x t
  have happrox :=
    finiteEnergyTargetQuadraticApproximateMaximizer_phase
      F v x ht
  have hfenchel := finiteEnergyFiniteTarget_fenchel F hp z
  have hclose := (abs_le.mp
    (finiteEnergyTargetGeodesic_uniform_error F v t x)).1
  have htest := abs_targetTest_le_finiteEnergyTargetTestBound
    K v hp.1
  have htbound : -t * v p ≤
      |t| * finiteEnergyTargetTestBound K v := by
    calc
      -t * v p = -(t * v p) := by ring
      _ ≤ |t * v p| := neg_le_abs _
      _ = |t| * |v p| := abs_mul _ _
      _ ≤ |t| * finiteEnergyTargetTestBound K v :=
        mul_le_mul_of_nonneg_left htest (abs_nonneg t)
  unfold finiteEnergyTargetDualPhase at happrox
  unfold phase
  change
    SupportFunction.pairing p z - F.potential z -
      (SupportFunction.pairing p x - F.potential x) ≤ _
  change
    SupportFunction.pairing p z -
      (sourceExtendedBodyLegendre F.potential p).toReal ≤
        F.potential z at hfenchel
  change
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p at happrox
  linarith

private theorem tendsto_finiteEnergyTargetQuadraticApproximateMaximizer
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    Tendsto
      (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (SpatialBergmanFatouScheffe.actualGradient
        F.potential x)) := by
  have herror :
      Tendsto
        (fun t : ℝ =>
          2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hcont : Continuous
        (fun t : ℝ =>
          2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2) :=
      ((continuous_const.mul continuous_id.abs).mul
        continuous_const).add (continuous_id.pow 2)
    simpa only [abs_zero, mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow,
      add_zero] using
      (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  refine K.compact.tendsto_nhds_of_unique_mapClusterPt ?_ ?_
  · exact Filter.Eventually.of_forall fun t =>
      (finiteEnergyTargetQuadraticApproximateMaximizer_mem
        F v x t).1
  · intro q _hq hcluster
    symm
    apply finiteEnergySourceGradient_eq_of_phase_maximizer
      F q x hx
    intro z
    by_contra hnot
    have hgap :
        0 < phase q F.potential z - phase q F.potential x := by
      linarith [lt_of_not_ge hnot]
    have hsmall : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        2 * |t| * finiteEnergyTargetTestBound K v + t ^ 2 <
          (phase q F.potential z -
            phase q F.potential x) / 2 :=
      herror.eventually (gt_mem_nhds (half_pos hgap))
    have hevent : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        phase (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) F.potential z -
          phase (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) F.potential x ≤
          (phase q F.potential z -
            phase q F.potential x) / 2 := by
      filter_upwards [hne, hsmall] with t ht hlt
      exact
        (finiteEnergyTargetQuadraticApproximateMaximizer_phase_defect
          F v x z ht).trans hlt.le
    have hmap :
        ∀ᶠ p : Space n in
          Filter.map
            (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
            (𝓝[≠] (0 : ℝ)),
          phase p F.potential z - phase p F.potential x ≤
            (phase q F.potential z -
              phase q F.potential x) / 2 := by
      exact hevent
    let l : Filter (Space n) :=
      𝓝 q ⊓ Filter.map
        (finiteEnergyTargetQuadraticApproximateMaximizer F v x)
        (𝓝[≠] (0 : ℝ))
    have : l.NeBot := hcluster
    have hphasez : Continuous
        (fun p : Space n => phase p F.potential z) := by
      unfold phase
      exact (SupportFunction.continuous_pairing_left z).fun_sub
        continuous_const
    have hphasex : Continuous
        (fun p : Space n => phase p F.potential x) := by
      unfold phase
      exact (SupportFunction.continuous_pairing_left x).fun_sub
        continuous_const
    have hlimit :
        Tendsto
          (fun p : Space n =>
            phase p F.potential z - phase p F.potential x)
          l
          (𝓝 (phase q F.potential z - phase q F.potential x)) :=
      (hphasez.sub hphasex).continuousAt.tendsto.mono_left
        inf_le_left
    have hle := le_of_tendsto hlimit
      (hmap.filter_mono inf_le_right)
    linarith

private theorem finiteEnergyTargetGeodesic_gradient_support
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    (t : ℝ) :
    F.potential x -
        t * v
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential x) ≤
      finiteEnergyTargetGeodesic F v t x := by
  let p : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hp : p ∈ finiteEnergyFiniteTargetSet F := by
    refine ⟨finiteEnergySourceGradient_mem_carrier F x hx, ?_⟩
    rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
    exact ENNReal.ofReal_ne_top
  have h := finiteEnergyTargetDualPhase_le_geodesic
    F v t hp x
  have hleg :=
    finiteEnergySourceExtendedLegendre_actualGradient_toReal
      F x hx
  unfold finiteEnergyTargetDualPhase at h
  change
    (sourceExtendedBodyLegendre F.potential p).toReal =
      SupportFunction.pairing p x - F.potential x at hleg
  linarith

private theorem finiteEnergyTargetGeodesic_le_quadraticApproximate
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    {t : ℝ} (ht : t ≠ 0) :
    finiteEnergyTargetGeodesic F v t x ≤
      F.potential x -
        t * v
          (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) + t ^ 2 := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  have hp := finiteEnergyTargetQuadraticApproximateMaximizer_mem
    F v x t
  have happrox :=
    finiteEnergyTargetQuadraticApproximateMaximizer_phase
      F v x ht
  have hfenchel := finiteEnergyFiniteTarget_fenchel F hp x
  unfold finiteEnergyTargetDualPhase at happrox
  change
    SupportFunction.pairing p x -
      (sourceExtendedBodyLegendre F.potential p).toReal ≤
        F.potential x at hfenchel
  change
    finiteEnergyTargetGeodesic F v t x - t ^ 2 <
      SupportFunction.pairing p x -
        (sourceExtendedBodyLegendre F.potential p).toReal -
          t * v p at happrox
  linarith

private theorem finiteEnergyTargetGeodesic_differenceQuotient_error
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x)
    {t : ℝ} (ht : t ≠ 0) :
    |(finiteEnergyTargetGeodesic F v t x - F.potential x) / t +
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)| ≤
      |v (finiteEnergyTargetQuadraticApproximateMaximizer
        F v x t) -
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x)| + |t| := by
  let p : Space n :=
    finiteEnergyTargetQuadraticApproximateMaximizer F v x t
  let q : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have hlower := finiteEnergyTargetGeodesic_gradient_support
    F v x hx t
  have hupper := finiteEnergyTargetGeodesic_le_quadraticApproximate
    F v x ht
  have hnum :
      0 ≤ finiteEnergyTargetGeodesic F v t x - F.potential x +
        t * v q := by
    linarith
  have hterm :
      t * (v q - v p) ≤ |t| * |v p - v q| := by
    calc
      t * (v q - v p) ≤ |t * (v q - v p)| := le_abs_self _
      _ = |t| * |v p - v q| := by
        rw [abs_mul, abs_sub_comm]
  have hnumupper :
      finiteEnergyTargetGeodesic F v t x - F.potential x +
          t * v q ≤
        |t| * (|v p - v q| + |t|) := by
    have habssq : |t| ^ 2 = t ^ 2 := sq_abs t
    nlinarith
  have hfrac :
      (finiteEnergyTargetGeodesic F v t x - F.potential x) / t +
        v q =
      (finiteEnergyTargetGeodesic F v t x - F.potential x +
        t * v q) / t := by
    field_simp
  rw [hfrac, abs_div, abs_of_nonneg hnum]
  exact (div_le_iff₀ (abs_pos.mpr ht)).mpr (by
    simpa only [mul_comm, q, p] using hnumupper)

private theorem hasDerivAt_finiteEnergyTargetGeodesic
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    HasDerivAt
      (fun t : ℝ => finiteEnergyTargetGeodesic F v t x)
      (-(v (SpatialBergmanFatouScheffe.actualGradient
        F.potential x))) 0 := by
  let q : Space n :=
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x
  have happrox :=
    tendsto_finiteEnergyTargetQuadraticApproximateMaximizer
      F v x hx
  have htarget :
      Tendsto
        (fun t : ℝ =>
          v (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t))
        (𝓝[≠] (0 : ℝ)) (𝓝 (v q)) :=
    v.continuous.continuousAt.tendsto.comp happrox
  have htzero : Tendsto (fun t : ℝ => |t|)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [id_eq, abs_zero] using
      (continuous_id.abs.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hbound :
      Tendsto
        (fun t : ℝ =>
          |v (finiteEnergyTargetQuadraticApproximateMaximizer
            F v x t) - v q| + |t|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hconst : Tendsto (fun _ : ℝ => v q)
        (𝓝[≠] (0 : ℝ)) (𝓝 (v q)) :=
      tendsto_const_nhds
    simpa only [sub_self, abs_zero, add_zero] using (htarget.sub hconst).abs.add htzero
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  have herr :
      Tendsto
        (fun t : ℝ =>
          |(finiteEnergyTargetGeodesic F v t x -
              F.potential x) / t + v q|)
        (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    apply squeeze_zero'
      (Filter.Eventually.of_forall fun t => abs_nonneg _)
    · filter_upwards [hne] with t ht
      exact finiteEnergyTargetGeodesic_differenceQuotient_error
        F v x hx ht
    · exact hbound
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  rw [finiteEnergyTargetGeodesic_zero_eq F v x]
  apply tendsto_iff_dist_tendsto_zero.mpr
  simpa only [zero_add, smul_eq_mul, inv_mul_eq_div, Real.dist_eq, sub_neg_eq_add] using herr

/-- A first-order bound on the error of the real exponential. -/
public
theorem abs_exp_sub_one_le_mul_exp_abs (z : ℝ) :
    |Real.exp z - 1| ≤ |z| * Real.exp |z| := by
  by_cases hz : 0 ≤ z
  · have he : 0 < Real.exp z := Real.exp_pos z
    have hfirst : 0 ≤ Real.exp z - 1 :=
      sub_nonneg.mpr (Real.one_le_exp hz)
    have htan := Real.add_one_le_exp (-z)
    have hmul := mul_le_mul_of_nonneg_right htan he.le
    have hinverse : Real.exp (-z) * Real.exp z = 1 := by
      rw [← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero]
    rw [hinverse] at hmul
    rw [abs_of_nonneg hfirst, abs_of_nonneg hz]
    nlinarith
  · have hz' : z ≤ 0 := le_of_not_ge hz
    have he : 0 < Real.exp (-z) := Real.exp_pos (-z)
    have hfirst : Real.exp z - 1 ≤ 0 := by
      have h := Real.exp_le_exp.mpr hz'
      simpa only [tsub_le_iff_right, zero_add, Real.exp_le_one_iff, ge_iff_le, Real.exp_zero]
        using h
    have htan := Real.add_one_le_exp z
    have hunit : 1 ≤ Real.exp (-z) :=
      Real.one_le_exp (neg_nonneg.mpr hz')
    rw [abs_of_nonpos hfirst, abs_of_nonpos hz']
    have hnonneg : 0 ≤ -z := neg_nonneg.mpr hz'
    have hscaled := mul_le_mul_of_nonneg_left hunit hnonneg
    nlinarith

private def finiteEnergyTargetDensityDifferenceQuotient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (t : ℝ) (x : Space n) : ℝ :=
  (Real.exp (-finiteEnergyTargetGeodesic F v t x) -
    Real.exp (-F.potential x)) / t

private theorem finiteEnergyTargetDensityDifferenceQuotient_le
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    {t : ℝ} (ht : t ≠ 0) (htsmall : |t| ≤ 1)
    (x : Space n) :
    |finiteEnergyTargetDensityDifferenceQuotient F v t x| ≤
      finiteEnergyTargetTestBound K v *
        (Real.exp (finiteEnergyTargetTestBound K v) *
          Real.exp (-F.potential x)) := by
  let M : ℝ := finiteEnergyTargetTestBound K v
  let d : ℝ :=
    -(finiteEnergyTargetGeodesic F v t x - F.potential x)
  have hM : 0 ≤ M := finiteEnergyTargetTestBound_nonneg K v
  have hd : |d| ≤ |t| * M := by
    simpa [d, M, abs_sub_comm] using
      finiteEnergyTargetGeodesic_uniform_error F v t x
  have hdM : |d| ≤ M := by
    calc
      |d| ≤ |t| * M := hd
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right htsmall hM
      _ = M := one_mul M
  have he : Real.exp |d| ≤ Real.exp M :=
    Real.exp_le_exp.mpr hdM
  have hfactor :
      Real.exp (-finiteEnergyTargetGeodesic F v t x) -
          Real.exp (-F.potential x) =
        Real.exp (-F.potential x) * (Real.exp d - 1) := by
    have harg :
        -finiteEnergyTargetGeodesic F v t x =
          -F.potential x + d := by
      dsimp [d]
      ring
    rw [harg, Real.exp_add, mul_sub, mul_one]
  unfold finiteEnergyTargetDensityDifferenceQuotient
  rw [hfactor, abs_div, abs_mul,
    abs_of_pos (Real.exp_pos (-F.potential x))]
  calc
    Real.exp (-F.potential x) * |Real.exp d - 1| / |t| ≤
        Real.exp (-F.potential x) *
          (|d| * Real.exp |d|) / |t| := by
      apply (div_le_div_iff_of_pos_right (abs_pos.mpr ht)).mpr
      exact mul_le_mul_of_nonneg_left
        (abs_exp_sub_one_le_mul_exp_abs d)
        (Real.exp_pos _).le
    _ ≤ Real.exp (-F.potential x) *
          ((|t| * M) * Real.exp M) / |t| := by
      apply (div_le_div_iff_of_pos_right (abs_pos.mpr ht)).mpr
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      exact mul_le_mul hd he (Real.exp_pos _).le
        (mul_nonneg (abs_nonneg _) hM)
    _ = finiteEnergyTargetTestBound K v *
        (Real.exp (finiteEnergyTargetTestBound K v) *
          Real.exp (-F.potential x)) := by
      dsimp [M]
      field_simp [abs_ne_zero.mpr ht]

private theorem finiteEnergyTargetGeodesicPartition_zero
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    finiteEnergyTargetGeodesicPartition F v 0 =
      finiteEnergySourcePartition F := by
  unfold finiteEnergyTargetGeodesicPartition
    finiteEnergySourcePartition
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [finiteEnergyTargetGeodesic_zero_eq F v x]

private theorem tendsto_finiteEnergyTargetDensityDifferenceQuotient
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ))
    (x : Space n)
    (hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x) :
    Tendsto
      (fun t : ℝ =>
        finiteEnergyTargetDensityDifferenceQuotient F v t x)
      (𝓝[≠] (0 : ℝ))
      (𝓝 (Real.exp (-F.potential x) *
        v (SpatialBergmanFatouScheffe.actualGradient
          F.potential x))) := by
  have hd :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp (-finiteEnergyTargetGeodesic F v t x))
        (Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)) 0 := by
    simpa only [Pi.neg_apply, finiteEnergyTargetGeodesic_zero_eq F v x, neg_neg] using
      (hasDerivAt_finiteEnergyTargetGeodesic F v x hx).neg.exp
  simpa only [finiteEnergyTargetDensityDifferenceQuotient, zero_add,
    finiteEnergyTargetGeodesic_zero_eq F v x, smul_eq_mul,
    inv_mul_eq_div] using hd.tendsto_slope_zero

private theorem hasDerivAt_finiteEnergyTargetGeodesicPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    HasDerivAt
      (finiteEnergyTargetGeodesicPartition F v)
      (∫ x : Space n,
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
        ∂(volume : Measure (Space n))) 0 := by
  let M : ℝ := finiteEnergyTargetTestBound K v
  have hmajor : Integrable
      (fun x : Space n =>
        M * (Real.exp M * Real.exp (-F.potential x)))
      (volume : Measure (Space n)) :=
    (F.densityIntegrable.const_mul (Real.exp M)).const_mul M
  have hne : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), t ≠ 0 := by
    change ({0}ᶜ : Set ℝ) ∈ 𝓝[({0}ᶜ : Set ℝ)] (0 : ℝ)
    exact self_mem_nhdsWithin
  have htlim : Tendsto (fun t : ℝ => |t|)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [id_eq, abs_zero] using
      (continuous_id.abs.tendsto (0 : ℝ)).mono_left
        nhdsWithin_le_nhds
  have hsmall : ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)), |t| ≤ 1 := by
    exact
      (htlim.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))).mono
        (fun _ ht => le_of_lt ht)
  have hmeas :
      ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        AEStronglyMeasurable
          (finiteEnergyTargetDensityDifferenceQuotient F v t)
          (volume : Measure (Space n)) := by
    filter_upwards with t
    unfold finiteEnergyTargetDensityDifferenceQuotient
    exact
      ((Real.continuous_exp.comp
        (continuous_finiteEnergyTargetGeodesic F v t).neg).sub
        (Real.continuous_exp.comp
          F.potential.continuous.neg)).div_const t
        |>.aestronglyMeasurable
  have hbound :
      ∀ᶠ t : ℝ in (𝓝[≠] (0 : ℝ)),
        ∀ᵐ x : Space n
          ∂(volume : Measure (Space n)),
          ‖finiteEnergyTargetDensityDifferenceQuotient F v t x‖ ≤
            M * (Real.exp M * Real.exp (-F.potential x)) := by
    filter_upwards [hne, hsmall] with t ht htsmall
    filter_upwards with x
    simpa only [Real.norm_eq_abs] using
      finiteEnergyTargetDensityDifferenceQuotient_le
        F v ht htsmall x
  have hlim :
      ∀ᵐ x : Space n
        ∂(volume : Measure (Space n)),
        Tendsto
          (fun t : ℝ =>
            finiteEnergyTargetDensityDifferenceQuotient F v t x)
          (𝓝[≠] (0 : ℝ))
          (𝓝 (Real.exp (-F.potential x) *
            v (SpatialBergmanFatouScheffe.actualGradient
              F.potential x))) := by
    filter_upwards [ae_differentiableAt_finiteEnergySource F]
      with x hx
    exact tendsto_finiteEnergyTargetDensityDifferenceQuotient
      F v x hx
  have hdct :=
    MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (μ := (volume : Measure (Space n)))
      (F := fun t x =>
        finiteEnergyTargetDensityDifferenceQuotient F v t x)
      (f := fun x : Space n =>
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x))
      (fun x : Space n =>
        M * (Real.exp M * Real.exp (-F.potential x)))
      hmeas hbound hmajor hlim
  have hquot (t : ℝ) :
      (∫ x : Space n,
        finiteEnergyTargetDensityDifferenceQuotient F v t x
        ∂(volume : Measure (Space n))) =
        (finiteEnergyTargetGeodesicPartition F v t -
          finiteEnergySourcePartition F) / t := by
    unfold finiteEnergyTargetDensityDifferenceQuotient
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_sub
        (finiteEnergyTargetGeodesic_densityIntegrable F v t)
        F.densityIntegrable]
    rfl
  have hslope :
      Tendsto
        (fun t : ℝ =>
          (finiteEnergyTargetGeodesicPartition F v t -
            finiteEnergySourcePartition F) / t)
        (𝓝[≠] (0 : ℝ))
        (𝓝 (∫ x : Space n,
          Real.exp (-F.potential x) *
            v (SpatialBergmanFatouScheffe.actualGradient
              F.potential x)
          ∂(volume : Measure (Space n)))) := by
    convert hdct using 1
    funext t
    exact (hquot t).symm
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  simpa only [zero_add, finiteEnergyTargetGeodesicPartition_zero F v, smul_eq_mul,
    inv_mul_eq_div] using hslope

private theorem hasDerivAt_finiteEnergyTargetGeodesicLogPartition
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (v : C(Space n, ℝ)) :
    HasDerivAt
      (fun t : ℝ =>
        Real.log (finiteEnergyTargetGeodesicPartition F v t))
      (∫ p : Space n, v p
        ∂(finiteEnergySourceGradientPushforward F)) 0 := by
  have hpart := hasDerivAt_finiteEnergyTargetGeodesicPartition F v
  have hzero := finiteEnergyTargetGeodesicPartition_zero F v
  have hpos := finiteEnergySourcePartition_pos F
  have hlog := hpart.log (hzero.trans_ne hpos.ne')
  have hmoment :
      (∫ x : Space n,
        Real.exp (-F.potential x) *
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x)
        ∂(volume : Measure (Space n))) /
          finiteEnergySourcePartition F =
        ∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F) := by
    rw [integral_finiteEnergySourceGradientPushforward F v,
      integral_finiteEnergySourceGibbsProbability F
        (fun x : Space n =>
          v (SpatialBergmanFatouScheffe.actualGradient
            F.potential x))]
    congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with x
    ring
  rw [← hmoment]
  simpa only [finiteEnergyTargetGeodesicPartition_zero F v] using hlog

private theorem exists_exact_optimizer_gradientPushforward_integral_eq
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      ∀ v : C(Space n, ℝ),
        (∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F)) =
        ∫ p : Space n, v p
          ∂(normalizedTargetBodyMeasure K) := by
  obtain ⟨F, hsup, hmax, hineq⟩ :=
    exists_exact_optimizer_targetGeodesic_logPartition_le K
  refine ⟨F, hsup, hmax, ?_⟩
  intro v
  let A : ℝ :=
    ∫ p : Space n, v p
      ∂(normalizedTargetBodyMeasure K)
  let H : ℝ → ℝ := fun t =>
    Real.log (finiteEnergyTargetGeodesicPartition F v t) -
      t * A
  have hlocal : IsLocalMax H 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    dsimp [H, A]
    simp only [zero_mul, sub_zero,
      finiteEnergyTargetGeodesicPartition_zero F v]
    linarith [hineq v t]
  have hd :=
    (hasDerivAt_finiteEnergyTargetGeodesicLogPartition F v).fun_sub
      ((hasDerivAt_id (0 : ℝ)).mul_const A)
  have hderiv :
      deriv
        (fun t : ℝ =>
          Real.log (finiteEnergyTargetGeodesicPartition F v t) -
            t * A) 0 =
        (∫ p : Space n, v p
          ∂(finiteEnergySourceGradientPushforward F)) - A := by
    simpa only [id, one_mul] using hd.deriv
  have hzero :
      deriv
        (fun t : ℝ =>
          Real.log (finiteEnergyTargetGeodesicPartition F v t) -
            t * A) 0 = 0 := by
    simpa only using hlocal.deriv_eq_zero
  change
    (∫ p : Space n, v p
      ∂(finiteEnergySourceGradientPushforward F)) = A
  linarith

private theorem exists_exact_optimizer_gradientPushforward_eq
    {n : ℕ} (K : CenteredBody n) :
    ∃ F : SourceFiniteEnergyPotential K,
      finiteEnergySourceBermanFunctional F =
        sSup
          (Set.range
            (fun D : SourceMomentPotential K =>
              sourceMomentBermanFunctional D)) ∧
      (∀ G : SourceFiniteEnergyPotential K,
        finiteEnergySourceBermanFunctional G ≤
          finiteEnergySourceBermanFunctional F) ∧
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K := by
  obtain ⟨F, hsup, hmax, htest⟩ :=
    exists_exact_optimizer_gradientPushforward_integral_eq K
  refine ⟨F, hsup, hmax, ?_⟩
  let : IsProbabilityMeasure
      (finiteEnergySourceGradientPushforward F) :=
    finiteEnergySourceGradientPushforward_isProbability F
  let : IsProbabilityMeasure (normalizedTargetBodyMeasure K) :=
    normalizedTargetBodyMeasure_isProbability K
  let μ : MeasureTheory.FiniteMeasure (Space n) :=
    ⟨finiteEnergySourceGradientPushforward F, inferInstance⟩
  let ν : MeasureTheory.FiniteMeasure (Space n) :=
    ⟨normalizedTargetBodyMeasure K, inferInstance⟩
  have heq : μ = ν := by
    apply MeasureTheory.FiniteMeasure.ext_of_forall_integral_eq
    intro v
    exact htest v.toContinuousMap
  exact congrArg (fun q : MeasureTheory.FiniteMeasure
    (Space n) => (q : Measure (Space n))) heq

end MomentTargetDanskin

namespace MomentRegularity

open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open scoped ENNReal Topology

private theorem finiteEnergySourceGradient_mem_carrier_everywhere
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    SpatialBergmanFatouScheffe.actualGradient
      F.potential x ∈ K.carrier := by
  by_cases hx : DifferentiableAt ℝ
      (F.potential : Space n → ℝ) x
  · exact finiteEnergySourceGradient_mem_carrier F x hx
  · have hzero :
        SpatialBergmanFatouScheffe.actualGradient
          F.potential x = 0 := by
      ext i
      change
        (fderiv ℝ (F.potential : Space n → ℝ) x)
          (Pi.single i (1 : ℝ)) = 0
      rw [fderiv_zero_of_not_differentiableAt hx]
      simp only [zero_apply]
    rw [hzero]
    exact interior_subset (LatticeAsymptotics.zero_mem_interior K)

private theorem normalizedTargetBodyMeasure_eq_interior_restrict
    {n : ℕ} (K : CenteredBody n) :
    normalizedTargetBodyMeasure K =
      ((volume : Measure (Space n)) K.carrier)⁻¹ •
        ((volume : Measure (Space n)).restrict
          (interior K.carrier)) := by
  have hrestrict :
      (volume : Measure (Space n)).restrict
          (interior K.carrier) =
        (volume : Measure (Space n)).restrict K.carrier :=
    Measure.restrict_congr_set
      (interior_ae_eq_of_null_frontier
        (K.convex.addHaar_frontier
          (volume : Measure (Space n))))
  unfold normalizedTargetBodyMeasure
  rw [hrestrict]

private theorem ae_normalizedTargetBodyMeasure_mem_interior
    {n : ℕ} (K : CenteredBody n) :
    ∀ᵐ p : Space n
      ∂(normalizedTargetBodyMeasure K),
      p ∈ interior K.carrier := by
  rw [normalizedTargetBodyMeasure_eq_interior_restrict K]
  exact Measure.ae_smul_measure
    (MeasureTheory.ae_restrict_mem
      isOpen_interior.measurableSet)
    (((volume : Measure (Space n)) K.carrier)⁻¹)

private theorem volume_absolutelyContinuous_finiteEnergySourceGibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (volume : Measure (Space n)) ≪
      finiteEnergySourceGibbsProbability F := by
  change
    (volume : Measure (Space n)) ≪
      (volume : Measure (Space n)).withDensity
        (fun x => ENNReal.ofReal
          (WeightedPoincare.normalizedDensity
            F.potential x))
  apply MeasureTheory.withDensity_absolutelyContinuous'
  · exact
      ((Real.continuous_exp.comp F.potential.continuous.neg).div_const
        (WeightedPoincare.partition F.potential)).measurable
          |>.ennreal_ofReal.aemeasurable
  · filter_upwards with x
    exact
      (ENNReal.ofReal_pos.mpr
        (WeightedPoincare.normalizedDensity_pos
          F.densityIntegrable x)).ne'

private theorem ae_finiteEnergySourceGradient_mem_interior_gibbs
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(finiteEnergySourceGibbsProbability F),
      SpatialBergmanFatouScheffe.actualGradient
        F.potential x ∈ interior K.carrier := by
  have htarget :
      ∀ᵐ p : Space n
        ∂(finiteEnergySourceGradientPushforward F),
        p ∈ interior K.carrier := by
    rw [htransport]
    exact ae_normalizedTargetBodyMeasure_mem_interior K
  unfold finiteEnergySourceGradientPushforward at htarget
  exact
    (MeasureTheory.ae_map_iff
      (measurable_finiteEnergySourceGradient F).aemeasurable
      isOpen_interior.measurableSet).mp htarget

private theorem ae_finiteEnergySourceGradient_mem_interior_volume
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ∀ᵐ x : Space n
      ∂(volume : Measure (Space n)),
      SpatialBergmanFatouScheffe.actualGradient
        F.potential x ∈ interior K.carrier := by
  exact
    (volume_absolutelyContinuous_finiteEnergySourceGibbs F).ae_le
      (ae_finiteEnergySourceGradient_mem_interior_gibbs F htransport)

private theorem normalizedTargetBodyMeasure_open_pos_of_inter_interior
    {n : ℕ} (K : CenteredBody n)
    {U : Set (Space n)} (hU : IsOpen U)
    (hinter : (U ∩ interior K.carrier).Nonempty) :
    0 < normalizedTargetBodyMeasure K U := by
  have hinner :
      0 < (volume : Measure (Space n))
        (U ∩ interior K.carrier) :=
    (hU.inter isOpen_interior).measure_pos
      (volume : Measure (Space n)) hinter
  have hbody :
      0 < (volume : Measure (Space n))
        (U ∩ K.carrier) :=
    lt_of_lt_of_le hinner
      (measure_mono (inter_subset_inter_right U interior_subset))
  have hscale :
      0 < ((volume : Measure (Space n))
        K.carrier)⁻¹ :=
    ENNReal.inv_pos.mpr K.compact.measure_ne_top
  unfold normalizedTargetBodyMeasure
  rw [Measure.smul_apply,
    Measure.restrict_apply hU.measurableSet]
  exact ENNReal.mul_pos hscale.ne' hbody.ne'

private def momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) : ℝ :=
  F.potential x +
    Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier)

private theorem exp_neg_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    Real.exp (-momentNormalizedPotential F x) =
      (normalizedVolume K.carrier /
        finiteEnergySourcePartition F) *
          Real.exp (-F.potential x) := by
  have hratio :
      0 < finiteEnergySourcePartition F /
        normalizedVolume K.carrier :=
    div_pos (finiteEnergySourcePartition_pos F) K.volume_pos
  unfold momentNormalizedPotential
  calc
    Real.exp
        (-(F.potential x +
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier))) =
        Real.exp
          (-Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
          Real.exp (-F.potential x) := by
            rw [← Real.exp_add]
            congr 1
            ring
    _ =
        (normalizedVolume K.carrier /
          finiteEnergySourcePartition F) *
            Real.exp (-F.potential x) := by
          rw [Real.exp_neg, Real.exp_log hratio, inv_div]

private theorem integral_exp_neg_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    (∫ x : Space n,
      Real.exp (-momentNormalizedPotential F x)
      ∂(volume : Measure (Space n))) =
        normalizedVolume K.carrier := by
  calc
    (∫ x : Space n,
      Real.exp (-momentNormalizedPotential F x)
      ∂(volume : Measure (Space n))) =
        ∫ x : Space n,
          (normalizedVolume K.carrier /
            finiteEnergySourcePartition F) *
              Real.exp (-F.potential x)
          ∂(volume : Measure (Space n)) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      exact exp_neg_momentNormalizedPotential F x
    _ = (normalizedVolume K.carrier /
          finiteEnergySourcePartition F) *
        finiteEnergySourcePartition F := by
      rw [MeasureTheory.integral_const_mul]
      rfl
    _ = normalizedVolume K.carrier := by
      field_simp [(finiteEnergySourcePartition_pos F).ne']

end MomentRegularity

namespace MomentMonotoneTransport

open Set Function Filter MeasureTheory
open MomentOptimizer MomentWeakFirstVariation MomentFirstVariation MomentTargetGeodesic
open MomentRegularity
open scoped BigOperators ENNReal Topology

private def finiteEnergyDifferentiableGradientImage
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) : Set (Space n) :=
  SpatialBergmanFatouScheffe.actualGradient F.potential ''
    {x : Space n |
      DifferentiableAt ℝ
        (F.potential : Space n → ℝ) x}

private theorem interior_subset_closure_finiteEnergyDifferentiableGradientImage
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    interior K.carrier ⊆
      closure (finiteEnergyDifferentiableGradientImage F) := by
  intro p hp
  apply mem_closure_iff.mpr
  intro U hU hpU
  by_contra hnonempty
  have hno :
      ∀ x : Space n,
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x →
        SpatialBergmanFatouScheffe.actualGradient
          F.potential x ∉ U := by
    intro x hx hgrad
    apply hnonempty
    exact ⟨SpatialBergmanFatouScheffe.actualGradient
      F.potential x, hgrad, ⟨x, hx, rfl⟩⟩
  have hae_diff :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        DifferentiableAt ℝ
          (F.potential : Space n → ℝ) x :=
    finiteEnergySourceGibbs_ae_of_volume F _
      (ae_differentiableAt_finiteEnergySource F)
  have hae_not :
      ∀ᵐ x : Space n
        ∂(finiteEnergySourceGibbsProbability F),
        x ∉
          (SpatialBergmanFatouScheffe.actualGradient
            F.potential) ⁻¹' U := by
    filter_upwards [hae_diff] with x hx
    exact hno x hx
  have hzero :
      finiteEnergySourceGibbsProbability F
        ((SpatialBergmanFatouScheffe.actualGradient
          F.potential) ⁻¹' U) = 0 := by
    exact MeasureTheory.measure_eq_zero_iff_ae_notMem.mpr hae_not
  have htarget : normalizedTargetBodyMeasure K U = 0 := by
    rw [← htransport]
    unfold finiteEnergySourceGradientPushforward
    rw [Measure.map_apply
      (measurable_finiteEnergySourceGradient F)
      hU.measurableSet]
    exact hzero
  exact
    (ne_of_gt
      (normalizedTargetBodyMeasure_open_pos_of_inter_interior
        K hU ⟨p, hpU, hp⟩)) htarget

private theorem closure_finiteEnergyDifferentiableGradientImage_eq_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    closure (finiteEnergyDifferentiableGradientImage F) =
      K.carrier := by
  apply le_antisymm
  · apply closure_minimal _ K.compact.isClosed
    rintro p ⟨x, _hx, rfl⟩
    exact finiteEnergySourceGradient_mem_carrier_everywhere F x
  · have hsubset :=
      closure_mono
        (interior_subset_closure_finiteEnergyDifferentiableGradientImage
          F htransport)
    have hbody : closure (interior K.carrier) = K.carrier := by
      simpa only [K.compact.isClosed.closure_eq] using
        K.convex.closure_interior_eq_closure_of_nonempty_interior
          K.fullDimensional
    rw [hbody, closure_closure] at hsubset
    exact hsubset

end MomentMonotoneTransport

namespace MomentInteriorLegendre

open Set Function Filter MeasureTheory
open LaplaceAsymptotics MomentFunctionalCoercivity MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentMonotoneTransport
open scoped BigOperators ENNReal Topology

private theorem finiteEnergySourcePhase_affine_target
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (p q x : Space n) (a b : ℝ)
    (hab : a + b = 1) :
    phase (a • p + b • q) F.potential x =
      a * phase p F.potential x +
        b * phase q F.potential x := by
  simp only [phase, SupportFunction.pairing_add_left,
    SupportFunction.pairing_smul_left]
  linear_combination F.potential x * hab

private theorem convex_finiteEnergyFiniteTargetSet
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Convex ℝ (finiteEnergyFiniteTargetSet F) := by
  intro p hp q hq a b ha hb hab
  refine ⟨K.convex hp.1 hq.1 ha hb hab, ?_⟩
  have hbdd :
      BddAbove
        (Set.range
          (phase (a • p + b • q) F.potential)) := by
    refine ⟨a * (sourceExtendedBodyLegendre F.potential p).toReal +
      b * (sourceExtendedBodyLegendre F.potential q).toReal, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [finiteEnergySourcePhase_affine_target F p q x a b hab]
    have hpfen := finiteEnergyFiniteTarget_fenchel F hp x
    have hqfen := finiteEnergyFiniteTarget_fenchel F hq x
    have hpbound :
        phase p F.potential x ≤
          (sourceExtendedBodyLegendre F.potential p).toReal := by
      unfold phase
      linarith
    have hqbound :
        phase q F.potential x ≤
          (sourceExtendedBodyLegendre F.potential q).toReal := by
      unfold phase
      linarith
    exact add_le_add
      (mul_le_mul_of_nonneg_left hpbound ha)
      (mul_le_mul_of_nonneg_left hqbound hb)
  rw [sourceExtendedBodyLegendre_eq_of_bddAbove
    F.potential (a • p + b • q) hbdd]
  exact ENNReal.ofReal_ne_top

private theorem finiteEnergyDifferentiableGradientImage_subset_finiteTarget
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    finiteEnergyDifferentiableGradientImage F ⊆
      finiteEnergyFiniteTargetSet F := by
  rintro p ⟨x, hx, rfl⟩
  refine ⟨finiteEnergySourceGradient_mem_carrier F x hx, ?_⟩
  rw [finiteEnergySourceExtendedLegendre_actualGradient F x hx]
  exact ENNReal.ofReal_ne_top

private theorem closure_finiteEnergyFiniteTargetSet_eq_carrier
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    closure (finiteEnergyFiniteTargetSet F) = K.carrier := by
  apply le_antisymm
  · apply closure_minimal _ K.compact.isClosed
    intro p hp
    exact hp.1
  · have hsubset :=
      closure_mono
        (finiteEnergyDifferentiableGradientImage_subset_finiteTarget F)
    rw [closure_finiteEnergyDifferentiableGradientImage_eq_carrier
      F htransport] at hsubset
    exact hsubset

private theorem affineSpan_finiteEnergyFiniteTargetSet_eq_top
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    affineSpan ℝ (finiteEnergyFiniteTargetSet F) = ⊤ := by
  have hbody :
      K.carrier ⊆
        (affineSpan ℝ
          (finiteEnergyFiniteTargetSet F) :
            Set (Space n)) := by
    rw [← closure_finiteEnergyFiniteTargetSet_eq_carrier
      F htransport]
    exact closure_minimal
      (subset_affineSpan ℝ (finiteEnergyFiniteTargetSet F))
      (affineSpan ℝ (finiteEnergyFiniteTargetSet F)).closed_of_finiteDimensional
  apply top_unique
  rw [← isOpen_interior.affineSpan_eq_top K.fullDimensional]
  exact affineSpan_le.mpr (interior_subset.trans hbody)

private theorem interior_finiteEnergyFiniteTargetSet_eq
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    interior (finiteEnergyFiniteTargetSet F) =
      interior K.carrier := by
  have hconv := convex_finiteEnergyFiniteTargetSet F
  have hnonempty :
      (interior (finiteEnergyFiniteTargetSet F)).Nonempty :=
    hconv.interior_nonempty_iff_affineSpan_eq_top.mpr
      (affineSpan_finiteEnergyFiniteTargetSet_eq_top
        F htransport)
  have hinter :=
    hconv.interior_closure_eq_interior_of_nonempty_interior
      hnonempty
  rw [closure_finiteEnergyFiniteTargetSet_eq_carrier
    F htransport] at hinter
  exact hinter.symm

private theorem finiteEnergySourceExtendedLegendre_ne_top_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    sourceExtendedBodyLegendre F.potential p ≠ ⊤ := by
  have hinter :
      p ∈ interior (finiteEnergyFiniteTargetSet F) := by
    rw [interior_finiteEnergyFiniteTargetSet_eq F htransport]
    exact hp
  exact (interior_subset hinter).2

private theorem finiteEnergySourcePhase_bddAbove_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K)
    {p : Space n} (hp : p ∈ interior K.carrier) :
    BddAbove (Set.range (phase p F.potential)) := by
  have hfinite : p ∈ finiteEnergyFiniteTargetSet F := by
    refine ⟨interior_subset hp, ?_⟩
    exact finiteEnergySourceExtendedLegendre_ne_top_of_mem_interior
      F htransport hp
  refine ⟨(sourceExtendedBodyLegendre F.potential p).toReal, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hfen := finiteEnergyFiniteTarget_fenchel F hfinite x
  unfold phase
  linarith

private theorem convexOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ConvexOn ℝ (interior K.carrier)
      (legendreTransform F.potential) := by
  refine ⟨K.convex.interior, ?_⟩
  intro p hp q hq a b ha hb hab
  unfold legendreTransform
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hpmax :
      phase p F.potential x ≤
        sSup (Set.range (phase p F.potential)) :=
    le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hp)
      ⟨x, rfl⟩
  have hqmax :
      phase q F.potential x ≤
        sSup (Set.range (phase q F.potential)) :=
    le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hq)
      ⟨x, rfl⟩
  rw [finiteEnergySourcePhase_affine_target F p q x a b hab]
  simpa only [smul_eq_mul, ge_iff_le] using
    add_le_add
      (mul_le_mul_of_nonneg_left hpmax ha)
      (mul_le_mul_of_nonneg_left hqmax hb)

private theorem locallyLipschitzOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    LocallyLipschitzOn (interior K.carrier)
      (legendreTransform F.potential) :=
  (convexOn_finiteEnergySourceLegendre_interior F htransport)
    |>.locallyLipschitzOn isOpen_interior

private theorem continuousOn_finiteEnergySourceLegendre_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport :
      finiteEnergySourceGradientPushforward F =
        normalizedTargetBodyMeasure K) :
    ContinuousOn (legendreTransform F.potential)
      (interior K.carrier) :=
  (convexOn_finiteEnergySourceLegendre_interior F htransport)
    |>.continuousOn isOpen_interior

end MomentInteriorLegendre

namespace MomentWeakBergman

open Set Function Filter MeasureTheory
open SupportFunction LaplaceAsymptotics MonomialIntegrability WeightedTorusHilbert MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentInteriorLegendre
open MomentMoserTrudinger
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem continuous_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentNormalizedPotential F) := by
  exact F.potential.continuous.add continuous_const

private theorem convexOn_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    ConvexOn ℝ Set.univ (momentNormalizedPotential F) := by
  have hpotential :
      (F.potential : Space n → ℝ) +
        (fun _ : Space n =>
          Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) =
        momentNormalizedPotential F := by
    funext x
    rfl
  rw [← hpotential]
  exact F.convex.add_const
    (Real.log
      (finiteEnergySourcePartition F /
        normalizedVolume K.carrier))

private theorem momentNormalizedPotential_le_support_add
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (x : Space n) :
    momentNormalizedPotential F x ≤
      supportFunction K.carrier x +
        Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier) := by
  unfold momentNormalizedPotential
  linarith [F.supportUpper x]

private theorem exists_finiteEnergySource_interior_phase_linear_coercivity
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ x : Space n,
        δ * ‖x‖ ≤
          F.potential x - pairing u x + C := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior) u hu
  let δ : ℝ := r / 2
  have hδ : 0 < δ := half_pos hr
  have hclosed : Metric.closedBall u δ ⊆ interior K.carrier := by
    intro p hp
    apply hball
    apply Metric.mem_ball.mpr
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hp)
      (half_lt_self hr)
  have hdual : ContinuousOn
      (legendreTransform F.potential)
      (Metric.closedBall u δ) :=
    (continuousOn_finiteEnergySourceLegendre_interior
      F htransport).mono hclosed
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall u δ).bddAbove_image hdual
  refine ⟨δ, C, hδ, ?_⟩
  intro x
  let p : Space n := u + δ • signVector x
  have hp : p ∈ Metric.closedBall u δ := by
    apply Metric.mem_closedBall.mpr
    rw [dist_eq_norm]
    have hscaled : ‖δ • signVector x‖ ≤ δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      exact mul_le_of_le_one_right hδ.le
        (norm_signVector_le_one x)
    simpa [p] using hscaled
  have hpi : p ∈ interior K.carrier := hclosed hp
  have hphase :
      pairing p x - F.potential x ≤
        legendreTransform F.potential p := by
    exact le_csSup
      (finiteEnergySourcePhase_bddAbove_of_mem_interior
        F htransport hpi)
      ⟨x, rfl⟩
  have hbound : legendreTransform F.potential p ≤ C :=
    hC ⟨p, hp, rfl⟩
  change
    pairing (u + δ • signVector x) x -
        F.potential x ≤
      legendreTransform F.potential p at hphase
  rw [pairing_add_left, pairing_smul_left,
    pairing_signVector] at hphase
  have hnorm := SupportFunction.norm_le_sum_abs x
  have hscaled := mul_le_mul_of_nonneg_left hnorm hδ.le
  linarith

private theorem integrable_monomialWeight_finiteEnergySource_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (monomialWeight k u F.potential)
      (volume : Measure (Space n)) := by
  obtain ⟨δ, C, hδ, hcoerc⟩ :=
    exists_finiteEnergySource_interior_phase_linear_coercivity
      F htransport hu
  have hdecay :=
    integrable_exp_neg_mul_norm_all (n := n) (mul_pos hk hδ)
  have hmajor := hdecay.const_mul (Real.exp (k * C))
  have hmeas :
      AEStronglyMeasurable (monomialWeight k u F.potential)
        (volume : Measure (Space n)) :=
    (continuous_monomialWeight k u F.potential.continuous).aestronglyMeasurable
  refine hmajor.mono' hmeas ?_
  filter_upwards [] with x
  unfold monomialWeight
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := hcoerc x
  nlinarith

private theorem monomialWeight_momentNormalizedPotential_eq
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (k : ℝ) (u x : Space n) :
    monomialWeight k u (momentNormalizedPotential F) x =
      Real.exp
        (-k * Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier)) *
        monomialWeight k u F.potential x := by
  unfold monomialWeight momentNormalizedPotential
  rw [← Real.exp_add]
  congr 1
  ring

private theorem integrable_monomialWeight_momentNormalized_of_mem_interior
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    Integrable
      (monomialWeight k u (momentNormalizedPotential F))
      (volume : Measure (Space n)) := by
  refine
    ((integrable_monomialWeight_finiteEnergySource_of_mem_interior
      F htransport hu hk).const_mul
        (Real.exp
          (-k * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)))).congr ?_
  filter_upwards [] with x
  exact (monomialWeight_momentNormalizedPotential_eq
    F k u x).symm

private theorem monomialIntegral_momentNormalized_pos
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {u : Space n} (hu : u ∈ interior K.carrier)
    {k : ℝ} (hk : 0 < k) :
    0 < monomialIntegral k u (momentNormalizedPotential F) := by
  unfold monomialIntegral monomialWeight
  exact MeasureTheory.integral_exp_pos
    (integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hk)

private theorem radial_exp_integrable_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        Real.exp (pairing (integerPoint n m) x))
      (radialMeasure k (momentNormalizedPotential F)) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hφ := continuous_momentNormalizedPotential F
  have hfinite : ∀ᵐ x ∂(volume : Measure (Space n)),
      radialWeight k (momentNormalizedPotential F) x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold radialMeasure
  apply (MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (radialWeight_measurable k hφ) hfinite).2
  have hmono :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport hu hkreal
  refine hmono.congr (Filter.Eventually.of_forall fun x => ?_)
  simpa only [smul_eq_mul] using
    (radialWeight_mul_exp_pairing k
      (momentNormalizedPotential F) m u hm x).symm

private theorem torusMonomial_sq_integrable_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun z : LogTorus n => ‖torusMonomial m z‖ ^ 2)
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  have hradial := radial_exp_integrable_momentNormalized
    K hk F htransport m u hu hm
  have hangular : Integrable
      (fun _ : TorusCharacters.AngularTorus n => (1 : ℝ))
      (angularMeasure n) := integrable_const _
  have hproduct := hradial.mul_prod hangular
  unfold weightedTorusMeasure
  convert hproduct using 1
  funext z
  simp only [torusMonomial_norm_sq, mul_one]

private theorem torusMonomial_memLp_momentNormalized
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (m : Fin n → ℤ) (u : Space n)
    (hu : u ∈ interior K.carrier)
    (hm : integerPoint n m = (k : ℝ) • u) :
    MemLp (torusMonomial m) 2
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_torusMonomial m).aestronglyMeasurable).2
  exact torusMonomial_sq_integrable_momentNormalized
    K hk F htransport m u hu hm

end MomentWeakBergman

namespace BergmanJetBasis

open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

private def momentIndexedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    weightedHilbert k (momentNormalizedPotential F) :=
  (torusMonomial_memLp_momentNormalized K hk F htransport
    (integerExponent K hk u) (u : Space n)
    u.property.1 (integerPoint_integerExponent K hk u)).toLp
      (torusMonomial (integerExponent K hk u))

private theorem momentIndexedMonomialLp_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (momentIndexedMonomialLp K hk F htransport u :
      LogTorus n → ℂ) =ᵐ[
        weightedTorusMeasure k (momentNormalizedPotential F)]
      torusMonomial (integerExponent K hk u) := by
  unfold momentIndexedMonomialLp
  exact MeasureTheory.MemLp.coeFn_toLp _

private theorem momentMonomialNormSquared_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    0 < monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact monomialIntegral_momentNormalized_pos
    F htransport u.property.1 hkreal

private theorem inner_momentIndexedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u v : monomialIndex K k) :
    @inner ℂ
      (weightedHilbert k (momentNormalizedPotential F)) _
      (momentIndexedMonomialLp K hk F htransport u)
      (momentIndexedMonomialLp K hk F htransport v) =
      if u = v then
        (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) : ℂ)
      else 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hu := momentIndexedMonomialLp_ae K hk F htransport u
  have hv := momentIndexedMonomialLp_ae K hk F htransport v
  calc
    (∫ z : LogTorus n,
      @inner ℂ ℂ _
        (momentIndexedMonomialLp K hk F htransport u z)
        (momentIndexedMonomialLp K hk F htransport v z)
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        ∫ z : LogTorus n,
          conj (torusMonomial (integerExponent K hk u) z) *
            torusMonomial (integerExponent K hk v) z
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := by
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hu, hv] with z huz hvz
            rw [huz, hvz, RCLike.inner_apply, mul_comm]
    _ = _ := by
      by_cases huv : u = v
      · subst v
        simp only [ite_true]
        calc
          (∫ z : LogTorus n,
            conj (torusMonomial (integerExponent K hk u) z) *
              torusMonomial (integerExponent K hk u) z
            ∂(weightedTorusMeasure k
              (momentNormalizedPotential F))) =
              ∫ z : LogTorus n,
                ((‖torusMonomial (integerExponent K hk u) z‖ ^ 2 : ℝ) : ℂ)
                ∂(weightedTorusMeasure k
                  (momentNormalizedPotential F)) := by
                  apply MeasureTheory.integral_congr_ae
                  filter_upwards [] with z
                  rw [← Complex.normSq_eq_conj_mul_self,
                    Complex.normSq_eq_norm_sq]
          _ = ((∫ z : LogTorus n,
                ‖torusMonomial (integerExponent K hk u) z‖ ^ 2
                ∂(weightedTorusMeasure k
                  (momentNormalizedPotential F)) : ℝ) : ℂ) :=
                integral_ofReal
          _ = (monomialNormSquared k (u : Space n)
                (momentNormalizedPotential F) : ℂ) := by
                rw [integral_torusMonomial_norm_sq_eq_monomialIntegral
                  k (continuous_momentNormalizedPotential F)
                  (integerExponent K hk u) (u : Space n)
                  (integerPoint_integerExponent K hk u)]
                rfl
      · have hmne : integerExponent K hk u ≠
            integerExponent K hk v := by
          intro heq
          exact huv ((integerExponent_injective K hk) heq)
        rw [torusMonomial_inner_eq_zero_of_ne
          k (momentNormalizedPotential F)
          (integerExponent K hk u)
          (integerExponent K hk v) hmne]
        simp only [huv, ↓reduceIte]

private def momentNormalizedMonomialLp
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    weightedHilbert k (momentNormalizedPotential F) :=
  ((Real.sqrt
    (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹) •
    momentIndexedMonomialLp K hk F htransport u

private theorem momentNormalizedMonomialLp_orthonormal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Orthonormal ℂ
      (momentNormalizedMonomialLp K hk F htransport) := by
  classical
  rw [orthonormal_iff_ite]
  intro u v
  unfold momentNormalizedMonomialLp
  rw [inner_smul_left, inner_smul_right,
    inner_momentIndexedMonomialLp K hk F htransport]
  by_cases huv : u = v
  · subst v
    simp only [ite_true]
    have hI := momentMonomialNormSquared_pos
      K hk F htransport u
    have hsqrt : 0 < Real.sqrt
        (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F)) :=
      Real.sqrt_pos.2 hI
    have hsqrt_complex :
        (Real.sqrt
          (monomialNormSquared k (u : Space n)
            (momentNormalizedPotential F)) : ℂ) ≠ 0 := by
      exact_mod_cast hsqrt.ne'
    have hsquare := Real.sq_sqrt hI.le
    simp only [map_inv₀, Complex.conj_ofReal]
    field_simp
    exact_mod_cast hsquare.symm
  · simp only [map_inv₀, Complex.conj_ofReal, huv, ↓reduceIte, mul_zero]

private def momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Submodule ℂ
      (weightedHilbert k (momentNormalizedPotential F)) :=
  Submodule.span ℂ
    (Set.range (momentNormalizedMonomialLp K hk F htransport))

private theorem finrank_momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Module.finrank ℂ
      (momentMonomialSpan K hk F htransport) =
      bergmanDimension K k := by
  let := (monomialIndex_finite K hk).fintype
  unfold momentMonomialSpan
  calc
    Module.finrank ℂ
      (Submodule.span ℂ
        (Set.range (momentNormalizedMonomialLp
          K hk F htransport))) =
        Fintype.card (monomialIndex K k) :=
          finrank_span_eq_card
            (momentNormalizedMonomialLp_orthonormal
              K hk F htransport).linearIndependent
    _ = bergmanDimension K k := by
      simp only [fintypeCard_eq_ncard, bergmanDimension, Nat.card_eq_fintype_card]

private def momentLatticeMonomialBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Basis (monomialIndex K k) ℂ
      (momentMonomialSpan K hk F htransport) :=
  Basis.span
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport).linearIndependent

private theorem momentLatticeMonomialBasis_apply
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ((momentLatticeMonomialBasis K hk F htransport u :
      momentMonomialSpan K hk F htransport) :
      weightedHilbert k (momentNormalizedPotential F)) =
        momentNormalizedMonomialLp K hk F htransport u := by
  exact Basis.coe_span_apply
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport).linearIndependent u

private theorem momentLatticeMonomialBasis_orthonormal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Orthonormal ℂ (momentLatticeMonomialBasis
      K hk F htransport) := by
  rw [orthonormal_iff_ite]
  intro u v
  change
    @inner ℂ
      (weightedHilbert k (momentNormalizedPotential F)) _
      ((momentLatticeMonomialBasis K hk F htransport u :
        momentMonomialSpan K hk F htransport) :
        weightedHilbert k (momentNormalizedPotential F))
      ((momentLatticeMonomialBasis K hk F htransport v :
        momentMonomialSpan K hk F htransport) :
        weightedHilbert k (momentNormalizedPotential F)) =
      if u = v then 1 else 0
  rw [momentLatticeMonomialBasis_apply,
    momentLatticeMonomialBasis_apply]
  exact (orthonormal_iff_ite.mp
    (momentNormalizedMonomialLp_orthonormal
      K hk F htransport)) u v

private def momentMonomialOrthonormalBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    OrthonormalBasis
      (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport) := by
  letI := (monomialIndex_finite K hk).fintype
  exact ((momentLatticeMonomialBasis K hk F htransport).toOrthonormalBasis
    (momentLatticeMonomialBasis_orthonormal
      K hk F htransport)).reindex
        (monomialIndexEquivFin K hk)

private theorem momentMonomialOrthonormalBasis_apply
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    ((momentMonomialOrthonormalBasis K hk F htransport
        (monomialIndexEquivFin K hk u) :
          momentMonomialSpan K hk F htransport) :
      weightedHilbert k (momentNormalizedPotential F)) =
        momentNormalizedMonomialLp K hk F htransport u := by
  classical
  let := (monomialIndex_finite K hk).fintype
  simpa only [momentMonomialOrthonormalBasis, OrthonormalBasis.reindex_apply,
    Equiv.symm_apply_apply, Basis.coe_toOrthonormalBasis] using
      momentLatticeMonomialBasis_apply K hk F htransport u

private theorem finiteDimensional_momentMonomialSpan
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    FiniteDimensional ℂ
      (momentMonomialSpan K hk F htransport) := by
  let := (monomialIndex_finite K hk).fintype
  exact FiniteDimensional.span_of_finite ℂ
    (Set.finite_range
      (momentNormalizedMonomialLp K hk F htransport))

private def momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (TorusCharacters.LogSpace n → ℂ) :=
  (Finsupp.linearCombination ℂ
    (normalizedHolomorphicMonomial K hk
      (momentNormalizedPotential F))).comp
        (momentLatticeMonomialBasis
          K hk F htransport).repr.toLinearMap

private theorem momentHolomorphicRepresentative_latticeMonomialBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    momentHolomorphicRepresentative K hk F htransport
      (momentLatticeMonomialBasis K hk F htransport u) =
      normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u := by
  classical
  simp only [momentHolomorphicRepresentative, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    Basis.repr_self, Finsupp.linearCombination_single, one_smul]

private theorem differentiable_momentHolomorphicRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Differentiable ℂ
      (momentHolomorphicRepresentative K hk F htransport s) := by
  classical
  unfold momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  apply Differentiable.sum
  intro u _
  exact
    (differentiable_normalizedHolomorphicMonomial K hk
      (momentNormalizedPotential F) u).const_smul _

private def momentHolomorphicJetMap
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (JetCounting.JetIndexLT n j → ℂ) :=
  (Finsupp.linearCombination ℂ
    (fun u (α : JetCounting.JetIndexLT n j) =>
      holomorphicMonomialJet K hk
        (momentNormalizedPotential F) p u α.val)).comp
    (momentLatticeMonomialBasis K hk F htransport).repr.toLinearMap

private def momentJetFiltration
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    Submodule ℂ (momentMonomialSpan K hk F htransport) :=
  LinearMap.ker
    (momentHolomorphicJetMap K hk F htransport p j)

private theorem bergmanDimension_le_momentJetFiltration_add_jetCount
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j : ℕ} (hj : 0 < j) :
    bergmanDimension K k ≤
      Module.finrank ℂ (momentJetFiltration
        K hk F htransport p j) +
        (n + j - 1).choose n := by
  let := finiteDimensional_momentMonomialSpan
    K hk F htransport
  have h := JetCounting.finrank_le_kernel_add_jetCount ℂ
    (momentMonomialSpan K hk F htransport) n j hj
    (momentHolomorphicJetMap K hk F htransport p j)
  rw [← finrank_momentMonomialSpan K hk F htransport]
  exact h

private theorem momentJetFiltration_finrank_ge
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j : ℕ} (hj : 0 < j) :
    bergmanDimension K k - (n + j - 1).choose n ≤
      Module.finrank ℂ
        (momentJetFiltration K hk F htransport p j) := by
  have h := bergmanDimension_le_momentJetFiltration_add_jetCount
    K hk F htransport p hj
  omega

end BergmanJetBasis

namespace MomentWeakGlobalKernel

open Set Function Filter MeasureTheory Module
open LaplaceAsymptotics MonomialIntegrability BergmanMonomials LatticeAsymptotics MomentMinimizer
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetBasis GlobalBergmanKernelBound
open scoped BigOperators ENNReal InnerProductSpace NNReal Topology

private theorem lipschitz_momentNormalizedPotential
    {n : ℕ} {K : CenteredBody n}
    (F : SourceFiniteEnergyPotential K) :
    LipschitzWith (sourceBodyLipschitzConstant K)
      (momentNormalizedPotential F) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [momentNormalizedPotential, dist_add_right] using
    F.lipschitz.dist_le_mul x y

private theorem monomialNormSquared_momentNormalized_global_lower_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    (2 / (k : ℝ)) ^ n *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) ≤
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkreal
  have hφ := lipschitz_momentNormalizedPotential F
  have hslope :
      phaseSlopeBound K (sourceBodyLipschitzConstant K) =
        bodyPhaseSlopeBound K := by
    exact phaseSlopeBound_body K
  have hweight :=
    integrable_monomialWeight_momentNormalized_of_mem_interior
      F htransport u.property.1 hkreal
  have hballfinite :
      (volume : Measure (Space n))
        (Metric.ball x (k : ℝ)⁻¹) ≠ ⊤ :=
    (measure_ball_lt_top
      (μ := (volume : Measure (Space n)))
      (x := x) (r := (k : ℝ)⁻¹)).ne
  have hconst : IntegrableOn
      (fun _ : Space n =>
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K))
      (Metric.ball x (k : ℝ)⁻¹)
      (volume : Measure (Space n)) :=
    integrableOn_const hballfinite
  calc
    (2 / (k : ℝ)) ^ n *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) =
        (volume : Measure (Space n)).real
          (Metric.ball x (k : ℝ)⁻¹) *
        Real.exp
          ((k : ℝ) * phase (u : Space n)
            (momentNormalizedPotential F) x -
              bodyPhaseSlopeBound K) := by
          rw [real_volume_ball_inv_nat hk x]
    _ = ∫ _v : Space n in Metric.ball x (k : ℝ)⁻¹,
          Real.exp
            ((k : ℝ) * phase (u : Space n)
              (momentNormalizedPotential F) x -
                bodyPhaseSlopeBound K)
          ∂(volume : Measure (Space n)) := by
          rw [setIntegral_const]
          simp only [smul_eq_mul]
    _ ≤ ∫ v : Space n in Metric.ball x (k : ℝ)⁻¹,
          monomialWeight (k : ℝ) (u : Space n)
            (momentNormalizedPotential F) v
          ∂(volume : Measure (Space n)) := by
          apply setIntegral_mono_on hconst hweight.integrableOn
            Metric.isOpen_ball.measurableSet
          intro v hv
          unfold monomialWeight
          apply Real.exp_le_exp.mpr
          have hphase := phase_lower_on_inv_nat_ball
            K hk hφ u x v hv
          rw [hslope] at hphase
          have hscaled := mul_le_mul_of_nonneg_left hphase hkreal.le
          have hcancel :
              (k : ℝ) *
                (phase (u : Space n)
                  (momentNormalizedPotential F) x -
                    bodyPhaseSlopeBound K / (k : ℝ)) =
                (k : ℝ) * phase (u : Space n)
                  (momentNormalizedPotential F) x -
                    bodyPhaseSlopeBound K := by
            field_simp
          rw [hcancel] at hscaled
          exact hscaled
    _ ≤ monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) := by
          unfold monomialNormSquared monomialIntegral
          apply setIntegral_le_integral hweight
          exact Filter.Eventually.of_forall
            (fun _ => (Real.exp_pos _).le)

private theorem normalizedMonomialDensity_momentNormalized_global_upper_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    normalizedMonomialDensity K k
        (momentNormalizedPotential F) u x ≤
      Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkreal
  have hnormpos := momentMonomialNormSquared_pos
    K hk F htransport u
  have hlower :=
    monomialNormSquared_momentNormalized_global_lower_bound
      K hk F htransport u x
  change
    Real.exp ((k : ℝ) * phase (u : Space n)
      (momentNormalizedPotential F) x) /
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) ≤
      Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n
  apply (div_le_iff₀ hnormpos).mpr
  have hcancel :
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) =
        Real.exp ((k : ℝ) * phase (u : Space n)
          (momentNormalizedPotential F) x) := by
    calc
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) =
        (((k : ℝ) / 2) * (2 / (k : ℝ))) ^ n *
          (Real.exp (bodyPhaseSlopeBound K) *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) := by
        rw [mul_pow]
        ring
      _ = Real.exp ((k : ℝ) * phase (u : Space n)
          (momentNormalizedPotential F) x) := by
        have hratio : ((k : ℝ) / 2) * (2 / (k : ℝ)) = 1 := by
          field_simp
        rw [hratio, one_pow, one_mul, ← Real.exp_add]
        congr 1
        ring
  calc
    Real.exp ((k : ℝ) * phase (u : Space n)
        (momentNormalizedPotential F) x) =
      (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
          ((2 / (k : ℝ)) ^ n *
            Real.exp
              ((k : ℝ) * phase (u : Space n)
                (momentNormalizedPotential F) x -
                  bodyPhaseSlopeBound K)) := hcancel.symm
    _ ≤ (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) *
        monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F) :=
      mul_le_mul_of_nonneg_left hlower (by positivity)

private theorem weightedDiagonalKernel_momentNormalized_global_upper_bound
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
      (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  rw [tsum_fintype]
  calc
    (∑ u : monomialIndex K k,
      normalizedMonomialDensity K k
        (momentNormalizedPotential F) u x) ≤
        ∑ _u : monomialIndex K k,
          (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
            Finset.sum_le_sum fun u _ =>
              normalizedMonomialDensity_momentNormalized_global_upper_bound
                K hk F htransport u x
    _ = (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) := by
          simp only [Finset.sum_const, Finset.card_univ, fintypeCard_eq_ncard, nsmul_eq_mul,
            bergmanDimension, Nat.card_eq_fintype_card]

private theorem weightedDiagonalKernel_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < weightedDiagonalKernel K k
      (momentNormalizedPotential F) x := by
  let := (monomialIndex_finite K hk).fintype
  unfold weightedDiagonalKernel
  rw [tsum_fintype]
  apply Finset.sum_pos
  · intro u _
    unfold normalizedMonomialDensity
    exact div_pos (Real.exp_pos _)
      (momentMonomialNormSquared_pos K hk F htransport u)
  · exact ⟨⟨0, zero_mem_monomialIndex K hk⟩,
      Finset.mem_univ _⟩

private theorem diagonalKernel_momentNormalized_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    0 < diagonalKernel K k
      (momentNormalizedPotential F) x := by
  have hweighted := weightedDiagonalKernel_momentNormalized_pos
    K hk F htransport x
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
      K hk (momentNormalizedPotential F) x] at hweighted
  exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp hweighted

private theorem eventually_momentNormalized_weightedDiagonalKernel_le_polynomial
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
        globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards [eventually_bergmanDimension_le_volume_mul_pow K,
    eventually_gt_atTop (0 : ℕ)] with k hdim hk x
  calc
    weightedDiagonalKernel K k
        (momentNormalizedPotential F) x ≤
      (bergmanDimension K k : ℝ) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
      weightedDiagonalKernel_momentNormalized_global_upper_bound
        K hk F htransport x
    _ ≤ ((normalizedVolume K.carrier + 1) * (k : ℝ) ^ n) *
        (Real.exp (bodyPhaseSlopeBound K) * ((k : ℝ) / 2) ^ n) :=
      mul_le_mul_of_nonneg_right hdim (by positivity)
    _ = globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
      unfold globalKernelPolynomialConstant
      rw [show 2 * n = n + n by omega, pow_add, div_pow]
      ring

private theorem eventually_momentNormalized_diagonalKernel_le_polynomial
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      diagonalKernel K k (momentNormalizedPotential F) x ≤
        Real.exp ((k : ℝ) * momentNormalizedPotential F x) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
  filter_upwards
    [eventually_momentNormalized_weightedDiagonalKernel_le_polynomial
      K F htransport, eventually_gt_atTop (0 : ℕ)]
    with k hweighted hk x
  let φ := momentNormalizedPotential F
  have hw := hweighted x
  rw [weightedDiagonalKernel_eq_exp_neg_mul_diagonalKernel
      K hk φ x] at hw
  have hscaled := mul_le_mul_of_nonneg_left hw
    (Real.exp_pos ((k : ℝ) * φ x)).le
  have hcancel :
      Real.exp ((k : ℝ) * φ x) *
        Real.exp (-(k : ℝ) * φ x) = 1 := by
    rw [← Real.exp_add,
      show (k : ℝ) * φ x + -(k : ℝ) * φ x = 0 by ring,
      Real.exp_zero]
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  simpa only [mul_assoc] using hscaled

private theorem eventually_log_momentNormalized_diagonalKernel_div_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      Real.log (diagonalKernel K k
          (momentNormalizedPotential F) x) / (k : ℝ) ≤
        momentNormalizedPotential F x +
          globalKernelLogError K k := by
  filter_upwards
    [eventually_momentNormalized_diagonalKernel_le_polynomial
      K F htransport, eventually_gt_atTop (0 : ℕ)]
    with k hpoly hk x
  let φ := momentNormalizedPotential F
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hconstant := globalKernelPolynomialConstant_pos K
  have hdiag := diagonalKernel_momentNormalized_pos
    K hk F htransport x
  have hmajor : 0 <
      Real.exp ((k : ℝ) * φ x) *
        globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n) := by
    positivity
  have hlog := Real.strictMonoOn_log.monotoneOn
    hdiag hmajor (hpoly x)
  have hexpand :
      Real.log (Real.exp ((k : ℝ) * φ x) *
          globalKernelPolynomialConstant K * (k : ℝ) ^ (2 * n)) =
        (k : ℝ) * φ x + Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ) := by
    rw [Real.log_mul
      (mul_ne_zero (Real.exp_ne_zero _)
        (ne_of_gt hconstant)) (pow_ne_zero _ (ne_of_gt hkreal)),
      Real.log_mul (Real.exp_ne_zero _) (ne_of_gt hconstant),
      Real.log_exp, Real.log_pow]
    push_cast
    ring
  rw [hexpand] at hlog
  unfold globalKernelLogError
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log (diagonalKernel K k φ x) ≤
        (k : ℝ) * φ x + Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ) := hlog
    _ = (φ x +
        (Real.log (globalKernelPolynomialConstant K) +
          2 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)) * (k : ℝ) := by
      field_simp
      ring_nf

private theorem eventually_log_momentNormalized_diagonalKernel_div_le_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ x : Space n,
      Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) ≤
        momentNormalizedPotential F x + ε := by
  have herr := (tendsto_globalKernelLogError K).eventually
    (gt_mem_nhds hε)
  filter_upwards
    [eventually_log_momentNormalized_diagonalKernel_div_le
      K F htransport, herr] with k hupper hsmall x
  exact (hupper x).trans (add_le_add_right hsmall.le _)

end MomentWeakGlobalKernel

namespace BergmanJetGeodesic

open Set Function Filter MeasureTheory Module
open BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity BergmanJetBasis JetAdaptedOrthonormalBasis
open GenuineJetAdaptedBasisCounting
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

private theorem momentJetFiltration_zero
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    momentJetFiltration K hk F htransport p 0 = ⊤ := by
  apply top_unique
  intro s _
  change momentHolomorphicJetMap K hk F htransport p 0 s = 0
  funext α
  exact (Nat.not_lt_zero _ α.property).elim

private theorem momentJetFiltration_antitone
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {j l : ℕ} (hjl : j ≤ l) :
    momentJetFiltration K hk F htransport p l ≤
      momentJetFiltration K hk F htransport p j := by
  classical
  intro s hs
  change momentHolomorphicJetMap K hk F htransport p l s = 0 at hs
  change momentHolomorphicJetMap K hk F htransport p j s = 0
  funext α
  let β : JetCounting.JetIndexLT n l :=
    ⟨α.val, lt_of_lt_of_le α.property hjl⟩
  have hβ := congrFun hs β
  simp only [momentHolomorphicJetMap, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.sum] at hβ ⊢
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hβ ⊢
  exact hβ

private theorem exists_momentSimultaneousJetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    ∃ b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport),
      ∀ (j : ℕ) (i : Fin (bergmanDimension K k)),
        b i ∈ momentJetFiltration K hk F htransport p j ∨
        b i ∈ (momentJetFiltration K hk F htransport p j)ᗮ := by
  classical
  let := finiteDimensional_momentMonomialSpan K hk F htransport
  obtain ⟨b, hb⟩ := exists_orthonormalBasis_simultaneously_adapted
    (momentJetFiltration K hk F htransport p)
    (fun _ _ h => momentJetFiltration_antitone
      K hk F htransport p h)
  let e := finCongr
    (finrank_momentMonomialSpan K hk F htransport)
  refine ⟨b.reindex e, ?_⟩
  intro j i
  simpa only [OrthonormalBasis.reindex_apply] using
    hb j (e.symm i)

private def momentSimultaneousJetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport) :=
  Classical.choose
    (exists_momentSimultaneousJetBasis K hk F htransport p)

private theorem momentSimultaneousJetBasis_adapted
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (j : ℕ) (i : Fin (bergmanDimension K k)) :
    momentSimultaneousJetBasis K hk F htransport p i ∈
        momentJetFiltration K hk F htransport p j ∨
      momentSimultaneousJetBasis K hk F htransport p i ∈
        (momentJetFiltration K hk F htransport p j)ᗮ :=
  Classical.choose_spec
    (exists_momentSimultaneousJetBasis K hk F htransport p) j i

private def momentUpperJetBasisIndices
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    Finset (Fin (bergmanDimension K k)) :=
  adaptedIndices (momentSimultaneousJetBasis K hk F htransport p)
    (momentJetFiltration K hk F htransport p j)

private theorem card_momentUpperJetBasisIndices_eq_finrank
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (j : ℕ) :
    (momentUpperJetBasisIndices K hk F htransport p j).card =
      Module.finrank ℂ
        (momentJetFiltration K hk F htransport p j) := by
  exact card_adaptedIndices_eq_finrank
    (momentSimultaneousJetBasis K hk F htransport p)
    (momentJetFiltration K hk F htransport p j)
    (momentSimultaneousJetBasis_adapted
      K hk F htransport p j)

private def momentTruncatedJetOrder
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) : ℕ := by
  classical
  exact ((Finset.range N).filter (fun j =>
    momentSimultaneousJetBasis K hk F htransport p i ∈
      momentJetFiltration K hk F htransport p (j + 1))).card

private theorem momentTruncatedJetOrder_le
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    momentTruncatedJetOrder K hk F htransport p N i ≤ N := by
  classical
  unfold momentTruncatedJetOrder
  simpa only [Finset.card_range] using Finset.card_filter_le (s := Finset.range N)
    (p := fun j =>
      momentSimultaneousJetBasis K hk F htransport p i ∈
        momentJetFiltration K hk F htransport p (j + 1))

private theorem sum_momentTruncatedJetOrder_eq_sum_upper_card
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    (∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p N i) =
      ∑ j ∈ Finset.range N,
        (momentUpperJetBasisIndices
          K hk F htransport p (j + 1)).card := by
  classical
  calc
    (∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p N i) =
      ∑ i : Fin (bergmanDimension K k),
        ∑ j ∈ Finset.range N,
          if momentSimultaneousJetBasis
            K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1)
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.card_filter _ _
    _ = ∑ j ∈ Finset.range N,
      ∑ i : Fin (bergmanDimension K k),
        if momentSimultaneousJetBasis
          K hk F htransport p i ∈
          momentJetFiltration K hk F htransport p (j + 1)
        then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j ∈ Finset.range N,
      (momentUpperJetBasisIndices
        K hk F htransport p (j + 1)).card := by
      apply Finset.sum_congr rfl
      intro j _
      change
        (∑ i : Fin (bergmanDimension K k),
          if momentSimultaneousJetBasis
            K hk F htransport p i ∈
            momentJetFiltration K hk F htransport p (j + 1)
          then 1 else 0) =
          (Finset.univ.filter
            (fun i : Fin (bergmanDimension K k) =>
              momentSimultaneousJetBasis
                K hk F htransport p i ∈
                momentJetFiltration
                  K hk F htransport p (j + 1))).card
      exact (Finset.card_filter
        (fun i : Fin (bergmanDimension K k) =>
          momentSimultaneousJetBasis K hk F htransport p i ∈
            momentJetFiltration
              K hk F htransport p (j + 1)) Finset.univ).symm

private theorem sum_momentTruncatedJetOrder_eq_sum_jetFiltration_finrank
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    (∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p N i) =
      ∑ j ∈ Finset.range N,
        Module.finrank ℂ
          (momentJetFiltration
            K hk F htransport p (j + 1)) := by
  rw [sum_momentTruncatedJetOrder_eq_sum_upper_card]
  apply Finset.sum_congr rfl
  intro j _
  exact card_momentUpperJetBasisIndices_eq_finrank
    K hk F htransport p (j + 1)

private theorem sum_momentJetFiltration_finrank_ge
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    (∑ j ∈ Finset.range N,
      (bergmanDimension K k - (n + j).choose n)) ≤
      ∑ j ∈ Finset.range N,
        Module.finrank ℂ
          (momentJetFiltration
            K hk F htransport p (j + 1)) := by
  apply Finset.sum_le_sum
  intro j _
  simpa only [tsub_le_iff_right, Nat.succ_eq_add_one,
    Nat.add_succ_sub_one] using momentJetFiltration_finrank_ge
    K hk F htransport p (Nat.zero_lt_succ j)

private theorem real_jetLayercake_le_sum_momentTruncatedJetOrder
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    (N : ℝ) * (bergmanDimension K k : ℝ) -
      (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
        ((∑ i : Fin (bergmanDimension K k),
          momentTruncatedJetOrder
            K hk F htransport p N i) : ℝ) := by
  calc
    (N : ℝ) * (bergmanDimension K k : ℝ) -
        (((n + N).choose (n + 1) : ℕ) : ℝ) ≤
      ((∑ j ∈ Finset.range N,
        (bergmanDimension K k - (n + j).choose n) : ℕ) : ℝ) :=
        BergmanJetFiltration.real_jetLayercake_le_nat_sum
          n (bergmanDimension K k) N
    _ ≤ ((∑ j ∈ Finset.range N,
          Module.finrank ℂ
            (momentJetFiltration
              K hk F htransport p (j + 1)) : ℕ) : ℝ) := by
      exact_mod_cast sum_momentJetFiltration_finrank_ge
        K hk F htransport p N
    _ = ((∑ i : Fin (bergmanDimension K k),
          momentTruncatedJetOrder
            K hk F htransport p N i) : ℝ) := by
      exact_mod_cast
        (sum_momentTruncatedJetOrder_eq_sum_jetFiltration_finrank
          K hk F htransport p N).symm

private def momentHolomorphicBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) : ℝ :=
  Complex.normSq
    (momentHolomorphicRepresentative
      K hk F htransport (b i) z)

private theorem momentHolomorphicBasisWeight_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (i : Fin (bergmanDimension K k)) :
    0 ≤ momentHolomorphicBasisWeight
      K hk F htransport b z i :=
  Complex.normSq_nonneg _

private theorem exists_positive_momentHolomorphicBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    ∃ i, 0 < momentHolomorphicBasisWeight
      K hk F htransport b z i := by
  classical
  by_contra! hzero
  have hvanish : ∀ i,
      momentHolomorphicRepresentative
        K hk F htransport (b i) z = 0 := by
    intro i
    apply Complex.normSq_eq_zero.mp
    exact le_antisymm (hzero i)
      (momentHolomorphicBasisWeight_nonneg
        K hk F htransport b z i)
  let u : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  let s := momentLatticeMonomialBasis
    K hk F htransport u
  have hrep : momentHolomorphicRepresentative
      K hk F htransport s z = 0 := by
    rw [← b.sum_repr s]
    simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hvanish, smul_eq_mul, mul_zero,
      Finset.sum_const_zero]
  rw [momentHolomorphicRepresentative_latticeMonomialBasis]
    at hrep
  unfold normalizedHolomorphicMonomial at hrep
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hsqrt :
      (Real.sqrt (monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 hnorm).ne'
  exact (mul_ne_zero (inv_ne_zero hsqrt)
    (TorusCharacters.torusCharacter_ne_zero _ z)) hrep

private def momentJointJetSection
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k))
    (q : TorusCharacters.LogSpace n × ℂ) : ℂ :=
  momentHolomorphicRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) q.1 *
    q.2 ^ (momentTruncatedJetOrder
      K hk F htransport p N i)

private theorem differentiable_momentJointJetSection
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k)) :
    Differentiable ℂ
      (momentJointJetSection K hk F htransport p N i) := by
  unfold momentJointJetSection
  exact
    ((differentiable_momentHolomorphicRepresentative
      K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i)).comp differentiable_fst).mul
      (differentiable_snd.pow
        (momentTruncatedJetOrder K hk F htransport p N i))

private def momentJointJetSectionVector
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) :
    EuclideanSpace ℂ (Fin (bergmanDimension K k)) :=
  WithLp.toLp 2
    (fun i => momentJointJetSection
      K hk F htransport p N i q)

private theorem differentiable_momentJointJetSectionVector
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    Differentiable ℂ
      (momentJointJetSectionVector K hk F htransport p N) := by
  apply (differentiable_piLp 2).2
  intro i
  exact differentiable_momentJointJetSection
    K hk F htransport p N i

private def momentJointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) : ℝ :=
  ∑ i : Fin (bergmanDimension K k),
    Complex.normSq
      (momentJointJetSection K hk F htransport p N i q)

private theorem momentJointJetSectionVector_norm_sq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (q : TorusCharacters.LogSpace n × ℂ) :
    ‖momentJointJetSectionVector
      K hk F htransport p N q‖ ^ 2 =
      momentJointJetDiagonal K hk F htransport p N q := by
  rw [EuclideanSpace.norm_sq_eq]
  change
    (∑ i, ‖momentJointJetSection
      K hk F htransport p N i q‖ ^ 2) =
      ∑ i, Complex.normSq
        (momentJointJetSection
          K hk F htransport p N i q)
  exact Finset.sum_congr rfl
    (fun i _ => (Complex.normSq_eq_norm_sq _).symm)

private theorem momentJointJetDiagonal_pos
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n)
    {τ : ℂ} (hτ : τ ≠ 0) :
    0 < momentJointJetDiagonal
      K hk F htransport p N (z, τ) := by
  classical
  obtain ⟨i, hi⟩ :=
    exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p) z
  have hvalue :
      momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis
          K hk F htransport p i) z ≠ 0 :=
    Complex.normSq_pos.mp hi
  have hsection :
      momentJointJetSection
        K hk F htransport p N i (z, τ) ≠ 0 := by
    exact mul_ne_zero hvalue (pow_ne_zero _ hτ)
  unfold momentJointJetDiagonal
  apply lt_of_lt_of_le (Complex.normSq_pos.mpr hsection)
  have hnonneg :
      ∀ j ∈ (Finset.univ : Finset (Fin (bergmanDimension K k))),
        0 ≤ Complex.normSq
          (momentJointJetSection
            K hk F htransport p N j (z, τ)) :=
    fun j _ => Complex.normSq_nonneg _
  exact Finset.single_le_sum hnonneg (Finset.mem_univ i)

end BergmanJetGeodesic

namespace BergmanJetProfileBridge

open Set Function Filter MeasureTheory Module InnerProductSpace
open SupportFunction BergmanMonomials LatticeAsymptotics WeightedTorusHilbert AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open BergmanJetGeodesic BergmanDiagonalBasisIndependence
open scoped BigOperators ComplexConjugate ENNReal InnerProductSpace
  Topology

private theorem normSq_momentHolomorphicMonomial_realLogSlice_eq_diagonalTerm
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) (x : Space n) :
    Complex.normSq
      (normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u
        (TorusCharacters.realLogSlice x)) =
      diagonalTerm K k (momentNormalizedPotential F) u x := by
  have hnorm := momentMonomialNormSquared_pos
    K hk F htransport u
  have hsqrt :
      Real.sqrt (monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F)) *
        Real.sqrt (monomialNormSquared k (u : Space n)
          (momentNormalizedPotential F)) =
      monomialNormSquared k (u : Space n)
        (momentNormalizedPotential F) := by
    simpa only [pow_two] using Real.sq_sqrt hnorm.le
  have hpair :
      (∑ i, (integerExponent K hk u i : ℝ) * x i) =
        (k : ℝ) * pairing (u : Space n) x := by
    calc
      (∑ i, (integerExponent K hk u i : ℝ) * x i) =
        pairing (integerPoint n (integerExponent K hk u)) x :=
          rfl
      _ = pairing ((k : ℝ) • (u : Space n)) x := by
          rw [integerPoint_integerExponent K hk u]
      _ = (k : ℝ) * pairing (u : Space n) x := by
          simp only [pairing, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
  unfold normalizedHolomorphicMonomial
  rw [Complex.normSq_mul, Complex.normSq_inv,
    Complex.normSq_ofReal, hsqrt, Complex.normSq_eq_norm_sq,
    TorusCharacters.norm_sq_torusCharacter_realLogSlice,
    hpair]
  simp only [diagonalTerm, div_eq_mul_inv, mul_comm]

private theorem normSq_momentHolomorphicMonomial_eq_diagonalTerm
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k)
    (z : TorusCharacters.LogSpace n) :
    Complex.normSq
      (normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u z) =
      diagonalTerm K k (momentNormalizedPotential F) u
        (realLogCoordinate z) := by
  calc
    Complex.normSq
        (normalizedHolomorphicMonomial K hk
          (momentNormalizedPotential F) u z) =
      Complex.normSq
        (normalizedHolomorphicMonomial K hk
          (momentNormalizedPotential F) u
            (TorusCharacters.realLogSlice
              (realLogCoordinate z))) := by
        unfold normalizedHolomorphicMonomial
        rw [Complex.normSq_mul, Complex.normSq_mul,
          normSq_torusCharacter_eq_realLogSlice]
    _ = diagonalTerm K k (momentNormalizedPotential F) u
          (realLogCoordinate z) :=
      normSq_momentHolomorphicMonomial_realLogSlice_eq_diagonalTerm
        K hk F htransport u (realLogCoordinate z)

private theorem momentHolomorphicRepresentative_monomialOrthonormalBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    momentHolomorphicRepresentative K hk F htransport
      (momentMonomialOrthonormalBasis K hk F htransport
        (monomialIndexEquivFin K hk u)) =
      normalizedHolomorphicMonomial K hk
        (momentNormalizedPotential F) u := by
  have hmono :
      momentMonomialOrthonormalBasis K hk F htransport
          (monomialIndexEquivFin K hk u) =
        momentLatticeMonomialBasis K hk F htransport u := by
    apply Subtype.ext
    exact
      (momentMonomialOrthonormalBasis_apply
        K hk F htransport u).trans
      (momentLatticeMonomialBasis_apply
        K hk F htransport u).symm
  rw [hmono]
  exact momentHolomorphicRepresentative_latticeMonomialBasis
    K hk F htransport u

private def momentHolomorphicEvaluationRepresenter
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    momentMonomialSpan K hk F htransport :=
  ∑ i, (starRingEnd ℂ)
    (momentHolomorphicRepresentative
      K hk F htransport (b i) z) • b i

private theorem momentHolomorphicEvaluationRepresenter_inner
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n)
    (s : momentMonomialSpan K hk F htransport) :
    @inner ℂ _ _
      (momentHolomorphicEvaluationRepresenter
        K hk F htransport b z) s =
      momentHolomorphicRepresentative
        K hk F htransport s z := by
  classical
  have hrepr := congrArg
    (fun v : momentMonomialSpan K hk F htransport =>
      momentHolomorphicRepresentative
        K hk F htransport v z)
    (b.sum_repr' s)
  calc
    @inner ℂ _ _
        (momentHolomorphicEvaluationRepresenter
          K hk F htransport b z) s =
      ∑ i, (momentHolomorphicRepresentative
          K hk F htransport (b i) z) *
        (@inner ℂ _ _ (b i) s) := by
          rw [momentHolomorphicEvaluationRepresenter, sum_inner]
          apply Finset.sum_congr rfl
          intro i _
          simp only [Submodule.coe_inner, inner_smul_left,
            RingHomCompTriple.comp_apply,
            RingHom.id_apply]
    _ = ∑ i, (@inner ℂ _ _ (b i) s) *
        (momentHolomorphicRepresentative
          K hk F htransport (b i) z) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = momentHolomorphicRepresentative
        K hk F htransport s z := by
          simpa only [Submodule.coe_inner, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul]
            using hrepr

private theorem sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b b₀ : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b₀ z‖ ^ 2 := by
  classical
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ∑ i, ‖@inner ℂ _ _
        (momentHolomorphicEvaluationRepresenter
          K hk F htransport b₀ z) (b i)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro i _
          rw [momentHolomorphicEvaluationRepresenter_inner,
            Complex.normSq_eq_norm_sq]
    _ = ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b₀ z‖ ^ 2 :=
      b.sum_sq_norm_inner_left _

private theorem sum_momentHolomorphicBasisWeight_eq_of_orthonormalBases
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b b' : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      ∑ i, momentHolomorphicBasisWeight
        K hk F htransport b' z i := by
  unfold momentHolomorphicBasisWeight
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b i) z)) =
      ‖momentHolomorphicEvaluationRepresenter
        K hk F htransport b z‖ ^ 2 :=
      sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
        K hk F htransport b b z
    _ = ∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport (b' i) z) :=
      (sum_normSq_momentHolomorphicRepresentative_eq_representer_norm_sq
        K hk F htransport b' b z).symm

private theorem sum_momentMonomialHolomorphicBasisWeight_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport
        (momentMonomialOrthonormalBasis K hk F htransport)
        z i) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold momentHolomorphicBasisWeight
  calc
    (∑ i, Complex.normSq
      (momentHolomorphicRepresentative
        K hk F htransport
          (momentMonomialOrthonormalBasis
            K hk F htransport i) z)) =
      ∑ u : monomialIndex K k,
        Complex.normSq
          (momentHolomorphicRepresentative
            K hk F htransport
              (momentMonomialOrthonormalBasis
                K hk F htransport
                  (monomialIndexEquivFin K hk u)) z) := by
        symm
        exact (monomialIndexEquivFin K hk).sum_comp
          (fun i => Complex.normSq
            (momentHolomorphicRepresentative
              K hk F htransport
                (momentMonomialOrthonormalBasis
                  K hk F htransport i) z))
    _ = ∑ u : monomialIndex K k,
        diagonalTerm K k (momentNormalizedPotential F)
          u (realLogCoordinate z) := by
        apply Finset.sum_congr rfl
        intro u _
        rw [momentHolomorphicRepresentative_monomialOrthonormalBasis
          K hk F htransport u]
        exact normSq_momentHolomorphicMonomial_eq_diagonalTerm
          K hk F htransport u z
    _ = diagonalKernel K k (momentNormalizedPotential F)
          (realLogCoordinate z) := by
        unfold diagonalKernel
        rw [tsum_fintype]

private theorem sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (z : TorusCharacters.LogSpace n) :
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  calc
    (∑ i, momentHolomorphicBasisWeight
      K hk F htransport b z i) =
      ∑ i, momentHolomorphicBasisWeight
        K hk F htransport
          (momentMonomialOrthonormalBasis K hk F htransport)
          z i :=
        sum_momentHolomorphicBasisWeight_eq_of_orthonormalBases
          K hk F htransport b
            (momentMonomialOrthonormalBasis
              K hk F htransport) z
    _ = diagonalKernel K k (momentNormalizedPotential F)
          (realLogCoordinate z) :=
      sum_momentMonomialHolomorphicBasisWeight_eq_diagonalKernel
        K hk F htransport z

private theorem momentJointJetDiagonal_one_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    momentJointJetDiagonal
      K hk F htransport p N (z, (1 : ℂ)) =
      diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z) := by
  unfold momentJointJetDiagonal momentJointJetSection
  simp only [one_pow, mul_one]
  exact sum_momentHolomorphicBasisWeight_eq_diagonalKernel
    K hk F htransport
    (momentSimultaneousJetBasis K hk F htransport p) z

private def normalizedMomentTruncatedJetOrderProfile
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) (k : ℕ) : ℝ :=
  if hk : 0 < k then
    ((∑ i : Fin (bergmanDimension K k),
      momentTruncatedJetOrder K hk F htransport p
        (Nat.floor (t * (k : ℝ))) i) : ℝ) /
      ((k : ℝ) * (bergmanDimension K k : ℝ))
  else 0

private theorem normalizedMomentTruncatedJetOrderProfile_ge
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (t : ℝ) :
    (((Nat.floor (t * (k : ℝ)) : ℕ) : ℝ) *
          (bergmanDimension K k : ℝ) -
        (((n + Nat.floor (t * (k : ℝ))).choose
          (n + 1) : ℕ) : ℝ)) /
        ((k : ℝ) * (bergmanDimension K k : ℝ)) ≤
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by
  rw [normalizedMomentTruncatedJetOrderProfile, dite_eq_left hk]
  apply div_le_div_of_nonneg_right
  · exact real_jetLayercake_le_sum_momentTruncatedJetOrder
      K hk F htransport p (Nat.floor (t * (k : ℝ)))
  · positivity

private theorem eventually_normalizedMomentTruncatedJetOrderProfile_ge
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier) - ε ≤
        normalizedMomentTruncatedJetOrderProfile
          K F htransport p t k := by
  have hlimit :=
    JetAsymptotics.tendsto_normalized_jetLayercake_profile K ht
  have hstrict :
      t - t ^ (n + 1) /
            (((n + 1).factorial : ℝ) *
              normalizedVolume K.carrier) - ε <
        t - t ^ (n + 1) /
          (((n + 1).factorial : ℝ) *
            normalizedVolume K.carrier) := by
    linarith
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    (tendsto_order.mp hlimit).1 _ hstrict] with k hk hlower
  exact le_trans (le_of_lt hlower)
    (normalizedMomentTruncatedJetOrderProfile_ge K
      (lt_of_lt_of_le Nat.zero_lt_one hk) F htransport p t)

private theorem eventually_normalizedMomentTruncatedJetOrderProfile_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        normalizedMomentTruncatedJetOrderProfile
          K F htransport p
          (BodyScale.canonicalScale K) k := by
  have h := eventually_normalizedMomentTruncatedJetOrderProfile_ge
    K F htransport p (BodyScale.canonicalScale_pos K) hε
  simpa only [tsub_le_iff_right, eventually_atTop,
    JetAsymptotics.normalized_jetLayercake_value_at_bodyScale K (BodyScale.canonicalScale_pow hn
      K)] using h

end BergmanJetProfileBridge

namespace BergmanJetRealGeodesic

open Set Function Filter MeasureTheory Module
open BergmanMonomials MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence
open scoped BigOperators ENNReal InnerProductSpace Topology

private def momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) : ℝ :=
  logarithmicPotential
    (momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z)
    (momentTruncatedJetOrder K hk F htransport p N)
    (k : ℝ) t

private theorem momentJointJetDiagonal_realTime
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ)) =
      exponentialPartition
        (momentHolomorphicBasisWeight
          K hk F htransport
          (momentSimultaneousJetBasis K hk F htransport p) z)
        (momentTruncatedJetOrder K hk F htransport p N) t := by
  classical
  unfold momentJointJetDiagonal exponentialPartition
    exponentialMoment
  simp only [pow_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  unfold momentJointJetSection momentHolomorphicBasisWeight
  rw [Complex.normSq_mul, map_pow, Complex.normSq_ofReal,
    ← Real.exp_add]
  have hhalf : t / 2 + t / 2 = t := by ring
  rw [hhalf, ← Real.exp_nat_mul]
  congr 2
  ring

private theorem momentJetGeodesic_eq_log_jointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    momentJetGeodesic K hk F htransport p N z t =
      Real.log (momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ))) / (k : ℝ) := by
  unfold momentJetGeodesic logarithmicPotential
  rw [momentJointJetDiagonal_realTime]

private theorem momentJetGeodesic_zero_eq_log_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    momentJetGeodesic K hk F htransport p N z 0 =
      Real.log (diagonalKernel K k (momentNormalizedPotential F)
        (realLogCoordinate z)) / (k : ℝ) := by
  rw [momentJetGeodesic_eq_log_jointJetDiagonal]
  norm_num
  rw [momentJointJetDiagonal_one_eq_diagonalKernel]

private theorem convexOn_momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) :
    ConvexOn ℝ Set.univ
      (momentJetGeodesic K hk F htransport p N z) := by
  unfold momentJetGeodesic
  apply convexOn_logarithmicPotential
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk

private theorem momentJetGeodesic_deriv_nonneg
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    0 ≤ deriv (momentJetGeodesic
      K hk F htransport p N z) t := by
  unfold momentJetGeodesic
  apply logarithmicPotential_deriv_nonneg
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk

private theorem momentJetGeodesic_deriv_le_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    deriv (momentJetGeodesic
      K hk F htransport p N z) t ≤
      (N : ℝ) / (k : ℝ) := by
  unfold momentJetGeodesic
  apply logarithmicPotential_deriv_le
  · exact momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  · exact_mod_cast hk
  · exact momentTruncatedJetOrder_le K hk F htransport p N

private theorem momentJetGeodesic_deriv_le_floor_cutoff
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {a : ℝ} (ha : 0 ≤ a)
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    deriv (momentJetGeodesic K hk F htransport p
      (Nat.floor (a * (k : ℝ))) z) t ≤ a := by
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  calc
    deriv (momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z) t ≤
        ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) / (k : ℝ) :=
      momentJetGeodesic_deriv_le_cutoff K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t
    _ ≤ a :=
      (div_le_iff₀ hkreal).mpr
        (Nat.floor_le (mul_nonneg ha hkreal.le))

private theorem momentJetGeodesic_le_zero_add_linear
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    momentJetGeodesic K hk F htransport p N z t ≤
      momentJetGeodesic K hk F htransport p N z 0 +
        (N : ℝ) / (k : ℝ) * t := by
  let w := momentHolomorphicBasisWeight
    K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  let order := momentTruncatedJetOrder
    K hk F htransport p N
  have hw : ∀ i, 0 ≤ w i :=
    momentHolomorphicBasisWeight_nonneg
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  have hpositive : ∃ i, 0 < w i :=
    exists_positive_momentHolomorphicBasisWeight
      K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p) z
  have horder : ∀ i, order i ≤ N :=
    momentTruncatedJetOrder_le K hk F htransport p N
  have hsum : 0 < ∑ i, w i := by
    have h := exponentialPartition_pos
      w order hw hpositive 0
    simpa only [gt_iff_lt, exponentialPartition, exponentialMoment, pow_zero, mul_one, zero_mul,
      Real.exp_zero] using h
  have hpart :=
    BergmanDiagonalBasisIndependence.exponentialPartition_le_exp_mul_sum
      w order hw N horder ht
  have hpartpos := exponentialPartition_pos
    w order hw hpositive t
  have hlog :
      Real.log (exponentialPartition w order t) ≤
        t * (N : ℝ) + Real.log (∑ i, w i) := by
    calc
      Real.log (exponentialPartition w order t) ≤
        Real.log (Real.exp (t * (N : ℝ)) * ∑ i, w i) :=
          Real.log_le_log hpartpos hpart
      _ = t * (N : ℝ) + Real.log (∑ i, w i) := by
        rw [Real.log_mul (Real.exp_ne_zero _) hsum.ne',
          Real.log_exp]
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  change
    Real.log (exponentialPartition w order t) / (k : ℝ) ≤
      Real.log (exponentialPartition w order 0) / (k : ℝ) +
        (N : ℝ) / (k : ℝ) * t
  have hzero : exponentialPartition w order 0 = ∑ i, w i := by
    simp only [exponentialPartition, exponentialMoment, pow_zero, mul_one, zero_mul, Real.exp_zero]
  rw [hzero]
  apply (div_le_iff₀ hkreal).mpr
  calc
    Real.log (exponentialPartition w order t) ≤
      t * (N : ℝ) + Real.log (∑ i, w i) := hlog
    _ = (Real.log (∑ i, w i) / (k : ℝ) +
      (N : ℝ) / (k : ℝ) * t) * (k : ℝ) := by
      field_simp
      ring

private theorem eventually_momentJetGeodesic_zero_le_potential_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (hk : 0 < k)
        (p z : TorusCharacters.LogSpace n) (N : ℕ),
      momentJetGeodesic K hk F htransport p N z 0 ≤
        momentNormalizedPotential F
          (realLogCoordinate z) + ε := by
  filter_upwards
    [eventually_log_momentNormalized_diagonalKernel_div_le_add
      K F htransport hε] with k hupper hk p z N
  rw [momentJetGeodesic_zero_eq_log_diagonalKernel]
  exact hupper (realLogCoordinate z)

private theorem eventually_momentJetGeodesic_le_potential_add_linear
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    {a : ℝ} (ha : 0 ≤ a)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ (hk : 0 < k)
        (p z : TorusCharacters.LogSpace n)
        (t : ℝ), 0 ≤ t →
      momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t ≤
        momentNormalizedPotential F
          (realLogCoordinate z) + ε + a * t := by
  filter_upwards
    [eventually_momentJetGeodesic_zero_le_potential_add
      K F htransport hε] with k hzero hk p z t ht
  have hkreal : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hfloor :
      ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) / (k : ℝ) ≤ a :=
    (div_le_iff₀ hkreal).mpr
      (Nat.floor_le (mul_nonneg ha hkreal.le))
  calc
    momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z t ≤
      momentJetGeodesic K hk F htransport p
        (Nat.floor (a * (k : ℝ))) z 0 +
          ((Nat.floor (a * (k : ℝ)) : ℕ) : ℝ) /
            (k : ℝ) * t :=
      momentJetGeodesic_le_zero_add_linear
        K hk F htransport p z (Nat.floor (a * (k : ℝ))) ht
    _ ≤ (momentNormalizedPotential F
          (realLogCoordinate z) + ε) + a * t :=
      add_le_add
        (hzero hk p z (Nat.floor (a * (k : ℝ))))
        (mul_le_mul_of_nonneg_right hfloor ht)
    _ = momentNormalizedPotential F
          (realLogCoordinate z) + ε + a * t := by ring

end BergmanJetRealGeodesic

namespace ActualJetPlurisubharmonicClosure

open Set Metric Filter Function MeasureTheory
open ActualJetUpperEnvelope
open scoped BigOperators Topology ENNReal

private theorem exists_mem_ball_sub_lt_upperRegularization
    {X : Type*} [PseudoMetricSpace X]
    (f : X → ℝ) (x : X) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ y ∈ Metric.ball x ε,
      upperRegularization f x - δ < f y := by
  by_contra h
  push Not at h
  have hev :
      ∀ᶠ y : X in 𝓝 x,
        f y ≤ upperRegularization f x - δ :=
    Filter.mem_of_superset (Metric.ball_mem_nhds x hε) h
  have hle :=
    upperRegularization_le_of_eventually f x hev
  linarith

private theorem exists_mem_ball_family_sub_lt_upperRegularization
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ y ∈ Metric.ball x ε, ∃ i : ι,
      upperRegularization
        (fun z : X => sSup (Set.range fun j => F j z)) x - δ <
        F i y := by
  obtain ⟨y, hy, hlt⟩ :=
    exists_mem_ball_sub_lt_upperRegularization
      (fun z : X => sSup (Set.range fun j => F j z))
      x hε hδ
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    exists_lt_of_lt_csSup
      (Set.range_nonempty fun j : ι => F j y) hlt
  exact ⟨y, hy, i, hi⟩

private def regularizationApproximationRadius (m : ℕ) : ℝ :=
  1 / ((m + 1 : ℕ) : ℝ)

private theorem regularizationApproximationRadius_pos (m : ℕ) :
    0 < regularizationApproximationRadius m := by
  unfold regularizationApproximationRadius
  positivity

private theorem tendsto_regularizationApproximationRadius :
    Tendsto regularizationApproximationRadius atTop (𝓝 0) := by
  change Tendsto
    (fun m : ℕ => 1 / ((m + 1 : ℕ) : ℝ)) atTop (𝓝 0)
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem exists_upperRegularizationFamilyApproximant
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    ∃ z : X × ι,
      z.1 ∈ Metric.ball x (regularizationApproximationRadius m) ∧
        upperRegularization
          (fun y : X => sSup (Set.range fun j => F j y)) x -
            regularizationApproximationRadius m < F z.2 z.1 := by
  obtain ⟨y, hy, i, hi⟩ :=
    exists_mem_ball_family_sub_lt_upperRegularization
      F x (regularizationApproximationRadius_pos m)
        (regularizationApproximationRadius_pos m)
  exact ⟨(y, i), hy, hi⟩

private def upperRegularizationFamilyApproximant
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) : X × ι :=
  Classical.choose
    (exists_upperRegularizationFamilyApproximant F x m)

private theorem upperRegularizationFamilyApproximant_mem_ball
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    (upperRegularizationFamilyApproximant F x m).1 ∈
      Metric.ball x (regularizationApproximationRadius m) := by
  exact (Classical.choose_spec
    (exists_upperRegularizationFamilyApproximant F x m)).1

private theorem upperRegularizationFamilyApproximant_sub_lt
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) (m : ℕ) :
    upperRegularization
        (fun y : X => sSup (Set.range fun j => F j y)) x -
          regularizationApproximationRadius m <
      F (upperRegularizationFamilyApproximant F x m).2
        (upperRegularizationFamilyApproximant F x m).1 := by
  exact (Classical.choose_spec
    (exists_upperRegularizationFamilyApproximant F x m)).2

private theorem tendsto_upperRegularizationFamilyApproximant_center
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X) :
    Tendsto
      (fun m : ℕ =>
        (upperRegularizationFamilyApproximant F x m).1)
      atTop (𝓝 x) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hev :
      ∀ᶠ m : ℕ in atTop,
        regularizationApproximationRadius m < ε :=
    tendsto_regularizationApproximationRadius
      (Iio_mem_nhds hε)
  filter_upwards [hev] with m hm
  exact lt_trans
    (Metric.mem_ball.mp
      (upperRegularizationFamilyApproximant_mem_ball F x m)) hm

private theorem tendsto_upperRegularizationFamilyApproximant_value
    {X : Type*} [PseudoMetricSpace X]
    {ι : Type*} [Nonempty ι]
    (F : ι → X → ℝ) (x : X)
    (hbounded : ∀ y : X,
      BddAbove (Set.range fun i : ι => F i y))
    (hlocal : ∀ y : X,
      (localUpperBounds
        (fun z : X => sSup (Set.range fun i => F i z)) y).Nonempty) :
    Tendsto
      (fun m : ℕ =>
        F (upperRegularizationFamilyApproximant F x m).2
          (upperRegularizationFamilyApproximant F x m).1)
      atTop
      (𝓝 (upperRegularization
        (fun y : X => sSup (Set.range fun i => F i y)) x)) := by
  let f : X → ℝ :=
    fun y => sSup (Set.range fun i : ι => F i y)
  have hreg : UpperSemicontinuous (upperRegularization f) :=
    upperSemicontinuous_upperRegularization f hlocal
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hlow :
        Tendsto
          (fun m : ℕ =>
            upperRegularization f x -
              regularizationApproximationRadius m)
          atTop (𝓝 (upperRegularization f x)) := by
      simpa only [sub_zero] using
        tendsto_regularizationApproximationRadius.const_sub
          (upperRegularization f x)
    filter_upwards [(tendsto_order.mp hlow).1 a ha] with m hm
    exact hm.trans
      (upperRegularizationFamilyApproximant_sub_lt F x m)
  · intro a ha
    have hnear :
        ∀ᶠ y : X in 𝓝 x,
          upperRegularization f y < a :=
      hreg x a ha
    have hev :=
      (tendsto_upperRegularizationFamilyApproximant_center F x)
        hnear
    filter_upwards [hev] with m hm
    let y := (upperRegularizationFamilyApproximant F x m).1
    let i := (upperRegularizationFamilyApproximant F x m).2
    have hfamily : F i y ≤ f y := by
      exact le_csSup (hbounded y) ⟨i, rfl⟩
    have hupper : f y ≤ upperRegularization f y :=
      le_upperRegularization f y (hlocal y)
    exact (hfamily.trans hupper).trans_lt hm

private theorem limsup_integral_le_of_nonnegative_bounded
    {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (F : ℕ → α → ℝ) (g : α → ℝ) (C : ℝ)
    (hFmeas : ∀ m : ℕ, Measurable (F m))
    (hgint : Integrable g μ)
    (hFnonneg : ∀ m : ℕ, ∀ a : α, 0 ≤ F m a)
    (hFbound : ∀ m : ℕ, ∀ a : α, F m a ≤ C)
    (hgnonneg : ∀ᵐ a ∂μ, 0 ≤ g a)
    (hlimsup : ∀ᵐ a ∂μ,
      Filter.limsup (fun m : ℕ => F m a) atTop ≤ g a) :
    Filter.limsup (fun m : ℕ => ∫ a, F m a ∂μ) atTop ≤
      ∫ a, g a ∂μ := by
  have hFint (m : ℕ) : Integrable (F m) μ := by
    refine (integrable_const C).mono'
      ((hFmeas m).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnonneg m a)]
      exact hFbound m a
  have hintnonneg (m : ℕ) : 0 ≤ ∫ a, F m a ∂μ :=
    integral_nonneg (hFnonneg m)
  have hintbound (m : ℕ) :
      (∫ a, F m a ∂μ) ≤ ∫ _ : α, C ∂μ :=
    integral_mono (hFint m) (integrable_const C)
      (hFbound m)
  have hseqcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ a, F m a ∂μ) :=
    Filter.isCoboundedUnder_le_of_le atTop hintnonneg
  have hseqbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ a, F m a ∂μ) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hintbound)
  apply (ENNReal.ofReal_le_ofReal_iff
    (integral_nonneg_of_ae hgnonneg)).mp
  rw [ENNReal.ofReal_limsup hseqcob hseqbdd]
  have hrewrite (m : ℕ) :
      ENNReal.ofReal (∫ a, F m a ∂μ) =
        ∫⁻ a, ENNReal.ofReal (F m a) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (hFint m)
      (Filter.Eventually.of_forall (hFnonneg m))
  simp_rw [hrewrite]
  calc
    Filter.limsup
        (fun m : ℕ => ∫⁻ a, ENNReal.ofReal (F m a) ∂μ)
          atTop ≤
        ∫⁻ a,
          Filter.limsup
            (fun m : ℕ => ENNReal.ofReal (F m a)) atTop ∂μ := by
      apply MeasureTheory.limsup_lintegral_le
        (fun _ : α => ENNReal.ofReal C)
      · intro m
        exact ENNReal.continuous_ofReal.measurable.comp
          (hFmeas m)
      · intro m
        exact Filter.Eventually.of_forall fun a =>
          ENNReal.ofReal_le_ofReal (hFbound m a)
      · rw [lintegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (measure_ne_top μ Set.univ)
    _ ≤ ∫⁻ a, ENNReal.ofReal (g a) ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hlimsup] with a ha
      have hpcob :
          Filter.IsCoboundedUnder (· ≤ ·) atTop
            (fun m : ℕ => F m a) :=
        Filter.isCoboundedUnder_le_of_le atTop
          (fun m => hFnonneg m a)
      have hpbdd :
          Filter.IsBoundedUnder (· ≤ ·) atTop
            (fun m : ℕ => F m a) :=
        Filter.isBoundedUnder_of_eventually_le
          (Filter.Eventually.of_forall
            (fun m => hFbound m a))
      change
        Filter.limsup
          (fun m : ℕ => ENNReal.ofReal (F m a)) atTop ≤
            ENNReal.ofReal (g a)
      rw [← ENNReal.ofReal_limsup hpcob hpbdd]
      exact ENNReal.ofReal_le_ofReal ha
    _ = ENNReal.ofReal (∫ a, g a ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hgint hgnonneg).symm

private theorem limsup_le_of_upperSemicontinuous_of_tendsto
    {X : Type*} [TopologicalSpace X]
    (u : X → ℝ) (hu : UpperSemicontinuous u)
    (x : ℕ → X) (p : X)
    (hx : Tendsto x atTop (𝓝 p))
    (L C : ℝ)
    (hlower : ∀ m : ℕ, L ≤ u (x m))
    (hupper : ∀ m : ℕ, u (x m) ≤ C) :
    Filter.limsup (fun m : ℕ => u (x m)) atTop ≤ u p := by
  have hcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ => u (x m)) :=
    Filter.isCoboundedUnder_le_of_le atTop hlower
  have hbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => u (x m)) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hupper)
  apply (Filter.limsup_le_iff hcob hbdd).mpr
  intro b hb
  exact hx (hu p b hb)

private theorem limsup_integral_sub_const_le_of_upperSemicontinuous
    {X : Type*} [TopologicalSpace X]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ]
    (u : X → ℝ) (hu : UpperSemicontinuous u)
    (γ : ℕ → α → X) (γ₀ : α → X)
    (hγ : ∀ m : ℕ, Continuous (γ m))
    (hγ₀ : Continuous γ₀)
    (htend : ∀ a : α,
      Tendsto (fun m : ℕ => γ m a) atTop (𝓝 (γ₀ a)))
    (L C : ℝ)
    (hbound : ∀ m : ℕ, ∀ a : α,
      L ≤ u (γ m a) ∧ u (γ m a) ≤ C)
    (hbound₀ : ∀ a : α,
      L ≤ u (γ₀ a) ∧ u (γ₀ a) ≤ C) :
    Filter.limsup
        (fun m : ℕ => ∫ a, u (γ m a) - L ∂μ) atTop ≤
      ∫ a, u (γ₀ a) - L ∂μ := by
  have hshift : UpperSemicontinuous (fun z : X => u z - L) := by
    have hconst : UpperSemicontinuous (fun _ : X => -L) :=
      (continuous_const : Continuous (fun _ : X => -L)).upperSemicontinuous
    simpa only [sub_eq_add_neg] using
      hu.add hconst
  have hmeas (m : ℕ) :
      Measurable (fun a : α => u (γ m a) - L) := by
    exact (hshift.comp (hγ m)).measurable
  have hgmeas : Measurable (fun a : α => u (γ₀ a) - L) := by
    exact (hshift.comp hγ₀).measurable
  have hgint :
      Integrable (fun a : α => u (γ₀ a) - L) μ := by
    refine (integrable_const (C - L)).mono'
      hgmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hbound₀ a).1)]
      exact sub_le_sub_right (hbound₀ a).2 L
  apply limsup_integral_le_of_nonnegative_bounded μ
    (fun m a => u (γ m a) - L)
    (fun a => u (γ₀ a) - L) (C - L)
    hmeas hgint
  · exact fun m a => sub_nonneg.mpr (hbound m a).1
  · exact fun m a => sub_le_sub_right (hbound m a).2 L
  · exact Filter.Eventually.of_forall fun a =>
      sub_nonneg.mpr (hbound₀ a).1
  · filter_upwards [] with a
    exact limsup_le_of_upperSemicontinuous_of_tendsto
      (fun z : X => u z - L) hshift
      (fun m : ℕ => γ m a) (γ₀ a) (htend a)
      0 (C - L)
      (fun m => sub_nonneg.mpr (hbound m a).1)
      (fun m => sub_le_sub_right (hbound m a).2 L)

end ActualJetPlurisubharmonicClosure

namespace BergmanJetUpperEnvelope

open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman
open BergmanJetGeodesic BergmanJetRealGeodesic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem continuous_momentJointJetDiagonal
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (N : ℕ) :
    Continuous (momentJointJetDiagonal
      K hk F htransport p N) := by
  have heq : momentJointJetDiagonal K hk F htransport p N =
      fun q => ‖momentJointJetSectionVector
        K hk F htransport p N q‖ ^ 2 := by
    funext q
    exact (momentJointJetSectionVector_norm_sq
      K hk F htransport p N q).symm
  rw [heq]
  exact (differentiable_momentJointJetSectionVector
    K hk F htransport p N).continuous.norm.pow 2

private theorem momentJointJetDiagonal_eq_radial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ)
    {τ : ℂ} (hτ : τ ≠ 0) :
    momentJointJetDiagonal K hk F htransport p N (z, τ) =
      momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (Real.log (Complex.normSq τ) / 2) : ℂ)) := by
  have hsq : 0 < Complex.normSq τ := Complex.normSq_pos.mpr hτ
  have hrad :
      Real.exp (Real.log (Complex.normSq τ) / 2) ^ 2 =
        Complex.normSq τ := by
    rw [pow_two, ← Real.exp_add,
      show Real.log (Complex.normSq τ) / 2 +
          Real.log (Complex.normSq τ) / 2 =
        Real.log (Complex.normSq τ) by ring,
      Real.exp_log hsq]
  unfold momentJointJetDiagonal
  apply Finset.sum_congr rfl
  intro i _
  simp only [momentJointJetSection,
    Complex.normSq_mul, map_pow, Complex.normSq_ofReal]
  rw [← pow_two, hrad]

private def momentPositiveJointGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (k : ℕ)
    (q : PositiveJointLogSpace n) : ℝ :=
  Real.log
    (momentJointJetDiagonal K (Nat.zero_lt_succ k)
      F htransport p
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) q.val) /
      ((k + 1 : ℕ) : ℝ)

private theorem momentPositiveJointGeodesic_eq_momentJetGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (k : ℕ)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k q =
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) q.val.1
          (jointLogTime q) := by
  have hτ : q.val.2 ≠ 0 :=
    Complex.normSq_pos.mp
      (lt_trans (by norm_num : (0 : ℝ) < 1) q.property)
  unfold momentPositiveJointGeodesic jointLogTime
  rw [momentJointJetDiagonal_eq_radial
    K (Nat.zero_lt_succ k) F htransport p q.val.1
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) hτ]
  exact
    (momentJetGeodesic_eq_log_jointJetDiagonal
      K (Nat.zero_lt_succ k) F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) q.val.1
          (Real.log (Complex.normSq q.val.2))).symm

private def momentJointMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : PositiveJointLogSpace n) : ℝ :=
  momentNormalizedPotential F (jointRealCoordinate q) +
    BodyScale.canonicalScale K * jointLogTime q

private theorem continuous_momentJointMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentJointMajorant K F) := by
  unfold momentJointMajorant
  exact (continuous_momentNormalizedPotential F).comp
      (continuous_jointRealCoordinate n) |>.add
        (continuous_const.mul (continuous_jointLogTime n))

private theorem eventually_momentPositiveJointGeodesic_le_majorant_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      ∀ q : PositiveJointLogSpace n,
        momentPositiveJointGeodesic K F htransport p k q ≤
          momentJointMajorant K F q + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentJetGeodesic_le_potential_add_linear
      K F htransport
      (BodyScale.canonicalScale_pos K).le hε)
  filter_upwards [eventually_ge_atTop N] with k hk q
  have h := hN (k + 1) (by omega)
    (Nat.zero_lt_succ k) p q.val.1
    (jointLogTime q) (jointLogTime_pos q).le
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, momentJointMajorant,
    jointRealCoordinate, add_comm, ge_iff_le, add_left_comm] using h

private def momentJointTailStart
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) : ℕ :=
  Classical.choose (Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p (by norm_num : (0 : ℝ) < 1)))

private theorem momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (k : ℕ) (hk : momentJointTailStart K F htransport p ≤ k)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k q ≤
      momentJointMajorant K F q + 1 := by
  exact (Classical.choose_spec (Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p (by norm_num : (0 : ℝ) < 1)))) k hk q

private def momentJointTailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) : ℝ :=
  sSup (Set.range fun j : ℕ =>
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j) q)

private theorem momentJointTailSup_range_bddAbove
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    BddAbove (Set.range fun j : ℕ =>
      momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
  refine ⟨momentJointMajorant K F q + 1, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p _ (by omega) q

private theorem momentJointTailSup_le_majorant_add_one
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p r q ≤
      momentJointMajorant K F q + 1 := by
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p _ (by omega) q

private def momentJointTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) : PositiveJointLogSpace n → ℝ :=
  upperRegularization (momentJointTailSup K F htransport p r)

private theorem momentJointTailSup_localUpperBounds_nonempty
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    (localUpperBounds
      (momentJointTailSup K F htransport p r) q).Nonempty := by
  exact localUpperBounds_nonempty_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + 1)
    ((continuous_momentJointMajorant K F).add continuous_const)
    (momentJointTailSup_le_majorant_add_one
      K F htransport p r) q

private theorem upperSemicontinuous_momentJointTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) (r : ℕ) :
    UpperSemicontinuous
      (momentJointTailUpperEnvelope
        K F htransport p r) :=
  upperSemicontinuous_upperRegularization
    (momentJointTailSup K F htransport p r)
    (momentJointTailSup_localUpperBounds_nonempty
      K F htransport p r)

private theorem momentJointTailUpperEnvelope_le_majorant_add_one
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r q ≤
      momentJointMajorant K F q + 1 :=
  upperRegularization_le_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + 1)
    ((continuous_momentJointMajorant K F).add continuous_const)
    (momentJointTailSup_le_majorant_add_one
      K F htransport p r) q

private theorem momentJointTailSup_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {r s : ℕ} (hrs : r ≤ s)
    (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p s q ≤
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  apply le_csSup
    (momentJointTailSup_range_bddAbove
      K F htransport p r q)
  have hindex :
      momentJointTailStart K F htransport p + r +
        (s - r + j) =
      momentJointTailStart K F htransport p + s + j := by
    omega
  refine ⟨s - r + j, ?_⟩
  change
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r +
        (s - r + j)) q =
    momentPositiveJointGeodesic K F htransport p
      (momentJointTailStart K F htransport p + s + j) q
  rw [hindex]

private theorem momentJointTailUpperEnvelope_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {r s : ℕ} (hrs : r ≤ s)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p s q ≤
      momentJointTailUpperEnvelope K F htransport p r q :=
  upperRegularization_mono
    (momentJointTailSup K F htransport p s)
    (momentJointTailSup K F htransport p r) q
    (momentJointTailSup_antitone K F htransport p hrs)
    (momentJointTailSup_localUpperBounds_nonempty
      K F htransport p r q)

private theorem eventually_momentJointTailSup_le_majorant_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ q : PositiveJointLogSpace n,
      momentJointTailSup K F htransport p r q ≤
        momentJointMajorant K F q + ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (eventually_momentPositiveJointGeodesic_le_majorant_add
      K F htransport p hε)
  filter_upwards [eventually_ge_atTop N] with r hr q
  unfold momentJointTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact hN _ (by omega) q

private theorem eventually_momentJointTailUpperEnvelope_le_majorant_add
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ q : PositiveJointLogSpace n,
      momentJointTailUpperEnvelope K F htransport p r q ≤
        momentJointMajorant K F q + ε := by
  filter_upwards
    [eventually_momentJointTailSup_le_majorant_add
      K F htransport p hε] with r hr q
  exact upperRegularization_le_of_continuous_majorant
    (momentJointTailSup K F htransport p r)
    (fun z => momentJointMajorant K F z + ε)
    ((continuous_momentJointMajorant K F).add continuous_const)
    hr q

end BergmanJetUpperEnvelope

namespace BergmanJetEnvelopePlurisubharmonic

open Set Function Filter MeasureTheory Module
open SupportFunction MonomialIntegrability BergmanMonomials LatticeAsymptotics MomentOptimizer
open MomentFirstVariation MomentTargetGeodesic MomentRegularity MomentWeakBergman BergmanJetBasis
open BergmanJetGeodesic BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanGeodesicConvexity
open BergmanDiagonalBasisIndependence ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem momentZeroMonomialNorm_le_partition
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    monomialNormSquared k (0 : Space n)
        (momentNormalizedPotential F) ≤
      Real.exp
        (-(k : ℝ) * Real.log
          (finiteEnergySourcePartition F /
            normalizedVolume K.carrier)) *
        finiteEnergySourcePartition F := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hrawint :=
    integrable_monomialWeight_finiteEnergySource_of_mem_interior
      F htransport (LatticeAsymptotics.zero_mem_interior K)
      hkreal
  have hraw :
      monomialIntegral (k : ℝ) (0 : Space n) F.potential ≤
        finiteEnergySourcePartition F := by
    unfold monomialIntegral finiteEnergySourcePartition
    apply MeasureTheory.integral_mono hrawint F.densityIntegrable
    intro x
    unfold monomialWeight pairing
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub]
    apply Real.exp_le_exp.mpr
    nlinarith [F.nonnegative x]
  have hshift :
      monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F) =
        Real.exp
          (-(k : ℝ) * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
          monomialIntegral (k : ℝ) (0 : Space n)
            F.potential := by
    unfold monomialNormSquared monomialIntegral
    rw [show
      (fun x : Space n =>
        monomialWeight (k : ℝ) (0 : Space n)
          (momentNormalizedPotential F) x) =
      (fun x : Space n =>
        Real.exp
          (-(k : ℝ) * Real.log
            (finiteEnergySourcePartition F /
              normalizedVolume K.carrier)) *
        monomialWeight (k : ℝ) (0 : Space n)
          F.potential x) by
        funext x
        exact monomialWeight_momentNormalizedPotential_eq
          F (k : ℝ) (0 : Space n) x]
    exact MeasureTheory.integral_const_mul _ _
  rw [hshift]
  exact mul_le_mul_of_nonneg_left hraw (Real.exp_pos _).le

private def momentJointGlobalLowerBound
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) : ℝ :=
  Real.log
    (finiteEnergySourcePartition F /
      normalizedVolume K.carrier) -
    |Real.log (finiteEnergySourcePartition F)|

private theorem momentJointGlobalLowerBound_le_zeroMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentJointGlobalLowerBound K F ≤
      -(Real.log
        (monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F))) / (k : ℝ) := by
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkone : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hZ := finiteEnergySourcePartition_pos F
  have hnorm : 0 < monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F) := by
    simpa only using
      (momentMonomialNormSquared_pos K hk F htransport u₀)
  have hbound := momentZeroMonomialNorm_le_partition
    K hk F htransport
  have hlog := Real.log_le_log hnorm hbound
  rw [Real.log_mul (Real.exp_ne_zero _) hZ.ne',
    Real.log_exp] at hlog
  have habs :
      Real.log (finiteEnergySourcePartition F) ≤
        (k : ℝ) * |Real.log (finiteEnergySourcePartition F)| := by
    calc
      Real.log (finiteEnergySourcePartition F) ≤
        |Real.log (finiteEnergySourcePartition F)| := le_abs_self _
      _ ≤ (k : ℝ) * |Real.log (finiteEnergySourcePartition F)| := by
        nlinarith [abs_nonneg
          (Real.log (finiteEnergySourcePartition F))]
  unfold momentJointGlobalLowerBound
  apply (le_div_iff₀ hkreal).mpr
  nlinarith

private theorem inv_momentZeroMonomialNorm_le_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    (monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F))⁻¹ ≤
      diagonalKernel K k (momentNormalizedPotential F) x := by
  classical
  let := (monomialIndex_finite K hk).fintype
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hterm :
      (monomialNormSquared k (0 : Space n)
        (momentNormalizedPotential F))⁻¹ =
        diagonalTerm K k (momentNormalizedPotential F) u₀ x := by
    simp only [diagonalTerm, pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, mul_zero,
      Real.exp_zero, one_div, u₀]
  rw [hterm]
  unfold diagonalKernel
  rw [tsum_fintype]
  have hnonneg :
      ∀ u ∈ (Finset.univ : Finset (monomialIndex K k)),
        0 ≤ diagonalTerm K k
          (momentNormalizedPotential F) u x := by
    intro u _
    unfold diagonalTerm
    exact div_nonneg (Real.exp_pos _).le
      (momentMonomialNormSquared_pos
        K hk F htransport u).le
  exact Finset.single_le_sum hnonneg (Finset.mem_univ u₀)

private theorem momentJointGlobalLowerBound_le_log_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (x : Space n) :
    momentJointGlobalLowerBound K F ≤
      Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) := by
  let u₀ : monomialIndex K k :=
    ⟨0, zero_mem_monomialIndex K hk⟩
  have hnorm : 0 < monomialNormSquared k (0 : Space n)
      (momentNormalizedPotential F) := by
    simpa only using
      (momentMonomialNormSquared_pos K hk F htransport u₀)
  have hbound := inv_momentZeroMonomialNorm_le_diagonalKernel
    K hk F htransport x
  have hlog := Real.log_le_log (inv_pos.mpr hnorm) hbound
  rw [Real.log_inv] at hlog
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  calc
    momentJointGlobalLowerBound K F ≤
      -(Real.log
        (monomialNormSquared k (0 : Space n)
          (momentNormalizedPotential F))) / (k : ℝ) :=
      momentJointGlobalLowerBound_le_zeroMonomial
        K hk F htransport
    _ ≤ Real.log (diagonalKernel K k
        (momentNormalizedPotential F) x) / (k : ℝ) :=
      (div_le_div_iff_of_pos_right hkreal).mpr hlog

private theorem monotone_momentJetGeodesic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : TorusCharacters.LogSpace n) (N : ℕ) :
    Monotone (momentJetGeodesic
      K hk F htransport p N z) := by
  apply monotone_of_deriv_nonneg
  · intro t
    unfold momentJetGeodesic
    exact (hasDerivAt_logarithmicPotential
      (momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (momentTruncatedJetOrder K hk F htransport p N)
      (momentHolomorphicBasisWeight_nonneg
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (exists_positive_momentHolomorphicBasisWeight
        K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p) z)
      (k : ℝ) t).differentiableAt
  · exact momentJetGeodesic_deriv_nonneg
      K hk F htransport p N z

private theorem momentJointGlobalLowerBound_le_positiveJointGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (k : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentPositiveJointGeodesic
        K F htransport p k q := by
  let hk : 0 < k + 1 := Nat.zero_lt_succ k
  let N := Nat.floor (BodyScale.canonicalScale K *
    ((k + 1 : ℕ) : ℝ))
  calc
    momentJointGlobalLowerBound K F ≤
      Real.log
        (diagonalKernel K (k + 1)
          (momentNormalizedPotential F)
          (realLogCoordinate q.val.1)) /
            ((k + 1 : ℕ) : ℝ) :=
      momentJointGlobalLowerBound_le_log_diagonalKernel
        K hk F htransport (realLogCoordinate q.val.1)
    _ = momentJetGeodesic
      K hk F htransport p N q.val.1 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K hk F htransport p q.val.1 N).symm
    _ ≤ momentJetGeodesic
      K hk F htransport p N q.val.1 (jointLogTime q) :=
      monotone_momentJetGeodesic
        K hk F htransport p q.val.1 N (jointLogTime_pos q).le
    _ = momentPositiveJointGeodesic
      K F htransport p k q :=
      (momentPositiveJointGeodesic_eq_momentJetGeodesic
        K F htransport p k q).symm

private theorem momentJointGlobalLowerBound_le_tailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentJointTailSup K F htransport p r q := by
  calc
    momentJointGlobalLowerBound K F ≤
      momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r) q :=
      momentJointGlobalLowerBound_le_positiveJointGeodesic
        K F htransport p
        (momentJointTailStart K F htransport p + r) q
    _ ≤ momentJointTailSup K F htransport p r q := by
      unfold momentJointTailSup
      apply le_csSup
        (momentJointTailSup_range_bddAbove
          K F htransport p r q)
      exact ⟨0, by simp only [add_zero]⟩

private theorem momentJointGlobalLowerBound_le_tailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (r : ℕ) (q : PositiveJointLogSpace n) :
    momentJointGlobalLowerBound K F ≤
      momentJointTailUpperEnvelope
        K F htransport p r q := by
  calc
    momentJointGlobalLowerBound K F ≤
      momentJointTailSup K F htransport p r q :=
      momentJointGlobalLowerBound_le_tailSup
        K F htransport p r q
    _ ≤ momentJointTailUpperEnvelope
      K F htransport p r q :=
      le_upperRegularization
        (momentJointTailSup K F htransport p r) q
        (momentJointTailSup_localUpperBounds_nonempty
          K F htransport p r q)

end BergmanJetEnvelopePlurisubharmonic

namespace BergmanJetEnvelopeLimit

open Set Function Filter MeasureTheory Module
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic BergmanJetUpperEnvelope
open BergmanJetEnvelopePlurisubharmonic ActualJetUpperEnvelope
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem momentJointTailUpperEnvelope_bddBelow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    BddBelow (Set.range fun r : ℕ =>
      momentJointTailUpperEnvelope
        K F htransport p r q) := by
  refine ⟨momentJointGlobalLowerBound K F, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact momentJointGlobalLowerBound_le_tailUpperEnvelope
    K F htransport p r q

private def momentJointUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) : ℝ :=
  ⨅ r : ℕ, momentJointTailUpperEnvelope
    K F htransport p r q

private theorem upperSemicontinuous_momentJointUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n) :
    UpperSemicontinuous
      (momentJointUpperEnvelope K F htransport p) :=
  upperSemicontinuous_ciInf
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p)
    (upperSemicontinuous_momentJointTailUpperEnvelope
      K F htransport p)

private theorem tendsto_momentJointTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    Tendsto
      (fun r : ℕ => momentJointTailUpperEnvelope
        K F htransport p r q)
      atTop (𝓝 (momentJointUpperEnvelope
        K F htransport p q)) :=
  tendsto_atTop_ciInf
    (fun _ _ hrs => momentJointTailUpperEnvelope_antitone
      K F htransport p hrs q)
    (momentJointTailUpperEnvelope_bddBelow
      K F htransport p q)

private theorem momentJointUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : PositiveJointLogSpace n) :
    momentJointUpperEnvelope K F htransport p q ≤
      momentJointMajorant K F q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨r, hr⟩ :=
    (eventually_momentJointTailUpperEnvelope_le_majorant_add
      K F htransport p hε).exists
  calc
    momentJointUpperEnvelope K F htransport p q ≤
      momentJointTailUpperEnvelope
        K F htransport p r q :=
      ciInf_le (momentJointTailUpperEnvelope_bddBelow
        K F htransport p q) r
    _ ≤ momentJointMajorant K F q + ε := hr q

end BergmanJetEnvelopeLimit

namespace LogPartitionConvexity

open Set Filter MeasureTheory Metric
open JetEnvelopeSlopeConvergence
open scoped ENNReal Topology

private theorem sourceTorusBaseMeasure_neZero (n : ℕ) :
    NeZero (sourceTorusBaseMeasure n) := by
  refine ⟨?_⟩
  intro hzero
  have hmap := congrArg
    (Measure.map (Prod.fst :
      WeightedTorusHilbert.LogTorus n → Space n)) hzero
  have hvol : (volume : Measure (Space n)) = 0 := by
    simpa only [sourceTorusBaseMeasure, Measure.map_fst_prod, measure_univ, one_smul,
      Measure.map_zero] using hmap
  exact (NeZero.ne (volume : Measure (Space n))) hvol

private def sourceTimeDensity {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  Real.exp (-a t q)

private def sourcePartition {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)

private def sourceLogPartition {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  -Real.log (sourcePartition a t)

private def sourceFirstMoment {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    f t q * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)

private def sourceSecondMoment {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    f t q ^ 2 * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)

private def sourceAccelerationMoment {n : ℕ}
    (a j : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    j t q * sourceTimeDensity a t q ∂(sourceTorusBaseMeasure n)

private def sourceLogSlope {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  sourceFirstMoment a f t / sourcePartition a t

private def sourceMomentVariance {n : ℕ}
    (a f : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : ℝ :=
  sourceSecondMoment a f t / sourcePartition a t -
    (sourceLogSlope a f t) ^ 2

private def sourceNormalizedDensity {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  sourceTimeDensity a t q / sourcePartition a t

private def sourceProbability {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) : Measure (WeightedTorusHilbert.LogTorus n) :=
  (sourceTorusBaseMeasure n).withDensity
    (fun q => ENNReal.ofReal (sourceNormalizedDensity a t q))

private def sourceProbabilityMean {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (F : WeightedTorusHilbert.LogTorus n → ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    F q ∂(sourceProbability a t)

private def sourceProbabilityVariance {n : ℕ}
    (a : ℝ → WeightedTorusHilbert.LogTorus n → ℝ)
    (t : ℝ) (F : WeightedTorusHilbert.LogTorus n → ℝ) : ℝ :=
  ∫ q : WeightedTorusHilbert.LogTorus n,
    (F q - sourceProbabilityMean a t F) ^ 2
      ∂(sourceProbability a t)

end LogPartitionConvexity

namespace WeightedBrascampLieb

open Set MeasureTheory Matrix Filter
open WeightedPoincare
open scoped BigOperators ENNReal InnerProductSpace

private def euclideanGradient {n : ℕ}
    (f : Space n → ℝ) (x : Space n) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (coordinateGradient f x)

private theorem continuous_euclideanGradient {n : ℕ}
    {f : Space n → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (euclideanGradient f) := by
  unfold euclideanGradient
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp
  exact continuous_pi (fun i =>
    (hf.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const)

end WeightedBrascampLieb

namespace WeightedResolventConstantCore

open Set Function MeasureTheory Filter Matrix
open WeightedPoincare WeightedBrascampLieb
open scoped BigOperators ENNReal InnerProductSpace Topology

private def growingBump {n : ℕ} (k : ℕ) : ContDiffBump (0 : Space n) where
  rIn := (k : ℝ) + 1
  rOut := 2 * ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    nlinarith [Nat.cast_nonneg (α := ℝ) k]

private def unitBump {n : ℕ} : ContDiffBump (0 : Space n) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

private theorem growingBump_apply_eq_unit {n : ℕ} (k : ℕ) (x : Space n) :
    growingBump (n := n) k x = unitBump (n := n) (((k : ℝ) + 1)⁻¹ • x) := by
  have hk : (k : ℝ) + 1 ≠ 0 := by positivity
  simp only [growingBump, ContDiffBump.apply, isUnit_iff_ne_zero, ne_eq, hk, not_false_eq_true,
    IsUnit.mul_div_cancel_right, sub_zero, unitBump, div_one, inv_one, one_smul]

private theorem growingBump_eventually_one {n : ℕ} (x : Space n) :
    ∀ᶠ k : ℕ in atTop, growingBump k x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with k hk
  apply (growingBump k).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (k : ℝ) + 1
  have hNk : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  linarith

private theorem growingBump_fderiv {n : ℕ} (k : ℕ) (x : Space n) :
    fderiv ℝ (fun y : Space n => growingBump k y) x =
      ((k : ℝ) + 1)⁻¹ •
        fderiv ℝ (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x) := by
  have hfun :
      (fun y : Space n => growingBump k y) =
        (fun y : Space n =>
          unitBump (((k : ℝ) + 1)⁻¹ • y)) :=
    funext (growingBump_apply_eq_unit k)
  rw [hfun, fderiv_comp_smul]

private theorem unitBump_euclideanGradient_hasCompactSupport {n : ℕ} :
    HasCompactSupport
      (euclideanGradient (fun x : Space n => unitBump x)) := by
  refine ((unitBump (n := n)).hasCompactSupport.fderiv ℝ).mono ?_
  intro x
  exact mt (fun hx => by
    ext i
    simp only [euclideanGradient, coordinateGradient, hx, _root_.zero_apply, PiLp.zero_apply])

private theorem unitBump_euclideanGradient_bound {n : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : Space n,
        ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C := by
  have hsmooth :
      ContDiff ℝ 1 (fun x : Space n => unitBump x) :=
    (unitBump (n := n)).contDiff
  obtain ⟨C, hC⟩ :=
    (continuous_euclideanGradient hsmooth).bounded_above_of_compact_support
      (unitBump_euclideanGradient_hasCompactSupport (n := n))
  exact ⟨max C 0, le_max_right C 0,
    fun x => (hC x).trans (le_max_left C 0)⟩

private theorem growingBump_euclideanGradient {n : ℕ}
    (k : ℕ) (x : Space n) :
    euclideanGradient (fun y : Space n => growingBump k y) x =
      ((k : ℝ) + 1)⁻¹ •
        euclideanGradient (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x) := by
  ext i
  change
    (fderiv ℝ (fun y : Space n => growingBump k y) x)
        (Pi.single i (1 : ℝ)) =
      ((k : ℝ) + 1)⁻¹ *
        (fderiv ℝ (fun y : Space n => unitBump y)
          (((k : ℝ) + 1)⁻¹ • x)) (Pi.single i (1 : ℝ))
  rw [growingBump_fderiv]
  rfl

private theorem growingBump_euclideanGradient_norm_le {n : ℕ}
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y : Space n => unitBump y) x‖ ≤ C)
    (k : ℕ) (x : Space n) :
    ‖euclideanGradient (fun y : Space n => growingBump k y) x‖ ≤
      ((k : ℝ) + 1)⁻¹ * C := by
  rw [growingBump_euclideanGradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : 0 < ((k : ℝ) + 1)⁻¹)]
  exact mul_le_mul_of_nonneg_left (hC _) (by positivity)

private theorem inv_nat_add_one_tendsto_zero :
    Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹)
      atTop (nhds 0) := by
  have hcast : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun k : ℕ => (k : ℝ)⁻¹)
      atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  simpa only [comp_def, Nat.cast_add, Nat.cast_one] using
    hinv.comp (tendsto_add_atTop_nat 1)

end WeightedResolventConstantCore

namespace WeightedBrascampSaturation

open Set Function MeasureTheory Filter Matrix
open scoped BigOperators ENNReal InnerProductSpace Topology

private abbrev weightedTorusFormL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (WeightedTorusHilbert.weightedTorusMeasure k φ)

end WeightedBrascampSaturation

namespace HolomorphicLaurentFourierCompletenessBridge

open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private theorem periodic_holomorphic_vertical_integral_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiod : Function.Periodic f (2 * (Real.pi : ℂ) * Complex.I))
    (a b : ℝ) :
    (∫ t : ℝ in 0..2 * Real.pi,
      f ((b : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ in 0..2 * Real.pi,
        f ((a : ℂ) + (t : ℂ) * Complex.I) := by
  have hrect :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      f (⟨a, 0⟩ : ℂ) (⟨b, 2 * Real.pi⟩ : ℂ)
      hf.differentiableOn
  have htop :
      (∫ x : ℝ in a..b,
        f ((x : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) =
        ∫ x : ℝ in a..b, f (x : ℂ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simpa only [ofReal_mul, ofReal_ofNat] using hperiod (x : ℂ)
  have heq :
      Complex.I *
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((b : ℂ) + (t : ℂ) * Complex.I)) =
        Complex.I *
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    have hsimpl :
        ((∫ x : ℝ in a..b, f (x : ℂ)) -
          (∫ x : ℝ in a..b,
            f ((x : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I)) +
          Complex.I *
            (∫ t : ℝ in 0..2 * Real.pi,
              f ((b : ℂ) + (t : ℂ) * Complex.I)) -
          Complex.I *
            (∫ t : ℝ in 0..2 * Real.pi,
              f ((a : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
      simpa only [ofReal_mul, ofReal_ofNat, ofReal_zero, zero_mul, add_zero, smul_eq_mul] using
        hrect
    rw [htop] at hsimpl
    exact sub_eq_zero.mp (by simpa only [sub_self, zero_add] using hsimpl)
  exact mul_left_cancel₀ Complex.I_ne_zero heq

private def angularFourierCoefficient {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  UnitAddTorus.mFourierCoeff
    (fun θ : TorusCharacters.AngularTorus n =>
      f (x, θ)) m

private theorem angularSlice_sq_integrable_ae {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      Integrable
        (fun θ : TorusCharacters.AngularTorus n =>
          ‖f (x, θ)‖ ^ 2)
        (WeightedTorusHilbert.angularMeasure n) := by
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp (MeasureTheory.Lp.memLp f)
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare
  exact hsquare.prod_right_ae

private theorem angularSlice_memLp_ae {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      MemLp
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
        2 (WeightedTorusHilbert.angularMeasure n) := by
  have hmeas :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        AEStronglyMeasurable
          (fun θ : TorusCharacters.AngularTorus n =>
            f (x, θ))
          (WeightedTorusHilbert.angularMeasure n) := by
    have hf := (MeasureTheory.Lp.aestronglyMeasurable f)
    unfold WeightedTorusHilbert.weightedTorusMeasure at hf
    exact hf.prodMk_left
  filter_upwards [hmeas, angularSlice_sq_integrable_ae φ f]
    with x hx hsquare
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hx).mpr hsquare

private theorem angularFourierCoefficient_aestronglyMeasurable {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    AEStronglyMeasurable (angularFourierCoefficient φ f m)
      (WeightedTorusHilbert.radialMeasure k φ) := by
  have hchar :
      AEStronglyMeasurable
        (fun θ : TorusCharacters.AngularTorus n =>
          UnitAddTorus.mFourier (-m) θ)
        (WeightedTorusHilbert.angularMeasure n) := by
    exact (UnitAddTorus.mFourier (-m)).continuous.aestronglyMeasurable
  have hprod :
      AEStronglyMeasurable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          UnitAddTorus.mFourier (-m) z.2 * f z)
        ((WeightedTorusHilbert.radialMeasure k φ).prod
          (WeightedTorusHilbert.angularMeasure n)) := by
    have hf := (MeasureTheory.Lp.aestronglyMeasurable f)
    unfold WeightedTorusHilbert.weightedTorusMeasure at hf
    exact hchar.comp_snd.mul hf
  have hcoeff := hprod.integral_prod_right'
  refine hcoeff.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [WeightedTorusHilbert.angularMeasure, angularFourierCoefficient,
    UnitAddTorus.mFourierCoeff, smul_eq_mul]

private theorem angularFourierCoefficient_sq_le_slice_energy_ae {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      ‖angularFourierCoefficient φ f m x‖ ^ 2 ≤
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
  filter_upwards [angularSlice_memLp_ae φ f] with x hx
  let fx : MeasureTheory.Lp ℂ 2
      (WeightedTorusHilbert.angularMeasure n) :=
    hx.toLp (fun θ : TorusCharacters.AngularTorus n =>
      f (x, θ))
  have hfx :
      (fun θ : TorusCharacters.AngularTorus n =>
        fx θ) =ᵐ[WeightedTorusHilbert.angularMeasure n]
          (fun θ => f (x, θ)) :=
    hx.coeFn_toLp
  have hcoeff :
      UnitAddTorus.mFourierCoeff
        (fun θ : TorusCharacters.AngularTorus n => fx θ) m =
        angularFourierCoefficient φ f m x := by
    unfold angularFourierCoefficient UnitAddTorus.mFourierCoeff
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfx] with θ hθ
    simp only [hθ, smul_eq_mul]
  have henergy :
      (∫ θ : TorusCharacters.AngularTorus n,
        ‖fx θ‖ ^ 2 ∂(WeightedTorusHilbert.angularMeasure n)) =
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [hfx] with θ hθ
    rw [hθ]
  have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff fx
  have hle := le_hasSum hparse m (fun j hj => sq_nonneg _)
  rw [← hcoeff, ← henergy]
  exact hle

private theorem angularFourierCoefficient_sq_integrable {n k : ℕ}
    (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    Integrable
      (fun x : Space n =>
        ‖angularFourierCoefficient φ f m x‖ ^ 2)
      (WeightedTorusHilbert.radialMeasure k φ) := by
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp (MeasureTheory.Lp.memLp f)
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare
  have hmajor := hsquare.integral_prod_left
  refine hmajor.mono'
    ((angularFourierCoefficient_aestronglyMeasurable φ f m).norm.pow 2) ?_
  filter_upwards [angularFourierCoefficient_sq_le_slice_energy_ae
    φ f m] with x hx
  rwa [Real.norm_of_nonneg (sq_nonneg _)]

private def coordinateHolomorphicSlice {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) : ℂ → ℂ :=
  fun w => F (fun j => if j = i then w else ζ j)

private theorem differentiable_coordinateHolomorphicSlice {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) :
    Differentiable ℂ (coordinateHolomorphicSlice F ζ i) := by
  unfold coordinateHolomorphicSlice
  change Differentiable ℂ
    (F ∘ fun w : ℂ => fun j => if j = i then w else ζ j)
  apply hF.comp
  apply differentiable_pi.mpr
  intro j
  by_cases hji : j = i
  · simp only [hji, ↓reduceIte, differentiable_fun_id]
  · simp only [hji, ↓reduceIte, differentiable_const]

private theorem periodic_coordinateHolomorphicSlice {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) :
    Function.Periodic (coordinateHolomorphicSlice F ζ i)
      (2 * (Real.pi : ℂ) * Complex.I) := by
  intro w
  change
    F (fun j => if j = i then w + (2 * (Real.pi : ℂ) * Complex.I) else ζ j) =
      F (fun j => if j = i then w else ζ j)
  have hshift :
      (fun j : Fin n =>
        if j = i then w + (2 * (Real.pi : ℂ) * Complex.I) else ζ j) =
        (fun j : Fin n => if j = i then w else ζ j) +
          TorusCharacters.imaginaryShift
            (Pi.single i (1 : ℤ)) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [↓reduceIte, Pi.add_apply, TorusCharacters.imaginaryShift,
        Pi.single_eq_same, Int.cast_one, one_mul]
    · simp only [hji, ↓reduceIte, Pi.add_apply, TorusCharacters.imaginaryShift, ne_eq,
        not_false_eq_true, Pi.single_eq_of_ne, Int.cast_zero, zero_mul, add_zero]
  rw [hshift]
  exact hperiod (Pi.single i (1 : ℤ)) _

private theorem mFourierCoefficient_torusMonomial {n : ℕ}
    (m q : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
      (fun θ : TorusCharacters.AngularTorus n =>
        WeightedTorusHilbert.torusMonomial q (x, θ)) m =
      if m = q then
        WeightedTorusHilbert.radialCharacter q x
      else 0 := by
  unfold UnitAddTorus.mFourierCoeff
    WeightedTorusHilbert.torusMonomial
  calc
    (∫ θ : TorusCharacters.AngularTorus n,
      UnitAddTorus.mFourier (-m) θ •
        (WeightedTorusHilbert.radialCharacter q x *
          UnitAddTorus.mFourier q θ)) =
      ∫ θ : TorusCharacters.AngularTorus n,
        WeightedTorusHilbert.radialCharacter q x *
          (conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      rw [UnitAddTorus.mFourier_neg]
      simp only [smul_eq_mul]
      ring
    _ = WeightedTorusHilbert.radialCharacter q x *
        (∫ θ : TorusCharacters.AngularTorus n,
          conj (UnitAddTorus.mFourier m θ) *
            UnitAddTorus.mFourier q θ) :=
      MeasureTheory.integral_const_mul _ _
    _ = _ := by
      have hinner :
          (∫ θ : TorusCharacters.AngularTorus n,
            conj (UnitAddTorus.mFourier m θ) *
              UnitAddTorus.mFourier q θ) =
            if m = q then (1 : ℂ) else 0 := by
        simpa only [WeightedTorusHilbert.angularMeasure] using
          WeightedTorusHilbert.angularCharacter_inner m q
      rw [hinner]
      split_ifs <;> simp

private theorem radialCharacter_sq_integrable_iff_monomialWeight
    {n : ℕ} (k : ℕ)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u) :
    Integrable
      (fun x : Space n =>
        ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
      (WeightedTorusHilbert.radialMeasure k φ) ↔
    Integrable
      (MonomialIntegrability.monomialWeight (k : ℝ) u φ)
      (volume : Measure (Space n)) := by
  have hfinite :
      ∀ᵐ x ∂(volume : Measure (Space n)),
        WeightedTorusHilbert.radialWeight k φ x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold WeightedTorusHilbert.radialMeasure
  rw [MeasureTheory.integrable_withDensity_iff_integrable_smul'
    (WeightedTorusHilbert.radialWeight_measurable k hφ)
    hfinite]
  apply MeasureTheory.integrable_congr
  filter_upwards [] with x
  change
    (WeightedTorusHilbert.radialWeight k φ x).toReal *
        ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2 =
      MonomialIntegrability.monomialWeight
        (k : ℝ) u φ x
  unfold WeightedTorusHilbert.radialCharacter
  rw [TorusCharacters.norm_sq_torusCharacter_realLogSlice]
  simpa only [SupportFunction.pairing, integerPoint] using
    WeightedTorusHilbert.radialWeight_mul_exp_pairing
      k φ m u hm x

private theorem forbidden_angularFourierCoefficient_constant_eq_zero
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (hu : u ∉ interior K.carrier)
    (c : ℂ)
    (hcoefficient :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        angularFourierCoefficient φ f m x =
          c * WeightedTorusHilbert.radialCharacter m x) :
    c = 0 := by
  by_contra hc
  have hsq := angularFourierCoefficient_sq_integrable φ f m
  have hscaled :
      Integrable
        (fun x : Space n =>
          ‖c‖ ^ 2 *
            ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
        (WeightedTorusHilbert.radialMeasure k φ) := by
    apply hsq.congr
    filter_upwards [hcoefficient] with x hx
    rw [hx, norm_mul, mul_pow]
  have hcnorm : ‖c‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr hc)
  have hradial :
      Integrable
        (fun x : Space n =>
          ‖WeightedTorusHilbert.radialCharacter m x‖ ^ 2)
        (WeightedTorusHilbert.radialMeasure k φ) := by
    have h := hscaled.const_mul (‖c‖ ^ 2)⁻¹
    simpa only [ne_eq, hcnorm, not_false_eq_true, inv_mul_cancel_left₀] using h
  have hmono :=
    (radialCharacter_sq_integrable_iff_monomialWeight
      k hφ m u hm).mp hradial
  have hupper : ∀ x : Space n,
      φ x ≤ SupportFunction.supportFunction K.carrier x + C := by
    intro x
    have h := (abs_le.mp (hbounded x)).2
    linarith
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  exact MonomialDivergence.not_integrable_monomialWeight_of_centeredBody_not_mem_interior
    K hu hupper hkreal hmono

private theorem weightedHilbert_eq_zero_of_fourier
    {n k : ℕ} (φ : Space n → ℝ)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    (hcoeff : ∀ m : Fin n → ℤ,
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        angularFourierCoefficient φ f m x = 0) :
    f = 0 := by
  have hall :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        ∀ m : Fin n → ℤ, angularFourierCoefficient φ f m x = 0 :=
    MeasureTheory.ae_all_iff.mpr hcoeff
  have henergy :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖f (x, θ)‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) = 0 := by
    filter_upwards [hall, angularSlice_memLp_ae φ f] with x hx hmem
    let fx : MeasureTheory.Lp ℂ 2
        (WeightedTorusHilbert.angularMeasure n) :=
      hmem.toLp
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
    have hfx :
        (fun θ : TorusCharacters.AngularTorus n => fx θ)
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
            (fun θ => f (x, θ)) :=
      hmem.coeFn_toLp
    have hzero :
        ∀ m : Fin n → ℤ,
          UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              fx θ) m = 0 := by
      intro m
      calc
        UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n => fx θ) m =
          angularFourierCoefficient φ f m x := by
            unfold angularFourierCoefficient UnitAddTorus.mFourierCoeff
            apply MeasureTheory.integral_congr_ae
            filter_upwards [hfx] with θ hθ
            simp only [hθ, smul_eq_mul]
        _ = 0 := hx m
    have hparse := UnitAddTorus.hasSum_sq_mFourierCoeff fx
    have hsumzero :
        HasSum (fun _m : Fin n → ℤ => (0 : ℝ))
          (∫ θ : TorusCharacters.AngularTorus n,
            ‖fx θ‖ ^ 2
            ∂(WeightedTorusHilbert.angularMeasure n)) := by
      change HasSum
        (fun m : Fin n → ℤ =>
          ‖UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              fx θ) m‖ ^ 2)
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) at hparse
      simpa only [hzero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] using hparse
    have hz :
        (∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n)) = 0 :=
      hsumzero.unique hasSum_zero
    calc
      (∫ θ : TorusCharacters.AngularTorus n,
        ‖f (x, θ)‖ ^ 2
        ∂(WeightedTorusHilbert.angularMeasure n)) =
        ∫ θ : TorusCharacters.AngularTorus n,
          ‖fx θ‖ ^ 2
          ∂(WeightedTorusHilbert.angularMeasure n) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hfx] with θ hθ
        rw [hθ]
      _ = 0 := hz
  have hsquare :
      Integrable
        (fun z : WeightedTorusHilbert.LogTorus n =>
          ‖f z‖ ^ 2)
        (WeightedTorusHilbert.weightedTorusMeasure k φ) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (MeasureTheory.Lp.aestronglyMeasurable f)).mp
        (MeasureTheory.Lp.memLp f)
  have hintegral :
      (∫ z : WeightedTorusHilbert.LogTorus n,
        ‖f z‖ ^ 2
        ∂(WeightedTorusHilbert.weightedTorusMeasure k φ)) =
        0 := by
    unfold WeightedTorusHilbert.weightedTorusMeasure at hsquare ⊢
    rw [MeasureTheory.integral_prod _ hsquare]
    exact MeasureTheory.integral_eq_zero_of_ae henergy
  have hzero :
      (fun z : WeightedTorusHilbert.LogTorus n =>
        ‖f z‖ ^ 2)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
          0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg
      (fun z => sq_nonneg _) hsquare).mp hintegral
  apply MeasureTheory.Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero] with z hz
  have hnorm : ‖f z‖ = 0 := by
    exact sq_eq_zero_iff.mp (by simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero,
                                  Pi.zero_apply] using hz)
  exact norm_eq_zero.mp hnorm

end HolomorphicLaurentFourierCompletenessBridge

namespace JointHolomorphicLaurentFourierCompatibility

open Set MeasureTheory Filter Complex
open scoped BigOperators ComplexConjugate ENNReal Topology InnerProductSpace

local instance : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩

local instance : IsProbabilityMeasure
    (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

private def angularBox (n : ℕ) : Set (Space n) :=
  Set.univ.pi fun _ : Fin n => Set.Ioc (0 : ℝ) 1

private def angularBoxMeasure (n : ℕ) : Measure (Space n) :=
  Measure.pi fun _ : Fin n =>
    (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)

private theorem angularBoxMeasure_eq_restrict (n : ℕ) :
    angularBoxMeasure n =
      (volume : Measure (Space n)).restrict (angularBox n) := by
  unfold angularBoxMeasure angularBox
  rw [MeasureTheory.volume_pi, MeasureTheory.Measure.restrict_pi_pi]

private theorem continuous_integrable_angularBox {n : ℕ}
    {g : Space n → ℂ} (hg : Continuous g) :
    Integrable g (angularBoxMeasure n) := by
  rw [angularBoxMeasure_eq_restrict]
  apply (hg.integrableOn_Icc (a := (0 : Space n))
    (b := (1 : Space n))).mono_set
  intro x hx
  change (∀ i, 0 ≤ x i) ∧ (∀ i, x i ≤ 1)
  constructor
  · intro i
    exact (hx i (Set.mem_univ i)).1.le
  · intro i
    exact (hx i (Set.mem_univ i)).2

private def logarithmicPoint {n : ℕ}
    (x t : Space n) : TorusCharacters.LogSpace n :=
  fun i => (x i : ℂ) / 2 +
    (2 * (Real.pi : ℂ) * Complex.I) * (t i : ℂ)

private def coverRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (x : Space n)
    (θ : TorusCharacters.AngularTorus n) : ℂ :=
  F (fun i => (x i : ℂ) / 2 +
    (2 * (Real.pi : ℂ) * Complex.I) *
      ((AddCircle.equivIoc 1 0 (θ i)).1 : ℂ))

private theorem coverRepresentative_coe {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (x t : Space n) (ht : t ∈ angularBox n) :
    coverRepresentative F x (fun i => (t i : UnitAddCircle)) =
      F (logarithmicPoint x t) := by
  unfold coverRepresentative logarithmicPoint
  congr 1
  funext i
  have hi : t i ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    simpa only [zero_add, mem_Ioc] using ht i (Set.mem_univ i)
  rw [AddCircle.equivIoc_coe_eq hi]

private def globalLaurentTwist {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) :
    TorusCharacters.LogSpace n → ℂ :=
  fun ζ => Complex.exp
      (-(TorusCharacters.characterExponent m ζ)) * F ζ

private theorem differentiable_globalLaurentTwist {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) (m : Fin n → ℤ) :
    Differentiable ℂ (globalLaurentTwist F m) := by
  unfold globalLaurentTwist TorusCharacters.characterExponent
  fun_prop

private theorem periodic_globalLaurentTwist {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m q : Fin n → ℤ) :
    Function.Periodic (globalLaurentTwist F m)
      (TorusCharacters.imaginaryShift q) := by
  intro ζ
  unfold globalLaurentTwist
  rw [TorusCharacters.characterExponent_add,
    TorusCharacters.characterExponent_imaginaryShift,
    neg_add_rev, Complex.exp_add, hperiod q ζ]
  have hneg :
      -(((∑ i, m i * q i : ℤ) : ℂ) *
        (2 * (Real.pi : ℂ) * Complex.I)) =
        ((-(∑ i, m i * q i : ℤ) : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [hneg, Complex.exp_int_mul_two_pi_mul_I]
  ring

private def twistedAngularIntegrand {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) :
    Space n → ℂ :=
  fun t => globalLaurentTwist F m (logarithmicPoint x t)

private theorem continuous_twistedAngularIntegrand {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F) (m : Fin n → ℤ)
    (x : Space n) :
    Continuous (twistedAngularIntegrand F m x) := by
  unfold twistedAngularIntegrand logarithmicPoint
  apply (differentiable_globalLaurentTwist hF m).continuous.comp
  fun_prop

private theorem unit_interval_vertical_integral_eq
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hperiod : Function.Periodic f (2 * (Real.pi : ℂ) * Complex.I))
    (a b : ℝ) :
    (∫ t : ℝ in 0..1,
      f ((b : ℂ) +
        (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
      ∫ t : ℝ in 0..1,
        f ((a : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)) := by
  have hcg :=
    HolomorphicLaurentFourierCompletenessBridge.periodic_holomorphic_vertical_integral_eq
      hf hperiod a b
  have hπ : (2 * Real.pi : ℝ) ≠ 0 :=
    ne_of_gt Real.two_pi_pos
  have hscale (r : ℝ) :
      (∫ t : ℝ in 0..1,
        f ((r : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
        (2 * Real.pi : ℝ)⁻¹ •
          (∫ t : ℝ in 0..2 * Real.pi,
            f ((r : ℂ) + (t : ℂ) * Complex.I)) := by
    have h := intervalIntegral.integral_comp_mul_left
      (a := (0 : ℝ)) (b := (1 : ℝ))
      (c := 2 * Real.pi)
      (fun t : ℝ => f ((r : ℂ) + (t : ℂ) * Complex.I)) hπ
    calc
      (∫ t : ℝ in 0..1,
        f ((r : ℂ) +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ))) =
        ∫ t : ℝ in 0..1,
          f ((r : ℂ) + ((2 * Real.pi * t : ℝ) : ℂ) *
            Complex.I) := by
          apply intervalIntegral.integral_congr
          intro t ht
          push_cast
          ring_nf
      _ = (2 * Real.pi : ℝ)⁻¹ •
          (∫ t : ℝ in (2 * Real.pi) * 0..(2 * Real.pi) * 1,
            f ((r : ℂ) + (t : ℂ) * Complex.I)) := h
      _ = _ := by simp only [mul_zero, mul_one]
  rw [hscale b, hscale a, hcg]

private theorem coordinate_unit_interval_twist_integral_eq {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ)
    (ζ : TorusCharacters.LogSpace n)
    (i : Fin n) (a b : ℝ) :
    (∫ t : ℝ in 0..1,
      globalLaurentTwist F m
        (fun j => if j = i
          then (b : ℂ) +
            (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
          else ζ j)) =
      ∫ t : ℝ in 0..1,
        globalLaurentTwist F m
          (fun j => if j = i
            then (a : ℂ) +
              (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
            else ζ j) := by
  apply unit_interval_vertical_integral_eq
    (HolomorphicLaurentFourierCompletenessBridge.differentiable_coordinateHolomorphicSlice
      (differentiable_globalLaurentTwist hF m) ζ i)
    (HolomorphicLaurentFourierCompletenessBridge.periodic_coordinateHolomorphicSlice
      (fun q => periodic_globalLaurentTwist hperiod m q) ζ i)

private theorem angularBoxIntegral_eq_of_coordinate_slice
    {n : ℕ} {g h : Space (n + 1) → ℂ}
    (hg : Continuous g) (hh : Continuous h)
    (i : Fin (n + 1))
    (hslice : ∀ y : Fin n → ℝ,
      (∫ t : ℝ in 0..1, g (i.insertNth t y)) =
        ∫ t : ℝ in 0..1, h (i.insertNth t y)) :
    (∫ t : Space (n + 1),
      g t ∂(angularBoxMeasure (n + 1))) =
      ∫ t : Space (n + 1),
        h t ∂(angularBoxMeasure (n + 1)) := by
  let μ : Fin (n + 1) → Measure ℝ :=
    fun _ => (volume : Measure ℝ).restrict (Set.Ioc (0 : ℝ) 1)
  let ν : Measure (Fin n → ℝ) :=
    Measure.pi fun j : Fin n => μ (i.succAbove j)
  let e :
      (ℝ × (Fin n → ℝ)) ≃ᵐ Space (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i).symm
  have he :
      MeasurePreserving e ((μ i).prod ν)
        (angularBoxMeasure (n + 1)) := by
    simpa [angularBoxMeasure, μ, ν, e] using
      (MeasureTheory.measurePreserving_piFinSuccAbove μ i).symm
  have hgi :
      Integrable
        (fun z : ℝ × (Fin n → ℝ) =>
          g (i.insertNth z.1 z.2))
        ((μ i).prod ν) := by
    have h' := he.integrable_comp_of_integrable
      (continuous_integrable_angularBox hg)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h'
  have hhi :
      Integrable
        (fun z : ℝ × (Fin n → ℝ) =>
          h (i.insertNth z.1 z.2))
        ((μ i).prod ν) := by
    have h' := he.integrable_comp_of_integrable
      (continuous_integrable_angularBox hh)
    simpa [e, Function.comp_def,
      MeasurableEquiv.piFinSuccAbove_symm_apply,
      Fin.insertNthEquiv] using h'
  calc
    (∫ t : Space (n + 1),
      g t ∂(angularBoxMeasure (n + 1))) =
      ∫ z : ℝ × (Fin n → ℝ),
        g (i.insertNth z.1 z.2) ∂((μ i).prod ν) := by
          simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Equiv.coe_fn_mk,
            e] using (he.integral_comp' g).symm
    _ = ∫ y : Fin n → ℝ,
          (∫ t : ℝ, g (i.insertNth t y) ∂(μ i)) ∂ν :=
        MeasureTheory.integral_prod_symm _ hgi
    _ = ∫ y : Fin n → ℝ,
          (∫ t : ℝ, h (i.insertNth t y) ∂(μ i)) ∂ν := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with y
          change
            (∫ t : ℝ in Set.Ioc (0 : ℝ) 1,
              g (i.insertNth t y)) =
              ∫ t : ℝ in Set.Ioc (0 : ℝ) 1,
                h (i.insertNth t y)
          simpa only [← intervalIntegral.integral_of_le
            (by norm_num : (0 : ℝ) ≤ 1)] using hslice y
    _ = ∫ z : ℝ × (Fin n → ℝ),
          h (i.insertNth z.1 z.2) ∂((μ i).prod ν) :=
        (MeasureTheory.integral_prod_symm _ hhi).symm
    _ = ∫ t : Space (n + 1),
          h t ∂(angularBoxMeasure (n + 1)) := by
          simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Equiv.coe_fn_mk,
            e] using (he.integral_comp' h)

private theorem logarithmicPoint_insertNth {n : ℕ}
    (x : Space (n + 1))
    (i : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    logarithmicPoint x (i.insertNth t y) =
      fun j => if j = i
        then (x i : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
        else logarithmicPoint x (i.insertNth 0 y) j := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp only [logarithmicPoint, Fin.insertNth_apply_same, ↓reduceIte]
  · intro j
    simp only [logarithmicPoint, Fin.insertNth_apply_succAbove, i.succAbove_ne, ↓reduceIte]

private theorem logarithmicPoint_update_insertNth {n : ℕ}
    (x : Space (n + 1))
    (i : Fin (n + 1)) (a : ℝ)
    (y : Fin n → ℝ) (t : ℝ) :
    logarithmicPoint (Function.update x i a) (i.insertNth t y) =
      fun j => if j = i
        then (a : ℂ) / 2 +
          (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
        else logarithmicPoint x (i.insertNth 0 y) j := by
  apply funext
  rw [i.forall_iff_succAbove]
  constructor
  · simp only [logarithmicPoint, Function.update_self, Fin.insertNth_apply_same, ↓reduceIte]
  · intro j
    simp only [logarithmicPoint, ne_eq, i.succAbove_ne, not_false_eq_true, Function.update_of_ne,
      Fin.insertNth_apply_succAbove, ↓reduceIte]

private theorem twistedAngularIntegral_coordinate_update {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n)
    (i : Fin n) (a : ℝ) :
    (∫ t : Space n,
      twistedAngularIntegrand F m x t
        ∂(angularBoxMeasure n)) =
      ∫ t : Space n,
        twistedAngularIntegrand F m
          (Function.update x i a) t
          ∂(angularBoxMeasure n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    apply angularBoxIntegral_eq_of_coordinate_slice
      (continuous_twistedAngularIntegrand hF m x)
      (continuous_twistedAngularIntegrand hF m
        (Function.update x i a)) i
    intro y
    have h :=
      coordinate_unit_interval_twist_integral_eq
        hF hperiod m
        (logarithmicPoint x (i.insertNth 0 y)) i
        (a / 2) (x i / 2)
    calc
      (∫ t : ℝ in 0..1,
        twistedAngularIntegrand F m x (i.insertNth t y)) =
        ∫ t : ℝ in 0..1,
          globalLaurentTwist F m
            (fun j => if j = i
              then ((x i / 2 : ℝ) : ℂ) +
                (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
              else logarithmicPoint x (i.insertNth 0 y) j) := by
            apply intervalIntegral.integral_congr
            intro t ht
            unfold twistedAngularIntegrand
            apply congrArg (globalLaurentTwist F m)
            simpa only [Complex.ofReal_div,
              Complex.ofReal_ofNat] using
              logarithmicPoint_insertNth x i y t
      _ = ∫ t : ℝ in 0..1,
          globalLaurentTwist F m
            (fun j => if j = i
              then ((a / 2 : ℝ) : ℂ) +
                (2 * (Real.pi : ℂ) * Complex.I) * (t : ℂ)
              else logarithmicPoint x (i.insertNth 0 y) j) := h
      _ = ∫ t : ℝ in 0..1,
          twistedAngularIntegrand F m
            (Function.update x i a) (i.insertNth t y) := by
            apply intervalIntegral.integral_congr
            intro t ht
            unfold twistedAngularIntegrand
            apply congrArg (globalLaurentTwist F m)
            symm
            simpa only [Complex.ofReal_div,
              Complex.ofReal_ofNat] using
              logarithmicPoint_update_insertNth x i a y t

private def twistedAngularAverage {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) : ℂ :=
  ∫ t : Space n,
    twistedAngularIntegrand F m x t ∂(angularBoxMeasure n)

private theorem twistedAngularAverage_coordinate_update {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n)
    (i : Fin n) (a : ℝ) :
    twistedAngularAverage F m x =
      twistedAngularAverage F m (Function.update x i a) := by
  exact twistedAngularIntegral_coordinate_update
    hF hperiod m x i a

private theorem twistedAngularAverage_eq_zero {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n) :
    twistedAngularAverage F m x =
      twistedAngularAverage F m 0 := by
  classical
  have hreset : ∀ s : Finset (Fin n),
      twistedAngularAverage F m x =
        twistedAngularAverage F m
          (fun i => if i ∈ s then 0 else x i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.notMem_empty, ↓reduceIte]
    | @insert i s hi ih =>
      calc
        twistedAngularAverage F m x =
          twistedAngularAverage F m
            (fun j => if j ∈ s then 0 else x j) := ih
        _ = twistedAngularAverage F m
            (Function.update
              (fun j => if j ∈ s then 0 else x j) i 0) :=
          twistedAngularAverage_coordinate_update
            hF hperiod m _ i 0
        _ = twistedAngularAverage F m
            (fun j => if j ∈ insert i s then 0 else x j) := by
          congr 1
          funext j
          by_cases hji : j = i
          · subst j
            simp only [Function.update_self, Finset.mem_insert, true_or, ↓reduceIte]
          · simp only [Function.update, hji, ↓reduceDIte, Finset.mem_insert, false_or]
  calc
    twistedAngularAverage F m x =
        twistedAngularAverage F m
          (fun i => if i ∈ (Finset.univ : Finset (Fin n))
            then 0 else x i) := hreset Finset.univ
    _ = twistedAngularAverage F m 0 := by
      congr 1
      funext i
      simp only [Finset.mem_univ, ↓reduceIte, Pi.zero_apply]

private theorem mFourier_neg_coe_eq_exp {n : ℕ}
    (m : Fin n → ℤ) (t : Space n) :
    UnitAddTorus.mFourier (-m)
        (fun i => (t i : UnitAddCircle)) =
      Complex.exp
        (-(TorusCharacters.characterExponent m
          (logarithmicPoint 0 t))) := by
  unfold UnitAddTorus.mFourier
    TorusCharacters.characterExponent
    logarithmicPoint
  simp only [ContinuousMap.coe_mk, Pi.neg_apply,
    Pi.zero_apply, Complex.ofReal_zero, zero_div, zero_add]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  push_cast
  ring

private theorem logarithmicPoint_eq_add {n : ℕ}
    (x t : Space n) :
    logarithmicPoint x t =
      TorusCharacters.realLogSlice x +
        logarithmicPoint 0 t := by
  funext i
  simp only [logarithmicPoint, Pi.add_apply, TorusCharacters.realLogSlice, Pi.zero_apply,
    ofReal_zero, zero_div, zero_add]

private theorem characterExponent_logarithmicPoint {n : ℕ}
    (m : Fin n → ℤ) (x t : Space n) :
    TorusCharacters.characterExponent m
        (logarithmicPoint x t) =
      TorusCharacters.characterExponent m
        (TorusCharacters.realLogSlice x) +
      TorusCharacters.characterExponent m
        (logarithmicPoint 0 t) := by
  rw [logarithmicPoint_eq_add,
    TorusCharacters.characterExponent_add]

private theorem fourier_times_cover_eq_radial_twist {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x t : Space n) :
    UnitAddTorus.mFourier (-m)
        (fun i => (t i : UnitAddCircle)) *
          F (logarithmicPoint x t) =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularIntegrand F m x t := by
  rw [mFourier_neg_coe_eq_exp]
  unfold WeightedTorusHilbert.radialCharacter
    TorusCharacters.torusCharacter
    twistedAngularIntegrand globalLaurentTwist
  rw [characterExponent_logarithmicPoint m x t]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  ring

private theorem measurableSet_angularBox (n : ℕ) :
    MeasurableSet (angularBox n) := by
  unfold angularBox
  exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

private theorem angularBox_eq_setOf (n : ℕ) :
    angularBox n =
      {t : Space n | ∀ i, t i ∈ Set.Ioc (0 : ℝ) 1} := by
  ext t
  simp only [angularBox, Set.mem_pi, mem_univ, mem_Ioc, forall_const, mem_ofPred_eq]

private theorem mFourierCoefficient_coverRepresentative_eq_twistedAverage
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x := by
  calc
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      ∫ t : Space n in angularBox n,
        UnitAddTorus.mFourier (-m)
          (fun i => (t i : UnitAddCircle)) *
            coverRepresentative F x
              (fun i => (t i : UnitAddCircle)) := by
          simpa only [angularBox_eq_setOf, mem_Ioc, zero_add, smul_eq_mul] using
            UnitAddTorus.mFourierCoeff_eq_integral
              (coverRepresentative F x) m (fun _ => 0)
    _ = ∫ t : Space n,
        (WeightedTorusHilbert.radialCharacter m x *
          twistedAngularIntegrand F m x t)
          ∂(angularBoxMeasure n) := by
          rw [angularBoxMeasure_eq_restrict]
          apply MeasureTheory.integral_congr_ae
          filter_upwards [MeasureTheory.ae_restrict_mem
            (measurableSet_angularBox n)] with t ht
          rw [coverRepresentative_coe F x t ht]
          exact fourier_times_cover_eq_radial_twist F m x t
    _ = WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x := by
          exact MeasureTheory.integral_const_mul _ _

private theorem mFourierCoefficient_coverRepresentative_eq_radial
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (m : Fin n → ℤ) (x : Space n) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x := by
  have hzero :
      UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m =
        twistedAngularAverage F m 0 := by
    rw [mFourierCoefficient_coverRepresentative_eq_twistedAverage]
    simp only [WeightedTorusHilbert.radialCharacter, TorusCharacters.torusCharacter,
      TorusCharacters.characterExponent, TorusCharacters.realLogSlice, Pi.zero_apply, ofReal_zero,
      zero_div, mul_zero, Finset.sum_const_zero, exp_zero, one_mul]
  calc
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m =
      WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m x :=
      mFourierCoefficient_coverRepresentative_eq_twistedAverage
        F m x
    _ = WeightedTorusHilbert.radialCharacter m x *
        twistedAngularAverage F m 0 := by
      rw [twistedAngularAverage_eq_zero hF hperiod]
    _ = UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x := by
      rw [hzero]
      ring

private theorem angularFourierCoefficient_of_holomorphic_representative_ae
    {n k : ℕ}
    {φ : Space n → ℝ}
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ f m x =
        UnitAddTorus.mFourierCoeff
            (coverRepresentative F 0) m *
          WeightedTorusHilbert.radialCharacter m x := by
  have hslices :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (fun θ : TorusCharacters.AngularTorus n =>
          f (x, θ))
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
        (fun θ => coverRepresentative F x θ) := by
    unfold WeightedTorusHilbert.weightedTorusMeasure
      at hrepresentative
    exact MeasureTheory.Measure.ae_ae_eq_curry_of_prod
      hrepresentative
  filter_upwards [hslices] with x hx
  calc
    HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
        φ f m x =
      UnitAddTorus.mFourierCoeff
        (coverRepresentative F x) m := by
        unfold
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          UnitAddTorus.mFourierCoeff
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hx] with θ hθ
        simp only [hθ, smul_eq_mul]
    _ = UnitAddTorus.mFourierCoeff
          (coverRepresentative F 0) m *
        WeightedTorusHilbert.radialCharacter m x :=
      mFourierCoefficient_coverRepresentative_eq_radial
        hF hperiod m x

private theorem forbidden_coefficient_of_holomorphic_representative_eq_zero
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    (m : Fin n → ℤ) (u : Space n)
    (hm : integerPoint n m = (k : ℝ) • u)
    (hu : u ∉ interior K.carrier) :
    UnitAddTorus.mFourierCoeff
        (coverRepresentative F 0) m = 0 := by
  exact
    HolomorphicLaurentFourierCompletenessBridge.forbidden_angularFourierCoefficient_constant_eq_zero
      K hk hφ hbounded f m u hm hu
      (UnitAddTorus.mFourierCoeff (coverRepresentative F 0) m)
      (angularFourierCoefficient_of_holomorphic_representative_ae
        f hF hperiod hrepresentative m)

private theorem angularCharacter_mul_slice_integrable {n : ℕ}
    {g : TorusCharacters.AngularTorus n → ℂ}
    (hg : MemLp g 2
      (WeightedTorusHilbert.angularMeasure n))
    (m : Fin n → ℤ) :
    Integrable
      (fun θ : TorusCharacters.AngularTorus n =>
        UnitAddTorus.mFourier (-m) θ * g θ)
      (WeightedTorusHilbert.angularMeasure n) := by
  refine (hg.integrable (by norm_num)).bdd_mul (c := (1 : ℝ))
    (UnitAddTorus.mFourier (-m)).continuous.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [WeightedTorusHilbert.angularCharacter_norm]

private theorem angularFourierCoefficient_sub_ae
    {n k : ℕ} (φ : Space n → ℝ)
    (f g : WeightedTorusHilbert.weightedHilbert k φ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ (f - g) m x =
        HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            φ f m x -
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            φ g m x := by
  have hsub := MeasureTheory.Lp.coeFn_sub f g
  unfold WeightedTorusHilbert.weightedTorusMeasure at hsub
  have hslices :
      ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
        (fun θ : TorusCharacters.AngularTorus n =>
          (f - g) (x, θ))
          =ᵐ[WeightedTorusHilbert.angularMeasure n]
        (fun θ => f (x, θ) - g (x, θ)) := by
    filter_upwards [MeasureTheory.Measure.ae_ae_eq_curry_of_prod hsub]
      with x hx
    filter_upwards [hx] with θ hθ
    exact hθ
  filter_upwards [hslices,
    HolomorphicLaurentFourierCompletenessBridge.angularSlice_memLp_ae φ f,
    HolomorphicLaurentFourierCompletenessBridge.angularSlice_memLp_ae φ g]
    with x hx hfx hgx
  unfold HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
    UnitAddTorus.mFourierCoeff
  simp only [smul_eq_mul]
  calc
    (∫ θ : TorusCharacters.AngularTorus n,
      UnitAddTorus.mFourier (-m) θ * (f - g) (x, θ)) =
      ∫ θ : TorusCharacters.AngularTorus n,
        (UnitAddTorus.mFourier (-m) θ * f (x, θ) -
          UnitAddTorus.mFourier (-m) θ * g (x, θ)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [hx] with θ hθ
        rw [hθ]
        ring
    _ = _ := MeasureTheory.integral_sub
      (angularCharacter_mul_slice_integrable hfx m)
      (angularCharacter_mul_slice_integrable hgx m)

private theorem indexedMonomial_finite_sum_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (s : Finset (LatticeAsymptotics.monomialIndex K k))
    (c : LatticeAsymptotics.monomialIndex K k → ℂ) :
    (fun z : WeightedTorusHilbert.LogTorus n =>
      (∑ u ∈ s, c u •
        WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u) z)
      =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
    (fun z =>
      ∑ u ∈ s, c u *
        WeightedTorusHilbert.torusMonomial
          (WeightedTorusHilbert.integerExponent K hk u) z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    filter_upwards [MeasureTheory.Lp.coeFn_zero ℂ 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)]
      with z hz
    simpa only [Finset.sum_empty, Pi.zero_apply] using hz
  | @insert u s hu ih =>
    have hadd :=
      MeasureTheory.Lp.coeFn_add
        (c u • WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u)
        (∑ v ∈ s, c v •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded v)
    have hsmul :=
      MeasureTheory.Lp.coeFn_smul (c u)
        (WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u)
    have hmono :=
      WeightedTorusHilbert.indexedMonomialLp_ae
        K hk hφ hbounded u
    filter_upwards [hadd, hsmul, hmono, ih]
      with z hzadd hzsmul hzmono hzsum
    simp only [Finset.sum_insert hu]
    rw [hzadd]
    change
      (c u • WeightedTorusHilbert.indexedMonomialLp
        K hk hφ hbounded u) z +
        (∑ v ∈ s, c v •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded v) z =
        c u * WeightedTorusHilbert.torusMonomial
          (WeightedTorusHilbert.integerExponent K hk u) z +
          ∑ v ∈ s, c v *
            WeightedTorusHilbert.torusMonomial
              (WeightedTorusHilbert.integerExponent K hk v) z
    rw [hzsmul, hzsum]
    change
      c u * WeightedTorusHilbert.indexedMonomialLp
          K hk hφ hbounded u z + _ = _
    rw [hzmono]

private theorem torusMonomial_angular_memLp {n : ℕ}
    (m : Fin n → ℤ) (x : Space n) :
    MemLp
      (fun θ : TorusCharacters.AngularTorus n =>
        WeightedTorusHilbert.torusMonomial m (x, θ))
      2 (WeightedTorusHilbert.angularMeasure n) := by
  refine MeasureTheory.MemLp.of_bound
    ((WeightedTorusHilbert.continuous_torusMonomial m).comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    ‖WeightedTorusHilbert.radialCharacter m x‖ ?_
  exact Filter.Eventually.of_forall fun θ => by
    simp only [WeightedTorusHilbert.torusMonomial, Complex.norm_mul,
      WeightedTorusHilbert.angularCharacter_norm, mul_one, Std.le_refl]

private theorem angularFourierCoefficient_indexed_finite_sum_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (s : Finset (LatticeAsymptotics.monomialIndex K k))
    (c : LatticeAsymptotics.monomialIndex K k → ℂ)
    (m : Fin n → ℤ) :
    ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
      HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ
          (∑ u ∈ s, c u •
            WeightedTorusHilbert.indexedMonomialLp
              K hk hφ hbounded u)
          m x =
        ∑ u ∈ s, c u *
          (if m =
              WeightedTorusHilbert.integerExponent K hk u
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk u) x
            else 0) := by
  have hrep :=
    indexedMonomial_finite_sum_ae K hk hφ hbounded s c
  unfold WeightedTorusHilbert.weightedTorusMeasure at hrep
  have hslices :=
    MeasureTheory.Measure.ae_ae_eq_curry_of_prod hrep
  filter_upwards [hslices] with x hx
  calc
    HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
          φ
          (∑ u ∈ s, c u •
            WeightedTorusHilbert.indexedMonomialLp
              K hk hφ hbounded u)
          m x =
      UnitAddTorus.mFourierCoeff
        (fun θ : TorusCharacters.AngularTorus n =>
          ∑ u ∈ s, c u *
            WeightedTorusHilbert.torusMonomial
              (WeightedTorusHilbert.integerExponent
                K hk u) (x, θ)) m := by
          unfold
            HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
            UnitAddTorus.mFourierCoeff
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hx] with θ hθ
          change
            UnitAddTorus.mFourier (-m) θ •
              (∑ u ∈ s, c u •
                WeightedTorusHilbert.indexedMonomialLp
                  K hk hφ hbounded u) (x, θ) =
            UnitAddTorus.mFourier (-m) θ •
              (∑ u ∈ s, c u *
                WeightedTorusHilbert.torusMonomial
                  (WeightedTorusHilbert.integerExponent
                    K hk u) (x, θ))
          congr 1
    _ = ∑ u ∈ s, c u *
          UnitAddTorus.mFourierCoeff
            (fun θ : TorusCharacters.AngularTorus n =>
              WeightedTorusHilbert.torusMonomial
                (WeightedTorusHilbert.integerExponent
                  K hk u) (x, θ)) m := by
          unfold UnitAddTorus.mFourierCoeff
          simp only [smul_eq_mul, Finset.mul_sum]
          have hint :
              ∀ u ∈ s,
                Integrable
                  (fun θ : TorusCharacters.AngularTorus n =>
                    UnitAddTorus.mFourier (-m) θ *
                      (c u *
                        WeightedTorusHilbert.torusMonomial
                          (WeightedTorusHilbert.integerExponent
                            K hk u) (x, θ)))
                  (volume : Measure
                    (TorusCharacters.AngularTorus n)) := by
            intro u hu
            simpa only [WeightedTorusHilbert.angularMeasure] using
              angularCharacter_mul_slice_integrable
              ((torusMonomial_angular_memLp
                (WeightedTorusHilbert.integerExponent
                  K hk u) x).const_mul (c u)) m
          rw [MeasureTheory.integral_finsetSum s hint]
          apply Finset.sum_congr rfl
          intro u hu
          calc
            (∫ θ : TorusCharacters.AngularTorus n,
              UnitAddTorus.mFourier (-m) θ *
                (c u *
                  WeightedTorusHilbert.torusMonomial
                    (WeightedTorusHilbert.integerExponent
                      K hk u) (x, θ))) =
              ∫ θ : TorusCharacters.AngularTorus n,
                c u *
                  (UnitAddTorus.mFourier (-m) θ *
                    WeightedTorusHilbert.torusMonomial
                      (WeightedTorusHilbert.integerExponent
                        K hk u) (x, θ)) := by
                    apply MeasureTheory.integral_congr_ae
                    filter_upwards [] with θ
                    ring
            _ = _ := MeasureTheory.integral_const_mul _ _
    _ = _ := by
      simp_rw [
        HolomorphicLaurentFourierCompletenessBridge.mFourierCoefficient_torusMonomial]

private def scaledExponent {n : ℕ}
    (k : ℕ) (m : Fin n → ℤ) : Space n :=
  (k : ℝ)⁻¹ • integerPoint n m

private theorem integerPoint_eq_smul_scaledExponent
    {n k : ℕ} (hk : 0 < k) (m : Fin n → ℤ) :
    integerPoint n m =
      (k : ℝ) • scaledExponent k m := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  unfold scaledExponent
  rw [smul_smul]
  simp only [ne_eq, hkreal, not_false_eq_true, mul_inv_cancel₀, one_smul]

private theorem scaledExponent_mem_monomialIndex_iff
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k) (m : Fin n → ℤ) :
    scaledExponent k m ∈
        LatticeAsymptotics.monomialIndex K k ↔
      scaledExponent k m ∈ interior K.carrier := by
  rw [LatticeAsymptotics.mem_monomialIndex_iff K hk]
  constructor
  · exact And.left
  · intro hmem
    refine ⟨hmem, ?_⟩
    intro i
    refine ⟨m i, ?_⟩
    have h :=
      congrFun (integerPoint_eq_smul_scaledExponent hk m) i
    simpa only [algebraMap_int_eq, eq_intCast, integerPoint, Pi.smul_apply, smul_eq_mul] using h

private theorem scaledExponent_integerExponent
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k) :
    scaledExponent k
        (WeightedTorusHilbert.integerExponent K hk u) =
      (u : Space n) := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  unfold scaledExponent
  rw [WeightedTorusHilbert.integerPoint_integerExponent]
  rw [smul_smul]
  simp only [ne_eq, hkreal, not_false_eq_true, inv_mul_cancel₀, one_smul]

private theorem integerExponent_eq_of_integerPoint
    {n k : ℕ} (K : CenteredBody n)
    (hk : 0 < k)
    (u : LatticeAsymptotics.monomialIndex K k)
    (m : Fin n → ℤ)
    (hm : integerPoint n m =
      (k : ℝ) • (u : Space n)) :
    WeightedTorusHilbert.integerExponent K hk u = m := by
  have hreal :
      integerPoint n
        (WeightedTorusHilbert.integerExponent K hk u) =
      integerPoint n m :=
    (WeightedTorusHilbert.integerPoint_integerExponent
      K hk u).trans hm.symm
  funext i
  have hi := congrFun hreal i
  change ((WeightedTorusHilbert.integerExponent
    K hk u i : ℤ) : ℝ) = ((m i : ℤ) : ℝ) at hi
  exact_mod_cast hi

private def laurentCoefficient {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (m : Fin n → ℤ) : ℂ :=
  UnitAddTorus.mFourierCoeff (coverRepresentative F 0) m

private theorem finiteLaurentCoefficient_sum_eq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    [Fintype (LatticeAsymptotics.monomialIndex K k)]
    (m : Fin n → ℤ) (x : Space n) :
    (∑ u : LatticeAsymptotics.monomialIndex K k,
      laurentCoefficient F
          (WeightedTorusHilbert.integerExponent K hk u) *
        (if m = WeightedTorusHilbert.integerExponent K hk u
          then WeightedTorusHilbert.radialCharacter
            (WeightedTorusHilbert.integerExponent K hk u) x
          else 0)) =
      laurentCoefficient F m *
        WeightedTorusHilbert.radialCharacter m x := by
  classical
  by_cases hinside : scaledExponent k m ∈ interior K.carrier
  · let u : LatticeAsymptotics.monomialIndex K k :=
      ⟨scaledExponent k m,
        (scaledExponent_mem_monomialIndex_iff
          K hk m).mpr hinside⟩
    have huexp :
        WeightedTorusHilbert.integerExponent K hk u = m := by
      apply integerExponent_eq_of_integerPoint K hk u m
      exact integerPoint_eq_smul_scaledExponent hk m
    calc
      (∑ v : LatticeAsymptotics.monomialIndex K k,
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent K hk v) *
          (if m = WeightedTorusHilbert.integerExponent
              K hk v
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk v) x
            else 0)) =
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent K hk u) *
          (if m = WeightedTorusHilbert.integerExponent
              K hk u
            then WeightedTorusHilbert.radialCharacter
              (WeightedTorusHilbert.integerExponent
                K hk u) x
            else 0) := by
          apply Finset.sum_eq_single u
          · intro v hv hvne
            have hne :
                m ≠ WeightedTorusHilbert.integerExponent
                  K hk v := by
              intro hmv
              apply hvne
              apply WeightedTorusHilbert.integerExponent_injective
                K hk
              exact hmv.symm.trans huexp.symm
            simp only [hne, ↓reduceIte, mul_zero]
          · simp only [Finset.mem_univ, not_true_eq_false, mul_ite, mul_zero, ite_eq_right_iff,
            mul_eq_zero,
              IsEmpty.forall_iff]
      _ = _ := by simp only [huexp, ↓reduceIte]
  · have hcoefficient :
        laurentCoefficient F m = 0 := by
      exact forbidden_coefficient_of_holomorphic_representative_eq_zero
        K hk hφ hbounded f hF hperiod hrepresentative
        m (scaledExponent k m)
        (integerPoint_eq_smul_scaledExponent hk m) hinside
    have hnone :
        ∀ u : LatticeAsymptotics.monomialIndex K k,
          m ≠ WeightedTorusHilbert.integerExponent K hk u := by
      intro u hmu
      apply hinside
      rw [hmu, scaledExponent_integerExponent K hk u]
      exact u.property.1
    simp only [hnone, ↓reduceIte, mul_zero, Finset.sum_const_zero, hcoefficient, zero_mul]

private theorem holomorphic_representative_eq_finite_laurent_sum
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {C : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction K.carrier x| ≤ C)
    (f : WeightedTorusHilbert.weightedHilbert k φ)
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℂ F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hrepresentative :
      (fun z : WeightedTorusHilbert.LogTorus n => f z)
        =ᵐ[WeightedTorusHilbert.weightedTorusMeasure k φ]
      (fun z => coverRepresentative F z.1 z.2))
    [Fintype (LatticeAsymptotics.monomialIndex K k)] :
    f =
      ∑ u : LatticeAsymptotics.monomialIndex K k,
        laurentCoefficient F
            (WeightedTorusHilbert.integerExponent
              K hk u) •
          WeightedTorusHilbert.indexedMonomialLp
            K hk hφ hbounded u := by
  classical
  let c : LatticeAsymptotics.monomialIndex K k → ℂ :=
    fun u => laurentCoefficient F
      (WeightedTorusHilbert.integerExponent K hk u)
  let g : WeightedTorusHilbert.weightedHilbert k φ :=
    ∑ u : LatticeAsymptotics.monomialIndex K k,
      c u • WeightedTorusHilbert.indexedMonomialLp
        K hk hφ hbounded u
  have hzero : f - g = 0 := by
    apply
      HolomorphicLaurentFourierCompletenessBridge.weightedHilbert_eq_zero_of_fourier
        φ (f - g)
    intro m
    have hfcoeff :
        ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
              φ f m x =
            laurentCoefficient F m *
              WeightedTorusHilbert.radialCharacter m x := by
      simpa only [laurentCoefficient] using
        angularFourierCoefficient_of_holomorphic_representative_ae
          f hF hperiod hrepresentative m
    have hgcoeff :
        ∀ᵐ x ∂(WeightedTorusHilbert.radialMeasure k φ),
          HolomorphicLaurentFourierCompletenessBridge.angularFourierCoefficient
              φ g m x =
            ∑ u : LatticeAsymptotics.monomialIndex K k,
              c u *
                (if m =
                    WeightedTorusHilbert.integerExponent
                      K hk u
                  then WeightedTorusHilbert.radialCharacter
                    (WeightedTorusHilbert.integerExponent
                      K hk u) x
                  else 0) := by
      simpa only [mul_ite, mul_zero] using
        angularFourierCoefficient_indexed_finite_sum_ae
          K hk hφ hbounded Finset.univ c m
    filter_upwards [
      angularFourierCoefficient_sub_ae φ f g m,
      hfcoeff, hgcoeff] with x hx hfx hgx
    rw [hx, hfx, hgx]
    change
      laurentCoefficient F m *
          WeightedTorusHilbert.radialCharacter m x -
        (∑ u : LatticeAsymptotics.monomialIndex K k,
          laurentCoefficient F
              (WeightedTorusHilbert.integerExponent
                K hk u) *
            (if m =
                WeightedTorusHilbert.integerExponent
                  K hk u
              then WeightedTorusHilbert.radialCharacter
                (WeightedTorusHilbert.integerExponent
                  K hk u) x
              else 0)) = 0
    rw [finiteLaurentCoefficient_sum_eq
      K hk hφ hbounded f hF hperiod hrepresentative m x]
    exact sub_self _
  change f = g
  exact sub_eq_zero.mp hzero

end JointHolomorphicLaurentFourierCompatibility

namespace EqualitySaturatingKillingPaths

open Set Function MeasureTheory Filter
open scoped BigOperators ENNReal InnerProductSpace Topology

private def barPartialCoordinate {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) (j : Fin n) : ℂ :=
  ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
    Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2

private def torusFormRepresentative {n : ℕ}
    (W : TorusCharacters.LogSpace n →
      TorusCharacters.LogSpace n)
    (z : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun i =>
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      (fun ζ => W ζ i) z.1 z.2

end EqualitySaturatingKillingPaths

namespace DolbeaultRegularity

open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

private def complexContinuousOfCoordinateCR {n : ℕ}
    (D : TorusCharacters.LogSpace n →L[ℝ] ℂ)
    (hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ))) :
    TorusCharacters.LogSpace n →L[ℂ] ℂ where
  __ := D
  map_smul' := by
    intro a x
    have hcoord (i : Fin n) (b d : ℂ) :
        D (Pi.single i (b • d)) =
          b • D (Pi.single i d) := by
      let L : ℂ →L[ℝ] ℂ := D.comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) i)
      have hL : L Complex.I = Complex.I • L 1 := by
        simpa [L, ContinuousLinearMap.comp_apply] using hI i
      have h := real_linearMap_map_smul_complex
        (ℓ := L.toLinearMap) hL b d
      simpa [L, ContinuousLinearMap.comp_apply] using h
    calc
      D (a • x) = ∑ i : Fin n,
          D (Pi.single i ((a • x) i)) := by
            simpa only [map_sum] using
              (congrArg D (Finset.univ_sum_single (a • x))).symm
      _ = ∑ i : Fin n, D (Pi.single i (a • x i)) := by rfl
      _ = ∑ i : Fin n, a • D (Pi.single i (x i)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hcoord i a (x i)
      _ = a • ∑ i : Fin n, D (Pi.single i (x i)) :=
            Finset.smul_sum.symm
      _ = a • D x := by
            rw [← map_sum, Finset.univ_sum_single]

private theorem complexContinuousOfCoordinateCR_restrictScalars {n : ℕ}
    (D : TorusCharacters.LogSpace n →L[ℝ] ℂ)
    (hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ))) :
    (complexContinuousOfCoordinateCR D hI).restrictScalars ℝ = D := by
  ext x
  rfl

private theorem differentiableAt_complex_of_barPartialCoordinate_eq_zero
    {n : ℕ} {F : TorusCharacters.LogSpace n → ℂ}
    {z : TorusCharacters.LogSpace n}
    (hF : DifferentiableAt ℝ F z)
    (hbar : ∀ j : Fin n, barPartialCoordinate F z j = 0) :
    DifferentiableAt ℂ F z := by
  let D : TorusCharacters.LogSpace n →L[ℝ] ℂ := fderiv ℝ F z
  have hI : ∀ j : Fin n,
      D (Pi.single j Complex.I) =
        Complex.I • D (Pi.single j (1 : ℂ)) := by
    intro j
    have hz := hbar j
    unfold barPartialCoordinate at hz
    have hnum :
        (fderiv ℝ F z) (Pi.single j (1 : ℂ)) +
          Complex.I * (fderiv ℝ F z)
            (Pi.single j Complex.I) = 0 := by
      rcases div_eq_zero_iff.mp hz with h | h
      · exact h
      · norm_num at h
    change
      (fderiv ℝ F z) (Pi.single j Complex.I) =
        Complex.I * (fderiv ℝ F z) (Pi.single j (1 : ℂ))
    have hsq : Complex.I ^ 2 = (-1 : ℂ) := by
      simp only [pow_two, Complex.I_mul_I]
    linear_combination -Complex.I * hnum +
      (fderiv ℝ F z) (Pi.single j Complex.I) * hsq
  apply (differentiableAt_iff_restrictScalars ℝ hF).mpr
  refine ⟨complexContinuousOfCoordinateCR D hI, ?_⟩
  exact complexContinuousOfCoordinateCR_restrictScalars D hI

private def complexRealMultiplication : ℂ →L[ℝ] ℝ →L[ℝ] ℂ :=
  (ContinuousLinearMap.lsmul ℝ ℝ).flip

private theorem complexRealMultiplication_apply (z : ℂ) (r : ℝ) :
    complexRealMultiplication z r = (r : ℂ) * z := by
  simp only [complexRealMultiplication, ContinuousLinearMap.lsmul_flip_apply,
    ContinuousLinearMap.toSpanSingleton_apply, Complex.real_smul]

private theorem translatedRealKernel_contDiff {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : ContDiff ℝ 1 κ)
    (x : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun t : TorusCharacters.LogSpace n => κ (x - t)) := by
  change ContDiff ℝ 1
    (κ ∘ (fun t : TorusCharacters.LogSpace n => x - t))
  exact hκ.comp (contDiff_const.sub contDiff_id)

private theorem translatedRealKernel_hasCompactSupport {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : HasCompactSupport κ)
    (x : TorusCharacters.LogSpace n) :
    HasCompactSupport
      (fun t : TorusCharacters.LogSpace n => κ (x - t)) := by
  simpa only [comp_def, Homeomorph.subLeft_apply] using
    hκ.comp_homeomorph (Homeomorph.subLeft x)

private theorem translatedRealKernel_fderiv {n : ℕ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hκ : ContDiff ℝ 1 κ)
    (x t v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun y : TorusCharacters.LogSpace n => κ (x - y)) t) v =
      -(fderiv ℝ κ (x - t)) v := by
  have hinner :
      HasFDerivAt
        (fun y : TorusCharacters.LogSpace n => x - y)
        (-(ContinuousLinearMap.id ℝ
          (TorusCharacters.LogSpace n))) t := by
    simpa only [hasFDerivAt_pi', Pi.sub_apply, ContinuousLinearMap.comp_neg,
      ContinuousLinearMap.comp_id, zero_sub, id_eq] using
      (hasFDerivAt_const (𝕜 := ℝ) x t).sub
        (hasFDerivAt_id (𝕜 := ℝ) t)
  have houter : DifferentiableAt ℝ κ (x - t) :=
    (hκ.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).differentiableAt
  have hchain := houter.hasFDerivAt.comp t hinner
  have heval := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℝ => D v)
      hchain.fderiv
  simpa only [comp_def, ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id,
    neg_apply] using heval

private theorem weak_barPartial_convolution_barPartial_eq_zero {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0))
    (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      x j = 0 := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := complexRealMultiplication
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have htest := hweak
    (fun t : E => κ (x - t))
    (translatedRealKernel_contDiff hκ x)
    (translatedRealKernel_hasCompactSupport hκcompact x) j
  have hnegative :
      (∫ t : E,
        -(g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)))
          ∂μ) = 0 := by
    simpa only [E, μ, v₀, v₁,
      translatedRealKernel_fderiv hκ x,
      Complex.ofReal_neg, mul_neg, ← neg_add] using htest
  have hzero :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ))
          ∂μ) = 0 := by
    simpa only [integral_neg, neg_eq_zero] using hnegative
  have hderiv := hκcompact.hasFDerivAt_convolution_right
    L hg hκ x
  have hint : Integrable
      (fun t : E =>
        (L.precompR E) (g t) (fderiv ℝ κ (x - t))) μ :=
    (hκcompact.fderiv ℝ).convolutionExists_right
      (L.precompR E) hg
        (hκ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) x
  have hfirst : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₀
    apply h.congr
    filter_upwards [] with t
    simp only [complexRealMultiplication, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.real_smul, mul_comm, L]
  have hsecond : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₁
    apply h.congr
    filter_upwards [] with t
    simp only [complexRealMultiplication, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.real_smul, mul_comm, L]
  have hsplit :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ) =
        (∫ t : E, g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ) ∂μ) +
          Complex.I *
            (∫ t : E, g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ) ∂μ) := by
    calc
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ) =
        ∫ t : E,
          g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I *
              (g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) ∂μ := by
            congr 1
            funext t
            ring
      _ = _ := by
        rw [integral_add hfirst (hsecond.const_mul Complex.I),
          integral_const_mul]
  unfold barPartialCoordinate
  rw [hderiv.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint v₀,
    ContinuousLinearMap.integral_apply hint v₁]
  change
    ((∫ t : E,
      (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ)) / 2 = 0
  have hgoal :
      (∫ t : E,
        (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ) = 0 := by
    simpa [L, complexRealMultiplication,
      Complex.real_smul, mul_comm] using
      (hsplit.symm.trans hzero)
  rw [hgoal]
  simp only [zero_div]

private theorem differentiable_complex_of_weak_barPartial_convolution {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0)) :
    Differentiable ℂ
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) := by
  intro x
  apply differentiableAt_complex_of_barPartialCoordinate_eq_zero
  · exact (hκcompact.hasFDerivAt_convolution_right
      complexRealMultiplication hg hκ x).differentiableAt
  · intro j
    exact weak_barPartial_convolution_barPartial_eq_zero
      hg hκ hκcompact hweak x j

private def complexShrinkingBump {n : ℕ} (k : ℕ) :
    ContDiffBump (0 : TorusCharacters.LogSpace n) where
  rIn := (1 / ((k : ℝ) + 1)) / 2
  rOut := 1 / ((k : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have h : 0 < 1 / ((k : ℝ) + 1) := by positivity
    exact half_lt_self h

private theorem complexShrinkingBump_rOut_tendsto {n : ℕ} :
    Tendsto (fun k : ℕ => (complexShrinkingBump (n := n) k).rOut)
      Filter.atTop (nhds 0) := by
  simpa only [complexShrinkingBump, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem complexShrinkingBump_radius_ratio {n : ℕ} (k : ℕ) :
    (complexShrinkingBump (n := n) k).rOut ≤
      2 * (complexShrinkingBump (n := n) k).rIn := by
  dsimp [complexShrinkingBump]
  ring_nf
  exact le_rfl

private theorem complex_convolution_flip {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ)
    (κ : TorusCharacters.LogSpace n → ℝ) :
    (g ⋆[complexRealMultiplication,
      (volume : Measure (TorusCharacters.LogSpace n))] κ) =
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g) := by
  exact MeasureTheory.convolution_flip
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (f := κ) (g := g) (ContinuousLinearMap.lsmul ℝ ℝ)

private theorem differentiable_complex_normalizedShrinkingConvolution
    {n : ℕ} {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : (∀ weakTest : TorusCharacters.LogSpace n → ℝ,
      ContDiff ℝ 1 weakTest → HasCompactSupport weakTest →
        ∀ weakCoordinate : Fin n,
          (∫ weakPoint, g weakPoint *
            (((fderiv ℝ weakTest weakPoint)
              (Pi.single weakCoordinate (1 : ℂ)) : ℂ) +
              Complex.I * ((fderiv ℝ weakTest weakPoint)
                (Pi.single weakCoordinate Complex.I) : ℂ))) = 0)) (k : ℕ) :
    Differentiable ℂ
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (TorusCharacters.LogSpace n))
       ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
         (volume : Measure (TorusCharacters.LogSpace n))] g) := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hhol := differentiable_complex_of_weak_barPartial_convolution
    hg hκ hκcompact hweak
  rw [complex_convolution_flip] at hhol
  exact hhol

private theorem ae_tendsto_normalized_holomorphic_mollifications {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n))) :
    ∀ᵐ z : TorusCharacters.LogSpace n
      ∂(volume : Measure (TorusCharacters.LogSpace n)),
      Tendsto (fun k : ℕ =>
        ((complexShrinkingBump (n := n) k).normed
          (volume : Measure (TorusCharacters.LogSpace n))
         ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
           (volume : Measure (TorusCharacters.LogSpace n))]
             g) z)
        atTop (nhds (g z)) := by
  exact ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (complexShrinkingBump_rOut_tendsto (n := n))
    (Filter.Eventually.of_forall
      (complexShrinkingBump_radius_ratio (n := n))) hg

end DolbeaultRegularity

namespace ComplexKillingSaturationBridge

open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths WeightedBrascampSaturation
open scoped BigOperators ENNReal InnerProductSpace Topology

private def torusScalarRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : WeightedTorusHilbert.LogTorus n) : ℂ :=
  JointHolomorphicLaurentFourierCompatibility.coverRepresentative
    F z.1 z.2

private def torusFunctionBarPartialRepresentative {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : WeightedTorusHilbert.LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 fun j =>
    JointHolomorphicLaurentFourierCompatibility.coverRepresentative
      (fun ζ => barPartialCoordinate F ζ j) z.1 z.2

private abbrev weightedTorusScalarL2 {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  WeightedTorusHilbert.weightedHilbert k φ

private abbrev functionDolbeaultGraphAmbient {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :=
  WithLp 2
    (weightedTorusScalarL2 k φ × weightedTorusFormL2 k φ)

private def torusScalarL2OfRepresentative {n k : ℕ}
    (φ : Space n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    weightedTorusScalarL2 k φ :=
  hF.toLp (torusScalarRepresentative F)

private def torusFunctionBarPartialL2 {n k : ℕ}
    (φ : Space n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hF : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ)) :
    weightedTorusFormL2 k φ :=
  hF.toLp (torusFunctionBarPartialRepresentative F)

private def smoothFunctionDolbeaultGraphSet {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :
    Set (functionDolbeaultGraphAmbient k φ) :=
  {v | ∃ F : TorusCharacters.LogSpace n → ℂ,
    ContDiff ℝ 3 F ∧
    (∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q)) ∧
    HasCompactSupport (torusScalarRepresentative F) ∧
    ∃ hF : MemLp (torusScalarRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ),
    ∃ hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (WeightedTorusHilbert.weightedTorusMeasure k φ),
      v = WithLp.toLp 2
        (torusScalarL2OfRepresentative φ F hF,
         torusFunctionBarPartialL2 φ F hD)}

private def functionDolbeaultGraph {n : ℕ} (k : ℕ)
    (φ : Space n → ℝ) :
    Submodule ℂ (functionDolbeaultGraphAmbient k φ) :=
  (Submodule.span ℂ
    (smoothFunctionDolbeaultGraphSet k φ)).topologicalClosure

end ComplexKillingSaturationBridge

namespace DolbeaultGraphDistributionBridge

open Set Function MeasureTheory Filter
open EqualitySaturatingKillingPaths DolbeaultRegularity
open scoped BigOperators ENNReal InnerProductSpace Topology Convolution

private theorem compactSupport_complexOfReal {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) :
    HasCompactSupport
      (fun z : TorusCharacters.LogSpace n => (ψ z : ℂ)) := by
  refine hψ.mono ?_
  intro z hz
  exact Complex.ofReal_ne_zero.mp hz

private theorem fderiv_complexOfReal {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Differentiable ℝ ψ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun w : TorusCharacters.LogSpace n => (ψ w : ℂ)) z) v =
      ((fderiv ℝ ψ z) v : ℂ) := by
  have h := (Complex.ofRealCLM.hasFDerivAt.comp z
    (hψ z).hasFDerivAt).fderiv
  exact congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v) h

private theorem complex_compact_integration_by_parts {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      F z * ((fderiv ℝ ψ z) v : ℂ)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(∫ z : TorusCharacters.LogSpace n,
        (fderiv ℝ F z) v * (ψ z : ℂ)
        ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun z => (ψ z : ℂ)
  have hG : ContDiff ℝ 1 G :=
    Complex.ofRealCLM.contDiff.comp hψ
  have hGcompact : HasCompactSupport G :=
    compactSupport_complexOfReal hψcompact
  have hFd : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v) :=
    (hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hGd : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ G z) v) :=
    (hG.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hdfG : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v * G z)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hFd.mul hG.continuous).integrable_of_hasCompactSupport
      hGcompact.mul_left
  have hfDG : Integrable
      (fun z : TorusCharacters.LogSpace n =>
        F z * (fderiv ℝ G z) v)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hF.continuous.mul hGd).integrable_of_hasCompactSupport
      (hGcompact.fderiv_apply ℝ v).mul_left
  have hFG : Integrable
      (fun z : TorusCharacters.LogSpace n => F z * G z)
      (volume : Measure (TorusCharacters.LogSpace n)) :=
    (hF.continuous.mul hG.continuous).integrable_of_hasCompactSupport
      hGcompact.mul_left
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (volume : Measure (TorusCharacters.LogSpace n)))
    (v := v) hdfG hfDG hFG
    (fun z _ => (hF.differentiable (by simp only [ne_eq, one_ne_zero,
      not_false_eq_true])).differentiableAt)
    (fun z _ => (hG.differentiable (by simp only [ne_eq, one_ne_zero,
      not_false_eq_true])).differentiableAt)
  simpa only [G,
    fderiv_complexOfReal (hψ.differentiable (by simp only [ne_eq, one_ne_zero,
      not_false_eq_true]))] using h

private def coverBarPartialTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) : ℂ :=
  ((fderiv ℝ ψ z) (Pi.single j (1 : ℂ)) : ℂ) +
    Complex.I *
      ((fderiv ℝ ψ z) (Pi.single j Complex.I) : ℂ)

private theorem complex_compact_barPartial_green {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hF : ContDiff ℝ 1 F)
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      F z * coverBarPartialTest ψ j z
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : TorusCharacters.LogSpace n,
          barPartialCoordinate F z j * (ψ z : ℂ)
          ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hψd₀ : Continuous
      (fun z : E => ((fderiv ℝ ψ z) v₀ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
        continuous_const)
  have hψd₁ : Continuous
      (fun z : E => ((fderiv ℝ ψ z) v₁ : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
        continuous_const)
  have hc₀ : HasCompactSupport
      (fun z : E => ((fderiv ℝ ψ z) v₀ : ℂ)) :=
    compactSupport_complexOfReal (hψcompact.fderiv_apply ℝ v₀)
  have hc₁ : HasCompactSupport
      (fun z : E => ((fderiv ℝ ψ z) v₁ : ℂ)) :=
    compactSupport_complexOfReal (hψcompact.fderiv_apply ℝ v₁)
  have hi₀ : Integrable
      (fun z : E => F z * ((fderiv ℝ ψ z) v₀ : ℂ)) μ :=
    (hF.continuous.mul hψd₀).integrable_of_hasCompactSupport
      hc₀.mul_left
  have hi₁ : Integrable
      (fun z : E => F z * ((fderiv ℝ ψ z) v₁ : ℂ)) μ :=
    (hF.continuous.mul hψd₁).integrable_of_hasCompactSupport
      hc₁.mul_left
  have hF₀ : Continuous
      (fun z : E => (fderiv ℝ F z) v₀) :=
    (hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hF₁ : Continuous
      (fun z : E => (fderiv ℝ F z) v₁) :=
    (hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hψC : Continuous (fun z : E => (ψ z : ℂ)) :=
    Complex.continuous_ofReal.comp hψ.continuous
  have hψCc : HasCompactSupport (fun z : E => (ψ z : ℂ)) :=
    compactSupport_complexOfReal hψcompact
  have hd₀ : Integrable
      (fun z : E => (fderiv ℝ F z) v₀ * (ψ z : ℂ)) μ :=
    (hF₀.mul hψC).integrable_of_hasCompactSupport hψCc.mul_left
  have hd₁ : Integrable
      (fun z : E => (fderiv ℝ F z) v₁ * (ψ z : ℂ)) μ :=
    (hF₁.mul hψC).integrable_of_hasCompactSupport hψCc.mul_left
  have hip₀ := complex_compact_integration_by_parts
    hF hψ hψcompact v₀
  have hip₁ := complex_compact_integration_by_parts
    hF hψ hψcompact v₁
  change
    (∫ z : E,
      F z *
        (((fderiv ℝ ψ z) v₀ : ℂ) +
          Complex.I * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ) =
      -(2 : ℂ) *
        (∫ z : E, barPartialCoordinate F z j * (ψ z : ℂ) ∂μ)
  have hleft :
      (∫ z : E,
        F z *
          (((fderiv ℝ ψ z) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ) =
        (∫ z : E, F z * ((fderiv ℝ ψ z) v₀ : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, F z * ((fderiv ℝ ψ z) v₁ : ℂ) ∂μ) := by
    calc
      _ = ∫ z : E,
        (F z * ((fderiv ℝ ψ z) v₀ : ℂ)) +
          Complex.I * (F z * ((fderiv ℝ ψ z) v₁ : ℂ)) ∂μ := by
            congr 1
            funext z
            ring
      _ = _ := by
        rw [integral_add hi₀ (hi₁.const_mul Complex.I),
          integral_const_mul]
  have hright :
      (∫ z : E, barPartialCoordinate F z j * (ψ z : ℂ) ∂μ) =
        ((∫ z : E, (fderiv ℝ F z) v₀ * (ψ z : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * (ψ z : ℂ) ∂μ)) / 2 := by
    unfold barPartialCoordinate
    calc
      _ = ∫ z : E,
        (((fderiv ℝ F z) v₀ * (ψ z : ℂ)) +
          Complex.I *
            ((fderiv ℝ F z) v₁ * (ψ z : ℂ))) / 2 ∂μ := by
            congr 1
            funext z
            ring
      _ = _ := by
        rw [integral_div,
          integral_add hd₀ (hd₁.const_mul Complex.I),
          integral_const_mul]
  rw [hleft, hright]
  change
    (∫ z : E, F z * ((fderiv ℝ ψ z) v₀ : ℂ) ∂μ) +
        Complex.I *
          (∫ z : E, F z * ((fderiv ℝ ψ z) v₁ : ℂ) ∂μ) =
      -(2 : ℂ) *
        (((∫ z : E, (fderiv ℝ F z) v₀ * (ψ z : ℂ) ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * (ψ z : ℂ) ∂μ)) / 2)
  rw [hip₀, hip₁]
  ring

private theorem complexReal_convolution_periodic {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (κ : TorusCharacters.LogSpace n → ℝ)
    {d : TorusCharacters.LogSpace n}
    (hperiod : Function.Periodic g d) :
    Function.Periodic
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) d := by
  intro x
  rw [MeasureTheory.convolution_def, MeasureTheory.convolution_def]
  let H : TorusCharacters.LogSpace n → ℂ :=
    fun t => complexRealMultiplication (g t) (κ (x - t))
  calc
    (∫ t : TorusCharacters.LogSpace n,
      complexRealMultiplication (g t) (κ (x + d - t))
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
      ∫ t : TorusCharacters.LogSpace n,
        H (t - d)
        ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
          congr 1
          funext t
          dsimp [H]
          rw [show g (t - d) = g t by
            have hp := hperiod (t - d)
            simpa only [sub_add_cancel] using hp.symm]
          congr 2
          abel
    _ = ∫ t : TorusCharacters.LogSpace n,
      H t ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
      simpa only [sub_eq_add_neg] using
        (integral_add_right_eq_self H (-d))
    _ = _ := rfl

private theorem normalizedShrinkingConvolution_periodic {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q))
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (TorusCharacters.LogSpace n))
       ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
         (volume : Measure (TorusCharacters.LogSpace n))] g)
      (TorusCharacters.imaginaryShift q) := by
  rw [← complex_convolution_flip]
  exact complexReal_convolution_periodic
    ((complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hperiod q)

private def coverAdjointScalarTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) : ℂ :=
  star (coverBarPartialTest ψ j z)

private def coverAdjointVectorTest {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℝ)
    (j : Fin n) (z : TorusCharacters.LogSpace n) :
    EuclideanSpace ℂ (Fin n) :=
  EuclideanSpace.single j ((2 : ℂ) * (ψ z : ℂ))

private theorem continuous_coverBarPartialTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (coverBarPartialTest ψ j) := by
  unfold coverBarPartialTest
  exact
    (Complex.continuous_ofReal.comp
      ((hψ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
        continuous_const)).add
      (continuous_const.mul
        (Complex.continuous_ofReal.comp
          ((hψ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
            continuous_const)))

private theorem compactSupport_coverBarPartialTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (coverBarPartialTest ψ j) := by
  unfold coverBarPartialTest
  exact
    (compactSupport_complexOfReal
      (hψ.fderiv_apply ℝ (Pi.single j (1 : ℂ)))).add
      (compactSupport_complexOfReal
        (hψ.fderiv_apply ℝ (Pi.single j Complex.I))).mul_left

private theorem continuous_coverAdjointScalarTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (j : Fin n) :
    Continuous (coverAdjointScalarTest ψ j) := by
  change Continuous
    (fun z => (starRingEnd ℂ) (coverBarPartialTest ψ j z))
  exact Complex.continuous_conj.comp
    (continuous_coverBarPartialTest hψ j)

private theorem compactSupport_coverAdjointScalarTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (coverAdjointScalarTest ψ j) := by
  refine (compactSupport_coverBarPartialTest hψ j).mono ?_
  intro z hz
  exact mt (fun h => by simp only [coverAdjointScalarTest, h, star_zero]) hz

private theorem continuous_coverAdjointVectorTest {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℝ}
    (hψ : Continuous ψ) (j : Fin n) :
    Continuous (coverAdjointVectorTest ψ j) := by
  classical
  have hs : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (2 : ℂ) * (ψ z : ℂ)) :=
    continuous_const.mul (Complex.continuous_ofReal.comp hψ)
  have hpi : Continuous
      (fun z : TorusCharacters.LogSpace n =>
        (Pi.single j ((2 : ℂ) * (ψ z : ℂ)) : Fin n → ℂ)) := by
    apply continuous_pi
    intro i
    by_cases hi : i = j
    · subst i
      simpa only [Pi.single_eq_same] using hs
    · simpa only [ne_eq, hi, not_false_eq_true, Pi.single_eq_of_ne] using
        (continuous_const :
          Continuous
            (fun _ : TorusCharacters.LogSpace n => (0 : ℂ)))
  change Continuous
    (fun z : TorusCharacters.LogSpace n =>
      WithLp.toLp 2
        (Pi.single j ((2 : ℂ) * (ψ z : ℂ)) : Fin n → ℂ))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp hpi

end DolbeaultGraphDistributionBridge

namespace WeightedDolbeaultBochnerIdentity

open Set MeasureTheory Filter
open EqualitySaturatingKillingPaths
open scoped BigOperators ENNReal ComplexConjugate

private def coverWeight {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℝ :=
  Real.exp (-a z)

private def coverWeightedMeasure {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ) :
    Measure (TorusCharacters.LogSpace n) :=
  (volume : Measure (TorusCharacters.LogSpace n)).withDensity
    (fun z => ENNReal.ofReal (coverWeight a z))

private theorem continuous_coverWeight {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : Continuous a) : Continuous (coverWeight a) := by
  exact Real.continuous_exp.comp ha.neg

private theorem coverWeightedMeasure_isLocallyFinite {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : Continuous a) :
    IsLocallyFiniteMeasure (coverWeightedMeasure a) := by
  unfold coverWeightedMeasure
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_coverWeight ha)

private theorem coverWeight_pos {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) :
    0 < coverWeight a z :=
  Real.exp_pos _

private theorem contDiff_coverWeight {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a) : ContDiff ℝ 1 (coverWeight a) := by
  exact ha.neg.exp

private def complexCoverWeight {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (coverWeight a z : ℂ)

private theorem contDiff_complexCoverWeight {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a) :
    ContDiff ℝ 1 (complexCoverWeight a) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_coverWeight ha)

private theorem integral_coverWeightedMeasure {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : Continuous a)
    (F : TorusCharacters.LogSpace n → ℂ) :
    (∫ z : TorusCharacters.LogSpace n, F z
      ∂(coverWeightedMeasure a)) =
    ∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z * F z
      ∂(volume : Measure (TorusCharacters.LogSpace n)) := by
  have hm : Measurable
      (fun z : TorusCharacters.LogSpace n =>
        ENNReal.ofReal (coverWeight a z)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_coverWeight ha).measurable
  have hf : ∀ᵐ z ∂(volume :
      Measure (TorusCharacters.LogSpace n)),
      ENNReal.ofReal (coverWeight a z) < ⊤ :=
    Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)
  unfold coverWeightedMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hm hf]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with z
  change
    (ENNReal.ofReal (coverWeight a z)).toReal • F z =
      (coverWeight a z : ℂ) * F z
  rw [ENNReal.toReal_ofReal (coverWeight_pos a z).le,
    Complex.real_smul]

private def holomorphicCoordinate {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) : ℂ :=
  ((fderiv ℝ F z) (Pi.single j (1 : ℂ)) -
    Complex.I * (fderiv ℝ F z) (Pi.single j Complex.I)) / 2

private def weightedRealDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (v : TorusCharacters.LogSpace n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  (fderiv ℝ F z) v - F z * ((fderiv ℝ a z) v : ℂ)

private def weightedHolomorphicDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  holomorphicCoordinate F z j -
    F z * holomorphicCoordinate (fun w => (a w : ℂ)) z j

private def weightedAntiholomorphicDerivative {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (F : TorusCharacters.LogSpace n → ℂ)
    (j : Fin n)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  barPartialCoordinate F z j -
    F z * barPartialCoordinate (fun w => (a w : ℂ)) z j

private def complexHessian {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) : ℂ :=
  barPartialCoordinate
    (fun w => holomorphicCoordinate (fun ξ => (a ξ : ℂ)) w i) z j

private theorem fderiv_complexCoverWeight {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (complexCoverWeight a) z) v =
      -((fderiv ℝ a z) v : ℂ) * complexCoverWeight a z := by
  have hd : Differentiable ℝ (coverWeight a) :=
    (contDiff_coverWeight ha).differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
  have he := DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    hd z v
  have hra := (ha.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
    z).hasFDerivAt.neg.exp.fderiv
  have hrv := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℝ => D v) hra
  change
    (fderiv ℝ (fun w => (coverWeight a w : ℂ)) z) v =
      -((fderiv ℝ a z) v : ℂ) * (coverWeight a z : ℂ)
  change (fderiv ℝ (fun w => (coverWeight a w : ℂ)) z) v =
    ((fderiv ℝ (coverWeight a) z) v : ℂ) at he
  rw [he]
  change
    (fderiv ℝ (fun w => Real.exp (-a w)) z) v =
      _ at hrv
  simp only [_root_.smul_apply,
    _root_.neg_apply, smul_eq_mul] at hrv
  change
    ((fderiv ℝ (fun w => Real.exp (-a w)) z) v : ℂ) =
      -((fderiv ℝ a z) v : ℂ) * (Real.exp (-a z) : ℂ)
  rw [hrv]
  push_cast
  simp only [Pi.neg_apply, Complex.ofReal_neg]
  ring

private theorem weighted_complex_coordinate_integration_by_parts_volume
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z * ((fderiv ℝ F z) v * G z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) =
    -(∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z *
        (F z * weightedRealDerivative a G v z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := volume
  let W : E → ℂ := fun z => G z * complexCoverWeight a z
  have hweight : ContDiff ℝ 1 (complexCoverWeight a) :=
    contDiff_complexCoverWeight ha
  have hW : ContDiff ℝ 1 W := hG.mul hweight
  have hWcompact : HasCompactSupport W := by
    change HasCompactSupport (G * complexCoverWeight a)
    exact hGcompact.mul_right
  have hFd : Continuous (fun z : E => (fderiv ℝ F z) v) :=
    (hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hWd : Continuous (fun z : E => (fderiv ℝ W z) v) :=
    (hW.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
      continuous_const
  have hdfW : Integrable
      (fun z : E => (fderiv ℝ F z) v * W z) μ :=
    (hFd.mul hW.continuous).integrable_of_hasCompactSupport
      hWcompact.mul_left
  have hfDW : Integrable
      (fun z : E => F z * (fderiv ℝ W z) v) μ :=
    (hF.continuous.mul hWd).integrable_of_hasCompactSupport
      (hWcompact.fderiv_apply ℝ v).mul_left
  have hfW : Integrable (fun z : E => F z * W z) μ :=
    (hF.continuous.mul hW.continuous).integrable_of_hasCompactSupport
      hWcompact.mul_left
  have hderiv (z : E) :
      (fderiv ℝ W z) v =
        weightedRealDerivative a G v z * complexCoverWeight a z := by
    have hg := (hG.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
      z).hasFDerivAt
    have hw := (hweight.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])
      z).hasFDerivAt
    have hp := congrArg (fun D : E →L[ℝ] ℂ => D v)
      (hg.mul hw).fderiv
    have hp' :
        (fderiv ℝ (G * complexCoverWeight a) z) v =
          G z * (fderiv ℝ (complexCoverWeight a) z) v +
            complexCoverWeight a z * (fderiv ℝ G z) v := by
      simpa only [_root_.add_apply,
        _root_.smul_apply, smul_eq_mul] using hp
    change (fderiv ℝ
      (fun y => G y * complexCoverWeight a y) z) v = _
    change
      (fderiv ℝ (G * complexCoverWeight a) z) v = _
    rw [hp', fderiv_complexCoverWeight ha z v]
    unfold weightedRealDerivative
    ring
  have hip := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := μ) (v := v) hdfW hfDW hfW
    (fun z _ => hF.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
    (fun z _ => hW.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
  have hleft :
      (∫ z : E, F z * (fderiv ℝ W z) v ∂μ) =
        ∫ z : E, complexCoverWeight a z *
          (F z * weightedRealDerivative a G v z) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    rw [hderiv z]
    ring
  have hright :
      (∫ z : E, (fderiv ℝ F z) v * W z ∂μ) =
        ∫ z : E, complexCoverWeight a z *
          ((fderiv ℝ F z) v * G z) ∂μ := by
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with z
    change (fderiv ℝ F z) v *
      (G z * complexCoverWeight a z) = _
    ring
  change
    (∫ z : E, complexCoverWeight a z *
      ((fderiv ℝ F z) v * G z) ∂μ) =
    -(∫ z : E, complexCoverWeight a z *
      (F z * weightedRealDerivative a G v z) ∂μ)
  calc
    _ = ∫ z : E, (fderiv ℝ F z) v * W z ∂μ := hright.symm
    _ = -(∫ z : E, F z * (fderiv ℝ W z) v ∂μ) := by
      linear_combination hip
    _ = _ := congrArg Neg.neg hleft

private theorem weighted_complex_coordinate_integration_by_parts
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    (∫ z : TorusCharacters.LogSpace n,
      (fderiv ℝ F z) v * G z ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * weightedRealDerivative a G v z
      ∂(coverWeightedMeasure a)) := by
  calc
    _ = ∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z * ((fderiv ℝ F z) v * G z)
      ∂(volume : Measure (TorusCharacters.LogSpace n)) :=
        integral_coverWeightedMeasure ha.continuous _
    _ = -(∫ z : TorusCharacters.LogSpace n,
      complexCoverWeight a z *
        (F z * weightedRealDerivative a G v z)
      ∂(volume : Measure (TorusCharacters.LogSpace n))) :=
        weighted_complex_coordinate_integration_by_parts_volume
          ha hF hG hGcompact v
    _ = _ := congrArg Neg.neg
      (integral_coverWeightedMeasure ha.continuous _).symm

private theorem fderiv_potential_complex {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => (a w : ℂ)) z) v =
      ((fderiv ℝ a z) v : ℂ) :=
  DolbeaultGraphDistributionBridge.fderiv_complexOfReal
    (ha.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) z v

private theorem weightedAntiholomorphicDerivative_eq_real {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedAntiholomorphicDerivative a F j z =
      (weightedRealDerivative a F (Pi.single j (1 : ℂ)) z +
        Complex.I *
          weightedRealDerivative a F
            (Pi.single j Complex.I) z) / 2 := by
  unfold weightedAntiholomorphicDerivative weightedRealDerivative
    barPartialCoordinate
  rw [fderiv_potential_complex ha z (Pi.single j (1 : ℂ)),
    fderiv_potential_complex ha z (Pi.single j Complex.I)]
  ring

private theorem weightedHolomorphicDerivative_eq_real {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedHolomorphicDerivative a F j z =
      (weightedRealDerivative a F (Pi.single j (1 : ℂ)) z -
        Complex.I *
          weightedRealDerivative a F
            (Pi.single j Complex.I) z) / 2 := by
  unfold weightedHolomorphicDerivative weightedRealDerivative
    holomorphicCoordinate
  rw [fderiv_potential_complex ha z (Pi.single j (1 : ℂ)),
    fderiv_potential_complex ha z (Pi.single j Complex.I)]
  ring

private theorem continuous_weightedRealDerivative {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (v : TorusCharacters.LogSpace n) :
    Continuous (weightedRealDerivative a F v) := by
  unfold weightedRealDerivative
  exact ((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
    continuous_const).sub
      (hF.continuous.mul
        (Complex.continuous_ofReal.comp
          ((ha.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
            continuous_const)))

private theorem compactSupport_weightedRealDerivative {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : HasCompactSupport F)
    (v : TorusCharacters.LogSpace n) :
    HasCompactSupport (weightedRealDerivative a F v) := by
  unfold weightedRealDerivative
  exact (hF.fderiv_apply ℝ v).sub hF.mul_right

private theorem integrable_fderiv_mul_coverWeightedMeasure {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v * G z)
      (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha.continuous
  apply (((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
    continuous_const).mul hG.continuous).integrable_of_hasCompactSupport
  exact hGcompact.mul_left

private theorem integrable_mul_weightedRealDerivative_coverWeightedMeasure
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (v : TorusCharacters.LogSpace n) :
    Integrable
      (fun z : TorusCharacters.LogSpace n =>
        F z * weightedRealDerivative a G v z)
      (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha.continuous
  exact (hF.continuous.mul
    (continuous_weightedRealDerivative ha hG v)).integrable_of_hasCompactSupport
      (compactSupport_weightedRealDerivative hGcompact v).mul_left

private theorem weighted_barPartial_integration_by_parts
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate F z j * G z
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * weightedAntiholomorphicDerivative a G j z
      ∂(coverWeightedMeasure a)) := by
  let E := TorusCharacters.LogSpace n
  let μ : Measure E := coverWeightedMeasure a
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hi₀ : Integrable (fun z : E =>
      (fderiv ℝ F z) v₀ * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v₀
  have hi₁ : Integrable (fun z : E =>
      (fderiv ℝ F z) v₁ * G z) μ :=
    integrable_fderiv_mul_coverWeightedMeasure
      ha hF hG hGcompact v₁
  have hj₀ : Integrable (fun z : E =>
      F z * weightedRealDerivative a G v₀ z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v₀
  have hj₁ : Integrable (fun z : E =>
      F z * weightedRealDerivative a G v₁ z) μ :=
    integrable_mul_weightedRealDerivative_coverWeightedMeasure
      ha hF hG hGcompact v₁
  have hb₀ := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v₀
  have hb₁ := weighted_complex_coordinate_integration_by_parts
    ha hF hG hGcompact v₁
  have hleft :
      (∫ z : E, barPartialCoordinate F z j * G z ∂μ) =
        ((∫ z : E, (fderiv ℝ F z) v₀ * G z ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * G z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        ((fderiv ℝ F z) v₀ * G z +
          Complex.I * ((fderiv ℝ F z) v₁ * G z)) / 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        unfold barPartialCoordinate
        change
          (((fderiv ℝ F z) v₀ +
            Complex.I * (fderiv ℝ F z) v₁) / 2) * G z = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hi₀
            (hi₁.const_mul Complex.I),
          MeasureTheory.integral_const_mul]
  have hright :
      (∫ z : E, F z *
          weightedAntiholomorphicDerivative a G j z ∂μ) =
        ((∫ z : E,
            F z * weightedRealDerivative a G v₀ z ∂μ) +
          Complex.I *
            (∫ z : E,
              F z * weightedRealDerivative a G v₁ z ∂μ)) / 2 := by
    calc
      _ = ∫ z : E,
        (F z * weightedRealDerivative a G v₀ z +
          Complex.I *
            (F z * weightedRealDerivative a G v₁ z)) / 2 ∂μ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with z
        rw [weightedAntiholomorphicDerivative_eq_real ha z j]
        change
          F z * ((weightedRealDerivative a G v₀ z +
            Complex.I * weightedRealDerivative a G v₁ z) / 2) = _
        ring
      _ = _ := by
        rw [MeasureTheory.integral_div,
          MeasureTheory.integral_add hj₀
            (hj₁.const_mul Complex.I),
          MeasureTheory.integral_const_mul]
  change
    (∫ z : E, barPartialCoordinate F z j * G z ∂μ) =
      -(∫ z : E,
        F z * weightedAntiholomorphicDerivative a G j z ∂μ)
  calc
    _ = ((∫ z : E, (fderiv ℝ F z) v₀ * G z ∂μ) +
          Complex.I *
            (∫ z : E, (fderiv ℝ F z) v₁ * G z ∂μ)) / 2 := hleft
    _ = -(((∫ z : E,
          F z * weightedRealDerivative a G v₀ z ∂μ) +
          Complex.I *
            (∫ z : E,
              F z * weightedRealDerivative a G v₁ z ∂μ)) / 2) := by
      rw [hb₀, hb₁]
      ring
    _ = _ := congrArg Neg.neg hright.symm

private theorem fderiv_conj {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : Differentiable ℝ F)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ (fun w => conj (F w)) z) v =
      conj ((fderiv ℝ F z) v) := by
  have h := (Complex.conjCLE.hasFDerivAt.comp z
    (hF z).hasFDerivAt).fderiv
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v) h
  change (fderiv ℝ (Complex.conjCLE ∘ F) z) v =
    conj ((fderiv ℝ F z) v)
  calc
    (fderiv ℝ (Complex.conjCLE ∘ F) z) v =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) ((fderiv ℝ F z) v) := by
      simpa only [ContinuousLinearMap.comp_apply] using hp
    _ = conj ((fderiv ℝ F z) v) := rfl

private theorem barPartial_conj_eq_conj_holomorphic {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => conj (F w)) z j =
      conj (holomorphicCoordinate F z j) := by
  unfold barPartialCoordinate holomorphicCoordinate
  rw [fderiv_conj (hF.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) z
        (Pi.single j (1 : ℂ)),
      fderiv_conj (hF.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) z
        (Pi.single j Complex.I)]
  simp only [map_div₀, map_sub, map_mul,
    Complex.conj_I, map_ofNat]
  ring

private theorem barPartial_potential_eq_conj_holomorphic {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => (a w : ℂ)) z j =
      conj (holomorphicCoordinate (fun w => (a w : ℂ)) z j) := by
  have hcomplex : ContDiff ℝ 1 (fun w => (a w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  have h := barPartial_conj_eq_conj_holomorphic hcomplex z j
  simpa only [Complex.conj_ofReal] using h

private theorem weightedAntiholomorphicDerivative_conj {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    weightedAntiholomorphicDerivative a (fun w => conj (F w)) j z =
      conj (weightedHolomorphicDerivative a F j z) := by
  unfold weightedAntiholomorphicDerivative weightedHolomorphicDerivative
  rw [barPartial_conj_eq_conj_holomorphic hF z j,
    barPartial_potential_eq_conj_holomorphic ha z j]
  simp only [map_sub, map_mul]

private theorem compactSupport_conj {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : HasCompactSupport F) :
    HasCompactSupport (fun z => conj (F z)) := by
  refine hF.mono ?_
  intro z hz
  change conj (F z) ≠ 0 at hz
  change F z ≠ 0
  intro hzero
  apply hz
  rw [hzero, map_zero]

private theorem weighted_barPartial_hermitian_integration_by_parts
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (hGcompact : HasCompactSupport G)
    (j : Fin n) :
    (∫ z : TorusCharacters.LogSpace n,
      barPartialCoordinate F z j * conj (G z)
      ∂(coverWeightedMeasure a)) =
    -(∫ z : TorusCharacters.LogSpace n,
      F z * conj (weightedHolomorphicDerivative a G j z)
      ∂(coverWeightedMeasure a)) := by
  have hGc : ContDiff ℝ 1 (fun z => conj (G z)) :=
    Complex.conjCLE.contDiff.comp hG
  have hcomp := compactSupport_conj hGcompact
  calc
    _ = -(∫ z : TorusCharacters.LogSpace n,
      F z *
        weightedAntiholomorphicDerivative
          a (fun w => conj (G w)) j z
      ∂(coverWeightedMeasure a)) :=
        weighted_barPartial_integration_by_parts ha hF hGc hcomp j
    _ = _ := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with z
      rw [weightedAntiholomorphicDerivative_conj ha hG z j]

private theorem contDiff_directional {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (v : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v) := by
  have hd : ContDiff ℝ 1
      (fun p : TorusCharacters.LogSpace n ×
          TorusCharacters.LogSpace n =>
        (fderiv ℝ F p.1) p.2) :=
    hF.contDiff_fderiv_apply (by norm_num)
  have hp : ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n => (z, v)) :=
    contDiff_id.prodMk contDiff_const
  exact hd.comp hp

private theorem fderiv_directional {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z v w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ζ : TorusCharacters.LogSpace n =>
        (fderiv ℝ F ζ) v) z) w =
      ((fderiv ℝ (fderiv ℝ F) z) w) v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiable
      (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) |>.differentiableAt
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := v))
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D w) he
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using hp

private theorem fderiv_directional_commute {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z v w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ζ : TorusCharacters.LogSpace n =>
        (fderiv ℝ F ζ) v) z) w =
    (fderiv ℝ
      (fun ζ : TorusCharacters.LogSpace n =>
        (fderiv ℝ F ζ) w) z) v := by
  rw [fderiv_directional hF z v w,
    fderiv_directional hF z w v]
  exact (hF.contDiffAt.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField,
    Std.le_refl])).eq w v

private theorem contDiff_holomorphicCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (j : Fin n) :
    ContDiff ℝ 1 (fun z => holomorphicCoordinate F z j) := by
  unfold holomorphicCoordinate
  exact ((contDiff_directional hF (Pi.single j (1 : ℂ))).sub
    (contDiff_const.mul
      (contDiff_directional hF (Pi.single j Complex.I)))).div_const 2

private theorem contDiff_barPartialCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (j : Fin n) :
    ContDiff ℝ 1 (fun z => barPartialCoordinate F z j) := by
  unfold barPartialCoordinate
  exact ((contDiff_directional hF (Pi.single j (1 : ℂ))).add
    (contDiff_const.mul
      (contDiff_directional hF (Pi.single j Complex.I)))).div_const 2

private theorem contDiff_weightedHolomorphicDerivative {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (j : Fin n) :
    ContDiff ℝ 1 (weightedHolomorphicDerivative a F j) := by
  have hac : ContDiff ℝ 2 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  unfold weightedHolomorphicDerivative
  exact (contDiff_holomorphicCoordinate hF j).sub
    ((hF.of_le (by norm_num)).mul
      (contDiff_holomorphicCoordinate hac j))

private theorem compactSupport_barPartialCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : HasCompactSupport F)
    (j : Fin n) :
    HasCompactSupport (fun z => barPartialCoordinate F z j) := by
  let v₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let v₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have hs : HasCompactSupport
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ F z) v₀ + Complex.I * (fderiv ℝ F z) v₁) := by
    exact (hF.fderiv_apply ℝ v₀).add
      ((hF.fderiv_apply ℝ v₁).mul_left)
  have hp := hs.mul_right
    (f' := fun _ : TorusCharacters.LogSpace n =>
      ((2 : ℂ)⁻¹))
  unfold barPartialCoordinate
  change HasCompactSupport
    ((fun z : TorusCharacters.LogSpace n =>
      (fderiv ℝ F z) v₀ + Complex.I * (fderiv ℝ F z) v₁) *
      fun _ : TorusCharacters.LogSpace n => (2 : ℂ)⁻¹)
  exact hp

private theorem fderiv_holomorphicCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z v : TorusCharacters.LogSpace n)
    (j : Fin n) :
    (fderiv ℝ
      (fun w => holomorphicCoordinate F w j) z) v =
      ((fderiv ℝ
        (fun w => (fderiv ℝ F w) (Pi.single j (1 : ℂ))) z) v -
        Complex.I *
          (fderiv ℝ
            (fun w =>
              (fderiv ℝ F w) (Pi.single j Complex.I)) z) v) / 2 := by
  let e₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let e₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have h₀ := (contDiff_directional hF e₀).differentiable
    (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z
  have h₁ := (contDiff_directional hF e₁).differentiable
    (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z
  have hd := (h₀.hasFDerivAt.sub
    (h₁.hasFDerivAt.const_mul Complex.I)).mul_const
      ((2 : ℂ)⁻¹)
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v)
      hd.fderiv
  simpa only [holomorphicCoordinate, e₀, e₁, div_eq_mul_inv,
    Pi.sub_apply,
    _root_.add_apply,
    _root_.sub_apply,
    _root_.smul_apply, smul_eq_mul, mul_comm] using hp

private theorem fderiv_barPartialCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z v : TorusCharacters.LogSpace n)
    (j : Fin n) :
    (fderiv ℝ
      (fun w => barPartialCoordinate F w j) z) v =
      ((fderiv ℝ
        (fun w => (fderiv ℝ F w) (Pi.single j (1 : ℂ))) z) v +
        Complex.I *
          (fderiv ℝ
            (fun w =>
              (fderiv ℝ F w) (Pi.single j Complex.I)) z) v) / 2 := by
  let e₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let e₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  have h₀ := (contDiff_directional hF e₀).differentiable
    (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z
  have h₁ := (contDiff_directional hF e₁).differentiable
    (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z
  have hd := (h₀.hasFDerivAt.add
    (h₁.hasFDerivAt.const_mul Complex.I)).mul_const
      ((2 : ℂ)⁻¹)
  have hp := congrArg
    (fun D : TorusCharacters.LogSpace n →L[ℝ] ℂ => D v)
      hd.fderiv
  simpa only [barPartialCoordinate, e₀, e₁, div_eq_mul_inv,
    Pi.add_apply,
    _root_.add_apply,
    _root_.smul_apply, smul_eq_mul, mul_comm] using hp

private theorem barPartial_holomorphic_commute {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    barPartialCoordinate
      (fun w => holomorphicCoordinate F w i) z j =
    holomorphicCoordinate
      (fun w => barPartialCoordinate F w j) z i := by
  let eᵢ₀ : TorusCharacters.LogSpace n :=
    Pi.single i (1 : ℂ)
  let eᵢ₁ : TorusCharacters.LogSpace n :=
    Pi.single i Complex.I
  let eⱼ₀ : TorusCharacters.LogSpace n :=
    Pi.single j (1 : ℂ)
  let eⱼ₁ : TorusCharacters.LogSpace n :=
    Pi.single j Complex.I
  change
    ((fderiv ℝ (fun w => holomorphicCoordinate F w i) z) eⱼ₀ +
      Complex.I *
        (fderiv ℝ (fun w => holomorphicCoordinate F w i) z) eⱼ₁) / 2 =
    ((fderiv ℝ (fun w => barPartialCoordinate F w j) z) eᵢ₀ -
      Complex.I *
        (fderiv ℝ (fun w => barPartialCoordinate F w j) z) eᵢ₁) / 2
  rw [fderiv_holomorphicCoordinate hF z eⱼ₀ i,
    fderiv_holomorphicCoordinate hF z eⱼ₁ i,
    fderiv_barPartialCoordinate hF z eᵢ₀ j,
    fderiv_barPartialCoordinate hF z eᵢ₁ j]
  rw [fderiv_directional_commute hF z eᵢ₀ eⱼ₀,
    fderiv_directional_commute hF z eᵢ₁ eⱼ₀,
    fderiv_directional_commute hF z eᵢ₀ eⱼ₁,
    fderiv_directional_commute hF z eᵢ₁ eⱼ₁]
  ring

private theorem barPartial_mul {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => F w * G w) z j =
      barPartialCoordinate F z j * G z +
        F z * barPartialCoordinate G z j := by
  have hp := fderiv_mul
    (hF.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
    (hG.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
  unfold barPartialCoordinate
  change
    ((fderiv ℝ (F * G) z) (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ (F * G) z) (Pi.single j Complex.I)) / 2 = _
  rw [hp]
  simp only [_root_.add_apply,
    _root_.smul_apply, smul_eq_mul]
  ring

private theorem barPartial_sub {n : ℕ}
    {F G : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (hG : ContDiff ℝ 1 G)
    (z : TorusCharacters.LogSpace n)
    (j : Fin n) :
    barPartialCoordinate (fun w => F w - G w) z j =
      barPartialCoordinate F z j -
        barPartialCoordinate G z j := by
  have hp := fderiv_sub
    (hF.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
    (hG.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)
  unfold barPartialCoordinate
  change
    ((fderiv ℝ (F - G) z) (Pi.single j (1 : ℂ)) +
      Complex.I *
        (fderiv ℝ (F - G) z) (Pi.single j Complex.I)) / 2 = _
  rw [hp]
  simp only [_root_.sub_apply]
  ring

private theorem barPartial_weightedHolomorphicDerivative_commutator
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 2 a)
    (hF : ContDiff ℝ 2 F)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    barPartialCoordinate
      (fun w => weightedHolomorphicDerivative a F i w) z j =
      weightedHolomorphicDerivative a
        (fun w => barPartialCoordinate F w j) i z -
          F z * complexHessian a z i j := by
  have haone : ContDiff ℝ 1 a := ha.of_le (by norm_num)
  have hfone : ContDiff ℝ 1 F := hF.of_le (by norm_num)
  have hac : ContDiff ℝ 2 (fun w => (a w : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  have hholF := contDiff_holomorphicCoordinate hF i
  have hholA := contDiff_holomorphicCoordinate hac i
  change
    barPartialCoordinate
      (fun w => holomorphicCoordinate F w i -
        F w * holomorphicCoordinate (fun ξ => (a ξ : ℂ)) w i)
      z j = _
  rw [barPartial_sub hholF (hfone.mul hholA) z j,
    barPartial_mul hfone hholA z j,
    barPartial_holomorphic_commute hF z i j]
  unfold weightedHolomorphicDerivative complexHessian
  ring

private theorem continuous_barPartialCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (fun z => barPartialCoordinate F z j) := by
  unfold barPartialCoordinate
  exact (((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
    continuous_const).add
    (continuous_const.mul
      ((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
        continuous_const))).div_const 2

private theorem continuous_holomorphicCoordinate {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (fun z => holomorphicCoordinate F z j) := by
  unfold holomorphicCoordinate
  exact (((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
    continuous_const).sub
    (continuous_const.mul
      ((hF.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])).clm_apply
        continuous_const))).div_const 2

private theorem continuous_weightedHolomorphicDerivative {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : ContDiff ℝ 1 a)
    (hF : ContDiff ℝ 1 F)
    (j : Fin n) :
    Continuous (weightedHolomorphicDerivative a F j) := by
  have hac : ContDiff ℝ 1 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  unfold weightedHolomorphicDerivative
  exact (continuous_holomorphicCoordinate hF j).sub
    (hF.continuous.mul (continuous_holomorphicCoordinate hac j))

private theorem continuous_complexHessian {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (i j : Fin n) :
    Continuous (fun z => complexHessian a z i j) := by
  have hac : ContDiff ℝ 2 (fun z => (a z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ha
  exact continuous_barPartialCoordinate
    (contDiff_holomorphicCoordinate hac i) j

private theorem integrable_of_continuous_compact_cover {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (ha : Continuous a)
    (hF : Continuous F)
    (hFcompact : HasCompactSupport F) :
    Integrable F (coverWeightedMeasure a) := by
  let : IsLocallyFiniteMeasure (coverWeightedMeasure a) :=
    coverWeightedMeasure_isLocallyFinite ha
  exact hF.integrable_of_hasCompactSupport hFcompact

private def coverFormAdjoint {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ∑ i : Fin n,
    weightedHolomorphicDerivative a (fun w => W w i) i z

private theorem antisymmetric_matrix_energy_add_cross {n : ℕ}
    (A : Fin n → Fin n → ℂ) :
    (∑ i : Fin n, ∑ j : Fin n,
      (A i j - A j i) * conj (A i j - A j i)) / 2 +
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j) := by
  have hdiag :
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A j i)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j) := by
    rw [Finset.sum_comm]
  have hcross :
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A i j)) =
      ∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i) := by
    rw [Finset.sum_comm]
  have hexpand :
      (∑ i : Fin n, ∑ j : Fin n,
        (A i j - A j i) * conj (A i j - A j i)) =
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A i j)) -
      (∑ i : Fin n, ∑ j : Fin n,
        A i j * conj (A j i)) -
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A i j)) +
      (∑ i : Fin n, ∑ j : Fin n,
        A j i * conj (A j i)) := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n,
        (A i j * conj (A i j) -
          A i j * conj (A j i) -
          A j i * conj (A i j) +
          A j i * conj (A j i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        simp only [map_sub]
        ring
      _ = _ := by
        simp_rw [Finset.sum_add_distrib,
          Finset.sum_sub_distrib]
  rw [hexpand, hdiag, hcross]
  ring

end WeightedDolbeaultBochnerIdentity

namespace SchurConvexity

open Set Matrix
open WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder

private def complexSchurColumn {n : ℕ} (b : Fin n → ℂ) :
    Matrix (Fin n) (Fin 1) ℂ :=
  fun i _ => b i

private def complexSchurScalar (c : ℝ) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (c : ℂ)

private theorem complexSchurColumn_mul_apply {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) :
    ((complexSchurColumn b)ᴴ * A * complexSchurColumn b)
      (0 : Fin 1) (0 : Fin 1) =
      star b ⬝ᵥ (A *ᵥ b) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    complexSchurColumn, Matrix.mulVec, dotProduct,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private def complexSchurEnergyDensity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) : ℝ :=
  (star b ⬝ᵥ (A⁻¹ *ᵥ b)).re

private theorem complexSchurEnergyDensity_nonneg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef) (b : Fin n → ℂ) :
    0 ≤ complexSchurEnergyDensity A b := by
  exact hA.inv.posSemidef.re_dotProduct_nonneg b

private theorem complex_schur_energy_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) (c : ℝ)
    (hblock :
      (Matrix.fromBlocks A (complexSchurColumn b)
        (complexSchurColumn b)ᴴ
        (complexSchurScalar c)).PosSemidef) :
    complexSchurEnergyDensity A b ≤ c := by
  let : Invertible A := hA.isUnit.invertible
  have hschur :=
    (Matrix.PosDef.fromBlocks₁₁
      (complexSchurColumn b) (complexSchurScalar c) hA).mp hblock
  have hdiag := hschur.diag_nonneg (i := (0 : Fin 1))
  have hreal := (Complex.nonneg_iff.mp hdiag).1
  change
    0 ≤ (c : ℂ).re -
      (((complexSchurColumn b)ᴴ * A⁻¹ * complexSchurColumn b)
        (0 : Fin 1) (0 : Fin 1)).re at hreal
  rw [complexSchurColumn_mul_apply] at hreal
  change 0 ≤ c - complexSchurEnergyDensity A b at hreal
  linarith

private def sourceCoverComplexHessian {n : ℕ}
    (a : TorusCharacters.LogSpace n → ℝ)
    (z : TorusCharacters.LogSpace n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => complexHessian a z i j

private def sourceCoverAntiholomorphicGradient {n : ℕ}
    (f : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  fun i => EqualitySaturatingKillingPaths.barPartialCoordinate
    f z i

end SchurConvexity

namespace JetEnvelopeRightDerivative

open Set Filter MeasureTheory Module
open scoped BigOperators Topology ENNReal InnerProductSpace

private def sourceTorusCoverPoint {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    TorusCharacters.LogSpace n :=
  JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
    q.1 (fun i => (AddCircle.equivIoc 1 0 (q.2 i)).1)

private theorem realLogCoordinate_sourceTorusCoverPoint {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    BergmanDiagonalBasisIndependence.realLogCoordinate
        (sourceTorusCoverPoint q) = q.1 := by
  funext i
  simp only [BergmanDiagonalBasisIndependence.realLogCoordinate, sourceTorusCoverPoint,
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint, Complex.add_re,
    Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.ofReal_im, mul_zero, sub_zero, Complex.I_re, Complex.mul_im, zero_mul, add_zero,
    Complex.I_im, mul_one, sub_self]
  ring

private theorem sourceTorusFundamentalAngularRepresentative {n : ℕ}
    (q : WeightedTorusHilbert.LogTorus n) :
    (fun i : Fin n =>
      (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : UnitAddCircle)) =
      q.2 := by
  funext i
  exact (AddCircle.equivIoc 1 0).symm_apply_apply (q.2 i)

private theorem torusCharacter_sourceTorusCoverPoint {n : ℕ}
    (m : Fin n → ℤ)
    (q : WeightedTorusHilbert.LogTorus n) :
    TorusCharacters.torusCharacter m
        (sourceTorusCoverPoint q) =
      WeightedTorusHilbert.torusMonomial m q := by
  let t : Space n :=
    fun i => (AddCircle.equivIoc 1 0 (q.2 i)).1
  have ht : (fun i : Fin n => (t i : UnitAddCircle)) = q.2 :=
    sourceTorusFundamentalAngularRepresentative q
  have hneg :
      TorusCharacters.characterExponent (-m)
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            0 t) =
        -TorusCharacters.characterExponent m
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            0 t) := by
    simp only [TorusCharacters.characterExponent, Pi.neg_apply, Int.cast_neg, neg_mul,
      Finset.sum_neg_distrib]
  have hfourier :
      UnitAddTorus.mFourier m q.2 =
        Complex.exp
          (TorusCharacters.characterExponent m
            (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
              0 t)) := by
    rw [← ht]
    have h :=
      JointHolomorphicLaurentFourierCompatibility.mFourier_neg_coe_eq_exp
        (-m) t
    simpa only [neg_neg, hneg] using h
  unfold WeightedTorusHilbert.torusMonomial
    WeightedTorusHilbert.radialCharacter
    TorusCharacters.torusCharacter
  change
    Complex.exp
        (TorusCharacters.characterExponent m
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            q.1 t)) =
      Complex.exp
          (TorusCharacters.characterExponent m
            (TorusCharacters.realLogSlice q.1)) *
        UnitAddTorus.mFourier m q.2
  rw [JointHolomorphicLaurentFourierCompatibility.characterExponent_logarithmicPoint,
    Complex.exp_add, hfourier]

private def sourcePositiveJointTimePoint {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.PositiveJointLogSpace n := by
  refine ⟨(z, (Real.exp (t / 2) : ℂ)), ?_⟩
  rw [Complex.normSq_ofReal]
  have h : (1 : ℝ) < Real.exp (t / 2) := by
    simpa only [Real.one_lt_exp_iff, Nat.ofNat_pos, div_pos_iff_of_pos_right,
      Real.exp_zero] using (Real.exp_lt_exp.mpr (half_pos ht))
  nlinarith

private theorem jointLogTime_sourcePositiveJointTimePoint {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.jointLogTime
      (sourcePositiveJointTimePoint z t ht) = t := by
  unfold ActualJetUpperEnvelope.jointLogTime
    sourcePositiveJointTimePoint
  rw [Complex.normSq_ofReal, ← Real.exp_add]
  have hadd : t / 2 + t / 2 = t := by ring
  rw [hadd, Real.log_exp]

private theorem jointRealCoordinate_sourcePositiveJointTimePoint
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t) :
    ActualJetUpperEnvelope.jointRealCoordinate
      (sourcePositiveJointTimePoint z t ht) =
      BergmanDiagonalBasisIndependence.realLogCoordinate z := by
  rfl

private theorem measurable_sourceTorusCoverPoint {n : ℕ} :
    Measurable
      (sourceTorusCoverPoint (n := n)) := by
  apply measurable_pi_lambda
  intro i
  have hangle :
      Measurable
        (fun q : WeightedTorusHilbert.LogTorus n =>
          ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ)) :=
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIoc 1 0).measurable.comp
        ((measurable_pi_apply i).comp measurable_snd))
  change Measurable
    (fun q : WeightedTorusHilbert.LogTorus n =>
      (q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ)) )
  fun_prop

end JetEnvelopeRightDerivative

namespace JetEnvelopeLocalGrowth

open Set Filter MeasureTheory Module Metric Asymptotics
open ActualJetUpperEnvelope JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace

universe u v

private theorem isLittleO_norm_pow_of_iteratedFDeriv_zero
    {E : Type u} {F : Type (max u v)}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (f : E → F) (hf : ContDiff ℂ ⊤ f)
    (p : E) (j : ℕ)
    (hzero : ∀ i : ℕ, i ≤ j → iteratedFDeriv ℂ i f p = 0) :
    (fun z : E => f z - f p) =o[𝓝 p]
      (fun z : E => ‖z - p‖ ^ j) := by
  induction j generalizing F f with
  | zero =>
      have hc : ContinuousAt f p := hf.continuous.continuousAt
      simpa only [pow_zero, isLittleO_one_iff, sub_self] using
        hc.tendsto.sub_const (f p)
  | succ j ih =>
      have hdf : ContDiff ℂ ⊤ (fderiv ℂ f) :=
        hf.fderiv_right (by simp only [WithTop.top_add, Std.le_refl])
      have hdzero :
          ∀ i : ℕ, i ≤ j →
            iteratedFDeriv ℂ i (fderiv ℂ f) p = 0 := by
        intro i hi
        apply norm_eq_zero.mp
        rw [norm_iteratedFDeriv_fderiv,
          hzero (i + 1) (by omega), norm_zero]
      have hdp : fderiv ℂ f p = 0 := by
        have h := hdzero 0 (Nat.zero_le j)
        apply norm_eq_zero.mp
        have hn := congrArg norm h
        simpa only [norm_eq_zero, norm_iteratedFDeriv_zero, norm_zero] using hn
      have hsmall :
          (fderiv ℂ f) =o[𝓝 p]
            (fun z : E => ‖z - p‖ ^ j) := by
        simpa only [hdp, sub_zero] using ih (fderiv ℂ f) hdf hdzero
      have hmean := (convex_univ : Convex ℝ (Set.univ : Set E))
        |>.isLittleO_pow_succ (Set.mem_univ p)
          (fun z _ =>
            (hf.differentiable (by simp only [ne_eq, WithTop.top_ne_zero,
              not_false_eq_true])).differentiableAt.hasFDerivAt
              |>.hasFDerivWithinAt)
          (by simpa only [nhdsWithin_univ] using hsmall)
      simpa only [nhdsWithin_univ] using hmean

private theorem sourceLocalSchwarzRatio_sq_mul_exp_le_one
    {d R t : ℝ} (hd : 0 ≤ d) (hR : 0 < R)
    (hshrinking : d < R * Real.exp (-t / 2)) :
    (d / R) ^ 2 * Real.exp t ≤ 1 := by
  have hratio : d / R < Real.exp (-t / 2) := by
    apply (div_lt_iff₀ hR).mpr
    simpa only [mul_comm] using hshrinking
  have hq : 0 ≤ d / R := div_nonneg hd hR.le
  have hsq : (d / R) ^ 2 ≤ Real.exp (-t) := by
    calc
      (d / R) ^ 2 ≤ Real.exp (-t / 2) ^ 2 :=
        (sq_le_sq₀ hq (Real.exp_pos _).le).mpr hratio.le
      _ = Real.exp (-t) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    (d / R) ^ 2 * Real.exp t ≤
        Real.exp (-t) * Real.exp t :=
      mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le
    _ = 1 := by
      rw [← Real.exp_add]
      simp only [neg_add_cancel, Real.exp_zero]

private def sourceLocalPolynomialConstant {n : ℕ}
    (K : CenteredBody n) : ℝ :=
  GlobalBergmanKernelBound.globalKernelPolynomialConstant K *
    (normalizedVolume K.carrier + 1)

private theorem sourceLocalPolynomialConstant_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < sourceLocalPolynomialConstant K := by
  unfold sourceLocalPolynomialConstant
  exact mul_pos
    (GlobalBergmanKernelBound.globalKernelPolynomialConstant_pos K)
    (by have hv := K.volume_pos; linarith)

private def sourceLocalKernelLogError {n : ℕ}
    (K : CenteredBody n) (k : ℕ) : ℝ :=
  (Real.log (sourceLocalPolynomialConstant K) +
    3 * (n : ℝ) * Real.log (k : ℝ)) / (k : ℝ)

private theorem tendsto_sourceLocalKernelLogError
    {n : ℕ} (K : CenteredBody n) :
    Tendsto (sourceLocalKernelLogError K) atTop (𝓝 0) := by
  have hnat : Tendsto (fun k : ℕ => (k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hconst : Tendsto
      (fun k : ℕ => Real.log (sourceLocalPolynomialConstant K) /
        (k : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hnat
  have hlog : Tendsto
      (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ))
      atTop (𝓝 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop
        1 0 1 one_ne_zero).comp hnat
    exact h.congr' (Filter.Eventually.of_forall fun _ => by simp only [pow_one, one_mul,
      add_zero, Function.comp_apply])
  have hsum := hconst.add (hlog.const_mul (3 * (n : ℝ)))
  have heq : sourceLocalKernelLogError K =
      (fun k : ℕ =>
        Real.log (sourceLocalPolynomialConstant K) / (k : ℝ) +
          3 * (n : ℝ) * (Real.log (k : ℝ) / (k : ℝ))) := by
    funext k
    unfold sourceLocalKernelLogError
    rw [add_div]
    ring
  rw [heq]
  simpa only [mul_zero, add_zero] using hsum

private def sourceLocalJointRegion {n : ℕ}
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    Set (PositiveJointLogSpace n) :=
  {w | dist w.val.1 p <
    R * Real.exp (-jointLogTime w / 2)}

private theorem isOpen_sourceLocalJointRegion {n : ℕ}
    (p : TorusCharacters.LogSpace n) (R : ℝ) :
    IsOpen (sourceLocalJointRegion p R) := by
  unfold sourceLocalJointRegion
  have htime : Continuous (jointLogTime (n := n)) :=
    continuous_jointLogTime n
  exact isOpen_lt (by fun_prop) (by fun_prop)

private theorem sourceUnitAngularHaar_eq_volume :
    (AddCircle.haarAddCircle : Measure UnitAddCircle) =
      (volume : Measure UnitAddCircle) := by
  simpa only [ENNReal.ofReal_one, one_smul] using
    (AddCircle.volume_eq_smul_haarAddCircle (T := 1)).symm

private def sourcePositiveAngularArc (δ : ℝ) : Set UnitAddCircle :=
  {θ | ((AddCircle.equivIoc 1 0 θ).1 : ℝ) < δ}

private theorem measurableSet_sourcePositiveAngularArc (δ : ℝ) :
    MeasurableSet (sourcePositiveAngularArc δ) := by
  have hrepr : Measurable
      (fun θ : UnitAddCircle =>
        ((AddCircle.equivIoc 1 0 θ).1 : ℝ)) :=
    measurable_subtype_coe.comp
      (AddCircle.measurableEquivIoc 1 0).measurable
  exact hrepr measurableSet_Iio

private theorem sourcePositiveAngularArc_haarMeasure
    {δ : ℝ} (hδ : δ ≤ 1) :
    AddCircle.haarAddCircle (sourcePositiveAngularArc δ) =
      ENNReal.ofReal δ := by
  rw [sourceUnitAngularHaar_eq_volume]
  rw [AddCircle.add_projection_respects_measure 1 0
    (measurableSet_sourcePositiveAngularArc δ)]
  have hset :
      (QuotientAddGroup.mk ⁻¹' sourcePositiveAngularArc δ ∩
        Set.Ioc (0 : ℝ) (0 + 1)) = Set.Ioo (0 : ℝ) δ := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨harc, hinter⟩
      have hrepr := AddCircle.equivIoc_coe_eq hinter
      change
        ((AddCircle.equivIoc 1 0 (x : UnitAddCircle)).1 : ℝ) < δ
        at harc
      rw [hrepr] at harc
      exact ⟨hinter.1, harc⟩
    · intro hx
      have hinter : x ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
        constructor
        · exact hx.1
        · linarith [hx.2]
      refine ⟨?_, hinter⟩
      change
        ((AddCircle.equivIoc 1 0 (x : UnitAddCircle)).1 : ℝ) < δ
      rw [AddCircle.equivIoc_coe_eq hinter]
      exact hx.2
  rw [hset, Real.volume_Ioo]
  simp only [sub_zero]

private def sourceLocalRadialBox (n : ℕ) (δ : ℝ) :
    Set (Space n) :=
  Set.univ.pi fun _ : Fin n => Set.Ioo (-δ) δ

private def sourceLocalAngularBox (n : ℕ) (δ : ℝ) :
    Set (TorusCharacters.AngularTorus n) :=
  Set.univ.pi fun _ : Fin n => sourcePositiveAngularArc δ

private def sourceLocalTorusBox (n : ℕ) (δ : ℝ) :
    Set (WeightedTorusHilbert.LogTorus n) :=
  sourceLocalRadialBox n δ ×ˢ sourceLocalAngularBox n δ

private theorem measurableSet_sourceLocalRadialBox (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalRadialBox n δ) := by
  exact MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_Ioo)

private theorem measurableSet_sourceLocalAngularBox (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalAngularBox n δ) := by
  exact MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_sourcePositiveAngularArc δ)

private theorem measurableSet_sourceLocalTorusBox (n : ℕ) (δ : ℝ) :
    MeasurableSet (sourceLocalTorusBox n δ) :=
  (measurableSet_sourceLocalRadialBox n δ).prod
    (measurableSet_sourceLocalAngularBox n δ)

private theorem sourceLocalRadialBox_volume (n : ℕ) (δ : ℝ) :
    (volume : Measure (Space n))
      (sourceLocalRadialBox n δ) =
        (ENNReal.ofReal (2 * δ)) ^ n := by
  unfold sourceLocalRadialBox
  rw [Real.volume_pi_Ioo]
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, two_mul]

private theorem sourceLocalAngularBox_volume
    (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    WeightedTorusHilbert.angularMeasure n
      (sourceLocalAngularBox n δ) =
        (ENNReal.ofReal δ) ^ n := by
  change
    (Measure.pi (fun _ : Fin n => AddCircle.haarAddCircle))
      (Set.univ.pi fun _ : Fin n => sourcePositiveAngularArc δ) = _
  rw [Measure.pi_pi]
  simp only [sourcePositiveAngularArc_haarMeasure hδ, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

private theorem sourceLocalTorusBox_volume
    (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    sourceTorusBaseMeasure n (sourceLocalTorusBox n δ) =
      (ENNReal.ofReal (2 * δ)) ^ n *
        (ENNReal.ofReal δ) ^ n := by
  unfold sourceTorusBaseMeasure sourceLocalTorusBox
  rw [Measure.prod_prod,
    sourceLocalRadialBox_volume,
    sourceLocalAngularBox_volume n hδ]

private def sourceLocalBoxScale (R : ℝ) : ℝ :=
  min 1 (R / (1 + 4 * Real.pi))

private def sourceLocalBoxRadius (R t : ℝ) : ℝ :=
  sourceLocalBoxScale R * Real.exp (-t / 2)

private theorem sourceLocalBoxScale_pos {R : ℝ} (hR : 0 < R) :
    0 < sourceLocalBoxScale R := by
  unfold sourceLocalBoxScale
  exact lt_min (by norm_num)
    (div_pos hR (by positivity))

private theorem sourceLocalBoxRadius_pos {R : ℝ} (hR : 0 < R)
    (t : ℝ) :
    0 < sourceLocalBoxRadius R t := by
  unfold sourceLocalBoxRadius
  exact mul_pos (sourceLocalBoxScale_pos hR) (Real.exp_pos _)

private theorem sourceLocalBoxRadius_le_one {R t : ℝ}
    (hR : 0 < R) (ht : 0 ≤ t) :
    sourceLocalBoxRadius R t ≤ 1 := by
  unfold sourceLocalBoxRadius
  calc
    sourceLocalBoxScale R * Real.exp (-t / 2) ≤
      sourceLocalBoxScale R * 1 := by
        gcongr
        · exact (sourceLocalBoxScale_pos hR).le
        · exact Real.exp_le_one_iff.mpr (by linarith)
    _ ≤ 1 := by
      simp only [sourceLocalBoxScale, mul_one, inf_le_left]

private theorem sourceTorusCoverPoint_mem_shrinkingBall_of_mem_box
    {n : ℕ} {R t : ℝ}
    (hR : 0 < R)
    (q : WeightedTorusHilbert.LogTorus n)
    (hq : q ∈ sourceLocalTorusBox n (sourceLocalBoxRadius R t)) :
    dist (sourceTorusCoverPoint q)
        (0 : TorusCharacters.LogSpace n) <
      R * Real.exp (-t / 2) := by
  have he : 0 < Real.exp (-t / 2) := Real.exp_pos _
  have htarget : 0 < R * Real.exp (-t / 2) :=
    mul_pos hR he
  apply (dist_pi_lt_iff htarget).mpr
  intro i
  have hx :
      -sourceLocalBoxRadius R t < q.1 i ∧
        q.1 i < sourceLocalBoxRadius R t :=
    hq.1 i (Set.mem_univ i)
  have hangle :
      ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) <
        sourceLocalBoxRadius R t :=
    hq.2 i (Set.mem_univ i)
  have hanglepos :
      0 < ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) :=
    (AddCircle.equivIoc 1 0 (q.2 i)).property.1
  have habsx : |q.1 i| < sourceLocalBoxRadius R t :=
    abs_lt.mpr hx
  have hpi : 0 < 2 * Real.pi := by positivity
  have htriangle :
      ‖((q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ))‖ ≤
        |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) := by
    calc
      ‖((q.1 i : ℂ) / 2 +
        (2 * (Real.pi : ℂ) * Complex.I) *
          (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ))‖ ≤
        ‖(q.1 i : ℂ) / 2‖ +
          ‖(2 * (Real.pi : ℂ) * Complex.I) *
            (((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) : ℂ)‖ :=
        norm_add_le _ _
      _ = |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) := by
        simp only [Complex.norm_div, Complex.norm_real, Real.norm_eq_abs, Complex.norm_ofNat,
          Complex.norm_mul, abs_of_pos Real.pi_pos, Complex.norm_I, mul_one, abs_of_pos hanglepos]
  have hstrict :
      |q.1 i| / 2 +
          (2 * Real.pi) *
            ((AddCircle.equivIoc 1 0 (q.2 i)).1 : ℝ) <
        sourceLocalBoxRadius R t / 2 +
          (2 * Real.pi) * sourceLocalBoxRadius R t :=
    add_lt_add
      (div_lt_div_of_pos_right habsx (by norm_num))
      (mul_lt_mul_of_pos_left hangle hpi)
  have hden : 0 < 1 + 4 * Real.pi := by positivity
  have hscale :
      sourceLocalBoxScale R * (1 + 4 * Real.pi) ≤ R := by
    apply (le_div_iff₀ hden).mp
    exact min_le_right _ _
  have hradius :
      sourceLocalBoxRadius R t / 2 +
          (2 * Real.pi) * sourceLocalBoxRadius R t <
        R * Real.exp (-t / 2) := by
    unfold sourceLocalBoxRadius
    calc
      sourceLocalBoxScale R * Real.exp (-t / 2) / 2 +
          (2 * Real.pi) *
            (sourceLocalBoxScale R * Real.exp (-t / 2)) =
        ((sourceLocalBoxScale R * (1 + 4 * Real.pi)) / 2) *
          Real.exp (-t / 2) := by ring
      _ ≤ (R / 2) * Real.exp (-t / 2) := by
        gcongr
      _ < R * Real.exp (-t / 2) := by
        nlinarith [mul_pos hR he]
  simpa only [sourceTorusCoverPoint, JointHolomorphicLaurentFourierCompatibility.logarithmicPoint,
    Pi.zero_apply, dist_zero_right, gt_iff_lt] using
      lt_of_le_of_lt htriangle (hstrict.trans hradius)

private theorem sourceLocalTorusBox_realVolume
    (n : ℕ) {δ : ℝ} (hδnonneg : 0 ≤ δ) (hδ : δ ≤ 1) :
    (sourceTorusBaseMeasure n).real (sourceLocalTorusBox n δ) =
      (2 * δ) ^ n * δ ^ n := by
  change
    (sourceTorusBaseMeasure n (sourceLocalTorusBox n δ)).toReal = _
  rw [sourceLocalTorusBox_volume n hδ,
    ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * δ),
    ENNReal.toReal_ofReal hδnonneg]

private def sourceLocalBallVolumeConstant (n : ℕ) (R : ℝ) : ℝ :=
  (2 : ℝ) ^ n * sourceLocalBoxScale R ^ (2 * n)

private theorem sourceLocalBallVolumeConstant_pos
    (n : ℕ) {R : ℝ} (hR : 0 < R) :
    0 < sourceLocalBallVolumeConstant n R := by
  unfold sourceLocalBallVolumeConstant
  exact mul_pos (pow_pos (by norm_num) n)
    (pow_pos (sourceLocalBoxScale_pos hR) (2 * n))

private theorem sourceLocalTorusBox_realVolume_at_time
    (n : ℕ) {R t : ℝ}
    (hR : 0 < R) (ht : 0 ≤ t) :
    (sourceTorusBaseMeasure n).real
      (sourceLocalTorusBox n (sourceLocalBoxRadius R t)) =
        sourceLocalBallVolumeConstant n R *
          Real.exp (-(n : ℝ) * t) := by
  rw [sourceLocalTorusBox_realVolume n
    (sourceLocalBoxRadius_pos hR t).le
    (sourceLocalBoxRadius_le_one hR ht)]
  unfold sourceLocalBoxRadius sourceLocalBallVolumeConstant
  have hexp :
      Real.exp (-t / 2) ^ (2 * n) =
        Real.exp (-(n : ℝ) * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  calc
    (2 * (sourceLocalBoxScale R * Real.exp (-t / 2))) ^ n *
        (sourceLocalBoxScale R * Real.exp (-t / 2)) ^ n =
      2 ^ n * sourceLocalBoxScale R ^ (2 * n) *
        Real.exp (-t / 2) ^ (2 * n) := by
      simp only [mul_pow,
        show 2 * n = n + n by omega, pow_add]
      ring
    _ = 2 ^ n * sourceLocalBoxScale R ^ (2 * n) *
        Real.exp (-(n : ℝ) * t) := by rw [hexp]

private theorem sourceLocalTorusBox_measure_ne_top
    (n : ℕ) {δ : ℝ} (hδ : δ ≤ 1) :
    sourceTorusBaseMeasure n (sourceLocalTorusBox n δ) ≠ ⊤ := by
  rw [sourceLocalTorusBox_volume n hδ]
  finiteness

end JetEnvelopeLocalGrowth

namespace JetEnvelopeGlobalPlurisubharmonic

open Set Filter MeasureTheory Metric
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology ENNReal InnerProductSpace

private abbrev SourceJointComplexCover (n : ℕ) :=
  TorusCharacters.LogSpace n × ℂ

private def sourceJointCoverTime {n : ℕ}
    (q : SourceJointComplexCover n) : ℝ :=
  2 * q.2.re

private theorem continuous_sourceJointCoverTime (n : ℕ) :
    Continuous (sourceJointCoverTime (n := n)) := by
  unfold sourceJointCoverTime
  fun_prop

private theorem normSq_mul_of_norm_one
    (u : ℂ) (hu : ‖u‖ = 1) (z : ℂ) :
    Complex.normSq (u * z) = Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq, hu]
  simp only [one_pow, one_mul]

private def sourceJointPhaseHomeomorph {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1) :
    PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n := by
  have hu0 : u ≠ 0 := by
    intro hzero
    simp only [hzero, norm_zero, zero_ne_one] at hu
  let h :
      (TorusCharacters.LogSpace n × ℂ) ≃ₜ
        (TorusCharacters.LogSpace n × ℂ) :=
    (Homeomorph.refl (TorusCharacters.LogSpace n)).prodCongr
      (Homeomorph.mulLeft₀ u hu0)
  exact h.subtype fun q => by
    change
      (1 : ℝ) < Complex.normSq q.2 ↔
        (1 : ℝ) < Complex.normSq (u * q.2)
    rw [normSq_mul_of_norm_one u hu]

private theorem sourceJointPhaseHomeomorph_spatial {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    (sourceJointPhaseHomeomorph u hu q).val.1 = q.val.1 := by
  rfl

private theorem jointLogTime_sourceJointPhaseHomeomorph {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    jointLogTime (sourceJointPhaseHomeomorph u hu q) =
      jointLogTime q := by
  change Real.log (Complex.normSq (u * q.val.2)) =
    Real.log (Complex.normSq q.val.2)
  rw [normSq_mul_of_norm_one u hu]

private theorem upperRegularization_comp_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (h : X ≃ₜ Y) (x : X) :
    upperRegularization (fun y : X => f (h y)) x =
      upperRegularization f (h x) := by
  unfold upperRegularization
  congr 1
  ext c
  change
    (∀ᶠ y : X in 𝓝 x, f (h y) ≤ c) ↔
      ∀ᶠ z : Y in 𝓝 (h x), f z ≤ c
  rw [← h.map_nhds_eq x, Filter.eventually_map]

private def sourceJointCoverExp {n : ℕ}
    (q : SourceJointComplexCover n) :
    TorusCharacters.LogSpace n × ℂ :=
  (q.1, Complex.exp q.2)

private theorem differentiable_sourceJointCoverExp (n : ℕ) :
    Differentiable ℂ (sourceJointCoverExp (n := n)) := by
  unfold sourceJointCoverExp
  fun_prop

private theorem continuous_sourceJointCoverExp (n : ℕ) :
    Continuous (sourceJointCoverExp (n := n)) :=
  (differentiable_sourceJointCoverExp n).continuous

private theorem normSq_sourceJointCoverExp
    {n : ℕ} (q : SourceJointComplexCover n) :
    Complex.normSq (sourceJointCoverExp q).2 =
      Real.exp (sourceJointCoverTime q) := by
  unfold sourceJointCoverExp sourceJointCoverTime
  calc
    Complex.normSq (Complex.exp q.2) =
        Real.exp q.2.re ^ 2 := by
      rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
    _ = Real.exp (2 * q.2.re) := by
      simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul q.2.re 2).symm

private def sourceJointExpPositiveLift {n : ℕ}
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    PositiveJointLogSpace n := by
  refine ⟨sourceJointCoverExp q, ?_⟩
  rw [normSq_sourceJointCoverExp]
  simpa only [Real.one_lt_exp_iff, Real.exp_zero] using (Real.exp_lt_exp.mpr hq)

private theorem jointLogTime_sourceJointExpPositiveLift
    {n : ℕ}
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    jointLogTime (sourceJointExpPositiveLift q hq) =
      sourceJointCoverTime q := by
  unfold jointLogTime sourceJointExpPositiveLift
  rw [normSq_sourceJointCoverExp, Real.log_exp]

private theorem sourceJointAuxiliaryPhase_norm
    (η : ℂ) :
    ‖Complex.exp ((η.im : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im,
    Complex.I_im, mul_one, sub_self, Real.exp_zero]

private theorem sourceJointExpPositiveLift_eq_phase_radialLift
    {n : ℕ}
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    sourceJointExpPositiveLift q hq =
      sourceJointPhaseHomeomorph
        (Complex.exp ((q.2.im : ℂ) * Complex.I))
        (sourceJointAuxiliaryPhase_norm q.2)
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change
      Complex.exp q.2 =
        Complex.exp ((q.2.im : ℂ) * Complex.I) *
          (Real.exp (sourceJointCoverTime q / 2) : ℂ)
    rw [sourceJointCoverTime,
      show 2 * q.2.re / 2 = q.2.re by ring,
      Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [add_comm, Complex.re_add_im]

private theorem sourceJointCircleAverage_eq_setAverage
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (R : ℝ) :
    (⨍ θ in Set.Ioc 0 (2 * Real.pi), f (circleMap 0 R θ)) =
      Real.circleAverage f 0 R := by
  rw [MeasureTheory.setAverage_eq, Real.circleAverage_def,
    intervalIntegral.integral_of_le Real.two_pi_pos.le]
  simp only [measureReal_def, Real.volume_Ioc, sub_zero, Nat.ofNat_nonneg, ENNReal.ofReal_mul,
    ENNReal.ofReal_ofNat, ENNReal.toReal_mul, ENNReal.toReal_ofNat, Real.pi_pos.le,
    ENNReal.toReal_ofReal, mul_inv_rev]

private theorem sourceJointSpatialLine_circleAverage
    {n : ℕ} (q v : SourceJointComplexCover n) (R : ℝ) :
    Real.circleAverage
      (fun w : ℂ => (q + w • v).1) 0 R = q.1 := by
  let f : ℂ → TorusCharacters.LogSpace n :=
    fun w => (q + w • v).1
  have hf : Differentiable ℂ f := by
    dsimp [f]
    fun_prop
  have hdc : DiffContOnCl ℂ f (Metric.ball (0 : ℂ) |R|) :=
    hf.diffContOnCl
  simpa [f] using hdc.circleAverage

end JetEnvelopeGlobalPlurisubharmonic

namespace EnvelopeSmoothing

open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology Convolution ContDiff

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)

private def sourceJointTimeEmbedding {n : ℕ}
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    SourceJointComplexCover n :=
  (z, (t / 2 : ℂ))

private theorem sourceJointCoverTime_timeEmbedding {n : ℕ}
    (z : TorusCharacters.LogSpace n) (t : ℝ) :
    sourceJointCoverTime (sourceJointTimeEmbedding z t) = t := by
  simp only [sourceJointCoverTime, sourceJointTimeEmbedding, Complex.div_ofNat_re,
    Complex.ofReal_re]
  ring

end EnvelopeSmoothing

namespace EnvelopeSpatialPeriodicity

open Set Function Filter MeasureTheory
open ActualJetUpperEnvelope JetEnvelopeRightDerivative
open scoped BigOperators Topology

private def sourceJointSpatialDeckHomeomorph {n : ℕ}
    (m : Fin n → ℤ) :
    PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n := by
  let h :
      (TorusCharacters.LogSpace n × ℂ) ≃ₜ
        (TorusCharacters.LogSpace n × ℂ) :=
    (Homeomorph.addRight (TorusCharacters.imaginaryShift m)).prodCongr
      (Homeomorph.refl ℂ)
  exact h.subtype fun _ => Iff.rfl

private theorem sourceJointSpatialDeckHomeomorph_spatial
    {n : ℕ} (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    (sourceJointSpatialDeckHomeomorph m q).val.1 =
      q.val.1 + TorusCharacters.imaginaryShift m := by
  rfl

private theorem jointLogTime_sourceJointSpatialDeckHomeomorph
    {n : ℕ} (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    jointLogTime (sourceJointSpatialDeckHomeomorph m q) =
      jointLogTime q := by
  rfl

private theorem sourcePositiveJointTimePoint_spatial_translate
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) (ht : 0 < t)
    (m : Fin n → ℤ) :
    sourcePositiveJointTimePoint
        (z + TorusCharacters.imaginaryShift m) t ht =
      sourceJointSpatialDeckHomeomorph m
        (sourcePositiveJointTimePoint z t ht) := by
  apply Subtype.ext
  rfl

end EnvelopeSpatialPeriodicity

namespace BergmanJetSpatialPeriodicity

open Set Function Filter MeasureTheory
open TorusCharacters AdaptedBergmanBasis BergmanMonomials MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic BergmanJetBasis BergmanJetGeodesic BergmanJetRealGeodesic
open BergmanJetUpperEnvelope ActualJetUpperEnvelope JetEnvelopeGlobalPlurisubharmonic
open EnvelopeSpatialPeriodicity
open scoped BigOperators Topology

private theorem momentHolomorphicRepresentative_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport)
    (m : Fin n → ℤ) :
    Function.Periodic
      (momentHolomorphicRepresentative K hk F htransport s)
      (imaginaryShift m) := by
  classical
  intro z
  simp only [momentHolomorphicRepresentative, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    normalizedHolomorphicMonomial, torusCharacter_imaginaryShift, smul_eq_mul]

private theorem momentJointJetSection_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (i : Fin (bergmanDimension K k))
    (τ : ℂ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointJetSection K hk F htransport p N i (z, τ))
      (imaginaryShift m) := by
  intro z
  change
    momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p i)
        (z + imaginaryShift m) *
      τ ^ momentTruncatedJetOrder K hk F htransport p N i =
    momentHolomorphicRepresentative K hk F htransport
        (momentSimultaneousJetBasis K hk F htransport p i) z *
      τ ^ momentTruncatedJetOrder K hk F htransport p N i
  rw [momentHolomorphicRepresentative_spatial_periodic
    K hk F htransport
    (momentSimultaneousJetBasis K hk F htransport p i) m z]

private theorem momentJointJetDiagonal_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (τ : ℂ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJointJetDiagonal K hk F htransport p N (z, τ))
      (imaginaryShift m) := by
  intro z
  unfold momentJointJetDiagonal
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact momentJointJetSection_spatial_periodic
    K hk F htransport p N i τ m z

private theorem momentJetGeodesic_spatial_periodic
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ)
    (t : ℝ) (m : Fin n → ℤ) :
    Function.Periodic
      (fun z : LogSpace n =>
        momentJetGeodesic K hk F htransport p N z t)
      (imaginaryShift m) := by
  intro z
  change
    momentJetGeodesic K hk F htransport p N
        (z + imaginaryShift m) t =
      momentJetGeodesic K hk F htransport p N z t
  rw [momentJetGeodesic_eq_log_jointJetDiagonal,
    momentJetGeodesic_eq_log_jointJetDiagonal]
  have hdiag := momentJointJetDiagonal_spatial_periodic
    K hk F htransport p N (Real.exp (t / 2) : ℂ) m z
  change
    momentJointJetDiagonal K hk F htransport p N
        (z + imaginaryShift m, (Real.exp (t / 2) : ℂ)) =
      momentJointJetDiagonal K hk F htransport p N
        (z, (Real.exp (t / 2) : ℂ)) at hdiag
  rw [hdiag]

private theorem momentPositiveJointGeodesic_spatial_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k
        (sourceJointSpatialDeckHomeomorph m q) =
      momentPositiveJointGeodesic K F htransport p k q := by
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
    momentPositiveJointGeodesic_eq_momentJetGeodesic,
    sourceJointSpatialDeckHomeomorph_spatial,
    jointLogTime_sourceJointSpatialDeckHomeomorph]
  exact momentJetGeodesic_spatial_periodic
    K (Nat.zero_lt_succ k) F htransport p
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) (jointLogTime q) m q.val.1

private theorem momentJointTailSup_spatial_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p r
        (sourceJointSpatialDeckHomeomorph m q) =
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  have hfun :
      (fun j : ℕ =>
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j)
          (sourceJointSpatialDeckHomeomorph m q)) =
      (fun j : ℕ =>
        momentPositiveJointGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentPositiveJointGeodesic_spatial_invariant
      K F htransport p _ m q
  rw [hfun]

private theorem momentJointTailUpperEnvelope_spatial_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r
        (sourceJointSpatialDeckHomeomorph m q) =
      momentJointTailUpperEnvelope K F htransport p r q := by
  let h : PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n :=
    sourceJointSpatialDeckHomeomorph m
  have hfun :
      (fun z : PositiveJointLogSpace n =>
        momentJointTailSup K F htransport p r (h z)) =
      momentJointTailSup K F htransport p r := by
    funext z
    exact momentJointTailSup_spatial_invariant
      K F htransport p r m z
  change
    upperRegularization (momentJointTailSup K F htransport p r) (h q) =
      upperRegularization (momentJointTailSup K F htransport p r) q
  rw [← upperRegularization_comp_homeomorph
    (momentJointTailSup K F htransport p r) h q, hfun]

end BergmanJetSpatialPeriodicity

end Ehrhart

end
