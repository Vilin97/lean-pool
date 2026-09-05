/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.FourierAnalysis
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import all LeanPool.EhrhartVolumeInequality.FourierAnalysis
import all Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Order

/-!
# Ehrhart volume inequality: Regularization

Regularization, descent, and positive-Hessian arguments.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace ComplexSaturatedKillingFieldBridge

open Set Function MeasureTheory Filter
open scoped BigOperators ContDiff Convolution ENNReal InnerProductSpace Topology

open WeightedTorusHilbert WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open JointHolomorphicLaurentFourierCompatibility

private theorem angularFundamentalCell_set_measurable (n : ℕ) :
    MeasurableSet
      {t : Space n |
        ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)} := by
  have hbox : MeasurableSet
      (angularFundamentalBox (0 : Space n)) := by
    unfold angularFundamentalBox
    exact MeasurableSet.univ_pi' (fun _ => measurableSet_Ioc)
  simpa only [zero_add, mem_Ioc, measurableSet_setOfPred, angularFundamentalBox,
    Pi.zero_apply] using hbox

private def realFundamentalEmbedding (n : ℕ) :
    Space n × angularFundamentalCell n →
      Space n × Space n :=
  fun p => (p.1, p.2.1)

private theorem realFundamentalEmbedding_measurePreserving (n : ℕ) :
    MeasurePreserving (realFundamentalEmbedding n)
      (unweightedFundamentalMeasure n)
      ((volume : Measure (Space n)).prod
        ((volume : Measure (Space n)).restrict
          {t : Space n |
            ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)})) := by
  let : IsFiniteMeasure (angularFundamentalMeasure n) := by
    rw [← (angularFundamentalEquiv_measurePreserving n).map_eq]
    infer_instance
  have hsub : MeasurePreserving
      (Subtype.val : angularFundamentalCell n → Space n)
      (angularFundamentalMeasure n)
      ((volume : Measure (Space n)).restrict
        {t : Space n |
          ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}) := by
    exact measurePreserving_subtype_coe
      (angularFundamentalCell_set_measurable n)
  change MeasurePreserving
    (Prod.map id (Subtype.val : angularFundamentalCell n → Space n))
    ((volume : Measure (Space n)).prod
      (angularFundamentalMeasure n))
    ((volume : Measure (Space n)).prod
      ((volume : Measure (Space n)).restrict
        {t : Space n |
          ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}))
  exact (MeasurePreserving.id
    (volume : Measure (Space n))).prod hsub

private theorem unweightedTorus_representative_ae_of_complexCover
    {n : ℕ}
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hcover : F =ᵐ[(volume :
      Measure (TorusCharacters.LogSpace n))]
        complexTorusCoverLift f) :
    (fun z : WeightedTorusHilbert.LogTorus n => f z) =ᵐ[unweightedTorusMeasure n]
        (fun z => coverRepresentative F z.1 z.2) := by
  have hpush : F =ᵐ[logarithmicCoverPushforward n]
      complexTorusCoverLift f := by
    rw [logarithmicCoverPushforward_eq_smul_volume]
    change F =ᵐ[
      ((logarithmicCoverJacobianFactor n : ℝ≥0∞) •
        (volume : Measure (TorusCharacters.LogSpace n)))]
      complexTorusCoverLift f
    exact (Measure.ae_ennreal_smul_measure_iff
      (ENNReal.coe_ne_zero.mpr
        (logarithmicCoverJacobianFactor_pos n).ne')).mpr hcover
  have hreal :
      (fun p : Space n × Space n =>
        F (logarithmicCoordinatesEquiv n p)) =ᵐ[
          (volume : Measure (Space n × Space n))]
      (fun p => f (realTorusCoverProjection n p)) := by
    have h :=
      (logarithmicCoordinates_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
        hpush
    simpa only [realTorusCoverProjection, comp_def, complexTorusCoverLift,
      complexTorusCoverProjection, ContinuousLinearEquiv.symm_apply_apply] using h
  let s : Set (Space n) :=
    {t | ∀ i : Fin n, t i ∈ Set.Ioc (0 : ℝ) ((0 : ℝ) + 1)}
  have hrestricted :
      (fun p : Space n × Space n =>
        F (logarithmicCoordinatesEquiv n p)) =ᵐ[
          (volume : Measure (Space n)).prod
            ((volume : Measure (Space n)).restrict s)]
      (fun p => f (realTorusCoverProjection n p)) := by
    have h := ae_restrict_of_ae
      (s := (Set.univ : Set (Space n)) ×ˢ s) hreal
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at h
    simp only [Measure.restrict_univ] at h
    filter_upwards [h] with x hx
    exact hx
  have hfund :=
    (realFundamentalEmbedding_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
      hrestricted
  have htorus :=
    (unweightedTorusFundamental_measurePreserving n).quasiMeasurePreserving.ae_eq_comp
      hfund
  filter_upwards [htorus] with z hz
  have hcell := coverRepresentative_fundamentalCell F z.1
    (angularFundamentalEquiv n z.2)
  have hcoverpoint : coverRepresentative F z.1 z.2 =
      F (logarithmicPoint z.1
        ((angularFundamentalEquiv n z.2) : Space n)) := by
    simpa only [MeasurableEquiv.symm_apply_apply] using hcell
  have hangle :
      angularCoverProjection n
        ((angularFundamentalEquiv n z.2) : Space n) = z.2 := by
    calc
      angularCoverProjection n
          ((angularFundamentalEquiv n z.2) : Space n) =
          (angularFundamentalEquiv n).symm
            (angularFundamentalEquiv n z.2) := by
        rw [angularFundamentalEquiv_symm_apply]
        rfl
      _ = z.2 := (angularFundamentalEquiv n).symm_apply_apply z.2
  rw [hcoverpoint]
  change
    F (logarithmicPoint z.1
      ((angularFundamentalEquiv n z.2) : Space n)) =
      f (z.1, angularCoverProjection n
        ((angularFundamentalEquiv n z.2) : Space n)) at hz
  rw [hangle] at hz
  exact hz.symm

private theorem weightedTorus_representative_ae_of_complexCover
    {n k : ℕ} {φ : Space n → ℝ}
    (hφ : Continuous φ)
    {f : WeightedTorusHilbert.LogTorus n → ℂ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hcover : F =ᵐ[(volume :
      Measure (TorusCharacters.LogSpace n))]
        complexTorusCoverLift f) :
    (fun z : WeightedTorusHilbert.LogTorus n => f z) =ᵐ[weightedTorusMeasure k φ]
        (fun z => coverRepresentative F z.1 z.2) := by
  exact unweightedTorus_ae_eq_weighted hφ
    (unweightedTorus_representative_ae_of_complexCover hcover)

private def weightOneZeroIndex {n : ℕ}
    (K : CenteredBody n) :
    LatticeAsymptotics.monomialIndex K 1 :=
  ⟨0, (LatticeAsymptotics.mem_monomialIndex_one_iff
    K 0).mpr rfl⟩

private theorem weightOneIndex_eq_zeroIndex {n : ℕ}
    (K : CenteredBody n)
    (u : LatticeAsymptotics.monomialIndex K 1) :
    u = weightOneZeroIndex K := by
  apply Subtype.ext
  exact (LatticeAsymptotics.mem_monomialIndex_one_iff
    K (u : Space n)).mp u.property

private theorem weightOne_integerExponent_eq_zero {n : ℕ}
    (K : CenteredBody n)
    (u : LatticeAsymptotics.monomialIndex K 1) :
    integerExponent K (by decide) u = (0 : Fin n → ℤ) := by
  apply integerExponent_eq_of_integerPoint
    K (by decide) u (0 : Fin n → ℤ)
  have hu := (LatticeAsymptotics.mem_monomialIndex_one_iff
    K (u : Space n)).mp u.property
  rw [hu]
  funext i
  simp only [integerPoint, Pi.zero_apply, Int.cast_zero, Nat.cast_one, Pi.smul_apply, smul_eq_mul,
    mul_zero]

private theorem torusMonomial_zero {n : ℕ}
    (p : WeightedTorusHilbert.LogTorus n) :
    torusMonomial (0 : Fin n → ℤ) p = 1 := by
  simp only [torusMonomial, radialCharacter, TorusCharacters.torusCharacter_zero,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, mul_one]

end ComplexSaturatedKillingFieldBridge

namespace WeightedTorusBrascampLieb

open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation ComplexKillingSaturationBridge
open ComplexSaturatedKillingFieldBridge WeightedTorusWeylWeakRepresentativeBridge
open JointHolomorphicLaurentFourierCompatibility WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private def angularTorusComplexHessianMatrix {n : ℕ}
    (a : LogTorus n → ℝ) (p : LogTorus n) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => angularTorusComplexHessian a i j p

private theorem continuous_angularTorusComplexHessianMatrix {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 2 (angularCoverPotential a)) :
    Continuous (angularTorusComplexHessianMatrix a) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact continuous_angularTorusComplexHessian ha i j

private theorem radialZeroGraph_weightOne_eq_constantMonomial
    {n : ℕ} (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {B : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction
        K.carrier x| ≤ B)
    (f : weightedTorusScalarL2 1 φ)
    (hf : WithLp.toLp 2
      (f, (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ) :
    ∃ c : ℂ,
      f = c • indexedMonomialLp K (by decide) hφ hbounded
        (weightOneZeroIndex K) := by
  classical
  let := (BergmanMonomials.monomialIndex_finite
    K (by decide : 0 < (1 : ℕ))).fintype
  obtain ⟨F, hF, hperiod, hcover⟩ :=
    weightedZeroGraph_exists_periodic_holomorphic_representative
      hφ f hf
  have hfinite := holomorphic_representative_eq_finite_laurent_sum
    K (by decide) hφ hbounded f hF hperiod
      (weightedTorus_representative_ae_of_complexCover hφ hcover)
  have hsingleton :
      (Finset.univ : Finset
        (LatticeAsymptotics.monomialIndex K 1)) =
          {weightOneZeroIndex K} := by
    ext u
    simp only [weightOneIndex_eq_zeroIndex K u, Finset.mem_univ, Finset.mem_singleton]
  refine ⟨laurentCoefficient F (0 : Fin n → ℤ), ?_⟩
  simpa only [hsingleton, Finset.sum_singleton,
    weightOne_integerExponent_eq_zero] using hfinite

private theorem radialZeroGraph_weightOne_ae_constant
    {n : ℕ} (K : CenteredBody n)
    {φ : Space n → ℝ} (hφ : Continuous φ)
    {B : ℝ}
    (hbounded : ∀ x : Space n,
      |φ x - SupportFunction.supportFunction
        K.carrier x| ≤ B)
    (f : weightedTorusScalarL2 1 φ)
    (hf : WithLp.toLp 2
      (f, (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ) :
    ∃ c : ℂ, (fun q : LogTorus n => f q) =ᵐ[
      weightedTorusMeasure 1 φ] (fun _ => c) := by
  obtain ⟨c, hc⟩ := radialZeroGraph_weightOne_eq_constantMonomial
    K hφ hbounded f hf
  let u := weightOneZeroIndex K
  let M : weightedTorusScalarL2 1 φ :=
    indexedMonomialLp K (by decide) hφ hbounded u
  refine ⟨c, ?_⟩
  have hmonomial := indexedMonomialLp_ae
    K (by decide) hφ hbounded u
  have hsmul := MeasureTheory.Lp.coeFn_smul c M
  filter_upwards [hmonomial, hsmul] with q hmono hmul
  calc
    f q = (c • M) q := by rw [hc]
    _ = c • M q := hmul
    _ = c := by
      rw [hmono, weightOne_integerExponent_eq_zero,
        torusMonomial_zero]
      simp only [smul_eq_mul, mul_one]

private theorem integrable_angularTorusFormAdjoint_mul_conj
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : TorusCharacters.LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (TorusCharacters.imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    Integrable
      (fun p : LogTorus n =>
        angularTorusFormAdjoint a W p *
          conj (angularTorusFormAdjoint a W p))
      (angularWeightedTorusMeasure a) := by
  have hpair (i j : Fin n) :
      Integrable
        (fun p : LogTorus n =>
          angularTorusWeightedHolomorphicDerivative a
            (fun z => W z i) i p *
            conj (angularTorusWeightedHolomorphicDerivative a
              (fun z => W z j) j p))
        (angularWeightedTorusMeasure a) :=
    integrable_angularTorusWeightedHolomorphic_pair
      ha ha2 (hW i) (hW j) (hWp i) (hWp j) (hWc j) i j
  have hsum :
      Integrable
        (fun p : LogTorus n =>
          ∑ i : Fin n, ∑ j : Fin n,
            angularTorusWeightedHolomorphicDerivative a
              (fun z => W z i) i p *
              conj (angularTorusWeightedHolomorphicDerivative a
                (fun z => W z j) j p))
        (angularWeightedTorusMeasure a) :=
    MeasureTheory.integrable_finsetSum Finset.univ
      (fun i _ => MeasureTheory.integrable_finsetSum Finset.univ
        (fun j _ => hpair i j))
  apply hsum.congr
  filter_upwards [] with p
  simp only [angularTorusFormAdjoint, map_sum,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

private def angularScalarEmbeddingCLM {n : ℕ}
    (a : LogTorus n → ℝ) :
    angularWeightedScalarL2 a →L[ℂ]
      angularDolbeaultGraphAmbient a :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ
    (angularWeightedScalarL2 a)
    (angularWeightedFormL2 a)).symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.inl ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a))

private def angularWeakScalarResolventCLM {n : ℕ}
    (a : LogTorus n → ℝ) :
    angularWeightedScalarL2 a →L[ℂ] angularWeightedScalarL2 a :=
  (WithLp.fstL 2 ℂ
    (angularWeightedScalarL2 a)
    (angularWeightedFormL2 a)).comp
      ((angularDolbeaultGraph a).starProjection.comp
        (angularScalarEmbeddingCLM a))

@[simp] private theorem angularWeakScalarResolventCLM_apply {n : ℕ}
    (a : LogTorus n → ℝ) (f : angularWeightedScalarL2 a) :
    angularWeakScalarResolventCLM a f =
      WithLp.fst (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a) := rfl

private theorem angularWeakScalarResolventCLM_selfAdjoint {n : ℕ}
    (a : LogTorus n → ℝ) (f g : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedScalarL2 a) _
      (angularWeakScalarResolventCLM a f) g =
      @inner ℂ (angularWeightedScalarL2 a) _ f
        (angularWeakScalarResolventCLM a g) := by
  have hfg := angularWeakDolbeaultResolvent_moment_components
    a f (angularWeakDolbeaultResolvent a g)
  have hgf := angularWeakDolbeaultResolvent_moment_components
    a g (angularWeakDolbeaultResolvent a f)
  have hgf' := congrArg conj hgf
  simp only [map_add, inner_conj_symm] at hgf'
  rw [angularWeakScalarResolventCLM_apply,
    angularWeakScalarResolventCLM_apply]
  exact hgf'.symm.trans hfg

private def angularWeakResolventFixedSpace {n : ℕ}
    (a : LogTorus n → ℝ) :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  LinearMap.eqLocus (angularWeakScalarResolventCLM a).toLinearMap 1

private theorem angularWeakScalarResolventCLM_fixed_iff_graph_zero
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a) :
    angularWeakScalarResolventCLM a f = f ↔
      WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a := by
  constructor
  · intro hfixed
    have hscalar :
        WithLp.fst (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) = f := by
      simpa only [angularWeakScalarResolventCLM_apply] using hfixed
    have hvar := angularWeakDolbeaultResolvent_moment_components
      a f (angularWeakDolbeaultResolvent a f)
    rw [hscalar] at hvar
    have hinner :
        @inner ℂ (angularWeightedFormL2 a) _
          (WithLp.snd (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
          (WithLp.snd (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) = 0 := by
      linear_combination hvar
    have hgradient :
        WithLp.snd (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) = 0 :=
      (inner_self_eq_zero).mp hinner
    have hpair :
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a) =
            WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)) := by
      apply (WithLp.prodContinuousLinearEquiv 2 ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a)).injective
      exact Prod.ext hscalar hgradient
    rw [← hpair]
    exact (angularWeakDolbeaultResolvent a f).property
  · intro hgraph
    have hproj :=
      (angularDolbeaultGraph a).starProjection_eq_self_iff.mpr hgraph
    change WithLp.fst
      ((angularDolbeaultGraph a).starProjection
        (WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)))) = f
    rw [hproj]
    rfl

private theorem angularWeakScalarResolventCLM_defect_range_closure
    {n : ℕ} (a : LogTorus n → ℝ) :
    ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a).range).topologicalClosure =
      (angularWeakResolventFixedSpace a)ᗮ := by
  let T : angularWeightedScalarL2 a →L[ℂ]
      angularWeightedScalarL2 a :=
    ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a
  have hTadj : T.adjoint = T := by
    symm
    apply (ContinuousLinearMap.eq_adjoint_iff T T).2
    intro x y
    change
      @inner ℂ (angularWeightedScalarL2 a) _
        (x - angularWeakScalarResolventCLM a x) y =
        @inner ℂ (angularWeightedScalarL2 a) _ x
          (y - angularWeakScalarResolventCLM a y)
    rw [inner_sub_left, inner_sub_right,
      angularWeakScalarResolventCLM_selfAdjoint]
  have hker : T.ker = angularWeakResolventFixedSpace a := by
    ext x
    change
      x - angularWeakScalarResolventCLM a x = 0 ↔
        angularWeakScalarResolventCLM a x = x
    rw [sub_eq_zero]
    exact eq_comm
  change T.range.topologicalClosure =
    (angularWeakResolventFixedSpace a)ᗮ
  calc
    T.range.topologicalClosure = T.kerᗮ := by
      simpa only [hTadj] using (T.orthogonal_ker).symm
    _ = (angularWeakResolventFixedSpace a)ᗮ := by rw [hker]

end WeightedTorusBrascampLieb

namespace ArbitraryBodyOneSidedAngularWeightedKernel

open Set Function MeasureTheory Filter Matrix
open WeightedTorusHilbert WeightedBrascampSaturation JetEnvelopeSlopeConvergence
open ComplexKillingSaturationBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem radialWeightedTorusDensity_le_angular_of_upper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (q : LogTorus n) :
    radialWeight 1 φ q.1 ≤
      ENNReal.ofReal (Real.exp C) *
        ENNReal.ofReal (angularWeightedTorusDensity a q) := by
  have hexp : Real.exp (-φ q.1) ≤
      Real.exp C * Real.exp (-a q) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [hupper q]
  simpa only [radialWeight, Nat.cast_one, neg_mul, one_mul, angularWeightedTorusDensity, ge_iff_le,
    ENNReal.ofReal_mul (Real.exp_pos C).le] using
    ENNReal.ofReal_le_ofReal hexp

private theorem radialWeightedTorusMeasure_le_angular_of_upper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    weightedTorusMeasure 1 φ ≤
      ENNReal.ofReal (Real.exp C) • angularWeightedTorusMeasure a := by
  rw [weightedTorusMeasure_eq_withDensity 1 hφ]
  change
    (sourceTorusBaseMeasure n).withDensity
        (fun q => radialWeight 1 φ q.1) ≤
      ENNReal.ofReal (Real.exp C) •
        (sourceTorusBaseMeasure n).withDensity
          (fun q => ENNReal.ofReal
            (angularWeightedTorusDensity a q))
  rw [← MeasureTheory.withDensity_smul'
    (ENNReal.ofReal (Real.exp C))
    (fun q : LogTorus n =>
      ENNReal.ofReal (angularWeightedTorusDensity a q))
    ENNReal.ofReal_ne_top]
  apply MeasureTheory.withDensity_mono
  filter_upwards [] with q
  simpa only [Pi.smul_apply, smul_eq_mul] using
    radialWeightedTorusDensity_le_angular_of_upper hupper q

private theorem memLp_radial_of_angular_upper
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    {f : LogTorus n → E}
    (hf : MemLp f 2 (angularWeightedTorusMeasure a)) :
    MemLp f 2 (weightedTorusMeasure 1 φ) :=
  hf.of_measure_le_smul ENNReal.ofReal_ne_top
    (radialWeightedTorusMeasure_le_angular_of_upper hφ hupper)

private def angularToRadialLpOfUpper
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    MeasureTheory.Lp E 2 (weightedTorusMeasure 1 φ) :=
  (memLp_radial_of_angular_upper hφ hupper
    (MeasureTheory.Lp.memLp f)).toLp f

private theorem angularToRadialLpOfUpper_ae_eq
    {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    (fun q => angularToRadialLpOfUpper hφ hupper f q) =ᵐ[
      weightedTorusMeasure 1 φ] (fun q => f q) :=
  (memLp_radial_of_angular_upper hφ hupper
    (MeasureTheory.Lp.memLp f)).coeFn_toLp

private def canonicalComplexLpTransfer {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {p : ℝ≥0∞} [Fact (1 ≤ p)] {μ ν : Measure α}
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : μ ≤ c • ν) :
    MeasureTheory.Lp E p ν →L[ℂ] MeasureTheory.Lp E p μ := by
  let L : MeasureTheory.Lp E p ν →L[ℝ] MeasureTheory.Lp E p μ :=
    MeasureTheory.Lp.LpToLpOfMeasureLeSMul hc h
  refine {toFun := L, map_add' := L.map_add, map_smul' := ?_, cont := L.cont}
  intro z f
  apply MeasureTheory.Lp.ext
  have hac : μ ≪ ν := Measure.absolutelyContinuous_of_le_smul h
  filter_upwards [
    MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul hc h (z • f),
    hac.ae_eq (MeasureTheory.Lp.coeFn_smul z f),
    MeasureTheory.Lp.coeFn_smul z (L f),
    MeasureTheory.Lp.coeFn_LpToLpOfMeasureLeSMul hc h f]
    with x hleft hsource hright hbase
  change L (z • f) x = (z • L f) x
  change L f x = f x at hbase
  rw [hleft, hsource, hright]
  change z • f x = z • L f x
  rw [hbase]

private def angularToRadialLpCLMOfUpper
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a) →L[ℂ]
      MeasureTheory.Lp E 2 (weightedTorusMeasure 1 φ) :=
  canonicalComplexLpTransfer ENNReal.ofReal_ne_top
    (radialWeightedTorusMeasure_le_angular_of_upper hφ hupper)

@[simp] private theorem angularToRadialLpCLMOfUpper_apply
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    angularToRadialLpCLMOfUpper hφ hupper f =
      angularToRadialLpOfUpper hφ hupper f := rfl

@[simp] private theorem angularToRadialLpOfUpper_zero
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    angularToRadialLpOfUpper hφ hupper
      (0 : MeasureTheory.Lp E 2
        (angularWeightedTorusMeasure a)) = 0 := by
  change angularToRadialLpCLMOfUpper hφ hupper 0 = 0
  exact map_zero _

private def angularToRadialGraphAmbientCLMOfUpper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    angularDolbeaultGraphAmbient a →L[ℂ]
      functionDolbeaultGraphAmbient 1 φ :=
  ((WithLp.prodContinuousLinearEquiv 2 ℂ
      (weightedTorusScalarL2 1 φ)
      (weightedTorusFormL2 1 φ)).symm.toContinuousLinearMap).comp
    (((angularToRadialLpCLMOfUpper
      (E := ℂ) hφ hupper).prodMap
      (angularToRadialLpCLMOfUpper
        (E := EuclideanSpace ℂ (Fin n)) hφ hupper)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℂ
        (angularWeightedScalarL2 a)
        (angularWeightedFormL2 a)).toContinuousLinearMap)

@[simp] private theorem angularToRadialGraphAmbientCLMOfUpper_pair
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : angularWeightedScalarL2 a)
    (v : angularWeightedFormL2 a) :
    angularToRadialGraphAmbientCLMOfUpper hφ hupper
        (WithLp.toLp 2 (f, v)) =
      WithLp.toLp 2
        (angularToRadialLpOfUpper hφ hupper f,
         angularToRadialLpOfUpper hφ hupper v) := by
  simp only [angularToRadialGraphAmbientCLMOfUpper, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, angularToRadialLpCLMOfUpper_apply,
    WithLp.prodContinuousLinearEquiv_symm_apply]

private theorem angularToRadialGraphAmbientCLMOfUpper_smooth_mem
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    {v : angularDolbeaultGraphAmbient a}
    (hv : v ∈ smoothAngularDolbeaultGraphSet a) :
    angularToRadialGraphAmbientCLMOfUpper hφ hupper v ∈
      smoothFunctionDolbeaultGraphSet 1 φ := by
  obtain ⟨F, hF, hperiod, hcompact, hf, hd, rfl⟩ := hv
  let hf' := memLp_radial_of_angular_upper hφ hupper hf
  let hd' := memLp_radial_of_angular_upper hφ hupper hd
  refine ⟨F, hF, hperiod, hcompact, hf', hd', ?_⟩
  rw [angularToRadialGraphAmbientCLMOfUpper_pair]
  apply congrArg (WithLp.toLp 2)
  apply Prod.ext
  · apply MeasureTheory.Lp.ext
    filter_upwards [
      angularToRadialLpOfUpper_ae_eq hφ hupper
        (angularScalarL2OfRepresentative a F hf),
      (Measure.absolutelyContinuous_of_le_smul
        (radialWeightedTorusMeasure_le_angular_of_upper
          hφ hupper)).ae_eq hf.coeFn_toLp,
      hf'.coeFn_toLp]
        with q htransfer hsource hradial
    exact htransfer.trans (hsource.trans hradial.symm)
  · apply MeasureTheory.Lp.ext
    filter_upwards [
      angularToRadialLpOfUpper_ae_eq hφ hupper
        (angularBarPartialL2OfRepresentative a F hd),
      (Measure.absolutelyContinuous_of_le_smul
        (radialWeightedTorusMeasure_le_angular_of_upper
          hφ hupper)).ae_eq hd.coeFn_toLp,
      hd'.coeFn_toLp]
        with q htransfer hsource hradial
    exact htransfer.trans (hsource.trans hradial.symm)

private theorem angularToRadialGraphAmbientCLMOfUpper_graph_le
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C) :
    (angularDolbeaultGraph a).map
      (angularToRadialGraphAmbientCLMOfUpper hφ hupper).toLinearMap ≤
        functionDolbeaultGraph 1 φ := by
  change
    ((Submodule.span ℂ
      (smoothAngularDolbeaultGraphSet a)).topologicalClosure).map
        (angularToRadialGraphAmbientCLMOfUpper hφ hupper).toLinearMap ≤
      (Submodule.span ℂ
        (smoothFunctionDolbeaultGraphSet 1 φ)).topologicalClosure
  refine (Submodule.topologicalClosure_map
    (angularToRadialGraphAmbientCLMOfUpper hφ hupper)
    (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))).trans ?_
  apply Submodule.topologicalClosure_mono
  rw [Submodule.map_span]
  apply Submodule.span_mono
  rintro _ ⟨v, hv, rfl⟩
  exact angularToRadialGraphAmbientCLMOfUpper_smooth_mem
    hφ hupper hv

private theorem angularZeroGraph_mem_radialZeroGraph_of_upper
    {n : ℕ} {a : LogTorus n → ℝ}
    {φ : Space n → ℝ} {C : ℝ}
    (hφ : Continuous φ)
    (hupper : ∀ q : LogTorus n, a q ≤ φ q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : WithLp.toLp 2
      (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a) :
    WithLp.toLp 2
      (angularToRadialLpOfUpper hφ hupper f,
       (0 : weightedTorusFormL2 1 φ)) ∈
        functionDolbeaultGraph 1 φ := by
  have hmap :=
    angularToRadialGraphAmbientCLMOfUpper_graph_le hφ hupper
      (Submodule.mem_map.mpr
        ⟨WithLp.toLp 2 (f, (0 : angularWeightedFormL2 a)),
          hf, rfl⟩)
  simpa only [ContinuousLinearMap.coe_coe, angularToRadialGraphAmbientCLMOfUpper_pair,
    angularToRadialLpOfUpper_zero] using hmap

private theorem radial_ae_iff_angular_of_continuous
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {φ : Space n → ℝ}
    (hφ : Continuous φ)
    (P : LogTorus n → Prop) :
    (∀ᵐ q ∂(weightedTorusMeasure 1 φ), P q) ↔
      ∀ᵐ q ∂(angularWeightedTorusMeasure a), P q := by
  rw [weightedTorusMeasure_eq_withDensity 1 hφ]
  change
    (∀ᵐ q ∂(sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n => radialWeight 1 φ q.1), P q) ↔
    ∀ᵐ q ∂(sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q)), P q
  have hrad :
      Measurable
        (fun q : LogTorus n => radialWeight 1 φ q.1) :=
    (radialWeight_measurable 1 hφ).comp measurable_fst
  have hang :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    (continuous_angularWeightedTorusDensity ha).measurable.ennreal_ofReal
  rw [MeasureTheory.ae_withDensity_iff hrad,
    MeasureTheory.ae_withDensity_iff hang]
  constructor
  · intro hP
    filter_upwards [hP] with q hq hne
    apply hq
    have hpos : 0 < radialWeight 1 φ q.1 := by
      unfold radialWeight
      exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
    exact hpos.ne'
  · intro hP
    filter_upwards [hP] with q hq hne
    apply hq
    exact (ENNReal.ofReal_pos.mpr
      (angularWeightedTorusDensity_pos a q)).ne'

private theorem smoothConvexPotential_upper_of_support_upper
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (q : LogTorus n) :
    a q ≤ smoothConvexPotential K q.1 + (C + 1) := by
  have hb := (abs_le.mp
    (smoothConvexPotential_bounded K q.1)).1
  linarith [hupper q]

private theorem angularZeroGraph_ae_constant_of_support_upper
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : WithLp.toLp 2
      (f, (0 : angularWeightedFormL2 a)) ∈
        angularDolbeaultGraph a) :
    ∃ c : ℂ,
      (fun q : LogTorus n => f q) =ᵐ[
        angularWeightedTorusMeasure a]
          (fun _ => c) := by
  let φ := smoothConvexPotential K
  have hφ : Continuous φ :=
    (smoothConvexPotential_contDiff K).continuous
  have hb : ∀ x : Space n,
      |φ x -
        SupportFunction.supportFunction K.carrier x| ≤ 1 :=
    smoothConvexPotential_bounded K
  have hcomparison : ∀ q : LogTorus n,
      a q ≤ φ q.1 + (C + 1) :=
    smoothConvexPotential_upper_of_support_upper K hupper
  have hgraph :=
    angularZeroGraph_mem_radialZeroGraph_of_upper
      hφ hcomparison f hf
  obtain ⟨c, hc⟩ :=
    radialZeroGraph_weightOne_ae_constant
      K hφ hb
      (angularToRadialLpOfUpper hφ hcomparison f)
      hgraph
  refine ⟨c, (radial_ae_iff_angular_of_continuous
    ha hφ (fun q : LogTorus n => f q = c)).mp ?_⟩
  filter_upwards [
    angularToRadialLpOfUpper_ae_eq hφ hcomparison f, hc]
      with q htransfer hconstant
  exact htransfer.symm.trans hconstant

private theorem angularWeakScalarResolventCLM_fixed_ae_eq_const_of_support_upper
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : angularWeakScalarResolventCLM a f = f) :
    ∃ c : ℂ,
      (fun q : LogTorus n => f q) =ᵐ[
        angularWeightedTorusMeasure a] (fun _ => c) :=
  angularZeroGraph_ae_constant_of_support_upper K ha hupper f
    ((angularWeakScalarResolventCLM_fixed_iff_graph_zero a f).mp hf)

end ArbitraryBodyOneSidedAngularWeightedKernel

namespace BergmanJetSpatialSmoothing

open Set Function Filter MeasureTheory
open TorusCharacters BergmanDiagonalBasisIndependence ArbitraryBodySmoothConvexPotentialBridge
open scoped BigOperators Topology Convolution ContDiff

private theorem norm_realLogCoordinate_le {n : ℕ} (z : LogSpace n) :
    ‖realLogCoordinate z‖ ≤ 2 * ‖z‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg z))).2
  intro j
  calc
    ‖realLogCoordinate z j‖ = 2 * |(z j).re| := by
      simp only [realLogCoordinate, norm_mul, Real.norm_ofNat, Real.norm_eq_abs]
    _ ≤ 2 * ‖z j‖ :=
      mul_le_mul_of_nonneg_left
        (Complex.abs_re_le_norm (z j)) (by norm_num)
    _ ≤ 2 * ‖z‖ :=
      mul_le_mul_of_nonneg_left
        (norm_le_pi_norm z j) (by norm_num)

private theorem dist_realLogCoordinate_sub_le
    {n : ℕ} (z y : LogSpace n) :
    dist (realLogCoordinate (z - y))
      (realLogCoordinate z) ≤ 2 * ‖y‖ := by
  rw [dist_eq_norm]
  have heq : realLogCoordinate (z - y) -
      realLogCoordinate z = -realLogCoordinate y := by
    funext j
    simp only [Pi.sub_apply, realLogCoordinate, Complex.sub_re, Pi.neg_apply]
    ring
  rw [heq, norm_neg]
  exact norm_realLogCoordinate_le y

private theorem supportFunction_realLogCoordinate_sub_le
    {n : ℕ} (K : CenteredBody n)
    {R : ℝ} (hR₀ : 0 ≤ R)
    (hR : ∀ u ∈ K.carrier, ‖u‖ ≤ R)
    (z y : LogSpace n) :
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate (z - y)) ≤
      SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) * (2 * ‖y‖) := by
  have hnR : 0 ≤ (n : ℝ) * R :=
    mul_nonneg (Nat.cast_nonneg n) hR₀
  have hlip := supportFunction_lipschitzWith K.compact
    (K.fullDimensional.mono interior_subset) hR
  have hdist := hlip.dist_le_mul
    (realLogCoordinate (z - y)) (realLogCoordinate z)
  rw [Real.coe_toNNReal _ hnR] at hdist
  calc
    SupportFunction.supportFunction K.carrier
        (realLogCoordinate (z - y)) ≤
      SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        dist
          (SupportFunction.supportFunction K.carrier
            (realLogCoordinate (z - y)))
          (SupportFunction.supportFunction K.carrier
            (realLogCoordinate z)) := by
      rw [Real.dist_eq]
      linarith [le_abs_self
        (SupportFunction.supportFunction K.carrier
          (realLogCoordinate (z - y)) -
          SupportFunction.supportFunction K.carrier
            (realLogCoordinate z))]
    _ ≤ SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) *
          dist (realLogCoordinate (z - y))
            (realLogCoordinate z) :=
      add_le_add (le_refl _) hdist
    _ ≤ SupportFunction.supportFunction K.carrier
          (realLogCoordinate z) +
        ((n : ℝ) * R) * (2 * ‖y‖) :=
      add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left
          (dist_realLogCoordinate_sub_le z y) hnR)

end BergmanJetSpatialSmoothing

namespace ArbitraryBodyOneSidedAngularResolventDefect

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence LogPartitionConvexity WeightedTorusDolbeault
open WeightedTorusBrascampLieb ArbitraryBodyOneSidedAngularWeightedKernel
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem angularWeightedTorusMeasure_isFinite_of_integrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (hintegrable :
      Integrable (angularWeightedTorusDensity a)
        (sourceTorusBaseMeasure n)) :
    IsFiniteMeasure (angularWeightedTorusMeasure a) := by
  unfold angularWeightedTorusMeasure
  exact isFiniteMeasure_withDensity_ofReal
    hintegrable.hasFiniteIntegral

private theorem angularWeightedTorusDensity_integral_pos
    {n : ℕ} {a : LogTorus n → ℝ}
    (hintegrable :
      Integrable (angularWeightedTorusDensity a)
        (sourceTorusBaseMeasure n)) :
    0 < ∫ q : LogTorus n,
      angularWeightedTorusDensity a q
        ∂(sourceTorusBaseMeasure n) := by
  let : NeZero (sourceTorusBaseMeasure n) :=
    sourceTorusBaseMeasure_neZero n
  exact MeasureTheory.integral_exp_pos hintegrable

private def sourceFreeAngularConstantL2
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (c : ℂ) : angularWeightedScalarL2 a :=
  (memLp_const c).toLp (fun _ : LogTorus n => c)

private theorem sourceFreeAngularConstantL2_ae_eq
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (c : ℂ) :
    (fun q : LogTorus n => sourceFreeAngularConstantL2 a c q) =ᵐ[
      angularWeightedTorusMeasure a] (fun _ => c) :=
  MeasureTheory.MemLp.coeFn_toLp
    (memLp_const (μ := angularWeightedTorusMeasure a)
      (p := 2) c)

private def sourceFreeAngularWeightedConstantSubmodule
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  ℂ ∙ sourceFreeAngularConstantL2 a 1

private theorem angularWeakResolventFixedSpace_le_sourceFreeConstants
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ}
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C) :
    angularWeakResolventFixedSpace a ≤
      sourceFreeAngularWeightedConstantSubmodule a := by
  intro f hf
  change angularWeakScalarResolventCLM a f = f at hf
  obtain ⟨c, hc⟩ :=
    angularWeakScalarResolventCLM_fixed_ae_eq_const_of_support_upper
      K ha hupper f hf
  apply Submodule.mem_span_singleton.mpr
  refine ⟨c, ?_⟩
  apply MeasureTheory.Lp.ext
  filter_upwards [
    MeasureTheory.Lp.coeFn_smul c
      (sourceFreeAngularConstantL2 a 1),
    sourceFreeAngularConstantL2_ae_eq a 1, hc]
      with q hsmul hone hconstant
  rw [hsmul]
  change c * sourceFreeAngularConstantL2 a 1 q = f q
  rw [hone, hconstant]
  simp only [mul_one]

private def sourceFreeAngularWeightedMeanCLM
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    angularWeightedScalarL2 a →L[ℂ] ℂ :=
  innerSL ℂ (sourceFreeAngularConstantL2 a 1)

private theorem sourceFreeAngularWeightedMeanCLM_apply
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (f : angularWeightedScalarL2 a) :
    sourceFreeAngularWeightedMeanCLM a f =
      ∫ q : LogTorus n, f q ∂(angularWeightedTorusMeasure a) := by
  change
    @inner ℂ (angularWeightedScalarL2 a) _
      (sourceFreeAngularConstantL2 a 1) f = _
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [sourceFreeAngularConstantL2_ae_eq a 1]
    with q hq
  rw [hq, RCLike.inner_apply]
  simp only [map_one, mul_one]

private def sourceFreeAngularWeightedMeanZeroSubmodule
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    Submodule ℂ (angularWeightedScalarL2 a) :=
  (sourceFreeAngularWeightedMeanCLM a).ker

private theorem mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (f : angularWeightedScalarL2 a) :
    f ∈ sourceFreeAngularWeightedMeanZeroSubmodule a ↔
      (∫ q : LogTorus n,
        f q ∂(angularWeightedTorusMeasure a)) = 0 := by
  change sourceFreeAngularWeightedMeanCLM a f = 0 ↔ _
  rw [sourceFreeAngularWeightedMeanCLM_apply]

private theorem sourceFreeAngularWeightedMeanZero_eq_constant_orthogonal
    {n : ℕ} (a : LogTorus n → ℝ)
    [IsFiniteMeasure (angularWeightedTorusMeasure a)] :
    sourceFreeAngularWeightedMeanZeroSubmodule a =
      (sourceFreeAngularWeightedConstantSubmodule a)ᗮ := by
  ext f
  rw [mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff]
  change
    (∫ q : LogTorus n,
      f q ∂(angularWeightedTorusMeasure a)) = 0 ↔
      f ∈ (ℂ ∙ sourceFreeAngularConstantL2 a 1)ᗮ
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  rw [← sourceFreeAngularWeightedMeanCLM_apply]
  rfl

private theorem sourceFreeAngularWeightedMeanZero_le_resolventDefect_range_closure
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ}
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C) :
    sourceFreeAngularWeightedMeanZeroSubmodule a ≤
      ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
        angularWeakScalarResolventCLM a).range).topologicalClosure := by
  rw [angularWeakScalarResolventCLM_defect_range_closure,
    sourceFreeAngularWeightedMeanZero_eq_constant_orthogonal]
  exact Submodule.orthogonal_le
    (angularWeakResolventFixedSpace_le_sourceFreeConstants
      K ha hupper)

private theorem sourceFreeAngularCentered_mem_resolventDefect_range_closure
    {n : ℕ} (K : CenteredBody n)
    {a : LogTorus n → ℝ}
    [IsFiniteMeasure (angularWeightedTorusMeasure a)]
    (ha : Continuous a)
    {C : ℝ}
    (hupper : ∀ q : LogTorus n,
      a q ≤ SupportFunction.supportFunction
        K.carrier q.1 + C)
    (f : angularWeightedScalarL2 a)
    (hf : (∫ q : LogTorus n,
      f q ∂(angularWeightedTorusMeasure a)) = 0) :
    f ∈ ((ContinuousLinearMap.id ℂ (angularWeightedScalarL2 a) -
      angularWeakScalarResolventCLM a).range).topologicalClosure := by
  apply sourceFreeAngularWeightedMeanZero_le_resolventDefect_range_closure
    K ha hupper
  exact (mem_sourceFreeAngularWeightedMeanZeroSubmodule_iff
    a f).mpr hf

end ArbitraryBodyOneSidedAngularResolventDefect

namespace BergmanJetTorusCoercivity

open Set Function Filter MeasureTheory Metric
open SupportFunction MonomialIntegrability LatticeAsymptotics WeightedTorusHilbert
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative MomentOptimizer MomentFirstVariation
open MomentTargetGeodesic MomentRegularity MomentMoserTrudinger MomentWeakBergman
open BergmanJetTorusEnvelope BergmanJetMonomialEnvelopeLower WeightedTorusDolbeault
open ArbitraryBodyOneSidedAngularResolventDefect
open scoped BigOperators ENNReal Topology

private def momentSignedUnitVector
    {n : ℕ} (k : ℕ) (σ : Fin n → Bool) : Space n :=
  fun i =>
    (if σ i = true then (1 : ℝ) else -1) / (k : ℝ)

private theorem norm_momentSignedUnitVector_le
    {n : ℕ} {k : ℕ} (hk : 0 < k)
    (σ : Fin n → Bool) :
    ‖momentSignedUnitVector k σ‖ ≤
      (k : ℝ)⁻¹ := by
  have hkreal : 0 < (k : ℝ) := by exact_mod_cast hk
  apply (pi_norm_le_iff_of_nonneg
    (inv_nonneg.mpr hkreal.le)).mpr
  intro i
  unfold momentSignedUnitVector
  split_ifs <;> simp [div_eq_mul_inv]

private theorem exists_momentSignedUnitMonomialDegree
    {n : ℕ} (K : CenteredBody n) :
    ∃ k : ℕ, 0 < k ∧
      ∀ σ : Fin n → Bool,
        momentSignedUnitVector k σ ∈
          monomialIndex K k := by
  obtain ⟨r, hr, hball⟩ :=
    (Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n) (zero_mem_interior K)
  obtain ⟨k, hklarge⟩ := exists_nat_gt (1 / r)
  have hkinv : 0 < (1 / r : ℝ) := one_div_pos.mpr hr
  have hkreal : 0 < (k : ℝ) := lt_trans hkinv hklarge
  have hk : 0 < k := by exact_mod_cast hkreal
  have hradius : (k : ℝ)⁻¹ < r :=
    inv_lt_of_inv_lt₀ hr (by simpa only [one_div] using hklarge)
  refine ⟨k, hk, ?_⟩
  intro σ
  apply (mem_monomialIndex_iff K hk
    (momentSignedUnitVector k σ)).mpr
  constructor
  · apply hball
    rw [Metric.mem_ball, dist_zero_right]
    exact lt_of_le_of_lt
      (norm_momentSignedUnitVector_le hk σ)
      hradius
  · intro i
    refine ⟨if σ i = true then (1 : ℤ) else -1, ?_⟩
    unfold momentSignedUnitVector
    split_ifs <;>
      simp [hkreal.ne', div_eq_mul_inv]

private def momentCoerciveMonomialDegree
    {n : ℕ} (K : CenteredBody n) : ℕ :=
  (exists_momentSignedUnitMonomialDegree K).choose

private theorem momentCoerciveMonomialDegree_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentCoerciveMonomialDegree K :=
  (exists_momentSignedUnitMonomialDegree K).choose_spec.1

private theorem momentSignedUnitVector_mem_monomialIndex
    {n : ℕ} (K : CenteredBody n)
    (σ : Fin n → Bool) :
    momentSignedUnitVector
        (momentCoerciveMonomialDegree K) σ ∈
      monomialIndex K (momentCoerciveMonomialDegree K) :=
  (exists_momentSignedUnitMonomialDegree K).choose_spec.2 σ

private def momentCoerciveSignedMonomial
    {n : ℕ} (K : CenteredBody n)
    (σ : Fin n → Bool) :
    monomialIndex K (momentCoerciveMonomialDegree K) :=
  ⟨momentSignedUnitVector
      (momentCoerciveMonomialDegree K) σ,
    momentSignedUnitVector_mem_monomialIndex K σ⟩

private def momentSignedMonomialLowerConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool) : ℝ :=
  (exists_moment_fixedMonomial_torusEnvelope_lower
    K (momentCoerciveMonomialDegree_pos K)
    F htransport
    (momentCoerciveSignedMonomial K σ)).choose

private theorem momentSignedMonomialLowerConstant_spec
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool)
    (p : TorusCharacters.LogSpace n)
    (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    pairing (momentSignedUnitVector
      (momentCoerciveMonomialDegree K) σ) q.1 -
        momentSignedMonomialLowerConstant
          K F htransport σ ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  exact
    (exists_moment_fixedMonomial_torusEnvelope_lower
      K (momentCoerciveMonomialDegree_pos K)
      F htransport
      (momentCoerciveSignedMonomial K σ)).choose_spec
        p q t ht

private def momentTorusEnvelopeCoercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) : ℝ :=
  ∑ σ : Fin n → Bool,
    |momentSignedMonomialLowerConstant
      K F htransport σ|

private theorem momentSignedMonomialLowerConstant_le_coercivityConstant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (σ : Fin n → Bool) :
    momentSignedMonomialLowerConstant K F htransport σ ≤
      momentTorusEnvelopeCoercivityConstant K F htransport := by
  unfold momentTorusEnvelopeCoercivityConstant
  calc
    momentSignedMonomialLowerConstant K F htransport σ ≤
      |momentSignedMonomialLowerConstant
        K F htransport σ| :=
      le_abs_self _
    _ ≤ ∑ τ : Fin n → Bool,
      |momentSignedMonomialLowerConstant
        K F htransport τ| := by
      simpa only using
        (Finset.single_le_sum
          (s := (Finset.univ : Finset (Fin n → Bool)))
          (f := fun τ : Fin n → Bool =>
            |momentSignedMonomialLowerConstant
              K F htransport τ|)
          (fun τ _ => abs_nonneg _)
          (Finset.mem_univ σ))

private def momentSpatialSign
    {n : ℕ} (x : Space n) : Fin n → Bool :=
  fun i => decide (0 ≤ x i)

private theorem pairing_momentSignedUnitVector_spatialSign
    {n k : ℕ} (x : Space n) :
    pairing
      (momentSignedUnitVector k
        (momentSpatialSign x)) x =
      (k : ℝ)⁻¹ * ∑ i, |x i| := by
  classical
  unfold pairing momentSignedUnitVector momentSpatialSign
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 ≤ x i
  · simp only [h, decide_true, ↓reduceIte, div_eq_mul_inv, one_mul, abs_of_nonneg h]
  · have hnonpos : x i ≤ 0 := le_of_not_ge h
    simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte, div_eq_mul_inv, neg_mul, one_mul,
      abs_of_nonpos hnonpos, mul_neg]

private theorem momentTorusEnvelope_norm_coercivity
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (q : LogTorus n) {t : ℝ} (ht : 0 < t) :
    ((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹ *
          ‖q.1‖ -
        momentTorusEnvelopeCoercivityConstant K F htransport ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t := by
  let σ := momentSpatialSign q.1
  have hsign := momentSignedMonomialLowerConstant_spec
    K F htransport σ p q ht
  have hconstant :=
    momentSignedMonomialLowerConstant_le_coercivityConstant
      K F htransport σ
  have hpair :=
    pairing_momentSignedUnitVector_spatialSign
      (k := momentCoerciveMonomialDegree K) q.1
  have hdegree :
      0 ≤
        (((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹) := by
    exact inv_nonneg.mpr
      (by exact_mod_cast
        (momentCoerciveMonomialDegree_pos K).le)
  have hnorm := mul_le_mul_of_nonneg_left
    (SupportFunction.norm_le_sum_abs q.1) hdegree
  dsimp [σ] at hsign
  rw [hpair] at hsign
  exact (sub_le_sub hnorm hconstant).trans hsign

private theorem integrable_exp_neg_momentTorusEnvelopeTimeSlice_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    {t : ℝ} (ht : 0 < t) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  let δ : ℝ :=
    ((momentCoerciveMonomialDegree K : ℕ) : ℝ)⁻¹
  let C : ℝ := momentTorusEnvelopeCoercivityConstant
    K F htransport
  have hδ : 0 < δ := by
    dsimp [δ]
    apply inv_pos.mpr
    exact_mod_cast momentCoerciveMonomialDegree_pos K
  have hrad :
      Integrable
        (fun x : Space n =>
          Real.exp (-δ * ‖x‖))
        (volume : Measure (Space n)) :=
    integrable_exp_neg_mul_norm_all hδ
  have hang :
      Integrable
        (fun _ : TorusCharacters.AngularTorus n =>
          (1 : ℝ))
        (angularMeasure n) :=
    integrable_const 1
  have hprod :
      Integrable
        (fun q : LogTorus n =>
          Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
        (sourceTorusBaseMeasure n) := by
    simpa only [neg_mul, mul_one, sourceTorusBaseMeasure] using hrad.mul_prod hang
  have hmajor := hprod.const_mul (Real.exp C)
  have hmeas :
      AEStronglyMeasurable
        (fun q : LogTorus n =>
          Real.exp
            (-momentTorusEnvelopeTimeSlice
              K F htransport p q t))
        (sourceTorusBaseMeasure n) :=
    (Real.continuous_exp.measurable.comp
      (measurable_momentTorusEnvelopeTimeSlice
        K F htransport p t).neg).aestronglyMeasurable
  apply hmajor.mono' hmeas
  filter_upwards [] with q
  change
    ‖Real.exp
        (-momentTorusEnvelopeTimeSlice
          K F htransport p q t)‖ ≤
      Real.exp C *
        (Real.exp (-δ * ‖q.1‖) * (1 : ℝ))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simp only [mul_one]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hcoerce :=
    momentTorusEnvelope_norm_coercivity
      K F htransport p q ht
  change
    δ * ‖q.1‖ - C ≤
      momentTorusEnvelopeTimeSlice
        K F htransport p q t at hcoerce
  simpa only [sub_eq_add_neg, neg_add_rev, neg_mul, neg_neg] using
    (neg_le_neg hcoerce)

private theorem integrable_exp_neg_momentTorusEnvelopeTimeSlice
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp
          (-momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  by_cases ht : 0 < t
  · exact
      integrable_exp_neg_momentTorusEnvelopeTimeSlice_of_pos
        K F htransport p ht
  · have hnonpos : t ≤ 0 := le_of_not_gt ht
    have hrad :=
      integrable_monomialWeight_momentNormalized_of_mem_interior
        F htransport (zero_mem_interior K)
        (k := (1 : ℝ)) zero_lt_one
    have hrad' :
        Integrable
          (fun x : Space n =>
            Real.exp (-momentNormalizedPotential F x))
          (volume : Measure (Space n)) := by
      apply hrad.congr
      filter_upwards [] with x
      simp only [monomialWeight, pairing, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_sub,
        mul_neg, one_mul]
    have hang :
        Integrable
          (fun _ : TorusCharacters.AngularTorus n =>
            (1 : ℝ))
          (angularMeasure n) :=
      integrable_const 1
    have hprod := hrad'.mul_prod hang
    change
      Integrable
        (fun q : LogTorus n =>
          Real.exp
            (-momentEnvelopeTimeSlice K F htransport p
              (sourceTorusCoverPoint q) t))
        (sourceTorusBaseMeasure n)
    have heq :
        (fun q : LogTorus n =>
          Real.exp
            (-momentEnvelopeTimeSlice K F htransport p
              (sourceTorusCoverPoint q) t)) =
        (fun q : LogTorus n =>
          Real.exp (-momentNormalizedPotential F q.1) *
            (1 : ℝ)) := by
      funext q
      rw [momentEnvelopeTimeSlice_of_nonpositive
        K F htransport p (sourceTorusCoverPoint q) hnonpos,
        JetEnvelopeRightDerivative.realLogCoordinate_sourceTorusCoverPoint]
      simp only [mul_one]
    rw [heq]
    simpa only [mul_one, sourceTorusBaseMeasure] using hprod

private theorem integrable_angularWeightedTorusDensity_momentEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    Integrable
      (angularWeightedTorusDensity
        (fun q : LogTorus n =>
          momentTorusEnvelopeTimeSlice
            K F htransport p q t))
      (sourceTorusBaseMeasure n) := by
  exact integrable_exp_neg_momentTorusEnvelopeTimeSlice
    K F htransport p t

private theorem momentTorusEnvelopePartition_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : TorusCharacters.LogSpace n)
    (t : ℝ) :
    0 < ∫ q : LogTorus n,
      Real.exp
        (-momentTorusEnvelopeTimeSlice
          K F htransport p q t)
        ∂(sourceTorusBaseMeasure n) := by
  exact angularWeightedTorusDensity_integral_pos
    (integrable_angularWeightedTorusDensity_momentEnvelope
      K F htransport p t)

end BergmanJetTorusCoercivity

namespace JetEnvelopeGlobalPlurisubharmonicClosure

open Set Filter Function MeasureTheory Metric
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope ActualJetPlurisubharmonicClosure
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace

private theorem upperRegularization_comp_isOpenMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) (g : X → Y)
    (hg : Continuous g) (ho : IsOpenMap g) (x : X) :
    upperRegularization (fun y : X => f (g y)) x =
      upperRegularization f (g x) := by
  unfold upperRegularization
  congr 1
  ext c
  change
    (∀ᶠ y : X in 𝓝 x, f (g y) ≤ c) ↔
      ∀ᶠ z : Y in 𝓝 (g x), f z ≤ c
  rw [← ho.map_nhds_eq hg.continuousAt, Filter.eventually_map]

private theorem isOpenMap_sourceJointCoverExp (n : ℕ) :
    IsOpenMap (sourceJointCoverExp (n := n)) := by
  have hid : IsOpenMap
      (fun z : TorusCharacters.LogSpace n => z) := by
    intro s hs
    simpa only [image_id'] using hs
  change IsOpenMap (Prod.map
    (fun z : TorusCharacters.LogSpace n => z) Complex.exp)
  exact hid.prodMap Complex.isOpenMap_exp

private abbrev PositiveSourceJointComplexCover (n : ℕ) :=
  {q : SourceJointComplexCover n // 0 < sourceJointCoverTime q}

private def sourcePositiveCoverExp {n : ℕ}
    (q : PositiveSourceJointComplexCover n) :
    PositiveJointLogSpace n :=
  sourceJointExpPositiveLift q.val q.property

private theorem continuous_sourcePositiveCoverExp (n : ℕ) :
    Continuous (sourcePositiveCoverExp (n := n)) := by
  apply Continuous.subtype_mk
  exact (continuous_sourceJointCoverExp n).comp
    continuous_subtype_val

private theorem isOpen_sourcePositiveCover (n : ℕ) :
    IsOpen
      {q : SourceJointComplexCover n | 0 < sourceJointCoverTime q} := by
  exact isOpen_Ioi.preimage (continuous_sourceJointCoverTime n)

private theorem isOpenMap_sourcePositiveCoverExp (n : ℕ) :
    IsOpenMap (sourcePositiveCoverExp (n := n)) := by
  let s : Set (SourceJointComplexCover n) :=
    {q | 0 < sourceJointCoverTime q}
  have hs : IsOpen s := isOpen_sourcePositiveCover n
  have hr : IsOpenMap (fun q : s => sourceJointCoverExp q.val) :=
    (isOpenMap_sourceJointCoverExp n).comp hs.isOpenMap_subtype_val
  have hlands : ∀ q : s,
      sourceJointCoverExp q.val ∈ positiveJointDomain n := by
    intro q
    change 1 < Complex.normSq (sourceJointCoverExp q.val).2
    rw [normSq_sourceJointCoverExp]
    simpa only [Real.one_lt_exp_iff, Real.exp_zero] using (Real.exp_lt_exp.mpr q.property)
  exact hr.subtype_mk hlands

private def sourceJointCoverCirclePoint
    {n : ℕ} (q v : SourceJointComplexCover n)
    (R θ : ℝ) : SourceJointComplexCover n :=
  q + circleMap 0 R θ • v

private theorem continuous_sourceJointCoverCirclePoint
    {n : ℕ} (q v : SourceJointComplexCover n) (R : ℝ) :
    Continuous (sourceJointCoverCirclePoint q v R) := by
  unfold sourceJointCoverCirclePoint
  fun_prop

private theorem tendsto_sourceJointCoverCirclePoint
    {n : ℕ} (q : ℕ → SourceJointComplexCover n)
    (q₀ : SourceJointComplexCover n)
    (hq : Tendsto q atTop (𝓝 q₀))
    (v : SourceJointComplexCover n) (R θ : ℝ) :
    Tendsto
      (fun m : ℕ => sourceJointCoverCirclePoint (q m) v R θ)
      atTop
      (𝓝 (sourceJointCoverCirclePoint q₀ v R θ)) := by
  exact hq.add_const (circleMap 0 R θ • v)

private theorem circleAverage_sourceJointCover_eq
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Real.circleAverage
      (fun w : ℂ => u (q + w • v)) 0 R =
        (2 * Real.pi)⁻¹ *
          ∫ θ in 0..2 * Real.pi,
            u (sourceJointCoverCirclePoint q v R θ) := by
  rw [Real.circleAverage_def]
  rfl

private theorem circleIntegrable_sourceJointCover_of_continuous
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (hu : Continuous u)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    CircleIntegrable
      (fun w : ℂ => u (q + w • v)) 0 R := by
  rw [circleIntegrable_def]
  exact (hu.comp
    (continuous_sourceJointCoverCirclePoint q v R)).intervalIntegrable
      0 (2 * Real.pi)

private theorem circleIntegrable_sourceJointCover_of_upperSemicontinuous
    {n : ℕ} (u : SourceJointComplexCover n → ℝ)
    (hu : UpperSemicontinuous u)
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C) :
    CircleIntegrable
      (fun w : ℂ => u (q + w • v)) 0 R := by
  rw [circleIntegrable_def,
    intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le]
  change Integrable
    (fun θ : ℝ => u (sourceJointCoverCirclePoint q v R θ))
    (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
  have husc : UpperSemicontinuous
      (fun θ : ℝ =>
        u (sourceJointCoverCirclePoint q v R θ)) :=
    hu.comp (continuous_sourceJointCoverCirclePoint q v R)
  refine (integrable_const (|L| + |C|)).mono'
    husc.measurable.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun θ => by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · linarith [(hbound θ).1, neg_abs_le L, abs_nonneg C]
    · linarith [(hbound θ).2, le_abs_self C, abs_nonneg L]

private theorem circleAverage_sourceJointCover_mono
    {n : ℕ} (f u : SourceJointComplexCover n → ℝ)
    (hf : Continuous f) (hu : UpperSemicontinuous u)
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C)
    (hle : ∀ z : SourceJointComplexCover n, f z ≤ u z) :
    Real.circleAverage
      (fun w : ℂ => f (q + w • v)) 0 R ≤
    Real.circleAverage
      (fun w : ℂ => u (q + w • v)) 0 R := by
  apply Real.circleAverage_mono
    (circleIntegrable_sourceJointCover_of_continuous f hf q v R)
    (circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu q v R L C hbound)
  intro w _
  exact hle (q + w • v)

private theorem tendsto_circleAverage_sourceJointCover_of_dominated
    {n : ℕ}
    (u : ℕ → SourceJointComplexCover n → ℝ)
    (u₀ : SourceJointComplexCover n → ℝ)
    (hu : ∀ r : ℕ, UpperSemicontinuous (u r))
    (hpoint : ∀ z : SourceJointComplexCover n,
      Tendsto (fun r : ℕ => u r z) atTop (𝓝 (u₀ z)))
    (q v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hbound : ∀ (r : ℕ) (θ : ℝ),
      L ≤ u r (sourceJointCoverCirclePoint q v R θ) ∧
        u r (sourceJointCoverCirclePoint q v R θ) ≤ C) :
    Tendsto
      (fun r : ℕ =>
        Real.circleAverage
          (fun w : ℂ => u r (q + w • v)) 0 R)
      atTop
      (𝓝 (Real.circleAverage
        (fun w : ℂ => u₀ (q + w • v)) 0 R)) := by
  have hγ := continuous_sourceJointCoverCirclePoint q v R
  have hdom :
      Tendsto
        (fun r : ℕ => ∫ θ,
          u r (sourceJointCoverCirclePoint q v R θ)
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
        atTop
        (𝓝 (∫ θ,
          u₀ (sourceJointCoverCirclePoint q v R θ)
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))) := by
    apply MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ => |L| + |C|)
    · intro r
      exact ((hu r).comp hγ).measurable.aestronglyMeasurable
    · exact integrable_const (|L| + |C|)
    · intro r
      exact Filter.Eventually.of_forall fun θ => by
        rw [Real.norm_eq_abs]
        apply abs_le.mpr
        constructor
        · linarith [(hbound r θ).1,
            neg_abs_le L, abs_nonneg C]
        · linarith [(hbound r θ).2,
            le_abs_self C, abs_nonneg L]
    · exact Filter.Eventually.of_forall fun θ =>
        hpoint (sourceJointCoverCirclePoint q v R θ)
  have hinter :
      Tendsto
        (fun r : ℕ =>
          ∫ θ in 0..2 * Real.pi,
            u r (sourceJointCoverCirclePoint q v R θ))
        atTop
        (𝓝 (∫ θ in 0..2 * Real.pi,
          u₀ (sourceJointCoverCirclePoint q v R θ))) := by
    simp_rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact hdom
  have hsource :
      (fun r : ℕ =>
        Real.circleAverage
          (fun w : ℂ => u r (q + w • v)) 0 R) =
        (fun r : ℕ =>
          (2 * Real.pi)⁻¹ *
            ∫ θ in 0..2 * Real.pi,
              u r (sourceJointCoverCirclePoint q v R θ)) := by
    funext r
    exact circleAverage_sourceJointCover_eq (u r) q v R
  have htarget :
      Real.circleAverage
        (fun w : ℂ => u₀ (q + w • v)) 0 R =
        (2 * Real.pi)⁻¹ *
          ∫ θ in 0..2 * Real.pi,
            u₀ (sourceJointCoverCirclePoint q v R θ) :=
    circleAverage_sourceJointCover_eq u₀ q v R
  rw [hsource, htarget]
  exact hinter.const_mul ((2 * Real.pi)⁻¹)

private theorem exists_sourceJointCoverCircle_uniform_bounds
    {n : ℕ}
    (a b : SourceJointComplexCover n → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    ∃ L C : ℝ,
      ∀ z : SourceJointComplexCover n,
        dist z q ≤ 1 →
          (L ≤ a z ∧ b z ≤ C) ∧
          ∀ θ : ℝ,
            L ≤ a (sourceJointCoverCirclePoint z v R θ) ∧
              b (sourceJointCoverCirclePoint z v R θ) ≤ C := by
  let S : ℝ := 1 + |R| * ‖v‖
  have hcompact :
      IsCompact (Metric.closedBall q S) :=
    isCompact_closedBall q S
  obtain ⟨L, hL⟩ := (hcompact.image ha).bddBelow
  obtain ⟨C, hC⟩ := (hcompact.image hb).bddAbove
  refine ⟨L, C, ?_⟩
  intro z hz
  have hzmem : z ∈ Metric.closedBall q S := by
    apply Metric.mem_closedBall.mpr
    dsimp [S]
    nlinarith [abs_nonneg R, norm_nonneg v,
      mul_nonneg (abs_nonneg R) (norm_nonneg v)]
  refine ⟨⟨hL ⟨_, hzmem, rfl⟩,
    hC ⟨_, hzmem, rfl⟩⟩, ?_⟩
  intro θ
  have hmem :
      sourceJointCoverCirclePoint z v R θ ∈
        Metric.closedBall q S := by
    apply Metric.mem_closedBall.mpr
    calc
      dist (sourceJointCoverCirclePoint z v R θ) q ≤
          dist (sourceJointCoverCirclePoint z v R θ) z +
            dist z q :=
        dist_triangle _ _ _
      _ = ‖circleMap 0 R θ • v‖ + dist z q := by
        simp only [sourceJointCoverCirclePoint, dist_eq_norm, add_sub_cancel_left]
      _ = |R| * ‖v‖ + dist z q := by
        rw [norm_smul, norm_circleMap_zero]
      _ ≤ S := by
        dsimp [S]
        linarith
  exact ⟨hL ⟨_, hmem, rfl⟩,
    hC ⟨_, hmem, rfl⟩⟩

private theorem sourceJointCover_complex_line_submean_of_convergent_finite_approximants
    {n : ℕ} {ι : Type*}
    (F : ι → SourceJointComplexCover n → ℝ)
    (hFcont : ∀ i : ι, Continuous (F i))
    (u : SourceJointComplexCover n → ℝ)
    (hu : UpperSemicontinuous u)
    (q : ℕ → SourceJointComplexCover n)
    (i : ℕ → ι)
    (q₀ : SourceJointComplexCover n)
    (hq : Tendsto q atTop (𝓝 q₀))
    (hvalue : Tendsto (fun m : ℕ => F (i m) (q m))
      atTop (𝓝 (u q₀)))
    (v : SourceJointComplexCover n) (R : ℝ)
    (L C : ℝ)
    (hflower : ∀ m : ℕ, L ≤ F (i m) (q m))
    (hbound : ∀ (m : ℕ) (θ : ℝ),
      L ≤ u (sourceJointCoverCirclePoint (q m) v R θ) ∧
        u (sourceJointCoverCirclePoint (q m) v R θ) ≤ C)
    (hbound₀ : ∀ θ : ℝ,
      L ≤ u (sourceJointCoverCirclePoint q₀ v R θ) ∧
        u (sourceJointCoverCirclePoint q₀ v R θ) ≤ C)
    (hle : ∀ (j : ι) (z : SourceJointComplexCover n),
      F j z ≤ u z)
    (hsubmean : ∀ m : ℕ,
      F (i m) (q m) ≤
        Real.circleAverage
          (fun w : ℂ => F (i m) (q m + w • v)) 0 R) :
    u q₀ ≤
      Real.circleAverage
        (fun w : ℂ => u (q₀ + w • v)) 0 R := by
  let γ : ℕ → ℝ → SourceJointComplexCover n :=
    fun m θ => sourceJointCoverCirclePoint (q m) v R θ
  let γ₀ : ℝ → SourceJointComplexCover n :=
    fun θ => sourceJointCoverCirclePoint q₀ v R θ
  have hγ (m : ℕ) : Continuous (γ m) :=
    continuous_sourceJointCoverCirclePoint (q m) v R
  have hγ₀ : Continuous γ₀ :=
    continuous_sourceJointCoverCirclePoint q₀ v R
  have hγt (θ : ℝ) :
      Tendsto (fun m : ℕ => γ m θ) atTop (𝓝 (γ₀ θ)) :=
    tendsto_sourceJointCoverCirclePoint q q₀ hq v R θ
  have hangleint (m : ℕ) :
      IntervalIntegrable
        (fun θ : ℝ => u (γ m θ)) volume 0 (2 * Real.pi) := by
    have hc := circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu (q m) v R L C (hbound m)
    rw [circleIntegrable_def] at hc
    exact hc
  have hangleint₀ :
      IntervalIntegrable
        (fun θ : ℝ => u (γ₀ θ)) volume 0 (2 * Real.pi) := by
    have hc := circleIntegrable_sourceJointCover_of_upperSemicontinuous
      u hu q₀ v R L C hbound₀
    rw [circleIntegrable_def] at hc
    exact hc
  have havg (m : ℕ) :
      F (i m) (q m) ≤
        Real.circleAverage
          (fun w : ℂ => u (q m + w • v)) 0 R :=
    (hsubmean m).trans
      (circleAverage_sourceJointCover_mono
        (F (i m)) u (hFcont (i m)) hu
          (q m) v R L C (hbound m) (hle (i m)))
  have hscaled (m : ℕ) :
      (2 * Real.pi) * (F (i m) (q m) - L) ≤
        ∫ θ,
          u (γ m θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    have hm := havg m
    rw [circleAverage_sourceJointCover_eq
      u (q m) v R] at hm
    have hmdiv :
        F (i m) (q m) ≤
          (∫ θ in 0..2 * Real.pi,
            u (γ m θ)) / (2 * Real.pi) := by
      simpa only [mul_comm, div_eq_mul_inv, mul_inv_rev] using hm
    have hmprod :
        (2 * Real.pi) * F (i m) (q m) ≤
          ∫ θ in 0..2 * Real.pi, u (γ m θ) := by
      nlinarith [(le_div_iff₀ Real.two_pi_pos).mp hmdiv]
    rw [← intervalIntegral.integral_of_le Real.two_pi_pos.le,
      intervalIntegral.integral_sub
        (hangleint m) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const,
      sub_zero, smul_eq_mul]
    nlinarith
  have hshiftint (m : ℕ) :
      Integrable
        (fun θ : ℝ => u (γ m θ) - L)
        (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    have hmeas :
        Measurable (fun θ : ℝ => u (γ m θ) - L) :=
      (hu.comp (hγ m)).measurable.sub measurable_const
    refine (integrable_const (C - L)).mono'
      hmeas.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun θ => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr (hbound m θ).1)]
      exact sub_le_sub_right (hbound m θ).2 L
  have hintbound (m : ℕ) :
      (∫ θ,
        u (γ m θ) - L
          ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) ≤
        ∫ _ : ℝ, C - L
          ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
    integral_mono (hshiftint m) (integrable_const (C - L))
      (fun θ => sub_le_sub_right (hbound m θ).2 L)
  have hseqbdd :
      Filter.IsBoundedUnder (· ≤ ·) atTop
        (fun m : ℕ => ∫ θ,
          u (γ m θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi)))) :=
    Filter.isBoundedUnder_of_eventually_le
      (Filter.Eventually.of_forall hintbound)
  have hseqcob :
      Filter.IsCoboundedUnder (· ≤ ·) atTop
        (fun m : ℕ =>
          (2 * Real.pi) * (F (i m) (q m) - L)) :=
    Filter.isCoboundedUnder_le_of_le atTop
      (fun m => mul_nonneg Real.two_pi_pos.le
        (sub_nonneg.mpr (hflower m)))
  have hscaledtendsto :
      Tendsto
        (fun m : ℕ =>
          (2 * Real.pi) * (F (i m) (q m) - L))
        atTop (𝓝 ((2 * Real.pi) * (u q₀ - L))) :=
    (hvalue.sub tendsto_const_nhds).const_mul
      (2 * Real.pi)
  have hfatou :=
    limsup_integral_sub_const_le_of_upperSemicontinuous
      (volume.restrict (Set.Ioc 0 (2 * Real.pi)))
      u hu γ γ₀ hγ hγ₀ hγt L C
      (by
        intro m θ
        exact hbound m θ)
      (by
        intro θ
        exact hbound₀ θ)
  have hmain :
      (2 * Real.pi) * (u q₀ - L) ≤
        ∫ θ,
          u (γ₀ θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    calc
      (2 * Real.pi) * (u q₀ - L) =
          Filter.limsup
            (fun m : ℕ =>
              (2 * Real.pi) * (F (i m) (q m) - L)) atTop :=
        hscaledtendsto.limsup_eq.symm
      _ ≤ Filter.limsup
          (fun m : ℕ => ∫ θ,
            u (γ m θ) - L
              ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))))
            atTop :=
        Filter.limsup_le_limsup
          (Filter.Eventually.of_forall hscaled)
            hseqcob hseqbdd
      _ ≤ ∫ θ,
          u (γ₀ θ) - L
            ∂(volume.restrict (Set.Ioc 0 (2 * Real.pi))) :=
        hfatou
  have hmaininterval :
      (2 * Real.pi) * (u q₀ - L) ≤
        ∫ θ in 0..2 * Real.pi, u (γ₀ θ) - L := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    exact hmain
  rw [intervalIntegral.integral_sub
    hangleint₀ intervalIntegrable_const] at hmaininterval
  simp only [intervalIntegral.integral_const,
    sub_zero, smul_eq_mul] at hmaininterval
  rw [circleAverage_sourceJointCover_eq u q₀ v R]
  have hprod :
      (2 * Real.pi) * u q₀ ≤
        ∫ θ in 0..2 * Real.pi, u (γ₀ θ) := by
    nlinarith
  have hdiv :
      u q₀ ≤
        (∫ θ in 0..2 * Real.pi, u (γ₀ θ)) /
          (2 * Real.pi) := by
    apply (le_div_iff₀ Real.two_pi_pos).mpr
    nlinarith
  simpa only [mul_comm, mul_inv_rev, ge_iff_le, div_eq_mul_inv] using hdiv

private theorem sourceJointCover_upperRegularization_family_complex_line_submean_all_radius
    {n : ℕ} {ι : Type*} [Nonempty ι]
    (F : ι → SourceJointComplexCover n → ℝ)
    (hFcont : ∀ i : ι, Continuous (F i))
    (a b : SourceJointComplexCover n → ℝ)
    (ha : Continuous a) (hb : Continuous b)
    (hlower : ∀ (i : ι) (z : SourceJointComplexCover n),
      a z ≤ F i z)
    (hmajor : ∀ (i : ι) (z : SourceJointComplexCover n),
      F i z ≤ b z)
    (hsubmean : ∀ (i : ι) (z v : SourceJointComplexCover n)
      (R : ℝ),
      F i z ≤
        Real.circleAverage
          (fun w : ℂ => F i (z + w • v)) 0 R)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    upperRegularization
        (fun z : SourceJointComplexCover n =>
          sSup (Set.range fun i : ι => F i z)) q ≤
      Real.circleAverage
        (fun w : ℂ => upperRegularization
          (fun z : SourceJointComplexCover n =>
            sSup (Set.range fun i : ι => F i z))
              (q + w • v)) 0 R := by
  let f : SourceJointComplexCover n → ℝ :=
    fun z => sSup (Set.range fun i : ι => F i z)
  let u : SourceJointComplexCover n → ℝ :=
    upperRegularization f
  have hbounded (z : SourceJointComplexCover n) :
      BddAbove (Set.range fun i : ι => F i z) := by
    refine ⟨b z, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact hmajor i z
  have hfmajor (z : SourceJointComplexCover n) : f z ≤ b z := by
    apply csSup_le (Set.range_nonempty fun i : ι => F i z)
    rintro _ ⟨i, rfl⟩
    exact hmajor i z
  have hlocal (z : SourceJointComplexCover n) :
      (localUpperBounds f z).Nonempty :=
    localUpperBounds_nonempty_of_continuous_majorant
      f b hb hfmajor z
  have hu : UpperSemicontinuous u :=
    upperSemicontinuous_upperRegularization f hlocal
  have huupper (z : SourceJointComplexCover n) : u z ≤ b z :=
    upperRegularization_le_of_continuous_majorant
      f b hb hfmajor z
  have hfamily (i : ι) (z : SourceJointComplexCover n) :
      F i z ≤ u z := by
    calc
      F i z ≤ f z := le_csSup (hbounded z) ⟨i, rfl⟩
      _ ≤ u z := le_upperRegularization f z (hlocal z)
  have hulower (z : SourceJointComplexCover n) : a z ≤ u z := by
    let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
    exact (hlower i₀ z).trans (hfamily i₀ z)
  obtain ⟨L, C, hcompact⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds a b ha hb q v R
  have hcent :=
    tendsto_upperRegularizationFamilyApproximant_center F q
  have hval :=
    tendsto_upperRegularizationFamilyApproximant_value
      F q hbounded hlocal
  have hnear :
      ∀ᶠ m : ℕ in atTop,
        dist (upperRegularizationFamilyApproximant F q m).1 q < 1 :=
    Metric.tendsto_nhds.mp hcent 1 (by norm_num)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hnear
  let qseq : ℕ → SourceJointComplexCover n :=
    fun m => (upperRegularizationFamilyApproximant F q (m + N)).1
  let iseq : ℕ → ι :=
    fun m => (upperRegularizationFamilyApproximant F q (m + N)).2
  have hqseq : Tendsto qseq atTop (𝓝 q) :=
    hcent.comp (Filter.tendsto_add_atTop_nat N)
  have hseqvalue :
      Tendsto (fun m : ℕ => F (iseq m) (qseq m))
        atTop (𝓝 (u q)) :=
    hval.comp (Filter.tendsto_add_atTop_nat N)
  have hqnear (m : ℕ) : dist (qseq m) q ≤ 1 :=
    (hN (m + N) (by omega)).le
  have hqself : dist q q ≤ (1 : ℝ) := by simp only [dist_self, zero_le_one]
  have hflower (m : ℕ) : L ≤ F (iseq m) (qseq m) :=
    ((hcompact (qseq m) (hqnear m)).1.1).trans
      (hlower (iseq m) (qseq m))
  have hbound (m : ℕ) (θ : ℝ) :
      L ≤ u (sourceJointCoverCirclePoint (qseq m) v R θ) ∧
        u (sourceJointCoverCirclePoint (qseq m) v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ :=
      (hcompact (qseq m) (hqnear m)).2 θ
    exact ⟨hlo.trans (hulower _),
      (huupper _).trans hup⟩
  have hbound₀ (θ : ℝ) :
      L ≤ u (sourceJointCoverCirclePoint q v R θ) ∧
        u (sourceJointCoverCirclePoint q v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ := (hcompact q hqself).2 θ
    exact ⟨hlo.trans (hulower _),
      (huupper _).trans hup⟩
  have hfinite (m : ℕ) :
      F (iseq m) (qseq m) ≤
        Real.circleAverage
          (fun w : ℂ => F (iseq m) (qseq m + w • v)) 0 R :=
    hsubmean (iseq m) (qseq m) v R
  exact sourceJointCover_complex_line_submean_of_convergent_finite_approximants
    F hFcont u hu qseq iseq q hqseq hseqvalue v R
    L C hflower hbound hbound₀ hfamily hfinite

end JetEnvelopeGlobalPlurisubharmonicClosure

namespace JetEnvelopeTrueRadialMollifier

open Set Filter Function MeasureTheory Metric
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)

private def sourceJointRadialNormSq {n : ℕ}
    (q : SourceJointComplexCover n) : ℝ :=
  (∑ i : Fin n, Complex.normSq (q.1 i)) + Complex.normSq q.2

private theorem contDiff_sourceJointRadialNormSq (n : ℕ) :
    ContDiff ℝ ∞ (sourceJointRadialNormSq (n := n)) := by
  unfold sourceJointRadialNormSq
  apply ContDiff.add
  · apply ContDiff.sum
    intro i _
    simp_rw [Complex.normSq_apply]
    have hz : ContDiff ℝ ∞
        (fun q : SourceJointComplexCover n => q.1 i) := by
      fun_prop
    exact ((Complex.reCLM.contDiff.comp hz).mul
      (Complex.reCLM.contDiff.comp hz)).add
        ((Complex.imCLM.contDiff.comp hz).mul
          (Complex.imCLM.contDiff.comp hz))
  · simp_rw [Complex.normSq_apply]
    have hz : ContDiff ℝ ∞
        (fun q : SourceJointComplexCover n => q.2) := by
      fun_prop
    exact ((Complex.reCLM.contDiff.comp hz).mul
      (Complex.reCLM.contDiff.comp hz)).add
        ((Complex.imCLM.contDiff.comp hz).mul
          (Complex.imCLM.contDiff.comp hz))

private theorem sourceJointRadialNormSq_coordinate_le {n : ℕ}
    (q : SourceJointComplexCover n) (i : Fin n) :
    Complex.normSq (q.1 i) ≤ sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  calc
    Complex.normSq (q.1 i) ≤
      ∑ j : Fin n, Complex.normSq (q.1 j) :=
        Finset.single_le_sum
          (fun j _ => Complex.normSq_nonneg (q.1 j))
          (Finset.mem_univ i)
    _ ≤ (∑ j : Fin n, Complex.normSq (q.1 j)) +
          Complex.normSq q.2 :=
        le_add_of_nonneg_right (Complex.normSq_nonneg q.2)

private theorem sourceJointRadialNormSq_auxiliary_le {n : ℕ}
    (q : SourceJointComplexCover n) :
    Complex.normSq q.2 ≤ sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  exact le_add_of_nonneg_left
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

private def sourceJointTrueRadialBump (n k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  Real.smoothTransition
    (1 - (((k + 1 : ℕ) : ℝ) ^ 2) * sourceJointRadialNormSq q)

private theorem contDiff_sourceJointTrueRadialBump (n k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialBump n k) := by
  unfold sourceJointTrueRadialBump
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub
      (contDiff_const.mul (contDiff_sourceJointRadialNormSq n)))

private theorem sourceJointTrueRadialBump_nonneg (n k : ℕ)
    (q : SourceJointComplexCover n) :
    0 ≤ sourceJointTrueRadialBump n k q :=
  Real.smoothTransition.nonneg _

private theorem support_sourceJointTrueRadialBump_subset_closedBall
    {n : ℕ} (k : ℕ) :
    Function.support (sourceJointTrueRadialBump n k) ⊆
      Metric.closedBall (0 : SourceJointComplexCover n)
        (1 / ((k + 1 : ℕ) : ℝ)) := by
  intro q hq
  have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  have harg :
      0 < 1 - (((k + 1 : ℕ) : ℝ) ^ 2) *
        sourceJointRadialNormSq q := by
    apply lt_of_not_ge
    intro h
    apply hq
    exact Real.smoothTransition.zero_iff_nonpos.mpr h
  have hrad :
      (((k + 1 : ℕ) : ℝ) ^ 2) * sourceJointRadialNormSq q < 1 := by
    linarith
  have hcoord (i : Fin n) :
      ‖q.1 i‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    have hs := sourceJointRadialNormSq_coordinate_le q i
    rw [Complex.normSq_eq_norm_sq] at hs
    have hsq :
        (((k + 1 : ℕ) : ℝ) * ‖q.1 i‖) ^ 2 < 1 := by
      rw [mul_pow]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hrad
    have hprod : 0 ≤ (((k + 1 : ℕ) : ℝ) * ‖q.1 i‖) :=
      mul_nonneg hk.le (norm_nonneg _)
    apply (le_div_iff₀ hk).mpr
    nlinarith
  have haux :
      ‖q.2‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    have hs := sourceJointRadialNormSq_auxiliary_le q
    rw [Complex.normSq_eq_norm_sq] at hs
    have hsq :
        (((k + 1 : ℕ) : ℝ) * ‖q.2‖) ^ 2 < 1 := by
      rw [mul_pow]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hs (sq_nonneg _)) hrad
    have hprod : 0 ≤ (((k + 1 : ℕ) : ℝ) * ‖q.2‖) :=
      mul_nonneg hk.le (norm_nonneg _)
    apply (le_div_iff₀ hk).mpr
    nlinarith
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def,
    max_le_iff]
  exact ⟨(pi_norm_le_iff_of_nonneg (by positivity)).mpr hcoord,
    haux⟩

private theorem hasCompactSupport_sourceJointTrueRadialBump (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialBump n k) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : SourceJointComplexCover n)
      (1 / ((k + 1 : ℕ) : ℝ)))
    (support_sourceJointTrueRadialBump_subset_closedBall k)

private def sourceJointTrueRadialBumpMass (n k : ℕ) : ℝ :=
  ∫ q : SourceJointComplexCover n,
    sourceJointTrueRadialBump n k q

private theorem sourceJointTrueRadialBumpMass_pos (n k : ℕ) :
    0 < sourceJointTrueRadialBumpMass n k := by
  unfold sourceJointTrueRadialBumpMass
  apply (contDiff_sourceJointTrueRadialBump n
    k).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_sourceJointTrueRadialBump n k)
    (fun q => sourceJointTrueRadialBump_nonneg n k q)
    (x := (0 : SourceJointComplexCover n))
  simp only [sourceJointTrueRadialBump, Nat.cast_add, Nat.cast_one, sourceJointRadialNormSq,
    Prod.fst_zero, Pi.zero_apply, map_zero, Finset.sum_const_zero, Prod.snd_zero, add_zero,
    mul_zero, sub_zero, Real.smoothTransition.one, ne_eq, one_ne_zero, not_false_eq_true]

private def sourceJointTrueRadialMollifier (n k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  sourceJointTrueRadialBump n k q / sourceJointTrueRadialBumpMass n k

private theorem contDiff_sourceJointTrueRadialMollifier (n k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialMollifier n k) := by
  unfold sourceJointTrueRadialMollifier
  exact (contDiff_sourceJointTrueRadialBump n k).div_const _

private theorem sourceJointTrueRadialMollifier_nonneg (n k : ℕ)
    (q : SourceJointComplexCover n) :
    0 ≤ sourceJointTrueRadialMollifier n k q :=
  div_nonneg (sourceJointTrueRadialBump_nonneg n k q)
    (sourceJointTrueRadialBumpMass_pos n k).le

private theorem support_sourceJointTrueRadialMollifier_subset_closedBall
    {n : ℕ} (k : ℕ) :
    Function.support (sourceJointTrueRadialMollifier n k) ⊆
      Metric.closedBall (0 : SourceJointComplexCover n)
        (1 / ((k + 1 : ℕ) : ℝ)) := by
  intro q hq
  apply support_sourceJointTrueRadialBump_subset_closedBall k
  intro hzero
  apply hq
  simp only [sourceJointTrueRadialMollifier, hzero, zero_div]

private theorem hasCompactSupport_sourceJointTrueRadialMollifier (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialMollifier n k) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : SourceJointComplexCover n)
      (1 / ((k + 1 : ℕ) : ℝ)))
    (support_sourceJointTrueRadialMollifier_subset_closedBall k)

private theorem integrable_sourceJointTrueRadialMollifier (n k : ℕ) :
    Integrable (sourceJointTrueRadialMollifier n k)
      (volume : Measure (SourceJointComplexCover n)) :=
  (contDiff_sourceJointTrueRadialMollifier n k).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_sourceJointTrueRadialMollifier n k)

private theorem integral_sourceJointTrueRadialMollifier (n k : ℕ) :
    (∫ q : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k q) = 1 := by
  unfold sourceJointTrueRadialMollifier
  rw [integral_div]
  change sourceJointTrueRadialBumpMass n k /
    sourceJointTrueRadialBumpMass n k = 1
  exact div_self (ne_of_gt (sourceJointTrueRadialBumpMass_pos n k))

private theorem tendsto_sourceJointTrueRadialRadius :
    Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one, one_div] using
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

private theorem sourceJointRadialNormSq_phase {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (q : SourceJointComplexCover n) :
    sourceJointRadialNormSq (u • q) = sourceJointRadialNormSq q := by
  unfold sourceJointRadialNormSq
  change
    (∑ i : Fin n, Complex.normSq (u * q.1 i)) +
      Complex.normSq (u * q.2) =
    (∑ i : Fin n, Complex.normSq (q.1 i)) + Complex.normSq q.2
  simp_rw [normSq_mul_of_norm_one u hu]

private theorem sourceJointTrueRadialBump_phase {n : ℕ}
    (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : SourceJointComplexCover n) :
    sourceJointTrueRadialBump n k (u • q) =
      sourceJointTrueRadialBump n k q := by
  simp only [sourceJointTrueRadialBump, Nat.cast_add, Nat.cast_one,
    sourceJointRadialNormSq_phase u hu q]

private theorem sourceJointTrueRadialMollifier_phase {n : ℕ}
    (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : SourceJointComplexCover n) :
    sourceJointTrueRadialMollifier n k (u • q) =
      sourceJointTrueRadialMollifier n k q := by
  simp only [sourceJointTrueRadialMollifier, sourceJointTrueRadialBump_phase k u hu q]

private theorem measurePreserving_sourceJointComplexPhase {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun q : SourceJointComplexCover n => u • q)
      (volume : Measure (SourceJointComplexCover n))
      (volume : Measure (SourceJointComplexCover n)) := by
  have hc : MeasurePreserving (fun z : ℂ => u * z)
      (volume : Measure ℂ) (volume : Measure ℂ) := by
    let a : Circle :=
      ⟨u, by simpa only [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk,
        mem_sphere_iff_norm,
               sub_zero] using hu⟩
    have hrotation : MeasurePreserving (rotation a)
        (volume : Measure ℂ) (volume : Measure ℂ) :=
      (rotation a).measurePreserving
    change MeasurePreserving (rotation a)
      (volume : Measure ℂ) (volume : Measure ℂ)
    exact hrotation
  have hp : MeasurePreserving
      (fun z : Fin n → ℂ => fun i => u * z i)
      (volume : Measure (Fin n → ℂ))
      (volume : Measure (Fin n → ℂ)) := by
    exact MeasureTheory.measurePreserving_pi
      (fun _ : Fin n => (volume : Measure ℂ))
      (fun _ : Fin n => (volume : Measure ℂ))
      (fun _ => hc)
  exact hp.prod hc

private theorem measurableEmbedding_sourceJointComplexPhase {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurableEmbedding
      (fun q : SourceJointComplexCover n => u • q) := by
  let a : Circle :=
    ⟨u, by simpa only [Submonoid.unitSphere, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_sphere_iff_norm,
             sub_zero] using hu⟩
  let e : ℂ ≃ᵐ ℂ :=
    (rotation a).toHomeomorph.toMeasurableEquiv
  let ep : (Fin n → ℂ) ≃ᵐ (Fin n → ℂ) :=
    MeasurableEquiv.piCongrRight (fun _ : Fin n => e)
  let ej : SourceJointComplexCover n ≃ᵐ
      SourceJointComplexCover n := ep.prodCongr e
  exact ej.measurableEmbedding

private theorem integral_sourceJointComplexPhase {n : ℕ}
    (u : ℂ) (hu : ‖u‖ = 1)
    (g : SourceJointComplexCover n → ℝ) :
    (∫ y : SourceJointComplexCover n, g (u • y)) =
      ∫ y : SourceJointComplexCover n, g y :=
  (measurePreserving_sourceJointComplexPhase u hu).integral_comp
    (measurableEmbedding_sourceJointComplexPhase u hu) g

private def sourceJointTrueRadialSmoothed {n : ℕ}
    (f : SourceJointComplexCover n → ℝ) (k : ℕ) :
    SourceJointComplexCover n → ℝ :=
  sourceJointTrueRadialMollifier n k
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (SourceJointComplexCover n))] f

private theorem integrable_sourceJointTrueRadialMollifier_mul_translate
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) (q : SourceJointComplexCover n) :
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y * f (q - y))
      (volume : Measure (SourceJointComplexCover n)) := by
  have h :=
    (hasCompactSupport_sourceJointTrueRadialMollifier n k).convolutionExists_left
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (contDiff_sourceJointTrueRadialMollifier n k).continuous hf q
  refine h.integrable.congr
    (Filter.Eventually.of_forall fun y => ?_)
  change sourceJointTrueRadialMollifier n k y * f (q - y) =
    sourceJointTrueRadialMollifier n k y * f (q - y)
  rfl

private theorem eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (q : SourceJointComplexCover n)
    (hupper : UpperSemicontinuousAt f q)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop,
      sourceJointTrueRadialSmoothed f k q ≤ f q + ε := by
  have hnear : ∀ᶠ z : SourceJointComplexCover n in 𝓝 q,
      f z < f q + ε :=
    hupper (f q + ε) (lt_add_of_pos_right _ hε)
  obtain ⟨δ, hδ, hlocal⟩ := Metric.eventually_nhds_iff.mp hnear
  have hradius :
      ∀ᶠ k : ℕ in atTop,
        1 / ((k + 1 : ℕ) : ℝ) < δ :=
    tendsto_sourceJointTrueRadialRadius (Iio_mem_nhds hδ)
  filter_upwards [hradius] with k hk
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y * f (q - y)
      ∂(volume : Measure (SourceJointComplexCover n))) ≤
        ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y * (f q + ε)
          ∂(volume : Measure (SourceJointComplexCover n)) := by
      apply MeasureTheory.integral_mono
        (integrable_sourceJointTrueRadialMollifier_mul_translate
          hf k q)
        ((integrable_sourceJointTrueRadialMollifier n k).mul_const
          (f q + ε))
      intro y
      by_cases hy : sourceJointTrueRadialMollifier n k y = 0
      · simp only [hy, zero_mul, Std.le_refl]
      · have hball :=
          support_sourceJointTrueRadialMollifier_subset_closedBall k hy
        have hnorm : ‖y‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
          simpa only [Nat.cast_add, Nat.cast_one, one_div, mem_closedBall, dist_zero_right]
            using hball
        have hdist : dist (q - y) q < δ := by
          have hsmall := hnorm.trans_lt hk
          simpa only [sub_eq_add_neg, dist_eq_norm, add_comm, add_left_comm,
            add_neg_cancel_left, norm_neg,
            gt_iff_lt] using hsmall
        exact mul_le_mul_of_nonneg_left
          (hlocal hdist).le
          (sourceJointTrueRadialMollifier_nonneg n k y)
    _ = f q + ε := by
      rw [MeasureTheory.integral_mul_const,
        integral_sourceJointTrueRadialMollifier, one_mul]

private theorem tendsto_sourceJointTrueRadialSmoothed_of_upperSemicontinuousAt_and_le
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (q : SourceJointComplexCover n)
    (hupper : UpperSemicontinuousAt f q)
    (hlower : ∀ k : ℕ, f q ≤ sourceJointTrueRadialSmoothed f k q) :
    Tendsto (fun k : ℕ => sourceJointTrueRadialSmoothed f k q)
      atTop (𝓝 (f q)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall
      (fun k => lt_of_lt_of_le hb (hlower k))
  · intro b hb
    have hε : 0 < (b - f q) / 2 := by linarith
    filter_upwards
      [eventually_sourceJointTrueRadialSmoothed_le_of_upperSemicontinuousAt
        hf q hupper hε] with k hk
    linarith

private theorem contDiff_sourceJointTrueRadialSmoothed {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) :
    ContDiff ℝ ∞ (sourceJointTrueRadialSmoothed f k) := by
  exact (hasCompactSupport_sourceJointTrueRadialMollifier n k).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (contDiff_sourceJointTrueRadialMollifier n k) hf

private theorem sourceJointTrueRadialSmoothed_periodic {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    {d : SourceJointComplexCover n}
    (hf : Function.Periodic f d)
    (k : ℕ) :
    Function.Periodic (sourceJointTrueRadialSmoothed f k) d := by
  intro x
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with y
  change
    sourceJointTrueRadialMollifier n k y * f (x + d - y) =
      sourceJointTrueRadialMollifier n k y * f (x - y)
  rw [show x + d - y = (x - y) + d by abel,
    hf (x - y)]

end JetEnvelopeTrueRadialMollifier

namespace JetEnvelopeTrueRadialHessian

open Set Filter Function MeasureTheory Metric Matrix
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators Topology ENNReal InnerProductSpace Convolution ContDiff

/-- Differentiate a parameterized interval integral under joint continuity. -/
public
theorem hasDerivAt_intervalIntegral_of_joint_continuous
    (F F' : ℝ → ℝ → ℝ)
    (hF : Continuous (Function.uncurry F))
    (hF' : Continuous (Function.uncurry F'))
    (hdiff : ∀ x θ : ℝ,
      HasDerivAt (fun r : ℝ => F r θ) (F' x θ) x)
    (x₀ a b : ℝ) :
    HasDerivAt
      (fun x : ℝ => ∫ θ in a..b, F x θ)
      (∫ θ in a..b, F' x₀ θ) x₀ := by
  have hFslice (x : ℝ) : Continuous (F x) := by
    change Continuous (fun θ : ℝ => (Function.uncurry F) (x, θ))
    fun_prop
  have hF'slice (x : ℝ) : Continuous (F' x) := by
    change Continuous (fun θ : ℝ => (Function.uncurry F') (x, θ))
    fun_prop
  obtain ⟨C, hC⟩ :=
    (((isCompact_closedBall x₀ (1 : ℝ)).prod
      (isCompact_uIcc : IsCompact (Set.uIcc a b))).image
        hF'.norm).bddAbove
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ))
    (s := Metric.closedBall x₀ (1 : ℝ))
    (bound := fun _ : ℝ => C)
    (Metric.closedBall_mem_nhds x₀ (by norm_num))
    (Eventually.of_forall fun x =>
      (hFslice x).measurable.aestronglyMeasurable)
    ((hFslice x₀).intervalIntegrable a b)
    ((hF'slice x₀).measurable.aestronglyMeasurable)
    (Eventually.of_forall fun θ hθ x hx =>
      hC ⟨(x, θ), ⟨hx, Set.uIoc_subset_uIcc hθ⟩, rfl⟩)
    ((continuous_const : Continuous (fun _ : ℝ => C)).intervalIntegrable
      a b)
    (Eventually.of_forall fun θ _ x _ => hdiff x θ)).2

private theorem sourceJoint_ofReal_smul {n : ℕ}
    (r : ℝ) (v : SourceJointComplexCover n) :
    (r : ℂ) • v = r • v := by
  apply Prod.ext
  · funext i
    change (r : ℂ) * v.1 i = r • v.1 i
    simp only [Complex.real_smul]
  · change (r : ℂ) * v.2 = r • v.2
    simp only [Complex.real_smul]

private theorem sourceJointCircleMap_radius_smul {n : ℕ}
    (v : SourceJointComplexCover n) (r θ : ℝ) :
    circleMap 0 r θ • v = r • (circleMap 0 1 θ • v) := by
  simp only [circleMap, zero_add]
  simpa only [Complex.ofReal_one, one_mul, Complex.real_smul] using
    (smul_assoc r (Complex.exp ((θ : ℂ) * Complex.I)) v)

private theorem sourceJointCircleMap_unit_direction {n : ℕ}
    (v : SourceJointComplexCover n) (θ : ℝ) :
    circleMap 0 1 θ • v =
      Real.cos θ • v + Real.sin θ • (Complex.I • v) := by
  have hcircle : circleMap 0 1 θ =
      Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, Complex.ofReal_one, one_mul, zero_add]
  rw [hcircle, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos θ, ← Complex.ofReal_sin θ,
    add_smul, ← smul_smul,
    sourceJoint_ofReal_smul (Real.cos θ) v,
    sourceJoint_ofReal_smul (Real.sin θ) (Complex.I • v)]

private theorem hasDerivAt_sourceJointRealAffine {n : ℕ}
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => q + x • d) d r := by
  simpa only [hasDerivAt_const_add_iff, id_eq,
    one_smul] using ((hasDerivAt_id r).smul_const d).const_add q

private theorem hasDerivAt_sourceJointCircleLine {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => f (q + x • d))
      ((fderiv ℝ f (q + r • d)) d) r := by
  exact ((hf.differentiable (by norm_num) (q + r • d)).hasFDerivAt).comp_hasDerivAt
    r (hasDerivAt_sourceJointRealAffine q d r)

private theorem hasDerivAt_sourceJointCircleLineDerivative {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q d : SourceJointComplexCover n) (r : ℝ) :
    HasDerivAt (fun x : ℝ => (fderiv ℝ f (q + x • d)) d)
      (((fderiv ℝ (fderiv ℝ f) (q + r • d)) d) d) r := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have heval : HasFDerivAt
      (fun y : SourceJointComplexCover n => (fderiv ℝ f y) d)
      ((ContinuousLinearMap.apply ℝ ℝ d).comp
        (fderiv ℝ (fderiv ℝ f) (q + r • d)))
      (q + r • d) := by
    exact (ContinuousLinearMap.apply ℝ ℝ d).hasFDerivAt.comp
      (q + r • d)
      (hfd.differentiable (by norm_num) (q + r • d)).hasFDerivAt
  have hcomp : HasDerivAt
      ((fun y : SourceJointComplexCover n => (fderiv ℝ f y) d) ∘
        (fun x : ℝ => q + x • d))
      (((ContinuousLinearMap.apply ℝ ℝ d).comp
        (fderiv ℝ (fderiv ℝ f) (q + r • d))) d) r := by
    exact heval.comp_hasDerivAt r
      (hasDerivAt_sourceJointRealAffine q d r)
  refine (hcomp.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
  rfl

private theorem local_min_second_derivative_nonnegative
    {g : ℝ → ℝ} {r : ℝ}
    (hmin : IsLocalMin g r)
    (hc : ContinuousAt g r) :
    0 ≤ deriv (deriv g) r := by
  by_contra h
  have hneg : deriv (deriv g) r < 0 := lt_of_not_ge h
  have hzero : deriv g r = 0 := hmin.deriv_eq_zero
  have hmax : IsLocalMax g r :=
    isLocalMax_of_deriv_deriv_neg hneg hzero hc
  have heq : g =ᶠ[𝓝 r] (fun _ : ℝ => g r) := by
    filter_upwards [hmin, hmax] with x hxmin hxmax
    exact le_antisymm hxmax hxmin
  have hsecond : deriv (deriv g) r = 0 := by
    have hd := heq.deriv.deriv_eq
    simpa only [deriv_const'] using hd
  linarith

private def sourceJointCircleRadiusProfile {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) (r : ℝ) : ℝ :=
  Real.circleAverage (fun w : ℂ => f (q + w • v)) 0 r

private theorem continuous_sourceJointCircleRadiusProfile {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : Continuous f)
    (q v : SourceJointComplexCover n) :
    Continuous (sourceJointCircleRadiusProfile f q v) := by
  let F : ℝ → ℝ → ℝ :=
    fun r θ => f (q + circleMap 0 r θ • v)
  have hjoint : Continuous (Function.uncurry F) := by
    dsimp [F, Function.uncurry]
    fun_prop
  have hint :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := (volume : Measure ℝ)) hjoint 0 (2 * Real.pi)
  unfold sourceJointCircleRadiusProfile
  simp_rw [Real.circleAverage_def]
  change Continuous
    (fun r : ℝ => (2 * Real.pi)⁻¹ •
      ∫ θ in 0..2 * Real.pi, F r θ)
  exact hint.fun_const_smul ((2 * Real.pi)⁻¹)

private theorem sourceJointCircleRadiusProfile_zero {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) :
    sourceJointCircleRadiusProfile f q v 0 = f q := by
  simp only [sourceJointCircleRadiusProfile, Real.circleAverage_zero, zero_smul, add_zero]

private theorem sourceJointCircleRadiusProfile_second_eq_integral
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n) :
    deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 =
      (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi,
          ((fderiv ℝ (fderiv ℝ f) q)
            (circleMap 0 1 θ • v))
              (circleMap 0 1 θ • v) := by
  let d : ℝ → SourceJointComplexCover n :=
    fun θ => circleMap 0 1 θ • v
  let F : ℝ → ℝ → ℝ :=
    fun r θ => f (q + r • d θ)
  let F' : ℝ → ℝ → ℝ :=
    fun r θ => (fderiv ℝ f (q + r • d θ)) (d θ)
  let F'' : ℝ → ℝ → ℝ :=
    fun r θ =>
      ((fderiv ℝ (fderiv ℝ f) (q + r • d θ)) (d θ)) (d θ)
  have hd : Continuous d := by
    dsimp [d]
    fun_prop
  have hpoint :
      Continuous (fun x : ℝ × ℝ => q + x.1 • d x.2) := by
    have heq :
        (fun x : ℝ × ℝ => q + x.1 • d x.2) =
          (fun x : ℝ × ℝ => q + circleMap 0 x.1 x.2 • v) := by
      funext x
      change q + x.1 • (circleMap 0 1 x.2 • v) =
        q + circleMap 0 x.1 x.2 • v
      exact congrArg
        (fun w : SourceJointComplexCover n => q + w)
        (sourceJointCircleMap_radius_smul v x.1 x.2).symm
    rw [heq]
    fun_prop
  have hdir : Continuous (fun x : ℝ × ℝ => d x.2) :=
    hd.comp continuous_snd
  have hF : Continuous (Function.uncurry F) := by
    change Continuous (fun x : ℝ × ℝ => f (q + x.1 • d x.2))
    exact hf.continuous.comp hpoint
  have hF' : Continuous (Function.uncurry F') := by
    change Continuous
      (fun x : ℝ × ℝ =>
        (fderiv ℝ f (q + x.1 • d x.2)) (d x.2))
    exact ((hf.continuous_fderiv (by norm_num)).comp hpoint).clm_apply hdir
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (by norm_num)
  have hF'' : Continuous (Function.uncurry F'') := by
    change Continuous
      (fun x : ℝ × ℝ =>
        ((fderiv ℝ (fderiv ℝ f) (q + x.1 • d x.2))
          (d x.2)) (d x.2))
    exact (((hfd.continuous_fderiv (by norm_num)).comp hpoint).clm_apply
      hdir).clm_apply hdir
  have hdiff (r θ : ℝ) :
      HasDerivAt (fun x : ℝ => F x θ) (F' r θ) r := by
    exact hasDerivAt_sourceJointCircleLine hf q (d θ) r
  have hdiff' (r θ : ℝ) :
      HasDerivAt (fun x : ℝ => F' x θ) (F'' r θ) r := by
    exact hasDerivAt_sourceJointCircleLineDerivative hf q (d θ) r
  have hI (r : ℝ) :
      HasDerivAt
        (fun x : ℝ => ∫ θ in 0..2 * Real.pi, F x θ)
        (∫ θ in 0..2 * Real.pi, F' r θ) r :=
    hasDerivAt_intervalIntegral_of_joint_continuous
      F F' hF hF' hdiff r 0 (2 * Real.pi)
  have hI' (r : ℝ) :
      HasDerivAt
        (fun x : ℝ => ∫ θ in 0..2 * Real.pi, F' x θ)
        (∫ θ in 0..2 * Real.pi, F'' r θ) r :=
    hasDerivAt_intervalIntegral_of_joint_continuous
      F' F'' hF' hF'' hdiff' r 0 (2 * Real.pi)
  have hprofile :
      sourceJointCircleRadiusProfile f q v =
        fun r : ℝ =>
          (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, F r θ := by
    funext r
    simp only [sourceJointCircleRadiusProfile, Real.circleAverage_def,
      smul_eq_mul]
    congr 1
    apply intervalIntegral.integral_congr
    intro θ _
    change f (q + circleMap 0 r θ • v) =
      f (q + r • (circleMap 0 1 θ • v))
    rw [sourceJointCircleMap_radius_smul]
  have hfirst :
      deriv (sourceJointCircleRadiusProfile f q v) =
        fun r : ℝ =>
          (2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, F' r θ := by
    funext r
    rw [hprofile]
    exact ((hI r).const_mul ((2 * Real.pi)⁻¹)).deriv
  rw [hfirst]
  calc
    _ = (2 * Real.pi)⁻¹ *
        ∫ θ in 0..2 * Real.pi, F'' 0 θ :=
      ((hI' 0).const_mul ((2 * Real.pi)⁻¹)).deriv
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      change
        ((fderiv ℝ (fderiv ℝ f) (q + (0 : ℝ) • d θ))
          (d θ)) (d θ) =
        ((fderiv ℝ (fderiv ℝ f) q) (d θ)) (d θ)
      have hz : (0 : ℝ) • d θ =
          (0 : SourceJointComplexCover n) := by
        change (0 : ℂ) • d θ = 0
        exact zero_smul ℂ (d θ)
      rw [hz, add_zero]

private theorem sourceJointCircleQuadratic_expand {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (v : SourceJointComplexCover n) (θ : ℝ) :
    (B (circleMap 0 1 θ • v)) (circleMap 0 1 θ • v) =
      Real.cos θ ^ 2 * (B v v) +
        (Real.sin θ * Real.cos θ) *
          (B v (Complex.I • v) + B (Complex.I • v) v) +
        Real.sin θ ^ 2 * (B (Complex.I • v) (Complex.I • v)) := by
  rw [sourceJointCircleMap_unit_direction]
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply, smul_eq_mul]
  ring

private theorem sourceJointIntegral_cos_sq_two_pi :
    (∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2) = Real.pi := by
  rw [integral_cos_sq]
  simp only [Real.cos_two_pi, Real.sin_two_pi, mul_zero, Real.cos_zero, Real.sin_zero, sub_self,
    zero_add, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]

private theorem sourceJointIntegral_sin_sq_two_pi :
    (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 2) = Real.pi := by
  rw [integral_sin_sq]
  simp only [Real.sin_zero, Real.cos_zero, mul_one, Real.sin_two_pi, Real.cos_two_pi, sub_self,
    zero_add, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]

private theorem sourceJointIntegral_sin_mul_cos_two_pi :
    (∫ θ in 0..2 * Real.pi,
      Real.sin θ * Real.cos θ) = 0 := by
  rw [integral_sin_mul_cos₁]
  simp only [Real.sin_two_pi, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Real.sin_zero, sub_self, zero_div]

private theorem sourceJointCircleQuadratic_average {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (v : SourceJointComplexCover n) :
    (2 * Real.pi)⁻¹ *
      (∫ θ in 0..2 * Real.pi,
        (B (circleMap 0 1 θ • v)) (circleMap 0 1 θ • v)) =
      ((B v v) + (B (Complex.I • v) (Complex.I • v))) / 2 := by
  let A : ℝ := B v v
  let C : ℝ := B v (Complex.I • v) + B (Complex.I • v) v
  let D : ℝ := B (Complex.I • v) (Complex.I • v)
  have hA : IntervalIntegrable
      (fun θ : ℝ => Real.cos θ ^ 2 * A)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hC : IntervalIntegrable
      (fun θ : ℝ => (Real.sin θ * Real.cos θ) * C)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hD : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ ^ 2 * D)
      (volume : Measure ℝ) 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    fun_prop
  calc
    _ = (2 * Real.pi)⁻¹ *
      (∫ θ in 0..2 * Real.pi,
        (Real.cos θ ^ 2 * A +
          (Real.sin θ * Real.cos θ) * C +
          Real.sin θ ^ 2 * D)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro θ _
      exact sourceJointCircleQuadratic_expand B v θ
    _ = (2 * Real.pi)⁻¹ *
      ((∫ θ in 0..2 * Real.pi, Real.cos θ ^ 2 * A) +
        (∫ θ in 0..2 * Real.pi,
          (Real.sin θ * Real.cos θ) * C) +
        (∫ θ in 0..2 * Real.pi, Real.sin θ ^ 2 * D)) := by
      rw [intervalIntegral.integral_add (hA.add hC) hD,
        intervalIntegral.integral_add hA hC]
    _ = (2 * Real.pi)⁻¹ *
      (Real.pi * A + 0 * C + Real.pi * D) := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        intervalIntegral.integral_mul_const,
        sourceJointIntegral_cos_sq_two_pi,
        sourceJointIntegral_sin_mul_cos_two_pi,
        sourceJointIntegral_sin_sq_two_pi]
    _ = _ := by
      dsimp [A, C, D]
      field_simp
      ring

private theorem sourceJointCircleRadiusProfile_second_eq_realHessian
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n) :
    deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 =
      (((fderiv ℝ (fderiv ℝ f) q) v) v +
        ((fderiv ℝ (fderiv ℝ f) q) (Complex.I • v))
          (Complex.I • v)) / 2 := by
  rw [sourceJointCircleRadiusProfile_second_eq_integral hf q v]
  exact sourceJointCircleQuadratic_average (fderiv ℝ (fderiv ℝ f) q) v

private def sourceJointRealLeviQuadratic {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n) : ℝ :=
  (((fderiv ℝ (fderiv ℝ f) q) v) v +
    ((fderiv ℝ (fderiv ℝ f) q) (Complex.I • v))
      (Complex.I • v)) / 4

end JetEnvelopeTrueRadialHessian

namespace JetEnvelopeTrueRadialComplexHessian

open Set Filter Function MeasureTheory Metric Matrix
open JetEnvelopeGlobalPlurisubharmonic EqualitySaturatingKillingPaths
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private theorem contDiff_sourceSpatialRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (u : TorusCharacters.LogSpace n) :
    ContDiff ℝ 1
      (fun z : TorusCharacters.LogSpace n =>
        (fderiv ℝ a z) u) := by
  exact (ha.fderiv_right (by norm_num)).clm_apply contDiff_const

private theorem fderiv_sourceSpatialRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z u w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ a ξ) u) z) w =
      ((fderiv ℝ (fderiv ℝ a) z) w) u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ a) z :=
    (ha.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) z
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := u))
  have happly := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] ℝ => L w)
    he
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using happly

private theorem fderiv_sourceSpatialComplexRealDirectional {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z u w : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        ((fderiv ℝ a ξ) u : ℂ)) z) w =
      (((fderiv ℝ (fderiv ℝ a) z) w) u : ℂ) := by
  rw [fderiv_complexOfReal
    ((contDiff_sourceSpatialRealDirectional ha u).differentiable
      (by norm_num))]
  rw [fderiv_sourceSpatialRealDirectional ha z u w]

private theorem fderiv_holomorphicCoordinate_sourceSpatialReal {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z w : TorusCharacters.LogSpace n)
    (i : Fin n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun p : TorusCharacters.LogSpace n => (a p : ℂ))
          ξ i) z) w =
      ((((fderiv ℝ (fderiv ℝ a) z) w)
          (Pi.single i (1 : ℂ)) : ℂ) -
        Complex.I *
          (((fderiv ℝ (fderiv ℝ a) z) w)
            (Pi.single i Complex.I) : ℂ)) / 2 := by
  let e : TorusCharacters.LogSpace n :=
    Pi.single i (1 : ℂ)
  let ie : TorusCharacters.LogSpace n :=
    Pi.single i Complex.I
  let g : TorusCharacters.LogSpace n → ℂ :=
    fun ξ => ((fderiv ℝ a ξ) e : ℂ)
  let h : TorusCharacters.LogSpace n → ℂ :=
    fun ξ => ((fderiv ℝ a ξ) ie : ℂ)
  have had : Differentiable ℝ a :=
    ha.differentiable (by norm_num)
  have hg : Differentiable ℝ g :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_sourceSpatialRealDirectional ha e)).differentiable
      (by norm_num)
  have hh : Differentiable ℝ h :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_sourceSpatialRealDirectional ha ie)).differentiable
      (by norm_num)
  have hfun :
      (fun ξ : TorusCharacters.LogSpace n =>
        holomorphicCoordinate
          (fun p : TorusCharacters.LogSpace n => (a p : ℂ))
          ξ i) =
      (fun ξ : TorusCharacters.LogSpace n =>
        (g ξ - Complex.I * h ξ) * ((2 : ℂ)⁻¹)) := by
    funext ξ
    unfold holomorphicCoordinate
    rw [fderiv_complexOfReal had ξ (Pi.single i (1 : ℂ)),
      fderiv_complexOfReal had ξ (Pi.single i Complex.I)]
    rfl
  rw [hfun]
  have hder :=
    ((hg z).hasFDerivAt.sub
      ((hh z).hasFDerivAt.const_mul Complex.I)).mul_const
      ((2 : ℂ)⁻¹)
  have heval := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] ℂ => L w)
    hder.fderiv
  calc
    _ = ((2 : ℂ)⁻¹) *
        ((fderiv ℝ g z) w -
          Complex.I * (fderiv ℝ h z) w) := by
      simpa only [Pi.sub_apply, _root_.smul_apply, _root_.sub_apply, smul_eq_mul]
        using heval
    _ = _ := by
      change
        ((2 : ℂ)⁻¹) *
          ((fderiv ℝ
              (fun ξ : TorusCharacters.LogSpace n =>
                ((fderiv ℝ a ξ) e : ℂ)) z) w -
            Complex.I * (fderiv ℝ
              (fun ξ : TorusCharacters.LogSpace n =>
                ((fderiv ℝ a ξ) ie : ℂ)) z) w) = _
      rw [fderiv_sourceSpatialComplexRealDirectional ha z e w,
        fderiv_sourceSpatialComplexRealDirectional ha z ie w]
      dsimp [e, ie]
      ring

private def sourceSpatialComplexHessianOfRealBilinear {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    (((B (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)) : ℝ) : ℂ) +
      ((B (Pi.single j Complex.I) (Pi.single i Complex.I) : ℝ) : ℂ) +
      Complex.I *
        (((B (Pi.single j Complex.I) (Pi.single i (1 : ℂ)) : ℝ) : ℂ) -
          ((B (Pi.single j (1 : ℂ)) (Pi.single i Complex.I) : ℝ) : ℂ))) /
      4

private theorem complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
    {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z : TorusCharacters.LogSpace n)
    (i j : Fin n) :
    complexHessian a z i j =
      sourceSpatialComplexHessianOfRealBilinear
        (fderiv ℝ (fderiv ℝ a) z) i j := by
  unfold sourceSpatialComplexHessianOfRealBilinear
  unfold complexHessian
  unfold barPartialCoordinate
  rw [fderiv_holomorphicCoordinate_sourceSpatialReal ha z
    (Pi.single j (1 : ℂ)) i,
    fderiv_holomorphicCoordinate_sourceSpatialReal ha z
      (Pi.single j Complex.I) i]
  linear_combination
    (-((((fderiv ℝ (fderiv ℝ a) z) (Pi.single j Complex.I))
        (Pi.single i Complex.I) : ℝ) : ℂ) / 4) * Complex.I_sq

private theorem sourceSpatialComplexHessianOfRealBilinear_isHermitian {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (hB : ∀ u v : TorusCharacters.LogSpace n,
      B u v = B v u) :
    (sourceSpatialComplexHessianOfRealBilinear B).IsHermitian := by
  change (sourceSpatialComplexHessianOfRealBilinear B)ᴴ =
    sourceSpatialComplexHessianOfRealBilinear B
  ext i j
  simp only [Matrix.conjTranspose_apply,
    sourceSpatialComplexHessianOfRealBilinear, Complex.star_def,
    map_div₀, map_add, map_sub, map_mul, map_ofNat,
    Complex.conj_ofReal, Complex.conj_I]
  rw [hB (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)),
    hB (Pi.single i Complex.I) (Pi.single j Complex.I),
    hB (Pi.single i Complex.I) (Pi.single j (1 : ℂ)),
    hB (Pi.single i (1 : ℂ)) (Pi.single j Complex.I)]
  ring

private theorem sourceCoverComplexHessian_isHermitian {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z : TorusCharacters.LogSpace n) :
    (sourceCoverComplexHessian a z).IsHermitian := by
  have hsym :
      ∀ u v : TorusCharacters.LogSpace n,
        ((fderiv ℝ (fderiv ℝ a) z) u) v =
          ((fderiv ℝ (fderiv ℝ a) z) v) u :=
    fun u v =>
      (ha.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v
  have hmatrix :
      sourceCoverComplexHessian a z =
        sourceSpatialComplexHessianOfRealBilinear
          (fderiv ℝ (fderiv ℝ a) z) := by
    ext i j
    exact complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j
  rw [hmatrix]
  exact sourceSpatialComplexHessianOfRealBilinear_isHermitian _ hsym

private def sourceJointSpatialSlice {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (τ : ℂ) (z : TorusCharacters.LogSpace n) : ℝ :=
  f (z, τ)

private theorem contDiff_sourceJointSpatialSlice {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ) :
    ContDiff ℝ 2 (sourceJointSpatialSlice f τ) := by
  exact hf.comp (contDiff_id.prodMk contDiff_const)

private theorem fderiv_sourceJointSpatialSlice_apply {n : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : SourceJointComplexCover n → F}
    (hf : Differentiable ℝ f)
    (τ : ℂ)
    (z v : TorusCharacters.LogSpace n) :
    (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n => f (ξ, τ)) z) v =
      (fderiv ℝ f (z, τ)) (v, 0) := by
  have hslice :=
    (hasFDerivAt_id (𝕜 := ℝ) z).prodMk
      (hasFDerivAt_const (𝕜 := ℝ) τ z)
  have hcomp := (hf (z, τ)).hasFDerivAt.comp z hslice
  have heval := congrArg
    (fun L : TorusCharacters.LogSpace n →L[ℝ] F => L v)
    hcomp.fderiv
  simpa only [id_eq, comp_def, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, _root_.zero_apply] using heval

private theorem fderiv_sourceJointRealDirectional {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q u w : SourceJointComplexCover n) :
    (fderiv ℝ
      (fun ξ : SourceJointComplexCover n => (fderiv ℝ f ξ) u) q) w =
      ((fderiv ℝ (fderiv ℝ f) q) w) u := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) q :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num) q
  have he := fderiv_clm_apply hd
    (differentiableAt_const (c := u))
  have happly := congrArg
    (fun L : SourceJointComplexCover n →L[ℝ] ℝ => L w) he
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] using happly

private theorem sndFDeriv_sourceJointSpatialSlice {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z v w : TorusCharacters.LogSpace n) :
    ((fderiv ℝ
      (fderiv ℝ (sourceJointSpatialSlice f τ)) z) w) v =
      ((fderiv ℝ (fderiv ℝ f) (z, τ)) (w, 0)) (v, 0) := by
  have hslice := contDiff_sourceJointSpatialSlice hf τ
  have hfirst :
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ (sourceJointSpatialSlice f τ) ξ) v) =
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ f (ξ, τ)) (v, 0)) := by
    funext ξ
    exact fderiv_sourceJointSpatialSlice_apply
      (hf.differentiable (by norm_num)) τ ξ v
  have hdirectional : Differentiable ℝ
      (fun q : SourceJointComplexCover n =>
        (fderiv ℝ f q) (v, 0)) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiff_const).differentiable (by norm_num)
  calc
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ (sourceJointSpatialSlice f τ) ξ) v) z) w :=
      (fderiv_sourceSpatialRealDirectional hslice z v w).symm
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ f (ξ, τ)) (v, 0)) z) w := by rw [hfirst]
    _ = (fderiv ℝ
      (fun q : SourceJointComplexCover n =>
        (fderiv ℝ f q) (v, 0)) (z, τ)) (w, 0) :=
      fderiv_sourceJointSpatialSlice_apply hdirectional τ z w
    _ = _ :=
      fderiv_sourceJointRealDirectional hf (z, τ) (v, 0) (w, 0)

private def sourceJointSpatialComplexHessian {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    Matrix (Fin n) (Fin n) ℂ :=
  sourceCoverComplexHessian (sourceJointSpatialSlice f τ) z

private theorem sourceJointSpatialComplexHessian_isHermitian {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    (sourceJointSpatialComplexHessian f τ z).IsHermitian := by
  unfold sourceJointSpatialComplexHessian
  exact sourceCoverComplexHessian_isHermitian
    (contDiff_sourceJointSpatialSlice hf τ) z

end JetEnvelopeTrueRadialComplexHessian

namespace JetEnvelopeTrueRadialComplexHessianPositivity

open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian SchurConvexity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private theorem sourceSpatialRealBasis_decomposition {n : ℕ}
    (x : TorusCharacters.LogSpace n) :
    x = ∑ i : Fin n,
      ((x i).re •
          (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
        (x i).im •
          (Pi.single i Complex.I : TorusCharacters.LogSpace n)) := by
  classical
  calc
    x = ∑ i : Fin n, Pi.single i (x i) :=
      (Finset.univ_sum_single x).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      ext j
      by_cases h : j = i
      · subst j
        simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one,
          Complex.re_add_im]
      · simp only [ne_eq, h, not_false_eq_true, Pi.single_eq_of_ne, Pi.add_apply, Pi.smul_apply,
          smul_zero, add_zero]

private theorem sourceSpatialRealBilinear_apply_eq_realBasis_sum {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (x y : TorusCharacters.LogSpace n) :
    B x y =
      ∑ i : Fin n, ∑ j : Fin n,
        ((x i).re * (y j).re *
          B (Pi.single i (1 : ℂ)) (Pi.single j (1 : ℂ)) +
         (x i).re * (y j).im *
          B (Pi.single i (1 : ℂ)) (Pi.single j Complex.I) +
         (x i).im * (y j).re *
          B (Pi.single i Complex.I) (Pi.single j (1 : ℂ)) +
         (x i).im * (y j).im *
          B (Pi.single i Complex.I) (Pi.single j Complex.I)) := by
  classical
  let u : Fin n → TorusCharacters.LogSpace n := fun i =>
    (x i).re •
        (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
      (x i).im •
        (Pi.single i Complex.I : TorusCharacters.LogSpace n)
  let v : Fin n → TorusCharacters.LogSpace n := fun j =>
    (y j).re •
        (Pi.single j (1 : ℂ) : TorusCharacters.LogSpace n) +
      (y j).im •
        (Pi.single j Complex.I : TorusCharacters.LogSpace n)
  have hx : x = ∑ i, u i := sourceSpatialRealBasis_decomposition x
  have hy : y = ∑ j, v j := sourceSpatialRealBasis_decomposition y
  calc
    B x y = B (∑ i, u i) (∑ j, v j) := by rw [← hx, ← hy]
    _ = ∑ i, B (u i) (∑ j, v j) := by
      simpa only [ContinuousLinearMap.flip_apply] using
        (map_sum (B.flip (∑ j, v j)) u Finset.univ)
    _ = ∑ i, ∑ j, B (u i) (v j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact map_sum (B (u i)) v Finset.univ
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [u, v]
      simp only [map_add, map_smul, _root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      ring

private theorem sourceSpatialComplexHessianOfRealBilinear_quadratic {n : ℕ}
    (B : TorusCharacters.LogSpace n →L[ℝ]
      TorusCharacters.LogSpace n →L[ℝ] ℝ)
    (hsymm : ∀ u v : TorusCharacters.LogSpace n,
      B u v = B v u)
    (x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ
        (sourceSpatialComplexHessianOfRealBilinear B *ᵥ x) =
      (((B (star x) (star x) +
        B (Complex.I • star x) (Complex.I • star x)) / 4 : ℝ) : ℂ) := by
  classical
  let Q : Fin n → Fin n → ℂ := fun i j =>
    star (x i) * (sourceSpatialComplexHessianOfRealBilinear B i j) * x j
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, Q i j) =
        ∑ i : Fin n, ∑ j : Fin n, Q j i := by
    rw [Finset.sum_comm]
  have havg :
      (∑ i : Fin n, ∑ j : Fin n, Q i j) =
        ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q j i) / 2 := by
    calc
      _ = ((∑ i : Fin n, ∑ j : Fin n, Q i j) +
        (∑ i : Fin n, ∑ j : Fin n, Q j i)) / 2 := by
          rw [← hswap]
          ring
      _ = _ := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_add_distrib, Finset.sum_div]
  calc
    _ = ∑ i : Fin n, ∑ j : Fin n, Q i j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [Q]
      ring
    _ = ∑ i : Fin n, ∑ j : Fin n, (Q i j + Q j i) / 2 :=
      havg
    _ = _ := by
      rw [sourceSpatialRealBilinear_apply_eq_realBasis_sum
          B (star x) (star x),
        sourceSpatialRealBilinear_apply_eq_realBasis_sum
          B (Complex.I • star x) (Complex.I • star x)]
      simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul,
        Complex.star_def, Complex.conj_re, Complex.conj_im,
        Complex.I_mul_re, Complex.I_mul_im]
      push_cast
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_add_distrib, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [Q, sourceSpatialComplexHessianOfRealBilinear]
      rw [hsymm (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)),
        hsymm (Pi.single j Complex.I) (Pi.single i Complex.I),
        hsymm (Pi.single j Complex.I) (Pi.single i (1 : ℂ)),
        hsymm (Pi.single j (1 : ℂ)) (Pi.single i Complex.I)]
      rw [← Complex.re_add_im (x i), ← Complex.re_add_im (x j)]
      simp only [map_add, map_mul,
        Complex.conj_ofReal, Complex.conj_I,
        Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im,
        mul_zero, mul_one,
        add_zero, zero_add, sub_zero]
      linear_combination
        ((-(((x i).im : ℂ) * ((x j).im : ℂ)) *
              ((((B (Pi.single i (1 : ℂ))) (Pi.single j (1 : ℂ)) : ℝ) : ℂ) +
                (((B (Pi.single i Complex.I)) (Pi.single j Complex.I) : ℝ) : ℂ)) +
            (((x i).re : ℂ) * ((x j).im : ℂ) -
                ((x i).im : ℂ) * ((x j).re : ℂ)) *
              ((((B (Pi.single i (1 : ℂ))) (Pi.single j Complex.I) : ℝ) : ℂ) -
                (((B (Pi.single i Complex.I)) (Pi.single j (1 : ℂ)) : ℝ) : ℂ))) / 4) *
          Complex.I_sq

private theorem sourceCoverComplexHessian_quadratic {n : ℕ}
    {a : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (z x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ (sourceCoverComplexHessian a z *ᵥ x) =
      (((((fderiv ℝ (fderiv ℝ a) z) (star x)) (star x) +
          ((fderiv ℝ (fderiv ℝ a) z) (Complex.I • star x))
            (Complex.I • star x)) / 4 : ℝ) : ℂ) := by
  have hsymm :
      ∀ u v : TorusCharacters.LogSpace n,
        ((fderiv ℝ (fderiv ℝ a) z) u) v =
          ((fderiv ℝ (fderiv ℝ a) z) v) u :=
    fun u v =>
      (ha.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq u v
  have hmatrix :
      sourceCoverComplexHessian a z =
        sourceSpatialComplexHessianOfRealBilinear
          (fderiv ℝ (fderiv ℝ a) z) := by
    ext i j
    exact complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j
  rw [hmatrix]
  exact sourceSpatialComplexHessianOfRealBilinear_quadratic
    (fderiv ℝ (fderiv ℝ a) z) hsymm x

private theorem sourceJointSpatialComplexHessian_quadratic_eq_realLevi
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (τ : ℂ)
    (z x : TorusCharacters.LogSpace n) :
    star x ⬝ᵥ (sourceJointSpatialComplexHessian f τ z *ᵥ x) =
      (sourceJointRealLeviQuadratic f (z, τ) (star x, 0) : ℂ) := by
  unfold sourceJointSpatialComplexHessian
  rw [sourceCoverComplexHessian_quadratic
    (contDiff_sourceJointSpatialSlice hf τ) z x]
  unfold sourceJointRealLeviQuadratic
  rw [sndFDeriv_sourceJointSpatialSlice hf τ z (star x) (star x),
    sndFDeriv_sourceJointSpatialSlice hf τ z
      (Complex.I • star x) (Complex.I • star x)]
  simp only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_ofNat, Prod.smul_mk,
    smul_eq_mul, mul_zero]

end JetEnvelopeTrueRadialComplexHessianPositivity

namespace JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite

open Set Function Matrix
open JetEnvelopeTrueRadialComplexHessian SchurConvexity WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Topology ContDiff

private theorem sndFDeriv_sourceSpatialRealAffine {n : ℕ}
    {a b : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b)
    (c d : ℝ)
    (z u v : TorusCharacters.LogSpace n) :
    ((fderiv ℝ
      (fderiv ℝ
        (fun ξ : TorusCharacters.LogSpace n =>
          c * a ξ + d * b ξ)) z) u) v =
      c * ((fderiv ℝ (fderiv ℝ a) z) u) v +
        d * ((fderiv ℝ (fderiv ℝ b) z) u) v := by
  have hda : Differentiable ℝ a :=
    ha.differentiable (by norm_num)
  have hdb : Differentiable ℝ b :=
    hb.differentiable (by norm_num)
  have hcomb : ContDiff ℝ 2
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) :=
    (contDiff_const.mul ha).add (contDiff_const.mul hb)
  have hfirst :
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ
          (fun η : TorusCharacters.LogSpace n =>
            c * a η + d * b η) ξ) v) =
      (fun ξ : TorusCharacters.LogSpace n =>
        c * (fderiv ℝ a ξ) v + d * (fderiv ℝ b ξ) v) := by
    funext ξ
    change (fderiv ℝ
      ((fun η : TorusCharacters.LogSpace n => c * a η) +
        (fun η : TorusCharacters.LogSpace n => d * b η))
      ξ) v = _
    rw [fderiv_add ((hda ξ).const_mul c) ((hdb ξ).const_mul d),
      fderiv_const_mul (hda ξ) c,
      fderiv_const_mul (hdb ξ) d]
    simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]
  have hga : Differentiable ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ a ξ) v) :=
    (contDiff_sourceSpatialRealDirectional ha v).differentiable
      (by norm_num)
  have hgb : Differentiable ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ b ξ) v) :=
    (contDiff_sourceSpatialRealDirectional hb v).differentiable
      (by norm_num)
  calc
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        (fderiv ℝ
          (fun η : TorusCharacters.LogSpace n =>
            c * a η + d * b η) ξ) v) z) u :=
      (fderiv_sourceSpatialRealDirectional hcomb z v u).symm
    _ = (fderiv ℝ
      (fun ξ : TorusCharacters.LogSpace n =>
        c * (fderiv ℝ a ξ) v + d * (fderiv ℝ b ξ) v) z) u := by
      rw [hfirst]
    _ = _ := by
      change (fderiv ℝ
        ((fun ξ : TorusCharacters.LogSpace n =>
          c * (fderiv ℝ a ξ) v) +
          (fun ξ : TorusCharacters.LogSpace n =>
            d * (fderiv ℝ b ξ) v)) z) u = _
      rw [fderiv_add ((hga z).const_mul c) ((hgb z).const_mul d),
        fderiv_const_mul (hga z) c,
        fderiv_const_mul (hgb z) d]
      simp only [_root_.add_apply,
        _root_.smul_apply, smul_eq_mul]
      rw [fderiv_sourceSpatialRealDirectional ha z v u,
        fderiv_sourceSpatialRealDirectional hb z v u]

private theorem sourceCoverComplexHessian_realAffine {n : ℕ}
    {a b : TorusCharacters.LogSpace n → ℝ}
    (ha : ContDiff ℝ 2 a)
    (hb : ContDiff ℝ 2 b)
    (c d : ℝ)
    (z : TorusCharacters.LogSpace n) :
    sourceCoverComplexHessian
        (fun ξ : TorusCharacters.LogSpace n =>
          c * a ξ + d * b ξ) z =
      c • sourceCoverComplexHessian a z +
        d • sourceCoverComplexHessian b z := by
  have hcomb : ContDiff ℝ 2
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) :=
    (contDiff_const.mul ha).add (contDiff_const.mul hb)
  ext i j
  change complexHessian
      (fun ξ : TorusCharacters.LogSpace n =>
        c * a ξ + d * b ξ) z i j =
    c • complexHessian a z i j + d • complexHessian b z i j
  rw [complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      hcomb z i j,
    complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      ha z i j,
    complexHessian_eq_sourceSpatialComplexHessianOfRealBilinear
      hb z i j]
  unfold sourceSpatialComplexHessianOfRealBilinear
  rw [sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j (1 : ℂ)) (Pi.single i (1 : ℂ)),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j Complex.I) (Pi.single i Complex.I),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j Complex.I) (Pi.single i (1 : ℂ)),
    sndFDeriv_sourceSpatialRealAffine ha hb c d z
      (Pi.single j (1 : ℂ)) (Pi.single i Complex.I)]
  push_cast
  simp only [Complex.real_smul]
  ring

end JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite

namespace EnvelopeTorusDescent

open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeSmoothing
open scoped Topology ContDiff

private def sourceJointTimeDirection (n : ℕ) :
    SourceJointComplexCover n :=
  (0, (1 / 2 : ℂ))

private theorem hasDerivAt_sourceJointTimeEmbedding
    {n : ℕ}
    (z : TorusCharacters.LogSpace n)
    (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => sourceJointTimeEmbedding z s)
      (sourceJointTimeDirection n) t := by
  unfold sourceJointTimeEmbedding sourceJointTimeDirection
  exact (hasDerivAt_const t z).prodMk
    (Complex.ofRealCLM.hasDerivAt.div_const (2 : ℂ))

private theorem sourceRealFderiv_periodic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (d : E)
    (hperiod : Function.Periodic F d) :
    Function.Periodic (fderiv ℝ F) d := by
  intro x
  have he : (fun y : E => F (y + d)) = F :=
    funext hperiod
  have hd := congrArg (fun G : E → ℝ => fderiv ℝ G x) he
  change fderiv ℝ (fun y : E => F (y + d)) x =
    fderiv ℝ F x at hd
  rw [fderiv_comp_add_right] at hd
  exact hd

end EnvelopeTorusDescent

namespace EnvelopeGeneralTorusDescent

open Set Function Filter MeasureTheory
open ComplexKillingSaturationBridge MatrixTorusBochnerIdentity JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeRightDerivative EnvelopeSmoothing EnvelopeTorusDescent
open scoped Topology ContDiff

private def jointSourceCoverTimeSlice {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (z : TorusCharacters.LogSpace n) : ℝ :=
  F (sourceJointTimeEmbedding z t)

private theorem continuous_jointSourceCoverTimeSlice {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : Continuous F) (t : ℝ) :
    Continuous (jointSourceCoverTimeSlice F t) := by
  unfold jointSourceCoverTimeSlice
  apply hF.comp
  unfold sourceJointTimeEmbedding
  fun_prop

private theorem jointSourceCoverTimeSlice_spatial_periodic {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverTimeSlice F t)
      (TorusCharacters.imaginaryShift m) := by
  intro z
  have h := hperiod m (sourceJointTimeEmbedding z t)
  simpa only [jointSourceCoverTimeSlice, sourceJointTimeEmbedding, Prod.mk_add_mk, add_zero] using h

private def jointSourceTorusWeight {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  (torusScalarRepresentative
    (fun z : TorusCharacters.LogSpace n =>
      (jointSourceCoverTimeSlice F t z : ℂ)) q).re

private theorem jointSourceTorusWeight_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusWeight F t q =
      F (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl

private theorem continuous_jointSourceTorusWeight {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : Continuous F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusWeight F t) := by
  unfold jointSourceTorusWeight
  apply Complex.continuous_re.comp
  apply continuous_torusScalarRepresentative_of_periodic
  · exact Complex.continuous_ofReal.comp
      (continuous_jointSourceCoverTimeSlice hF t)
  · intro m z
    exact congrArg Complex.ofReal
      (jointSourceCoverTimeSlice_spatial_periodic hperiod t m z)

private def jointSourceCoverVelocity {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (q : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ F q) (sourceJointTimeDirection n)

private def jointSourceCoverAcceleration {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (q : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ (jointSourceCoverVelocity F) q)
    (sourceJointTimeDirection n)

private theorem contDiff_jointSourceCoverVelocity {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F) :
    ContDiff ℝ 1 (jointSourceCoverVelocity F) := by
  unfold jointSourceCoverVelocity
  exact (hF.fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiff_const

private theorem continuous_jointSourceCoverAcceleration {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F) :
    Continuous (jointSourceCoverAcceleration F) := by
  unfold jointSourceCoverAcceleration
  exact ((contDiff_jointSourceCoverVelocity hF).continuous_fderiv
    (by norm_num)).clm_apply continuous_const

private theorem jointSourceCoverVelocity_spatial_periodic {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverVelocity F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold jointSourceCoverVelocity
  exact congrArg (fun L => L (sourceJointTimeDirection n))
    (sourceRealFderiv_periodic F
      (TorusCharacters.imaginaryShift m, (0 : ℂ))
      (hperiod m) q)

private theorem jointSourceCoverAcceleration_spatial_periodic {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (m : Fin n → ℤ) :
    Function.Periodic (jointSourceCoverAcceleration F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold jointSourceCoverAcceleration
  exact congrArg (fun L => L (sourceJointTimeDirection n))
    (sourceRealFderiv_periodic (jointSourceCoverVelocity F)
      (TorusCharacters.imaginaryShift m, (0 : ℂ))
      (jointSourceCoverVelocity_spatial_periodic hperiod m) q)

private def jointSourceTorusVelocity {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  jointSourceTorusWeight (jointSourceCoverVelocity F) t q

private def jointSourceTorusAcceleration {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) : ℝ :=
  jointSourceTorusWeight (jointSourceCoverAcceleration F) t q

private theorem jointSourceTorusVelocity_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusVelocity F t q =
      jointSourceCoverVelocity F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl

private theorem jointSourceTorusAcceleration_eq_cover {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    jointSourceTorusAcceleration F t q =
      jointSourceCoverAcceleration F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t) := by
  rfl

private theorem continuous_jointSourceTorusVelocity {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusVelocity F t) := by
  unfold jointSourceTorusVelocity
  exact continuous_jointSourceTorusWeight
    (contDiff_jointSourceCoverVelocity hF).continuous
    (jointSourceCoverVelocity_spatial_periodic hperiod) t

private theorem continuous_jointSourceTorusAcceleration {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    Continuous (jointSourceTorusAcceleration F t) := by
  unfold jointSourceTorusAcceleration
  exact continuous_jointSourceTorusWeight
    (continuous_jointSourceCoverAcceleration hF)
    (jointSourceCoverAcceleration_spatial_periodic hperiod) t

private theorem hasDerivAt_jointSourceTorusWeight {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    HasDerivAt (fun s : ℝ => jointSourceTorusWeight F s q)
      (jointSourceTorusVelocity F t q) t := by
  have heq :
      (fun s : ℝ => jointSourceTorusWeight F s q) =
      (fun s : ℝ =>
        F (sourceJointTimeEmbedding (sourceTorusCoverPoint q) s)) := by
    funext s
    exact jointSourceTorusWeight_eq_cover F s q
  rw [heq, jointSourceTorusVelocity_eq_cover]
  exact (hF.differentiable (by norm_num)
    (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)).hasFDerivAt
      |>.comp_hasDerivAt t
        (hasDerivAt_sourceJointTimeEmbedding
          (sourceTorusCoverPoint q) t)

private theorem hasDerivAt_jointSourceTorusVelocity {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (t : ℝ) (q : WeightedTorusHilbert.LogTorus n) :
    HasDerivAt (fun s : ℝ => jointSourceTorusVelocity F s q)
      (jointSourceTorusAcceleration F t q) t := by
  have heq :
      (fun s : ℝ => jointSourceTorusVelocity F s q) =
      (fun s : ℝ => jointSourceCoverVelocity F
        (sourceJointTimeEmbedding (sourceTorusCoverPoint q) s)) := by
    funext s
    exact jointSourceTorusVelocity_eq_cover F s q
  rw [heq, jointSourceTorusAcceleration_eq_cover]
  exact ((contDiff_jointSourceCoverVelocity hF).differentiable
    (by norm_num)
    (sourceJointTimeEmbedding (sourceTorusCoverPoint q) t)).hasFDerivAt
      |>.comp_hasDerivAt t
        (hasDerivAt_sourceJointTimeEmbedding
          (sourceTorusCoverPoint q) t)

end EnvelopeGeneralTorusDescent

namespace TorusHessianPositiveDefinite

open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialComplexHessian
open EnvelopeGeneralTorusDescent WeightedTorusGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology ContDiff

private theorem angularCoverPotential_jointSourceTorusWeight_eq
    {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (hperiod : ∀ m : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift m, (0 : ℂ)))
    (t : ℝ) :
    angularCoverPotential (jointSourceTorusWeight F t) =
      sourceJointSpatialSlice F (t / 2 : ℂ) := by
  funext z
  let G : TorusCharacters.LogSpace n → ℂ :=
    fun w => (jointSourceCoverTimeSlice F t w : ℂ)
  have hG : ∀ m : Fin n → ℤ,
      Function.Periodic G
        (TorusCharacters.imaginaryShift m) := by
    intro m w
    exact congrArg Complex.ofReal
      (jointSourceCoverTimeSlice_spatial_periodic hperiod t m w)
  have hrec := congrFun
    (complexTorusCoverLift_torusScalarRepresentative_eq G hG) z
  exact congrArg Complex.re hrec

end TorusHessianPositiveDefinite

namespace TorusMatrixSquareRootContinuity

open Set Function Filter Matrix
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator Topology ContDiff

private theorem continuous_complexMatrixSquareRoot
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ x, (H x).PosSemidef) :
    Continuous (fun x => CFC.sqrt (H x)) := by
  have hnonneg : ∀ x : X,
      (0 : Matrix (Fin n) (Fin n) ℂ) ≤ H x :=
    fun x => (hH x).nonneg
  have hcfc : Continuous
      (fun x : X =>
        cfc (fun t : NNReal => NNReal.sqrt t) (H x)) := by
    exact Continuous.cfc_nnreal_of_mem_nhdsSet
      (A := Matrix (Fin n) (Fin n) ℂ)
      (X := X)
      (a := H)
      (s := (Set.univ : Set NNReal))
      (fun t : NNReal => NNReal.sqrt t)
      Filter.univ_mem
      hcont
      (ha' := hnonneg)
      (hf := NNReal.continuous_sqrt.continuousOn)
  simp_rw [CFC.sqrt_eq_cfc]
  exact hcfc

private theorem continuous_complexMatrixSquareRoot_inverse
    {n : ℕ} {X : Type*} [TopologicalSpace X]
    {H : X → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ x, (H x).PosDef) :
    Continuous (fun x => (CFC.sqrt (H x))⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hdet : (CFC.sqrt (H x)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (hH x).isStrictlyPositive.sqrt.posDef.isUnit).ne_zero
  have hinv : ContinuousAt Ring.inverse (CFC.sqrt (H x)).det := by
    simpa only [Ring.inverse_eq_inv'] using
      (continuousAt_inv₀ hdet)
  have hsqrt : ContinuousAt (fun y : X => CFC.sqrt (H y)) x :=
    (continuous_complexMatrixSquareRoot hcont
      (fun y => (hH y).posSemidef)).continuousAt
  have hcomp :
      ContinuousAt
        ((fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) ∘
          (fun y : X => CFC.sqrt (H y))) x :=
    ContinuousAt.comp
      (f := fun y : X => CFC.sqrt (H y))
      (g := fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹)
      (continuousAt_matrix_inv (CFC.sqrt (H x)) hinv) hsqrt
  exact hcomp

end TorusMatrixSquareRootContinuity

namespace BergmanJetStrictRadialRegularizer

open Set Function Filter MeasureTheory Matrix
open TorusCharacters SupportFunction LatticeAsymptotics BergmanAsymptotics
open ComplexMatrixWeightedHilbert MatrixTorusBochnerBridge MatrixTorusBochnerCore
open WeightedDolbeaultBochnerIdentity SchurConvexity
open scoped BigOperators ENNReal Topology ContDiff MatrixOrder
  ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

private def momentBodyInteriorRadius
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  ((Metric.isOpen_iff.mp isOpen_interior)
    (0 : Space n) (zero_mem_interior K)).choose

private theorem momentBodyInteriorRadius_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentBodyInteriorRadius K :=
  ((Metric.isOpen_iff.mp isOpen_interior)
    (0 : Space n) (zero_mem_interior K)).choose_spec.1

private theorem ball_momentBodyInteriorRadius_subset
    {n : ℕ} (K : CenteredBody n) :
    Metric.ball (0 : Space n)
      (momentBodyInteriorRadius K) ⊆ K.carrier := by
  intro x hx
  exact interior_subset
    (((Metric.isOpen_iff.mp isOpen_interior)
      (0 : Space n) (zero_mem_interior K)).choose_spec.2 hx)

private def momentBodyStrictScale
    {n : ℕ} (K : CenteredBody n) : ℝ :=
  momentBodyInteriorRadius K / 2

private theorem momentBodyStrictScale_pos
    {n : ℕ} (K : CenteredBody n) :
    0 < momentBodyStrictScale K :=
  half_pos (momentBodyInteriorRadius_pos K)

private theorem momentBodyStrictScale_sum_abs_le_support
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * (∑ i : Fin n, |x i|) ≤
      supportFunction K.carrier x := by
  let c : ℝ := momentBodyStrictScale K
  have hc : 0 < c := momentBodyStrictScale_pos K
  have hnorm : ‖c • signVector x‖ ≤ c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    exact mul_le_of_le_one_right hc.le (norm_signVector_le_one x)
  have hradius : c < momentBodyInteriorRadius K := by
    exact half_lt_self (momentBodyInteriorRadius_pos K)
  have hball : c • signVector x ∈
      Metric.ball (0 : Space n)
        (momentBodyInteriorRadius K) := by
    rw [Metric.mem_ball, dist_zero_right]
    exact hnorm.trans_lt hradius
  have hmem := ball_momentBodyInteriorRadius_subset K hball
  have hs := pairing_le_supportFunction K.compact hmem x
  rw [pairing_smul_left, pairing_signVector] at hs
  exact hs

private def momentStrictRadialCoordinate (y : ℝ) : ℝ :=
  Real.log (Real.exp y + Real.exp (-y))

private theorem momentStrictRadialCoordinate_denominator_pos
    (y : ℝ) : 0 < Real.exp y + Real.exp (-y) :=
  add_pos (Real.exp_pos y) (Real.exp_pos (-y))

private theorem contDiff_momentStrictRadialCoordinate :
    ContDiff ℝ ∞ momentStrictRadialCoordinate := by
  unfold momentStrictRadialCoordinate
  apply (Real.contDiff_exp.add
    (Real.contDiff_exp.comp contDiff_neg)).log
  intro y
  exact (momentStrictRadialCoordinate_denominator_pos y).ne'

private def momentStrictRadialCoordinateDerivative (y : ℝ) : ℝ :=
  (Real.exp y - Real.exp (-y)) /
    (Real.exp y + Real.exp (-y))

private theorem hasDerivAt_momentStrictRadialCoordinate (y : ℝ) :
    HasDerivAt momentStrictRadialCoordinate
      (momentStrictRadialCoordinateDerivative y) y := by
  have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    have hcomp : HasDerivAt
        (Real.exp ∘ fun x : ℝ => -x)
        (Real.exp (-y) * (-1)) y :=
      (Real.hasDerivAt_exp (-y)).comp y
        (hasDerivAt_id y).neg
    refine (hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  have hsum : HasDerivAt
      (fun x : ℝ => Real.exp x + Real.exp (-x))
      (Real.exp y - Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_add hneg).congr_deriv ?_
    ring
  exact hsum.log
    (momentStrictRadialCoordinate_denominator_pos y).ne'

private def momentStrictRadialCoordinateSecond (y : ℝ) : ℝ :=
  4 / (Real.exp y + Real.exp (-y)) ^ 2

private theorem hasDerivAt_momentStrictRadialCoordinateDerivative
    (y : ℝ) :
    HasDerivAt momentStrictRadialCoordinateDerivative
      (momentStrictRadialCoordinateSecond y) y := by
  have hneg : HasDerivAt (fun x : ℝ => Real.exp (-x))
      (-Real.exp (-y)) y := by
    have hcomp : HasDerivAt
        (Real.exp ∘ fun x : ℝ => -x)
        (Real.exp (-y) * (-1)) y :=
      (Real.hasDerivAt_exp (-y)).comp y
        (hasDerivAt_id y).neg
    refine (hcomp.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => rfl)).congr_deriv ?_
    ring
  have hnum : HasDerivAt
      (fun x : ℝ => Real.exp x - Real.exp (-x))
      (Real.exp y + Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_sub hneg).congr_deriv ?_
    ring
  have hden : HasDerivAt
      (fun x : ℝ => Real.exp x + Real.exp (-x))
      (Real.exp y - Real.exp (-y)) y := by
    refine ((Real.hasDerivAt_exp y).fun_add hneg).congr_deriv ?_
    ring
  have h := hnum.fun_div hden
    (momentStrictRadialCoordinate_denominator_pos y).ne'
  change HasDerivAt
    (fun x : ℝ =>
      (Real.exp x - Real.exp (-x)) /
        (Real.exp x + Real.exp (-x)))
    (4 / (Real.exp y + Real.exp (-y)) ^ 2) y
  have he : Real.exp (-y) * Real.exp y = 1 := by
    rw [← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero]
  refine h.congr_deriv ?_
  congr 1
  nlinarith [he]

private theorem momentStrictRadialCoordinateSecond_pos (y : ℝ) :
    0 < momentStrictRadialCoordinateSecond y := by
  unfold momentStrictRadialCoordinateSecond
  positivity

private theorem abs_le_momentStrictRadialCoordinate (y : ℝ) :
    |y| ≤ momentStrictRadialCoordinate y := by
  have hsum : Real.exp |y| ≤ Real.exp y + Real.exp (-y) := by
    by_cases hy : 0 ≤ y
    · rw [abs_of_nonneg hy]
      exact le_add_of_nonneg_right (Real.exp_pos (-y)).le
    · rw [abs_of_neg (lt_of_not_ge hy)]
      exact le_add_of_nonneg_left (Real.exp_pos y).le
  have hmono := Real.strictMonoOn_log.monotoneOn
    (show Real.exp |y| ∈ Set.Ioi (0 : ℝ) from Real.exp_pos _)
    (show Real.exp y + Real.exp (-y) ∈ Set.Ioi (0 : ℝ) from
      momentStrictRadialCoordinate_denominator_pos y)
    hsum
  simpa only [momentStrictRadialCoordinate, ge_iff_le, Real.log_exp] using hmono

private theorem momentStrictRadialCoordinate_le_abs_add_log_two
    (y : ℝ) :
    momentStrictRadialCoordinate y ≤ |y| + Real.log 2 := by
  have hpos : Real.exp y ≤ Real.exp |y| :=
    Real.exp_le_exp.mpr (le_abs_self y)
  have hnegarg : -y ≤ |y| := by
    calc
      -y ≤ |-y| := le_abs_self (-y)
      _ = |y| := abs_neg y
  have hneg : Real.exp (-y) ≤ Real.exp |y| :=
    Real.exp_le_exp.mpr hnegarg
  have hsum : Real.exp y + Real.exp (-y) ≤
      2 * Real.exp |y| := by linarith
  calc
    momentStrictRadialCoordinate y =
        Real.log (Real.exp y + Real.exp (-y)) := rfl
    _ ≤ Real.log (2 * Real.exp |y|) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show Real.exp y + Real.exp (-y) ∈ Set.Ioi (0 : ℝ) from
          momentStrictRadialCoordinate_denominator_pos y)
        (show 2 * Real.exp |y| ∈ Set.Ioi (0 : ℝ) from
          mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos |y|))
        hsum
    _ = |y| + Real.log 2 := by
      rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
        (Real.exp_ne_zero |y|), Real.log_exp]
      ring

private def momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) : ℝ :=
  ∑ i : Fin n,
    momentStrictRadialCoordinate
      (momentBodyStrictScale K * x i)

private theorem contDiff_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n) :
    ContDiff ℝ ∞ (momentBodyStrictRadialPotential K) := by
  unfold momentBodyStrictRadialPotential
  apply ContDiff.sum
  intro i _
  exact contDiff_momentStrictRadialCoordinate.comp
    (contDiff_const.mul (contDiff_apply ℝ ℝ i))

private theorem momentBodyStrictRadialPotential_sum_abs_lower
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictScale K * (∑ i : Fin n, |x i|) ≤
      momentBodyStrictRadialPotential K x := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h := abs_le_momentStrictRadialCoordinate
    (momentBodyStrictScale K * x i)
  rwa [abs_mul,
    abs_of_pos (momentBodyStrictScale_pos K)] at h

private theorem momentBodyStrictRadialPotential_le_support_add
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    momentBodyStrictRadialPotential K x ≤
      supportFunction K.carrier x + (n : ℝ) * Real.log 2 := by
  calc
    momentBodyStrictRadialPotential K x ≤
        ∑ i : Fin n,
          (|momentBodyStrictScale K * x i| + Real.log 2) := by
      apply Finset.sum_le_sum
      intro i _
      exact momentStrictRadialCoordinate_le_abs_add_log_two
        (momentBodyStrictScale K * x i)
    _ = momentBodyStrictScale K * (∑ i : Fin n, |x i|) +
          (n : ℝ) * Real.log 2 := by
      simp_rw [abs_mul,
        abs_of_pos (momentBodyStrictScale_pos K)]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := add_le_add
      (momentBodyStrictScale_sum_abs_le_support K x)
      (le_refl ((n : ℝ) * Real.log 2))

private def momentBodyStrictRadialGradient
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) : Space n →L[ℝ] ℝ :=
  ∑ i : Fin n,
    (momentBodyStrictScale K *
      momentStrictRadialCoordinateDerivative
        (momentBodyStrictScale K * x i)) •
      (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)

private theorem hasFDerivAt_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    HasFDerivAt (momentBodyStrictRadialPotential K)
      (momentBodyStrictRadialGradient K x) x := by
  unfold momentBodyStrictRadialPotential
    momentBodyStrictRadialGradient
  have hterm (i : Fin n) :
      HasFDerivAt
        (fun y : Space n =>
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * y i))
        ((momentBodyStrictScale K *
          momentStrictRadialCoordinateDerivative
            (momentBodyStrictScale K * x i)) •
          (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
        x := by
    let c : ℝ := momentBodyStrictScale K
    let P : Space n →L[ℝ] ℝ :=
      ContinuousLinearMap.proj i
    have hc : HasFDerivAt (fun y : Space n => c * y i)
        (c • P) x := by
      exact P.hasFDerivAt.const_mul c
    have h :=
      (hasDerivAt_momentStrictRadialCoordinate (c * x i))
        |>.comp_hasFDerivAt x hc
    simpa only [mul_comm, comp_def, smul_smul] using h
  exact HasFDerivAt.fun_sum
    (u := Finset.univ) (fun i _ => hterm i)

private theorem fderiv_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    fderiv ℝ (momentBodyStrictRadialPotential K) x =
      momentBodyStrictRadialGradient K x :=
  (hasFDerivAt_momentBodyStrictRadialPotential K x).fderiv

private def momentBodyStrictRadialHessianDiagonal
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) : ℝ :=
  momentBodyStrictScale K ^ 2 *
    momentStrictRadialCoordinateSecond
      (momentBodyStrictScale K * x i)

private theorem momentBodyStrictRadialHessianDiagonal_pos
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) :
    0 < momentBodyStrictRadialHessianDiagonal K x i := by
  unfold momentBodyStrictRadialHessianDiagonal
  exact mul_pos (sq_pos_of_pos (momentBodyStrictScale_pos K))
    (momentStrictRadialCoordinateSecond_pos _)

private theorem hasFDerivAt_momentBodyStrictRadialGradientCoefficient
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) (i : Fin n) :
    HasFDerivAt
      (fun y : Space n =>
        momentBodyStrictScale K *
          momentStrictRadialCoordinateDerivative
            (momentBodyStrictScale K * y i))
      (momentBodyStrictRadialHessianDiagonal K x i •
        (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
      x := by
  let c : ℝ := momentBodyStrictScale K
  let P : Space n →L[ℝ] ℝ :=
    ContinuousLinearMap.proj i
  have hinner : HasFDerivAt
      (fun y : Space n => c * y i) (c • P) x :=
    P.hasFDerivAt.const_mul c
  have hfirst :=
    (hasDerivAt_momentStrictRadialCoordinateDerivative
      (c * x i)).comp_hasFDerivAt x hinner
  have hscaled := hfirst.const_mul c
  simpa only [mul_comm, momentBodyStrictRadialHessianDiagonal, pow_two, mul_assoc,
    Function.comp_apply, smul_smul] using hscaled

private theorem fderiv_momentBodyStrictRadialGradient_apply
    {n : ℕ} (K : CenteredBody n)
    (x v w : Space n) :
    ((fderiv ℝ (momentBodyStrictRadialGradient K) x) v) w =
      ∑ i : Fin n,
        momentBodyStrictRadialHessianDiagonal K x i *
          v i * w i := by
  have h : HasFDerivAt
      (momentBodyStrictRadialGradient K)
      (∑ i : Fin n,
        (momentBodyStrictRadialHessianDiagonal K x i •
          (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)).smulRight
            (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
      x := by
    unfold momentBodyStrictRadialGradient
    have hterm (i : Fin n) :
        HasFDerivAt
          (fun y : Space n =>
            (momentBodyStrictScale K *
              momentStrictRadialCoordinateDerivative
                (momentBodyStrictScale K * y i)) •
              (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
          ((momentBodyStrictRadialHessianDiagonal K x i •
            (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)).smulRight
              (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ))
          x :=
      (hasFDerivAt_momentBodyStrictRadialGradientCoefficient
        K x i).smul_const
        (ContinuousLinearMap.proj i : Space n →L[ℝ] ℝ)
    exact HasFDerivAt.fun_sum
      (u := Finset.univ) (fun i _ => hterm i)
  rw [h.fderiv]
  simp only [_root_.sum_apply, ContinuousLinearMap.smulRight_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_assoc]

private theorem fderiv_fderiv_momentBodyStrictRadialPotential_apply
    {n : ℕ} (K : CenteredBody n)
    (x v w : Space n) :
    ((fderiv ℝ
      (fderiv ℝ (momentBodyStrictRadialPotential K)) x) v) w =
      ∑ i : Fin n,
        momentBodyStrictRadialHessianDiagonal K x i *
          v i * w i := by
  have heq :
      fderiv ℝ (momentBodyStrictRadialPotential K) =
        momentBodyStrictRadialGradient K := by
    funext y
    exact fderiv_momentBodyStrictRadialPotential K y
  rw [heq]
  exact fderiv_momentBodyStrictRadialGradient_apply K x v w

private theorem sourceMatrixHessian_momentBodyStrictRadialPotential_eq_diagonal
    {n : ℕ} (K : CenteredBody n)
    (x : Space n) :
    sourceMatrixHessian (momentBodyStrictRadialPotential K) x =
      Matrix.diagonal
        (momentBodyStrictRadialHessianDiagonal K x) := by
  classical
  ext i j
  unfold sourceMatrixHessian actualHessianMatrix
  rw [LinearMap.toMatrix₂'_apply]
  change
    ((fderiv ℝ
      (fderiv ℝ (momentBodyStrictRadialPotential K)) x)
      (Pi.single i (1 : ℝ)))
      (Pi.single j (1 : ℝ)) =
      Matrix.diagonal
        (momentBodyStrictRadialHessianDiagonal K x) i j
  rw [fderiv_fderiv_momentBodyStrictRadialPotential_apply]
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one, diagonal_apply_eq]
    · intro b _ hb
      have hz : (Pi.single i (1 : ℝ) : Space n) b = 0 := by
        simp only [ne_eq, hb, not_false_eq_true, Pi.single_eq_of_ne]
      simp only [hz, mul_zero]
    · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, mul_one, IsEmpty.forall_iff]
  · rw [Matrix.diagonal_apply, ite_eq_right hij,
      Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one, ne_eq, hij, not_false_eq_true, Pi.single_eq_of_ne,
        mul_zero]
    · intro b _ hb
      have hz : (Pi.single i (1 : ℝ) : Space n) b = 0 := by
        simp only [ne_eq, hb, not_false_eq_true, Pi.single_eq_of_ne]
      simp only [hz, mul_zero, zero_mul]
    · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, mul_one, mul_eq_zero,
        IsEmpty.forall_iff]

private theorem sourceCoverComplexHessian_momentBodyStrictRadialPotential_eq_diagonal
    {n : ℕ} (K : CenteredBody n)
    (z : LogSpace n) :
    sourceCoverComplexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z =
      Matrix.diagonal
        (fun i : Fin n =>
          (momentBodyStrictRadialHessianDiagonal K
            (sourceCoverRadialLinear n z) i : ℂ)) := by
  classical
  ext i j
  change
    complexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z i j =
      Matrix.diagonal
        (fun k : Fin n =>
          (momentBodyStrictRadialHessianDiagonal K
            (sourceCoverRadialLinear n z) k : ℂ)) i j
  rw [complexHessian_matrixSourceCoverPotential_eq_real
    ((contDiff_infty.mp
      (contDiff_momentBodyStrictRadialPotential K)) 2) z i j,
    sourceMatrixHessian_momentBodyStrictRadialPotential_eq_diagonal]
  by_cases h : i = j
  · subst j
    simp only [diagonal_apply_eq]
  · simp only [ne_eq, h, not_false_eq_true, diagonal_apply_ne, Complex.ofReal_zero]

private theorem sourceCoverComplexHessian_momentBodyStrictRadialPotential_posDef
    {n : ℕ} (K : CenteredBody n)
    (z : LogSpace n) :
    (sourceCoverComplexHessian
      (matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K)) z).PosDef := by
  rw [sourceCoverComplexHessian_momentBodyStrictRadialPotential_eq_diagonal]
  apply Matrix.PosDef.diagonal
  intro i
  exact_mod_cast
    momentBodyStrictRadialHessianDiagonal_pos
      K (sourceCoverRadialLinear n z) i

end BergmanJetStrictRadialRegularizer

namespace BergmanJetPartitionEndpoint

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentTargetDanskin
open MomentFirstVariation MomentRegularity BergmanJetTorusEnvelope BergmanJetTorusCoercivity
open JetEnvelopeSlopeConvergence JetEnvelopeRightDerivative LogPartitionConvexity
open scoped BigOperators ENNReal Topology

private def momentBodyOptimizer
    {n : ℕ} (K : CenteredBody n) :
    SourceFiniteEnergyPotential K :=
  Classical.choose (exists_exact_optimizer_gradientPushforward_eq K)

private theorem momentBodyOptimizer_transport
    {n : ℕ} (K : CenteredBody n) :
    finiteEnergySourceGradientPushforward (momentBodyOptimizer K) =
      normalizedTargetBodyMeasure K := by
  exact (Classical.choose_spec
    (exists_exact_optimizer_gradientPushforward_eq K)).2.2

private def momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n)
    (t : ℝ) (q : LogTorus n) : ℝ :=
  momentTorusEnvelopeTimeSlice
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p q t

@[simp] private theorem momentBodyTorusWeight_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (q : LogTorus n) :
    momentBodyTorusWeight K p 0 q =
      momentNormalizedPotential (momentBodyOptimizer K) q.1 := by
  exact momentTorusEnvelopeTimeSlice_zero
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p q

private theorem momentBodyTorusWeight_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0)
    (q : LogTorus n) :
    momentBodyTorusWeight K p t q =
      momentNormalizedPotential (momentBodyOptimizer K) q.1 := by
  unfold momentBodyTorusWeight momentTorusEnvelopeTimeSlice
  rw [momentEnvelopeTimeSlice_of_nonpositive
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p
    (sourceTorusCoverPoint q) ht,
    realLogCoordinate_sourceTorusCoverPoint]

private theorem measurable_momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Measurable (momentBodyTorusWeight K p t) := by
  exact measurable_momentTorusEnvelopeTimeSlice
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p t

private theorem integrable_exp_neg_momentBodyTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Integrable
      (fun q : LogTorus n =>
        Real.exp (-momentBodyTorusWeight K p t q))
      (sourceTorusBaseMeasure n) := by
  exact integrable_exp_neg_momentTorusEnvelopeTimeSlice
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p t

private def momentBodyPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  sourcePartition (momentBodyTorusWeight K p) t

private theorem momentBodyPartition_eq_integral
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    momentBodyPartition K p t =
      ∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight K p t q)
          ∂(sourceTorusBaseMeasure n) := by
  rfl

private theorem momentBodyPartition_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    0 < momentBodyPartition K p t := by
  exact momentTorusEnvelopePartition_pos
    K (momentBodyOptimizer K)
    (momentBodyOptimizer_transport K) p t

private theorem momentBodyPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyPartition K p t =
      normalizedVolume K.carrier := by
  rw [momentBodyPartition_eq_integral]
  calc
    (∫ q : LogTorus n,
        Real.exp (-momentBodyTorusWeight K p t q)
          ∂(sourceTorusBaseMeasure n)) =
        ∫ q : LogTorus n,
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) q.1) * (1 : ℝ)
          ∂((volume : Measure (Space n)).prod
            (angularMeasure n)) := by
          unfold sourceTorusBaseMeasure
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with q
          rw [momentBodyTorusWeight_of_nonpositive K p ht q]
          simp only [mul_one]
    _ = (∫ x : Space n,
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) x)
            ∂(volume : Measure (Space n))) *
          (∫ _ : AngularTorus n, (1 : ℝ) ∂(angularMeasure n)) :=
      MeasureTheory.integral_prod_mul
        (μ := (volume : Measure (Space n)))
        (ν := angularMeasure n)
        (fun x : Space n =>
          Real.exp
            (-momentNormalizedPotential
              (momentBodyOptimizer K) x))
        (fun _ : AngularTorus n => (1 : ℝ))
    _ = normalizedVolume K.carrier := by
      rw [integral_exp_neg_momentNormalizedPotential
        (momentBodyOptimizer K)]
      simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]

@[simp] private theorem momentBodyPartition_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyPartition K p 0 =
      normalizedVolume K.carrier := by
  exact momentBodyPartition_of_nonpositive K p (le_refl 0)

private def momentBodyNormalizedPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  momentBodyPartition K p t /
    normalizedVolume K.carrier

private theorem momentBodyNormalizedPartition_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    0 < momentBodyNormalizedPartition K p t := by
  exact div_pos (momentBodyPartition_pos K p t) K.volume_pos

private theorem momentBodyNormalizedPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyNormalizedPartition K p t = 1 := by
  unfold momentBodyNormalizedPartition
  rw [momentBodyPartition_of_nonpositive K p ht]
  exact div_self K.volume_pos.ne'

private def momentBodyLogPartition
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) : ℝ :=
  -Real.log (momentBodyNormalizedPartition K p t)

private theorem momentBodyLogPartition_of_nonpositive
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) {t : ℝ} (ht : t ≤ 0) :
    momentBodyLogPartition K p t = 0 := by
  simp only [momentBodyLogPartition, momentBodyNormalizedPartition_of_nonpositive K p ht,
    Real.log_one, neg_zero]

@[simp] private theorem momentBodyLogPartition_zero
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) :
    momentBodyLogPartition K p 0 = 0 := by
  exact momentBodyLogPartition_of_nonpositive K p (le_refl 0)

private theorem momentBodyLogPartition_eq_sourceLogPartition_add_log_volume
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    momentBodyLogPartition K p t =
      sourceLogPartition (momentBodyTorusWeight K p) t +
        Real.log (normalizedVolume K.carrier) := by
  change
    -Real.log
      (momentBodyPartition K p t /
        normalizedVolume K.carrier) =
      -Real.log (momentBodyPartition K p t) +
        Real.log (normalizedVolume K.carrier)
  rw [Real.log_div
    (momentBodyPartition_pos K p t).ne'
    K.volume_pos.ne']
  ring

private theorem sourceNormalizedDensity_momentBody_pos
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) (q : LogTorus n) :
    0 < sourceNormalizedDensity
      (momentBodyTorusWeight K p) t q := by
  exact div_pos (Real.exp_pos _)
    (momentBodyPartition_pos K p t)

private theorem sourceNormalizedDensity_momentBody_integrable
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    Integrable
      (sourceNormalizedDensity (momentBodyTorusWeight K p) t)
      (sourceTorusBaseMeasure n) := by
  exact (integrable_exp_neg_momentBodyTorusWeight
    K p t).div_const _

private theorem integral_sourceNormalizedDensity_momentBody
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      sourceNormalizedDensity (momentBodyTorusWeight K p) t q
        ∂(sourceTorusBaseMeasure n)) = 1 := by
  unfold sourceNormalizedDensity
  rw [MeasureTheory.integral_div]
  exact div_self (momentBodyPartition_pos K p t).ne'

private theorem sourceProbability_momentBody_univ
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    sourceProbability (momentBodyTorusWeight K p) t Set.univ = 1 := by
  unfold sourceProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (sourceNormalizedDensity_momentBody_integrable K p t)
    (Filter.Eventually.of_forall fun q =>
      (sourceNormalizedDensity_momentBody_pos K p t q).le),
    integral_sourceNormalizedDensity_momentBody K p t]
  exact ENNReal.ofReal_one

private theorem sourceProbability_momentBody_isProbability
    {n : ℕ} (K : CenteredBody n)
    (p : LogSpace n) (t : ℝ) :
    IsProbabilityMeasure
      (sourceProbability (momentBodyTorusWeight K p) t) :=
  ⟨sourceProbability_momentBody_univ K p t⟩

end BergmanJetPartitionEndpoint

namespace BergmanJetTorusSlopeBridge

open Set Function Filter MeasureTheory Module InnerProductSpace
open TorusCharacters WeightedTorusHilbert BergmanMonomials LatticeAsymptotics AdaptedBergmanBasis
open MomentOptimizer MomentFirstVariation MomentTargetGeodesic MomentRegularity BergmanJetBasis
open MomentWeakGlobalKernel BergmanJetGeodesic BergmanJetProfileBridge JetEnvelopeRightDerivative
open scoped BigOperators ENNReal InnerProductSpace Topology

private def momentNormalizedTorusMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (u : monomialIndex K k) (q : LogTorus n) : ℂ :=
  ((Real.sqrt (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹) *
    torusMonomial (integerExponent K hk u) q

private theorem continuous_momentNormalizedTorusMonomial
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (u : monomialIndex K k) :
    Continuous (momentNormalizedTorusMonomial K hk F u) := by
  unfold momentNormalizedTorusMonomial
  exact continuous_const.mul
    (continuous_torusMonomial (integerExponent K hk u))

private theorem momentNormalizedTorusMonomial_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (u : monomialIndex K k) :
    (fun q : LogTorus n =>
      momentNormalizedMonomialLp K hk F htransport u q)
      =ᵐ[weightedTorusMeasure k (momentNormalizedPotential F)]
        momentNormalizedTorusMonomial K hk F u := by
  let c : ℂ :=
    ((Real.sqrt (monomialNormSquared k (u : Space n)
      (momentNormalizedPotential F)) : ℂ)⁻¹)
  have hsmul := MeasureTheory.Lp.coeFn_smul c
    (momentIndexedMonomialLp K hk F htransport u)
  have hmono := momentIndexedMonomialLp_ae K hk F htransport u
  filter_upwards [hsmul, hmono] with q hq hindex
  change
    ((c • momentIndexedMonomialLp K hk F htransport u :
      weightedHilbert k (momentNormalizedPotential F)) :
        LogTorus n → ℂ) q =
      c * torusMonomial (integerExponent K hk u) q
  rw [hq, Pi.smul_apply, hindex, smul_eq_mul]

private def momentTorusRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentMonomialSpan K hk F htransport →ₗ[ℂ]
      (LogTorus n → ℂ) :=
  (Finsupp.linearCombination ℂ
    (momentNormalizedTorusMonomial K hk F)).comp
      (momentLatticeMonomialBasis
        K hk F htransport).repr.toLinearMap

private theorem continuous_momentTorusRepresentative
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Continuous (momentTorusRepresentative K hk F htransport s) := by
  classical
  unfold momentTorusRepresentative
  rw [LinearMap.comp_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  rw [Finset.sum_fn]
  exact continuous_finsetSum _ (fun u _ =>
    (continuous_momentNormalizedTorusMonomial
      K hk F u).const_smul
        ((momentLatticeMonomialBasis
          K hk F htransport).repr s u))

private theorem momentTorusRepresentative_ae
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    (fun q : LogTorus n =>
      ((s : weightedHilbert k (momentNormalizedPotential F)) :
        LogTorus n → ℂ) q)
      =ᵐ[weightedTorusMeasure k (momentNormalizedPotential F)]
        momentTorusRepresentative K hk F htransport s := by
  classical
  let := (monomialIndex_finite K hk).fintype
  let b := momentLatticeMonomialBasis K hk F htransport
  let c : monomialIndex K k → ℂ := fun u => b.repr s u
  let v : monomialIndex K k →
      weightedHilbert k (momentNormalizedPotential F) :=
    fun u => c u • momentNormalizedMonomialLp
      K hk F htransport u
  have hvsum : (∑ u, v u) =
      (s : weightedHilbert k (momentNormalizedPotential F)) := by
    have h := congrArg
      (fun w : momentMonomialSpan K hk F htransport =>
        (w : weightedHilbert k (momentNormalizedPotential F)))
      (b.sum_repr s)
    simpa only [v, c, b, Submodule.coe_sum, Submodule.coe_smul,
      momentLatticeMonomialBasis_apply] using h
  have hvpoint :
      ∀ᵐ q ∂(weightedTorusMeasure k (momentNormalizedPotential F)),
        ∀ u : monomialIndex K k,
          v u q = c u * momentNormalizedTorusMonomial K hk F u q := by
    apply Filter.eventually_all.mpr
    intro u
    have hsmul := MeasureTheory.Lp.coeFn_smul (c u)
      (momentNormalizedMonomialLp K hk F htransport u)
    have hrep := momentNormalizedTorusMonomial_ae
      K hk F htransport u
    filter_upwards [hsmul, hrep] with q hq hr
    change
      ((c u • momentNormalizedMonomialLp
        K hk F htransport u :
          weightedHilbert k (momentNormalizedPotential F)) :
            LogTorus n → ℂ) q =
        c u * momentNormalizedTorusMonomial K hk F u q
    rw [hq, Pi.smul_apply, hr, smul_eq_mul]
  have hsum := JetEnvelopeSlopeBridge.coeFn_finset_sum_ae
    (weightedTorusMeasure k (momentNormalizedPotential F))
    (Finset.univ : Finset (monomialIndex K k)) v
  filter_upwards [hsum, hvpoint] with q hq hall
  rw [← hvsum]
  rw [hq]
  simp only [Finset.sum_congr rfl (fun u _ => hall u)]
  simp only [momentTorusRepresentative, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
    Finsupp.linearCombination_apply, zero_smul, implies_true, Finsupp.sum_fintype,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, c, b]

private theorem integral_momentTorusRepresentative_normSq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    (∫ q : LogTorus n,
      Complex.normSq (momentTorusRepresentative
        K hk F htransport s q)
        ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
          ‖s‖ ^ 2 := by
  let f : weightedHilbert k (momentNormalizedPotential F) := s
  have hae := momentTorusRepresentative_ae
    K hk F htransport s
  have hcomplex :
      ((∫ q : LogTorus n,
        Complex.normSq (momentTorusRepresentative
          K hk F htransport s q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) : ℝ) : ℂ) =
        ((‖s‖ ^ 2 : ℝ) : ℂ) := by
    calc
      ((∫ q : LogTorus n,
        Complex.normSq (momentTorusRepresentative
          K hk F htransport s q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) : ℝ) : ℂ) =
        ∫ q : LogTorus n,
          (Complex.normSq (momentTorusRepresentative
            K hk F htransport s q) : ℂ)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := integral_ofReal.symm
      _ = ∫ q : LogTorus n,
          @inner ℂ ℂ _ (f q) (f q)
          ∂(weightedTorusMeasure k
            (momentNormalizedPotential F)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hae] with q hq
          change
            (Complex.normSq (momentTorusRepresentative
              K hk F htransport s q) : ℂ) =
                @inner ℂ ℂ _
                  ((s : weightedHilbert k
                    (momentNormalizedPotential F)) q)
                  ((s : weightedHilbert k
                    (momentNormalizedPotential F)) q)
          rw [hq, RCLike.inner_apply,
            Complex.normSq_eq_conj_mul_self]
          ring
      _ = @inner ℂ (weightedHilbert k
            (momentNormalizedPotential F)) _ f f :=
          (MeasureTheory.L2.inner_def f f).symm
      _ = ((‖s‖ ^ 2 : ℝ) : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K]
        simp only [Complex.coe_algebraMap, Submodule.coe_norm, Complex.ofReal_pow, f]
  exact Complex.ofReal_injective hcomplex

private theorem integral_momentTorusRepresentative_jetBasis
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (i : Fin (bergmanDimension K k)) :
    (∫ q : LogTorus n,
      Complex.normSq (momentTorusRepresentative
        K hk F htransport
          (momentSimultaneousJetBasis
            K hk F htransport p i) q)
        ∂(weightedTorusMeasure k
          (momentNormalizedPotential F))) = 1 := by
  rw [integral_momentTorusRepresentative_normSq]
  rw [(momentSimultaneousJetBasis
    K hk F htransport p).orthonormal.norm_eq_one i]
  norm_num

private theorem integrable_momentTorusRepresentative_normSq
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport) :
    Integrable
      (fun q : LogTorus n => Complex.normSq
        (momentTorusRepresentative K hk F htransport s q))
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  have hmem : MemLp (momentTorusRepresentative
      K hk F htransport s) 2
        (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    (MeasureTheory.memLp_congr_ae
      (momentTorusRepresentative_ae
        K hk F htransport s)).mp
          (MeasureTheory.Lp.memLp
            (s : weightedHilbert k (momentNormalizedPotential F)))
  have hint := (MeasureTheory.memLp_two_iff_integrable_sq_norm
    (continuous_momentTorusRepresentative
      K hk F htransport s).aestronglyMeasurable).mp hmem
  simpa only [Complex.normSq_eq_norm_sq] using hint

private def momentTorusJetBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : LogTorus n)
    (i : Fin (bergmanDimension K k)) : ℝ :=
  Complex.normSq
    (momentTorusRepresentative K hk F htransport
      (momentSimultaneousJetBasis
        K hk F htransport p i) q)

private theorem continuous_momentTorusJetBasisWeight
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (i : Fin (bergmanDimension K k)) :
    Continuous (fun q : LogTorus n =>
      momentTorusJetBasisWeight K hk F htransport p q i) := by
  unfold momentTorusJetBasisWeight
  exact Complex.continuous_normSq.comp
    (continuous_momentTorusRepresentative K hk F htransport
      (momentSimultaneousJetBasis K hk F htransport p i))

private def momentTorusTruncatedJetOrderDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) : ℝ :=
  ∑ i : Fin (bergmanDimension K k),
    (momentTruncatedJetOrder K hk F htransport p N i : ℝ) *
      momentTorusJetBasisWeight K hk F htransport p q i

private theorem continuous_momentTorusTruncatedJetOrderDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) :
    Continuous
      (momentTorusTruncatedJetOrderDensity
        K hk F htransport p N) := by
  unfold momentTorusTruncatedJetOrderDensity
  exact continuous_finsetSum _ (fun i _ =>
    continuous_const.mul
      (continuous_momentTorusJetBasisWeight
        K hk F htransport p i))

private theorem integral_momentTorusTruncatedJetOrderDensity
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) :
    (∫ q : LogTorus n,
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        ∑ i : Fin (bergmanDimension K k),
          (momentTruncatedJetOrder
            K hk F htransport p N i : ℝ) := by
  unfold momentTorusTruncatedJetOrderDensity
  rw [MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [MeasureTheory.integral_const_mul]
    simp only [momentTorusJetBasisWeight]
    rw [integral_momentTorusRepresentative_jetBasis]
    simp only [mul_one]
  · intro i _
    exact
      (integrable_momentTorusRepresentative_normSq
        K hk F htransport
          (momentSimultaneousJetBasis
            K hk F htransport p i)).const_mul _

private theorem momentTorusRepresentative_eq_holomorphicRepresentative_cover
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (s : momentMonomialSpan K hk F htransport)
    (q : LogTorus n) :
    momentTorusRepresentative K hk F htransport s q =
      momentHolomorphicRepresentative K hk F htransport s
        (sourceTorusCoverPoint q) := by
  classical
  unfold momentTorusRepresentative
    momentHolomorphicRepresentative
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  unfold Finsupp.sum
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro u _
  congr 1
  unfold momentNormalizedTorusMonomial
    normalizedHolomorphicMonomial
  rw [torusCharacter_sourceTorusCoverPoint]

private theorem sum_momentTorusRepresentative_normSq_eq_diagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (b : OrthonormalBasis (Fin (bergmanDimension K k)) ℂ
      (momentMonomialSpan K hk F htransport))
    (q : LogTorus n) :
    (∑ i, Complex.normSq
      (momentTorusRepresentative K hk F htransport
        (b i) q)) =
      diagonalKernel K k (momentNormalizedPotential F) q.1 := by
  calc
    (∑ i, Complex.normSq
      (momentTorusRepresentative K hk F htransport
        (b i) q)) =
      ∑ i, Complex.normSq
        (momentHolomorphicRepresentative K hk F htransport
          (b i) (sourceTorusCoverPoint q)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [momentTorusRepresentative_eq_holomorphicRepresentative_cover]
    _ = diagonalKernel K k (momentNormalizedPotential F)
      (BergmanDiagonalBasisIndependence.realLogCoordinate
        (sourceTorusCoverPoint q)) :=
      sum_momentHolomorphicBasisWeight_eq_diagonalKernel
        K hk F htransport b (sourceTorusCoverPoint q)
    _ = diagonalKernel K k (momentNormalizedPotential F) q.1 := by
      rw [realLogCoordinate_sourceTorusCoverPoint]

private theorem integrable_momentDiagonalKernel_weightedTorus
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    Integrable
      (fun q : LogTorus n =>
        diagonalKernel K k (momentNormalizedPotential F) q.1)
      (weightedTorusMeasure k (momentNormalizedPotential F)) := by
  let b := momentMonomialOrthonormalBasis K hk F htransport
  have hsum : Integrable
      (fun q : LogTorus n =>
        ∑ i : Fin (bergmanDimension K k),
          Complex.normSq
            (momentTorusRepresentative
              K hk F htransport (b i) q))
      (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    integrable_finsetSum _ (fun i _ =>
      integrable_momentTorusRepresentative_normSq
        K hk F htransport (b i))
  exact hsum.congr
    (Filter.Eventually.of_forall fun q =>
      sum_momentTorusRepresentative_normSq_eq_diagonalKernel
        K hk F htransport b q)

private theorem integral_momentDiagonalKernel_weightedTorus
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    (∫ q : LogTorus n,
      diagonalKernel K k (momentNormalizedPotential F) q.1
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
        (bergmanDimension K k : ℝ) := by
  let b := momentMonomialOrthonormalBasis K hk F htransport
  calc
    (∫ q : LogTorus n,
      diagonalKernel K k (momentNormalizedPotential F) q.1
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) =
      ∫ q : LogTorus n,
        (∑ i : Fin (bergmanDimension K k),
          Complex.normSq
            (momentTorusRepresentative K hk F htransport
              (b i) q))
        ∂(weightedTorusMeasure k (momentNormalizedPotential F)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with q
          exact (sum_momentTorusRepresentative_normSq_eq_diagonalKernel
            K hk F htransport b q).symm
    _ = ∑ i : Fin (bergmanDimension K k),
          ∫ q : LogTorus n,
            Complex.normSq
              (momentTorusRepresentative K hk F htransport
                (b i) q)
            ∂(weightedTorusMeasure k
              (momentNormalizedPotential F)) := by
          rw [MeasureTheory.integral_finsetSum]
          intro i _
          exact integrable_momentTorusRepresentative_normSq
            K hk F htransport (b i)
    _ = (bergmanDimension K k : ℝ) := by
      have hunit (i : Fin (bergmanDimension K k)) :
          (∫ q : LogTorus n,
            Complex.normSq
              (momentTorusRepresentative K hk F htransport
                (b i) q)
              ∂(weightedTorusMeasure k
                (momentNormalizedPotential F))) = 1 := by
        rw [integral_momentTorusRepresentative_normSq]
        rw [b.orthonormal.norm_eq_one i]
        norm_num
      simp_rw [hunit]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

private theorem continuous_momentDiagonalKernel
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (diagonalKernel K k (momentNormalizedPotential F)) := by
  classical
  let := (monomialIndex_finite K hk).fintype
  unfold diagonalKernel
  simp_rw [tsum_fintype]
  apply continuous_finsetSum
  intro u _
  unfold diagonalTerm SupportFunction.pairing
  fun_prop

private def momentTorusBergmanProbability
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) (k : ℕ) : Measure (LogTorus n) :=
  (weightedTorusMeasure k (momentNormalizedPotential F)).withDensity
    (fun q : LogTorus n =>
      ENNReal.ofReal
        (diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ)))

private theorem momentTorusBergmanProbability_univ
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    momentTorusBergmanProbability K F k Set.univ = 1 := by
  have hdim : 0 < (bergmanDimension K k : ℝ) := by
    exact_mod_cast bergmanDimension_pos K hk
  have hint : Integrable
      (fun q : LogTorus n =>
        diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ))
      (weightedTorusMeasure k (momentNormalizedPotential F)) :=
    (integrable_momentDiagonalKernel_weightedTorus
      K hk F htransport).div_const _
  unfold momentTorusBergmanProbability
  rw [MeasureTheory.withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun q =>
      div_nonneg
        (diagonalKernel_momentNormalized_pos
          K hk F htransport q.1).le hdim.le),
    MeasureTheory.integral_div,
    integral_momentDiagonalKernel_weightedTorus
      K hk F htransport]
  rw [div_self hdim.ne', ENNReal.ofReal_one]

private theorem momentTorusBergmanProbability_isProbability
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K) :
    IsProbabilityMeasure (momentTorusBergmanProbability K F k) :=
  ⟨momentTorusBergmanProbability_univ K hk F htransport⟩

private def momentPositiveTorusJetSlope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) : ℝ :=
  momentTorusTruncatedJetOrderDensity
      K hk F htransport p N q /
    ((k : ℝ) * diagonalKernel K k
      (momentNormalizedPotential F) q.1)

private theorem momentTorusNormalizedDensity_mul_positiveJetSlope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) (q : LogTorus n) :
    (diagonalKernel K k (momentNormalizedPotential F) q.1 /
      (bergmanDimension K k : ℝ)) *
        momentPositiveTorusJetSlope
          K hk F htransport p N q =
      momentTorusTruncatedJetOrderDensity
        K hk F htransport p N q /
          ((k : ℝ) * (bergmanDimension K k : ℝ)) := by
  have hkreal : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  have hdim : (bergmanDimension K k : ℝ) ≠ 0 := by
    exact_mod_cast (bergmanDimension_pos K hk).ne'
  have hdiag :
      diagonalKernel K k (momentNormalizedPotential F) q.1 ≠ 0 :=
    (diagonalKernel_momentNormalized_pos
      K hk F htransport q.1).ne'
  unfold momentPositiveTorusJetSlope
  field_simp

private theorem integral_momentPositiveTorusJetSlope
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (N : ℕ) :
    (∫ q : LogTorus n,
      momentPositiveTorusJetSlope K hk F htransport p N q
        ∂(momentTorusBergmanProbability K F k)) =
      (∑ i : Fin (bergmanDimension K k),
        (momentTruncatedJetOrder
          K hk F htransport p N i : ℝ)) /
        ((k : ℝ) * (bergmanDimension K k : ℝ)) := by
  let d : LogTorus n → ℝ≥0∞ := fun q =>
    ENNReal.ofReal
      (diagonalKernel K k (momentNormalizedPotential F) q.1 /
        (bergmanDimension K k : ℝ))
  have hdmeas : Measurable d :=
    ENNReal.measurable_ofReal.comp
      (((continuous_momentDiagonalKernel K hk F).div_const
        (bergmanDimension K k : ℝ)).comp
          continuous_fst).measurable
  have hfinite :
      ∀ᵐ q ∂(weightedTorusMeasure k (momentNormalizedPotential F)),
        d q < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  unfold momentTorusBergmanProbability
  rw [integral_withDensity_eq_integral_toReal_smul hdmeas hfinite]
  have hdim : 0 < (bergmanDimension K k : ℝ) := by
    exact_mod_cast bergmanDimension_pos K hk
  change
    (∫ q : LogTorus n,
      (ENNReal.ofReal
        (diagonalKernel K k (momentNormalizedPotential F) q.1 /
          (bergmanDimension K k : ℝ))).toReal *
        momentPositiveTorusJetSlope K hk F htransport p N q
      ∂(weightedTorusMeasure k (momentNormalizedPotential F))) = _
  simp_rw [ENNReal.toReal_ofReal
    (div_nonneg
      (diagonalKernel_momentNormalized_pos
        K hk F htransport _).le hdim.le),
    momentTorusNormalizedDensity_mul_positiveJetSlope
      K hk F htransport p N]
  rw [MeasureTheory.integral_div,
    integral_momentTorusTruncatedJetOrderDensity
      K hk F htransport p N]

private theorem integral_momentPositiveTorusJetSlope_eq_normalizedProfile
    {n k : ℕ} (K : CenteredBody n) (hk : 0 < k)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (t : ℝ) :
    (∫ q : LogTorus n,
      momentPositiveTorusJetSlope
        K hk F htransport p (Nat.floor (t * (k : ℝ))) q
        ∂(momentTorusBergmanProbability K F k)) =
      normalizedMomentTruncatedJetOrderProfile
        K F htransport p t k := by
  rw [integral_momentPositiveTorusJetSlope]
  simp only [normalizedMomentTruncatedJetOrderProfile, hk, ↓reduceDIte]

private theorem eventually_integral_momentPositiveTorusJetSlope_ge_sharp
    {n : ℕ} (hn : 0 < n) (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ hk : 0 < k,
      (n : ℝ) * BodyScale.canonicalScale K /
          ((n : ℝ) + 1) - ε ≤
        ∫ q : LogTorus n,
          momentPositiveTorusJetSlope
            K hk F htransport p
            (Nat.floor
              (BodyScale.canonicalScale K * (k : ℝ))) q
          ∂(momentTorusBergmanProbability K F k) := by
  filter_upwards
    [eventually_normalizedMomentTruncatedJetOrderProfile_ge_sharp
      hn K F htransport p hε]
    with k hlower hk
  rw [integral_momentPositiveTorusJetSlope_eq_normalizedProfile
    K hk F htransport p (BodyScale.canonicalScale K)]
  exact hlower

end BergmanJetTorusSlopeBridge

namespace JetEnvelopeTrueRadialLocalHessian

open Set Filter Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialComplexHessianPositivity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private theorem sourceJointCircleRadiusProfile_isLocalMin_of_local_circle_submean
    {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    IsLocalMin (sourceJointCircleRadiusProfile f q v) 0 := by
  obtain ⟨ρ, hρ, hmean⟩ := hmean
  have hnear : ∀ᶠ r : ℝ in 𝓝 0, |r| < ρ := by
    have hzero : |(0 : ℝ)| < ρ := by simpa only [abs_zero] using hρ
    exact (continuous_abs.tendsto (0 : ℝ)).eventually
      (Iio_mem_nhds hzero)
  filter_upwards [hnear] with r hr
  rw [sourceJointCircleRadiusProfile_zero]
  exact hmean r hr

private theorem sourceJointCircleRadiusProfile_second_derivative_nonnegative_of_local_circle_submean
    {n : ℕ}
    (f : SourceJointComplexCover n → ℝ)
    (hf : Continuous f)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    0 ≤ deriv (deriv (sourceJointCircleRadiusProfile f q v)) 0 :=
  local_min_second_derivative_nonnegative
    (sourceJointCircleRadiusProfile_isLocalMin_of_local_circle_submean
      f q v hmean)
    (continuous_sourceJointCircleRadiusProfile hf q v).continuousAt

private theorem sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (q v : SourceJointComplexCover n)
    (hmean : ∃ ρ : ℝ, 0 < ρ ∧
      ∀ r : ℝ, |r| < ρ →
        f q ≤ Real.circleAverage
          (fun w : ℂ => f (q + w • v)) 0 r) :
    0 ≤ sourceJointRealLeviQuadratic f q v := by
  have hsecond :=
    sourceJointCircleRadiusProfile_second_derivative_nonnegative_of_local_circle_submean
      f hf.continuous q v hmean
  rw [sourceJointCircleRadiusProfile_second_eq_realHessian
    hf q v] at hsecond
  unfold sourceJointRealLeviQuadratic
  linarith

private theorem sourceJointSpatialComplexHessian_posSemidef_of_local_circle_submean
    {n : ℕ}
    {f : SourceJointComplexCover n → ℝ}
    (hf : ContDiff ℝ 2 f)
    (hmean : ∀ (q v : SourceJointComplexCover n),
      ∃ ρ : ℝ, 0 < ρ ∧
        ∀ r : ℝ, |r| < ρ →
          f q ≤ Real.circleAverage
            (fun w : ℂ => f (q + w • v)) 0 r)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    (sourceJointSpatialComplexHessian f τ z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (sourceJointSpatialComplexHessian_isHermitian hf τ z)
  intro x
  rw [sourceJointSpatialComplexHessian_quadratic_eq_realLevi
    hf τ z x]
  apply (Complex.nonneg_iff).2
  constructor
  · simpa only [Complex.ofReal_re] using
      sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
        hf (z, τ) (star x, 0) (hmean (z, τ) (star x, 0))
  · simp only [Complex.ofReal_im]

end JetEnvelopeTrueRadialLocalHessian

namespace RadialSchurBlock

open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic EnvelopeGeneralTorusDescent SchurConvexity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private def sourceComplexRowSchurEnergyDensity {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) : ℝ :=
  complexSchurEnergyDensity A (star b)

private theorem sourceComplexRowSchurEnergyDensity_eq {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) :
    sourceComplexRowSchurEnergyDensity A b =
      (b ⬝ᵥ (A⁻¹ *ᵥ star b)).re := by
  simp only [sourceComplexRowSchurEnergyDensity, complexSchurEnergyDensity, star_star]

private theorem sourceComplexRowSchurEnergyDensity_nonneg {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) :
    0 ≤ sourceComplexRowSchurEnergyDensity A b :=
  complexSchurEnergyDensity_nonneg hA (star b)

private def sourceComplexRowSchurBlock {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
  Matrix.fromBlocks A (complexSchurColumn (star b))
    (complexSchurColumn (star b))ᴴ (complexSchurScalar c)

private theorem sourceComplexRowSchurBlock_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian)
    (b : Fin n → ℂ) (c : ℝ) :
    (sourceComplexRowSchurBlock A b c).IsHermitian := by
  unfold sourceComplexRowSchurBlock
  apply Matrix.IsHermitian.fromBlocks hA rfl
  ext i j
  simp only [conjTranspose_apply, complexSchurScalar, RCLike.star_def, Complex.conj_ofReal]

private theorem sourceComplexRowSchurEnergy_le {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) (c : ℝ)
    (hblock : (sourceComplexRowSchurBlock A b c).PosSemidef) :
    sourceComplexRowSchurEnergyDensity A b ≤ c := by
  exact complex_schur_energy_le hA (star b) c hblock

private def sourceJointCoverAntiholomorphicVelocityGradient {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  sourceCoverAntiholomorphicGradient
    (fun w : TorusCharacters.LogSpace n =>
      (jointSourceCoverVelocity F (w, τ) : ℂ)) z

private def sourceJointCoverHolomorphicVelocityGradient {n : ℕ}
    (F : SourceJointComplexCover n → ℝ)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) : Fin n → ℂ :=
  fun i => holomorphicCoordinate
    (fun w : TorusCharacters.LogSpace n =>
      (jointSourceCoverVelocity F (w, τ) : ℂ)) z i

private theorem star_sourceJointCoverAntiholomorphicVelocityGradient
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n) :
    star (sourceJointCoverAntiholomorphicVelocityGradient F τ z) =
      sourceJointCoverHolomorphicVelocityGradient F τ z := by
  have hv : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        jointSourceCoverVelocity F (w, τ)) :=
    ((contDiff_jointSourceCoverVelocity hF).comp
      (contDiff_id.prodMk contDiff_const)).differentiable
        (by norm_num)
  ext i
  exact conj_barPartialCoordinate_real hv z i

private theorem sourceComplexSchurBlock_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (Matrix.fromBlocks A (complexSchurColumn b)
        (complexSchurColumn b)ᴴ (complexSchurScalar c) *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      (star (x ∘ Sum.inl) ⬝ᵥ b) * x (Sum.inr 0) +
      star (x (Sum.inr 0)) *
        (star b ⬝ᵥ (x ∘ Sum.inl)) +
      star (x (Sum.inr 0)) * (c : ℂ) * x (Sum.inr 0) := by
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, mulVec, Fintype.sum_sum_type,
    Finset.univ_unique, Fin.default_eq_zero, Fin.isValue, Finset.sum_singleton,
    fromBlocks_apply₁₁, fromBlocks_apply₁₂, complexSchurColumn, fromBlocks_apply₂₁,
    conjTranspose_apply, fromBlocks_apply₂₂, complexSchurScalar, comp_def, Function.comp_apply,
    Finset.mul_sum, Finset.sum_mul]
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  simp only [mul_comm, mul_assoc, Fin.isValue, mul_left_comm]
  ring

private theorem sourceComplexRowSchurBlock_quadratic {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ)
    (b : Fin n → ℂ) (c : ℝ)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ (sourceComplexRowSchurBlock A b c *ᵥ x) =
      star (x ∘ Sum.inl) ⬝ᵥ (A *ᵥ (x ∘ Sum.inl)) +
      (star (x ∘ Sum.inl) ⬝ᵥ star b) * x (Sum.inr 0) +
      star (x (Sum.inr 0)) *
        (b ⬝ᵥ (x ∘ Sum.inl)) +
      star (x (Sum.inr 0)) * (c : ℂ) * x (Sum.inr 0) := by
  unfold sourceComplexRowSchurBlock
  simpa only [Fin.isValue, RCLike.star_def,
    star_star] using sourceComplexSchurBlock_quadratic A (star b) c x

end RadialSchurBlock

namespace RadialFullLeviFoundations

open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open RadialSchurBlock WeightedDolbeaultBochnerIdentity
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private theorem sourceJointImaginaryTime_fderiv_eq_zero
    {n : ℕ} {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (q : SourceJointComplexCover n) :
    (fderiv ℝ F q)
      ((0 : TorusCharacters.LogSpace n), Complex.I) = 0 := by
  let v : SourceJointComplexCover n :=
    ((0 : TorusCharacters.LogSpace n), Complex.I)
  have hline :
      (fun r : ℝ => F (q + r • v)) = fun _ : ℝ => F q := by
    funext r
    have hr : r • v =
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I) := by
      apply Prod.ext
      · ext i
        simp only [Prod.smul_mk, smul_zero, Complex.real_smul, Pi.zero_apply, v]
      · simp only [Prod.smul_mk, smul_zero, Complex.real_smul, v]
    rw [hr]
    exact hperiod r q
  have hzero : q + (0 : ℝ) • v = q := by
    apply Prod.ext
    · ext i
      simp only [zero_smul, add_zero, v]
    · simp only [zero_smul, add_zero, v]
  have hder :=
    (hasDerivAt_sourceJointCircleLine hF q v 0).deriv
  rw [hline, hzero] at hder
  simpa only [deriv_const'] using hder.symm

private theorem sourceJointImaginaryTime_sndFDeriv_eq_zero
    {n : ℕ} {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (q w : SourceJointComplexCover n) :
    ((fderiv ℝ (fderiv ℝ F) q) w)
      ((0 : TorusCharacters.LogSpace n), Complex.I) = 0 := by
  have hfun :
      (fun ξ : SourceJointComplexCover n =>
        (fderiv ℝ F ξ)
          ((0 : TorusCharacters.LogSpace n), Complex.I)) =
      (fun _ : SourceJointComplexCover n => (0 : ℝ)) := by
    funext ξ
    exact sourceJointImaginaryTime_fderiv_eq_zero hF hperiod ξ
  rw [← fderiv_sourceJointRealDirectional hF q
    ((0 : TorusCharacters.LogSpace n), Complex.I) w,
    hfun]
  simp only [fderiv_fun_const, Pi.zero_apply, _root_.zero_apply]

private theorem sourceJointCoverHolomorphicVelocityGradient_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n)
    (i : Fin n) :
    sourceJointCoverHolomorphicVelocityGradient F τ z i =
      ((((fderiv ℝ (fderiv ℝ F) (z, τ))
          (Pi.single i (1 : ℂ), (0 : ℂ))
          (sourceJointTimeDirection n) : ℝ) : ℂ) -
        Complex.I *
          (((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Pi.single i Complex.I, (0 : ℂ))
            (sourceJointTimeDirection n) : ℝ) : ℂ)) / 2 := by
  have hv : Differentiable ℝ
      (fun w : TorusCharacters.LogSpace n =>
        jointSourceCoverVelocity F (w, τ)) :=
    ((contDiff_jointSourceCoverVelocity hF).comp
      (contDiff_id.prodMk contDiff_const)).differentiable
        (by norm_num)
  unfold sourceJointCoverHolomorphicVelocityGradient
    holomorphicCoordinate
  rw [DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hv z (Pi.single i (1 : ℂ)),
    DolbeaultGraphDistributionBridge.fderiv_complexOfReal
      hv z (Pi.single i Complex.I)]
  rw [fderiv_sourceJointSpatialSlice_apply
      ((contDiff_jointSourceCoverVelocity hF).differentiable
        (by norm_num)) τ z (Pi.single i (1 : ℂ)),
    fderiv_sourceJointSpatialSlice_apply
      ((contDiff_jointSourceCoverVelocity hF).differentiable
        (by norm_num)) τ z (Pi.single i Complex.I)]
  unfold jointSourceCoverVelocity
  rw [fderiv_sourceJointRealDirectional hF (z, τ)
      (sourceJointTimeDirection n)
      (Pi.single i (1 : ℂ), (0 : ℂ)),
    fderiv_sourceJointRealDirectional hF (z, τ)
      (sourceJointTimeDirection n)
      (Pi.single i Complex.I, (0 : ℂ))]

end RadialFullLeviFoundations

namespace RadialFullLeviSchur

open Set Function Matrix
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialComplexHessianPositivity
open EnvelopeTorusDescent EnvelopeGeneralTorusDescent RadialSchurBlock RadialFullLeviFoundations
open scoped BigOperators ComplexConjugate ComplexOrder Topology ContDiff

private theorem sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
    {n : ℕ}
    (B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ)
    (u : TorusCharacters.LogSpace n)
    (t : SourceJointComplexCover n) :
    (B (u, 0)) t =
      ∑ i : Fin n,
        ((u i).re * (B (Pi.single i (1 : ℂ), 0)) t +
          (u i).im * (B (Pi.single i Complex.I, 0)) t) := by
  classical
  let U : Fin n → SourceJointComplexCover n := fun i =>
    ((u i).re •
        (Pi.single i (1 : ℂ) : TorusCharacters.LogSpace n) +
      (u i).im •
        (Pi.single i Complex.I : TorusCharacters.LogSpace n), 0)
  have hu : (u, (0 : ℂ)) = ∑ i, U i := by
    apply Prod.ext
    · change u = (∑ i, U i).1
      have hfst :
          (∑ i, U i).1 = ∑ i, (U i).1 := by
        change
          (ContinuousLinearMap.fst ℝ
            (TorusCharacters.LogSpace n) ℂ) (∑ i, U i) =
            ∑ i,
              (ContinuousLinearMap.fst ℝ
                (TorusCharacters.LogSpace n) ℂ) (U i)
        exact map_sum
          (ContinuousLinearMap.fst ℝ
            (TorusCharacters.LogSpace n) ℂ)
          U Finset.univ
      rw [hfst]
      simpa only [U] using sourceSpatialRealBasis_decomposition u
    · change (0 : ℂ) = (∑ i, U i).2
      have hsnd :
          (∑ i, U i).2 = ∑ i, (U i).2 := by
        change
          (ContinuousLinearMap.snd ℝ
            (TorusCharacters.LogSpace n) ℂ) (∑ i, U i) =
            ∑ i,
              (ContinuousLinearMap.snd ℝ
                (TorusCharacters.LogSpace n) ℂ) (U i)
        exact map_sum
          (ContinuousLinearMap.snd ℝ
            (TorusCharacters.LogSpace n) ℂ)
          U Finset.univ
      rw [hsnd]
      simp only [Finset.sum_const_zero, U]
  calc
    (B (u, 0)) t = (B (∑ i, U i)) t := by rw [hu]
    _ = ∑ i, (B (U i)) t := by
      simpa only [ContinuousLinearMap.flip_apply] using
        (map_sum (B.flip t) U Finset.univ)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      have hp :
          U i =
            (u i).re •
                ((Pi.single i (1 : ℂ) :
                  TorusCharacters.LogSpace n), (0 : ℂ)) +
              (u i).im •
                ((Pi.single i Complex.I :
                  TorusCharacters.LogSpace n), (0 : ℂ)) := by
        apply Prod.ext
        · rfl
        · simp only [Prod.smul_mk, smul_zero, Prod.mk_add_mk, add_zero, U]
      calc
        (B (U i)) t =
            (B ((u i).re •
              ((Pi.single i (1 : ℂ) :
                TorusCharacters.LogSpace n), (0 : ℂ)) +
                (u i).im •
                  ((Pi.single i Complex.I :
                    TorusCharacters.LogSpace n), (0 : ℂ)))) t := by
              rw [hp]
        _ = _ := by
          rw [map_add, map_smul, map_smul]
          simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul]

private theorem sourceJointCoverHolomorphicVelocityGradient_dot_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z u : TorusCharacters.LogSpace n) :
    u ⬝ᵥ sourceJointCoverHolomorphicVelocityGradient F τ z =
      ((↑(((fderiv ℝ (fderiv ℝ F) (z, τ)) (u, 0))
          (sourceJointTimeDirection n)) : ℂ) -
        Complex.I *
          (↑(((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Complex.I • u, 0))
            (sourceJointTimeDirection n)) : ℂ)) / 2 := by
  classical
  simp only [dotProduct]
  simp_rw [sourceJointCoverHolomorphicVelocityGradient_eq_sndFDeriv hF τ z]
  rw [sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
      (fderiv ℝ (fderiv ℝ F) (z, τ)) u
      (sourceJointTimeDirection n),
    sourceJointRealBilinear_spatial_apply_eq_realBasis_sum
      (fderiv ℝ (fderiv ℝ F) (z, τ)) (Complex.I • u)
      (sourceJointTimeDirection n)]
  simp only [Pi.smul_apply, smul_eq_mul,
    Complex.I_mul_re, Complex.I_mul_im]
  push_cast
  let A : Fin n → ℝ := fun i =>
    ((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Pi.single i (1 : ℂ), 0)) (sourceJointTimeDirection n)
  let C : Fin n → ℝ := fun i =>
    ((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Pi.single i Complex.I, 0)) (sourceJointTimeDirection n)
  have hpoint (i : Fin n) :
      u i * (((A i : ℂ) - Complex.I * (C i : ℂ)) / 2) =
        (((u i).re : ℂ) * (A i : ℂ) +
          ((u i).im : ℂ) * (C i : ℂ) -
          Complex.I *
            (-((u i).im : ℂ) * (A i : ℂ) +
              ((u i).re : ℂ) * (C i : ℂ))) / 2 := by
    rw [← Complex.re_add_im (u i)]
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.mul_re, Complex.mul_im,
      mul_zero, mul_one,
      add_zero, zero_add, sub_zero]
    ring_nf
    simp only [Complex.I_sq]
    ring
  change
    (∑ i : Fin n,
      u i * (((A i : ℂ) - Complex.I * (C i : ℂ)) / 2)) =
      ((∑ i : Fin n,
          (((u i).re : ℂ) * (A i : ℂ) +
            ((u i).im : ℂ) * (C i : ℂ))) -
        Complex.I *
          (∑ i : Fin n,
            (-((u i).im : ℂ) * (A i : ℂ) +
              ((u i).re : ℂ) * (C i : ℂ)))) / 2
  simp_rw [hpoint]
  rw [← Finset.sum_div]
  congr 1
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, Finset.sum_add_distrib]

private theorem jointSourceCoverAcceleration_eq_sndFDeriv
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (q : SourceJointComplexCover n) :
    jointSourceCoverAcceleration F q =
      ((fderiv ℝ (fderiv ℝ F) q)
        (sourceJointTimeDirection n))
        (sourceJointTimeDirection n) := by
  unfold jointSourceCoverAcceleration jointSourceCoverVelocity
  exact fderiv_sourceJointRealDirectional hF q
    (sourceJointTimeDirection n) (sourceJointTimeDirection n)

private theorem sourceJointComplexTime_decomposition
    {n : ℕ} (s : ℂ) :
    ((0 : TorusCharacters.LogSpace n), s) =
      (2 * s.re) • sourceJointTimeDirection n +
        s.im • ((0 : TorusCharacters.LogSpace n), Complex.I) := by
  apply Prod.ext
  · ext i
    simp only [Pi.zero_apply, sourceJointTimeDirection, one_div, Prod.smul_mk, smul_zero,
      Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat, Prod.mk_add_mk, add_zero]
  · simp only [sourceJointTimeDirection, one_div, Prod.smul_mk, smul_zero, Complex.real_smul,
      Complex.ofReal_mul, Complex.ofReal_ofNat, Prod.mk_add_mk, add_zero]
    simpa only [mul_comm, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_inv_cancel_right₀] using (Complex.re_add_im s).symm

private theorem sourceJointCoverAntiholomorphicVelocityGradient_dot_eq_star_holomorphic
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (τ : ℂ)
    (z y : TorusCharacters.LogSpace n) :
    sourceJointCoverAntiholomorphicVelocityGradient F τ z ⬝ᵥ y =
      star ((star y) ⬝ᵥ
        sourceJointCoverHolomorphicVelocityGradient F τ z) := by
  rw [← star_sourceJointCoverAntiholomorphicVelocityGradient hF τ z]
  simp only [dotProduct, mul_comm, Pi.star_apply, RCLike.star_def, star_sum, star_mul',
    RingHomCompTriple.comp_apply, RingHom.id_apply]

private theorem sourceJointRealLeviQuadratic_eq_spatial_mixed_time
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (τ : ℂ)
    (z u : TorusCharacters.LogSpace n)
    (s : ℂ) :
    sourceJointRealLeviQuadratic F (z, τ) (u, s) =
      sourceJointRealLeviQuadratic F (z, τ) (u, 0) +
        s.re *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (u, 0)) (sourceJointTimeDirection n) -
        s.im *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (Complex.I • u, 0)) (sourceJointTimeDirection n) +
        (s.re ^ 2 + s.im ^ 2) *
          ((fderiv ℝ (fderiv ℝ F) (z, τ))
            (sourceJointTimeDirection n))
            (sourceJointTimeDirection n) := by
  let B : SourceJointComplexCover n →L[ℝ]
      SourceJointComplexCover n →L[ℝ] ℝ :=
    fderiv ℝ (fderiv ℝ F) (z, τ)
  let T : SourceJointComplexCover n := sourceJointTimeDirection n
  let J : SourceJointComplexCover n :=
    ((0 : TorusCharacters.LogSpace n), Complex.I)
  let U : SourceJointComplexCover n := (u, 0)
  let V : SourceJointComplexCover n := (Complex.I • u, 0)
  have hsymm (a b : SourceJointComplexCover n) :
      (B a) b = (B b) a :=
    (hF.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq a b
  have hJ (w : SourceJointComplexCover n) : (B w) J = 0 := by
    exact sourceJointImaginaryTime_sndFDeriv_eq_zero hF hperiod
      (z, τ) w
  have hJleft (w : SourceJointComplexCover n) : (B J) w = 0 := by
    rw [hsymm]
    exact hJ w
  have hv :
      (u, s) = U + (2 * s.re) • T + s.im • J := by
    calc
      (u, s) = (u, 0) + ((0 : TorusCharacters.LogSpace n), s) := by
        ext <;> simp
      _ = U + (2 * s.re) • T + s.im • J := by
        rw [sourceJointComplexTime_decomposition s]
        dsimp [U, T, J]
        abel
  have hi :
      Complex.I • (u, s) =
        V + (-2 * s.im) • T + s.re • J := by
    change (Complex.I • u, Complex.I * s) =
      V + (-2 * s.im) • T + s.re • J
    calc
      (Complex.I • u, Complex.I * s) =
          (Complex.I • u, 0) +
            ((0 : TorusCharacters.LogSpace n),
              Complex.I * s) := by
          ext <;> simp
      _ = V + (-2 * s.im) • T + s.re • J := by
        rw [sourceJointComplexTime_decomposition (Complex.I * s)]
        simp only [Complex.I_mul_re, Complex.I_mul_im]
        dsimp [V, T, J]
        module
  have hIU : Complex.I • U = V := by
    ext <;> simp [U, V]
  unfold sourceJointRealLeviQuadratic
  change
    ((B (u, s)) (u, s) +
      (B (Complex.I • (u, s))) (Complex.I • (u, s))) / 4 =
      ((B U) U + (B (Complex.I • U)) (Complex.I • U)) / 4 +
        s.re * (B U) T - s.im * (B V) T +
        (s.re ^ 2 + s.im ^ 2) * (B T) T
  rw [hi, hv, hIU]
  simp only [map_add, map_smul, _root_.add_apply,
    _root_.smul_apply, smul_eq_mul,
    hJ, hJleft, mul_zero, add_zero]
  rw [hsymm T U, hsymm T V]
  ring

private theorem complex_sourceRowSchurMixedScalar_eq_real
    (a : ℂ) (L P Q R : ℝ) :
    (L : ℂ) +
        (((P : ℂ) - Complex.I * (Q : ℂ)) / 2) * a +
        star a * star (((P : ℂ) - Complex.I * (Q : ℂ)) / 2) +
        star a * (R : ℂ) * a =
      (↑(L + (star a).re * P - (star a).im * Q +
        ((star a).re ^ 2 + (star a).im ^ 2) * R) : ℂ) := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, pow_two] <;>
    ring

private theorem sourceJointCoverRowSchurBlock_quadratic_eq_realLevi
    {n : ℕ}
    {F : SourceJointComplexCover n → ℝ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ r : ℝ,
      Function.Periodic F
        ((0 : TorusCharacters.LogSpace n),
          (r : ℂ) * Complex.I))
    (τ : ℂ)
    (z : TorusCharacters.LogSpace n)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (sourceComplexRowSchurBlock
        (sourceJointSpatialComplexHessian F τ z)
        (sourceJointCoverAntiholomorphicVelocityGradient F τ z)
        (jointSourceCoverAcceleration F (z, τ)) *ᵥ x) =
      (sourceJointRealLeviQuadratic F (z, τ)
        (star (x ∘ Sum.inl), star (x (Sum.inr 0))) : ℂ) := by
  rw [sourceComplexRowSchurBlock_quadratic]
  rw [sourceJointSpatialComplexHessian_quadratic_eq_realLevi
      hF τ z (x ∘ Sum.inl)]
  rw [star_sourceJointCoverAntiholomorphicVelocityGradient hF τ z]
  rw [sourceJointCoverAntiholomorphicVelocityGradient_dot_eq_star_holomorphic
      hF τ z (x ∘ Sum.inl)]
  rw [sourceJointCoverHolomorphicVelocityGradient_dot_eq_sndFDeriv
      hF τ z (star (x ∘ Sum.inl))]
  rw [jointSourceCoverAcceleration_eq_sndFDeriv hF (z, τ)]
  rw [sourceJointRealLeviQuadratic_eq_spatial_mixed_time hF hperiod τ z
      (star (x ∘ Sum.inl)) (star (x (Sum.inr 0)))]
  exact complex_sourceRowSchurMixedScalar_eq_real
    (x (Sum.inr 0))
    (sourceJointRealLeviQuadratic F (z, τ)
      (star (x ∘ Sum.inl), 0))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (star (x ∘ Sum.inl), 0)) (sourceJointTimeDirection n))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (Complex.I • star (x ∘ Sum.inl), 0))
      (sourceJointTimeDirection n))
    (((fderiv ℝ (fderiv ℝ F) (z, τ))
      (sourceJointTimeDirection n)) (sourceJointTimeDirection n))

end RadialFullLeviSchur

namespace BergmanJetJointEnvelopeRegularization

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters BergmanDiagonalBasisIndependence MomentOptimizer MomentTargetGeodesic
open MomentFirstVariation BergmanJetEnvelopeLimit BergmanJetTorusEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology ContDiff Convolution ComplexOrder

private def momentWeakJointCoverEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) : ℝ :=
  momentEnvelopeTimeSlice K F htransport p q.1
    (sourceJointCoverTime q)

private theorem momentWeakJointCoverEnvelope_of_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq) := by
  exact momentEnvelopeTimeSlice_of_positive
    K F htransport p q.1 hq

private theorem continuous_momentWeakJointRealLogCoordinate (n : ℕ) :
    Continuous (fun q : SourceJointComplexCover n =>
      realLogCoordinate q.1) := by
  apply continuous_pi
  intro j
  change Continuous
    (fun q : SourceJointComplexCover n => 2 * (q.1 j).re)
  fun_prop

end BergmanJetJointEnvelopeRegularization

namespace BergmanJetJointHolomorphicPhase

open Set Function Filter MeasureTheory
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal Topology

private theorem momentPositiveJointGeodesic_phase_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentPositiveJointGeodesic K F htransport p k
        (sourceJointPhaseHomeomorph u hu q) =
      momentPositiveJointGeodesic K F htransport p k q := by
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
    momentPositiveJointGeodesic_eq_momentJetGeodesic,
    sourceJointPhaseHomeomorph_spatial,
    jointLogTime_sourceJointPhaseHomeomorph]

private theorem momentJointTailSup_phase_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentJointTailSup K F htransport p r
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointTailSup K F htransport p r q := by
  unfold momentJointTailSup
  have hfun :
      (fun j : ℕ => momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          (sourceJointPhaseHomeomorph u hu q)) =
      (fun j : ℕ => momentPositiveJointGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentPositiveJointGeodesic_phase_invariant
      K F htransport p _ u hu q
  rw [hfun]

private theorem momentJointTailUpperEnvelope_phase_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentJointTailUpperEnvelope K F htransport p r
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointTailUpperEnvelope K F htransport p r q := by
  let h : PositiveJointLogSpace n ≃ₜ PositiveJointLogSpace n :=
    sourceJointPhaseHomeomorph (n := n) u hu
  have hfun :
      (fun z : PositiveJointLogSpace n =>
        momentJointTailSup K F htransport p r (h z)) =
        momentJointTailSup K F htransport p r := by
    funext z
    exact momentJointTailSup_phase_invariant
      K F htransport p r u hu z
  change
    upperRegularization
        (momentJointTailSup K F htransport p r) (h q) =
      upperRegularization
        (momentJointTailSup K F htransport p r) q
  rw [← upperRegularization_comp_homeomorph
    (momentJointTailSup K F htransport p r) h q, hfun]

private theorem momentJointUpperEnvelope_phase_invariant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (u : ℂ) (hu : ‖u‖ = 1)
    (q : PositiveJointLogSpace n) :
    momentJointUpperEnvelope K F htransport p
        (sourceJointPhaseHomeomorph u hu q) =
      momentJointUpperEnvelope K F htransport p q := by
  unfold momentJointUpperEnvelope
  congr 1
  funext r
  exact momentJointTailUpperEnvelope_phase_invariant
    K F htransport p r u hu q

private theorem momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourceJointExpPositiveLift q hq) := by
  let u : ℂ := Complex.exp ((q.2.im : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := sourceJointAuxiliaryPhase_norm q.2
  have hrad := momentWeakJointCoverEnvelope_of_positive
    K F htransport p q hq
  rw [sourceJointExpPositiveLift_eq_phase_radialLift]
  exact hrad.trans
    (momentJointUpperEnvelope_phase_invariant
      K F htransport p u hu
        (sourcePositiveJointTimePoint q.1
          (sourceJointCoverTime q) hq)).symm

end BergmanJetJointHolomorphicPhase

namespace BergmanJetJointHolomorphicClosure

open Set Function Filter MeasureTheory Metric
open TorusCharacters BergmanMonomials BergmanDiagonalBasisIndependence MomentOptimizer
open MomentTargetGeodesic MomentFirstVariation MomentRegularity MomentWeakBergman BergmanJetGeodesic
open BergmanJetRealGeodesic BergmanJetUpperEnvelope BergmanJetEnvelopePlurisubharmonic
open BergmanJetEnvelopeLimit BergmanJetJointEnvelopeRegularization BergmanJetJointHolomorphicPhase
open ActualJetUpperEnvelope ActualJetPlurisubharmonicEnvelope JetEnvelopeRightDerivative
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeGlobalPlurisubharmonicClosure
open BergmanGeodesicConvexity
open scoped BigOperators ENNReal Topology InnerProductSpace

private def momentWeakJointCoverFiniteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJetGeodesic K (Nat.zero_lt_succ k) F htransport p
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) q.1 (sourceJointCoverTime q)

private theorem momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q =
      Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) := by
  have hnorm :
      Complex.normSq (Complex.exp q.2) =
        Real.exp (sourceJointCoverTime q) := by
    simpa only [sourceJointCoverExp] using
      (normSq_sourceJointCoverExp q)
  have hrad := momentJointJetDiagonal_eq_radial
    K (Nat.zero_lt_succ k) F htransport p q.1
    (Nat.floor (BodyScale.canonicalScale K *
      ((k + 1 : ℕ) : ℝ))) (Complex.exp_ne_zero q.2)
  rw [hnorm, Real.log_exp] at hrad
  unfold momentWeakJointCoverFiniteGeodesic
  rw [momentJetGeodesic_eq_log_jointJetDiagonal, ← hrad]
  rfl

private theorem continuous_momentWeakJointCoverFiniteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) :
    Continuous (momentWeakJointCoverFiniteGeodesic
      K F htransport p k) := by
  have heq :
      momentWeakJointCoverFiniteGeodesic K F htransport p k =
        fun q : SourceJointComplexCover n =>
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p
              (Nat.floor (BodyScale.canonicalScale K *
                ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q)) /
              ((k + 1 : ℕ) : ℝ) := by
    funext q
    exact momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
      K F htransport p k q
  rw [heq]
  apply Continuous.div_const
  apply Continuous.log
    ((continuous_momentJointJetDiagonal
      K (Nat.zero_lt_succ k) F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ)))).comp
            (continuous_sourceJointCoverExp n))
  intro q
  exact (momentJointJetDiagonal_pos
    K (Nat.zero_lt_succ k) F htransport p
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ))) (sourceJointCoverExp q).1
        (show (sourceJointCoverExp q).2 ≠ 0 from
          Complex.exp_ne_zero q.2)).ne'

private theorem momentWeakJointCoverFiniteGeodesic_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q ≤
      Real.circleAverage
        (fun w : ℂ => momentWeakJointCoverFiniteGeodesic
          K F htransport p k (q + w • v)) 0 R := by
  let N := Nat.floor (BodyScale.canonicalScale K *
    ((k + 1 : ℕ) : ℝ))
  let G : ℂ → EuclideanSpace ℂ
      (Fin (bergmanDimension K (k + 1))) :=
    fun w => momentJointJetSectionVector
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp (q + w • v))
  have hline : Differentiable ℂ
      (fun w : ℂ => q + w • v) := by
    fun_prop
  have hG : Differentiable ℂ G := by
    simpa only [Nat.succ_eq_add_one, comp_def] using
      (differentiable_momentJointJetSectionVector
        K (Nat.zero_lt_succ k) F htransport p N).comp
          ((differentiable_sourceJointCoverExp n).comp hline)
  have hsection (y : SourceJointComplexCover n) :
      momentJointJetSectionVector
        K (Nat.zero_lt_succ k) F htransport p N
          (sourceJointCoverExp y) ≠ 0 := by
    intro hzero
    have hsquare := momentJointJetSectionVector_norm_sq
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp y)
    rw [hzero, norm_zero, zero_pow (by norm_num)] at hsquare
    have hpositive := momentJointJetDiagonal_pos
      K (Nat.zero_lt_succ k) F htransport p N
        (sourceJointCoverExp y).1
          (show (sourceJointCoverExp y).2 ≠ 0 from
            Complex.exp_ne_zero y.2)
    linarith
  have hzero : G 0 ≠ 0 := by
    simpa [G] using hsection q
  have hboundary :
      ∀ w ∈ Metric.sphere (0 : ℂ) |R|, G w ≠ 0 := by
    intro w _
    exact hsection (q + w • v)
  have hmean := log_hilbert_norm_sq_le_circleAverage_all_radius
    hG hzero R hboundary
  have hbase :
      Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p N
            (sourceJointCoverExp q)) ≤
        Real.circleAverage
          (fun w : ℂ => Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) 0 R := by
    simpa only [G, zero_smul, add_zero,
      momentJointJetSectionVector_norm_sq] using hmean
  have hkreal : 0 < ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_lt_succ k
  have hscaled := (div_le_div_iff_of_pos_right hkreal).mpr hbase
  have havg :
      Real.circleAverage
          (fun w : ℂ => Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) 0 R /
            ((k + 1 : ℕ) : ℝ) =
        Real.circleAverage
          (fun w : ℂ =>
            Real.log
              (momentJointJetDiagonal
                K (Nat.zero_lt_succ k) F htransport p N
                  (sourceJointCoverExp (q + w • v))) /
                ((k + 1 : ℕ) : ℝ)) 0 R := by
    rw [show
      (fun w : ℂ =>
        Real.log
          (momentJointJetDiagonal
            K (Nat.zero_lt_succ k) F htransport p N
              (sourceJointCoverExp (q + w • v))) /
            ((k + 1 : ℕ) : ℝ)) =
        (fun w : ℂ => (((k + 1 : ℕ) : ℝ)⁻¹) •
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v)))) by
        funext w
        simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm,
          smul_eq_mul],
      Real.circleAverage_fun_smul]
    simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_comm,
      smul_eq_mul]
  rw [momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
    K F htransport p k q]
  change
    Real.log
      (momentJointJetDiagonal
        K (Nat.zero_lt_succ k) F htransport p N
          (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) ≤ _
  calc
    Real.log
        (momentJointJetDiagonal
          K (Nat.zero_lt_succ k) F htransport p N
            (sourceJointCoverExp q)) /
        ((k + 1 : ℕ) : ℝ) ≤
      Real.circleAverage
        (fun w : ℂ => Real.log
          (momentJointJetDiagonal
            K (Nat.zero_lt_succ k) F htransport p N
              (sourceJointCoverExp (q + w • v)))) 0 R /
            ((k + 1 : ℕ) : ℝ) := hscaled
    _ = Real.circleAverage
        (fun w : ℂ =>
          Real.log
            (momentJointJetDiagonal
              K (Nat.zero_lt_succ k) F htransport p N
                (sourceJointCoverExp (q + w • v))) /
              ((k + 1 : ℕ) : ℝ)) 0 R := havg
    _ = Real.circleAverage
        (fun w : ℂ => momentWeakJointCoverFiniteGeodesic
          K F htransport p k (q + w • v)) 0 R := by
      congr 1
      funext w
      exact (momentWeakJointCoverFiniteGeodesic_eq_log_diagonal
        K F htransport p k (q + w • v)).symm

private theorem differentiable_momentWeakBodyScaleJetGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) :
    Differentiable ℝ
      (momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z) := by
  intro t
  unfold momentJetGeodesic
  exact (hasDerivAt_logarithmicPotential
    (momentHolomorphicBasisWeight
      K (Nat.zero_lt_succ k) F htransport
      (momentSimultaneousJetBasis
        K (Nat.zero_lt_succ k) F htransport p) z)
    (momentTruncatedJetOrder K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))))
    (momentHolomorphicBasisWeight_nonneg
      K (Nat.zero_lt_succ k) F htransport
        (momentSimultaneousJetBasis
          K (Nat.zero_lt_succ k) F htransport p) z)
    (exists_positive_momentHolomorphicBasisWeight
      K (Nat.zero_lt_succ k) F htransport
        (momentSimultaneousJetBasis
          K (Nat.zero_lt_succ k) F htransport p) z)
    ((k + 1 : ℕ) : ℝ) t).differentiableAt

private theorem momentWeakBodyScaleJetGeodesic_time_shift_le
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ)
    {s t : ℝ} (hst : s ≤ t) :
    momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z t ≤
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z s +
        BodyScale.canonicalScale K * (t - s) := by
  rcases hst.eq_or_lt with rfl | hst
  · simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, sub_self, mul_zero, add_zero,
      Std.le_refl]
  · let g := momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z
    have hg : Differentiable ℝ g :=
      differentiable_momentWeakBodyScaleJetGeodesic
        K F htransport p z k
    obtain ⟨c, _, hc⟩ := exists_deriv_eq_slope g hst
      hg.continuous.continuousOn hg.differentiableOn
    have hbound := momentJetGeodesic_deriv_le_floor_cutoff
      K (Nat.zero_lt_succ k) F htransport p
        (BodyScale.canonicalScale_pos K).le z c
    change deriv g c ≤ BodyScale.canonicalScale K at hbound
    rw [hc] at hbound
    have hpositive : 0 < t - s := sub_pos.mpr hst
    have hmul := (div_le_iff₀ hpositive).mp hbound
    change g t ≤ g s + BodyScale.canonicalScale K * (t - s)
    linarith

private theorem momentJointGlobalLowerBound_le_coverFiniteGeodesic_zero
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ) :
    momentJointGlobalLowerBound K F ≤
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z 0 := by
  calc
    momentJointGlobalLowerBound K F ≤
        Real.log
          (diagonalKernel K (k + 1)
            (momentNormalizedPotential F)
            (realLogCoordinate z)) / ((k + 1 : ℕ) : ℝ) :=
      momentJointGlobalLowerBound_le_log_diagonalKernel
        K (Nat.zero_lt_succ k) F htransport (realLogCoordinate z)
    _ = momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z 0 :=
      (momentJetGeodesic_zero_eq_log_diagonalKernel
        K (Nat.zero_lt_succ k) F htransport p z
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ)))).symm

private def momentWeakJointCoverFiniteMinorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentJointGlobalLowerBound K F +
    BodyScale.canonicalScale K *
      min (sourceJointCoverTime q) 0

private theorem continuous_momentWeakJointCoverFiniteMinorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakJointCoverFiniteMinorant K F) := by
  unfold momentWeakJointCoverFiniteMinorant
  exact continuous_const.add
    (continuous_const.mul
      ((continuous_sourceJointCoverTime n).min continuous_const))

private theorem momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverFiniteGeodesic
        K F htransport p k q := by
  have hzero := momentJointGlobalLowerBound_le_coverFiniteGeodesic_zero
    K F htransport p q.1 k
  by_cases ht : 0 ≤ sourceJointCoverTime q
  · have hmono := monotone_momentJetGeodesic
      K (Nat.zero_lt_succ k) F htransport p q.1
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) ht
    simpa only [momentWeakJointCoverFiniteMinorant, min_eq_right ht, mul_zero, add_zero,
      momentWeakJointCoverFiniteGeodesic, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
      ge_iff_le]
        using hzero.trans hmono
  · have hneg : sourceJointCoverTime q ≤ 0 := le_of_not_ge ht
    have hshift := momentWeakBodyScaleJetGeodesic_time_shift_le
      K F htransport p q.1 k hneg
    unfold momentWeakJointCoverFiniteMinorant
      momentWeakJointCoverFiniteGeodesic
    rw [min_eq_left hneg]
    linarith

private theorem momentWeakJointCoverFiniteGeodesic_zero_le_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p z : LogSpace n) (k : ℕ)
    (hk : momentJointTailStart K F htransport p ≤ k) :
    momentJetGeodesic K (Nat.zero_lt_succ k)
      F htransport p
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) z 0 ≤
      momentNormalizedPotential F (realLogCoordinate z) +
        BodyScale.canonicalScale K + 1 := by
  let hunit : (0 : ℝ) < 1 := by norm_num
  let q₁ : PositiveJointLogSpace n :=
    sourcePositiveJointTimePoint z 1 hunit
  have htail := momentPositiveJointGeodesic_le_majorant_add_one_of_tail
    K F htransport p k hk q₁
  have hmono := monotone_momentJetGeodesic
    K (Nat.zero_lt_succ k) F htransport p z
      (Nat.floor (BodyScale.canonicalScale K *
        ((k + 1 : ℕ) : ℝ)))
      (show (0 : ℝ) ≤ 1 by norm_num)
  have htime :
      momentPositiveJointGeodesic K F htransport p k q₁ =
        momentJetGeodesic K (Nat.zero_lt_succ k)
          F htransport p
            (Nat.floor (BodyScale.canonicalScale K *
              ((k + 1 : ℕ) : ℝ))) z 1 := by
    rw [momentPositiveJointGeodesic_eq_momentJetGeodesic]
    change
      momentJetGeodesic K (Nat.zero_lt_succ k)
        F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ))) z (jointLogTime q₁) = _
    rw [show jointLogTime q₁ = 1 by
      exact jointLogTime_sourcePositiveJointTimePoint z 1 hunit]
  have hmajor :
      momentJointMajorant K F q₁ =
        momentNormalizedPotential F (realLogCoordinate z) +
          BodyScale.canonicalScale K := by
    unfold momentJointMajorant
    rw [jointRealCoordinate_sourcePositiveJointTimePoint,
      jointLogTime_sourcePositiveJointTimePoint]
    ring
  rw [htime, hmajor] at htail
  exact hmono.trans htail

private def momentWeakJointCoverFiniteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  momentNormalizedPotential F (realLogCoordinate q.1) +
    BodyScale.canonicalScale K + 1 +
    BodyScale.canonicalScale K *
      max (sourceJointCoverTime q) 0

private theorem continuous_momentWeakJointCoverFiniteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakJointCoverFiniteMajorant K F) := by
  unfold momentWeakJointCoverFiniteMajorant
  exact (((((continuous_momentNormalizedPotential F).comp
    (continuous_momentWeakJointRealLogCoordinate n)).add
      continuous_const).add continuous_const)).add
        (continuous_const.mul
          ((continuous_sourceJointCoverTime n).max continuous_const))

private theorem momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (hk : momentJointTailStart K F htransport p ≤ k)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q ≤
      momentWeakJointCoverFiniteMajorant K F q := by
  have hzero := momentWeakJointCoverFiniteGeodesic_zero_le_of_tail
    K F htransport p q.1 k hk
  by_cases ht : 0 ≤ sourceJointCoverTime q
  · have hshift := momentWeakBodyScaleJetGeodesic_time_shift_le
      K F htransport p q.1 k ht
    unfold momentWeakJointCoverFiniteGeodesic
      momentWeakJointCoverFiniteMajorant
    rw [max_eq_left ht]
    linarith
  · have hneg : sourceJointCoverTime q ≤ 0 := le_of_not_ge ht
    have hmono := monotone_momentJetGeodesic
      K (Nat.zero_lt_succ k) F htransport p q.1
        (Nat.floor (BodyScale.canonicalScale K *
          ((k + 1 : ℕ) : ℝ))) hneg
    unfold momentWeakJointCoverFiniteGeodesic
      momentWeakJointCoverFiniteMajorant
    rw [max_eq_right hneg, mul_zero, add_zero]
    exact hmono.trans hzero

private def momentWeakJointCoverTailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  sSup (Set.range fun j : ℕ =>
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j) q)

private def momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) : SourceJointComplexCover n → ℝ :=
  upperRegularization (momentWeakJointCoverTailSup
    K F htransport p r)

private theorem momentWeakJointCoverTailSup_range_bddAbove
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    BddAbove (Set.range fun j : ℕ =>
      momentWeakJointCoverFiniteGeodesic K F htransport p
        (momentJointTailStart K F htransport p + r + j) q) := by
  refine ⟨momentWeakJointCoverFiniteMajorant K F q, ?_⟩
  rintro _ ⟨j, rfl⟩
  exact momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    K F htransport p
      (momentJointTailStart K F htransport p + r + j)
        (by omega) q

private theorem momentWeakJointCoverTailSup_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p r q ≤
      momentWeakJointCoverFiniteMajorant K F q := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  exact momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
    K F htransport p
      (momentJointTailStart K F htransport p + r + j)
        (by omega) q

private theorem momentWeakJointCoverTailSup_localUpperBounds_nonempty
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    (localUpperBounds
      (momentWeakJointCoverTailSup K F htransport p r) q).Nonempty :=
  localUpperBounds_nonempty_of_continuous_majorant
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverFiniteMajorant K F)
    (continuous_momentWeakJointCoverFiniteMajorant K F)
    (momentWeakJointCoverTailSup_le_majorant
      K F htransport p r) q

private theorem upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) :
    UpperSemicontinuous
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p r) :=
  upperSemicontinuous_upperRegularization
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r)

private theorem momentWeakJointCoverTailUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q ≤
        momentWeakJointCoverFiniteMajorant K F q :=
  upperRegularization_le_of_continuous_majorant
    (momentWeakJointCoverTailSup K F htransport p r)
    (momentWeakJointCoverFiniteMajorant K F)
    (continuous_momentWeakJointCoverFiniteMajorant K F)
    (momentWeakJointCoverTailSup_le_majorant
      K F htransport p r) q

private theorem momentWeakJointCoverFiniteMinorant_le_tailSup
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverTailSup K F htransport p r q := by
  calc
    momentWeakJointCoverFiniteMinorant K F q ≤
        momentWeakJointCoverFiniteGeodesic K F htransport p
          (momentJointTailStart K F htransport p + r) q :=
      momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r) q
    _ ≤ momentWeakJointCoverTailSup K F htransport p r q := by
      unfold momentWeakJointCoverTailSup
      apply le_csSup
        (momentWeakJointCoverTailSup_range_bddAbove
          K F htransport p r q)
      exact ⟨0, by simp only [add_zero]⟩

private theorem momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q := by
  calc
    momentWeakJointCoverFiniteMinorant K F q ≤
        momentWeakJointCoverTailSup K F htransport p r q :=
      momentWeakJointCoverFiniteMinorant_le_tailSup
        K F htransport p r q
    _ ≤ momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q :=
      le_upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q
        (momentWeakJointCoverTailSup_localUpperBounds_nonempty
          K F htransport p r q)

private theorem momentWeakJointCoverTailSup_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {r s : ℕ} (hrs : r ≤ s)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailSup K F htransport p s q ≤
      momentWeakJointCoverTailSup K F htransport p r q := by
  unfold momentWeakJointCoverTailSup
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨j, rfl⟩
  apply le_csSup
    (momentWeakJointCoverTailSup_range_bddAbove
      K F htransport p r q)
  have hindex :
      momentJointTailStart K F htransport p + r + (s - r + j) =
        momentJointTailStart K F htransport p + s + j := by
    omega
  refine ⟨s - r + j, ?_⟩
  change
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r +
        (s - r + j)) q =
    momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + s + j) q
  rw [hindex]

private theorem momentWeakJointCoverTailUpperEnvelope_antitone
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) {r s : ℕ} (hrs : r ≤ s)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p s q ≤
        momentWeakJointCoverTailUpperEnvelope
          K F htransport p r q :=
  upperRegularization_mono
    (momentWeakJointCoverTailSup K F htransport p s)
    (momentWeakJointCoverTailSup K F htransport p r) q
    (momentWeakJointCoverTailSup_antitone
      K F htransport p hrs)
    (momentWeakJointCoverTailSup_localUpperBounds_nonempty
      K F htransport p r q)

private theorem momentWeakJointCoverTailUpperEnvelope_bddBelow
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    BddBelow (Set.range fun r : ℕ =>
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q) := by
  refine ⟨momentWeakJointCoverFiniteMinorant K F q, ?_⟩
  rintro _ ⟨r, rfl⟩
  exact momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
    K F htransport p r q

private def momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) : ℝ :=
  ⨅ r : ℕ,
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q

private theorem upperSemicontinuous_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    UpperSemicontinuous
      (momentWeakJointCoverUpperEnvelope
        K F htransport p) :=
  upperSemicontinuous_ciInf
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p)
    (upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
      K F htransport p)

private theorem tendsto_momentWeakJointCoverTailUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    Tendsto
      (fun r : ℕ => momentWeakJointCoverTailUpperEnvelope
        K F htransport p r q) atTop
          (𝓝 (momentWeakJointCoverUpperEnvelope
            K F htransport p q)) :=
  tendsto_atTop_ciInf
    (fun _ _ hrs =>
      momentWeakJointCoverTailUpperEnvelope_antitone
        K F htransport p hrs q)
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p q)

private theorem momentWeakJointCoverFiniteMinorant_le_upperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverFiniteMinorant K F q ≤
      momentWeakJointCoverUpperEnvelope
        K F htransport p q :=
  (le_ciInf_iff
    (momentWeakJointCoverTailUpperEnvelope_bddBelow
      K F htransport p q)).mpr
      (fun r => momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
        K F htransport p r q)

private theorem momentWeakJointCoverUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope
      K F htransport p q ≤
        momentWeakJointCoverFiniteMajorant K F q := by
  calc
    momentWeakJointCoverUpperEnvelope
        K F htransport p q ≤
      momentWeakJointCoverTailUpperEnvelope
        K F htransport p 0 q :=
      ciInf_le (momentWeakJointCoverTailUpperEnvelope_bddBelow
        K F htransport p q) 0
    _ ≤ momentWeakJointCoverFiniteMajorant K F q :=
      momentWeakJointCoverTailUpperEnvelope_le_majorant
        K F htransport p 0 q

private theorem momentWeakJointCoverTailUpperEnvelope_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q ≤
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverTailUpperEnvelope
              K F htransport p r (q + w • v)) 0 R := by
  let G : ℕ → SourceJointComplexCover n → ℝ :=
    fun j => momentWeakJointCoverFiniteGeodesic K F htransport p
      (momentJointTailStart K F htransport p + r + j)
  have hGcont (j : ℕ) : Continuous (G j) :=
    continuous_momentWeakJointCoverFiniteGeodesic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
  have hlower (j : ℕ) (z : SourceJointComplexCover n) :
      momentWeakJointCoverFiniteMinorant K F z ≤ G j z :=
    momentWeakJointCoverFiniteMinorant_le_finiteGeodesic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) z
  have hmajor (j : ℕ) (z : SourceJointComplexCover n) :
      G j z ≤ momentWeakJointCoverFiniteMajorant K F z :=
    momentWeakJointCoverFiniteGeodesic_le_majorant_of_tail
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          (by omega) z
  have hsub (j : ℕ) (z v' : SourceJointComplexCover n)
      (R' : ℝ) :
      G j z ≤ Real.circleAverage
        (fun w : ℂ => G j (z + w • v')) 0 R' :=
    momentWeakJointCoverFiniteGeodesic_complex_line_submean_all_radius
      K F htransport p
        (momentJointTailStart K F htransport p + r + j)
          z v' R'
  have h :=
    sourceJointCover_upperRegularization_family_complex_line_submean_all_radius
      G hGcont
      (momentWeakJointCoverFiniteMinorant K F)
      (momentWeakJointCoverFiniteMajorant K F)
      (continuous_momentWeakJointCoverFiniteMinorant K F)
      (continuous_momentWeakJointCoverFiniteMajorant K F)
      hlower hmajor hsub q v R
  have hsup :
      (fun z : SourceJointComplexCover n =>
        sSup (Set.range fun j : ℕ => G j z)) =
        momentWeakJointCoverTailSup K F htransport p r := by
    funext z
    rfl
  change
    upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q ≤
      Real.circleAverage
        (fun w : ℂ =>
          upperRegularization
            (momentWeakJointCoverTailSup K F htransport p r)
            (q + w • v)) 0 R
  rw [← hsup]
  exact h

private theorem momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakJointCoverUpperEnvelope
      K F htransport p q ≤
        Real.circleAverage
          (fun w : ℂ => momentWeakJointCoverUpperEnvelope
            K F htransport p (q + w • v)) 0 R := by
  obtain ⟨L, C, hcompact⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds
      (momentWeakJointCoverFiniteMinorant K F)
      (momentWeakJointCoverFiniteMajorant K F)
      (continuous_momentWeakJointCoverFiniteMinorant K F)
      (continuous_momentWeakJointCoverFiniteMajorant K F)
      q v R
  have hqself : dist q q ≤ (1 : ℝ) := by simp only [dist_self, zero_le_one]
  have hbound (r : ℕ) (θ : ℝ) :
      L ≤ momentWeakJointCoverTailUpperEnvelope
          K F htransport p r
            (sourceJointCoverCirclePoint q v R θ) ∧
        momentWeakJointCoverTailUpperEnvelope
          K F htransport p r
            (sourceJointCoverCirclePoint q v R θ) ≤ C := by
    obtain ⟨hlo, hup⟩ := (hcompact q hqself).2 θ
    exact ⟨hlo.trans
      (momentWeakJointCoverFiniteMinorant_le_tailUpperEnvelope
        K F htransport p r _),
      (momentWeakJointCoverTailUpperEnvelope_le_majorant
        K F htransport p r _).trans hup⟩
  have havg := tendsto_circleAverage_sourceJointCover_of_dominated
    (fun r : ℕ => momentWeakJointCoverTailUpperEnvelope
      K F htransport p r)
    (momentWeakJointCoverUpperEnvelope K F htransport p)
    (fun r => upperSemicontinuous_momentWeakJointCoverTailUpperEnvelope
      K F htransport p r)
    (fun z => tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p z)
    q v R L C hbound
  exact le_of_tendsto_of_tendsto
    (tendsto_momentWeakJointCoverTailUpperEnvelope
      K F htransport p q)
    havg
    (Filter.Eventually.of_forall fun r =>
      momentWeakJointCoverTailUpperEnvelope_complex_line_submean_all_radius
        K F htransport p r q v R)

private theorem momentWeakJointCoverFiniteGeodesic_eq_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverFiniteGeodesic K F htransport p k q =
      momentPositiveJointGeodesic K F htransport p k
        (sourceJointExpPositiveLift q hq) := by
  rw [momentPositiveJointGeodesic_eq_momentJetGeodesic,
    jointLogTime_sourceJointExpPositiveLift]
  rfl

private theorem momentWeakJointCoverTailSup_eq_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverTailSup K F htransport p r q =
      momentJointTailSup K F htransport p r
        (sourceJointExpPositiveLift q hq) := by
  have hfamily :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) =
      (fun j : ℕ => momentPositiveJointGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
            (sourceJointExpPositiveLift q hq)) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_eq_positive
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) q hq
  unfold momentWeakJointCoverTailSup momentJointTailSup
  rw [hfamily]

private theorem momentWeakJointCoverTailUpperEnvelope_eq_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverTailUpperEnvelope
      K F htransport p r q =
      momentJointTailUpperEnvelope K F htransport p r
        (sourceJointExpPositiveLift q hq) := by
  let Q : PositiveSourceJointComplexCover n := ⟨q, hq⟩
  have hopenval : IsOpenMap
      (fun y : PositiveSourceJointComplexCover n => y.val) :=
    (isOpen_sourcePositiveCover n).isOpenEmbedding_subtypeVal.isOpenMap
  have hcontval : Continuous
      (fun y : PositiveSourceJointComplexCover n => y.val) :=
    continuous_subtype_val
  have hregval := upperRegularization_comp_isOpenMap
    (momentWeakJointCoverTailSup K F htransport p r)
    (fun y : PositiveSourceJointComplexCover n => y.val)
    hcontval hopenval Q
  have hregexp := upperRegularization_comp_isOpenMap
    (momentJointTailSup K F htransport p r)
    (sourcePositiveCoverExp (n := n))
    (continuous_sourcePositiveCoverExp n)
    (isOpenMap_sourcePositiveCoverExp n) Q
  have hfun :
      (fun y : PositiveSourceJointComplexCover n =>
        momentWeakJointCoverTailSup K F htransport p r y.val) =
      (fun y : PositiveSourceJointComplexCover n =>
        momentJointTailSup K F htransport p r
          (sourcePositiveCoverExp y)) := by
    funext y
    exact momentWeakJointCoverTailSup_eq_positive
      K F htransport p r y.val y.property
  unfold momentWeakJointCoverTailUpperEnvelope
    momentJointTailUpperEnvelope
  calc
    upperRegularization
        (momentWeakJointCoverTailSup K F htransport p r) q =
      upperRegularization
        (fun y : PositiveSourceJointComplexCover n =>
          momentWeakJointCoverTailSup
            K F htransport p r y.val) Q := hregval.symm
    _ = upperRegularization
        (fun y : PositiveSourceJointComplexCover n =>
          momentJointTailSup K F htransport p r
            (sourcePositiveCoverExp y)) Q := by rw [hfun]
    _ = upperRegularization
        (momentJointTailSup K F htransport p r)
          (sourcePositiveCoverExp Q) := hregexp
    _ = upperRegularization
        (momentJointTailSup K F htransport p r)
          (sourceJointExpPositiveLift q hq) := by rfl

private theorem momentWeakJointCoverUpperEnvelope_eq_positive
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverUpperEnvelope K F htransport p q =
      momentJointUpperEnvelope K F htransport p
        (sourceJointExpPositiveLift q hq) := by
  unfold momentWeakJointCoverUpperEnvelope momentJointUpperEnvelope
  simp_rw [momentWeakJointCoverTailUpperEnvelope_eq_positive
    K F htransport p _ q hq]

private theorem momentWeakJointCoverEnvelope_eq_upperEnvelope_of_pos
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n)
    (q : SourceJointComplexCover n)
    (hq : 0 < sourceJointCoverTime q) :
    momentWeakJointCoverEnvelope K F htransport p q =
      momentWeakJointCoverUpperEnvelope
        K F htransport p q := by
  rw [momentWeakJointCoverEnvelope_eq_holomorphicExpLift_of_pos
    K F htransport p q hq,
    momentWeakJointCoverUpperEnvelope_eq_positive
      K F htransport p q hq]

end BergmanJetJointHolomorphicClosure

namespace BergmanJetJointHolomorphicPlurisubharmonicSmoothing

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeGlobalPlurisubharmonicClosure JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)

private def momentWeakHolomorphicJointAbsoluteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (q : SourceJointComplexCover n) : ℝ :=
  |momentWeakJointCoverFiniteMinorant K F q| +
    |momentWeakJointCoverFiniteMajorant K F q|

private theorem continuous_momentWeakHolomorphicJointAbsoluteMajorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K) :
    Continuous (momentWeakHolomorphicJointAbsoluteMajorant K F) := by
  unfold momentWeakHolomorphicJointAbsoluteMajorant
  exact (continuous_momentWeakJointCoverFiniteMinorant K F).abs.add
    (continuous_momentWeakJointCoverFiniteMajorant K F).abs

private theorem norm_momentWeakJointCoverUpperEnvelope_le_majorant
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    ‖momentWeakJointCoverUpperEnvelope
        K F htransport p q‖ ≤
      momentWeakHolomorphicJointAbsoluteMajorant K F q := by
  rw [Real.norm_eq_abs]
  unfold momentWeakHolomorphicJointAbsoluteMajorant
  have hl := momentWeakJointCoverFiniteMinorant_le_upperEnvelope
    K F htransport p q
  have hu := momentWeakJointCoverUpperEnvelope_le_majorant
    K F htransport p q
  have hminor := neg_abs_le
    (momentWeakJointCoverFiniteMinorant K F q)
  have hmajor := le_abs_self
    (momentWeakJointCoverFiniteMajorant K F q)
  have hm := abs_nonneg
    (momentWeakJointCoverFiniteMinorant K F q)
  have hM := abs_nonneg
    (momentWeakJointCoverFiniteMajorant K F q)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem measurable_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    Measurable (momentWeakJointCoverUpperEnvelope
      K F htransport p) :=
  (upperSemicontinuous_momentWeakJointCoverUpperEnvelope
    K F htransport p).measurable

private theorem locallyIntegrable_momentWeakJointCoverUpperEnvelope
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) :
    LocallyIntegrable
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      (volume : Measure (SourceJointComplexCover n)) := by
  apply locallyIntegrable_iff.mpr
  intro A hA
  have hmajor : IntegrableOn
      (momentWeakHolomorphicJointAbsoluteMajorant K F) A
      (volume : Measure (SourceJointComplexCover n)) :=
    (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)
      |>.continuousOn.integrableOn_compact hA
  apply hmajor.mono'
    (measurable_momentWeakJointCoverUpperEnvelope
      K F htransport p).aestronglyMeasurable
  filter_upwards [] with q
  exact norm_momentWeakJointCoverUpperEnvelope_le_majorant
    K F htransport p q

private def momentWeakHolomorphicJointTrueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) : SourceJointComplexCover n → ℝ :=
  sourceJointTrueRadialSmoothed
    (momentWeakJointCoverUpperEnvelope K F htransport p) k

private theorem contDiff_momentWeakHolomorphicJointTrueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) :
    ContDiff ℝ ∞
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k) := by
  exact contDiff_sourceJointTrueRadialSmoothed
    (locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p) k

private theorem integrable_momentWeakHolomorphicJointComplexLineIntegrand
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Integrable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            ((q - z.1) + circleMap 0 R z.2 • v))
      ((volume : Measure (SourceJointComplexCover n)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  obtain ⟨L, C, hbound⟩ :=
    exists_sourceJointCoverCircle_uniform_bounds
      (fun _ : SourceJointComplexCover n => 0)
      (momentWeakHolomorphicJointAbsoluteMajorant K F)
      continuous_const
      (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)
      q v R
  have hdom :
      Integrable
        (fun z : SourceJointComplexCover n × ℝ =>
          sourceJointTrueRadialMollifier n k z.1 * C)
        ((volume : Measure (SourceJointComplexCover n)).prod ν) := by
    exact (integrable_sourceJointTrueRadialMollifier n k).mul_prod
      (integrable_const C)
  have hmap : Continuous
      (fun z : SourceJointComplexCover n × ℝ =>
        (q - z.1) + circleMap 0 R z.2 • v) := by
    fun_prop
  have hmeas : Measurable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            ((q - z.1) + circleMap 0 R z.2 • v)) :=
    ((contDiff_sourceJointTrueRadialMollifier n k).continuous.measurable.comp
      measurable_fst).mul
        ((measurable_momentWeakJointCoverUpperEnvelope
          K F htransport p).comp hmap.measurable)
  change Integrable _
    ((volume : Measure (SourceJointComplexCover n)).prod ν)
  apply hdom.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : sourceJointTrueRadialMollifier n k z.1 = 0
    · simp only [hz, zero_mul, norm_zero, Std.le_refl]
    · have hsupp :=
        support_sourceJointTrueRadialMollifier_subset_closedBall k hz
      have hnorm : ‖z.1‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one, one_div, mem_closedBall, dist_zero_right] using
          hsupp
      have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_lt_succ k
      have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hk).mpr
        norm_num
      have hdist : dist (q - z.1) q ≤ 1 := by
        simpa only [sub_eq_add_neg, dist_eq_norm, add_comm, add_left_comm, add_neg_cancel_left,
          norm_neg] using
          hnorm.trans hradius
      have hmaj :
          momentWeakHolomorphicJointAbsoluteMajorant K F
            ((q - z.1) + circleMap 0 R z.2 • v) ≤ C := by
        simpa only [sourceJointCoverCirclePoint] using
          ((hbound (q - z.1) hdist).2 z.2).2
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (sourceJointTrueRadialMollifier_nonneg n k z.1)]
      exact mul_le_mul_of_nonneg_left
        ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
          K F htransport p _).trans hmaj)
        (sourceJointTrueRadialMollifier_nonneg n k z.1)

private theorem integrable_momentWeakHolomorphicJointComplexLineAverage
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope K F htransport p
                ((q - y) + w • v)) 0 R)
      (volume : Measure (SourceJointComplexCover n)) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hinner :
      Integrable
        (fun y : SourceJointComplexCover n =>
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v) ∂ν)
        (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_momentWeakHolomorphicJointComplexLineIntegrand
      K F htransport p k q v R).integral_prod_left
  refine (hinner.const_mul ((2 * Real.pi)⁻¹)).congr ?_
  filter_upwards [] with y
  rw [Real.circleAverage_def]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in 0..2 * Real.pi,
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v)))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ : ℝ,
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν))
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem momentWeakHolomorphicJointComplexLineAverage_integral_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              ((q - y) + w • v)) 0 R) =
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hswap :
      (∫ y : SourceJointComplexCover n,
        ∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) ∂ν) =
        ∫ θ : ℝ,
          (∫ y : SourceJointComplexCover n,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v)) ∂ν := by
    exact MeasureTheory.integral_integral_swap
      (integrable_momentWeakHolomorphicJointComplexLineIntegrand
        K F htransport p k q v R)
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope
              K F htransport p ((q - y) + w • v)) 0 R) =
      ∫ y : SourceJointComplexCover n,
        (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope
                K F htransport p
                  ((q - y) + circleMap 0 R θ • v) ∂ν := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        rw [Real.circleAverage_def]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in 0..2 * Real.pi,
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v))) =
            (2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                sourceJointTrueRadialMollifier n k y *
                  momentWeakJointCoverUpperEnvelope
                    K F htransport p
                      ((q - y) + circleMap 0 R θ • v) ∂ν)
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v) ∂ν)) = _
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (2 * Real.pi)⁻¹ *
          ∫ y : SourceJointComplexCover n,
            ∫ θ : ℝ,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v) ∂ν := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope
                  K F htransport p
                    ((q - y) + circleMap 0 R θ • v)) ∂ν := by
      rw [hswap]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k
                (q + circleMap 0 R θ • v) ∂ν := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      unfold momentWeakHolomorphicJointTrueRadialMollification
        sourceJointTrueRadialSmoothed
      rw [MeasureTheory.convolution_def]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with y
      change
        sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q - y) + circleMap 0 R θ • v) =
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope
              K F htransport p
                ((q + circleMap 0 R θ • v) - y)
      congr 2
      abel
    _ = Real.circleAverage
          (fun w : ℂ =>
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k (q + w • v)) 0 R := by
      rw [Real.circleAverage_def,
        intervalIntegral.integral_of_le Real.two_pi_pos.le]
      rfl

private theorem momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q ≤
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
  rw [← momentWeakHolomorphicJointComplexLineAverage_integral_eq
    K F htransport p k q v R]
  unfold momentWeakHolomorphicJointTrueRadialMollification
    sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  change
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope
          K F htransport p (q - y)) ≤
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope
                K F htransport p ((q - y) + w • v)) 0 R
  apply MeasureTheory.integral_mono
    (integrable_sourceJointTrueRadialMollifier_mul_translate
      (locallyIntegrable_momentWeakJointCoverUpperEnvelope
        K F htransport p) k q)
    (integrable_momentWeakHolomorphicJointComplexLineAverage
      K F htransport p k q v R)
  intro y
  exact mul_le_mul_of_nonneg_left
    (momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
      K F htransport p (q - y) v R)
    (sourceJointTrueRadialMollifier_nonneg n k y)

end BergmanJetJointHolomorphicPlurisubharmonicSmoothing

namespace BergmanJetJointHolomorphicStrictSchur

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters WeightedTorusHilbert MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetUpperEnvelope BergmanJetSpatialPeriodicity BergmanJetStrictRadialRegularizer
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open ActualJetUpperEnvelope JetEnvelopeRightDerivative JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeTrueRadialMollifier JetEnvelopeTrueRadialComplexHessian
open JetEnvelopeTrueRadialLocalHessian JetEnvelopeTrueRadialPerturbedComplexHessianPositiveDefinite
open EnvelopeGeneralTorusDescent TorusHessianPositiveDefinite SchurConvexity
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder MatrixOrder

private theorem upperRegularization_sourceJointCover_periodic
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    {d : SourceJointComplexCover n}
    (hf : Function.Periodic f d) :
    Function.Periodic (upperRegularization f) d := by
  intro q
  let h : SourceJointComplexCover n ≃ₜ SourceJointComplexCover n :=
    Homeomorph.addRight d
  have hfun : (fun z : SourceJointComplexCover n => f (h z)) = f := by
    funext z
    exact hf z
  change upperRegularization f (h q) = upperRegularization f q
  rw [← upperRegularization_comp_homeomorph f h q, hfun]

private theorem momentWeakJointCoverFiniteGeodesic_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverFiniteGeodesic K F htransport p k)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  simpa only [momentWeakJointCoverFiniteGeodesic, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    Prod.fst_add, sourceJointCoverTime, Prod.snd_add, add_zero] using
      momentJetGeodesic_spatial_periodic
        K (Nat.zero_lt_succ k) F htransport p
          (Nat.floor (BodyScale.canonicalScale K *
            ((k + 1 : ℕ) : ℝ)))
          (sourceJointCoverTime q) m q.1

private theorem momentWeakJointCoverFiniteGeodesic_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverFiniteGeodesic K F htransport p k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  simp only [momentWeakJointCoverFiniteGeodesic, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one,
    Prod.fst_add, add_zero, sourceJointCoverTime, Prod.snd_add, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self]

private theorem momentWeakJointCoverTailSup_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverTailSup K F htransport p r)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakJointCoverTailSup
  have hfun :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j)
            (q + (imaginaryShift m, (0 : ℂ)))) =
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + r + j) q) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_spatial_periodic
      K F htransport p
        (momentJointTailStart K F htransport p + r + j) m q
  rw [hfun]

private theorem momentWeakJointCoverTailSup_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (s : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverTailSup K F htransport p s)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakJointCoverTailSup
  have hfun :
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + s + j)
            (q + ((0 : LogSpace n), (r : ℂ) * Complex.I))) =
      (fun j : ℕ => momentWeakJointCoverFiniteGeodesic
        K F htransport p
          (momentJointTailStart K F htransport p + s + j) q) := by
    funext j
    exact momentWeakJointCoverFiniteGeodesic_imaginary_periodic
      K F htransport p
        (momentJointTailStart K F htransport p + s + j) r q
  rw [hfun]

private theorem momentWeakJointCoverTailUpperEnvelope_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p r)
      (imaginaryShift m, (0 : ℂ)) := by
  exact upperRegularization_sourceJointCover_periodic
    (momentWeakJointCoverTailSup_spatial_periodic
      K F htransport p r m)

private theorem momentWeakJointCoverTailUpperEnvelope_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (s : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverTailUpperEnvelope
        K F htransport p s)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  exact upperRegularization_sourceJointCover_periodic
    (momentWeakJointCoverTailSup_imaginary_periodic
      K F htransport p s r)

private theorem momentWeakJointCoverUpperEnvelope_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakJointCoverUpperEnvelope
  congr 1
  funext r
  exact momentWeakJointCoverTailUpperEnvelope_spatial_periodic
    K F htransport p r m q

private theorem momentWeakJointCoverUpperEnvelope_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (r : ℝ) :
    Function.Periodic
      (momentWeakJointCoverUpperEnvelope K F htransport p)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakJointCoverUpperEnvelope
  congr 1
  funext s
  exact momentWeakJointCoverTailUpperEnvelope_imaginary_periodic
    K F htransport p s r q

private theorem momentWeakHolomorphicJointTrueRadialMollification_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (imaginaryShift m, (0 : ℂ)) := by
  exact sourceJointTrueRadialSmoothed_periodic
    (momentWeakJointCoverUpperEnvelope_spatial_periodic
      K F htransport p m) k

private theorem momentWeakHolomorphicJointTrueRadialMollification_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  exact sourceJointTrueRadialSmoothed_periodic
    (momentWeakJointCoverUpperEnvelope_imaginary_periodic
      K F htransport p r) k

private theorem sourceComplexHessian_radialMollification_posSemidef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k) τ z).PosSemidef := by
  apply sourceJointSpatialComplexHessian_posSemidef_of_local_circle_submean
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)) 2)
  intro q v
  refine ⟨1, by norm_num, ?_⟩
  intro r _
  exact
    momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
      K F htransport p k q v r

private def momentWeakHolomorphicStrictJointCoverWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (q : SourceJointComplexCover n) : ℝ :=
  (1 - ε) * momentWeakHolomorphicJointTrueRadialMollification
    K F htransport p k q +
      ε * matrixSourceCoverPotential
        (momentBodyStrictRadialPotential K) q.1

private theorem contDiff_momentWeakHolomorphicStrictJointCoverWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) :
    ContDiff ℝ ∞
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) := by
  have hfst : ContDiff ℝ ∞
      (fun q : SourceJointComplexCover n => q.1) := by
    fun_prop
  unfold momentWeakHolomorphicStrictJointCoverWeight
  exact (contDiff_const.mul
    (contDiff_momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k)).add
    (contDiff_const.mul
      ((contDiff_matrixSourceCoverPotential
        (contDiff_momentBodyStrictRadialPotential K)).comp hfst))

private theorem momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (m : Fin n → ℤ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      (imaginaryShift m, (0 : ℂ)) := by
  intro q
  unfold momentWeakHolomorphicStrictJointCoverWeight
  rw [momentWeakHolomorphicJointTrueRadialMollification_spatial_periodic
    K F htransport p k m q]
  have hp := matrixSourceCoverPotential_periodic
    (momentBodyStrictRadialPotential K) m q.1
  simpa only [Prod.fst_add, add_right_inj, mul_eq_mul_left_iff] using congrArg (fun x : ℝ =>
    (1 - ε) * momentWeakHolomorphicJointTrueRadialMollification
      K F htransport p k q + ε * x) hp

private theorem momentWeakHolomorphicStrictJointCoverWeight_imaginary_periodic
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (r : ℝ) :
    Function.Periodic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)
      ((0 : LogSpace n), (r : ℂ) * Complex.I) := by
  intro q
  unfold momentWeakHolomorphicStrictJointCoverWeight
  rw [momentWeakHolomorphicJointTrueRadialMollification_imaginary_periodic
    K F htransport p k r q]
  simp only [Prod.fst_add, add_zero]

private theorem sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z =
      (1 - ε) • sourceJointSpatialComplexHessian
        (momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k) τ z +
      ε • sourceCoverComplexHessian
        (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K)) z := by
  change
    sourceCoverComplexHessian
      (fun ξ : LogSpace n =>
        (1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (ξ, τ) +
        ε * matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K) ξ) z =
      (1 - ε) • sourceCoverComplexHessian
        (fun ξ : LogSpace n =>
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (ξ, τ)) z +
      ε • sourceCoverComplexHessian
        (matrixSourceCoverPotential
          (momentBodyStrictRadialPotential K)) z
  exact sourceCoverComplexHessian_realAffine
    (contDiff_sourceJointSpatialSlice
      ((contDiff_infty.mp
        (contDiff_momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k)) 2) τ)
    ((contDiff_infty.mp
      (contDiff_matrixSourceCoverPotential
        (contDiff_momentBodyStrictRadialPotential K))) 2)
    (1 - ε) ε z

private theorem sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z).PosDef := by
  rw [sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_eq
    K F htransport p ε k τ z]
  exact Matrix.PosDef.posSemidef_add
    ((sourceComplexHessian_radialMollification_posSemidef
      K F htransport p k τ z).smul (sub_nonneg.mpr hε₁))
    ((sourceCoverComplexHessian_momentBodyStrictRadialPotential_posDef
      K z).smul hε₀)

private def momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (t : ℝ) (q : LogTorus n) : ℝ :=
  jointSourceTorusWeight
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k) t q

private theorem angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    angularCoverPotential
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) =
      sourceJointSpatialSlice
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (t / 2 : ℂ) := by
  exact angularCoverPotential_jointSourceTorusWeight_eq
    (momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k)
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) t

private theorem contDiff_angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    ContDiff ℝ ∞
      (angularCoverPotential
        (momentWeakHolomorphicStrictJointTorusWeight
          K F htransport p ε k t)) := by
  rw [angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t]
  exact
    (contDiff_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k).comp
      (contDiff_id.prodMk contDiff_const)

private theorem angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ)
    (q : LogTorus n) :
    angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q =
      sourceJointSpatialComplexHessian
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k)
        (t / 2 : ℂ) (sourceTorusCoverPoint q) := by
  ext i j
  change
    torusScalarRepresentative
      (fun z => complexHessian
        (angularCoverPotential
          (momentWeakHolomorphicStrictJointTorusWeight
            K F htransport p ε k t)) z i j) q =
      complexHessian
        (sourceJointSpatialSlice
          (momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k) (t / 2 : ℂ))
        (sourceTorusCoverPoint q) i j
  rw [angularCoverPotential_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t]
  rfl

private theorem angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_posDef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (t : ℝ) (q : LogTorus n) :
    (angularTorusComplexHessianMatrix
      (momentWeakHolomorphicStrictJointTorusWeight
        K F htransport p ε k t) q).PosDef := by
  rw [angularTorusComplexHessianMatrix_momentWeakHolomorphicStrictJointTorusWeight_eq
    K F htransport p ε k t q]
  exact
    sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
      K F htransport p ε hε₀ hε₁ k
        (t / 2 : ℂ) (sourceTorusCoverPoint q)

private theorem continuous_momentWeakHolomorphicStrictJointTorusWeight
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ) (t : ℝ) :
    Continuous (momentWeakHolomorphicStrictJointTorusWeight
      K F htransport p ε k t) := by
  exact continuous_jointSourceTorusWeight
    (contDiff_momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k).continuous
    (momentWeakHolomorphicStrictJointCoverWeight_spatial_periodic
      K F htransport p ε k) t

end BergmanJetJointHolomorphicStrictSchur

namespace BergmanJetJointHolomorphicFullLeviSchur

open Set Function Filter MeasureTheory Metric Matrix
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetStrictRadialRegularizer BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open BergmanJetJointHolomorphicStrictSchur JetEnvelopeGlobalPlurisubharmonic
open JetEnvelopeGlobalPlurisubharmonicClosure JetEnvelopeTrueRadialHessian
open JetEnvelopeTrueRadialComplexHessian JetEnvelopeTrueRadialLocalHessian
open EnvelopeGeneralTorusDescent RadialSchurBlock RadialFullLeviSchur MatrixTorusBochnerBridge
open MatrixTorusBochnerCore
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder MatrixOrder

private theorem convexOn_momentStrictRadialCoordinate :
    ConvexOn ℝ Set.univ momentStrictRadialCoordinate := by
  have hd : deriv momentStrictRadialCoordinate =
      momentStrictRadialCoordinateDerivative := by
    funext y
    exact (hasDerivAt_momentStrictRadialCoordinate y).deriv
  apply convexOn_univ_of_deriv2_nonneg
  · exact fun y =>
      (hasDerivAt_momentStrictRadialCoordinate y).differentiableAt
  · rw [hd]
    exact fun y =>
      (hasDerivAt_momentStrictRadialCoordinateDerivative y)
        |>.differentiableAt
  · intro y
    change 0 ≤ deriv (deriv momentStrictRadialCoordinate) y
    rw [hd, (hasDerivAt_momentStrictRadialCoordinateDerivative y).deriv]
    exact (momentStrictRadialCoordinateSecond_pos y).le

private theorem convexOn_momentBodyStrictRadialPotential
    {n : ℕ} (K : CenteredBody n) :
    ConvexOn ℝ Set.univ (momentBodyStrictRadialPotential K) := by
  classical
  have hcoord (i : Fin n) :
      ConvexOn ℝ (Set.univ : Set (Space n))
        (fun x : Space n =>
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * x i)) := by
    let L : Space n →ₗ[ℝ] ℝ :=
      momentBodyStrictScale K • (LinearMap.proj i)
    have h := convexOn_momentStrictRadialCoordinate.comp_linearMap L
    simpa [L, Function.comp_def] using h
  have hsum (s : Finset (Fin n)) :
      ConvexOn ℝ (Set.univ : Set (Space n))
        (fun x : Space n =>
          ∑ i ∈ s,
            momentStrictRadialCoordinate
              (momentBodyStrictScale K * x i)) := by
    induction s using Finset.induction_on with
    | empty =>
        simpa only [Finset.sum_empty] using
          (convexOn_const (0 : ℝ)
            (convex_univ : Convex ℝ
              (Set.univ : Set (Space n))))
    | @insert i s hi ih =>
        have hadd := (hcoord i).add ih
        have hfun :
            (fun x : Space n =>
              momentStrictRadialCoordinate
                (momentBodyStrictScale K * x i)) +
              (fun x : Space n =>
                ∑ j ∈ s,
                  momentStrictRadialCoordinate
                    (momentBodyStrictScale K * x j)) =
              (fun x : Space n =>
                ∑ j ∈ insert i s,
                  momentStrictRadialCoordinate
                    (momentBodyStrictScale K * x j)) := by
          funext x
          simp only [Pi.add_apply, Finset.sum_insert hi]
        rw [hfun] at hadd
        exact hadd
  have hfun :
      (fun x : Space n =>
        ∑ i ∈ (Finset.univ : Finset (Fin n)),
          momentStrictRadialCoordinate
            (momentBodyStrictScale K * x i)) =
        momentBodyStrictRadialPotential K := by
    funext x
    simp only [momentBodyStrictRadialPotential]
  rw [← hfun]
  exact hsum (Finset.univ : Finset (Fin n))

private def momentBodyStrictJointCoverReference
    {n : ℕ} (K : CenteredBody n)
    (q : SourceJointComplexCover n) : ℝ :=
  matrixSourceCoverPotential (momentBodyStrictRadialPotential K) q.1

private theorem continuous_momentBodyStrictJointCoverReference
    {n : ℕ} (K : CenteredBody n) :
    Continuous (momentBodyStrictJointCoverReference K) := by
  unfold momentBodyStrictJointCoverReference
  exact (continuous_matrixSourceCoverPotential
    (contDiff_momentBodyStrictRadialPotential K).continuous).comp
      continuous_fst

private theorem momentBodyStrictJointCoverReference_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (q v : SourceJointComplexCover n) (R : ℝ) :
    momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ => momentBodyStrictJointCoverReference
          K (q + w • v)) 0 R := by
  let f : ℂ → Space n := fun w =>
    sourceCoverRadialLinear n ((q + w • v).1)
  have hf : Continuous f := by
    unfold f
    fun_prop
  have hangle : Continuous
      (fun θ : ℝ => f (circleMap 0 R θ)) :=
    hf.comp (continuous_circleMap 0 R)
  have hfi : IntegrableOn
      (fun θ : ℝ => f (circleMap 0 R θ))
      (Set.Ioc 0 (2 * Real.pi)) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp
    exact hangle.intervalIntegrable 0 (2 * Real.pi)
  have hgi : IntegrableOn
      (momentBodyStrictRadialPotential K ∘
        fun θ : ℝ => f (circleMap 0 R θ))
      (Set.Ioc 0 (2 * Real.pi)) volume := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le
      Real.two_pi_pos.le).mp
    exact ((contDiff_momentBodyStrictRadialPotential K).continuous.comp
      hangle).intervalIntegrable 0 (2 * Real.pi)
  have hzero :
      (volume : Measure ℝ) (Set.Ioc 0 (2 * Real.pi)) ≠ 0 := by
    rw [Real.volume_Ioc, sub_zero]
    exact (ENNReal.ofReal_pos.mpr Real.two_pi_pos).ne'
  have hfinite :
      (volume : Measure ℝ) (Set.Ioc 0 (2 * Real.pi)) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hmean :=
    (convexOn_momentBodyStrictRadialPotential K).map_set_average_le
      (contDiff_momentBodyStrictRadialPotential K).continuous.continuousOn
      isClosed_univ hzero hfinite
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      hfi hgi
  have hline : CircleIntegrable
      (fun w : ℂ => (q + w • v).1) 0 R := by
    rw [circleIntegrable_def]
    exact (by fun_prop : Continuous
      (fun θ : ℝ =>
        (q + circleMap 0 R θ • v).1)).intervalIntegrable
          0 (2 * Real.pi)
  have hcenter :
      (⨍ θ in Set.Ioc 0 (2 * Real.pi),
        f (circleMap 0 R θ)) =
        sourceCoverRadialLinear n q.1 := by
    rw [sourceJointCircleAverage_eq_setAverage]
    calc
      Real.circleAverage f 0 R =
        sourceCoverRadialLinear n
          (Real.circleAverage
            (fun w : ℂ => (q + w • v).1) 0 R) := by
            simpa only [Prod.fst_add, Prod.smul_fst, map_add, comp_def, f] using
              (sourceCoverRadialLinear n).circleAverage_comp_comm hline
      _ = sourceCoverRadialLinear n q.1 := by
            rw [sourceJointSpatialLine_circleAverage]
  have htarget :
      (⨍ θ in Set.Ioc 0 (2 * Real.pi),
        momentBodyStrictRadialPotential K
          (f (circleMap 0 R θ))) =
        Real.circleAverage
          (fun w : ℂ => momentBodyStrictRadialPotential K (f w))
          0 R :=
    sourceJointCircleAverage_eq_setAverage
      (fun w : ℂ => momentBodyStrictRadialPotential K (f w)) R
  rw [hcenter, htarget] at hmean
  simpa [f, momentBodyStrictJointCoverReference,
    matrixSourceCoverPotential, sourceCoverRadialLinear] using hmean

private theorem momentWeakHolomorphicStrictJointCoverWeight_complex_line_submean_all_radius
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (q v : SourceJointComplexCover n) (R : ℝ) :
    momentWeakHolomorphicStrictJointCoverWeight
      K F htransport p ε k q ≤
      Real.circleAverage
        (fun w : ℂ =>
          momentWeakHolomorphicStrictJointCoverWeight
            K F htransport p ε k (q + w • v)) 0 R := by
  have hm : CircleIntegrable
      (fun w : ℂ =>
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k (q + w • v)) 0 R :=
    circleIntegrable_sourceJointCover_of_continuous
      (momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k)
      (contDiff_momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k).continuous q v R
  have hp : CircleIntegrable
      (fun w : ℂ =>
        momentBodyStrictJointCoverReference K (q + w • v)) 0 R :=
    circleIntegrable_sourceJointCover_of_continuous
      (momentBodyStrictJointCoverReference K)
      (continuous_momentBodyStrictJointCoverReference K)
      q v R
  have hm' : CircleIntegrable
      (fun w : ℂ =>
        (1 - ε) *
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R := by
    simpa only [smul_eq_mul] using
      (hm.const_fun_smul (a := 1 - ε))
  have hp' : CircleIntegrable
      (fun w : ℂ =>
        ε * momentBodyStrictJointCoverReference
          K (q + w • v)) 0 R := by
    simpa only [smul_eq_mul] using
      (hp.const_fun_smul (a := ε))
  unfold momentWeakHolomorphicStrictJointCoverWeight
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ =>
          (1 - ε) *
            momentWeakHolomorphicJointTrueRadialMollification
              K F htransport p k (q + w • v) +
          ε * momentBodyStrictJointCoverReference
            K (q + w • v)) 0 R
  rw [Real.circleAverage_fun_add hm' hp']
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      Real.circleAverage
        (fun w : ℂ => (1 - ε) •
          momentWeakHolomorphicJointTrueRadialMollification
            K F htransport p k (q + w • v)) 0 R +
      Real.circleAverage
        (fun w : ℂ => ε •
          momentBodyStrictJointCoverReference
            K (q + w • v)) 0 R
  rw [Real.circleAverage_fun_smul,
    Real.circleAverage_fun_smul]
  change
    (1 - ε) *
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q +
      ε * momentBodyStrictJointCoverReference K q ≤
      (1 - ε) *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakHolomorphicJointTrueRadialMollification
                K F htransport p k (q + w • v)) 0 R +
        ε *
          Real.circleAverage
            (fun w : ℂ =>
              momentBodyStrictJointCoverReference
                K (q + w • v)) 0 R
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (momentWeakHolomorphicJointTrueRadialMollification_complex_line_submean_all_radius
        K F htransport p k q v R)
      (sub_nonneg.mpr hε₁))
    (mul_le_mul_of_nonneg_left
      (momentBodyStrictJointCoverReference_complex_line_submean_all_radius
        K q v R) hε₀)

private theorem sourceJointRealLeviQuadratic_momentWeakHolomorphicStrictJointCoverWeight_nonneg
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (q v : SourceJointComplexCover n) :
    0 ≤ sourceJointRealLeviQuadratic
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) q v := by
  apply sourceJointRealLeviQuadratic_nonnegative_of_local_circle_submean
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2)
  refine ⟨1, by norm_num, ?_⟩
  intro r _
  exact
    momentWeakHolomorphicStrictJointCoverWeight_complex_line_submean_all_radius
      K F htransport p ε hε₀ hε₁ k q v r

private def momentWeakHolomorphicStrictJointCoverSchurBlock
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℂ :=
  sourceComplexRowSchurBlock
    (sourceJointSpatialComplexHessian
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z)
    (sourceJointCoverAntiholomorphicVelocityGradient
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) τ z)
    (jointSourceCoverAcceleration
      (momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k) (z, τ))

private theorem momentWeakHolomorphicStrictJointCoverSchurBlock_isHermitian
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n) :
    (momentWeakHolomorphicStrictJointCoverSchurBlock
      K F htransport p ε k τ z).IsHermitian := by
  unfold momentWeakHolomorphicStrictJointCoverSchurBlock
  apply sourceComplexRowSchurBlock_isHermitian
  exact sourceJointSpatialComplexHessian_isHermitian
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2) τ z

private theorem momentWeakHolomorphicStrictJointCoverSchurBlock_quadratic_eq_realLevi
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ) (k : ℕ)
    (τ : ℂ) (z : LogSpace n)
    (x : Fin n ⊕ Fin 1 → ℂ) :
    star x ⬝ᵥ
      (momentWeakHolomorphicStrictJointCoverSchurBlock
        K F htransport p ε k τ z *ᵥ x) =
      (sourceJointRealLeviQuadratic
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (z, τ)
        (star (x ∘ Sum.inl), star (x (Sum.inr 0))) : ℂ) := by
  unfold momentWeakHolomorphicStrictJointCoverSchurBlock
  exact sourceJointCoverRowSchurBlock_quadratic_eq_realLevi
    ((contDiff_infty.mp
      (contDiff_momentWeakHolomorphicStrictJointCoverWeight
        K F htransport p ε k)) 2)
    (fun r => momentWeakHolomorphicStrictJointCoverWeight_imaginary_periodic
      K F htransport p ε k r)
    τ z x

private theorem momentWeakHolomorphicStrictJointCoverSchurBlock_posSemidef
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (τ : ℂ) (z : LogSpace n) :
    (momentWeakHolomorphicStrictJointCoverSchurBlock
      K F htransport p ε k τ z).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (momentWeakHolomorphicStrictJointCoverSchurBlock_isHermitian
      K F htransport p ε k τ z)
  intro x
  rw [momentWeakHolomorphicStrictJointCoverSchurBlock_quadratic_eq_realLevi
    K F htransport p ε k τ z x]
  apply (Complex.nonneg_iff).2
  constructor
  · exact
      sourceJointRealLeviQuadratic_momentWeakHolomorphicStrictJointCoverWeight_nonneg
        K F htransport p ε hε₀ hε₁ k (z, τ)
          (star (x ∘ Sum.inl), star (x (Sum.inr 0)))
  · simp only [Fin.isValue, RCLike.star_def, Complex.ofReal_im]

private theorem momentWeakHolomorphicStrictJointCover_rowSchurEnergy_le_acceleration
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (ε : ℝ)
    (hε₀ : 0 < ε) (hε₁ : ε ≤ 1)
    (k : ℕ) (τ : ℂ) (z : LogSpace n) :
    sourceComplexRowSchurEnergyDensity
      (sourceJointSpatialComplexHessian
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) τ z)
      (sourceJointCoverAntiholomorphicVelocityGradient
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) τ z) ≤
      jointSourceCoverAcceleration
        (momentWeakHolomorphicStrictJointCoverWeight
          K F htransport p ε k) (z, τ) := by
  exact sourceComplexRowSchurEnergy_le
    (sourceJointSpatialComplexHessian_momentWeakHolomorphicStrictJointCoverWeight_posDef
      K F htransport p ε hε₀ hε₁ k τ z)
    _ _
    (momentWeakHolomorphicStrictJointCoverSchurBlock_posSemidef
      K F htransport p ε hε₀.le hε₁ k τ z)

end BergmanJetJointHolomorphicFullLeviSchur

namespace BergmanJetJointHolomorphicApproximation

open Set Function Filter MeasureTheory Metric
open TorusCharacters MomentOptimizer MomentTargetGeodesic MomentFirstVariation
open BergmanJetJointHolomorphicClosure BergmanJetJointHolomorphicPlurisubharmonicSmoothing
open JetEnvelopeGlobalPlurisubharmonic JetEnvelopeTrueRadialMollifier
open scoped BigOperators ENNReal Topology ContDiff Convolution
  ComplexConjugate ComplexOrder

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (LogSpace n)) (volume : Measure ℂ)

private theorem integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    Integrable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - circleMap 0 1 z.2 • z.1))
      ((volume : Measure (SourceJointComplexCover n)).prod
        (volume.restrict (Set.Ioc 0 (2 * Real.pi)))) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  obtain ⟨C, hC⟩ :=
    ((isCompact_closedBall q (1 : ℝ)).image
      (continuous_momentWeakHolomorphicJointAbsoluteMajorant K F)).bddAbove
  have hCnonneg : 0 ≤ C := by
    have hq : q ∈ Metric.closedBall q (1 : ℝ) := by simp only [mem_closedBall, dist_self,
      zero_le_one]
    have hmaj : momentWeakHolomorphicJointAbsoluteMajorant K F q ≤ C :=
      hC ⟨q, hq, rfl⟩
    exact (norm_nonneg
      (momentWeakJointCoverUpperEnvelope K F htransport p q)).trans
      ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
        K F htransport p q).trans hmaj)
  have hdom :
      Integrable
        (fun z : SourceJointComplexCover n × ℝ =>
          sourceJointTrueRadialMollifier n k z.1 * C)
        ((volume : Measure (SourceJointComplexCover n)).prod ν) := by
    exact (integrable_sourceJointTrueRadialMollifier n k).mul_prod
      (integrable_const C)
  have hmap : Continuous
      (fun z : SourceJointComplexCover n × ℝ =>
        q - circleMap 0 1 z.2 • z.1) := by
    fun_prop
  have hmeas : Measurable
      (fun z : SourceJointComplexCover n × ℝ =>
        sourceJointTrueRadialMollifier n k z.1 *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - circleMap 0 1 z.2 • z.1)) :=
    ((contDiff_sourceJointTrueRadialMollifier n k).continuous.measurable.comp
      measurable_fst).mul
        ((measurable_momentWeakJointCoverUpperEnvelope
          K F htransport p).comp hmap.measurable)
  change Integrable _ ((volume : Measure
    (SourceJointComplexCover n)).prod ν)
  apply hdom.mono' hmeas.aestronglyMeasurable
  exact Eventually.of_forall fun z => by
    by_cases hz : sourceJointTrueRadialMollifier n k z.1 = 0
    · simp only [hz, zero_mul, norm_zero, Std.le_refl]
    · have hsupp :=
        support_sourceJointTrueRadialMollifier_subset_closedBall k hz
      have hnorm : ‖z.1‖ ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
        simpa only [Nat.cast_add, Nat.cast_one, one_div, mem_closedBall, dist_zero_right] using
          hsupp
      have hk : 0 < ((k + 1 : ℕ) : ℝ) := by
        exact_mod_cast Nat.zero_lt_succ k
      have hradius : 1 / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hk).mpr
        norm_num
      have hpoint :
          q - circleMap 0 1 z.2 • z.1 ∈
            Metric.closedBall q (1 : ℝ) := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have hunit : ‖circleMap 0 1 z.2‖ = 1 := by
          simp only [norm_circleMap_zero, abs_one]
        simpa only [sub_eq_add_neg, add_comm, add_left_comm, add_neg_cancel_left, norm_neg,
          norm_smul,
          hunit, one_mul, ge_iff_le] using
          hnorm.trans hradius
      have hmaj :
          momentWeakHolomorphicJointAbsoluteMajorant K F
            (q - circleMap 0 1 z.2 • z.1) ≤ C :=
        hC ⟨_, hpoint, rfl⟩
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_nonneg (sourceJointTrueRadialMollifier_nonneg n k z.1)]
      exact mul_le_mul_of_nonneg_left
        ((norm_momentWeakJointCoverUpperEnvelope_le_majorant
          K F htransport p _).trans hmaj)
        (sourceJointTrueRadialMollifier_nonneg n k z.1)

private theorem momentWeakHolomorphicJointRadialEnvelopeAngleIntegral
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ)
    (q : SourceJointComplexCover n) (θ : ℝ) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p
          (q - circleMap 0 1 θ • y)) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) := by
  let w : ℂ := circleMap 0 1 θ
  have hw : ‖w‖ = 1 := by
    simp only [norm_circleMap_zero, abs_one, w]
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p (q - w • y)) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k (w • y) *
          momentWeakJointCoverUpperEnvelope K F htransport p
            (q - w • y) := by
              apply MeasureTheory.integral_congr_ae
              filter_upwards [] with y
              rw [sourceJointTrueRadialMollifier_phase k w hw y]
    _ = ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) :=
      integral_sourceJointComplexPhase w hw
        (fun y : SourceJointComplexCover n =>
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p (q - y))

private theorem momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - w • y)) 0 1) =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p (q - y) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hswap :
      (∫ y : SourceJointComplexCover n,
        ∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
        ∫ θ : ℝ,
          (∫ y : SourceJointComplexCover n,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y)) ∂ν := by
    exact MeasureTheory.integral_integral_swap
      (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
        K F htransport p k q)
  calc
    (∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        Real.circleAverage
          (fun w : ℂ =>
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - w • y)) 0 1) =
      ∫ y : SourceJointComplexCover n,
        (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y) ∂ν := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with y
        rw [Real.circleAverage_def]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ in 0..2 * Real.pi,
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y))) =
            (2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                sourceJointTrueRadialMollifier n k y *
                  momentWeakJointCoverUpperEnvelope K F htransport p
                    (q - circleMap 0 1 θ • y) ∂ν)
        rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
        change
          sourceJointTrueRadialMollifier n k y *
            ((2 * Real.pi)⁻¹ *
              (∫ θ : ℝ,
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y) ∂ν)) = _
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (2 * Real.pi)⁻¹ *
          ∫ y : SourceJointComplexCover n,
            ∫ θ : ℝ,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y) ∂ν := by
      rw [MeasureTheory.integral_const_mul]
    _ = (2 * Real.pi)⁻¹ *
          ∫ θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - circleMap 0 1 θ • y)) ∂ν := by
      rw [hswap]
    _ = (2 * Real.pi)⁻¹ *
          ∫ _θ : ℝ,
            (∫ y : SourceJointComplexCover n,
              sourceJointTrueRadialMollifier n k y *
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - y)) ∂ν := by
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards [] with θ
      exact momentWeakHolomorphicJointRadialEnvelopeAngleIntegral
        K F htransport p k q θ
    _ = ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - y) := by
      rw [MeasureTheory.integral_const]
      simp only [mul_inv_rev, measureReal_def, MeasurableSet.univ, Measure.restrict_apply,
        univ_inter,
        Real.volume_Ioc, sub_zero, Nat.ofNat_nonneg, ENNReal.ofReal_mul, ENNReal.ofReal_ofNat,
        ENNReal.toReal_mul, ENNReal.toReal_ofNat, Real.pi_pos.le, ENNReal.toReal_ofReal,
        smul_eq_mul, ν]
      field_simp [Real.pi_ne_zero]

private theorem integrable_momentWeakHolomorphicJointRadialEnvelopeCircleAverage
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    Integrable
      (fun y : SourceJointComplexCover n =>
        sourceJointTrueRadialMollifier n k y *
          Real.circleAverage
            (fun w : ℂ =>
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - w • y)) 0 1)
      (volume : Measure (SourceJointComplexCover n)) := by
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc 0 (2 * Real.pi))
  have hinner :
      Integrable
        (fun y : SourceJointComplexCover n =>
          ∫ θ : ℝ,
            sourceJointTrueRadialMollifier n k y *
              momentWeakJointCoverUpperEnvelope K F htransport p
                (q - circleMap 0 1 θ • y) ∂ν)
        (volume : Measure (SourceJointComplexCover n)) :=
    (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleIntegrand
      K F htransport p k q).integral_prod_left
  refine (hinner.const_mul ((2 * Real.pi)⁻¹)).congr ?_
  filter_upwards [] with y
  rw [Real.circleAverage_def]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ in 0..2 * Real.pi,
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y)))
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  change
    (2 * Real.pi)⁻¹ *
        (∫ θ : ℝ,
          sourceJointTrueRadialMollifier n k y *
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν) =
      sourceJointTrueRadialMollifier n k y *
        ((2 * Real.pi)⁻¹ *
          (∫ θ : ℝ,
            momentWeakJointCoverUpperEnvelope K F htransport p
              (q - circleMap 0 1 θ • y) ∂ν))
  rw [MeasureTheory.integral_const_mul]
  ring

private theorem momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (k : ℕ) (q : SourceJointComplexCover n) :
    momentWeakJointCoverUpperEnvelope K F htransport p q ≤
      momentWeakHolomorphicJointTrueRadialMollification
        K F htransport p k q := by
  change momentWeakJointCoverUpperEnvelope K F htransport p q ≤
    sourceJointTrueRadialSmoothed
      (momentWeakJointCoverUpperEnvelope K F htransport p) k q
  unfold sourceJointTrueRadialSmoothed
  rw [MeasureTheory.convolution_def]
  change momentWeakJointCoverUpperEnvelope K F htransport p q ≤
    ∫ y : SourceJointComplexCover n,
      sourceJointTrueRadialMollifier n k y *
        momentWeakJointCoverUpperEnvelope K F htransport p (q - y)
  rw [← momentWeakHolomorphicJointRadialEnvelopeCircleAverageIntegral
    K F htransport p k q]
  calc
    momentWeakJointCoverUpperEnvelope K F htransport p q =
      ∫ y : SourceJointComplexCover n,
        sourceJointTrueRadialMollifier n k y *
          momentWeakJointCoverUpperEnvelope K F htransport p q := by
        rw [MeasureTheory.integral_mul_const,
          integral_sourceJointTrueRadialMollifier, one_mul]
    _ ≤ ∫ y : SourceJointComplexCover n,
          sourceJointTrueRadialMollifier n k y *
            Real.circleAverage
              (fun w : ℂ =>
                momentWeakJointCoverUpperEnvelope K F htransport p
                  (q - w • y)) 0 1 := by
      apply MeasureTheory.integral_mono
        ((integrable_sourceJointTrueRadialMollifier n k).mul_const
          (momentWeakJointCoverUpperEnvelope K F htransport p q))
        (integrable_momentWeakHolomorphicJointRadialEnvelopeCircleAverage
          K F htransport p k q)
      intro y
      apply mul_le_mul_of_nonneg_left _
        (sourceJointTrueRadialMollifier_nonneg n k y)
      have hmean :=
        momentWeakJointCoverUpperEnvelope_complex_line_submean_all_radius
          K F htransport p q (-y) 1
      simpa only [sub_eq_add_neg, ge_iff_le, smul_neg] using hmean

private theorem tendsto_momentWeakHolomorphicJointTrueRadialMollification
    {n : ℕ} (K : CenteredBody n)
    (F : SourceFiniteEnergyPotential K)
    (htransport : finiteEnergySourceGradientPushforward F =
      normalizedTargetBodyMeasure K)
    (p : LogSpace n) (q : SourceJointComplexCover n) :
    Tendsto
      (fun k : ℕ =>
        momentWeakHolomorphicJointTrueRadialMollification
          K F htransport p k q)
      atTop
        (𝓝 (momentWeakJointCoverUpperEnvelope
          K F htransport p q)) := by
  apply tendsto_sourceJointTrueRadialSmoothed_of_upperSemicontinuousAt_and_le
    (locallyIntegrable_momentWeakJointCoverUpperEnvelope
      K F htransport p) q
    (upperSemicontinuous_momentWeakJointCoverUpperEnvelope
      K F htransport p q)
  intro k
  exact momentWeakJointCoverUpperEnvelope_le_trueRadialMollification
    K F htransport p k q

end BergmanJetJointHolomorphicApproximation

namespace RadialPartitionBounds

open Set Function Filter MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic
open scoped BigOperators ENNReal NNReal Topology ContDiff

private def sourceJointRealTimeCLM (n : ℕ) :
    SourceJointComplexCover n →L[ℝ] ℝ :=
  (2 : ℝ) •
    (Complex.reCLM.comp
      (ContinuousLinearMap.snd ℝ
        (TorusCharacters.LogSpace n) ℂ))

private theorem sourceJointRealTimeCLM_apply {n : ℕ}
    (q : SourceJointComplexCover n) :
    sourceJointRealTimeCLM n q = sourceJointCoverTime q := by
  simp only [sourceJointRealTimeCLM, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_snd', Complex.reCLM_apply, smul_eq_mul, sourceJointCoverTime]

private theorem abs_sourceJointCoverTime_sub_le {n : ℕ}
    (q y : SourceJointComplexCover n) :
    |sourceJointCoverTime (q - y)| ≤
      |sourceJointCoverTime q| +
        ‖sourceJointRealTimeCLM n‖ * ‖y‖ := by
  have hop := (sourceJointRealTimeCLM n).le_opNorm y
  rw [Real.norm_eq_abs] at hop
  calc
    |sourceJointCoverTime (q - y)| =
      |sourceJointCoverTime q -
        sourceJointRealTimeCLM n y| := by
          rw [← sourceJointRealTimeCLM_apply,
            map_sub, sourceJointRealTimeCLM_apply]
    _ ≤ |sourceJointCoverTime q| +
          |sourceJointRealTimeCLM n y| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        (abs_add_le (sourceJointCoverTime q)
          (-(sourceJointRealTimeCLM n y)))
    _ ≤ |sourceJointCoverTime q| +
          ‖sourceJointRealTimeCLM n‖ * ‖y‖ :=
      add_le_add (le_refl _) hop

end RadialPartitionBounds

namespace TorusFriedrichsCutoff

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters JetEnvelopeRightDerivative EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff

private theorem angularSourceRadialCutoff_smul_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a))
    (m : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) • F q)
      2 (angularWeightedTorusMeasure a) := by
  have hscalar : Continuous
      (fun q : LogTorus n => (sourceRadialCutoff m q : ℂ)) :=
    Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)
  apply hF.of_le_mul (c := (1 : ℝ))
    (hscalar.aestronglyMeasurable.fun_smul hF.aestronglyMeasurable)
  filter_upwards [] with q
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
  exact mul_le_mul_of_nonneg_right
    (sourceRadialCutoff_le_one m q) (norm_nonneg (F q))

private theorem angularSourceRadialCutoff_smul_squared_error_integrals_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hbound : Integrable
      (fun q : LogTorus n => ‖F q‖ ^ 2)
      (angularWeightedTorusMeasure a) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hF.aestronglyMeasurable).mp hF
  have hdom := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := angularWeightedTorusMeasure a)
    (F := fun m : ℕ =>
      fun q : LogTorus n =>
        ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2)
    (f := fun _ : LogTorus n => (0 : ℝ))
    (fun q : LogTorus n => ‖F q‖ ^ 2)
    (by
      intro m
      have hscalar : Continuous
          (fun q : LogTorus n => (sourceRadialCutoff m q : ℂ)) :=
        Complex.continuous_ofReal.comp
          (continuous_sourceRadialCutoff m)
      exact ((hscalar.aestronglyMeasurable.smul
        hF.aestronglyMeasurable).sub
          hF.aestronglyMeasurable).norm.pow 2)
    hbound
    (by
      intro m
      filter_upwards [] with q
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hzero := sourceRadialCutoff_nonneg m q
      have hone := sourceRadialCutoff_le_one m q
      have hscalar : |sourceRadialCutoff m q - 1| ≤ 1 := by
        rw [abs_of_nonpos (sub_nonpos.mpr hone)]
        linarith
      have hrewrite :
          (sourceRadialCutoff m q : ℂ) • F q - F q =
            ((sourceRadialCutoff m q - 1 : ℝ) : ℂ) • F q := by
        simp only [Complex.coe_smul, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      rw [hrewrite, norm_smul, Complex.norm_real, Real.norm_eq_abs]
      apply (sq_le_sq₀
        (mul_nonneg (abs_nonneg _) (norm_nonneg _))
        (norm_nonneg _)).mpr
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hscalar
        (norm_nonneg (F q)))
    (by
      filter_upwards [] with q
      apply Filter.Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [sourceRadialCutoff_eventually_one q]
        with m hm
      simp only [hm, Complex.ofReal_one, one_smul, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow])
  simpa only [Complex.coe_smul, integral_zero] using hdom

private theorem angularSourceRadialCutoff_smul_L2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E]
    {F : LogTorus n → E}
    (hF : MemLp F 2 (angularWeightedTorusMeasure a)) :
    Tendsto
      (fun m : ℕ =>
        (angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q))
      atTop (nhds (hF.toLp F)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hnormsq (m : ℕ) :
      ‖(angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q) -
        hF.toLp F‖ ^ 2 =
      ∫ q : LogTorus n,
        ‖(sourceRadialCutoff m q : ℂ) • F q - F q‖ ^ 2
        ∂(angularWeightedTorusMeasure a) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((angularSourceRadialCutoff_smul_memLp hF m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • F q))
        (hF.toLp F),
       (angularSourceRadialCutoff_smul_memLp hF m).coeFn_toLp,
       hF.coeFn_toLp]
      with q hsub hcut hfull
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hcut, hfull]
  have hsq :
      Tendsto
        (fun m : ℕ =>
          ‖(angularSourceRadialCutoff_smul_memLp hF m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) • F q) -
            hF.toLp F‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hnormsq] using
      angularSourceRadialCutoff_smul_squared_error_integrals_tendsto_zero hF
  simpa only [Complex.coe_smul, norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsq.sqrt

private theorem angularTorusWeightedHolomorphicDerivative_cutoffPhysicalField
    {n : ℕ} (a : LogTorus n → ℝ) (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (i : Fin n) (q : LogTorus n) :
    angularTorusWeightedHolomorphicDerivative a
      (fun z => cutoffPhysicalField m W z i) i q =
      (sourceRadialCutoff m q : ℂ) *
        angularTorusWeightedHolomorphicDerivative a
          (fun z => W z i) i q +
      torusScalarRepresentative (fun z => W z i) q *
        torusScalarRepresentative
          (fun z => holomorphicCoordinate
            (complexSourceCoverRadialCutoff m) z i) q := by
  have hproduct :
      (fun z : LogSpace n =>
        weightedHolomorphicDerivative (angularCoverPotential a)
          (fun w => complexSourceCoverRadialCutoff m w * W w i)
            i z) =
      (fun z : LogSpace n =>
        complexSourceCoverRadialCutoff m z *
          weightedHolomorphicDerivative
            (angularCoverPotential a) (fun w => W w i) i z +
        W z i *
          holomorphicCoordinate (complexSourceCoverRadialCutoff m) z i) := by
    funext z
    exact weightedHolomorphicDerivative_mul
      (angularCoverPotential a)
      ((contDiff_complexSourceCoverRadialCutoff m).differentiable
        (by norm_num))
      ((contDiff_pi.mp hW i).differentiable
        (by norm_num)) z i
  unfold angularTorusWeightedHolomorphicDerivative
  change
    torusScalarRepresentative
      (fun z => weightedHolomorphicDerivative
        (angularCoverPotential a)
        (fun w => complexSourceCoverRadialCutoff m w * W w i)
          i z) q = _
  rw [hproduct, torusScalarRepresentative_add,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_mul,
    torusScalarRepresentative_complexSourceCoverRadialCutoff]

private theorem torusHolomorphicDerivative_complexSourceCoverRadialCutoff
    {n : ℕ} (m : ℕ) (i : Fin n) (q : LogTorus n) :
    torusScalarRepresentative
      (fun z => holomorphicCoordinate
        (complexSourceCoverRadialCutoff m) z i) q =
      conj (sourceTorusBarPartial
        (complexSourceCoverRadialCutoff m) i q) := by
  change
    holomorphicCoordinate
      (fun z => (sourceCoverRadialCutoff m z : ℂ))
        (sourceTorusCoverPoint q) i =
      conj (barPartialCoordinate
        (fun z => (sourceCoverRadialCutoff m z : ℂ))
          (sourceTorusCoverPoint q) i)
  exact (conj_barPartialCoordinate_real
    ((contDiff_sourceCoverRadialCutoff m).differentiable
      (by norm_num)) (sourceTorusCoverPoint q) i).symm

private def angularSourceCutoffAdjointCommutator
    {n : ℕ} (m : ℕ)
    (W : LogSpace n → LogSpace n)
    (q : LogTorus n) : ℂ :=
  @inner ℂ (EuclideanSpace ℂ (Fin n)) _
    (sourceCutoffBarGradient m q)
    (torusFormRepresentative W q)

private theorem angularSourceCutoffAdjointCommutator_eq_sum
    {n : ℕ} (m : ℕ)
    (W : LogSpace n → LogSpace n)
    (q : LogTorus n) :
    angularSourceCutoffAdjointCommutator m W q =
      ∑ i : Fin n,
        torusScalarRepresentative (fun z => W z i) q *
          torusScalarRepresentative
            (fun z => holomorphicCoordinate
              (complexSourceCoverRadialCutoff m) z i) q := by
  unfold angularSourceCutoffAdjointCommutator
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [dotProduct, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [torusHolomorphicDerivative_complexSourceCoverRadialCutoff]
  rfl

private theorem angularTorusFormAdjoint_cutoffPhysicalField
    {n : ℕ} (a : LogTorus n → ℝ) (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W) (q : LogTorus n) :
    angularTorusFormAdjoint a (cutoffPhysicalField m W) q =
      (sourceRadialCutoff m q : ℂ) *
        angularTorusFormAdjoint a W q +
      angularSourceCutoffAdjointCommutator m W q := by
  unfold angularTorusFormAdjoint
  simp_rw [angularTorusWeightedHolomorphicDerivative_cutoffPhysicalField
    a m hW]
  rw [angularSourceCutoffAdjointCommutator_eq_sum]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

private theorem continuous_angularSourceCutoffAdjointCommutator
    {n : ℕ} (m : ℕ)
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hWp : ∀ q : Fin n → ℤ,
      Function.Periodic W (imaginaryShift q)) :
    Continuous (angularSourceCutoffAdjointCommutator m W) := by
  exact (continuous_sourceCutoffBarGradient m).inner
    (continuous_torusFormRepresentative_of_smooth_periodic hW hWp)

end TorusFriedrichsCutoff

namespace RadialAccelerationBounds

open Set Filter Function MeasureTheory
open JetEnvelopeGlobalPlurisubharmonic EnvelopeTorusDescent EnvelopeGeneralTorusDescent
open JetEnvelopeTrueRadialMollifier
open scoped Topology ENNReal Convolution ContDiff

local instance sourceJointCoverVolume_isAddHaar (n : ℕ) :
    Measure.IsAddHaarMeasure
      (volume : Measure (SourceJointComplexCover n)) :=
  Measure.prod.instIsAddHaarMeasure
    (volume : Measure (TorusCharacters.LogSpace n))
    (volume : Measure ℂ)

private def sourceJointTrueRadialTimeKernel (n k : ℕ)
    (y : SourceJointComplexCover n) : ℝ :=
  (fderiv ℝ (sourceJointTrueRadialMollifier n k) y)
    (sourceJointTimeDirection n)

private theorem hasCompactSupport_sourceJointTrueRadialTimeKernel (n k : ℕ) :
    HasCompactSupport (sourceJointTrueRadialTimeKernel n k) := by
  exact (hasCompactSupport_sourceJointTrueRadialMollifier n k).fderiv_apply
    ℝ (sourceJointTimeDirection n)

private theorem continuous_sourceJointTrueRadialTimeKernel (n k : ℕ) :
    Continuous (sourceJointTrueRadialTimeKernel n k) := by
  unfold sourceJointTrueRadialTimeKernel
  exact ((contDiff_sourceJointTrueRadialMollifier n k).continuous_fderiv
    (by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero,
          not_false_eq_true])).clm_apply continuous_const

private theorem integrable_sourceJointTrueRadialTimeKernel (n k : ℕ) :
    Integrable (sourceJointTrueRadialTimeKernel n k)
      (volume : Measure (SourceJointComplexCover n)) :=
  (continuous_sourceJointTrueRadialTimeKernel n k).integrable_of_hasCompactSupport
    (hasCompactSupport_sourceJointTrueRadialTimeKernel n k)

private def sourceJointTrueRadialTimeKernelMass (n k : ℕ) : ℝ :=
  ∫ y : SourceJointComplexCover n,
    |sourceJointTrueRadialTimeKernel n k y|

private theorem sourceJointTrueRadialTimeKernelMass_nonneg (n k : ℕ) :
    0 ≤ sourceJointTrueRadialTimeKernelMass n k := by
  exact integral_nonneg (fun y => abs_nonneg _)

private theorem jointSourceCoverVelocity_sourceJointTrueRadialSmoothed
    {n : ℕ} {f : SourceJointComplexCover n → ℝ}
    (hf : LocallyIntegrable f
      (volume : Measure (SourceJointComplexCover n)))
    (k : ℕ) (q : SourceJointComplexCover n) :
    jointSourceCoverVelocity (sourceJointTrueRadialSmoothed f k) q =
      (sourceJointTrueRadialTimeKernel n k
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (SourceJointComplexCover n))] f) q := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  let κ : SourceJointComplexCover n → ℝ :=
    sourceJointTrueRadialMollifier n k
  let v : SourceJointComplexCover n := sourceJointTimeDirection n
  have hκ : ContDiff ℝ 1 κ :=
    (contDiff_sourceJointTrueRadialMollifier n k).of_le (by simp only [WithTop.one_le_coe, le_top])
  have hc : HasCompactSupport κ :=
    hasCompactSupport_sourceJointTrueRadialMollifier n k
  have hd := hc.hasFDerivAt_convolution_left L hκ hf q
  have hint : Integrable
      (fun y : SourceJointComplexCover n =>
        (L.precompL (SourceJointComplexCover n))
          (fderiv ℝ κ y) (f (q - y)))
      (volume : Measure (SourceJointComplexCover n)) :=
    (hc.fderiv ℝ).convolutionExists_left
      (L.precompL (SourceJointComplexCover n))
      (hκ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) hf q
  change
    (fderiv ℝ
      (κ ⋆[L, (volume : Measure (SourceJointComplexCover n))] f)
      q) v =
    (sourceJointTrueRadialTimeKernel n k
      ⋆[L, (volume : Measure (SourceJointComplexCover n))] f) q
  rw [hd.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul,
    sourceJointTrueRadialTimeKernel, L, κ, v]

end RadialAccelerationBounds

namespace TorusWeakDolbeaultMollification

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths DolbeaultRegularity DolbeaultGraphDistributionBridge
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem barPartial_complexReal_convolution_eq_of_compact_green
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {G : Fin n → TorusCharacters.LogSpace n → ℂ}
    {κ : TorusCharacters.LogSpace n → ℝ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hκ : ContDiff ℝ 1 κ)
    (hκcompact : HasCompactSupport κ)
    (hweak : ∀ (ψ : TorusCharacters.LogSpace n → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ j : Fin n,
        (∫ t : TorusCharacters.LogSpace n,
          g t * coverBarPartialTest ψ j t
          ∂(volume : Measure (TorusCharacters.LogSpace n))) =
        -(2 : ℂ) *
          (∫ t : TorusCharacters.LogSpace n,
            G j t * (ψ t : ℂ)
            ∂(volume : Measure (TorusCharacters.LogSpace n))))
    (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (g ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ)
      x j =
    (G j ⋆[complexRealMultiplication,
      (volume : Measure (TorusCharacters.LogSpace n))] κ) x := by
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
          ∂μ) =
      -(2 : ℂ) *
        (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    simpa only [E, μ, v₀, v₁, coverBarPartialTest,
      translatedRealKernel_fderiv hκ x,
      Complex.ofReal_neg, mul_neg, ← neg_add] using htest
  have hpositive :
      (∫ t : E,
        g t *
          (((fderiv ℝ κ (x - t)) v₀ : ℂ) +
            Complex.I * ((fderiv ℝ κ (x - t)) v₁ : ℂ))
          ∂μ) =
      (2 : ℂ) *
        (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    rw [integral_neg] at hnegative
    linear_combination -hnegative
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
  have hgoal :
      (∫ t : E,
        (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ) =
        (2 : ℂ) *
          (∫ t : E, G j t * (κ (x - t) : ℂ) ∂μ) := by
    simpa [L, complexRealMultiplication,
      Complex.real_smul, mul_comm] using
      (hsplit.symm.trans hpositive)
  change
    ((∫ t : E,
      (L (g t)) ((fderiv ℝ κ (x - t)) v₀) ∂μ) +
      Complex.I *
        (∫ t : E,
          (L (g t)) ((fderiv ℝ κ (x - t)) v₁) ∂μ)) / 2 =
      (G j ⋆[complexRealMultiplication,
        (volume : Measure (TorusCharacters.LogSpace n))] κ) x
  rw [hgoal, MeasureTheory.convolution_def]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
    complexRealMultiplication_apply, mul_comm, E, μ]

private def normalizedCoverMollification {n : ℕ}
    (g : TorusCharacters.LogSpace n → ℂ) (k : ℕ) :
    TorusCharacters.LogSpace n → ℂ :=
  (complexShrinkingBump (n := n) k).normed
    (volume : Measure (TorusCharacters.LogSpace n))
    ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g

private theorem contDiff_normalizedCoverMollification
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (k r : ℕ) :
    ContDiff ℝ r (normalizedCoverMollification g k) := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ r κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  change ContDiff ℝ r
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (TorusCharacters.LogSpace n))] g)
  exact hκcompact.contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg

private theorem normalizedCoverMollification_periodic
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic g (TorusCharacters.imaginaryShift q))
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (normalizedCoverMollification g k)
      (TorusCharacters.imaginaryShift q) := by
  exact normalizedShrinkingConvolution_periodic hperiod k q

private theorem barPartial_normalizedCoverMollification_eq_of_compact_green
    {n : ℕ}
    {g : TorusCharacters.LogSpace n → ℂ}
    {G : Fin n → TorusCharacters.LogSpace n → ℂ}
    (hg : LocallyIntegrable g
      (volume : Measure (TorusCharacters.LogSpace n)))
    (hweak : ∀ (ψ : TorusCharacters.LogSpace n → ℝ),
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ j : Fin n,
        (∫ t : TorusCharacters.LogSpace n,
          g t * coverBarPartialTest ψ j t
          ∂(volume : Measure (TorusCharacters.LogSpace n))) =
        -(2 : ℂ) *
          (∫ t : TorusCharacters.LogSpace n,
            G j t * (ψ t : ℂ)
            ∂(volume : Measure (TorusCharacters.LogSpace n))))
    (k : ℕ) (x : TorusCharacters.LogSpace n) (j : Fin n) :
    barPartialCoordinate (normalizedCoverMollification g k) x j =
      normalizedCoverMollification (G j) k x := by
  let κ : TorusCharacters.LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (TorusCharacters.LogSpace n))
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have h := barPartial_complexReal_convolution_eq_of_compact_green
    (κ := κ) hg hκ hκcompact hweak x j
  simpa only [normalizedCoverMollification, κ,
    complex_convolution_flip] using h

end TorusWeakDolbeaultMollification

end Ehrhart

end
