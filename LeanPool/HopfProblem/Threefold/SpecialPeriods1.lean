/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core4
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.PeriodFamily.HolomorphicPeriodMap1
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Foundations.Core4

/-!
# Hopf problem: threefold · special periods 1

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def SpecialPeriods.CuspFamily.logBase (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨CuspUniformization.exponential ⁻¹' Metric.ball 0 ε,
    Metric.isOpen_ball.preimage CuspUniformization.exponential_holomorphic.continuous⟩

private abbrev SpecialPeriods.CuspFamily.LogBase (ε : ℝ) :=
  logBase ε

@[simp]
private theorem SpecialPeriods.CuspFamily.mem_logBase (ε : ℝ) (s : ℂ) :
    s ∈ logBase ε ↔ ‖CuspUniformization.exponential s‖ < ε := by simp [logBase, Metric.mem_ball]

private def SpecialPeriods.CuspFamily.puncturedDisc (ε : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.ball 0 ε ∩ {t | t ≠ 0},
    Metric.isOpen_ball.inter (isOpen_ne_fun continuous_id continuous_const)⟩

@[simp]
private theorem SpecialPeriods.CuspFamily.mem_puncturedDisc (ε : ℝ) (t : ℂ) :
    t ∈ puncturedDisc ε ↔ ‖t‖ < ε ∧ t ≠ 0 := by simp [puncturedDisc, Metric.mem_ball]

private def SpecialPeriods.CuspFamily.baseExponential (ε : ℝ) (s : LogBase ε) : puncturedDisc ε :=
  ⟨CuspUniformization.exponential s, s.2, CuspUniformization.exponential_ne_zero s⟩

private theorem SpecialPeriods.CuspFamily.baseExponential_surjective (ε : ℝ) :
    Function.Surjective (baseExponential ε) := by
  intro t
  let s : LogBase ε :=
    ⟨CuspUniformization.logarithm t,
      by
      change CuspUniformization.exponential (CuspUniformization.logarithm t) ∈ Metric.ball 0 ε
      rw [CuspUniformization.exponential_logarithm t.2.2]
      exact t.2.1⟩
  exact ⟨s, Subtype.ext (CuspUniformization.exponential_logarithm t.2.2)⟩

private theorem SpecialPeriods.CuspFamily.exponential_sub_int (s : ℂ) (k : ℤ) :
    CuspUniformization.exponential (s - k) = CuspUniformization.exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, CuspUniformization.exponential_add,
    CuspUniformization.exponential_int, mul_one]

private def
    SpecialPeriods.CuspFamily.logBaseTranslate (ε : ℝ) (k : ℤ) (s : LogBase ε) : LogBase ε :=
  ⟨(s : ℂ) - k,
    by
    change CuspUniformization.exponential ((s : ℂ) - k) ∈ Metric.ball 0 ε
    rw [exponential_sub_int]
    exact s.2⟩

@[simp]
private theorem SpecialPeriods.CuspFamily.logBaseTranslate_coe (ε : ℝ) (k : ℤ) (s : LogBase ε) :
    (logBaseTranslate ε k s : ℂ) = (s : ℂ) - k :=
  rfl

@[instance_reducible]
private def
    SpecialPeriods.CuspFamily.logBaseAction (ε : ℝ) : MulAction (Multiplicative ℤ) (LogBase ε)
    where
  smul g s := logBaseTranslate ε g.toAdd s
  mul_smul g h
    s := by
    apply Subtype.ext
    change (s : ℂ) - ((g.toAdd + h.toAdd : ℤ) : ℂ) = ((s : ℂ) - h.toAdd) - g.toAdd
    push_cast
    abel
  one_smul
    s := by
    apply Subtype.ext
    change (s : ℂ) - ((1 : Multiplicative ℤ).toAdd : ℂ) = (s : ℂ)
    simp only [toAdd_one, Int.cast_zero, sub_zero]

private theorem SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic (ε : ℝ) (k : ℤ) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (logBaseTranslate ε k) := by
  intro s
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (Subtype.val ∘ logBaseTranslate ε k) s ↔
      ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω (logBaseTranslate ε k)
        s :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp ((contMDiff_subtype_val.sub contMDiff_const) s)

private theorem SpecialPeriods.CuspFamily.logBase_action_holomorphic (ε : ℝ) :
    letI := logBaseAction ε
    ∀ g : Multiplicative ℤ,
      ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
        (fun s : LogBase ε => g • s) := by
  let := logBaseAction ε
  intro g
  exact logBaseTranslate_holomorphic ε g.toAdd

private theorem SpecialPeriods.CuspFamily.logBase_continuousConstSMul (ε : ℝ) :
    letI := logBaseAction ε
    ContinuousConstSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  exact ⟨fun g => (logBase_action_holomorphic ε g).continuous⟩

private theorem SpecialPeriods.CuspFamily.logBase_free_action (ε : ℝ) :
    letI := logBaseAction ε
    IsCancelSMul (Multiplicative ℤ) (LogBase ε) := by
  let := logBaseAction ε
  constructor
  intro g h s he
  have hc := congrArg (Subtype.val : LogBase ε → ℂ) he
  change (s : ℂ) - g.toAdd = (s : ℂ) - h.toAdd at hc
  apply Multiplicative.toAdd.injective
  exact_mod_cast sub_right_inj.mp hc

@[simp]
private theorem SpecialPeriods.CuspFamily.baseExponential_smul (ε : ℝ) (g : Multiplicative ℤ)
    (s : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε (g • s) = baseExponential ε s := by
  let := logBaseAction ε
  apply Subtype.ext
  exact exponential_sub_int s g.toAdd

private theorem SpecialPeriods.CuspFamily.baseExponential_eq_iff_orbit (ε : ℝ) (s t : LogBase ε) :
    letI := logBaseAction ε
    baseExponential ε s = baseExponential ε t ↔ s ∈ MulAction.orbit (Multiplicative ℤ) t := by
  let := logBaseAction ε
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      (CuspUniformization.exponential_eq_iff (s : ℂ) t).mp (congrArg Subtype.val h)
    refine ⟨Multiplicative.ofAdd (-k), Subtype.ext ?_⟩
    change (t : ℂ) - ((-k : ℤ) : ℂ) = (s : ℂ)
    rw [hk, Int.cast_neg, sub_neg_eq_add]
  · rintro ⟨g, rfl⟩
    exact baseExponential_smul ε g t

private def SpecialPeriods.CuspFamily.scalarExponentialChart (s : ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  CuspUniformization.exponential_holomorphic.contDiffAt.toOpenPartialHomeomorph
    CuspUniformization.exponential
    ((CuspUniformization.exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (CuspUniformization.exponential_ne_zero s)
        CuspUniformization.exponential_factor_ne_zero))
    (by simp)

private theorem SpecialPeriods.CuspFamily.scalarExponentialChart_mem_source (s : ℂ) :
    s ∈ (scalarExponentialChart s).source :=
  CuspUniformization.exponential_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    ((CuspUniformization.exponential_hasDerivAt s).hasFDerivAt_equiv
      (mul_ne_zero (CuspUniformization.exponential_ne_zero s)
        CuspUniformization.exponential_factor_ne_zero))
    (by simp)

private theorem SpecialPeriods.CuspFamily.scalarExponentialChart_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s) (scalarExponentialChart s).source :=
  CuspUniformization.exponential_holomorphic.contDiffOn

private theorem SpecialPeriods.CuspFamily.scalarExponentialChart_symm_holomorphic (s : ℂ) :
    ContDiffOn ℂ ω (scalarExponentialChart s).symm (scalarExponentialChart s).target := by
  intro t ht
  exact
    ((scalarExponentialChart s).contDiffAt_symm ht
        ((CuspUniformization.exponential_hasDerivAt
              ((scalarExponentialChart s).symm t)).hasFDerivAt_equiv
          (mul_ne_zero (CuspUniformization.exponential_ne_zero _)
            CuspUniformization.exponential_factor_ne_zero))
        CuspUniformization.exponential_holomorphic.contDiffAt).contDiffWithinAt

private theorem SpecialPeriods.CuspFamily.exponential_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      CuspUniformization.exponential := by
  intro s
  refine
    ⟨{  toPartialEquiv := (scalarExponentialChart s).toPartialEquiv
        open_source := (scalarExponentialChart s).open_source
        open_target := (scalarExponentialChart s).open_target
        contMDiffOn_toFun := (scalarExponentialChart_holomorphic s).contMDiffOn
        contMDiffOn_invFun := (scalarExponentialChart_symm_holomorphic s).contMDiffOn },
      scalarExponentialChart_mem_source s, ?_⟩
  intro t _
  rfl

private theorem SpecialPeriods.CuspFamily.baseExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (baseExponential ε) :=
  isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
    exponential_isLocalDiffeomorph (logBase ε) (puncturedDisc ε)
    (fun s hs => ⟨hs, CuspUniformization.exponential_ne_zero s⟩)

private theorem SpecialPeriods.CuspFamily.baseExponential_isLocalHomeomorph (ε : ℝ) :
    IsLocalHomeomorph (baseExponential ε) :=
  (baseExponential_isLocalDiffeomorph ε).isLocalHomeomorph

private theorem SpecialPeriods.CuspFamily.baseExponential_covering (ε : ℝ) :
    letI := logBaseAction ε
    IsQuotientCoveringMap (baseExponential ε) (Multiplicative ℤ) := by
  let := logBaseAction ε
  let := logBase_continuousConstSMul ε
  let := logBase_free_action ε
  exact
    quotientCoveringMap_of_localHomeomorph (baseExponential_isLocalHomeomorph ε)
      (baseExponential_surjective ε) (baseExponential_eq_iff_orbit ε)

private instance SpecialPeriods.CuspFamily.logBaseProductChartedSpace (ε : ℝ) :
    ChartedSpace (ℂ × ComplexPlane₂) (LogBase ε × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (LogBase ε × ComplexPlane₂))

private instance SpecialPeriods.CuspFamily.logBaseProductManifold (ε : ℝ) :
    IsManifold (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (LogBase ε × ComplexPlane₂) := by
  rw [modelWithCornersSelf_prod]
  exact
    IsManifold.prod (I := (modelWithCornersSelf ℂ ℂ)) (I' :=
      (modelWithCornersSelf ℂ ComplexPlane₂)) (LogBase ε) ComplexPlane₂

private def SpecialPeriods.CuspFamily.logCoverProductEquiv (ε : ℝ) :
    CuspUniformization.LogCover ε ≃ (LogBase ε × ComplexPlane₂)
    where
  toFun p := (⟨p.1.1, p.2⟩, p.1.2)
  invFun p := ⟨((p.1 : ℂ), p.2), p.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
private theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_snd (ε : ℝ)
    (p : CuspUniformization.LogCover ε) : (logCoverProductEquiv ε p).2 = p.1.2 :=
  rfl

private theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε) := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : CuspUniformization.LogCover ε => p.1.1) :=
    contDiff_fst.contMDiff.comp contMDiff_subtype_val
  have hb' :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (fun p : CuspUniformization.LogCover ε => (⟨p.1.1, p.2⟩ : LogBase ε)) := by
    intro p
    have he :
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
          (Subtype.val ∘ fun q : CuspUniformization.LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p ↔
        ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
          (fun q : CuspUniformization.LogCover ε => (⟨q.1.1, q.2⟩ : LogBase ε)) p :=
      ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
    exact he.mp (hb p)
  have hz :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (fun p : CuspUniformization.LogCover ε => p.1.2) :=
    contDiff_snd.contMDiff.comp contMDiff_subtype_val
  rw [modelWithCornersSelf_prod]
  exact hb'.prodMk hz

private theorem SpecialPeriods.CuspFamily.logCoverProductEquiv_symm_holomorphic (ε : ℝ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε).symm := by
  have hb :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ℂ) ω
      (Prod.fst : LogBase ε × ComplexPlane₂ → LogBase ε) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_fst
  have hz :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (modelWithCornersSelf ℂ ComplexPlane₂)
      ω (Prod.snd : LogBase ε × ComplexPlane₂ → ComplexPlane₂) := by
    rw [modelWithCornersSelf_prod]
    exact contMDiff_snd
  have hp :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
      (fun p : LogBase ε × ComplexPlane₂ => ((p.1 : ℂ), p.2)) :=
    (contMDiff_subtype_val.comp hb).prodMk_space hz
  intro p
  have he :
    ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
        (Subtype.val ∘ (logCoverProductEquiv ε).symm) p ↔
      ContMDiffAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
        (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (logCoverProductEquiv ε).symm p :=
    ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..
  exact he.mp (hp p)

private def SpecialPeriods.CuspFamily.logCoverProductBiholomorph (ε : ℝ) :
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (CuspUniformization.LogCover ε)
      (LogBase ε × ComplexPlane₂) ω
    where
  toEquiv := logCoverProductEquiv ε
  contMDiff_toFun := logCoverProductEquiv_holomorphic ε
  contMDiff_invFun := logCoverProductEquiv_symm_holomorphic ε

/-- Analytic correction data defining a cusp family on a punctured disc. -/
public
structure SpecialPeriods.CuspFamily.Data where
  /-- The diagonal holomorphic correction coefficient. -/
  μ : ℂ → ℂ
  /-- The lower-left holomorphic correction coefficient. -/
  b : ℂ → ℂ
  /-- The off-diagonal holomorphic correction coefficient. -/
  h : ℂ → ℂ
  /-- The radius on which the cusp-family estimates hold. -/
  radius : ℝ
  radius_pos : 0 < radius
  radius_lt_one : radius < 1
  holomorphic :
    ∀ i j,
      ContDiffOn ℂ ω (fun t => SpecialPeriods.cuspCorrection μ b h t i j) (Metric.ball 0 radius)
  smallDrift : ToricSpace.SmallDrift (SpecialPeriods.cuspCorrection μ b h) radius

/-- The correction matrix associated to cusp-family data. -/
public
abbrev SpecialPeriods.CuspFamily.Data.correction (D : SpecialPeriods.CuspFamily.Data) :
    ℂ → Matrix (Fin 2) (Fin 2) ℂ :=
  SpecialPeriods.cuspCorrection D.μ D.b D.h

private theorem
    SpecialPeriods.CuspFamily.Data.logarithmic_height (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    Real.log ‖CuspUniformization.exponential (s : ℂ)‖ < 0 :=
  Real.log_neg (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))
    (((SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.2).trans D.radius_lt_one)

private theorem
    SpecialPeriods.CuspFamily.Data.logarithmic_drift (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    ToricSpace.entryNorm
        (ToricSpace.driftMatrix D.correction (CuspUniformization.exponential (s : ℂ))) ≤
      -Real.log ‖CuspUniformization.exponential (s : ℂ)‖ / 4 :=
  D.smallDrift _ (norm_pos_iff.mpr (CuspUniformization.exponential_ne_zero _))
    ((SpecialPeriods.CuspFamily.mem_logBase _ _).mp s.2)

private def SpecialPeriods.CuspFamily.Data.point (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) : PeriodDomain :=
  SpecialPeriods.cuspPeriodDomain D.μ D.b D.h s (D.logarithmic_height s) (D.logarithmic_drift s)

private theorem SpecialPeriods.CuspFamily.Data.correction_entry_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (i j : Fin 2) :
    ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun s : SpecialPeriods.CuspFamily.LogBase D.radius =>
        D.correction (CuspUniformization.exponential (s : ℂ)) i j) := by
  intro s
  have hC :
    ContMDiffAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω
      (fun t => D.correction t i j) (CuspUniformization.exponential (s : ℂ)) :=
    ((D.holomorphic i j).contDiffAt (Metric.isOpen_ball.mem_nhds s.2)).contMDiffAt
  exact
    hC.comp s
      ((CuspUniformization.exponential_holomorphic.contMDiff.comp
          contMDiff_subtype_val).contMDiffAt)

private def SpecialPeriods.CuspFamily.Data.periods (D : SpecialPeriods.CuspFamily.Data) :
    HolomorphicPeriodMap ℂ (SpecialPeriods.CuspFamily.LogBase D.radius)
    where
  point := D.point
  holomorphic_tau := contMDiff_subtype_val.add (D.correction_entry_holomorphic 0 1)
  holomorphic_mu := D.correction_entry_holomorphic 1 1
  holomorphic_beta := by
    convert (D.correction_entry_holomorphic 1 0).sub contMDiff_subtype_val using 1
    funext s
    change
      D.b (CuspUniformization.exponential (s : ℂ)) - (s : ℂ) -
          D.h (CuspUniformization.exponential (s : ℂ)) =
        (D.b (CuspUniformization.exponential (s : ℂ)) -
            D.h (CuspUniformization.exponential (s : ℂ))) -
          (s : ℂ)
    ring

@[simp]
private theorem SpecialPeriods.CuspFamily.Data.periods_point (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) : D.periods.point s = D.point s :=
  rfl

private theorem SpecialPeriods.CuspFamily.Data.point_leftBlock (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) :
    (D.point s).val.leftBlock = CuspUniformization.logarithmicPeriod D.correction (s : ℂ) :=
  SpecialPeriods.cuspPeriodPoint_leftBlock D.μ D.b D.h s

private abbrev SpecialPeriods.CuspFamily.Data.TotalSpace (D : SpecialPeriods.CuspFamily.Data) :=
  D.periods.TotalSpace

private def SpecialPeriods.CuspFamily.Data.familyCover (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.LogCover D.radius → D.TotalSpace :=
  D.periods.quotientMap ∘ SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius

@[simp]
private theorem
    SpecialPeriods.CuspFamily.Data.familyCover_apply (D : SpecialPeriods.CuspFamily.Data)
    (x : CuspUniformization.LogCover D.radius) :
    D.familyCover x = D.periods.quotientMap (⟨x.1.1, x.2⟩, x.1.2) :=
  rfl

private theorem SpecialPeriods.CuspFamily.Data.familyCover_surjective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Surjective D.familyCover :=
  D.periods.quotientMap_surjective.comp
    (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius).surjective

private theorem SpecialPeriods.CuspFamily.Data.familyCover_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  exact
    D.periods.quotientMap_holomorphic.comp
      (SpecialPeriods.CuspFamily.logCoverProductBiholomorph D.radius).contMDiff

private theorem SpecialPeriods.CuspFamily.Data.familyCover_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.familyCover := by
  let := D.periods.totalChartedSpace
  let := D.periods.coveringAction
  have hq :=
    CoveringQuotient.project_isLocalDiffeomorph D.periods.quotientCoveringMap
      D.periods.coveringAction_holomorphic
  intro x
  exact
    ((SpecialPeriods.CuspFamily.logCoverProductBiholomorph D.radius).isLocalDiffeomorph x).comp
      (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) (P := D.TotalSpace)
      (hq (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius x))

private theorem
    SpecialPeriods.CuspFamily.Data.quotientMap_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    D.periods.quotientMap x = D.periods.quotientMap y ↔
      x.1 = y.1 ∧ x.2 - y.2 ∈ (D.periods.point y.1).lattice := by
  rcases x with ⟨s, z⟩
  rcases y with ⟨t, w⟩
  constructor
  · intro he
    have hs : s = t := congrArg Prod.fst he
    subst t
    refine ⟨rfl, ?_⟩
    apply (Submodule.Quotient.eq _).mp
    exact (D.periods.fibreInclusion_injective s) he
  · rintro ⟨hs, he⟩
    dsimp only at hs he
    subst t
    exact congrArg (D.periods.fibreInclusion s) ((Submodule.Quotient.eq _).mpr he)

private theorem
    SpecialPeriods.CuspFamily.Data.familyCover_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : CuspUniformization.LogCover D.radius) :
    D.familyCover x = D.familyCover y ↔
      x.1.1 = y.1.1 ∧
        ∃ m n : Fin 2 → ℤ,
          x.1.2 =
            y.1.2 + (fun i => (m i : ℂ)) +
              CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) := by
  let s : SpecialPeriods.CuspFamily.LogBase D.radius := ⟨y.1.1, y.2⟩
  have hlat :
    (D.periods.point s).lattice =
      (CuspUniformization.periodData D.correction y.1.1 (D.logarithmic_height s)
          (D.logarithmic_drift s)).lattice := by
    exact
      (SpecialPeriods.cusp_period_lattice_eq D.μ D.b D.h (D.point s) y.1.1 rfl rfl rfl
          (D.logarithmic_height s) (D.logarithmic_drift s)).symm
  rw [familyCover_apply, familyCover_apply, D.quotientMap_eq_iff]
  change
    (⟨x.1.1, x.2⟩ : SpecialPeriods.CuspFamily.LogBase D.radius) = s ∧
        x.1.2 - y.1.2 ∈ (D.periods.point s).lattice ↔
      _
  rw [hlat, FullPeriodMatrix.mem_lattice_iff]
  constructor
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨congrArg Subtype.val hs, m, n, ?_⟩
    change
      x.1.2 - y.1.2 =
        (fun i => (m i : ℂ)) +
          CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ)) at hmn
    rw [sub_eq_iff_eq_add] at hmn
    rw [hmn]
    abel
  · rintro ⟨hs, m, n, hmn⟩
    refine ⟨Subtype.ext hs, m, n, ?_⟩
    change
      x.1.2 - y.1.2 =
        (fun i => (m i : ℂ)) +
          CuspUniformization.logarithmicPeriod D.correction y.1.1 *ᵥ (fun i => (n i : ℂ))
    rw [hmn]
    abel

private def SpecialPeriods.CuspFamily.cuspIntegralMatrix (k : ℤ) : LatticeMatrix :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, k, 1, 0; -k, 0, 0, 1]

@[simp]
private theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_zero : cuspIntegralMatrix 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspIntegralMatrix]

@[simp]
private theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_one : cuspIntegralMatrix 1 = M₀ :=
  rfl

private theorem SpecialPeriods.CuspFamily.cuspIntegralMatrix_add (k l : ℤ) :
    cuspIntegralMatrix (k + l) = cuspIntegralMatrix k * cuspIntegralMatrix l := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cuspIntegralMatrix, Matrix.mul_apply, Fin.sum_univ_four]
  all_goals ring

private def SpecialPeriods.CuspFamily.cuspRealEquiv (k : ℤ) : RealPlane₄ ≃ₗ[ℝ] RealPlane₄
    where
  toFun x := ![x 0, x 1, x 2 + (k : ℝ) * x 1, x 3 - (k : ℝ) * x 0]
  invFun x := ![x 0, x 1, x 2 - (k : ℝ) * x 1, x 3 + (k : ℝ) * x 0]
  map_add' x
    y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a
    x := by
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring
  left_inv
    x := by
    ext i
    fin_cases i <;> simp
  right_inv
    x := by
    ext i
    fin_cases i <;> simp

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_apply (k : ℤ) (x : RealPlane₄) :
    cuspRealEquiv k x = (cuspIntegralMatrix k).map (Int.castRingHom ℝ) *ᵥ x := by
  ext i
  fin_cases i <;>
      simp [cuspRealEquiv, cuspIntegralMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring

@[simp]
private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_zero :
    cuspRealEquiv 0 = LinearEquiv.refl ℝ RealPlane₄ := by
  ext x i
  fin_cases i <;> simp [cuspRealEquiv]

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_add_apply (k l : ℤ) (x : RealPlane₄) :
    cuspRealEquiv (k + l) x = cuspRealEquiv k (cuspRealEquiv l x) := by
  ext i
  fin_cases i <;> simp [cuspRealEquiv] <;> ring

@[simp]
private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_neg (k : ℤ) :
    cuspRealEquiv (-k) = (cuspRealEquiv k).symm := by
  ext x i
  fin_cases i <;> simp [cuspRealEquiv, sub_eq_add_neg]

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_realCast (k : ℤ) (v : Lattice) :
    cuspRealEquiv k (Elliptic.realCast v) = Elliptic.realCast (cuspIntegralMatrix k *ᵥ v) := by
  rw [cuspRealEquiv_apply]
  ext i
  exact (RingHom.map_mulVec (Int.castRingHom ℝ) (cuspIntegralMatrix k) v i).symm

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_complexCast (k : ℤ) (x : RealPlane₄) :
    (fun i => ((cuspRealEquiv k x) i : ℂ)) =
      (cuspIntegralMatrix k).map (Int.castRingHom ℂ) *ᵥ (fun i => (x i : ℂ)) := by
  ext i
  fin_cases i <;>
      simp [cuspRealEquiv, cuspIntegralMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;>
    ring

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_mem_standardLattice (k : ℤ) {x : RealPlane₄}
    (hx : x ∈ standardLattice) : cuspRealEquiv k x ∈ standardLattice := by
  obtain ⟨v, rfl⟩ := (Elliptic.standardLattice_mem_iff x).mp hx
  exact
    (Elliptic.standardLattice_mem_iff _).mpr
      ⟨cuspIntegralMatrix k *ᵥ v, cuspRealEquiv_realCast k v⟩

private theorem SpecialPeriods.CuspFamily.cuspRealEquiv_map_standardLattice (k : ℤ) :
    standardLattice.map ((cuspRealEquiv k).restrictScalars ℤ).toLinearMap = standardLattice := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact cuspRealEquiv_mem_standardLattice k hy
  · intro hx
    refine ⟨cuspRealEquiv (-k) x, cuspRealEquiv_mem_standardLattice (-k) hx, ?_⟩
    change cuspRealEquiv k (cuspRealEquiv (-k) x) = x
    rw [cuspRealEquiv_neg, LinearEquiv.apply_symm_apply]

/-- The lattice-linear automorphism of the cusp torus with exponent `k`. -/
public
def SpecialPeriods.CuspFamily.cuspTorusLinearEquiv (k : ℤ) : RealTorus₄ ≃ₗ[ℤ] RealTorus₄ :=
  Submodule.Quotient.equiv standardLattice standardLattice ((cuspRealEquiv k).restrictScalars ℤ)
    (cuspRealEquiv_map_standardLattice k)

/-- The torus homeomorphism induced by the cusp lattice automorphism. -/
public
def SpecialPeriods.CuspFamily.cuspTorusHomeomorph (k : ℤ) : RealTorus₄ ≃ₜ RealTorus₄
    where
  toEquiv := (cuspTorusLinearEquiv k).toEquiv
  continuous_toFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact standardLattice.continuous_mkQ.comp (cuspRealEquiv k).toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply standardLattice.isQuotientMap_mkQ.continuous_iff.mpr
    exact
      standardLattice.continuous_mkQ.comp
        (cuspRealEquiv k).symm.toContinuousLinearEquiv.continuous

private theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ (k : ℤ) (x : RealPlane₄) :
    cuspTorusHomeomorph k (standardLattice.mkQ x) = standardLattice.mkQ (cuspRealEquiv k x) :=
  rfl

private theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_apply (x : RealTorus₄) :
    cuspTorusHomeomorph 0 x = x := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspRealEquiv_zero]
  rfl

@[simp]
private theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_eq :
    cuspTorusHomeomorph 0 = Homeomorph.refl RealTorus₄ := by
  apply Homeomorph.ext
  exact cuspTorusHomeomorph_zero_apply

private theorem SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply (k l : ℤ) (x : RealTorus₄) :
    cuspTorusHomeomorph (k + l) x = cuspTorusHomeomorph k (cuspTorusHomeomorph l x) := by
  obtain ⟨y, rfl⟩ := standardLattice.mkQ_surjective x
  rw [cuspTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ, cuspTorusHomeomorph_mkQ,
    cuspRealEquiv_add_apply]

@[instance_reducible]
private def SpecialPeriods.CuspFamily.cuspTorusAction : MulAction (Multiplicative ℤ) RealTorus₄
    where
  smul k x := cuspTorusHomeomorph k.toAdd x
  one_smul := cuspTorusHomeomorph_zero_apply
  mul_smul k l := cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

@[simp]
private theorem SpecialPeriods.CuspFamily.cusp_exponential_sub_int (s : ℂ) (k : ℤ) :
    CuspUniformization.exponential (s - (k : ℂ)) = CuspUniformization.exponential s := by
  rw [sub_eq_add_neg, ← Int.cast_neg, CuspUniformization.exponential_add,
    CuspUniformization.exponential_int, mul_one]

private theorem SpecialPeriods.CuspFamily.cuspPeriodPoint_matrix_covariance (μ b h : ℂ → ℂ) (s : ℂ)
    (k : ℤ) :
    (SpecialPeriods.cuspPeriodPoint μ b h (s - (k : ℂ))).matrix *
        (cuspIntegralMatrix k).map (Int.castRingHom ℂ) =
      (SpecialPeriods.cuspPeriodPoint μ b h s).matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
      simp [PeriodPoint.matrix, SpecialPeriods.cuspPeriodPoint, cuspIntegralMatrix,
        Matrix.mul_apply, Fin.sum_univ_four, cusp_exponential_sub_int] <;>
    ring

@[instance_reducible]
private def SpecialPeriods.CuspFamily.Data.totalAction (D : SpecialPeriods.CuspFamily.Data) :
    MulAction (Multiplicative ℤ) D.TotalSpace := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := SpecialPeriods.CuspFamily.cuspTorusAction
  exact
    inferInstanceAs
      (MulAction (Multiplicative ℤ) (SpecialPeriods.CuspFamily.LogBase D.radius × RealTorus₄))

private theorem SpecialPeriods.CuspFamily.Data.totalAction_continuous
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.totalAction
    ContinuousConstSMul (Multiplicative ℤ) D.TotalSpace := by
  let := D.totalAction
  constructor
  intro k
  exact
    ((SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic D.radius k.toAdd).continuous.comp
          continuous_fst).prodMk
      ((SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd).continuous.comp continuous_snd)

private theorem
    SpecialPeriods.CuspFamily.Data.periodEquiv_matrix (D : SpecialPeriods.CuspFamily.Data)
    (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv s x = (D.periods.point s).val.matrix *ᵥ (fun i => (x i : ℂ)) := by
  rw [HolomorphicPeriodMap.periodEquiv_coordinates]
  ext i
  fin_cases i <;> simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

private theorem
    SpecialPeriods.CuspFamily.Data.periodEquiv_monodromy (D : SpecialPeriods.CuspFamily.Data)
    (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase D.radius) (x : RealPlane₄) :
    D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)
        (SpecialPeriods.CuspFamily.cuspRealEquiv k x) =
      D.periods.periodEquiv s x := by
  rw [D.periodEquiv_matrix, SpecialPeriods.CuspFamily.cuspRealEquiv_complexCast,
    Matrix.mulVec_mulVec, D.periodEquiv_matrix]
  change
    ((SpecialPeriods.cuspPeriodPoint D.μ D.b D.h ((s : ℂ) - (k : ℂ))).matrix *
          (SpecialPeriods.CuspFamily.cuspIntegralMatrix k).map (Int.castRingHom ℂ)) *ᵥ
        (fun i => (x i : ℂ)) =
      _
  rw [SpecialPeriods.CuspFamily.cuspPeriodPoint_matrix_covariance]
  rfl

private theorem SpecialPeriods.CuspFamily.Data.periodEquiv_symm_monodromy
    (D : SpecialPeriods.CuspFamily.Data) (k : ℤ) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (z : ComplexPlane₂) :
    (D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)).symm z =
      SpecialPeriods.CuspFamily.cuspRealEquiv k ((D.periods.periodEquiv s).symm z) := by
  apply
    (D.periods.periodEquiv (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k s)).injective
  rw [LinearEquiv.apply_symm_apply, D.periodEquiv_monodromy, LinearEquiv.apply_symm_apply]

private def SpecialPeriods.CuspFamily.Data.complexLift (D : SpecialPeriods.CuspFamily.Data)
    (k : Multiplicative ℤ) (x : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂ :=
  (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1, x.2)

private theorem SpecialPeriods.CuspFamily.Data.complexLift_quotientMap
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ)
    (x : SpecialPeriods.CuspFamily.LogBase D.radius × ComplexPlane₂) :
    letI := D.totalAction
    D.periods.quotientMap (D.complexLift k x) = k • D.periods.quotientMap x := by
  let := D.totalAction
  change
    (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1,
        standardLattice.mkQ
          ((D.periods.periodEquiv
                (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1)).symm
            x.2)) =
      (SpecialPeriods.CuspFamily.logBaseTranslate D.radius k.toAdd x.1,
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd
          (standardLattice.mkQ ((D.periods.periodEquiv x.1).symm x.2)))
  rw [D.periodEquiv_symm_monodromy, SpecialPeriods.CuspFamily.cuspTorusHomeomorph_mkQ]

private theorem SpecialPeriods.CuspFamily.Data.complexLift_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) :
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (D.complexLift k) := by
  rw [modelWithCornersSelf_prod]
  exact
    ((SpecialPeriods.CuspFamily.logBaseTranslate_holomorphic D.radius k.toAdd).comp
          contMDiff_fst).prodMk
      contMDiff_snd

private theorem SpecialPeriods.CuspFamily.Data.totalAction_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) :
    letI := D.periods.totalChartedSpace
    letI := D.totalAction
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (fun x : D.TotalSpace => k • x) := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  let := D.periods.coveringAction
  apply
    CoveringQuotient.contMDiff_of_comp D.periods.quotientCoveringMap
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω
  have hf := D.periods.quotientMap_holomorphic.comp (D.complexLift_holomorphic k)
  exact hf.congr (fun x => (D.complexLift_quotientMap k x).symm)

private theorem SpecialPeriods.CuspFamily.Data.familyCover_logarithmicShift
    (D : SpecialPeriods.CuspFamily.Data) (k : ℤ) (x : CuspUniformization.LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      Multiplicative.ofAdd (-k) • D.familyCover x := by
  let := D.totalAction
  have he :
    SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius
        (CuspUniformization.logCoverTransform D.correction D.radius ⟨k, 0, 0⟩ x) =
      D.complexLift (Multiplicative.ofAdd (-k))
        (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius x) := by
    apply Prod.ext
    · apply Subtype.ext
      change x.1.1 + (k : ℂ) = x.1.1 - ((-k : ℤ) : ℂ)
      simp only [Int.cast_neg, sub_neg_eq_add]
    · simp only [SpecialPeriods.CuspFamily.logCoverProductEquiv_snd,
        CuspUniformization.logCoverTransform_coe, CuspUniformization.logDeckTransform_snd,
        Pi.zero_apply, Int.cast_zero, ofAdd_neg]
      change
        x.1.2 + (0 : ComplexPlane₂) +
            CuspUniformization.logarithmicPeriod D.correction x.1.1 *ᵥ 0 =
          x.1.2
      rw [add_zero, Matrix.mulVec_zero, add_zero]
  change D.periods.quotientMap (SpecialPeriods.CuspFamily.logCoverProductEquiv D.radius _) = _
  rw [he, D.complexLift_quotientMap]
  rfl

private theorem
    SpecialPeriods.CuspFamily.Data.familyCover_period (D : SpecialPeriods.CuspFamily.Data)
    (m n : Fin 2 → ℤ) (x : CuspUniformization.LogCover D.radius) :
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius ⟨0, m, n⟩ x) =
      D.familyCover x := by
  apply (D.familyCover_eq_iff _ x).mpr
  refine ⟨?_, m, n, rfl⟩
  change x.1.1 + ((0 : ℤ) : ℂ) = x.1.1
  simp

private theorem
    SpecialPeriods.CuspFamily.Data.familyCover_logDeck (D : SpecialPeriods.CuspFamily.Data)
    (g : CuspUniformization.LogDeck) (x : CuspUniformization.LogCover D.radius) :
    letI := D.totalAction
    D.familyCover (CuspUniformization.logCoverTransform D.correction D.radius g x) =
      Multiplicative.ofAdd (-g.k) • D.familyCover x := by
  let := D.totalAction
  have hg : g = (⟨g.k, 0, 0⟩ : CuspUniformization.LogDeck) * ⟨0, g.m, g.n⟩ := by
    apply CuspUniformization.LogDeck.ext <;> simp
  have he :
    CuspUniformization.logCoverTransform D.correction D.radius g x =
      CuspUniformization.logCoverTransform D.correction D.radius ⟨g.k, 0, 0⟩
        (CuspUniformization.logCoverTransform D.correction D.radius ⟨0, g.m, g.n⟩ x) := by
    apply Subtype.ext
    exact
      (congrArg (fun u => CuspUniformization.logDeckTransform D.correction u x) hg).trans
        (CuspUniformization.logDeckTransform_mul D.correction _ _ x)
  rw [he, D.familyCover_logarithmicShift, D.familyCover_period]

/-- The quotient total space of a cusp family. -/
public
def SpecialPeriods.CuspFamily.Data.Space (D : SpecialPeriods.CuspFamily.Data) : Type :=
  @MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction

private instance SpecialPeriods.CuspFamily.Data.spaceTopology (D : SpecialPeriods.CuspFamily.Data) :
    TopologicalSpace D.Space :=
  inferInstanceAs
    (TopologicalSpace
      (@MulAction.orbitRel.Quotient (Multiplicative ℤ) D.TotalSpace _ D.totalAction))

private def SpecialPeriods.CuspFamily.Data.quotient (D : SpecialPeriods.CuspFamily.Data) :
    D.TotalSpace → D.Space := by
  let := D.totalAction
  exact Quotient.mk (MulAction.orbitRel (Multiplicative ℤ) D.TotalSpace)

private theorem
    SpecialPeriods.CuspFamily.Data.quotient_surjective (D : SpecialPeriods.CuspFamily.Data) :
    Function.Surjective D.quotient :=
  Quotient.mk_surjective

private theorem SpecialPeriods.CuspFamily.Data.quotient_eq_iff (D : SpecialPeriods.CuspFamily.Data)
    (x y : D.TotalSpace) :
    letI := D.totalAction
    D.quotient x = D.quotient y ↔ ∃ k : Multiplicative ℤ, k • y = x :=
  Quotient.eq''

@[simp]
private theorem SpecialPeriods.CuspFamily.Data.quotient_smul (D : SpecialPeriods.CuspFamily.Data)
    (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    D.quotient (k • x) = D.quotient x := by
  let := D.totalAction
  exact (D.quotient_eq_iff _ _).mpr ⟨k, rfl⟩

private def SpecialPeriods.CuspFamily.Data.projection (D : SpecialPeriods.CuspFamily.Data) :
    D.Space → SpecialPeriods.CuspFamily.puncturedDisc D.radius := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := D.totalAction
  exact
    Quotient.lift (fun x : D.TotalSpace => SpecialPeriods.CuspFamily.baseExponential D.radius x.1)
      (by
        rintro x y ⟨k, hk⟩
        rw [← hk]
        exact SpecialPeriods.CuspFamily.baseExponential_smul D.radius k y.1)

@[simp]
private theorem
    SpecialPeriods.CuspFamily.Data.projection_quotient (D : SpecialPeriods.CuspFamily.Data)
    (x : D.TotalSpace) :
    D.projection (D.quotient x) = SpecialPeriods.CuspFamily.baseExponential D.radius x.1 :=
  rfl

private theorem
    SpecialPeriods.CuspFamily.Data.quotientCoveringMap (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.totalAction
    IsQuotientCoveringMap D.quotient (Multiplicative ℤ) := by
  let := SpecialPeriods.CuspFamily.logBaseAction D.radius
  let := D.totalAction
  let := D.totalAction_continuous
  refine
    { toIsQuotientMap := isQuotientMap_quotient_mk'
      continuous_const_smul := ContinuousConstSMul.continuous_const_smul
      apply_eq_iff_mem_orbit := Quotient.eq''
      disjoint := ?_ }
  intro x
  obtain ⟨U, hU, hd⟩ := (SpecialPeriods.CuspFamily.baseExponential_covering D.radius).disjoint x.1
  refine ⟨Prod.fst ⁻¹' U, continuous_fst.continuousAt hU, ?_⟩
  rintro k ⟨z, ⟨w, hw, rfl⟩, hz⟩
  exact hd k ⟨k • w.1, ⟨w.1, hw, rfl⟩, hz⟩

@[instance_reducible]
private def SpecialPeriods.CuspFamily.Data.chartedSpace (D : SpecialPeriods.CuspFamily.Data) :
    ChartedSpace (ℂ × ComplexPlane₂) D.Space := by
  let := D.periods.totalChartedSpace
  let := D.totalAction
  exact CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂) D.quotientCoveringMap

private theorem
    SpecialPeriods.CuspFamily.Data.quotient_holomorphic (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact CoveringQuotient.contMDiff_project D.quotientCoveringMap ω D.totalAction_holomorphic

private theorem SpecialPeriods.CuspFamily.Data.quotient_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.periods.totalChartedSpace
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.quotient := by
  let := D.periods.totalChartedSpace
  let := D.periods.totalSpace_isManifold
  let := D.totalAction
  exact
    CoveringQuotient.project_isLocalDiffeomorph D.quotientCoveringMap D.totalAction_holomorphic

/-- The covering map from the logarithmic cover to the cusp-family space. -/
public
def SpecialPeriods.CuspFamily.Data.iteratedCover (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.LogCover D.radius → D.Space :=
  D.quotient ∘ D.familyCover

private theorem SpecialPeriods.CuspFamily.Data.iteratedCover_surjective
    (D : SpecialPeriods.CuspFamily.Data) : Function.Surjective D.iteratedCover :=
  D.quotient_surjective.comp D.familyCover_surjective

private theorem SpecialPeriods.CuspFamily.Data.iteratedCover_holomorphic
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  exact D.quotient_holomorphic.comp D.familyCover_holomorphic

private theorem SpecialPeriods.CuspFamily.Data.iteratedCover_isLocalDiffeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    letI := D.chartedSpace
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω D.iteratedCover := by
  let := D.periods.totalChartedSpace
  let := D.chartedSpace
  intro x
  exact
    (D.familyCover_isLocalDiffeomorph x).comp (K := modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (P := D.Space) (D.quotient_isLocalDiffeomorph (D.familyCover x))

@[simp]
private theorem SpecialPeriods.CuspFamily.Data.projection_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (x : CuspUniformization.LogCover D.radius) :
    (D.projection (D.iteratedCover x) : ℂ) = CuspUniformization.exponential x.1.1 :=
  rfl

end Mathoverflow1973

end
