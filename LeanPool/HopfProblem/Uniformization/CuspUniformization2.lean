/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core4
public import LeanPool.HopfProblem.PeriodFamily.PeriodDomain
import all LeanPool.HopfProblem.Foundations.Core1
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.Foundations.Core4
import all LeanPool.HopfProblem.PeriodFamily.PeriodDomain

/-!
# Hopf problem: uniformization · cusp uniformization 2

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

private def CuspUniformization.totalExponentialChart (p : LogModel) :
    OpenPartialHomeomorph LogModel (ToricCharts.CoordinateSpace 3) :=
  totalExponentialCoordinates_holomorphic.contDiffAt.toOpenPartialHomeomorph
    totalExponentialCoordinates (totalExponentialCoordinates_hasFDerivAt p) (by simp)

private theorem CuspUniformization.totalExponentialChart_mem_source (p : LogModel) :
    p ∈ (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffAt.mem_toOpenPartialHomeomorph_source
    (totalExponentialCoordinates_hasFDerivAt p) (by simp)

private theorem CuspUniformization.totalExponentialChart_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p) (totalExponentialChart p).source :=
  totalExponentialCoordinates_holomorphic.contDiffOn

private theorem CuspUniformization.totalExponentialChart_symm_holomorphic (p : LogModel) :
    ContDiffOn ℂ ω (totalExponentialChart p).symm (totalExponentialChart p).target := by
  intro w hw
  exact
    ((totalExponentialChart p).contDiffAt_symm hw
        (totalExponentialCoordinates_hasFDerivAt ((totalExponentialChart p).symm w))
        totalExponentialCoordinates_holomorphic.contDiffAt).contDiffWithinAt

private theorem CuspUniformization.totalExponentialCoordinates_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialCoordinates := by
  intro p
  refine
    ⟨{  toPartialEquiv := (totalExponentialChart p).toPartialEquiv
        open_source := (totalExponentialChart p).open_source
        open_target := (totalExponentialChart p).open_target
        contMDiffOn_toFun := (totalExponentialChart_holomorphic p).contMDiffOn
        contMDiffOn_invFun := (totalExponentialChart_symm_holomorphic p).contMDiffOn },
      totalExponentialChart_mem_source p, ?_⟩
  intro q _
  rfl

private theorem
    CuspUniformization.torusPoint_isLocalDiffeomorphAt {z : ToricCharts.CoordinateSpace 3}
    (hz : z ∈ ToricCharts.torus) :
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω torusPoint z := by
  refine
    ⟨{  toPartialEquiv := torusChart.symm.toPartialEquiv
        open_source := torusChart.open_target
        open_target := torusChart.open_source
        contMDiffOn_toFun := torusPoint_holomorphic
        contMDiffOn_invFun := ToricSpace.torusCoordinates_holomorphic }, hz, ?_⟩
  intro w _
  rfl

private theorem CuspUniformization.totalExponentialPoint_isLocalDiffeomorph :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω totalExponentialPoint := by
  intro p
  change
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (torusPoint ∘ totalExponentialCoordinates) p
  exact
    (totalExponentialCoordinates_isLocalDiffeomorph p).comp (K :=
      modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (P := ToricSpace.Space)
      (torusPoint_isLocalDiffeomorphAt (totalExponentialCoordinates_mem_torus p))

private theorem CuspUniformization.totalExponentialLift_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalExponentialLift ε) := by
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      totalExponentialPoint_isLocalDiffeomorph (logDomain ε)
      (ToricSpace.tubeOpen (CuspQuotient.disc ε))
      (fun p hp => (totalExponentialLift ε ⟨p, hp⟩).prop)

private theorem CuspUniformization.puncturedExponential_isLocalDiffeomorph (ε : ℝ) :
    IsLocalDiffeomorph (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedExponential ε) := by
  exact
    isLocalDiffeomorph_codRestrictOpens (modelWithCornersSelf ℂ LogModel)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (totalExponentialLift_isLocalDiffeomorph ε) (puncturedTubeOpen ε)
      (fun p => (puncturedExponential ε p).prop)

private theorem CuspUniformization.quotientMap_isLocalDiffeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (CuspQuotient.quotientMap C ε) :=
  by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    CoveringQuotient.project_isLocalDiffeomorph
      (CuspQuotient.quotientMap_covering C ε hε hε1 hC hR)
      (fun g => ToricSpace.tubeTranslate_holomorphic C (CuspQuotient.disc ε) g.toAdd hC)

private theorem CuspUniformization.puncturedQuotientMap_isLocalDiffeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedQuotientMap C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    isLocalDiffeomorph_restrictOpens (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (quotientMap_isLocalDiffeomorph C ε hε hε1 hC hR) (puncturedTubeOpen ε)
      (puncturedQuotientOpen C ε) (fun _ hx => hx)

private theorem CuspUniformization.puncturedCuspCover_isLocalDiffeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    IsLocalDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  intro p
  change
    IsLocalDiffeomorphAt (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
      (puncturedQuotientMap C ε ∘ puncturedExponential ε) p
  exact
    (puncturedExponential_isLocalDiffeomorph ε p).comp (K :=
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))) (P := PuncturedQuotient C ε)
      (puncturedQuotientMap_isLocalDiffeomorph C ε hε hε1 hC hR (puncturedExponential ε p))

private theorem CuspUniformization.puncturedCuspCover_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).contMDiff

private theorem
    CuspUniformization.puncturedCuspCover_isLocalHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsLocalHomeomorph (puncturedCuspCover C ε) := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR).isLocalHomeomorph

private theorem
    CuspUniformization.puncturedCuspCover_isOpenMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpenMap (puncturedCuspCover C ε) :=
  (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR).isOpenMap

/-- The setoid of total-period equivalence on the logarithmic cover. -/
public
def CuspUniformization.totalPeriodRelation (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    Setoid (LogCover ε) where
  r p q := TotalPeriodRelated C p q
  iseqv :=
    { refl p := (puncturedCuspCover_eq_iff C ε p p).mp rfl
      symm
        h :=
        (puncturedCuspCover_eq_iff C ε _ _).mp ((puncturedCuspCover_eq_iff C ε _ _).mpr h).symm
      trans h
        h' :=
        (puncturedCuspCover_eq_iff C ε _ _).mp
          (((puncturedCuspCover_eq_iff C ε _ _).mpr h).trans
            ((puncturedCuspCover_eq_iff C ε _ _).mpr h')) }

/-- The quotient of the logarithmic cover by total-period equivalence. -/
public
abbrev CuspUniformization.TotalPeriodQuotient (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :=
  Quotient (totalPeriodRelation C ε)

/-- The canonical map to the total-period quotient. -/
public
def CuspUniformization.totalPeriodQuotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    LogCover ε → TotalPeriodQuotient C ε :=
  Quotient.mk (totalPeriodRelation C ε)

private theorem
    CuspUniformization.totalPeriodQuotientMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Surjective (totalPeriodQuotientMap C ε) :=
  Quotient.mk_surjective

private theorem
    CuspUniformization.totalPeriodQuotientMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Continuous (totalPeriodQuotientMap C ε) :=
  continuous_quotient_mk'

@[simp]
public
theorem CuspUniformization.totalPeriodQuotientMap_eq_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p q : LogCover ε) :
    totalPeriodQuotientMap C ε p = totalPeriodQuotientMap C ε q ↔ TotalPeriodRelated C p q :=
  Quotient.eq''

private def CuspUniformization.totalUniformizationMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TotalPeriodQuotient C ε → PuncturedQuotient C ε :=
  Quotient.lift (puncturedCuspCover C ε) fun p q h => (puncturedCuspCover_eq_iff C ε p q).mpr h

private theorem
    CuspUniformization.totalUniformizationMap_bijective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Function.Bijective (totalUniformizationMap C ε) := by
  constructor
  · intro p q
    induction p using Quotient.inductionOn with
    | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
        intro h
        exact Quotient.sound ((puncturedCuspCover_eq_iff C ε p q).mp h)
  · intro q
    obtain ⟨p, hp⟩ := puncturedCuspCover_surjective C ε q
    exact ⟨totalPeriodQuotientMap C ε p, hp⟩

private def CuspUniformization.totalUniformizationEquiv (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) :
    TotalPeriodQuotient C ε ≃ PuncturedQuotient C ε :=
  Equiv.ofBijective (totalUniformizationMap C ε) (totalUniformizationMap_bijective C ε)

@[simp]
private theorem
    CuspUniformization.totalUniformizationEquiv_quotientMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    totalUniformizationEquiv C ε (totalPeriodQuotientMap C ε p) = puncturedCuspCover C ε p :=
  rfl

@[simp]
private theorem
    CuspUniformization.totalUniformizationEquiv_symm_cover (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (p : LogCover ε) :
    (totalUniformizationEquiv C ε).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p := by
  simpa only [totalUniformizationEquiv_quotientMap] using
    (totalUniformizationEquiv C ε).symm_apply_apply (totalPeriodQuotientMap C ε p)

private theorem
    CuspUniformization.totalUniformizationMap_continuous (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) : Continuous (totalUniformizationMap C ε) := by
  apply Continuous.quotient_lift
  exact
    ((CuspQuotient.quotientMap_continuous C ε).comp
          (totalExponentialLift_holomorphic ε).continuous).subtype_mk
      _

private theorem
    CuspUniformization.totalUniformizationMap_isOpenMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : IsOpenMap (totalUniformizationMap C ε) := by
  apply
    IsOpenMap.of_comp (totalPeriodQuotientMap_continuous C ε)
      (totalPeriodQuotientMap_surjective C ε)
  exact puncturedCuspCover_isOpenMap C ε hε hε1 hC hR

private def
    CuspUniformization.totalUniformizationHomeomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) : TotalPeriodQuotient C ε ≃ₜ PuncturedQuotient C ε :=
  (totalUniformizationEquiv C ε).toHomeomorphOfContinuousOpen
    (totalUniformizationMap_continuous C ε) (totalUniformizationMap_isOpenMap C ε hε hε1 hC hR)

@[simp]
private theorem CuspUniformization.totalUniformizationHomeomorph_symm_cover
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : LogCover ε) :
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm (puncturedCuspCover C ε p) =
      totalPeriodQuotientMap C ε p :=
  totalUniformizationEquiv_symm_cover C ε p

private theorem
    CuspUniformization.puncturedCuspCover_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (puncturedCuspCover C ε) LogDeck := by
  let := logCoverAction C ε
  let := logCover_continuousConstSMul C ε hC
  let := logCover_free_action C ε hε1 hR
  exact
    quotientCoveringMap_of_localHomeomorph (puncturedCuspCover_isLocalHomeomorph C ε hε hε1 hC hR)
      (puncturedCuspCover_surjective C ε) (puncturedCuspCover_eq_iff_orbit C ε)

private theorem
    CuspUniformization.totalPeriodQuotientMap_covering (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := logCoverAction C ε
    IsQuotientCoveringMap (totalPeriodQuotientMap C ε) LogDeck := by
  let := logCoverAction C ε
  have h :=
    (puncturedCuspCover_covering C ε hε hε1 hC hR).homeomorph_comp
      (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm
  have he :
    (totalUniformizationHomeomorph C ε hε hε1 hC hR).symm ∘ puncturedCuspCover C ε =
      totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationHomeomorph_symm_cover C ε hε hε1 hC hR p
  rwa [he] at h

@[instance_reducible]
private def
    CuspUniformization.totalPeriodQuotientChartedSpace (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    ChartedSpace (ℂ × ComplexPlane₂) (TotalPeriodQuotient C ε) :=
  letI := logCoverAction C ε
  CoveringQuotient.chartedSpace (E := ℂ × ComplexPlane₂)
    (totalPeriodQuotientMap_covering C ε hε hε1 hC hR)

private theorem
    CuspUniformization.totalPeriodQuotientMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (totalPeriodQuotientMap C ε) := by
  let := logCoverAction C ε
  exact
    CoveringQuotient.contMDiff_project (totalPeriodQuotientMap_covering C ε hε hε1 hC hR) ω
      (logCover_action_holomorphic C ε hC)

private theorem
    CuspUniformization.totalUniformizationMap_holomorphic (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω (totalUniformizationMap C ε) := by
  let := logCoverAction C ε
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply
    CoveringQuotient.contMDiff_of_comp (totalPeriodQuotientMap_covering C ε hε hε1 hC hR)
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) ω
  exact puncturedCuspCover_holomorphic C ε hε hε1 hC hR

private theorem CuspUniformization.totalUniformizationEquiv_symm_holomorphic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    ContMDiff (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)) ω (totalUniformizationEquiv C ε).symm := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  apply
    contMDiff_of_comp_localDiffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3))
      (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (puncturedCuspCover_isLocalDiffeomorph C ε hε hε1 hC hR) (puncturedCuspCover_surjective C ε)
  have he :
    (totalUniformizationEquiv C ε).symm ∘ puncturedCuspCover C ε = totalPeriodQuotientMap C ε := by
    funext p
    exact totalUniformizationEquiv_symm_cover C ε p
  rw [he]
  exact totalPeriodQuotientMap_holomorphic C ε hε hε1 hC hR

private def
    CuspUniformization.totalUniformizationBiholomorph (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    Diffeomorph (modelWithCornersSelf ℂ (ℂ × ComplexPlane₂))
      (modelWithCornersSelf ℂ (ToricCharts.CoordinateSpace 3)) (TotalPeriodQuotient C ε)
      (PuncturedQuotient C ε) ω := by
  let := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact
    { toEquiv := totalUniformizationEquiv C ε
      contMDiff_toFun := totalUniformizationMap_holomorphic C ε hε hε1 hC hR
      contMDiff_invFun := totalUniformizationEquiv_symm_holomorphic C ε hε hε1 hC hR }

@[simp]
private theorem CuspUniformization.totalUniformizationBiholomorph_quotientMap
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (p : LogCover ε) :
    letI := totalPeriodQuotientChartedSpace C ε hε hε1 hC hR
    letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
    totalUniformizationBiholomorph C ε hε hε1 hC hR (totalPeriodQuotientMap C ε p) =
      puncturedCuspCover C ε p :=
  rfl

private def CuspUniformization.sourcePeriodCoordinates : Lattice ≃+ FullPeriodMatrix.IntegerPeriods
    where
  toFun v := (![v 2, v 3], ![v 0, v 1])
  invFun c := ![c.2 0, c.2 1, c.1 0, c.1 1]
  left_inv v := by ext i; fin_cases i <;> rfl
  right_inv c := by apply Prod.ext <;> ext i <;> fin_cases i <;> rfl
  map_add' v w := by apply Prod.ext <;> ext i <;> fin_cases i <;> rfl

private def CuspUniformization.cuspLatticeProjection : Lattice →+ (Fin 2 → ℤ)
    where
  toFun v := ![v 0, v 1]
  map_zero' := by ext i; fin_cases i <;> rfl
  map_add' v w := by ext i; fin_cases i <;> rfl

private theorem CuspUniformization.cuspLatticeProjection_eq_zero_iff (v : Lattice) :
    cuspLatticeProjection v = 0 ↔ (M₀ - 1) *ᵥ v = 0 := by
  rw [M₀_sub_one_kernel]
  constructor
  · intro h
    exact ⟨congrFun h 0, congrFun h 1⟩
  · rintro ⟨h₀, h₁⟩
    ext i
    fin_cases i <;> assumption

private theorem
    CuspUniformization.exponentialLift_period_translate (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (z : ComplexPlane₂) (m n : Fin 2 → ℤ) :
    exponentialLift ε s hs
        (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
      ToricSpace.tubeTranslate C (CuspQuotient.disc ε) n (exponentialLift ε s hs z) := by
  apply Subtype.ext
  change
    exponentialPoint (exponential s)
        (z + (fun i => (m i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (n j : ℂ))) =
      ToricSpace.twistedTranslate C n (exponentialPoint (exponential s) z)
  rw [twistedTranslate_exponentialPoint]
  apply (exponentialPoint_eq_iff (exponential_ne_zero s) _ _).mpr
  exact ⟨m, by abel⟩

private def
    CuspUniformization.fibreFundamentalGroupMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FundamentalGroup (periodData C s hlog hRp).Torus 0 →*
      FundamentalGroup (CuspQuotient.QuotientSpace C ε)
        (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩ 0

private theorem
    CuspUniformization.fibreFundamentalGroupMap_marking (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp γ) =
      Multiplicative.ofAdd (((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2) := by
  let := ToricSpace.tubeAction C (CuspQuotient.disc ε)
  let p := periodData C s hlog hRp
  let hq := CuspQuotient.quotientMap_covering C ε hε hε1 hC hR
  let c := (p.fundamentalGroupEquiv γ).toAdd
  have hnat :=
    covering_monodromy_naturality p.quotientCovering.isCoveringMap hq.isCoveringMap
      ⟨exponentialLift ε s hs, exponentialLift_continuous ε s hs⟩
      ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩ (fun _ => rfl)
      (0 : ComplexPlane₂) γ
  have hper := p.fundamentalGroupEquiv_monodromy γ
  have htrans := exponentialLift_period_translate C ε s hs 0 c.1 c.2
  have he :
    ToricSpace.tubeTranslate C (CuspQuotient.disc ε)
        (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
            (fibreFundamentalGroupMap C ε s hs hlog hRp γ)).toAdd
        (exponentialLift ε s hs 0) =
      ToricSpace.tubeTranslate C (CuspQuotient.disc ε) c.2 (exponentialLift ε s hs 0) := by
    rw [CuspQuotient.fundamentalGroupEquivAt_monodromy]
    change
      (hq.isCoveringMap.monodromy
            (Path.Homotopic.Quotient.map γ
              ⟨fibreMap C ε s hs hlog hRp, fibreMap_continuous C ε s hs hlog hRp⟩)
            ⟨exponentialLift ε s hs 0, rfl⟩ :
          ToricSpace.Tube (CuspQuotient.disc ε)) =
        _
    apply hnat.trans
    apply (congrArg (exponentialLift ε s hs) hper.symm).trans
    change
      exponentialLift ε s hs
          ((fun i => (c.1 i : ℂ)) + logarithmicPeriod C s *ᵥ (fun j => (c.2 j : ℂ))) =
        _
    simpa only [zero_add] using htrans
  exact hq.isCancelSMul.right_cancel _ _ (exponentialLift ε s hs 0) he

private theorem
    CuspUniformization.fibrePeriodLoop_marking (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ)
    (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (m n : Fin 2 → ℤ) :
    CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)
        (fibreFundamentalGroupMap C ε s hs hlog hRp
          (FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (m, n)⟧)) =
      Multiplicative.ofAdd n := by
  rw [fibreFundamentalGroupMap_marking, FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]
  rfl

private theorem
    CuspUniformization.fibreFundamentalGroupMap_eq_one_iff (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreFundamentalGroupMap C ε s hs hlog hRp γ = 1 ↔
      ((periodData C s hlog hRp).fundamentalGroupEquiv γ).toAdd.2 = 0 := by
  rw [←
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR
        (exponentialLift ε s hs 0)).map_eq_one_iff,
    fibreFundamentalGroupMap_marking]
  rfl

private theorem
    CuspUniformization.fibreFundamentalGroupMap_surjective (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (fibreFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  let n :=
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0) γ).toAdd
  refine ⟨FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (0, n)⟧, ?_⟩
  apply
    (CuspQuotient.fundamentalGroupEquivAt C ε hε hε1 hC hR (exponentialLift ε s hs 0)).injective
  rw [fibrePeriodLoop_marking]
  rfl

private theorem CuspUniformization.fibre_integerPeriod_loop_nullhomotopic
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (m : Fin 2 → ℤ) :
    Path.Homotopic
      (((periodData C s hlog hRp).periodLoop (m, 0)).map (fibreMap_continuous C ε s hs hlog hRp))
      (Path.refl (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0))) := by
  have he :=
    (fibreFundamentalGroupMap_eq_one_iff C ε s hs hlog hRp hε hε1 hC hR
          (FundamentalGroup.fromPath ⟦(periodData C s hlog hRp).periodLoop (m, 0)⟧)).mpr
      (by rw [FullPeriodMatrix.fundamentalGroupEquiv_periodLoop]; rfl)
  exact Path.Homotopic.Quotient.eq.mp he

private def CuspUniformization.fibreBasePoint (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ)
    (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    CuspQuotient.projection C ε ⁻¹' {exponential s} :=
  fibreMapToFibre C ε s hs hlog hRp 0

private def CuspUniformization.fibreInclusionFundamentalGroupMap (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε) (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4) :
    FundamentalGroup (CuspQuotient.projection C ε ⁻¹' {exponential s})
        (fibreBasePoint C ε s hs hlog hRp) →*
      FundamentalGroup (CuspQuotient.QuotientSpace C ε)
        (CuspQuotient.quotientMap C ε (exponentialLift ε s hs 0)) :=
  FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (fibreBasePoint C ε s hs hlog hRp)

private theorem CuspUniformization.fibreInclusionFundamentalGroupMap_comp_homeomorph
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) (γ : FundamentalGroup (periodData C s hlog hRp).Torus 0) :
    fibreInclusionFundamentalGroupMap C ε s hs hlog hRp
        (homeomorphFundamentalGroupEquiv (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 γ) =
      fibreFundamentalGroupMap C ε s hs hlog hRp γ := by
  obtain ⟨γ⟩ := γ
  apply congrArg Path.Homotopic.Quotient.mk
  ext t
  rfl

private theorem CuspUniformization.fibreInclusionFundamentalGroupMap_surjective
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (s : ℂ) (hs : ‖exponential s‖ < ε)
    (hlog : Real.log ‖exponential s‖ < 0)
    (hRp :
      ToricSpace.entryNorm (ToricSpace.driftMatrix C (exponential s)) ≤
        -Real.log ‖exponential s‖ / 4)
    (hε : 0 < ε) (hε1 : ε < 1) (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
    (hR : ToricSpace.SmallDrift C ε) :
    Function.Surjective (fibreInclusionFundamentalGroupMap C ε s hs hlog hRp) := by
  intro γ
  obtain ⟨δ, hδ⟩ := fibreFundamentalGroupMap_surjective C ε s hs hlog hRp hε hε1 hC hR γ
  refine
    ⟨homeomorphFundamentalGroupEquiv (fibreHomeomorph C ε s hs hlog hRp hε hε1 hC hR) 0 δ, ?_⟩
  rw [fibreInclusionFundamentalGroupMap_comp_homeomorph]
  exact hδ

end Mathoverflow1973

end
