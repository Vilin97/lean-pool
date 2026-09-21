/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.ExtendedMilnorInstance
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.Over.SheafyEndpoints

/-!
# From the Gauss ring to the Tate extension over a general nonarchimedean base

The Gauss-normed ring `StrictLoc.PA K n` and the topological Tate extension
`(JetA K)⟨V₁,…,Vₙ⟩ = restrictedMvPowerSeriesSubring n (JetA K)` are the same subring
of the power-series ring. This file proves that the identification is a homeomorphism and
transports `isSheafy_extJetA` to the canonical Tate-algebra topology.  The
sheafiness statements require a uniformizer and noetherianity of the base norm
unit ball; a discrete valuation ring supplies both in `StrongSheafy.lean`.
-/

@[expose] public section

noncomputable section

namespace FiniteJetOver

open FiniteJet ValuationSpectrum TopologicalRing GraphKoszul MvTateAlgebra

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (n : ℕ)

/-! ### The two continuity directions -/

/-- The identification from the Gauss topology to the canonical Tate-algebra topology is
continuous. -/
theorem gaussToTate_continuous :
    @Continuous (StrictLoc.PA K n) ↥(restrictedMvPowerSeriesSubring n (JetA K)) _
      (mvTateAlgebraTopology' (A := JetA K) n)
      ⇑(UnitDiscExample.restrictedGaussEquiv (JetA K) n) := by
  let _i := mvTateAlgebraTopology' (A := JetA K) n
  have := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
  set P := IsTateRing.principalPair (JetA K) with hPdef
  refine continuous_of_continuousAt_zero
    (UnitDiscExample.restrictedGaussEquiv (JetA K) n).toRingHom.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((mvTateAlgBasis' (A := JetA K) n).hasBasis_nhds_zero.tendsto_right_iff).mpr ?_
  intro j _
  have hIj : (Subtype.val ''
      ((P.toPairOfDefinition.I ^ j : Ideal P.toPairOfDefinition.A₀) :
        Set P.toPairOfDefinition.A₀)) ∈ nhds (0 : JetA K) :=
    P.toPairOfDefinition.hasBasis_nhds_zero.mem_of_mem trivial
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hIj
  have hcoeff : ∀ f : StrictLoc.PA K n, ‖f‖ < δ →
      ∀ l : Fin n →₀ ℕ, ∃ b : P.toPairOfDefinition.A₀,
      b ∈ P.toPairOfDefinition.I ^ j ∧ (b : JetA K) =
        MvPowerSeries.coeff l
          ((UnitDiscExample.restrictedGaussEquiv (JetA K) n) f).val := by
    intro f hf l
    have hmem : MvPowerSeries.coeff l f.1 ∈
        Subtype.val '' ((P.toPairOfDefinition.I ^ j :
          Ideal P.toPairOfDefinition.A₀) : Set P.toPairOfDefinition.A₀) := by
      refine hball ?_
      rw [Metric.mem_ball, dist_zero_right]
      exact lt_of_le_of_lt (norm_coeff_le_gauss f l) hf
    obtain ⟨b, hbI, hbeq⟩ := hmem
    exact ⟨b, hbI, hbeq⟩
  refine Filter.eventually_iff_exists_mem.mpr
    ⟨Metric.ball 0 δ, Metric.ball_mem_nhds _ hδ, fun f hf => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hf
  refine mvTateAlgNhd_of_coeff_mem_principal n P.toPairOfDefinition j
    P.π P.I_eq_span P.π_isUnit ?_ (hcoeff f hf)
  intro l
  obtain ⟨b, -, hbeq⟩ := hcoeff f hf l
  show MvPowerSeries.coeff l
    ((UnitDiscExample.restrictedGaussEquiv (JetA K) n) f).val ∈
      P.toPairOfDefinition.A₀
  rw [← hbeq]
  exact b.2

/-- The inverse identification from the canonical Tate-algebra topology to the Gauss
topology is continuous. -/
theorem tateToGauss_continuous :
    @Continuous ↥(restrictedMvPowerSeriesSubring n (JetA K)) (StrictLoc.PA K n)
      (mvTateAlgebraTopology' (A := JetA K) n) _
      ⇑(UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm := by
  let _i := mvTateAlgebraTopology' (A := JetA K) n
  have := mvTateAlgebraTopology'_isTopologicalRing (A := JetA K) n
  set P := IsTateRing.principalPair (JetA K) with hPdef
  refine continuous_of_continuousAt_zero
    (UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm.toRingHom.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  rw [Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  have hballA : Metric.ball (0 : JetA K) (ε / 2) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (by positivity)
  obtain ⟨j, -, hjsub⟩ :=
    (P.toPairOfDefinition.hasBasis_nhds_zero).mem_iff.mp hballA
  have hsrc : (mvTateAlgNhd n P.toPairOfDefinition j :
      Set ↥(restrictedMvPowerSeriesSubring n (JetA K))) ∈
      @nhds _ (mvTateAlgebraTopology' (A := JetA K) n) 0 :=
    (mvTateAlgBasis' (A := JetA K) n).hasBasis_nhds_zero.mem_of_mem trivial
  refine Filter.eventually_iff_exists_mem.mpr ⟨_, hsrc, fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hcoeff : ∀ l : Fin n →₀ ℕ,
      ‖MvPowerSeries.coeff l
        ((UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm y).1‖ ≤ ε / 2 := by
    intro l
    obtain ⟨b, hbI, hbeq⟩ := mvTateAlgNhd_coeff_mem n P.toPairOfDefinition j hy l
    have hmem : (b : JetA K) ∈ Metric.ball (0 : JetA K) (ε / 2) :=
      hjsub ⟨b, hbI, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have hval : MvPowerSeries.coeff l
        ((UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm y).1 =
        (b : JetA K) := by
      rw [hbeq]
      rfl
    rw [hval]
    exact hmem.le
  calc ‖(UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm y‖
      = MvPowerSeries.gaussNorm (norm : JetA K → ℝ) (fun _ : Fin n => (1 : ℝ))
        ((UnitDiscExample.restrictedGaussEquiv (JetA K) n).symm y).1 :=
        MvRestricted.norm_eq _ _
    _ ≤ ε / 2 := by
        rw [MvPowerSeries.gaussNorm]
        refine Real.iSup_le (fun l => ?_) (by positivity)
        rw [finsupp_prod_one, mul_one]
        exact hcoeff l
    _ < ε := by linarith

/-! ### Sheafiness of the Gauss model -/

/-- The canonical valid ring of integral elements of the extended Gauss ring. -/
def extJetPlus : RingOfIntegralElements (StrictLoc.PA K n) :=
  ⟨((StrictLoc.PA K n)⁺ : Subring (StrictLoc.PA K n)), inferInstance⟩

/-- Pair-level sheafiness of the extended Gauss ring. -/
theorem ext_isSheafyFor (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyFor (StrictLoc.PA K n) (extJetPlus K n) := by
  classical
  let _i := (extJetPlus K n).toPlusSubring
  have : IsRingOfIntegralElements
      (((StrictLoc.PA K n)⁺ : Subring (StrictLoc.PA K n))) :=
    (extJetPlus K n).2
  have : HasLocLiftPowerBounded (StrictLoc.PA K n) := hasLocLiftPowerBounded_faithful
  have : IsSheafy (StrictLoc.PA K n) := isSheafy_extJetA K ϖ hK₀ n
  show IsLimitSheaf (StrictLoc.PA K n)
  exact isLimitSheaf_of_isSheafy

/-- Sheafiness of the extended Gauss ring for every valid ring of integral elements. -/
theorem ext_isSheafyComplete (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    IsSheafyComplete (StrictLoc.PA K n) :=
  (isSheafyFor_iff_isSheafyComplete (extJetPlus K n)).mp
    (ext_isSheafyFor K n ϖ hK₀)

end FiniteJetOver
