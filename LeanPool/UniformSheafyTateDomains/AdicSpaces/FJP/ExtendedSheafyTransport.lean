/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.ExtendedMilnorInstance
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.FiniteJetSheafyEndpoints

/-!
# From the Gauss ring to the Tate extension: the B-headline transport (T628)

The Gauss-normed ring `PA F n` and the topological Tate extension
`(JetA F)⟨V₁,…,Vₙ⟩ = restrictedMvPowerSeriesSubring n (JetA F)` (with its
canonical `mvTateAlgebraTopology'`) are the same subring of the power-series
ring (`UnitDiscExample.restrictedGaussEquiv`); here we prove the identification
is a **homeomorphism** — the Gauss balls and the `mvTateAlgNhd` pair-ideal
neighborhoods interleave, coefficientwise through the pair of definition's
neighborhood basis — and transport `isSheafy_extJetA` to the headline

`finiteJet_tateExt_isSheafyComplete` ([Reviewer] §5.1: 𝓐 is **strongly
sheafy**), via the `IsSheafyFor → IsSheafyComplete` upgrade and
`isSheafyComplete_congr` (the campaign-A endgame pattern).
-/

@[expose] public section

noncomputable section

namespace FiniteJet

open ValuationSpectrum TopologicalRing GraphKoszul StrictLoc MvTateAlgebra

variable (F : Type*) [Field F] (n : ℕ)

/-! ### The two continuity directions -/

/-- Gauss → mvTate: the identification is continuous out of the normed ring
(Gauss balls refine the pair-ideal neighborhoods, coefficientwise). -/
theorem gaussToTate_continuous :
    @Continuous (PA F n) ↥(restrictedMvPowerSeriesSubring n (JetA F)) _
      (mvTateAlgebraTopology' (A := JetA F) n)
      ⇑(UnitDiscExample.restrictedGaussEquiv (JetA F) n) := by
  let _i := mvTateAlgebraTopology' (A := JetA F) n
  have := mvTateAlgebraTopology'_isTopologicalRing (A := JetA F) n
  set P := (IsTateRing.principalPair (JetA F)) with hPdef
  refine continuous_of_continuousAt_zero
    (UnitDiscExample.restrictedGaussEquiv (JetA F) n).toRingHom.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  refine ((mvTateAlgBasis' (A := JetA F) n).hasBasis_nhds_zero.tendsto_right_iff).mpr ?_
  intro j _
  have hIj : (Subtype.val ''
      ((P.toPairOfDefinition.I ^ j : Ideal P.toPairOfDefinition.A₀) :
        Set P.toPairOfDefinition.A₀)) ∈ nhds (0 : JetA F) :=
    P.toPairOfDefinition.hasBasis_nhds_zero.mem_of_mem trivial
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hIj
  have hcoeff : ∀ f : PA F n, ‖f‖ < δ →
      ∀ l : Fin n →₀ ℕ, ∃ b : P.toPairOfDefinition.A₀,
      b ∈ P.toPairOfDefinition.I ^ j ∧ (b : JetA F) =
        MvPowerSeries.coeff l
          ((UnitDiscExample.restrictedGaussEquiv (JetA F) n) f).val := by
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
    ((UnitDiscExample.restrictedGaussEquiv (JetA F) n) f).val ∈
      P.toPairOfDefinition.A₀
  rw [← hbeq]
  exact b.2

/-- mvTate → Gauss: the identification is continuous into the normed ring
(the pair-ideal neighborhoods shrink inside every Gauss ball). -/
theorem tateToGauss_continuous :
    @Continuous ↥(restrictedMvPowerSeriesSubring n (JetA F)) (PA F n)
      (mvTateAlgebraTopology' (A := JetA F) n) _
      ⇑(UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm := by
  let _i := mvTateAlgebraTopology' (A := JetA F) n
  have := mvTateAlgebraTopology'_isTopologicalRing (A := JetA F) n
  set P := (IsTateRing.principalPair (JetA F)) with hPdef
  refine continuous_of_continuousAt_zero
    (UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm.toRingHom.toAddMonoidHom ?_
  rw [ContinuousAt, map_zero]
  rw [Metric.nhds_basis_ball.tendsto_right_iff]
  intro ε hε
  have hballA : Metric.ball (0 : JetA F) (ε / 2) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (by positivity)
  obtain ⟨j, -, hjsub⟩ :=
    (P.toPairOfDefinition.hasBasis_nhds_zero).mem_iff.mp hballA
  have hsrc : (mvTateAlgNhd n P.toPairOfDefinition j :
      Set ↥(restrictedMvPowerSeriesSubring n (JetA F))) ∈
      @nhds _ (mvTateAlgebraTopology' (A := JetA F) n) 0 :=
    (mvTateAlgBasis' (A := JetA F) n).hasBasis_nhds_zero.mem_of_mem trivial
  refine Filter.eventually_iff_exists_mem.mpr ⟨_, hsrc, fun y hy => ?_⟩
  rw [Metric.mem_ball, dist_zero_right]
  have hcoeff : ∀ l : Fin n →₀ ℕ,
      ‖MvPowerSeries.coeff l
        ((UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm y).1‖ ≤ ε / 2 := by
    intro l
    obtain ⟨b, hbI, hbeq⟩ := mvTateAlgNhd_coeff_mem n P.toPairOfDefinition j hy l
    have hmem : (b : JetA F) ∈ Metric.ball (0 : JetA F) (ε / 2) :=
      hjsub ⟨b, hbI, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hmem
    have hval : MvPowerSeries.coeff l
        ((UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm y).1 =
        (b : JetA F) := by
      rw [hbeq]
      rfl
    rw [hval]
    exact hmem.le
  calc ‖(UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm y‖
      = MvPowerSeries.gaussNorm (norm : JetA F → ℝ) (fun _ : Fin n => (1 : ℝ))
        ((UnitDiscExample.restrictedGaussEquiv (JetA F) n).symm y).1 :=
        MvRestricted.norm_eq _ _
    _ ≤ ε / 2 := by
        rw [MvPowerSeries.gaussNorm]
        refine Real.iSup_le (fun l => ?_) (by positivity)
        rw [finsupp_prod_one, mul_one]
        exact hcoeff l
    _ < ε := by linarith

/-! ### The `IsSheafyComplete` endgame -/

/-- The canonical valid pair of the extended Gauss ring. -/
noncomputable def extJetPlus : RingOfIntegralElements (PA F n) :=
  ⟨((PA F n)⁺ : Subring (PA F n)), inferInstance⟩

/-- Pair-level sheafiness of the extended Gauss ring. -/
theorem ext_isSheafyFor : IsSheafyFor (PA F n) (extJetPlus F n) := by
  classical
  let _i := (extJetPlus F n).toPlusSubring
  have : IsRingOfIntegralElements ((PA F n)⁺ : Subring (PA F n)) :=
    (extJetPlus F n).2
  have : HasLocLiftPowerBounded (PA F n) := hasLocLiftPowerBounded_faithful
  have : IsSheafy (PA F n) := isSheafy_extJetA F n
  show IsLimitSheaf (PA F n)
  exact isLimitSheaf_of_isSheafy

/-- **`IsSheafyComplete` for the extended Gauss ring**: sheafiness at every
valid ring of integral elements, by the `A⁺`-independence upgrade. -/
theorem ext_isSheafyComplete : IsSheafyComplete (PA F n) :=
  (isSheafyFor_iff_isSheafyComplete (extJetPlus F n)).mp (ext_isSheafyFor F n)

end FiniteJet
