/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.ChartCutoff
public import LeanPool.PoincareGeometry.AlmostSchur.L2Multiplier

/-! # Actual compact-cutoff graph approximation of energy-completion elements

The approximation is proved from the existing C¹ energy-core density and
bounded actual coordinate maps. No weak-H¹ density theorem is assumed.
-/

@[expose] public noncomputable section
open Set Bundle MeasureTheory Filter
open scoped Manifold ContDiff Topology
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Graphs of genuine compactly supported C¹ tests, recording designated
directional derivatives as L² classes. -/
def c1SupportedTestGraph {ι : Type*} (b : ι → E) (U : Set E) :
    Set (Lp ℝ 2 (volume : Measure E) × (ι → Lp ℝ 2 (volume : Measure E))) :=
  {p | ∃ φ : E → ℝ, ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U ∧
    p.1 =ᵐ[volume] φ ∧ ∀ i, p.2 i =ᵐ[volume] (fun z => fderiv ℝ φ z (b i))}

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance energyCutoffGraphContinuousRiemannianBundle :
    IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- A compactly cut-off actual coordinate realization and its product-rule
derivatives belong to the closure of genuine supported C¹ test graphs.
For finite `ι`, this is simultaneous strong L² approximation of all recorded
derivatives. The operators and their representatives are constructed here. -/
theorem exists_energyCutoffGraph {ι : Type*} (b : ι → E)
    (c : M) {K : Set E} (hK : IsCompact K)
    (hKt : K ⊆ (extChartAt I c).target)
    (χ : E → ℝ) (hχ : ContDiff ℝ 1 χ) (hcχ : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ K) :
    ∃ P : EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (volume : Measure E),
    ∃ Q : ι → EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (volume : Measure E),
      (∀ u, P u =ᵐ[volume] chartCutoff (I := I) c χ (energyCompletionToL2 u)) ∧
      (∀ u i, Q i u =ᵐ[volume] (fun z =>
        fderiv ℝ χ z (b i) * energyCompletionToL2 u ((extChartAt I c).symm z) +
          χ z * energyChartDerivative c hK hKt (b i) u z)) ∧
      ∀ u, (P u, fun i => Q i u) ∈ closure (c1SupportedTestGraph b (tsupport χ)) := by
  classical
  let μ := (volume : Measure E).restrict K
  obtain ⟨_, _, T, _, hT⟩ := exists_chartL2Pullback (I := I) c hK hKt
  let R := T.comp (energyCompletionToL2 (I := I) (M := M))
  obtain ⟨S, hS⟩ := exists_cutoffL2Extension (μ := (volume : Measure E))
    χ hχ.continuous hcχ hK.measurableSet hχK
  have hdS (i : ι) := exists_cutoffL2Extension (μ := (volume : Measure E))
    (fun z => fderiv ℝ χ z (b i))
    ((hχ.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hcχ.fderiv_apply ℝ (b i)) hK.measurableSet
    ((tsupport_fderiv_apply_subset ℝ (b i)).trans hχK)
  choose Sd hSd using hdS
  let P := S.comp R
  let Q : ι → EnergyCompletion (I := I) (M := M) →L[ℝ] Lp ℝ 2 (volume : Measure E) :=
    fun i => (Sd i).comp R + S.comp (energyChartDerivative c hK hKt (b i))
  have hP (u) : P u =ᵐ[volume] chartCutoff (I := I) c χ (energyCompletionToL2 u) :=
    hS (R u) _ (hT _)
  have hQ (u) (i) : Q i u =ᵐ[volume] (fun z =>
      fderiv ℝ χ z (b i) * energyCompletionToL2 u ((extChartAt I c).symm z) +
        χ z * energyChartDerivative c hK hKt (b i) u z) := by
    filter_upwards [hSd i (R u) _ (hT _),
      hS (energyChartDerivative c hK hKt (b i) u) _ Filter.EventuallyEq.rfl,
      Lp.coeFn_add ((Sd i) (R u)) (S (energyChartDerivative c hK hKt (b i) u))]
      with z hz hd ha
    exact ha.trans (by rw [Pi.add_apply, hz, hd]; rfl)
  refine ⟨P, Q, hP, hQ, ?_⟩
  intro u
  refine (denseRange_energyToCompletion (I := I) (M := M)).induction_on
    (p := fun w => (P w, fun i => Q i w) ∈ closure (c1SupportedTestGraph b (tsupport χ)))
    u ?_ ?_
  · exact isClosed_closure.preimage
      (P.continuous.prodMk (continuous_pi fun i => (Q i).continuous))
  · intro f
    apply subset_closure
    refine ⟨chartCutoff (I := I) c χ f.val,
      contDiff_chartCutoff c hχ (hχK.trans hKt) f.property.1,
      hasCompactSupport_chartCutoff c hcχ f.val,
      tsupport_chartCutoff_subset c χ f.val, ?_, ?_⟩
    · exact hS (R (energyToCompletion f)) _
        ((hT _).trans (ae_eq_comp_chart_symm
          (energyCompletionToL2_core_ae_eq f) c hK hKt))
    · intro i
      have hRc : R (energyToCompletion f) =ᵐ[μ] f.val ∘ (extChartAt I c).symm :=
        (hT _).trans (ae_eq_comp_chart_symm
          (energyCompletionToL2_core_ae_eq f) c hK hKt)
      have hDc : energyChartDerivative c hK hKt (b i) (energyToCompletion f) =ᵐ[μ]
          (fun z => fderiv ℝ (f.val ∘ (extChartAt I c).symm) z (b i)) := by
        rw [energyChartDerivative_energyToCompletion]
        exact energyChartDerivativeLinear_ae_eq c hK hKt (b i) f
      filter_upwards [hSd i (R (energyToCompletion f)) _ hRc,
        hS (energyChartDerivative c hK hKt (b i) (energyToCompletion f)) _ hDc,
        Lp.coeFn_add ((Sd i) (R (energyToCompletion f)))
          (S (energyChartDerivative c hK hKt (b i) (energyToCompletion f)))]
        with z hz hd ha
      change Q i (energyToCompletion f) z = _
      exact ha.trans (by
        rw [Pi.add_apply, hz, hd]
        exact (fderiv_chartCutoff_global c hχ (hχK.trans hKt) f.property.1 z (b i)).symm)

end AlmostSchur
