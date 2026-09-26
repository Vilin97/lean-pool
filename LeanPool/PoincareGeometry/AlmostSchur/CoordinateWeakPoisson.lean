/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.AlmostSchur.CoordinateForcing
public import LeanPool.PoincareGeometry.AlmostSchur.EnergyLocalVariational

/-! # Local first-order data for the actual weak Poisson solution

The Euclidean predicate below records precisely the L² data and C¹ test
identities supplied to an interior regularity theorem. Its realization is
proved for the actual completed solution, not assumed as an analytic bridge.
-/

@[expose] public noncomputable section
open Bundle Set MeasureTheory
open scoped Manifold ContDiff Topology BigOperators

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Local weak first-order Poisson data on a compact coordinate neighborhood.
No regularity conclusion is built into this predicate. -/
structure LocalWeakPoissonData (b : OrthonormalBasis ι ℝ E) (K : Set E)
    (A : E → Matrix ι ι ℝ) (U F : E → ℝ) (D : ι → E → ℝ) : Prop where
  solution_memLp : MemLp U 2 ((volume : Measure E).restrict K)
  forcing_memLp : MemLp F 2 ((volume : Measure E).restrict K)
  derivative_memLp : ∀ i, MemLp (D i) 2 ((volume : Measure E).restrict K)
  weakDerivative : ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
    tsupport φ ⊆ K → ∀ i,
      (∫ z in K, U z * fderiv ℝ φ z (b i)) = -(∫ z in K, D i z * φ z)
  variational : ∀ (φ : E → ℝ), ContDiff ℝ 1 φ → HasCompactSupport φ →
    tsupport φ ⊆ K →
      (∫ z in K, ∑ i, ∑ j, A z i j * D i z * fderiv ℝ φ z (b j)) =
        -(∫ z in K, F z * φ z)

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [MeasurableSpace M] [BorelSpace M] [Nonempty M] [LindelofSpace M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M]

local instance coordinateWeakPoisson_contMDiffRiemannian : IsContMDiffRiemannianBundle I (↑(0 : ℕ)) E
    (TangentSpace I : M → Type _) :=
  IsContMDiffRiemannianBundle.of_le (n := 1) (by norm_num)
local instance coordinateWeakPoisson_continuousRiemannian : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
  continuousRiemannianBundle_of_contMDiff (I := I)

/-- All local L² and weak PDE hypotheses are satisfied by the constructed solution. -/
theorem weakPoissonSolution_local_data (b : OrthonormalBasis ι ℝ E) (c : M)
    {K : Set E} (hK : IsCompact K) (hKt : K ⊆ (extChartAt I c).target)
    (h : Lp ℝ 2 (riemannianVolume (I := I) (M := M)))
    (hh : (∫ x, h x ∂riemannianVolume (I := I)) = 0) :
    LocalWeakPoissonData b K (coordinateEllipticMatrix (I := I) b.toBasis c)
      (fun z => energyCompletionToL2 (weakPoissonSolution h) ((extChartAt I c).symm z))
      (fun z => matrixDensity (coordinateMetric (I := I) b.toBasis c z) *
        h ((extChartAt I c).symm z))
      (fun i z => energyChartDerivative c hK hKt (b i) (weakPoissonSolution h) z) where
  solution_memLp := memLp_chart_comp_on_compact c hK hKt _
  forcing_memLp := memLp_density_chart_comp_on_compact b.toBasis c hK hKt h
  derivative_memLp i := Lp.memLp _
  weakDerivative φ hφ hc hφK i :=
    setIntegral_energyChartDerivative c hK hKt (b i) (weakPoissonSolution h) φ hφ hc hφK
  variational φ hφ hc hφK :=
    weakPoissonSolution_coordinate_variational b c hK hKt h hh φ hφ hc hφK

end AlmostSchur
