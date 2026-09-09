/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeightedNaturality

@[expose] public section

/-!
# The cylinder forward solution has its actual mixed translation orbit

The coefficient intertwining identity and uniqueness identify the translated
initial-value problem with the genuine mixed translation of the original
solution. Compact support gives an equality on a neighborhood of the zero
translation. No norm estimate depends on the size of that neighborhood.
-/

noncomputable section

namespace EulerLpCylinderSolutionTranslation

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpSupportedMultiplier EulerLpSupportedTranslation
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderCoefficients EulerLinearDuhamel
  EulerContinuousTimeWeight
open scoped ContDiff Topology BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T)
  (K Ω : Set Space) (hK : MeasurableSet K) (hΩ : MeasurableSet Ω)
  (B : C(Icc (0 : ℝ) T,Field (α := Space) (V := V)))
  (U : Evolution (E := Supported period V K hK) T hT (liftedOperatorPath period K hK T B))

private local instance : NormedAddCommGroup (CylinderL2 period V) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period V) := inferInstance
private local instance : NormedAddCommGroup (Supported period V K hK) := inferInstance
private local instance : NormedSpace ℝ (Supported period V K hK) := inferInstance
private local instance : NormedAddCommGroup (Supported period V Ω hΩ) := inferInstance
private local instance : NormedSpace ℝ (Supported period V Ω hΩ) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V K hK) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V K hK) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V Ω hΩ) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω hΩ) := inferInstance

/-- The normalized supported solution has the actual normalized translation orbit. -/
theorem weighted_solution_translation (a : LiftTangent) (ha : shiftedSet a.1 K ⊆ Ω)
    (W : Evolution (E := Supported period V Ω hΩ) T hT (liftedOperatorPath period Ω hΩ T
      (EulerMeanCoefficients.translateCoefficientPath B a.1)))
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,Supported period V K hK))
    (a₀ : Supported period V K hK) :
    includePath period Ω hΩ (W.weightedSolution g hg
      (translatedForcing period Ω hΩ (includePath period K hK f) a)
      (translatedData period Ω hΩ (a₀ : CylinderL2 period V) a)) =
      pathTranslate period a
        (includePath period K hK (U.weightedSolution g hg f a₀)) := by
  let L : Supported period V K hK →L[ℝ] Supported period V Ω hΩ :=
    (EulerLpCylinderTranslation.intoLarger period a K Ω hK hΩ ha).toContinuousLinearMap
  have hL : ∀ t u, liftedOperatorPath period Ω hΩ T
      (EulerMeanCoefficients.translateCoefficientPath B a.1) t (L u) =
        L (liftedOperatorPath period K hK T B t u) := by
    intro t u
    exact EulerLpCylinderCoefficients.operator_intertwines period K hK Ω hΩ a ha (B t) u
  rw [translatedForcing_eq_intoLarger period Ω hΩ K hK f a ha,
    translatedData_eq_intoLarger period Ω hΩ K hK a₀ a ha]
  have he := Evolution.weightedSolution_map
    (E := Supported period V K hK) (F := Supported period V Ω hΩ)
    U W L hL g hg f a₀
  change includePath period Ω hΩ (W.weightedSolution g hg
    (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) (L a₀)) = _
  rw [he]
  apply ContinuousMap.ext
  intro t
  rfl

/-- Normalization preserves the exact local translation identification. -/
theorem weighted_solution_translation_eventually
    (hKc : IsCompact K) (hΩo : IsOpen Ω) (hsub : K ⊆ Ω)
    (W : ∀ a : LiftTangent, Evolution (E := Supported period V Ω hΩ) T hT (liftedOperatorPath
      period Ω hΩ T
      (EulerMeanCoefficients.translateCoefficientPath B a.1)))
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,Supported period V K hK))
    (a₀ : Supported period V K hK) :
    (fun a : LiftTangent => includePath period Ω hΩ ((W a).weightedSolution g hg
      (translatedForcing period Ω hΩ (includePath period K hK f) a)
      (translatedData period Ω hΩ (a₀ : CylinderL2 period V) a))) =ᶠ[𝓝 0]
      (fun a => pathTranslate period a
        (includePath period K hK (U.weightedSolution g hg f a₀))) := by
  obtain ⟨δ,hδ,hmargin⟩ := compact_support_mixed_margin K Ω hKc hΩo hsub
  filter_upwards [Metric.ball_mem_nhds (0 : LiftTangent) hδ] with a ha
  exact weighted_solution_translation period T hT K Ω hK hΩ B U a
    (hmargin a (by simpa only [Metric.mem_ball, dist_zero_right] using ha)) (W a) g hg f a₀

end EulerLpCylinderSolutionTranslation
