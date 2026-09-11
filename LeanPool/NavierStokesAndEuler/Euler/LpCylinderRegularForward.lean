/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderCoefficients
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelGevrey
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderOrbit
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularCoefficient
import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelNaturality

/-!
# The actual fixed-space family for a genuinely regular bounded forward coefficient

The family is constructed from translated coefficient fields and projected
translations of the original data. All homogeneous evolutions are obtained
from the proved Picard construction. On the support-margin neighborhood it
is exactly the mixed cylinder translation orbit of the original solution.
Only the zero-parameter propagator uses the quantitative H3 assumption.
-/

section

/-!
# The cylinder forward solution has its actual mixed translation orbit

The coefficient intertwining identity and uniqueness identify the translated
initial-value problem with the genuine mixed translation of the original
solution. Compact support gives an equality on a neighborhood of the zero
translation. No norm estimate depends on the size of that neighborhood.
-/

section

/-! Genuine scalar-profile normalization commutes with bounded linear intertwiners. -/

@[expose] public section

noncomputable section

namespace EulerLinearDuhamel.Evolution

open Set ContinuousLinearMap EulerContinuousTimeWeight EulerContinuousTimeIntegral

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {T : ℝ} {hT : 0 ≤ T}
  {B : C(Icc (0 : ℝ) T, E →L[ℝ] E)}
  {D : C(Icc (0 : ℝ) T, F →L[ℝ] F)}
  (U : Evolution T hT B) (V : Evolution T hT D)
  (L : E →L[ℝ] F) (hL : ∀ t u, D t (L u) = L (B t u))

include hL

/-- Exact naturality of the actual normalized Duhamel solution. -/
theorem weightedSolution_map (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, E)) (a₀ : E) :
    V.weightedSolution g hg (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) (L a₀) =
      L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (U.weightedSolution g hg f a₀) := by
  have hw : weight g (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) f) =
      L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (weight g f) := by
    apply ContinuousMap.ext
    intro t
    exact (map_smul L (g t) (f t)).symm
  have hn (p : C(Icc (0 : ℝ) T,E)) :
      normalize g hg (L.compLeftContinuous ℝ (Icc (0 : ℝ) T) p) =
        L.compLeftContinuous ℝ (Icc (0 : ℝ) T) (normalize g hg p) := by
    apply ContinuousMap.ext
    intro t
    exact (map_smul L ((g t)⁻¹) (p t)).symm
  unfold weightedSolution
  rw [hw, U.solution_map V L hL, hn]

end EulerLinearDuhamel.Evolution

end
end

end

@[expose] public section

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
  (B : C(Icc (0 : ℝ) T, Field (α := Space) (V := V)))
  (U : Evolution (E := Supported period V K hK) T hT (liftedOperatorPath period K hK T B))

/-- Cache the standard `NormedAddCommGroup (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderSolutionTranslation1 : NormedAddCommGroup (CylinderL2 period V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderSolutionTranslation2 : NormedSpace ℝ (CylinderL2 period V) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V K hK)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation3 : NormedAddCommGroup (Supported period V K hK) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V K hK)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderSolutionTranslation4 : NormedSpace ℝ (Supported period V K hK) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V Ω hΩ)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation5 : NormedAddCommGroup (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V Ω hΩ)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderSolutionTranslation6 : NormedSpace ℝ (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation7 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2
    period V) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation8 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period
    V) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V K hK)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation9 : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported
    period V K hK) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V K hK)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation10 : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period
    V K hK) := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation11 : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported
    period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderSolutionTranslation12 : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period
    V Ω hΩ) := inferInstance

/-- The normalized supported solution has the actual normalized translation orbit. -/
theorem weighted_solution_translation (a : LiftTangent) (ha : shiftedSet a.1 K ⊆ Ω)
    (W : Evolution (E := Supported period V Ω hΩ) T hT (liftedOperatorPath period Ω hΩ T
      (EulerMeanCoefficients.translateCoefficientPath B a.1)))
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, Supported period V K hK))
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerLpCylinderRegularForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpSupportedMultiplier
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerLpCylinderSolutionTranslation
  EulerLpCylinderCoefficients EulerLinearDuhamel EulerLinearFundamentalExistence
  EulerMeanCoefficients
open scoped ContDiff Topology BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  (T : ℝ) (hT : 0 ≤ T) (Ω : Set Space) (hΩ : MeasurableSet Ω)
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))

/-- Cache the standard `NormedRing (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularForward1 : NormedRing (V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularForward2 : NormedRing (Space →ᵇ V →L[ℝ] V) := inferInstance

/-- Cache the standard `NormedAddCommGroup (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularForward3 : NormedAddCommGroup (CylinderL2 period V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularForward4 : NormedSpace ℝ (CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V Ω hΩ)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularForward5 : NormedAddCommGroup (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V Ω hΩ)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularForward6 : NormedSpace ℝ (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularForward7 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period
    V) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularForward8 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularForward9 : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period
    V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularForward10 : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω
    hΩ) := inferInstance

/-- The actual multiplication coefficient on the one fixed supported space. -/
def coefficientFamily (a : LiftTangent) :
    C(Icc (0 : ℝ) T,Supported period V Ω hΩ →L[ℝ] Supported period V Ω hΩ) :=
  liftedOperatorPath period Ω hΩ T (translateCoefficientPath B a.1)

/-- Its homogeneous evolution is constructed, not assumed. -/
def evolutionFamily (a : LiftTangent) : Evolution T hT (coefficientFamily period T Ω hΩ B a) :=
  constructedEvolution period Ω hΩ T hT (translateCoefficientPath B a.1)

/-- The genuine profile-normalized forced solution in this fixed space. -/
def solutionFamily (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, CylinderL2 period V)) (a₀ : CylinderL2 period V) (a : LiftTangent) :
    C(Icc (0 : ℝ) T,Supported period V Ω hΩ) :=
  (evolutionFamily period T hT Ω hΩ B a).weightedSolution g hg
    (translatedForcing period Ω hΩ f a) (translatedData period Ω hΩ a₀ a)

include hB in
/-- Actual coefficient and data regularity give actual smoothness of the solved family. -/
theorem solutionFamily_contDiff (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, CylinderL2 period V)) (a₀ : CylinderL2 period V)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a a₀)) :
    ContDiff ℝ ∞ (solutionFamily period T hT Ω hΩ B g hg f a₀) :=
  weightedSolution_contDiff T hT (coefficientFamily period T Ω hΩ B) (evolutionFamily period T hT Ω
      hΩ B)
    g hg (translatedForcing period Ω hΩ f) (translatedData period Ω hΩ a₀)
    (mixedCoefficient_contDiff period Ω hΩ T B hB)
    (translatedForcing_contDiff period Ω hΩ f hf) (translatedData_contDiff period Ω hΩ a₀ ha₀)

/-- Localized pointwise H3 is precisely the needed base-parameter L² bound. -/
theorem evolutionFamily_propagator_zero
    (g : Icc (0 : ℝ) T → ℝ) (hg : ∀ t, 0 < g t) (C : ℝ) (hC : 0 ≤ C)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ Ω,
      ‖((fundamentalPath T hT B).forward t x).comp
        ((fundamentalPath T hT B).backward s x)‖ ≤ C*g t/g s)
    (t s : Icc (0 : ℝ) T) (hst : s ≤ t) :
    ‖(evolutionFamily period T hT Ω hΩ B 0).propagator t s‖ ≤ C*g t/g s := by
  have hz : translateCoefficientPath B (0 : Space) = B := by
    apply ContinuousMap.ext
    intro r
    exact translated_zero (B r)
  change ‖(constructedEvolution period Ω hΩ T hT (translateCoefficientPath B 0)).propagator t s‖ ≤ _
  rw [hz]
  exact constructedEvolution_propagator_norm period Ω hΩ T hT B g hg C hC hprop t s hst

/-- The locally translated family equals the actual cylinder L² mixed translation orbit
of the actual normalized source solution. -/
theorem solutionFamily_translation_eventually
    (K : Set Space) (hK : MeasurableSet K) (hKc : IsCompact K) (hΩo : IsOpen Ω) (hsub : K ⊆ Ω)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, Supported period V K hK))
    (a₀ : Supported period V K hK) :
    (fun a : LiftTangent => includePath period Ω hΩ
      (solutionFamily period T hT Ω hΩ B g hg (includePath period K hK f) (a₀ : CylinderL2 period
          V) a)) =ᶠ[𝓝 0]
      (fun a => pathTranslate period a (includePath period K hK
        ((constructedEvolution period K hK T hT B).weightedSolution g hg f a₀))) :=
  weighted_solution_translation_eventually period T hT K Ω hK hΩ B
    (constructedEvolution period K hK T hT B) hKc hΩo hsub
    (evolutionFamily period T hT Ω hΩ B) g hg f a₀

include hΩ hB in
/-- The locally constructed family proves genuine smoothness of the entire
mixed translation orbit of the actual solution. -/
theorem source_solution_contDiff
    (K : Set Space) (hK : MeasurableSet K) (hKc : IsCompact K) (hΩo : IsOpen Ω) (hsub : K ⊆ Ω)
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T, Supported period V K hK)) (a₀ : Supported period V K hK)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period K hK f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period V))) :
    ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period K hK
      ((constructedEvolution period K hK T hT B).weightedSolution g hg f a₀))) := by
  apply pathOrbit_contDiff_of_zero
  have hu := solutionFamily_contDiff period T hT Ω hΩ B hB g hg (includePath period K hK f)
    (a₀ : CylinderL2 period V) hf ha₀
  have hi : ContDiff ℝ ∞ (fun a : LiftTangent => includePath period Ω hΩ
      (solutionFamily period T hT Ω hΩ B g hg (includePath period K hK f) (a₀ : CylinderL2 period
          V) a)) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := ∞)
      (E := C(Icc (0 : ℝ) T,Supported period V Ω hΩ))
      (F := C(Icc (0 : ℝ) T,CylinderL2 period V)) (includePath period Ω hΩ)).comp hu
  exact hi.contDiffAt.congr_of_eventuallyEq
    (solutionFamily_translation_eventually period T hT Ω hΩ B K hK hKc hΩo hsub g hg f a₀).symm

end EulerLpCylinderRegularForward
