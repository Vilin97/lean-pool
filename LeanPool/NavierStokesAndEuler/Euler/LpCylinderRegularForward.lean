/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderSolutionTranslation
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderOrbit
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelGevrey

@[expose] public section

/-!
# The actual fixed-space family for a genuinely regular bounded forward coefficient

The family is constructed from translated coefficient fields and projected
translations of the original data. All homogeneous evolutions are obtained
from the proved Picard construction. On the support-margin neighborhood it
is exactly the mixed cylinder translation orbit of the original solution.
Only the zero-parameter propagator uses the quantitative H3 assumption.
-/

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
  (B : C(Icc (0 : ℝ) T,Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))

private local instance : NormedRing (V →L[ℝ] V) := inferInstance
private local instance : NormedRing (Space →ᵇ V →L[ℝ] V) := inferInstance

private local instance : NormedAddCommGroup (CylinderL2 period V) := inferInstance
private local instance : NormedSpace ℝ (CylinderL2 period V) := inferInstance
private local instance : NormedAddCommGroup (Supported period V Ω hΩ) := inferInstance
private local instance : NormedSpace ℝ (Supported period V Ω hΩ) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period V) := inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V) := inferInstance
private local instance : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V Ω hΩ) :=
  inferInstance
private local instance : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω hΩ) := inferInstance

/-- The actual multiplication coefficient on the one fixed supported space. -/
def coefficientFamily (a : LiftTangent) :
    C(Icc (0 : ℝ) T,Supported period V Ω hΩ →L[ℝ] Supported period V Ω hΩ) :=
  liftedOperatorPath period Ω hΩ T (translateCoefficientPath B a.1)

/-- Its homogeneous evolution is constructed, not assumed. -/
def evolutionFamily (a : LiftTangent) : Evolution T hT (coefficientFamily period T Ω hΩ B a) :=
  constructedEvolution period Ω hΩ T hT (translateCoefficientPath B a.1)

/-- The genuine profile-normalized forced solution in this fixed space. -/
def solutionFamily (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,CylinderL2 period V)) (a₀ : CylinderL2 period V) (a : LiftTangent) :
    C(Icc (0 : ℝ) T,Supported period V Ω hΩ) :=
  (evolutionFamily period T hT Ω hΩ B a).weightedSolution g hg
    (translatedForcing period Ω hΩ f a) (translatedData period Ω hΩ a₀ a)

include hB in
/-- Actual coefficient and data regularity give actual smoothness of the solved family. -/
theorem solutionFamily_contDiff (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,CylinderL2 period V)) (a₀ : CylinderL2 period V)
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
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,Supported period V K hK))
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
    (g : C(Icc (0 : ℝ) T,ℝ)) (hg : ∀ t, 0 < g t)
    (f : C(Icc (0 : ℝ) T,Supported period V K hK)) (a₀ : Supported period V K hK)
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
