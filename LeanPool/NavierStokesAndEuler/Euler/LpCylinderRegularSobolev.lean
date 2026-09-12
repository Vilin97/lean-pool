/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularForward
public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelSobolevGevrey
import LeanPool.NavierStokesAndEuler.Euler.LpCylinderRegularCoefficient
public import LeanPool.NavierStokesAndEuler.Euler.ParameterSobolevBlocks
public import LeanPool.NavierStokesAndEuler.Euler.ParameterWordGevrey

/-!
# Localized H3 gives actual mixed cylinder L² fixed-Hq forward estimates

The coefficient is the literal bounded matrix field, the homogeneous and
forced solutions are constructed, and the final derivative block is the
actual mixed R³×R translation orbit of the actual solution. A compact support
inside an open subset of the H3 ball supplies only a qualitative neighborhood.
The radius and polynomial constants do not depend on that support margin.
-/

section

/-! Local equality preserves genuine fixed-Sobolev external derivative blocks. -/

section

/-! Actual ordered derivative sums depend only on the local function germ. -/

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open scoped Topology

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

omit [Fintype ι] in
/-- Equality on a genuine neighborhood identifies every actual ordered word derivative. -/
theorem wordDerivative_eq_of_eventuallyEq (directions : ι → P) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) {n : ℕ} (w : Fin n → ι) :
    wordDerivative directions f w x = wordDerivative directions g w x := by
  unfold wordDerivative
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]

/-- The identical external-word sum transfers across local equality, with no radius factor. -/
theorem wordSum_eq_of_eventuallyEq (directions : ι → P) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : wordSum directions f n x = wordSum directions g n x := by
  unfold wordSum
  apply Finset.sum_congr rfl
  intro w _
  rw [wordDerivative_eq_of_eventuallyEq directions h w]

end EulerParameterWordGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerParameterWordGevrey

open scoped Topology

variable {P E ι : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]

/-- A fixed finite Sobolev sum depends only on the actual function germ. -/
theorem baseSize_eq_of_eventuallyEq (directions : ι → P) (q : ℕ) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) : baseSize directions q f x = baseSize directions q g x := by
  unfold baseSize
  exact Finset.sum_congr rfl (fun k _ => wordSum_eq_of_eventuallyEq directions h k)

/-- All inner and external word derivatives agree under equality on a neighborhood. -/
theorem block_eq_of_eventuallyEq (directions : ι → P) (q : ℕ) {f g : P → E} {x : P}
    (h : f =ᶠ[𝓝 x] g) (n : ℕ) : block directions q f n x = block directions q g n x := by
  unfold block
  apply Finset.sum_congr rfl
  intro w _
  apply baseSize_eq_of_eventuallyEq directions q
  filter_upwards [h.iteratedFDeriv ℝ n] with y hy
  exact congrArg (fun D : P [×n]→L[ℝ] E => D (fun j => directions (w j))) hy

end EulerParameterWordGevrey

end
end

end

@[expose] public section

noncomputable section

namespace EulerLpCylinderRegularForward

open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerLpSupportedSubspace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderCoefficients
  EulerLinearDuhamel EulerLinearFundamentalExistence EulerMeanCoefficients
  EulerGevrey EulerParameterWordGevrey
open scoped ContDiff Topology BoundedContinuousFunction

variable (period : ℝ) [Fact (0 < period)]

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V] [Fintype ι]
  (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (T : ℝ) (hT : 0 ≤ T) (Ω : Set Space) (hΩ : MeasurableSet Ω)
  (B : C(Icc (0 : ℝ) T, Space →ᵇ V →L[ℝ] V))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) (hg₀ : g ⟨0, le_rfl, hT⟩ = 1)

/-- Cache the standard `NormedRing (V →L[ℝ] V)` instance to shorten typeclass synthesis. -/
local instance instLpCylinderRegularSobolev1 : NormedRing (V →L[ℝ] V) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ V →L[ℝ] V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularSobolev2 : NormedRing (Space →ᵇ V →L[ℝ] V) := inferInstance

/-- Cache the standard `NormedAddCommGroup (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularSobolev3 : NormedAddCommGroup (CylinderL2 period V) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (CylinderL2 period V)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularSobolev4 : NormedSpace ℝ (CylinderL2 period V) := inferInstance
/-- Cache the standard `NormedAddCommGroup (Supported period V Ω hΩ)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularSobolev5 : NormedAddCommGroup (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ (Supported period V Ω hΩ)` instance to shorten typeclass
synthesis. -/
local instance instLpCylinderRegularSobolev6 : NormedSpace ℝ (Supported period V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularSobolev7 : NormedAddCommGroup C(Icc (0 : ℝ) T,CylinderL2 period
    V) := inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V)` instance to shorten
typeclass synthesis. -/
local instance instLpCylinderRegularSobolev8 : NormedSpace ℝ C(Icc (0 : ℝ) T,CylinderL2 period V)
    := inferInstance
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularSobolev9 : NormedAddCommGroup C(Icc (0 : ℝ) T,Supported period
    V Ω hΩ) :=
    inferInstance
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω hΩ)` instance to
shorten typeclass synthesis. -/
local instance instLpCylinderRegularSobolev10 : NormedSpace ℝ C(Icc (0 : ℝ) T,Supported period V Ω
    hΩ) := inferInstance

include hd hg₀ hΩ hB

/-- The constructed fixed-space family has a true fixed-Sobolev word bound
at the base parameter, with the same radius as the data. -/
theorem solutionFamily_block_bound
    (f : C(Icc (0 : ℝ) T, CylinderL2 period V)) (a₀ : CylinderL2 period V)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a f))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a a₀))
    (C A D CB Rc R : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hCB : 0 ≤ CB) (hRc : 0 ≤ Rc)
    (hR : 2*forwardSobolevCost ι q T C A D CB Rc*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hBb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) x‖ ≤ CB*majorant Rc 0 n)
    (hprop : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x ∈ Ω,
      ‖((fundamentalPath T hT B).forward t x).comp
        ((fundamentalPath T hT B).backward s x)‖ ≤ C*g t/g s)
    (d : ℕ)
    (hforce : ∀ n, block directions q (fun a : LiftTangent => pathTranslate period a f) n 0 ≤
      D*majorant R d n)
    (hinitial : ∀ n, block directions q (fun a : LiftTangent => translate period a a₀) n 0 ≤
        A*majorant R d n)
    (n : ℕ) :
    block directions q (solutionFamily period T hT Ω hΩ B g hg f a₀) n 0 ≤ majorant R (d+1) n := by
  have hBc : ContDiff ℝ ∞ (coefficientFamily period T Ω hΩ B) :=
    mixedCoefficient_contDiff period Ω hΩ T B hB
  have hBbound (j : ℕ) (a : LiftTangent) :
      ‖iteratedFDeriv ℝ j (coefficientFamily period T Ω hΩ B) a‖ ≤ CB*majorant Rc 0 j :=
    mixedCoefficient_bound period Ω hΩ T B hB j (CB*majorant Rc 0 j) (hBb j) a
  exact weightedSolution_block_gevrey_at directions hd q T hT (coefficientFamily period T Ω hΩ B)
    (evolutionFamily period T hT Ω hΩ B) g hg (translatedForcing period Ω hΩ f) (translatedData
        period Ω hΩ a₀)
    hBc (translatedForcing_contDiff period Ω hΩ f hf) (translatedData_contDiff period Ω hΩ a₀ ha₀)
    hg₀ C A D CB Rc R hC hA hD hCB hRc hR hBbound 0
    (evolutionFamily_propagator_zero period T hT Ω hΩ B g hg C hC hprop) d
    (fun j => (translatedForcing_block_le period Ω hΩ directions q f hf j 0).trans (hforce j))
    (fun j => (translatedData_block_le period Ω hΩ directions q a₀ ha₀ j 0).trans (hinitial j)) n

/-- The actual cylinder-L² solution has the source's fixed-Hq
external-word bound. H3 is used only on its stated ball of radius one half. -/
theorem source_forward_block_bound
    (K : Set Space) (hK : MeasurableSet K) (hKc : IsCompact K) (hΩo : IsOpen Ω) (hsub : K ⊆ Ω)
    (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
    (f : C(Icc (0 : ℝ) T, Supported period V K hK))
    (a₀ : Supported period V K hK)
    (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate period a (includePath period K hK f)))
    (ha₀ : ContDiff ℝ ∞ (fun a : LiftTangent => translate period a (a₀ : CylinderL2 period V)))
    (C A D CB Rc R : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D) (hCB : 0 ≤ CB) (hRc : 0 ≤ Rc)
    (hR : 2*forwardSobolevCost ι q T C A D CB Rc*(sobolevCoefficientRadius ι Rc+1) ≤ R)
    (hBb : ∀ n x, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) x‖ ≤ CB*majorant Rc 0 n)
    (hH3 : ∀ t s : Icc (0 : ℝ) T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
      ‖((fundamentalPath T hT B).forward t x).comp
        ((fundamentalPath T hT B).backward s x)‖ ≤ C*g t/g s)
    (d : ℕ)
    (hforce : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate period a (includePath period K hK f)) n 0 ≤ D*majorant
          R d n)
    (hinitial : ∀ n, block directions q (fun a : LiftTangent => translate period a (a₀ : CylinderL2
        period V)) n 0 ≤
      A*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent => pathTranslate period a (includePath period K hK
      ((constructedEvolution period K hK T hT B).weightedSolution g hg f a₀))) n 0 ≤
      majorant R (d+1) n := by
  let u := solutionFamily period T hT Ω hΩ B g hg (includePath period K hK f) (a₀ : CylinderL2
      period V)
  have hu : ContDiff ℝ ∞ u := solutionFamily_contDiff period T hT Ω hΩ B hB g hg (includePath
      period K hK f)
    (a₀ : CylinderL2 period V) hf ha₀
  have he := solutionFamily_translation_eventually period T hT Ω hΩ B K hK hKc hΩo hsub g hg f a₀
  rw [← block_eq_of_eventuallyEq directions q he n]
  exact (includePath_block_le period Ω hΩ directions q u hu n 0).trans
    (solutionFamily_block_bound period directions hd q T hT Ω hΩ B hB g hg hg₀ (includePath period
        K hK f)
      (a₀ : CylinderL2 period V) hf ha₀ C A D CB Rc R hC hA hD hCB hRc hR hBb
      (fun t s hst x hx => hH3 t s hst x (hΩball x hx)) d hforce hinitial n)

end EulerLpCylinderRegularForward
