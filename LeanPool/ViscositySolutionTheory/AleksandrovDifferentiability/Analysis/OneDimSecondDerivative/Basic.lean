/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.LocalizedMaximal.Covering
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.QuadraticTrap.Basic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# One-dimensional convex second-derivative measure interfaces

This file records the source-proof interface for the distributional second derivative measure of a
bounded convex function on `(-3,3)`. The actual construction of this measure is still future
work; the statements here isolate exactly the mass and endpoint-control facts needed by the
localized maximal argument.
-/

@[expose] public noncomputable section

open MeasureTheory
open Filter
open scoped MeasureTheory

namespace AleksandrovDifferentiability

/-! ## Stieltjes-measure candidate -/

/-- The Stieltjes function associated to a monotone real function.

For the source proof, `g` will be a one-sided derivative of a one-dimensional convex function.
Mathlib's construction replaces `g` by its right-continuous representative `rightLim g`, which is
the usual convention for the Stieltjes measure assigning mass `G(b) - G(a)` to `(a,b]`. -/
def monotoneStieltjesSecondDerivativeFunction (g : ℝ → ℝ) (hg : Monotone g) :
    StieltjesFunction ℝ :=
  hg.stieltjesFunction

/-- The Stieltjes measure associated to a monotone real function.

This is the concrete candidate for the distributional derivative measure of a monotone one-sided
derivative. -/
def monotoneStieltjesSecondDerivativeMeasure (g : ℝ → ℝ) (hg : Monotone g) : Measure ℝ :=
  (monotoneStieltjesSecondDerivativeFunction g hg).measure

/-- The Stieltjes function associated to the project-local right derivative, assuming that right
derivative has already been extended or localized as a globally monotone function. -/
def rightDerivStieltjesSecondDerivativeFunction (v : ℝ → ℝ)
    (hmono : Monotone (rightDeriv v)) : StieltjesFunction ℝ :=
  monotoneStieltjesSecondDerivativeFunction (rightDeriv v) hmono

/-- The Stieltjes second-derivative measure associated to the project-local right derivative,
under a global monotonicity hypothesis.

The convex source proof will eventually supply this by applying the construction to a monotone
extension of the right derivative from `(-3,3)`. -/
def rightDerivStieltjesSecondDerivativeMeasure (v : ℝ → ℝ)
    (hmono : Monotone (rightDeriv v)) : Measure ℝ :=
  monotoneStieltjesSecondDerivativeMeasure (rightDeriv v) hmono

@[simp]
theorem monotoneStieltjesSecondDerivativeFunction_apply
    {g : ℝ → ℝ} (hg : Monotone g) (x : ℝ) :
    monotoneStieltjesSecondDerivativeFunction g hg x = Function.rightLim g x := by
  simpa [monotoneStieltjesSecondDerivativeFunction] using hg.stieltjesFunction_eq x

@[simp]
theorem monotoneStieltjesSecondDerivativeMeasure_Ioc
    {g : ℝ → ℝ} (hg : Monotone g) (a b : ℝ) :
    monotoneStieltjesSecondDerivativeMeasure g hg (Set.Ioc a b) =
      ENNReal.ofReal
        (monotoneStieltjesSecondDerivativeFunction g hg b -
          monotoneStieltjesSecondDerivativeFunction g hg a) := by
  simp [monotoneStieltjesSecondDerivativeMeasure]

@[simp]
theorem rightDerivStieltjesSecondDerivativeMeasure_Ioc
    {v : ℝ → ℝ} (hmono : Monotone (rightDeriv v)) (a b : ℝ) :
    rightDerivStieltjesSecondDerivativeMeasure v hmono (Set.Ioc a b) =
      ENNReal.ofReal
        (rightDerivStieltjesSecondDerivativeFunction v hmono b -
          rightDerivStieltjesSecondDerivativeFunction v hmono a) := by
  simp [rightDerivStieltjesSecondDerivativeMeasure,
    rightDerivStieltjesSecondDerivativeFunction]

@[simp]
theorem monotoneStieltjesSecondDerivativeMeasure_sourceMaximalDomain
    {g : ℝ → ℝ} (hg : Monotone g) :
    monotoneStieltjesSecondDerivativeMeasure g hg sourceMaximalDomain =
      ENNReal.ofReal
        (Function.leftLim (monotoneStieltjesSecondDerivativeFunction g hg) (2 : ℝ) -
          monotoneStieltjesSecondDerivativeFunction g hg (-2 : ℝ)) := by
  rw [monotoneStieltjesSecondDerivativeMeasure, sourceMaximalDomain]
  exact (monotoneStieltjesSecondDerivativeFunction g hg).measure_Ioo (a := (-2 : ℝ)) (b := 2)

@[simp]
theorem rightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain
    {v : ℝ → ℝ} (hmono : Monotone (rightDeriv v)) :
    rightDerivStieltjesSecondDerivativeMeasure v hmono sourceMaximalDomain =
      ENNReal.ofReal
        (Function.leftLim (rightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) -
          rightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ)) := by
  rw [rightDerivStieltjesSecondDerivativeMeasure, rightDerivStieltjesSecondDerivativeFunction]
  exact monotoneStieltjesSecondDerivativeMeasure_sourceMaximalDomain (g := rightDeriv v) hmono

/-! ## Source-local right-derivative extension -/

/-- Clamp a real parameter to the closed source interval `[-2,2]`.

This is used to turn the right derivative, known to be monotone only on the source line interval,
into a globally monotone function to which Mathlib's Stieltjes construction applies. -/
def sourceDerivativeClamp (s : ℝ) : ℝ :=
  max (-2 : ℝ) (min 2 s)

theorem sourceDerivativeClamp_mem_Icc (s : ℝ) :
    sourceDerivativeClamp s ∈ Set.Icc (-2 : ℝ) 2 := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by norm_num) (min_le_left _ _)

theorem monotone_sourceDerivativeClamp : Monotone sourceDerivativeClamp := by
  intro a b hab
  exact max_le_max le_rfl (min_le_min le_rfl hab)

theorem sourceDerivativeClamp_eq_of_mem_sourceMaximalDomain {s : ℝ}
    (hs : s ∈ sourceMaximalDomain) :
    sourceDerivativeClamp s = s := by
  rcases hs with ⟨hs_left, hs_right⟩
  simp [sourceDerivativeClamp, min_eq_right hs_right.le, max_eq_right hs_left.le]

/-- The source-local right derivative extended to all of `ℝ` by clamping the line parameter to
`[-2,2]`. -/
def sourceRightDerivExtension (v : ℝ → ℝ) (s : ℝ) : ℝ :=
  rightDeriv v (sourceDerivativeClamp s)

theorem sourceRightDerivExtension_eq_of_mem_sourceMaximalDomain {v : ℝ → ℝ} {s : ℝ}
    (hs : s ∈ sourceMaximalDomain) :
    sourceRightDerivExtension v s = rightDeriv v s := by
  simp [sourceRightDerivExtension, sourceDerivativeClamp_eq_of_mem_sourceMaximalDomain hs]

/-- To the left of a point strictly inside the source interval, the clamp is eventually the
identity. -/
theorem sourceDerivativeClamp_eventuallyEq_id_nhdsLT {s : ℝ}
    (hs : s ∈ sourceMaximalDomain) :
    sourceDerivativeClamp =ᶠ[nhdsWithin s (Set.Iio s)] id := by
  rcases hs with ⟨hs_left, hs_right⟩
  filter_upwards [Ioo_mem_nhdsLT hs_left] with y hy
  exact sourceDerivativeClamp_eq_of_mem_sourceMaximalDomain
    ⟨hy.1, hy.2.trans hs_right⟩

/-- To the right of a point strictly inside the source interval, the clamp is eventually the
identity. -/
theorem sourceDerivativeClamp_eventuallyEq_id_nhdsGT {s : ℝ}
    (hs : s ∈ sourceMaximalDomain) :
    sourceDerivativeClamp =ᶠ[nhdsWithin s (Set.Ioi s)] id := by
  rcases hs with ⟨hs_left, hs_right⟩
  filter_upwards [Ioo_mem_nhdsGT hs_right] with y hy
  exact sourceDerivativeClamp_eq_of_mem_sourceMaximalDomain
    ⟨hs_left.trans hy.1, hy.2⟩

/-- To the left of a point strictly inside the source interval, the clamped right-derivative
extension is eventually the ordinary right derivative. -/
theorem sourceRightDerivExtension_eventuallyEq_rightDeriv_nhdsLT
    {v : ℝ → ℝ} {s : ℝ} (hs : s ∈ sourceMaximalDomain) :
    sourceRightDerivExtension v =ᶠ[nhdsWithin s (Set.Iio s)] rightDeriv v := by
  filter_upwards [sourceDerivativeClamp_eventuallyEq_id_nhdsLT hs] with y hy
  simp [sourceRightDerivExtension, hy]

/-- To the right of a point strictly inside the source interval, the clamped right-derivative
extension is eventually the ordinary right derivative. -/
theorem sourceRightDerivExtension_eventuallyEq_rightDeriv_nhdsGT
    {v : ℝ → ℝ} {s : ℝ} (hs : s ∈ sourceMaximalDomain) :
    sourceRightDerivExtension v =ᶠ[nhdsWithin s (Set.Ioi s)] rightDeriv v := by
  filter_upwards [sourceDerivativeClamp_eventuallyEq_id_nhdsGT hs] with y hy
  simp [sourceRightDerivExtension, hy]

/-- A left limit of the ordinary right derivative transfers to the clamped source extension at
points strictly inside the source interval. -/
theorem sourceRightDerivExtension_leftLim_eq_of_tendsto_rightDeriv_nhdsLT
    {v : ℝ → ℝ} {s L : ℝ} (hs : s ∈ sourceMaximalDomain)
    (hlim : Tendsto (rightDeriv v) (nhdsWithin s (Set.Iio s)) (nhds L)) :
    Function.leftLim (sourceRightDerivExtension v) s = L := by
  have hlim_ext :
      Tendsto (sourceRightDerivExtension v) (nhdsWithin s (Set.Iio s)) (nhds L) :=
    hlim.congr' (sourceRightDerivExtension_eventuallyEq_rightDeriv_nhdsLT hs).symm
  exact leftLim_eq_of_tendsto hlim_ext

/-- A right limit of the ordinary right derivative transfers to the clamped source extension at
points strictly inside the source interval. -/
theorem sourceRightDerivExtension_rightLim_eq_of_tendsto_rightDeriv_nhdsGT
    {v : ℝ → ℝ} {s L : ℝ} (hs : s ∈ sourceMaximalDomain)
    (hlim : Tendsto (rightDeriv v) (nhdsWithin s (Set.Ioi s)) (nhds L)) :
    Function.rightLim (sourceRightDerivExtension v) s = L := by
  have hlim_ext :
      Tendsto (sourceRightDerivExtension v) (nhdsWithin s (Set.Ioi s)) (nhds L) :=
    hlim.congr' (sourceRightDerivExtension_eventuallyEq_rightDeriv_nhdsGT hs).symm
  exact rightLim_eq_of_tendsto hlim_ext

/-- A right derivative monotone on the source interval `[-2,2]` gives a globally monotone
clamped extension. -/
theorem monotone_sourceRightDerivExtension {v : ℝ → ℝ}
    (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    Monotone (sourceRightDerivExtension v) := by
  intro a b hab
  exact hmono (sourceDerivativeClamp_mem_Icc a) (sourceDerivativeClamp_mem_Icc b)
    (monotone_sourceDerivativeClamp hab)

/-- Stieltjes function of the source-local right-derivative extension. -/
def sourceRightDerivStieltjesSecondDerivativeFunction
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    StieltjesFunction ℝ :=
  monotoneStieltjesSecondDerivativeFunction (sourceRightDerivExtension v)
    (monotone_sourceRightDerivExtension hmono)

/-- Stieltjes measure of the source-local right-derivative extension.

This is the source-local concrete candidate for the distributional second derivative measure used
by the localized maximal argument. -/
def sourceRightDerivStieltjesSecondDerivativeMeasure
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) : Measure ℝ :=
  monotoneStieltjesSecondDerivativeMeasure (sourceRightDerivExtension v)
    (monotone_sourceRightDerivExtension hmono)

/-- The source-local Stieltjes measure has finite mass on every bounded open interval. -/
theorem sourceRightDerivStieltjesSecondDerivativeMeasure_Ioo_lt_top
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (a b : ℝ) :
    sourceRightDerivStieltjesSecondDerivativeMeasure v hmono (Set.Ioo a b) < ⊤ := by
  rw [sourceRightDerivStieltjesSecondDerivativeMeasure,
    monotoneStieltjesSecondDerivativeMeasure]
  exact measure_Ioo_lt_top

@[simp]
theorem sourceRightDerivStieltjesSecondDerivativeFunction_apply
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (s : ℝ) :
    sourceRightDerivStieltjesSecondDerivativeFunction v hmono s =
      Function.rightLim (sourceRightDerivExtension v) s := by
  simp [sourceRightDerivStieltjesSecondDerivativeFunction]

/-- The left limit of the right-continuous Stieltjes representative agrees with the left limit
of the clamped right-derivative extension that generated it. -/
theorem sourceRightDerivStieltjesSecondDerivativeFunction_leftLim_eq_extension_leftLim
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (s : ℝ) :
    Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) s =
      Function.leftLim (sourceRightDerivExtension v) s := by
  change
    Function.leftLim (Function.rightLim (sourceRightDerivExtension v)) s =
      Function.leftLim (sourceRightDerivExtension v) s
  exact leftLim_rightLim ((monotone_sourceRightDerivExtension hmono).tendsto_leftLim s)

@[simp]
theorem sourceRightDerivStieltjesSecondDerivativeMeasure_Ioc
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    (a b : ℝ) :
    sourceRightDerivStieltjesSecondDerivativeMeasure v hmono (Set.Ioc a b) =
      ENNReal.ofReal
        (sourceRightDerivStieltjesSecondDerivativeFunction v hmono b -
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono a) := by
  simp [sourceRightDerivStieltjesSecondDerivativeMeasure,
    sourceRightDerivStieltjesSecondDerivativeFunction]

@[simp]
theorem sourceRightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    sourceRightDerivStieltjesSecondDerivativeMeasure v hmono sourceMaximalDomain =
      ENNReal.ofReal
        (Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) -
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ)) := by
  rw [sourceRightDerivStieltjesSecondDerivativeMeasure,
    sourceRightDerivStieltjesSecondDerivativeFunction]
  exact monotoneStieltjesSecondDerivativeMeasure_sourceMaximalDomain
    (g := sourceRightDerivExtension v) (monotone_sourceRightDerivExtension hmono)

/-- The real jump of the clamped right-derivative Stieltjes function across the source maximal
domain `(-2,2)`. By the Stieltjes interval formula this is the real mass of `(-2,2)`. -/
def sourceRightDerivStieltjesSourceJump
    (v : ℝ → ℝ) (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) : ℝ :=
  Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) -
    sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ)

theorem sourceRightDerivStieltjesSourceJump_nonneg
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    0 ≤ sourceRightDerivStieltjesSourceJump v hmono := by
  let F := sourceRightDerivStieltjesSecondDerivativeFunction v hmono
  have hle : F (-2 : ℝ) ≤ Function.leftLim F (2 : ℝ) :=
    F.mono.le_leftLim (by norm_num : (-2 : ℝ) < 2)
  simpa [sourceRightDerivStieltjesSourceJump, F] using sub_nonneg.mpr hle

theorem sourceRightDerivStieltjesSourceJump_le_of_function_bounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {lower upper osc : ℝ}
    (hlower :
      lower ≤ sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ))
    (hupper :
      Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) ≤
        upper)
    (hwidth : upper - lower ≤ 2 * osc) :
    sourceRightDerivStieltjesSourceJump v hmono ≤ 2 * osc := by
  calc
    sourceRightDerivStieltjesSourceJump v hmono =
        Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) -
          sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ) := rfl
    _ ≤ upper - lower := sub_le_sub hupper hlower
    _ ≤ 2 * osc := hwidth

theorem sourceRightDerivStieltjesSourceJump_le_of_abs_function_bound
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower :
      -osc ≤ sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ))
    (hupper :
      Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) ≤
        osc) :
    sourceRightDerivStieltjesSourceJump v hmono ≤ 2 * osc :=
  sourceRightDerivStieltjesSourceJump_le_of_function_bounds
    (lower := -osc) (upper := osc) hlower hupper (by ring_nf; exact le_rfl)

theorem sourceRightDerivStieltjesFunction_neg_two_ge_of_rightDeriv_lower
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {lower : ℝ}
    (hlower : lower ≤ rightDeriv v (-2 : ℝ)) :
    lower ≤ sourceRightDerivStieltjesSecondDerivativeFunction v hmono (-2 : ℝ) := by
  let g := sourceRightDerivExtension v
  have hg : Monotone g := monotone_sourceRightDerivExtension hmono
  have hle_rightLim : g (-2 : ℝ) ≤ Function.rightLim g (-2 : ℝ) :=
    hg.le_rightLim le_rfl
  have hg_neg_two : lower ≤ g (-2 : ℝ) := by
    simpa [g, sourceRightDerivExtension, sourceDerivativeClamp] using hlower
  exact hg_neg_two.trans (by
    change g (-2 : ℝ) ≤
      (monotone_sourceRightDerivExtension hmono).stieltjesFunction (-2 : ℝ)
    rw [(monotone_sourceRightDerivExtension hmono).stieltjesFunction_eq]
    exact hle_rightLim)

theorem sourceRightDerivStieltjesFunction_leftLim_two_le_of_rightDeriv_upper
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {upper : ℝ}
    (hupper : rightDeriv v (2 : ℝ) ≤ upper) :
    Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) (2 : ℝ) ≤
      upper := by
  let g := sourceRightDerivExtension v
  let F := sourceRightDerivStieltjesSecondDerivativeFunction v hmono
  have hleft_le : Function.leftLim F (2 : ℝ) ≤ F (2 : ℝ) :=
    F.mono.leftLim_le le_rfl
  have hg : Monotone g := monotone_sourceRightDerivExtension hmono
  have hF_two_le_g_three : F (2 : ℝ) ≤ g (3 : ℝ) := by
    have hright : Function.rightLim g (2 : ℝ) ≤ g (3 : ℝ) :=
      hg.rightLim_le (by norm_num : (2 : ℝ) < 3)
    change (monotone_sourceRightDerivExtension hmono).stieltjesFunction (2 : ℝ) ≤
      g (3 : ℝ)
    rw [(monotone_sourceRightDerivExtension hmono).stieltjesFunction_eq]
    exact hright
  have hg_three_le : g (3 : ℝ) ≤ upper := by
    have hclamp : sourceDerivativeClamp (3 : ℝ) = 2 := by
      norm_num [sourceDerivativeClamp]
    simpa [g, sourceRightDerivExtension, hclamp] using hupper
  exact hleft_le.trans (hF_two_le_g_three.trans hg_three_le)

theorem sourceRightDerivStieltjesSourceJump_le_of_rightDeriv_bounds
    {v : ℝ → ℝ} {hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)}
    {osc : ℝ}
    (hlower : -osc ≤ rightDeriv v (-2 : ℝ))
    (hupper : rightDeriv v (2 : ℝ) ≤ osc) :
    sourceRightDerivStieltjesSourceJump v hmono ≤ 2 * osc :=
  sourceRightDerivStieltjesSourceJump_le_of_abs_function_bound
    (sourceRightDerivStieltjesFunction_neg_two_ge_of_rightDeriv_lower hlower)
    (sourceRightDerivStieltjesFunction_leftLim_two_le_of_rightDeriv_upper hupper)

theorem sourceRightDerivStieltjesSecondDerivativeMeasure_real_sourceMaximalDomain
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono).real sourceMaximalDomain =
      sourceRightDerivStieltjesSourceJump v hmono := by
  rw [measureReal_def, sourceRightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain]
  exact ENNReal.toReal_ofReal (sourceRightDerivStieltjesSourceJump_nonneg hmono)

/-- Real-valued `Ioo` formula for the source-local clamped right-derivative Stieltjes measure. -/
theorem sourceRightDerivStieltjesSecondDerivativeMeasure_real_Ioo
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2))
    {a b : ℝ} (hab : a < b) :
    (sourceRightDerivStieltjesSecondDerivativeMeasure v hmono).real (Set.Ioo a b) =
      Function.leftLim (sourceRightDerivStieltjesSecondDerivativeFunction v hmono) b -
        sourceRightDerivStieltjesSecondDerivativeFunction v hmono a := by
  let F := sourceRightDerivStieltjesSecondDerivativeFunction v hmono
  have hnonneg : 0 ≤ Function.leftLim F b - F a :=
    sub_nonneg.mpr (F.mono.le_leftLim hab)
  have hmeasure :
      sourceRightDerivStieltjesSecondDerivativeMeasure v hmono (Set.Ioo a b) =
        ENNReal.ofReal (Function.leftLim F b - F a) := by
    change F.measure (Set.Ioo a b) = ENNReal.ofReal (Function.leftLim F b - F a)
    exact F.measure_Ioo
  rw [measureReal_def, hmeasure]
  exact ENNReal.toReal_ofReal hnonneg

theorem sourceRightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain_lt_top
    {v : ℝ → ℝ} (hmono : MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2)) :
    sourceRightDerivStieltjesSecondDerivativeMeasure v hmono sourceMaximalDomain < ⊤ := by
  rw [sourceRightDerivStieltjesSecondDerivativeMeasure_sourceMaximalDomain]
  exact ENNReal.ofReal_lt_top

/-- Convexity on `(-3,3)` supplies the monotonicity of the project-local right derivative on
the clamped source interval `[-2,2]`. -/
theorem ConvexOn.monotoneOn_projectRightDeriv_sourceIcc
    {v : ℝ → ℝ} (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v) :
    MonotoneOn (rightDeriv v) (Set.Icc (-2 : ℝ) 2) := by
  intro a ha b hb hab
  rcases ha with ⟨ha_left, ha_right⟩
  rcases hb with ⟨hb_left, hb_right⟩
  have hmono := AleksandrovDifferentiability.ConvexOn.monotoneOn_projectRightDeriv hv
  have ha' : a ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show a ∈ Set.Ioo (-3 : ℝ) 3 by constructor <;> linarith)
  have hb' : b ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show b ∈ Set.Ioo (-3 : ℝ) 3 by constructor <;> linarith)
  exact hmono ha' hb' hab

/-- If all value differences on `(-3,3)` are bounded above by `osc`, then a forward secant from
`2` to a point near `3` has slope at most `osc + ε`.

This is the elementary endpoint step used in the source proof to turn bounded oscillation into
right-derivative control. -/
theorem exists_right_secant_two_le_add_of_pairwise_sub_le
    {v : ℝ → ℝ} {osc ε : ℝ} (hosc : 0 ≤ osc) (hε : 0 < ε)
    (hbound :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Ioo (-3 : ℝ) 3 → y ∈ Set.Ioo (-3 : ℝ) 3 →
        v y - v x ≤ osc) :
    ∃ y : ℝ, y ∈ Set.Ioo (2 : ℝ) 3 ∧ slope v (2 : ℝ) y ≤ osc + ε := by
  by_cases hosc_zero : osc = 0
  · refine ⟨(5 / 2 : ℝ), by norm_num, ?_⟩
    have hdiff :
        v (5 / 2 : ℝ) - v (2 : ℝ) ≤ 0 := by
      simpa [hosc_zero] using
        hbound (x := (2 : ℝ)) (y := (5 / 2 : ℝ))
          (by norm_num : (2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3)
          (by norm_num : (5 / 2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3)
    have hslope : slope v (2 : ℝ) (5 / 2 : ℝ) ≤ 0 := by
      rw [slope_def_field]
      exact (div_le_iff₀ (by norm_num : 0 < (5 / 2 : ℝ) - 2)).mpr (by simpa using hdiff)
    linarith
  · have hosc_pos : 0 < osc := lt_of_le_of_ne hosc (Ne.symm hosc_zero)
    let d : ℝ := osc / (osc + ε)
    have hden_pos : 0 < osc + ε := add_pos hosc_pos hε
    have hd_pos : 0 < d := div_pos hosc_pos hden_pos
    have hd_lt_one : d < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    let y : ℝ := 2 + d
    have hy : y ∈ Set.Ioo (2 : ℝ) 3 := by
      constructor <;> dsimp [y] <;> linarith
    refine ⟨y, hy, ?_⟩
    have hy_domain : y ∈ Set.Ioo (-3 : ℝ) 3 := by
      constructor <;> linarith [hy.1, hy.2]
    have hdiff :
        v y - v (2 : ℝ) ≤ osc :=
      hbound (x := (2 : ℝ)) (y := y)
        (by norm_num : (2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3) hy_domain
    have hmul_eq : (osc + ε) * (y - 2) = osc := by
      dsimp [y, d]
      field_simp [hden_pos.ne']
      ring
    rw [slope_def_field]
    exact (div_le_iff₀ (by dsimp [y]; linarith)).mpr (by
      simpa [hmul_eq] using hdiff)

/-- If all value differences on `(-3,3)` are bounded above by `osc`, then a backward secant
from a point near `-3` to `-2` has slope at least `-osc - ε`. -/
theorem exists_neg_add_le_left_secant_neg_two_of_pairwise_sub_le
    {v : ℝ → ℝ} {osc ε : ℝ} (hosc : 0 ≤ osc) (hε : 0 < ε)
    (hbound :
      ∀ ⦃x y : ℝ⦄, x ∈ Set.Ioo (-3 : ℝ) 3 → y ∈ Set.Ioo (-3 : ℝ) 3 →
        v y - v x ≤ osc) :
    ∃ y : ℝ, y ∈ Set.Ioo (-3 : ℝ) (-2) ∧ -osc - ε ≤ slope v y (-2 : ℝ) := by
  by_cases hosc_zero : osc = 0
  · refine ⟨(-5 / 2 : ℝ), by norm_num, ?_⟩
    have hdiff :
        v (-5 / 2 : ℝ) - v (-2 : ℝ) ≤ 0 := by
      simpa [hosc_zero] using
        hbound (x := (-2 : ℝ)) (y := (-5 / 2 : ℝ))
          (by norm_num : (-2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3)
          (by norm_num : (-5 / 2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3)
    have hnum : 0 ≤ v (-2 : ℝ) - v (-5 / 2 : ℝ) := by linarith
    have hslope_nonneg : 0 ≤ slope v (-5 / 2 : ℝ) (-2 : ℝ) := by
      rw [slope_def_field]
      exact div_nonneg hnum (by norm_num : 0 ≤ (-2 : ℝ) - (-5 / 2 : ℝ))
    linarith
  · have hosc_pos : 0 < osc := lt_of_le_of_ne hosc (Ne.symm hosc_zero)
    let d : ℝ := osc / (osc + ε)
    have hden_pos : 0 < osc + ε := add_pos hosc_pos hε
    have hd_pos : 0 < d := div_pos hosc_pos hden_pos
    have hd_lt_one : d < 1 := by
      rw [div_lt_one hden_pos]
      linarith
    let y : ℝ := -2 - d
    have hy : y ∈ Set.Ioo (-3 : ℝ) (-2) := by
      constructor <;> dsimp [y] <;> linarith
    refine ⟨y, hy, ?_⟩
    have hy_domain : y ∈ Set.Ioo (-3 : ℝ) 3 := by
      constructor <;> linarith [hy.1, hy.2]
    have hdiff :
        v y - v (-2 : ℝ) ≤ osc :=
      hbound (x := (-2 : ℝ)) (y := y)
        (by norm_num : (-2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3) hy_domain
    have hnum_lower : -osc ≤ v (-2 : ℝ) - v y := by linarith
    have hmul_eq : (-osc - ε) * ((-2 : ℝ) - y) = -osc := by
      dsimp [y, d]
      field_simp [hden_pos.ne']
      ring
    rw [slope_def_field]
    exact (le_div_iff₀ (by dsimp [y]; linarith)).mpr (by
      simpa [hmul_eq] using hnum_lower)

/-- Forward secants approaching the right source endpoint control the right derivative at `2`.

This is the source-proof shape needed because the ambient interval is open at `3`. -/
theorem ConvexOn.rightDeriv_two_le_of_forall_exists_secant_le_add
    {v : ℝ → ℝ} {osc : ℝ} (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v)
    (hsec :
      ∀ ε : ℝ, 0 < ε →
        ∃ y : ℝ, y ∈ Set.Ioo (2 : ℝ) 3 ∧ slope v (2 : ℝ) y ≤ osc + ε) :
    rightDeriv v (2 : ℝ) ≤ osc := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases hsec ε hε with ⟨y, hy, hslope⟩
  have htwo : (2 : ℝ) ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show (2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3 by norm_num)
  have hy_domain : y ∈ Set.Ioo (-3 : ℝ) 3 := by
    constructor <;> linarith [hy.1, hy.2]
  exact (AleksandrovDifferentiability.ConvexOn.rightDeriv_le_slope
    (S := Set.Ioo (-3 : ℝ) 3) (f := v) hv htwo hy_domain hy.1).trans hslope

/-- Backward secants approaching the left source endpoint control the right derivative at `-2`
from below. -/
theorem ConvexOn.neg_osc_le_rightDeriv_neg_two_of_forall_exists_secant_add_le
    {v : ℝ → ℝ} {osc : ℝ} (hv : ConvexOn ℝ (Set.Ioo (-3 : ℝ) 3) v)
    (hsec :
      ∀ ε : ℝ, 0 < ε →
        ∃ y : ℝ, y ∈ Set.Ioo (-3 : ℝ) (-2) ∧ -osc - ε ≤ slope v y (-2 : ℝ)) :
    -osc ≤ rightDeriv v (-2 : ℝ) := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases hsec ε hε with ⟨y, hy, hslope⟩
  have hy_domain : y ∈ Set.Ioo (-3 : ℝ) 3 := by
    constructor <;> linarith [hy.1, hy.2]
  have hneg_two : (-2 : ℝ) ∈ interior (Set.Ioo (-3 : ℝ) 3) := by
    simpa using (show (-2 : ℝ) ∈ Set.Ioo (-3 : ℝ) 3 by norm_num)
  have hslope_le_left :
      slope v y (-2 : ℝ) ≤ leftDeriv v (-2 : ℝ) :=
    AleksandrovDifferentiability.ConvexOn.slope_le_leftDeriv
      (S := Set.Ioo (-3 : ℝ) 3) (f := v) hv hy_domain hneg_two hy.2
  have hleft_le_right :
      leftDeriv v (-2 : ℝ) ≤ rightDeriv v (-2 : ℝ) :=
    AleksandrovDifferentiability.ConvexOn.leftDeriv_le_rightDeriv
      (S := Set.Ioo (-3 : ℝ) 3) (f := v) hv hneg_two
  have hmain : -osc - ε ≤ rightDeriv v (-2 : ℝ) :=
    hslope.trans (hslope_le_left.trans hleft_le_right)
  linarith

/-- Forward affine remainders of a one-dimensional convex function are controlled by the gap
between the right derivative at the endpoint and the chosen subgradient. -/
theorem SubgradientOn.affineRemainder_add_le_mul_rightDeriv_sub
    {S : Set ℝ} {v : ℝ → ℝ} {x p h : ℝ}
    (_hp : SubgradientOn S v x p) (hv : ConvexOn ℝ S v)
    (hx : x ∈ interior S) (hxh : x + h ∈ interior S) (hh : 0 ≤ h) :
    affineRemainder v x p (x + h) ≤ h * (rightDeriv v (x + h) - p) := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  have hslope_le :
      slope v x (x + h) ≤ rightDeriv v (x + h) :=
    (ConvexOn.slope_le_leftDeriv
      (S := S) (f := v) (x := x) (y := x + h)
      hv (interior_subset hx) hxh (by linarith)).trans
      (ConvexOn.leftDeriv_le_rightDeriv
        (S := S) (f := v) (x := x + h) hv hxh)
  have hrem_eq :
      affineRemainder v x p (x + h) = h * (slope v x (x + h) - p) := by
    rw [affineRemainder, slope_def_field]
    rw [Real.inner_apply]
    have hden : x + h - x = h := by ring
    field_simp [hden, hh_pos.ne']
    ring_nf
  rw [hrem_eq]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hslope_le p) hh

/-- Forward affine remainders of a one-dimensional convex function are controlled by the gap
between the left derivative at the endpoint and the chosen subgradient.

This variant is better suited to open-interval Stieltjes masses, which see the left limit at the
right endpoint. -/
theorem SubgradientOn.affineRemainder_add_le_mul_leftDeriv_sub
    {S : Set ℝ} {v : ℝ → ℝ} {x p h : ℝ}
    (_hp : SubgradientOn S v x p) (hv : ConvexOn ℝ S v)
    (hx : x ∈ interior S) (hxh : x + h ∈ interior S) (hh : 0 ≤ h) :
    affineRemainder v x p (x + h) ≤ h * (leftDeriv v (x + h) - p) := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  have hslope_le :
      slope v x (x + h) ≤ leftDeriv v (x + h) :=
    ConvexOn.slope_le_leftDeriv
      (S := S) (f := v) (x := x) (y := x + h)
      hv (interior_subset hx) hxh (by linarith)
  have hrem_eq :
      affineRemainder v x p (x + h) = h * (slope v x (x + h) - p) := by
    rw [affineRemainder, slope_def_field]
    rw [Real.inner_apply]
    have hden : x + h - x = h := by ring
    field_simp [hden, hh_pos.ne']
    ring_nf
  rw [hrem_eq]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_right hslope_le p) hh

/-- Backward affine remainders of a one-dimensional convex function are controlled by the gap
between the chosen subgradient and the right derivative at the left endpoint. -/
theorem SubgradientOn.affineRemainder_sub_le_mul_sub_rightDeriv
    {S : Set ℝ} {v : ℝ → ℝ} {x p h : ℝ}
    (_hp : SubgradientOn S v x p) (hv : ConvexOn ℝ S v)
    (hx : x ∈ interior S) (hxmh : x - h ∈ interior S) (hh : 0 ≤ h) :
    affineRemainder v x p (x - h) ≤ h * (p - rightDeriv v (x - h)) := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  have hright_le_slope :
      rightDeriv v (x - h) ≤ slope v (x - h) x :=
    ConvexOn.rightDeriv_le_slope
      (S := S) (f := v) (x := x - h) (y := x)
      hv hxmh (interior_subset hx) (by linarith)
  have hrem_eq :
      affineRemainder v x p (x - h) = h * (p - slope v (x - h) x) := by
    rw [affineRemainder, slope_def_field]
    rw [Real.inner_apply]
    have hden : x - (x - h) = h := by ring
    field_simp [hden, hh_pos.ne']
    ring_nf
  rw [hrem_eq]
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left hright_le_slope p) hh

/-- Two-sided affine remainders of a one-dimensional convex function are controlled by the
right-derivative variation across the symmetric interval. -/
theorem SubgradientOn.affineRemainder_pm_le_mul_rightDeriv_sub
    {S : Set ℝ} {v : ℝ → ℝ} {x p h : ℝ}
    (hp : SubgradientOn S v x p) (hv : ConvexOn ℝ S v)
    (hx : x ∈ interior S) (hxmh : x - h ∈ interior S) (hxph : x + h ∈ interior S)
    (hh : 0 ≤ h) :
    affineRemainder v x p (x + h) ≤
        h * (rightDeriv v (x + h) - rightDeriv v (x - h)) ∧
      affineRemainder v x p (x - h) ≤
        h * (rightDeriv v (x + h) - rightDeriv v (x - h)) := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  have hmono : MonotoneOn (rightDeriv v) (interior S) :=
    ConvexOn.monotoneOn_projectRightDeriv (S := S) (f := v) hv
  have hleft_le_p : rightDeriv v (x - h) ≤ p := by
    have hrd_le_slope :
        rightDeriv v (x - h) ≤ slope v (x - h) x :=
      ConvexOn.rightDeriv_le_slope
        (S := S) (f := v) (x := x - h) (y := x)
        hv hxmh (interior_subset hx) (by linarith)
    have hslope_le_left :
        slope v (x - h) x ≤ leftDeriv v x :=
      ConvexOn.slope_le_leftDeriv
        (S := S) (f := v) (x := x - h) (y := x)
        hv (interior_subset hxmh) hx (by linarith)
    exact (hrd_le_slope.trans hslope_le_left).trans
      (SubgradientOn.leftDeriv_le_of_convex
        (S := S) (f := v) (x := x) hp hv hx)
  have hp_le_right : p ≤ rightDeriv v (x + h) := by
    exact (SubgradientOn.le_rightDeriv_of_convex
      (S := S) (f := v) (x := x) hp hv hx).trans
      (hmono hx hxph (by linarith))
  constructor
  · exact (hp.affineRemainder_add_le_mul_rightDeriv_sub hv hx hxph hh).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hleft_le_p (rightDeriv v (x + h))) hh)
  · exact (hp.affineRemainder_sub_le_mul_sub_rightDeriv hv hx hxmh hh).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hp_le_right (rightDeriv v (x - h))) hh)

/-- Two-sided affine remainders of a one-dimensional convex function are controlled by the
open-interval derivative variation from the right derivative at the left endpoint to the left
derivative at the right endpoint. -/
theorem SubgradientOn.affineRemainder_pm_le_mul_leftDeriv_sub_rightDeriv
    {S : Set ℝ} {v : ℝ → ℝ} {x p h : ℝ}
    (hp : SubgradientOn S v x p) (hv : ConvexOn ℝ S v)
    (hx : x ∈ interior S) (hxmh : x - h ∈ interior S) (hxph : x + h ∈ interior S)
    (hh : 0 ≤ h) :
    affineRemainder v x p (x + h) ≤
        h * (leftDeriv v (x + h) - rightDeriv v (x - h)) ∧
      affineRemainder v x p (x - h) ≤
        h * (leftDeriv v (x + h) - rightDeriv v (x - h)) := by
  by_cases hzero : h = 0
  · simp [hzero]
  have hh_pos : 0 < h := lt_of_le_of_ne hh (Ne.symm hzero)
  have hleft_le_p : rightDeriv v (x - h) ≤ p := by
    have hrd_le_slope :
        rightDeriv v (x - h) ≤ slope v (x - h) x :=
      ConvexOn.rightDeriv_le_slope
        (S := S) (f := v) (x := x - h) (y := x)
        hv hxmh (interior_subset hx) (by linarith)
    have hslope_le_left :
        slope v (x - h) x ≤ leftDeriv v x :=
      ConvexOn.slope_le_leftDeriv
        (S := S) (f := v) (x := x - h) (y := x)
        hv (interior_subset hxmh) hx (by linarith)
    exact (hrd_le_slope.trans hslope_le_left).trans
      (SubgradientOn.leftDeriv_le_of_convex
        (S := S) (f := v) (x := x) hp hv hx)
  have hp_le_left : p ≤ leftDeriv v (x + h) := by
    have hp_le_right : p ≤ rightDeriv v x :=
      SubgradientOn.le_rightDeriv_of_convex
        (S := S) (f := v) (x := x) hp hv hx
    have hright_le_slope :
        rightDeriv v x ≤ slope v x (x + h) :=
      ConvexOn.rightDeriv_le_slope
        (S := S) (f := v) (x := x) (y := x + h)
        hv hx (interior_subset hxph) (by linarith)
    have hslope_le_left :
        slope v x (x + h) ≤ leftDeriv v (x + h) :=
      ConvexOn.slope_le_leftDeriv
        (S := S) (f := v) (x := x) (y := x + h)
        hv (interior_subset hx) hxph (by linarith)
    exact hp_le_right.trans (hright_le_slope.trans hslope_le_left)
  constructor
  · exact (hp.affineRemainder_add_le_mul_leftDeriv_sub hv hx hxph hh).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hleft_le_p (leftDeriv v (x + h))) hh)
  · exact (hp.affineRemainder_sub_le_mul_sub_rightDeriv hv hx hxmh hh).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_right hp_le_left (rightDeriv v (x - h))) hh)

end AleksandrovDifferentiability
