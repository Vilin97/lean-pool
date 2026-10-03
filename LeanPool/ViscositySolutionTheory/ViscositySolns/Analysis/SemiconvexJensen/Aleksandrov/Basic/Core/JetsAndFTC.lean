/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Comparison.Semiconvex
public import LeanPool.ViscositySolutionTheory.ViscositySolns.TestFunctions.Taylor

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Core Aleksandrov Jet Infrastructure (JetsAndFTC)

Part of the core Aleksandrov jet infrastructure development. Split from
`Core.lean`; see the umbrella module docstring.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal
open scoped intervalIntegral

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
A strict local maximum point.

In quantified mathematical form, `StrictLocalMax f x0` means that there is a
neighborhood `U` of `x0` such that, for every `x ∈ U`, if `x ≠ x0`, then
`f x < f x0`.
-/
def StrictLocalMax (f : Point n -> Real) (x0 : Point n) : Prop :=
  ∃ U ∈ 𝓝 x0, ∀ x : Point n, x ∈ U -> x ≠ x0 -> f x < f x0

/--
The function obtained by adding the linear term `p · x`.
-/
def linearPerturbation (f : Point n -> Real) (p : Point n) : Point n -> Real :=
  fun x => f x + dotProduct p x

/--
The derivative of a linear perturbation.

In quantified mathematical form, if `f` is differentiable at `x` with
gradient `p`, then the function `y ↦ f y + q · y` is differentiable at `x`
with gradient `p + q`.
-/
theorem hasFDerivAt_linearPerturbation
    {f : Point n -> Real} {x p q : Point n}
    (hf : HasFDerivAt f (gradientLinearMap p) x) :
    HasFDerivAt (linearPerturbation f q) (gradientLinearMap (p + q)) x := by
  have hlin : HasFDerivAt (fun y : Point n => dotProduct q y) (gradientLinearMap q) x := by
    convert (gradientLinearMap q).hasFDerivAt (x := x) using 1
    ext y
    simp
  have hsum :
      HasFDerivAt (fun y : Point n => f y + dotProduct q y)
        (gradientLinearMap p + gradientLinearMap q) x :=
    hf.add hlin
  have hmap : gradientLinearMap p + gradientLinearMap q = gradientLinearMap (p + q) := by
    ext y
    simp [dotProduct, Finset.sum_add_distrib, add_mul]
  rw [← hmap]
  exact hsum

/--
The coordinate-gradient-to-Fréchet-derivative map as a continuous linear map.

This is the inverse direction to `linearMapGradientCLM`: it sends a coordinate
vector `p` to the continuous linear functional `v ↦ p · v`.
-/
def gradientLinearMapCLM : Point n →L[Real] Point n →L[Real] Real :=
  ∑ i : Fin n,
    (ContinuousLinearMap.smulRightL Real (Point n) Real
      (ContinuousLinearMap.proj (R := Real) i)).comp
        (ContinuousLinearMap.proj (R := Real) i)

@[simp]
theorem gradientLinearMapCLM_apply (p : Point n) :
    gradientLinearMapCLM p = gradientLinearMap p := by
  ext v
  simp [gradientLinearMapCLM, gradientLinearMap,
    ContinuousLinearMap.smulRightL_apply_apply]

/--
At a local maximum point of a differentiable linear perturbation, the
gradient of the original function is the negative perturbing vector.

In quantified mathematical form, if `x` is a local maximum of
`y ↦ f y + q · y`, and `f` is differentiable at `x` with gradient `p`, then
`p + q = 0`.
-/
theorem gradient_add_eq_zero_of_isLocalMax_linearPerturbation_hasFDerivAt
    {f : Point n -> Real} {x p q : Point n}
    (hmax : IsLocalMax (linearPerturbation f q) x)
    (hf : HasFDerivAt f (gradientLinearMap p) x) :
    p + q = 0 := by
  have hzero : gradientLinearMap (p + q) = 0 :=
    hmax.hasFDerivAt_eq_zero (hasFDerivAt_linearPerturbation (q := q) hf)
  have hgrad := congrArg linearMapGradient hzero
  rw [linearMapGradient_gradientLinearMap] at hgrad
  rw [hgrad]
  ext i
  simp

/--
Second-order differentiability expressed through ordinary superjets and
subjets.

In quantified mathematical form, `HasSecondOrderJet f x p X` means that
`(p, X)` belongs both to the superjet and to the subjet of `f` at `x`,
relative to all of `R^n`.
-/
def HasSecondOrderJet (f : Point n -> Real) (x p : Point n) (X : Hessian n) :
    Prop :=
  ({ gradient := p, hessian := X } : Jet n) ∈ Superjet Set.univ f x ∧
    ({ gradient := p, hessian := X } : Jet n) ∈ Subjet Set.univ f x

/--
A second-order expansion gives the corresponding ordinary two-sided jet.

This is the bridge from the classical Taylor-expansion conclusion of
Aleksandrov's theorem to the jet language used by the maximum-principle
formalization.
-/
theorem HasSecondOrderExpansionWithin.hasSecondOrderJet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n)) :
    HasSecondOrderJet f x p X := by
  rcases h with ⟨rho, hrho, heq⟩
  constructor
  · refine ⟨rho, hrho, ?_⟩
    filter_upwards [heq] with y hy
    exact le_of_eq hy
  · refine ⟨rho, hrho, ?_⟩
    filter_upwards [heq] with y hy
    exact le_of_eq hy.symm

/--
A second-order expansion on a set which is a neighborhood of the base point
gives the corresponding ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSecondOrderJet_of_mem_nhds
    {C : Set (Point n)} {f : Point n -> Real} {x : Point n}
    {J : Jet n} (hC : C ∈ 𝓝 x)
    (h : HasSecondOrderExpansionWithin C f x J) :
    HasSecondOrderJet f x J.gradient J.hessian := by
  have hfilter : 𝓝[C] x = 𝓝[Set.univ] x := by
    rw [nhdsWithin_eq_nhds.mpr hC, nhdsWithin_univ]
  have huniv : HasSecondOrderExpansionWithin Set.univ f x J :=
    (hasSecondOrderExpansionWithin_congr_nhdsWithin hfilter).1 h
  simpa using huniv.hasSecondOrderJet

/--
The set of points where a function has some second-order jet.

In quantified mathematical form, `HasSomeSecondOrderJet f x` means that there
exist `p : R^n` and a Hermitian matrix `X` such that `(p, X)` belongs both to
the ordinary superjet and to the ordinary subjet of `f` at `x`.
-/
def HasSomeSecondOrderJet (f : Point n -> Real) (x : Point n) : Prop :=
  ∃ p : Point n, ∃ X : Hessian n, X.IsHermitian ∧ HasSecondOrderJet f x p X

/--
Ordinary two-sided jets depend only on the germ of the function at the base
point.
-/
theorem HasSecondOrderJet.congr_of_eventuallyEq
    {f g : Point n -> Real} {x p : Point n} {X : Hessian n}
    (hfg : f =ᶠ[𝓝 x] g) (h : HasSecondOrderJet f x p X) :
    HasSecondOrderJet g x p X := by
  have hxfg : f x = g x := hfg.eq_of_nhds
  have hfgWithin : f =ᶠ[𝓝[Set.univ] x] g :=
    hfg.filter_mono nhdsWithin_le_nhds
  constructor
  · rcases h.1 with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, hfgWithin] with y hy hyfg
    simpa [hxfg, hyfg] using hy
  · rcases h.2 with ⟨rho, hrho, hineq⟩
    refine ⟨rho, hrho, ?_⟩
    filter_upwards [hineq, hfgWithin] with y hy hyfg
    simpa [hxfg, hyfg] using hy

/--
Existence of an ordinary two-sided jet depends only on the germ of the function
at the base point.
-/
theorem HasSomeSecondOrderJet.congr_of_eventuallyEq
    {f g : Point n -> Real} {x : Point n}
    (hfg : f =ᶠ[𝓝 x] g) (h : HasSomeSecondOrderJet f x) :
    HasSomeSecondOrderJet g x := by
  rcases h with ⟨p, X, hHerm, hJet⟩
  exact ⟨p, X, hHerm, hJet.congr_of_eventuallyEq hfg⟩

/--
A symmetric continuous bilinear map has a Hermitian coordinate Hessian.
-/
theorem bilinearMapHessian_isHermitian_of_isSymmetricBilinear
    {D2 : Point n →L[Real] Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2) :
    (bilinearMapHessian D2).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change D2 (coordinateVector j) (coordinateVector i) =
    D2 (coordinateVector i) (coordinateVector j)
  exact hD2sym (coordinateVector j) (coordinateVector i)

/--
A second-order expansion with Hermitian Hessian gives existence of some
ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSomeSecondOrderJet
    {f : Point n -> Real} {x p : Point n} {X : Hessian n}
    (h : HasSecondOrderExpansionWithin Set.univ f x
      ({ gradient := p, hessian := X } : Jet n))
    (hHerm : X.IsHermitian) :
    HasSomeSecondOrderJet f x :=
  ⟨p, X, hHerm, h.hasSecondOrderJet⟩

/--
A second-order expansion whose Fréchet second derivative is symmetric gives an
ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSomeSecondOrderJet_of_isSymmetricBilinear
    {f : Point n -> Real} {x : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (h : HasSecondOrderExpansionWithin Set.univ f x (Jet.ofDerivatives Dφ D2φ))
    (hD2sym : IsSymmetricBilinear D2φ) :
    HasSomeSecondOrderJet f x :=
  h.hasSomeSecondOrderJet
    (bilinearMapHessian_isHermitian_of_isSymmetricBilinear hD2sym)

/--
A second-order expansion on a neighborhood set whose Fréchet second derivative
is symmetric gives an ordinary two-sided jet.
-/
theorem HasSecondOrderExpansionWithin.hasSomeSecondOrderJet_of_isSymmetricBilinear_of_mem_nhds
    {C : Set (Point n)} {f : Point n -> Real} {x : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hC : C ∈ 𝓝 x)
    (h : HasSecondOrderExpansionWithin C f x (Jet.ofDerivatives Dφ D2φ))
    (hD2sym : IsSymmetricBilinear D2φ) :
    HasSomeSecondOrderJet f x :=
  let J : Jet n := Jet.ofDerivatives Dφ D2φ
  ⟨J.gradient, J.hessian,
    by
      change (bilinearMapHessian D2φ).IsHermitian
      exact bilinearMapHessian_isHermitian_of_isSymmetricBilinear hD2sym,
    by
      exact h.hasSecondOrderJet_of_mem_nhds hC⟩

/--
A Fréchet second-order little-oh remainder gives an ordinary two-sided jet.

This is the final target shape for the source proof's a.e. line-integration
argument: once the Taylor remainder is known to be `o(‖z - x‖²)`, the jet
conclusion follows without requiring differentiability on a whole
neighborhood.
-/
theorem HasSomeSecondOrderJet.of_frechetLittleO
    {f : Point n -> Real} {x : Point n}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hD2sym : IsSymmetricBilinear D2φ)
    (hTaylor : Asymptotics.IsLittleO (𝓝 x)
      (fun z : Point n => f z - frechetSecondOrderModel x (f x) Dφ D2φ z)
      (fun z : Point n => ‖z - x‖ ^ 2)) :
    HasSomeSecondOrderJet f x := by
  have hTaylorWithin : Asymptotics.IsLittleO (𝓝[Set.univ] x)
      (fun z : Point n => f z - frechetSecondOrderModel x (f x) Dφ D2φ z)
      (fun z : Point n => ‖z - x‖ ^ 2) := by
    simpa [nhdsWithin_univ] using hTaylor
  have hexp :
      HasSecondOrderExpansionWithin Set.univ f x (Jet.ofDerivatives Dφ D2φ) :=
    hasSecondOrderExpansionWithin_of_frechetTaylor
      (J := Jet.ofDerivatives Dφ D2φ)
      (Dφ := Dφ) (D2φ := D2φ)
      (by rw [Jet.toFirstDerivative_ofDerivatives])
      (by rw [Jet.toSecondDerivative_ofDerivatives])
      hTaylorWithin
  exact hexp.hasSomeSecondOrderJet_of_isSymmetricBilinear hD2sym

/--
One-dimensional FTC estimate used in the source proof's final Taylor step.

If a derivative-error field has an a.e. limit `c` at the base point, then its
interval integral from `0` to `t` has first-order expansion with slope `c`.
-/
theorem intervalIntegral_integral_sub_linear_isLittleO_of_tendsto_ae_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f : Real -> E} {c : E}
    (hfm : StronglyMeasurableAtFilter f (𝓝 (0 : Real)) volume)
    (hf : Filter.Tendsto f
      (𝓝 (0 : Real) ⊓ MeasureTheory.ae volume) (𝓝 c)) :
    (fun t : Real => (∫ s in (0 : Real)..t, f s) - t • c)
      =o[𝓝 (0 : Real)] (fun t : Real => t) := by
  have hraw :=
    intervalIntegral.integral_sub_linear_isLittleO_of_tendsto_ae
      (a := (0 : Real)) (l := 𝓝 (0 : Real)) (l' := 𝓝 (0 : Real))
      (lt := 𝓝 (0 : Real)) (f := f) (c := c)
      hfm hf
      (u := fun _ : Real => (0 : Real)) (v := fun t : Real => t)
      tendsto_const_nhds continuousAt_id
  have hclean := hraw.congr_right (g₂ := fun t : Real => t) (by
    intro t
    simp)
  simpa using hclean

/--
Zero-slope specialization of the a.e. FTC estimate.
-/
theorem intervalIntegral_integral_isLittleO_of_tendsto_ae_zero_nhds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]
    {f : Real -> E}
    (hfm : StronglyMeasurableAtFilter f (𝓝 (0 : Real)) volume)
    (hf : Filter.Tendsto f
      (𝓝 (0 : Real) ⊓ MeasureTheory.ae volume) (𝓝 (0 : E))) :
    (fun t : Real => ∫ s in (0 : Real)..t, f s)
      =o[𝓝 (0 : Real)] (fun t : Real => t) := by
  simpa using
    (intervalIntegral_integral_sub_linear_isLittleO_of_tendsto_ae_nhds
      (f := f) (c := (0 : E)) hfm hf)

/--
FTC for an absolutely continuous one-dimensional function when the derivative
is supplied as an a.e. `HasDerivAt` field.

This is the source proof's line-restriction identity in a reusable form:
absolute continuity identifies the increment with the integral of the a.e.
derivative field.
-/
theorem AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt
    {F g : Real -> Real} {a b : Real}
    (hF : AbsolutelyContinuousOnInterval F a b)
    (hg : ∀ᵐ x ∂volume, x ∈ Set.uIcc a b -> HasDerivAt F (g x) x) :
    (∫ x in a..b, g x) = F b - F a := by
  have hderivEq : ∀ᵐ x ∂volume, x ∈ Set.uIoc a b -> deriv F x = g x := by
    filter_upwards [hg] with x hx hxI
    exact (hx (Set.uIoc_subset_uIcc hxI)).deriv
  calc
    (∫ x in a..b, g x) = ∫ x in a..b, deriv F x := by
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hderivEq] with x hx hxI
      exact (hx hxI).symm
    _ = F b - F a := hF.integral_deriv_eq_sub

/--
First-order little-oh consequence of the source proof's a.e. line-integration
step.

If a line restriction is absolutely continuous on all sufficiently small
intervals from `0` to `t`, has a.e. derivative field `g`, and `g` has an a.e.
limit `c` at `0`, then the line restriction has first-order expansion with
slope `c`.
-/
theorem absolutelyContinuous_sub_linear_isLittleO_of_ae_hasDerivAt_tendsto_ae_nhds
    {F g : Real -> Real} {c : Real}
    (hAC : ∀ᶠ t in 𝓝 (0 : Real), AbsolutelyContinuousOnInterval F 0 t)
    (hderiv : ∀ᵐ s ∂volume, HasDerivAt F (g s) s)
    (hgm : StronglyMeasurableAtFilter g (𝓝 (0 : Real)) volume)
    (hg : Filter.Tendsto g
      (𝓝 (0 : Real) ⊓ MeasureTheory.ae volume) (𝓝 c)) :
    (fun t : Real => (F t - F 0) - t • c)
      =o[𝓝 (0 : Real)] (fun t : Real => t) := by
  have hint : (fun t : Real => (∫ s in (0 : Real)..t, g s) - t • c)
      =o[𝓝 (0 : Real)] (fun t : Real => t) :=
    intervalIntegral_integral_sub_linear_isLittleO_of_tendsto_ae_nhds hgm hg
  have heq :
      (fun t : Real => (∫ s in (0 : Real)..t, g s) - t • c)
        =ᶠ[𝓝 (0 : Real)]
      (fun t : Real => (F t - F 0) - t • c) := by
    filter_upwards [hAC] with t ht
    have hftc : (∫ s in (0 : Real)..t, g s) = F t - F 0 := by
      refine
        AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt ht ?_
      filter_upwards [hderiv] with x hx _hxmem
      exact hx
    rw [hftc]
  exact hint.congr' heq Filter.EventuallyEq.rfl

/--
Points in the unordered interval from `0` to `t` have norm at most `‖t‖`.

This elementary estimate is the geometric input that turns a pointwise
`o(s)` derivative-error bound into a uniform bound on small line segments.
-/
theorem norm_le_norm_right_of_mem_uIoc_zero
    {s t : Real} (hs : s ∈ Set.uIoc (0 : Real) t) :
    ‖s‖ ≤ ‖t‖ := by
  rcases Set.mem_uIoc.mp hs with ⟨h0s, hst⟩ | ⟨hts, hs0⟩
  · have h0t : 0 ≤ t := (lt_of_lt_of_le h0s hst).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0s.le,
      abs_of_nonneg h0t]
    exact hst
  · have ht0 : t ≤ 0 := (lt_of_lt_of_le hts hs0).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonpos hs0,
      abs_of_nonpos ht0]
    linarith

/--
Uniform small-segment form of a one-dimensional `o(id)` bound.

If `g(s) = o(s)` at `0`, then for every `c > 0` and all sufficiently small
endpoints `t`, the bound `‖g s‖ ≤ c * ‖t‖` holds throughout the unordered
interval `Ι 0 t`.
-/
theorem isLittleO_id_uniform_uIoc_bound_nhds
    {g : Real -> Real}
    (hg : g =o[𝓝 (0 : Real)] (fun s : Real => s)) :
    ∀ c > 0, ∀ᶠ t in 𝓝 (0 : Real),
      ∀ s ∈ Set.uIoc (0 : Real) t, ‖g s‖ ≤ c * ‖t‖ := by
  intro c hc
  have hgsmall : ∀ᶠ s in 𝓝 (0 : Real), ‖g s‖ ≤ c * ‖s‖ :=
    hg.bound hc
  rcases Metric.nhds_basis_closedBall.eventually_iff.mp hgsmall with
    ⟨δ, hδ, hδbound⟩
  filter_upwards [Metric.closedBall_mem_nhds (0 : Real) hδ] with t ht s hs
  have hsNorm : ‖s‖ ≤ ‖t‖ :=
    norm_le_norm_right_of_mem_uIoc_zero hs
  have hsδ : s ∈ Metric.closedBall (0 : Real) δ := by
    rw [Metric.mem_closedBall, dist_zero_right]
    have htδ : ‖t‖ ≤ δ := by
      simpa [Metric.mem_closedBall, dist_zero_right] using ht
    exact hsNorm.trans htδ
  exact (hδbound hsδ).trans (mul_le_mul_of_nonneg_left hsNorm hc.le)

/--
Quadratic little-oh consequence of the source proof's a.e. line-integration
step.

If a line restriction is absolutely continuous on all sufficiently small
intervals from `0` to `t`, has a.e. derivative field `g`, and the derivative
error is uniformly bounded by `c * ‖t‖` on the unordered interval from `0` to
`t` for every small `c`, then the line increment is `o(t²)`.
-/
theorem absolutelyContinuous_sub_const_isLittleO_sq_of_ae_hasDerivAt_bound
    {F g : Real -> Real}
    (hAC : ∀ᶠ t in 𝓝 (0 : Real), AbsolutelyContinuousOnInterval F 0 t)
    (hderiv : ∀ᵐ s ∂volume, HasDerivAt F (g s) s)
    (hbound :
      ∀ c > 0, ∀ᶠ t in 𝓝 (0 : Real),
        ∀ s ∈ Set.uIoc (0 : Real) t, ‖g s‖ ≤ c * ‖t‖) :
    (fun t : Real => F t - F 0)
      =o[𝓝 (0 : Real)] (fun t : Real => t ^ 2) := by
  refine Asymptotics.IsLittleO.of_bound ?_
  intro c hc
  filter_upwards [hAC, hbound c hc] with t ht htb
  have hftc : (∫ s in (0 : Real)..t, g s) = F t - F 0 := by
    refine
      AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt ht ?_
    filter_upwards [hderiv] with x hx _hxmem
    exact hx
  have hnormInt :
      ‖∫ s in (0 : Real)..t, g s‖ ≤ (c * ‖t‖) * |t - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : Real)) (b := t) (C := c * ‖t‖)
      (f := fun s : Real => g s) ?_
    intro s hs
    exact htb s hs
  calc
    ‖F t - F 0‖ = ‖∫ s in (0 : Real)..t, g s‖ := by rw [hftc]
    _ ≤ (c * ‖t‖) * |t - 0| := hnormInt
    _ = c * ‖t ^ 2‖ := by
      rw [sub_zero]
      calc
        (c * ‖t‖) * |t| = (c * ‖t‖) * ‖t‖ := by
          simp [Real.norm_eq_abs]
        _ = c * (‖t‖ ^ 2) := by ring
        _ = c * ‖t ^ 2‖ := by
          rw [norm_pow]

/--
Direct quadratic little-oh consequence of the a.e. FTC line-integration step.

If a line restriction is absolutely continuous on sufficiently small intervals,
has a.e. derivative field `g`, and `g(t) = o(t)` at `0`, then the line
increment is `o(t²)`.
-/
theorem absolutelyContinuous_sub_const_isLittleO_sq_of_ae_hasDerivAt_isLittleO
    {F g : Real -> Real}
    (hAC : ∀ᶠ t in 𝓝 (0 : Real), AbsolutelyContinuousOnInterval F 0 t)
    (hderiv : ∀ᵐ s ∂volume, HasDerivAt F (g s) s)
    (hg : g =o[𝓝 (0 : Real)] (fun s : Real => s)) :
    (fun t : Real => F t - F 0)
      =o[𝓝 (0 : Real)] (fun t : Real => t ^ 2) :=
  absolutelyContinuous_sub_const_isLittleO_sq_of_ae_hasDerivAt_bound
    hAC hderiv (isLittleO_id_uniform_uIoc_bound_nhds hg)

/--
A Lipschitz function restricted to an affine line segment is absolutely
continuous.

This is the basic regularity input for the source proof's segment integration
step: local Lipschitz control in the ambient coordinate space gives absolute
continuity of one-dimensional restrictions.
-/
theorem LipschitzOnWith.absolutelyContinuousOnInterval_comp_segment
    {F : Point n -> Real} {x0 v : Point n} {K : NNReal}
    (hF : LipschitzOnWith K F Set.univ) :
    AbsolutelyContinuousOnInterval (fun t : Real => F (x0 + t • v)) 0 1 := by
  have hLip :
      LipschitzOnWith (Real.toNNReal ((K : Real) * ‖v‖))
        (fun t : Real => F (x0 + t • v)) (Set.uIcc (0 : Real) 1) := by
    refine LipschitzOnWith.of_dist_le' ?_
    intro s _hs t _ht
    have hFdist :
        dist (F (x0 + s • v)) (F (x0 + t • v)) ≤
          (K : Real) * dist (x0 + s • v) (x0 + t • v) := by
      simpa using hF.dist_le_mul
        (x0 + s • v) trivial (x0 + t • v) trivial
    have hline :
        dist (x0 + s • v) (x0 + t • v) = ‖v‖ * dist s t := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x0 + s • v) - (x0 + t • v) = (s - t) • v := by
        module
      rw [hsub, norm_smul, Real.norm_eq_abs]
      ring
    calc
      dist (F (x0 + s • v)) (F (x0 + t • v))
          ≤ (K : Real) * dist (x0 + s • v) (x0 + t • v) := hFdist
      _ = ((K : Real) * ‖v‖) * dist s t := by
        rw [hline]
        ring
  exact hLip.absolutelyContinuousOnInterval

/--
A local Lipschitz bound on a set containing the segment gives absolute
continuity of the corresponding line restriction.
-/
theorem LipschitzOnWith.absolutelyContinuousOnInterval_comp_segment_of_subset
    {F : Point n -> Real} {x0 v : Point n} {K : NNReal} {s : Set (Point n)}
    (hF : LipschitzOnWith K F s)
    (hseg : ∀ t ∈ Set.uIcc (0 : Real) 1, x0 + t • v ∈ s) :
    AbsolutelyContinuousOnInterval (fun t : Real => F (x0 + t • v)) 0 1 := by
  have hLip :
      LipschitzOnWith (Real.toNNReal ((K : Real) * ‖v‖))
        (fun t : Real => F (x0 + t • v)) (Set.uIcc (0 : Real) 1) := by
    refine LipschitzOnWith.of_dist_le' ?_
    intro u hu t ht
    have hFdist :
        dist (F (x0 + u • v)) (F (x0 + t • v)) ≤
          (K : Real) * dist (x0 + u • v) (x0 + t • v) := by
      simpa using hF.dist_le_mul
        (x0 + u • v) (hseg u hu) (x0 + t • v) (hseg t ht)
    have hline :
        dist (x0 + u • v) (x0 + t • v) = ‖v‖ * dist u t := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x0 + u • v) - (x0 + t • v) = (u - t) • v := by
        module
      rw [hsub, norm_smul, Real.norm_eq_abs]
      ring
    calc
      dist (F (x0 + u • v)) (F (x0 + t • v))
          ≤ (K : Real) * dist (x0 + u • v) (x0 + t • v) := hFdist
      _ = ((K : Real) * ‖v‖) * dist u t := by
        rw [hline]
        ring
  exact hLip.absolutelyContinuousOnInterval

/--
The Taylor residual of a globally Lipschitz function is absolutely continuous
on affine line segments.

The nonlinear part is supplied by the Lipschitz restriction lemma above; the
quadratic Taylor model is `C¹` after restricting to a line, hence absolutely
continuous.
-/
theorem LipschitzOnWith.absolutelyContinuousOnInterval_frechetResidual_comp_segment
    {F : Point n -> Real} {x0 v : Point n} {K : NNReal}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hF : LipschitzOnWith K F Set.univ) :
    AbsolutelyContinuousOnInterval
      (fun t : Real =>
        F (x0 + t • v) -
          frechetSecondOrderModel x0 (F x0) Dφ D2φ (x0 + t • v))
      0 1 := by
  exact
    (LipschitzOnWith.absolutelyContinuousOnInterval_comp_segment
      (x0 := x0) (v := v) hF).sub
      (by
        apply ContDiffOn.absolutelyContinuousOnInterval
        unfold frechetSecondOrderModel
        fun_prop)

/--
Eventually-nearby segment form of
`LipschitzOnWith.absolutelyContinuousOnInterval_frechetResidual_comp_segment`.
-/
theorem LipschitzOnWith.eventually_absolutelyContinuousOnInterval_frechetResidual_segment
    {F : Point n -> Real} {x0 : Point n} {K : NNReal}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hF : LipschitzOnWith K F Set.univ) :
    ∀ᶠ z in 𝓝 x0,
      AbsolutelyContinuousOnInterval
        (fun t : Real =>
          F (x0 + t • (z - x0)) -
            frechetSecondOrderModel x0 (F x0) Dφ D2φ
              (x0 + t • (z - x0)))
        0 1 :=
  Filter.Eventually.of_forall fun z =>
    LipschitzOnWith.absolutelyContinuousOnInterval_frechetResidual_comp_segment
      (x0 := x0) (v := z - x0) hF

/--
Local Lipschitz control near the base point gives eventual absolute
continuity of Taylor residuals on nearby segments.
-/
theorem LipschitzOnWith.eventually_ac_frechetResidual_segment_of_mem_nhds
    {F : Point n -> Real} {x0 : Point n} {K : NNReal} {s : Set (Point n)}
    {Dφ : Point n →L[Real] Real}
    {D2φ : Point n →L[Real] Point n →L[Real] Real}
    (hF : LipschitzOnWith K F s)
    (hs : s ∈ 𝓝 x0) :
    ∀ᶠ z in 𝓝 x0,
      AbsolutelyContinuousOnInterval
        (fun t : Real =>
          F (x0 + t • (z - x0)) -
            frechetSecondOrderModel x0 (F x0) Dφ D2φ
              (x0 + t • (z - x0)))
        0 1 := by
  rcases Metric.nhds_basis_closedBall.mem_iff.mp hs with
    ⟨δ, hδ, hclosed⟩
  filter_upwards [Metric.closedBall_mem_nhds x0 hδ] with z hz
  have hseg :
      ∀ t ∈ Set.uIcc (0 : Real) 1, x0 + t • (z - x0) ∈ s := by
    intro t ht
    have ht01 : 0 ≤ t ∧ t ≤ 1 := by
      rcases Set.mem_uIcc.mp ht with h | h
      · exact ⟨h.1, h.2⟩
      · linarith
    refine hclosed ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hseg_sub : (x0 + t • (z - x0)) - x0 = t • (z - x0) := by
      simp
    rw [hseg_sub, norm_smul]
    have ht_norm : ‖t‖ ≤ (1 : Real) := by
      rw [Real.norm_of_nonneg ht01.1]
      exact ht01.2
    have hzδ : ‖z - x0‖ ≤ δ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hz
    calc
      ‖t‖ * ‖z - x0‖ ≤ 1 * ‖z - x0‖ :=
        mul_le_mul_of_nonneg_right ht_norm (norm_nonneg _)
      _ = ‖z - x0‖ := by simp
      _ ≤ δ := hzδ
  exact
    (LipschitzOnWith.absolutelyContinuousOnInterval_comp_segment_of_subset
      (x0 := x0) (v := z - x0) hF hseg).sub
      (by
        apply ContDiffOn.absolutelyContinuousOnInterval
        unfold frechetSecondOrderModel
        fun_prop)

end ViscositySolns
