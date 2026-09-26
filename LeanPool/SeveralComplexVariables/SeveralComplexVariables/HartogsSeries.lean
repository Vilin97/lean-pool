/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsDomain
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsLaurent

/-!
# Hartogs–Taylor and Hartogs–Laurent expansions

Functions take values in a complex Banach space, and the base is a finite-dimensional complex
normed space (possibly zero dimensional). Taylor coefficients are the normalized iterated
derivatives in the fiber variable at zero. On an open complete Hartogs set these coefficients
are holomorphic on the base and the expansion converges locally uniformly.

The Laurent theorem assumes Hartogs symmetry and, separately, preconnected fibers. Its
coefficients are single-valued holomorphic functions on the projected base. Without the fiber
assumption, coefficients need only be locally functions of the base variable; connectedness of
the total set does not repair that issue. Thus we make explicit the hypothesis needed for the
global-base interpretation of [Range][Range1986]'s Exercise E.1.10. Negative coefficients vanish
on fibers containing zero. Integer powers in Lean are totalized at zero, so this vanishing is
recorded as part of the Laurent statement.

`HasSumLocallyUniformlyOn` uses finite subsets of the index type, including for the
integer-indexed Laurent series. It gives unconditional pointwise convergence and uniform
convergence on compact subsets. We use `ℤ → E → F`, rather than the algebraic `LaurentSeries`,
whose support must be bounded below and therefore excludes general essential singularities.
Neither theorem needs the base or the total set to be connected or nonempty. The Taylor theorem
is proved by fiber differentiation and uniform Cauchy estimates on local product neighborhoods.
The Laurent theorem uses the one-variable annular Cauchy formula, holomorphic dependence of
circle coefficients, and geometric bounds from `LaurentSeries.OneVariable` and `HartogsLaurent`.
Neither expansion depends on the multivariable Laurent theorem.

References: [Shabat][Shabat1991] (1991), I §3.8, Theorem 1 and the Hartogs–Laurent expansion,
pp. 34–36; [Range][Range1986] (1986), Chapter I, E.1.9–E.1.10.

## Main definitions

* `hartogsTaylorCoeff`: The Taylor coefficient in the distinguished fiber coordinate, centered at
  zero.

## Main results

* `differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn`: **Hartogs–Taylor expansion.**
  Holomorphic functions on open complete Hartogs sets have holomorphic Taylor coefficients on the
  base and a locally uniformly convergent fiber expansion.
* `exists_hartogsLaurent_expansion`: **Hartogs–Laurent expansion with connected nonempty fibers.**
  The coefficients are holomorphic on the whole projected base, the series converges locally
  uniformly, and negative coefficients vanish on every fiber containing zero.

## References

* [R. M. Range, *Holomorphic Functions and Integral Representations in Several Complex
  Variables*][Range1986]
* [B. V. Shabat, *Introduction to Complex Analysis, Part II: Functions of Several
  Variables*][Shabat1991]
-/

public noncomputable section

open Set Filter Metric
open scoped Topology

namespace SeveralComplexVariables

variable {E F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Taylor coefficient in the distinguished fiber coordinate, centered at zero. -/
@[expose] def hartogsTaylorCoeff (f : E × ℂ → F) (k : ℕ) (z : E) : F :=
  ((k.factorial : ℂ)⁻¹) • iteratedDeriv k (fun w => f (z, w)) 0

/-- The constant coefficient is restriction to the zero section. -/
@[simp] theorem hartogsTaylorCoeff_zero (f : E × ℂ → F) (z : E) :
    hartogsTaylorCoeff f 0 z = f (z, 0) := by
  simp [hartogsTaylorCoeff]

variable [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [CompleteSpace F] {U : Set (E × ℂ)} {f : E × ℂ → F}

omit [FiniteDimensional ℂ E] in
/-- All derivatives in the fiber variable remain jointly analytic on an open set. -/
theorem analyticOnNhd_iteratedDeriv_fiber (hU : IsOpen U) (hf : AnalyticOnNhd ℂ f U)
    (k : ℕ) : AnalyticOnNhd ℂ (fun p : E × ℂ =>
      iteratedDeriv k (fun w => f (p.1, w)) p.2) U := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    let g : E × ℂ → F := fun p => iteratedDeriv k (fun w => f (p.1, w)) p.2
    intro p hp
    have hA : AnalyticAt ℂ (fun q => fderiv ℂ g q (0, 1)) p := by
      exact ((ContinuousLinearMap.apply ℂ F (0, 1)).analyticAt _).comp (ih p hp).fderiv
    apply hA.congr
    filter_upwards [hU.eventually_mem hp] with q hq
    have hs : HasDerivAt (fun w : ℂ => (q.1, w)) (0, 1) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    have hd := (ih q hq).differentiableAt.hasFDerivAt.comp_hasDerivAt q.2 hs
    simpa only [iteratedDeriv_succ, g, Function.comp_def] using hd.deriv.symm

omit [NormedSpace ℂ E] [FiniteDimensional ℂ E] in
/-- Around each point of an open complete Hartogs set there is a product neighborhood whose closed
fiber disc has strictly larger radius than the given fiber coordinate. -/
theorem IsCompleteHartogs.exists_product_closedBall (hH : IsCompleteHartogs U)
    (hU : IsOpen U) {p : E × ℂ} (hp : p ∈ U) :
    ∃ δ R : ℝ, 0 < δ ∧ ‖p.2‖ < R ∧
      ball p.1 δ ×ˢ closedBall (0 : ℂ) R ⊆ U := by
  have hq : (p.1, (‖p.2‖ : ℂ)) ∈ U :=
    hH hp (by simp)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ hq
  refine ⟨ε / 2, ‖p.2‖ + ε / 2, half_pos hε, by linarith, ?_⟩
  rintro ⟨z, w⟩ ⟨hz, hw⟩
  have hR : 0 ≤ ‖p.2‖ + ε / 2 := by positivity
  apply hH (hball (show (z, ((‖p.2‖ + ε / 2 : ℝ) : ℂ)) ∈
      ball (p.1, (‖p.2‖ : ℂ)) ε from ?_))
  · simpa only [mem_closedBall, dist_zero_right, Complex.norm_of_nonneg hR] using hw
  · rw [mem_ball, Prod.dist_eq, max_lt_iff]
    refine ⟨(mem_ball.mp hz).trans (half_lt_self hε), ?_⟩
    rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real]
    simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_pos (half_pos hε)]
    exact half_lt_self hε

/-- **Hartogs–Taylor expansion.** Holomorphic functions on open complete Hartogs sets
have holomorphic Taylor coefficients on the base and a locally uniformly convergent
fiber expansion. Local product neighborhoods and Cauchy estimates give a summable
geometric majorant; the one-variable Taylor theorem identifies the sum. -/
theorem differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn (hU : IsOpen U)
    (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) :
    (∀ k, DifferentiableOn ℂ (hartogsTaylorCoeff f k) (hartogsBase U)) ∧
      HasSumLocallyUniformlyOn
        (fun k (p : E × ℂ) => p.2 ^ k • hartogsTaylorCoeff f k p.1) f U := by
  let : ProperSpace E := FiniteDimensional.proper ℂ E
  have hA := hf.analyticOnNhd_of_finiteDimensional hU
  constructor
  · intro k z hz
    have ha := (analyticOnNhd_iteratedDeriv_fiber hU hA k) (z, 0) (hH.zero_mem_fiber hz)
    have hc : AnalyticAt ℂ (fun z => iteratedDeriv k (fun w => f (z, w)) 0) z :=
      ha.comp (f := fun z : E => (z, (0 : ℂ))) (analyticAt_id.prod analyticAt_const)
    exact (analyticAt_const.smul hc).differentiableAt.differentiableWithinAt
  · apply hasSumLocallyUniformlyOn_of_of_forall_exists_nhds
    intro p hp
    obtain ⟨δ, R, hδ, hpR, hsub⟩ := hH.exists_product_closedBall hU hp
    have hR : 0 < R := (norm_nonneg _).trans_lt hpR
    let r := (‖p.2‖ + R) / 2
    have hr : 0 < r := by dsimp [r]; positivity
    have hrR : r < R := by dsimp [r]; linarith
    have hpr : ‖p.2‖ < r := by dsimp [r]; linarith
    let N := ball p.1 (δ / 2) ×ˢ ball (0 : ℂ) r
    let K := closedBall p.1 (δ / 2) ×ˢ closedBall (0 : ℂ) R
    have hKU : K ⊆ U :=
      (Set.prod_mono (closedBall_subset_ball (half_lt_self hδ)) Subset.rfl).trans hsub
    have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
    obtain ⟨M, hM⟩ := hK.bddAbove_image (hf.continuousOn.mono hKU).norm
    let C := max M 0
    have hC : 0 ≤ C := le_max_right _ _
    have hbound : ∀ q ∈ K, ‖f q‖ ≤ C :=
      fun q hq => (hM (mem_image_of_mem _ hq)).trans (le_max_left _ _)
    have hslice (z : E) (hz : z ∈ closedBall p.1 (δ / 2)) :
        DifferentiableOn ℂ (fun w => f (z, w)) (closedBall 0 R) := by
      apply hf.comp ((differentiable_const z).prodMk differentiable_id).differentiableOn
      intro w hw
      exact hKU ⟨hz, hw⟩
    have hsum (q : E × ℂ) (hq : q ∈ N) :
        HasSum (fun k => q.2 ^ k • hartogsTaylorCoeff f k q.1) (f q) := by
      have hs := Complex.hasSum_taylorSeries_on_ball
        ((hslice q.1 (ball_subset_closedBall hq.1)).mono ball_subset_closedBall)
        ((ball_subset_ball hrR.le) hq.2)
      convert hs using 1
      funext k
      simp only [sub_zero, hartogsTaylorCoeff]
      exact smul_comm _ _ _
    have hterm (k : ℕ) (q : E × ℂ) (hq : q ∈ N) :
        ‖q.2 ^ k • hartogsTaylorCoeff f k q.1‖ ≤ C * (r / R) ^ k := by
      have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hR
        ((hslice q.1 (ball_subset_closedBall hq.1)).mono
          closure_ball_subset_closedBall).diffContOnCl
        (fun w hw => hbound (q.1, w) ⟨ball_subset_closedBall hq.1, sphere_subset_closedBall hw⟩)
      have hfact : (k.factorial : ℝ) ≠ 0 := by positivity
      have hc : ‖hartogsTaylorCoeff f k q.1‖ ≤ C / R ^ k := by
        rw [hartogsTaylorCoeff, norm_smul, norm_inv, Complex.norm_natCast]
        calc
          (k.factorial : ℝ)⁻¹ * ‖iteratedDeriv k (fun w => f (q.1, w)) 0‖ ≤
              (k.factorial : ℝ)⁻¹ * (k.factorial * C / R ^ k) :=
            mul_le_mul_of_nonneg_left hd (by positivity)
          _ = C / R ^ k := by field_simp
      rw [norm_smul, norm_pow]
      calc
        ‖q.2‖ ^ k * ‖hartogsTaylorCoeff f k q.1‖ ≤ r ^ k * (C / R ^ k) := by
          gcongr
          exact (mem_ball_zero_iff.mp hq.2).le
        _ = C * (r / R) ^ k := by simp only [div_eq_mul_inv, mul_pow, inv_pow]; ac_rfl
    have hsummable : Summable (fun k : ℕ => C * (r / R) ^ k) :=
      (summable_geometric_of_lt_one (div_nonneg hr.le hR.le) ((div_lt_one hR).mpr hrR)).mul_left C
    refine ⟨N, mem_nhdsWithin_of_mem_nhds ((isOpen_ball.prod isOpen_ball).mem_nhds
      ⟨mem_ball_self (half_pos hδ), mem_ball_zero_iff.mpr hpr⟩), ?_⟩
    apply hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr
    exact (tendstoUniformlyOn_tsum hsummable hterm).congr_right
      (fun q hq => (hsum q hq).tsum_eq)

/-- The Hartogs–Taylor expansion converges locally uniformly on an open complete Hartogs set. -/
theorem hasSumLocallyUniformlyOn_hartogsTaylor (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) :
    HasSumLocallyUniformlyOn
      (fun k (p : E × ℂ) => p.2 ^ k • hartogsTaylorCoeff f k p.1) f U :=
  (differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn hU hH hf).2

/-- The canonical Hartogs–Taylor coefficients are holomorphic on the projected base. This follows
from the Taylor expansion theorem. -/
theorem differentiableOn_hartogsTaylorCoeff (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) (k : ℕ) :
    DifferentiableOn ℂ (hartogsTaylorCoeff f k) (hartogsBase U) :=
  (differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn hU hH hf).1 k

/-- The Hartogs–Taylor series sums to the function at every point of the set. This follows from the
Taylor expansion theorem. -/
theorem hasSum_hartogsTaylor (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) {p : E × ℂ} (hp : p ∈ U) :
    HasSum (fun k => p.2 ^ k • hartogsTaylorCoeff f k p.1) (f p) :=
  (differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn hU hH hf).2.hasSum hp

/-- Hartogs–Taylor sums converge uniformly on each compact subset of the set. This follows from the
Taylor expansion theorem. -/
theorem tendstoUniformlyOn_hartogsTaylor (hU : IsOpen U) (hH : IsCompleteHartogs U)
    (hf : DifferentiableOn ℂ f U) {K : Set (E × ℂ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    TendstoUniformlyOn
      (fun s : Finset ℕ => fun p : E × ℂ => ∑ k ∈ s, p.2 ^ k • hartogsTaylorCoeff f k p.1)
      f Filter.atTop K :=
  (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
    ((differentiableOn_hartogsTaylorCoeff_and_hasSumLocallyUniformlyOn hU hH hf).2.mono hKU)

/-- **Hartogs–Laurent expansion with connected nonempty fibers.** The coefficients are
holomorphic on the whole projected base, the series converges locally uniformly, and
negative coefficients vanish on every fiber containing zero. The one-variable Laurent
expansion follows from Cauchy’s formula on an annulus; fixed-circle integrals
give local holomorphic coefficients and geometric bounds give local uniform convergence.
The independent fiber hypothesis is essential for this global-base formulation. -/
theorem exists_hartogsLaurent_expansion (hU : IsOpen U) (hH : IsHartogs U)
    (hfib : HasPreconnectedFibers U) (hf : DifferentiableOn ℂ f U) :
    ∃ a : ℤ → E → F,
      (∀ k, DifferentiableOn ℂ (a k) (hartogsBase U)) ∧
      (∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0) ∧
      HasSumLocallyUniformlyOn (fun k (p : E × ℂ) => p.2 ^ k • a k p.1) f U := by
  classical
  have hA := hf.analyticOnNhd_of_finiteDimensional hU
  have hrad : ∀ z : E, ∃ r : ℝ, 0 < r ∧ (z ∈ hartogsBase U → (z, (r : ℂ)) ∈ U) := by
    intro z
    by_cases hz : z ∈ hartogsBase U
    · obtain ⟨w, hw⟩ := mem_hartogsBase_iff.mp hz
      obtain ⟨r, hwr, hrU⟩ := hH.exists_larger_radius hU hw
      exact ⟨r, (norm_nonneg _).trans_lt hwr, fun _ => hrU⟩
    · exact ⟨1, zero_lt_one, fun h => (hz h).elim⟩
  choose R hR hRU using hrad
  let a : ℤ → E → F := fun k z => circleLaurentCoeff (fun w => f (z, w)) (R z) k
  have hLaurent (z : E) (hz : z ∈ hartogsBase U) := circleLaurent_expansion
    (isOpen_hartogsFiber hU z) ⟨mem_hartogsBase_iff.mp hz, hfib z⟩
    (fun w hw v hv => hH hw hv)
    (fun w hw => (hA (z, w) hw).comp (analyticAt_const.prod analyticAt_id))
    (hR z) (hRU z hz)
  have hcoeff (z : E) (r : ℝ) (hr : 0 < r) (hzr : (z, (r : ℂ)) ∈ U) (k : ℤ) :
      a k z = circleLaurentCoeff (fun w => f (z, w)) r k := by
    exact (congrFun ((hLaurent z ⟨(z, (r : ℂ)), hzr, rfl⟩).2.1 r hr hzr) k).symm
  have hzero (z : E) (hz : (z, 0) ∈ U) (k : ℤ) (hk : k < 0) : a k z = 0 :=
    (hLaurent z ⟨(z, 0), hz, rfl⟩).2.2 hz k hk
  have hsum (p : E × ℂ) (hp : p ∈ U) :
      HasSum (fun k : ℤ => p.2 ^ k • a k p.1) (f p) :=
    (hLaurent p.1 ⟨p, hp, rfl⟩).1 p.2 hp
  refine ⟨a, ?_, hzero, hasSumLocallyUniformlyOn_hartogsLaurent hH hU hf.continuousOn
    hcoeff hzero hsum⟩
  intro k z hz
  obtain ⟨δ, _, hδ, _, hc⟩ := hH.exists_circle_bound hU hf.continuousOn (hR z) (hRU z hz)
  have hcoeffA := analyticOnNhd_circleLaurentCoeff isOpen_ball hA (hR z)
    (fun y hy w hw => (hc y hy w hw).1) k
  have heq : (fun y => circleLaurentCoeff (fun w => f (y, w)) (R z) k) =ᶠ[𝓝 z] a k := by
    filter_upwards [ball_mem_nhds z hδ] with y hy
    exact (hcoeff y (R z) (hR z) (hc y hy (R z : ℂ) (by simp [(hR z).le])).1 k).symm
  exact ((hcoeffA z (mem_ball_self hδ)).congr heq).differentiableAt.differentiableWithinAt

/-- A pointwise version of the Hartogs–Laurent expansion, retaining global holomorphic coefficients
and their vanishing at the zero section. -/
theorem exists_hasSum_hartogsLaurent (hU : IsOpen U) (hH : IsHartogs U)
    (hfib : HasPreconnectedFibers U) (hf : DifferentiableOn ℂ f U) :
    ∃ a : ℤ → E → F,
      (∀ k, DifferentiableOn ℂ (a k) (hartogsBase U)) ∧
      (∀ z, (z, 0) ∈ U → ∀ k : ℤ, k < 0 → a k z = 0) ∧
      ∀ p ∈ U, HasSum (fun k => p.2 ^ k • a k p.1) (f p) := by
  obtain ⟨a, ha, hzero, hsum⟩ := exists_hartogsLaurent_expansion hU hH hfib hf
  exact ⟨a, ha, hzero, fun _ hp => hsum.hasSum hp⟩

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
