/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Supporting normals of smooth convex Jordan domains

At a regular point of a smooth convex boundary, the tangent line is a
supporting line.  Its two possible normal orientations are distinguished by
the sign at any one point in the open carrier.  This file formalizes that
principle for the complex normal used by the Crouzeix--Palencia double-layer
kernel.

The proof obtains an abstract supporting functional from Hahn--Banach.  Its
composition with the boundary trace has a maximum at the chosen parameter,
so the functional annihilates the nonzero tangent.  In the real plane, two
linear functionals annihilating the same nonzero tangent are proportional.
The sign at one carrier point makes the proportionality factor positive and
therefore fixes the normal sign on the full frontier.

## Main declarations

* `SmoothJordanDomain.carrier_nonempty` -- every represented domain has a
  nonempty carrier;
* `SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier`
  -- weak support on the closure and strict support in the open carrier;
* `SmoothJordanDomain.canonicalNormal_support_all_of_support_at` -- the
  canonical-normal sign at one carrier point and one parameter fixes the
  orientation globally;
* `SmoothJordanDomain.frontier_support_of_support_at_mem_carrier` -- the
  oriented normal sign at one carrier point propagates to the entire
  frontier;
* `SmoothJordanDomain.reverseOrientation` -- reversal of the boundary trace
  without changing the represented carrier;
* `SmoothJordanDomain.canonicalOrientation` -- a canonical choice between a
  trace and its reversal that has the supporting-normal sign.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothApprox
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.Order.IntermediateValue

open Complex Set
open scoped Real

/-- A smooth Jordan domain represented by a regular boundary trace has a
nonempty open carrier.  Otherwise its frontier would be empty, contradicting
the nonempty range of the trace. -/
theorem SmoothJordanDomain.carrier_nonempty
    (Omega : SmoothJordanDomain) : Omega.carrier.Nonempty := by
  have hfrontier : (frontier Omega.carrier).Nonempty :=
    ⟨Omega.boundaryParam 0, by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self 0⟩
  by_contra hnot
  have hempty : Omega.carrier = ∅ := not_nonempty_iff_eq_empty.mp hnot
  rw [hempty, frontier_empty] at hfrontier
  exact hfrontier.ne_empty rfl

private theorem realCLM_apply_eq_re_im
    (f : ℂ →L[ℝ] ℝ) (z : ℂ) :
    f z = z.re * f 1 + z.im * f I := by
  conv_lhs => rw [← Complex.re_add_im z]
  rw [map_add]
  rw [show (z.re : ℂ) = z.re • (1 : ℂ) by
      rw [Complex.real_smul, mul_one],
    show z.im * I = z.im • I by
      rw [Complex.real_smul],
    map_smul, map_smul]
  simp only [smul_eq_mul]

/-- At a regular trace point of a smooth convex Jordan domain, the canonical
complex normal is nonpositive on the closed carrier and strictly negative on
the open carrier as soon as its nonpositive sign is known at one carrier
point. -/
theorem
    SmoothJordanDomain.closure_support_and_carrier_strict_of_support_at_mem_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    (∀ z ∈ closure Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re ≤ 0) ∧
    ∀ z ∈ Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (z - Omega.boundaryParam t)).re < 0 := by
  let gamma := Omega.boundaryParam
  let D := deriv gamma t
  have hgammaFrontier : gamma t ∈ frontier Omega.carrier := by
    rw [← Omega.boundaryParam_range]
    exact mem_range_self t
  have hgammaNot : gamma t ∉ Omega.carrier := by
    intro hmem
    have hempty : gamma t ∈ (∅ : Set ℂ) := by
      rw [← Omega.isOpen_carrier.inter_frontier_eq]
      exact ⟨hmem, hgammaFrontier⟩
    exact hempty
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    Omega.strictConvex_carrier.convex Omega.isOpen_carrier hgammaNot
  have hfclosed : IsClosed {z : ℂ | f z ≤ f (gamma t)} :=
    isClosed_le f.continuous continuous_const
  have hfcarrier : Omega.carrier ⊆ {z : ℂ | f z ≤ f (gamma t)} := by
    intro z hz
    exact (hf z hz).le
  have hfclosure : closure Omega.carrier ⊆
      {z : ℂ | f z ≤ f (gamma t)} :=
    closure_minimal hfcarrier hfclosed
  have hfall : ∀ s, f (gamma s) ≤ f (gamma t) := by
    intro s
    exact hfclosure (frontier_subset_closure (by
      rw [← Omega.boundaryParam_range]
      exact mem_range_self s))
  have hlocal : IsLocalMax (f ∘ gamma) t :=
    Filter.Eventually.of_forall hfall
  have hgammaDeriv : HasDerivAt gamma D t :=
    (Omega.boundaryParam_contDiff.differentiable (by norm_num) t).hasDerivAt
  have hcompDeriv := f.hasFDerivAt.comp_hasDerivAt t hgammaDeriv
  have hfD : f D = 0 := by
    rw [← hcompDeriv.deriv]
    exact hlocal.deriv_eq_zero
  let alpha := f 1
  let beta := f I
  let nsq := Complex.normSq D
  let lambda := (D.im * alpha - D.re * beta) / nsq
  have hDcoord : D.re * alpha + D.im * beta = 0 := by
    simpa only [alpha, beta] using
      (realCLM_apply_eq_re_im f D).symm.trans hfD
  have hnsq : nsq ≠ 0 := by
    dsimp only [nsq]
    intro hzero
    exact Omega.boundaryParam_regular t
      (Complex.normSq_eq_zero.mp hzero)
  have halpha : alpha = lambda * D.im := by
    dsimp only [lambda, nsq]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hnsq).2
    dsimp only [nsq]
    rw [Complex.normSq_apply, ← sub_eq_zero]
    calc
      alpha * (D.re * D.re + D.im * D.im) -
          (D.im * alpha - D.re * beta) * D.im =
        D.re * (D.re * alpha + D.im * beta) := by ring
      _ = 0 := by rw [hDcoord, mul_zero]
  have hbeta : beta = lambda * (-D.re) := by
    dsimp only [lambda, nsq]
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hnsq).2
    dsimp only [nsq]
    rw [Complex.normSq_apply, ← sub_eq_zero]
    calc
      beta * (D.re * D.re + D.im * D.im) -
          (D.im * alpha - D.re * beta) * (-D.re) =
        D.im * (D.re * alpha + D.im * beta) := by ring
      _ = 0 := by rw [hDcoord, mul_zero]
  have hf_normal : ∀ z : ℂ,
      f z = lambda *
        ((starRingEnd ℂ) (-I * D) * z).re := by
    intro z
    rw [realCLM_apply_eq_re_im f z]
    change z.re * alpha + z.im * beta = _
    rw [halpha, hbeta]
    simp only [map_mul, map_neg, Complex.conj_I, Complex.mul_re,
      Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.I_re,
      Complex.I_im, Complex.conj_re, Complex.conj_im]
    ring
  have hfcneg : f (c - gamma t) < 0 := by
    have hlt := hf c hc
    rw [map_sub]
    linarith
  have hNcneg :
      ((starRingEnd ℂ) (-I * D) * (c - gamma t)).re < 0 := by
    apply lt_of_le_of_ne hcside
    intro hzero
    rw [hf_normal, hzero, mul_zero] at hfcneg
    exact lt_irrefl 0 hfcneg
  have hlambda : 0 < lambda := by
    rw [hf_normal] at hfcneg
    rcases mul_neg_iff.mp hfcneg with h | h
    · exact h.1
    · exact (not_lt_of_ge hNcneg.le h.2).elim
  constructor
  · intro z hz
    have hfz : f (z - gamma t) ≤ 0 := by
      rw [map_sub]
      have hle := hfclosure hz
      exact sub_nonpos.mpr hle
    rw [hf_normal] at hfz
    nlinarith only [hfz, hlambda]
  · intro z hz
    have hfz : f (z - gamma t) < 0 := by
      rw [map_sub]
      exact sub_neg.mpr (hf z hz)
    rw [hf_normal] at hfz
    nlinarith only [hfz, hlambda]

/-- For a smooth strictly convex Jordan trace, the canonical-normal sign at
one point of the open carrier cannot change along the parameter line.  It is
strict at the carrier point, never vanishes at any parameter, and continuity
then rules out a sign change by the intermediate value theorem. -/
theorem SmoothJordanDomain.canonicalNormal_support_all_of_support_at
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t0 : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t0) *
        (c - Omega.boundaryParam t0)).re ≤ 0) :
    ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0 := by
  let f : ℝ → ℝ := fun t ↦
    ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
      (c - Omega.boundaryParam t)).re
  have hgamma : Continuous Omega.boundaryParam :=
    Omega.boundaryParam_contDiff.continuous
  have hderiv : Continuous (deriv Omega.boundaryParam) :=
    Omega.boundaryParam_contDiff.continuous_deriv (by norm_num)
  have hfcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hfne : ∀ t, f t ≠ 0 := by
    intro t hzero
    have hstrict :=
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (by
          change f t ≤ 0
          exact hzero.le)).2 c hc
    change f t < 0 at hstrict
    exact (ne_of_lt hstrict) hzero
  have hfneg : f t0 < 0 := by
    have hstrict :=
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t0 hcside).2 c hc
    exact hstrict
  intro t
  change f t ≤ 0
  by_contra ht
  have htpos : 0 < f t := lt_of_not_ge ht
  have hzeroMem : 0 ∈ Set.range f :=
    (intermediate_value_univ t0 t hfcont) ⟨hfneg.le, htpos.le⟩
  obtain ⟨u, hu⟩ := hzeroMem
  exact hfne u hu

/-- At a regular trace point of a smooth convex Jordan domain, the canonical
complex normal has a constant oriented sign on the frontier as soon as that
sign is known at one point of the open carrier. -/
theorem SmoothJordanDomain.frontier_support_of_support_at_mem_carrier
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (t : ℝ)
    (hcside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0) :
    ∀ xi ∈ frontier Omega.carrier,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (xi - Omega.boundaryParam t)).re ≤ 0 := by
  intro xi hxi
  exact
    (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
      c hc t hcside).1 xi (frontier_subset_closure hxi)

/-- Reverse the orientation of a smooth Jordan boundary by the affine
reparametrization `t ↦ 2π - t`.  The carrier and all of its geometric
properties are unchanged. -/
noncomputable def SmoothJordanDomain.reverseOrientation
    (Omega : SmoothJordanDomain) : SmoothJordanDomain where
  carrier := Omega.carrier
  isOpen_carrier := Omega.isOpen_carrier
  strictConvex_carrier := Omega.strictConvex_carrier
  boundaryParam := fun t ↦ Omega.boundaryParam (2 * Real.pi - t)
  boundaryParam_periodic := by
    intro t
    calc
      Omega.boundaryParam (2 * Real.pi - (t + 2 * Real.pi)) =
          Omega.boundaryParam (-t) := by
            congr 1
            ring_nf
      _ = Omega.boundaryParam (2 * Real.pi - t) :=
        Omega.boundaryParam_periodic.sub_eq'.symm
  boundaryParam_contDiff :=
    Omega.boundaryParam_contDiff.comp (contDiff_const.sub contDiff_id)
  boundaryParam_range := by
    apply Set.Subset.antisymm
    · rintro z ⟨t, rfl⟩
      rw [← Omega.boundaryParam_range]
      exact mem_range_self (2 * Real.pi - t)
    · intro z hz
      rw [← Omega.boundaryParam_range] at hz
      obtain ⟨u, rfl⟩ := hz
      refine ⟨2 * Real.pi - u, ?_⟩
      ring_nf
  boundaryParam_injOn := by
    intro x hx y hy hxy
    let r : ℝ → ℝ := fun t ↦ if t = 0 then 0 else 2 * Real.pi - t
    have hr_mem : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
        r t ∈ Ico (0 : ℝ) (2 * Real.pi) := by
      intro t ht
      by_cases ht0 : t = 0
      · subst t
        simp only [r, if_pos, mem_Ico, le_refl, true_and]
        positivity
      · have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
        simp only [r, ht0, if_false, mem_Ico]
        exact ⟨(sub_pos.mpr ht.2).le, sub_lt_self _ htpos⟩
    have hparam : ∀ t ∈ Ico (0 : ℝ) (2 * Real.pi),
        Omega.boundaryParam (2 * Real.pi - t) =
          Omega.boundaryParam (r t) := by
      intro t _ht
      by_cases ht0 : t = 0
      · subst t
        simp only [sub_zero, r, if_pos]
        simpa only [zero_add] using Omega.boundaryParam_periodic 0
      · simp only [ht0, ↓reduceIte, r]
    have hr_eq : r x = r y := by
      apply Omega.boundaryParam_injOn (hr_mem x hx) (hr_mem y hy)
      rw [← hparam x hx, ← hparam y hy]
      exact hxy
    by_cases hx0 : x = 0
    · by_cases hy0 : y = 0
      · exact hx0.trans hy0.symm
      · subst x
        simp only [r, if_pos, hy0, if_false] at hr_eq
        have : 0 < 2 * Real.pi - y := sub_pos.mpr hy.2
        linarith
    · by_cases hy0 : y = 0
      · subst y
        simp only [r, hx0, if_false, if_pos] at hr_eq
        have : 0 < 2 * Real.pi - x := sub_pos.mpr hx.2
        linarith
      · simp only [r, hx0, hy0, if_false] at hr_eq
        linarith
  boundaryParam_regular := by
    intro t
    rw [deriv_comp_const_sub]
    exact neg_ne_zero.mpr (Omega.boundaryParam_regular (2 * Real.pi - t))

@[simp] theorem SmoothJordanDomain.reverseOrientation_carrier
    (Omega : SmoothJordanDomain) :
    Omega.reverseOrientation.carrier = Omega.carrier := rfl

@[simp] theorem SmoothJordanDomain.reverseOrientation_boundaryParam
    (Omega : SmoothJordanDomain) (t : ℝ) :
    Omega.reverseOrientation.boundaryParam t =
      Omega.boundaryParam (2 * Real.pi - t) := rfl

theorem SmoothJordanDomain.deriv_reverseOrientation_boundaryParam
    (Omega : SmoothJordanDomain) (t : ℝ) :
    deriv Omega.reverseOrientation.boundaryParam t =
      -deriv Omega.boundaryParam (2 * Real.pi - t) := by
  exact deriv_comp_const_sub Omega.boundaryParam (2 * Real.pi) t

private noncomputable def SmoothJordanDomain.orientationPointSupport
    (Omega : SmoothJordanDomain) : ℂ :=
  Classical.choose Omega.carrier_nonempty

private theorem SmoothJordanDomain.orientationPointSupport_mem
    (Omega : SmoothJordanDomain) :
    Omega.orientationPointSupport ∈ Omega.carrier :=
  Classical.choose_spec Omega.carrier_nonempty

/-- Choose the original boundary orientation when its canonical normal points
outward at a fixed carrier point, and choose the reversed orientation
otherwise. -/
noncomputable def SmoothJordanDomain.canonicalOrientation
    (Omega : SmoothJordanDomain) : SmoothJordanDomain :=
  if ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
      (Omega.orientationPointSupport - Omega.boundaryParam 0)).re ≤ 0 then
    Omega
  else
    Omega.reverseOrientation

@[simp] theorem SmoothJordanDomain.canonicalOrientation_carrier
    (Omega : SmoothJordanDomain) :
    Omega.canonicalOrientation.carrier = Omega.carrier := by
  unfold SmoothJordanDomain.canonicalOrientation
  split <;> rfl

private theorem periodic_deriv_boundaryParam_support
    (Omega : SmoothJordanDomain) :
    Function.Periodic (deriv Omega.boundaryParam) (2 * Real.pi) := by
  intro t
  have hfun : (fun x : ℝ ↦ Omega.boundaryParam (x + 2 * Real.pi)) =
      Omega.boundaryParam := by
    funext x
    exact Omega.boundaryParam_periodic x
  have h := congrArg (fun f : ℝ → ℂ ↦ deriv f t) hfun
  rwa [deriv_comp_add_const] at h

/-- The canonical orientation has an interior point whose canonical normal
has the supporting sign at parameter zero. -/
theorem SmoothJordanDomain.exists_oriented_point_canonicalOrientation
    (Omega : SmoothJordanDomain) :
    ∃ c ∈ Omega.canonicalOrientation.carrier,
      ((starRingEnd ℂ)
          (-I * deriv Omega.canonicalOrientation.boundaryParam 0) *
        (c - Omega.canonicalOrientation.boundaryParam 0)).re ≤ 0 := by
  let c := Omega.orientationPointSupport
  have hc : c ∈ Omega.carrier := Omega.orientationPointSupport_mem
  by_cases hside :
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
        (c - Omega.boundaryParam 0)).re ≤ 0
  · have horient : Omega.canonicalOrientation = Omega := by
      simp only [SmoothJordanDomain.canonicalOrientation, c, hside, if_pos]
    rw [horient]
    exact ⟨c, hc, hside⟩
  · have hpos : 0 <
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
          (c - Omega.boundaryParam 0)).re := lt_of_not_ge hside
    have horient : Omega.canonicalOrientation = Omega.reverseOrientation := by
      simp only [SmoothJordanDomain.canonicalOrientation, c, hside, if_false]
    rw [horient]
    refine ⟨c, by simpa only [reverseOrientation_carrier] using hc, ?_⟩
    rw [deriv_reverseOrientation_boundaryParam,
      reverseOrientation_boundaryParam, sub_zero]
    have hderivT : deriv Omega.boundaryParam (2 * Real.pi) =
        deriv Omega.boundaryParam 0 := by
      simpa only [zero_add] using periodic_deriv_boundaryParam_support Omega 0
    rw [hderivT]
    rw [show Omega.boundaryParam (2 * Real.pi) =
        Omega.boundaryParam 0 by
      simpa only [zero_add] using Omega.boundaryParam_periodic 0]
    have hcomplex :
        (starRingEnd ℂ) (-I * -deriv Omega.boundaryParam 0) *
            (c - Omega.boundaryParam 0) =
          -((starRingEnd ℂ) (-I * deriv Omega.boundaryParam 0) *
            (c - Omega.boundaryParam 0)) := by
      simp only [map_mul, map_neg]
      ring
    rw [hcomplex, neg_re]
    exact neg_nonpos.mpr hpos.le

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
