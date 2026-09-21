/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.Analyticity
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.CompactHole
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsContinuation
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.HartogsDomain

/-!
# Hartogs extension

This file develops the geometry of a standard Hartogs figure and uniqueness of its analytic
extensions. Extension from the figure follows from Hartogs continuation over a connected base.
Extension across general compact holes is deduced from the product-space theorem of
`CompactHole`, proved by Ehrenpreis' method, by a choice of linear coordinates. Separate
analyticity is treated in `SeparateAnalytic`.

References: [Boas][Boas2013] (2013), Section 2.7; [Scheidemann][Scheidemann2005] (2005),
Exercise 2.1.7 and Section 2.3; [Jakóbczak–Jarnicki][JakobczakJarnicki2021] (2021), Corollary
2.1.2.

All extension targets are subsets of finite-dimensional complex normed spaces. Coordinate balls
use the supremum norm, so the figure is built from polydiscs. Extension means agreement on the
old domain; functions outside the new domain are unrestricted.

## Main definitions

* `hartogsFigure`: A standard Hartogs figure: a thin full cylinder together with an outer annular
  cylinder in the last coordinate.

## Main results

* `exists_analyticOnNhd_extension_hartogsFigure`: **Extension from a Hartogs figure.** A
  Banach-valued holomorphic function on the figure extends to its full unit polydisc, by Hartogs
  continuation in the last coordinate.
* `exists_analyticOnNhd_extension_of_isCompact`: **Hartogs' compact-hole extension theorem.** In
  complex dimension at least two, a holomorphic function extends across a compact subset if its
  complement in the domain is connected.

## References

* [H. P. Boas, *Lecture Notes on Several Complex Variables*][Boas2013]
* [P. Jakóbczak and M. Jarnicki, *Lectures on Holomorphic Functions of Several Complex
  Variables*][JakobczakJarnicki2021]
* [V. Scheidemann, *Introduction to Complex Analysis in Several Variables*][Scheidemann2005]
-/

public section

open Function Metric Set
open scoped Topology

namespace SeveralComplexVariables

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section Figure

variable {ι : Type*} [Fintype ι]

/-- A standard Hartogs figure: a thin full cylinder together with an outer annular cylinder in the
last coordinate. The intended parameters satisfy `0 < r < 1` and `0 < s < 1`. -/
@[expose] def hartogsFigure (r s : ℝ) : Set ((ι → ℂ) × ℂ) :=
  (ball 0 r ×ˢ ball 0 1) ∪ (ball 0 1 ×ˢ (ball 0 1 \ closedBall 0 s))

/-- The standard Hartogs figure has rotational symmetry in its fiber coordinate, including for
degenerate parameters and an empty base coordinate type. -/
theorem isHartogs_hartogsFigure (r s : ℝ) : IsHartogs (hartogsFigure (ι := ι) r s) := by
  unfold hartogsFigure
  apply (isCompleteHartogs_prod_ball _ _).isHartogs.union
  intro z w hw v hv
  refine ⟨hw.1, ?_⟩
  simpa only [mem_sdiff, mem_ball, mem_closedBall, dist_zero_right, hv] using hw.2

/-- The standard Hartogs figure is open, even for an empty coordinate index type. -/
theorem isOpen_hartogsFigure (r s : ℝ) : IsOpen (hartogsFigure (ι := ι) r s) :=
  (isOpen_ball.prod isOpen_ball).union
    (isOpen_ball.prod (isOpen_ball.sdiff isClosed_closedBall))

/-- The Hartogs figure lies in the full unit polydisc when its inner base radius is at most one. -/
theorem hartogsFigure_subset {r : ℝ} (hr : r ≤ 1) (s : ℝ) :
    hartogsFigure (ι := ι) r s ⊆ ball 0 1 ×ˢ ball 0 1 := by
  rintro z (hz | hz)
  · exact ⟨ball_subset_ball hr hz.1, hz.2⟩
  · exact ⟨hz.1, hz.2.1⟩

/-- A positive inner base radius makes the Hartogs figure contain the origin. -/
theorem zero_mem_hartogsFigure {r : ℝ} (hr : 0 < r) (s : ℝ) :
    (0 : (ι → ℂ) × ℂ) ∈ hartogsFigure r s :=
  Or.inl ⟨mem_ball_self hr, mem_ball_self zero_lt_one⟩

/-- With no base coordinates, a positive-radius Hartogs figure is already the full disk. Thus the
figure-extension statement needs no positive-dimensional base assumption. -/
theorem hartogsFigure_eq_of_isEmpty [IsEmpty ι] {r : ℝ} (hr : 0 < r) (s : ℝ) :
    hartogsFigure (ι := ι) r s = ball 0 1 ×ˢ ball 0 1 := by
  ext z
  simp only [hartogsFigure, mem_union, mem_prod, Subsingleton.elim z.1 (0 : ι → ℂ),
    mem_ball, dist_self, hr, dist_zero_right, true_and, zero_lt_one, mem_sdiff,
    mem_closedBall, not_le, or_iff_left_iff_imp, and_imp]
  exact fun h _ => h

omit [CompleteSpace F] in
/-- Two analytic extensions from a Hartogs figure agree throughout the full unit polydisc. This
uniqueness theorem is proved independently of the extension-existence theorem. -/
theorem eqOn_of_eqOn_hartogsFigure {r : ℝ} (hr : 0 < r) (s : ℝ)
    {f g : ((ι → ℂ) × ℂ) → F}
    (hf : AnalyticOnNhd ℂ f (ball 0 1 ×ˢ ball 0 1))
    (hg : AnalyticOnNhd ℂ g (ball 0 1 ×ˢ ball 0 1))
    (heq : EqOn f g (hartogsFigure r s)) : EqOn f g (ball 0 1 ×ˢ ball 0 1) := by
  apply hf.eqOn_of_preconnected_of_eventuallyEq hg
    (isPreconnected_ball.prod isPreconnected_ball)
    (show (0 : (ι → ℂ) × ℂ) ∈ ball 0 1 ×ˢ ball 0 1 from
      ⟨mem_ball_self zero_lt_one, mem_ball_self zero_lt_one⟩)
  exact Filter.mem_of_superset
    ((isOpen_hartogsFigure r s).mem_nhds (zero_mem_hartogsFigure hr s)) heq

/-- **Extension from a Hartogs figure.** A Banach-valued holomorphic function on the figure
extends to its full unit polydisc, by Hartogs continuation in the last coordinate. -/
theorem exists_analyticOnNhd_extension_hartogsFigure
    {r s : ℝ} (hr : 0 < r) (hr1 : r < 1) (hs : 0 < s) (hs1 : s < 1)
    {f : ((ι → ℂ) × ℂ) → F} (hf : AnalyticOnNhd ℂ f (hartogsFigure r s)) :
    ∃ g : ((ι → ℂ) × ℂ) → F,
      AnalyticOnNhd ℂ g (ball 0 1 ×ˢ ball 0 1) ∧ EqOn g f (hartogsFigure r s) := by
  obtain ⟨g, hg, he⟩ := exists_extension_hartogsCylinder
    (D := ball (0 : ι → ℂ) 1) (D₀ := ball 0 r) isOpen_ball isPreconnected_ball
    isOpen_ball ⟨0, mem_ball_self hr⟩ (ball_subset_ball hr1.le) hs.le hs1
    (by simpa only [hartogsCylinder, hartogsFigure, union_comm] using hf)
  exact ⟨g, hg, by simpa only [hartogsCylinder, hartogsFigure, union_comm] using he⟩

end Figure

/-- **Hartogs' compact-hole extension theorem.** In complex dimension at least two, a
holomorphic function extends across a compact subset if its complement in the domain is
connected. No boundedness of the function near the hole is required, and the domain itself
need not be connected.

The dimension and connected-complement hypotheses are essential. The open domain itself need not
be bounded, and an empty domain or empty compact set is allowed. -/
theorem exists_analyticOnNhd_extension_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (hdim : 2 ≤ Module.finrank ℂ E) {U K : Set E}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hcompl : IsPreconnected (U \ K)) {f : E → F}
    (hf : AnalyticOnNhd ℂ f (U \ K)) :
    ∃ g : E → F, AnalyticOnNhd ℂ g U ∧ EqOn g f (U \ K) := by
  obtain ⟨k, hk⟩ : ∃ k, Module.finrank ℂ E = k + 2 := ⟨Module.finrank ℂ E - 2, by omega⟩
  let b := Module.finBasisOfFinrankEq ℂ E hk
  let e₂ : (Fin (k + 2) → ℂ) ≃L[ℂ] ℂ × (Fin (k + 1) → ℂ) :=
    (Fin.consLinearEquiv ℂ (fun _ : Fin (k + 1).succ => ℂ)).symm.toContinuousLinearEquiv
  let e : E ≃L[ℂ] ℂ × (Fin (k + 1) → ℂ) := b.equivFunL.trans e₂
  set D' : Set (ℂ × (Fin (k + 1) → ℂ)) := e.symm ⁻¹' U with hD'
  set K' : Set (ℂ × (Fin (k + 1) → ℂ)) := e.symm ⁻¹' K with hK'
  have himg : ∀ s : Set E, e.symm ⁻¹' s = e '' s := fun s => by
    ext w
    constructor
    · intro hw
      exact ⟨e.symm w, hw, e.apply_symm_apply w⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  have hD'o : IsOpen D' := hU.preimage e.symm.continuous
  have hK'c : IsCompact K' := by
    rw [hK', himg]
    exact hK.image e.continuous
  have hK'D' : K' ⊆ D' := fun w hw => hKU hw
  have hconn' : IsPreconnected (D' \ K') := by
    have : D' \ K' = e '' (U \ K) := by rw [← himg]; rfl
    rw [this]
    exact hcompl.image e e.continuous.continuousOn
  have hf' : AnalyticOnNhd ℂ (f ∘ e.symm) (D' \ K') :=
    hf.comp (e.symm.toContinuousLinearMap.analyticOnNhd _) fun w hw => hw
  obtain ⟨g', hg', hg'f⟩ :=
    exists_analyticOnNhd_extension_of_isCompact_prod hD'o hK'c hK'D' hconn' hf'
  refine ⟨g' ∘ e, hg'.comp (e.toContinuousLinearMap.analyticOnNhd _) fun z hz => ?_, ?_⟩
  · change e.symm (e z) ∈ U
    simpa using hz
  · intro z hz
    have hz' : e z ∈ D' \ K' := by
      refine ⟨?_, ?_⟩ <;> simp only [hD', hK', mem_preimage, e.symm_apply_apply]
      · exact hz.1
      · exact hz.2
    have := hg'f hz'
    simpa using this

end SeveralComplexVariables

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
