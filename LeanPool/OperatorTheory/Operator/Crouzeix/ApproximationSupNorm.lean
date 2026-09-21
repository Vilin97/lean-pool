/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
# Polynomial sup-norms on decreasing compact sets

This file supplies the compact-exhaustion transfer needed by approximation
arguments in the Crouzeix chain.  If `K n` is a decreasing sequence of
nonempty compact subsets of `ℂ`, then the polynomial sup-norms on `K n`
decrease to the sup-norm on their intersection.

The proof uses the extreme value theorem and Cantor's intersection theorem:
if the limiting infimum were strictly above the sup-norm on the intersection,
the corresponding closed superlevel subsets of every `K n` would be nonempty
and nested, hence would have a point in their common intersection.

## Main declarations

* `polynomialSupNorm_mono_of_isCompact` gives monotonicity when the larger
  set is compact.
* `polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact` identifies the
  sup-norm on the intersection with the infimum of the approximating norms.
* `tendsto_polynomialSupNorm_atTop_of_antitone_isCompact` is the sequential
  convergence form of the same result.
* `exists_polynomialSupNorm_convexThickeningApprox_le_add` and
  `tendsto_polynomialSupNorm_convexThickeningApprox_atTop` apply this
  approximation principle to the explicit open thickenings from
  `SmoothApprox.lean`.
-/
import LeanPool.OperatorTheory.Operator.Crouzeix.SmoothApprox
import LeanPool.OperatorTheory.Operator.Crouzeix.VonNeumann

open Filter Polynomial Set

private theorem polynomialSupNorm_eq_of_isMaxOn
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {z : ℂ}
    (hz : z ∈ K) (hmax : IsMaxOn (fun w ↦ ‖p.eval w‖) K z) :
    polynomialSupNorm p K = ‖p.eval z‖ := by
  apply le_antisymm
  · unfold polynomialSupNorm
    refine Real.iSup_le (fun w ↦ ?_) (norm_nonneg _)
    exact Real.iSup_le (fun hw ↦ hmax hw) (norm_nonneg _)
  · exact norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz

/-- Polynomial sup norms are monotone under set inclusion whenever the values
on the larger set are bounded, in particular when that set is compact. -/
theorem polynomialSupNorm_mono_of_isCompact
    (p : Polynomial ℂ) {K L : Set ℂ} (hKL : K ⊆ L) (hL : IsCompact L) :
    polynomialSupNorm p K ≤ polynomialSupNorm p L := by
  rw [show polynomialSupNorm p K =
    ⨆ z ∈ K, ‖Polynomial.eval z p‖ from rfl]
  refine Real.iSup_le (fun z ↦ ?_) (polynomialSupNorm_nonneg p L)
  exact Real.iSup_le (fun hz ↦
    norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hL) (hKL hz))
    (polynomialSupNorm_nonneg p L)

/-- The polynomial sup-norm on the intersection of a decreasing sequence of
nonempty compact sets is the infimum of the sup-norms on those sets. -/
theorem polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    polynomialSupNorm p (⋂ n, K n) =
      ⨅ n, polynomialSupNorm p (K n) := by
  let M : ℕ → ℝ := fun n ↦ polynomialSupNorm p (K n)
  have hMbdd : BddBelow (Set.range M) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact polynomialSupNorm_nonneg p (K n)
  have hKclosed : ∀ n, IsClosed (K n) := fun n ↦ (hcompact n).isClosed
  have hI_compact : IsCompact (⋂ n, K n) :=
    (hcompact 0).of_isClosed_subset (isClosed_iInter hKclosed) (iInter_subset K 0)
  apply le_antisymm
  · exact le_ciInf fun n ↦
      polynomialSupNorm_mono_of_isCompact p (iInter_subset K n)
        (hcompact n)
  · by_contra! hlt
    let r : ℝ := (polynomialSupNorm p (⋂ n, K n) + ⨅ n, M n) / 2
    have hIr : polynomialSupNorm p (⋂ n, K n) < r := by
      dsimp only [r]
      linarith
    have hrInf : r < ⨅ n, M n := by
      dsimp only [r]
      linarith
    let L : ℕ → Set ℂ := fun n ↦ K n ∩ {z | r ≤ ‖p.eval z‖}
    have hLclosed : ∀ n, IsClosed (L n) := fun n ↦ by
      exact (hcompact n).isClosed.inter (isClosed_le continuous_const p.continuous.norm)
    have hLcompact : ∀ n, IsCompact (L n) := fun n ↦
      (hcompact n).inter_right (isClosed_le continuous_const p.continuous.norm)
    have hLanti : Antitone L := by
      intro m n hmn z hz
      exact ⟨hanti hmn hz.1, hz.2⟩
    have hLnonempty : ∀ n, (L n).Nonempty := by
      intro n
      obtain ⟨z, hz, hmax⟩ :=
        (hcompact n).exists_isMaxOn (hnonempty n) p.continuous.norm.continuousOn
      refine ⟨z, hz, ?_⟩
      change r ≤ ‖p.eval z‖
      rw [← polynomialSupNorm_eq_of_isMaxOn p (hcompact n) hz hmax]
      simpa only [M] using (hrInf.trans_le (ciInf_le hMbdd n)).le
    obtain ⟨z, hz⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed L
        (fun n ↦ hLanti (Nat.le_succ n)) hLnonempty (hLcompact 0) hLclosed
    have hzI : z ∈ ⋂ n, K n := by
      rw [mem_iInter]
      intro n
      exact (mem_iInter.mp hz n).1
    have hrz : r ≤ ‖p.eval z‖ := (mem_iInter.mp hz 0).2
    have hzM : ‖p.eval z‖ ≤ polynomialSupNorm p (⋂ n, K n) :=
      norm_eval_le_polynomialSupNorm p
        (bddAbove_norm_eval_image_of_isCompact p hI_compact) hzI
    exact (hIr.trans_le (hrz.trans hzM)).false

/-- Along a decreasing sequence of nonempty compact sets, polynomial
sup-norms converge to the sup-norm on the intersection. -/
theorem tendsto_polynomialSupNorm_atTop_of_antitone_isCompact
    (p : Polynomial ℂ) (K : ℕ → Set ℂ)
    (hanti : Antitone K)
    (hcompact : ∀ n, IsCompact (K n))
    (hnonempty : ∀ n, (K n).Nonempty) :
    Tendsto (fun n ↦ polynomialSupNorm p (K n)) atTop
      (nhds (polynomialSupNorm p (⋂ n, K n))) := by
  have hManti : Antitone (fun n ↦ polynomialSupNorm p (K n)) := fun _ _ hmn ↦
    polynomialSupNorm_mono_of_isCompact p (hanti hmn) (hcompact _)
  have hMbdd : BddBelow (Set.range fun n ↦ polynomialSupNorm p (K n)) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact polynomialSupNorm_nonneg p (K n)
  rw [polynomialSupNorm_iInter_eq_iInf_of_antitone_isCompact p K hanti hcompact hnonempty]
  exact tendsto_atTop_ciInf hManti hMbdd

/-! ### The explicit open thickening approximation -/

private theorem polynomialSupNorm_mono_of_subset_of_bddAbove
    (p : Polynomial ℂ) {K L : Set ℂ} (hKL : K ⊆ L)
    (hL : BddAbove ((fun z ↦ ‖p.eval z‖) '' L)) :
    polynomialSupNorm p K ≤ polynomialSupNorm p L := by
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) (polynomialSupNorm_nonneg p L)
  refine Real.iSup_le (fun hz ↦ ?_) (polynomialSupNorm_nonneg p L)
  exact norm_eval_le_polynomialSupNorm p hL (hKL hz)

private theorem bddAbove_norm_eval_convexThickeningApprox
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) (n : ℕ) :
    BddAbove ((fun z ↦ ‖p.eval z‖) '' convexThickeningApprox K n) := by
  refine (bddAbove_norm_eval_image_of_isCompact p
    (hK.cthickening : IsCompact (Metric.cthickening (smoothApproxRadius n) K))).mono ?_
  exact image_mono (Metric.thickening_subset_cthickening _ K)

private theorem convexThickeningApprox_antitone (K : Set ℂ) :
    Antitone (convexThickeningApprox K) := by
  intro m n hmn
  exact Metric.thickening_mono (Nat.one_div_le_one_div hmn) K

private theorem polynomialSupNorm_convexThickeningApprox_antitone
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Antitone (fun n ↦ polynomialSupNorm p (convexThickeningApprox K n)) := by
  intro m n hmn
  exact polynomialSupNorm_mono_of_subset_of_bddAbove p
    (convexThickeningApprox_antitone K hmn)
    (bddAbove_norm_eval_convexThickeningApprox p hK m)

/-- Every positive error tolerance is achieved by one of the explicit open
metric thickenings of a compact set. -/
theorem exists_polynomialSupNorm_convexThickeningApprox_le_add
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ n : ℕ,
      polynomialSupNorm p (convexThickeningApprox K n) ≤
        polynomialSupNorm p K + ε := by
  let U : Set ℂ := {z | ‖p.eval z‖ < polynomialSupNorm p K + ε}
  have hU : IsOpen U := isOpen_lt p.continuous.norm continuous_const
  have hKU : K ⊆ U := by
    intro z hz
    exact (norm_eval_le_polynomialSupNorm p
      (bddAbove_norm_eval_image_of_isCompact p hK) hz).trans_lt
      (lt_add_of_pos_right _ hε)
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine ⟨n, ?_⟩
  have hsubset : convexThickeningApprox K n ⊆ U :=
    (Metric.thickening_mono hn.le K).trans hthick
  have hbound : 0 ≤ polynomialSupNorm p K + ε :=
    add_nonneg (polynomialSupNorm_nonneg p K) hε.le
  unfold polynomialSupNorm
  refine Real.iSup_le (fun z ↦ ?_) hbound
  exact Real.iSup_le (fun hz ↦ (hsubset hz).le) hbound

/-- Polynomial sup-norms on the explicit open metric thickenings of a compact
set converge to the sup-norm on that set. -/
theorem tendsto_polynomialSupNorm_convexThickeningApprox_atTop
    (p : Polynomial ℂ) {K : Set ℂ} (hK : IsCompact K) :
    Tendsto (fun n ↦ polynomialSupNorm p (convexThickeningApprox K n)) atTop
      (nhds (polynomialSupNorm p K)) := by
  have hanti := polynomialSupNorm_convexThickeningApprox_antitone p hK
  have hlower : ∀ n, polynomialSupNorm p K ≤
      polynomialSupNorm p (convexThickeningApprox K n) := by
    intro n
    exact polynomialSupNorm_mono_of_subset_of_bddAbove p
      (Metric.self_subset_thickening (by
        unfold smoothApproxRadius
        positivity) K)
      (bddAbove_norm_eval_convexThickeningApprox p hK n)
  refine Metric.tendsto_atTop.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ :=
    exists_polynomialSupNorm_convexThickeningApprox_le_add p hK (half_pos hε)
  refine ⟨N, fun n hn ↦ ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor
  · linarith [hlower n]
  · have hupper := (hanti hn).trans hN
    linarith

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
