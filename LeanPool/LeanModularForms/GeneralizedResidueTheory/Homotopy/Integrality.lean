/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import LeanPool.LeanModularForms.GeneralizedResidueTheory.Basic
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-!
# Winding Number Integrality

Definitions for piecewise and smooth homotopies, plus the exp trick proof
that winding numbers of closed curves avoiding a point are integers.

## Main Definitions

* `PiecewiseCurvesHomotopicAvoiding` — piecewise C¹ homotopy avoiding z₀
* `ClosedCurvesHomotopicAvoiding` — smooth closed homotopy avoiding z₀

## Main Results

* `windingNumber_integer_of_piecewise_closed_avoiding` — winding number is
    an integer for piecewise C¹ closed curves
* `windingNumber_integer_of_closed_avoiding` — winding number is an integer
    for smooth closed curves
* `exp_integral_eq_endpoint_ratio` — exponential of the log-derivative
    integral equals endpoint ratio
* `integral_closed_curve_eq_two_pi_int` — closed curve integral is 2πi times
    an integer
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Piecewise C¹ homotopy between **closed** curves (i.e. `γ₀ a = γ₀ b` and
`γ₁ a = γ₁ b`) avoiding `z₀`, where `P` is the finite partition set of points
at which the derivative of the homotopy may be discontinuous or undefined.

Use this when working with closed piecewise-smooth curves; it is strictly
stronger than `CurvesHomotopicAvoiding` (which handles open-endpoint curves
fixed at `z₀`) but weaker than `ClosedCurvesHomotopicAvoiding` (which requires
a globally continuous derivative without a partition). -/
def PiecewiseCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = H (b, s)) ∧
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo a b, t ∉ P →
      ∀ s ∈ Icc (0 : ℝ) 1,
        DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    (∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) →
        Ioo p₁ p₂ ⊆ Ioo a b →
          ContinuousOn
            (fun (p : ℝ × ℝ) =>
              deriv (fun t' => H (t', p.2)) p.1)
            (Ioo p₁ p₂ ×ˢ Icc 0 1)) ∧
    (∃ M : ℝ, ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M)

/-- Smooth closed homotopy between **closed** curves avoiding `z₀`.

This is the strongest of the four homotopy notions: the homotopy `H` is
everywhere continuously differentiable (no partition needed). Use this when
the curves and homotopy are genuinely smooth; it implies
`PiecewiseCurvesHomotopicAvoiding` (via `ClosedCurvesHomotopicAvoiding.toPiecewise`)
but does **not** directly imply `CurvesHomotopicAvoiding`, which has a different
endpoint condition (endpoints fixed at `z₀` rather than identified). -/
def ClosedCurvesHomotopicAvoiding (γ₀ γ₁ : ℝ → ℂ)
    (a b : ℝ) (z₀ : ℂ) : Prop :=
  ∃ H : ℝ × ℝ → ℂ,
    Continuous H ∧
    (∀ t ∈ Icc a b, H (t, 0) = γ₀ t) ∧
    (∀ t ∈ Icc a b, H (t, 1) = γ₁ t) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, H (a, s) = H (b, s)) ∧
    (∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      H (t, s) ≠ z₀) ∧
    (∀ t ∈ Ioo a b, ∀ s ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ (fun t' => H (t', s)) t) ∧
    (Continuous (fun p : ℝ × ℝ =>
      deriv (fun t' => H (t', p.2)) p.1))

/-!
### Conversion lemmas between homotopy definitions

The four homotopy notions form the following hierarchy (stronger → weaker):

```
ClosedCurvesHomotopicAvoiding
        |
        v  (toPiecewise)
PiecewiseCurvesHomotopicAvoiding   CurvesHomotopicAvoiding
        |                                   ^
        v  (toBasic, when endpoints = z₀)   |
        (structurally different endpoint conditions)
```

`CurvesHomotopicAvoiding` (from `Basic.lean`) requires `H(a,s) = z₀` and
`H(b,s) = z₀` (endpoints are the fixed point `z₀`), while the Closed/Piecewise
variants require `H(a,s) = H(b,s)` (the curve is merely *closed*).  These are
different conditions, so there is no general implication between the two groups.
-/

/-- A smooth closed homotopy is a piecewise homotopy with empty partition.

The empty partition `∅` means no breakpoints are needed: differentiability
holds everywhere in `Ioo a b` (vacuously, the partition condition is void),
and the global continuity of the derivative supplies the required local
continuity on every sub-interval. The bound on `‖deriv H‖` is obtained from
compactness of `Icc a b × Icc 0 1` together with continuity of the derivative. -/
theorem ClosedCurvesHomotopicAvoiding.toPiecewise
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (h : ClosedCurvesHomotopicAvoiding γ₀ γ₁ a b z₀) :
    PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ ∅ := by
  obtain ⟨H, hcont, hH0, hH1, hclosed, havoid, hdiff, hderiv_cont⟩ := h
  refine ⟨H, hcont, hH0, hH1, hclosed, havoid, ?_, ?_, ?_⟩
  · -- Differentiability: P = ∅, so the hypothesis t ∉ P is always vacuously true
    intro t ht _ht_not_in_empty s hs
    exact hdiff t ht s hs
  · -- Continuous deriv on sub-intervals: global continuity restricts to any subset
    intro p₁ p₂ _hp _hvac _hI
    exact hderiv_cont.continuousOn.mono (Set.subset_univ _)
  · -- Bound on deriv: compactness of Icc a b × Icc 0 1 + continuity gives a uniform bound
    have hK : IsCompact (Set.Icc a b ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hf_cont : Continuous (fun p : ℝ × ℝ => ‖deriv (fun t' => H (t', p.2)) p.1‖) :=
      hderiv_cont.norm
    rcases hK.exists_bound_of_continuousOn hf_cont.continuousOn with ⟨M, hM⟩
    simp only [norm_norm] at hM
    exact ⟨M, fun t ht s hs => hM ⟨t, s⟩ ⟨ht, hs⟩⟩

/-- A piecewise homotopy (forgetting derivative bounds) gives a basic homotopy.

**Note**: this conversion requires an extra hypothesis `hpts` asserting that the
homotopy `H` (from `h`) satisfies `H(a,s) = z₀` and `H(b,s) = z₀` for all `s`.
This is the endpoint condition required by `CurvesHomotopicAvoiding` (Basic.lean).
The piecewise/closed variants only require `H(a,s) = H(b,s)` (closed curves),
which is a strictly weaker condition — so no hypothesis-free conversion exists. -/
theorem PiecewiseCurvesHomotopicAvoiding.toBasic
    {γ₀ γ₁ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (h : PiecewiseCurvesHomotopicAvoiding γ₀ γ₁ a b z₀ P)
    (hpts : ∀ H : ℝ × ℝ → ℂ,
        Continuous H →
        (∀ t ∈ Set.Icc a b, H (t, 0) = γ₀ t) →
        (∀ t ∈ Set.Icc a b, H (t, 1) = γ₁ t) →
        ∀ s ∈ Set.Icc (0 : ℝ) 1, H (a, s) = z₀ ∧ H (b, s) = z₀) :
    CurvesHomotopicAvoiding γ₀ γ₁ a b z₀ := by
  obtain ⟨H, hcont, hH0, hH1, _hclosed, havoid, _hdiff, _hderiv, _hbound⟩ := h
  exact ⟨H, hcont, hH0, hH1,
    hpts H hcont hH0 hH1,
    fun t ht s hs => havoid t (Set.Ioo_subset_Icc_self ht) s hs⟩

/-- If f is eventually equal to a constant, `limUnder` equals that constant. -/
theorem limUnder_eventually_eq_const {α : Type*} [TopologicalSpace α] {f : α → ℂ}
    {l : Filter α} {c : ℂ} [l.NeBot] (hf : ∀ᶠ x in l, f x = c) : limUnder l f = c :=
  (tendsto_const_nhds.congr' (hf.mono fun _ h => h.symm)).limUnder_eq

/-- At a point not in a finite set, there is an open ball disjoint from the set. -/
lemma exists_ball_avoiding_finset {P : Finset ℝ} {t : ℝ} (ht : t ∉ P) :
    ∃ ε > 0, ∀ x ∈ Ioo (t - ε) (t + ε), x ∉ P := by
  by_cases hP_empty : P = ∅
  · exact ⟨1, one_pos, fun x _ => by simp [hP_empty]⟩
  · have hP_ne := Finset.nonempty_of_ne_empty hP_empty
    have h_ne : ∀ p ∈ P, p ≠ t := fun p hp => ne_of_mem_of_not_mem hp ht
    let d := Finset.inf' P hP_ne (fun p => |p - t|)
    have hd_pos : 0 < d := by
      rw [Finset.lt_inf'_iff]; exact fun p hp => abs_pos.mpr (sub_ne_zero.mpr (h_ne p hp))
    exact ⟨d / 2, by linarith, fun x hx hxP => by
      have : d ≤ |x - t| := Finset.inf'_le (fun p => |p - t|) hxP
      have : |x - t| < d := by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2]
      linarith⟩

private lemma bound_away_from_z₀
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ δ > 0, ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖ := by
  have hc := isCompact_Icc.image_of_continuousOn hγ_cont
  have hn : (γ '' Icc a b).Nonempty :=
    ⟨γ a, mem_image_of_mem γ (left_mem_Icc.mpr hab.le)⟩
  have hz : z₀ ∉ γ '' Icc a b := fun ⟨t, ht, he⟩ => hγ_avoids t ht he
  exact ⟨_, (hc.isClosed.notMem_iff_infDist_pos hn).mp hz, fun t ht => by
    calc Metric.infDist z₀ (γ '' Icc a b)
        ≤ dist z₀ (γ t) := Metric.infDist_le_dist_of_mem (mem_image_of_mem γ ht)
      _ = ‖γ t - z₀‖ := by rw [Complex.dist_eq, norm_sub_rev]⟩

private lemma logDeriv_integrand_bound
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {M δ : ℝ}
    (hδ : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖)
    (hM : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖deriv γ t / (γ t - z₀)‖ ≤ M / δ := by
  rw [norm_div]
  exact (div_le_div_of_nonneg_left (norm_nonneg _) hδ (hδ_bd t ht)).trans
    (div_le_div_of_nonneg_right (hM t ht) hδ.le)

private lemma logDeriv_continuousOn_off_finset
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b \ (P ∪ {a, b})) := by
  intro t ⟨ht_Icc, ht_notP'⟩
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at ht_notP'
  have ht_Ioo : t ∈ Ioo a b :=
    ⟨lt_of_le_of_ne ht_Icc.1 (Ne.symm ht_notP'.2.1),
     lt_of_le_of_ne ht_Icc.2 ht_notP'.2.2⟩
  obtain ⟨ε, hε, hε_avoid⟩ := exists_ball_avoiding_finset ht_notP'.1
  let p₁ := max a (t - ε / 2)
  let p₂ := min b (t + ε / 2)
  have hp₁p₂ : p₁ < p₂ := by
    simp only [p₁, p₂, lt_min_iff, max_lt_iff]
    exact ⟨⟨lt_trans ht_Ioo.1 ht_Ioo.2, by linarith [ht_Ioo.2, hε]⟩,
           ⟨by linarith [ht_Ioo.1, hε], by linarith⟩⟩
  have h_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := fun s hs => hε_avoid s (by
    simp only [p₁, p₂, mem_Ioo] at hs
    exact ⟨by linarith [le_max_right a (t - ε / 2), hs.1],
           by linarith [min_le_right b (t + ε / 2), hs.2]⟩)
  have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
    simp only [p₁, p₂, mem_Ioo] at hx ⊢
    exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1, lt_of_lt_of_le hx.2 (min_le_left b _)⟩
  have ht_in : t ∈ Ioo p₁ p₂ := by
    simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
    exact ⟨⟨ht_Ioo.1, by linarith [hε]⟩, ⟨ht_Ioo.2, by linarith [hε]⟩⟩
  exact ContinuousWithinAt.div
    ((hγ_deriv_cont p₁ p₂ hp₁p₂ h_avoid h_sub).continuousAt
      (Ioo_mem_nhds ht_in.1 ht_in.2)).continuousWithinAt
    ((hγ_cont.sub continuousOn_const).continuousWithinAt ht_Icc)
    (sub_ne_zero.mpr (hγ_avoids t ht_Icc))
    |>.mono diff_subset

private lemma logDeriv_continuousAt_off_finset
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    {t : ℝ} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    ContinuousAt (fun t => deriv γ t / (γ t - z₀)) t := by
  obtain ⟨ε, hε, hε_avoid⟩ := exists_ball_avoiding_finset ht_notP
  let p₁ := max a (t - ε / 2)
  let p₂ := min b (t + ε / 2)
  have hp₁p₂ : p₁ < p₂ := by
    simp only [p₁, p₂, lt_min_iff, max_lt_iff]
    exact ⟨⟨lt_trans ht.1 ht.2, by linarith [ht.2, hε]⟩,
           ⟨by linarith [ht.1, hε], by linarith⟩⟩
  have h_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := fun s hs => hε_avoid s (by
    simp only [p₁, p₂, mem_Ioo] at hs
    exact ⟨by linarith [le_max_right a (t - ε / 2)],
           by linarith [min_le_right b (t + ε / 2)]⟩)
  have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
    simp only [p₁, p₂, mem_Ioo] at hx ⊢
    exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1,
           lt_of_lt_of_le hx.2 (min_le_left b _)⟩
  have ht_in : t ∈ Ioo p₁ p₂ := by
    simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
    exact ⟨⟨ht.1, by linarith [hε]⟩, ⟨ht.2, by linarith [hε]⟩⟩
  exact ContinuousAt.div
    ((hγ_deriv_cont p₁ p₂ hp₁p₂ h_avoid h_sub).continuousAt
      (Ioo_mem_nhds ht_in.1 ht_in.2))
    (hγ_cont.continuousAt (Icc_mem_nhds ht.1 ht.2) |>.sub continuousAt_const)
    (sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht)))

private lemma logDeriv_stronglyMeasurableAtFilter_off_finset
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    {t : ℝ} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    StronglyMeasurableAtFilter (fun t => deriv γ t / (γ t - z₀)) (𝓝 t) volume := by
  obtain ⟨ε, hε, hε_avoid⟩ := exists_ball_avoiding_finset ht_notP
  let p₁ := max a (t - ε / 2)
  let p₂ := min b (t + ε / 2)
  have hp₁p₂ : p₁ < p₂ := by
    simp only [p₁, p₂, lt_min_iff, max_lt_iff]
    exact ⟨⟨lt_trans ht.1 ht.2, by linarith [ht.2, hε]⟩,
           ⟨by linarith [ht.1, hε], by linarith⟩⟩
  have h_avoid : ∀ s ∈ Ioo p₁ p₂, s ∉ P := fun s hs => hε_avoid s (by
    simp only [p₁, p₂, mem_Ioo] at hs
    exact ⟨by linarith [le_max_right a (t - ε / 2)],
           by linarith [min_le_right b (t + ε / 2)]⟩)
  have h_sub : Ioo p₁ p₂ ⊆ Ioo a b := fun x hx => by
    simp only [p₁, p₂, mem_Ioo] at hx ⊢
    exact ⟨lt_of_le_of_lt (le_max_left a _) hx.1,
           lt_of_lt_of_le hx.2 (min_le_left b _)⟩
  have ht_in : t ∈ Ioo p₁ p₂ := by
    simp only [p₁, p₂, mem_Ioo, lt_min_iff, max_lt_iff]
    exact ⟨⟨ht.1, by linarith [hε]⟩, ⟨ht.2, by linarith [hε]⟩⟩
  have h_cont_on : ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Ioo p₁ p₂) := by
    intro x hx
    exact ContinuousWithinAt.div
      ((hγ_deriv_cont p₁ p₂ hp₁p₂ h_avoid h_sub).continuousWithinAt hx)
      (((hγ_cont.sub continuousOn_const).continuousWithinAt
        (Ioo_subset_Icc_self (h_sub hx))).mono
        ((Ioo_subset_Ioo (le_max_left _ _) (min_le_left _ _)).trans Ioo_subset_Icc_self))
      (sub_ne_zero.mpr (hγ_avoids _ (Ioo_subset_Icc_self (h_sub hx))))
  exact ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
    (fun x hx => h_cont_on.continuousAt (Ioo_mem_nhds hx.1 hx.2)) t ht_in

private lemma logDeriv_integral_hasDerivAt_off_finset
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b)
    {t : ℝ} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    HasDerivAt (fun t => ∫ s in a..t, deriv γ s / (γ s - z₀))
      (deriv γ t / (γ t - z₀)) t := by
  have ht_in_uIcc : t ∈ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab.le]; exact Ioo_subset_Icc_self ht
  exact intervalIntegral.integral_hasDerivAt_right
    (h_int.mono_set (Set.uIcc_subset_uIcc_left ht_in_uIcc))
    (logDeriv_stronglyMeasurableAtFilter_off_finset hγ_cont hγ_deriv_cont hγ_avoids ht ht_notP)
    (logDeriv_continuousAt_off_finset hγ_cont hγ_deriv_cont hγ_avoids ht ht_notP)

private lemma gFunc_deriv_zero_off_finset
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b)
    {t : ℝ} (ht : t ∈ Ioo a b) (ht_notP : t ∉ P) :
    let F := fun t => ∫ s in a..t, deriv γ s / (γ s - z₀)
    let G := fun t => (γ t - z₀) * Complex.exp (-F t)
    deriv G t = 0 := by
  intro F G
  have hne : γ t - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids t (Ioo_subset_Icc_self ht))
  have hF_deriv : HasDerivAt F (deriv γ t / (γ t - z₀)) t :=
    logDeriv_integral_hasDerivAt_off_finset hab hγ_cont hγ_deriv_cont hγ_avoids h_int ht ht_notP
  have hG_at : HasDerivAt G
      (deriv γ t * Complex.exp (-F t) +
        (γ t - z₀) * (Complex.exp (-F t) * -(deriv γ t / (γ t - z₀)))) t :=
    ((hγ_diff t ht ht_notP).hasDerivAt.sub_const z₀).mul hF_deriv.neg.cexp
  rw [hG_at.deriv]; field_simp [hne]; ring

private lemma gFunc_constant_piecewise
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b) :
    ∀ t ∈ Icc a b,
      (γ t - z₀) * Complex.exp (-(∫ s in a..t, deriv γ s / (γ s - z₀))) =
      (γ a - z₀) * Complex.exp (-(∫ s in a..a, deriv γ s / (γ s - z₀))) := by
  set F : ℝ → ℂ := fun t => ∫ s in a..t, deriv γ s / (γ s - z₀) with hF_def
  set G : ℝ → ℂ := fun t => (γ t - z₀) * Complex.exp (-F t) with hG_def
  have hG_cont : ContinuousOn G (Icc a b) := by
    apply ContinuousOn.mul (hγ_cont.sub continuousOn_const)
    apply Continuous.comp_continuousOn Complex.continuous_exp
    have := intervalIntegral.continuousOn_primitive_interval' h_int left_mem_uIcc
    exact (show ContinuousOn F (Icc a b) from
      Set.uIcc_of_le hab.le ▸ this).neg
  have hG_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ G t := by
    intro t ht ht_notP
    exact ((hγ_diff t ht ht_notP).sub (differentiableAt_const z₀)).mul
      (logDeriv_integral_hasDerivAt_off_finset hab hγ_cont hγ_deriv_cont
        hγ_avoids h_int ht ht_notP).differentiableAt.neg.cexp
  have hG_deriv : ∀ t ∈ Ioo a b, t ∉ P → deriv G t = 0 :=
    fun t ht ht_notP =>
      gFunc_deriv_zero_off_finset hab hγ_cont hγ_diff hγ_deriv_cont hγ_avoids h_int ht ht_notP
  exact constant_of_has_deriv_right_zero hG_cont
    (hasDerivWithinAt_zero_of_deriv_zero_off_finite G a b P hab hG_cont hG_diff hG_deriv)

private lemma pv_eq_integral_of_bound_away
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖) :
    cauchyPrincipalValue' (·⁻¹) (fun t => γ t - z₀) a b 0 =
    ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t := by
  unfold cauchyPrincipalValue'
  apply limUnder_eventually_eq_const
  filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
  apply intervalIntegral.integral_congr_ae
  filter_upwards with t ht
  simp only [sub_zero]
  have ht' : t ∈ Icc a b := Ioc_subset_Icc_self (Set.uIoc_of_le hab.le ▸ ht)
  simp only [(mem_Ioo.mp hε).2.trans_le (hδ_bd t ht'), ↓reduceIte, deriv_sub_const]

private lemma exp_neg_integral_eq_one_of_closed
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {P : Finset ℝ}
    (hab : a < b) (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b) :
    Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) = 1 := by
  have hG_const := gFunc_constant_piecewise hab hγ_cont hγ_diff hγ_deriv_cont hγ_avoids h_int
  have hne_a : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids a (left_mem_Icc.mpr hab.le))
  have hGb : (γ a - z₀) *
      Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) = γ a - z₀ := by
    calc (γ a - z₀) * Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀)))
        = (γ b - z₀) *
          Complex.exp (-(∫ s in a..b, deriv γ s / (γ s - z₀))) := by
          rw [hγ_closed]
      _ = (γ a - z₀) * Complex.exp (-(∫ s in a..a, deriv γ s / (γ s - z₀))) :=
          hG_const b (right_mem_Icc.mpr hab.le)
      _ = γ a - z₀ := by simp [intervalIntegral.integral_same]
  exact mul_left_cancel₀ hne_a (hGb.trans (mul_one _).symm)

private lemma winding_integer_from_exp_one
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ : ℝ}
    (hab : a < b) (hδ : 0 < δ)
    (hδ_bd : ∀ t ∈ Icc a b, δ ≤ ‖γ t - z₀‖)
    (hFb : ∃ n : ℤ, -(∫ t in a..b, deriv γ t / (γ t - z₀)) =
      ↑n * (2 * ↑Real.pi * I)) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  obtain ⟨n, hn⟩ := hFb
  use -n
  unfold generalizedWindingNumber'
  rw [pv_eq_integral_of_bound_away hab hδ hδ_bd]
  have h_eq : ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t =
      ∫ t in a..b, deriv γ t / (γ t - z₀) := by
    congr 1; ext t; rw [mul_comm, div_eq_mul_inv]
  rw [h_eq]
  have hFb' : ∫ t in a..b, deriv γ t / (γ t - z₀) = -(↑n * (2 * Real.pi * I)) := by
    have h := hn; linear_combination -h
  rw [hFb']
  have hne : (2 : ℂ) * Real.pi * I ≠ 0 := by
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, Complex.ofReal_eq_zero,
      Real.pi_ne_zero, Complex.I_ne_zero, or_self, not_false_eq_true]
  field_simp; simp [Int.cast_neg]

private lemma windingNumber_integer_of_piecewise_with_bound
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ)
    (M : ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_deriv_bound : ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M)
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := bound_away_from_z₀ γ a b z₀ hab hγ_cont hγ_avoids
  have h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b := by
    have h_coe : (↑(P ∪ {a, b}) : Set ℝ) = ↑P ∪ {a, b} := by
      simp only [Finset.coe_union, Finset.coe_insert, Finset.coe_singleton]
    exact intervalIntegrable_of_piecewise_continuousOn_bounded (M / δ) hab.le
      (h_coe ▸ logDeriv_continuousOn_off_finset hγ_cont hγ_deriv_cont hγ_avoids)
      (fun t ht => logDeriv_integrand_bound hδ_pos hδ_bound hγ_deriv_bound t ht)
  have h_exp := exp_neg_integral_eq_one_of_closed hab hγ_closed hγ_cont hγ_diff
    hγ_deriv_cont hγ_avoids h_int
  rw [Complex.exp_eq_one_iff] at h_exp
  exact winding_integer_from_exp_one hab hδ_pos hδ_bound h_exp

lemma windingNumber_integer_of_piecewise_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ_deriv_bound_ex : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
    ∃ n : ℤ, generalizedWindingNumber' γ a b z₀ = n := by
  obtain ⟨M, hM⟩ := hγ_deriv_bound_ex
  exact windingNumber_integer_of_piecewise_with_bound
    γ a b z₀ P M hab hγ_closed hγ_cont hγ_diff hγ_deriv_cont hM hγ_avoids

/-- Piecewise generalization of `exp_integral_eq_endpoint_ratio`: for a piecewise C¹
curve avoiding z₀ with bounded derivative, the exponential of the log-derivative
integral equals the endpoint ratio. Uses the G-function technique. -/
theorem exp_integral_eq_endpoint_ratio_piecewise
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (P : Finset ℝ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, t ∉ P → DifferentiableAt ℝ γ t)
    (hγ_deriv_cont : ∀ p₁ p₂ : ℝ, p₁ < p₂ →
      (∀ t ∈ Ioo p₁ p₂, t ∉ P) → Ioo p₁ p₂ ⊆ Ioo a b →
      ContinuousOn (deriv γ) (Ioo p₁ p₂))
    (hγ_avoids : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ_deriv_bound : ∃ M, ∀ t ∈ Icc a b, ‖deriv γ t‖ ≤ M) :
    Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (γ b - z₀) / (γ a - z₀) := by
  obtain ⟨M, hM⟩ := hγ_deriv_bound
  obtain ⟨δ, hδ, hδ_bd⟩ := bound_away_from_z₀ γ a b z₀ hab hγ_cont hγ_avoids
  have h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b := by
    have h_coe : (↑(P ∪ {a, b}) : Set ℝ) = ↑P ∪ {a, b} := by
      simp only [Finset.coe_union, Finset.coe_insert, Finset.coe_singleton]
    exact intervalIntegrable_of_piecewise_continuousOn_bounded (M / δ) hab.le
      (h_coe ▸ logDeriv_continuousOn_off_finset hγ_cont hγ_deriv_cont hγ_avoids)
      (fun t ht => logDeriv_integrand_bound hδ hδ_bd hM t ht)
  have hG_const := gFunc_constant_piecewise hab hγ_cont hγ_diff hγ_deriv_cont hγ_avoids h_int
  have hne_a : γ a - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids a (left_mem_Icc.mpr hab.le))
  have hne_b : γ b - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoids b (right_mem_Icc.mpr hab.le))
  have hGb' : (γ b - z₀) *
      Complex.exp (-(∫ s in a..b, deriv γ s / (γ s - z₀))) = γ a - z₀ := by
    have := hG_const b (right_mem_Icc.mpr hab.le)
    simp only [intervalIntegral.integral_same, neg_zero, exp_zero, mul_one] at this
    exact this
  have h_neg : Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) =
      (γ a - z₀) / (γ b - z₀) := by
    rw [eq_div_iff hne_b, mul_comm]; exact hGb'
  rw [show Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))))⁻¹ from by
    rw [Complex.exp_neg, inv_inv], h_neg, inv_div]

/-- Uniform bound for winding number integrand from homotopy avoidance. -/
theorem winding_integrand_bounded_of_uniform_avoidance
    {H : ℝ × ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {δ M : ℝ}
    (hδ_pos : 0 < δ)
    (hδ_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1, δ ≤ ‖H (t, s) - z₀‖)
    (hM_bound : ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖deriv (fun t' => H (t', s)) t‖ ≤ M) :
    ∀ t ∈ Icc a b, ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖ ≤ M / δ := by
  intro t ht s hs
  have h_ne : H (t, s) - z₀ ≠ 0 := by
    intro heq
    have h := hδ_bound t ht s hs
    simp only [heq, norm_zero] at h
    linarith
  have h_inv_bound : ‖(H (t, s) - z₀)⁻¹‖ ≤ δ⁻¹ := by
    rw [norm_inv, inv_eq_one_div, inv_eq_one_div]
    exact one_div_le_one_div_of_le hδ_pos (hδ_bound t ht s hs)
  calc ‖(H (t, s) - z₀)⁻¹ * deriv (fun t' => H (t', s)) t‖
      ≤ ‖(H (t, s) - z₀)⁻¹‖ * ‖deriv (fun t' => H (t', s)) t‖ := norm_mul_le _ _
    _ ≤ δ⁻¹ * M := mul_le_mul h_inv_bound (hM_bound t ht s hs)
        (norm_nonneg _) (le_of_lt (inv_pos.mpr hδ_pos))
    _ = M / δ := by ring

private lemma gFunc_constant_smooth
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (h_integrand_cont : ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b))
    (h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b) :
    ∀ t ∈ Icc a b,
      (γ t - z₀) * Complex.exp (-(∫ s in a..t, deriv γ s / (γ s - z₀))) =
      (γ a - z₀) * Complex.exp (-(∫ s in a..a, deriv γ s / (γ s - z₀))) := by
  set F : ℝ → ℂ := fun t => ∫ s in a..t, deriv γ s / (γ s - z₀) with hF_def
  set G : ℝ → ℂ := fun t => (γ t - z₀) * Complex.exp (-F t) with hG_def
  have hG_cont : ContinuousOn G (Icc a b) := by
    apply ContinuousOn.mul (hγ_cont.sub continuousOn_const)
    apply Continuous.comp_continuousOn Complex.continuous_exp
    exact (show ContinuousOn F (Icc a b) from
      Set.uIcc_of_le hab.le ▸
        intervalIntegral.continuousOn_primitive_interval' h_int left_mem_uIcc).neg
  have hF_hasDerivAt : ∀ t ∈ Ioo a b, HasDerivAt F (deriv γ t / (γ t - z₀)) t := by
    intro t ht
    have huIcc_sub : Set.uIcc a t ⊆ Set.uIcc a b := by
      rw [Set.uIcc_of_le ht.1.le, Set.uIcc_of_le hab.le]
      exact Icc_subset_Icc le_rfl ht.2.le
    exact intervalIntegral.integral_hasDerivAt_right
      (h_int.mono_set huIcc_sub)
      (ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioo
        (fun x hx => h_integrand_cont.continuousAt (Icc_mem_nhds hx.1 hx.2)) t ht)
      (h_integrand_cont.continuousAt (Icc_mem_nhds ht.1 ht.2))
  have h_deriv_zero : ∀ t ∈ Ioo a b, deriv G t = 0 := by
    intro t ht
    exact (((hγ_diff t ht).hasDerivAt.sub_const z₀).mul
      (hF_hasDerivAt t ht).neg.cexp).deriv.trans (by
      have := sub_ne_zero.mpr (hγ_avoid t (Ioo_subset_Icc_self ht)); field_simp; ring)
  have h_Ioo_mem : Ioo a b ∈ nhdsWithin a (Ioi a) := by
    rw [mem_nhdsWithin]
    exact ⟨Iio b, isOpen_Iio, mem_Iio.mpr hab, fun x ⟨hxb, hxa⟩ => ⟨hxa, hxb⟩⟩
  have hG_deriv_right : ∀ t ∈ Ico a b, HasDerivWithinAt G 0 (Ici t) t := by
    intro t ht
    by_cases ha_eq : t = a
    · rw [ha_eq]
      exact hasDerivWithinAt_Ici_of_tendsto_deriv
        (fun t ht => ((hγ_diff t ht).sub_const z₀).mul
          (Complex.differentiable_exp.differentiableAt.comp t
            (hF_hasDerivAt t ht).differentiableAt.neg) |>.differentiableWithinAt)
        (hG_cont.continuousWithinAt (left_mem_Icc.mpr hab.le) |>.mono Ioo_subset_Icc_self)
        h_Ioo_mem
        (tendsto_const_nhds.congr' (by
          filter_upwards [h_Ioo_mem] with t ht; exact (h_deriv_zero t ht).symm))
    · have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ha_eq), ht.2⟩
      have hG_hasDerivAt : HasDerivAt G 0 t := by
        convert ((hγ_diff t ht').hasDerivAt.sub_const z₀).mul
          (hF_hasDerivAt t ht').neg.cexp using 1
        have := sub_ne_zero.mpr (hγ_avoid t (Ioo_subset_Icc_self ht'))
        field_simp; ring
      exact hG_hasDerivAt.hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hG_cont hG_deriv_right

private lemma exp_endpoint_ratio_from_gFunc
    {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ}
    (hab : a < b)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hG_const : ∀ t ∈ Icc a b,
      (γ t - z₀) * Complex.exp (-(∫ s in a..t, deriv γ s / (γ s - z₀))) =
      (γ a - z₀) * Complex.exp (-(∫ s in a..a, deriv γ s / (γ s - z₀)))) :
    Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) = (γ b - z₀) / (γ a - z₀) := by
  have hne_b : γ b - z₀ ≠ 0 := sub_ne_zero.mpr (hγ_avoid b (right_mem_Icc.mpr hab.le))
  have hGb' : (γ b - z₀) *
      Complex.exp (-(∫ s in a..b, deriv γ s / (γ s - z₀))) = γ a - z₀ := by
    have := hG_const b (right_mem_Icc.mpr hab.le)
    simp only [intervalIntegral.integral_same, neg_zero, exp_zero, mul_one] at this
    exact this
  have h_neg : Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))) =
      (γ a - z₀) / (γ b - z₀) := by
    rw [eq_div_iff hne_b, mul_comm]; exact hGb'
  rw [show Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (Complex.exp (-(∫ t in a..b, deriv γ t / (γ t - z₀))))⁻¹ from by
    rw [Complex.exp_neg, inv_inv], h_neg, inv_div]

theorem exp_integral_eq_endpoint_ratio
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    Complex.exp (∫ t in a..b, deriv γ t / (γ t - z₀)) =
      (γ b - z₀) / (γ a - z₀) := by
  have h_integrand_cont : ContinuousOn (fun t => deriv γ t / (γ t - z₀)) (Icc a b) :=
    hγ'_cont.div (hγ_cont.sub continuousOn_const)
      fun t ht => sub_ne_zero.mpr (hγ_avoid t ht)
  have h_int : IntervalIntegrable (fun t => deriv γ t / (γ t - z₀)) volume a b :=
    h_integrand_cont.intervalIntegrable_of_Icc hab.le
  exact exp_endpoint_ratio_from_gFunc hab hγ_avoid
    (gFunc_constant_smooth hab hγ_cont hγ_diff hγ_avoid h_integrand_cont h_int)

private theorem integral_closed_curve_eq_two_pi_int
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b, DifferentiableAt ℝ γ t)
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b)) :
    ∃ n : ℤ, ∫ t in a..b, deriv γ t / (γ t - z₀) =
      2 * Real.pi * I * n := by
  have hexp : Complex.exp
      (∫ t in a..b, deriv γ t / (γ t - z₀)) = 1 := by
    rw [exp_integral_eq_endpoint_ratio γ a b z₀ hab
      hγ_cont hγ_diff hγ_avoid hγ'_cont, hγ_closed]
    exact div_self (sub_ne_zero.mpr
      (hγ_avoid b (right_mem_Icc.mpr (le_of_lt hab))))
  rw [Complex.exp_eq_one_iff] at hexp
  obtain ⟨n, hn⟩ := hexp
  exact ⟨n, by rw [hn]; ring⟩

/-- The winding number of a smooth closed curve avoiding z₀
is an integer. -/
theorem windingNumber_integer_of_closed_avoiding
    (γ : ℝ → ℂ) (a b : ℝ) (z₀ : ℂ) (hab : a < b)
    (hγ_closed : γ a = γ b)
    (hγ_cont : ContinuousOn γ (Icc a b))
    (hγ_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ γ t)
    (hγ'_cont : ContinuousOn (deriv γ) (Icc a b))
    (hγ_avoid : ∀ t ∈ Icc a b, γ t ≠ z₀) :
    ∃ n : ℤ,
    generalizedWindingNumber' γ a b z₀ = n := by
  let τ := fun t => γ t - z₀
  have hτ_closed : τ a = τ b := by
    simp only [τ]; rw [hγ_closed]
  have hτ_cont : ContinuousOn τ (Icc a b) :=
    hγ_cont.sub continuousOn_const
  have hτ_diff : ∀ t ∈ Ioo a b,
      DifferentiableAt ℝ τ t := fun t ht =>
    (hγ_diff t ht).sub (differentiableAt_const z₀)
  have hτ_avoid : ∀ t ∈ Icc a b, τ t ≠ 0 :=
    fun t ht => sub_ne_zero.mpr (hγ_avoid t ht)
  have hτ'_cont : ContinuousOn (deriv τ) (Icc a b) := by
    rw [show deriv τ = deriv γ from
      funext fun t => deriv_sub_const z₀]
    exact hγ'_cont
  obtain ⟨n, hn⟩ := integral_closed_curve_eq_two_pi_int
    τ a b 0 hab hτ_closed hτ_cont hτ_diff hτ_avoid
    hτ'_cont
  use n
  unfold generalizedWindingNumber'
  have h_eq : (fun t => deriv τ t / (τ t - 0)) = (fun t => deriv γ t / (γ t - z₀)) := by
    ext t; simp only [τ, sub_zero, deriv_sub_const]
  rw [h_eq] at hn
  obtain ⟨δ, hδ, hδ_bd⟩ := bound_away_from_z₀ γ a b z₀ hab hγ_cont hγ_avoid
  rw [pv_eq_integral_of_bound_away hab hδ hδ_bd,
    show ∫ t in a..b, (γ t - z₀)⁻¹ * deriv γ t =
      ∫ t in a..b, deriv γ t / (γ t - z₀) from by
    congr 1; ext t; rw [mul_comm, div_eq_mul_inv], hn]
  field_simp

end
