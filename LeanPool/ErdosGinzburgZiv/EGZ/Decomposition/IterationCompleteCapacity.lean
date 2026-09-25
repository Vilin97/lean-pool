/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/
module


public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.StoppedLineages
public import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationIntervalBounds

/-!
# Capacity of complete-event lineages

At a fixed complete-event level, every selected lineage is killed. If all
intervening event colors are at least that level's color, no lineage can
return. A finite family of such events therefore has cardinality bounded by
the initial node population.
-/

@[expose] public section

namespace EGZ.FlagDecomposition.Iteration

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

namespace State.Event

theorem exists_complete_of_color_eq {s : State p d f} (E : s.Event) {L : ℕ}
    (hL : L < (d + 1) ^ 2) (hcolor : E.color = 2 * L) :
    ∃ x, E = .complete x ∧ s.decomposition.level x = L := by
  cases E with
  | gap => dsimp [color] at hcolor; omega
  | face x Γ => dsimp [color] at hcolor; omega
  | complete x =>
    refine ⟨x, rfl, ?_⟩
    dsimp [color] at hcolor
    omega

end State.Event

/-- Complete-event capacity only requires progress at the selected event
times; all other comparisons may be identities after a finite endpoint. -/
theorem card_complete_events_le_of_lineage
    {s : ℕ → State p d f} (D : LineageMassMaps (fun i ↦ (s i).decomposition))
    {L : ℕ} (hcut : ∀ i, L ≤ D.cutoff i)
    {E : Type*} [Fintype E] (time : E → ℕ) (htime : Function.Injective time)
    {ε : ℝ} {δ : E → ℝ} {g : ℕ → ℕ}
    (P : ∀ e, Progress (s (time e)) (s (time e + 1)) ε (δ e) g)
    (hstep : ∀ e, D.step (time e) = (P e).subdivision)
    (node : ∀ e, (s (time e)).decomposition.flag.Node)
    (hevent : ∀ e, (P e).event = .complete (node e))
    (hlevel : ∀ e, (s (time e)).decomposition.level (node e) = L) :
    Fintype.card E ≤ Fintype.card (s 0).decomposition.flag.Node := by
  let selected : ∀ e, D.system.LowNode L (time e) := fun e ↦ ⟨node e, (hlevel e).le⟩
  apply D.system.card_killed_events_le (D.system_injectiveBelow hcut) time selected htime
  intro e y
  have hr := (P e).resolves
  rw [hevent e] at hr
  change (D.step (time e)).node y ≠ node e
  rw [hstep e]
  exact hr y.1 (by rw [hlevel e]; exact y.2)

theorem card_even_color_events_le_stopped
    {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ}
    (n : ℕ) (hstop : ∀ i, n ≤ i → s (i + 1) = s i)
    (P : ∀ i, i < n → Progress (s i) (s (i + 1)) ε (δ i) g)
    {L : ℕ} (hL : L < (d + 1) ^ 2)
    (hcolors : ∀ i hi, 2 * L ≤ (P i hi).event.color)
    {E : Type*} [Fintype E] (time : E → ℕ) (htime : Function.Injective time)
    (hbound : ∀ e, time e < n)
    (hcolor : ∀ e, (P (time e) (hbound e)).event.color = 2 * L) :
    Fintype.card E ≤ Fintype.card (s 0).decomposition.flag.Node := by
  classical
  let D := stoppedLineageMassMaps n hstop P
  have hcut : ∀ i, L ≤ D.cutoff i := stoppedLineageMassMaps_cutoff_ge n hstop P hL.le hcolors
  choose node hevent hlevel using fun e ↦
    (P (time e) (hbound e)).event.exists_complete_of_color_eq hL (hcolor e)
  exact card_complete_events_le_of_lineage D hcut time htime
    (fun e ↦ P (time e) (hbound e))
    (fun e ↦ stoppedLineageMassMaps_step n hstop P (time e) (hbound e)) node hevent hlevel

/-- The number of complete events in an interval whose colors are all at
least the selected color is bounded by the population at its left endpoint. -/
theorem card_complete_events_interval_le
    {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ} {N : ℕ}
    (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)
    (χ : ℕ → ℕ) (hχ : ∀ i (hi : i < N), χ i = (P i hi).event.color)
    {a b L : ℕ} (hab : a ≤ b) (hbN : b < N) (hL : L < (d + 1) ^ 2)
    (hcolors : ∀ i ∈ Finset.Icc a b, 2 * L ≤ χ i) :
    ((Finset.Icc a b).filter fun i ↦ χ i = 2 * L).card ≤
      Fintype.card (s a).decomposition.flag.Node := by
  classical
  let n := b + 1 - a
  have han : a + n ≤ N := by dsimp [n]; omega
  let Q := intervalProgress P a n han
  let T := (Finset.range n).filter fun i ↦ χ (a + i) = 2 * L
  have hbound : ∀ e : T, (e : ℕ) < n := fun e ↦
    Finset.mem_range.mp (Finset.mem_filter.mp e.property).1
  have hge : ∀ i hi, 2 * L ≤ (Q i hi).event.color := by
    intro i hi
    rw [intervalProgress_event_color, ← hχ]
    apply hcolors (a + i)
    apply Finset.mem_Icc.mpr
    dsimp [n] at hi
    omega
  have heq : ∀ e : T, (Q e (hbound e)).event.color = 2 * L := by
    intro e
    rw [intervalProgress_event_color, ← hχ]
    exact (Finset.mem_filter.mp e.property).2
  have hc := card_even_color_events_le_stopped n (intervalState_succ_eq s a n) Q hL hge
    (fun e : T ↦ (e : ℕ)) Subtype.val_injective hbound heq
  have hcard : Fintype.card T = ((Finset.Icc a b).filter fun i ↦ χ i = 2 * L).card := by
    rw [Fintype.card_coe]
    exact card_filter_range_offset χ a b (2 * L) hab
  rw [hcard] at hc
  simpa only [intervalState, Nat.zero_min, Nat.add_zero] using hc

variable {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ}
    (P : ∀ i, Progress (s i) (s (i + 1)) ε (δ i) g)
    {L : ℕ} (hcolors : ∀ i, 2 * L ≤ (P i).event.color)
    {E : Type*} [Fintype E]

include P hcolors

/-- Distinct complete-event times at level `L` consume distinct initial
lineages. The argument uses only the certified resolution and parent data. -/
theorem card_complete_events_le (time : E → ℕ) (htime : Function.Injective time)
    (node : ∀ e, (s (time e)).decomposition.flag.Node)
    (hevent : ∀ e, (P (time e)).event = .complete (node e))
    (hlevel : ∀ e, (s (time e)).decomposition.level (node e) = L) :
    Fintype.card E ≤ Fintype.card (s 0).decomposition.flag.Node := by
  let D := lineageMassMaps P
  have hcut : ∀ i, L ≤ D.cutoff i := cutoff_ge_of_colors_ge P hcolors
  let selected : ∀ e, D.system.LowNode L (time e) :=
    fun e ↦ ⟨node e, (hlevel e).le⟩
  apply D.system.card_killed_events_le (D.system_injectiveBelow hcut) time selected htime
  intro e y
  have hr := (P (time e)).resolves
  rw [hevent e] at hr
  exact hr y.1 (by rw [hlevel e]; exact y.2)

/-- The finite family may be specified just by its complete-event color. -/
theorem card_even_color_events_le (hL : L < (d + 1) ^ 2)
    (time : E → ℕ) (htime : Function.Injective time)
    (hcolor : ∀ e, (P (time e)).event.color = 2 * L) :
    Fintype.card E ≤ Fintype.card (s 0).decomposition.flag.Node := by
  classical
  choose node hevent hlevel using fun e ↦
    (P (time e)).event.exists_complete_of_color_eq hL (hcolor e)
  exact card_complete_events_le P hcolors time htime node hevent hlevel

end EGZ.FlagDecomposition.Iteration
