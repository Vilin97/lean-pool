/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import LeanPool.ErdosGinzburgZiv.EGZ.Decomposition.IterationLineages

/-!
# Geometric lineages for finite progress intervals

Finite comparisons extend by identity maps after their endpoint. The
extension requires no progress certificate, event, or unsatisfied condition
at the constant stages.
-/

namespace EGZ.FlagDecomposition

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}

/-- The comparison data of one step, independently of its event. -/
structure LineageStep (Φ Ψ : FlagDecomposition p d f) where
  /-- The subdivision map sending each descendant node to its parent in the previous
  decomposition. -/
  subdivision : SubdivisionMap Φ Ψ
  /-- The largest level up to which the lineage step supplies stable and injective node
  transport. -/
  cutoff : ℕ
  level_parent : ∀ y, Φ.level (subdivision.node y) ≤ Ψ.level y
  /-- The stable node maps for descendants whose levels do not exceed the cutoff. -/
  stable : ∀ y, Ψ.level y ≤ cutoff → StableNodeMap Φ Ψ (subdivision.node y) y
  stable_real : ∀ y h, (stable y h).coord.real = subdivision.fibre y
  injective_below : Set.InjOn subdivision.node {y | Ψ.level y ≤ cutoff}

namespace LineageStep

/-- The identity lineage step with an arbitrary prescribed cutoff. -/
def refl (Φ : FlagDecomposition p d f) (K : ℕ) : LineageStep Φ Φ where
  subdivision := SubdivisionMap.refl Φ
  cutoff := K
  level_parent _ := le_rfl
  stable y _ := StableNodeMap.refl Φ y
  stable_real _ _ := rfl
  injective_below := fun _ _ _ _ h ↦ h

/-- The identity lineage step transported across an equality of decompositions. -/
def ofEq {Φ Ψ : FlagDecomposition p d f} (h : Ψ = Φ) (K : ℕ) :
    LineageStep Φ Ψ := h.symm ▸ refl Φ K

@[simp]
theorem ofEq_cutoff {Φ Ψ : FlagDecomposition p d f} (h : Ψ = Φ) (K : ℕ) :
    (ofEq h K).cutoff = K := by subst Ψ; rfl

/-- The lineage step supplied by an iteration progress certificate. -/
noncomputable def ofProgress {s t : Iteration.State p d f} {ε δ : ℝ} {g : ℕ → ℕ}
    (P : Iteration.Progress s t ε δ g) : LineageStep s.decomposition t.decomposition where
  subdivision := P.subdivision
  cutoff := P.event.cutoff
  level_parent := P.level_parent
  stable := P.stable
  stable_real := P.stable_real
  injective_below := P.parent_injective

end LineageStep

namespace LineageMassMaps

variable {Φ : ℕ → FlagDecomposition p d f}

/-- The lineage mass maps assembled from consecutive lineage steps of minimal decompositions. -/
def ofSteps (hminimal : ∀ i, (Φ i).IsMinimal)
    (D : ∀ i, LineageStep (Φ i) (Φ (i + 1))) : LineageMassMaps Φ where
  minimal := hminimal
  step i := (D i).subdivision
  cutoff i := (D i).cutoff
  level_parent i := (D i).level_parent
  stable i := (D i).stable
  stable_real i := (D i).stable_real
  injective_below i _ h := (D i).injective_below.mono (fun _ hy ↦ hy.trans h)

/-- Extend a finite list of comparisons on an already stopped sequence. -/
noncomputable def stopped (hminimal : ∀ i, (Φ i).IsMinimal) (n K : ℕ)
    (hstop : ∀ i, n ≤ i → Φ (i + 1) = Φ i)
    (D : ∀ i, i < n → LineageStep (Φ i) (Φ (i + 1))) : LineageMassMaps Φ :=
  ofSteps hminimal (fun i ↦ if h : i < n then D i h else LineageStep.ofEq (hstop i (by omega)) K)

@[simp]
theorem stopped_step_of_lt (hminimal : ∀ i, (Φ i).IsMinimal) (n K : ℕ)
    (hstop : ∀ i, n ≤ i → Φ (i + 1) = Φ i)
    (D : ∀ i, i < n → LineageStep (Φ i) (Φ (i + 1))) (i : ℕ) (hi : i < n) :
    (stopped hminimal n K hstop D).step i = (D i hi).subdivision := by
  simp only [stopped, ofSteps, dite_eq_left hi]

@[simp]
theorem stopped_cutoff_of_lt (hminimal : ∀ i, (Φ i).IsMinimal) (n K : ℕ)
    (hstop : ∀ i, n ≤ i → Φ (i + 1) = Φ i)
    (D : ∀ i, i < n → LineageStep (Φ i) (Φ (i + 1))) (i : ℕ) (hi : i < n) :
    (stopped hminimal n K hstop D).cutoff i = (D i hi).cutoff := by
  simp only [stopped, ofSteps, dite_eq_left hi]

theorem stopped_cutoff_ge (hminimal : ∀ i, (Φ i).IsMinimal) (n K : ℕ)
    (hstop : ∀ i, n ≤ i → Φ (i + 1) = Φ i)
    (D : ∀ i, i < n → LineageStep (Φ i) (Φ (i + 1))) {L : ℕ}
    (hLK : L ≤ K) (hcut : ∀ i hi, L ≤ (D i hi).cutoff) :
    ∀ i, L ≤ (stopped hminimal n K hstop D).cutoff i := by
  intro i
  by_cases hi : i < n
  · simpa only [stopped_cutoff_of_lt hminimal n K hstop D i hi] using hcut i hi
  · simpa only [stopped, ofSteps, dite_eq_right hi, LineageStep.ofEq_cutoff] using hLK

end LineageMassMaps

namespace Iteration

/-- Restart at `a` and hold the state constant after `n` further steps. -/
abbrev intervalState (s : ℕ → State p d f) (a n i : ℕ) : State p d f :=
  s (a + min i n)

theorem intervalState_eq (s : ℕ → State p d f) (a n i : ℕ) (hi : i ≤ n) :
    intervalState s a n i = s (a + i) := by simp only [intervalState, Nat.min_eq_left hi]

theorem intervalState_succ_eq (s : ℕ → State p d f) (a n i : ℕ) (hi : n ≤ i) :
    intervalState s a n (i + 1) = intervalState s a n i := by
  simp only [intervalState, Nat.min_eq_right hi, Nat.min_eq_right (by omega : n ≤ i + 1)]

variable {s : ℕ → State p d f} {ε : ℝ} {δ : ℕ → ℝ} {g : ℕ → ℕ}

/-- The geometric comparison sequence of a genuinely finite progress list. -/
noncomputable def stoppedLineageMassMaps (n : ℕ)
    (hstop : ∀ i, n ≤ i → s (i + 1) = s i)
    (P : ∀ i, i < n → Progress (s i) (s (i + 1)) ε (δ i) g) :
    LineageMassMaps (fun i ↦ (s i).decomposition) :=
  LineageMassMaps.stopped (fun i ↦ (s i).minimal) n ((d + 1) ^ 2)
    (fun i hi ↦ congrArg State.decomposition (hstop i hi))
    (fun i hi ↦ LineageStep.ofProgress (P i hi))

@[simp]
theorem stoppedLineageMassMaps_step (n : ℕ)
    (hstop : ∀ i, n ≤ i → s (i + 1) = s i)
    (P : ∀ i, i < n → Progress (s i) (s (i + 1)) ε (δ i) g)
    (i : ℕ) (hi : i < n) :
    (stoppedLineageMassMaps n hstop P).step i = (P i hi).subdivision :=
  LineageMassMaps.stopped_step_of_lt _ _ _ _ _ i hi

theorem stoppedLineageMassMaps_cutoff_ge (n : ℕ)
    (hstop : ∀ i, n ≤ i → s (i + 1) = s i)
    (P : ∀ i, i < n → Progress (s i) (s (i + 1)) ε (δ i) g)
    {L : ℕ} (hL : L ≤ (d + 1) ^ 2)
    (hcolors : ∀ i hi, 2 * L ≤ (P i hi).event.color) :
    ∀ i, L ≤ (stoppedLineageMassMaps n hstop P).cutoff i :=
  LineageMassMaps.stopped_cutoff_ge _ _ _ _ _ hL
    (fun i hi ↦ (P i hi).event.cutoff_ge_of_color_ge (hcolors i hi))

variable {N : ℕ} (P : ∀ i, i < N → Progress (s i) (s (i + 1)) ε (δ i) g)

/-- Transport a progress certificate across equalities of its source and target states. -/
def Progress.castStates {s t s' t' : State p d f} {ε δ : ℝ} {g : ℕ → ℕ}
    (Q : Progress s t ε δ g) (hs : s' = s) (ht : t' = t) : Progress s' t' ε δ g :=
  hs.symm ▸ ht.symm ▸ Q

@[simp]
theorem Progress.castStates_event_color {s t s' t' : State p d f} {ε δ : ℝ} {g : ℕ → ℕ}
    (Q : Progress s t ε δ g) (hs : s' = s) (ht : t' = t) :
    (Q.castStates hs ht).event.color = Q.event.color := by
  subst s'
  subst t'
  rfl

/-- A genuine original progress certificate on a shifted, stopped interval. -/
def intervalProgress (a n : ℕ) (h : a + n ≤ N) (i : ℕ) (hi : i < n) :
    Progress (intervalState s a n i) (intervalState s a n (i + 1)) ε (δ (a + i)) g :=
  (P (a + i) (by omega)).castStates (intervalState_eq s a n i hi.le)
    (by rw [intervalState_eq s a n (i + 1) (by omega), Nat.add_assoc])

@[simp]
theorem intervalProgress_event_color (a n : ℕ) (h : a + n ≤ N) (i : ℕ) (hi : i < n) :
    (intervalProgress P a n h i hi).event.color = (P (a + i) (by omega)).event.color := by
  exact Progress.castStates_event_color _ _ _

/-- The lineage mass maps for a finite interval of an iteration, held constant after its
endpoint. -/
noncomputable def intervalLineageMassMaps (a n : ℕ) (h : a + n ≤ N) :
    LineageMassMaps (fun i ↦ (intervalState s a n i).decomposition) :=
  stoppedLineageMassMaps n (intervalState_succ_eq s a n) (intervalProgress P a n h)

@[simp]
theorem intervalLineageMassMaps_step (a n : ℕ) (h : a + n ≤ N) (i : ℕ) (hi : i < n) :
    (intervalLineageMassMaps P a n h).step i = (intervalProgress P a n h i hi).subdivision :=
  stoppedLineageMassMaps_step n _ _ i hi

theorem intervalLineageMassMaps_cutoff_ge (a n : ℕ) (h : a + n ≤ N)
    {L : ℕ} (hL : L ≤ (d + 1) ^ 2)
    (hcolors : ∀ i (hi : i < n), 2 * L ≤ (P (a + i) (by omega)).event.color) :
    ∀ i, L ≤ (intervalLineageMassMaps P a n h).cutoff i := by
  apply stoppedLineageMassMaps_cutoff_ge n _ _ hL
  intro i hi
  simpa only [intervalProgress_event_color] using hcolors i hi

end Iteration
end EGZ.FlagDecomposition
