/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
import LeanPool.Sabidussi.LocalPattern
import LeanPool.Sabidussi.OddBalance
import LeanPool.Sabidussi.Parity
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.Interval.Finset.Fin

/-!
# The cyclic-word four-colouring lemma

This file is the combinatorial core of the compatibility proof.  A letter at a position records
the transition between the preceding and the current gap.  If every letter occurs at least twice,
the local patterns from `LocalPattern` and the odd balancing theorem produce colours on the gaps
such that adjacent gaps have different colours and every colour occurs evenly at each letter.
-/

namespace Sabidussi
namespace CyclicWord

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty cyclic word, represented with a chosen cut. -/
structure Word where
  /-- The word has `n + 1` positions, so it is always nonempty. -/
  n : ℕ
  /-- The letter recorded at each position. -/
  letter : Fin (n + 1) → V

namespace Word

variable (W : Word (V := V))

/-- Positions of the cyclic word. -/
abbrev Pos := Fin (W.n + 1)

/-- The position immediately preceding `i`, cyclically. -/
def prev (i : W.Pos) : W.Pos := (finRotate (W.n + 1)).symm i

/-- Occurrences of a letter. -/
abbrev Occurrence (v : V) := {i : W.Pos // W.letter i = v}

instance (v : V) : Fintype (W.Occurrence v) :=
  Subtype.fintype fun i : W.Pos ↦ W.letter i = v

/-- The two gap colours incident with an occurrence. -/
def incidentColor (x : W.Pos → Color) {v : V} (o : W.Occurrence v) (s : Fin 2) : Color :=
  if s = 0 then x (W.prev o.1) else x o.1

/-- The desired output of the cyclic-word construction. -/
structure Coloring where
  /-- The colour assigned to each gap of the cyclic word. -/
  color : W.Pos → Color
  /-- Consecutive gaps receive different colours. -/
  transition_ne : ∀ i, color (W.prev i) ≠ color i
  /-- Each colour occurs an even number of times among the incidences at every letter. -/
  color_even : ∀ (v : V) (z : Color),
    Even (Fintype.card {os : W.Occurrence v × Fin 2 // W.incidentColor color os.1 os.2 = z})

end Word

section LocalPattern

/-- The quadratic contribution of a finite ordered difference pattern. -/
def localQuadraticContribution (n : ℕ) (c : Fin 3) : F₂ :=
  (∑ i, quadratic (localDifference n c i)) +
    ∑ i, ∑ j, if j < i then bracket (localDifference n c i) (localDifference n c j) else 0

private theorem orderedPairSum_succ (k : ℕ) (f : Fin (k + 1) → Color) :
    (∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0) =
      (∑ i : Fin k, ∑ j : Fin k,
        if j < i then bracket (f i.castSucc) (f j.castSucc) else 0) +
      ∑ j : Fin k, bracket (f (Fin.last k)) (f j.castSucc) := by
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Fintype.sum_congr
    intro i
    rw [Fin.sum_univ_castSucc]
    rw [if_neg (not_lt_of_ge (Fin.castSucc_lt_last i).le)]
    simp
  · rw [Fin.sum_univ_castSucc]
    simp

/-- Polarization of `quadratic` over a linearly ordered finite family. -/
theorem quadratic_sum_fin (k : ℕ) (f : Fin k → Color) :
    quadratic (∑ i, f i) =
      (∑ i, quadratic (f i)) +
        ∑ i, ∑ j, if j < i then bracket (f i) (f j) else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, quadratic_add, ih (fun i ↦ f i.castSucc),
        Fin.sum_univ_castSucc, orderedPairSum_succ]
      rw [bracket_comm, ← sum_bracket_right]
      abel

/-- The recursively extended local patterns retain the quadratic cancellation of the pair and
triple base cases. -/
theorem localQuadraticContribution_eq_zero (n : ℕ) (c : Fin 3) :
    localQuadraticContribution n c = 0 := by
  unfold localQuadraticContribution
  rw [← quadratic_sum_fin]
  rw [sum_localDifference_occurrences]
  rfl

end LocalPattern

namespace Word

section Frames

variable (W : Word (V := V))

/-- An arbitrary enumeration of the occurrences of each letter, used only to transport the
explicit local patterns. -/
noncomputable def occurrenceOrderIsoFin
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) :
    W.Occurrence v ≃o Fin (Fintype.card (W.Occurrence v) - 2 + 2) :=
  (Fintype.orderIsoFinOfCardEq (W.Occurrence v)
    (Nat.sub_add_cancel (hmin v)).symm).symm

/-- The difference at an occurrence for one of the three local choices. -/
noncomputable def frameDifference
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (c : Fin 3) (o : W.Occurrence v) : Color :=
  localDifference (Fintype.card (W.Occurrence v) - 2) c (W.occurrenceOrderIsoFin hmin v o)

omit [Fintype V] in
theorem frameDifference_ne_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (c : Fin 3) (o : W.Occurrence v) :
    W.frameDifference hmin v c o ≠ 0 := by
  exact localDifference_ne_zero _ _ _

omit [Fintype V] in
theorem sum_frameDifference_occurrences
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    ∑ o, W.frameDifference hmin v c o = 0 := by
  rw [← (W.occurrenceOrderIsoFin hmin v).symm.toEquiv.sum_comp]
  simpa [frameDifference] using sum_localDifference_occurrences
    (Fintype.card (W.Occurrence v) - 2) c

omit [Fintype V] in
theorem sum_frameDifference_choices
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v : V) (o : W.Occurrence v) :
    ∑ c, W.frameDifference hmin v c o = 0 := by
  exact sum_localDifference_choices _ _

omit [Fintype V] in
theorem frameDifference_localQuadratic
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) (v : V) (c : Fin 3) :
    (∑ o, quadratic (W.frameDifference hmin v c o)) +
      (∑ o, ∑ p,
        if p.1 < o.1 then
          bracket (W.frameDifference hmin v c o) (W.frameDifference hmin v c p)
        else 0) = 0 := by
  let k := Fintype.card (W.Occurrence v) - 2
  let e := W.occurrenceOrderIsoFin hmin v
  change (∑ o, quadratic (localDifference k c (e o))) +
      (∑ o, ∑ p,
        if p.1 < o.1 then bracket (localDifference k c (e o)) (localDifference k c (e p))
        else 0) = 0
  have hq :
      (∑ o, quadratic (localDifference k c (e o))) =
        ∑ i : Fin (k + 2), quadratic (localDifference k c i) := by
    apply Fintype.sum_equiv e.toEquiv
    intro o
    rfl
  rw [hq]
  have hpairs :
      (∑ o, ∑ p,
        if p.1 < o.1 then bracket (localDifference k c (e o)) (localDifference k c (e p))
        else 0) =
      ∑ i : Fin (k + 2), ∑ j : Fin (k + 2),
        if j < i then bracket (localDifference k c i) (localDifference k c j) else 0 := by
    apply Fintype.sum_equiv e.toEquiv
    intro o
    apply Fintype.sum_equiv e.toEquiv
    intro p
    change (if p < o then _ else _) = (if e p < e o then _ else _)
    by_cases hpo : p < o
    · simp [hpo, (e.lt_iff_lt).mpr hpo]
    · have he : ¬ e p < e o := by simpa using hpo
      simp [hpo, he]
  rw [hpairs]
  exact localQuadraticContribution_eq_zero k c

end Frames

section Interaction

variable (W : Word (V := V))

/-- The ordered interaction between the local patterns at two letters.  The diagonal is set to
zero because the balancing theorem is phrased on all ordered pairs of letters. -/
noncomputable def interaction
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv cu : Fin 3) : F₂ :=
  if v = u then 0 else
    ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
      if j.1 < i.1 then
        bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j)
      else 0

omit [Fintype V] in
theorem interaction_symm
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv cu : Fin 3) :
    W.interaction hmin v u cv cu = W.interaction hmin u v cu cv := by
  by_cases hvu : v = u
  · subst u
    simp [interaction]
  · have hswap :
        (∑ i : W.Occurrence u, ∑ j : W.Occurrence v,
          if j.1 < i.1 then
            bracket (W.frameDifference hmin u cu i) (W.frameDifference hmin v cv j)
          else 0) =
        ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
          if i.1 < j.1 then
            bracket (W.frameDifference hmin u cu j) (W.frameDifference hmin v cv i)
          else 0 := by
      exact Finset.sum_comm
    have hsum :
        W.interaction hmin v u cv cu + W.interaction hmin u v cu cv = 0 := by
      simp only [interaction, if_neg hvu, if_neg (Ne.symm hvu)]
      rw [hswap, ← Finset.sum_add_distrib]
      simp_rw [← Finset.sum_add_distrib]
      calc
        (∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
          ((if j.1 < i.1 then
              bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j)
            else 0) +
           if i.1 < j.1 then
              bracket (W.frameDifference hmin u cu j) (W.frameDifference hmin v cv i)
            else 0)) =
            ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
              bracket (W.frameDifference hmin v cv i) (W.frameDifference hmin u cu j) := by
                apply Fintype.sum_congr
                intro i
                apply Fintype.sum_congr
                intro j
                have hij : i.1 ≠ j.1 := by
                  intro h
                  apply hvu
                  calc
                    v = W.letter i.1 := i.2.symm
                    _ = W.letter j.1 := congrArg W.letter h
                    _ = u := j.2
                rcases lt_trichotomy j.1 i.1 with hji | heq | hij'
                · simp [hji, not_lt_of_ge hji.le]
                · exact (hij heq.symm).elim
                · rw [if_neg (not_lt_of_ge hij'.le), if_pos hij', zero_add]
                  exact bracket_comm _ _
        _ = ∑ i : W.Occurrence v,
              bracket (W.frameDifference hmin v cv i)
                (∑ j : W.Occurrence u, W.frameDifference hmin u cu j) := by
              apply Fintype.sum_congr
              intro i
              exact sum_bracket_right _ _
        _ = 0 := by rw [W.sum_frameDifference_occurrences hmin u cu]; simp
    calc
      W.interaction hmin v u cv cu = W.interaction hmin v u cv cu + 0 := by simp
      _ = W.interaction hmin v u cv cu +
          (W.interaction hmin v u cv cu + W.interaction hmin u v cu cv) := by rw [hsum]
      _ = W.interaction hmin u v cu cv := by
        rw [← add_assoc, F₂_add_self, zero_add]

omit [Fintype V] in
theorem sum_interaction_choices
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (v u : V) (cv : Fin 3) :
    ∑ cu, W.interaction hmin v u cv cu = 0 := by
  by_cases hvu : v = u
  · subst u
    simp [interaction]
  · simp only [interaction, if_neg hvu]
    rw [Finset.sum_comm]
    apply Fintype.sum_eq_zero
    intro i
    rw [Finset.sum_comm]
    apply Fintype.sum_eq_zero
    intro j
    by_cases hji : j.1 < i.1
    · simp only [hji, if_pos]
      calc
        (∑ cu, bracket (W.frameDifference hmin v cv i)
            (W.frameDifference hmin u cu j)) =
            bracket (W.frameDifference hmin v cv i)
              (∑ cu, W.frameDifference hmin u cu j) := sum_bracket_right _ _
        _ = 0 := by rw [W.sum_frameDifference_choices hmin u j]; simp
    · simp [hji]

/-- The odd balancing theorem chooses one local frame at every letter so that every external
interaction obstruction vanishes. -/
theorem exists_balanced_choice
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) :
    ∃ choice : V → Fin 3,
      ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0 := by
  exact OddBalance.exists_balanced (W.interaction hmin)
    (W.interaction_symm hmin) (W.sum_interaction_choices hmin)

end Interaction

section DifferencesAndPrefixes

variable (W : Word (V := V))

/-- Differences on all positions induced by choices of the local frames. -/
noncomputable def chosenDifference
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (i : W.Pos) : Color :=
  W.frameDifference hmin (W.letter i) (choice (W.letter i)) ⟨i, rfl⟩

omit [Fintype V] in
theorem chosenDifference_ne_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (i : W.Pos) :
    W.chosenDifference hmin choice i ≠ 0 := by
  exact W.frameDifference_ne_zero hmin _ _ _

omit [Fintype V] in
theorem chosenDifference_at_occurrence
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) (o : W.Occurrence v) :
    W.chosenDifference hmin choice o.1 = W.frameDifference hmin v (choice v) o := by
  rcases o with ⟨i, hi⟩
  subst v
  rfl

omit [Fintype V] in
theorem sum_chosenDifference_occurrences
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    ∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1 = 0 := by
  calc
    (∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1) =
        ∑ o : W.Occurrence v, W.frameDifference hmin v (choice v) o := by
          apply Fintype.sum_congr
          rintro ⟨i, hi⟩
          subst v
          rfl
    _ = 0 := W.sum_frameDifference_occurrences hmin v (choice v)

omit [Fintype V] in
theorem sum_chosenDifference [Finite V]
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) :
    ∑ i, W.chosenDifference hmin choice i = 0 := by
  have : Fintype V := Fintype.ofFinite V
  let e := Equiv.sigmaFiberEquiv W.letter
  calc
    (∑ i, W.chosenDifference hmin choice i) =
        ∑ p : Σ v, W.Occurrence v, W.chosenDifference hmin choice p.2.1 := by
          symm
          simpa [e] using e.sum_comp (W.chosenDifference hmin choice)
    _ = ∑ v, ∑ o : W.Occurrence v, W.chosenDifference hmin choice o.1 := by
          exact Fintype.sum_sigma _
    _ = 0 := by
          apply Fintype.sum_eq_zero
          exact W.sum_chosenDifference_occurrences hmin choice

/-- Prefix integration of differences, with the cut placed immediately before position zero. -/
def prefixColor (y : W.Pos → Color) (i : W.Pos) : Color :=
  ∑ j ∈ Finset.Iic i, y j

omit [DecidableEq V] [Fintype V] in
theorem prefixColor_transition
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    W.prefixColor y (W.prev i) + W.prefixColor y i = y i := by
  by_cases hi : i = 0
  · subst i
    have hprev : W.prev 0 = Fin.last W.n := by
      apply (finRotate (W.n + 1)).injective
      simp [prev]
    change (∑ j ∈ Finset.Iic (W.prev 0), y j) +
        (∑ j ∈ Finset.Iic 0, y j) = y 0
    rw [hprev, show Fin.last W.n = (⊤ : W.Pos) from rfl, Finset.Iic_top]
    rw [htotal, zero_add]
    rw [show (0 : W.Pos) = ⊥ from rfl, Finset.Iic_bot]
    simp
  · have hprev : W.prev i = i - 1 := by
      exact finRotate_symm_apply i
    rw [prefixColor, prefixColor, hprev,
      Fin.Iic_sub_one_eq_Iio (Fin.pos_iff_ne_zero.mpr hi), Finset.Iic_eq_cons_Iio]
    rw [Finset.sum_cons]
    calc
      (∑ j ∈ Finset.Iio i, y j) + (y i + ∑ j ∈ Finset.Iio i, y j) =
          ((∑ j ∈ Finset.Iio i, y j) + ∑ j ∈ Finset.Iio i, y j) + y i := by abel
      _ = y i := by rw [color_add_self, zero_add]

omit [DecidableEq V] [Fintype V] in
theorem prefixColor_prev_eq_strictPrefix
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    W.prefixColor y (W.prev i) = ∑ j ∈ Finset.Iio i, y j := by
  by_cases hi : i = 0
  · subst i
    have hprev : W.prev 0 = Fin.last W.n := by
      apply (finRotate (W.n + 1)).injective
      simp [prev]
    rw [prefixColor, hprev, show Fin.last W.n = (⊤ : W.Pos) from rfl, Finset.Iic_top]
    change (∑ j, y j) = ∑ j ∈ Finset.Iio 0, y j
    rw [htotal]
    rw [show (0 : W.Pos) = ⊥ from rfl, Finset.Iio_bot]
    simp
  · have hprev : W.prev i = i - 1 := finRotate_symm_apply i
    rw [prefixColor, hprev, Fin.Iic_sub_one_eq_Iio (Fin.pos_iff_ne_zero.mpr hi)]

/-- Contribution of all earlier occurrences of `u` to occurrences of `v`. -/
def orderedLetterInteraction (y : W.Pos → Color) (v u : V) : F₂ :=
  ∑ i : W.Occurrence v, ∑ j : W.Occurrence u,
    if j.1 < i.1 then bracket (y i.1) (y j.1) else 0

/-- Partitioning earlier word positions according to their letter. -/
theorem sum_orderedLetterInteraction (y : W.Pos → Color) (v : V) :
    (∑ u, W.orderedLetterInteraction y v u) =
      ∑ i : W.Occurrence v, ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
  unfold orderedLetterInteraction
  rw [Finset.sum_comm]
  apply Fintype.sum_congr
  intro i
  let e := Equiv.sigmaFiberEquiv W.letter
  calc
    (∑ u, ∑ j : W.Occurrence u,
        if j.1 < i.1 then bracket (y i.1) (y j.1) else 0) =
        ∑ p : Σ u, W.Occurrence u,
          if p.2.1 < i.1 then bracket (y i.1) (y p.2.1) else 0 := by
            symm
            exact Fintype.sum_sigma _
    _ = ∑ j : W.Pos, if j < i.1 then bracket (y i.1) (y j) else 0 := by
          apply Fintype.sum_equiv e
          rintro ⟨u, ⟨j, hj⟩⟩
          rfl
    _ = ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
          rw [← Finset.sum_filter]
          apply Finset.sum_congr
          · ext j
            simp
          · intro j hj
            rfl

omit [Fintype V] in
theorem orderedLetterInteraction_chosen_eq_interaction
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) {v u : V} (hvu : v ≠ u) :
    W.orderedLetterInteraction (W.chosenDifference hmin choice) v u =
      W.interaction hmin v u (choice v) (choice u) := by
  unfold orderedLetterInteraction interaction
  rw [if_neg hvu]
  apply Fintype.sum_congr
  intro i
  apply Fintype.sum_congr
  intro j
  rw [W.chosenDifference_at_occurrence hmin choice v i,
    W.chosenDifference_at_occurrence hmin choice u j]

omit [Fintype V] in
theorem chosen_localQuadratic
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    (∑ i : W.Occurrence v, quadratic (W.chosenDifference hmin choice i.1)) +
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v v = 0 := by
  unfold orderedLetterInteraction
  simp_rw [W.chosenDifference_at_occurrence hmin choice v]
  exact W.frameDifference_localQuadratic hmin v (choice v)

theorem chosen_externalInteraction_eq_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    ∑ u ∈ Finset.univ.erase v,
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v u = 0 := by
  calc
    (∑ u ∈ Finset.univ.erase v,
      W.orderedLetterInteraction (W.chosenDifference hmin choice) v u) =
        ∑ u ∈ Finset.univ.erase v,
          W.interaction hmin v u (choice v) (choice u) := by
            apply Finset.sum_congr rfl
            intro u hu
            exact W.orderedLetterInteraction_chosen_eq_interaction hmin choice
              (Ne.symm (Finset.mem_erase.mp hu).1)
    _ = OddBalance.obstruction (W.interaction hmin) choice v := rfl
    _ = 0 := hbalanced v

omit [DecidableEq V] [Fintype V] in
theorem quadratic_prefix_pair
    (y : W.Pos → Color) (htotal : ∑ i, y i = 0) (i : W.Pos) :
    quadratic (W.prefixColor y (W.prev i)) + quadratic (W.prefixColor y i) =
      quadratic (y i) + bracket (y i) (W.prefixColor y (W.prev i)) := by
  let a := W.prefixColor y (W.prev i)
  let b := W.prefixColor y i
  have hab : a + b = y i := W.prefixColor_transition y htotal i
  have hbracket : bracket a b = bracket (y i) a := by
    calc
      bracket a b = bracket b a := bracket_comm _ _
      _ = bracket (a + b) a := by
        rw [bracket_add_left, bracket_self, zero_add]
      _ = bracket (y i) a := by rw [hab]
  calc
    quadratic a + quadratic b =
        (quadratic a + quadratic b + bracket a b) + bracket a b := by
          symm
          calc
            quadratic a + quadratic b + bracket a b + bracket a b =
                (quadratic a + quadratic b) + (bracket a b + bracket a b) := by abel
            _ = quadratic a + quadratic b := by rw [F₂_add_self, add_zero]
    _ = quadratic (a + b) + bracket a b := by rw [quadratic_add]
    _ = quadratic (y i) + bracket (y i) a := by rw [hab, hbracket]

/-- The balanced interaction equations are exactly the missing quadratic moment at each letter. -/
theorem quadratic_incident_sum_eq_zero
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3)
    (hbalanced : ∀ v, OddBalance.obstruction (W.interaction hmin) choice v = 0)
    (v : V) :
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, quadratic (W.incidentColor x os.1 os.2) = 0 := by
  dsimp only
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  have hstrict :
      (∑ i : W.Occurrence v, bracket (y i.1) (x (W.prev i.1))) =
        ∑ i : W.Occurrence v, ∑ j ∈ Finset.Iio i.1, bracket (y i.1) (y j) := by
    apply Fintype.sum_congr
    intro i
    rw [show x (W.prev i.1) = ∑ j ∈ Finset.Iio i.1, y j from
      W.prefixColor_prev_eq_strictPrefix y htotal i.1]
    change bracketRightHom (y i.1) (∑ j ∈ Finset.Iio i.1, y j) = _
    exact map_sum (bracketRightHom (y i.1)) y (Finset.Iio i.1)
  have hsplit :
      (∑ u, W.orderedLetterInteraction y v u) =
        (∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u) +
          W.orderedLetterInteraction y v v := by
    exact (Finset.sum_erase_add Finset.univ
      (fun u ↦ W.orderedLetterInteraction y v u) (Finset.mem_univ v)).symm
  calc
    (∑ os : W.Occurrence v × Fin 2, quadratic (W.incidentColor x os.1 os.2)) =
        ∑ i : W.Occurrence v,
          (quadratic (x (W.prev i.1)) + quadratic (x i.1)) := by
            rw [Fintype.sum_prod_type]
            apply Fintype.sum_congr
            intro i
            rw [Fin.sum_univ_two]
            rfl
    _ = ∑ i : W.Occurrence v,
          (quadratic (y i.1) + bracket (y i.1) (x (W.prev i.1))) := by
            apply Fintype.sum_congr
            intro i
            exact W.quadratic_prefix_pair y htotal i.1
    _ = (∑ i : W.Occurrence v, quadratic (y i.1)) +
          ∑ i : W.Occurrence v, bracket (y i.1) (x (W.prev i.1)) := by
            exact Finset.sum_add_distrib
    _ = (∑ i : W.Occurrence v, quadratic (y i.1)) +
          ∑ u, W.orderedLetterInteraction y v u := by
            rw [hstrict, W.sum_orderedLetterInteraction y v]
    _ = ((∑ i : W.Occurrence v, quadratic (y i.1)) +
          W.orderedLetterInteraction y v v) +
          ∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u := by
            rw [hsplit]
            abel
    _ = 0 := by
      rw [show (∑ i : W.Occurrence v, quadratic (y i.1)) +
          W.orderedLetterInteraction y v v = 0 from
            W.chosen_localQuadratic hmin choice v]
      rw [show (∑ u ∈ Finset.univ.erase v, W.orderedLetterInteraction y v u) = 0 from
        W.chosen_externalInteraction_eq_zero hmin choice hbalanced v]
      simp

omit [Fintype V] in
theorem incident_sum_eq_zero [Finite V]
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v))
    (choice : V → Fin 3) (v : V) :
    let y := W.chosenDifference hmin choice
    let x := W.prefixColor y
    ∑ os : W.Occurrence v × Fin 2, W.incidentColor x os.1 os.2 = 0 := by
  dsimp only
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  calc
    (∑ os : W.Occurrence v × Fin 2, W.incidentColor x os.1 os.2) =
        ∑ i : W.Occurrence v, (x (W.prev i.1) + x i.1) := by
          rw [Fintype.sum_prod_type]
          apply Fintype.sum_congr
          intro i
          rw [Fin.sum_univ_two]
          rfl
    _ = ∑ i : W.Occurrence v, y i.1 := by
          apply Fintype.sum_congr
          intro i
          exact W.prefixColor_transition y htotal i.1
    _ = 0 := W.sum_chosenDifference_occurrences hmin choice v

omit [Fintype V] in
/-- Every nonempty cyclic word in which each letter occurs at least twice has the required
four-colouring of its gaps. -/
theorem exists_coloring [Finite V]
    (hmin : ∀ v, 2 ≤ Fintype.card (W.Occurrence v)) : Nonempty W.Coloring := by
  have : Fintype V := Fintype.ofFinite V
  obtain ⟨choice, hbalanced⟩ := W.exists_balanced_choice hmin
  let y := W.chosenDifference hmin choice
  let x := W.prefixColor y
  have htotal : ∑ i, y i = 0 := W.sum_chosenDifference hmin choice
  refine ⟨{
    color := x
    transition_ne := ?_
    color_even := ?_ }⟩
  · intro i hxeq
    apply W.chosenDifference_ne_zero hmin choice i
    calc
      y i = x (W.prev i) + x i := (W.prefixColor_transition y htotal i).symm
      _ = 0 := by rw [hxeq, color_add_self]
  · intro v z
    let f : W.Occurrence v × Fin 2 → Color :=
      fun os ↦ W.incidentColor x os.1 os.2
    have hcard : Even (Fintype.card (W.Occurrence v × Fin 2)) := by
      rw [Fintype.card_prod, Fintype.card_fin]
      exact ⟨Fintype.card (W.Occurrence v), by omega⟩
    have hsum : ∑ os, f os = 0 := W.incident_sum_eq_zero hmin choice v
    have hquad : ∑ os, quadratic (f os) = 0 :=
      W.quadratic_incident_sum_eq_zero hmin choice hbalanced v
    have heven := colorFiber_card_even_of_moments f hcard hsum hquad z
    rw [Fintype.card_subtype]
    simpa [colorFiber, f] using heven

end DifferencesAndPrefixes

end Word

end CyclicWord
end Sabidussi
