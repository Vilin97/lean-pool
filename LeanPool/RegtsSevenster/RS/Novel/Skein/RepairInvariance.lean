/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TransitionMove
import LeanPool.RegtsSevenster.RS.Novel.Skein.OrientationFlip

/-!
# Invariance of the constrained summand under the repair move

What one elementary 2-opt re-pairing move
(`RelTransitionSystem.repair`) does to the corrected constrained
summand (`throughSummand`).

## Main results

* `MixedFunctional.evalOdd_transpose` — transposing two entries of
  an odd list (at arbitrary positions) negates the alternating
  evaluation, unconditionally.
* `EdgeSubset.openCircuitCount_matchEq` and
  `EdgeSubset.throughSummand_ofMatchEq` — matching-equal systems
  have equal open circuit counts and equal summands (over the
  transported orientation).
* `EdgeSubset.throughSummand_transportRepair` — **the vertex-`v`
  ledger**: in the separated case (`isOut c = !isOut a`, where the
  orientation transports unchanged), one repair move negates the
  constrained summand at every fixed circuit exponent.  The two
  changed pair-blocks at `v` swap their partner entries — one list
  transposition — while the sign factors merely commute.
* `EdgeSubset.throughSummand_repair` — the move preserves the
  summand at the open circuit counts whenever the count parity
  flips (`Odd (count κ + count κ')`), by the ledger above.

## Why the count-parity hypothesis is needed

The count-parity hypothesis of `throughSummand_repair` cannot be
dropped.  A move whose four flags lie on two distinct
boundary-terminated paths leaves `openCircuitCount` unchanged while
the ledger still negates the summand, so on such squares the
per-move invariance fails.  It fails for the reason orientation
invariance is restricted to differences on fully internal edges
(`throughSummand_orientation_invariant` in `OrientationFlip.lean`):
a two-path square re-pairs which boundary ends chain together, and
the two pairings differ in sign.  The
two-path squares are handled instead by the pathSign-corrected
ledger of `PathLedger.lean`, whose statements weigh the summand by
the boundary pairing's chord sign.
-/

namespace RS

open scoped Classical

/-! ## List helpers -/

section ListHelpers

variable {γ δ : Type*}

/-- Pointwise-equal block functions give equal `flatMap`s. -/
private theorem flatMap_congr_mem {l : List γ} {g g' : γ → List δ}
    (h : ∀ x ∈ l, g x = g' x) : l.flatMap g = l.flatMap g' := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.flatMap_cons, List.flatMap_cons,
      h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

/-- `attachWith` over propositionally equal lists. -/
private theorem attachWith_congr {l₁ l₂ : List γ} (h : l₁ = l₂)
    {p : γ → Prop} (H₁ : ∀ x ∈ l₁, p x) :
    l₁.attachWith p H₁ = l₂.attachWith p (h ▸ H₁) := by
  subst h; rfl

/-- `attachWith` preserves `Nodup`. -/
private theorem nodup_attachWith {p : γ → Prop} :
    ∀ {l : List γ}, l.Nodup → ∀ (H : ∀ x ∈ l, p x),
      (l.attachWith p H).Nodup
  | [], _, _ => List.nodup_nil
  | a :: t, hnd, H => by
    rw [List.attachWith_cons, List.nodup_cons]
    rw [List.nodup_cons] at hnd
    exact ⟨fun hmem => hnd.1 ((List.mem_attachWith _ _).mp hmem),
      nodup_attachWith hnd.2 _⟩

/-- A list with a repeated element is not `Nodup`. -/
private theorem not_nodup_two (l₁ l₂ l₃ : List γ) (x : γ) :
    ¬ (l₁ ++ x :: (l₂ ++ x :: l₃)).Nodup := by
  intro hnd
  have h2 : (x :: (l₂ ++ x :: l₃)).Nodup :=
    (List.nodup_append.mp hnd).2.1
  rw [List.nodup_cons] at h2
  exact h2.1 (List.mem_append_right _ List.mem_cons_self)

/-- Split a list at two distinct members, in one of the two
orders. -/
private theorem exists_two_split {l : List γ} {u w : γ}
    (hu : u ∈ l) (hw : w ∈ l) (huw : u ≠ w) :
    (∃ P Q R, l = P ++ u :: (Q ++ w :: R)) ∨
      (∃ P Q R, l = P ++ w :: (Q ++ u :: R)) := by
  obtain ⟨P, t, rfl⟩ := List.append_of_mem hu
  rcases List.mem_append.mp hw with hwP | hwt
  · obtain ⟨P₁, P₂, rfl⟩ := List.append_of_mem hwP
    right
    exact ⟨P₁, P₂, t, by simp⟩
  · have hwt' : w ∈ t := by
      rcases List.mem_cons.mp hwt with h | h
      · exact absurd h.symm huw
      · exact h
    obtain ⟨Q, R, rfl⟩ := List.append_of_mem hwt'
    left
    exact ⟨P, Q, R, rfl⟩

/-- Distinctness facts from `Nodup` of a two-point split. -/
private theorem split_facts {P Q R : List γ} {u w : γ}
    (hnd : (P ++ u :: (Q ++ w :: R)).Nodup) :
    (∀ f ∈ P, f ≠ u ∧ f ≠ w) ∧ (∀ f ∈ Q, f ≠ u ∧ f ≠ w) ∧
      (∀ f ∈ R, f ≠ u ∧ f ≠ w) := by
  rw [List.nodup_append] at hnd
  obtain ⟨-, hnd2, hdisj⟩ := hnd
  rw [List.nodup_cons] at hnd2
  obtain ⟨hu_nin, hnd3⟩ := hnd2
  rw [List.nodup_append] at hnd3
  obtain ⟨-, hnd4, hdisjQ⟩ := hnd3
  rw [List.nodup_cons] at hnd4
  refine ⟨fun f hf => ⟨?_, ?_⟩, fun f hf => ⟨?_, ?_⟩,
    fun f hf => ⟨?_, ?_⟩⟩
  · exact hdisj f hf u List.mem_cons_self
  · exact hdisj f hf w (List.mem_cons_of_mem _
      (List.mem_append_right _ List.mem_cons_self))
  · intro he
    exact hu_nin (List.mem_append_left _ (he ▸ hf))
  · exact hdisjQ f hf w List.mem_cons_self
  · intro he
    exact hu_nin (List.mem_append_right _
      (List.mem_cons_of_mem _ (he ▸ hf)))
  · intro he
    exact hnd4.1 (he ▸ hf)

end ListHelpers

/-! ## The transposition lemma for the alternating evaluation -/

/-- **Transposing two entries** of an odd list, at arbitrary
positions, negates the alternating evaluation.  Unconditional: when
the two entries are equal both sides vanish on the duplicate. -/
theorem MixedFunctional.evalOdd_transpose {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    (l₂ : List (Fin (2 * ℓ))) :
    ∀ (l₁ l₃ : List (Fin (2 * ℓ))) (x y : Fin (2 * ℓ)),
      hM.evalOdd μ (l₁ ++ y :: (l₂ ++ x :: l₃)) =
        -hM.evalOdd μ (l₁ ++ x :: (l₂ ++ y :: l₃)) := by
  induction l₂ with
  | nil =>
    intro l₁ l₃ x y
    simp only [List.nil_append]
    by_cases hxy : x = y
    · subst hxy
      have h0 := not_nodup_two l₁ [] l₃ x
      simp only [List.nil_append] at h0
      rw [hM.evalOdd_of_not_nodup μ h0, neg_zero]
    · exact hM.evalOdd_swap_adjacent μ l₁ l₃ hxy
  | cons z l₂' ih =>
    intro l₁ l₃ x y
    simp only [List.cons_append]
    by_cases hzy : z = y
    · subst hzy
      have h1 := not_nodup_two l₁ [] (l₂' ++ x :: l₃) z
      simp only [List.nil_append] at h1
      rw [hM.evalOdd_of_not_nodup μ h1]
      have h2 := not_nodup_two (l₁ ++ [x]) l₂' l₃ z
      simp only [List.append_assoc, List.cons_append,
        List.nil_append] at h2
      rw [hM.evalOdd_of_not_nodup μ h2, neg_zero]
    · by_cases hzx : z = x
      · subst hzx
        have h1 := not_nodup_two (l₁ ++ [y]) l₂' l₃ z
        simp only [List.append_assoc, List.cons_append,
          List.nil_append] at h1
        rw [hM.evalOdd_of_not_nodup μ h1]
        have h2 := not_nodup_two l₁ [] (l₂' ++ y :: l₃) z
        simp only [List.nil_append] at h2
        rw [hM.evalOdd_of_not_nodup μ h2, neg_zero]
      · have hswap1 :
            hM.evalOdd μ (l₁ ++ y :: z :: (l₂' ++ x :: l₃)) =
              -hM.evalOdd μ (l₁ ++ z :: y :: (l₂' ++ x :: l₃)) :=
          hM.evalOdd_swap_adjacent μ l₁ (l₂' ++ x :: l₃) hzy
        have hih := ih (l₁ ++ [z]) l₃ x y
        simp only [List.append_assoc, List.cons_append,
          List.nil_append] at hih
        have hswap2 :
            hM.evalOdd μ (l₁ ++ z :: x :: (l₂' ++ y :: l₃)) =
              -hM.evalOdd μ (l₁ ++ x :: z :: (l₂' ++ y :: l₃)) :=
          hM.evalOdd_swap_adjacent μ l₁ (l₂' ++ y :: l₃)
            (fun he => hzx he.symm)
        calc hM.evalOdd μ (l₁ ++ y :: z :: (l₂' ++ x :: l₃))
            = -hM.evalOdd μ (l₁ ++ z :: y :: (l₂' ++ x :: l₃)) :=
              hswap1
          _ = hM.evalOdd μ (l₁ ++ z :: x :: (l₂' ++ y :: l₃)) := by
              rw [hih]; ring
          _ = -hM.evalOdd μ (l₁ ++ x :: z :: (l₂' ++ y :: l₃)) :=
              hswap2

/-! ## The two-block swap ledger -/

section SwapLedger

variable {γ : Type*}

/-- **The pair-block swap**: exchanging the second entries of two
pair blocks in a `flatMap` of blocks negates the alternating
evaluation. -/
private theorem evalOdd_flatMap_swap {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    (g g' : γ → List (Fin (2 * ℓ))) (u w : γ) (huw : u ≠ w)
    (cu cw x y : Fin (2 * ℓ))
    (hgu : g u = [cu, x]) (hgw : g w = [cw, y])
    (hgu' : g' u = [cu, y]) (hgw' : g' w = [cw, x])
    {l : List γ} (hnd : l.Nodup) (hu : u ∈ l) (hw : w ∈ l)
    (hoff : ∀ f ∈ l, f ≠ u → f ≠ w → g' f = g f) :
    hM.evalOdd μ (l.flatMap g') = -hM.evalOdd μ (l.flatMap g) := by
  rcases exists_two_split hu hw huw with
    ⟨P, Q, R, rfl⟩ | ⟨P, Q, R, rfl⟩
  · obtain ⟨fP, fQ, fR⟩ := split_facts hnd
    have hP : P.flatMap g' = P.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fP f hf).1 (fP f hf).2)
    have hQ : Q.flatMap g' = Q.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fQ f hf).1 (fQ f hf).2)
    have hR : R.flatMap g' = R.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fR f hf).1 (fR f hf).2)
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hgu, hgw, hgu', hgw', hP, hQ, hR]
    have key := hM.evalOdd_transpose μ (Q.flatMap g ++ [cw])
      (P.flatMap g ++ [cu]) (R.flatMap g) x y
    simp only [List.append_assoc, List.cons_append,
      List.nil_append] at key ⊢
    exact key
  · obtain ⟨fP, fQ, fR⟩ := split_facts hnd
    have hP : P.flatMap g' = P.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fP f hf).2 (fP f hf).1)
    have hQ : Q.flatMap g' = Q.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fQ f hf).2 (fQ f hf).1)
    have hR : R.flatMap g' = R.flatMap g :=
      flatMap_congr_mem (fun f hf =>
        hoff f (by simp [hf]) (fR f hf).2 (fR f hf).1)
    simp only [List.flatMap_append, List.flatMap_cons]
    rw [hgu, hgw, hgu', hgw', hP, hQ, hR]
    have key := hM.evalOdd_transpose μ (Q.flatMap g ++ [cu])
      (P.flatMap g ++ [cw]) (R.flatMap g) y x
    simp only [List.append_assoc, List.cons_append,
      List.nil_append] at key ⊢
    exact key

/-- Swapping two values of a sign function leaves the list product
unchanged. -/
private theorem prod_map_swap (s s' : γ → ℤ) (u w : γ)
    (huw : u ≠ w) (hsu : s' u = s w) (hsw : s' w = s u)
    {l : List γ} (hnd : l.Nodup) (hu : u ∈ l) (hw : w ∈ l)
    (hoff : ∀ f ∈ l, f ≠ u → f ≠ w → s' f = s f) :
    (l.map s').prod = (l.map s).prod := by
  rcases exists_two_split hu hw huw with
    ⟨P, Q, R, rfl⟩ | ⟨P, Q, R, rfl⟩
  · obtain ⟨fP, fQ, fR⟩ := split_facts hnd
    simp only [List.map_append, List.map_cons, List.prod_append,
      List.prod_cons]
    rw [hsu, hsw,
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fP f hf).1 (fP f hf).2),
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fQ f hf).1 (fQ f hf).2),
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fR f hf).1 (fR f hf).2)]
    ring
  · obtain ⟨fP, fQ, fR⟩ := split_facts hnd
    simp only [List.map_append, List.map_cons, List.prod_append,
      List.prod_cons]
    rw [hsu, hsw,
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fP f hf).2 (fP f hf).1),
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fQ f hf).2 (fQ f hf).1),
      List.map_congr_left (fun f hf =>
        hoff f (by simp [hf]) (fR f hf).2 (fR f hf).1)]
    ring

end SwapLedger

/-! ## Orientation-local congruence for the vertex data -/

namespace EdgeSubset

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}

/-- The in-flag list depends on the orientation only through
`isOut`. -/
theorem relInFlagsAt_congr {κ₁ κ₂ : F.RelTransitionSystem}
    {o₁ : κ₁.Orientation} {o₂ : κ₂.Orientation}
    (hiso : o₁.isOut = o₂.isOut) (vv : W.Vertex) :
    F.relInFlagsAt o₁ vv = F.relInFlagsAt o₂ vv := by
  letI := W.flagOrder
  letI := Classical.dec
  unfold EdgeSubset.relInFlagsAt
  have hfil : F.flags.filter
      (fun f => W.attach f = Sum.inl vv ∧ o₁.isOut f = false) =
      F.flags.filter
        (fun f => W.attach f = Sum.inl vv ∧ o₂.isOut f = false) :=
    Finset.filter_congr (fun f _ => by rw [hiso])
  exact congrArg (fun s : Finset W.Flag => s.sort (· ≤ ·)) hfil

/-- The pair block at a flag, with the matched value evaluated. -/
private theorem coreOddPairFn_eq_of_match {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) {m : W.Flag}
    (hm : κ.match_ f.val = m) (hmi : m ∈ F.coreFlags) :
    F.coreOddPairFn κ φ f =
      [φ.val ⟨f.val, F.internalFlags_subset_coreFlags f.prop⟩,
        oddPartner ℓ (φ.val ⟨m, hmi⟩)] := by
  subst hm
  rfl

/-- The sign factor at a flag, with the matched value evaluated. -/
private theorem coreOddSignFn_eq_of_match {ℓ : ℕ}
    {κ : F.RelTransitionSystem} (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) {m : W.Flag}
    (hm : κ.match_ f.val = m) (hmi : m ∈ F.coreFlags) :
    F.coreOddSignFn κ φ f = oddPartnerSign ℓ (φ.val ⟨m, hmi⟩) := by
  subst hm
  rfl

/-- The vertex odd list depends only on `isOut` and the matching
at internal flags. -/
theorem coreOddListAt_congr {ℓ : ℕ}
    {κ₁ κ₂ : F.RelTransitionSystem}
    {o₁ : κ₁.Orientation} {o₂ : κ₂.Orientation}
    (hiso : o₁.isOut = o₂.isOut)
    (hmatch : ∀ f ∈ F.internalFlags, κ₁.match_ f = κ₂.match_ f)
    (φ : F.CoreOddColouring ℓ) (vv : W.Vertex) :
    F.coreOddListAt o₁ φ vv = F.coreOddListAt o₂ φ vv := by
  unfold EdgeSubset.coreOddListAt
  rw [attachWith_congr (relInFlagsAt_congr hiso vv)]
  exact flatMap_congr_mem (fun f _ => by
    rw [coreOddPairFn_eq_of_match φ f (hmatch f.val f.prop)
        (F.internalFlags_subset_coreFlags (κ₂.match_mem _ f.prop)),
      coreOddPairFn_eq_of_match φ f rfl
        (F.internalFlags_subset_coreFlags (κ₂.match_mem _ f.prop))])

/-- The vertex sign depends only on `isOut` and the matching at
internal flags. -/
theorem coreOddSignAt_congr {ℓ : ℕ}
    {κ₁ κ₂ : F.RelTransitionSystem}
    {o₁ : κ₁.Orientation} {o₂ : κ₂.Orientation}
    (hiso : o₁.isOut = o₂.isOut)
    (hmatch : ∀ f ∈ F.internalFlags, κ₁.match_ f = κ₂.match_ f)
    (φ : F.CoreOddColouring ℓ) (vv : W.Vertex) :
    F.coreOddSignAt o₁ φ vv = F.coreOddSignAt o₂ φ vv := by
  unfold EdgeSubset.coreOddSignAt
  rw [attachWith_congr (relInFlagsAt_congr hiso vv)]
  refine congrArg List.prod
    (List.map_congr_left (fun f _ => ?_))
  rw [coreOddSignFn_eq_of_match φ f (hmatch f.val f.prop)
      (F.internalFlags_subset_coreFlags (κ₂.match_mem _ f.prop)),
    coreOddSignFn_eq_of_match φ f rfl
      (F.internalFlags_subset_coreFlags (κ₂.match_mem _ f.prop))]

/-- The through summand depends only on `isOut`, the matching at
internal flags, and the circuit exponent. -/
theorem throughSummand_congr [LinearOrder α] {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ : F.RelTransitionSystem}
    {o₁ : κ₁.Orientation} {o₂ : κ₂.Orientation}
    (hiso : o₁.isOut = o₂.isOut)
    (hmatch : ∀ f ∈ F.internalFlags, κ₁.match_ f = κ₂.match_ f)
    (n : ℕ) :
    F.throughSummand hM st hbnd o₁ n =
      F.throughSummand hM st hbnd o₂ n := by
  unfold EdgeSubset.throughSummand
  refine congrArg _ (Finset.sum_congr rfl (fun ψ _ => ?_))
  refine if_congr Iff.rfl (Finset.sum_congr rfl (fun φ _ => ?_)) rfl
  refine if_congr Iff.rfl (Finset.prod_congr rfl (fun vv _ => ?_))
    rfl
  rw [coreOddSignAt_congr hiso hmatch φ vv,
    coreOddListAt_congr hiso hmatch φ vv]

/-! ## The MatchEq layer -/

/-- Along a `κ₁`-periodic walk, matching-equal systems walk
identically. -/
theorem iterWalk_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) {f : W.Flag}
    (hper : κ₁.PeriodicFlag f) (j : ℕ) :
    iterWalk κ₂ f j = iterWalk κ₁ f j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [iterWalk_succ, iterWalk_succ, ih]
    exact (heq _ (all_pairings_internal_of_periodic κ₁ hper j)).symm

/-- Periodicity transfers across matching equality. -/
theorem RelTransitionSystem.PeriodicFlag.matchEq
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂)
    {f : W.Flag} (hper : κ₁.PeriodicFlag f) :
    κ₂.PeriodicFlag f := by
  obtain ⟨hint, n, hn1, hcont, hperiod⟩ := hper
  have hper' : κ₁.PeriodicFlag f := ⟨hint, n, hn1, hcont, hperiod⟩
  refine ⟨hint, n, hn1, fun j hj => ?_, ?_⟩
  · rw [iterWalk_matchEq heq hper' j]
    exact hcont j hj
  · rw [iterWalk_matchEq heq hper' n]
    exact hperiod

/-- Matching-equal systems have the same periodic flags. -/
theorem periodicFlags_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) :
    κ₁.periodicFlags = κ₂.periodicFlags := by
  ext f
  rw [κ₁.mem_periodicFlags, κ₂.mem_periodicFlags]
  exact ⟨fun h => h.matchEq heq, fun h => h.matchEq heq.symm⟩

/-- The carrier equivalence of `periodicFlags_matchEq`. -/
noncomputable def periodicEquivMatchEq
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂) :
    {f : W.Flag // f ∈ κ₁.periodicFlags} ≃
      {f : W.Flag // f ∈ κ₂.periodicFlags} :=
  Equiv.subtypeEquivRight (fun f => by
    rw [periodicFlags_matchEq heq])

/-- The periodic walk permutations agree across matching
equality. -/
theorem walkPermPeriodic_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) :
    κ₂.walkPermPeriodic =
      (periodicEquivMatchEq heq).permCongr κ₁.walkPermPeriodic := by
  apply Equiv.ext
  rintro ⟨f, hf⟩
  apply Subtype.ext
  have hper₂ : κ₂.PeriodicFlag f := κ₂.mem_periodicFlags.mp hf
  have hpint : W.pairing f ∈ F.internalFlags := by
    have h0 := all_pairings_internal_of_periodic κ₂ hper₂ 0
    simpa using h0
  show κ₂.match_ (W.pairing f) = _
  exact (heq _ hpint).symm.trans rfl

/-- **Matching-equal systems have equal open circuit counts.** -/
theorem openCircuitCount_matchEq {κ₁ κ₂ : F.RelTransitionSystem}
    (heq : κ₁.MatchEq κ₂) :
    κ₂.openCircuitCount = κ₁.openCircuitCount := by
  unfold RelTransitionSystem.openCircuitCount
  rw [walkPermPeriodic_matchEq heq, cycleType_permCongr,
    card_fixedPoints_permCongr]

/-- **Matching-equal systems have equal summands** over the
transported orientation, at every circuit exponent. -/
theorem throughSummand_ofMatchEq [LinearOrder α] {k ℓ : ℕ}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂)
    (o : κ₁.Orientation) (n : ℕ) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.ofMatchEq heq o) n =
      F.throughSummand hM st hbnd o n :=
  throughSummand_congr
    (o₁ := RelTransitionSystem.Orientation.ofMatchEq heq o)
    (o₂ := o) hM st hbnd rfl (fun f hf => (heq f hf).symm) n

/-! ## The repair ledger at the vertex -/

section RepairLedger

variable {k ℓ : ℕ} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex}

/-- The transported orientation keeps `isOut`. -/
private theorem isOut_transportRepair (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a) :
    (RelTransitionSystem.Orientation.transportRepair hsq o
      hflip).isOut = o.isOut := rfl

/-- `b` is oriented opposite to `a`. -/
private theorem isOut_b_eq (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) : o.isOut b = !o.isOut a := by
  rw [← hsq.hab]
  exact o.match_flip a hsq.ha

/-- In the separated case, `d` is oriented like `a`. -/
private theorem isOut_d_eq (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hflip : o.isOut c = !o.isOut a) :
    o.isOut d = o.isOut a := by
  have hd : o.isOut d = !o.isOut c := by
    rw [← hsq.hcd]
    exact o.match_flip c hsq.hc
  rw [hd, hflip, Bool.not_not]

/-- Away from the move's vertex, the odd list is untouched. -/
private theorem coreOddListAt_transportRepair_ne
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (φ : F.CoreOddColouring ℓ)
    {vv : W.Vertex} (hvv : vv ≠ v) :
    F.coreOddListAt
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) φ vv =
      F.coreOddListAt o φ vv := by
  unfold EdgeSubset.coreOddListAt
  rw [attachWith_congr (relInFlagsAt_congr
    (isOut_transportRepair hsq o hflip) vv)]
  refine flatMap_congr_mem (fun f hf => ?_)
  have hfmem : f.val ∈ F.relInFlagsAt o vv :=
    (List.mem_attachWith _ _).mp hf
  have hatt : W.attach f.val = Sum.inl vv :=
    (mem_relInFlagsAt_iff.mp hfmem).2.1
  have hne : ∀ g, W.attach g = Sum.inl v → f.val ≠ g := by
    intro g hg he
    rw [he, hg] at hatt
    exact hvv (Sum.inl.inj hatt).symm
  rw [coreOddPairFn_eq_of_match φ f
      (RelTransitionSystem.repair_match_of_ne hsq
        (hne a hsq.hav) (hne b hsq.hbv) (hne c hsq.hcv)
        (hne d hsq.hdv))
      (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)),
    coreOddPairFn_eq_of_match φ f rfl
      (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop))]

/-- Away from the move's vertex, the sign is untouched. -/
private theorem coreOddSignAt_transportRepair_ne
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (φ : F.CoreOddColouring ℓ)
    {vv : W.Vertex} (hvv : vv ≠ v) :
    F.coreOddSignAt
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) φ vv =
      F.coreOddSignAt o φ vv := by
  unfold EdgeSubset.coreOddSignAt
  rw [attachWith_congr (relInFlagsAt_congr
    (isOut_transportRepair hsq o hflip) vv)]
  refine congrArg List.prod
    (List.map_congr_left (fun f hf => ?_))
  have hfmem : f.val ∈ F.relInFlagsAt o vv :=
    (List.mem_attachWith _ _).mp hf
  have hatt : W.attach f.val = Sum.inl vv :=
    (mem_relInFlagsAt_iff.mp hfmem).2.1
  have hne : ∀ g, W.attach g = Sum.inl v → f.val ≠ g := by
    intro g hg he
    rw [he, hg] at hatt
    exact hvv (Sum.inl.inj hatt).symm
  rw [coreOddSignFn_eq_of_match φ f
      (RelTransitionSystem.repair_match_of_ne hsq
        (hne a hsq.hav) (hne b hsq.hbv) (hne c hsq.hcv)
        (hne d hsq.hdv))
      (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)),
    coreOddSignFn_eq_of_match φ f rfl
      (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop))]

/-- At the move's vertex, the sign factors merely commute. -/
private theorem coreOddSignAt_transportRepair_v
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (φ : F.CoreOddColouring ℓ) :
    F.coreOddSignAt
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) φ v =
      F.coreOddSignAt o φ v := by
  unfold EdgeSubset.coreOddSignAt
  rw [attachWith_congr (relInFlagsAt_congr
    (isOut_transportRepair hsq o hflip) v)]
  have hndL : (F.relInFlagsAt o v).Nodup := relInFlagsAt_nodup o v
  -- ═══════ THE DIRECTION AT `a` ═══════
  -- It decides which of the square's flags the vertex enumerates,
  -- and the repaired enumeration differs from it by one
  -- transposition either way.
  cases hxa : o.isOut a with
  | false =>
    have hain : a ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.ha, hsq.hav, hxa⟩
    have hdin : d ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hd, hsq.hdv, by
          rw [isOut_d_eq hsq o hflip, hxa]⟩
    have hbout : o.isOut b = true := by
      rw [isOut_b_eq hsq o, hxa, Bool.not_false]
    have hcout : o.isOut c = true := by
      rw [hflip, hxa, Bool.not_false]
    refine prod_map_swap _ _ (⟨a, hsq.ha⟩ :
        {f : W.Flag // f ∈ F.internalFlags}) ⟨d, hsq.hd⟩
      (fun he => hsq.had (congrArg Subtype.val he)) ?_ ?_
      (nodup_attachWith hndL _)
      ((List.mem_attachWith _ _).mpr hain)
      ((List.mem_attachWith _ _).mpr hdin)
      (fun f hf hfu hfw => ?_)
    · rw [coreOddSignFn_eq_of_match φ _
          (RelTransitionSystem.repair_match_a hsq)
          (F.internalFlags_subset_coreFlags hsq.hc),
        coreOddSignFn_eq_of_match φ _ hsq.hmd
          (F.internalFlags_subset_coreFlags hsq.hc)]
    · rw [coreOddSignFn_eq_of_match φ _
          (RelTransitionSystem.repair_match_d hsq)
          (F.internalFlags_subset_coreFlags hsq.hb),
        coreOddSignFn_eq_of_match φ _ hsq.hab
          (F.internalFlags_subset_coreFlags hsq.hb)]
    · have hfmem : f.val ∈ F.relInFlagsAt o v :=
        (List.mem_attachWith _ _).mp hf
      have hisoutf : o.isOut f.val = false :=
        (mem_relInFlagsAt_iff.mp hfmem).2.2
      have hnev : ∀ g, o.isOut g = true → f.val ≠ g := by
        intro g hg he
        rw [he, hg] at hisoutf
        cases hisoutf
      rw [coreOddSignFn_eq_of_match φ f
          (RelTransitionSystem.repair_match_of_ne hsq
            (fun he => hfu (Subtype.ext he)) (hnev b hbout)
            (hnev c hcout) (fun he => hfw (Subtype.ext he)))
          (F.internalFlags_subset_coreFlags
            (κ.match_mem _ f.prop)),
        coreOddSignFn_eq_of_match φ f rfl
          (F.internalFlags_subset_coreFlags
            (κ.match_mem _ f.prop))]
  | true =>
    have hbin : b ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hb, hsq.hbv, by
          rw [isOut_b_eq hsq o, hxa, Bool.not_true]⟩
    have hcin : c ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hc, hsq.hcv, by
          rw [hflip, hxa, Bool.not_true]⟩
    have hdout : o.isOut d = true := by
      rw [isOut_d_eq hsq o hflip, hxa]
    refine prod_map_swap _ _ (⟨b, hsq.hb⟩ :
        {f : W.Flag // f ∈ F.internalFlags}) ⟨c, hsq.hc⟩
      (fun he => hsq.hbc (congrArg Subtype.val he)) ?_ ?_
      (nodup_attachWith hndL _)
      ((List.mem_attachWith _ _).mpr hbin)
      ((List.mem_attachWith _ _).mpr hcin)
      (fun f hf hfu hfw => ?_)
    · rw [coreOddSignFn_eq_of_match φ _
          (RelTransitionSystem.repair_match_b hsq)
          (F.internalFlags_subset_coreFlags hsq.hd),
        coreOddSignFn_eq_of_match φ _ hsq.hcd
          (F.internalFlags_subset_coreFlags hsq.hd)]
    · rw [coreOddSignFn_eq_of_match φ _
          (RelTransitionSystem.repair_match_c hsq)
          (F.internalFlags_subset_coreFlags hsq.ha),
        coreOddSignFn_eq_of_match φ _ hsq.hmb
          (F.internalFlags_subset_coreFlags hsq.ha)]
    · have hfmem : f.val ∈ F.relInFlagsAt o v :=
        (List.mem_attachWith _ _).mp hf
      have hisoutf : o.isOut f.val = false :=
        (mem_relInFlagsAt_iff.mp hfmem).2.2
      have hnev : ∀ g, o.isOut g = true → f.val ≠ g := by
        intro g hg he
        rw [he, hg] at hisoutf
        cases hisoutf
      rw [coreOddSignFn_eq_of_match φ f
          (RelTransitionSystem.repair_match_of_ne hsq
            (hnev a hxa) (fun he => hfu (Subtype.ext he))
            (fun he => hfw (Subtype.ext he)) (hnev d hdout))
          (F.internalFlags_subset_coreFlags
            (κ.match_mem _ f.prop)),
        coreOddSignFn_eq_of_match φ f rfl
          (F.internalFlags_subset_coreFlags
            (κ.match_mem _ f.prop))]

/-- **The vertex ledger**: at the move's vertex, the transported
odd list is the old list with one transposition — the two changed
pair blocks swap their partner entries. -/
private theorem evalOdd_coreOddListAt_transportRepair_v
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (hM : MixedFunctional k ℓ)
    (μ : Multiset (Fin k)) (φ : F.CoreOddColouring ℓ) :
    hM.evalOdd μ (F.coreOddListAt
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) φ v) =
      -hM.evalOdd μ (F.coreOddListAt o φ v) := by
  unfold EdgeSubset.coreOddListAt
  rw [attachWith_congr (relInFlagsAt_congr
    (isOut_transportRepair hsq o hflip) v)]
  have hndL : (F.relInFlagsAt o v).Nodup := relInFlagsAt_nodup o v
  -- ═══════ THE DIRECTION AT `a` ═══════
  -- It decides which of the square's flags the vertex enumerates,
  -- and the repaired enumeration differs from it by one
  -- transposition either way.
  cases hxa : o.isOut a with
  | false =>
    have hain : a ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.ha, hsq.hav, hxa⟩
    have hdin : d ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hd, hsq.hdv, by
          rw [isOut_d_eq hsq o hflip, hxa]⟩
    have hbout : o.isOut b = true := by
      rw [isOut_b_eq hsq o, hxa, Bool.not_false]
    have hcout : o.isOut c = true := by
      rw [hflip, hxa, Bool.not_false]
    refine evalOdd_flatMap_swap hM μ _ _ (⟨a, hsq.ha⟩ :
        {f : W.Flag // f ∈ F.internalFlags}) ⟨d, hsq.hd⟩
      (fun he => hsq.had (congrArg Subtype.val he))
      (φ.val ⟨a, F.internalFlags_subset_coreFlags hsq.ha⟩)
      (φ.val ⟨d, F.internalFlags_subset_coreFlags hsq.hd⟩)
      (oddPartner ℓ (φ.val ⟨b,
        F.internalFlags_subset_coreFlags hsq.hb⟩))
      (oddPartner ℓ (φ.val ⟨c,
        F.internalFlags_subset_coreFlags hsq.hc⟩))
      (coreOddPairFn_eq_of_match φ _ hsq.hab
        (F.internalFlags_subset_coreFlags hsq.hb))
      (coreOddPairFn_eq_of_match φ _ hsq.hmd
        (F.internalFlags_subset_coreFlags hsq.hc))
      (coreOddPairFn_eq_of_match φ _
        (RelTransitionSystem.repair_match_a hsq)
        (F.internalFlags_subset_coreFlags hsq.hc))
      (coreOddPairFn_eq_of_match φ _
        (RelTransitionSystem.repair_match_d hsq)
        (F.internalFlags_subset_coreFlags hsq.hb))
      (nodup_attachWith hndL _)
      ((List.mem_attachWith _ _).mpr hain)
      ((List.mem_attachWith _ _).mpr hdin)
      (fun f hf hfu hfw => ?_)
    have hfmem : f.val ∈ F.relInFlagsAt o v :=
      (List.mem_attachWith _ _).mp hf
    have hisoutf : o.isOut f.val = false :=
      (mem_relInFlagsAt_iff.mp hfmem).2.2
    have hnev : ∀ g, o.isOut g = true → f.val ≠ g := by
      intro g hg he
      rw [he, hg] at hisoutf
      cases hisoutf
    rw [coreOddPairFn_eq_of_match φ f
        (RelTransitionSystem.repair_match_of_ne hsq
          (fun he => hfu (Subtype.ext he)) (hnev b hbout)
          (hnev c hcout) (fun he => hfw (Subtype.ext he)))
        (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)),
      coreOddPairFn_eq_of_match φ f rfl
        (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop))]
  | true =>
    have hbin : b ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hb, hsq.hbv, by
          rw [isOut_b_eq hsq o, hxa, Bool.not_true]⟩
    have hcin : c ∈ F.relInFlagsAt o v :=
      mem_relInFlagsAt_iff.mpr
        ⟨mem_flags_of_internalFlags F hsq.hc, hsq.hcv, by
          rw [hflip, hxa, Bool.not_true]⟩
    have hdout : o.isOut d = true := by
      rw [isOut_d_eq hsq o hflip, hxa]
    refine evalOdd_flatMap_swap hM μ _ _ (⟨b, hsq.hb⟩ :
        {f : W.Flag // f ∈ F.internalFlags}) ⟨c, hsq.hc⟩
      (fun he => hsq.hbc (congrArg Subtype.val he))
      (φ.val ⟨b, F.internalFlags_subset_coreFlags hsq.hb⟩)
      (φ.val ⟨c, F.internalFlags_subset_coreFlags hsq.hc⟩)
      (oddPartner ℓ (φ.val ⟨a,
        F.internalFlags_subset_coreFlags hsq.ha⟩))
      (oddPartner ℓ (φ.val ⟨d,
        F.internalFlags_subset_coreFlags hsq.hd⟩))
      (coreOddPairFn_eq_of_match φ _ hsq.hmb
        (F.internalFlags_subset_coreFlags hsq.ha))
      (coreOddPairFn_eq_of_match φ _ hsq.hcd
        (F.internalFlags_subset_coreFlags hsq.hd))
      (coreOddPairFn_eq_of_match φ _
        (RelTransitionSystem.repair_match_b hsq)
        (F.internalFlags_subset_coreFlags hsq.hd))
      (coreOddPairFn_eq_of_match φ _
        (RelTransitionSystem.repair_match_c hsq)
        (F.internalFlags_subset_coreFlags hsq.ha))
      (nodup_attachWith hndL _)
      ((List.mem_attachWith _ _).mpr hbin)
      ((List.mem_attachWith _ _).mpr hcin)
      (fun f hf hfu hfw => ?_)
    have hfmem : f.val ∈ F.relInFlagsAt o v :=
      (List.mem_attachWith _ _).mp hf
    have hisoutf : o.isOut f.val = false :=
      (mem_relInFlagsAt_iff.mp hfmem).2.2
    have hnev : ∀ g, o.isOut g = true → f.val ≠ g := by
      intro g hg he
      rw [he, hg] at hisoutf
      cases hisoutf
    rw [coreOddPairFn_eq_of_match φ f
        (RelTransitionSystem.repair_match_of_ne hsq
          (hnev a hxa) (fun he => hfu (Subtype.ext he))
          (fun he => hfw (Subtype.ext he)) (hnev d hdout))
        (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop)),
      coreOddPairFn_eq_of_match φ f rfl
        (F.internalFlags_subset_coreFlags (κ.match_mem _ f.prop))]

end RepairLedger

/-! ## The summand under one separated move -/

section SummandRepair

/-- **The separated-case ledger**: one repair move negates the
constrained summand at every fixed circuit exponent, over the
transported orientation. -/
theorem throughSummand_transportRepair
    [LinearOrder α] {k : ℕ} {ℓ : ℕ} {κ : F.RelTransitionSystem} {a : W.Flag}
    {b : W.Flag} {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (n : ℕ) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) n =
      -F.throughSummand hM st hbnd o n := by
  have hprod : ∀ (ψ : F.EvenColouring k)
      (φ : F.CoreOddColouring ℓ),
      (∏ vv : W.Vertex,
        ((F.coreOddSignAt
            (RelTransitionSystem.Orientation.transportRepair hsq o
              hflip) φ vv : ℂ) *
          hM.evalOdd (F.evenColoursAt ψ vv)
            (F.coreOddListAt
              (RelTransitionSystem.Orientation.transportRepair hsq
                o hflip) φ vv))) =
      -(∏ vv : W.Vertex,
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd (F.evenColoursAt ψ vv)
            (F.coreOddListAt o φ vv))) := by
    intro ψ φ
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v),
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ v)]
    have herase : ∀ vv ∈ Finset.univ.erase v,
        ((F.coreOddSignAt
            (RelTransitionSystem.Orientation.transportRepair hsq o
              hflip) φ vv : ℂ) *
          hM.evalOdd (F.evenColoursAt ψ vv)
            (F.coreOddListAt
              (RelTransitionSystem.Orientation.transportRepair hsq
                o hflip) φ vv)) =
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd (F.evenColoursAt ψ vv)
            (F.coreOddListAt o φ vv)) := by
      intro vv hvv
      rw [coreOddSignAt_transportRepair_ne hsq o hflip φ
          (Finset.mem_erase.mp hvv).1,
        coreOddListAt_transportRepair_ne hsq o hflip φ
          (Finset.mem_erase.mp hvv).1]
    rw [Finset.prod_congr rfl herase,
      coreOddSignAt_transportRepair_v hsq o hflip φ,
      evalOdd_coreOddListAt_transportRepair_v hsq o hflip hM
        (F.evenColoursAt ψ v) φ]
    ring
  unfold EdgeSubset.throughSummand
  rw [← mul_neg]
  refine congrArg _ ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  split_ifs with hP
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun φ _ => ?_)
    split_ifs with hQ
    · exact hprod ψ φ
    · rw [neg_zero]
  · rw [neg_zero]

/-- The summand at exponent `n` factors through exponent `0`. -/
theorem throughSummand_exp
    [LinearOrder α] {k : ℕ} {ℓ : ℕ} {κ : F.RelTransitionSystem}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) (n : ℕ) :
    F.throughSummand hM st hbnd o n =
      (-1 : ℂ) ^ n * F.throughSummand hM st hbnd o 0 := by
  unfold EdgeSubset.throughSummand
  rw [pow_zero]
  ring

private theorem neg_one_pow_eq_neg {m n : ℕ} (hodd : Odd (n + m)) :
    ((-1 : ℂ)) ^ m = -((-1 : ℂ)) ^ n := by
  have hmul : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ m = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow hodd
  have hsq2 : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc ((-1 : ℂ)) ^ m
      = ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * (-1 : ℂ) ^ m := by
        rw [hsq2, one_mul]
    _ = (-1 : ℂ) ^ n * ((-1 : ℂ) ^ n * (-1 : ℂ) ^ m) := by ring
    _ = (-1 : ℂ) ^ n * -1 := by rw [hmul]
    _ = -((-1 : ℂ)) ^ n := by ring

/-- **The separated repair step** (target shape): when the
circuit-count parity flips across the move, the summand at the
open circuit counts is preserved, over the transported
orientation. -/
theorem throughSummand_repair
    [LinearOrder α] {k : ℕ} {ℓ : ℕ} {κ : F.RelTransitionSystem} {a : W.Flag}
    {b : W.Flag} {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a)
    (hodd : Odd (κ.openCircuitCount +
      (κ.repair a b c d v hsq).openCircuitCount)) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip)
        ((κ.repair a b c d v hsq).openCircuitCount) =
      F.throughSummand hM st hbnd o κ.openCircuitCount := by
  rw [throughSummand_exp hM st hbnd _
      ((κ.repair a b c d v hsq).openCircuitCount),
    throughSummand_exp hM st hbnd o κ.openCircuitCount,
    throughSummand_transportRepair hM st hbnd hsq o hflip 0,
    neg_one_pow_eq_neg hodd]
  ring

end SummandRepair

end EdgeSubset

end RS
