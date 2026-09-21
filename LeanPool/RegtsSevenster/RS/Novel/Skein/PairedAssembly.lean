/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.StepStatusNonsep
import LeanPool.RegtsSevenster.RS.Novel.Skein.FourLabelParity
import LeanPool.RegtsSevenster.RS.Novel.Skein.FlipSignForm

/-!
# The paired assembly: `PairedLedgerUnsigned`

The final assembly of Proposition 3's paired step.  Along any
π-returning repair block, the canonical route accumulates a state
relabel and a sign; this file pins both.

**The state**: the accumulated relabel set is the
status difference `statusDiff` of the endpoint systems — per step
the relabel pairs are exactly the labels whose high-status changed
(`antiLow_labels_eq_statusChange` for separated steps,
`nonsep_labels_eq_statusChange` for non-separated ones), and the
status difference telescopes (`statusDiff_trans`) to `∅` at the
π-returning endpoint (`statusDiff_of_samePairing`).

**The sign**: the accumulated sign is carried as
`(−1)^tp · flipSignProd g T` — one `−1` per two-path step, and the
port-sign product of the full flip list `T` at the evolving
colours.  At the endpoint the flip list has all label counts even
(its parity fold is the empty status difference), so
`flipSignProd_of_even` evaluates the product to `(−1)^{T.length}`;
the per-step parity identity `tp_k + |T_k| ≡ Δcc_k (mod 2)` — the
four-label parity lemmas fed by the exact per-step flip counts —
telescopes the exponent against the chord-crossing counts, which
return with the pairing.  Hence the total sign is `+1`.

Main results: `chainStatusLedger` (the enriched chain induction),
`stepStatusLedger` (the per-step composed ledger),
`pairedLedgerUnsigned`, and `pairedLedger`.
-/

namespace RS

open scoped Classical

/-! ## Flip-sign list algebra -/

section SignAlgebra

variable {α : Type} {ℓ : ℕ}

/-- The flip-sign product is involutive: each factor is `±1`. -/
theorem flipSignProd_mul_self (f : α → Fin (2 * ℓ))
    (L : List (α × α)) :
    flipSignProd f L * flipSignProd f L = 1 := by
  induction L generalizing f with
  | nil =>
    rw [flipSignProd_nil, one_mul]
  | cons p L ih =>
    rw [flipSignProd_cons]
    have h1 := oddPartnerSign_mul_self ℓ (f p.1)
    have h2 := oddPartnerSign_mul_self ℓ (f p.2)
    have h3 := ih (flipColours f p)
    calc (oddPartnerSign ℓ (f p.1) * oddPartnerSign ℓ (f p.2) *
          flipSignProd (flipColours f p) L) *
        (oddPartnerSign ℓ (f p.1) * oddPartnerSign ℓ (f p.2) *
          flipSignProd (flipColours f p) L)
        = (oddPartnerSign ℓ (f p.1) * oddPartnerSign ℓ (f p.1)) *
            ((oddPartnerSign ℓ (f p.2) * oddPartnerSign ℓ (f p.2)) *
              (flipSignProd (flipColours f p) L *
                flipSignProd (flipColours f p) L)) := by ring
      _ = 1 := by rw [h1, h2, h3, one_mul, one_mul]

/-- The accumulated colour relabel of a flip sequence. -/
noncomputable def flipColoursFold (f : α → Fin (2 * ℓ))
    (L : List (α × α)) : α → Fin (2 * ℓ) :=
  L.foldl flipColours f

/-- The empty flip sequence leaves the colours alone. -/
theorem flipColoursFold_nil (f : α → Fin (2 * ℓ)) :
    flipColoursFold f [] = f := rfl

/-- One more flip moves its two labels' colours, then continues. -/
theorem flipColoursFold_cons (f : α → Fin (2 * ℓ)) (p : α × α)
    (L : List (α × α)) :
    flipColoursFold f (p :: L) =
      flipColoursFold (flipColours f p) L := rfl

/-- The flip-sign product splits along an append, the second block
evaluated at the accumulated colours of the first. -/
theorem flipSignProd_append (f : α → Fin (2 * ℓ))
    (L₁ L₂ : List (α × α)) :
    flipSignProd f (L₁ ++ L₂) =
      flipSignProd f L₁ *
        flipSignProd (flipColoursFold f L₁) L₂ := by
  induction L₁ generalizing f with
  | nil =>
    rw [List.nil_append, flipSignProd_nil, one_mul,
      flipColoursFold_nil]
  | cons p L ih =>
    rw [List.cons_append, flipSignProd_cons, flipSignProd_cons,
      ih (flipColours f p), flipColoursFold_cons]
    ring

private theorem flipLabels_count_cons (p : α × α)
    (L : List (α × α)) (i : α) :
    (flipLabels (p :: L)).count i =
      (flipLabels L).count i + (if i = p.1 then 1 else 0) +
        (if i = p.2 then 1 else 0) := by
  have hbase : (flipLabels (p :: L)).count i =
      ((flipLabels L).count i + if p.2 = i then 1 else 0) +
        if p.1 = i then 1 else 0 := by
    simp only [flipLabels_cons, List.count_cons, beq_iff_eq]
  rw [hbase]
  by_cases h1 : i = p.1 <;> by_cases h2 : i = p.2
  · rw [if_pos h1.symm, if_pos h2.symm, if_pos h1, if_pos h2]
  · rw [if_neg (fun h => h2 h.symm), if_pos h1.symm, if_pos h1,
      if_neg h2]
  · rw [if_pos h2.symm, if_neg (fun h => h1 h.symm), if_neg h1,
      if_pos h2]
  · rw [if_neg (fun h => h2 h.symm), if_neg (fun h => h1 h.symm),
      if_neg h1, if_neg h2]

/-- The odd-count set of a cons toggles exactly at the head's
labels. -/
private theorem mem_oddCountLabels_cons {p : α × α}
    (hp : p.1 ≠ p.2) {L : List (α × α)} {i : α} :
    i ∈ oddCountLabels (p :: L) ↔
      (((i = p.1 ∨ i = p.2) ∧ i ∉ oddCountLabels L) ∨
        (i ∈ oddCountLabels L ∧ ¬(i = p.1 ∨ i = p.2))) := by
  simp only [mem_oddCountLabels, flipLabels_count_cons p L i]
  by_cases h1 : i = p.1 <;> by_cases h2 : i = p.2
  · exact absurd (h1.symm.trans h2) hp
  · rw [if_pos h1, if_neg h2]
    have hm : i = p.1 ∨ i = p.2 := Or.inl h1
    constructor
    · intro h
      exact Or.inl ⟨hm, by omega⟩
    · rintro (⟨-, hodd⟩ | ⟨-, hnot⟩)
      · omega
      · exact absurd hm hnot
  · rw [if_neg h1, if_pos h2]
    have hm : i = p.1 ∨ i = p.2 := Or.inr h2
    constructor
    · intro h
      exact Or.inl ⟨hm, by omega⟩
    · rintro (⟨-, hodd⟩ | ⟨-, hnot⟩)
      · omega
      · exact absurd hm hnot
  · rw [if_neg h1, if_neg h2]
    have hm : ¬(i = p.1 ∨ i = p.2) := by
      rintro (h | h)
      · exact h1 h
      · exact h2 h
    constructor
    · intro h
      exact Or.inr ⟨by omega, hm⟩
    · rintro (⟨hor, -⟩ | ⟨hodd, -⟩)
      · exact absurd hor hm
      · omega

/-- For pairs with distinct components the symmetric-difference
fold is the odd-count set. -/
theorem pairFold_eq_oddCountLabels {L : List (α × α)}
    (hd : ∀ p ∈ L, p.1 ≠ p.2) :
    pairFold L = oddCountLabels L := by
  induction L with
  | nil =>
    rw [pairFold_nil]
    refine (Finset.eq_empty_of_forall_notMem fun i hi => ?_).symm
    rw [mem_oddCountLabels] at hi
    simp [flipLabels_nil] at hi
  | cons p L ih =>
    have hp := hd p List.mem_cons_self
    have hd' : ∀ q ∈ L, q.1 ≠ q.2 := fun q hq =>
      hd q (List.mem_cons_of_mem p hq)
    rw [pairFold_cons, ih hd']
    apply Finset.ext
    intro i
    rw [mem_symmU, mem_oddCountLabels_cons hp]
    simp only [mem_pairSet]

/-- The accumulated colour relabel is the odd-partner relabel at
the odd-count labels. -/
theorem flipColoursFold_apply {L : List (α × α)}
    (hd : ∀ p ∈ L, p.1 ≠ p.2) (f : α → Fin (2 * ℓ)) (i : α) :
    flipColoursFold f L i =
      if i ∈ oddCountLabels L then oddPartner ℓ (f i) else f i := by
  induction L generalizing f with
  | nil =>
    rw [flipColoursFold_nil, if_neg (fun h => by
      rw [mem_oddCountLabels] at h
      simp [flipLabels_nil] at h)]
  | cons p L ih =>
    have hp := hd p List.mem_cons_self
    have hd' : ∀ q ∈ L, q.1 ≠ q.2 := fun q hq =>
      hd q (List.mem_cons_of_mem p hq)
    rw [flipColoursFold_cons, ih hd' (flipColours f p)]
    by_cases hm : i = p.1 ∨ i = p.2
    · have hfc : flipColours f p i = oddPartner ℓ (f i) := by
        unfold flipColours
        rw [if_pos hm]
      by_cases ho : i ∈ oddCountLabels L
      · have hnot : i ∉ oddCountLabels (p :: L) := by
          rw [mem_oddCountLabels_cons hp]
          rintro (⟨-, h⟩ | ⟨-, h⟩)
          · exact h ho
          · exact h hm
        rw [if_pos ho, hfc, oddPartner_invol, if_neg hnot]
      · have hyes : i ∈ oddCountLabels (p :: L) :=
          (mem_oddCountLabels_cons hp).mpr (Or.inl ⟨hm, ho⟩)
        rw [if_neg ho, hfc, if_pos hyes]
    · have hfc : flipColours f p i = f i := by
        unfold flipColours
        rw [if_neg hm]
      by_cases ho : i ∈ oddCountLabels L
      · have hyes : i ∈ oddCountLabels (p :: L) :=
          (mem_oddCountLabels_cons hp).mpr (Or.inr ⟨ho, hm⟩)
        rw [if_pos ho, hfc, if_pos hyes]
      · have hnot : i ∉ oddCountLabels (p :: L) := by
          rw [mem_oddCountLabels_cons hp]
          rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact hm h
          · exact ho h
        rw [if_neg ho, hfc, if_neg hnot]

end SignAlgebra

/-! ## Indicator and crossing-symmetry helpers -/

section Indicators

variable {β : Type}

/-- The cardinality of a subset of an explicit finset as an
indicator sum. -/
private theorem card_eq_sum_indicator {s t : Finset β}
    (h : s ⊆ t) :
    s.card = ∑ z ∈ t, if z ∈ s then 1 else 0 := by
  have he : t.filter (fun z => z ∈ s) = s := by
    apply Finset.ext
    intro z
    rw [Finset.mem_filter]
    exact ⟨fun hz => hz.2, fun hz => ⟨h hz, hz⟩⟩
  calc s.card = (t.filter (fun z => z ∈ s)).card := by rw [he]
    _ = ∑ z ∈ t, if z ∈ s then 1 else 0 := by
        rw [Finset.card_filter]

end Indicators

section OrderIndicators

variable {α : Type}

/-- Two membership indicators of one new chord combine into the
low-end indicator gated by the label comparison. -/
private theorem two_indicator_if [LinearOrder α]
    {x y : α} (hxy : x ≠ y)
    (P Q : Prop) [Decidable P] [Decidable Q] :
    ((if x < y ∧ P then 1 else 0) +
        (if y < x ∧ Q then 1 else 0) : ℕ) =
      if (if x < y then P else Q) then 1 else 0 := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have e2 : (if y < x ∧ Q then 1 else 0 : ℕ) = 0 :=
      if_neg (fun hc => lt_asymm h hc.1)
    have hcond : (if x < y then P else Q) ↔ P := by
      rw [if_pos h]
    rw [e2, add_zero, if_congr (and_iff_right h) rfl rfl,
      if_congr hcond rfl rfl]
  · have e1 : (if x < y ∧ P then 1 else 0 : ℕ) = 0 :=
      if_neg (fun hc => lt_asymm h hc.1)
    have hcond : (if x < y then P else Q) ↔ Q := by
      rw [if_neg (lt_asymm h)]
    rw [e1, zero_add, if_congr (and_iff_right h) rfl rfl,
      if_congr hcond rfl rfl]

/-- Exactly one of the two strict comparisons of distinct elements
holds. -/
private theorem indicator_pair_one [LinearOrder α]
    {x y : α} (hxy : x ≠ y) :
    ((if x < y then 1 else 0) + (if y < x then 1 else 0) : ℕ) =
      1 := by
  rcases lt_or_gt_of_ne hxy with h | h
  · rw [if_pos h, if_neg (lt_asymm h)]
  · rw [if_neg (lt_asymm h), if_pos h]

/-- The symmetrized chord crossing is symmetric in its two
arguments. -/
private theorem chordPairCrossSym_comm [LinearOrder α]
    (p q : α × α) :
    chordPairCrossSym p q ↔ chordPairCrossSym q p :=
  Or.comm

/-- The symmetrized chord crossing ignores the internal order of
each recorded pair. -/
private theorem chordPairCrossSym_swap_pair [LinearOrder α]
    (a₁ a₂ b₁ b₂ : α) :
    chordPairCrossSym (a₂, a₁) (b₂, b₁) ↔
      chordPairCrossSym (a₁, a₂) (b₁, b₂) := by
  show (ChordPairCross (min a₂ a₁) (max a₂ a₁) (min b₂ b₁)
        (max b₂ b₁) ∨
      ChordPairCross (min b₂ b₁) (max b₂ b₁) (min a₂ a₁)
        (max a₂ a₁)) ↔
    (ChordPairCross (min a₁ a₂) (max a₁ a₂) (min b₁ b₂)
        (max b₁ b₂) ∨
      ChordPairCross (min b₁ b₂) (max b₁ b₂) (min a₁ a₂)
        (max a₁ a₂))
  rw [min_comm a₂ a₁, max_comm a₂ a₁, min_comm b₂ b₁,
    max_comm b₂ b₁]

end OrderIndicators

/-! ## Status-difference membership and transport -/

namespace EdgeSubset

variable {α : Type}

/-- A matching equality induces the same boundary pairing. -/
private theorem samePairing_of_matchEq {W : Fragment α} {F : EdgeSubset W}
    {κ₁ κ₂ : F.RelTransitionSystem} (heq : κ₁.MatchEq κ₂) :
    SamePairing κ₁ κ₂ :=
  fun _ hδ => (pathMatch_matchEq heq hδ).symm

-- Raised budget: membership in the symmetric difference is
-- unfolded through the status sets on both sides.
/-- Membership in the status difference is the status change. -/
private theorem mem_statusDiff
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    {i : α} :
    i ∈ statusDiff κ κ' ↔
      ((i ∈ highSet κ') ≠ (i ∈ highSet κ)) := by
  unfold statusDiff
  rw [mem_symmU, prop_ne_iff]
  tauto

/-- Status differences transport across matching equality on the
right. -/
private theorem statusDiff_matchEq_right
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ₁ κ₂ κ₂' : F.RelTransitionSystem} (heq : κ₂.MatchEq κ₂') :
    statusDiff κ₁ κ₂ = statusDiff κ₁ κ₂' := by
  unfold statusDiff
  rw [highSet_of_samePairing (samePairing_of_matchEq heq)]

/-- **A re-partnered end participates**: if the path match of a
boundary flag differs between two systems, its entry edge is
internal — a boundary-paired end has the same (pairing-determined)
path match in every system. -/
theorem repartner_internal {W : Fragment α} {F : EdgeSubset W}
    {κ κ' : F.RelTransitionSystem}
    {ε : W.Flag} (hε : ε ∈ F.boundaryFlags)
    (hch : κ'.pathMatch ε hε ≠ κ.pathMatch ε hε) :
    W.pairing ε ∈ F.internalFlags := by
  rcases F.mem_internalFlags_or_boundaryFlags
      (F.pairing_mem ε (mem_flags_of_boundaryFlags F hε)) with
    h | h
  · exact h
  · exact absurd ((κ'.pathMatch_eq_pairing hε h).trans
      (κ.pathMatch_eq_pairing hε h).symm) hch

end EdgeSubset

/-! ## Colour functions matching a state -/

section StateColours

variable {k ℓ : ℕ} {α : Type}

/-- One flip: the flipped colour function matches the flipped
state. -/
private theorem flipColours_matches {st : GenBoundaryState k ℓ α}
    {g : α → Fin (2 * ℓ)}
    (hg : ∀ i c, st i = Sum.inr c → g i = c) (l₁ l₂ : α) :
    ∀ i c, stateOddFlip st l₁ l₂ i = Sum.inr c →
      flipColours g (l₁, l₂) i = c := by
  intro i c hic
  by_cases hm : i = l₁ ∨ i = l₂
  · have hst : stateOddFlip st l₁ l₂ i =
        Sum.map id (oddPartner ℓ) (st i) := by
      rcases hm with rfl | rfl
      · exact stateOddFlip_left
      · exact stateOddFlip_right
    rw [hst] at hic
    have hfc : flipColours g (l₁, l₂) i = oddPartner ℓ (g i) := by
      unfold flipColours
      rw [if_pos hm]
    rcases hval : st i with a | c₀
    · rw [hval] at hic
      simp only [Sum.map_inl] at hic
      simp at hic
    · rw [hval] at hic
      simp only [Sum.map_inr] at hic
      rw [hfc, hg i c₀ hval]
      exact Sum.inr.inj hic
  · have hst : stateOddFlip st l₁ l₂ i = st i :=
      stateOddFlip_of_ne (fun h => hm (Or.inl h))
        (fun h => hm (Or.inr h))
    have hfc : flipColours g (l₁, l₂) i = g i := by
      unfold flipColours
      rw [if_neg hm]
    rw [hst] at hic
    rw [hfc]
    exact hg i c hic

/-- The accumulated colour relabel matches the accumulated state
relabel. -/
private theorem flipColoursFold_matches
    {st : GenBoundaryState k ℓ α} {g : α → Fin (2 * ℓ)}
    (hg : ∀ i c, st i = Sum.inr c → g i = c)
    {T : List (α × α)} (hd : ∀ p ∈ T, p.1 ≠ p.2) :
    ∀ i c, stateOddFlipSet st (pairFold T) i = Sum.inr c →
      flipColoursFold g T i = c := by
  intro i c hic
  rw [flipColoursFold_apply hd g i, ← pairFold_eq_oddCountLabels hd]
  by_cases hm : i ∈ pairFold T
  · rw [stateOddFlipSet_of_mem hm] at hic
    rw [if_pos hm]
    rcases hval : st i with a | c₀
    · rw [hval] at hic
      simp only [Sum.map_inl] at hic
      simp at hic
    · rw [hval] at hic
      simp only [Sum.map_inr] at hic
      rw [hg i c₀ hval]
      exact Sum.inr.inj hic
  · rw [stateOddFlipSet_of_notMem hm] at hic
    rw [if_neg hm]
    exact hg i c hic

end StateColours

/-! ## The signed full re-canonicalization -/

namespace EdgeSubset

variable {α : Type}

section RecanonSigned

/-- **Sign-explicit full re-canonicalization**: as
`exists_recanonicalize_sets`, but with the accumulated sign pinned
as the flip-sign product `flipSignProd g L` of the flip list at
any colour function `g` matching the state. -/
theorem exists_recanonicalize_signed
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) (g : α → Fin (2 * ℓ))
    (hg : ∀ i c, st i = Sum.inr c → g i = c) :
    ∃ (o₁ : κ.Orientation) (L : List (α × α)),
      PathCanonical o₁ ∧
      L.length = (antiLowSet o).card ∧
      L.Pairwise PairDisjoint ∧
      (∀ p ∈ L, AntiLowPair o p) ∧
      ∀ n, F.throughSummand hM st hbnd o n =
        ((flipSignProd g L : ℤ) : ℂ) *
          F.throughSummand hM (stateOddFlipSet st (pairFold L))
            (genBoundarySubsetMatches_stateOddFlipSet hbnd
              (pairFold L)) o₁ n := by
  suffices H : ∀ (N : ℕ) (st : GenBoundaryState k ℓ α)
      (hbnd : genBoundarySubsetMatches W F.flags st)
      (g : α → Fin (2 * ℓ))
      (hg : ∀ i c, st i = Sum.inr c → g i = c)
      (o : κ.Orientation), (antiLowSet o).card = N →
      ∃ (o₁ : κ.Orientation) (L : List (α × α)),
        PathCanonical o₁ ∧ L.length = N ∧
        L.Pairwise PairDisjoint ∧
        (∀ p ∈ L, AntiLowPair o p) ∧
        ∀ n, F.throughSummand hM st hbnd o n =
          ((flipSignProd g L : ℤ) : ℂ) *
            F.throughSummand hM (stateOddFlipSet st (pairFold L))
              (genBoundarySubsetMatches_stateOddFlipSet hbnd
                (pairFold L)) o₁ n by
    obtain ⟨o₁, L, h1, h2, h3, h4, h5⟩ := H _ st hbnd g hg o rfl
    exact ⟨o₁, L, h1, h2.trans rfl, h3, h4, h5⟩
  -- ═══════ INDUCTION ON THE ANTI-CANONICAL COUNT ═══════
  -- Zero anti-canonical chains means the frame is already
  -- canonical; each step flips one chain and drops the count.
  intro N
  induction N with
  | zero =>
    intro st hbnd g hg o hcard
    refine ⟨o, [], ?_, rfl, List.Pairwise.nil, ?_, ?_⟩
    · rw [pathCanonical_iff_antiLowSet_empty]
      exact Finset.card_eq_zero.mp hcard
    · intro p hp
      cases hp
    · intro n
      rw [flipSignProd_nil, Int.cast_one, one_mul, pairFold_nil]
      exact (F.throughSummand_state_congr hM stateOddFlipSet_empty
        (genBoundarySubsetMatches_stateOddFlipSet hbnd ∅) hbnd
        o n).symm
  | succ N ih =>
    intro st hbnd g hg o hcard
    have hne : (antiLowSet o).Nonempty := by
      rw [← Finset.card_pos, hcard]
      omega
    obtain ⟨β, hβmem⟩ := hne
    obtain ⟨hβ, hint, hlow, hdir⟩ := mem_antiLowSet.mp hβmem
    obtain ⟨c₁, hcol₁⟩ :
        ∃ c, st (F.boundaryLabel hβ) = Sum.inr c := by
      apply (hbnd _).mp
      have he : W.boundaryFlag (F.boundaryLabel hβ) = β :=
        (W.eq_boundaryFlag _ β (attach_boundaryLabel hβ)).symm
      rw [he]
      exact mem_flags_of_boundaryFlags F hβ
    obtain ⟨c₂, hcol₂⟩ :
        ∃ c, st (F.boundaryLabel (κ.pathMatch_mem hβ)) =
          Sum.inr c := by
      apply (hbnd _).mp
      have he : W.boundaryFlag
          (F.boundaryLabel (κ.pathMatch_mem hβ)) =
          κ.pathMatch β hβ :=
        (W.eq_boundaryFlag _ _
          (attach_boundaryLabel (κ.pathMatch_mem hβ))).symm
      rw [he]
      exact mem_flags_of_boundaryFlags F (κ.pathMatch_mem hβ)
    obtain ⟨o₁, hd₁, hd₂, hpres, hled⟩ :=
      exists_chainRecanonicalize hM st hbnd o hβ hint hcol₁ hcol₂
    have hset : antiLowSet o₁ = (antiLowSet o).erase β :=
      antiLowSet_flip hβ hβmem hd₁ hpres
    have hcard₁ : (antiLowSet o₁).card = N := by
      rw [hset, Finset.card_erase_of_mem hβmem, hcard]
      omega
    have hsub : antiLowSet o₁ ⊆ antiLowSet o := by
      intro x hx
      rw [hset] at hx
      exact Finset.mem_of_mem_erase hx
    obtain ⟨o₂, L', hcanon, hlen', hpw', hprov', hled₂⟩ :=
      ih (stateOddFlip st (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ)))
        (genBoundarySubsetMatches_stateOddFlip hbnd
          (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ)))
        (flipColours g (F.boundaryLabel hβ,
          F.boundaryLabel (κ.pathMatch_mem hβ)))
        (flipColours_matches hg _ _) o₁ hcard₁
    have hstEq : stateOddFlipSet
        (stateOddFlip st (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ))) (pairFold L') =
        stateOddFlipSet st
          (pairFold ((F.boundaryLabel hβ,
            F.boundaryLabel (κ.pathMatch_mem hβ)) :: L')) := by
      rw [stateOddFlip_eq_flipSet, stateOddFlipSet_symmU,
        pairFold_cons]
      rfl
    have hpd : ∀ q ∈ L', PairDisjoint
        (F.boundaryLabel hβ,
          F.boundaryLabel (κ.pathMatch_mem hβ)) q := by
      intro q hq
      obtain ⟨γ, hγ, hγm, hq1, hq2⟩ := hprov' q hq
      rw [hset] at hγm
      obtain ⟨hγβ, hγmo⟩ := Finset.mem_erase.mp hγm
      have hd := antiLowPair_disjoint hβ hγ hβmem hγmo
        (Ne.symm hγβ)
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hq1]
        exact hd.fst_ne_fst
      · rw [hq2]
        exact hd.fst_ne_snd
      · rw [hq1]
        exact hd.snd_ne_fst
      · rw [hq2]
        exact hd.snd_ne_snd
    have hprovNew : ∀ p ∈ ((F.boundaryLabel hβ,
        F.boundaryLabel (κ.pathMatch_mem hβ)) :: L'),
        AntiLowPair o p := by
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨β, hβ, hβmem, rfl, rfl⟩
      · exact AntiLowPair.mono hsub (hprov' p hp')
    refine ⟨o₂,
      (F.boundaryLabel hβ,
        F.boundaryLabel (κ.pathMatch_mem hβ)) :: L',
      hcanon, ?_, ?_, hprovNew, ?_⟩
    · rw [List.length_cons, hlen']
    · exact List.pairwise_cons.mpr ⟨hpd, hpw'⟩
    · intro n
      have hb1 := genBoundarySubsetMatches_stateOddFlipSet
        (genBoundarySubsetMatches_stateOddFlip hbnd
          (F.boundaryLabel hβ)
          (F.boundaryLabel (κ.pathMatch_mem hβ))) (pairFold L')
      have hb2 := genBoundarySubsetMatches_stateOddFlipSet hbnd
        (pairFold ((F.boundaryLabel hβ,
          F.boundaryLabel (κ.pathMatch_mem hβ)) :: L'))
      have hsign : ((flipSignProd g
          ((F.boundaryLabel hβ,
            F.boundaryLabel (κ.pathMatch_mem hβ)) :: L') : ℤ) :
            ℂ) =
          ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
            ((flipSignProd (flipColours g (F.boundaryLabel hβ,
              F.boundaryLabel (κ.pathMatch_mem hβ))) L' : ℤ) :
              ℂ) := by
        rw [flipSignProd_cons,
          show g (F.boundaryLabel hβ,
            F.boundaryLabel (κ.pathMatch_mem hβ)).1 = c₁ from
            hg _ c₁ hcol₁,
          show g (F.boundaryLabel hβ,
            F.boundaryLabel (κ.pathMatch_mem hβ)).2 = c₂ from
            hg _ c₂ hcol₂]
        push_cast
        ring
      rw [hled n, hled₂ n,
        F.throughSummand_state_congr hM hstEq hb1 hb2 o₂ n,
        hsign, mul_assoc]

end RecanonSigned

/-! ## The anchored transported frame: per-end evaluation -/

section NonsepCount

/-- Membership of a re-paired end in the transported anti set, for
an arbitrary source orientation: the low-in-new comparison and the
source chain direction. -/
private theorem mem_antiLowSet_transport_end
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) {x y : W.Flag}
    (hx : x ∈ F.boundaryFlags) (hy : y ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hnew : (κ.repair a b c d v hsq).pathMatch x hx = y) :
    x ∈ antiLowSet
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) ↔
      (F.boundaryLabel hx < F.boundaryLabel hy ∧
        chainDir o x = true) := by
  rw [mem_antiLowSet_transport hsq o hflip]
  constructor
  · rintro ⟨hx', hint', hlt, hdir⟩
    refine ⟨?_, hdir⟩
    rwa [boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx) hy hnew] at hlt
  · rintro ⟨hlt, hdir⟩
    refine ⟨hx, hintx, ?_, hdir⟩
    rwa [boundaryLabel_congr
      ((κ.repair a b c d v hsq).pathMatch_mem hx) hy hnew]

/-- The chain direction of the anchored flip at an untoggled end is
the canonical high-status. -/
private theorem dir_portFlip_untoggled_iff
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    {o : κ.Orientation}
    (hc : PathCanonical o) (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hT : W.pairing x ∉ S) :
    chainDir (o.portFlip hpf) x = true ↔
      F.boundaryLabel (κ.pathMatch_mem hx) < F.boundaryLabel hx := by
  rw [chainDir_portFlip_of_notMem o hpf hT]
  exact chainDir_true_iff_high hc hx hintx

/-- The chain direction of the anchored flip at a toggled end is
the negated canonical high-status. -/
private theorem dir_portFlip_toggled_iff
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    {o : κ.Orientation}
    (hc : PathCanonical o) (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags)
    (hT : W.pairing x ∈ S) :
    chainDir (o.portFlip hpf) x = true ↔
      ¬ F.boundaryLabel (κ.pathMatch_mem hx) <
        F.boundaryLabel hx := by
  rw [chainDir_portFlip_of_mem o hpf hT]
  constructor
  · intro hd hlt
    rw [(chainDir_true_iff_high hc hx hintx).mpr hlt] at hd
    simp at hd
  · intro hn
    cases hb : chainDir o x
    · rfl
    · exact absurd ((chainDir_true_iff_high hc hx hintx).mp hb) hn

/-- The anchor-chain toggle is chord-wise: an end's entry edge is
on the flipped chain iff its path match's entry edge is. -/
private theorem toggle_partner
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hintβ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags, OnBoundaryChain κ β₂ f → f ∈ S)
    {x : W.Flag} (hx : x ∈ F.boundaryFlags)
    (hintx : W.pairing x ∈ F.internalFlags) :
    W.pairing (κ.pathMatch x hx) ∈ S ↔ W.pairing x ∈ S := by
  rw [pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon
      (κ.pathMatch_mem hx) (pathMatch_pairing_internal hx hintx),
    pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon hx hintx]
  constructor
  · rintro (h | h)
    · right
      calc x = κ.pathMatch (κ.pathMatch x hx)
            (κ.pathMatch_mem hx) := (κ.pathMatch_invol hx).symm
        _ = κ.pathMatch β₂ hβ₂ :=
            κ.pathMatch_congr h (κ.pathMatch_mem hx) hβ₂
    · left
      calc x = κ.pathMatch (κ.pathMatch x hx)
            (κ.pathMatch_mem hx) := (κ.pathMatch_invol hx).symm
        _ = κ.pathMatch (κ.pathMatch β₂ hβ₂)
            (κ.pathMatch_mem hβ₂) :=
            κ.pathMatch_congr h (κ.pathMatch_mem hx)
              (κ.pathMatch_mem hβ₂)
        _ = β₂ := κ.pathMatch_invol hβ₂
  · rintro (rfl | h)
    · exact Or.inr rfl
    · left
      calc κ.pathMatch x hx
          = κ.pathMatch (κ.pathMatch β₂ hβ₂)
            (κ.pathMatch_mem hβ₂) :=
            κ.pathMatch_congr h hx (κ.pathMatch_mem hβ₂)
        _ = β₂ := κ.pathMatch_invol hβ₂

/-- **The mixed-toggle anti count**: when the cross-pairing joins
an untoggled end `ε₁` to a toggled end `ε₂` (an end of the anchor
chord), the anti set of the anchored transported frame lies on the
four re-paired ends and its cardinality is the toggled four-label
indicator sum of `fourLabel_parity_nonsep`. -/
private theorem nonsep_anti_card_mixed
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hc : PathCanonical o)
    (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    (hflip : (o.portFlip hpf).isOut c = !(o.portFlip hpf).isOut a)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hintβ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags, OnBoundaryChain κ β₂ f → f ∈ S)
    {ε₁ ε₂ : W.Flag} (hε₁ : ε₁ ∈ F.boundaryFlags)
    (hε₂ : ε₂ ∈ F.boundaryFlags)
    (hne : ε₁ ≠ ε₂) (hPne : κ.pathMatch ε₁ hε₁ ≠ ε₂)
    (hcross : (κ.repair a b c d v hsq).pathMatch ε₁ hε₁ = ε₂)
    (hfar : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch ε₁ hε₁) (κ.pathMatch_mem hε₁) =
      κ.pathMatch ε₂ hε₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ ε₁ → δ ≠ ε₂ → δ ≠ κ.pathMatch ε₁ hε₁ →
      δ ≠ κ.pathMatch ε₂ hε₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ)
    (hT₁ : W.pairing ε₁ ∉ S) (hT₂ : W.pairing ε₂ ∈ S) :
    (antiLowSet (RelTransitionSystem.Orientation.transportRepair
        hsq (o.portFlip hpf) hflip)).card =
      (if (if F.boundaryLabel hε₁ < F.boundaryLabel hε₂ then
            F.boundaryLabel (κ.pathMatch_mem hε₁) <
              F.boundaryLabel hε₁
          else ¬ F.boundaryLabel (κ.pathMatch_mem hε₂) <
              F.boundaryLabel hε₂) then 1 else 0) +
      (if (if F.boundaryLabel (κ.pathMatch_mem hε₁) <
            F.boundaryLabel (κ.pathMatch_mem hε₂) then
            F.boundaryLabel hε₁ <
              F.boundaryLabel (κ.pathMatch_mem hε₁)
          else ¬ F.boundaryLabel hε₂ <
              F.boundaryLabel (κ.pathMatch_mem hε₂)) then 1
        else 0) := by
  have hcross₂ : (κ.repair a b c d v hsq).pathMatch ε₂ hε₂ = ε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hcross.symm hε₂
      ((κ.repair a b c d v hsq).pathMatch_mem hε₁)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol hε₁)
  have hfar₂ : (κ.repair a b c d v hsq).pathMatch
      (κ.pathMatch ε₂ hε₂) (κ.pathMatch_mem hε₂) =
      κ.pathMatch ε₁ hε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hfar.symm
      (κ.pathMatch_mem hε₂)
      ((κ.repair a b c d v hsq).pathMatch_mem
        (κ.pathMatch_mem hε₁))).trans
      ((κ.repair a b c d v hsq).pathMatch_invol
        (κ.pathMatch_mem hε₁))
  have hPne' : ε₁ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    hPne ((κ.pathMatch_congr h hε₁ (κ.pathMatch_mem hε₂)).trans
      (κ.pathMatch_invol hε₂))
  have hPP : κ.pathMatch ε₁ hε₁ ≠ κ.pathMatch ε₂ hε₂ := by
    intro h
    apply hne
    calc ε₁ = κ.pathMatch (κ.pathMatch ε₁ hε₁)
          (κ.pathMatch_mem hε₁) := (κ.pathMatch_invol hε₁).symm
      _ = κ.pathMatch (κ.pathMatch ε₂ hε₂)
          (κ.pathMatch_mem hε₂) :=
        κ.pathMatch_congr h (κ.pathMatch_mem hε₁)
          (κ.pathMatch_mem hε₂)
      _ = ε₂ := κ.pathMatch_invol hε₂
  have hint₁ : W.pairing ε₁ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₁ (by
        rw [hcross]
        exact fun h => hPne h.symm)
  have hint₂' : W.pairing ε₂ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₂ (by
        rw [hcross₂]
        exact hPne')
  have hintP₁ : W.pairing (κ.pathMatch ε₁ hε₁) ∈
      F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      (κ.pathMatch_mem hε₁) (by
        rw [hfar, κ.pathMatch_invol hε₁]
        exact fun h => hPne' h.symm)
  have hintP₂ : W.pairing (κ.pathMatch ε₂ hε₂) ∈
      F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      (κ.pathMatch_mem hε₂) (by
        rw [hfar₂, κ.pathMatch_invol hε₂]
        exact hPne)
  have hT₃ : W.pairing (κ.pathMatch ε₁ hε₁) ∉ S := fun hmem =>
    hT₁ ((toggle_partner hpf hβ₂ hintβ honS hSon hε₁ hint₁).mp
      hmem)
  have hT₄ : W.pairing (κ.pathMatch ε₂ hε₂) ∈ S :=
    (toggle_partner hpf hβ₂ hintβ honS hSon hε₂ hint₂').mpr hT₂
  have hLxy : F.boundaryLabel hε₁ ≠ F.boundaryLabel hε₂ :=
    fun h => hne (boundaryLabel_inj hε₁ hε₂ h)
  have hLxbyb : F.boundaryLabel (κ.pathMatch_mem hε₁) ≠
      F.boundaryLabel (κ.pathMatch_mem hε₂) :=
    fun h => hPP (boundaryLabel_inj (κ.pathMatch_mem hε₁)
      (κ.pathMatch_mem hε₂) h)
  have hππ₁ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem hε₁)) =
      F.boundaryLabel hε₁ :=
    boundaryLabel_congr _ hε₁ (κ.pathMatch_invol hε₁)
  have hππ₂ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem hε₂)) =
      F.boundaryLabel hε₂ :=
    boundaryLabel_congr _ hε₂ (κ.pathMatch_invol hε₂)
  have hm₁ : ε₁ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel hε₁ < F.boundaryLabel hε₂ ∧
        F.boundaryLabel (κ.pathMatch_mem hε₁) <
          F.boundaryLabel hε₁) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      hε₁ hε₂ hint₁ hcross]
    exact and_congr_right fun _ =>
      dir_portFlip_untoggled_iff hc hpf hε₁ hint₁ hT₁
  have hm₂ : ε₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel hε₂ < F.boundaryLabel hε₁ ∧
        ¬ F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel hε₂) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      hε₂ hε₁ hint₂' hcross₂]
    exact and_congr_right fun _ =>
      dir_portFlip_toggled_iff hc hpf hε₂ hint₂' hT₂
  have hm₃ : κ.pathMatch ε₁ hε₁ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel (κ.pathMatch_mem hε₁) <
          F.boundaryLabel (κ.pathMatch_mem hε₂) ∧
        F.boundaryLabel hε₁ <
          F.boundaryLabel (κ.pathMatch_mem hε₁)) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      (κ.pathMatch_mem hε₁) (κ.pathMatch_mem hε₂) hintP₁ hfar]
    refine and_congr_right fun _ => ?_
    have h1 := dir_portFlip_untoggled_iff hc hpf
      (κ.pathMatch_mem hε₁) hintP₁ hT₃
    rw [hππ₁] at h1
    exact h1
  have hm₄ : κ.pathMatch ε₂ hε₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel (κ.pathMatch_mem hε₁) ∧
        ¬ F.boundaryLabel hε₂ <
          F.boundaryLabel (κ.pathMatch_mem hε₂)) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      (κ.pathMatch_mem hε₂) (κ.pathMatch_mem hε₁) hintP₂ hfar₂]
    refine and_congr_right fun _ => ?_
    have h1 := dir_portFlip_toggled_iff hc hpf
      (κ.pathMatch_mem hε₂) hintP₂ hT₄
    rw [hππ₂] at h1
    exact h1
  have hsub : antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ⊆
      ({ε₁, ε₂, κ.pathMatch ε₁ hε₁, κ.pathMatch ε₂ hε₂} :
        Finset W.Flag) := by
    intro δ hδmem
    by_contra hnot
    have h1 : δ ≠ ε₁ := fun h => hnot (by
      rw [h]
      exact Finset.mem_insert_self _ _)
    have h2 : δ ≠ ε₂ := fun h => hnot (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have h3 : δ ≠ κ.pathMatch ε₁ hε₁ := fun h => hnot (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_self _ _)))
    have h4 : δ ≠ κ.pathMatch ε₂ hε₂ := fun h => hnot (by
      rw [h]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))))
    have h5 := (mem_antiLowSet_transport_untouched hsq
      (o.portFlip hpf) hflip hε₁ hε₂ hout h1 h2 h3 h4).mp hδmem
    obtain ⟨hδb, hintδ, hlowδ, hdirδ⟩ := mem_antiLowSet.mp h5
    by_cases hTδ : W.pairing δ ∈ S
    · rcases (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon
          hδb hintδ).mp hTδ with hδ1 | hδ1 <;>
        rcases (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon
          hε₂ hint₂').mp hT₂ with hδ2 | hδ2
      · exact h2 (hδ1.trans hδ2.symm)
      · apply h4
        rw [hδ1]
        exact ((κ.pathMatch_congr hδ2 hε₂
          (κ.pathMatch_mem hβ₂)).trans
          (κ.pathMatch_invol hβ₂)).symm
      · apply h4
        rw [hδ1]
        exact (κ.pathMatch_congr hδ2 hε₂ hβ₂).symm
      · exact h2 (hδ1.trans hδ2.symm)
    · rw [chainDir_portFlip_of_notMem o hpf hTδ] at hdirδ
      exact absurd ((chainDir_true_iff_high hc hδb hintδ).mp
        hdirδ) (lt_asymm hlowδ)
  have d13 : ε₁ ≠ κ.pathMatch ε₁ hε₁ := fun h =>
    κ.pathMatch_ne_self hε₁ h.symm
  have d24 : ε₂ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    κ.pathMatch_ne_self hε₂ h.symm
  have d23 : ε₂ ≠ κ.pathMatch ε₁ hε₁ := fun h => hPne h.symm
  -- ═══════ COUNTING THE CANDIDATES ═══════
  have hcards := card_eq_sum_indicator hsub
  rw [Finset.sum_insert (by simp [hne, d13, hPne']),
    Finset.sum_insert (by simp [d23, d24]),
    Finset.sum_insert (by simp [hPP]),
    Finset.sum_singleton] at hcards
  simp only [hm₁, hm₂, hm₃, hm₄] at hcards
  rw [hcards,
    ← two_indicator_if hLxy
      (F.boundaryLabel (κ.pathMatch_mem hε₁) <
        F.boundaryLabel hε₁)
      (¬ F.boundaryLabel (κ.pathMatch_mem hε₂) <
        F.boundaryLabel hε₂),
    ← two_indicator_if hLxbyb
      (F.boundaryLabel hε₁ <
        F.boundaryLabel (κ.pathMatch_mem hε₁))
      (¬ F.boundaryLabel hε₂ <
        F.boundaryLabel (κ.pathMatch_mem hε₂))]
  omega

/-- **The untoggled anti count**: when neither re-paired chord is
the anchor chord, the anchor chord is untouched by the repair and
contributes exactly its low end to the anti set of the anchored
transported frame; the four re-paired ends contribute the plain
separated indicators. -/
private theorem nonsep_anti_card_untoggled
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hc : PathCanonical o)
    (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    (hflip : (o.portFlip hpf).isOut c = !(o.portFlip hpf).isOut a)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hintβ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags, OnBoundaryChain κ β₂ f → f ∈ S)
    {ε₁ ε₂ : W.Flag} (hε₁ : ε₁ ∈ F.boundaryFlags)
    (hε₂ : ε₂ ∈ F.boundaryFlags)
    (hne : ε₁ ≠ ε₂) (hPne : κ.pathMatch ε₁ hε₁ ≠ ε₂)
    (hcross : (κ.repair a b c d v hsq).pathMatch ε₁ hε₁ = ε₂)
    (hfar : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch ε₁ hε₁) (κ.pathMatch_mem hε₁) =
      κ.pathMatch ε₂ hε₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ ε₁ → δ ≠ ε₂ → δ ≠ κ.pathMatch ε₁ hε₁ →
      δ ≠ κ.pathMatch ε₂ hε₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ)
    (hT₁ : W.pairing ε₁ ∉ S) (hT₂ : W.pairing ε₂ ∉ S) :
    (antiLowSet (RelTransitionSystem.Orientation.transportRepair
        hsq (o.portFlip hpf) hflip)).card =
      (if (if F.boundaryLabel hε₁ < F.boundaryLabel hε₂ then
            F.boundaryLabel (κ.pathMatch_mem hε₁) <
              F.boundaryLabel hε₁
          else F.boundaryLabel (κ.pathMatch_mem hε₂) <
              F.boundaryLabel hε₂) then 1 else 0) +
      (if (if F.boundaryLabel (κ.pathMatch_mem hε₁) <
            F.boundaryLabel (κ.pathMatch_mem hε₂) then
            F.boundaryLabel hε₁ <
              F.boundaryLabel (κ.pathMatch_mem hε₁)
          else F.boundaryLabel hε₂ <
              F.boundaryLabel (κ.pathMatch_mem hε₂)) then 1
        else 0) + 1 := by
  have hcross₂ : (κ.repair a b c d v hsq).pathMatch ε₂ hε₂ = ε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hcross.symm hε₂
      ((κ.repair a b c d v hsq).pathMatch_mem hε₁)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol hε₁)
  have hfar₂ : (κ.repair a b c d v hsq).pathMatch
      (κ.pathMatch ε₂ hε₂) (κ.pathMatch_mem hε₂) =
      κ.pathMatch ε₁ hε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hfar.symm
      (κ.pathMatch_mem hε₂)
      ((κ.repair a b c d v hsq).pathMatch_mem
        (κ.pathMatch_mem hε₁))).trans
      ((κ.repair a b c d v hsq).pathMatch_invol
        (κ.pathMatch_mem hε₁))
  have hPne' : ε₁ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    hPne ((κ.pathMatch_congr h hε₁ (κ.pathMatch_mem hε₂)).trans
      (κ.pathMatch_invol hε₂))
  have hPP : κ.pathMatch ε₁ hε₁ ≠ κ.pathMatch ε₂ hε₂ := by
    intro h
    apply hne
    calc ε₁ = κ.pathMatch (κ.pathMatch ε₁ hε₁)
          (κ.pathMatch_mem hε₁) := (κ.pathMatch_invol hε₁).symm
      _ = κ.pathMatch (κ.pathMatch ε₂ hε₂)
          (κ.pathMatch_mem hε₂) :=
        κ.pathMatch_congr h (κ.pathMatch_mem hε₁)
          (κ.pathMatch_mem hε₂)
      _ = ε₂ := κ.pathMatch_invol hε₂
  have hint₁ : W.pairing ε₁ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₁ (by
        rw [hcross]
        exact fun h => hPne h.symm)
  have hint₂' : W.pairing ε₂ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₂ (by
        rw [hcross₂]
        exact hPne')
  have hintP₁ : W.pairing (κ.pathMatch ε₁ hε₁) ∈
      F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      (κ.pathMatch_mem hε₁) (by
        rw [hfar, κ.pathMatch_invol hε₁]
        exact fun h => hPne' h.symm)
  have hintP₂ : W.pairing (κ.pathMatch ε₂ hε₂) ∈
      F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      (κ.pathMatch_mem hε₂) (by
        rw [hfar₂, κ.pathMatch_invol hε₂]
        exact hPne)
  have hintPβ : W.pairing (κ.pathMatch β₂ hβ₂) ∈
      F.internalFlags := pathMatch_pairing_internal hβ₂ hintβ
  have hT₃ : W.pairing (κ.pathMatch ε₁ hε₁) ∉ S := fun hmem =>
    hT₁ ((toggle_partner hpf hβ₂ hintβ honS hSon hε₁ hint₁).mp
      hmem)
  have hT₄ : W.pairing (κ.pathMatch ε₂ hε₂) ∉ S := fun hmem =>
    hT₂ ((toggle_partner hpf hβ₂ hintβ honS hSon hε₂ hint₂').mp
      hmem)
  have hTβ : W.pairing β₂ ∈ S :=
    (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon hβ₂
      hintβ).mpr (Or.inl rfl)
  have hTγ : W.pairing (κ.pathMatch β₂ hβ₂) ∈ S :=
    (toggle_partner hpf hβ₂ hintβ honS hSon hβ₂ hintβ).mpr hTβ
  have hLxy : F.boundaryLabel hε₁ ≠ F.boundaryLabel hε₂ :=
    fun h => hne (boundaryLabel_inj hε₁ hε₂ h)
  have hLxbyb : F.boundaryLabel (κ.pathMatch_mem hε₁) ≠
      F.boundaryLabel (κ.pathMatch_mem hε₂) :=
    fun h => hPP (boundaryLabel_inj (κ.pathMatch_mem hε₁)
      (κ.pathMatch_mem hε₂) h)
  have hLβγ : F.boundaryLabel hβ₂ ≠
      F.boundaryLabel (κ.pathMatch_mem hβ₂) := fun h =>
    κ.pathMatch_ne_self hβ₂
      (boundaryLabel_inj hβ₂ (κ.pathMatch_mem hβ₂) h).symm
  have hππ₁ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem hε₁)) =
      F.boundaryLabel hε₁ :=
    boundaryLabel_congr _ hε₁ (κ.pathMatch_invol hε₁)
  have hππ₂ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem hε₂)) =
      F.boundaryLabel hε₂ :=
    boundaryLabel_congr _ hε₂ (κ.pathMatch_invol hε₂)
  have hππβ : F.boundaryLabel
      (κ.pathMatch_mem (κ.pathMatch_mem hβ₂)) =
      F.boundaryLabel hβ₂ :=
    boundaryLabel_congr _ hβ₂ (κ.pathMatch_invol hβ₂)
  -- distinctness
  have d13 : ε₁ ≠ κ.pathMatch ε₁ hε₁ := fun h =>
    κ.pathMatch_ne_self hε₁ h.symm
  have d24 : ε₂ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    κ.pathMatch_ne_self hε₂ h.symm
  have d23 : ε₂ ≠ κ.pathMatch ε₁ hε₁ := fun h => hPne h.symm
  have b1 : β₂ ≠ ε₁ := fun h => hT₁ (h ▸ hTβ)
  have b2 : β₂ ≠ ε₂ := fun h => hT₂ (h ▸ hTβ)
  have b3 : β₂ ≠ κ.pathMatch ε₁ hε₁ := fun h => hT₃ (h ▸ hTβ)
  have b4 : β₂ ≠ κ.pathMatch ε₂ hε₂ := fun h => hT₄ (h ▸ hTβ)
  have c1 : κ.pathMatch β₂ hβ₂ ≠ ε₁ := fun h => hT₁ (h ▸ hTγ)
  have c2 : κ.pathMatch β₂ hβ₂ ≠ ε₂ := fun h => hT₂ (h ▸ hTγ)
  have c3 : κ.pathMatch β₂ hβ₂ ≠ κ.pathMatch ε₁ hε₁ := fun h =>
    hT₃ (h ▸ hTγ)
  have c4 : κ.pathMatch β₂ hβ₂ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    hT₄ (h ▸ hTγ)
  have d56 : β₂ ≠ κ.pathMatch β₂ hβ₂ := fun h =>
    κ.pathMatch_ne_self hβ₂ h.symm
  -- membership formulas
  have hm₁ : ε₁ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel hε₁ < F.boundaryLabel hε₂ ∧
        F.boundaryLabel (κ.pathMatch_mem hε₁) <
          F.boundaryLabel hε₁) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      hε₁ hε₂ hint₁ hcross]
    exact and_congr_right fun _ =>
      dir_portFlip_untoggled_iff hc hpf hε₁ hint₁ hT₁
  have hm₂ : ε₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel hε₂ < F.boundaryLabel hε₁ ∧
        F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel hε₂) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      hε₂ hε₁ hint₂' hcross₂]
    exact and_congr_right fun _ =>
      dir_portFlip_untoggled_iff hc hpf hε₂ hint₂' hT₂
  have hm₃ : κ.pathMatch ε₁ hε₁ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel (κ.pathMatch_mem hε₁) <
          F.boundaryLabel (κ.pathMatch_mem hε₂) ∧
        F.boundaryLabel hε₁ <
          F.boundaryLabel (κ.pathMatch_mem hε₁)) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      (κ.pathMatch_mem hε₁) (κ.pathMatch_mem hε₂) hintP₁ hfar]
    refine and_congr_right fun _ => ?_
    have h1 := dir_portFlip_untoggled_iff hc hpf
      (κ.pathMatch_mem hε₁) hintP₁ hT₃
    rw [hππ₁] at h1
    exact h1
  have hm₄ : κ.pathMatch ε₂ hε₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      (F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel (κ.pathMatch_mem hε₁) ∧
        F.boundaryLabel hε₂ <
          F.boundaryLabel (κ.pathMatch_mem hε₂)) := by
    rw [mem_antiLowSet_transport_end hsq (o.portFlip hpf) hflip
      (κ.pathMatch_mem hε₂) (κ.pathMatch_mem hε₁) hintP₂ hfar₂]
    refine and_congr_right fun _ => ?_
    have h1 := dir_portFlip_untoggled_iff hc hpf
      (κ.pathMatch_mem hε₂) hintP₂ hT₄
    rw [hππ₂] at h1
    exact h1
  have hm₅ : β₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      F.boundaryLabel hβ₂ <
        F.boundaryLabel (κ.pathMatch_mem hβ₂) := by
    rw [mem_antiLowSet_transport_untouched hsq (o.portFlip hpf)
        hflip hε₁ hε₂ hout b1 b2 b3 b4,
      mem_antiLowSet]
    constructor
    · rintro ⟨hb, -, hlow, -⟩
      exact hlow
    · intro h
      exact ⟨hβ₂, hintβ, h,
        (dir_portFlip_toggled_iff hc hpf hβ₂ hintβ hTβ).mpr
          (lt_asymm h)⟩
  have hm₆ : κ.pathMatch β₂ hβ₂ ∈ antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ↔
      F.boundaryLabel (κ.pathMatch_mem hβ₂) <
        F.boundaryLabel hβ₂ := by
    rw [mem_antiLowSet_transport_untouched hsq (o.portFlip hpf)
        hflip hε₁ hε₂ hout c1 c2 c3 c4,
      mem_antiLowSet]
    constructor
    · rintro ⟨hb, -, hlow, -⟩
      rwa [hππβ] at hlow
    · intro h
      refine ⟨κ.pathMatch_mem hβ₂, hintPβ, ?_, ?_⟩
      · rwa [hππβ]
      · have h1 := dir_portFlip_toggled_iff hc hpf
          (κ.pathMatch_mem hβ₂) hintPβ hTγ
        rw [hππβ] at h1
        exact h1.mpr (lt_asymm h)
  -- ═══════ THE ANTI SET LIES ON SIX CANDIDATES ═══════
  -- Everything off the four re-paired ends and the anchor chord's
  -- two ends is untouched by both the flip and the repair.
  -- the anti set lies on the six candidates
  have hsub : antiLowSet
      (RelTransitionSystem.Orientation.transportRepair hsq
        (o.portFlip hpf) hflip) ⊆
      ({ε₁, ε₂, κ.pathMatch ε₁ hε₁, κ.pathMatch ε₂ hε₂, β₂,
        κ.pathMatch β₂ hβ₂} : Finset W.Flag) := by
    intro δ hδmem
    by_contra hnot
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      at hnot
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hnot
    have h7 := (mem_antiLowSet_transport_untouched hsq
      (o.portFlip hpf) hflip hε₁ hε₂ hout h1 h2 h3 h4).mp hδmem
    obtain ⟨hδb, hintδ, hlowδ, hdirδ⟩ := mem_antiLowSet.mp h7
    by_cases hTδ : W.pairing δ ∈ S
    · rcases (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon
        hδb hintδ).mp hTδ with hδ1 | hδ1
      · exact h5 hδ1
      · exact h6 hδ1
    · rw [chainDir_portFlip_of_notMem o hpf hTδ] at hdirδ
      exact absurd ((chainDir_true_iff_high hc hδb hintδ).mp
        hdirδ) (lt_asymm hlowδ)
  -- ═══════ COUNTING THE CANDIDATES ═══════
  have hcards := card_eq_sum_indicator hsub
  rw [Finset.sum_insert (by
      simp [hne, d13, hPne', Ne.symm b1, Ne.symm c1]),
    Finset.sum_insert (by
      simp [d23, d24, Ne.symm b2, Ne.symm c2]),
    Finset.sum_insert (by simp [hPP, Ne.symm b3, Ne.symm c3]),
    Finset.sum_insert (by simp [Ne.symm b4, Ne.symm c4]),
    Finset.sum_insert (by simp [d56]),
    Finset.sum_singleton] at hcards
  simp only [hm₁, hm₂, hm₃, hm₄, hm₅, hm₆] at hcards
  have e56 := indicator_pair_one hLβγ
  rw [hcards,
    ← two_indicator_if hLxy
      (F.boundaryLabel (κ.pathMatch_mem hε₁) <
        F.boundaryLabel hε₁)
      (F.boundaryLabel (κ.pathMatch_mem hε₂) <
        F.boundaryLabel hε₂),
    ← two_indicator_if hLxbyb
      (F.boundaryLabel hε₁ <
        F.boundaryLabel (κ.pathMatch_mem hε₁))
      (F.boundaryLabel hε₂ <
        F.boundaryLabel (κ.pathMatch_mem hε₂))]
  omega

/-- **The non-separated per-step flip-count parity**: the anti
count of the anchored transported frame matches, mod 2, the
chord-crossing change of the repair.  The toggle configuration of
the four re-paired ends is resolved by cases: both re-paired new
chords cannot lie on the anchor chord; a mixed configuration feeds
`fourLabel_parity_nonsep`; the untoggled configuration leaves the
anchor chord untouched, contributing the extra flip that feeds
`fourLabel_parity_sep`. -/
private theorem nonsep_count_parity
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex} {S : Finset W.Flag} {p₁ : W.Flag}
    {p₂ : W.Flag} {iβ : α} {iγ : α}
    (hsq : RepairSquare κ a b c d v) {o : κ.Orientation}
    (hc : PathCanonical o)
    (hpf : PortedFlipSet κ S p₁ p₂ iβ iγ)
    (hflip : (o.portFlip hpf).isOut c = !(o.portFlip hpf).isOut a)
    {β₂ : W.Flag} (hβ₂ : β₂ ∈ F.boundaryFlags)
    (hintβ : W.pairing β₂ ∈ F.internalFlags)
    (honS : ∀ f ∈ S, OnBoundaryChain κ β₂ f)
    (hSon : ∀ f ∈ F.internalFlags, OnBoundaryChain κ β₂ f → f ∈ S)
    {ε₁ ε₂ : W.Flag} (hε₁ : ε₁ ∈ F.boundaryFlags)
    (hε₂ : ε₂ ∈ F.boundaryFlags)
    (hne : ε₁ ≠ ε₂) (hPne : κ.pathMatch ε₁ hε₁ ≠ ε₂)
    (hcross : (κ.repair a b c d v hsq).pathMatch ε₁ hε₁ = ε₂)
    (hfar : (κ.repair a b c d v hsq).pathMatch
        (κ.pathMatch ε₁ hε₁) (κ.pathMatch_mem hε₁) =
      κ.pathMatch ε₂ hε₂)
    (hout : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      δ ≠ ε₁ → δ ≠ ε₂ → δ ≠ κ.pathMatch ε₁ hε₁ →
      δ ≠ κ.pathMatch ε₂ hε₂ →
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ) :
    ((antiLowSet (RelTransitionSystem.Orientation.transportRepair
        hsq (o.portFlip hpf) hflip)).card +
      (chordCrossingCount κ +
        chordCrossingCount (κ.repair a b c d v hsq))) % 2 = 0 := by
  have hcross₂ : (κ.repair a b c d v hsq).pathMatch ε₂ hε₂ = ε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hcross.symm hε₂
      ((κ.repair a b c d v hsq).pathMatch_mem hε₁)).trans
      ((κ.repair a b c d v hsq).pathMatch_invol hε₁)
  have hfar₂ : (κ.repair a b c d v hsq).pathMatch
      (κ.pathMatch ε₂ hε₂) (κ.pathMatch_mem hε₂) =
      κ.pathMatch ε₁ hε₁ :=
    ((κ.repair a b c d v hsq).pathMatch_congr hfar.symm
      (κ.pathMatch_mem hε₂)
      ((κ.repair a b c d v hsq).pathMatch_mem
        (κ.pathMatch_mem hε₁))).trans
      ((κ.repair a b c d v hsq).pathMatch_invol
        (κ.pathMatch_mem hε₁))
  have hPne' : ε₁ ≠ κ.pathMatch ε₂ hε₂ := fun h =>
    hPne ((κ.pathMatch_congr h hε₁ (κ.pathMatch_mem hε₂)).trans
      (κ.pathMatch_invol hε₂))
  have hPP : κ.pathMatch ε₁ hε₁ ≠ κ.pathMatch ε₂ hε₂ := by
    intro h
    apply hne
    calc ε₁ = κ.pathMatch (κ.pathMatch ε₁ hε₁)
          (κ.pathMatch_mem hε₁) := (κ.pathMatch_invol hε₁).symm
      _ = κ.pathMatch (κ.pathMatch ε₂ hε₂)
          (κ.pathMatch_mem hε₂) :=
        κ.pathMatch_congr h (κ.pathMatch_mem hε₁)
          (κ.pathMatch_mem hε₂)
      _ = ε₂ := κ.pathMatch_invol hε₂
  have hint₁ : W.pairing ε₁ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₁ (by
        rw [hcross]
        exact fun h => hPne h.symm)
  have hint₂' : W.pairing ε₂ ∈ F.internalFlags :=
    repartner_internal (κ := κ) (κ' := κ.repair a b c d v hsq)
      hε₂ (by
        rw [hcross₂]
        exact hPne')
  have hLxy : F.boundaryLabel hε₁ ≠ F.boundaryLabel hε₂ :=
    fun h => hne (boundaryLabel_inj hε₁ hε₂ h)
  have hLxbyb : F.boundaryLabel (κ.pathMatch_mem hε₁) ≠
      F.boundaryLabel (κ.pathMatch_mem hε₂) :=
    fun h => hPP (boundaryLabel_inj (κ.pathMatch_mem hε₁)
      (κ.pathMatch_mem hε₂) h)
  have hLx_xb : F.boundaryLabel hε₁ ≠
      F.boundaryLabel (κ.pathMatch_mem hε₁) := fun h =>
    κ.pathMatch_ne_self hε₁
      (boundaryLabel_inj hε₁ (κ.pathMatch_mem hε₁) h).symm
  have hLy_yb : F.boundaryLabel hε₂ ≠
      F.boundaryLabel (κ.pathMatch_mem hε₂) := fun h =>
    κ.pathMatch_ne_self hε₂
      (boundaryLabel_inj hε₂ (κ.pathMatch_mem hε₂) h).symm
  have hLx_yb : F.boundaryLabel hε₁ ≠
      F.boundaryLabel (κ.pathMatch_mem hε₂) := fun h =>
    hPne' (boundaryLabel_inj hε₁ (κ.pathMatch_mem hε₂) h)
  have hLxb_y : F.boundaryLabel (κ.pathMatch_mem hε₁) ≠
      F.boundaryLabel hε₂ := fun h =>
    hPne (boundaryLabel_inj (κ.pathMatch_mem hε₁) hε₂ h)
  -- ═══════ THE FOUR ENDS AND THEIR LABELS ═══════
  -- Above: the re-paired ends are four distinct flags carrying four
  -- distinct labels.  Below: the crossing parity and the directions.
  have hccp := chordCrossingCount_repair_parity hε₁ hε₂ hne hPne
    hcross hfar hout
  have hdirs := swap_dirs_opposite hsq (o.portFlip hpf) hflip hε₁
    hcross hint₁
  have i1 := chainDir_true_iff_high hc hε₁ hint₁
  have i2 := chainDir_true_iff_high hc hε₂ hint₂'
  -- ═══════ WHICH ENDS THE CHAIN FLIP TOGGLES ═══════
  -- The anchor chain meets at most one of the two chords, so the
  -- both-toggled case is impossible and the rest split by which.
  by_cases hT₁ : W.pairing ε₁ ∈ S <;>
    by_cases hT₂ : W.pairing ε₂ ∈ S
  · -- both toggled: impossible
    exfalso
    rcases (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon hε₁
        hint₁).mp hT₁ with h1 | h1 <;>
      rcases (pairing_mem_flipSet_iff hpf hβ₂ hintβ honS hSon hε₂
        hint₂').mp hT₂ with h2 | h2
    · exact hne (h1.trans h2.symm)
    · apply hPne
      rw [h2]
      exact κ.pathMatch_congr h1 hε₁ hβ₂
    · apply hPne
      rw [h2]
      calc κ.pathMatch ε₁ hε₁
          = κ.pathMatch (κ.pathMatch β₂ hβ₂)
            (κ.pathMatch_mem hβ₂) :=
            κ.pathMatch_congr h1 hε₁ (κ.pathMatch_mem hβ₂)
        _ = β₂ := κ.pathMatch_invol hβ₂
    · exact hne (h1.trans h2.symm)
  · -- toggled cross untoggled: the swapped mixed case
    have h1 := hdirs
    rw [chainDir_portFlip_of_mem o hpf hT₁,
      chainDir_portFlip_of_notMem o hpf hT₂] at h1
    have hdd : chainDir o ε₂ = chainDir o ε₁ := by
      rw [h1, Bool.not_not]
    have hsame' : (F.boundaryLabel (κ.pathMatch_mem hε₂) <
        F.boundaryLabel hε₂) =
        (F.boundaryLabel (κ.pathMatch_mem hε₁) <
          F.boundaryLabel hε₁) := by
      apply propext
      constructor
      · intro h
        exact i1.mp (hdd.symm.trans (i2.mpr h))
      · intro h
        exact i2.mp (hdd.trans (i1.mpr h))
    have hcard := nonsep_anti_card_mixed hsq hc hpf hflip hβ₂
      hintβ honS hSon hε₂ hε₁ (Ne.symm hne)
      (fun h => hPne' h.symm) hcross₂ hfar₂
      (fun δ hδ k1 k2 k3 k4 => hout δ hδ k2 k1 k4 k3) hT₂ hT₁
    have hfour := fourLabel_parity_nonsep hLy_yb hLx_xb
      (Ne.symm hLxy) (Ne.symm hLxb_y) (Ne.symm hLx_yb)
      (Ne.symm hLxbyb) hsame'
    have ec1 : (if chordPairCrossSym
        (F.boundaryLabel hε₂, F.boundaryLabel (κ.pathMatch_mem hε₂))
        (F.boundaryLabel hε₁, F.boundaryLabel (κ.pathMatch_mem hε₁))
        then 1 else 0 : ℕ) =
        if chordPairCrossSym
          (F.boundaryLabel hε₁,
            F.boundaryLabel (κ.pathMatch_mem hε₁))
          (F.boundaryLabel hε₂,
            F.boundaryLabel (κ.pathMatch_mem hε₂))
          then 1 else 0 :=
      if_congr (chordPairCrossSym_comm _ _) rfl rfl
    have ec2 : (if chordPairCrossSym
        (F.boundaryLabel hε₂, F.boundaryLabel hε₁)
        (F.boundaryLabel (κ.pathMatch_mem hε₂),
          F.boundaryLabel (κ.pathMatch_mem hε₁))
        then 1 else 0 : ℕ) =
        if chordPairCrossSym
          (F.boundaryLabel hε₁, F.boundaryLabel hε₂)
          (F.boundaryLabel (κ.pathMatch_mem hε₁),
            F.boundaryLabel (κ.pathMatch_mem hε₂))
          then 1 else 0 :=
      if_congr (chordPairCrossSym_swap_pair
        (F.boundaryLabel hε₁) (F.boundaryLabel hε₂)
        (F.boundaryLabel (κ.pathMatch_mem hε₁))
        (F.boundaryLabel (κ.pathMatch_mem hε₂))) rfl rfl
    omega
  · -- untoggled cross toggled: the direct mixed case
    have h1 := hdirs
    rw [chainDir_portFlip_of_notMem o hpf hT₁,
      chainDir_portFlip_of_mem o hpf hT₂] at h1
    have hdd : chainDir o ε₂ = chainDir o ε₁ := by
      have h2 := congrArg (fun z => !z) h1
      simpa using h2
    have hsame : (F.boundaryLabel (κ.pathMatch_mem hε₁) <
        F.boundaryLabel hε₁) =
        (F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel hε₂) := by
      apply propext
      constructor
      · intro h
        exact i2.mp (hdd.trans (i1.mpr h))
      · intro h
        exact i1.mp (hdd.symm.trans (i2.mpr h))
    have hcard := nonsep_anti_card_mixed hsq hc hpf hflip hβ₂
      hintβ honS hSon hε₁ hε₂ hne hPne hcross hfar hout hT₁ hT₂
    have hfour := fourLabel_parity_nonsep hLx_xb hLy_yb hLxy
      hLx_yb hLxb_y hLxbyb hsame
    omega
  · -- both untoggled: the anchored extra flip
    have h1 := hdirs
    rw [chainDir_portFlip_of_notMem o hpf hT₁,
      chainDir_portFlip_of_notMem o hpf hT₂] at h1
    have hsep : (F.boundaryLabel (κ.pathMatch_mem hε₁) <
        F.boundaryLabel hε₁) ≠
        (F.boundaryLabel (κ.pathMatch_mem hε₂) <
          F.boundaryLabel hε₂) := by
      cases hb : chainDir o ε₁
      · rw [hb, Bool.not_false] at h1
        refine prop_ne_of_right ?_ (i2.mp h1)
        intro hlt
        rw [i1.mpr hlt] at hb
        cases hb
      · rw [hb, Bool.not_true] at h1
        refine prop_ne_of_left (i1.mp hb) ?_
        intro hlt
        rw [i2.mpr hlt] at h1
        cases h1
    have hcard := nonsep_anti_card_untoggled hsq hc hpf hflip hβ₂
      hintβ honS hSon hε₁ hε₂ hne hPne hcross hfar hout hT₁ hT₂
    have hfour := fourLabel_parity_sep hLx_xb hLy_yb hLxy hLx_yb
      hLxb_y hLxbyb hsep
    omega

end NonsepCount

/-! ## The per-step composed status ledger -/

section StepLemma

/-- **The per-step composed ledger**: across one repair step from a
canonical frame, the state relabel is `stateOddFlipSet` at the fold
of an explicit flip list `T` with `pairFold T = statusDiff κ₁ κ₂`,
the sign is `(−1)^tp · flipSignProd g T` at any colour function `g`
matching the state, and the flip count satisfies the crossing
parity `tp + |T| ≡ cc κ₁ + cc κ₂ (mod 2)`. -/
theorem stepStatusLedger
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ : F.RelTransitionSystem} (hstep : IsRepairStep κ₁ κ₂)
    {o₁ : κ₁.Orientation} (hc₁ : PathCanonical o₁)
    (g : α → Fin (2 * ℓ))
    (hg : ∀ i c, st i = Sum.inr c → g i = c) :
    ∃ (o₂ : κ₂.Orientation) (T : List (α × α)) (tp : ℕ),
      PathCanonical o₂ ∧
      (∀ p ∈ T, p.1 ≠ p.2) ∧
      pairFold T = statusDiff κ₁ κ₂ ∧
      (tp + T.length + chordCrossingCount κ₁ +
        chordCrossingCount κ₂) % 2 = 0 ∧
      F.throughSummand hM (stateOddFlipSet st (pairFold T))
          (genBoundarySubsetMatches_stateOddFlipSet hbnd
            (pairFold T)) o₂ κ₂.openCircuitCount =
        (((-1) ^ tp * flipSignProd g T : ℤ) : ℂ) *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount := by
  obtain ⟨a, b, c, d, v, hsq, heq⟩ := hstep
  by_cases hloc : SquareLocalized κ₁ a b c d
  · -- ═══════ LOCALIZED SQUARE ═══════
    -- No relabel, no sign, and no status change: the step is
    -- pairing-preserving, so the single-step ledger applies and the
    -- flip list is empty.
    have hmps : MatchPreservingStep κ₁ κ₂ :=
      ⟨a, b, c, d, v, hsq, RelTransitionSystem.MatchEq.symm heq,
        pathMatch_repair_of_localized hsq hloc⟩
    obtain ⟨o₂, hc₂, hval⟩ := stepLedger_single hM st hbnd κ₁ κ₂
      hmps o₁ hc₁
    have hsp : SamePairing κ₁ κ₂ := samePairing_of_step hmps
    have hps : pathSign κ₁ = pathSign κ₂ :=
      pathSign_of_samePairing hsp
    have hnz : pathSign κ₂ ≠ 0 := by
      unfold pathSign
      exact pow_ne_zero _ (by norm_num)
    refine ⟨o₂, [], 0, hc₂, ?_, ?_, ?_, ?_⟩
    · intro p hp
      cases hp
    · rw [pairFold_nil]
      exact (statusDiff_of_samePairing hsp).symm
    · have hcc := chordCrossingCount_of_samePairing hsp
      simp only [List.length_nil]
      omega
    · have h1 : (((-1 : ℤ)) ^ 0 * flipSignProd g [] : ℤ) = 1 := by
        rw [flipSignProd_nil]
        norm_num
      rw [pairFold_nil, h1, Int.cast_one, one_mul,
        F.throughSummand_state_congr hM stateOddFlipSet_empty
          (genBoundarySubsetMatches_stateOddFlipSet hbnd ∅) hbnd
          o₂ κ₂.openCircuitCount]
      rw [hps] at hval
      exact mul_left_cancel₀ hnz hval
  · -- ═══════ TWO-CHAIN SQUARE ═══════
    -- The repair transposes the boundary pairing at the two chain
    -- ends `ε₁, ε₂`; the flip list is those two labels, and the
    -- orientation splits into the separated and non-separated cases.
    obtain ⟨ε₁, ε₂, hε₁, hε₂, hne, hPne, hcross, hfar, hout⟩ :=
      pathMatch_repair_swap hsq hloc
    have hcross₂ : (κ₁.repair a b c d v hsq).pathMatch ε₂ hε₂ =
        ε₁ :=
      ((κ₁.repair a b c d v hsq).pathMatch_congr hcross.symm hε₂
        ((κ₁.repair a b c d v hsq).pathMatch_mem hε₁)).trans
        ((κ₁.repair a b c d v hsq).pathMatch_invol hε₁)
    have hfar₂ : (κ₁.repair a b c d v hsq).pathMatch
        (κ₁.pathMatch ε₂ hε₂) (κ₁.pathMatch_mem hε₂) =
        κ₁.pathMatch ε₁ hε₁ :=
      ((κ₁.repair a b c d v hsq).pathMatch_congr hfar.symm
        (κ₁.pathMatch_mem hε₂)
        ((κ₁.repair a b c d v hsq).pathMatch_mem
          (κ₁.pathMatch_mem hε₁))).trans
        ((κ₁.repair a b c d v hsq).pathMatch_invol
          (κ₁.pathMatch_mem hε₁))
    have hPne' : ε₁ ≠ κ₁.pathMatch ε₂ hε₂ := fun h =>
      hPne ((κ₁.pathMatch_congr h hε₁
        (κ₁.pathMatch_mem hε₂)).trans (κ₁.pathMatch_invol hε₂))
    have hPP : κ₁.pathMatch ε₁ hε₁ ≠ κ₁.pathMatch ε₂ hε₂ := by
      intro h
      apply hne
      calc ε₁ = κ₁.pathMatch (κ₁.pathMatch ε₁ hε₁)
            (κ₁.pathMatch_mem hε₁) :=
            (κ₁.pathMatch_invol hε₁).symm
        _ = κ₁.pathMatch (κ₁.pathMatch ε₂ hε₂)
            (κ₁.pathMatch_mem hε₂) :=
          κ₁.pathMatch_congr h (κ₁.pathMatch_mem hε₁)
            (κ₁.pathMatch_mem hε₂)
        _ = ε₂ := κ₁.pathMatch_invol hε₂
    have hint₁ : W.pairing ε₁ ∈ F.internalFlags :=
      repartner_internal (κ := κ₁)
        (κ' := κ₁.repair a b c d v hsq) hε₁ (by
          rw [hcross]
          exact fun h => hPne h.symm)
    have hint₂' : W.pairing ε₂ ∈ F.internalFlags :=
      repartner_internal (κ := κ₁)
        (κ' := κ₁.repair a b c d v hsq) hε₂ (by
          rw [hcross₂]
          exact hPne')
    have hintP₁ : W.pairing (κ₁.pathMatch ε₁ hε₁) ∈
        F.internalFlags :=
      repartner_internal (κ := κ₁)
        (κ' := κ₁.repair a b c d v hsq)
        (κ₁.pathMatch_mem hε₁) (by
          rw [hfar, κ₁.pathMatch_invol hε₁]
          exact fun h => hPne' h.symm)
    have hintP₂ : W.pairing (κ₁.pathMatch ε₂ hε₂) ∈
        F.internalFlags :=
      repartner_internal (κ := κ₁)
        (κ' := κ₁.repair a b c d v hsq)
        (κ₁.pathMatch_mem hε₂) (by
          rw [hfar₂, κ₁.pathMatch_invol hε₂]
          exact hPne)
    have hLxy : F.boundaryLabel hε₁ ≠ F.boundaryLabel hε₂ :=
      fun h => hne (boundaryLabel_inj hε₁ hε₂ h)
    have hLxbyb : F.boundaryLabel (κ₁.pathMatch_mem hε₁) ≠
        F.boundaryLabel (κ₁.pathMatch_mem hε₂) :=
      fun h => hPP (boundaryLabel_inj (κ₁.pathMatch_mem hε₁)
        (κ₁.pathMatch_mem hε₂) h)
    have hLx_xb : F.boundaryLabel hε₁ ≠
        F.boundaryLabel (κ₁.pathMatch_mem hε₁) := fun h =>
      κ₁.pathMatch_ne_self hε₁
        (boundaryLabel_inj hε₁ (κ₁.pathMatch_mem hε₁) h).symm
    have hLy_yb : F.boundaryLabel hε₂ ≠
        F.boundaryLabel (κ₁.pathMatch_mem hε₂) := fun h =>
      κ₁.pathMatch_ne_self hε₂
        (boundaryLabel_inj hε₂ (κ₁.pathMatch_mem hε₂) h).symm
    have hLx_yb : F.boundaryLabel hε₁ ≠
        F.boundaryLabel (κ₁.pathMatch_mem hε₂) := fun h =>
      hPne' (boundaryLabel_inj hε₁ (κ₁.pathMatch_mem hε₂) h)
    have hLxb_y : F.boundaryLabel (κ₁.pathMatch_mem hε₁) ≠
        F.boundaryLabel hε₂ := fun h =>
      hPne (boundaryLabel_inj (κ₁.pathMatch_mem hε₁) hε₂ h)
    have hccp := chordCrossingCount_repair_parity hε₁ hε₂ hne
      hPne hcross hfar hout
    have hcc₂ : chordCrossingCount κ₂ =
        chordCrossingCount (κ₁.repair a b c d v hsq) :=
      chordCrossingCount_matchEq heq
    by_cases hsame : o₁.isOut c = o₁.isOut a
    · -- ─────── non-separated ───────
      -- The chain of `c` is flipped first, which moves the state at
      -- its two ends, and the flipped square is then separated.
      obtain ⟨β₁, β₂, hβ₁, hβ₂, hca, hcc, h21, h2γ⟩ :=
        twoChains_of_not_localized hsq hloc
      obtain ⟨kc, hkle, hcont, hterm⟩ :=
        chain_terminates_with_data κ₁ hβ₂
      have hk : 1 ≤ kc := by
        by_contra hlt
        obtain rfl : kc = 0 := by omega
        obtain ⟨k', t, htk, hcont', hterm', hft⟩ := hcc
        have hkk : k' = 0 :=
          chain_exit_unique hcont' hterm' hcont hterm
        subst hkk
        obtain rfl : t = 0 := by omega
        simp only [iterWalk_zero] at hterm
        rcases hft with hE | hE
        · rw [iterWalk_zero] at hE
          exact Finset.disjoint_left.mp
            F.internalFlags_disjoint_boundaryFlags (hE ▸ hsq.hc)
            hβ₂
        · rw [iterWalk_zero] at hE
          exact Finset.disjoint_left.mp
            F.internalFlags_disjoint_boundaryFlags (hE ▸ hsq.hc)
            hterm
      obtain ⟨iβ, hiβ⟩ := F.attach_boundary_of_mem hβ₂
      obtain ⟨iγ, hiγ⟩ := F.attach_boundary_of_mem hterm
      obtain ⟨S, hpf, honS, hSon⟩ :=
        exists_chainPortedFlipSet κ₁ hβ₂ hcont hterm hk hiβ hiγ
      have hcS : c ∈ S := hSon c hsq.hc hcc
      have h1γ2 : β₁ ≠ κ₁.pathMatch β₂ hβ₂ := by
        intro he
        apply h2γ
        have h3 := κ₁.pathMatch_congr he hβ₁
          (κ₁.pathMatch_mem hβ₂)
        exact (h3.trans (κ₁.pathMatch_invol hβ₂)).symm
      have haS : a ∉ S := fun hmem =>
        onBoundaryChain_disjoint hβ₂ hβ₁ (Ne.symm h21) h1γ2
          (honS a hmem) hca
      have hbF₁ : W.boundaryFlag iβ ∈ F.flags := by
        rw [← W.eq_boundaryFlag iβ β₂ hiβ]
        exact mem_flags_of_boundaryFlags F hβ₂
      have hbF₂ : W.boundaryFlag iγ ∈ F.flags := by
        rw [← W.eq_boundaryFlag iγ _ hiγ]
        exact mem_flags_of_boundaryFlags F hterm
      obtain ⟨c₁, hcol₁⟩ := (hbnd iβ).mp hbF₁
      obtain ⟨c₂, hcol₂⟩ := (hbnd iγ).mp hbF₂
      have hbndS := genBoundarySubsetMatches_stateOddFlip hbnd
        iβ iγ
      have hcol₁' : stateOddFlip st iβ iγ iβ =
          Sum.inr (oddPartner ℓ c₁) := stateOddFlip_left_odd hcol₁
      have hcol₂' : stateOddFlip st iβ iγ iγ =
          Sum.inr (oddPartner ℓ c₂) := stateOddFlip_right_odd hcol₂
      have hflip' := portFlip_separated o₁ hpf hsame hcS haS
      have htrans := twoPathNonSep_transform hM
        (stateOddFlip st iβ iγ) hbndS hsq o₁ hsame hloc hpf hcS
        haS hcol₁' hcol₂'
      have hret := F.throughSummand_state_congr hM
        (stateOddFlip_stateOddFlip (st := st) (i₁ := iβ)
          (i₂ := iγ))
        (genBoundarySubsetMatches_stateOddFlip hbndS iβ iγ) hbnd
        (κ := κ₁) o₁ κ₁.openCircuitCount
      rw [hret] at htrans
      have hint₂ : W.pairing β₂ ∈ F.internalFlags := by
        have h0 := hcont 0 hk
        rwa [iterWalk_zero] at h0
      have hpm₂ : κ₁.pathMatch β₂ hβ₂ =
          W.pairing (iterWalk κ₁ β₂ kc) :=
        κ₁.pathMatch_eq hβ₂ (traceChain_fuel_mono κ₁ (by omega)
          (traceChain_forward κ₁ β₂ hcont hterm))
      have hlabβ : F.boundaryLabel hβ₂ = iβ :=
        boundaryLabel_eq_of_attach hβ₂ hiβ
      have hlabγ : F.boundaryLabel (κ₁.pathMatch_mem hβ₂) =
          iγ := by
        apply boundaryLabel_eq_of_attach
        rw [hpm₂]
        exact hiγ
      obtain ⟨o'', L, hcanon, hlen, hpw, hprov, hled⟩ :=
        exists_recanonicalize_signed hM (stateOddFlip st iβ iγ)
          hbndS
          (RelTransitionSystem.Orientation.transportRepair hsq
            (o₁.portFlip hpf) hflip')
          (flipColours g (iβ, iγ)) (flipColours_matches hg iβ iγ)
      have hstEq : stateOddFlipSet (stateOddFlip st iβ iγ)
          (pairFold L) =
          stateOddFlipSet st (pairFold ((iβ, iγ) :: L)) := by
        rw [stateOddFlip_eq_flipSet, stateOddFlipSet_symmU,
          pairFold_cons]
        rfl
      have hb1 := genBoundarySubsetMatches_stateOddFlipSet hbndS
        (pairFold L)
      have hb2 := genBoundarySubsetMatches_stateOddFlipSet hbnd
        (pairFold ((iβ, iγ) :: L))
      have hsq2 : ((flipSignProd (flipColours g (iβ, iγ)) L :
          ℤ) : ℂ) *
          ((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) : ℂ) =
          1 := by
        rw [← Int.cast_mul, flipSignProd_mul_self, Int.cast_one]
      have hval' : F.throughSummand hM
          (stateOddFlipSet st (pairFold ((iβ, iγ) :: L))) hb2 o''
          ((κ₁.repair a b c d v hsq).openCircuitCount) =
          (((-1) ^ 1 * flipSignProd g ((iβ, iγ) :: L) : ℤ) : ℂ) *
            F.throughSummand hM st hbnd o₁
              κ₁.openCircuitCount := by
        have h1 := hled
          ((κ₁.repair a b c d v hsq).openCircuitCount)
        have h3 : ((flipSignProd (flipColours g (iβ, iγ)) L :
            ℤ) : ℂ) *
            F.throughSummand hM
              (stateOddFlipSet (stateOddFlip st iβ iγ)
                (pairFold L)) hb1 o''
              ((κ₁.repair a b c d v hsq).openCircuitCount) =
            twoPathNonSepFactor ℓ (oddPartner ℓ c₁)
                (oddPartner ℓ c₂) *
              F.throughSummand hM st hbnd o₁
                κ₁.openCircuitCount :=
          h1.symm.trans htrans
        have hcongr := F.throughSummand_state_congr hM hstEq hb1
          hb2 o'' ((κ₁.repair a b c d v hsq).openCircuitCount)
        have hfac : twoPathNonSepFactor ℓ (oddPartner ℓ c₁)
            (oddPartner ℓ c₂) =
            -((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) :
              ℂ) := by
          rw [twoPathNonSepFactor_eq, oddPartnerSign_oddPartner,
            oddPartnerSign_oddPartner]
          push_cast
          ring
        have hsign : (((-1) ^ 1 *
            flipSignProd g ((iβ, iγ) :: L) : ℤ) : ℂ) =
            -((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) :
              ℂ) *
              ((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                ℂ) := by
          rw [flipSignProd_cons,
            show g (iβ, iγ).1 = c₁ from hg _ c₁ hcol₁,
            show g (iβ, iγ).2 = c₂ from hg _ c₂ hcol₂]
          push_cast
          ring
        calc F.throughSummand hM
              (stateOddFlipSet st (pairFold ((iβ, iγ) :: L)))
              hb2 o''
              ((κ₁.repair a b c d v hsq).openCircuitCount)
            = F.throughSummand hM
                (stateOddFlipSet (stateOddFlip st iβ iγ)
                  (pairFold L)) hb1 o''
                ((κ₁.repair a b c d v hsq).openCircuitCount) :=
              hcongr.symm
          _ = (((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                ℂ) *
                ((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                  ℂ)) *
              F.throughSummand hM
                (stateOddFlipSet (stateOddFlip st iβ iγ)
                  (pairFold L)) hb1 o''
                ((κ₁.repair a b c d v hsq).openCircuitCount) := by
              rw [hsq2, one_mul]
          _ = ((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                ℂ) *
              (((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                ℂ) *
                F.throughSummand hM
                  (stateOddFlipSet (stateOddFlip st iβ iγ)
                    (pairFold L)) hb1 o''
                  ((κ₁.repair a b c d v hsq).openCircuitCount)) :=
              by ring
          _ = ((flipSignProd (flipColours g (iβ, iγ)) L : ℤ) :
                ℂ) *
              (twoPathNonSepFactor ℓ (oddPartner ℓ c₁)
                  (oddPartner ℓ c₂) *
                F.throughSummand hM st hbnd o₁
                  κ₁.openCircuitCount) := by rw [h3]
          _ = (((-1) ^ 1 * flipSignProd g ((iβ, iγ) :: L) : ℤ) :
                ℂ) *
              F.throughSummand hM st hbnd o₁
                κ₁.openCircuitCount := by
              rw [hfac, hsign]
              ring
      obtain ⟨o₂, hc₂, htrans₂⟩ := matchEq_canonical_transfer hM
        (stateOddFlipSet st (pairFold ((iβ, iγ) :: L))) hb2 heq
        hcanon
      refine ⟨o₂, (iβ, iγ) :: L, 1, hc₂, ?_, ?_, ?_, ?_⟩
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp'
        · exact hpf.hlab
        · exact ne_of_lt (AntiLowPair.lt (hprov p hp'))
      · rw [← statusDiff_matchEq_right heq]
        apply Finset.ext
        intro i
        rw [mem_statusDiff]
        exact nonsep_labels_eq_statusChange hsq hc₁ hpf hflip'
          hβ₂ hint₂ honS hSon hlabβ hlabγ hprov hpw hlen
      · have hcnt := nonsep_count_parity hsq hc₁ hpf hflip' hβ₂
          hint₂ honS hSon hε₁ hε₂ hne hPne hcross hfar hout
        rw [List.length_cons, hlen]
        omega
      · exact htrans₂.trans hval'
    · -- ─────── separated ───────
      -- The orientation transports verbatim; re-canonicalizing it
      -- supplies the flip list and the transform gives the sign.
      have hflip : o₁.isOut c = !o₁.isOut a := by
        cases h1 : o₁.isOut c <;> cases h2 : o₁.isOut a <;>
          simp_all
      obtain ⟨o'', L, hcanon, hlen, hpw, hprov, hled⟩ :=
        exists_recanonicalize_signed hM st hbnd
          (RelTransitionSystem.Orientation.transportRepair hsq o₁
            hflip) g hg
      have hb2 := genBoundarySubsetMatches_stateOddFlipSet hbnd
        (pairFold L)
      have h2 := twoPath_transform hM st hbnd hsq o₁ hflip hloc
      rw [twoPathTransformFactor_eq_neg_one] at h2
      have hsq2 : ((flipSignProd g L : ℤ) : ℂ) *
          ((flipSignProd g L : ℤ) : ℂ) = 1 := by
        rw [← Int.cast_mul, flipSignProd_mul_self, Int.cast_one]
      have hval' : F.throughSummand hM
          (stateOddFlipSet st (pairFold L)) hb2 o''
          ((κ₁.repair a b c d v hsq).openCircuitCount) =
          (((-1) ^ 1 * flipSignProd g L : ℤ) : ℂ) *
            F.throughSummand hM st hbnd o₁
              κ₁.openCircuitCount := by
        have h1 := hled
          ((κ₁.repair a b c d v hsq).openCircuitCount)
        have h3 : ((flipSignProd g L : ℤ) : ℂ) *
            F.throughSummand hM (stateOddFlipSet st (pairFold L))
              hb2 o''
              ((κ₁.repair a b c d v hsq).openCircuitCount) =
            -1 * F.throughSummand hM st hbnd o₁
              κ₁.openCircuitCount :=
          h1.symm.trans h2
        calc F.throughSummand hM (stateOddFlipSet st (pairFold L))
              hb2 o''
              ((κ₁.repair a b c d v hsq).openCircuitCount)
            = (((flipSignProd g L : ℤ) : ℂ) *
                ((flipSignProd g L : ℤ) : ℂ)) *
              F.throughSummand hM
                (stateOddFlipSet st (pairFold L)) hb2 o''
                ((κ₁.repair a b c d v hsq).openCircuitCount) := by
              rw [hsq2, one_mul]
          _ = ((flipSignProd g L : ℤ) : ℂ) *
              (((flipSignProd g L : ℤ) : ℂ) *
                F.throughSummand hM
                  (stateOddFlipSet st (pairFold L)) hb2 o''
                  ((κ₁.repair a b c d v hsq).openCircuitCount)) :=
              by ring
          _ = ((flipSignProd g L : ℤ) : ℂ) *
              (-1 * F.throughSummand hM st hbnd o₁
                κ₁.openCircuitCount) := by rw [h3]
          _ = (((-1) ^ 1 * flipSignProd g L : ℤ) : ℂ) *
              F.throughSummand hM st hbnd o₁
                κ₁.openCircuitCount := by
              push_cast
              ring
      obtain ⟨o₂, hc₂, htrans₂⟩ := matchEq_canonical_transfer hM
        (stateOddFlipSet st (pairFold L)) hb2 heq hcanon
      refine ⟨o₂, L, 1, hc₂, ?_, ?_, ?_, ?_⟩
      · exact fun p hp => ne_of_lt (AntiLowPair.lt (hprov p hp))
      · rw [← statusDiff_matchEq_right heq]
        apply Finset.ext
        intro i
        rw [mem_statusDiff, mem_pairFold_antiLow hprov hpw hlen]
        exact antiLow_labels_eq_statusChange hsq hflip hc₁ hε₁
          hε₂ hcross hfar hout hint₁ hint₂' hintP₁ hintP₂
      · have hcardL := hlen.trans (antiLowSet_transport_card hsq
          hflip hc₁ hε₁ hε₂ hne hPne hcross hfar hout hint₁
          hint₂' hintP₁ hintP₂)
        have hdirs := swap_dirs_opposite hsq o₁ hflip hε₁ hcross
          hint₁
        have i1 := chainDir_true_iff_high hc₁ hε₁ hint₁
        have i2 := chainDir_true_iff_high hc₁ hε₂ hint₂'
        have hsep : (F.boundaryLabel (κ₁.pathMatch_mem hε₁) <
            F.boundaryLabel hε₁) ≠
            (F.boundaryLabel (κ₁.pathMatch_mem hε₂) <
              F.boundaryLabel hε₂) := by
          cases hb : chainDir o₁ ε₁
          · rw [hb, Bool.not_false] at hdirs
            refine prop_ne_of_right ?_ (i2.mp hdirs)
            intro hlt
            rw [i1.mpr hlt] at hb
            cases hb
          · rw [hb, Bool.not_true] at hdirs
            refine prop_ne_of_left (i1.mp hb) ?_
            intro hlt
            rw [i2.mpr hlt] at hdirs
            cases hdirs
        have hfour := fourLabel_parity_sep hLx_xb hLy_yb hLxy
          hLx_yb hLxb_y hLxbyb hsep
        omega
      · exact htrans₂.trans hval'

/-- **The chain status ledger**: fold the per-step ledger along a
repair chain — the relabel set is the status difference of the
endpoint stages, the sign is the explicit
`(−1)^tp · flipSignProd g T`, and the flip count carries the
crossing parity telescope. -/
theorem chainStatusLedger
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st) {n : ℕ}
    (chain : Fin (n + 1) → F.RelTransitionSystem)
    (hstep : ∀ r : Fin n,
      IsRepairStep (chain r.castSucc) (chain r.succ))
    {o₀ : (chain 0).Orientation} (hc₀ : PathCanonical o₀)
    (g : α → Fin (2 * ℓ))
    (hg : ∀ i c, st i = Sum.inr c → g i = c) :
    ∀ r : Fin (n + 1),
      ∃ (oᵣ : (chain r).Orientation) (T : List (α × α)) (tp : ℕ),
        PathCanonical oᵣ ∧
        (∀ p ∈ T, p.1 ≠ p.2) ∧
        pairFold T = statusDiff (chain 0) (chain r) ∧
        (tp + T.length + chordCrossingCount (chain 0) +
          chordCrossingCount (chain r)) % 2 = 0 ∧
        F.throughSummand hM (stateOddFlipSet st (pairFold T))
            (genBoundarySubsetMatches_stateOddFlipSet hbnd
              (pairFold T)) oᵣ (chain r).openCircuitCount =
          (((-1) ^ tp * flipSignProd g T : ℤ) : ℂ) *
            F.throughSummand hM st hbnd o₀
              (chain 0).openCircuitCount := by
  intro r
  induction r using Fin.induction with
  | zero =>
    refine ⟨o₀, [], 0, hc₀, ?_, ?_, ?_, ?_⟩
    · intro p hp
      cases hp
    · rw [pairFold_nil]
      exact (statusDiff_self _).symm
    · simp only [List.length_nil]
      omega
    · have h1 : (((-1 : ℤ)) ^ 0 * flipSignProd g [] : ℤ) = 1 := by
        rw [flipSignProd_nil]
        norm_num
      rw [pairFold_nil, h1, Int.cast_one, one_mul]
      exact F.throughSummand_state_congr hM stateOddFlipSet_empty
        (genBoundarySubsetMatches_stateOddFlipSet hbnd ∅) hbnd o₀
        (chain 0).openCircuitCount
  | succ r ih =>
    obtain ⟨oᵣ, T, tp, hcᵣ, hdT, hSD, hpar, hval⟩ := ih
    have hgr := flipColoursFold_matches hg hdT
    obtain ⟨o', T', tp', hc', hdT', hSD', hpar', hval'⟩ :=
      stepStatusLedger hM (stateOddFlipSet st (pairFold T))
        (genBoundarySubsetMatches_stateOddFlipSet hbnd
          (pairFold T)) (hstep r) hcᵣ (flipColoursFold g T) hgr
    refine ⟨o', T ++ T', tp + tp', hc', ?_, ?_, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with h | h
      · exact hdT p h
      · exact hdT' p h
    · rw [pairFold_append, hSD, hSD']
      exact statusDiff_trans _ _ _
    · rw [List.length_append]
      omega
    · have hstEq : stateOddFlipSet st (pairFold (T ++ T')) =
          stateOddFlipSet (stateOddFlipSet st (pairFold T))
            (pairFold T') := by
        rw [stateOddFlipSet_symmU, pairFold_append]
      have hb1 := genBoundarySubsetMatches_stateOddFlipSet
        (genBoundarySubsetMatches_stateOddFlipSet hbnd
          (pairFold T)) (pairFold T')
      have hb2 := genBoundarySubsetMatches_stateOddFlipSet hbnd
        (pairFold (T ++ T'))
      have hsign : (((-1) ^ (tp + tp') *
          flipSignProd g (T ++ T') : ℤ) : ℂ) =
          (((-1) ^ tp' * flipSignProd (flipColoursFold g T) T' :
            ℤ) : ℂ) *
            (((-1) ^ tp * flipSignProd g T : ℤ) : ℂ) := by
        rw [flipSignProd_append, pow_add]
        push_cast
        ring
      calc F.throughSummand hM
            (stateOddFlipSet st (pairFold (T ++ T'))) hb2 o'
            (chain r.succ).openCircuitCount
          = F.throughSummand hM
              (stateOddFlipSet (stateOddFlipSet st (pairFold T))
                (pairFold T')) hb1 o'
              (chain r.succ).openCircuitCount :=
            F.throughSummand_state_congr hM hstEq hb2 hb1 o' _
        _ = (((-1) ^ tp' *
              flipSignProd (flipColoursFold g T) T' : ℤ) : ℂ) *
            F.throughSummand hM
              (stateOddFlipSet st (pairFold T))
              (genBoundarySubsetMatches_stateOddFlipSet hbnd
                (pairFold T)) oᵣ
              (chain r.castSucc).openCircuitCount := hval'
        _ = (((-1) ^ tp' *
              flipSignProd (flipColoursFold g T) T' : ℤ) : ℂ) *
            ((((-1) ^ tp * flipSignProd g T : ℤ) : ℂ) *
              F.throughSummand hM st hbnd o₀
                (chain 0).openCircuitCount) := by rw [hval]
        _ = (((-1) ^ (tp + tp') *
              flipSignProd g (T ++ T') : ℤ) : ℂ) *
            F.throughSummand hM st hbnd o₀
              (chain 0).openCircuitCount := by
            rw [hsign]
            ring

end StepLemma

end EdgeSubset

/-! ## The paired assembly -/

open EdgeSubset in
/-- **The paired step, unsigned form**: across any π-returning
repair block, a canonical frame carries to a canonical frame with
the *same* summand at the *same* state — the accumulated relabel is
the (empty) status difference of the endpoints, and the accumulated
sign telescopes to `+1` through the crossing-parity ledger. -/
theorem pairedLedgerUnsigned : PairedLedgerUnsigned := by
  intro α _ W F k ℓ hM st hbnd κ₁ κ₂ hps o₁ hc₁
  obtain ⟨⟨n, chain, h0, hlast, hstep⟩, hsp⟩ := hps
  have hsp0n : SamePairing (chain 0) (chain (Fin.last n)) :=
    ((samePairing_of_matchEq h0).trans hsp).trans
      (samePairing_of_matchEq hlast).symm
  have hcc0n : chordCrossingCount (chain 0) =
      chordCrossingCount (chain (Fin.last n)) :=
    chordCrossingCount_of_samePairing hsp0n
  obtain ⟨o₀, hc₀, hval₀⟩ := matchEq_canonical_transfer hM st hbnd
    (RelTransitionSystem.MatchEq.symm h0) hc₁
  by_cases hcol : Nonempty (Fin (2 * ℓ))
  · -- the colour function matching the state
    have hex : ∀ i : α, ∃ cc : Fin (2 * ℓ),
        ∀ c0, st i = Sum.inr c0 → cc = c0 := by
      intro i
      rcases hsi : st i with a | c0
      · obtain ⟨c₀⟩ := hcol
        refine ⟨c₀, fun c0 h => ?_⟩
        simp at h
      · refine ⟨c0, fun c0' h => ?_⟩
        exact Sum.inr.inj h
    choose g hgspec using hex
    have hg : ∀ i c0, st i = Sum.inr c0 → g i = c0 :=
      fun i c0 h => hgspec i c0 h
    obtain ⟨oₙ, T, tp, hcₙ, hdT, hSD, hpar, hval⟩ :=
      chainStatusLedger hM st hbnd chain hstep hc₀ g hg
        (Fin.last n)
    have hSDnil : pairFold T = ∅ := by
      rw [hSD]
      exact statusDiff_of_samePairing hsp0n
    have hodd : oddCountLabels T = ∅ := by
      rw [← pairFold_eq_oddCountLabels hdT]
      exact hSDnil
    have hprodT : flipSignProd g T = (-1) ^ T.length := by
      refine flipSignProd_of_even g T hdT fun a => ?_
      by_contra hne0
      have h2 : a ∈ oddCountLabels T :=
        mem_oddCountLabels.mpr (by omega)
      rw [hodd] at h2
      exact Finset.notMem_empty a h2
    have hsign1 : (((-1) ^ tp * flipSignProd g T : ℤ) : ℂ) =
        1 := by
      obtain ⟨m, hm⟩ : ∃ m, tp + T.length = 2 * m :=
        ⟨(tp + T.length) / 2, by omega⟩
      rw [hprodT, ← pow_add, hm, pow_mul]
      norm_num
    rw [hSDnil] at hval
    have hstid := F.throughSummand_state_congr hM
      stateOddFlipSet_empty
      (genBoundarySubsetMatches_stateOddFlipSet hbnd ∅) hbnd oₙ
      (chain (Fin.last n)).openCircuitCount
    obtain ⟨o₂, hc₂, hval₂⟩ := matchEq_canonical_transfer hM st
      hbnd hlast hcₙ
    refine ⟨o₂, hc₂, ?_⟩
    rw [hval₂, ← hstid, hval, hsign1, one_mul, hval₀]
  · -- degenerate: no odd colours, hence no boundary flags and
    -- every step is match-preserving
    have hbf : F.boundaryFlags = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun β hβ => ?_
      obtain ⟨i, hi⟩ := F.attach_boundary_of_mem hβ
      have hflag : W.boundaryFlag i ∈ F.flags := by
        rw [← W.eq_boundaryFlag i β hi]
        exact mem_flags_of_boundaryFlags F hβ
      obtain ⟨cc, -⟩ := (hbnd i).mp hflag
      exact hcol ⟨cc⟩
    have hmp : ∀ r : Fin n,
        MatchPreservingStep (chain r.castSucc) (chain r.succ) := by
      intro r
      obtain ⟨a, b, c, d, v, hsq, heq⟩ := hstep r
      by_cases hl : SquareLocalized (chain r.castSucc) a b c d
      · exact ⟨a, b, c, d, v, hsq,
          RelTransitionSystem.MatchEq.symm heq,
          pathMatch_repair_of_localized hsq hl⟩
      · exfalso
        obtain ⟨β₁, β₂, hβ₁, hβ₂, -, -, -, -⟩ :=
          twoChains_of_not_localized hsq hl
        rw [hbf] at hβ₁
        exact Finset.notMem_empty β₁ hβ₁
    have hcarry : ∀ r : Fin (n + 1),
        ∃ oᵣ : (chain r).Orientation, PathCanonical oᵣ ∧
        pathSign (chain r) *
            F.throughSummand hM st hbnd oᵣ
              (chain r).openCircuitCount =
          pathSign (chain 0) *
            F.throughSummand hM st hbnd o₀
              (chain 0).openCircuitCount := by
      intro r
      induction r using Fin.induction with
      | zero => exact ⟨o₀, hc₀, rfl⟩
      | succ r ih =>
        obtain ⟨oᵣ, hcᵣ, hvᵣ⟩ := ih
        obtain ⟨o', hc', hv'⟩ := stepLedger_single hM st hbnd _ _
          (hmp r) oᵣ hcᵣ
        exact ⟨o', hc', hv'.trans hvᵣ⟩
    obtain ⟨oₙ, hcₙ, hvₙ⟩ := hcarry (Fin.last n)
    have hps0 : pathSign (chain 0) =
        pathSign (chain (Fin.last n)) :=
      pathSign_of_samePairing hsp0n
    have hnz : pathSign (chain (Fin.last n)) ≠ 0 := by
      unfold pathSign
      exact pow_ne_zero _ (by norm_num)
    rw [hps0] at hvₙ
    have hveq : F.throughSummand hM st hbnd oₙ
        (chain (Fin.last n)).openCircuitCount =
        F.throughSummand hM st hbnd o₀
          (chain 0).openCircuitCount :=
      mul_left_cancel₀ hnz hvₙ
    obtain ⟨o₂, hc₂, hval₂⟩ := matchEq_canonical_transfer hM st
      hbnd hlast hcₙ
    exact ⟨o₂, hc₂, by rw [hval₂, hveq, hval₀]⟩

/-- **The paired step**: the last input of Proposition 3's
per-π well-definedness — across any π-returning repair block the
`pathSign`-weighted canonical summand is preserved. -/
theorem pairedLedger : EdgeSubset.PairedLedger :=
  EdgeSubset.pairedLedger_iff_unsigned.mpr pairedLedgerUnsigned

end RS
