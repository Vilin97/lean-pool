/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueRelTransport

/-!
# Circuit-count delta across a participating glued interface

`GlueRelTransport` proved `openCircuitCount` stability for the open
single-pair glue when the glued edge's flags do **not** participate
in the edge subset.  This file treats the participating case: the
lifted subset contains both boundary flags `bf_i, bf_j` of `W`,
which are boundary flags of the lifted edge subset, so the `W`-side
walks terminate there, while the glued walk continues through the
rewire.

## Main results

* `pairing_iterWalk_ne` — the master collision lemma: along any
  walk with internal pairings, `W.pairing (iterWalk κ b m)` never
  equals `iterWalk κ b l` (a parity argument on the alternating
  chain); specialised to `pathMatch_ne_self` (the path matching has
  no fixed points).
* `InterfaceLinked` — the two interface chains splice into a closed
  circuit: `pathMatch` of `bf_i` is `bf_j`.
* `openCircuitCount_linked_chain`,
  `openCircuitCount_glueOpen_participating` — the circuit-count
  delta: gluing adds exactly one circuit when the interface is
  linked and none otherwise.
-/

namespace RS

open scoped Classical

/-! ### Permutation counting helpers: `sumCongr` -/

section PermHelpers

open Equiv

variable {γ δ : Type}

/-- A rotation of length `k ≥ 1` contributes exactly one orbit:
one nontrivial cycle when `k ≥ 2`, one fixed point when `k = 1`. -/
theorem finRotate_orbit_count (k : ℕ) (hk : 1 ≤ k) :
    (finRotate k).cycleType.card +
      Fintype.card (Function.fixedPoints (finRotate k)) = 1 := by
  match k, hk with
  | 1, _ =>
    rw [finRotate_one]
    have h1 : (Equiv.refl (Fin 1)) = (1 : Perm (Fin 1)) := rfl
    rw [h1, Perm.cycleType_one]
    have hall : ∀ x : Fin 1,
        x ∈ Function.fixedPoints (⇑(1 : Perm (Fin 1))) :=
      fun x => rfl
    have hcard := Fintype.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [Fintype.card_fin] at hcard
    rw [hcard]
    simp
  | (n + 2), _ =>
    rw [cycleType_finRotate]
    have hempty :
        IsEmpty (Function.fixedPoints (finRotate (n + 2))) := by
      refine ⟨fun x => ?_⟩
      obtain ⟨x, hx⟩ := x
      have hx' : finRotate (n + 2) x = x := hx
      rw [finRotate_apply] at hx'
      have h1 : (1 : Fin (n + 2)) = 0 := by
        have := add_left_cancel (a := x) (b := (1 : Fin (n + 2)))
          (c := 0) (by rw [add_zero]; exact hx')
        exact this
      simp [] at h1
    rw [Fintype.card_eq_zero_iff.mpr hempty]
    simp

end PermHelpers

namespace EdgeSubset

variable {α : Type} {W : Fragment α}

/-! ### Generic walk lemmas -/

section GenericWalk

variable {F : EdgeSubset W}

/-- Splitting an iterated walk. -/
theorem iterWalk_add (κ : F.RelTransitionSystem) (f : W.Flag)
    (a b : ℕ) :
    iterWalk κ f (a + b) = iterWalk κ (iterWalk κ f a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from rfl, iterWalk_succ,
      ih, ← iterWalk_succ]

/-- Iterates of a periodic flag are periodic. -/
theorem periodicFlag_iterWalk (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : κ.PeriodicFlag f) (m : ℕ) :
    κ.PeriodicFlag (iterWalk κ f m) := by
  induction m with
  | zero => exact hf
  | succ m ih =>
    have h := RelTransitionSystem.periodicFlag_step ih
    rwa [← iterWalk_add κ f m 1] at h

/-- Reduce a walk index modulo a period. -/
theorem iterWalk_mod (κ : F.RelTransitionSystem) {f : W.Flag}
    {n : ℕ} (_ : 1 ≤ n)
    (hcont : ∀ t, t < n →
      W.pairing (iterWalk κ f t) ∈ F.internalFlags)
    (hper : iterWalk κ f n = f) (a : ℕ) :
    iterWalk κ f a = iterWalk κ f (a % n) := by
  have hmod : ∀ q r, iterWalk κ f (n * q + r) = iterWalk κ f r := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show n * (q + 1) + r = n + (n * q + r) from by ring,
        iterWalk_add_period κ f n (n * q + r) hper hcont]
      exact ih r
  conv_lhs =>
    rw [show a = n * (a / n) + a % n from (Nat.div_add_mod a n).symm]
  exact hmod (a / n) (a % n)

/-- **Master collision lemma**: along a walk whose pairings up to
step `k` are internal, the pairing of an iterate never equals an
iterate (parity argument on the alternating chain: a collision
would force a fixed point of the edge pairing or of the
matching). -/
theorem pairing_iterWalk_ne (κ : F.RelTransitionSystem)
    {b : W.Flag} {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags)
    {m l : ℕ} (hm : m ≤ k) (hl : l ≤ k) :
    W.pairing (iterWalk κ b m) ≠ iterWalk κ b l := by
  have haux : ∀ d m l, l - m = d → m ≤ l → l ≤ k →
      W.pairing (iterWalk κ b m) = iterWalk κ b l → False := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro m l hd hml hlk heq
      rcases d with _ | (_ | d)
      · -- m = l: a fixed point of the edge pairing
        have hml' : m = l := by omega
        subst hml'
        exact W.pairing_ne _ heq
      · -- l = m + 1: a fixed point of the matching
        have hlm : l = m + 1 := by omega
        subst hlm
        rw [iterWalk_succ] at heq
        exact κ.match_ne _ (hcont m (by omega)) heq.symm
      · -- propagate the collision inward
        obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        have hstep : iterWalk κ b (m + 1) =
            W.pairing (iterWalk κ b l') := by
          rw [iterWalk_succ, heq, iterWalk_succ,
            κ.match_invol _ (hcont l' (by omega))]
        have heq' : W.pairing (iterWalk κ b (m + 1)) =
            iterWalk κ b l' := by
          rw [hstep, W.pairing_invol]
        exact ih d (by omega) (m + 1) l' (by omega)
          (by omega) (by omega) heq'
  intro heq
  rcases Nat.le_total m l with h | h
  · exact haux (l - m) m l rfl h hl heq
  · have heq' : W.pairing (iterWalk κ b l) = iterWalk κ b m := by
      rw [← heq, W.pairing_invol]
    exact haux (m - l) l m rfl h hm heq'

/-- The path matching has no fixed points. -/
theorem RelTransitionSystem.pathMatch_ne_self
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags) :
    κ.pathMatch b hb ≠ b := by
  obtain ⟨k, _, hcont, hpm⟩ := pathMatch_chain_length κ hb
  rw [hpm]
  intro h
  exact pairing_iterWalk_ne κ hcont le_rfl (Nat.zero_le k)
    (h.trans (iterWalk_zero κ b).symm)

/-- Congruence for `pathMatch` in its base point. -/
theorem RelTransitionSystem.pathMatch_congr
    (κ : F.RelTransitionSystem) {b b' : W.Flag} (h : b = b')
    (hb : b ∈ F.boundaryFlags) (hb' : b' ∈ F.boundaryFlags) :
    κ.pathMatch b hb = κ.pathMatch b' hb' := by
  subst h; rfl

/-- Flags strictly inside a boundary-terminated chain segment are
not periodic. -/
theorem not_periodic_of_chain_segment (κ : F.RelTransitionSystem)
    {b : W.Flag} {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ b k) ∈ F.boundaryFlags)
    {m : ℕ} (hm1 : 1 ≤ m) (hmk : m ≤ k) :
    ¬ κ.PeriodicFlag (iterWalk κ b m) := by
  apply not_periodic_of_boundary_chain κ _
    (iterWalk_mem_internal κ k hm1 hmk hcont)
  refine ⟨(k - m) + 1,
    W.pairing (iterWalk κ (iterWalk κ b m) (k - m)), ?_⟩
  apply traceChain_forward κ (iterWalk κ b m) (k := k - m)
  · intro t ht
    rw [← iterWalk_add]
    exact hcont (m + t) (by omega)
  · rw [← iterWalk_add, show m + (k - m) = k from by omega]
    exact hterm

end GenericWalk

/-! ### The participating open glue -/

open Fragment

variable {i j : α}

section OpenGlueParticipating

variable (hij : i ≠ j)
  (hopen : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j)
  (s' : Finset (SurvivingFlag W i j))
  (hc' : ∀ f ∈ s', (W.gluePairOpen i j hij hopen).pairing f ∈ s')
  (hc : ∀ f ∈ liftSubsetOpen hopen s',
    W.pairing f ∈ liftSubsetOpen hopen s')

/-- The glued edge subset. -/
local notation "Fg" =>
  (EdgeSubset.mk s' hc' : EdgeSubset (W.gluePairOpen i j hij hopen))

/-- The lifted edge subset. -/
local notation "Fl" =>
  (EdgeSubset.mk (liftSubsetOpen hopen s') hc : EdgeSubset W)

include hc' hc

/-! #### Interface membership -/

omit hc in
include hij in
/-- Participation propagates to the far end of the `j`-edge. -/
theorem partnerSurvJ_mem_of_mem (hpi : partnerSurvI hopen ∈ s') :
    partnerSurvJ hopen ∈ s' := by
  have h := hc' _ hpi
  rwa [gluePairOpen_pairing_interface_i hij hopen _ (by
    rw [partnerSurvI_val hopen, W.pairing_invol])] at h

omit hc' in
include hij in
/-- With participation, `bf_i` is a boundary flag of the lift. -/
theorem boundaryFlagI_mem_boundaryFlags (hpi : partnerSurvI hopen ∈ s') :
    W.boundaryFlag i ∈ (Fl).boundaryFlags := by
  have hmem : W.boundaryFlag i ∈ liftSubsetOpen hopen s' :=
    (boundaryFlagI_mem_liftOpen_iff hij hopen s').mpr hpi
  rcases mem_internalFlags_or_boundaryFlags (Fl) hmem with hint | hbd
  · obtain ⟨v, hv⟩ := attach_internal_of_mem _ hint
    rw [W.attach_boundaryFlag i] at hv
    cases hv
  · exact hbd

/-- With participation, `bf_j` is a boundary flag of the lift. -/
theorem boundaryFlagJ_mem_boundaryFlags (hpi : partnerSurvI hopen ∈ s') :
    W.boundaryFlag j ∈ (Fl).boundaryFlags := by
  have hmem : W.boundaryFlag j ∈ liftSubsetOpen hopen s' :=
    (boundaryFlagJ_mem_liftOpen_iff hij hopen s').mpr
      (partnerSurvJ_mem_of_mem hij hopen s' hc' hpi)
  rcases mem_internalFlags_or_boundaryFlags (Fl) hmem with hint | hbd
  · obtain ⟨v, hv⟩ := attach_internal_of_mem _ hint
    rw [W.attach_boundaryFlag j] at hv
    cases hv
  · exact hbd

/-! #### Walk correspondence -/

/-- Walk correspondence from glued-side interface avoidance. -/
theorem iterWalk_val_of_glued_avoids
    (κ' : (Fg).RelTransitionSystem) (g : SurvivingFlag W i j)
    (n : ℕ)
    (hav : ∀ t, t < n →
      iterWalk κ' g t ≠ partnerSurvI hopen ∧
        iterWalk κ' g t ≠ partnerSurvJ hopen) :
    ∀ m, m ≤ n →
      iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ') g.val m = (iterWalk κ' g m).val := by
  intro m
  induction m with
  | zero => exact fun _ => rfl
  | succ m ih =>
    intro hm
    have hval := ih (by omega)
    obtain ⟨havI, havJ⟩ := hav m (by omega)
    have h1 : W.pairing (iterWalk κ' g m).val ≠ W.boundaryFlag i :=
      fun hh => havI (eq_partnerSurvI_of_pairing hopen _ hh)
    have h2 : W.pairing (iterWalk κ' g m).val ≠ W.boundaryFlag j :=
      fun hh => havJ (eq_partnerSurvJ_of_pairing hopen _ hh)
    show (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').match_ (W.pairing (iterWalk
          (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
          g.val m)) =
      (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' g m))).val
    rw [hval]
    have hag : W.pairing (iterWalk κ' g m).val =
        ((W.gluePairOpen i j hij hopen).pairing
          (iterWalk κ' g m)).val :=
      (gluePairOpen_pairing_val_of_ne hij hopen _ h1 h2).symm
    rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
      ((W.gluePairOpen i j hij hopen).pairing (iterWalk κ' g m))]

/-- Walk correspondence from lifted-side internality data. -/
theorem iterWalk_val_of_internal
    (κ' : (Fg).RelTransitionSystem) (g : SurvivingFlag W i j)
    (n : ℕ)
    (hcontW : ∀ t, t < n →
      W.pairing (iterWalk (RelTransitionSystem.unglueOpen hij hopen
        s' hc' hc κ') g.val t) ∈ (Fl).internalFlags) :
    ∀ m, m ≤ n →
      iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ') g.val m = (iterWalk κ' g m).val := by
  intro m
  induction m with
  | zero => exact fun _ => rfl
  | succ m ih =>
    intro hm
    have hval := ih (by omega)
    have hp := hcontW m (by omega)
    rw [hval] at hp
    obtain ⟨h1, h2⟩ := internal_surviving i j hp
    show (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').match_ (W.pairing (iterWalk
          (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
          g.val m)) =
      (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' g m))).val
    rw [hval]
    have hag : W.pairing (iterWalk κ' g m).val =
        ((W.gluePairOpen i j hij hopen).pairing
          (iterWalk κ' g m)).val :=
      (gluePairOpen_pairing_val_of_ne hij hopen _ h1 h2).symm
    rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
      ((W.gluePairOpen i j hij hopen).pairing (iterWalk κ' g m))]

/-- Under lifted-side internality, the glued pairings along the
walk are internal. -/
theorem gluedPairing_internal_of_internal
    (κ' : (Fg).RelTransitionSystem) (g : SurvivingFlag W i j)
    (n : ℕ)
    (hcontW : ∀ t, t < n →
      W.pairing (iterWalk (RelTransitionSystem.unglueOpen hij hopen
        s' hc' hc κ') g.val t) ∈ (Fl).internalFlags) :
    ∀ m, m < n → (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' g m) ∈ (Fg).internalFlags := by
  intro m hm
  have hp := hcontW m hm
  rw [iterWalk_val_of_internal hij hopen s' hc' hc κ' g n hcontW m
    (le_of_lt hm)] at hp
  obtain ⟨h1, h2⟩ := internal_surviving i j hp
  have hrw : (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' g m) =
      (⟨W.pairing (iterWalk κ' g m).val, h1, h2⟩ :
        SurvivingFlag W i j) :=
    Subtype.ext (gluePairOpen_pairing_val_of_ne hij hopen _ h1 h2)
  rw [hrw]
  exact internal_mk_of_glueOpen hij hopen s' hc' hc hp h1 h2

/-! #### Periodic-flag transport -/

/-- Periodic flags lift backward along the unglue transport
(participating case: internality of the lifted-side pairings keeps
the walk away from the interface). -/
theorem mem_periodicFlags_glued_of_val
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g.val ∈ (RelTransitionSystem.unglueOpen hij hopen s' hc'
      hc κ').periodicFlags) :
    g ∈ κ'.periodicFlags := by
  obtain ⟨hint, n, hn1, hcontW, hper⟩ :=
    ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').mem_periodicFlags).mp hg
  refine (κ'.mem_periodicFlags).mpr
    ⟨(mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr hint,
     n, hn1, ?_, ?_⟩
  · intro m hm
    exact gluedPairing_internal_of_internal hij hopen s' hc' hc κ'
      g n hcontW m hm
  · refine Subtype.ext ?_
    rw [← iterWalk_val_of_internal hij hopen s' hc' hc κ' g n
      hcontW n le_rfl]
    exact hper

/-- Classification of glued periodic flags: either the value is
periodic on the lifted side, or the flag lies on the orbit of one
of the two interface far ends. -/
theorem periodicFlag_val_or_orbit
    (κ' : (Fg).RelTransitionSystem) {g : SurvivingFlag W i j}
    (hg : g ∈ κ'.periodicFlags) :
    g.val ∈ (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').periodicFlags ∨
      ((κ'.PeriodicFlag (partnerSurvI hopen) ∧
        ∃ c, iterWalk κ' (partnerSurvI hopen) c = g) ∨
       (κ'.PeriodicFlag (partnerSurvJ hopen) ∧
        ∃ c, iterWalk κ' (partnerSurvJ hopen) c = g)) := by
  obtain ⟨hint, n, hn1, hcont', hper⟩ := (κ'.mem_periodicFlags).mp hg
  have hgper' : κ'.PeriodicFlag g := ⟨hint, n, hn1, hcont', hper⟩
  by_cases hhit : ∃ m, m < n ∧
      (iterWalk κ' g m = partnerSurvI hopen ∨
        iterWalk κ' g m = partnerSurvJ hopen)
  · obtain ⟨m, hm, hor⟩ := hhit
    right
    have hback : iterWalk κ' (iterWalk κ' g m) (n - m) = g := by
      have h := iterWalk_add κ' g m (n - m)
      rw [show m + (n - m) = n from by omega, hper] at h
      exact h.symm
    have hperm := periodicFlag_iterWalk κ' hgper' m
    rcases hor with h | h
    · rw [h] at hback hperm
      exact Or.inl ⟨hperm, n - m, hback⟩
    · rw [h] at hback hperm
      exact Or.inr ⟨hperm, n - m, hback⟩
  · left
    have hav : ∀ t, t < n →
        iterWalk κ' g t ≠ partnerSurvI hopen ∧
          iterWalk κ' g t ≠ partnerSurvJ hopen := by
      intro t ht
      exact ⟨fun h => hhit ⟨t, ht, Or.inl h⟩,
        fun h => hhit ⟨t, ht, Or.inr h⟩⟩
    have hcorr := iterWalk_val_of_glued_avoids hij hopen s' hc' hc
      κ' g n hav
    refine ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').mem_periodicFlags).mpr
      ⟨(mem_internalFlags_glueOpen hij hopen s' hc' hc).mp hint,
       n, hn1, ?_, ?_⟩
    · intro m hm
      rw [hcorr m (le_of_lt hm)]
      obtain ⟨havI, havJ⟩ := hav m hm
      have h1 : W.pairing (iterWalk κ' g m).val ≠
          W.boundaryFlag i :=
        fun hh => havI (eq_partnerSurvI_of_pairing hopen _ hh)
      have h2 : W.pairing (iterWalk κ' g m).val ≠
          W.boundaryFlag j :=
        fun hh => havJ (eq_partnerSurvJ_of_pairing hopen _ hh)
      have hag : W.pairing (iterWalk κ' g m).val =
          ((W.gluePairOpen i j hij hopen).pairing
            (iterWalk κ' g m)).val :=
        (gluePairOpen_pairing_val_of_ne hij hopen _ h1 h2).symm
      rw [hag]
      exact (mem_internalFlags_glueOpen hij hopen s' hc' hc).mp
        (hcont' m hm)
    · rw [hcorr n le_rfl]
      exact congrArg Subtype.val hper

/-! #### Exit forced to the interface -/

/-- If the glued walk entering the chain of a boundary flag `b`
has all its pairings internal, the `W`-side chain from `b` must
exit at the glued interface. -/
theorem pathMatch_mem_interface_of_glued_internal
    (κ' : (Fg).RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ (Fl).boundaryFlags)
    (h1 : W.pairing b ≠ W.boundaryFlag i)
    (h2 : W.pairing b ≠ W.boundaryFlag j)
    (h0 : (⟨W.pairing b, h1, h2⟩ : SurvivingFlag W i j) ∈
      (Fg).internalFlags)
    (hz : ∀ t, (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' (κ'.match_ ⟨W.pairing b, h1, h2⟩) t) ∈
        (Fg).internalFlags) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').pathMatch b hb = W.boundaryFlag i ∨
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').pathMatch b hb = W.boundaryFlag j := by
  set κW := RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ'
    with hκW
  obtain ⟨k, hk_le, hcont, hpm⟩ := pathMatch_chain_length κW hb
  have hpmb : W.pairing (iterWalk κW b k) ∈ (Fl).boundaryFlags := by
    rw [← hpm]
    exact κW.pathMatch_mem hb
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · -- k = 0: the partner of b would be both internal and boundary
    rw [iterWalk_zero] at hpmb
    have hintFl : W.pairing b ∈ (Fl).internalFlags :=
      (mem_internalFlags_glueOpen hij hopen s' hc' hc).mp h0
    exact absurd hpmb
      (Finset.disjoint_left.mp
        ((Fl).internalFlags_disjoint_boundaryFlags) hintFl)
  · by_cases hne1 : κW.pathMatch b hb = W.boundaryFlag i
    · exact Or.inl hne1
    by_cases hne2 : κW.pathMatch b hb = W.boundaryFlag j
    · exact Or.inr hne2
    exfalso
    rw [hpm] at hne1 hne2
    -- track the chain through the glued walk up to the exit
    have hzval : (κ'.match_ (⟨W.pairing b, h1, h2⟩ :
        SurvivingFlag W i j)).val = κW.match_ (W.pairing b) :=
      (unglueOpen_match_val hij hopen s' hc' hc κ'
        ⟨W.pairing b, h1, h2⟩).symm
    have hzwalk : ∀ t, iterWalk κW
        (κ'.match_ (⟨W.pairing b, h1, h2⟩ :
          SurvivingFlag W i j)).val t = iterWalk κW b (t + 1) := by
      intro t
      rw [hzval]
      exact iterWalk_shift κW b t
    have hcontW : ∀ t, t < k - 1 →
        W.pairing (iterWalk κW
          (κ'.match_ (⟨W.pairing b, h1, h2⟩ :
            SurvivingFlag W i j)).val t) ∈ (Fl).internalFlags := by
      intro t ht
      rw [hzwalk t]
      exact hcont (t + 1) (by omega)
    have hyval : (iterWalk κ'
        (κ'.match_ (⟨W.pairing b, h1, h2⟩ : SurvivingFlag W i j))
        (k - 1)).val = iterWalk κW b k := by
      rw [← iterWalk_val_of_internal hij hopen s' hc' hc κ' _
        (k - 1) hcontW (k - 1) le_rfl, hzwalk,
        show k - 1 + 1 = k from by omega]
    have hexit1 : W.pairing (iterWalk κ'
        (κ'.match_ (⟨W.pairing b, h1, h2⟩ : SurvivingFlag W i j))
        (k - 1)).val ≠ W.boundaryFlag i := by
      rw [hyval]; exact hne1
    have hexit2 : W.pairing (iterWalk κ'
        (κ'.match_ (⟨W.pairing b, h1, h2⟩ : SurvivingFlag W i j))
        (k - 1)).val ≠ W.boundaryFlag j := by
      rw [hyval]; exact hne2
    have hyint := hz (k - 1)
    have hagy : ((W.gluePairOpen i j hij hopen).pairing
        (iterWalk κ' (κ'.match_ (⟨W.pairing b, h1, h2⟩ :
          SurvivingFlag W i j)) (k - 1))).val =
        W.pairing (iterWalk κW b k) := by
      rw [gluePairOpen_pairing_val_of_ne hij hopen _ hexit1 hexit2,
        hyval]
    have hintFl : W.pairing (iterWalk κW b k) ∈
        (Fl).internalFlags := by
      rw [← hagy]
      exact (mem_internalFlags_glueOpen hij hopen s' hc' hc).mp
        hyint
    exact Finset.disjoint_left.mp
      ((Fl).internalFlags_disjoint_boundaryFlags) hintFl hpmb

/-! #### The link condition -/

/-- **The interface link condition**: the `W`-side chain from
`bf_i` (under the unglued transition data) exits at `bf_j`.  When
it holds, gluing splices the two interface chains into one new
closed circuit; otherwise it concatenates two boundary paths. -/
def InterfaceLinked (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s') : Prop :=
  (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ').pathMatch
    (W.boundaryFlag i)
    (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi) =
    W.boundaryFlag j

/-- **Feed-forward form of the link condition**: it is literally
the `pathMatch` pairing of the two interface boundary flags. -/
theorem interfaceLinked_iff_pathMatch (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s') :
    InterfaceLinked hij hopen s' hc' hc κ' hpi ↔
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').pathMatch (W.boundaryFlag i)
        (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi) =
        W.boundaryFlag j :=
  Iff.rfl

/-- If the far end of the `i`-edge is periodic in the glued
system, the interface is linked. -/
theorem interfaceLinked_of_periodicI (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hper : κ'.PeriodicFlag (partnerSurvI hopen)) :
    InterfaceLinked hij hopen s' hc' hc κ' hpi := by
  have hbj := boundaryFlagJ_mem_boundaryFlags hij hopen s' hc' hc
    hpi
  have h1 : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag i :=
    fun h => hopen (W.pairing_boundaryFlag_comm h)
  have h2 : W.pairing (W.boundaryFlag j) ≠ W.boundaryFlag j :=
    W.pairing_ne _
  have hmk : (⟨W.pairing (W.boundaryFlag j), h1, h2⟩ :
      SurvivingFlag W i j) = partnerSurvJ hopen := rfl
  have hrw : (W.gluePairOpen i j hij hopen).pairing
      (partnerSurvI hopen) = partnerSurvJ hopen :=
    gluePairOpen_pairing_interface_i hij hopen _
      (by rw [partnerSurvI_val hopen, W.pairing_invol])
  have h0 : (⟨W.pairing (W.boundaryFlag j), h1, h2⟩ :
      SurvivingFlag W i j) ∈ (Fg).internalFlags := by
    rw [hmk]
    have h := all_pairings_internal_of_periodic κ' hper 0
    have h' : (W.gluePairOpen i j hij hopen).pairing
        (partnerSurvI hopen) ∈ (Fg).internalFlags := h
    rw [hrw] at h'
    exact h'
  have hz : ∀ t, (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' (κ'.match_
        ⟨W.pairing (W.boundaryFlag j), h1, h2⟩) t) ∈
        (Fg).internalFlags := by
    intro t
    have hshift := iterWalk_shift κ' (partnerSurvI hopen) t
    rw [hrw] at hshift
    rw [hmk, hshift]
    exact all_pairings_internal_of_periodic κ' hper (t + 1)
  rcases pathMatch_mem_interface_of_glued_internal hij hopen s'
    hc' hc κ' hbj h1 h2 h0 hz with h | h
  · unfold InterfaceLinked
    calc (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').pathMatch (W.boundaryFlag i)
          (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi)
        = (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
            κ').pathMatch
            ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
              κ').pathMatch (W.boundaryFlag j) hbj)
            ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
              κ').pathMatch_mem hbj) :=
          RelTransitionSystem.pathMatch_congr _ h.symm _ _
      _ = W.boundaryFlag j :=
          (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
            κ').pathMatch_invol hbj
  · exact absurd h
      ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').pathMatch_ne_self hbj)

/-- If the far end of the `j`-edge is periodic in the glued
system, the interface is linked. -/
theorem interfaceLinked_of_periodicJ (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hper : κ'.PeriodicFlag (partnerSurvJ hopen)) :
    InterfaceLinked hij hopen s' hc' hc κ' hpi := by
  have hbi := boundaryFlagI_mem_boundaryFlags hij hopen s' hc
    hpi
  have h1 : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag i :=
    W.pairing_ne _
  have h2 : W.pairing (W.boundaryFlag i) ≠ W.boundaryFlag j :=
    hopen
  have hmk : (⟨W.pairing (W.boundaryFlag i), h1, h2⟩ :
      SurvivingFlag W i j) = partnerSurvI hopen := rfl
  have hrw : (W.gluePairOpen i j hij hopen).pairing
      (partnerSurvJ hopen) = partnerSurvI hopen :=
    gluePairOpen_pairing_interface_j hij hopen _
      (by
        rw [partnerSurvJ_val hopen, W.pairing_invol]
        exact fun hh => hij (W.boundaryFlag_injective hh).symm)
      (by rw [partnerSurvJ_val hopen, W.pairing_invol])
  have h0 : (⟨W.pairing (W.boundaryFlag i), h1, h2⟩ :
      SurvivingFlag W i j) ∈ (Fg).internalFlags := by
    rw [hmk]
    have h := all_pairings_internal_of_periodic κ' hper 0
    have h' : (W.gluePairOpen i j hij hopen).pairing
        (partnerSurvJ hopen) ∈ (Fg).internalFlags := h
    rw [hrw] at h'
    exact h'
  have hz : ∀ t, (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' (κ'.match_
        ⟨W.pairing (W.boundaryFlag i), h1, h2⟩) t) ∈
        (Fg).internalFlags := by
    intro t
    have hshift := iterWalk_shift κ' (partnerSurvJ hopen) t
    rw [hrw] at hshift
    rw [hmk, hshift]
    exact all_pairings_internal_of_periodic κ' hper (t + 1)
  rcases pathMatch_mem_interface_of_glued_internal hij hopen s'
    hc' hc κ' hbi h1 h2 h0 hz with h | h
  · exact absurd h
      ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').pathMatch_ne_self hbi)
  · exact h

/-! #### The unlinked case: counts agree -/

/-- The periodic-flag bijection in the unlinked participating
case. -/
noncomputable def periodicEquivNotLinked (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hnl : ¬ InterfaceLinked hij hopen s' hc' hc κ' hpi) :
    {f : W.Flag // f ∈ (RelTransitionSystem.unglueOpen hij hopen
      s' hc' hc κ').periodicFlags} ≃
      {g : (W.gluePairOpen i j hij hopen).Flag //
        g ∈ κ'.periodicFlags} where
  toFun f := ⟨(⟨f.val,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).1,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).2⟩ :
        SurvivingFlag W i j),
    mem_periodicFlags_glued_of_val hij hopen s' hc' hc κ' f.prop⟩
  invFun g := ⟨g.val.val, by
    rcases periodicFlag_val_or_orbit hij hopen s' hc' hc κ' g.prop
      with h | (⟨hperI, _⟩ | ⟨hperJ, _⟩)
    · exact h
    · exact absurd (interfaceLinked_of_periodicI hij hopen s' hc'
        hc κ' hpi hperI) hnl
    · exact absurd (interfaceLinked_of_periodicJ hij hopen s' hc'
        hc κ' hpi hperJ) hnl⟩
  left_inv _f := Subtype.ext rfl
  right_inv _g := Subtype.ext (Subtype.ext rfl)

/-- The walk permutations agree under the bijection (unlinked
case). -/
theorem walkPermPeriodic_notLinked (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hnl : ¬ InterfaceLinked hij hopen s' hc' hc κ' hpi) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').walkPermPeriodic =
      (periodicEquivNotLinked hij hopen s' hc' hc κ' hpi
        hnl).symm.permCongr κ'.walkPermPeriodic := by
  apply Equiv.ext
  rintro ⟨f, hf⟩
  obtain ⟨h1, h2⟩ := internal_surviving i j
    ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').periodicFlags_sub hf)
  apply Subtype.ext
  show (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').match_ (W.pairing f) =
    (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
      ⟨f, h1, h2⟩)).val
  have hpf := all_pairings_internal_of_periodic
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
    (((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').mem_periodicFlags).mp hf) 0
  rw [iterWalk_zero] at hpf
  obtain ⟨hp1, hp2⟩ := internal_surviving i j hpf
  have hag : W.pairing f =
      ((W.gluePairOpen i j hij hopen).pairing ⟨f, h1, h2⟩).val :=
    (gluePairOpen_pairing_val_of_ne hij hopen ⟨f, h1, h2⟩ hp1
      hp2).symm
  rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
    ((W.gluePairOpen i j hij hopen).pairing ⟨f, h1, h2⟩)]

/-- **Count stability in the unlinked case.** -/
theorem openCircuitCount_notLinked (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s')
    (hnl : ¬ InterfaceLinked hij hopen s' hc' hc κ' hpi) :
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ').openCircuitCount = κ'.openCircuitCount := by
  unfold RelTransitionSystem.openCircuitCount
  rw [walkPermPeriodic_notLinked hij hopen s' hc' hc κ' hpi hnl,
    cycleType_permCongr, card_fixedPoints_permCongr]

/-! #### The spliced interface cycle -/

section SpliceSide

variable (κ' : (EdgeSubset.mk s' hc' :
    EdgeSubset (W.gluePairOpen i j hij hopen)).RelTransitionSystem)
  (x y : SurvivingFlag W i j) (b bo : W.Flag)
  (hb : b ∈ (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W).boundaryFlags)
  (hbo : bo ∈ (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
    EdgeSubset W).boundaryFlags)
  (hxb : x.val = W.pairing b) (hyo : y.val = W.pairing bo)
  (hryx : (W.gluePairOpen i j hij hopen).pairing y = x)
  (k : ℕ) (hk1 : 1 ≤ k)
  (hcont : ∀ t, t < k → W.pairing (iterWalk
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') b t) ∈
      (EdgeSubset.mk (liftSubsetOpen hopen s') hc :
        EdgeSubset W).internalFlags)
  (hterm : W.pairing (iterWalk
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') b k) =
      bo)

include hb hbo hxb hyo hryx hk1 hcont hterm

omit hb hbo hyo hryx hterm in
/-- The near end of the entry edge is internal in the glued
subset. -/
theorem splice_x_internal : x ∈ (Fg).internalFlags := by
  refine (mem_internalFlags_glueOpen hij hopen s' hc' hc).mpr ?_
  rw [hxb]
  exact hcont 0 (by omega)

omit hb hbo hyo hryx hk1 hcont hterm in
/-- The entry value of the spliced walk. -/
theorem splice_entry_val : (κ'.match_ x).val =
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ').match_
      (W.pairing b) := by
  rw [← hxb]
  exact (unglueOpen_match_val hij hopen s' hc' hc κ' x).symm

omit hb hbo hyo hryx hk1 hcont hterm in
/-- The lifted walk from the entry point is the shifted chain. -/
theorem splice_walk_valW : ∀ t,
    iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ') (κ'.match_ x).val t =
    iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
      κ') b (t + 1) := by
  intro t
  rw [splice_entry_val hij hopen s' hc' hc κ' x b hxb]
  exact iterWalk_shift
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') b t

omit hb hbo hyo hryx hk1 hterm in
/-- The lifted pairings along the shifted chain stay internal. -/
theorem splice_contW : ∀ t, t < k - 1 →
    W.pairing (iterWalk (RelTransitionSystem.unglueOpen hij hopen
      s' hc' hc κ') (κ'.match_ x).val t) ∈ (Fl).internalFlags := by
  intro t ht
  rw [splice_walk_valW hij hopen s' hc' hc κ' x b hxb t]
  exact hcont (t + 1) (by omega)

omit hb hbo hyo hryx hterm in
/-- **Cycle values**: the glued walk from the entry point follows
the `W`-side chain from `b`. -/
theorem splice_walk_val : ∀ t, t < k →
    (iterWalk κ' (κ'.match_ x) t).val =
      iterWalk (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ') b (t + 1) := by
  intro t ht
  rw [← iterWalk_val_of_internal hij hopen s' hc' hc κ'
    (κ'.match_ x) (k - 1)
    (splice_contW hij hopen s' hc' hc κ' x b hxb k hcont) t (by omega),
    splice_walk_valW hij hopen s' hc' hc κ' x b hxb t]

omit hb hbo hryx in
/-- **Exit flag**: at step `k - 1` the glued walk sits at the far
end of the exit edge. -/
theorem splice_last : iterWalk κ' (κ'.match_ x) (k - 1) = y := by
  refine Subtype.ext ?_
  rw [splice_walk_val hij hopen s' hc' hc κ' x b hxb k hk1 hcont (k - 1) (by
    omega),
    show k - 1 + 1 = k from by omega, hyo]
  have h := congrArg W.pairing hterm
  rwa [W.pairing_invol] at h

omit hb hbo in
/-- **The wrap**: the glued walk closes up with period `k`. -/
theorem splice_period : iterWalk κ' (κ'.match_ x) k = κ'.match_ x
    := by
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  show κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
    (iterWalk κ' (κ'.match_ x) k0)) = κ'.match_ x
  have hlast := splice_last hij hopen s' hc' hc κ' x y b bo
    hxb hyo (k0 + 1) hk1 hcont hterm
  rw [show (k0 + 1) - 1 = k0 from rfl] at hlast
  rw [hlast, hryx]

omit hb hbo in
/-- The glued pairings along the spliced cycle are internal. -/
theorem splice_pairing_internal : ∀ t, t < k →
    (W.gluePairOpen i j hij hopen).pairing
      (iterWalk κ' (κ'.match_ x) t) ∈ (Fg).internalFlags := by
  intro t ht
  rcases Nat.lt_or_ge t (k - 1) with h | h
  · exact gluedPairing_internal_of_internal hij hopen s' hc' hc κ'
      (κ'.match_ x) (k - 1)
      (splice_contW hij hopen s' hc' hc κ' x b hxb k hcont) t h
  · have ht' : t = k - 1 := by omega
    subst ht'
    rw [splice_last hij hopen s' hc' hc κ' x y b bo hxb hyo
      k hk1 hcont hterm, hryx]
    exact splice_x_internal hij hopen s' hc' hc κ' x b
      hxb k hk1 hcont

omit hb hbo in
/-- **The spliced cycle is periodic** in the glued system. -/
theorem splice_periodicFlag : κ'.PeriodicFlag (κ'.match_ x) :=
  ⟨κ'.match_mem x
    (splice_x_internal hij hopen s' hc' hc κ' x b hxb
      k hk1 hcont),
   k, hk1,
   splice_pairing_internal hij hopen s' hc' hc κ' x y b bo
     hxb hyo hryx k hk1 hcont hterm,
   splice_period hij hopen s' hc' hc κ' x y b bo hxb hyo
     hryx k hk1 hcont hterm⟩

omit hb hyo hryx in
/-- Cycle values are not periodic on the lifted side. -/
theorem splice_val_not_periodic : ∀ t, t < k →
    (iterWalk κ' (κ'.match_ x) t).val ∉
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').periodicFlags := by
  intro t ht hmem
  have hper := ((RelTransitionSystem.unglueOpen hij hopen s' hc'
    hc κ').mem_periodicFlags).mp hmem
  rw [splice_walk_val hij hopen s' hc' hc κ' x b hxb k hk1 hcont t ht] at hper
  exact not_periodic_of_chain_segment
    (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') hcont
    (by rw [hterm]; exact hbo) (by omega : 1 ≤ t + 1)
    (by omega : t + 1 ≤ k) hper

omit hbo hyo hryx hterm in
/-- Distinctness along the spliced cycle. -/
theorem splice_inj : ∀ t₁ t₂, t₁ < k → t₂ < k →
    iterWalk κ' (κ'.match_ x) t₁ = iterWalk κ' (κ'.match_ x) t₂ →
      t₁ = t₂ := by
  intro t₁ t₂ ht₁ ht₂ hEq
  have hval := congrArg Subtype.val hEq
  rw [splice_walk_val hij hopen s' hc' hc κ' x b hxb k hk1 hcont t₁ ht₁,
    splice_walk_val hij hopen s' hc' hc κ' x b hxb k hk1 hcont t₂ ht₂] at hval
  rcases Nat.lt_trichotomy t₁ t₂ with h | h | h
  · exfalso
    refine iterWalk_no_repeat
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') hb k
      hcont (t₁ + 1) (t₂ - t₁) (by omega) (by omega) ?_
    rw [show t₁ + 1 + (t₂ - t₁) = t₂ + 1 from by omega]
    exact hval
  · exact h
  · exfalso
    refine iterWalk_no_repeat
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ') hb k
      hcont (t₂ + 1) (t₁ - t₂) (by omega) (by omega) ?_
    rw [show t₂ + 1 + (t₁ - t₂) = t₁ + 1 from by omega]
    exact hval.symm

omit hb hbo in
/-- Index reduction along the spliced cycle. -/
theorem splice_mod : ∀ c,
    iterWalk κ' (κ'.match_ x) c = iterWalk κ' (κ'.match_ x) (c % k)
    := by
  intro c
  exact iterWalk_mod κ' hk1
    (splice_pairing_internal hij hopen s' hc' hc κ' x y b bo
      hxb hyo hryx k hk1 hcont hterm)
    (splice_period hij hopen s' hc' hc κ' x y b bo hxb hyo
      hryx k hk1 hcont hterm) c

end SpliceSide

/-! #### The linked case: the counting bijection -/

/-- Forward-map component: a lifted periodic flag, as a glued
periodic flag. -/
noncomputable def liftPeriodic (κ' : (Fg).RelTransitionSystem)
    (f : {f : W.Flag // f ∈ (RelTransitionSystem.unglueOpen hij
      hopen s' hc' hc κ').periodicFlags}) :
    {g : (W.gluePairOpen i j hij hopen).Flag //
      g ∈ κ'.periodicFlags} :=
  ⟨(⟨f.val,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).1,
      (internal_surviving i j ((RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags_sub f.prop)).2⟩ :
        SurvivingFlag W i j),
    mem_periodicFlags_glued_of_val hij hopen s' hc' hc κ' f.prop⟩

/-- Forward-map component: a flag on a spliced cycle. -/
noncomputable def spliceFlag (κ' : (Fg).RelTransitionSystem)
    (x : SurvivingFlag W i j)
    (hper : κ'.PeriodicFlag (κ'.match_ x)) (t : ℕ) :
    {g : (W.gluePairOpen i j hij hopen).Flag //
      g ∈ κ'.periodicFlags} :=
  ⟨iterWalk κ' (κ'.match_ x) t,
    (κ'.mem_periodicFlags).mpr (periodicFlag_iterWalk κ' hper t)⟩

/-- **The linked-case conjugation**: when the chain from `bf_i`
exits at `bf_j`, the glued walk permutation is, up to a bijection,
the lifted walk permutation plus two `k`-rotations (the two
directions of the spliced circuit). -/
theorem exists_walkPerm_linked (κ' : (Fg).RelTransitionSystem)
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    (k : ℕ) (hk1 : 1 ≤ k)
    (hcontA : ∀ t, t < k → W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag i) t) ∈ (Fl).internalFlags)
    (htermA : W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag i) k) = W.boundaryFlag j) :
    ∃ e : ({f : W.Flag // f ∈ (RelTransitionSystem.unglueOpen hij
        hopen s' hc' hc κ').periodicFlags} ⊕ (Fin k ⊕ Fin k)) ≃
        {g : (W.gluePairOpen i j hij hopen).Flag //
          g ∈ κ'.periodicFlags},
      κ'.walkPermPeriodic = e.permCongr
        (Equiv.sumCongr (RelTransitionSystem.unglueOpen hij hopen
          s' hc' hc κ').walkPermPeriodic
          (Equiv.sumCongr (finRotate k) (finRotate k))) := by
  -- ═══════ SETUP: THE TWO SPLICED CYCLES ═══════
  -- The open glue rewires the two interface flags; the walk out of
  -- `bf_i` and the reversed walk out of `bf_j` splice into the two
  -- cycles `SA`, `SB`, whose basic properties are collected here.
  -- interface rewires
  have hpIpJ : (W.gluePairOpen i j hij hopen).pairing
      (partnerSurvI hopen) = partnerSurvJ hopen :=
    gluePairOpen_pairing_interface_i hij hopen _
      (by rw [partnerSurvI_val hopen, W.pairing_invol])
  have hpJpI : (W.gluePairOpen i j hij hopen).pairing
      (partnerSurvJ hopen) = partnerSurvI hopen :=
    gluePairOpen_pairing_interface_j hij hopen _
      (by
        rw [partnerSurvJ_val hopen, W.pairing_invol]
        exact fun hh => hij (W.boundaryFlag_injective hh).symm)
      (by rw [partnerSurvJ_val hopen, W.pairing_invol])
  -- the reversed chain from bf_j
  have hbfj_eq : W.boundaryFlag j = W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag i) k) := htermA.symm
  have hcontB : ∀ t, t < k → W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag j) t) ∈ (Fl).internalFlags := by
    intro t ht
    rw [hbfj_eq]
    exact reverse_chain_continues
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      hbi hcontA t ht
  have htermB : W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag j) k) = W.boundaryFlag i := by
    rw [hbfj_eq]
    exact reverse_chain_terminates
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      hcontA
  -- the two spliced cycles
  have hperA := splice_periodicFlag hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (partnerSurvJ hopen)
    (W.boundaryFlag i) (W.boundaryFlag j) rfl rfl hpJpI
    k hk1 hcontA htermA
  have hperB := splice_periodicFlag hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (partnerSurvI hopen)
    (W.boundaryFlag j) (W.boundaryFlag i) rfl rfl hpIpJ
    k hk1 hcontB htermB
  have hSA_val := splice_walk_val hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (W.boundaryFlag i) rfl k hk1 hcontA
  have hSB_val := splice_walk_val hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (W.boundaryFlag j) rfl k hk1 hcontB
  have hSA_last := splice_last hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (partnerSurvJ hopen)
    (W.boundaryFlag i) (W.boundaryFlag j) rfl rfl k hk1 hcontA htermA
  have hSB_last := splice_last hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (partnerSurvI hopen)
    (W.boundaryFlag j) (W.boundaryFlag i) rfl rfl k hk1 hcontB htermB
  have hSA_inj := splice_inj hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (W.boundaryFlag i) hbi rfl
    k hk1 hcontA
  have hSB_inj := splice_inj hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (W.boundaryFlag j) hbj rfl
    k hk1 hcontB
  have hSA_notper := splice_val_not_periodic hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (W.boundaryFlag i) (W.boundaryFlag j)
    hbj rfl k hk1 hcontA htermA
  have hSB_notper := splice_val_not_periodic hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (W.boundaryFlag j) (W.boundaryFlag i)
    hbi rfl k hk1 hcontB htermB
  have hSA_mod := splice_mod hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (partnerSurvJ hopen)
    (W.boundaryFlag i) (W.boundaryFlag j) rfl rfl hpJpI
    k hk1 hcontA htermA
  have hSB_mod := splice_mod hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (partnerSurvI hopen)
    (W.boundaryFlag j) (W.boundaryFlag i) rfl rfl hpIpJ
    k hk1 hcontB htermB
  have hSA_per := splice_period hij hopen s' hc' hc κ'
    (partnerSurvI hopen) (partnerSurvJ hopen)
    (W.boundaryFlag i) (W.boundaryFlag j) rfl rfl hpJpI
    k hk1 hcontA htermA
  have hSB_per := splice_period hij hopen s' hc' hc κ'
    (partnerSurvJ hopen) (partnerSurvI hopen)
    (W.boundaryFlag j) (W.boundaryFlag i) rfl rfl hpIpJ
    k hk1 hcontB htermB
  -- cross-cycle disjointness at the value level
  have hcross : ∀ t₁ t₂ : ℕ, t₁ < k → t₂ < k →
      (iterWalk κ' (κ'.match_ (partnerSurvI hopen)) t₁).val ≠
      (iterWalk κ' (κ'.match_ (partnerSurvJ hopen)) t₂).val
      := by
    intro t₁ t₂ h₁ h₂ hEq
    rw [hSA_val t₁ h₁, hSB_val t₂ h₂] at hEq
    have hrev : iterWalk
        (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
        (W.boundaryFlag j) (t₂ + 1) =
        W.pairing (iterWalk
          (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
          (W.boundaryFlag i) (k - (t₂ + 1))) := by
      rw [hbfj_eq]
      exact iterWalk_reverse
        (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
        hcontA (t₂ + 1) (by omega)
    rw [hrev] at hEq
    exact pairing_iterWalk_ne
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      hcontA (by omega : k - (t₂ + 1) ≤ k) (by omega : t₁ + 1 ≤ k)
      hEq.symm
  -- ═══════ STAGE 1: THE FORWARD MAP IS INJECTIVE ═══════
  -- injectivity of the forward map
  have hinj : Function.Injective
      (Sum.elim (liftPeriodic hij hopen s' hc' hc κ')
        (Sum.elim
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvI hopen) hperA t.val)
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvJ hopen) hperB t.val))) := by
    rintro (f₁ | (t₁ | t₁)) (f₂ | (t₂ | t₂)) hEq
    · exact congrArg Sum.inl (Subtype.ext
        (congrArg (fun z => z.val.val) hEq : f₁.val = f₂.val))
    · exfalso
      have h1 : f₁.val = (iterWalk κ'
          (κ'.match_ (partnerSurvI hopen)) t₂.val).val :=
        congrArg (fun z => z.val.val) hEq
      have hf := f₁.prop
      rw [h1] at hf
      exact hSA_notper t₂.val t₂.isLt hf
    · exfalso
      have h1 : f₁.val = (iterWalk κ'
          (κ'.match_ (partnerSurvJ hopen)) t₂.val).val :=
        congrArg (fun z => z.val.val) hEq
      have hf := f₁.prop
      rw [h1] at hf
      exact hSB_notper t₂.val t₂.isLt hf
    · exfalso
      have h1 : (iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          t₁.val).val = f₂.val :=
        congrArg (fun z => z.val.val) hEq
      have hf := f₂.prop
      rw [← h1] at hf
      exact hSA_notper t₁.val t₁.isLt hf
    · have h1 : iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          t₁.val =
          iterWalk κ' (κ'.match_ (partnerSurvI hopen)) t₂.val :=
        congrArg Subtype.val hEq
      exact congrArg (fun t => Sum.inr (Sum.inl t))
        (Fin.ext (hSA_inj t₁.val t₂.val t₁.isLt t₂.isLt h1))
    · exfalso
      have h1 : (iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          t₁.val).val =
          (iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
            t₂.val).val :=
        congrArg (fun z => z.val.val) hEq
      exact hcross t₁.val t₂.val t₁.isLt t₂.isLt h1
    · exfalso
      have h1 : (iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
          t₁.val).val = f₂.val :=
        congrArg (fun z => z.val.val) hEq
      have hf := f₂.prop
      rw [← h1] at hf
      exact hSB_notper t₁.val t₁.isLt hf
    · exfalso
      have h1 : (iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          t₂.val).val =
          (iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
            t₁.val).val :=
        (congrArg (fun z => z.val.val) hEq).symm
      exact hcross t₂.val t₁.val t₂.isLt t₁.isLt h1
    · have h1 : iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
          t₁.val =
          iterWalk κ' (κ'.match_ (partnerSurvJ hopen)) t₂.val
          :=
        congrArg Subtype.val hEq
      exact congrArg (fun t => Sum.inr (Sum.inr t))
        (Fin.ext (hSB_inj t₁.val t₂.val t₁.isLt t₂.isLt h1))
  -- ═══════ STAGE 2: THE FORWARD MAP IS SURJECTIVE ═══════
  -- surjectivity of the forward map
  have hsurj : Function.Surjective
      (Sum.elim (liftPeriodic hij hopen s' hc' hc κ')
        (Sum.elim
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvI hopen) hperA t.val)
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvJ hopen) hperB t.val))) := by
    rintro ⟨g, hg⟩
    rcases periodicFlag_val_or_orbit hij hopen s' hc' hc κ' hg with
      hval | (⟨hperI', c, hcEq⟩ | ⟨hperJ', c, hcEq⟩)
    · exact ⟨Sum.inl ⟨g.val, hval⟩, Subtype.ext (Subtype.ext rfl)⟩
    · -- g lies on the orbit of the i-side far end (the B-cycle)
      have hstep : iterWalk κ'
          (κ'.match_ (partnerSurvJ hopen)) ((k - 1) + c) = g
          := by
        have h := iterWalk_add κ'
          (κ'.match_ (partnerSurvJ hopen)) (k - 1) c
        rw [hSB_last] at h
        rw [h]
        exact hcEq
      refine ⟨Sum.inr (Sum.inr ⟨((k - 1) + c) % k,
        Nat.mod_lt _ (by omega)⟩), Subtype.ext ?_⟩
      show iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
        (((k - 1) + c) % k) = g
      rw [← hSB_mod ((k - 1) + c)]
      exact hstep
    · -- g lies on the orbit of the j-side far end (the A-cycle)
      have hstep : iterWalk κ'
          (κ'.match_ (partnerSurvI hopen)) ((k - 1) + c) = g := by
        have h := iterWalk_add κ'
          (κ'.match_ (partnerSurvI hopen)) (k - 1) c
        rw [hSA_last] at h
        rw [h]
        exact hcEq
      refine ⟨Sum.inr (Sum.inl ⟨((k - 1) + c) % k,
        Nat.mod_lt _ (by omega)⟩), Subtype.ext ?_⟩
      show iterWalk κ' (κ'.match_ (partnerSurvI hopen))
        (((k - 1) + c) % k) = g
      rw [← hSA_mod ((k - 1) + c)]
      exact hstep
  refine ⟨Equiv.ofBijective _ ⟨hinj, hsurj⟩, ?_⟩
  -- ═══════ STAGE 3: THE BIJECTION IS WALK-EQUIVARIANT ═══════
  -- the walk equivariance of the forward map
  have key : ∀ z, κ'.walkPermPeriodic
      ((Sum.elim (liftPeriodic hij hopen s' hc' hc κ')
        (Sum.elim
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvI hopen) hperA t.val)
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvJ hopen) hperB t.val))) z) =
      (Sum.elim (liftPeriodic hij hopen s' hc' hc κ')
        (Sum.elim
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvI hopen) hperA t.val)
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvJ hopen) hperB t.val)))
        ((Equiv.sumCongr (RelTransitionSystem.unglueOpen hij hopen
          s' hc' hc κ').walkPermPeriodic
          (Equiv.sumCongr (finRotate k) (finRotate k))) z) := by
    intro z
    rcases z with f | (t | t)
    · -- lifted periodic flags: the walk corresponds valuewise
      obtain ⟨h1, h2⟩ := internal_surviving i j
        ((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').periodicFlags_sub f.prop)
      refine Subtype.ext (Subtype.ext ?_)
      show (κ'.match_ ((W.gluePairOpen i j hij hopen).pairing
          ⟨f.val, h1, h2⟩)).val =
        (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
          κ').match_ (W.pairing f.val)
      have hpf : W.pairing f.val ∈ (Fl).internalFlags :=
        all_pairings_internal_of_periodic
          (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
          (((RelTransitionSystem.unglueOpen hij hopen s' hc' hc
            κ').mem_periodicFlags).mp f.prop) 0
      obtain ⟨hp1, hp2⟩ := internal_surviving i j hpf
      have hag : W.pairing f.val =
          ((W.gluePairOpen i j hij hopen).pairing
            ⟨f.val, h1, h2⟩).val :=
        (gluePairOpen_pairing_val_of_ne hij hopen ⟨f.val, h1, h2⟩
          hp1 hp2).symm
      rw [hag, unglueOpen_match_val hij hopen s' hc' hc κ'
        ((W.gluePairOpen i j hij hopen).pairing ⟨f.val, h1, h2⟩)]
    · -- the A-cycle rotates
      refine Subtype.ext ?_
      show iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          (t.val + 1) =
        iterWalk κ' (κ'.match_ (partnerSurvI hopen))
          (((finRotate k) t).val)
      obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
      rcases eq_or_ne t (Fin.last k0) with rfl | hne
      · rw [finRotate_last, Fin.val_zero, Fin.val_last]
        exact hSA_per
      · have hne' : t.val ≠ k0 := by
          intro h
          exact hne (Fin.ext (by rw [h, Fin.val_last]))
        have hlt : t.val < k0 := by
          have := t.isLt
          omega
        have hrot : ((finRotate (k0 + 1)) t).val = t.val + 1 := by
          rw [finRotate_apply]
          exact Fin.val_add_one_of_lt' (by omega)
        rw [hrot]
    · -- the B-cycle rotates
      refine Subtype.ext ?_
      show iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
          (t.val + 1) =
        iterWalk κ' (κ'.match_ (partnerSurvJ hopen))
          (((finRotate k) t).val)
      obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
      rcases eq_or_ne t (Fin.last k0) with rfl | hne
      · rw [finRotate_last, Fin.val_zero, Fin.val_last]
        exact hSB_per
      · have hne' : t.val ≠ k0 := by
          intro h
          exact hne (Fin.ext (by rw [h, Fin.val_last]))
        have hlt : t.val < k0 := by
          have := t.isLt
          omega
        have hrot : ((finRotate (k0 + 1)) t).val = t.val + 1 := by
          rw [finRotate_apply]
          exact Fin.val_add_one_of_lt' (by omega)
        rw [hrot]
  apply Equiv.ext
  intro xg
  obtain ⟨z, rfl⟩ := hsurj xg
  rw [Equiv.permCongr_apply]
  have hsymm : (Equiv.ofBijective _ ⟨hinj, hsurj⟩).symm
      ((Sum.elim (liftPeriodic hij hopen s' hc' hc κ')
        (Sum.elim
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvI hopen) hperA t.val)
          (fun t : Fin k => spliceFlag hij hopen s' hc' κ'
            (partnerSurvJ hopen) hperB t.val))) z) = z :=
    Equiv.symm_apply_apply _ z
  rw [hsymm]
  exact key z

/-! #### The circuit-count delta -/

/-- **Count delta in the linked case**: the splice closes exactly
one new circuit (two new walk orbits). -/
theorem openCircuitCount_linked_chain (κ' : (Fg).RelTransitionSystem)
    (hbi : W.boundaryFlag i ∈ (Fl).boundaryFlags)
    (hbj : W.boundaryFlag j ∈ (Fl).boundaryFlags)
    (k : ℕ) (hk1 : 1 ≤ k)
    (hcontA : ∀ t, t < k → W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag i) t) ∈ (Fl).internalFlags)
    (htermA : W.pairing (iterWalk
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (W.boundaryFlag i) k) = W.boundaryFlag j) :
    κ'.openCircuitCount =
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').openCircuitCount + 1 := by
  obtain ⟨e, he⟩ := exists_walkPerm_linked hij hopen s' hc' hc κ'
    hbi hbj k hk1 hcontA htermA
  unfold RelTransitionSystem.openCircuitCount
  rw [he, cycleType_permCongr, card_fixedPoints_permCongr,
    cycleType_sumCongr, cycleType_sumCongr,
    card_fixedPoints_sumCongr, card_fixedPoints_sumCongr,
    Multiset.card_add, Multiset.card_add]
  have hrot := finRotate_orbit_count k hk1
  omega

/-- **The circuit-count delta of a participating open glue**: the
glued count exceeds the unglued count by `1` exactly when the
interface is linked. -/
theorem openCircuitCount_glueOpen_participating (κ' : (Fg).RelTransitionSystem)
    (hpi : partnerSurvI hopen ∈ s') :
    κ'.openCircuitCount =
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc
        κ').openCircuitCount +
        (if InterfaceLinked hij hopen s' hc' hc κ' hpi then 1
          else 0) := by
  by_cases hL : InterfaceLinked hij hopen s' hc' hc κ' hpi
  · rw [if_pos hL]
    obtain ⟨k, hk_le, hcontA, hpm⟩ := pathMatch_chain_length
      (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
      (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi)
    have htermA : W.pairing (iterWalk
        (RelTransitionSystem.unglueOpen hij hopen s' hc' hc κ')
        (W.boundaryFlag i) k) = W.boundaryFlag j := by
      rw [← hpm]
      exact hL
    have hk1 : 1 ≤ k := by
      by_contra hk0
      have hk0' : k = 0 := by omega
      subst hk0'
      exact hopen htermA
    exact openCircuitCount_linked_chain hij hopen s' hc' hc κ'
      (boundaryFlagI_mem_boundaryFlags hij hopen s' hc hpi)
      (boundaryFlagJ_mem_boundaryFlags hij hopen s' hc' hc hpi)
      k hk1 hcontA htermA
  · rw [if_neg hL, add_zero]
    exact (openCircuitCount_notLinked hij hopen s' hc' hc κ' hpi
      hL).symm

end OpenGlueParticipating

end EdgeSubset

end RS
