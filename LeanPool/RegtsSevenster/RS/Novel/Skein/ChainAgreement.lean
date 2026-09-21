/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PathCanon

/-!
# Chain agreement of path-canonical orientations

Two path-canonical orientations of the same boundary-relative
transition system agree on every non-periodic internal flag: a
non-periodic flag lies on the boundary-to-boundary chain of a unique
pair of boundary ends, the low-labelled end's entry value is pinned to
incoming by canonicality, and orientation values propagate rigidly
along a chain (`match_flip` and `pairing_flip` alternate), so the
whole chain's values are determined by the pinned seed.

## Main results

* `pathCanonical_agree_nonperiodic` — path-canonical orientations
  agree off the periodic flags.
* `pathCanonical_diff_pairing_closed` — hence their difference set is
  pairing-closed on internal flags (disagreement forces periodicity,
  and periodic flags have internal pairings).
* `throughSummand_pathCanonical` — hence the constrained summand does
  not depend on the choice of path-canonical orientation, discharging
  the `hchain` hypothesis of `throughSummand_canonical_unique`.

## Proof route

1. `traceChain_some_exit` converts a terminating chain into walk
   data: an exit step count with internal pairings before it.
2. `isOut_iterWalk_eq_not_seed` / `isOut_pairing_iterWalk_eq_seed`
   propagate any orientation's value along a chain: every match-side
   flag carries the negated seed value, every pairing-side flag the
   seed value, where the seed is the value at the entry edge.
3. `pathCanonical_agree_on_chain` compares the two chain ends by
   label; canonicality pins the seed at the low end, and the reverse
   walk identities transport the pinned value to the given flag.
4. `pathCanonical_agree_nonperiodic` places an arbitrary
   non-periodic internal flag on the chain of the boundary end its
   forward walk reaches, as a pairing-side flag of the reverse
   chain.
-/

namespace RS

open scoped Classical

variable {α : Type}

namespace EdgeSubset

/-! ### 1. From terminating chains to walk exit data -/

/-- A terminating chain yields walk data: an exit step `k` whose
earlier pairings are all internal and whose pairing at `k` is the
boundary result. -/
theorem traceChain_some_exit {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) :
    ∀ (fuel : ℕ) (f b : W.Flag), traceChain κ fuel f = some b →
      ∃ k, (∀ j, j < k →
          W.pairing (iterWalk κ f j) ∈ F.internalFlags) ∧
        W.pairing (iterWalk κ f k) = b ∧ b ∈ F.boundaryFlags := by
  intro fuel
  induction fuel with
  | zero => intro f b h; simp [traceChain] at h
  | succ n ih =>
    intro f b h
    by_cases hb : W.pairing f ∈ F.boundaryFlags
    · rw [traceChain_boundary κ n f hb] at h
      refine ⟨0, fun j hj => absurd hj (by omega), ?_, ?_⟩
      · simpa using Option.some.inj h
      · rw [← Option.some.inj h]; exact hb
    · by_cases hi : W.pairing f ∈ F.internalFlags
      · rw [traceChain_internal κ n f hi] at h
        obtain ⟨k, hcont, hexit, hbb⟩ :=
          ih (κ.match_ (W.pairing f)) b h
        refine ⟨k + 1, ?_, ?_, hbb⟩
        · intro j hj
          cases j with
          | zero => simpa using hi
          | succ j' =>
            have hstep := hcont j' (by omega)
            rwa [iterWalk_shift] at hstep
        · rwa [iterWalk_shift] at hexit
      · rw [traceChain_neither κ n f hb hi] at h; cases h

/-! ### 2. Rigid propagation of orientation values along a chain -/

/-- **Match-side propagation**: along a walk with internal pairings
up to step `k`, every visited flag (step `1 ≤ j ≤ k`) carries the
negated seed value, for any orientation. -/
theorem isOut_iterWalk_eq_not_seed {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {b : W.Flag} {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags) :
    ∀ j, 1 ≤ j → j ≤ k →
      o.isOut (iterWalk κ b j) = !o.isOut (W.pairing b) := by
  intro j
  induction j with
  | zero => intro h1 _; exact absurd h1 (by omega)
  | succ j ih =>
    intro _ hjk
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · have h0 : W.pairing (iterWalk κ b 0) ∈ F.internalFlags :=
        hcont 0 (by omega)
      rw [iterWalk_succ, o.match_flip _ h0, iterWalk_zero]
    · have hpj : W.pairing (iterWalk κ b j) ∈ F.internalFlags :=
        hcont j (by omega)
      have hwj : iterWalk κ b j ∈ F.internalFlags :=
        iterWalk_mem_internal κ k hj1 (by omega) hcont
      rw [iterWalk_succ, o.match_flip _ hpj,
        o.pairing_flip _ hwj hpj, Bool.not_not]
      exact ih hj1 (by omega)

/-- **Pairing-side propagation**: along a walk with internal
pairings up to step `k`, every intermediate pairing (step `j < k`)
carries the seed value, for any orientation. -/
theorem isOut_pairing_iterWalk_eq_seed {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    (o : κ.Orientation) {b : W.Flag} {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags) :
    ∀ j, j < k →
      o.isOut (W.pairing (iterWalk κ b j)) =
        o.isOut (W.pairing b) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · rfl
  · have hpj : W.pairing (iterWalk κ b j) ∈ F.internalFlags :=
      hcont j hj
    have hwj : iterWalk κ b j ∈ F.internalFlags :=
      iterWalk_mem_internal κ k hj1 (by omega) hcont
    rw [o.pairing_flip _ hwj hpj,
      isOut_iterWalk_eq_not_seed o hcont j hj1 (by omega),
      Bool.not_not]

/-! ### 3. Chain agreement from the low-end seed -/

/-- **Agreement on a chain**: two path-canonical orientations agree
on every pairing-side flag of a boundary-terminated chain — whichever
end has the lower label, canonicality pins its entry value to
incoming for both orientations, and rigid propagation transports the
pinned seed to the given flag. -/
theorem pathCanonical_agree_on_chain
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o o' : κ.Orientation}
    (hc : PathCanonical o) (hc' : PathCanonical o')
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ b k) ∈ F.boundaryFlags)
    (hkle : k ≤ F.flags.card) {m : ℕ} (hm : m < k) :
    o.isOut (W.pairing (iterWalk κ b m)) =
      o'.isOut (W.pairing (iterWalk κ b m)) := by
  -- the chain's other end is the path match of `b`
  have hpm : κ.pathMatch b hb = W.pairing (iterWalk κ b k) :=
    κ.pathMatch_eq hb (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ b hcont hterm))
  -- name the two boundary labels
  obtain ⟨iℓ, hiℓ⟩ := attach_boundary_of_mem F hb
  have hbi : b = W.boundaryFlag iℓ := W.eq_boundaryFlag iℓ b hiℓ
  obtain ⟨jℓ, hjℓ⟩ := attach_boundary_of_mem F hterm
  have hbj : W.pairing (iterWalk κ b k) = W.boundaryFlag jℓ :=
    W.eq_boundaryFlag jℓ _ hjℓ
  have hne_label : iℓ ≠ jℓ := by
    intro hEq
    apply κ.pathMatch_ne_self hb
    rw [hpm, hbj, ← hEq, ← hbi]
  rcases lt_or_gt_of_ne hne_label with hij | hji
  · -- `b` is the low end: canonicality pins the seed at `pairing b`
    have hbB : W.boundaryFlag iℓ ∈ F.boundaryFlags := by
      rw [← hbi]; exact hb
    have hpair_int :
        W.pairing (W.boundaryFlag iℓ) ∈ F.internalFlags := by
      rw [← hbi]; exact hcont 0 (by omega)
    have hpm' : κ.pathMatch (W.boundaryFlag iℓ) hbB =
        W.boundaryFlag jℓ := by
      rw [← hbj, ← hpm]
      exact κ.pathMatch_congr hbi.symm hbB hb
    have seedo : o.isOut (W.pairing b) = false := by
      rw [hbi]; exact hc iℓ jℓ hbB hpair_int hpm' hij
    have seedo' : o'.isOut (W.pairing b) = false := by
      rw [hbi]; exact hc' iℓ jℓ hbB hpair_int hpm' hij
    rw [isOut_pairing_iterWalk_eq_seed o hcont m hm,
      isOut_pairing_iterWalk_eq_seed o' hcont m hm, seedo, seedo']
  · -- the far end is the low end: pin its seed and walk back
    have hb2B : W.boundaryFlag jℓ ∈ F.boundaryFlags := by
      rw [← hbj]; exact hterm
    have hpair2_int :
        W.pairing (W.boundaryFlag jℓ) ∈ F.internalFlags := by
      rw [← hbj, W.pairing_invol]
      exact iterWalk_mem_internal κ k (by omega) le_rfl hcont
    have hpminv : κ.pathMatch (W.boundaryFlag jℓ) hb2B =
        W.boundaryFlag iℓ := by
      rw [← hbi]
      have h1 : κ.pathMatch (W.boundaryFlag jℓ) hb2B =
          κ.pathMatch (κ.pathMatch b hb) (κ.pathMatch_mem hb) := by
        apply κ.pathMatch_congr
        rw [← hbj]
        exact hpm.symm
      rw [h1, κ.pathMatch_invol hb]
    have seedo2 : o.isOut (W.pairing (W.boundaryFlag jℓ)) = false :=
      hc jℓ iℓ hb2B hpair2_int hpminv hji
    have seedo2' :
        o'.isOut (W.pairing (W.boundaryFlag jℓ)) = false :=
      hc' jℓ iℓ hb2B hpair2_int hpminv hji
    have hseed :
        o.isOut (W.pairing (W.pairing (iterWalk κ b k))) = false :=
      by rw [hbj]; exact seedo2
    have hseed' :
        o'.isOut (W.pairing (W.pairing (iterWalk κ b k))) = false :=
      by rw [hbj]; exact seedo2'
    -- the reverse chain from the far end
    have hcont2 : ∀ t, t < k →
        W.pairing (iterWalk κ (W.pairing (iterWalk κ b k)) t) ∈
          F.internalFlags :=
      fun t ht => reverse_chain_continues κ hb hcont t ht
    have hfm : iterWalk κ (W.pairing (iterWalk κ b k)) (k - m) =
        W.pairing (iterWalk κ b m) := by
      have hrev := iterWalk_reverse κ hcont (k - m) (by omega)
      rwa [show k - (k - m) = m from by omega] at hrev
    have ho := isOut_iterWalk_eq_not_seed o hcont2 (k - m)
      (by omega) (by omega)
    have ho' := isOut_iterWalk_eq_not_seed o' hcont2 (k - m)
      (by omega) (by omega)
    rw [hfm, hseed, Bool.not_false] at ho
    rw [hfm, hseed', Bool.not_false] at ho'
    rw [ho, ho']

/-! ### Agreement off the periodic flags -/

/-- **Chain agreement of path-canonical orientations**: two
path-canonical orientations of one relative transition system agree
on every non-periodic internal flag. -/
theorem pathCanonical_agree_nonperiodic
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o o' : κ.Orientation}
    (hc : PathCanonical o) (hc' : PathCanonical o') :
    ∀ f ∈ F.internalFlags, ¬ κ.PeriodicFlag f →
      o.isOut f = o'.isOut f := by
  intro f hf hnper
  -- the forward walk from `f` exits at a boundary flag
  obtain ⟨fuel, b0, hchain⟩ :=
    (internal_periodic_or_terminates κ f hf).resolve_left hnper
  obtain ⟨kf, hcontf, hexitf, hb0⟩ :=
    traceChain_some_exit κ fuel f b0 hchain
  have hbf : W.pairing (iterWalk κ f kf) ∈ F.boundaryFlags := by
    rw [hexitf]; exact hb0
  -- the reverse chain from that boundary end runs past `f`
  have hcontb : ∀ t, t ≤ kf →
      W.pairing (iterWalk κ (W.pairing (iterWalk κ f kf)) t) ∈
        F.internalFlags := by
    intro t ht
    rw [iterWalk_reverse κ hcontf t ht, W.pairing_invol]
    rcases Nat.lt_or_ge t kf with h | h
    · exact iterWalk_mem_internal κ kf (by omega) (by omega) hcontf
    · rw [show kf - t = 0 from by omega, iterWalk_zero]
      exact hf
  -- the full chain from the boundary end
  obtain ⟨k', hk'le, hcont', hterm'⟩ :=
    chain_terminates_with_data κ hbf
  have hk'gt : kf < k' := by
    by_contra hle
    exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags
      (hcontb k' (by omega)) hterm'
  -- `f` is the pairing-side flag of that chain at step `kf`
  have hfeq :
      W.pairing (iterWalk κ (W.pairing (iterWalk κ f kf)) kf) =
        f := reverse_chain_terminates κ hcontf
  have hagree := pathCanonical_agree_on_chain hc hc' hbf hcont'
    hterm' hk'le (m := kf) hk'gt
  rwa [hfeq] at hagree

/-! ### 5. Corollaries -/

/-- **Pairing-closure of the difference set**: where two
path-canonical orientations disagree, the flag is periodic, so its
pairing is internal — exactly the `hchain` hypothesis of
`throughSummand_canonical_unique`. -/
theorem pathCanonical_diff_pairing_closed
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o o' : κ.Orientation}
    (hc : PathCanonical o) (hc' : PathCanonical o') :
    ∀ f ∈ F.internalFlags, o.isOut f ≠ o'.isOut f →
      W.pairing f ∈ F.internalFlags := by
  intro f hf hne
  by_cases hper : κ.PeriodicFlag f
  · have hp := all_pairings_internal_of_periodic κ hper 0
    simpa using hp
  · exact absurd (pathCanonical_agree_nonperiodic hc hc' f hf hper)
      hne

/-- **Well-definedness of the canonical summand**: the constrained
summand agrees across all path-canonical orientations of one
relative transition system, unconditionally. -/
theorem throughSummand_pathCanonical
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {k ℓ : ℕ}
    (h : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ : F.RelTransitionSystem} {o o' : κ.Orientation}
    (hc : PathCanonical o) (hc' : PathCanonical o') (c : ℕ) :
    F.throughSummand h st hbnd o c =
      F.throughSummand h st hbnd o' c :=
  throughSummand_canonical_unique h st hbnd hc hc'
    (pathCanonical_diff_pairing_closed hc hc') c

end EdgeSubset

end RS
