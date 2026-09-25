/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ChainAgreement

/-!
# Existence of path-canonical orientations

Every orientation of a boundary-relative transition system can be
repaired into a path-canonical one by flipping exactly the internal
flags lying on non-canonically oriented boundary-to-boundary chains.

## Main results

* `EdgeSubset.exists_pathCanonical` — from any orientation of a
  relative transition system, a path-canonical orientation of the
  *same* system exists.
* `EdgeSubset.canonOrientation` — the orientation it produces,
  built by flipping every chain whose low end points outwards.

## Proof route

1. `BadFlag` marks the pairing-side flags of chains whose low-labelled
   boundary end has an outgoing entry edge (`ChainNonCanon`); the
   symmetric formulation covers every internal flag of such a chain,
   since match-side flags are the pairing-side flags of the reverse
   chain (`iterWalk_reverse`).
2. The flip set is closed under the matching (`badFlag_match`) and
   under the edge pairing on internal partners (`badFlag_pairing`),
   so negating `isOut` on it yields a valid orientation
   (`canonOrientation`).
3. Exit steps of a forward walk are unique
   (`exit_step_unique`), and a pairing-side flag's forward walk exits
   at its chain's base end (`chain_flag_exit`); hence the chain data
   witnessing badness of an entry flag are pinned to the entry's own
   chain, and the flip decision at each entry flag matches its
   chain's canonicality status (`pathCanonical_canonOrientation`).
-/

namespace RS



variable {α : Type}

namespace EdgeSubset

/-! ### 1. Exit uniqueness and chain membership -/

/-- **Exit uniqueness**: two boundary-exit data for the forward walk
of one flag agree on the exit step. -/
theorem exit_step_unique {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {f : W.Flag}
    {k₁ k₂ : ℕ}
    (hc₁ : ∀ t, t < k₁ →
      W.pairing (iterWalk κ f t) ∈ F.internalFlags)
    (ht₁ : W.pairing (iterWalk κ f k₁) ∈ F.boundaryFlags)
    (hc₂ : ∀ t, t < k₂ →
      W.pairing (iterWalk κ f t) ∈ F.internalFlags)
    (ht₂ : W.pairing (iterWalk κ f k₂) ∈ F.boundaryFlags) :
    k₁ = k₂ := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags (hc₂ k₁ h) ht₁
  · exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags (hc₁ k₂ h) ht₂

/-- **Chain-flag exit data**: the forward walk of the pairing-side
flag at step `m` of a chain from `b` has internal pairings before
step `m` and exits at `b` at step `m`. -/
theorem chain_flag_exit {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) {b : W.Flag}
    {k m : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags)
    (hmk : m < k) :
    (∀ t, t < m →
        W.pairing (iterWalk κ (W.pairing (iterWalk κ b m)) t) ∈
          F.internalFlags) ∧
      W.pairing (iterWalk κ (W.pairing (iterWalk κ b m)) m) = b := by
  have hcont' : ∀ t, t < m →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags :=
    fun t ht => hcont t (by omega)
  constructor
  · intro t ht
    rw [iterWalk_reverse κ hcont' t (by omega), W.pairing_invol]
    exact iterWalk_mem_internal κ k (by omega) (by omega) hcont
  · rw [iterWalk_reverse κ hcont' m le_rfl, Nat.sub_self,
      iterWalk_zero, W.pairing_invol]

/-- The path match of a boundary end equals the terminal pairing of
any boundary-terminated chain data from it (via exit uniqueness — no
fuel bound required on the given data). -/
theorem pathMatch_eq_of_chain {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ b k) ∈ F.boundaryFlags) :
    κ.pathMatch b hb = W.pairing (iterWalk κ b k) := by
  obtain ⟨k₀, -, hcont₀, hpm₀⟩ := pathMatch_chain_length κ hb
  have hterm₀ : W.pairing (iterWalk κ b k₀) ∈ F.boundaryFlags := by
    rw [← hpm₀]
    exact κ.pathMatch_mem hb
  have hk : k = k₀ := exit_step_unique κ hcont hterm hcont₀ hterm₀
  rw [hpm₀, hk]

open EdgeSubset in
/-- **A flag whose partner is a boundary flag is matched to it.** -/
theorem pathMatch_eq_pairing_of_boundary {α : Type}
    {W : Fragment α} {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags)
    (hp : W.pairing b ∈ F.boundaryFlags) :
    κ.pathMatch b hb = W.pairing b := by
  have h := pathMatch_eq_of_chain κ hb (k := 0)
    (fun _ ht => absurd ht (by omega))
    (by rw [iterWalk_zero]; exact hp)
  rwa [iterWalk_zero] at h

/-! ### 2. Non-canonical chains and the flip set -/

/-- The chain from boundary end `b` is **non-canonically oriented**:
its lower-labelled end — whichever of `b` and its path match that is —
has an outgoing entry edge. -/
def ChainNonCanon [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (b : W.Flag) : Prop :=
  ∃ (hb : b ∈ F.boundaryFlags) (i j : α),
    W.attach b = Sum.inr i ∧
    W.attach (κ.pathMatch b hb) = Sum.inr j ∧
    ((i < j ∧ o.isOut (W.pairing b) = true) ∨
      (j < i ∧ o.isOut (W.pairing (κ.pathMatch b hb)) = true))

/-- Non-canonicality passes to the opposite chain end. -/
theorem chainNonCanon_pathMatch
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {b : W.Flag} (h : ChainNonCanon κ o b)
    (hb : b ∈ F.boundaryFlags) :
    ChainNonCanon κ o (κ.pathMatch b hb) := by
  obtain ⟨hb₂, i, j, hai, haj, hdisj⟩ := h
  refine ⟨κ.pathMatch_mem hb, j, i, ?_, ?_, ?_⟩
  · exact haj
  · rw [κ.pathMatch_invol hb]
    exact hai
  · rcases hdisj with ⟨hij, hout⟩ | ⟨hji, hout⟩
    · refine Or.inr ⟨hij, ?_⟩
      rw [κ.pathMatch_invol hb]
      exact hout
    · exact Or.inl ⟨hji, hout⟩

/-- **The flip set**: `f` is a pairing-side flag of a
non-canonically oriented boundary-to-boundary chain. -/
def BadFlag [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem) (o : κ.Orientation)
    (f : W.Flag) : Prop :=
  ∃ (b : W.Flag) (k m : ℕ),
    (∀ t, t < k →
      W.pairing (iterWalk κ b t) ∈ F.internalFlags) ∧
    W.pairing (iterWalk κ b k) ∈ F.boundaryFlags ∧
    m < k ∧ f = W.pairing (iterWalk κ b m) ∧
    ChainNonCanon κ o b

/-- **Match closure**: the flip set is closed under the matching —
the match of a pairing-side flag is a pairing-side flag of the
reverse chain, whose base end is the path match of the original. -/
theorem badFlag_match [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {f : W.Flag} (h : BadFlag κ o f) :
    BadFlag κ o (κ.match_ f) := by
  obtain ⟨b, k, m, hcont, hterm, hmk, hfe, hnc⟩ := h
  have hb : b ∈ F.boundaryFlags := by
    obtain ⟨hb, -⟩ := hnc
    exact hb
  refine ⟨W.pairing (iterWalk κ b k), k, k - (m + 1),
    fun t ht => reverse_chain_continues κ hb hcont t ht, ?_,
    by omega, ?_, ?_⟩
  · rw [reverse_chain_terminates κ hcont]
    exact hb
  · have h2 := iterWalk_reverse κ hcont (k - (m + 1)) (by omega)
    rw [show k - (k - (m + 1)) = m + 1 from by omega] at h2
    rw [h2, W.pairing_invol, hfe]
    exact (iterWalk_succ κ b m).symm
  · have hpm := pathMatch_eq_of_chain κ hb hcont hterm
    have htr := chainNonCanon_pathMatch hnc hb
    rwa [hpm] at htr

/-- **Pairing closure**: the flip set is closed under the edge
pairing whenever the partner is internal — the partner is a
match-side flag, i.e. a pairing-side flag of the reverse chain. -/
theorem badFlag_pairing [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {f : W.Flag} (h : BadFlag κ o f)
    (hp : W.pairing f ∈ F.internalFlags) :
    BadFlag κ o (W.pairing f) := by
  obtain ⟨b, k, m, hcont, hterm, hmk, hfe, hnc⟩ := h
  have hb : b ∈ F.boundaryFlags := by
    obtain ⟨hb, -⟩ := hnc
    exact hb
  have hpf : W.pairing f = iterWalk κ b m := by
    rw [hfe, W.pairing_invol]
  rcases Nat.eq_zero_or_pos m with rfl | hm1
  · rw [iterWalk_zero] at hpf
    exact absurd hb (Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags (hpf ▸ hp))
  · refine ⟨W.pairing (iterWalk κ b k), k, k - m,
      fun t ht => reverse_chain_continues κ hb hcont t ht, ?_,
      by omega, ?_, ?_⟩
    · rw [reverse_chain_terminates κ hcont]
      exact hb
    · have h2 := iterWalk_reverse κ hcont (k - m) (by omega)
      rw [show k - (k - m) = m from by omega] at h2
      rw [hpf, h2, W.pairing_invol]
    · have hpm := pathMatch_eq_of_chain κ hb hcont hterm
      have htr := chainNonCanon_pathMatch hnc hb
      rwa [hpm] at htr

/-! ### 3. The flipped orientation -/

/-- The candidate canonical orientation as a raw flag function:
negate on the flip set. -/
noncomputable def canonIsOut [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (f : W.Flag) : Bool :=
  if BadFlag κ o f then !o.isOut f else o.isOut f

/-- On a flag of a badly oriented chain the repair reverses. -/
theorem canonIsOut_of_bad [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {f : W.Flag} (h : BadFlag κ o f) :
    canonIsOut κ o f = !o.isOut f := by
  unfold canonIsOut
  rw [ite_eq_left h]

/-- Elsewhere it leaves the orientation alone. -/
theorem canonIsOut_of_not_bad
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {o : κ.Orientation} {f : W.Flag} (h : ¬ BadFlag κ o f) :
    canonIsOut κ o f = o.isOut f := by
  unfold canonIsOut
  rw [ite_eq_right h]

/-- **The flipped orientation**: negate the given orientation on the
flip set.  The closure lemmas make the flip commute with both
orientation axioms. -/
noncomputable def canonOrientation
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    (o : κ.Orientation) : κ.Orientation where
  isOut := canonIsOut κ o
  match_flip := fun f hf => by
    by_cases hB : BadFlag κ o f
    · rw [canonIsOut_of_bad (badFlag_match hB), canonIsOut_of_bad hB,
        o.match_flip f hf]
    · have hBm : ¬ BadFlag κ o (κ.match_ f) := fun hc => hB (by
        have h2 := badFlag_match hc
        rwa [κ.match_invol f hf] at h2)
      rw [canonIsOut_of_not_bad hBm, canonIsOut_of_not_bad hB,
        o.match_flip f hf]
  pairing_flip := fun f hf hp => by
    by_cases hB : BadFlag κ o f
    · rw [canonIsOut_of_bad (badFlag_pairing hB hp),
        canonIsOut_of_bad hB, o.pairing_flip f hf hp]
    · have hBp : ¬ BadFlag κ o (W.pairing f) := fun hc => hB (by
        have h2 := badFlag_pairing hc (by
          rw [W.pairing_invol]
          exact hf)
        rwa [W.pairing_invol] at h2)
      rw [canonIsOut_of_not_bad hBp, canonIsOut_of_not_bad hB,
        o.pairing_flip f hf hp]

/-- The repaired orientation's table is that repair. -/
theorem canonOrientation_isOut
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    (o : κ.Orientation) (f : W.Flag) :
    (canonOrientation κ o).isOut f = canonIsOut κ o f := rfl

/-! ### 4. Canonicality of the flipped orientation -/

/-- **The flipped orientation is path-canonical**: at each low-end
entry flag, exit uniqueness pins any badness witness to the entry's
own chain, so the flip decision matches the chain's prior status. -/
theorem pathCanonical_canonOrientation
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    (o : κ.Orientation) : PathCanonical (canonOrientation κ o) := by
  intro i j hb hint hpm hij
  rw [canonOrientation_isOut]
  by_cases hB : BadFlag κ o (W.pairing (W.boundaryFlag i))
  · rw [canonIsOut_of_bad hB]
    obtain ⟨bs, ks, ms, hconts, -, hms, hfes, hncs⟩ := hB
    obtain ⟨hbs, is', js', hais, hajs, hdisjs⟩ := hncs
    obtain ⟨hce, hexit⟩ := chain_flag_exit κ hconts hms
    rw [← hfes] at hce hexit
    have ht₁ : W.pairing
        (iterWalk κ (W.pairing (W.boundaryFlag i)) 0) ∈
          F.boundaryFlags := by
      rw [iterWalk_zero, W.pairing_invol]
      exact hb
    have hms0 : (0 : ℕ) = ms :=
      exit_step_unique κ (fun t ht => absurd ht (Nat.not_lt_zero t))
        ht₁ hce (by rw [hexit]; exact hbs)
    have hbse : bs = W.boundaryFlag i := by
      have h0 := hexit
      rw [← hms0, iterWalk_zero, W.pairing_invol] at h0
      exact h0.symm
    subst hbse
    have hi : i = is' :=
      Sum.inr.inj ((W.attach_boundaryFlag i).symm.trans hais)
    rw [κ.pathMatch_congr rfl hbs hb, hpm] at hajs
    have hj : j = js' :=
      Sum.inr.inj ((W.attach_boundaryFlag j).symm.trans hajs)
    rcases hdisjs with ⟨-, hout⟩ | ⟨hlt, -⟩
    · rw [hout]
      rfl
    · rw [← hi, ← hj] at hlt
      exact absurd (hlt.trans hij) (lt_irrefl j)
  · rw [canonIsOut_of_not_bad hB]
    obtain ⟨k, -, hcont, hterm⟩ := chain_terminates_with_data κ hb
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | h
      · rw [iterWalk_zero] at hterm
        exact absurd hterm (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hint)
      · exact h
    cases hout : o.isOut (W.pairing (W.boundaryFlag i)) with
    | false => rfl
    | true =>
      exact absurd
        (show BadFlag κ o (W.pairing (W.boundaryFlag i)) from
          ⟨W.boundaryFlag i, k, 0, hcont, hterm, hk1,
            by rw [iterWalk_zero],
            ⟨hb, i, j, W.attach_boundaryFlag i,
              by rw [hpm]; exact W.attach_boundaryFlag j,
              Or.inl ⟨hij, hout⟩⟩⟩)
        hB

/-! ### Existence and its canonical-frame form -/

/-- **Existence of path-canonical orientations**: any orientation of
a boundary-relative transition system can be repaired into a
path-canonical orientation of the same system. -/
theorem exists_pathCanonical [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    (o : κ.Orientation) : ∃ o' : κ.Orientation, PathCanonical o' :=
  ⟨canonOrientation κ o, pathCanonical_canonOrientation κ o⟩

end EdgeSubset

end RS
