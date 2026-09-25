/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.RelTransition

/-!
# Path matching on boundary flags

For a boundary-relative transition system `κ : RelTransitionSystem F`,
the alternating paths traced by `traceChain` pair the boundary flags
of the edge subset.  This file constructs the path matching as a
proven involution on boundary flags.

## Main results

* `RelTransitionSystem.pathMatch` — sends each boundary flag to the
  boundary flag at the other end of its alternating chain.
* `pathMatch_mem` — the result is a boundary flag.
* `pathMatch_invol` — `pathMatch` is an involution.

## Proof architecture

Chain termination uses a pigeonhole/backward-injectivity argument on
the pairings visited at each step.  The involution is proved via an
identity on the reverse iterate sequence:
`iterWalk κ b' j = σ(iterWalk κ b (k - j))` (where `b'` is the
chain result and `σ` is the edge pairing), established by induction
on `j` using `match_invol`.
-/

@[expose] public section

namespace RS



variable {α : Type} {W : Fragment α}

namespace EdgeSubset

variable {F : EdgeSubset W}

/-! ### Flag classification helpers -/

private theorem not_boundary_of_internal
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    f ∉ F.boundaryFlags :=
  Finset.disjoint_left.mp F.internalFlags_disjoint_boundaryFlags hf

/-! ### traceChain rewriting lemmas -/

/-- One step of the chain when the flag's edge partner is internal:
match and recurse on one less fuel. -/
theorem traceChain_internal (κ : F.RelTransitionSystem)
    (n : ℕ) (f : W.Flag) (h : W.pairing f ∈ F.internalFlags) :
    traceChain κ (n + 1) f =
      traceChain κ n (κ.match_ (W.pairing f)) := by
  conv_lhs => unfold traceChain
  simp only [ite_eq_right (not_boundary_of_internal h), dite_eq_left h]

/-- The chain stops at the first boundary partner and returns it. -/
theorem traceChain_boundary (κ : F.RelTransitionSystem)
    (n : ℕ) (f : W.Flag) (h : W.pairing f ∈ F.boundaryFlags) :
    traceChain κ (n + 1) f = some (W.pairing f) := by
  conv_lhs => unfold traceChain; simp only [ite_eq_left h]

/-- The chain fails on a partner outside the subset. -/
theorem traceChain_neither (κ : F.RelTransitionSystem)
    (n : ℕ) (f : W.Flag)
    (hb : W.pairing f ∉ F.boundaryFlags)
    (hi : W.pairing f ∉ F.internalFlags) :
    traceChain κ (n + 1) f = none := by
  conv_lhs => unfold traceChain
  simp only [ite_eq_right hb, dite_eq_right hi]

/-! ### Fuel monotonicity -/

/-- Extra fuel does not change a successful result. -/
theorem traceChain_fuel_mono (κ : F.RelTransitionSystem)
    {f g : W.Flag} {n m : ℕ} (hnm : n ≤ m)
    (h : traceChain κ n f = some g) :
    traceChain κ m f = some g := by
  induction n generalizing f m with
  | zero => simp [traceChain] at h
  | succ n ih =>
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [show n + 1 + d = (n + d) + 1 from by omega]
    by_cases hb : W.pairing f ∈ F.boundaryFlags
    · rw [traceChain_boundary κ n f hb] at h
      rw [traceChain_boundary κ (n + d) f hb]; exact h
    · by_cases hi : W.pairing f ∈ F.internalFlags
      · rw [traceChain_internal κ n f hi] at h
        rw [traceChain_internal κ (n + d) f hi]
        exact ih (Nat.le_add_right n d) h
      · rw [traceChain_neither κ n f hb hi] at h; cases h

/-! ### Result is boundary -/

/-- A chain that succeeds ends at a boundary flag. -/
theorem traceChain_result_boundary (κ : F.RelTransitionSystem)
    {f g : W.Flag} {n : ℕ}
    (h : traceChain κ n f = some g) : g ∈ F.boundaryFlags := by
  induction n generalizing f with
  | zero => simp [traceChain] at h
  | succ n ih =>
    by_cases hb : W.pairing f ∈ F.boundaryFlags
    · rw [traceChain_boundary κ n f hb] at h
      exact (Option.some.inj h) ▸ hb
    · by_cases hi : W.pairing f ∈ F.internalFlags
      · rw [traceChain_internal κ n f hi] at h; exact ih h
      · rw [traceChain_neither κ n f hb hi] at h; cases h

/-! ### Iterated walk -/

/-- The fuel-free chain step iterated: cross the edge, then match.
This is `traceChain`'s recursion without the termination test, so
the two can be compared step by step. -/
noncomputable def iterWalk (κ : F.RelTransitionSystem)
    (f : W.Flag) : ℕ → W.Flag
  | 0 => f
  | n + 1 => κ.match_ (W.pairing (iterWalk κ f n))

/-- No steps leave the flag where it is. -/
@[simp] theorem iterWalk_zero (κ : F.RelTransitionSystem)
    (f : W.Flag) : iterWalk κ f 0 = f := rfl

/-- One more step: cross the edge from the current flag, then
match. -/
theorem iterWalk_succ (κ : F.RelTransitionSystem)
    (f : W.Flag) (n : ℕ) :
    iterWalk κ f (n + 1) =
      κ.match_ (W.pairing (iterWalk κ f n)) := rfl

/-- Splitting an iterated walk. -/
theorem iterWalk_add (κ : F.RelTransitionSystem) (f : W.Flag)
    (a b : ℕ) :
    iterWalk κ f (a + b) = iterWalk κ (iterWalk κ f a) b := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 from rfl, iterWalk_succ,
      ih, ← iterWalk_succ]

/-- Starting one step along is the same as taking one more step. -/
theorem iterWalk_shift (κ : F.RelTransitionSystem)
    (f : W.Flag) (k : ℕ) :
    iterWalk κ (κ.match_ (W.pairing f)) k =
      iterWalk κ f (k + 1) := by
  induction k with
  | zero => simp [iterWalk]
  | succ k ih => simp only [iterWalk, ih]

/-- While the chain continues, every flag it reaches after the first
step is internal. -/
theorem iterWalk_mem_internal (κ : F.RelTransitionSystem)
    {b : W.Flag} (k : ℕ) {j : ℕ} (hj : 1 ≤ j)
    (hjk : j ≤ k)
    (hcont : ∀ i, i < k →
      W.pairing (iterWalk κ b i) ∈ F.internalFlags) :
    iterWalk κ b j ∈ F.internalFlags := by
  cases j with
  | zero => omega
  | succ j' =>
    rw [iterWalk_succ]
    exact κ.match_mem _ (hcont j' (by omega))

/-! ### match_ injectivity on internal flags -/

/-- The matching is injective on internal flags, being an
involution there. -/
theorem RelTransitionSystem.match_injOn
    (κ : F.RelTransitionSystem) {x y : W.Flag}
    (hx : x ∈ F.internalFlags) (hy : y ∈ F.internalFlags)
    (h : κ.match_ x = κ.match_ y) : x = y :=
  calc x = κ.match_ (κ.match_ x) := (κ.match_invol x hx).symm
    _ = κ.match_ (κ.match_ y) := by rw [h]
    _ = y := κ.match_invol y hy

/-! ### Chain unfolding -/

/-- Splitting the fuel: `k` steps of a continuing chain can be run
first, leaving the rest of the chain from the flag reached. -/
theorem traceChain_unfold (κ : F.RelTransitionSystem)
    (f : W.Flag) (k m : ℕ)
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags) :
    traceChain κ (k + m + 1) f =
      traceChain κ (m + 1) (iterWalk κ f k) := by
  induction k generalizing f with
  | zero => simp [iterWalk]
  | succ k ih =>
    have h0 := hcont 0 (by omega)
    simp only [iterWalk_zero] at h0
    rw [show k + 1 + m + 1 = (k + m + 1) + 1 from by omega]
    rw [traceChain_internal κ (k + m + 1) f h0]
    rw [ih _ (fun j hj => by
      rw [iterWalk_shift]; exact hcont (j + 1) (by omega))]
    congr 1; exact iterWalk_shift κ f k

/-! ### Backward injectivity -/

/-- **A continuing chain never revisits a flag.**  A repeat would
force the matching to send two distinct internal flags to the same
place, or the chain to re-enter its own boundary start. -/
theorem iterWalk_no_repeat (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) (k : ℕ)
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    (i d : ℕ) (hd : 1 ≤ d) (hidk : i + d ≤ k)
    (heq : iterWalk κ b i = iterWalk κ b (i + d)) :
    False := by
  induction i with
  | zero =>
    simp only [Nat.zero_add] at heq hidk
    have hmem : iterWalk κ b d ∈ F.internalFlags :=
      iterWalk_mem_internal κ k hd hidk
        (fun j hj => hcont j (by omega))
    rw [← heq] at hmem
    exact not_boundary_of_internal hmem hb
  | succ i ih =>
    apply ih (by omega)
    rw [iterWalk_succ,
        show i + 1 + d = (i + d) + 1 from by omega,
        iterWalk_succ] at heq
    have hm1 := hcont i (by omega)
    have hm2 := hcont (i + d) (by omega)
    calc iterWalk κ b i
        = W.pairing (W.pairing (iterWalk κ b i)) :=
          (W.pairing_invol _).symm
      _ = W.pairing (W.pairing (iterWalk κ b (i + d))) :=
          by rw [κ.match_injOn hm1 hm2 heq]
      _ = iterWalk κ b (i + d) := W.pairing_invol _

/-- The edge partners visited by a continuing chain are pairwise
distinct — the pigeonhole input for termination. -/
theorem pairing_iterWalk_injective
    (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) (k : ℕ)
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    {i j : ℕ} (hi : i < k) (hj : j < k)
    (heq : W.pairing (iterWalk κ b i) =
      W.pairing (iterWalk κ b j)) : i = j := by
  by_cases hij : i ≤ j
  · by_contra hne
    have heq_iter : iterWalk κ b i = iterWalk κ b j :=
      calc iterWalk κ b i
          = W.pairing (W.pairing (iterWalk κ b i)) :=
            (W.pairing_invol _).symm
        _ = W.pairing (W.pairing (iterWalk κ b j)) :=
            by rw [heq]
        _ = iterWalk κ b j := W.pairing_invol _
    exact absurd (iterWalk_no_repeat κ hb k hcont
      i (j - i) (by omega) (by omega)
      (by rwa [Nat.add_sub_cancel' hij])) not_false
  · by_contra _hne
    have heq_iter : iterWalk κ b j = iterWalk κ b i :=
      calc iterWalk κ b j
          = W.pairing (W.pairing (iterWalk κ b j)) :=
            (W.pairing_invol _).symm
        _ = W.pairing (W.pairing (iterWalk κ b i)) :=
            by rw [← heq]
        _ = iterWalk κ b i := W.pairing_invol _
    exact absurd (iterWalk_no_repeat κ hb k hcont
      j (i - j) (by omega) (by omega)
      (by rwa [Nat.add_sub_cancel' (by omega : j ≤ i)]))
      not_false

/-! ### Chain termination with data -/

private theorem pairing_iterWalk_mem_flags
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags) (j : ℕ)
    (hcont : ∀ i, i < j →
      W.pairing (iterWalk κ b i) ∈ F.internalFlags) :
    W.pairing (iterWalk κ b j) ∈ F.flags := by
  cases j with
  | zero =>
    exact F.pairing_mem b (mem_flags_of_boundaryFlags F hb)
  | succ j =>
    exact F.pairing_mem _
      (mem_flags_of_internalFlags F
        (iterWalk_mem_internal κ (j + 1) (by omega) (by omega)
          (fun i hi => hcont i (by omega))))

/-- **The chain terminates**, within `F.flags.card` steps, at a
boundary partner: the visited partners are distinct and there are
only that many flags. -/
theorem chain_terminates_with_data
    (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) :
    ∃ k, k ≤ F.flags.card ∧
      (∀ j, j < k →
        W.pairing (iterWalk κ b j) ∈ F.internalFlags) ∧
      W.pairing (iterWalk κ b k) ∈ F.boundaryFlags := by
  have hex : ∃ k, k ≤ F.flags.card ∧
      W.pairing (iterWalk κ b k) ∉ F.internalFlags := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hinj : Function.Injective
        (fun (i : Fin (F.flags.card + 1)) =>
          (⟨W.pairing (iterWalk κ b i.val),
            hall i.val (by omega)⟩ :
            {f : W.Flag // f ∈ F.internalFlags})) := by
      intro ⟨i, hi⟩ ⟨j, hj⟩ h
      simp only [Subtype.mk.injEq] at h
      exact Fin.ext (pairing_iterWalk_injective κ hb
        (F.flags.card + 1)
        (fun j hj => hall j (by omega))
        (by omega) (by omega) h)
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin, Fintype.card_coe] at hcard
    have hsub : F.internalFlags.card ≤ F.flags.card :=
      Finset.card_le_card
        (fun f hf => mem_flags_of_internalFlags F hf)
    omega
  have hex' : ∃ k, W.pairing (iterWalk κ b k) ∉
      F.internalFlags := ⟨_, hex.choose_spec.2⟩
  have : DecidablePred (fun k =>
      W.pairing (iterWalk κ b k) ∉ F.internalFlags) :=
    fun k => Classical.dec _
  set k₀ := Nat.find hex'
  have hk₀_spec := Nat.find_spec hex'
  have hk₀_min : ∀ j, j < k₀ →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags :=
    fun j hj => not_not.mp (Nat.find_min hex' hj)
  obtain ⟨k, hk_le, hk_not⟩ := hex
  have hk₀_le : k₀ ≤ F.flags.card :=
    (Nat.find_min' hex' hk_not).trans hk_le
  have hmem := pairing_iterWalk_mem_flags κ hb k₀ hk₀_min
  exact ⟨k₀, hk₀_le, hk₀_min,
    (F.mem_internalFlags_or_boundaryFlags hmem).resolve_left
      hk₀_spec⟩

/-! ### traceChain terminates -/

/-- With `F.flags.card + 1` fuel every chain from a boundary flag
succeeds. -/
theorem traceChain_terminates (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) :
    ∃ g, traceChain κ (F.flags.card + 1) b = some g := by
  obtain ⟨k, hk_le, hcont, hterm⟩ :=
    chain_terminates_with_data κ hb
  have hfwd : traceChain κ (k + 1) b =
      some (W.pairing (iterWalk κ b k)) := by
    rw [show k + 1 = k + 0 + 1 from by omega,
      traceChain_unfold κ b k 0 hcont]
    exact traceChain_boundary κ 0 _ hterm
  exact ⟨_, traceChain_fuel_mono κ (by omega) hfwd⟩

/-! ### pathMatch definition -/

/-- **The path matching**: the boundary flag at the other end of a
boundary flag's alternating chain. -/
noncomputable def RelTransitionSystem.pathMatch
    (κ : F.RelTransitionSystem) (b : W.Flag)
    (hb : b ∈ F.boundaryFlags) : W.Flag :=
  (traceChain κ (F.flags.card + 1) b).get
    (by rw [Option.isSome_iff_exists]
        exact traceChain_terminates κ hb)

/-- Reading `pathMatch` off any successful trace at the standard
fuel. -/
theorem RelTransitionSystem.pathMatch_eq
    (κ : F.RelTransitionSystem) {b g : W.Flag}
    (hb : b ∈ F.boundaryFlags)
    (h : traceChain κ (F.flags.card + 1) b = some g) :
    κ.pathMatch b hb = g := by
  unfold RelTransitionSystem.pathMatch; simp [h]

/-- The path matching lands in the boundary flags. -/
theorem RelTransitionSystem.pathMatch_mem
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags) :
    κ.pathMatch b hb ∈ F.boundaryFlags := by
  unfold RelTransitionSystem.pathMatch
  exact traceChain_result_boundary κ (Option.get_mem _)

/-! ### Forward/reverse chain helpers -/

/-- A chain that continues for `k` steps and then meets a boundary
partner traces to that partner. -/
theorem traceChain_forward (κ : F.RelTransitionSystem)
    (b : W.Flag) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ b k) ∈
      F.boundaryFlags) :
    traceChain κ (k + 1) b =
      some (W.pairing (iterWalk κ b k)) := by
  rw [show k + 1 = k + 0 + 1 from by omega,
    traceChain_unfold κ b k 0 hcont]
  exact traceChain_boundary κ 0 _ hterm

/-- **The reverse-iterate identity**: walking back from the chain's
far end retraces the forward walk under the edge pairing.  This is
what makes the path matching an involution. -/
theorem iterWalk_reverse (κ : F.RelTransitionSystem)
    {b : W.Flag} {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    (j : ℕ) (hjk : j ≤ k) :
    iterWalk κ (W.pairing (iterWalk κ b k)) j =
      W.pairing (iterWalk κ b (k - j)) := by
  induction j with
  | zero => simp [iterWalk]
  | succ j ih =>
    rw [iterWalk_succ, ih (by omega),
      show k - j = (k - (j + 1)) + 1 from by omega,
      iterWalk_succ, W.pairing_invol]
    exact κ.match_invol _
      (hcont (k - (j + 1)) (by omega))

/-- The reversed chain continues wherever the forward one did. -/
theorem reverse_chain_continues
    (κ : F.RelTransitionSystem)
    {b : W.Flag} (_hb : b ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    (j : ℕ) (hjk : j < k) :
    W.pairing
      (iterWalk κ (W.pairing (iterWalk κ b k)) j) ∈
        F.internalFlags := by
  rw [iterWalk_reverse κ hcont j (by omega),
    W.pairing_invol]
  exact iterWalk_mem_internal κ k (by omega) (by omega)
    (fun i hi => hcont i (by omega))

/-- The reversed chain arrives back at the original start. -/
theorem reverse_chain_terminates
    (κ : F.RelTransitionSystem)
    {b : W.Flag} {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags) :
    W.pairing
      (iterWalk κ (W.pairing (iterWalk κ b k)) k) =
        b := by
  rw [iterWalk_reverse κ hcont k (le_refl k)]
  simp [W.pairing_invol]

/-! ### Involution -/

/-- The trace from the far end returns the original boundary
flag. -/
theorem traceChain_reverse (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ b j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ b k) ∈
      F.boundaryFlags) :
    traceChain κ (k + 1)
      (W.pairing (iterWalk κ b k)) = some b := by
  cases k with
  | zero =>
    simp only [iterWalk_zero] at hterm ⊢
    have hpb : W.pairing (W.pairing b) ∈
        F.boundaryFlags := by
      rw [W.pairing_invol]; exact hb
    have h := traceChain_boundary κ 0 (W.pairing b) hpb
    rwa [W.pairing_invol] at h
  | succ k =>
    rw [show k + 1 + 1 = (k + 1) + 0 + 1 from by omega,
      traceChain_unfold κ _ (k + 1) 0
        (reverse_chain_continues κ hb hcont)]
    have hrt := reverse_chain_terminates κ hcont
    have hpb : W.pairing
        (iterWalk κ (W.pairing (iterWalk κ b (k + 1)))
          (k + 1)) ∈ F.boundaryFlags := by
      rw [hrt]; exact hb
    have h := traceChain_boundary κ 0 _ hpb
    rwa [hrt] at h

/-- **The path matching is an involution**: it pairs the boundary
flags of the subset. -/
theorem RelTransitionSystem.pathMatch_invol
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags) :
    κ.pathMatch (κ.pathMatch b hb)
      (κ.pathMatch_mem hb) = b := by
  obtain ⟨k, hk_le, hcont, hterm⟩ :=
    chain_terminates_with_data κ hb
  have hfwd := traceChain_forward κ b hcont hterm
  have hpm : κ.pathMatch b hb =
      W.pairing (iterWalk κ b k) :=
    κ.pathMatch_eq hb
      (traceChain_fuel_mono κ (by omega) hfwd)
  have hrev := traceChain_reverse κ hb hcont hterm
  have hchain :
      traceChain κ (F.flags.card + 1)
        (κ.pathMatch b hb) = some b := by
    rw [hpm]
    exact traceChain_fuel_mono κ (by omega) hrev
  exact κ.pathMatch_eq (κ.pathMatch_mem hb) hchain

/-! ### Self-matching analysis -/

/-- A boundary flag whose edge partner is also boundary is matched
to that partner: the chain has no internal steps. -/
theorem RelTransitionSystem.pathMatch_eq_pairing
    (κ : F.RelTransitionSystem) {b : W.Flag}
    (hb : b ∈ F.boundaryFlags)
    (hp : W.pairing b ∈ F.boundaryFlags) :
    κ.pathMatch b hb = W.pairing b :=
  κ.pathMatch_eq hb
    (traceChain_fuel_mono κ (by omega)
      (traceChain_boundary κ 0 b hp))

/-! ### Interaction lemmas -/

/-- The path matching, together with the length of the chain that
produced it and the continuation data along the way — the form
downstream chain arguments consume. -/
theorem pathMatch_chain_length
    (κ : F.RelTransitionSystem)
    {b : W.Flag} (hb : b ∈ F.boundaryFlags) :
    ∃ k, k ≤ F.flags.card ∧
      (∀ j, j < k →
        W.pairing (iterWalk κ b j) ∈
          F.internalFlags) ∧
      κ.pathMatch b hb =
        W.pairing (iterWalk κ b k) := by
  obtain ⟨k, hk_le, hcont, hterm⟩ :=
    chain_terminates_with_data κ hb
  exact ⟨k, hk_le, hcont, κ.pathMatch_eq hb
    (traceChain_fuel_mono κ (by omega)
      (traceChain_forward κ b hcont hterm))⟩

end EdgeSubset

end RS
