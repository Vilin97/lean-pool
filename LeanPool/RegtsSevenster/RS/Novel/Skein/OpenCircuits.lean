/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.PathMatch

/-!
# Open circuit count for boundary-relative transition systems

For an edge subset `F` that may have boundary flags, the internal
circuit count (`internalCircuitCount`) is defined only when
`F.allInternal` holds.  This file generalises the count to open
edge subsets by restricting to the *periodic* flags — internal flags
whose forward walk eventually returns to them.

## Main definitions

* `PeriodicFlag` — a flag on a closed circuit: internal, with the
  walk staying internal and returning to it.
* `periodicFlags` — the finset of periodic flags.
* `walkPermPeriodic` — the walk restricted to periodic flags as a
  permutation.
* `openCircuitCount` — `(cycleType.card + fixedPoints) / 2` on
  periodic flags.

## Main results

* `openCircuitCount_of_allInternal` — when all flags are internal
  the open and internal circuit counts agree.
* `internal_periodic_or_terminates` — every internal flag is either
  periodic or its chain reaches the boundary.
* `not_periodic_of_boundary_chain` — boundary-terminating flags are
  not periodic.
-/

@[expose] public section

namespace RS



variable {α : Type} {W : Fragment α}

namespace EdgeSubset

variable {F : EdgeSubset W}

/-! ### 1. PeriodicFlag -/

/-- A flag on a closed circuit: it is internal, every intermediate
pairing stays internal, and the walk returns to it. -/
def RelTransitionSystem.PeriodicFlag
    (κ : F.RelTransitionSystem) (f : W.Flag) : Prop :=
  f ∈ F.internalFlags ∧
    ∃ n : ℕ, 1 ≤ n ∧
      (∀ j, j < n →
        W.pairing (iterWalk κ f j) ∈ F.internalFlags) ∧
      iterWalk κ f n = f

/-- A periodic flag is internal. -/
theorem RelTransitionSystem.PeriodicFlag.mem_internal
    {κ : F.RelTransitionSystem} {f : W.Flag}
    (hf : κ.PeriodicFlag f) : f ∈ F.internalFlags :=
  hf.1

/-! #### Periodicity helpers -/

/-- Shift a period: `iterWalk κ f (n + k) = iterWalk κ f k` when
`iterWalk κ f n = f` and all intermediate pairings are internal. -/
theorem iterWalk_add_period (κ : F.RelTransitionSystem)
    (f : W.Flag) (n k : ℕ)
    (hperiod : iterWalk κ f n = f)
    (_hcont : ∀ j, j < n →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags) :
    iterWalk κ f (n + k) = iterWalk κ f k := by
  induction k with
  | zero => simp [hperiod]
  | succ k ih =>
    rw [show n + (k + 1) = (n + k) + 1 from by omega,
      iterWalk_succ, ih, ← iterWalk_succ]

/-- All pairings along a periodic walk are internal. -/
theorem all_pairings_internal_of_periodic
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (hper : κ.PeriodicFlag f) (j : ℕ) :
    W.pairing (iterWalk κ f j) ∈ F.internalFlags := by
  obtain ⟨_, n, hn1, hcont, hperiod⟩ := hper
  have hmod : ∀ k, k < n →
      iterWalk κ f (n * (j / n) + k) = iterWalk κ f k := by
    intro k _hkn
    induction j / n with
    | zero => simp
    | succ m ih =>
      rw [show n * (m + 1) + k = n + (n * m + k) from by ring]
      rw [iterWalk_add_period κ f n (n * m + k) hperiod hcont]
      exact ih
  rw [show j = n * (j / n) + j % n from
    (Nat.div_add_mod j n).symm]
  rw [hmod (j % n) (Nat.mod_lt j (by omega))]
  exact hcont (j % n) (Nat.mod_lt j (by omega))

/-- All iterates along a periodic walk are internal. -/
theorem iterWalk_mem_internal_of_periodic
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (hper : κ.PeriodicFlag f) (j : ℕ) (hj : 1 ≤ j) :
    iterWalk κ f j ∈ F.internalFlags := by
  cases j with
  | zero => omega
  | succ j =>
    rw [iterWalk_succ]
    exact κ.match_mem _
      (all_pairings_internal_of_periodic κ hper j)

/-- The walk-successor of a periodic flag is periodic (same period). -/
theorem RelTransitionSystem.periodicFlag_step
    {κ : F.RelTransitionSystem} {f : W.Flag}
    (hf : κ.PeriodicFlag f) :
    κ.PeriodicFlag (iterWalk κ f 1) := by
  have hmem := hf.1
  obtain ⟨_, n, hn1, hcont, hperiod⟩ := hf
  have hf' : κ.PeriodicFlag f := ⟨hmem, n, hn1, hcont, hperiod⟩
  refine ⟨iterWalk_mem_internal_of_periodic κ hf' 1 (by omega),
    n, hn1, fun j hj => ?_, ?_⟩
  · -- iterWalk κ f 1 is definitionally κ.match_ (W.pairing f)
    change W.pairing (iterWalk κ (κ.match_ (W.pairing f)) j) ∈
      F.internalFlags
    rw [iterWalk_shift]
    exact all_pairings_internal_of_periodic κ hf' (j + 1)
  · change iterWalk κ (κ.match_ (W.pairing f)) n =
      κ.match_ (W.pairing f)
    rw [iterWalk_shift, iterWalk_succ, hperiod]

/-! ### 2. periodicFlags -/

open scoped Classical in
/-- The finset of periodic flags. -/
noncomputable def RelTransitionSystem.periodicFlags
    (κ : F.RelTransitionSystem) : Finset W.Flag :=
  F.internalFlags.filter (fun f =>
    ∃ n : ℕ, 1 ≤ n ∧
      (∀ j, j < n →
        W.pairing (iterWalk κ f j) ∈ F.internalFlags) ∧
      iterWalk κ f n = f)

/-- Membership in periodicFlags iff PeriodicFlag. -/
theorem RelTransitionSystem.mem_periodicFlags
    (κ : F.RelTransitionSystem) {f : W.Flag} :
    f ∈ κ.periodicFlags ↔ κ.PeriodicFlag f := by
  simp only [RelTransitionSystem.periodicFlags,
    Finset.mem_filter, RelTransitionSystem.PeriodicFlag]

/-- A periodic flag is internal. -/
theorem RelTransitionSystem.periodicFlags_sub
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (hf : f ∈ κ.periodicFlags) : f ∈ F.internalFlags :=
  ((κ.mem_periodicFlags).mp hf).1

/-! ### Walk closure on periodic flags -/

/-- The walk maps periodic flags to periodic flags. -/
theorem RelTransitionSystem.internalWalk_periodic
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (hf : f ∈ κ.periodicFlags) :
    κ.internalWalk f ∈ κ.periodicFlags := by
  rw [κ.mem_periodicFlags] at hf ⊢
  change κ.PeriodicFlag (κ.match_ (W.pairing f))
  rw [show κ.match_ (W.pairing f) = iterWalk κ f 1 from rfl]
  exact κ.periodicFlag_step hf

/-- The walk is injective on periodic flags. -/
theorem RelTransitionSystem.internalWalk_injOn_periodic
    (κ : F.RelTransitionSystem) {f g : W.Flag}
    (hf : f ∈ κ.periodicFlags) (hg : g ∈ κ.periodicFlags)
    (h : κ.internalWalk f = κ.internalWalk g) : f = g := by
  have hfi := κ.periodicFlags_sub hf
  have hgi := κ.periodicFlags_sub hg
  have hpf : W.pairing f ∈ F.internalFlags :=
    all_pairings_internal_of_periodic κ
      (κ.mem_periodicFlags.mp hf) 0
  have hpg : W.pairing g ∈ F.internalFlags :=
    all_pairings_internal_of_periodic κ
      (κ.mem_periodicFlags.mp hg) 0
  exact κ.internalWalk_injOn hfi hgi hpf hpg h

/-! ### 3. walkPermPeriodic -/

/-- The walk permutation restricted to periodic flags. -/
noncomputable def RelTransitionSystem.walkPermPeriodic
    (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ κ.periodicFlags} :=
  Equiv.ofBijective
    (fun f => ⟨κ.internalWalk f.val,
      κ.internalWalk_periodic f.prop⟩)
    (Finite.injective_iff_bijective.mp
      (fun f g h => Subtype.ext
        (κ.internalWalk_injOn_periodic f.prop g.prop
          (congrArg Subtype.val h))))

/-! ### 4. openCircuitCount -/

/-- The open circuit count: half the orbit count of the walk on
periodic flags. -/
noncomputable def RelTransitionSystem.openCircuitCount
    (κ : F.RelTransitionSystem) : ℕ :=
  (κ.walkPermPeriodic.cycleType.card +
    Fintype.card
      (Function.fixedPoints κ.walkPermPeriodic)) / 2

/-! ### Backward period extraction -/

/-- If the walk repeats at positions `i` and `i + d` (with all
intermediate pairings internal), then it has period `d` from
position 0. -/
theorem iterWalk_period_of_repeat
    (κ : F.RelTransitionSystem) (f : W.Flag)
    (i d : ℕ) (_hd : 1 ≤ d)
    (hcont : ∀ j, j < i + d →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags)
    (heq : iterWalk κ f i = iterWalk κ f (i + d)) :
    iterWalk κ f d = f := by
  induction i with
  | zero => simp at heq; exact heq.symm
  | succ i ih =>
    apply ih (fun j hj => hcont j (by omega))
    rw [iterWalk_succ,
      show i + 1 + d = (i + d) + 1 from by omega,
      iterWalk_succ] at heq
    have hm1 := hcont i (by omega)
    have hm2 := hcont (i + d) (by omega)
    calc iterWalk κ f i
        = W.pairing (W.pairing (iterWalk κ f i)) :=
          (W.pairing_invol _).symm
      _ = W.pairing (W.pairing (iterWalk κ f (i + d))) :=
          by rw [κ.match_injOn hm1 hm2 heq]
      _ = iterWalk κ f (i + d) := W.pairing_invol _

/-! ### Pigeonhole period extraction -/

/-- Helper for the pigeonhole argument: given a non-injective
map from `Fin (n+1)` to a type, extract a collision. -/
private theorem exists_collision_of_not_injective
    {α : Type*} {n : ℕ} {g : Fin (n + 1) → α}
    (h : ¬ Function.Injective g) :
    ∃ (i j : Fin (n + 1)), i ≠ j ∧ g i = g j := by
  by_contra hall
  apply h
  intro a b hab
  by_contra hne
  exact hall ⟨a, b, hne, hab⟩

/-! ### 5. Compatibility with internalCircuitCount -/

/-- Under `allInternal`, every internal flag is periodic (via
pigeonhole on the walk iterates). -/
theorem periodic_of_allInternal
    (κ : F.RelTransitionSystem) (hall : F.allInternal)
    {f : W.Flag} (hf : f ∈ F.internalFlags) :
    κ.PeriodicFlag f := by
  refine ⟨hf, ?_⟩
  -- Under allInternal, all iterates are internal.
  have hmem : ∀ j, iterWalk κ f j ∈ F.internalFlags := by
    intro j
    induction j with
    | zero => exact hf
    | succ j ih =>
      rw [iterWalk_succ]
      exact κ.match_mem _
        (κ.pairing_internal_of_allInternal hall ih)
  have hcont_all : ∀ j,
      W.pairing (iterWalk κ f j) ∈ F.internalFlags :=
    fun j => κ.pairing_internal_of_allInternal hall (hmem j)
  -- Pigeonhole: N+1 iterates in a set of size N.
  set N := F.internalFlags.card
  have hinj_false : ¬ Function.Injective
      (fun (i : Fin (N + 1)) =>
        (⟨iterWalk κ f i.val, hmem i.val⟩ :
          {g : W.Flag // g ∈ F.internalFlags})) := by
    intro hinj
    have hcard := Fintype.card_le_of_injective _ hinj
    rw [Fintype.card_fin, Fintype.card_coe] at hcard
    omega
  obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne, heq_sub⟩ :=
    exists_collision_of_not_injective hinj_false
  have heq : iterWalk κ f i = iterWalk κ f j :=
    congrArg Subtype.val heq_sub
  have hne_val : i ≠ j := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne_val with hij | hij
  · exact ⟨j - i, by omega,
      fun k _ => hcont_all k,
      iterWalk_period_of_repeat κ f i (j - i) (by omega)
        (fun k _ => hcont_all k)
        (by rw [Nat.add_sub_cancel' hij.le]; exact heq)⟩
  · exact ⟨i - j, by omega,
      fun k _ => hcont_all k,
      iterWalk_period_of_repeat κ f j (i - j) (by omega)
        (fun k _ => hcont_all k)
        (by rw [Nat.add_sub_cancel' hij.le]; exact heq.symm)⟩

/-- The equivalence between periodic-flag and internal-flag subtypes
under `allInternal`. -/
noncomputable def periodicEquivInternal
    (κ : F.RelTransitionSystem) (hall : F.allInternal) :
    {f : W.Flag // f ∈ κ.periodicFlags} ≃
      {f : W.Flag // f ∈ F.internalFlags} where
  toFun g := ⟨g.val, κ.periodicFlags_sub g.prop⟩
  invFun g := ⟨g.val, (κ.mem_periodicFlags).mpr
    (periodic_of_allInternal κ hall g.prop)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- The two walk permutations agree under the canonical equivalence. -/
theorem walkPermPeriodic_eq_of_allInternal
    (κ : F.RelTransitionSystem) (hall : F.allInternal) :
    κ.walkPermPeriodic =
      (periodicEquivInternal κ hall).symm.permCongr
        (κ.walkPermInternal hall) := by
  ext ⟨f, hf⟩
  -- Goal after ext: ↑(walkPermPeriodic ⟨f, hf⟩) = ↑(permCongr ... ⟨f, hf⟩)
  -- Both sides have .val = κ.internalWalk f
  simp only [RelTransitionSystem.walkPermPeriodic,
    RelTransitionSystem.walkPermInternal,
    Equiv.ofBijective_apply, Equiv.permCongr_apply,
    Equiv.symm_symm, periodicEquivInternal]
  rfl

/-- **Compatibility**: for a closed edge subset, `openCircuitCount`
equals `internalCircuitCount`. -/
theorem openCircuitCount_of_allInternal
    {F : EdgeSubset W} (κ : F.RelTransitionSystem)
    (hall : F.allInternal) :
    κ.openCircuitCount = κ.internalCircuitCount hall := by
  unfold RelTransitionSystem.openCircuitCount
    RelTransitionSystem.internalCircuitCount
  rw [walkPermPeriodic_eq_of_allInternal κ hall,
    cycleType_permCongr, card_fixedPoints_permCongr]

/-! ### 6. Boundary paths are not periodic -/

/-- The chain from a flag with all-internal pairings always returns
`none` (never reaches the boundary). -/
theorem traceChain_none_of_all_internal_pairings
    (κ : F.RelTransitionSystem) {f : W.Flag}
    (h : ∀ j, W.pairing (iterWalk κ f j) ∈ F.internalFlags)
    (fuel : ℕ) : traceChain κ fuel f = none := by
  induction fuel generalizing f with
  | zero => rfl
  | succ n ih =>
    have h0 := h 0
    simp only [iterWalk_zero] at h0
    rw [traceChain_internal κ n f h0]
    exact ih (fun j => by
      show W.pairing (iterWalk κ (κ.match_ (W.pairing f)) j) ∈
        F.internalFlags
      rw [iterWalk_shift]; exact h (j + 1))

/-- A flag whose chain reaches the boundary is not periodic. -/
theorem not_periodic_of_boundary_chain
    (κ : F.RelTransitionSystem) (f : W.Flag)
    (_hf : f ∈ F.internalFlags)
    (hterm : ∃ fuel b, traceChain κ fuel f = some b) :
    ¬ κ.PeriodicFlag f := by
  intro hper
  obtain ⟨fuel, b, hfuel⟩ := hterm
  have := traceChain_none_of_all_internal_pairings κ
    (all_pairings_internal_of_periodic κ hper) fuel
  rw [this] at hfuel; cases hfuel

/-! #### Dichotomy: periodic or boundary-terminating -/

/-- Every internal flag is either periodic or its chain reaches the
boundary. -/
theorem internal_periodic_or_terminates
    (κ : F.RelTransitionSystem) (f : W.Flag)
    (hf : f ∈ F.internalFlags) :
    κ.PeriodicFlag f ∨
      (∃ fuel b, traceChain κ fuel f = some b) := by
  set N := F.internalFlags.card
  -- Does the walk ever exit to a non-internal pairing?
  by_cases hexall : ∀ j,
      W.pairing (iterWalk κ f j) ∈ F.internalFlags
  · -- Walk stays internal forever. Pigeonhole gives periodicity.
    left
    have hmem : ∀ j, iterWalk κ f j ∈ F.internalFlags := by
      intro j; cases j with
      | zero => exact hf
      | succ j =>
        rw [iterWalk_succ]
        exact κ.match_mem _ (hexall j)
    have hinj_false : ¬ Function.Injective
        (fun (i : Fin (N + 1)) =>
          (⟨iterWalk κ f i.val, hmem i.val⟩ :
            {g : W.Flag // g ∈ F.internalFlags})) := by
      intro hinj
      have hcard := Fintype.card_le_of_injective _ hinj
      rw [Fintype.card_fin, Fintype.card_coe] at hcard
      omega
    obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hne, heq_sub⟩ :=
      exists_collision_of_not_injective hinj_false
    have heq : iterWalk κ f i = iterWalk κ f j :=
      congrArg Subtype.val heq_sub
    have hne_val : i ≠ j := fun h => hne (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne_val with hij | hij
    · exact ⟨hf, j - i, by omega,
        fun k _ => hexall k,
        iterWalk_period_of_repeat κ f i (j - i) (by omega)
          (fun k _ => hexall k)
          (by rw [Nat.add_sub_cancel' hij.le]; exact heq)⟩
    · exact ⟨hf, i - j, by omega,
        fun k _ => hexall k,
        iterWalk_period_of_repeat κ f j (i - j) (by omega)
          (fun k _ => hexall k)
          (by rw [Nat.add_sub_cancel' hij.le];
              exact heq.symm)⟩
  · -- Walk exits at some step. Find the first exit.
    right
    simp only [not_forall] at hexall
    have : DecidablePred (fun k =>
        W.pairing (iterWalk κ f k) ∉ F.internalFlags) :=
      fun k => Classical.dec _
    have hk₀_spec := Nat.find_spec hexall
    have hk₀_min : ∀ j, j < Nat.find hexall →
        W.pairing (iterWalk κ f j) ∈ F.internalFlags :=
      fun j hj => by
        by_contra h; exact Nat.find_min hexall hj h
    -- iterWalk κ f (Nat.find hexall) is internal
    have hk₀_mem :
        iterWalk κ f (Nat.find hexall) ∈ F.internalFlags := by
      rcases Nat.eq_zero_or_pos (Nat.find hexall) with h | h
      · rw [h]; exact hf
      · exact iterWalk_mem_internal κ (Nat.find hexall)
          h le_rfl hk₀_min
    have hk₀_flags :
        W.pairing (iterWalk κ f (Nat.find hexall)) ∈ F.flags :=
      F.pairing_mem _ (mem_flags_of_internalFlags F hk₀_mem)
    have hk₀_bdry :
        W.pairing (iterWalk κ f (Nat.find hexall)) ∈
          F.boundaryFlags :=
      (F.mem_internalFlags_or_boundaryFlags hk₀_flags
        ).resolve_left hk₀_spec
    exact ⟨Nat.find hexall + 1,
      W.pairing (iterWalk κ f (Nat.find hexall)),
      traceChain_forward κ f hk₀_min hk₀_bdry⟩

/-! ### The edge-pairing reversal on periodic flags

Reversing every periodic flag along its own edge conjugates the walk
permutation into its inverse, which is what makes the open circuits
come in pairs.
-/

/-- The periodic flags are closed under the edge pairing: a closed
circuit's edges lie wholly on it. -/
theorem pairing_mem_periodicFlags (κ : F.RelTransitionSystem)
    {f : W.Flag} (hf : f ∈ κ.periodicFlags) :
    W.pairing f ∈ κ.periodicFlags := by
  have hper := κ.mem_periodicFlags.mp hf
  obtain ⟨hint, n, hn1, hcont, hperiod⟩ := hper
  have hper' : κ.PeriodicFlag f :=
    ⟨hint, n, hn1, hcont, hperiod⟩
  have hcont_all : ∀ j,
      W.pairing (iterWalk κ f j) ∈ F.internalFlags :=
    all_pairings_internal_of_periodic κ hper'
  have hrev : ∀ j, j ≤ n →
      iterWalk κ (W.pairing f) j =
        W.pairing (iterWalk κ f (n - j)) := by
    intro j hj
    have h := iterWalk_reverse κ (fun i _ => hcont_all i) j hj
    rwa [hperiod] at h
  refine κ.mem_periodicFlags.mpr ⟨hcont_all 0, n, hn1, ?_, ?_⟩
  · intro j hj
    rw [hrev j (le_of_lt hj), W.pairing_invol]
    exact iterWalk_mem_internal_of_periodic κ hper' (n - j)
      (by omega)
  · rw [hrev n le_rfl, Nat.sub_self, iterWalk_zero]

/-- The edge-pairing reversal on periodic flags. -/
noncomputable def revPerm (κ : F.RelTransitionSystem) :
    Equiv.Perm {f : W.Flag // f ∈ κ.periodicFlags} :=
  Function.Involutive.toPerm
    (fun x => ⟨W.pairing x.val, pairing_mem_periodicFlags κ x.prop⟩)
    (fun x => Subtype.ext (W.pairing_invol x.val))

/-- **The reversal conjugates the walk to its inverse**: traversing
a circuit backwards. -/
theorem walkPerm_revPerm_walkPerm (κ : F.RelTransitionSystem) :
    κ.walkPermPeriodic * revPerm κ * κ.walkPermPeriodic = revPerm κ := by
  ext x
  have hp0 : W.pairing x.val ∈ F.internalFlags :=
    all_pairings_internal_of_periodic κ
      (κ.mem_periodicFlags.mp x.prop) 0
  change κ.internalWalk (W.pairing (κ.internalWalk x.val)) =
    W.pairing x.val
  calc κ.internalWalk (W.pairing (κ.internalWalk x.val))
      = κ.match_ (W.pairing (W.pairing
          (κ.match_ (W.pairing x.val)))) := rfl
    _ = κ.match_ (κ.match_ (W.pairing x.val)) := by
          rw [W.pairing_invol]
    _ = W.pairing x.val := κ.match_invol _ hp0

/-- The reversal is an involution. -/
theorem revPerm_mul_self (κ : F.RelTransitionSystem) :
    revPerm κ * revPerm κ = 1 := by
  ext x
  change W.pairing (W.pairing x.val) = x.val
  exact W.pairing_invol x.val

/-- Equivalently, it is its own inverse. -/
theorem revPerm_inv (κ : F.RelTransitionSystem) :
    (revPerm κ)⁻¹ = revPerm κ := by
  rw [← mul_one (revPerm κ)⁻¹, ← revPerm_mul_self κ, ← mul_assoc,
    inv_mul_cancel, one_mul]

end EdgeSubset

end RS
