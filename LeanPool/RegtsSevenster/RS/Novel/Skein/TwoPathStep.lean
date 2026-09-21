/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger
import LeanPool.RegtsSevenster.RS.Novel.Skein.CanonExistence

/-!
# The two-path separated move

A repair square is *non-localized* when its two re-paired edges lie
on genuinely distinct boundary chains.  This file establishes the
chain geometry of such a square and the count invariance it gives:

* `EdgeSubset.not_periodic_of_onBoundaryChain` — flags on a
  boundary chain are not periodic;
* `EdgeSubset.onBoundaryChain_disjoint` — genuinely distinct
  boundary chains share no flag (chain rigidity);
* `EdgeSubset.square_hit` — a chain carrying one matched edge of
  the square crosses it exactly once, by a pairing argument;
* `EdgeSubset.openCircuitCount_repair_of_not_localized` — **count
  invariance**: a non-localized square leaves the open circuit
  count unchanged, the repaired components being still boundary
  chains, so `periodicFlags` and the periodic walk permutation are
  untouched.

The transform factor the move contributes to the summand is pinned
in `TransposeLedger.lean`, on top of this count invariance.
-/

namespace RS

open scoped Classical

namespace EdgeSubset

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {κ : F.RelTransitionSystem}

/-! ## Chain membership excludes periodicity -/

/-- A flag on a boundary chain is not periodic. -/
theorem not_periodic_of_onBoundaryChain {β f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (h : OnBoundaryChain κ β f) :
    ¬ κ.PeriodicFlag f := by
  intro hper
  obtain ⟨k, t, htk, hcont, hterm, hft⟩ := h
  rcases hft with rfl | rfl
  · cases t with
    | zero =>
      rw [iterWalk_zero] at hper
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hper.mem_internal hβ
    | succ t =>
      exact not_periodic_of_chain_segment κ hcont hterm
        (by omega) htk hper
  · rcases Nat.lt_or_ge t k with hlt | hge
    · exact chain_arg_ne_of_periodic hβ hcont hterm hper hlt rfl
    · obtain rfl : t = k := by omega
      exact Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hper.mem_internal
        hterm

/-! ## Distinct chains share no flag -/

/-- **Chain disjointness**: two genuinely distinct boundary chains
(the second end not among the first chain's two ends) share no
flag, on either side of an edge. -/
theorem onBoundaryChain_disjoint [LinearOrder α] {β β' f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hβ' : β' ∈ F.boundaryFlags)
    (hne : β' ≠ β) (hne' : β' ≠ κ.pathMatch β hβ)
    (h : OnBoundaryChain κ β f) (h' : OnBoundaryChain κ β' f) :
    False := by
  obtain ⟨k, t, htk, hcont, hterm, hft⟩ := h
  obtain ⟨k', t', htk', hcont', hterm', hft'⟩ := h'
  have hγ : κ.pathMatch β hβ = W.pairing (iterWalk κ β k) :=
    pathMatch_eq_of_chain κ hβ hcont hterm
  have hcontγ : ∀ j, j < k →
      W.pairing (iterWalk κ (W.pairing (iterWalk κ β k)) j) ∈
        F.internalFlags :=
    fun j hj => reverse_chain_continues κ hβ hcont j hj
  -- reduce `f` on the `β'` side to a walk flag
  have hf'W : iterWalk κ β' t' = f ∨
      iterWalk κ β' t' = W.pairing f := by
    rcases hft' with hE | hE
    · exact Or.inl hE.symm
    · refine Or.inr ?_
      have := congrArg W.pairing hE
      rwa [W.pairing_invol, eq_comm] at this
  rcases hft with hW | hP
  · -- `f` is a walk flag of `β`'s chain
    rcases hf'W with hE | hE
    · exact hne (chain_meet hβ hβ' hcont hcont' t' t htk' htk
        (hE.trans hW)).1
    · -- `iterWalk β' t' = pairing (iterWalk β t)`: reverse chain
      have h5 : iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) =
          W.pairing (iterWalk κ β t) := by
        rw [iterWalk_reverse κ hcont (k - t) (by omega),
          show k - (k - t) = t from by omega]
      have h6 : iterWalk κ β' t' =
          iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) := by
        rw [hE, hW, h5]
      have h7 := (chain_meet hterm hβ' hcontγ hcont' t' (k - t)
        htk' (by omega) h6).1
      exact hne' (h7.trans hγ.symm)
  · -- `f` is a pairing-side flag of `β`'s chain
    rcases hf'W with hE | hE
    · have h5 : iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) =
          W.pairing (iterWalk κ β t) := by
        rw [iterWalk_reverse κ hcont (k - t) (by omega),
          show k - (k - t) = t from by omega]
      have h6 : iterWalk κ β' t' =
          iterWalk κ (W.pairing (iterWalk κ β k)) (k - t) := by
        rw [hE, hP, h5]
      have h7 := (chain_meet hterm hβ' hcontγ hcont' t' (k - t)
        htk' (by omega) h6).1
      exact hne' (h7.trans hγ.symm)
    · have h6 : iterWalk κ β' t' = iterWalk κ β t := by
        rw [hE, hP, W.pairing_invol]
      exact hne (chain_meet hβ hβ' hcont hcont' t' t htk' htk h6).1

/-! ## The square hit on a chain -/

/-- A chain carrying one matched edge `X ↔ Y` of the square meets it
as a pairing argument: at some step `s < k` the argument is `X` or
`Y`, and the next walk flag is the other. -/
theorem square_hit {X Y β : W.Flag} (hβ : β ∈ F.boundaryFlags)
    (hXi : X ∈ F.internalFlags) (hXY : κ.match_ X = Y) {k : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    (hon : OnBoundaryChain κ β X) :
    ∃ s, s < k ∧
      ((W.pairing (iterWalk κ β s) = X ∧
          iterWalk κ β (s + 1) = Y) ∨
        (W.pairing (iterWalk κ β s) = Y ∧
          iterWalk κ β (s + 1) = X)) := by
  obtain ⟨k', t, htk, hcont', hterm', hft⟩ := hon
  have hkk : k' = k := chain_exit_unique hcont' hterm' hcont hterm
  rcases hft with hW | hP
  · cases t with
    | zero =>
      rw [iterWalk_zero] at hW
      subst hW
      exact absurd hβ (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hXi)
    | succ t =>
      refine ⟨t, by omega, Or.inr ⟨?_, hW.symm⟩⟩
      have h1 : κ.match_ (W.pairing (iterWalk κ β t)) = X := by
        rw [← iterWalk_succ]
        exact hW.symm
      have h2 : W.pairing (iterWalk κ β t) = κ.match_ X := by
        rw [← h1, κ.match_invol _ (hcont t (by omega))]
      rw [h2, hXY]
  · have htk2 : t < k := by
      rcases Nat.lt_or_ge t k with hlt | hge
      · exact hlt
      · obtain rfl : t = k := by omega
        rw [← hP] at hterm
        exact absurd hterm (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hXi)
    refine ⟨t, htk2, Or.inl ⟨hP.symm, ?_⟩⟩
    rw [iterWalk_succ, ← hP, hXY]

/-! ## Repaired chains through the square -/

section RepairChains

variable {a b c d : W.Flag} {v : W.Vertex}

/-- The repaired chain from `β` reaches the first square argument:
if the arguments before step `s` avoid the square, the argument at
step `s` lies on the repaired chain of `β`. -/
theorem onBoundaryChain_repair_of_hit (hsq : RepairSquare κ a b c d v)
    {β : W.Flag} (hβ : β ∈ F.boundaryFlags) {k s : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hs : s < k)
    (havoid : ∀ j, j < s →
      W.pairing (iterWalk κ β j) ≠ a ∧
      W.pairing (iterWalk κ β j) ≠ b ∧
      W.pairing (iterWalk κ β j) ≠ c ∧
      W.pairing (iterWalk κ β j) ≠ d) :
    OnBoundaryChain (κ.repair a b c d v hsq) β
      (W.pairing (iterWalk κ β s)) := by
  have hagree := repair_iterWalk_of_avoid hsq (k := s) havoid
  obtain ⟨k', hk'le, hcont', hterm'⟩ :=
    chain_terminates_with_data (κ.repair a b c d v hsq) hβ
  have hsk' : s < k' := by
    by_contra hle
    have hk's : k' ≤ s := by omega
    have h1 : W.pairing (iterWalk (κ.repair a b c d v hsq) β k') =
        W.pairing (iterWalk κ β k') := by
      rw [hagree k' hk's]
    rw [h1] at hterm'
    exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags
      (hcont k' (by omega)) hterm'
  exact ⟨k', s, by omega, hcont', hterm',
    Or.inr (by rw [hagree s le_rfl])⟩

/-- The walk-side square flag on a chain is not periodic in the
repaired system: the repaired walk from it follows the old chain
tail to the boundary. -/
theorem not_periodic_repair_of_tail (hsq : RepairSquare κ a b c d v)
    {β : W.Flag} {k s : ℕ}
    (hcont : ∀ j, j < k →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β k) ∈ F.boundaryFlags)
    (hs : s < k)
    (hav : ∀ j, s < j → j < k →
      W.pairing (iterWalk κ β j) ≠ a ∧
      W.pairing (iterWalk κ β j) ≠ b ∧
      W.pairing (iterWalk κ β j) ≠ c ∧
      W.pairing (iterWalk κ β j) ≠ d) :
    ¬ (κ.repair a b c d v hsq).PeriodicFlag
      (iterWalk κ β (s + 1)) := by
  have hYint : iterWalk κ β (s + 1) ∈ F.internalFlags :=
    iterWalk_mem_internal κ k (by omega) (by omega) hcont
  have hYW : ∀ t, iterWalk κ (iterWalk κ β (s + 1)) t =
      iterWalk κ β (s + 1 + t) :=
    fun t => (iterWalk_add κ β (s + 1) t).symm
  have havY : ∀ t, t < k - s - 1 →
      W.pairing (iterWalk κ (iterWalk κ β (s + 1)) t) ≠ a ∧
      W.pairing (iterWalk κ (iterWalk κ β (s + 1)) t) ≠ b ∧
      W.pairing (iterWalk κ (iterWalk κ β (s + 1)) t) ≠ c ∧
      W.pairing (iterWalk κ (iterWalk κ β (s + 1)) t) ≠ d := by
    intro t ht
    rw [hYW]
    exact hav (s + 1 + t) (by omega) (by omega)
  have hagree := repair_iterWalk_of_avoid hsq (k := k - s - 1) havY
  apply not_periodic_of_boundary_chain (κ.repair a b c d v hsq) _
    hYint
  refine ⟨(k - s - 1) + 1,
    W.pairing (iterWalk (κ.repair a b c d v hsq)
      (iterWalk κ β (s + 1)) (k - s - 1)), ?_⟩
  apply traceChain_forward (κ.repair a b c d v hsq)
    (iterWalk κ β (s + 1)) (k := k - s - 1)
  · intro t ht
    rw [hagree t (by omega), hYW]
    exact hcont (s + 1 + t) (by omega)
  · rw [hagree (k - s - 1) le_rfl, hYW,
      show s + 1 + (k - s - 1) = k from by omega]
    exact hterm

/-- One chain side of a two-chain square: its two square flags are
non-periodic in the repaired system.  Stated for a matched pair
`X ↔ Y` on the chain of `β`, with the other two square flags on the
genuinely distinct chain of `βo`; `hperm` identifies the four square
flags with `{X, Y, Z₁, Z₂}`. -/
theorem chain_side_not_periodic_repair [LinearOrder α]
    (hsq : RepairSquare κ a b c d v)
    {β βo X Y Z₁ Z₂ : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (hβo : βo ∈ F.boundaryFlags)
    (hne1 : β ≠ βo) (hne2 : β ≠ κ.pathMatch βo hβo)
    (hXi : X ∈ F.internalFlags) (hXY : κ.match_ X = Y)
    (honX : OnBoundaryChain κ β X)
    (honZ₁ : OnBoundaryChain κ βo Z₁)
    (honZ₂ : OnBoundaryChain κ βo Z₂)
    (hperm : ∀ g : W.Flag,
      (g = a ∨ g = b ∨ g = c ∨ g = d) ↔
        (g = X ∨ g = Y ∨ g = Z₁ ∨ g = Z₂)) :
    ¬ (κ.repair a b c d v hsq).PeriodicFlag X ∧
      ¬ (κ.repair a b c d v hsq).PeriodicFlag Y := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  obtain ⟨s, hs, hhit⟩ := square_hit hβ hXi hXY hcont hterm honX
  -- arguments away from step `s` avoid all four square flags
  have havoid : ∀ j, j < k → j ≠ s →
      W.pairing (iterWalk κ β j) ≠ a ∧
      W.pairing (iterWalk κ β j) ≠ b ∧
      W.pairing (iterWalk κ β j) ≠ c ∧
      W.pairing (iterWalk κ β j) ≠ d := by
    intro j hj hjs
    have hXne : W.pairing (iterWalk κ β j) ≠ X ∧
        W.pairing (iterWalk κ β j) ≠ Y := by
      rcases hhit with ⟨hargX, hwalkY⟩ | ⟨hargY, hwalkX⟩
      · constructor
        · intro he
          exact hjs (pairing_iterWalk_injective κ hβ k hcont hj hs
            (he.trans hargX.symm))
        · intro he
          exact pairing_iterWalk_ne κ hcont (le_of_lt hj)
            (by omega : s + 1 ≤ k) (he.trans hwalkY.symm)
      · constructor
        · intro he
          exact pairing_iterWalk_ne κ hcont (le_of_lt hj)
            (by omega : s + 1 ≤ k) (he.trans hwalkX.symm)
        · intro he
          exact hjs (pairing_iterWalk_injective κ hβ k hcont hj hs
            (he.trans hargY.symm))
    have hZne : W.pairing (iterWalk κ β j) ≠ Z₁ ∧
        W.pairing (iterWalk κ β j) ≠ Z₂ := by
      constructor
      · intro he
        exact onBoundaryChain_disjoint hβo hβ hne1 hne2 honZ₁
          ⟨k, j, le_of_lt hj, hcont, hterm, Or.inr he.symm⟩
      · intro he
        exact onBoundaryChain_disjoint hβo hβ hne1 hne2 honZ₂
          ⟨k, j, le_of_lt hj, hcont, hterm, Or.inr he.symm⟩
    have hall : ¬ (W.pairing (iterWalk κ β j) = a ∨
        W.pairing (iterWalk κ β j) = b ∨
        W.pairing (iterWalk κ β j) = c ∨
        W.pairing (iterWalk κ β j) = d) := by
      intro hor
      rcases (hperm (W.pairing (iterWalk κ β j))).mp hor with
        h | h | h | h
      · exact hXne.1 h
      · exact hXne.2 h
      · exact hZne.1 h
      · exact hZne.2 h
    exact ⟨fun he => hall (Or.inl he),
      fun he => hall (Or.inr (Or.inl he)),
      fun he => hall (Or.inr (Or.inr (Or.inl he))),
      fun he => hall (Or.inr (Or.inr (Or.inr he)))⟩
  have hOn : OnBoundaryChain (κ.repair a b c d v hsq) β
      (W.pairing (iterWalk κ β s)) :=
    onBoundaryChain_repair_of_hit hsq hβ hcont hs
      (fun j hj => havoid j (by omega) (by omega))
  have hTail : ¬ (κ.repair a b c d v hsq).PeriodicFlag
      (iterWalk κ β (s + 1)) :=
    not_periodic_repair_of_tail hsq hcont hterm hs
      (fun j hj1 hj2 => havoid j hj2 (by omega))
  have hArg : ¬ (κ.repair a b c d v hsq).PeriodicFlag
      (W.pairing (iterWalk κ β s)) :=
    not_periodic_of_onBoundaryChain hβ hOn
  rcases hhit with ⟨hargX, hwalkY⟩ | ⟨hargY, hwalkX⟩
  · exact ⟨hargX ▸ hArg, hwalkY ▸ hTail⟩
  · exact ⟨hwalkX ▸ hTail, hargY ▸ hArg⟩

/-- Periodicity transfer across a repair whose four flags are
non-periodic on both sides. -/
theorem periodicFlag_repair_iff (hsq : RepairSquare κ a b c d v)
    (hna : ¬ κ.PeriodicFlag a) (hnb : ¬ κ.PeriodicFlag b)
    (hnc : ¬ κ.PeriodicFlag c) (hnd : ¬ κ.PeriodicFlag d)
    (hna' : ¬ (κ.repair a b c d v hsq).PeriodicFlag a)
    (hnb' : ¬ (κ.repair a b c d v hsq).PeriodicFlag b)
    (hnc' : ¬ (κ.repair a b c d v hsq).PeriodicFlag c)
    (hnd' : ¬ (κ.repair a b c d v hsq).PeriodicFlag d)
    (f : W.Flag) :
    (κ.repair a b c d v hsq).PeriodicFlag f ↔ κ.PeriodicFlag f := by
  constructor
  · intro hper
    have hagree : ∀ j,
        iterWalk (κ.repair a b c d v hsq) f j = iterWalk κ f j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        have harg : (κ.repair a b c d v hsq).PeriodicFlag
            (W.pairing (iterWalk (κ.repair a b c d v hsq) f j)) :=
          periodicFlag_pairing
            (periodicFlag_iterWalk (κ.repair a b c d v hsq) hper j)
        rw [ih] at harg
        rw [iterWalk_succ, iterWalk_succ, ih]
        exact RelTransitionSystem.repair_match_of_ne hsq
          (fun he => hna' (he ▸ harg)) (fun he => hnb' (he ▸ harg))
          (fun he => hnc' (he ▸ harg)) (fun he => hnd' (he ▸ harg))
    obtain ⟨hint, n, hn1, hcont, hret⟩ := hper
    refine ⟨hint, n, hn1, fun j hj => ?_, ?_⟩
    · rw [← hagree j]
      exact hcont j hj
    · rw [← hagree n]
      exact hret
  · intro hper
    have hagree : ∀ j,
        iterWalk (κ.repair a b c d v hsq) f j = iterWalk κ f j := by
      intro j
      induction j with
      | zero => rfl
      | succ j ih =>
        have harg : κ.PeriodicFlag (W.pairing (iterWalk κ f j)) :=
          periodicFlag_pairing (periodicFlag_iterWalk κ hper j)
        rw [iterWalk_succ, iterWalk_succ, ih]
        exact RelTransitionSystem.repair_match_of_ne hsq
          (fun he => hna (he ▸ harg)) (fun he => hnb (he ▸ harg))
          (fun he => hnc (he ▸ harg)) (fun he => hnd (he ▸ harg))
    obtain ⟨hint, n, hn1, hcont, hret⟩ := hper
    refine ⟨hint, n, hn1, fun j hj => ?_, ?_⟩
    · rw [hagree j]
      exact hcont j hj
    · rw [hagree n]
      exact hret

/-- **Count invariance for two-chain squares**: a non-localized
square leaves the open circuit count unchanged — both repaired
components are still boundary-terminated chains, so the periodic
flags and the periodic walk permutation are untouched. -/
theorem openCircuitCount_repair_of_not_localized [LinearOrder α]
    (hsq : RepairSquare κ a b c d v)
    (hnl : ¬ SquareLocalized κ a b c d) :
    (κ.repair a b c d v hsq).openCircuitCount =
      κ.openCircuitCount := by
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hca, hcc, h21, h2γ⟩ :=
    twoChains_of_not_localized hsq hnl
  have h12 : β₁ ≠ β₂ := Ne.symm h21
  have h1γ2 : β₁ ≠ κ.pathMatch β₂ hβ₂ := by
    intro he
    apply h2γ
    have h3 := κ.pathMatch_congr he hβ₁ (κ.pathMatch_mem hβ₂)
    exact (h3.trans (κ.pathMatch_invol hβ₂)).symm
  have hcb : OnBoundaryChain κ β₁ b :=
    hsq.hab ▸ onBoundaryChain_match hβ₁ hsq.ha hca
  have hcd : OnBoundaryChain κ β₂ d :=
    hsq.hcd ▸ onBoundaryChain_match hβ₂ hsq.hc hcc
  -- non-periodicity in `κ`
  have hna : ¬ κ.PeriodicFlag a :=
    not_periodic_of_onBoundaryChain hβ₁ hca
  have hnb : ¬ κ.PeriodicFlag b :=
    not_periodic_of_onBoundaryChain hβ₁ hcb
  have hnc : ¬ κ.PeriodicFlag c :=
    not_periodic_of_onBoundaryChain hβ₂ hcc
  have hnd : ¬ κ.PeriodicFlag d :=
    not_periodic_of_onBoundaryChain hβ₂ hcd
  -- non-periodicity in the repaired system
  obtain ⟨hna', hnb'⟩ := chain_side_not_periodic_repair hsq
    hβ₁ hβ₂ h12 h1γ2 hsq.ha hsq.hab hca hcc hcd
    (fun g => Iff.rfl)
  obtain ⟨hnc', hnd'⟩ := chain_side_not_periodic_repair hsq
    hβ₂ hβ₁ h21 h2γ hsq.hc hsq.hcd hcc hca hcb
    (fun g => by tauto)
  -- the periodic flags agree
  have hset : (κ.repair a b c d v hsq).periodicFlags =
      κ.periodicFlags := by
    apply Finset.ext
    intro f
    rw [(κ.repair a b c d v hsq).mem_periodicFlags,
      κ.mem_periodicFlags]
    exact periodicFlag_repair_iff hsq hna hnb hnc hnd
      hna' hnb' hnc' hnd' f
  -- transport the walk permutation
  have hperm : (κ.repair a b c d v hsq).walkPermPeriodic =
      (Equiv.subtypeEquivRight (fun f => by rw [hset]) :
          {f : W.Flag // f ∈ κ.periodicFlags} ≃
            {f : W.Flag //
              f ∈ (κ.repair a b c d v hsq).periodicFlags}).permCongr
        κ.walkPermPeriodic := by
    apply Equiv.ext
    rintro ⟨f, hf⟩
    apply Subtype.ext
    have hfp : κ.PeriodicFlag f := by
      rw [hset] at hf
      exact κ.mem_periodicFlags.mp hf
    have hσ : κ.PeriodicFlag (W.pairing f) := periodicFlag_pairing hfp
    rw [Equiv.permCongr_apply]
    simp only [Equiv.subtypeEquivRight_symm_apply,
      Equiv.subtypeEquivRight_apply]
    show (κ.repair a b c d v hsq).match_ (W.pairing f) =
      κ.match_ (W.pairing f)
    exact RelTransitionSystem.repair_match_of_ne hsq
      (fun he => hna (he ▸ hσ)) (fun he => hnb (he ▸ hσ))
      (fun he => hnc (he ▸ hσ)) (fun he => hnd (he ▸ hσ))
  unfold RelTransitionSystem.openCircuitCount
  rw [hperm, cycleType_permCongr, card_fixedPoints_permCongr]

end RepairChains

end EdgeSubset

end RS
