/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingConnectivity
import LeanPool.RegtsSevenster.RS.Novel.Skein.OrbitParities
import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathStep

/-!
# The pairing-preserving step ledger

Discharges the single-repair disjunct of `MatchPreservingLedger`:
every pairing-preserving repair step (`MatchPreservingStep`) carries
a path-canonical orientation to a path-canonical orientation on the
repaired side with the same pathSign-weighted canonical summand.

## Main results

* `EdgeSubset.squareLocalized_of_pathMatch_eq` — **two-path
  exclusion**: a repair square that preserves every path matching is
  localized.  A non-localized square has its two re-paired edges on
  genuinely distinct boundary chains (`twoChains_of_not_localized`);
  after the repair, the `a`-flag and the `c`-flag land on the
  repaired chains of the two old chains' ends (`hit_membership`,
  from the unique square crossing of each chain), and `a`, `c` are
  matched by the repaired system, so the two repaired chains share a
  flag — contradicting chain disjointness when the pairing is
  preserved.
* `EdgeSubset.walkReach_or_walkReach_of_chain` — on one boundary
  chain, two coherently oriented internal flags see one another
  along the walk (orientation rigidity kills the mixed walk-side /
  pairing-side cases; positions order the same-side cases).
* Canonicality transfer: `EdgeSubset.pathCanonical_of_entry_eq` plus
  the per-case entry computations — `transportRepair` keeps `isOut`
  verbatim; `flipOrbit` is supported on a periodic orbit and entry
  flags are non-periodic (`entry_not_periodic`); the reversal
  segment of `segFlip` is pairing-closed and internal, so it carries
  no entry flag (`entry_notMem_repairSegment`).
* `EdgeSubset.stepLedger_single` — **the single-step ledger**: the
  `MatchPreservingStep` disjunct of the per-move interface, fully
  discharged from the parity theorems (`separatedCountParity`,
  `nonSeparatedSegmentParity`, `nonSeparatedMergeParity`).
* `EdgeSubset.PairedLedger` — the named input: the `PairedStep`
  disjunct (two consecutive repairs with net pairing
  preservation); a theorem downstream (`pairedLedger`,
  `PairedAssembly.lean`).
* `EdgeSubset.matchPreservingLedger_of` — the dispatch:
  `MatchPreservingLedger` from `PairedLedger` and the single-step
  theorem.

## Why a pair is one move

`PairedLedger` carries the content.  Each half of a `PairedStep`
may be a two-path repair that changes the boundary pairing, where
the per-repair vertex ledger negates the summand and re-pairs the
boundary colour blocks; across the pair the values net-agree via a
re-pairing (colour-swap) identity for the vertex functional on the
re-routed strand.  `TwoPathStep` supplies the count invariance the halves need
(`openCircuitCount_repair_of_not_localized`).  A single two-path
repair does not carry the ledger on its own, which is why a pair
is treated as one composite move.
-/

namespace RS



namespace EdgeSubset

variable {α : Type}

/-! ## Entry flags: non-periodicity and segment avoidance -/

section EntryFlags

/-- The entry edge of a participating boundary flag is not periodic:
it is the step-`0` pairing argument of a boundary-terminated chain. -/
theorem entry_not_periodic
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {i : α}
    (hb : W.boundaryFlag i ∈ F.boundaryFlags)
    (hint : W.pairing (W.boundaryFlag i) ∈ F.internalFlags) :
    ¬ κ.PeriodicFlag (W.pairing (W.boundaryFlag i)) := by
  intro hper
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hb
  have hk : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [iterWalk_zero] at hterm
      exact absurd hterm
        (Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hint)
    · exact h
  have h := chain_arg_ne_of_periodic hb hcont hterm hper (s := 0) hk
  rw [iterWalk_zero] at h
  exact h rfl

/-- A reversal segment carries no entry flag: the segment is
pairing-closed and internal, while the pairing of an entry flag is a
boundary flag. -/
theorem entry_notMem_repairSegment
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a b c d : W.Flag}
    {S : Finset W.Flag} (hseg : RepairSegment κ a b c d S) (i : α) :
    W.pairing (W.boundaryFlag i) ∉ S := by
  intro hmem
  have h2 := hseg.pairing_mem _ hmem
  rw [W.pairing_invol] at h2
  exact hseg.notMem_boundaryFlag i h2

/-- **Canonicality transfer**: an orientation of a system with the
same path matching, agreeing with a path-canonical orientation on
every entry flag, is path-canonical. -/
theorem pathCanonical_of_entry_eq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem}
    {κ' : F.RelTransitionSystem}
    {o : κ.Orientation} {o' : κ'.Orientation}
    (hpm : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      κ'.pathMatch δ hδ = κ.pathMatch δ hδ)
    (hentry : ∀ i : α, W.boundaryFlag i ∈ F.boundaryFlags →
      W.pairing (W.boundaryFlag i) ∈ F.internalFlags →
      o'.isOut (W.pairing (W.boundaryFlag i)) =
        o.isOut (W.pairing (W.boundaryFlag i)))
    (hc : PathCanonical o) : PathCanonical o' := by
  intro i j hb hint hpm' hij
  rw [hentry i hb hint]
  exact hc i j hb hint ((hpm _ hb).symm.trans hpm') hij

end EntryFlags

/-! ## Two-path exclusion -/

section TwoPathExclusion

/-- Chain membership from the exit end of a terminating forward
walk. -/
theorem onBoundaryChain_of_exit
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {f : W.Flag}
    (hf : f ∈ F.internalFlags) {m : ℕ}
    (hcont : ∀ j, j < m →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ f m) ∈ F.boundaryFlags) :
    OnBoundaryChain κ (W.pairing (iterWalk κ f m)) f := by
  have hcontb : ∀ t, t ≤ m →
      W.pairing (iterWalk κ (W.pairing (iterWalk κ f m)) t) ∈
        F.internalFlags := by
    intro t ht
    rw [iterWalk_reverse κ hcont t ht, W.pairing_invol]
    rcases Nat.lt_or_ge t m with h | h
    · exact iterWalk_mem_internal κ m (by omega) (by omega) hcont
    · rw [show m - t = 0 from by omega, iterWalk_zero]
      exact hf
  obtain ⟨k', hk'le, hcont', hterm'⟩ :=
    chain_terminates_with_data κ hterm
  have hk'gt : m < k' := by
    by_contra hle
    exact Finset.disjoint_left.mp
      F.internalFlags_disjoint_boundaryFlags
      (hcontb k' (by omega)) hterm'
  have hfeq :
      W.pairing (iterWalk κ (W.pairing (iterWalk κ f m)) m) = f :=
    reverse_chain_terminates κ hcont
  exact ⟨k', m, by omega, hcont', hterm', Or.inr hfeq.symm⟩

/-- **The tail exit**: after the walk flag following the square hit,
the repaired walk follows the old chain tail and exits at the old
chain's far end, so that walk flag lies on the repaired chain of the
far end. -/
private theorem tail_exits_repair
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a : W.Flag} {b : W.Flag} {c : W.Flag} {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
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
    OnBoundaryChain (κ.repair a b c d v hsq)
      (W.pairing (iterWalk κ β k)) (iterWalk κ β (s + 1)) := by
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
  have hcont' : ∀ t, t < k - s - 1 →
      W.pairing (iterWalk (κ.repair a b c d v hsq)
        (iterWalk κ β (s + 1)) t) ∈ F.internalFlags := by
    intro t ht
    rw [hagree t (by omega), hYW]
    exact hcont (s + 1 + t) (by omega)
  have hexit : W.pairing (iterWalk (κ.repair a b c d v hsq)
      (iterWalk κ β (s + 1)) (k - s - 1)) =
      W.pairing (iterWalk κ β k) := by
    rw [hagree (k - s - 1) le_rfl, hYW,
      show s + 1 + (k - s - 1) = k from by omega]
  have hterm' : W.pairing (iterWalk (κ.repair a b c d v hsq)
      (iterWalk κ β (s + 1)) (k - s - 1)) ∈ F.boundaryFlags := by
    rw [hexit]
    exact hterm
  have h := onBoundaryChain_of_exit
    (κ := κ.repair a b c d v hsq) hYint hcont' hterm'
  rwa [hexit] at h

/-- **The hit membership**: on a two-chain square, the `X`-flag of
the matched pair carried by `β`'s chain lies, after the repair, on
the repaired chain of `β` or of `β`'s far end. -/
theorem hit_membership [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
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
    OnBoundaryChain (κ.repair a b c d v hsq) β X ∨
      OnBoundaryChain (κ.repair a b c d v hsq)
        (κ.pathMatch β hβ) X := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  obtain ⟨s, hs, hhit⟩ := square_hit hβ hXi hXY hcont hterm honX
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
  rcases hhit with ⟨hargX, _⟩ | ⟨_, hwalkX⟩
  · left
    have h := onBoundaryChain_repair_of_hit hsq hβ hcont hs
      (fun j hj => havoid j (by omega) (by omega))
    rwa [hargX] at h
  · right
    have h := tail_exits_repair hsq hcont hterm hs
      (fun j hj1 hj2 => havoid j hj2 (by omega))
    rw [hwalkX] at h
    rw [pathMatch_eq_of_chain κ hβ hcont hterm]
    exact h

/-- **Two-path exclusion**: a repair square that preserves every
path matching is localized.  On a non-localized square the repaired
`a`-flag and its repaired match `c` land on the repaired chains of
two genuinely distinct pairs of ends, which share no flag. -/
theorem squareLocalized_of_pathMatch_eq
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v)
    (hpres : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
      (κ.repair a b c d v hsq).pathMatch δ hδ =
        κ.pathMatch δ hδ) :
    SquareLocalized κ a b c d := by
  by_contra hnl
  obtain ⟨β₁, β₂, hβ₁, hβ₂, hca, hcc, h21, h2γ⟩ :=
    twoChains_of_not_localized hsq hnl
  have h12 : β₁ ≠ β₂ := Ne.symm h21
  have hγ₁mem : κ.pathMatch β₁ hβ₁ ∈ F.boundaryFlags :=
    κ.pathMatch_mem hβ₁
  have hγ₂mem : κ.pathMatch β₂ hβ₂ ∈ F.boundaryFlags :=
    κ.pathMatch_mem hβ₂
  have h1γ2 : β₁ ≠ κ.pathMatch β₂ hβ₂ := by
    intro he
    apply h2γ
    have h3 := κ.pathMatch_congr he hβ₁ hγ₂mem
    exact (h3.trans (κ.pathMatch_invol hβ₂)).symm
  have hγ2γ1 : κ.pathMatch β₂ hβ₂ ≠ κ.pathMatch β₁ hβ₁ := by
    intro he
    apply h21
    have h3 := κ.pathMatch_congr he hγ₂mem hγ₁mem
    exact ((κ.pathMatch_invol hβ₂).symm.trans h3).trans
      (κ.pathMatch_invol hβ₁)
  have hγ2β1 : κ.pathMatch β₂ hβ₂ ≠ β₁ := fun he => h1γ2 he.symm
  have hcb : OnBoundaryChain κ β₁ b :=
    hsq.hab ▸ onBoundaryChain_match hβ₁ hsq.ha hca
  have hcd : OnBoundaryChain κ β₂ d :=
    hsq.hcd ▸ onBoundaryChain_match hβ₂ hsq.hc hcc
  have hA := hit_membership hsq hβ₁ hβ₂ h12 h1γ2 hsq.ha hsq.hab
    hca hcc hcd (fun g => Iff.rfl)
  have hC := hit_membership hsq hβ₂ hβ₁ h21 h2γ hsq.hc hsq.hcd
    hcc hca hcb (fun g => by tauto)
  have honc : ∀ {e : W.Flag}, e ∈ F.boundaryFlags →
      OnBoundaryChain (κ.repair a b c d v hsq) e a →
      OnBoundaryChain (κ.repair a b c d v hsq) e c := by
    intro e he h
    have h2 := onBoundaryChain_match
      (κ := κ.repair a b c d v hsq) he hsq.ha h
    rwa [RelTransitionSystem.repair_match_a hsq] at h2
  have hpm1 : (κ.repair a b c d v hsq).pathMatch β₁ hβ₁ =
      κ.pathMatch β₁ hβ₁ := hpres β₁ hβ₁
  have hpmγ1 : (κ.repair a b c d v hsq).pathMatch
      (κ.pathMatch β₁ hβ₁) hγ₁mem = β₁ :=
    (hpres _ hγ₁mem).trans (κ.pathMatch_invol hβ₁)
  rcases hA with h₁ | h₁ <;> rcases hC with h₂ | h₂
  · exact onBoundaryChain_disjoint hβ₁ hβ₂ h21
      (by rw [hpm1]; exact h2γ) (honc hβ₁ h₁) h₂
  · exact onBoundaryChain_disjoint hβ₁ hγ₂mem hγ2β1
      (by rw [hpm1]; exact hγ2γ1) (honc hβ₁ h₁) h₂
  · exact onBoundaryChain_disjoint hγ₁mem hβ₂ h2γ
      (by rw [hpmγ1]; exact h21) (honc hγ₁mem h₁) h₂
  · exact onBoundaryChain_disjoint hγ₁mem hγ₂mem hγ2γ1
      (by rw [hpmγ1]; exact hγ2β1) (honc hγ₁mem h₁) h₂

end TwoPathExclusion

/-! ## Same-chain reach for coherent orientations -/

section SameChainReach

/-- **Same-chain reach**: two distinct coherently oriented internal
flags on one boundary chain see one another along the walk.
Orientation rigidity (walk-side flags carry the negated seed,
pairing-side flags the seed) excludes the mixed cases; on a common
side the walk runs from the earlier to the later position. -/
theorem walkReach_or_walkReach_of_chain
    {W : Fragment α} {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β f g : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (o : κ.Orientation)
    (hsame : o.isOut f = o.isOut g) (hfg : f ≠ g)
    (hf : f ∈ F.internalFlags) (hg : g ∈ F.internalFlags)
    (honf : OnBoundaryChain κ β f)
    (hong : OnBoundaryChain κ β g) :
    WalkReach κ f g ∨ WalkReach κ g f := by
  obtain ⟨k, hkle, hcont, hterm⟩ := chain_terminates_with_data κ hβ
  obtain ⟨kf, t, htk, hcontf, htermf, hft⟩ := honf
  obtain ⟨kg, s, hsk, hcontg, htermg, hgs⟩ := hong
  have hkf : kf = k := chain_exit_unique hcontf htermf hcont hterm
  have hkg : kg = k := chain_exit_unique hcontg htermg hcont hterm
  rw [hkf] at htk
  rw [hkg] at hsk
  have hwalkpos : ∀ {x : W.Flag} {u : ℕ}, x ∈ F.internalFlags →
      x = iterWalk κ β u → 1 ≤ u := by
    intro x u hx hxe
    rcases Nat.eq_zero_or_pos u with rfl | h
    · rw [iterWalk_zero] at hxe
      rw [hxe] at hx
      exact absurd hβ (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hx)
    · exact h
  have hpairpos : ∀ {x : W.Flag} {u : ℕ}, u ≤ k →
      x ∈ F.internalFlags →
      x = W.pairing (iterWalk κ β u) → u < k := by
    intro x u huk hx hxe
    rcases Nat.lt_or_ge u k with h | h
    · exact h
    · obtain rfl : u = k := by omega
      rw [hxe] at hx
      exact absurd hterm (Finset.disjoint_left.mp
        F.internalFlags_disjoint_boundaryFlags hx)
  have hreach_walk : ∀ {t s : ℕ}, t < s → s ≤ k →
      WalkReach κ (iterWalk κ β t) (iterWalk κ β s) := by
    intro t s hts hsk'
    refine ⟨s - t, by omega, ?_, ?_⟩
    · intro j hj
      rw [← iterWalk_add κ β t j]
      exact hcont (t + j) (by omega)
    · rw [← iterWalk_add κ β t (s - t),
        show t + (s - t) = s from by omega]
  have hreach_pair : ∀ {t s : ℕ}, s < t → t ≤ k →
      WalkReach κ (W.pairing (iterWalk κ β t))
        (W.pairing (iterWalk κ β s)) := by
    intro t s hst htk'
    have hcont' : ∀ j, j < t →
        W.pairing (iterWalk κ β j) ∈ F.internalFlags :=
      fun j hj => hcont j (by omega)
    have hrev : ∀ j, j ≤ t →
        iterWalk κ (W.pairing (iterWalk κ β t)) j =
          W.pairing (iterWalk κ β (t - j)) :=
      fun j hj => iterWalk_reverse κ hcont' j hj
    refine ⟨t - s, by omega, ?_, ?_⟩
    · intro j hj
      rw [hrev j (by omega), W.pairing_invol]
      exact iterWalk_mem_internal κ k (by omega) (by omega) hcont
    · rw [hrev (t - s) (by omega),
        show t - (t - s) = s from by omega]
  rcases hft with hfw | hfp <;> rcases hgs with hgw | hgp
  · -- both walk-side
    rcases Nat.lt_trichotomy t s with h | h | h
    · left
      rw [hfw, hgw]
      exact hreach_walk h hsk
    · exact absurd (by rw [hfw, hgw, h]) hfg
    · right
      rw [hfw, hgw]
      exact hreach_walk h htk
  · -- f walk-side, g pairing-side: orientation obstruction
    exfalso
    have ht1 : 1 ≤ t := hwalkpos hf hfw
    have hsk2 : s < k := hpairpos hsk hg hgp
    have h1 : o.isOut f = !o.isOut (W.pairing β) := by
      rw [hfw]
      exact isOut_iterWalk_eq_not_seed o hcont t ht1 htk
    have h2 : o.isOut g = o.isOut (W.pairing β) := by
      rw [hgp]
      exact isOut_pairing_iterWalk_eq_seed o hcont s hsk2
    rw [h1, h2] at hsame
    exact Bool.not_ne_self _ hsame
  · -- f pairing-side, g walk-side: orientation obstruction
    exfalso
    have hs1 : 1 ≤ s := hwalkpos hg hgw
    have htk2 : t < k := hpairpos htk hf hfp
    have h1 : o.isOut f = o.isOut (W.pairing β) := by
      rw [hfp]
      exact isOut_pairing_iterWalk_eq_seed o hcont t htk2
    have h2 : o.isOut g = !o.isOut (W.pairing β) := by
      rw [hgw]
      exact isOut_iterWalk_eq_not_seed o hcont s hs1 hsk
    rw [h1, h2] at hsame
    exact Bool.not_ne_self _ hsame.symm
  · -- both pairing-side
    rcases Nat.lt_trichotomy t s with h | h | h
    · right
      rw [hfp, hgp]
      exact hreach_pair h hsk
    · exact absurd (by rw [hfp, hgp, h]) hfg
    · left
      rw [hfp, hgp]
      exact hreach_pair h htk

end SameChainReach

/-! ## The single-step ledger -/

section StepLedger

private theorem neg_one_pow_congr_of_even {m n : ℕ}
    (h : Even (n + m)) : ((-1 : ℂ)) ^ m = ((-1 : ℂ)) ^ n := by
  have h1 : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ m = 1 := by
    rw [← pow_add]
    exact h.neg_one_pow
  have h2 : ((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  calc ((-1 : ℂ)) ^ m
      = (((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ n) * ((-1 : ℂ)) ^ m := by
        rw [h2, one_mul]
    _ = ((-1 : ℂ)) ^ n * (((-1 : ℂ)) ^ n * ((-1 : ℂ)) ^ m) := by
        ring
    _ = ((-1 : ℂ)) ^ n := by rw [h1, mul_one]

/-- Transport of the canonical signed conclusion across the
`MatchEq` slack of the step relation. -/
private theorem step_conclusion
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ₁ κ₂ κ' : F.RelTransitionSystem}
    (heq : κ₂.MatchEq κ') (o₁ : κ₁.Orientation)
    (o' : κ'.Orientation) (hc' : PathCanonical o')
    (hval : pathSign κ' *
        F.throughSummand hM st hbnd o' κ'.openCircuitCount =
      pathSign κ₁ *
        F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount) :
    ∃ o₂ : κ₂.Orientation, PathCanonical o₂ ∧
      pathSign κ₂ *
          F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount := by
  refine ⟨RelTransitionSystem.Orientation.ofMatchEq
    (RelTransitionSystem.MatchEq.symm heq) o', ?_, ?_⟩
  · exact pathCanonical_of_entry_eq
      (fun δ hδ => pathMatch_matchEq
        (RelTransitionSystem.MatchEq.symm heq) hδ)
      (fun _ _ _ => rfl) hc'
  · rw [openCircuitCount_matchEq
      (RelTransitionSystem.MatchEq.symm heq),
      throughSummand_ofMatchEq hM st hbnd
        (RelTransitionSystem.MatchEq.symm heq) o',
      pathSign_matchEq (RelTransitionSystem.MatchEq.symm heq)]
    exact hval

/-- **The single-step ledger** (the `MatchPreservingStep` disjunct
of `MatchPreservingLedger`, fully discharged): a pairing-preserving
repair step carries a path-canonical orientation to a
path-canonical orientation with the same pathSign-weighted
canonical summand.  The square is localized by the two-path
exclusion; the separated case transports the orientation verbatim,
the non-separated case dispatches into the segment-reversal,
swapped-segment, orbit-flip, and swapped-orbit-flip ledgers, whose
count parities are `separatedCountParity`,
`nonSeparatedSegmentParity`, and `nonSeparatedMergeParity`; in
every case the produced orientation agrees with the input on all
entry flags, so canonicality transfers. -/
theorem stepLedger_single
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem)
    (hstep : MatchPreservingStep κ₁ κ₂)
    (o₁ : κ₁.Orientation) (hc₁ : PathCanonical o₁) :
    ∃ o₂ : κ₂.Orientation, PathCanonical o₂ ∧
      pathSign κ₂ *
          F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount := by
  obtain ⟨a, b, c, d, v, hsq, heq, hpres⟩ := hstep
  have hloc : SquareLocalized κ₁ a b c d :=
    squareLocalized_of_pathMatch_eq hsq hpres
  -- ═══════ SEPARATED OR NOT ═══════
  -- A separated square transports the orientation verbatim; a
  -- non-separated one dispatches on where the walk reaches.
  by_cases hflip : o₁.isOut c = !o₁.isOut a
  · -- separated localized: transport the orientation verbatim
    refine step_conclusion hM st hbnd heq o₁
      (RelTransitionSystem.Orientation.transportRepair hsq o₁ hflip)
      (pathCanonical_of_entry_eq hpres (fun _ _ _ => rfl) hc₁) ?_
    rw [pathSign_congr hpres,
      throughSummand_repair hM st hbnd hsq o₁ hflip
        (separatedCountParity hsq o₁ hflip hloc)]
  · have hsame : o₁.isOut c = o₁.isOut a := by
      cases h1 : o₁.isOut a <;> cases h2 : o₁.isOut c <;> simp_all
    have hpres2 : ∀ (δ : W.Flag) (hδ : δ ∈ F.boundaryFlags),
        (κ₁.repair c d a b v hsq.swap).pathMatch δ hδ =
          κ₁.pathMatch δ hδ :=
      fun δ hδ =>
        (pathMatch_matchEq (repair_swap_matchEq hsq) hδ).symm.trans
          (hpres δ hδ)
    have heq2 : κ₂.MatchEq (κ₁.repair c d a b v hsq.swap) :=
      heq.trans
        (RelTransitionSystem.MatchEq.symm (repair_swap_matchEq hsq))
    by_cases hr1 : WalkReach κ₁ c a
    · -- same-component segment reversal
      obtain ⟨S, hseg⟩ := exists_repairSegment hsq o₁ hsame hr1
      refine step_conclusion hM st hbnd heq o₁
        (RelTransitionSystem.Orientation.segFlip hsq o₁ hsame hseg)
        (pathCanonical_of_entry_eq hpres
          (fun i hb hint =>
            segFlip_isOut_of_notMem hsq o₁ hsame hseg
              (entry_notMem_repairSegment hseg i)) hc₁) ?_
      rw [pathSign_congr hpres,
        throughSummand_exp hM st hbnd
          (RelTransitionSystem.Orientation.segFlip hsq o₁ hsame
            hseg)
          ((κ₁.repair a b c d v hsq).openCircuitCount),
        throughSummand_exp hM st hbnd o₁ κ₁.openCircuitCount,
        throughSummand_segFlip hM st hbnd hsq o₁ hsame hseg 0,
        neg_one_pow_congr_of_even
          (nonSeparatedSegmentParity hsq hr1)]
    · by_cases hr2 : WalkReach κ₁ a c
      · -- same component, swapped roles
        obtain ⟨S, hseg⟩ :=
          exists_repairSegment hsq.swap o₁ hsame.symm hr2
        refine step_conclusion hM st hbnd heq2 o₁
          (RelTransitionSystem.Orientation.segFlip hsq.swap o₁
            hsame.symm hseg)
          (pathCanonical_of_entry_eq hpres2
            (fun i hb hint =>
              segFlip_isOut_of_notMem hsq.swap o₁ hsame.symm hseg
                (entry_notMem_repairSegment hseg i)) hc₁) ?_
        rw [pathSign_congr hpres2,
          throughSummand_exp hM st hbnd
            (RelTransitionSystem.Orientation.segFlip hsq.swap o₁
              hsame.symm hseg)
            ((κ₁.repair c d a b v hsq.swap).openCircuitCount),
          throughSummand_exp hM st hbnd o₁ κ₁.openCircuitCount,
          throughSummand_segFlip hM st hbnd hsq.swap o₁ hsame.symm
            hseg 0,
          neg_one_pow_congr_of_even
            (nonSeparatedSegmentParity hsq.swap hr2)]
      · by_cases hpc : κ₁.PeriodicFlag c
        · -- `c` periodic on a distinct component: orbit flip
          have hdisj : ¬ OrbitFlag κ₁ c a := fun horb =>
            hr1 (walkReach_of_orbitFlag hpc hsame hsq.hac horb)
          have hflip2 : (o₁.flipOrbit hpc).isOut c =
              !(o₁.flipOrbit hpc).isOut a := by
            rw [flipOrbit_isOut_of_mem o₁ hpc (orbitFlag_self κ₁ c),
              flipOrbit_isOut_of_notMem o₁ hpc hdisj, hsame]
          refine step_conclusion hM st hbnd heq o₁
            (RelTransitionSystem.Orientation.transportRepair hsq
              (o₁.flipOrbit hpc) hflip2)
            (pathCanonical_of_entry_eq hpres
              (fun i hb hint =>
                flipOrbit_isOut_of_notMem o₁ hpc
                  (fun horb => entry_not_periodic hb hint
                    (periodicFlag_of_orbitFlag hpc horb))) hc₁) ?_
          rw [pathSign_congr hpres,
            throughSummand_repair hM st hbnd hsq (o₁.flipOrbit hpc)
              hflip2 (nonSeparatedMergeParity hsq hpc hdisj),
            throughSummand_flipOrbit hM st hbnd o₁ hpc
              κ₁.openCircuitCount]
        · by_cases hpa : κ₁.PeriodicFlag a
          · -- `a` periodic on a distinct component: swapped flip
            have hdisj2 : ¬ OrbitFlag κ₁ a c := fun horb =>
              hr2 (walkReach_of_orbitFlag hpa hsame.symm
                (Ne.symm hsq.hac) horb)
            have hflip2 : (o₁.flipOrbit hpa).isOut a =
                !(o₁.flipOrbit hpa).isOut c := by
              rw [flipOrbit_isOut_of_mem o₁ hpa
                  (orbitFlag_self κ₁ a),
                flipOrbit_isOut_of_notMem o₁ hpa hdisj2, hsame]
            refine step_conclusion hM st hbnd heq2 o₁
              (RelTransitionSystem.Orientation.transportRepair
                hsq.swap (o₁.flipOrbit hpa) hflip2)
              (pathCanonical_of_entry_eq hpres2
                (fun i hb hint =>
                  flipOrbit_isOut_of_notMem o₁ hpa
                    (fun horb => entry_not_periodic hb hint
                      (periodicFlag_of_orbitFlag hpa horb))) hc₁) ?_
            rw [pathSign_congr hpres2,
              throughSummand_repair hM st hbnd hsq.swap
                (o₁.flipOrbit hpa) hflip2
                (nonSeparatedMergeParity hsq.swap hpa hdisj2),
              throughSummand_flipOrbit hM st hbnd o₁ hpa
                κ₁.openCircuitCount]
          · -- both non-periodic: the localized square forces a
            -- same-chain configuration, hence a reach
            exfalso
            rcases hloc with ⟨hpa', -⟩ | ⟨β, hβ, hall⟩
            · exact hpa hpa'
            · rcases walkReach_or_walkReach_of_chain hβ o₁ hsame
                (Ne.symm hsq.hac) hsq.hc hsq.ha
                ((hall c (Or.inr (Or.inr (Or.inl rfl)))).resolve_left
                  hpc)
                ((hall a (Or.inl rfl)).resolve_left hpa)
                with h | h
              · exact hr1 h
              · exact hr2 h

end StepLedger

/-! ## The paired step and the dispatch -/

/-- **The paired two-path move** (a theorem downstream,
`pairedLedger`): a
`PairedStep` — two consecutive repairs `κ₁ → κmid → κ₂` whose net
effect preserves the boundary pairing — carries a path-canonical
orientation to a path-canonical orientation with the same
pathSign-weighted canonical summand.

The pair is the unit, not the half.  In the double-crossing
configuration each half is a two-path repair that *changes* the
pairing, so `stepLedger_single` does not apply to it: the per-half
vertex ledger negates the summand while re-pairing the boundary
colour blocks across the two chains.  Across the pair the second
repair undoes the re-routing of the first, the composite walk
change is supported on the two crossing squares, and the two vertex
negations cancel against the net chord-parity change.  Proved in
`PairedAssembly.lean`. -/
def PairedLedger : Prop :=
  ∀ {α : Type} [LinearOrder α] {W : Fragment α}
    {F : EdgeSubset W} {k ℓ : ℕ} (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (κ₁ κ₂ : F.RelTransitionSystem),
    PairedStep κ₁ κ₂ →
    ∀ (o₁ : κ₁.Orientation), PathCanonical o₁ →
    ∃ (o₂ : κ₂.Orientation), PathCanonical o₂ ∧
      pathSign κ₂ *
          F.throughSummand hM st hbnd o₂ κ₂.openCircuitCount =
        pathSign κ₁ *
          F.throughSummand hM st hbnd o₁ κ₁.openCircuitCount

/-- **The per-move ledger from the paired step**: the
`MatchPreservingStep` disjunct is discharged by
`stepLedger_single`; the `PairedStep` disjunct is the named input. -/
theorem matchPreservingLedger_of (HPaired : PairedLedger) :
    MatchPreservingLedger := by
  intro α _ W F k ℓ hM st hbnd κ₁ κ₂ hmove o₁ hc₁
  rcases hmove with hstep | hpair
  · exact stepLedger_single hM st hbnd κ₁ κ₂ hstep o₁ hc₁
  · exact HPaired hM st hbnd κ₁ κ₂ hpair o₁ hc₁

end EdgeSubset

end RS
