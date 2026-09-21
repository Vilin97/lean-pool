/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PathLedger

/-!
# The non-separated repair move: the flipped-segment ledger

The non-separated case of the per-move path ledger: a repair square
whose two re-paired edges are traversed coherently
(`o.isOut c = o.isOut a`).  The repaired walk reverses the segment
between the two match-pairs, and the transported orientation must
flip `isOut` exactly on the reversed segment.

## Main results

* `EdgeSubset.RepairSegment` — the abstract reversal-segment
  package: a pairing-closed set of internal flags containing `b`
  and `c`, avoiding `a` and `d`, and closed under the matching
  except at the two cut points `b`, `c`.
* `EdgeSubset.RelTransitionSystem.Orientation.segFlip` — the
  flipped-segment orientation of the repaired system (valid exactly
  because the flip meets the non-separated condition at the cuts).
* `EdgeSubset.throughSummand_segFlip` — **the flipped-segment
  ledger**: the constrained summand over the repaired system with
  the flipped-segment orientation equals the old summand at every
  fixed circuit exponent (total `+1`: the vertex transposition's
  `−1` cancels against the cut-block `∂`-sign, and the reversed
  segment telescopes to `∏_{f ∈ S} sign(φ f) = 1`).
* `EdgeSubset.WalkReach` / `EdgeSubset.exists_repairSegment` — the
  same-component configuration (the walk from `c` reaches `a`) and
  the construction of the reversal segment from it; covers both the
  same-circuit and the same-path (chain) reversal sub-cases.
* `EdgeSubset.squareLocalized_of_walkReach` — a same-component
  square is localized, so the path sign is untouched (committed
  `pathMatch_repair_of_localized`).
* `EdgeSubset.RepairSquare.swap` and `repair_swap_matchEq` — the
  square with the roles of the two re-paired edges exchanged
  produces the same repaired system.

## The two counting inputs

The ledger needs the circuit-count parity of the move, which is a
separate, orbit-counting question.  It is named here and proved in
the parity files:

* `NonSeparatedSegmentParity` — a same-component square preserves
  the circuit-count parity (the segment reversal maps the two
  traversal orbits of the affected component to two orbits, Δ = 0);
* `NonSeparatedMergeParity` — a square whose `c`-edge lies on a
  circuit not carrying `a` flips the count parity (the splice
  merges the circuit into `a`'s component, Δ = −1).
-/

namespace RS

open scoped Classical

variable {α : Type} {W : Fragment α}

namespace EdgeSubset

/-! ## The abstract reversal-segment package -/

section SegmentPackage

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex} {S : Finset W.Flag}

/-- The reversal-segment data for a repair square: a pairing-closed
set of internal flags containing the two cut flags `b`, `c`,
avoiding `a`, `d`, and closed under the matching away from the
cuts.  The repaired matching sends the cuts outside (`b ↦ d`,
`c ↦ a`), so the set is exactly the flag support of the walk
segment the repair reverses. -/
structure RepairSegment (κ : F.RelTransitionSystem)
    (a b c d : W.Flag) (S : Finset W.Flag) : Prop where
  hbS : b ∈ S
  hcS : c ∈ S
  haS : a ∉ S
  hdS : d ∉ S
  int_of_mem : ∀ f ∈ S, f ∈ F.internalFlags
  pairing_mem : ∀ f ∈ S, W.pairing f ∈ S
  match_mem : ∀ f ∈ S, f ≠ b → f ≠ c → κ.match_ f ∈ S

namespace RepairSegment

/-- The complement is closed under the pairing. -/
theorem pairing_notMem (h : RepairSegment κ a b c d S) {f : W.Flag}
    (hf : f ∉ S) : W.pairing f ∉ S := by
  intro hmem
  have h2 := h.pairing_mem _ hmem
  rw [W.pairing_invol] at h2
  exact hf h2

/-- The complement is closed under the matching away from `a`, `d`. -/
theorem match_notMem (h : RepairSegment κ a b c d S)
    (hsq : RepairSquare κ a b c d v) {f : W.Flag}
    (hf : f ∈ F.internalFlags) (hfS : f ∉ S)
    (h1 : f ≠ a) (h4 : f ≠ d) : κ.match_ f ∉ S := by
  intro hmem
  by_cases hb2 : κ.match_ f = b
  · refine h1 ?_
    have h3 := congrArg κ.match_ hb2
    rwa [κ.match_invol f hf, hsq.hmb] at h3
  by_cases hc2 : κ.match_ f = c
  · refine h4 ?_
    have h3 := congrArg κ.match_ hc2
    rwa [κ.match_invol f hf, hsq.hcd] at h3
  · have h3 := h.match_mem _ hmem hb2 hc2
    rw [κ.match_invol f hf] at h3
    exact hfS h3

/-- Boundary flags are never on the segment. -/
theorem notMem_boundaryFlag (h : RepairSegment κ a b c d S)
    (i : α) : W.boundaryFlag i ∉ S := by
  intro hmem
  obtain ⟨w, hw⟩ := F.attach_internal_of_mem (h.int_of_mem _ hmem)
  rw [W.attach_boundaryFlag] at hw
  cases hw

end RepairSegment

end SegmentPackage

/-! ## The flipped-segment orientation of the repaired system -/

/-- **The flipped-segment orientation**: flip `isOut` exactly on
the reversal segment.  The result is an orientation of the
*repaired* system: at the cuts the new matches `a ↔ c`, `b ↔ d`
flip orientation exactly because the move is non-separated
(`isOut c = isOut a`). -/
noncomputable def RelTransitionSystem.Orientation.segFlip
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a b c d : W.Flag} {v : W.Vertex} {S : Finset W.Flag}
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hsame : o.isOut c = o.isOut a)
    (hseg : RepairSegment κ a b c d S) :
    (κ.repair a b c d v hsq).Orientation where
  isOut f := if f ∈ S then !o.isOut f else o.isOut f
  match_flip := by
    have hbflip : o.isOut b = !o.isOut a := by
      rw [← hsq.hab]; exact o.match_flip a hsq.ha
    have hdflip : o.isOut d = !o.isOut c := by
      rw [← hsq.hcd]; exact o.match_flip c hsq.hc
    intro f hf
    show (if (κ.repair a b c d v hsq).match_ f ∈ S then
        !o.isOut ((κ.repair a b c d v hsq).match_ f)
      else o.isOut ((κ.repair a b c d v hsq).match_ f)) =
      !(if f ∈ S then !o.isOut f else o.isOut f)
    by_cases h1 : f = a
    · subst h1
      rw [RelTransitionSystem.repair_match_a hsq,
        if_pos hseg.hcS, if_neg hseg.haS, hsame]
    by_cases h3 : f = c
    · subst h3
      rw [RelTransitionSystem.repair_match_c hsq,
        if_neg hseg.haS, if_pos hseg.hcS, Bool.not_not, hsame]
    by_cases h2 : f = b
    · subst h2
      rw [RelTransitionSystem.repair_match_b hsq,
        if_neg hseg.hdS, if_pos hseg.hbS, Bool.not_not,
        hdflip, hbflip, hsame]
    by_cases h4 : f = d
    · subst h4
      rw [RelTransitionSystem.repair_match_d hsq,
        if_pos hseg.hbS, if_neg hseg.hdS, hbflip, hdflip, hsame]
    · rw [RelTransitionSystem.repair_match_of_ne hsq h1 h2 h3 h4]
      by_cases hfS : f ∈ S
      · rw [if_pos (hseg.match_mem f hfS h2 h3), if_pos hfS,
          o.match_flip f hf]
      · rw [if_neg (hseg.match_notMem hsq hf hfS h1 h4), if_neg hfS]
        exact o.match_flip f hf
  pairing_flip := by
    intro f hf hp
    show (if W.pairing f ∈ S then !o.isOut (W.pairing f)
        else o.isOut (W.pairing f)) =
      !(if f ∈ S then !o.isOut f else o.isOut f)
    by_cases hfS : f ∈ S
    · rw [if_pos (hseg.pairing_mem f hfS), if_pos hfS,
        o.pairing_flip f hf hp]
    · rw [if_neg (hseg.pairing_notMem hfS), if_neg hfS]
      exact o.pairing_flip f hf hp

section SegFlipEval

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex} {S : Finset W.Flag}

/-- Off the segment it is unchanged. -/
theorem segFlip_isOut_of_notMem (hsq : RepairSquare κ a b c d v)
    (o : κ.Orientation) (hsame : o.isOut c = o.isOut a)
    (hseg : RepairSegment κ a b c d S) {f : W.Flag} (hf : f ∉ S) :
    (RelTransitionSystem.Orientation.segFlip hsq o hsame
      hseg).isOut f = o.isOut f := if_neg hf

end SegFlipEval

/-! ## The `∂`-flip of the colouring on the segment -/

section SegColouring

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {S : Finset W.Flag}

/-- The `∂`-flip of a core odd colouring on the segment edges. -/
noncomputable def segFlipColouring (hSpair : ∀ f ∈ S, W.pairing f ∈ S) {ℓ : ℕ}
    (φ : F.CoreOddColouring ℓ) : F.CoreOddColouring ℓ :=
  ⟨fun g => if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g,
   fun g => by
     have hnot : ∀ f : W.Flag, f ∉ S → W.pairing f ∉ S := by
       intro f hf hmem
       have h2 := hSpair _ hmem
       rw [W.pairing_invol] at h2
       exact hf h2
     have hbeta : (if W.pairing g.val ∈ S then
           oddPartner ℓ (φ.val
             ⟨W.pairing g.val, F.pairing_mem_coreFlags g.prop⟩)
         else φ.val
           ⟨W.pairing g.val, F.pairing_mem_coreFlags g.prop⟩) =
         (if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g) := by
       by_cases hg : g.val ∈ S
       · rw [if_pos (hSpair _ hg), if_pos hg, φ.prop g]
       · rw [if_neg (hnot _ hg), if_neg hg, φ.prop g]
     exact hbeta⟩

/-- The segment-flipped colouring, unfolded. -/
theorem segFlipColouring_val (hSpair : ∀ f ∈ S, W.pairing f ∈ S) {ℓ : ℕ}
    (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags}) :
    (segFlipColouring hSpair φ).val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g :=
  rfl

/-- It is an involution, so it is a bijection of the colouring
sum. -/
theorem segFlipColouring_involutive
    (hSpair : ∀ f ∈ S, W.pairing f ∈ S) {ℓ : ℕ} :
    Function.Involutive
      (segFlipColouring hSpair (F := F) (ℓ := ℓ)) := by
  intro φ
  apply Subtype.ext
  funext g
  show (if g.val ∈ S then
      oddPartner ℓ ((segFlipColouring hSpair φ).val g)
    else (segFlipColouring hSpair φ).val g) = φ.val g
  by_cases hg : g.val ∈ S
  · rw [if_pos hg, segFlipColouring_val hSpair φ g, if_pos hg,
      oddPartner_invol]
  · rw [if_neg hg, segFlipColouring_val hSpair φ g, if_neg hg]

/-- The `∂`-flip preserves the odd boundary constraint when the
segment carries no boundary flags. -/
theorem coreOddBoundaryMatch_segFlipColouring {k ℓ : ℕ}
    (st : GenBoundaryState k ℓ α)
    (hSpair : ∀ f ∈ S, W.pairing f ∈ S)
    (hSb : ∀ i : α, W.boundaryFlag i ∉ S)
    (φ : F.CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st (segFlipColouring hSpair φ) ↔
      F.coreOddBoundaryMatch st φ := by
  have hval : ∀ (i : α) (hcore : W.boundaryFlag i ∈ F.coreFlags),
      (segFlipColouring hSpair φ).val ⟨W.boundaryFlag i, hcore⟩ =
        φ.val ⟨W.boundaryFlag i, hcore⟩ := by
    intro i hcore
    rw [segFlipColouring_val hSpair φ _, if_neg (hSb i)]
  unfold coreOddBoundaryMatch
  constructor
  · intro H i cc hst hcore
    rw [← hval i hcore]
    exact H i cc hst hcore
  · intro H i cc hst hcore
    rw [hval i hcore]
    exact H i cc hst hcore

end SegColouring

/-! ## The flipped-segment ledger -/

section SegLedger

variable {F : EdgeSubset W} {k ℓ : ℕ} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex} {S : Finset W.Flag}

/-! ### The pairing sign as a total function -/

private theorem flipVal_of_mem {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    (g : {g : W.Flag // g ∈ F.coreFlags}) (hg : g.val ∈ S) :
    φ'.val g = oddPartner ℓ (φ.val g) := by
  rw [hφ' g, if_pos hg]

private theorem flipVal_of_notMem {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    (g : {g : W.Flag // g ∈ F.coreFlags}) (hg : g.val ∉ S) :
    φ'.val g = φ.val g := by
  rw [hφ' g, if_neg hg]

/-! ### Vertex-local in-sets -/

/-- The in-flags at a vertex whose colours the flip on `S` leaves
alone. -/
noncomputable def keepS (S : Finset W.Flag)
    {κ₀ : F.RelTransitionSystem} (o₀ : κ₀.Orientation)
    (vv : W.Vertex) : Finset W.Flag :=
  (relInSetAt o₀ vv).filter (fun g => g ∉ S)

/-- The in-flags at a vertex whose colours the flip on `S`
reverses. -/
noncomputable def flipS (S : Finset W.Flag)
    {κ₀ : F.RelTransitionSystem} (o₀ : κ₀.Orientation)
    (vv : W.Vertex) : Finset W.Flag :=
  (relInSetAt o₀ vv).filter (fun g => g ∈ S)

private noncomputable def outbS (S : Finset W.Flag)
    {κ₀ : F.RelTransitionSystem} (o₀ : κ₀.Orientation)
    (vv : W.Vertex) : Finset W.Flag :=
  F.flags.filter
    (fun f => W.attach f = Sum.inl vv ∧ o₀.isOut f = true ∧ f ∈ S)

private noncomputable def diffAtS (S : Finset W.Flag)
    (vv : W.Vertex) : Finset W.Flag :=
  S.filter (fun g => W.attach g = Sum.inl vv)

/-- Membership in the kept part of a vertex's in-set. -/
theorem mem_keepS {κ₀ : F.RelTransitionSystem}
    {o₀ : κ₀.Orientation} {vv : W.Vertex} {g : W.Flag} :
    g ∈ keepS S o₀ vv ↔ g ∈ relInSetAt o₀ vv ∧ g ∉ S :=
  Finset.mem_filter

/-- Membership in the flipped part of a vertex's in-set. -/
theorem mem_flipS {κ₀ : F.RelTransitionSystem}
    {o₀ : κ₀.Orientation} {vv : W.Vertex} {g : W.Flag} :
    g ∈ flipS S o₀ vv ↔ g ∈ relInSetAt o₀ vv ∧ g ∈ S :=
  Finset.mem_filter

/-- The flip on `S` splits a vertex's in-set into the kept and the
flipped part. -/
theorem relInSetAt_val_split {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) :
    (relInSetAt o₀ vv).val =
      (keepS S o₀ vv).val + (flipS S o₀ vv).val := by
  unfold keepS flipS
  rw [Finset.filter_val, Finset.filter_val, add_comm]
  exact (Multiset.filter_add_not (fun g => g ∈ S)
    (relInSetAt o₀ vv).val).symm

/-- A product over a vertex's in-set splits along that partition. -/
theorem prod_relInSetAt_split {M : Type*} [CommMonoid M]
    {κ₀ : F.RelTransitionSystem} (o₀ : κ₀.Orientation)
    (vv : W.Vertex) (f : W.Flag → M) :
    ∏ g ∈ relInSetAt o₀ vv, f g =
      (∏ g ∈ flipS S o₀ vv, f g) * ∏ g ∈ keepS S o₀ vv, f g := by
  unfold flipS keepS
  exact (Finset.prod_filter_mul_prod_filter_not
    (relInSetAt o₀ vv) _ f).symm

private theorem mem_outbS {κ₀ : F.RelTransitionSystem}
    {o₀ : κ₀.Orientation} {vv : W.Vertex} {g : W.Flag} :
    g ∈ outbS S o₀ vv ↔
      g ∈ F.flags ∧ W.attach g = Sum.inl vv ∧
        o₀.isOut g = true ∧ g ∈ S :=
  Finset.mem_filter

private theorem mem_diffAtS {vv : W.Vertex} {g : W.Flag} :
    g ∈ diffAtS S vv ↔ g ∈ S ∧ W.attach g = Sum.inl vv :=
  Finset.mem_filter

private theorem keepS_disjoint_outbS {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) :
    Disjoint (keepS S o₀ vv) (outbS S o₀ vv) := by
  rw [Finset.disjoint_left]
  intro g hg1 hg2
  obtain ⟨-, -, -, hgS⟩ := mem_outbS.mp hg2
  exact (mem_keepS.mp hg1).2 hgS

private theorem flipS_disjoint_outbS {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) :
    Disjoint (flipS S o₀ vv) (outbS S o₀ vv) := by
  rw [Finset.disjoint_left]
  intro g hg1 hg2
  have h1 := (mem_relInSetAt.mp (mem_flipS.mp hg1).1).2.2
  obtain ⟨-, -, h2, -⟩ := mem_outbS.mp hg2
  rw [h1] at h2
  cases h2

private theorem match_injOn_flipS {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation) (vv : W.Vertex) :
    ∀ x ∈ flipS S o₀ vv, ∀ y ∈ flipS S o₀ vv,
      κ₀.match_ x = κ₀.match_ y → x = y := by
  intro x hx y hy hxy
  have hxint := relInSetAt_subset_internal (mem_flipS.mp hx).1
  have hyint := relInSetAt_subset_internal (mem_flipS.mp hy).1
  calc x = κ₀.match_ (κ₀.match_ x) := (κ₀.match_invol x hxint).symm
    _ = κ₀.match_ (κ₀.match_ y) := by rw [hxy]
    _ = y := κ₀.match_invol y hyint

private theorem diffAtS_split {κ₀ : F.RelTransitionSystem}
    (o₀ : κ₀.Orientation)
    (hSint : ∀ f ∈ S, f ∈ F.internalFlags) (vv : W.Vertex) :
    diffAtS S vv = (flipS S o₀ vv).disjUnion (outbS S o₀ vv)
      (flipS_disjoint_outbS o₀ vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion, mem_diffAtS, mem_flipS, mem_outbS,
    mem_relInSetAt]
  constructor
  · rintro ⟨hgS, hgat⟩
    have hgfl : g ∈ F.flags :=
      mem_flags_of_internalFlags F (hSint g hgS)
    cases hb : o₀.isOut g
    · exact Or.inl ⟨⟨hgfl, hgat, rfl⟩, hgS⟩
    · exact Or.inr ⟨hgfl, hgat, rfl, hgS⟩
  · rintro (⟨⟨_, hgat, _⟩, hgS⟩ | ⟨_, hgat, _, hgS⟩)
    · exact ⟨hgS, hgat⟩
    · exact ⟨hgS, hgat⟩

private theorem S_eq_biUnion_diffAtS (hSint : ∀ f ∈ S, f ∈ F.internalFlags) :
    S = Finset.univ.biUnion (fun vv => diffAtS S vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_biUnion]
  constructor
  · intro hg
    obtain ⟨vv, hvv⟩ := F.attach_internal_of_mem (hSint g hg)
    exact ⟨vv, Finset.mem_univ vv, mem_diffAtS.mpr ⟨hg, hvv⟩⟩
  · rintro ⟨vv, _, hvv⟩
    exact (mem_diffAtS.mp hvv).1

private theorem diffAtS_pairwiseDisjoint :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset W.Vertex))
      (fun vv => diffAtS S vv) := by
  intro x _ y _ hxy
  refine Finset.disjoint_left.mpr (fun g hgx hgy => hxy ?_)
  have h1 := (mem_diffAtS.mp hgx).2
  have h2 := (mem_diffAtS.mp hgy).2
  rw [h1] at h2
  exact Sum.inl.inj h2

private theorem prod_inSign_seg (hSpair : ∀ f ∈ S, W.pairing f ∈ S)
    (hScore : ∀ f ∈ S, f ∈ F.coreFlags)
    (φ : F.CoreOddColouring ℓ) :
    ∏ g ∈ S, inSign φ g = 1 := by
  refine Finset.prod_involution (fun g _ => W.pairing g) ?_ ?_ ?_ ?_
  · intro g hg
    rw [inSign_pairing φ (hScore g hg)]
    exact inSign_mul_self φ g
  · exact fun g _ _ => W.pairing_ne g
  · exact fun g hg => hSpair g hg
  · exact fun g _ => W.pairing_invol g

/-! ### The pair blocks -/

private theorem pairFn_eq {κ₀ : F.RelTransitionSystem}
    (φ : F.CoreOddColouring ℓ)
    (f : {f : W.Flag // f ∈ F.internalFlags}) {m : W.Flag}
    (hm : κ₀.match_ f.val = m) (hmi : m ∈ F.coreFlags) :
    F.coreOddPairFn κ₀ φ f =
      [φ.val ⟨f.val, F.internalFlags_subset_coreFlags f.prop⟩,
        oddPartner ℓ (φ.val ⟨m, hmi⟩)] := by
  subst hm
  rfl

/-! ### The parametric vertex data of the move -/

/-- The abstract data of the flipped-segment comparison at the
move's vertex, unifying the two orientation branches: `P` is the
kept in-flag whose partner changes (`P–R` re-pairs to `P–Q`), `Q`
the flipped in-flag, `R` the flipped out-flag re-paired to `T`,
`T` the kept out-flag. -/
private structure SegData (κ κ' : F.RelTransitionSystem)
    (o : κ.Orientation) (o' : κ'.Orientation)
    (S : Finset W.Flag) (v : W.Vertex) (P Q R T : W.Flag) :
    Prop where
  hiso : ∀ f, o'.isOut f = if f ∈ S then !o.isOut f else o.isOut f
  hSpair : ∀ f ∈ S, W.pairing f ∈ S
  hSint : ∀ f ∈ S, f ∈ F.internalFlags
  hSmatch : ∀ g ∈ S, g ≠ Q → g ≠ R → κ.match_ g ∈ S
  hSnot : ∀ g ∈ F.internalFlags, g ∉ S → g ≠ P → g ≠ T →
    κ.match_ g ∉ S
  hoff : ∀ g, g ≠ P → g ≠ Q → g ≠ R → g ≠ T →
    κ'.match_ g = κ.match_ g
  hPint : P ∈ F.internalFlags
  hQint : Q ∈ F.internalFlags
  hRint : R ∈ F.internalFlags
  hTint : T ∈ F.internalFlags
  hPS : P ∉ S
  hQS : Q ∈ S
  hRS : R ∈ S
  hTS : T ∉ S
  hPout : o.isOut P = false
  hQout : o.isOut Q = false
  hRout : o.isOut R = true
  hTout : o.isOut T = true
  hPv : W.attach P = Sum.inl v
  hQv : W.attach Q = Sum.inl v
  hRv : W.attach R = Sum.inl v
  hTv : W.attach T = Sum.inl v
  hmPR : κ.match_ P = R
  hmQT : κ.match_ Q = T
  hm'PQ : κ'.match_ P = Q
  hm'RT : κ'.match_ R = T

namespace SegData

variable {κ' : F.RelTransitionSystem} {o : κ.Orientation}
  {o' : κ'.Orientation} {P Q R T : W.Flag}

private theorem hmRP (hd : SegData κ κ' o o' S v P Q R T) :
    κ.match_ R = P := by
  rw [← hd.hmPR, κ.match_invol P hd.hPint]

private theorem hmTQ (hd : SegData κ κ' o o' S v P Q R T) :
    κ.match_ T = Q := by
  rw [← hd.hmQT, κ.match_invol Q hd.hQint]

private theorem hScore (hd : SegData κ κ' o o' S v P Q R T)
    {f : W.Flag} (hf : f ∈ S) : f ∈ F.coreFlags :=
  F.internalFlags_subset_coreFlags (hd.hSint f hf)

/-- A flag at another vertex avoids the square, so its repaired
match is untouched. -/
private theorem hoff_at (hd : SegData κ κ' o o' S v P Q R T)
    {vv : W.Vertex} (hvv : vv ≠ v) {g : W.Flag}
    (hg : W.attach g = Sum.inl vv) :
    κ'.match_ g = κ.match_ g := by
  have hne : ∀ x : W.Flag, W.attach x = Sum.inl v → g ≠ x := by
    intro x hx he
    rw [he, hx] at hg
    exact hvv (Sum.inl.inj hg).symm
  exact hd.hoff g (hne P hd.hPv) (hne Q hd.hQv) (hne R hd.hRv)
    (hne T hd.hTv)

/-- The in-set of the flipped orientation: the kept in-flags plus
the segment flags that were outgoing. -/
private theorem inb_flip (hd : SegData κ κ' o o' S v P Q R T)
    (vv : W.Vertex) :
    relInSetAt o' vv = (keepS S o vv).disjUnion (outbS S o vv)
      (keepS_disjoint_outbS o vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion, mem_relInSetAt, mem_keepS, mem_outbS,
    mem_relInSetAt]
  constructor
  · rintro ⟨hgfl, hgat, hgout⟩
    rw [hd.hiso g] at hgout
    by_cases hgS : g ∈ S
    · rw [if_pos hgS] at hgout
      refine Or.inr ⟨hgfl, hgat, ?_, hgS⟩
      cases hb : o.isOut g
      · rw [hb] at hgout
        cases hgout
      · rfl
    · rw [if_neg hgS] at hgout
      exact Or.inl ⟨⟨hgfl, hgat, hgout⟩, hgS⟩
  · rintro (⟨⟨hgfl, hgat, hgout⟩, hgS⟩ | ⟨hgfl, hgat, hgout, hgS⟩)
    · refine ⟨hgfl, hgat, ?_⟩
      rw [hd.hiso g, if_neg hgS]
      exact hgout
    · refine ⟨hgfl, hgat, ?_⟩
      rw [hd.hiso g, if_pos hgS, hgout]
      rfl

/-- Away from the move's vertex, the outgoing segment flags are the
matches of the flipped in-flags. -/
private theorem outbS_ne (hd : SegData κ κ' o o' S v P Q R T)
    {vv : W.Vertex} (hvv : vv ≠ v) :
    outbS S o vv = (flipS S o vv).image κ.match_ := by
  apply Finset.ext
  intro g
  rw [mem_outbS, Finset.mem_image]
  constructor
  · rintro ⟨hgfl, hgat, hgout, hgS⟩
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨vv, hgat⟩
    have hne : ∀ x : W.Flag, W.attach x = Sum.inl v → g ≠ x := by
      intro x hx he
      rw [he, hx] at hgat
      exact hvv (Sum.inl.inj hgat).symm
    have hmS : κ.match_ g ∈ S :=
      hd.hSmatch g hgS (hne Q hd.hQv) (hne R hd.hRv)
    have hmint := κ.match_mem g hgint
    refine ⟨κ.match_ g, mem_flipS.mpr ⟨mem_relInSetAt.mpr
      ⟨mem_flags_of_internalFlags F hmint,
        κ.match_vertex g hgint vv hgat, ?_⟩, hmS⟩,
      κ.match_invol g hgint⟩
    rw [o.match_flip g hgint, hgout]
    rfl
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨hxin, hxS⟩ := mem_flipS.mp hx
    obtain ⟨hxfl, hxat, hxout⟩ := mem_relInSetAt.mp hxin
    have hxint : x ∈ F.internalFlags :=
      mem_internalFlags_of hxfl ⟨vv, hxat⟩
    have hne : ∀ y : W.Flag, W.attach y = Sum.inl v → x ≠ y := by
      intro y hy he
      rw [he, hy] at hxat
      exact hvv (Sum.inl.inj hxat).symm
    have hmint := κ.match_mem x hxint
    refine ⟨mem_flags_of_internalFlags F hmint,
      κ.match_vertex x hxint vv hxat, ?_,
      hd.hSmatch x hxS (hne Q hd.hQv) (hne R hd.hRv)⟩
    rw [o.match_flip x hxint, hxout]
    rfl

private theorem Q_mem_flipS (hd : SegData κ κ' o o' S v P Q R T) :
    Q ∈ flipS S o v :=
  mem_flipS.mpr ⟨mem_relInSetAt.mpr
    ⟨mem_flags_of_internalFlags F hd.hQint, hd.hQv, hd.hQout⟩,
    hd.hQS⟩

private theorem P_mem_keepS (hd : SegData κ κ' o o' S v P Q R T) :
    P ∈ keepS S o v :=
  mem_keepS.mpr ⟨mem_relInSetAt.mpr
    ⟨mem_flags_of_internalFlags F hd.hPint, hd.hPv, hd.hPout⟩,
    hd.hPS⟩

/-- At the move's vertex, the outgoing segment flags are `R`
together with the matches of the flipped in-flags other than `Q`. -/
private theorem outbS_v (hd : SegData κ κ' o o' S v P Q R T) :
    outbS S o v =
      insert R (((flipS S o v).erase Q).image κ.match_) := by
  apply Finset.ext
  intro g
  rw [mem_outbS, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro ⟨hgfl, hgat, hgout, hgS⟩
    by_cases hgR : g = R
    · exact Or.inl hgR
    · have hgint : g ∈ F.internalFlags :=
        mem_internalFlags_of hgfl ⟨v, hgat⟩
      have hgQ : g ≠ Q := by
        intro he
        rw [he, hd.hQout] at hgout
        cases hgout
      have hmS : κ.match_ g ∈ S := hd.hSmatch g hgS hgQ hgR
      have hmint := κ.match_mem g hgint
      have hmQ : κ.match_ g ≠ Q := by
        intro he
        have h2 := congrArg κ.match_ he
        rw [κ.match_invol g hgint, hd.hmQT] at h2
        rw [h2] at hgS
        exact hd.hTS hgS
      refine Or.inr ⟨κ.match_ g, Finset.mem_erase.mpr
        ⟨hmQ, mem_flipS.mpr ⟨mem_relInSetAt.mpr
          ⟨mem_flags_of_internalFlags F hmint,
            κ.match_vertex g hgint v hgat, ?_⟩, hmS⟩⟩,
        κ.match_invol g hgint⟩
      rw [o.match_flip g hgint, hgout]
      rfl
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨mem_flags_of_internalFlags F hd.hRint, hd.hRv,
        hd.hRout, hd.hRS⟩
    · obtain ⟨hxQ, hxfli⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxin, hxS⟩ := mem_flipS.mp hxfli
      obtain ⟨hxfl, hxat, hxout⟩ := mem_relInSetAt.mp hxin
      have hxint : x ∈ F.internalFlags :=
        mem_internalFlags_of hxfl ⟨v, hxat⟩
      have hxR : x ≠ R := by
        intro he
        rw [he, hd.hRout] at hxout
        cases hxout
      have hmint := κ.match_mem x hxint
      refine ⟨mem_flags_of_internalFlags F hmint,
        κ.match_vertex x hxint v hxat, ?_,
        hd.hSmatch x hxS hxQ hxR⟩
      rw [o.match_flip x hxint, hxout]
      rfl

private theorem R_notMem_image (hd : SegData κ κ' o o' S v P Q R T) :
    R ∉ ((flipS S o v).erase Q).image κ.match_ := by
  intro hmem
  obtain ⟨x, hx, hxR⟩ := Finset.mem_image.mp hmem
  have hxint : x ∈ F.internalFlags :=
    relInSetAt_subset_internal (mem_flipS.mp (Finset.mem_erase.mp hx).2).1
  have h2 := congrArg κ.match_ hxR
  rw [κ.match_invol x hxint, hd.hmRP] at h2
  have hxS := (mem_flipS.mp (Finset.mem_erase.mp hx).2).2
  rw [h2] at hxS
  exact hd.hPS hxS

/-- Away from the move's vertex: the flipped vertex sign. -/
private theorem signAt_flip_ne (hd : SegData κ κ' o o' S v P Q R T)
    {vv : W.Vertex} (hvv : vv ≠ v) {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g) :
    F.coreOddSignAt o' φ' vv =
      (-1 : ℤ) ^ (flipS S o vv).card *
        (∏ g ∈ diffAtS S vv, inSign φ g) *
        F.coreOddSignAt o φ vv := by
  have hne : ∀ g : W.Flag, W.attach g = Sum.inl vv →
      ∀ x : W.Flag, W.attach x = Sum.inl v → g ≠ x := by
    intro g hg x hx he
    rw [he, hx] at hg
    exact hvv (Sum.inl.inj hg).symm
  rw [signAt_eq_prod o' φ' vv, signAt_eq_prod o φ vv,
    hd.inb_flip vv, Finset.prod_disjUnion, hd.outbS_ne hvv,
    Finset.prod_image (match_injOn_flipS o vv)]
  have hkeep : ∏ g ∈ keepS S o vv, inSign φ' (κ'.match_ g) =
      ∏ g ∈ keepS S o vv, inSign φ (κ.match_ g) := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    obtain ⟨hgin, hgS⟩ := mem_keepS.mp hg
    obtain ⟨hgfl, hgat, _⟩ := mem_relInSetAt.mp hgin
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨vv, hgat⟩
    rw [hd.hoff_at hvv hgat,
      inSign_flip_of_notMem hφ'
        (hd.hSnot g hgint hgS (hne g hgat P hd.hPv)
          (hne g hgat T hd.hTv))]
  have himg : ∏ g ∈ flipS S o vv,
      inSign φ' (κ'.match_ (κ.match_ g)) =
      ∏ g ∈ flipS S o vv, -inSign φ g := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    obtain ⟨hgin, hgS⟩ := mem_flipS.mp hg
    obtain ⟨hgfl, hgat, _⟩ := mem_relInSetAt.mp hgin
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨vv, hgat⟩
    have hmat : W.attach (κ.match_ g) = Sum.inl vv :=
      κ.match_vertex g hgint vv hgat
    rw [hd.hoff_at hvv hmat, κ.match_invol g hgint,
      inSign_flip_of_mem hφ' hgS
        (F.internalFlags_subset_coreFlags hgint)]
  rw [hkeep, himg, Finset.prod_neg,
    diffAtS_split o hd.hSint vv, Finset.prod_disjUnion,
    hd.outbS_ne hvv, Finset.prod_image (match_injOn_flipS o vv),
    prod_relInSetAt_split (S := S) o vv (fun g => inSign φ (κ.match_ g))]
  have hsq2 : (∏ g ∈ flipS S o vv, inSign φ (κ.match_ g)) *
      (∏ g ∈ flipS S o vv, inSign φ (κ.match_ g)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun g _ => inSign_mul_self φ _)
  have key : ∀ (A M K : ℤ) (cN : ℕ), M * M = 1 →
      K * ((-1) ^ cN * A) = (-1) ^ cN * (A * M) * (M * K) := by
    intro A M K cN hM
    calc K * ((-1) ^ cN * A)
        = (M * M) * (K * ((-1) ^ cN * A)) := by rw [hM, one_mul]
      _ = (-1) ^ cN * (A * M) * (M * K) := by ring
  exact key _ _ _ _ hsq2

/-- At the move's vertex: the flipped vertex sign. -/
private theorem signAt_flip_v (hd : SegData κ κ' o o' S v P Q R T)
    {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g) :
    F.coreOddSignAt o' φ' v =
      (-1 : ℤ) ^ (flipS S o v).card *
        (∏ g ∈ diffAtS S v, inSign φ g) *
        F.coreOddSignAt o φ v := by
  have hinjE : ∀ x ∈ (flipS S o v).erase Q,
      ∀ y ∈ (flipS S o v).erase Q,
        κ.match_ x = κ.match_ y → x = y :=
    fun x hx y hy => match_injOn_flipS o v x
      (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
  rw [signAt_eq_prod o' φ' v, hd.inb_flip v, Finset.prod_disjUnion,
    hd.outbS_v, Finset.prod_insert hd.R_notMem_image,
    Finset.prod_image hinjE,
    ← Finset.mul_prod_erase _ _ hd.P_mem_keepS]
  have hPterm : inSign φ' (κ'.match_ P) = -inSign φ Q := by
    rw [hd.hm'PQ, inSign_flip_of_mem hφ' hd.hQS
      (F.internalFlags_subset_coreFlags hd.hQint)]
  have hkeep : ∏ g ∈ (keepS S o v).erase P,
      inSign φ' (κ'.match_ g) =
      ∏ g ∈ (keepS S o v).erase P, inSign φ (κ.match_ g) := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    obtain ⟨hgP, hgk⟩ := Finset.mem_erase.mp hg
    obtain ⟨hgin, hgS⟩ := mem_keepS.mp hgk
    obtain ⟨hgfl, hgat, hgout⟩ := mem_relInSetAt.mp hgin
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨v, hgat⟩
    have hgQ : g ≠ Q := fun he => hgS (he ▸ hd.hQS)
    have hgR : g ≠ R := fun he => hgS (he ▸ hd.hRS)
    have hgT : g ≠ T := by
      intro he
      rw [he, hd.hTout] at hgout
      cases hgout
    rw [hd.hoff g hgP hgQ hgR hgT,
      inSign_flip_of_notMem hφ' (hd.hSnot g hgint hgS hgP hgT)]
  have hRterm : inSign φ' (κ'.match_ R) = inSign φ T := by
    rw [hd.hm'RT, inSign_flip_of_notMem hφ' hd.hTS]
  have himg : ∏ g ∈ (flipS S o v).erase Q,
      inSign φ' (κ'.match_ (κ.match_ g)) =
      ∏ g ∈ (flipS S o v).erase Q, -inSign φ g := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    obtain ⟨hgQ, hgfli⟩ := Finset.mem_erase.mp hg
    obtain ⟨hgin, hgS⟩ := mem_flipS.mp hgfli
    obtain ⟨hgfl, hgat, hgout⟩ := mem_relInSetAt.mp hgin
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨v, hgat⟩
    have hgR : g ≠ R := by
      intro he
      rw [he, hd.hRout] at hgout
      cases hgout
    have hmP : κ.match_ g ≠ P := by
      intro he
      have h2 := congrArg κ.match_ he
      rw [κ.match_invol g hgint, hd.hmPR] at h2
      exact hgR h2
    have hmQ : κ.match_ g ≠ Q := by
      intro he
      have h2 := congrArg κ.match_ he
      rw [κ.match_invol g hgint, hd.hmQT] at h2
      exact hd.hTS (h2 ▸ hgS)
    have hmR : κ.match_ g ≠ R := by
      intro he
      have h2 := congrArg κ.match_ he
      rw [κ.match_invol g hgint, hd.hmRP] at h2
      exact hd.hPS (h2 ▸ hgS)
    have hmT : κ.match_ g ≠ T := by
      intro he
      have h2 := congrArg κ.match_ he
      rw [κ.match_invol g hgint, hd.hmTQ] at h2
      exact hgQ h2
    rw [hd.hoff _ hmP hmQ hmR hmT, κ.match_invol g hgint,
      inSign_flip_of_mem hφ' hgS
        (F.internalFlags_subset_coreFlags hgint)]
  rw [hPterm, hkeep, hRterm, himg, Finset.prod_neg,
    signAt_eq_prod o φ v, diffAtS_split o hd.hSint v,
    Finset.prod_disjUnion, hd.outbS_v,
    Finset.prod_insert hd.R_notMem_image,
    Finset.prod_image hinjE,
    ← Finset.mul_prod_erase _ (fun g => inSign φ g)
      hd.Q_mem_flipS,
    prod_relInSetAt_split (S := S) o v (fun g => inSign φ (κ.match_ g)),
    ← Finset.mul_prod_erase _ (fun g => inSign φ (κ.match_ g))
      hd.Q_mem_flipS,
    ← Finset.mul_prod_erase _ (fun g => inSign φ (κ.match_ g))
      hd.P_mem_keepS,
    hd.hmPR, hd.hmQT,
    ← Finset.card_erase_add_one hd.Q_mem_flipS, pow_succ]
  have hr2 : inSign φ R * inSign φ R = 1 := inSign_mul_self φ R
  have hM2 : (∏ g ∈ (flipS S o v).erase Q,
      inSign φ (κ.match_ g)) *
      (∏ g ∈ (flipS S o v).erase Q, inSign φ (κ.match_ g)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one (fun g _ => inSign_mul_self φ _)
  have key : ∀ (q r t A M K : ℤ) (cN : ℕ), r * r = 1 → M * M = 1 →
      (-q * K) * (t * ((-1) ^ cN * A)) =
        (-1) ^ cN * -1 * ((q * A) * (r * M)) * ((t * M) * (r * K)) := by
    intro q r t A M K cN hr hM
    calc (-q * K) * (t * ((-1) ^ cN * A))
        = (r * r) * ((M * M) *
            ((-q * K) * (t * ((-1) ^ cN * A)))) := by
          rw [hr, hM, one_mul, one_mul]
      _ = (-1) ^ cN * -1 * ((q * A) * (r * M)) *
            ((t * M) * (r * K)) := by ring
  exact key _ _ _ _ _ _ _ hr2 hM2

/-- Away from the move's vertex: the flipped vertex list. -/
private theorem evalList_flip_ne (hd : SegData κ κ' o o' S v P Q R T)
    (hM : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {vv : W.Vertex} (hvv : vv ≠ v) {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g) :
    hM.evalOdd μ (F.coreOddListAt o' φ' vv) =
      (-1 : ℂ) ^ (flipS S o vv).card *
        hM.evalOdd μ (F.coreOddListAt o φ vv) := by
  have hne : ∀ g : W.Flag, W.attach g = Sum.inl vv →
      ∀ x : W.Flag, W.attach x = Sum.inl v → g ≠ x := by
    intro g hg x hx he
    rw [he, hx] at hg
    exact hvv (Sum.inl.inj hg).symm
  have Hk : ∀ g ∈ (keepS S o vv).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_keepS.mp (Finset.mem_toList.mp hg)).1
  have Hf : ∀ g ∈ (flipS S o vv).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_flipS.mp (Finset.mem_toList.mp hg)).1
  have H2 : ∀ g ∈ (keepS S o vv).toList ++
      (flipS S o vv).toList.map κ.match_,
      g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
      exact κ.match_mem x (Hf x hx)
  have H3 : ∀ g ∈ (keepS S o vv).toList ++ (flipS S o vv).toList,
      g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · exact Hf g hg
  -- ═══════ BOTH IN-FLAG ENUMERATIONS, SPLIT BY THE FLIP ═══════
  -- The unflipped in-flags are common to the two orientations; the
  -- flipped ones appear under the transported one through the
  -- matching.
  have hbase : (F.relInFlagsAt o vv).Perm
      ((keepS S o vv).toList ++ (flipS S o vv).toList) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o vv,
      ← Multiset.coe_add, Finset.coe_toList, Finset.coe_toList]
    exact relInSetAt_val_split (S := S) o vv
  have hbase' : (F.relInFlagsAt o' vv).Perm
      ((keepS S o vv).toList ++
        (flipS S o vv).toList.map κ.match_) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o' vv,
      ← Multiset.coe_add, Finset.coe_toList, ← Multiset.map_coe,
      Finset.coe_toList]
    rw [hd.inb_flip vv, Finset.disjUnion_val, hd.outbS_ne hvv,
      Finset.image_val_of_injOn (fun x hx y hy =>
        match_injOn_flipS o vv x (Finset.mem_coe.mp hx) y
          (Finset.mem_coe.mp hy))]
  unfold EdgeSubset.coreOddListAt
  simp only [List.attachWith]
  calc hM.evalOdd μ ((List.pmap Subtype.mk (F.relInFlagsAt o' vv)
        (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
        (F.coreOddPairFn κ' φ'))
      = hM.evalOdd μ ((List.pmap Subtype.mk
          ((keepS S o vv).toList ++
            (flipS S o vv).toList.map κ.match_) H2).flatMap
          (F.coreOddPairFn κ' φ')) := by
        have hp := hM.evalOdd_flatMap_perm μ
          (F.coreOddPairFn κ' φ') (fun _ => rfl)
          (perm_pmap Subtype.mk hbase'
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf) H2)
          []
        simpa using hp
    _ = hM.evalOdd μ
          ((List.pmap Subtype.mk (keepS S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipS S o vv).toList Hf).flatMap
            (fun fs => [pairB (κ₀ := κ) φ fs, pairA φ fs])) := by
        rw [List.pmap_append, List.flatMap_append]
        refine congrArg (hM.evalOdd μ) (congrArg₂
          (fun x y : List (Fin (2 * ℓ)) => x ++ y) ?_ ?_)
        · refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro g hg h₁ h₂
          obtain ⟨hgin, hgS⟩ :=
            mem_keepS.mp (Finset.mem_toList.mp hg)
          obtain ⟨hgfl, hgat, _⟩ := mem_relInSetAt.mp hgin
          have hgint : g ∈ F.internalFlags :=
            mem_internalFlags_of hgfl ⟨vv, hgat⟩
          have hmS : κ.match_ g ∉ S :=
            hd.hSnot g hgint hgS (hne g hgat P hd.hPv)
              (hne g hgat T hd.hTv)
          rw [pairFn_eq (κ₀ := κ') φ' ⟨g, h₁⟩
              (hd.hoff_at hvv hgat)
              (F.internalFlags_subset_coreFlags
                (κ.match_mem g hgint)),
            pairFn_eq (κ₀ := κ) φ ⟨g, h₂⟩ rfl
              (F.internalFlags_subset_coreFlags
                (κ.match_mem g hgint)),
            flipVal_of_notMem hφ' _ hgS,
            flipVal_of_notMem hφ' _ hmS]
        · rw [List.pmap_map]
          refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro x hx h₁ h₂
          obtain ⟨hxin, hxS⟩ :=
            mem_flipS.mp (Finset.mem_toList.mp hx)
          obtain ⟨hxfl, hxat, _⟩ := mem_relInSetAt.mp hxin
          have hxint : x ∈ F.internalFlags :=
            mem_internalFlags_of hxfl ⟨vv, hxat⟩
          have hmat : W.attach (κ.match_ x) = Sum.inl vv :=
            κ.match_vertex x hxint vv hxat
          have hmS : κ.match_ x ∈ S :=
            hd.hSmatch x hxS (hne x hxat Q hd.hQv)
              (hne x hxat R hd.hRv)
          have hm'eq : κ'.match_ (κ.match_ x) = x := by
            rw [hd.hoff_at hvv hmat, κ.match_invol x hxint]
          rw [pairFn_eq (κ₀ := κ') φ' ⟨κ.match_ x, h₁⟩ hm'eq
              (F.internalFlags_subset_coreFlags hxint),
            flipVal_of_mem hφ' _ hmS,
            flipVal_of_mem hφ' _ hxS,
            oddPartner_invol]
          rfl
    _ = (-1 : ℂ) ^ (flipS S o vv).card * hM.evalOdd μ
          ((List.pmap Subtype.mk (keepS S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipS S o vv).toList Hf).flatMap
            (fun fs => [pairA φ fs, pairB (κ₀ := κ) φ fs])) := by
        have hrev := evalOdd_flatMap_rev hM μ (pairA φ)
          (pairB (κ₀ := κ) φ)
          (List.pmap Subtype.mk (flipS S o vv).toList Hf)
          ((List.pmap Subtype.mk (keepS S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ))
        rw [hrev, List.length_pmap, Finset.length_toList]
    _ = (-1 : ℂ) ^ (flipS S o vv).card * hM.evalOdd μ
          ((List.pmap Subtype.mk
            ((keepS S o vv).toList ++ (flipS S o vv).toList)
            H3).flatMap (F.coreOddPairFn κ φ)) := by
        rw [List.pmap_append, List.flatMap_append]
        rw [coreOddPairFn_eq' (κ₀ := κ) φ]
    _ = (-1 : ℂ) ^ (flipS S o vv).card * hM.evalOdd μ
          ((List.pmap Subtype.mk (F.relInFlagsAt o vv)
            (fun _ hf =>
              F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
            (F.coreOddPairFn κ φ)) := by
        have hp := hM.evalOdd_flatMap_perm μ (F.coreOddPairFn κ φ)
          (fun _ => rfl)
          (perm_pmap Subtype.mk hbase.symm H3
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf))
          []
        simp only [List.nil_append] at hp
        rw [hp]

/-- At the move's vertex: the flipped vertex list. -/
private theorem evalList_flip_v (hd : SegData κ κ' o o' S v P Q R T)
    (hM : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g) :
    hM.evalOdd μ (F.coreOddListAt o' φ' v) =
      (-1 : ℂ) ^ (flipS S o v).card *
        hM.evalOdd μ (F.coreOddListAt o φ v) := by
  have hPint := hd.hPint
  have hQint := hd.hQint
  have hRint := hd.hRint
  have hTint := hd.hTint
  have HkE : ∀ g ∈ ((keepS S o v).erase P).toList,
      g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_keepS.mp (Finset.mem_of_mem_erase
        (Finset.mem_toList.mp hg))).1
  have HfE : ∀ g ∈ ((flipS S o v).erase Q).toList,
      g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_flipS.mp (Finset.mem_of_mem_erase
        (Finset.mem_toList.mp hg))).1
  have Hold : ∀ g ∈ P :: (((keepS S o v).erase P).toList ++
      Q :: ((flipS S o v).erase Q).toList), g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hPint
    rcases List.mem_append.mp hg with hg | hg
    · exact HkE g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hQint
    · exact HfE g hg
  have Hnew : ∀ g ∈ P :: (((keepS S o v).erase P).toList ++
      R :: (((flipS S o v).erase Q).toList.map κ.match_)),
      g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hPint
    rcases List.mem_append.mp hg with hg | hg
    · exact HkE g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact hRint
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hg
      exact κ.match_mem x (HfE x hx)
  -- ═══════ SPLITTING THE IN-FLAGS INTO KEPT AND FLIPPED ═══════
  have hkeepval : (keepS S o v).val =
      P ::ₘ ((keepS S o v).erase P).val := by
    rw [Finset.erase_val]
    exact (Multiset.cons_erase
      (Finset.mem_def.mp hd.P_mem_keepS)).symm
  have hflipval : (flipS S o v).val =
      Q ::ₘ ((flipS S o v).erase Q).val := by
    rw [Finset.erase_val]
    exact (Multiset.cons_erase
      (Finset.mem_def.mp hd.Q_mem_flipS)).symm
  -- ═══════ THE TWO ENUMERATIONS ARE THE SAME MULTISET ═══════
  have hbase : (F.relInFlagsAt o v).Perm
      (P :: (((keepS S o v).erase P).toList ++
        Q :: ((flipS S o v).erase Q).toList)) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o v,
      ← Multiset.cons_coe, ← Multiset.coe_add,
      ← Multiset.cons_coe, Finset.coe_toList, Finset.coe_toList,
      relInSetAt_val_split (S := S) o v, hkeepval, hflipval,
      Multiset.cons_add]
  have hinjE : ∀ x ∈ ((flipS S o v).erase Q : Finset W.Flag),
      ∀ y ∈ ((flipS S o v).erase Q : Finset W.Flag),
        κ.match_ x = κ.match_ y → x = y :=
    fun x hx y hy => match_injOn_flipS o v x
      (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy)
  have hbase' : (F.relInFlagsAt o' v).Perm
      (P :: (((keepS S o v).erase P).toList ++
        R :: (((flipS S o v).erase Q).toList.map κ.match_))) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o' v,
      ← Multiset.cons_coe, ← Multiset.coe_add,
      ← Multiset.cons_coe, ← Multiset.map_coe,
      Finset.coe_toList, Finset.coe_toList,
      hd.inb_flip v, Finset.disjUnion_val, hkeepval,
      hd.outbS_v, Finset.insert_val_of_notMem hd.R_notMem_image,
      Finset.image_val_of_injOn (fun x hx y hy =>
        hinjE x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy)),
      Multiset.cons_add]
  unfold EdgeSubset.coreOddListAt
  simp only [List.attachWith]
  -- ═══════ THE SIGN COMPUTATION ═══════
  calc hM.evalOdd μ ((List.pmap Subtype.mk (F.relInFlagsAt o' v)
        (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
        (F.coreOddPairFn κ' φ'))
      = hM.evalOdd μ ((List.pmap Subtype.mk
          (P :: (((keepS S o v).erase P).toList ++
            R :: (((flipS S o v).erase Q).toList.map κ.match_)))
          Hnew).flatMap (F.coreOddPairFn κ' φ')) := by
        have hp := hM.evalOdd_flatMap_perm μ
          (F.coreOddPairFn κ' φ') (fun _ => rfl)
          (perm_pmap Subtype.mk hbase'
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)
            Hnew) []
        simpa using hp
    _ = hM.evalOdd μ
          ([φ.val ⟨P, F.internalFlags_subset_coreFlags hPint⟩,
            φ.val ⟨Q, F.internalFlags_subset_coreFlags hQint⟩] ++
          (((List.pmap Subtype.mk ((keepS S o v).erase P).toList
              HkE).flatMap (F.coreOddPairFn κ φ)) ++
            ([oddPartner ℓ (φ.val ⟨R,
                F.internalFlags_subset_coreFlags hRint⟩),
              oddPartner ℓ (φ.val ⟨T,
                F.internalFlags_subset_coreFlags hTint⟩)] ++
              (List.pmap Subtype.mk
                ((flipS S o v).erase Q).toList HfE).flatMap
                (fun fs => [pairB (κ₀ := κ) φ fs,
                  pairA φ fs])))) := by
        simp only [List.pmap, List.pmap_append, List.flatMap_cons,
          List.flatMap_append]
        refine congrArg (hM.evalOdd μ) (congrArg₂
          (fun x y : List (Fin (2 * ℓ)) => x ++ y) ?_
          (congrArg₂ (fun x y : List (Fin (2 * ℓ)) => x ++ y) ?_
            (congrArg₂ (fun x y : List (Fin (2 * ℓ)) => x ++ y)
              ?_ ?_)))
        · rw [pairFn_eq (κ₀ := κ') φ' _ hd.hm'PQ
              (F.internalFlags_subset_coreFlags hQint),
            flipVal_of_notMem hφ' _ hd.hPS,
            flipVal_of_mem hφ' _ hd.hQS, oddPartner_invol]
        · refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro g hg h₁ h₂
          obtain ⟨hgP, hgk⟩ := Finset.mem_erase.mp
            (Finset.mem_toList.mp hg)
          obtain ⟨hgin, hgS⟩ := mem_keepS.mp hgk
          obtain ⟨hgfl, hgat, hgout⟩ := mem_relInSetAt.mp hgin
          have hgint : g ∈ F.internalFlags :=
            mem_internalFlags_of hgfl ⟨v, hgat⟩
          have hgQ : g ≠ Q := fun he => hgS (he ▸ hd.hQS)
          have hgR : g ≠ R := fun he => hgS (he ▸ hd.hRS)
          have hgT : g ≠ T := by
            intro he
            rw [he, hd.hTout] at hgout
            cases hgout
          have hmS : κ.match_ g ∉ S :=
            hd.hSnot g hgint hgS hgP hgT
          rw [pairFn_eq (κ₀ := κ') φ' ⟨g, h₁⟩
              (hd.hoff g hgP hgQ hgR hgT)
              (F.internalFlags_subset_coreFlags
                (κ.match_mem g hgint)),
            pairFn_eq (κ₀ := κ) φ ⟨g, h₂⟩ rfl
              (F.internalFlags_subset_coreFlags
                (κ.match_mem g hgint)),
            flipVal_of_notMem hφ' _ hgS,
            flipVal_of_notMem hφ' _ hmS]
        · rw [pairFn_eq (κ₀ := κ') φ' _ hd.hm'RT
              (F.internalFlags_subset_coreFlags hTint),
            flipVal_of_mem hφ' _ hd.hRS,
            flipVal_of_notMem hφ' _ hd.hTS]
        · rw [List.pmap_map]
          refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro x hx h₁ h₂
          obtain ⟨hxQ, hxfli⟩ := Finset.mem_erase.mp
            (Finset.mem_toList.mp hx)
          obtain ⟨hxin, hxS⟩ := mem_flipS.mp hxfli
          obtain ⟨hxfl, hxat, hxout⟩ := mem_relInSetAt.mp hxin
          have hxint : x ∈ F.internalFlags :=
            mem_internalFlags_of hxfl ⟨v, hxat⟩
          have hxR : x ≠ R := by
            intro he
            rw [he, hd.hRout] at hxout
            cases hxout
          have hmS : κ.match_ x ∈ S := hd.hSmatch x hxS hxQ hxR
          have hmP : κ.match_ x ≠ P := by
            intro he
            have h2 := congrArg κ.match_ he
            rw [κ.match_invol x hxint, hd.hmPR] at h2
            exact hxR h2
          have hmQ : κ.match_ x ≠ Q := by
            intro he
            have h2 := congrArg κ.match_ he
            rw [κ.match_invol x hxint, hd.hmQT] at h2
            exact hd.hTS (h2 ▸ hxS)
          have hmR : κ.match_ x ≠ R := by
            intro he
            have h2 := congrArg κ.match_ he
            rw [κ.match_invol x hxint, hd.hmRP] at h2
            exact hd.hPS (h2 ▸ hxS)
          have hmT : κ.match_ x ≠ T := by
            intro he
            have h2 := congrArg κ.match_ he
            rw [κ.match_invol x hxint, hd.hmTQ] at h2
            exact hxQ h2
          have hm'eq : κ'.match_ (κ.match_ x) = x := by
            rw [hd.hoff _ hmP hmQ hmR hmT,
              κ.match_invol x hxint]
          rw [pairFn_eq (κ₀ := κ') φ' ⟨κ.match_ x, h₁⟩ hm'eq
              (F.internalFlags_subset_coreFlags hxint),
            flipVal_of_mem hφ' _ hmS,
            flipVal_of_mem hφ' _ hxS,
            oddPartner_invol]
          rfl
    _ = (-1 : ℂ) ^ ((flipS S o v).erase Q).card *
        hM.evalOdd μ
          ([φ.val ⟨P, F.internalFlags_subset_coreFlags hPint⟩,
            φ.val ⟨Q, F.internalFlags_subset_coreFlags hQint⟩] ++
          (((List.pmap Subtype.mk ((keepS S o v).erase P).toList
              HkE).flatMap (F.coreOddPairFn κ φ)) ++
            ([oddPartner ℓ (φ.val ⟨R,
                F.internalFlags_subset_coreFlags hRint⟩),
              oddPartner ℓ (φ.val ⟨T,
                F.internalFlags_subset_coreFlags hTint⟩)] ++
              (List.pmap Subtype.mk
                ((flipS S o v).erase Q).toList HfE).flatMap
                (fun fs => [pairA φ fs,
                  pairB (κ₀ := κ) φ fs])))) := by
        have hrev := evalOdd_flatMap_rev hM μ (pairA φ)
          (pairB (κ₀ := κ) φ)
          (List.pmap Subtype.mk ((flipS S o v).erase Q).toList HfE)
          ([φ.val ⟨P, F.internalFlags_subset_coreFlags hPint⟩,
            φ.val ⟨Q, F.internalFlags_subset_coreFlags hQint⟩] ++
          (((List.pmap Subtype.mk ((keepS S o v).erase P).toList
              HkE).flatMap (F.coreOddPairFn κ φ)) ++
            [oddPartner ℓ (φ.val ⟨R,
                F.internalFlags_subset_coreFlags hRint⟩),
              oddPartner ℓ (φ.val ⟨T,
                F.internalFlags_subset_coreFlags hTint⟩)]))
        simp only [List.append_assoc, List.cons_append,
          List.nil_append, List.length_pmap,
          Finset.length_toList] at hrev ⊢
        rw [hrev]
    _ = (-1 : ℂ) ^ ((flipS S o v).erase Q).card * -hM.evalOdd μ
          ([φ.val ⟨P, F.internalFlags_subset_coreFlags hPint⟩,
            oddPartner ℓ (φ.val ⟨R,
              F.internalFlags_subset_coreFlags hRint⟩)] ++
          (((List.pmap Subtype.mk ((keepS S o v).erase P).toList
              HkE).flatMap (F.coreOddPairFn κ φ)) ++
            ([φ.val ⟨Q, F.internalFlags_subset_coreFlags hQint⟩,
              oddPartner ℓ (φ.val ⟨T,
                F.internalFlags_subset_coreFlags hTint⟩)] ++
              (List.pmap Subtype.mk
                ((flipS S o v).erase Q).toList HfE).flatMap
                (fun fs => [pairA φ fs,
                  pairB (κ₀ := κ) φ fs])))) := by
        have htr := MixedFunctional.evalOdd_transpose hM μ
          ((List.pmap Subtype.mk ((keepS S o v).erase P).toList
            HkE).flatMap (F.coreOddPairFn κ φ))
          [φ.val ⟨P, F.internalFlags_subset_coreFlags hPint⟩]
          (oddPartner ℓ (φ.val ⟨T,
            F.internalFlags_subset_coreFlags hTint⟩) ::
            (List.pmap Subtype.mk
              ((flipS S o v).erase Q).toList HfE).flatMap
              (fun fs => [pairA φ fs, pairB (κ₀ := κ) φ fs]))
          (oddPartner ℓ (φ.val ⟨R,
            F.internalFlags_subset_coreFlags hRint⟩))
          (φ.val ⟨Q, F.internalFlags_subset_coreFlags hQint⟩)
        simp only [List.cons_append, List.nil_append] at htr ⊢
        rw [htr]
    _ = (-1 : ℂ) ^ (flipS S o v).card * hM.evalOdd μ
          ((List.pmap Subtype.mk
            (P :: (((keepS S o v).erase P).toList ++
              Q :: ((flipS S o v).erase Q).toList))
            Hold).flatMap (F.coreOddPairFn κ φ)) := by
        rw [← Finset.card_erase_add_one hd.Q_mem_flipS, pow_succ]
        simp only [List.pmap, List.pmap_append, List.flatMap_cons,
          List.flatMap_append]
        rw [pairFn_eq (κ₀ := κ) φ
            ⟨P, hPint⟩ hd.hmPR
            (F.internalFlags_subset_coreFlags hRint),
          pairFn_eq (κ₀ := κ) φ ⟨Q, hQint⟩ hd.hmQT
            (F.internalFlags_subset_coreFlags hTint),
          coreOddPairFn_eq' (κ₀ := κ) φ]
        simp only [List.cons_append, List.nil_append]
        ring
    _ = (-1 : ℂ) ^ (flipS S o v).card * hM.evalOdd μ
          ((List.pmap Subtype.mk (F.relInFlagsAt o v)
            (fun _ hf =>
              F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
            (F.coreOddPairFn κ φ)) := by
        have hp := hM.evalOdd_flatMap_perm μ (F.coreOddPairFn κ φ)
          (fun _ => rfl)
          (perm_pmap Subtype.mk hbase.symm Hold
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf))
          []
        simp only [List.nil_append] at hp
        rw [hp]

/-- Boundary flags are never on the segment. -/
private theorem hSb (hd : SegData κ κ' o o' S v P Q R T) (i : α) :
    W.boundaryFlag i ∉ S := by
  intro hmem
  obtain ⟨w, hw⟩ := F.attach_internal_of_mem (hd.hSint _ hmem)
  rw [W.attach_boundaryFlag] at hw
  cases hw

/-- The combined vertex factor of the flipped comparison. -/
private theorem vertexFactor (hd : SegData κ κ' o o' S v P Q R T)
    (hM : MixedFunctional k ℓ) (μ : Multiset (Fin k))
    {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    (vv : W.Vertex) :
    (F.coreOddSignAt o' φ' vv : ℂ) *
        hM.evalOdd μ (F.coreOddListAt o' φ' vv) =
      (∏ g ∈ diffAtS S vv, ((inSign φ g : ℤ) : ℂ)) *
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd μ (F.coreOddListAt o φ vv)) := by
  have hsign : F.coreOddSignAt o' φ' vv =
      (-1 : ℤ) ^ (flipS S o vv).card *
        (∏ g ∈ diffAtS S vv, inSign φ g) *
        F.coreOddSignAt o φ vv := by
    by_cases hvv : vv = v
    · subst hvv
      exact hd.signAt_flip_v hφ'
    · exact hd.signAt_flip_ne hvv hφ'
  have hlist : hM.evalOdd μ (F.coreOddListAt o' φ' vv) =
      (-1 : ℂ) ^ (flipS S o vv).card *
        hM.evalOdd μ (F.coreOddListAt o φ vv) := by
    by_cases hvv : vv = v
    · subst hvv
      exact hd.evalList_flip_v hM μ hφ'
    · exact hd.evalList_flip_ne hM μ hvv hφ'
  rw [hsign, hlist]
  have hsq : (-1 : ℂ) ^ (flipS S o vv).card *
      (-1 : ℂ) ^ (flipS S o vv).card = 1 := by
    rw [← mul_pow]
    norm_num
  push_cast
  calc ((-1 : ℂ) ^ (flipS S o vv).card *
        (∏ g ∈ diffAtS S vv, ((inSign φ g : ℤ) : ℂ)) *
        (F.coreOddSignAt o φ vv : ℂ)) *
      ((-1 : ℂ) ^ (flipS S o vv).card *
        hM.evalOdd μ (F.coreOddListAt o φ vv)) =
      ((-1 : ℂ) ^ (flipS S o vv).card *
        (-1 : ℂ) ^ (flipS S o vv).card) *
      ((∏ g ∈ diffAtS S vv, ((inSign φ g : ℤ) : ℂ)) *
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd μ (F.coreOddListAt o φ vv))) := by
        ring
    _ = (∏ g ∈ diffAtS S vv, ((inSign φ g : ℤ) : ℂ)) *
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd μ (F.coreOddListAt o φ vv)) := by
        rw [hsq, one_mul]

/-- The vertex-product identity of the flipped comparison. -/
private theorem vertexProd (hd : SegData κ κ' o o' S v P Q R T)
    (hM : MixedFunctional k ℓ) {φ φ' : F.CoreOddColouring ℓ}
    (hφ' : ∀ g, φ'.val g =
      if g.val ∈ S then oddPartner ℓ (φ.val g) else φ.val g)
    (μf : W.Vertex → Multiset (Fin k)) :
    ∏ vv : W.Vertex,
        ((F.coreOddSignAt o' φ' vv : ℂ) *
          hM.evalOdd (μf vv) (F.coreOddListAt o' φ' vv)) =
      ∏ vv : W.Vertex,
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd (μf vv) (F.coreOddListAt o φ vv)) := by
  have hglobal : ∏ vv : W.Vertex,
      ∏ g ∈ diffAtS S vv, ((inSign φ g : ℤ) : ℂ) = 1 := by
    have h1 : ∏ vv : W.Vertex,
        ∏ g ∈ diffAtS S vv, inSign φ g = 1 := by
      rw [← Finset.prod_biUnion diffAtS_pairwiseDisjoint,
        ← S_eq_biUnion_diffAtS hd.hSint]
      exact prod_inSign_seg hd.hSpair (fun f hf => hd.hScore hf) φ
    have h2 : ((∏ vv : W.Vertex,
        ∏ g ∈ diffAtS S vv, inSign φ g : ℤ) : ℂ) = 1 := by
      rw [h1]
      norm_num
    push_cast at h2
    exact h2
  rw [Finset.prod_congr rfl
      (fun vv _ => hd.vertexFactor hM (μf vv) hφ' vv),
    Finset.prod_mul_distrib, hglobal, one_mul]

/-- The colouring-sum identity of the flipped comparison. -/
private theorem phiSum (hd : SegData κ κ' o o' S v P Q R T)
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (μf : W.Vertex → Multiset (Fin k)) :
    ∑ φ : F.CoreOddColouring ℓ,
        (if F.coreOddBoundaryMatch st φ then
          ∏ vv : W.Vertex, ((F.coreOddSignAt o' φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o' φ vv))
        else 0) =
      ∑ φ : F.CoreOddColouring ℓ,
        (if F.coreOddBoundaryMatch st φ then
          ∏ vv : W.Vertex, ((F.coreOddSignAt o φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o φ vv))
        else 0) := by
  refine ((Equiv.sum_comp (Function.Involutive.toPerm _
      (segFlipColouring_involutive hd.hSpair (ℓ := ℓ)))
      _).symm).trans
    (Finset.sum_congr rfl (fun φ _ => ?_))
  show (if F.coreOddBoundaryMatch st
        (segFlipColouring hd.hSpair φ) then
      ∏ vv : W.Vertex,
        ((F.coreOddSignAt o' (segFlipColouring hd.hSpair φ)
            vv : ℂ) *
          hM.evalOdd (μf vv)
            (F.coreOddListAt o' (segFlipColouring hd.hSpair φ) vv))
      else 0) =
    (if F.coreOddBoundaryMatch st φ then
      ∏ vv : W.Vertex, ((F.coreOddSignAt o φ vv : ℂ) *
        hM.evalOdd (μf vv) (F.coreOddListAt o φ vv))
    else 0)
  exact if_congr
    (coreOddBoundaryMatch_segFlipColouring st hd.hSpair hd.hSb φ)
    (hd.vertexProd hM (fun g => rfl) μf) rfl

end SegData

/-- The parametric core of the flipped-segment ledger. -/
private theorem throughSummand_seg_core [LinearOrder α]
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {κ' : F.RelTransitionSystem} {o : κ.Orientation}
    {o' : κ'.Orientation} {P Q R T : W.Flag}
    (hd : SegData κ κ' o o' S v P Q R T) (n : ℕ) :
    F.throughSummand hM st hbnd o' n =
      F.throughSummand hM st hbnd o n := by
  unfold EdgeSubset.throughSummand
  apply congrArg (fun z : ℂ => ((-1 : ℂ) ^ n) * F.throughProduct st * z)
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  exact if_congr Iff.rfl (hd.phiSum hM st (F.evenColoursAt ψ)) rfl

/-- **The flipped-segment ledger**: the constrained summand of the
repaired system over the flipped-segment orientation and equals
the old summand at every fixed circuit exponent. -/
theorem throughSummand_segFlip [LinearOrder α]
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hsame : o.isOut c = o.isOut a)
    (hseg : RepairSegment κ a b c d S) (n : ℕ) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.segFlip hsq o hsame hseg)
        n =
      F.throughSummand hM st hbnd o n := by
  have hbflip : o.isOut b = !o.isOut a := by
    rw [← hsq.hab]
    exact o.match_flip a hsq.ha
  have hdflip : o.isOut d = !o.isOut c := by
    rw [← hsq.hcd]
    exact o.match_flip c hsq.hc
  cases hxa : o.isOut a with
  | false =>
    refine throughSummand_seg_core hM st hbnd (S := S) (v := v)
      (P := a) (Q := c) (R := b) (T := d) ?_ n
    exact
      { hiso := fun f => rfl
        hSpair := hseg.pairing_mem
        hSint := hseg.int_of_mem
        hSmatch := fun g hg hgQ hgR => hseg.match_mem g hg hgR hgQ
        hSnot := fun g hgint hgS hgP hgT =>
          hseg.match_notMem hsq hgint hgS hgP hgT
        hoff := fun g h1 h2 h3 h4 =>
          RelTransitionSystem.repair_match_of_ne hsq h1 h3 h2 h4
        hPint := hsq.ha
        hQint := hsq.hc
        hRint := hsq.hb
        hTint := hsq.hd
        hPS := hseg.haS
        hQS := hseg.hcS
        hRS := hseg.hbS
        hTS := hseg.hdS
        hPout := hxa
        hQout := hsame.trans hxa
        hRout := by rw [hbflip, hxa]; rfl
        hTout := by rw [hdflip, hsame, hxa]; rfl
        hPv := hsq.hav
        hQv := hsq.hcv
        hRv := hsq.hbv
        hTv := hsq.hdv
        hmPR := hsq.hab
        hmQT := hsq.hcd
        hm'PQ := RelTransitionSystem.repair_match_a hsq
        hm'RT := RelTransitionSystem.repair_match_b hsq }
  | true =>
    refine throughSummand_seg_core hM st hbnd (S := S) (v := v)
      (P := d) (Q := b) (R := c) (T := a) ?_ n
    exact
      { hiso := fun f => rfl
        hSpair := hseg.pairing_mem
        hSint := hseg.int_of_mem
        hSmatch := fun g hg hgQ hgR => hseg.match_mem g hg hgQ hgR
        hSnot := fun g hgint hgS hgP hgT =>
          hseg.match_notMem hsq hgint hgS hgT hgP
        hoff := fun g h1 h2 h3 h4 =>
          RelTransitionSystem.repair_match_of_ne hsq h4 h2 h3 h1
        hPint := hsq.hd
        hQint := hsq.hb
        hRint := hsq.hc
        hTint := hsq.ha
        hPS := hseg.hdS
        hQS := hseg.hbS
        hRS := hseg.hcS
        hTS := hseg.haS
        hPout := by rw [hdflip, hsame, hxa]; rfl
        hQout := by rw [hbflip, hxa]; rfl
        hRout := hsame.trans hxa
        hTout := hxa
        hPv := hsq.hdv
        hQv := hsq.hbv
        hRv := hsq.hcv
        hTv := hsq.hav
        hmPR := hsq.hmd
        hmQT := hsq.hmb
        hm'PQ := RelTransitionSystem.repair_match_d hsq
        hm'RT := RelTransitionSystem.repair_match_c hsq }

end SegLedger

/-! ## The same-component configuration and its segment -/

section WalkReach

variable {F : EdgeSubset W}

/-- The walk from `c` reaches `a` with internal pairings: the
same-component configuration of the non-separated move (both the
same-circuit and the same-chain reversal sub-cases). -/
def WalkReach (κ : F.RelTransitionSystem) (c a : W.Flag) : Prop :=
  ∃ m : ℕ, 1 ≤ m ∧
    (∀ j, j < m →
      W.pairing (iterWalk κ c j) ∈ F.internalFlags) ∧
    iterWalk κ c m = a

variable {κ : F.RelTransitionSystem}

/-- Iterates along an internally-continuing walk are internal. -/
theorem iterWalk_int_of_cont {f : W.Flag}
    (hf : f ∈ F.internalFlags) {m : ℕ}
    (hcont : ∀ j, j < m →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags) :
    ∀ j, j ≤ m → iterWalk κ f j ∈ F.internalFlags := by
  intro j
  cases j with
  | zero => intro _; exact hf
  | succ j =>
    intro hj
    rw [iterWalk_succ]
    exact κ.match_mem _ (hcont j (by omega))

/-- The orientation is constant along the walk positions of an
internally-continuing walk. -/
theorem isOut_iterWalk_of_cont (o : κ.Orientation) {f : W.Flag}
    (hf : f ∈ F.internalFlags) {m : ℕ}
    (hcont : ∀ j, j < m →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags) :
    ∀ j, j ≤ m → o.isOut (iterWalk κ f j) = o.isOut f := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [iterWalk_succ, o.match_flip _ (hcont j (by omega)),
      o.pairing_flip _ (iterWalk_int_of_cont hf hcont j (by omega))
        (hcont j (by omega)),
      Bool.not_not, ih (by omega)]

/-- **The reversal segment of a same-component non-separated
square**: the flags of the walk from `c` up to (excluding) `a`, on
both sides of each visited edge. -/
theorem exists_repairSegment {a b c d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hsame : o.isOut c = o.isOut a) (hreach : WalkReach κ c a) :
    ∃ S : Finset W.Flag, RepairSegment κ a b c d S := by
  haveI : DecidablePred (fun m : ℕ => 1 ≤ m ∧
      (∀ j, j < m →
        W.pairing (iterWalk κ c j) ∈ F.internalFlags) ∧
      iterWalk κ c m = a) := fun m => Classical.dec _
  obtain ⟨m₀, ⟨hm1, hcont, hlast⟩, hmin⟩ :
      ∃ m : ℕ, (1 ≤ m ∧
        (∀ j, j < m →
          W.pairing (iterWalk κ c j) ∈ F.internalFlags) ∧
        iterWalk κ c m = a) ∧
        ∀ j, j < m → ¬ (1 ≤ j ∧
          (∀ i, i < j →
            W.pairing (iterWalk κ c i) ∈ F.internalFlags) ∧
          iterWalk κ c j = a) :=
    ⟨Nat.find hreach, Nat.find_spec hreach,
      fun j hj => Nat.find_min hreach hj⟩
  refine ⟨(Finset.range m₀).image (fun j => iterWalk κ c j) ∪
    (Finset.range m₀).image
      (fun j => W.pairing (iterWalk κ c j)), ?_⟩
  have hmemS : ∀ f : W.Flag,
      f ∈ (Finset.range m₀).image (fun j => iterWalk κ c j) ∪
        (Finset.range m₀).image
          (fun j => W.pairing (iterWalk κ c j)) ↔
      ∃ j, j < m₀ ∧ (f = iterWalk κ c j ∨
        f = W.pairing (iterWalk κ c j)) := by
    intro f
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
      · exact ⟨j, Finset.mem_range.mp hj, Or.inl rfl⟩
      · exact ⟨j, Finset.mem_range.mp hj, Or.inr rfl⟩
    · rintro ⟨j, hj, rfl | rfl⟩
      · exact Or.inl ⟨j, Finset.mem_range.mpr hj, rfl⟩
      · exact Or.inr ⟨j, Finset.mem_range.mpr hj, rfl⟩
  -- the walk positions never hit `a`
  have haW : ∀ j, j < m₀ → iterWalk κ c j ≠ a := by
    intro j hj heq
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · rw [iterWalk_zero] at heq
      exact hsq.hac heq.symm
    · exact hmin j hj ⟨hj1, fun i hi => hcont i (by omega), heq⟩
  -- the pairing positions never hit `a` (orientation obstruction)
  have haP : ∀ j, j < m₀ → W.pairing (iterWalk κ c j) ≠ a := by
    intro j hj heq
    have h1 : o.isOut (W.pairing (iterWalk κ c j)) = !o.isOut c := by
      rw [o.pairing_flip _
          (iterWalk_int_of_cont hsq.hc hcont j (by omega))
          (hcont j hj),
        isOut_iterWalk_of_cont o hsq.hc hcont j (by omega)]
    rw [heq, hsame] at h1
    simp at h1
  -- the walk positions never hit `d` (orientation obstruction)
  have hdW : ∀ j, j < m₀ → iterWalk κ c j ≠ d := by
    intro j hj heq
    have h1 : o.isOut d = !o.isOut c := by
      rw [← hsq.hcd]; exact o.match_flip c hsq.hc
    rw [← heq, isOut_iterWalk_of_cont o hsq.hc hcont j (by omega)]
      at h1
    simp at h1
  -- the pairing positions never hit `d` (minimality obstruction)
  have hdP : ∀ j, j < m₀ → W.pairing (iterWalk κ c j) ≠ d := by
    intro j hj heq
    have h1 : iterWalk κ c (j + 1) = c := by
      rw [iterWalk_succ, heq, hsq.hmd]
    have h2 : iterWalk κ c m₀ = iterWalk κ c (m₀ - (j + 1)) := by
      conv_lhs =>
        rw [show m₀ = (j + 1) + (m₀ - (j + 1)) from by omega]
      rw [iterWalk_add, h1]
    rw [hlast] at h2
    rcases Nat.eq_zero_or_pos (m₀ - (j + 1)) with hz | hpos
    · rw [hz, iterWalk_zero] at h2
      exact hsq.hac h2
    · exact hmin (m₀ - (j + 1)) (by omega)
        ⟨hpos, fun i hi => hcont i (by omega), h2.symm⟩
  -- `b` sits at the last pairing position
  have hbP : W.pairing (iterWalk κ c (m₀ - 1)) = b := by
    have h1 : κ.match_ a =
        κ.match_ (iterWalk κ c m₀) := by rw [hlast]
    have h2 : iterWalk κ c m₀ =
        κ.match_ (W.pairing (iterWalk κ c (m₀ - 1))) := by
      conv_lhs => rw [show m₀ = (m₀ - 1) + 1 from by omega]
      rw [iterWalk_succ]
    rw [h2, κ.match_invol _ (hcont (m₀ - 1) (by omega)),
      hsq.hab] at h1
    exact h1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ═══════ b ∈ S ═══════
    rw [hmemS]
    exact ⟨m₀ - 1, by omega, Or.inr hbP.symm⟩
  · -- ═══════ c ∈ S ═══════
    rw [hmemS]
    exact ⟨0, by omega, Or.inl (iterWalk_zero κ c).symm⟩
  · -- ═══════ a ∉ S ═══════
    rw [hmemS]
    rintro ⟨j, hj, heq | heq⟩
    · exact haW j hj heq.symm
    · exact haP j hj heq.symm
  · -- ═══════ d ∉ S ═══════
    rw [hmemS]
    rintro ⟨j, hj, heq | heq⟩
    · exact hdW j hj heq.symm
    · exact hdP j hj heq.symm
  · -- ═══════ INTERNALITY ═══════
    intro f hf
    rw [hmemS] at hf
    obtain ⟨j, hj, rfl | rfl⟩ := hf
    · exact iterWalk_int_of_cont hsq.hc hcont j (by omega)
    · exact hcont j hj
  · -- ═══════ PAIRING CLOSURE ═══════
    intro f hf
    rw [hmemS] at hf ⊢
    obtain ⟨j, hj, rfl | rfl⟩ := hf
    · exact ⟨j, hj, Or.inr rfl⟩
    · exact ⟨j, hj, Or.inl (W.pairing_invol _)⟩
  · -- ═══════ MATCHING CLOSURE AWAY FROM THE CUTS ═══════
    intro f hf hfb hfc
    rw [hmemS] at hf ⊢
    obtain ⟨j, hj, rfl | rfl⟩ := hf
    · cases j with
      | zero =>
        rw [iterWalk_zero] at hfc ⊢
        exact absurd rfl hfc
      | succ j =>
        refine ⟨j, by omega, Or.inr ?_⟩
        rw [iterWalk_succ,
          κ.match_invol _ (hcont j (by omega))]
    · rcases Nat.lt_or_ge (j + 1) m₀ with hjm | hjm
      · refine ⟨j + 1, hjm, Or.inl ?_⟩
        rw [iterWalk_succ]
      · exfalso
        have hje : j = m₀ - 1 := by omega
        rw [hje, hbP] at hfb
        exact hfb rfl

end WalkReach

/-! ## Localization of the same-component square -/

section WalkReachLocalized

/-- The chain membership is closed under the pairing. -/
theorem onBoundaryChain_pairing {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β f : W.Flag}
    (h : OnBoundaryChain κ β f) :
    OnBoundaryChain κ β (W.pairing f) := by
  obtain ⟨k, t, htk, hcont, hterm, hf⟩ := h
  refine ⟨k, t, htk, hcont, hterm, ?_⟩
  rcases hf with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl (W.pairing_invol _)

/-- The chain membership is closed along internally-continuing
walks. -/
theorem onBoundaryChain_iterWalk {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {β f : W.Flag}
    (hβ : β ∈ F.boundaryFlags) (h : OnBoundaryChain κ β f)
    {m : ℕ}
    (hcont : ∀ j, j < m →
      W.pairing (iterWalk κ f j) ∈ F.internalFlags) :
    ∀ j, j ≤ m → OnBoundaryChain κ β (iterWalk κ f j) := by
  intro j
  induction j with
  | zero => intro _; exact h
  | succ j ih =>
    intro hj
    rw [iterWalk_succ]
    exact onBoundaryChain_match hβ (hcont j (by omega))
      (onBoundaryChain_pairing (ih (by omega)))

/-- A same-component square is localized: `c`'s component either
is a circuit carrying all four flags, or is the chain of a
boundary flag carrying them. -/
theorem squareLocalized_of_walkReach
    {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a b c d : W.Flag}
    {v : W.Vertex} (hsq : RepairSquare κ a b c d v)
    (hreach : WalkReach κ c a) :
    SquareLocalized κ a b c d := by
  obtain ⟨m, hm1, hcont, hlast⟩ := hreach
  rcases periodic_or_onBoundaryChain κ hsq.hc with
    hpc | ⟨β, hβ, hchain⟩
  · exact Or.inl ⟨hlast ▸ periodicFlag_iterWalk κ hpc m, hpc⟩
  · refine Or.inr ⟨β, hβ, ?_⟩
    have hca : OnBoundaryChain κ β a :=
      hlast ▸ onBoundaryChain_iterWalk hβ hchain hcont m le_rfl
    intro f hf
    rcases hf with rfl | rfl | rfl | rfl
    · exact Or.inr hca
    · exact Or.inr (hsq.hab ▸ onBoundaryChain_match hβ hsq.ha hca)
    · exact Or.inr hchain
    · exact Or.inr
        (hsq.hcd ▸ onBoundaryChain_match hβ hsq.hc hchain)

/-- On a component with an orientation, membership of `a` on `c`'s
periodic orbit forces the forward reach under the non-separated
condition: the pairing-side (reverse) membership contradicts the
orientation. -/
theorem walkReach_of_orbitFlag {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {a c : W.Flag} {o : κ.Orientation}
    (hpc : κ.PeriodicFlag c) (hsame : o.isOut c = o.isOut a)
    (hac : a ≠ c) (horb : OrbitFlag κ c a) :
    WalkReach κ c a := by
  have hcont : ∀ j, j < 0 + 1 →
      W.pairing (iterWalk κ c j) ∈ F.internalFlags :=
    fun j _ => all_pairings_internal_of_periodic κ hpc j
  obtain ⟨m, hm | hm⟩ := horb
  · rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [iterWalk_zero] at hm
      exact absurd hm hac
    · exact ⟨m, hpos,
        fun j _ => all_pairings_internal_of_periodic κ hpc j,
        hm.symm⟩
  · exfalso
    have h1 : o.isOut (W.pairing (iterWalk κ c m)) =
        !o.isOut c := by
      rw [o.pairing_flip _
          (iterWalk_int_of_cont hpc.mem_internal
            (fun j (_ : j < m) =>
              all_pairings_internal_of_periodic κ hpc j) m le_rfl)
          (all_pairings_internal_of_periodic κ hpc m),
        isOut_iterWalk_of_cont o hpc.mem_internal
          (fun j (_ : j < m) =>
            all_pairings_internal_of_periodic κ hpc j) m le_rfl]
    rw [← hm, hsame] at h1
    simp at h1

/-- Orbit membership on a periodic component is periodic. -/
theorem periodicFlag_of_orbitFlag {F : EdgeSubset W} {κ : F.RelTransitionSystem}
    {c f : W.Flag}
    (hpc : κ.PeriodicFlag c) (horb : OrbitFlag κ c f) :
    κ.PeriodicFlag f := by
  obtain ⟨m, rfl | rfl⟩ := horb
  · exact periodicFlag_iterWalk κ hpc m
  · exact periodicFlag_pairing (periodicFlag_iterWalk κ hpc m)

end WalkReachLocalized

/-! ## The swapped square -/

section SwapSquare

variable {F : EdgeSubset W} {κ : F.RelTransitionSystem}
  {a b c d : W.Flag} {v : W.Vertex}

/-- The square with the two re-paired edges exchanged. -/
theorem RepairSquare.swap (h : RepairSquare κ a b c d v) :
    RepairSquare κ c d a b v where
  ha := h.hc
  hc := h.ha
  hab := h.hcd
  hcd := h.hab
  hac := Ne.symm h.hac
  had := Ne.symm h.hbc
  hbc := Ne.symm h.had
  hbd := Ne.symm h.hbd
  hav := h.hcv
  hcv := h.hav

/-- The swapped square repairs to the same system. -/
theorem repair_swap_matchEq (h : RepairSquare κ a b c d v) :
    (κ.repair c d a b v h.swap).MatchEq
      (κ.repair a b c d v h) := by
  intro f hf
  by_cases h1 : f = a
  · subst h1
    rw [RelTransitionSystem.repair_match_c h.swap,
      RelTransitionSystem.repair_match_a h]
  by_cases h3 : f = c
  · subst h3
    rw [RelTransitionSystem.repair_match_a h.swap,
      RelTransitionSystem.repair_match_c h]
  by_cases h2 : f = b
  · subst h2
    rw [RelTransitionSystem.repair_match_d h.swap,
      RelTransitionSystem.repair_match_b h]
  by_cases h4 : f = d
  · subst h4
    rw [RelTransitionSystem.repair_match_b h.swap,
      RelTransitionSystem.repair_match_d h]
  · rw [RelTransitionSystem.repair_match_of_ne h.swap h3 h4 h1 h2,
      RelTransitionSystem.repair_match_of_ne h h1 h2 h3 h4]

end SwapSquare

end EdgeSubset

/-! ## The inputs and the dispatch -/

/-- **Input (segment count parity)**: a same-component
square preserves the circuit-count parity — the segment reversal
maps the two traversal orbits of the affected component onto two
orbits of the same sizes (Δ = 0 on circuits; chains carry no
periodic flags).  Proved in `OrbitParities.lean`. -/
def NonSeparatedSegmentParity : Prop :=
  ∀ {α : Type} {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}
    (hsq : EdgeSubset.RepairSquare κ a b c d v),
    EdgeSubset.WalkReach κ c a →
    Even (κ.openCircuitCount +
      (κ.repair a b c d v hsq).openCircuitCount)

/-- **Input (merge count parity)**: a square whose
`c`-edge lies on a circuit not carrying `a` flips the count parity
— the splice merges the circuit into `a`'s component (Δ = −1).
Proved in `OrbitParities.lean`. -/
def NonSeparatedMergeParity : Prop :=
  ∀ {α : Type} {W : Fragment α} {F : EdgeSubset W}
    {κ : F.RelTransitionSystem} {a b c d : W.Flag} {v : W.Vertex}
    (hsq : EdgeSubset.RepairSquare κ a b c d v),
    κ.PeriodicFlag c → ¬ EdgeSubset.OrbitFlag κ c a →
    Odd (κ.openCircuitCount +
      (κ.repair a b c d v hsq).openCircuitCount)

end RS
