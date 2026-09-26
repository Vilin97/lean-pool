/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TransposeLedger
public import LeanPool.RegtsSevenster.RS.Novel.Skein.NonSeparatedStep

/-!
# The two-path non-separated transform

The value transformation of the constrained summand under a
non-localized repair square whose orientation is non-separated
(`o.isOut c = o.isOut a`).  The transported orientation flips the
whole boundary chain of `c`, which is legal because the chain's two
ends carry unconstrained boundary partners, and then transports
across the now-separated square.

The chain flip is not a scalar at a fixed state: the `∂`-reindex of
the colour sum meets the boundary at the chain's two end labels, so
the flipped summand is a signed summand at a *modified* state, the
two end labels' odd colours replaced by their `∂`-partners.
Composing with the separated ledger gives the transform, whose
factor is minus the product of the two end colours' odd-partner
signs.
-/

@[expose] public section

namespace RS



/-! ## The two-label `∂`-relabel of a boundary state -/

open scoped Classical in
/-- Apply the odd-partner involution to the (odd) state entries at
two labels, leaving all other labels untouched. -/
noncomputable def stateOddFlip {k ℓ : ℕ} {α : Type}
    (st : GenBoundaryState k ℓ α) (i₁ i₂ : α) :
    GenBoundaryState k ℓ α :=
  fun i => if i = i₁ ∨ i = i₂ then Sum.map id (oddPartner ℓ) (st i)
    else st i

section StateFlip

variable {k ℓ : ℕ} {α : Type} {st : GenBoundaryState k ℓ α}
  {i₁ i₂ : α}

open scoped Classical in
/-- Away from the two labels the state is unchanged. -/
theorem stateOddFlip_of_ne {i : α} (h1 : i ≠ i₁) (h2 : i ≠ i₂) :
    stateOddFlip st i₁ i₂ i = st i :=
  ite_eq_right (fun h => h.elim h1 h2)

open scoped Classical in
/-- At the first label the state entry is `∂`-flipped. -/
theorem stateOddFlip_left :
    stateOddFlip st i₁ i₂ i₁ = Sum.map id (oddPartner ℓ) (st i₁) :=
  ite_eq_left (Or.inl rfl)

open scoped Classical in
/-- At the second label likewise. -/
theorem stateOddFlip_right :
    stateOddFlip st i₁ i₂ i₂ = Sum.map id (oddPartner ℓ) (st i₂) :=
  ite_eq_left (Or.inr rfl)

/-- At the first label, on an odd entry: the colour is replaced by
its odd partner. -/
theorem stateOddFlip_left_odd {c : Fin (2 * ℓ)}
    (hc : st i₁ = Sum.inr c) :
    stateOddFlip st i₁ i₂ i₁ = Sum.inr (oddPartner ℓ c) := by
  rw [stateOddFlip_left, hc]
  rfl

/-- At the second label likewise. -/
theorem stateOddFlip_right_odd {c : Fin (2 * ℓ)}
    (hc : st i₂ = Sum.inr c) :
    stateOddFlip st i₁ i₂ i₂ = Sum.inr (oddPartner ℓ c) := by
  rw [stateOddFlip_right, hc]
  rfl

open scoped Classical in
/-- The relabel preserves odd-ness of every entry. -/
theorem stateOddFlip_isInr (i : α) :
    (∃ c, stateOddFlip st i₁ i₂ i = Sum.inr c) ↔
      ∃ c, st i = Sum.inr c := by
  unfold stateOddFlip
  by_cases h : i = i₁ ∨ i = i₂
  · rw [ite_eq_left h]
    cases hst : st i with
    | inl a =>
      constructor
      · rintro ⟨c, hc⟩
        cases hc
      · rintro ⟨c, hc⟩
        cases hc
    | inr b => exact ⟨fun _ => ⟨b, rfl⟩,
        fun _ => ⟨oddPartner ℓ b, rfl⟩⟩
  · rw [ite_eq_right h]

open scoped Classical in
/-- The relabel fixes every even entry. -/
theorem stateOddFlip_isInl (i : α) (a : Fin k) :
    stateOddFlip st i₁ i₂ i = Sum.inl a ↔ st i = Sum.inl a := by
  unfold stateOddFlip
  by_cases h : i = i₁ ∨ i = i₂
  · rw [ite_eq_left h]
    cases hst : st i with
    | inl a' => exact Iff.rfl
    | inr b =>
      constructor
      · intro hc
        cases hc
      · intro hc
        cases hc
  · rw [ite_eq_right h]

/-- The boundary-membership constraint transfers across the
relabel. -/
theorem genBoundarySubsetMatches_stateOddFlip {W : Fragment α}
    {s : Finset W.Flag} (hbnd : genBoundarySubsetMatches W s st)
    (i₁ i₂ : α) :
    genBoundarySubsetMatches W s (stateOddFlip st i₁ i₂) :=
  fun i => (hbnd i).trans (stateOddFlip_isInr i).symm

open scoped Classical in
/-- **The relabel is an involution.** -/
theorem stateOddFlip_stateOddFlip :
    stateOddFlip (stateOddFlip st i₁ i₂) i₁ i₂ = st := by
  funext i
  change (if i = i₁ ∨ i = i₂ then
      Sum.map id (oddPartner ℓ) (stateOddFlip st i₁ i₂ i)
    else stateOddFlip st i₁ i₂ i) = st i
  by_cases h : i = i₁ ∨ i = i₂
  · rw [ite_eq_left h, show stateOddFlip st i₁ i₂ i =
      Sum.map id (oddPartner ℓ) (st i) from ite_eq_left h]
    cases st i with
    | inl a => rfl
    | inr b =>
      change Sum.inr (oddPartner ℓ (oddPartner ℓ b)) = Sum.inr b
      rw [oddPartner_invol]
  · rw [ite_eq_right h]
    exact stateOddFlip_of_ne (fun he => h (Or.inl he))
      (fun he => h (Or.inr he))

/-- The summand only reads the state and the proof of the boundary
constraint is irrelevant: propositionally equal states give equal
summands over any proofs. -/
theorem EdgeSubset.throughSummand_state_congr {W : Fragment α}
    [LinearOrder α] (F : EdgeSubset W)
    (hM : MixedFunctional k ℓ) {st₁ st₂ : GenBoundaryState k ℓ α}
    (hst : st₁ = st₂)
    (hbnd₁ : genBoundarySubsetMatches W F.flags st₁)
    (hbnd₂ : genBoundarySubsetMatches W F.flags st₂)
    {κ : F.RelTransitionSystem} (o : κ.Orientation) (n : ℕ) :
    F.throughSummand hM st₁ hbnd₁ o n =
      F.throughSummand hM st₂ hbnd₂ o n := by
  subst hst
  rfl

end StateFlip

namespace EdgeSubset

/-! ## The ported flip set and the chain-flipped orientation -/

section PortedFlip

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {κ : F.RelTransitionSystem} {S : Finset W.Flag}
  {p₁ p₂ : W.Flag} {i₁ i₂ : α}

/-- **The ported flip set**: a set of internal flags closed under
the matching and closed under the edge pairing except at two
*ports* `p₁`, `p₂`, whose edge partners are the boundary flags of
the labels `i₁`, `i₂`.  The internal-flag support of a full
boundary chain is the motivating instance
(`exists_chainPortedFlipSet`). -/
structure PortedFlipSet (κ : F.RelTransitionSystem)
    (S : Finset W.Flag) (p₁ p₂ : W.Flag) (i₁ i₂ : α) : Prop where
  int_of_mem : ∀ f ∈ S, f ∈ F.internalFlags
  match_mem : ∀ f ∈ S, κ.match_ f ∈ S
  pairing_mem : ∀ f ∈ S, f ≠ p₁ → f ≠ p₂ → W.pairing f ∈ S
  hp₁S : p₁ ∈ S
  hp₂S : p₂ ∈ S
  hp₁₂ : p₁ ≠ p₂
  hσ₁ : W.pairing p₁ = W.boundaryFlag i₁
  hσ₂ : W.pairing p₂ = W.boundaryFlag i₂

namespace PortedFlipSet

/-- The two port labels are distinct. -/
theorem hlab (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) : i₁ ≠ i₂ := by
  intro he
  apply h.hp₁₂
  have h1 : W.pairing (W.pairing p₁) = W.pairing (W.pairing p₂) := by
    rw [h.hσ₁, h.hσ₂, he]
  rwa [W.pairing_invol, W.pairing_invol] at h1

/-- The complement of the flip set is closed under the matching. -/
theorem match_notMem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {f : W.Flag} (hf : f ∈ F.internalFlags)
    (hfS : f ∉ S) : κ.match_ f ∉ S := by
  intro hmem
  have h2 := h.match_mem _ hmem
  rw [κ.match_invol f hf] at h2
  exact hfS h2

/-- The edge partner of the first port is the first boundary
flag. -/
theorem bF₁_pairing (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.pairing (W.boundaryFlag i₁) = p₁ := by
  rw [← h.hσ₁, W.pairing_invol]

/-- The edge partner of the second port is the second boundary
flag. -/
theorem bF₂_pairing (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.pairing (W.boundaryFlag i₂) = p₂ := by
  rw [← h.hσ₂, W.pairing_invol]

/-- Boundary-attached flags are not in the flip set. -/
theorem attach_inr_notMem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {f : W.Flag} {i : α}
    (hat : W.attach f = Sum.inr i) : f ∉ S := by
  intro hmem
  obtain ⟨v, hv⟩ := F.attach_internal_of_mem (h.int_of_mem _ hmem)
  rw [hv] at hat
  cases hat

/-- Boundary flags are not in the flip set. -/
theorem boundaryFlag_notMem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (i : α) : W.boundaryFlag i ∉ S :=
  h.attach_inr_notMem (W.attach_boundaryFlag i)

/-- The complement of the flip set is closed under the pairing away
from the two boundary ends. -/
theorem pairing_notMem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {f : W.Flag} (hfS : f ∉ S)
    (h1 : f ≠ W.boundaryFlag i₁) (h2 : f ≠ W.boundaryFlag i₂) :
    W.pairing f ∉ S := by
  intro hmem
  by_cases hq₁ : W.pairing f = p₁
  · refine h1 ?_
    have h3 := congrArg W.pairing hq₁
    rwa [W.pairing_invol, h.hσ₁] at h3
  by_cases hq₂ : W.pairing f = p₂
  · refine h2 ?_
    have h3 := congrArg W.pairing hq₂
    rwa [W.pairing_invol, h.hσ₂] at h3
  · have h3 := h.pairing_mem _ hmem hq₁ hq₂
    rw [W.pairing_invol] at h3
    exact hfS h3

/-- Internal flags are never the boundary flags of the ports. -/
theorem int_ne_boundaryFlag {f : W.Flag}
    (hf : f ∈ F.internalFlags) (i : α) :
    f ≠ W.boundaryFlag i := by
  intro he
  obtain ⟨v, hv⟩ := F.attach_internal_of_mem hf
  rw [he, W.attach_boundaryFlag] at hv
  cases hv

/-- The ports are core flags. -/
theorem p₁_core (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    p₁ ∈ F.coreFlags :=
  F.internalFlags_subset_coreFlags (h.int_of_mem _ h.hp₁S)

/-- The second port is a core flag. -/
theorem p₂_core (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    p₂ ∈ F.coreFlags :=
  F.internalFlags_subset_coreFlags (h.int_of_mem _ h.hp₂S)

/-- The port boundary flags are core flags. -/
theorem bF₁_core (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.boundaryFlag i₁ ∈ F.coreFlags := by
  have h1 := F.pairing_mem_coreFlags h.p₁_core
  rwa [h.hσ₁] at h1

/-- The second port's boundary end is a core flag — the colour
reindexing needs a value there. -/
theorem bF₂_core (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    W.boundaryFlag i₂ ∈ F.coreFlags := by
  have h1 := F.pairing_mem_coreFlags h.p₂_core
  rwa [h.hσ₂] at h1

end PortedFlipSet

/-- **The chain-flipped orientation** of the *same* system: negate
`isOut` exactly on the flip set.  The flip is legal at the two
ports because their edge partners are boundary flags, whose
orientation is unconstrained. -/
noncomputable def RelTransitionSystem.Orientation.portFlip
    (o : κ.Orientation) (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    κ.Orientation where
  isOut f := if f ∈ S then !o.isOut f else o.isOut f
  match_flip := by
    intro f hf
    show (if κ.match_ f ∈ S then !o.isOut (κ.match_ f)
        else o.isOut (κ.match_ f)) =
      !(if f ∈ S then !o.isOut f else o.isOut f)
    by_cases hfS : f ∈ S
    · rw [ite_eq_left (h.match_mem f hfS), ite_eq_left hfS,
        o.match_flip f hf]
    · rw [ite_eq_right (h.match_notMem hf hfS), ite_eq_right hfS]
      exact o.match_flip f hf
  pairing_flip := by
    intro f hf hp
    show (if W.pairing f ∈ S then !o.isOut (W.pairing f)
        else o.isOut (W.pairing f)) =
      !(if f ∈ S then !o.isOut f else o.isOut f)
    by_cases hfS : f ∈ S
    · have hfp₁ : f ≠ p₁ := by
        intro he
        subst he
        rw [h.hσ₁] at hp
        obtain ⟨v, hv⟩ := F.attach_internal_of_mem hp
        rw [W.attach_boundaryFlag] at hv
        cases hv
      have hfp₂ : f ≠ p₂ := by
        intro he
        subst he
        rw [h.hσ₂] at hp
        obtain ⟨v, hv⟩ := F.attach_internal_of_mem hp
        rw [W.attach_boundaryFlag] at hv
        cases hv
      rw [ite_eq_left (h.pairing_mem f hfS hfp₁ hfp₂), ite_eq_left hfS,
        o.pairing_flip f hf hp]
    · rw [ite_eq_right (h.pairing_notMem hfS
          (PortedFlipSet.int_ne_boundaryFlag hf i₁)
          (PortedFlipSet.int_ne_boundaryFlag hf i₂)), ite_eq_right hfS]
      exact o.pairing_flip f hf hp

section PortFlipEval

variable (o : κ.Orientation) (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)

/-- On the flip set the orientation reverses. -/
theorem portFlip_isOut_of_mem {f : W.Flag} (hf : f ∈ S) :
    (o.portFlip h).isOut f = !o.isOut f := ite_eq_left hf

/-- Off the flip set the orientation is unchanged. -/
theorem portFlip_isOut_of_notMem {f : W.Flag} (hf : f ∉ S) :
    (o.portFlip h).isOut f = o.isOut f := ite_eq_right hf

end PortFlipEval

end PortedFlip

/-! ## The chain-flip value ledger -/

section PortFlipLedger

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {κ : F.RelTransitionSystem} {S : Finset W.Flag}
  {p₁ p₂ : W.Flag} {i₁ i₂ : α} {k ℓ : ℕ}

/-! ### The pairing-closed colour-flip core -/

/-- The flip set together with the two boundary ends: the
pairing-closed support of the colour reindexing. -/
noncomputable def portFlipCore {W : Fragment α} (S : Finset W.Flag)
    (i₁ i₂ : α) : Finset W.Flag :=
  insert (W.boundaryFlag i₁) (insert (W.boundaryFlag i₂) S)

/-- Membership in the colour-flip core: the flip set plus the two
chain-end boundary flags. -/
theorem mem_portFlipCore {f : W.Flag} :
    f ∈ portFlipCore S i₁ i₂ ↔
      f = W.boundaryFlag i₁ ∨ f = W.boundaryFlag i₂ ∨ f ∈ S := by
  unfold portFlipCore
  rw [Finset.mem_insert, Finset.mem_insert]

/-- The flip set sits inside its colour-flip core. -/
theorem mem_portFlipCore_of_mem {f : W.Flag} (hf : f ∈ S) :
    f ∈ portFlipCore S i₁ i₂ :=
  mem_portFlipCore.mpr (Or.inr (Or.inr hf))

namespace PortedFlipSet

/-- The colour-flip core is fully pairing-closed. -/
theorem flipCore_pairing (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    ∀ f ∈ portFlipCore S i₁ i₂,
      W.pairing f ∈ portFlipCore S i₁ i₂ := by
  intro f hf
  rcases mem_portFlipCore.mp hf with rfl | rfl | hfS
  · exact mem_portFlipCore_of_mem (h.bF₁_pairing ▸ h.hp₁S)
  · exact mem_portFlipCore_of_mem (h.bF₂_pairing ▸ h.hp₂S)
  · by_cases h1 : f = p₁
    · subst h1
      rw [h.hσ₁]
      exact mem_portFlipCore.mpr (Or.inl rfl)
    by_cases h2 : f = p₂
    · subst h2
      rw [h.hσ₂]
      exact mem_portFlipCore.mpr (Or.inr (Or.inl rfl))
    · exact mem_portFlipCore_of_mem (h.pairing_mem f hfS h1 h2)

/-- On internal flags the colour-flip core is the flip set. -/
theorem mem_flipCore_int (_ : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {g : W.Flag} (hg : g ∈ F.internalFlags) :
    g ∈ portFlipCore S i₁ i₂ ↔ g ∈ S := by
  rw [mem_portFlipCore]
  constructor
  · rintro (rfl | rfl | hgS)
    · exact absurd rfl (PortedFlipSet.int_ne_boundaryFlag hg i₁)
    · exact absurd rfl (PortedFlipSet.int_ne_boundaryFlag hg i₂)
    · exact hgS
  · exact fun hgS => Or.inr (Or.inr hgS)

/-- On boundary flags the colour-flip core is the two end
labels. -/
theorem mem_flipCore_boundaryFlag (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (i : α) :
    W.boundaryFlag i ∈ portFlipCore S i₁ i₂ ↔ i = i₁ ∨ i = i₂ := by
  rw [mem_portFlipCore]
  constructor
  · rintro (he | he | hmem)
    · exact Or.inl (W.boundaryFlag_injective he)
    · exact Or.inr (W.boundaryFlag_injective he)
    · exact absurd hmem (h.boundaryFlag_notMem i)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)

end PortedFlipSet

/-! ### The colour reindexing -/

/-- The `∂`-flip of a core odd colouring on the flip set together
with the two chain-end edges. -/
noncomputable def portColourFlip (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ) : F.CoreOddColouring ℓ :=
  segFlipColouring h.flipCore_pairing φ

/-- The reindexed colouring, unfolded: `∂`-flipped on the core,
unchanged off it. -/
theorem portColourFlip_val (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags}) :
    (portColourFlip h φ).val g =
      if g.val ∈ portFlipCore S i₁ i₂ then oddPartner ℓ (φ.val g)
      else φ.val g :=
  segFlipColouring_val h.flipCore_pairing φ g

/-- On the flip set the colour is `∂`-flipped. -/
theorem portColourFlip_val_of_mem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags}) (hg : g.val ∈ S) :
    (portColourFlip h φ).val g = oddPartner ℓ (φ.val g) := by
  rw [portColourFlip_val h φ g, ite_eq_left (mem_portFlipCore_of_mem hg)]

/-- On an internal flag off the flip set the colour is
unchanged. -/
theorem portColourFlip_val_int_of_notMem (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ)
    (g : {g : W.Flag // g ∈ F.coreFlags})
    (hgint : g.val ∈ F.internalFlags) (hg : g.val ∉ S) :
    (portColourFlip h φ).val g = φ.val g := by
  rw [portColourFlip_val h φ g,
    ite_eq_right (fun hc => hg ((h.mem_flipCore_int hgint).mp hc))]

/-- At the first chain end the colour is `∂`-flipped: this is where
the reindexing meets the boundary, and why the transform relabels
the state. -/
theorem portColourFlip_val_bF₁ (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ)
    (hcore : W.boundaryFlag i₁ ∈ F.coreFlags) :
    (portColourFlip h φ).val ⟨W.boundaryFlag i₁, hcore⟩ =
      oddPartner ℓ (φ.val ⟨W.boundaryFlag i₁, hcore⟩) := by
  rw [portColourFlip_val h φ _,
    ite_eq_left ((h.mem_flipCore_boundaryFlag i₁).mpr (Or.inl rfl))]

/-- At the second chain end likewise. -/
theorem portColourFlip_val_bF₂ (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ)
    (hcore : W.boundaryFlag i₂ ∈ F.coreFlags) :
    (portColourFlip h φ).val ⟨W.boundaryFlag i₂, hcore⟩ =
      oddPartner ℓ (φ.val ⟨W.boundaryFlag i₂, hcore⟩) := by
  rw [portColourFlip_val h φ _,
    ite_eq_left ((h.mem_flipCore_boundaryFlag i₂).mpr (Or.inr rfl))]

/-- At every other boundary flag the colour is unchanged: only the
two chain-end labels move. -/
theorem portColourFlip_val_bF_of_ne (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ) {i : α} (hi₁ : i ≠ i₁)
    (hi₂ : i ≠ i₂) (hcore : W.boundaryFlag i ∈ F.coreFlags) :
    (portColourFlip h φ).val ⟨W.boundaryFlag i, hcore⟩ =
      φ.val ⟨W.boundaryFlag i, hcore⟩ := by
  rw [portColourFlip_val h φ _, ite_eq_right (fun hc => by
    rcases (h.mem_flipCore_boundaryFlag i).mp hc with he | he
    · exact hi₁ he
    · exact hi₂ he)]

/-- The colour reindexing is an involution, so it is a bijection of
the colouring sum. -/
theorem portColourFlip_involutive (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    Function.Involutive (portColourFlip (ℓ := ℓ) h) :=
  fun φ => segFlipColouring_involutive h.flipCore_pairing φ

/-- **The boundary-constraint exchange**: the flipped colouring
matches the original state exactly when the original colouring
matches the `∂`-relabelled state. -/
theorem coreOddBoundaryMatch_portColourFlip (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (st : GenBoundaryState k ℓ α) (φ : F.CoreOddColouring ℓ) :
    F.coreOddBoundaryMatch st (portColourFlip h φ) ↔
      F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ := by
  unfold coreOddBoundaryMatch
  constructor
  · intro H i cc hst hcore
    by_cases hi₁ : i = i₁
    · subst hi₁
      cases hsti : st i with
      | inl a =>
        rw [stateOddFlip_left, hsti] at hst
        cases hst
      | inr c' =>
        have hcc : cc = oddPartner ℓ c' := by
          rw [stateOddFlip_left_odd hsti] at hst
          exact (Sum.inr.inj hst).symm
        have hΦ := H i c' hsti hcore
        rw [portColourFlip_val_bF₁ h φ hcore] at hΦ
        rw [hcc, ← hΦ, oddPartner_invol]
    by_cases hi₂ : i = i₂
    · subst hi₂
      cases hsti : st i with
      | inl a =>
        rw [stateOddFlip_right, hsti] at hst
        cases hst
      | inr c' =>
        have hcc : cc = oddPartner ℓ c' := by
          rw [stateOddFlip_right_odd hsti] at hst
          exact (Sum.inr.inj hst).symm
        have hΦ := H i c' hsti hcore
        rw [portColourFlip_val_bF₂ h φ hcore] at hΦ
        rw [hcc, ← hΦ, oddPartner_invol]
    · have hst' : st i = Sum.inr cc :=
        (stateOddFlip_of_ne hi₁ hi₂).symm.trans hst
      have hΦ := H i cc hst' hcore
      rwa [portColourFlip_val_bF_of_ne h φ hi₁ hi₂ hcore] at hΦ
  · intro H i cc hst hcore
    by_cases hi₁ : i = i₁
    · subst hi₁
      have hstpar : stateOddFlip st i i₂ i = Sum.inr (oddPartner ℓ cc) :=
        stateOddFlip_left_odd hst
      have hφ := H i (oddPartner ℓ cc) hstpar hcore
      rw [portColourFlip_val_bF₁ h φ hcore, hφ, oddPartner_invol]
    by_cases hi₂ : i = i₂
    · subst hi₂
      have hstpar : stateOddFlip st i₁ i i = Sum.inr (oddPartner ℓ cc) :=
        stateOddFlip_right_odd hst
      have hφ := H i (oddPartner ℓ cc) hstpar hcore
      rw [portColourFlip_val_bF₂ h φ hcore, hφ, oddPartner_invol]
    · have hst' : stateOddFlip st i₁ i₂ i = Sum.inr cc := by
        rw [stateOddFlip_of_ne hi₁ hi₂]
        exact hst
      rw [portColourFlip_val_bF_of_ne h φ hi₁ hi₂ hcore]
      exact H i cc hst' hcore

/-! ### The pairing sign as a total function -/

private theorem inSign_portFlip_of_mem
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (φ : F.CoreOddColouring ℓ)
    {g : W.Flag} (hg : g ∈ S) :
    inSign (portColourFlip h φ) g = -inSign φ g := by
  have hcore : g ∈ F.coreFlags :=
    F.internalFlags_subset_coreFlags (h.int_of_mem g hg)
  unfold inSign
  rw [dite_eq_left hcore, dite_eq_left hcore,
    portColourFlip_val_of_mem h φ ⟨g, hcore⟩ hg,
    oddPartnerSign_oddPartner]

private theorem inSign_portFlip_of_int_notMem
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (φ : F.CoreOddColouring ℓ)
    {g : W.Flag} (hgint : g ∈ F.internalFlags) (hg : g ∉ S) :
    inSign (portColourFlip h φ) g = inSign φ g := by
  have hcore : g ∈ F.coreFlags :=
    F.internalFlags_subset_coreFlags hgint
  unfold inSign
  rw [dite_eq_left hcore, dite_eq_left hcore,
    portColourFlip_val_int_of_notMem h φ ⟨g, hcore⟩ hgint hg]

/-! ### Vertex-local in-sets -/

private noncomputable def keepP (S : Finset W.Flag)
    (o₀ : κ.Orientation) (vv : W.Vertex) : Finset W.Flag :=
  (relInSetAt o₀ vv).filter (fun g => g ∉ S)

private noncomputable def flipP (S : Finset W.Flag)
    (o₀ : κ.Orientation) (vv : W.Vertex) : Finset W.Flag :=
  (relInSetAt o₀ vv).filter (fun g => g ∈ S)

private theorem mem_keepP {o₀ : κ.Orientation} {vv : W.Vertex}
    {g : W.Flag} :
    g ∈ keepP S o₀ vv ↔ g ∈ relInSetAt o₀ vv ∧ g ∉ S :=
  Finset.mem_filter

private theorem mem_flipP {o₀ : κ.Orientation} {vv : W.Vertex}
    {g : W.Flag} :
    g ∈ flipP S o₀ vv ↔ g ∈ relInSetAt o₀ vv ∧ g ∈ S :=
  Finset.mem_filter

private theorem match_injOn_flipP (o₀ : κ.Orientation)
    (vv : W.Vertex) :
    ∀ x ∈ flipP S o₀ vv, ∀ y ∈ flipP S o₀ vv,
      κ.match_ x = κ.match_ y → x = y := by
  intro x hx y hy hxy
  have hxint := relInSetAt_subset_internal (mem_flipP.mp hx).1
  have hyint := relInSetAt_subset_internal (mem_flipP.mp hy).1
  calc x = κ.match_ (κ.match_ x) := (κ.match_invol x hxint).symm
    _ = κ.match_ (κ.match_ y) := by rw [hxy]
    _ = y := κ.match_invol y hyint

/-- The port flip on `S` splits a vertex's in-set into the kept and
the flipped part. -/
private theorem relInSetAt_val_split_port (o₀ : κ.Orientation)
    (vv : W.Vertex) :
    (relInSetAt o₀ vv).val =
      (keepP S o₀ vv).val + (flipP S o₀ vv).val := by
  unfold keepP flipP
  rw [Finset.filter_val, Finset.filter_val, add_comm]
  exact (Multiset.filter_add_not (fun g => g ∈ S)
    (relInSetAt o₀ vv).val).symm

/-- A product over a vertex's in-set splits along that
partition. -/
private theorem prod_relInSetAt_split_port {M : Type*} [CommMonoid M]
    (o₀ : κ.Orientation) (vv : W.Vertex) (f : W.Flag → M) :
    ∏ g ∈ relInSetAt o₀ vv, f g =
      (∏ g ∈ flipP S o₀ vv, f g) * ∏ g ∈ keepP S o₀ vv, f g := by
  unfold flipP keepP
  exact (Finset.prod_filter_mul_prod_filter_not
    (relInSetAt o₀ vv) _ f).symm

private theorem keepP_disjoint_image
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (o₀ : κ.Orientation)
    (vv : W.Vertex) :
    Disjoint (keepP S o₀ vv) ((flipP S o₀ vv).image κ.match_) := by
  rw [Finset.disjoint_left]
  intro g hgk hgi
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hgi
  exact (mem_keepP.mp hgk).2
    (h.match_mem f (mem_flipP.mp hf).2)

/-- **The in-set identity**: the in-flags of the flipped
orientation are the kept in-flags together with the matches of the
flipped ones. -/
private theorem inb_portFlip (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (o : κ.Orientation) (vv : W.Vertex) :
    relInSetAt (o.portFlip h) vv = (keepP S o vv).disjUnion
      ((flipP S o vv).image κ.match_)
      (keepP_disjoint_image h o vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion, mem_relInSetAt]
  constructor
  · rintro ⟨hgfl, hgat, hgout⟩
    have hgint : g ∈ F.internalFlags :=
      mem_internalFlags_of hgfl ⟨vv, hgat⟩
    by_cases hgS : g ∈ S
    · right
      refine Finset.mem_image.mpr
        ⟨κ.match_ g, ?_, κ.match_invol g hgint⟩
      have hone : o.isOut g = true := by
        rw [portFlip_isOut_of_mem o h hgS] at hgout
        cases hb : o.isOut g
        · rw [hb] at hgout
          cases hgout
        · rfl
      have hmint := κ.match_mem g hgint
      refine mem_flipP.mpr ⟨mem_relInSetAt.mpr
        ⟨mem_flags_of_internalFlags F hmint,
          κ.match_vertex g hgint vv hgat, ?_⟩, h.match_mem g hgS⟩
      rw [o.match_flip g hgint, hone]
      rfl
    · left
      refine mem_keepP.mpr ⟨mem_relInSetAt.mpr ⟨hgfl, hgat, ?_⟩, hgS⟩
      rw [← portFlip_isOut_of_notMem o h hgS]
      exact hgout
  · rintro (hg | hg)
    · obtain ⟨hgin, hgS⟩ := mem_keepP.mp hg
      obtain ⟨h1, h2, h3⟩ := mem_relInSetAt.mp hgin
      refine ⟨h1, h2, ?_⟩
      rw [portFlip_isOut_of_notMem o h hgS]
      exact h3
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨hfin, hfS⟩ := mem_flipP.mp hf
      obtain ⟨h1, h2, h3⟩ := mem_relInSetAt.mp hfin
      have hfint : f ∈ F.internalFlags :=
        mem_internalFlags_of h1 ⟨vv, h2⟩
      have hmint := κ.match_mem f hfint
      refine ⟨mem_flags_of_internalFlags F hmint,
        κ.match_vertex f hfint vv h2, ?_⟩
      rw [portFlip_isOut_of_mem o h (h.match_mem f hfS),
        o.match_flip f hfint, h3]
      rfl

/-! ### The flip set split by vertex -/

open scoped Classical in
private noncomputable def diffAtP (S : Finset W.Flag)
    (vv : W.Vertex) : Finset W.Flag :=
  S.filter (fun g => W.attach g = Sum.inl vv)

open scoped Classical in
private theorem mem_diffAtP {vv : W.Vertex} {g : W.Flag} :
    g ∈ diffAtP S vv ↔ g ∈ S ∧ W.attach g = Sum.inl vv :=
  Finset.mem_filter

private theorem flipP_disjoint_image (o₀ : κ.Orientation)
    (vv : W.Vertex) :
    Disjoint (flipP S o₀ vv) ((flipP S o₀ vv).image κ.match_) := by
  rw [Finset.disjoint_left]
  intro g hgf hgi
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hgi
  have hfint := relInSetAt_subset_internal (mem_flipP.mp hf).1
  have hffalse := (mem_relInSetAt.mp (mem_flipP.mp hf).1).2.2
  have hmtrue : o₀.isOut (κ.match_ f) = true := by
    rw [o₀.match_flip f hfint, hffalse]
    rfl
  have hmfalse := (mem_relInSetAt.mp (mem_flipP.mp hgf).1).2.2
  rw [hmtrue] at hmfalse
  cases hmfalse

private theorem diffAtP_eq (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (o₀ : κ.Orientation) (vv : W.Vertex) :
    diffAtP S vv = (flipP S o₀ vv).disjUnion
      ((flipP S o₀ vv).image κ.match_)
      (flipP_disjoint_image o₀ vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_disjUnion, mem_diffAtP]
  constructor
  · rintro ⟨hgS, hgat⟩
    have hgint : g ∈ F.internalFlags := h.int_of_mem g hgS
    have hgfl : g ∈ F.flags := mem_flags_of_internalFlags F hgint
    cases hb : o₀.isOut g
    · left
      exact mem_flipP.mpr ⟨mem_relInSetAt.mpr ⟨hgfl, hgat, hb⟩, hgS⟩
    · right
      refine Finset.mem_image.mpr
        ⟨κ.match_ g, ?_, κ.match_invol g hgint⟩
      have hmint := κ.match_mem g hgint
      refine mem_flipP.mpr ⟨mem_relInSetAt.mpr
        ⟨mem_flags_of_internalFlags F hmint,
          κ.match_vertex g hgint vv hgat, ?_⟩, h.match_mem g hgS⟩
      rw [o₀.match_flip g hgint, hb]
      rfl
  · rintro (hg | hg)
    · exact ⟨(mem_flipP.mp hg).2,
        (mem_relInSetAt.mp (mem_flipP.mp hg).1).2.1⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      have hfint := relInSetAt_subset_internal (mem_flipP.mp hf).1
      exact ⟨h.match_mem f (mem_flipP.mp hf).2,
        κ.match_vertex f hfint vv
          (mem_relInSetAt.mp (mem_flipP.mp hf).1).2.1⟩

private theorem S_eq_biUnion_diffAtP (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) :
    S = Finset.univ.biUnion (fun vv => diffAtP S vv) := by
  apply Finset.ext
  intro g
  rw [Finset.mem_biUnion]
  constructor
  · intro hg
    obtain ⟨vv, hvv⟩ :=
      F.attach_internal_of_mem (h.int_of_mem g hg)
    exact ⟨vv, Finset.mem_univ vv, mem_diffAtP.mpr ⟨hg, hvv⟩⟩
  · rintro ⟨vv, _, hvv⟩
    exact (mem_diffAtP.mp hvv).1

private theorem diffAtP_pairwiseDisjoint :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset W.Vertex))
      (fun vv => diffAtP S vv) := by
  intro x _ y _ hxy
  refine Finset.disjoint_left.mpr (fun g hgx hgy => hxy ?_)
  have h1 := (mem_diffAtP.mp hgx).2
  have h2 := (mem_diffAtP.mp hgy).2
  rw [h1] at h2
  exact Sum.inl.inj h2

/-! ### The port telescoping -/

/-- The flip-set sign product telescopes to the two port signs. -/
private theorem prod_inSign_ports (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (φ : F.CoreOddColouring ℓ) :
    ∏ g ∈ S, inSign φ g = inSign φ p₁ * inSign φ p₂ := by
  have hp₂mem : p₂ ∈ S.erase p₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm h.hp₁₂, h.hp₂S⟩
  rw [← Finset.mul_prod_erase S _ h.hp₁S,
    ← Finset.mul_prod_erase (S.erase p₁) _ hp₂mem, ← mul_assoc]
  have hone : ∏ g ∈ (S.erase p₁).erase p₂, inSign φ g = 1 := by
    refine Finset.prod_involution (fun g _ => W.pairing g) ?_ ?_ ?_ ?_
    · intro g hg
      have hgS : g ∈ S := Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hg)
      rw [inSign_pairing φ
        (F.internalFlags_subset_coreFlags (h.int_of_mem g hgS))]
      exact inSign_mul_self φ g
    · exact fun g _ _ => W.pairing_ne g
    · intro g hg
      have hg₂ : g ≠ p₂ := (Finset.mem_erase.mp hg).1
      have hg₁ : g ≠ p₁ :=
        (Finset.mem_erase.mp (Finset.mem_of_mem_erase hg)).1
      have hgS : g ∈ S := Finset.mem_of_mem_erase
        (Finset.mem_of_mem_erase hg)
      have hpS : W.pairing g ∈ S := h.pairing_mem g hgS hg₁ hg₂
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr
        ⟨?_, hpS⟩⟩
      · intro he
        have h3 := congrArg W.pairing he
        rw [W.pairing_invol, h.hσ₂] at h3
        exact h.boundaryFlag_notMem i₂ (h3 ▸ hgS)
      · intro he
        have h3 := congrArg W.pairing he
        rw [W.pairing_invol, h.hσ₁] at h3
        exact h.boundaryFlag_notMem i₁ (h3 ▸ hgS)
    · exact fun g _ => W.pairing_invol g
  rw [hone, mul_one]

/-- The global flipped-visit sign product is the two port signs. -/
private theorem flip_prod_ports (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (o : κ.Orientation) (φ : F.CoreOddColouring ℓ) :
    ∏ vv : W.Vertex, ∏ f ∈ flipP S o vv,
      (inSign φ f * inSign φ (κ.match_ f)) =
      inSign φ p₁ * inSign φ p₂ := by
  have hv : ∀ vv : W.Vertex,
      ∏ f ∈ flipP S o vv,
        (inSign φ f * inSign φ (κ.match_ f)) =
        ∏ g ∈ diffAtP S vv, inSign φ g := by
    intro vv
    rw [diffAtP_eq h o vv, Finset.prod_disjUnion,
      Finset.prod_image (match_injOn_flipP o vv),
      Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun vv _ => hv vv),
    ← Finset.prod_biUnion diffAtP_pairwiseDisjoint,
    ← S_eq_biUnion_diffAtP h]
  exact prod_inSign_ports h φ

/-! ### The per-vertex sign identity -/

private theorem signAt_portFlip (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (o : κ.Orientation) (φ : F.CoreOddColouring ℓ)
    (vv : W.Vertex) :
    F.coreOddSignAt (o.portFlip h) (portColourFlip h φ) vv =
      (-1 : ℤ) ^ (flipP S o vv).card *
        (∏ f ∈ flipP S o vv,
          inSign φ f * inSign φ (κ.match_ f)) *
        F.coreOddSignAt o φ vv := by
  rw [signAt_eq_prod (o.portFlip h) _ vv, signAt_eq_prod o φ vv,
    inb_portFlip h o vv, Finset.prod_disjUnion]
  have hkeep : ∏ g ∈ keepP S o vv,
      inSign (portColourFlip h φ) (κ.match_ g) =
      ∏ g ∈ keepP S o vv, inSign φ (κ.match_ g) := by
    refine Finset.prod_congr rfl (fun g hg => ?_)
    have hgint := relInSetAt_subset_internal (mem_keepP.mp hg).1
    exact inSign_portFlip_of_int_notMem h φ
      (κ.match_mem g hgint)
      (h.match_notMem hgint (mem_keepP.mp hg).2)
  have himg : ∏ g ∈ (flipP S o vv).image κ.match_,
      inSign (portColourFlip h φ) (κ.match_ g) =
      ∏ f ∈ flipP S o vv, -inSign φ f := by
    rw [Finset.prod_image (match_injOn_flipP o vv)]
    refine Finset.prod_congr rfl (fun f hf => ?_)
    have hfint := relInSetAt_subset_internal (mem_flipP.mp hf).1
    rw [κ.match_invol f hfint]
    exact inSign_portFlip_of_mem h φ (mem_flipP.mp hf).2
  rw [hkeep, himg,
    prod_relInSetAt_split_port (S := S) o vv (fun g => inSign φ (κ.match_ g)),
    Finset.prod_neg]
  have hsq : ∏ f ∈ flipP S o vv, inSign φ f =
      (∏ f ∈ flipP S o vv,
        inSign φ f * inSign φ (κ.match_ f)) *
        ∏ f ∈ flipP S o vv, inSign φ (κ.match_ f) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl (fun f _ => ?_)
    rw [mul_assoc, inSign_mul_self, mul_one]
  rw [hsq]
  ring

/-! ### The per-vertex list identity -/

private theorem evalList_portFlip
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (hM : MixedFunctional k ℓ)
    (μ : Multiset (Fin k)) (o : κ.Orientation)
    (φ : F.CoreOddColouring ℓ) (vv : W.Vertex) :
    hM.evalOdd μ
        (F.coreOddListAt (o.portFlip h) (portColourFlip h φ) vv) =
      (-1 : ℂ) ^ (flipP S o vv).card *
        hM.evalOdd μ (F.coreOddListAt o φ vv) := by
  have Hk : ∀ g ∈ (keepP S o vv).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_keepP.mp (Finset.mem_toList.mp hg)).1
  have Hf : ∀ g ∈ (flipP S o vv).toList, g ∈ F.internalFlags :=
    fun g hg => relInSetAt_subset_internal
      (mem_flipP.mp (Finset.mem_toList.mp hg)).1
  have H2 : ∀ g ∈ (keepP S o vv).toList ++
      (flipP S o vv).toList.map κ.match_, g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hg
      exact κ.match_mem f (Hf f hf)
  have H3 : ∀ g ∈ (keepP S o vv).toList ++ (flipP S o vv).toList,
      g ∈ F.internalFlags := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact Hk g hg
    · exact Hf g hg
  -- ═══════ BOTH IN-FLAG ENUMERATIONS, SPLIT BY THE PORT FLIP ═══════
  -- The unported in-flags are common to the two orientations; the
  -- ported ones appear under the flipped one through the matching.
  have hbase : (F.relInFlagsAt o vv).Perm
      ((keepP S o vv).toList ++ (flipP S o vv).toList) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe o vv,
      ← Multiset.coe_add, Finset.coe_toList, Finset.coe_toList]
    exact relInSetAt_val_split_port o vv
  have hbase' : (F.relInFlagsAt (o.portFlip h) vv).Perm
      ((keepP S o vv).toList ++
        (flipP S o vv).toList.map κ.match_) := by
    rw [← Multiset.coe_eq_coe, relInFlagsAt_coe (o.portFlip h) vv,
      ← Multiset.coe_add, Finset.coe_toList, ← Multiset.map_coe,
      Finset.coe_toList]
    rw [inb_portFlip h o vv, Finset.disjUnion_val,
      Finset.image_val_of_injOn (fun x hx y hy =>
        match_injOn_flipP o vv x (Finset.mem_coe.mp hx) y
          (Finset.mem_coe.mp hy))]
  unfold EdgeSubset.coreOddListAt
  simp only [List.attachWith]
  calc hM.evalOdd μ ((List.pmap Subtype.mk
        (F.relInFlagsAt (o.portFlip h) vv)
        (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf)).flatMap
        (F.coreOddPairFn κ (portColourFlip h φ)))
      = hM.evalOdd μ ((List.pmap Subtype.mk
          ((keepP S o vv).toList ++
            (flipP S o vv).toList.map κ.match_) H2).flatMap
          (F.coreOddPairFn κ (portColourFlip h φ))) := by
        have hp := hM.evalOdd_flatMap_perm μ
          (F.coreOddPairFn κ (portColourFlip h φ))
          (fun _ => rfl)
          (perm_pmap Subtype.mk hbase'
            (fun _ hf => F.mem_internal_of_mem_relInFlagsAt hf) H2)
          []
        simpa using hp
    _ = hM.evalOdd μ
          ((List.pmap Subtype.mk (keepP S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipP S o vv).toList Hf).flatMap
            (fun fs => [pairB (κ₀ := κ) φ fs, pairA φ fs])) := by
        rw [List.pmap_append, List.flatMap_append]
        refine congrArg (hM.evalOdd μ) (congrArg₂
          (fun x y : List (Fin (2 * ℓ)) => x ++ y) ?_ ?_)
        · refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro g hg h₁ h₂
          have hgS : g ∉ S :=
            (mem_keepP.mp (Finset.mem_toList.mp hg)).2
          have hmS : κ.match_ g ∉ S := h.match_notMem h₁ hgS
          change [(portColourFlip h φ).val
              ⟨g, F.internalFlags_subset_coreFlags h₁⟩,
            oddPartner ℓ ((portColourFlip h φ).val
              ⟨κ.match_ g, F.internalFlags_subset_coreFlags
                (κ.match_mem _ h₁)⟩)] =
            [φ.val ⟨g, F.internalFlags_subset_coreFlags h₂⟩,
              oddPartner ℓ (φ.val ⟨κ.match_ g,
                F.internalFlags_subset_coreFlags
                  (κ.match_mem _ h₂)⟩)]
          rw [portColourFlip_val_int_of_notMem h φ _ h₁ hgS,
            portColourFlip_val_int_of_notMem h φ _
              (κ.match_mem _ h₁) hmS]
        · rw [List.pmap_map]
          refine pmap_flatMap_congr _ _ _ _ _ _ _ ?_
          intro f hf h₁ h₂
          have hfS : f ∈ S :=
            (mem_flipP.mp (Finset.mem_toList.mp hf)).2
          have hmS : κ.match_ f ∈ S := h.match_mem f hfS
          have hsub : (⟨κ.match_ (κ.match_ f),
              F.internalFlags_subset_coreFlags
                (κ.match_mem _ h₁)⟩ :
              {g : W.Flag // g ∈ F.coreFlags}) =
              ⟨f, F.internalFlags_subset_coreFlags h₂⟩ :=
            Subtype.ext (κ.match_invol f h₂)
          change [(portColourFlip h φ).val
              ⟨κ.match_ f, F.internalFlags_subset_coreFlags h₁⟩,
            oddPartner ℓ ((portColourFlip h φ).val
              ⟨κ.match_ (κ.match_ f),
                F.internalFlags_subset_coreFlags
                  (κ.match_mem _ h₁)⟩)] =
            [pairB (κ₀ := κ) φ ⟨f, h₂⟩, pairA φ ⟨f, h₂⟩]
          rw [hsub,
            portColourFlip_val_of_mem h φ _ hmS,
            portColourFlip_val_of_mem h φ _ hfS,
            oddPartner_invol]
          rfl
    _ = (-1 : ℂ) ^ (flipP S o vv).card * hM.evalOdd μ
          ((List.pmap Subtype.mk (keepP S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ) ++
          (List.pmap Subtype.mk (flipP S o vv).toList Hf).flatMap
            (fun fs => [pairA φ fs, pairB (κ₀ := κ) φ fs])) := by
        have hrev := evalOdd_flatMap_rev hM μ (pairA φ)
          (pairB (κ₀ := κ) φ)
          (List.pmap Subtype.mk (flipP S o vv).toList Hf)
          ((List.pmap Subtype.mk (keepP S o vv).toList Hk).flatMap
            (F.coreOddPairFn κ φ))
        rw [hrev, List.length_pmap, Finset.length_toList]
    _ = (-1 : ℂ) ^ (flipP S o vv).card * hM.evalOdd μ
          ((List.pmap Subtype.mk
            ((keepP S o vv).toList ++ (flipP S o vv).toList)
            H3).flatMap (F.coreOddPairFn κ φ)) := by
        rw [List.pmap_append, List.flatMap_append]
        rw [coreOddPairFn_eq' (κ₀ := κ) φ]
    _ = (-1 : ℂ) ^ (flipP S o vv).card * hM.evalOdd μ
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

/-! ### The vertex product and the colouring sum -/

private theorem vertexProd_portFlip
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (hM : MixedFunctional k ℓ)
    (o : κ.Orientation) (φ : F.CoreOddColouring ℓ)
    (μf : W.Vertex → Multiset (Fin k)) :
    ∏ vv : W.Vertex,
        ((F.coreOddSignAt (o.portFlip h) (portColourFlip h φ)
            vv : ℂ) *
          hM.evalOdd (μf vv)
            (F.coreOddListAt (o.portFlip h) (portColourFlip h φ)
              vv)) =
      ((inSign φ p₁ * inSign φ p₂ : ℤ) : ℂ) *
        ∏ vv : W.Vertex,
          ((F.coreOddSignAt o φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o φ vv)) := by
  have hglobal : ∏ vv : W.Vertex, ∏ f ∈ flipP S o vv,
      ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ)) =
      ((inSign φ p₁ * inSign φ p₂ : ℤ) : ℂ) := by
    have h1 := flip_prod_ports h o φ
    have h2 : ((∏ vv : W.Vertex, ∏ f ∈ flipP S o vv,
        (inSign φ f * inSign φ (κ.match_ f)) : ℤ) : ℂ) =
        ((inSign φ p₁ * inSign φ p₂ : ℤ) : ℂ) := by
      rw [h1]
    push_cast at h2 ⊢
    exact h2
  have hv : ∀ vv : W.Vertex,
      ((F.coreOddSignAt (o.portFlip h) (portColourFlip h φ)
          vv : ℂ) *
        hM.evalOdd (μf vv)
          (F.coreOddListAt (o.portFlip h) (portColourFlip h φ)
            vv)) =
      (∏ f ∈ flipP S o vv,
        ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
        ((F.coreOddSignAt o φ vv : ℂ) *
          hM.evalOdd (μf vv) (F.coreOddListAt o φ vv)) := by
    intro vv
    rw [signAt_portFlip h o φ vv,
      evalList_portFlip h hM (μf vv) o φ vv]
    have hsq : (-1 : ℂ) ^ (flipP S o vv).card *
        (-1 : ℂ) ^ (flipP S o vv).card = 1 := by
      rw [← mul_pow]
      norm_num
    push_cast
    calc ((-1 : ℂ) ^ (flipP S o vv).card *
          (∏ f ∈ flipP S o vv,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          (F.coreOddSignAt o φ vv : ℂ)) *
        ((-1 : ℂ) ^ (flipP S o vv).card *
          hM.evalOdd (μf vv) (F.coreOddListAt o φ vv)) =
        ((-1 : ℂ) ^ (flipP S o vv).card *
          (-1 : ℂ) ^ (flipP S o vv).card) *
        ((∏ f ∈ flipP S o vv,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          ((F.coreOddSignAt o φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o φ vv))) := by
          ring
      _ = (∏ f ∈ flipP S o vv,
            ((inSign φ f : ℂ) * (inSign φ (κ.match_ f) : ℂ))) *
          ((F.coreOddSignAt o φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o φ vv)) := by
          rw [hsq, one_mul]
  rw [Finset.prod_congr rfl (fun vv _ => hv vv),
    Finset.prod_mul_distrib, hglobal]

/-! ### Pinning the port signs by the boundary constraint -/

private theorem inSign_pin₁ (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {st : GenBoundaryState k ℓ α} {φ : F.CoreOddColouring ℓ}
    (hO : F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ)
    {c₁ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁) :
    inSign φ p₁ = oddPartnerSign ℓ (oddPartner ℓ c₁) := by
  have hstpar : stateOddFlip st i₁ i₂ i₁ = Sum.inr (oddPartner ℓ c₁) :=
    stateOddFlip_left_odd hc₁
  have hval : φ.val ⟨W.boundaryFlag i₁, h.bF₁_core⟩ =
      oddPartner ℓ c₁ :=
    hO i₁ (oddPartner ℓ c₁) hstpar h.bF₁_core
  have h1 : φ.val ⟨p₁, h.p₁_core⟩ =
      φ.val ⟨W.pairing (W.boundaryFlag i₁),
        F.pairing_mem_coreFlags h.bF₁_core⟩ :=
    congrArg φ.val (Subtype.ext h.bF₁_pairing.symm)
  have h2 : φ.val ⟨W.pairing (W.boundaryFlag i₁),
      F.pairing_mem_coreFlags h.bF₁_core⟩ =
      φ.val ⟨W.boundaryFlag i₁, h.bF₁_core⟩ :=
    φ.prop ⟨W.boundaryFlag i₁, h.bF₁_core⟩
  have h3 : inSign φ p₁ =
      oddPartnerSign ℓ (φ.val ⟨p₁, h.p₁_core⟩) := dite_eq_left h.p₁_core
  rw [h3, h1, h2, hval]

private theorem inSign_pin₂ (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {st : GenBoundaryState k ℓ α} {φ : F.CoreOddColouring ℓ}
    (hO : F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ)
    {c₂ : Fin (2 * ℓ)} (hc₂ : st i₂ = Sum.inr c₂) :
    inSign φ p₂ = oddPartnerSign ℓ (oddPartner ℓ c₂) := by
  have hstpar : stateOddFlip st i₁ i₂ i₂ = Sum.inr (oddPartner ℓ c₂) :=
    stateOddFlip_right_odd hc₂
  have hval : φ.val ⟨W.boundaryFlag i₂, h.bF₂_core⟩ =
      oddPartner ℓ c₂ :=
    hO i₂ (oddPartner ℓ c₂) hstpar h.bF₂_core
  have h1 : φ.val ⟨p₂, h.p₂_core⟩ =
      φ.val ⟨W.pairing (W.boundaryFlag i₂),
        F.pairing_mem_coreFlags h.bF₂_core⟩ :=
    congrArg φ.val (Subtype.ext h.bF₂_pairing.symm)
  have h2 : φ.val ⟨W.pairing (W.boundaryFlag i₂),
      F.pairing_mem_coreFlags h.bF₂_core⟩ =
      φ.val ⟨W.boundaryFlag i₂, h.bF₂_core⟩ :=
    φ.prop ⟨W.boundaryFlag i₂, h.bF₂_core⟩
  have h3 : inSign φ p₂ =
      oddPartnerSign ℓ (φ.val ⟨p₂, h.p₂_core⟩) := dite_eq_left h.p₂_core
  rw [h3, h1, h2, hval]

/-! ### The colouring-sum and even-sum identities -/

open scoped Classical in
private theorem phiSum_portFlip (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (o : κ.Orientation)
    (μf : W.Vertex → Multiset (Fin k)) :
    ∑ φ : F.CoreOddColouring ℓ,
        (if F.coreOddBoundaryMatch st φ then
          ∏ vv : W.Vertex,
            ((F.coreOddSignAt (o.portFlip h) φ vv : ℂ) *
              hM.evalOdd (μf vv)
                (F.coreOddListAt (o.portFlip h) φ vv))
        else 0) =
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
        ∑ φ : F.CoreOddColouring ℓ,
          (if F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ then
            ∏ vv : W.Vertex,
              ((F.coreOddSignAt o φ vv : ℂ) *
                hM.evalOdd (μf vv) (F.coreOddListAt o φ vv))
          else 0) := by
  rw [Finset.mul_sum]
  refine ((Equiv.sum_comp (Function.Involutive.toPerm _
      (portColourFlip_involutive h)) _).symm).trans
    (Finset.sum_congr rfl (fun φ _ => ?_))
  change (if F.coreOddBoundaryMatch st (portColourFlip h φ) then
      ∏ vv : W.Vertex,
        ((F.coreOddSignAt (o.portFlip h) (portColourFlip h φ)
            vv : ℂ) *
          hM.evalOdd (μf vv)
            (F.coreOddListAt (o.portFlip h) (portColourFlip h φ)
              vv))
    else 0) =
    ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
      (if F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ then
        ∏ vv : W.Vertex,
          ((F.coreOddSignAt o φ vv : ℂ) *
            hM.evalOdd (μf vv) (F.coreOddListAt o φ vv))
      else 0)
  rcases Classical.em
      (F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂) φ) with
    hO | hO
  · rw [ite_eq_left ((coreOddBoundaryMatch_portColourFlip h st φ).mpr
        hO),
      ite_eq_left hO, vertexProd_portFlip h hM o φ μf,
      inSign_pin₁ h hO hc₁, inSign_pin₂ h hO hc₂,
      oddPartnerSign_oddPartner, oddPartnerSign_oddPartner]
    push_cast
    ring
  · rw [ite_eq_right (fun hc =>
        hO ((coreOddBoundaryMatch_portColourFlip h st φ).mp hc)),
      ite_eq_right hO, mul_zero]

private theorem evenMatch_stateOddFlip {st : GenBoundaryState k ℓ α}
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (ψ : F.EvenColouring k) :
    genEvenBoundaryMatch F (stateOddFlip st i₁ i₂)
        (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) ψ ↔
      genEvenBoundaryMatch F st hbnd ψ := by
  unfold genEvenBoundaryMatch
  constructor
  · intro H i c hst
    exact H i c ((stateOddFlip_isInl i c).mpr hst)
  · intro H i c hst
    exact H i c ((stateOddFlip_isInl i c).mp hst)

/-! ### The through product is untouched -/

private noncomputable def tBody [LinearOrder α]
    (st : GenBoundaryState k ℓ α) (f : W.Flag) : ℂ :=
  match W.attach f, W.attach (W.pairing f) with
  | Sum.inr i, Sum.inr j =>
      if i < j then throughStateFactor (st i) (st j) else 1
  | _, _ => 1

private theorem throughProduct_eq_body [LinearOrder α]
    (st : GenBoundaryState k ℓ α) :
    F.throughProduct st = ∏ f ∈ F.throughFlags, tBody st f := by
  unfold EdgeSubset.throughProduct
  exact Finset.prod_attach _ (tBody st)

open scoped Classical in
private theorem tBody_stateOddFlip [LinearOrder α]
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (st : GenBoundaryState k ℓ α) {f : W.Flag}
    (hf : f ∈ F.throughFlags) :
    tBody (stateOddFlip st i₁ i₂) f = tBody st f := by
  obtain ⟨hfl, ⟨i, hi⟩, ⟨j, hj⟩⟩ := Finset.mem_filter.mp hf
  have hi' : i ≠ i₁ ∧ i ≠ i₂ := by
    have hfb : f = W.boundaryFlag i := W.eq_boundaryFlag i f hi
    constructor
    · intro he
      have hp : W.pairing f = p₁ := by
        rw [hfb, he]
        exact h.bF₁_pairing
      have hint : W.pairing f ∈ F.internalFlags := by
        rw [hp]
        exact h.int_of_mem p₁ h.hp₁S
      obtain ⟨v, hv⟩ := F.attach_internal_of_mem hint
      rw [hv] at hj
      cases hj
    · intro he
      have hp : W.pairing f = p₂ := by
        rw [hfb, he]
        exact h.bF₂_pairing
      have hint : W.pairing f ∈ F.internalFlags := by
        rw [hp]
        exact h.int_of_mem p₂ h.hp₂S
      obtain ⟨v, hv⟩ := F.attach_internal_of_mem hint
      rw [hv] at hj
      cases hj
  have hj' : j ≠ i₁ ∧ j ≠ i₂ := by
    have hfb : W.pairing f = W.boundaryFlag j :=
      W.eq_boundaryFlag j _ hj
    constructor
    · intro he
      have hp : f = p₁ := by
        have h1 := congrArg W.pairing hfb
        rw [W.pairing_invol, he, h.bF₁_pairing] at h1
        exact h1
      have hint : f ∈ F.internalFlags := by
        rw [hp]
        exact h.int_of_mem p₁ h.hp₁S
      obtain ⟨v, hv⟩ := F.attach_internal_of_mem hint
      rw [hv] at hi
      cases hi
    · intro he
      have hp : f = p₂ := by
        have h1 := congrArg W.pairing hfb
        rw [W.pairing_invol, he, h.bF₂_pairing] at h1
        exact h1
      have hint : f ∈ F.internalFlags := by
        rw [hp]
        exact h.int_of_mem p₂ h.hp₂S
      obtain ⟨v, hv⟩ := F.attach_internal_of_mem hint
      rw [hv] at hi
      cases hi
  unfold tBody
  rw [hi, hj]
  change (if i < j then
      throughStateFactor (stateOddFlip st i₁ i₂ i)
        (stateOddFlip st i₁ i₂ j) else 1) =
    (if i < j then throughStateFactor (st i) (st j) else 1)
  rw [stateOddFlip_of_ne hi'.1 hi'.2,
    stateOddFlip_of_ne hj'.1 hj'.2]

private theorem throughProduct_stateOddFlip [LinearOrder α]
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (st : GenBoundaryState k ℓ α) :
    F.throughProduct (stateOddFlip st i₁ i₂) =
      F.throughProduct st := by
  rw [throughProduct_eq_body (stateOddFlip st i₁ i₂),
    throughProduct_eq_body st]
  exact Finset.prod_congr rfl
    (fun f hf => tBody_stateOddFlip h st hf)

/-! ### The chain-flip ledger -/

open scoped Classical in
/-- **The chain-flip ledger at the colouring sum**: flipping the
orientation of a ported chain multiplies the sum over colourings by
the two chain-end colour signs and flips the state there.  This is
the vertex-sum form of the ledger; the through-edge product is
untouched, so the constrained summand's form follows. -/
theorem psiSum_portFlip
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (o : κ.Orientation) :
    ∑ ψ : F.EvenColouring k,
        (if genEvenBoundaryMatch F st hbnd ψ then
          ∑ φ : F.CoreOddColouring ℓ,
            (if F.coreOddBoundaryMatch st φ then
              ∏ vv : W.Vertex,
                ((F.coreOddSignAt (o.portFlip h) φ vv : ℂ) *
                  hM.evalOdd (F.evenColoursAt ψ vv)
                    (F.coreOddListAt (o.portFlip h) φ vv))
            else 0)
        else 0) =
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
        ∑ ψ : F.EvenColouring k,
          (if genEvenBoundaryMatch F (stateOddFlip st i₁ i₂)
              (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂)
              ψ then
            ∑ φ : F.CoreOddColouring ℓ,
              (if F.coreOddBoundaryMatch (stateOddFlip st i₁ i₂)
                  φ then
                ∏ vv : W.Vertex,
                  ((F.coreOddSignAt o φ vv : ℂ) *
                    hM.evalOdd (F.evenColoursAt ψ vv)
                      (F.coreOddListAt o φ vv))
              else 0)
          else 0) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ψ _ => ?_)
  rcases Classical.em (genEvenBoundaryMatch F st hbnd ψ) with
    hE | hE
  · rw [ite_eq_left hE, ite_eq_left ((evenMatch_stateOddFlip hbnd ψ).mpr hE)]
    exact phiSum_portFlip h hM st hc₁ hc₂ o (F.evenColoursAt ψ)
  · rw [ite_eq_right hE,
      ite_eq_right (fun hc => hE ((evenMatch_stateOddFlip hbnd ψ).mp hc)),
      mul_zero]

/-- **The chain-flip ledger**: flipping the orientation of a ported
flip set (a full boundary chain) multiplies the constrained summand
by the two chain-end colour signs *and `∂`-relabels the state at
the two end labels* — the local system acts on states.  Valid at
every circuit exponent. -/
theorem throughSummand_portFlip [LinearOrder α]
    (hM : MixedFunctional k ℓ) (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (o : κ.Orientation) (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (n : ℕ) :
    F.throughSummand hM st hbnd (o.portFlip h) n =
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
        F.throughSummand hM (stateOddFlip st i₁ i₂)
          (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o n := by
  unfold EdgeSubset.throughSummand
  rw [psiSum_portFlip h hM st hbnd hc₁ hc₂ o,
    throughProduct_stateOddFlip h st]
  ring

end PortFlipLedger

/-! ## The boundary chain as a ported flip set -/

section ChainConstruction

variable {α : Type}

/-- **The chain flip set**: the internal flags of a full
boundary-terminated chain form a ported flip set whose ports are
the two chain-end entry flags and whose labels are the chain's two
boundary labels. -/
theorem exists_chainPortedFlipSet {W : Fragment α} {F : EdgeSubset W}
    (κ : F.RelTransitionSystem)
    {β : W.Flag} (hβ : β ∈ F.boundaryFlags) {kc : ℕ}
    (hcont : ∀ j, j < kc →
      W.pairing (iterWalk κ β j) ∈ F.internalFlags)
    (hterm : W.pairing (iterWalk κ β kc) ∈ F.boundaryFlags)
    (hk : 1 ≤ kc) {iβ iγ : α} (hiβ : W.attach β = Sum.inr iβ)
    (hiγ : W.attach (W.pairing (iterWalk κ β kc)) = Sum.inr iγ) :
    ∃ S : Finset W.Flag,
      PortedFlipSet κ S (W.pairing β) (iterWalk κ β kc) iβ iγ ∧
      (∀ f ∈ S, OnBoundaryChain κ β f) ∧
      (∀ f ∈ F.internalFlags, OnBoundaryChain κ β f → f ∈ S) := by
  -- ═══════ THE PORTED FLIP SET IS THE CHAIN'S WALK IMAGE ═══════
  -- The set is the first `kc` steps of the walk from the chain's
  -- entry; the obligations are that it is internal, matching-closed
  -- and pairing-closed except at the two ends.
  refine ⟨(Finset.range kc).image
      (fun j => W.pairing (iterWalk κ β j)) ∪
    (Finset.range kc).image (fun j => iterWalk κ β (j + 1)),
    ?_, ?_, ?_⟩
  case _ =>
    have hmemS : ∀ f : W.Flag,
        f ∈ (Finset.range kc).image
            (fun j => W.pairing (iterWalk κ β j)) ∪
          (Finset.range kc).image
            (fun j => iterWalk κ β (j + 1)) ↔
        ∃ j, j < kc ∧ (f = W.pairing (iterWalk κ β j) ∨
          f = iterWalk κ β (j + 1)) := by
      intro f
      rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
      constructor
      · rintro (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
        · exact ⟨j, Finset.mem_range.mp hj, Or.inl rfl⟩
        · exact ⟨j, Finset.mem_range.mp hj, Or.inr rfl⟩
      · rintro ⟨j, hj, rfl | rfl⟩
        · exact Or.inl ⟨j, Finset.mem_range.mpr hj, rfl⟩
        · exact Or.inr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    refine
      { int_of_mem := ?_
        match_mem := ?_
        pairing_mem := ?_
        hp₁S := ?_
        hp₂S := ?_
        hp₁₂ := ?_
        hσ₁ := ?_
        hσ₂ := ?_ }
    · intro f hf
      rw [hmemS] at hf
      obtain ⟨j, hj, rfl | rfl⟩ := hf
      · exact hcont j hj
      · exact iterWalk_mem_internal κ kc (by omega) (by omega)
          hcont
    · intro f hf
      rw [hmemS] at hf ⊢
      obtain ⟨j, hj, rfl | rfl⟩ := hf
      · exact ⟨j, hj, Or.inr (iterWalk_succ κ β j).symm⟩
      · refine ⟨j, hj, Or.inl ?_⟩
        rw [iterWalk_succ, κ.match_invol _ (hcont j hj)]
    · intro f hf hne₁ hne₂
      rw [hmemS] at hf ⊢
      obtain ⟨j, hj, rfl | rfl⟩ := hf
      · rcases Nat.eq_zero_or_pos j with rfl | hj1
        · exact absurd (by rw [iterWalk_zero]) hne₁
        · refine ⟨j - 1, by omega, Or.inr ?_⟩
          rw [W.pairing_invol, show j - 1 + 1 = j from by omega]
      · rcases Nat.lt_or_ge (j + 1) kc with hjk | hjk
        · refine ⟨j + 1, hjk, Or.inl ?_⟩
          rfl
        · exfalso
          have hje : j + 1 = kc := by omega
          rw [hje] at hne₂
          exact hne₂ rfl
    · rw [hmemS]
      exact ⟨0, by omega, Or.inl (by rw [iterWalk_zero])⟩
    · rw [hmemS]
      refine ⟨kc - 1, by omega, Or.inr ?_⟩
      rw [show kc - 1 + 1 = kc from by omega]
    · have h1 := pairing_iterWalk_ne κ hcont (Nat.zero_le kc)
        (le_refl kc)
      rwa [iterWalk_zero] at h1
    · rw [W.pairing_invol]
      exact W.eq_boundaryFlag iβ β hiβ
    · exact W.eq_boundaryFlag iγ _ hiγ
  case _ =>
    intro f hf
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image] at hf
    rcases hf with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · exact ⟨kc, j, le_of_lt (Finset.mem_range.mp hj), hcont,
        hterm, Or.inr rfl⟩
    · exact ⟨kc, j + 1, by
        have := Finset.mem_range.mp hj
        omega, hcont, hterm, Or.inl rfl⟩
  case _ =>
    intro f hfint hon
    obtain ⟨k', t, htk, hcont', hterm', hft⟩ := hon
    have hkk : kc = k' :=
      (chain_exit_unique hcont' hterm' hcont hterm).symm
    subst hkk
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rcases hft with rfl | rfl
    · rcases Nat.eq_zero_or_pos t with rfl | ht1
      · exfalso
        rw [iterWalk_zero] at hfint
        exact Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hfint hβ
      · refine Or.inr ⟨t - 1, Finset.mem_range.mpr (by omega), ?_⟩
        rw [show t - 1 + 1 = t from by omega]
    · rcases Nat.lt_or_ge t kc with htk' | htk'
      · exact Or.inl ⟨t, Finset.mem_range.mpr htk', rfl⟩
      · exfalso
        have hte : t = kc := by omega
        rw [hte] at hfint
        exact Finset.disjoint_left.mp
          F.internalFlags_disjoint_boundaryFlags hfint hterm

end ChainConstruction

/-! ## The two-path non-separated transform -/

section NonSepTransform

variable {α : Type} {W : Fragment α} {F : EdgeSubset W}
  {κ : F.RelTransitionSystem} {S : Finset W.Flag}
  {p₁ p₂ : W.Flag} {i₁ i₂ : α} {k ℓ : ℕ}

/-- **The two-path non-separated transform factor**: minus the
product of the `∂`-signs of the two chain-end colours of the
original state.  Unlike the separated factor `−1`, it depends on
the boundary state (only through those two signs), and the
transform additionally `∂`-relabels the state at the two chain-end
labels. -/
noncomputable def twoPathNonSepFactor (ℓ : ℕ)
    (c₁ c₂ : Fin (2 * ℓ)) : ℂ :=
  -(((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ))

/-- The factor unfolded: minus the product of the two chain-end
colours' odd-partner signs. -/
theorem twoPathNonSepFactor_eq (ℓ : ℕ) (c₁ c₂ : Fin (2 * ℓ)) :
    twoPathNonSepFactor ℓ c₁ c₂ =
      -(((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ)) :=
  rfl

private theorem signProd_cast_mul_self (ℓ : ℕ)
    (c₁ c₂ : Fin (2 * ℓ)) :
    ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) *
      ((oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂ : ℤ) : ℂ) = 1 := by
  have hz : (oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂) *
      (oddPartnerSign ℓ c₁ * oddPartnerSign ℓ c₂) = (1 : ℤ) := by
    unfold oddPartnerSign
    split_ifs <;> norm_num
  rw [← Int.cast_mul, hz, Int.cast_one]

/-- The factor is an involution: the two signs are each `±1`. -/
theorem twoPathNonSepFactor_mul_self (ℓ : ℕ)
    (c₁ c₂ : Fin (2 * ℓ)) :
    twoPathNonSepFactor ℓ c₁ c₂ * twoPathNonSepFactor ℓ c₁ c₂ =
      1 := by
  unfold twoPathNonSepFactor
  rw [neg_mul_neg]
  exact signProd_cast_mul_self ℓ c₁ c₂

/-- The chain flip separates a non-separated square when `c` is on
the flipped chain and `a` is off it. -/
theorem portFlip_separated (o : κ.Orientation)
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂) {a c : W.Flag}
    (hsame : o.isOut c = o.isOut a) (hcS : c ∈ S) (haS : a ∉ S) :
    (o.portFlip h).isOut c = !(o.portFlip h).isOut a := by
  rw [portFlip_isOut_of_mem o h hcS,
    portFlip_isOut_of_notMem o h haS, hsame]

/-- **The two-path non-separated transform, fixed exponent**: with
the transported chain-flip orientation, the repaired summand at any
circuit exponent is `twoPathNonSepFactor` times the original
summand at the `∂`-relabelled state. -/
theorem twoPathNonSep_transform_exp [LinearOrder α]
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {a b c d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hsame : o.isOut c = o.isOut a)
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hcS : c ∈ S) (haS : a ∉ S)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) (n : ℕ) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip h) (portFlip_separated o h hsame hcS haS))
        n =
      twoPathNonSepFactor ℓ c₁ c₂ *
        F.throughSummand hM (stateOddFlip st i₁ i₂)
          (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o
          n := by
  rw [twoPath_transform_exp hM st hbnd hsq (o.portFlip h)
      (portFlip_separated o h hsame hcS haS) n,
    throughSummand_portFlip hM st hbnd o h hc₁ hc₂ n,
    twoPathTransformFactor_eq_neg_one]
  unfold twoPathNonSepFactor
  ring

/-- **The two-path non-separated transform** (parametric form):
for a non-localized square with non-separated orientation, flipping
the ported chain of `c` and transporting across the repair
transforms the constrained summand at the open circuit counts by
the explicit factor `twoPathNonSepFactor ℓ c₁ c₂ = −(sign c₁ ·
sign c₂)` — **evaluated at the `∂`-relabelled state**.  The state
relabel is intrinsic: the chain flip meets the boundary at the
chain's two end labels, so no state-preserving scalar form of the
move exists. -/
theorem twoPathNonSep_transform [LinearOrder α]
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    {a b c d : W.Flag} {v : W.Vertex}
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hsame : o.isOut c = o.isOut a)
    (hnl : ¬ SquareLocalized κ a b c d)
    (h : PortedFlipSet κ S p₁ p₂ i₁ i₂)
    (hcS : c ∈ S) (haS : a ∉ S)
    {c₁ c₂ : Fin (2 * ℓ)} (hc₁ : st i₁ = Sum.inr c₁)
    (hc₂ : st i₂ = Sum.inr c₂) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq
          (o.portFlip h) (portFlip_separated o h hsame hcS haS))
        ((κ.repair a b c d v hsq).openCircuitCount) =
      twoPathNonSepFactor ℓ c₁ c₂ *
        F.throughSummand hM (stateOddFlip st i₁ i₂)
          (genBoundarySubsetMatches_stateOddFlip hbnd i₁ i₂) o
          κ.openCircuitCount := by
  rw [openCircuitCount_repair_of_not_localized hsq hnl]
  exact twoPathNonSep_transform_exp hM st hbnd hsq o hsame h hcS
    haS hc₁ hc₂ κ.openCircuitCount

end NonSepTransform

end EdgeSubset

end RS
