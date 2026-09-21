/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.TwoPathStep
import LeanPool.RegtsSevenster.RS.Novel.Skein.PairingConnectivity

/-!
# The transpose ledger: the explicit two-path transform factor

The two-path separated move transforms the
constrained summand by an **explicit** factor `T`.  This file pins
`T` down, for the separated orientation class over the transported
orientation:

  `T = twoPathTransformFactor = −1`,

**independent of the boundary state, of the `∂`-data at the four
re-paired ends, and of the transition system** beyond the two-chain
separated configuration.  The decomposition behind the constant:

* the vertex bookkeeping contributes the alternating-evaluation
  transposition sign of the two re-paired pair-blocks at the
  square's vertex (`MixedFunctional.evalOdd_transpose`, the
  engine inside `throughSummand_transportRepair`): `−1`;
* the `oddPartnerSign` factors at the two changed blocks merely
  commute (`+1`);
* the colour re-routing between the two chains is, at the sum
  level, the **identity** reindexing of the `φ`-sum: the
  transported orientation keeps `isOut`, each repaired chain still
  carries its boundary colour data along the same strand segments,
  and only the *partner* entries of the two vertex blocks swap.
  So the state-dependent piece is `+1` for every boundary state —
  the colour sets the functional is evaluated on change, but the
  colourings themselves are not re-indexed.

## Main results

* `EdgeSubset.twoPathTransformFactor` — the explicit factor,
  `(-1 : ℂ)` (`twoPathTransformFactor_eq_neg_one`).
* `EdgeSubset.twoPath_transform` — **the two-path transform**: on a
  two-chain (non-localized) separated square,
  `throughSummand (transportRepair o) (count κ') =
    T * throughSummand o (count κ)`
  (count invariance `openCircuitCount_repair_of_not_localized` plus
  the vertex ledger `throughSummand_transportRepair`);
  `twoPath_transform_exp` is the fixed-exponent form, showing `T`
  is exponent-independent.
* `TransposeVerify` — a worked instance carrying the vocabulary
  concretely, and the value `cSummand_O = −1` that
  `ThroughIndCFalse.lean` compares against.
-/

namespace RS

namespace EdgeSubset

/-- **The two-path transform factor**: the explicit `T` of the
separated two-path move over the transported orientation.  It is
the transposition sign of the alternating evaluation at the
square's vertex; the `oddPartnerSign` commutation and the colour
re-routing contribute `+1` each, so `T` is constant — independent
of the boundary state, the `∂`-data at the four re-paired ends,
and the transition system. -/
noncomputable def twoPathTransformFactor : ℂ := -1

/-- The factor unfolded. -/
theorem twoPathTransformFactor_eq_neg_one :
    twoPathTransformFactor = -1 := rfl

section Transform

open scoped Classical

variable {α : Type}

/-- The fixed-exponent transform: at every circuit exponent the
transported summand is `T` times the old summand — `T` is
exponent-independent (restating the vertex ledger with
the explicit factor). -/
theorem twoPath_transform_exp
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a) (n : ℕ) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip) n =
      twoPathTransformFactor *
        F.throughSummand hM st hbnd o n := by
  rw [throughSummand_transportRepair hM st hbnd hsq o hflip n]
  unfold twoPathTransformFactor
  ring

/-- **The two-path transform**: a repair at a two-chain square
(`twoChains_of_not_localized` configuration), separated class, over
the transported orientation, transforms the constrained summand at
the open circuit counts by the explicit factor
`T = twoPathTransformFactor = −1` — the circuit count is unchanged
and the vertex transposition supplies the sign; the state-dependent
`∂`-piece of the colour re-routing is trivial at the sum level. -/
theorem twoPath_transform
    [LinearOrder α] {W : Fragment α} {F : EdgeSubset W} {k : ℕ} {ℓ : ℕ}
    {κ : F.RelTransitionSystem} {a : W.Flag} {b : W.Flag} {c : W.Flag}
    {d : W.Flag} {v : W.Vertex}
    (hM : MixedFunctional k ℓ)
    (st : GenBoundaryState k ℓ α)
    (hbnd : genBoundarySubsetMatches W F.flags st)
    (hsq : RepairSquare κ a b c d v) (o : κ.Orientation)
    (hflip : o.isOut c = !o.isOut a)
    (hnl : ¬ SquareLocalized κ a b c d) :
    F.throughSummand hM st hbnd
        (RelTransitionSystem.Orientation.transportRepair hsq o
          hflip)
        ((κ.repair a b c d v hsq).openCircuitCount) =
      twoPathTransformFactor *
        F.throughSummand hM st hbnd o κ.openCircuitCount := by
  rw [openCircuitCount_repair_of_not_localized hsq hnl]
  exact twoPath_transform_exp hM st hbnd hsq o hflip
    κ.openCircuitCount

end Transform

end EdgeSubset

/-!
## The worked instance

One vertex carrying two boundary-to-boundary paths with disjoint
boundary chords: labels `0 < 1 < 2 < 3`, chain `(0,1)` through the
matched pair `0 ↔ 1`, chain `(2,3)` through `2 ↔ 3` (flags `0–3`
internal, flags `4–7` at the boundary labels), edge assignment
`pairing = ![4,5,7,6,0,1,3,2]`.  The square `0 ↔ 1`, `2 ↔ 3` is
non-localized, the orientation `![F,T,T,F]` is separated
(`isOut 2 = !isOut 0`), both circuit counts are `0`, and both
chord-crossing counts are `0`, so both path signs are trivial
(`cChord_kappa`, `cPathSign_kappa`).

Against the functional supported on the colour set `{0,5,2,7}` the
constrained summand is `−1` (`cSummand_O`).  `LoopVerify.lean`
computes the same summand for a repaired system at a flipped
orientation, and `ThroughIndCFalse.lean` reads the two values off
to refute independence across boundary pairings.
-/

namespace TransposeVerify

open EdgeSubset

/-- One vertex, four pendant edges: flags `0–3` at the vertex,
flags `4–7` at boundary labels `0–3`; edges `{0,4}`, `{1,5}`,
`{3,6}`, `{2,7}`. -/
@[reducible] def cFragment : Fragment (Fin 4) where
  Flag := Fin 8
  Vertex := Unit
  attach := ![Sum.inl (), Sum.inl (), Sum.inl (), Sum.inl (),
    Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
  pairing := ![4, 5, 7, 6, 0, 1, 3, 2]
  pairing_invol := by decide
  pairing_ne := by decide
  boundaryFlag := ![4, 5, 6, 7]
  attach_boundaryFlag := by decide
  eq_boundaryFlag := by decide
  circles := 0

/-- The unique vertex. -/
def cV : cFragment.Vertex := ()

/-- The full edge subset. -/
def cSubset : EdgeSubset cFragment :=
  ⟨Finset.univ, fun f _ => Finset.mem_univ (cFragment.pairing f)⟩

/-- The verification instance's matching: `0 ↔ 1`, `2 ↔ 3` at the
single vertex, boundary flags fixed. -/
def cMatch : Fin 8 → Fin 8 := ![1, 0, 3, 2, 4, 5, 6, 7]

/-- The instance's internal flags are exactly `0–3`. -/
theorem cInternal_cases {f : Fin 8}
    (hf : f ∈ cSubset.internalFlags) :
    f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3 := by
  obtain ⟨v, hv⟩ := cSubset.attach_internal_of_mem hf
  cases v
  fin_cases f
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact absurd hv (by decide)
  · exact absurd hv (by decide)
  · exact absurd hv (by decide)
  · exact absurd hv (by decide)

/-- Each of `0–3` is an internal flag. -/
theorem cMem_internal {f : Fin 8}
    (hf : f = 0 ∨ f = 1 ∨ f = 2 ∨ f = 3) :
    f ∈ cSubset.internalFlags := by
  rcases hf with rfl | rfl | rfl | rfl <;>
    exact mem_internalFlags_of (Finset.mem_univ _) ⟨(), rfl⟩

/-- A boundary-attached flag is a boundary flag. -/
theorem cMem_boundary {f : Fin 8} (i : Fin 4)
    (h : cFragment.attach f = Sum.inr i) :
    f ∈ cSubset.boundaryFlags := by
  rcases cSubset.mem_internalFlags_or_boundaryFlags
      (Finset.mem_univ f) with hint | hb
  · obtain ⟨v, hv⟩ := cSubset.attach_internal_of_mem hint
    rw [h] at hv
    cases hv
  · exact hb

/-- The instance's boundary flags are exactly `4–7`. -/
theorem cBoundary_cases {f : Fin 8}
    (hf : f ∈ cSubset.boundaryFlags) :
    f = 4 ∨ f = 5 ∨ f = 6 ∨ f = 7 := by
  obtain ⟨lab, hlab⟩ := cSubset.attach_boundary_of_mem hf
  have hbf := cFragment.eq_boundaryFlag lab f hlab
  subst hbf
  fin_cases lab
  · exact Or.inl (by decide)
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inr (Or.inr (Or.inl (by decide)))
  · exact Or.inr (Or.inr (Or.inr (by decide)))

/-- The matching `0 ↔ 1`, `2 ↔ 3`: two boundary chains with
disjoint chords `(0,1)` and `(2,3)`. -/
def cKappa : cSubset.RelTransitionSystem where
  match_ := cMatch
  match_invol := fun f hf => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;> rfl
  match_ne := fun f hf => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;> decide
  match_mem := fun f hf => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl
    · exact cMem_internal (Or.inr (Or.inl rfl))
    · exact cMem_internal (Or.inl rfl)
    · exact cMem_internal (Or.inr (Or.inr (Or.inr rfl)))
    · exact cMem_internal (Or.inr (Or.inr (Or.inl rfl)))
  match_vertex := fun f hf v hv => by
    cases v
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;> rfl

/-- The square `0 ↔ 1`, `2 ↔ 3` at the vertex. -/
theorem cSquare : RepairSquare cKappa 0 1 2 3 cV :=
  ⟨cMem_internal (Or.inl rfl),
    cMem_internal (Or.inr (Or.inr (Or.inl rfl))),
    rfl, rfl, by decide, by decide, by decide, by decide, rfl, rfl⟩

/-- The separated, path-canonical orientation: both chains enter
the vertex through their low-label ends. -/
def cO : cKappa.Orientation where
  isOut := ![false, true, true, false, false, false, false, false]
  match_flip := fun f hf => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;> rfl
  pairing_flip := fun f hf hp => by
    rcases cInternal_cases hf with rfl | rfl | rfl | rfl <;>
      · rcases cInternal_cases hp with h | h | h | h <;>
          exact absurd h (by decide)

/-- The boundary state: odd colours `0, 1, 2, 3` at labels
`0, 1, 2, 3`. -/
def cState : GenBoundaryState 0 4 (Fin 4) :=
  ![Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]

/-- The state matches the fragment's boundary: each of the four
legs carries the colour the state names. -/
theorem cBnd :
    genBoundarySubsetMatches cFragment cSubset.flags cState := by
  intro i
  constructor
  · intro _
    fin_cases i
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
  · intro _
    exact Finset.mem_univ _

/-- The functional supported on the colour set `{0, 5, 2, 7}` (the
odd-list set of the original summand). -/
noncomputable def cFunctional : MixedFunctional 0 4 :=
  fun _ s => if s = ({0, 5, 2, 7} : Finset (Fin (2 * 4))) then 1
    else 0

/-- The functional's values, unfolded: `1` at the original
summand's odd-list set and `0` elsewhere. -/
theorem cFunctional_apply (μ : Multiset (Fin 0))
    (s : Finset (Fin (2 * 4))) :
    cFunctional μ s =
      if s = ({0, 5, 2, 7} : Finset (Fin (2 * 4))) then 1 else 0 :=
  rfl

/-! ### The pinned core colouring -/

/-- Every flag is a core flag. -/
theorem cCoreFlags : cSubset.coreFlags = Finset.univ := by
  apply Finset.ext
  intro g
  simp only [Finset.mem_univ, iff_true]
  rw [EdgeSubset.mem_coreFlags_iff]
  refine ⟨Finset.mem_univ g, ?_⟩
  fin_cases g
  · exact Or.inl ⟨cV, rfl⟩
  · exact Or.inl ⟨cV, rfl⟩
  · exact Or.inl ⟨cV, rfl⟩
  · exact Or.inl ⟨cV, rfl⟩
  · exact Or.inr ⟨cV, rfl⟩
  · exact Or.inr ⟨cV, rfl⟩
  · exact Or.inr ⟨cV, rfl⟩
  · exact Or.inr ⟨cV, rfl⟩

/-- No flag is a through flag: both boundary chains pass through
the vertex. -/
theorem cThroughFlags : cSubset.throughFlags = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  have hcore : f ∈ cSubset.coreFlags := by
    rw [cCoreFlags]
    exact Finset.mem_univ f
  unfold EdgeSubset.coreFlags at hcore
  exact (Finset.mem_sdiff.mp hcore).2 hf

/-- With no through flags the through product is `1`, so it drops
out of both summands being compared. -/
theorem cThroughProduct :
    cSubset.throughProduct cState = 1 := by
  unfold EdgeSubset.throughProduct
  rw [cThroughFlags]
  simp

/-- The edge colours: edge `{0,4}` gets `0`, `{1,5}` gets `1`,
`{3,6}` gets `2`, `{2,7}` gets `3`. -/
def cColour : Fin 8 → Fin (2 * 4) := ![0, 1, 3, 2, 0, 1, 2, 3]

/-- The pinned core odd colouring. -/
noncomputable def cPhi : cSubset.CoreOddColouring 4 :=
  ⟨fun g => cColour g.val, fun g => by
    have hval : ∀ x : Fin 8,
        cColour (cFragment.pairing x) = cColour x := by decide
    exact hval g.val⟩

/-- Every flag participates, so there are no non-participating
flags to colour. -/
instance :
    IsEmpty {f : cFragment.Flag // f ∉ cSubset.flags} :=
  ⟨fun f => f.prop (Finset.mem_univ f.val)⟩

/-- The unique (empty) even colouring. -/
noncomputable def cPsi : cSubset.EvenColouring 0 :=
  ⟨fun f => isEmptyElim f, fun f => isEmptyElim f⟩

/-- The even colouring is unique: there is nothing to choose. -/
instance : Subsingleton (cSubset.EvenColouring 0) :=
  ⟨fun _ _ => Subtype.ext (funext fun f => isEmptyElim f)⟩

/-- The empty even colouring matches the state's even part: with
`k = 0` there is nothing to check. -/
theorem cEvenMatch :
    genEvenBoundaryMatch cSubset cState cBnd cPsi :=
  fun _ c _ => Fin.elim0 c

/-- The pinned colouring is boundary-matched. -/
theorem cOddMatch :
    cSubset.coreOddBoundaryMatch cState cPhi := by
  intro i c hst hcore
  fin_cases i
  · obtain rfl : (0 : Fin (2 * 4)) = c := Sum.inr.inj hst
    rfl
  · obtain rfl : (1 : Fin (2 * 4)) = c := Sum.inr.inj hst
    rfl
  · obtain rfl : (2 : Fin (2 * 4)) = c := Sum.inr.inj hst
    rfl
  · obtain rfl : (3 : Fin (2 * 4)) = c := Sum.inr.inj hst
    rfl

/-- **The colouring is forced**: every boundary-matched core odd
colouring is the pinned one, so each summand is a single term. -/
theorem cPhi_unique (φ : cSubset.CoreOddColouring 4)
    (hB : cSubset.coreOddBoundaryMatch cState φ) : φ = cPhi := by
  have hcore : ∀ g : Fin 8, g ∈ cSubset.coreFlags := fun g => by
    rw [cCoreFlags]
    exact Finset.mem_univ g
  have h4 : φ.val ⟨(4 : Fin 8), hcore 4⟩ = 0 := hB 0 0 rfl (hcore 4)
  have h5 : φ.val ⟨(5 : Fin 8), hcore 5⟩ = 1 := hB 1 1 rfl (hcore 5)
  have h6 : φ.val ⟨(6 : Fin 8), hcore 6⟩ = 2 := hB 2 2 rfl (hcore 6)
  have h7 : φ.val ⟨(7 : Fin 8), hcore 7⟩ = 3 := hB 3 3 rfl (hcore 7)
  have h0 : φ.val ⟨(0 : Fin 8), hcore 0⟩ = 0 := by
    have hp := φ.prop ⟨(0 : Fin 8), hcore 0⟩
    exact hp.symm.trans h4
  have h1 : φ.val ⟨(1 : Fin 8), hcore 1⟩ = 1 := by
    have hp := φ.prop ⟨(1 : Fin 8), hcore 1⟩
    exact hp.symm.trans h5
  have h2 : φ.val ⟨(2 : Fin 8), hcore 2⟩ = 3 := by
    have hp := φ.prop ⟨(2 : Fin 8), hcore 2⟩
    exact hp.symm.trans h7
  have h3 : φ.val ⟨(3 : Fin 8), hcore 3⟩ = 2 := by
    have hp := φ.prop ⟨(3 : Fin 8), hcore 3⟩
    exact hp.symm.trans h6
  apply Subtype.ext
  funext g
  have hval : ∀ (x : Fin 8) (hx : x ∈ cSubset.coreFlags),
      φ.val ⟨x, hx⟩ = cColour x := by
    intro x hx
    fin_cases x
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  exact hval g.val g.prop

/-! ### Two-element in-lists -/

/-- A duplicate-free list whose members are exactly two distinct
elements is one of the two orderings of that pair. -/
theorem list_pair_cases {γ : Type} {x y : γ} {l : List γ}
    (hxy : x ≠ y) (hnd : l.Nodup)
    (hmem : ∀ g, g ∈ l ↔ (g = x ∨ g = y)) :
    l = [x, y] ∨ l = [y, x] := by
  rcases l with _ | ⟨u, l₂⟩
  · have := (hmem x).mpr (Or.inl rfl)
    simp at this
  rcases l₂ with _ | ⟨w, l₃⟩
  · have hx := (hmem x).mpr (Or.inl rfl)
    have hy := (hmem y).mpr (Or.inr rfl)
    simp only [List.mem_singleton] at hx hy
    exact absurd (hx.trans hy.symm) hxy
  rcases l₃ with _ | ⟨r, l₄⟩
  · have hu := (hmem u).mp (by simp)
    have hw := (hmem w).mp (by simp)
    have hne : u ≠ w := by
      simp only [List.nodup_cons, List.mem_singleton] at hnd
      exact fun he => hnd.1 (by simp [he])
    rcases hu with rfl | rfl
    · rcases hw with rfl | rfl
      · exact absurd rfl hne
      · exact Or.inl rfl
    · rcases hw with rfl | rfl
      · exact Or.inr rfl
      · exact absurd rfl hne
  · exfalso
    have hu := (hmem u).mp (by simp)
    have hw := (hmem w).mp (by simp)
    have hr := (hmem r).mp (by simp)
    simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
    obtain ⟨⟨huw, hur, -⟩, ⟨hwr, -⟩, -⟩ := hnd
    rcases hu with rfl | rfl <;> rcases hw with rfl | rfl <;>
      rcases hr with rfl | rfl <;> simp_all

/-- The in-flag list at the vertex, up to order, read off an
orientation's `isOut` table: the two flags oriented inwards. -/
theorem cRelIn_pair {κ : cSubset.RelTransitionSystem}
    (o : κ.Orientation) {i0 i1 i2 i3 : Bool}
    (h0 : o.isOut 0 = i0) (h1 : o.isOut 1 = i1)
    (h2 : o.isOut 2 = i2) (h3 : o.isOut 3 = i3)
    (g₁ g₂ : Fin 8) (hne : g₁ ≠ g₂)
    (hpat : ∀ g : Fin 8,
      ((g = 0 ∧ i0 = false) ∨ (g = 1 ∧ i1 = false) ∨
        (g = 2 ∧ i2 = false) ∨ (g = 3 ∧ i3 = false)) ↔
        (g = g₁ ∨ g = g₂)) :
    cSubset.relInFlagsAt o cV = [g₁, g₂] ∨
      cSubset.relInFlagsAt o cV = [g₂, g₁] := by
  refine list_pair_cases hne (relInFlagsAt_nodup o cV) (fun g => ?_)
  rw [mem_relInFlagsAt_iff, ← hpat g]
  constructor
  · rintro ⟨-, hat, hout⟩
    fin_cases g
    · exact Or.inl ⟨rfl, h0.symm.trans hout⟩
    · exact Or.inr (Or.inl ⟨rfl, h1.symm.trans hout⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, h2.symm.trans hout⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, h3.symm.trans hout⟩))
    · exact absurd hat (by decide)
    · exact absurd hat (by decide)
    · exact absurd hat (by decide)
    · exact absurd hat (by decide)
  · rintro (⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩)
    · exact ⟨Finset.mem_univ _, rfl, h0.trans hb⟩
    · exact ⟨Finset.mem_univ _, rfl, h1.trans hb⟩
    · exact ⟨Finset.mem_univ _, rfl, h2.trans hb⟩
    · exact ⟨Finset.mem_univ _, rfl, h3.trans hb⟩

/-! ### The summand over a two-element in-list -/

/-- The vertex sign over a two-element in-list: the product of the
two entry partners' `oddPartnerSign`s. -/
theorem cCoreOddSignAt (κ : cSubset.RelTransitionSystem)
    (o : κ.Orientation) (g₁ g₂ : Fin 8)
    (hglist : cSubset.relInFlagsAt o cV = [g₁, g₂]) :
    cSubset.coreOddSignAt o cPhi cV =
      oddPartnerSign 4 (cColour (κ.match_ g₁)) *
        oddPartnerSign 4 (cColour (κ.match_ g₂)) := by
  unfold EdgeSubset.coreOddSignAt
  rw [List.attachWith_congr hglist]
  simp only [List.attachWith_cons, List.attachWith_nil,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    mul_one]
  rfl

/-- The vertex odd list over a two-element in-list: each in-flag's
colour followed by its match's partner colour. -/
theorem cCoreOddListAt (κ : cSubset.RelTransitionSystem)
    (o : κ.Orientation) (g₁ g₂ : Fin 8)
    (hglist : cSubset.relInFlagsAt o cV = [g₁, g₂]) :
    cSubset.coreOddListAt o cPhi cV =
      [cColour g₁, oddPartner 4 (cColour (κ.match_ g₁)),
        cColour g₂, oddPartner 4 (cColour (κ.match_ g₂))] := by
  unfold EdgeSubset.coreOddListAt
  rw [List.attachWith_congr hglist]
  simp only [List.attachWith_cons, List.attachWith_nil,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rfl

open Classical in
/-- **The summand over a two-element in-list**: with the colouring
forced and the through product trivial, the whole summand is the
single vertex factor. -/
theorem cThroughSummand (κ : cSubset.RelTransitionSystem)
    (o : κ.Orientation) (g₁ g₂ : Fin 8)
    (hglist : cSubset.relInFlagsAt o cV = [g₁, g₂]) :
    cSubset.throughSummand cFunctional cState cBnd o 0 =
      ((oddPartnerSign 4 (cColour (κ.match_ g₁)) *
          oddPartnerSign 4 (cColour (κ.match_ g₂)) : ℤ) : ℂ) *
        MixedFunctional.evalOdd cFunctional
          (cSubset.evenColoursAt cPsi cV)
          [cColour g₁, oddPartner 4 (cColour (κ.match_ g₁)),
            cColour g₂, oddPartner 4 (cColour (κ.match_ g₂))] := by
  unfold EdgeSubset.throughSummand
  rw [cThroughProduct, pow_zero, one_mul, one_mul]
  rw [Fintype.sum_subsingleton _ cPsi]
  rw [if_pos cEvenMatch]
  have hzero : ∀ φ : cSubset.CoreOddColouring 4, φ ≠ cPhi →
      (if cSubset.coreOddBoundaryMatch cState φ then
        ∏ v : cFragment.Vertex,
          ((cSubset.coreOddSignAt o φ v : ℂ) *
            MixedFunctional.evalOdd cFunctional
              (cSubset.evenColoursAt cPsi v)
              (cSubset.coreOddListAt o φ v))
      else 0) = 0 := by
    intro φ hφ
    rcases Classical.em (cSubset.coreOddBoundaryMatch cState φ) with
      hb | hb
    · exact absurd (cPhi_unique φ hb) hφ
    · rw [if_neg hb]
  rw [Fintype.sum_eq_single cPhi hzero]
  rw [if_pos cOddMatch]
  rw [Fintype.prod_subsingleton _ cV]
  rw [cCoreOddSignAt κ o g₁ g₂ hglist, cCoreOddListAt κ o g₁ g₂
    hglist]

/-! ### Open circuit counts -/

/-- No system on this instance has periodic flags: every flag lies
on a boundary-to-boundary chain. -/
theorem cPeriodic_empty (κ : cSubset.RelTransitionSystem) :
    κ.periodicFlags = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro f hf
  obtain ⟨hint, n, hn1, hcont, -⟩ := κ.mem_periodicFlags.mp hf
  have h0 := hcont 0 (by omega)
  rw [iterWalk_zero] at h0
  rcases cInternal_cases hint with rfl | rfl | rfl | rfl <;>
    · rcases cInternal_cases h0 with h | h | h | h <;>
        exact absurd h (by decide)

/-- Pointwise form of `cPeriodic_empty`. -/
theorem cNot_periodic (κ : cSubset.RelTransitionSystem)
    (f : Fin 8) : ¬ κ.PeriodicFlag f := fun hper =>
  Finset.notMem_empty f
    (cPeriodic_empty κ ▸ κ.mem_periodicFlags.mpr hper)

open Classical in
/-- Every system on this instance has open circuit count `0`, so
the original and repaired summands are compared at the same loop
weight. -/
theorem cCount_zero (κ : cSubset.RelTransitionSystem) :
    κ.openCircuitCount = 0 := by
  have hemp : IsEmpty {f : cFragment.Flag // f ∈ κ.periodicFlags} :=
    ⟨fun x => cNot_periodic κ x.val (κ.mem_periodicFlags.mp x.prop)⟩
  have h1 : κ.walkPermPeriodic = 1 := Equiv.ext (fun x => hemp.elim x)
  unfold RelTransitionSystem.openCircuitCount
  rw [h1, Equiv.Perm.cycleType_one, Multiset.card_zero]
  have h2 : ∀ (inst : Fintype (Function.fixedPoints
      (1 : Equiv.Perm {f : cFragment.Flag // f ∈ κ.periodicFlags}))),
      @Fintype.card _ inst = 0 := fun inst =>
    (@Fintype.card_eq_zero_iff _ inst).mpr
      ⟨fun x => hemp.elim x.val⟩
  rw [h2 _]

/-! ### Path matchings and chord-crossing counts -/

/-- Path-match evaluation along a one-internal-step chain: enter at
`β`, cross to `x`, match, leave at `g`. -/
theorem cPathMatch_eval (κ : cSubset.RelTransitionSystem)
    {β x g : Fin 8} (hβ : β ∈ cSubset.boundaryFlags)
    (h1 : cFragment.pairing β = x)
    (hx : x ∈ cSubset.internalFlags)
    (h2 : cFragment.pairing (κ.match_ x) = g)
    (hg : g ∈ cSubset.boundaryFlags) :
    κ.pathMatch β hβ = g := by
  have hcont : ∀ t, t < 1 →
      cFragment.pairing (iterWalk κ β t) ∈ cSubset.internalFlags := by
    intro t ht
    obtain rfl : t = 0 := by omega
    rw [iterWalk_zero, h1]
    exact hx
  have hw1 : iterWalk κ β 1 = κ.match_ x := by
    rw [iterWalk_succ, iterWalk_zero, h1]
  have hterm : cFragment.pairing (iterWalk κ β 1) ∈
      cSubset.boundaryFlags := by
    rw [hw1, h2]
    exact hg
  have hpm := pathMatch_eq_of_chain κ hβ hcont hterm
  rw [hpm, hw1, h2]

/-- The original system's chain from `4` ends at `5`. -/
theorem cPM_4 (h : (4 : Fin 8) ∈ cSubset.boundaryFlags) :
    cKappa.pathMatch 4 h = 5 :=
  cPathMatch_eval cKappa (x := 0) h rfl (cMem_internal (Or.inl rfl))
    rfl (cMem_boundary 1 rfl)

/-- The original system's chain from `5` ends at `4`. -/
theorem cPM_5 (h : (5 : Fin 8) ∈ cSubset.boundaryFlags) :
    cKappa.pathMatch 5 h = 4 :=
  cPathMatch_eval cKappa (x := 1) h rfl
    (cMem_internal (Or.inr (Or.inl rfl))) rfl (cMem_boundary 0 rfl)

/-- The original system's chain from `6` ends at `7`. -/
theorem cPM_6 (h : (6 : Fin 8) ∈ cSubset.boundaryFlags) :
    cKappa.pathMatch 6 h = 7 :=
  cPathMatch_eval cKappa (x := 3) h rfl
    (cMem_internal (Or.inr (Or.inr (Or.inr rfl)))) rfl
    (cMem_boundary 3 rfl)

/-- The original system's chain from `7` ends at `6`. -/
theorem cPM_7 (h : (7 : Fin 8) ∈ cSubset.boundaryFlags) :
    cKappa.pathMatch 7 h = 6 :=
  cPathMatch_eval cKappa (x := 2) h rfl
    (cMem_internal (Or.inr (Or.inr (Or.inl rfl)))) rfl
    (cMem_boundary 2 rfl)

/-- The repaired system re-pairs the boundary: its chain from `4`
ends at `7`, not `5`. -/
theorem cPM'_4 (h : (4 : Fin 8) ∈ cSubset.boundaryFlags) :
    (cKappa.repair 0 1 2 3 cV cSquare).pathMatch 4 h = 7 :=
  cPathMatch_eval _ (x := 0) h rfl (cMem_internal (Or.inl rfl))
    (by rw [RelTransitionSystem.repair_match_a cSquare]; rfl)
    (cMem_boundary 3 rfl)

/-- The repaired system's chain from `5` ends at `6`. -/
theorem cPM'_5 (h : (5 : Fin 8) ∈ cSubset.boundaryFlags) :
    (cKappa.repair 0 1 2 3 cV cSquare).pathMatch 5 h = 6 :=
  cPathMatch_eval _ (x := 1) h rfl
    (cMem_internal (Or.inr (Or.inl rfl)))
    (by rw [RelTransitionSystem.repair_match_b cSquare]; rfl)
    (cMem_boundary 2 rfl)

/-- The repaired system's chain from `6` ends at `5`. -/
theorem cPM'_6 (h : (6 : Fin 8) ∈ cSubset.boundaryFlags) :
    (cKappa.repair 0 1 2 3 cV cSquare).pathMatch 6 h = 5 :=
  cPathMatch_eval _ (x := 3) h rfl
    (cMem_internal (Or.inr (Or.inr (Or.inr rfl))))
    (by rw [RelTransitionSystem.repair_match_d cSquare]; rfl)
    (cMem_boundary 1 rfl)

/-- The repaired system's chain from `7` ends at `4`. -/
theorem cPM'_7 (h : (7 : Fin 8) ∈ cSubset.boundaryFlags) :
    (cKappa.repair 0 1 2 3 cV cSquare).pathMatch 7 h = 4 :=
  cPathMatch_eval _ (x := 2) h rfl
    (cMem_internal (Or.inr (Or.inr (Or.inl rfl))))
    (by rw [RelTransitionSystem.repair_match_c cSquare]; rfl)
    (cMem_boundary 0 rfl)

/-- Reading a chord's two labels off a chain: the labels recorded
by `attach` at the chain's ends are the chord's. -/
theorem cChord_label {κ : cSubset.RelTransitionSystem}
    {x g : Fin 8} {hx : x ∈ cSubset.boundaryFlags} {i j : Fin 4}
    (hpm : κ.pathMatch x hx = g)
    (h1 : cFragment.attach x = Sum.inr i)
    (h2 : cFragment.attach (κ.pathMatch x hx) = Sum.inr j)
    {i0 j0 : Fin 4}
    (hxa : cFragment.attach x = Sum.inr i0)
    (hga : cFragment.attach g = Sum.inr j0) :
    i = i0 ∧ j = j0 := by
  rw [h1] at hxa
  rw [hpm, hga] at h2
  exact ⟨Sum.inr.inj hxa, (Sum.inr.inj h2).symm⟩

open Classical in
/-- A system whose chords all join adjacent labels has no
interleaving pair, hence crossing count `0`. -/
theorem cChord_empty (κ : cSubset.RelTransitionSystem)
    (hpair : ∀ (x : Fin 8) (hx : x ∈ cSubset.boundaryFlags)
      (i j : Fin 4), cFragment.attach x = Sum.inr i →
      cFragment.attach (κ.pathMatch x hx) = Sum.inr j →
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨
        (i = 3 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) :
    chordCrossingCount κ = 0 := by
  unfold chordCrossingCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨⟨x, hx⟩, ⟨x', hx'⟩⟩ -
  rintro ⟨i, j, i', j', ha1, ha2, ha3, ha4, h5, h6, h7, h8, h9⟩
  have hp := hpair x hx i j ha1 ha2
  have hp' := hpair x' hx' i' j' ha3 ha4
  rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    rcases hp' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;>
    revert h5 h6 h7 h8 h9 <;> decide

open Classical in
/-- The original system's chords `(0,1)` and `(2,3)` are disjoint:
crossing count `0`. -/
theorem cChord_kappa : chordCrossingCount cKappa = 0 := by
  refine cChord_empty cKappa ?_
  intro x hx i j h1 h2
  rcases cBoundary_cases hx with rfl | rfl | rfl | rfl
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM_4 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM_5 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM_6 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM_7 hx) h1 h2 rfl rfl
    tauto

open Classical in
/-- The repaired system's chords `(0,3)` and `(1,2)` nest:
crossing count `0` as well. -/
theorem cChord_repair :
    chordCrossingCount (cKappa.repair 0 1 2 3 cV cSquare) = 0 := by
  refine cChord_empty _ ?_
  intro x hx i j h1 h2
  rcases cBoundary_cases hx with rfl | rfl | rfl | rfl
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM'_4 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM'_5 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM'_6 hx) h1 h2 rfl rfl
    tauto
  · obtain ⟨rfl, rfl⟩ := cChord_label (cPM'_7 hx) h1 h2 rfl rfl
    tauto

/-- The original path sign is `1`. -/
theorem cPathSign_kappa : pathSign cKappa = 1 := by
  unfold EdgeSubset.pathSign
  rw [cChord_kappa, pow_zero]

/-- The repaired path sign is `1` too — so the factor the two
summands differ by is *not* the chord sign. -/
theorem cPathSign_repair :
    pathSign (cKappa.repair 0 1 2 3 cV cSquare) = 1 := by
  unfold EdgeSubset.pathSign
  rw [cChord_repair, pow_zero]

/-! ### The two summand values -/

open Classical in
/-- **The original summand is `−1`.** -/
theorem cSummand_O :
    cSubset.throughSummand cFunctional cState cBnd cO 0 = -1 := by
  rcases cRelIn_pair (κ := cKappa) cO rfl rfl rfl rfl 0 3 (by decide)
      (by decide) with h | h
  · rw [cThroughSummand cKappa cO 0 3 h,
      show cKappa.match_ 0 = 1 from rfl,
      show cKappa.match_ 3 = 2 from rfl,
      show (oddPartnerSign 4 (cColour 1) *
        oddPartnerSign 4 (cColour 2) : ℤ) = 1 from by decide,
      show [cColour 0, oddPartner 4 (cColour 1), cColour 3,
        oddPartner 4 (cColour 2)] =
        ([0, 5, 2, 7] : List (Fin (2 * 4))) from by decide,
      MixedFunctional.evalOdd,
      if_pos (by decide : ([0, 5, 2, 7] : List (Fin (2 * 4))).Nodup),
      show sortSign ([0, 5, 2, 7] : List (Fin (2 * 4))) = -1 from
        by decide,
      show ([0, 5, 2, 7] : List (Fin (2 * 4))).toFinset =
        ({0, 5, 2, 7} : Finset (Fin (2 * 4))) from by decide,
      cFunctional_apply, if_pos rfl]
    norm_num
  · rw [cThroughSummand cKappa cO 3 0 h,
      show cKappa.match_ 0 = 1 from rfl,
      show cKappa.match_ 3 = 2 from rfl,
      show (oddPartnerSign 4 (cColour 2) *
        oddPartnerSign 4 (cColour 1) : ℤ) = 1 from by decide,
      show [cColour 3, oddPartner 4 (cColour 2), cColour 0,
        oddPartner 4 (cColour 1)] =
        ([2, 7, 0, 5] : List (Fin (2 * 4))) from by decide,
      MixedFunctional.evalOdd,
      if_pos (by decide : ([2, 7, 0, 5] : List (Fin (2 * 4))).Nodup),
      show sortSign ([2, 7, 0, 5] : List (Fin (2 * 4))) = -1 from
        by decide,
      show ([2, 7, 0, 5] : List (Fin (2 * 4))).toFinset =
        ({0, 5, 2, 7} : Finset (Fin (2 * 4))) from by decide,
      cFunctional_apply, if_pos rfl]
    norm_num

end TransposeVerify

end RS
