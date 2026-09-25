/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.LLL.Asymmetric
public import LeanPool.BlockSpectralSensitivity.Construction.Basic
public import LeanPool.BlockSpectralSensitivity.Numerics.Binomial

/-!
# Internal obstructions

The bad events of the local lemma are *not* the global proximity events "some point of
`C_h` is close to many other certificates": those depend on gate labels with an endpoint
outside the support, and so have no local dependency graph (Section 7).

Instead we keep only the necessary conditions that mention arcs internal to the support.
For a support `S`, an owner `h ∈ S` and a radius `ell`, a *centered internal obstruction*
is a family of putative zero sets `Z j ⊆ Fin r` — the coordinates of block `j` at which a
hypothetical point is `0` — such that `Z h = ∅`, every gate out of `h` lands in its target
zero set, and every non-owner spends at most `ell` on its own zeros plus its internal
misses.  This is `IntObstruction`, and `intObstruction_of_close` is the implication of
Section 7: a genuine proximity configuration produces one.  The converse is neither
claimed nor needed.

Section 8 analyses radius one.  Every non-owner has already spent its whole budget on its
unique conflict with the owner, so the set of non-owners beating the owner has at most one
element, leaving exactly two patterns on a five-element support: `Type A`, where the owner
dominates the other four, and `Type B`, where a single vertex `a` beats the owner and both
beat the remaining three.  In either case all six arcs among the non-owners are forced to
reproduce the owner's gate label in their head block, an event of probability `r ^ (-6)`.

Section 9 consolidates radius two on a nine-element support into the single event
`radiusTwoEvent` of probability at most `radiusTwoConst / r ^ 20`.

The lemmas below take an `IsTournament` hypothesis rather than an `IsDRTournamentWith`
instance: none of them needs double regularity.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

public section

namespace BSLambda

namespace LLL

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {r : ℕ}

/-- The arc variables: an independent uniform gate label for each ordered pair. -/
abbrev GateCfg (ι : Type*) (r : ℕ) : Type _ := ι × ι → Fin r

/-- Read a configuration of the product space as a gate labelling. -/
def toGamma : GateCfg ι r → ι → ι → Fin r := Function.curry

omit [Fintype ι] in
/-- Supports meeting in at most one vertex share no arc variable (Section 7).  This is what
makes the dependency graph of Section 10 — adjacency iff the supports share at least two
vertices — a valid one.

The variables of a support `S` are its *off-diagonal* pairs: no event ever reads a loop
variable `ω (v, v)`, since every arc is irreflexive and every conditioned owner gate `(h, j)`
has `j` a non-owner, and leaving the diagonal out is exactly what makes this true. -/
theorem disjoint_offDiag_of_card_inter_le_one {S T : Finset ι} (h : (S ∩ T).card ≤ 1) :
    Disjoint S.offDiag T.offDiag := by
  simp only [Finset.disjoint_left, Finset.mem_offDiag]
  rintro p ⟨hS1, hS2, hne⟩ ⟨hT1, hT2, -⟩
  exact hne (Finset.card_le_one.mp h _ (Finset.mem_inter.2 ⟨hS1, hT1⟩) _
    (Finset.mem_inter.2 ⟨hS2, hT2⟩))

/-- **The owner gates of `i` into `T`**: the arc variables `(i, j)` for `j ∈ T`.  Both
probability estimates condition on this family and pin the remaining internal arc labels to
values read off it. -/
def ownerGates (i : ι) (T : Finset ι) : Finset (ι × ι) := {i} ×ˢ T

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_ownerGates {i : ι} {T : Finset ι} {p : ι × ι} :
    p ∈ ownerGates i T ↔ p.1 = i ∧ p.2 ∈ T := by
  rw [ownerGates, Finset.mem_product, Finset.mem_singleton]

/-! ### The arcs inside a vertex set -/

/-- **The arcs internal to `T`**: the ordered pairs of distinct vertices of `T` carrying a
forward arc.  These are exactly the variables constrained by the radius-one flag event of
Section 8.1 (with `T` the non-owners of the flag) and by the radius-two branches of
Section 9 (with `T` the non-owners of the support). -/
def arcSet (Arc : ι → ι → Bool) (T : Finset ι) : Finset (ι × ι) :=
  T.offDiag.filter fun p => Arc p.1 p.2 = true

section ArcSet

omit [Fintype ι]
variable {Arc : ι → ι → Bool} {T : Finset ι} {p : ι × ι}

omit [DecidableEq ι] in
@[simp]
theorem mem_arcSet : p ∈ arcSet Arc T ↔ (p.1 ∈ T ∧ p.2 ∈ T ∧ p.1 ≠ p.2) ∧ Arc p.1 p.2 := by
  simp [arcSet, Finset.mem_offDiag]

omit [DecidableEq ι] in
/-- Swapping the two entries is a bijection from the arcs of `T` to the reversed arcs. -/
theorem card_arcSet_swap (Arc : ι → ι → Bool) (T : Finset ι) :
    (arcSet (fun a b => Arc b a) T).card = (arcSet Arc T).card := by
  classical
  refine Finset.card_bij (fun p _ ↦ Prod.swap p) (fun p hp ↦ ?_) (fun p _ q _ hpq ↦ ?_)
    fun p hp ↦ ⟨Prod.swap p, ?_, by simp⟩
  · exact mem_arcSet.2 ⟨⟨(mem_arcSet.1 hp).1.2.1, (mem_arcSet.1 hp).1.1,
      (mem_arcSet.1 hp).1.2.2.symm⟩, (mem_arcSet.1 hp).2⟩
  · simpa using congrArg Prod.swap hpq
  · exact mem_arcSet.2 ⟨⟨(mem_arcSet.1 hp).1.2.1, (mem_arcSet.1 hp).1.1,
      (mem_arcSet.1 hp).1.2.2.symm⟩, (mem_arcSet.1 hp).2⟩

variable (hT : IsTournament Arc)
include hT

/-- In a tournament the arcs of `T` and the reversed arcs of `T` together exhaust the
off-diagonal pairs of `T`. -/
theorem arcSet_union_arcSet_swap (T : Finset ι) :
    arcSet Arc T ∪ arcSet (fun a b => Arc b a) T = T.offDiag := by
  ext p
  simp only [Finset.mem_union, mem_arcSet, Finset.mem_offDiag]
  refine ⟨fun h ↦ h.elim (·.1) (·.1), fun h ↦ ?_⟩
  cases hA : Arc p.1 p.2
  · exact Or.inr ⟨h, hT.arc_of_not_arc h.2.2.symm hA⟩
  · exact Or.inl ⟨h, rfl⟩

omit [DecidableEq ι] in
/-- A pair cannot carry an arc in both directions. -/
theorem disjoint_arcSet_arcSet_swap (T : Finset ι) :
    Disjoint (arcSet Arc T) (arcSet (fun a b => Arc b a) T) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  exact hT.arc_asymm (mem_arcSet.1 hp).2 (mem_arcSet.1 hp').2

omit [DecidableEq ι] in
/-- A tournament on `T` has exactly `C(|T|, 2)` internal arcs: six for the four non-owners
of a radius-one flag, and `Q = 28` for the eight non-owners of Section 9. -/
theorem card_arcSet (T : Finset ι) : (arcSet Arc T).card = Nat.choose T.card 2 := by
  classical
  have hcard := congrArg Finset.card (arcSet_union_arcSet_swap hT T)
  rw [Finset.card_union_of_disjoint (disjoint_arcSet_arcSet_swap hT T),
    card_arcSet_swap Arc T, Finset.offDiag_card] at hcard
  have hmul : T.card * (T.card - 1) = T.card * T.card - T.card := by
    rw [Nat.mul_sub, Nat.mul_one]
  rw [Nat.choose_two_right, hmul]
  generalize T.card * T.card - T.card = N at hcard ⊢
  omega

end ArcSet

/-! ### Internal obstructions (Section 7) -/

/-- **The misses of `i` inside `T`** (Section 7): the out-neighbours `j ∈ T` of `i` whose
gate label `γ i j` avoids the putative zero set `Z j`, so that the gate literal of the arc
`i → j` is violated.  A *miss* costs `i` one unit of its budget. -/
def missSet (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r)) (T : Finset ι)
    (i : ι) : Finset ι :=
  T.filter fun j => Arc i j = true ∧ γ i j ∉ Z j

section MissSet

omit [Fintype ι] [DecidableEq ι]
variable {Arc : ι → ι → Bool} {γ γ' : ι → ι → Fin r} {Z : ι → Finset (Fin r)}
  {T T' S : Finset ι} {i j : ι}

@[simp]
theorem mem_missSet : j ∈ missSet Arc γ Z T i ↔ j ∈ T ∧ Arc i j ∧ γ i j ∉ Z j := by
  simp [missSet]

@[gcongr]
theorem missSet_subset_missSet (hT : T ⊆ T') : missSet Arc γ Z T i ⊆ missSet Arc γ Z T' i :=
  Finset.filter_subset_filter _ hT

/-- The misses out of `i` only read gate labels of arcs with both endpoints in `S`, so they
are unchanged by a relabelling that fixes those arcs. -/
theorem missSet_congr (hT : IsTournament Arc) (hi : i ∈ S) (Z : ι → Finset (Fin r))
    (hagree : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → γ a b = γ' a b) :
    missSet Arc γ Z S i = missSet Arc γ' Z S i := by
  refine Finset.filter_congr fun j hj ↦ ?_
  by_cases harc : Arc i j = true
  · rw [hagree i hi j hj (hT.ne_of_arc harc)]
  · simp [harc]

end MissSet

/-- **A centered internal obstruction of radius `ell`** (Section 7).  The sets `Z j` are
the putative zero coordinates of a hypothetical point in block `j`.  `Z h = ∅` because a
point of `C_h` is `1` throughout its own block; each gate out of the owner is forced into
its target zero set; and every other index of the support spends at most `ell` on its own
zeros together with its internal misses. -/
def IntObstruction (Arc : ι → ι → Bool) (ell : ℕ) (S : Finset ι) (h : ι)
    (γ : ι → ι → Fin r) : Prop :=
  ∃ Z : ι → Finset (Fin r),
    Z h = ∅ ∧
    (∀ j ∈ S, Arc h j → γ h j ∈ Z j) ∧
    (∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ ell)

omit [Fintype ι] [DecidableEq ι] in
/-- A centered internal obstruction only reads gate labels of arcs with both endpoints in
its support, so it transports along any relabelling that fixes those arcs. -/
theorem intObstruction_congr {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {ell : ℕ} {S : Finset ι} {h : ι} (hh : h ∈ S) {γ γ' : ι → ι → Fin r}
    (hagree : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → γ a b = γ' a b)
    (hobs : IntObstruction Arc ell S h γ) : IntObstruction Arc ell S h γ' := by
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  refine ⟨Z, hZh, fun j hj harc ↦ ?_, fun i hi hin ↦ ?_⟩
  · rw [← hagree h hh j hj (hT.ne_of_arc harc)]
    exact hgate j hj harc
  · rw [← missSet_congr hT hi Z hagree]
    exact hbud i hi hin

/-- The zero set of an input inside a block. -/
def zeroSet (x : Input (Construction.Coord ι r)) (i : ι) : Finset (Fin r) :=
  Finset.univ.filter fun k => x (i, k) = false

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem mem_zeroSet {x : Input (Construction.Coord ι r)} {i : ι} {k : Fin r} :
    k ∈ zeroSet x i ↔ x (i, k) = false := by
  simp [zeroSet]

omit [Fintype ι] in
/-- The zero set of a point of `C_h` in the owner's own block is empty. -/
theorem zeroSet_owner_eq_empty {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {h : ι}
    {x : Input (Construction.Coord ι r)} (hx : (Construction.cert Arc γ h).Sat x) :
    zeroSet x h = ∅ := by
  rw [Construction.sat_cert_iff] at hx
  ext k
  simpa [zeroSet] using hx.1 k

/-- The literals of `P_i` violated by `x`, spelled out: either a coordinate of the owner
block `B_i` where `x` is `0`, or the gate coordinate of an outgoing arc where `x` is `1`. -/
theorem mem_violSet_cert {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {i : ι}
    {x : Input (Construction.Coord ι r)} {v : Construction.Coord ι r} :
    v ∈ (Construction.cert Arc γ i).violSet x ↔
      (v.1 = i ∧ x v = false) ∨
        (v.1 ≠ i ∧ Arc i v.1 = true ∧ v.2 = γ i v.1 ∧ x v = true) := by
  rw [PartialAssign.mem_violSet, Construction.cert_apply]
  by_cases h1 : v.1 = i
  · rw [ite_eq_left h1]
    cases hx : x v <;> simp [h1]
  · rw [ite_eq_right h1]
    by_cases h2 : Arc i v.1 = true ∧ v.2 = γ i v.1
    · rw [ite_eq_left h2]
      cases hx : x v <;> simp [h1, h2.1, h2.2]
    · rw [ite_eq_right h2]
      simp only [ne_eq, not_true_eq_false, false_and]
      refine ⟨False.elim, ?_⟩
      rintro (⟨he, -⟩ | ⟨-, ha, hb, -⟩)
      · exact absurd he h1
      · exact absurd ⟨ha, hb⟩ h2

/-- The violated literals of `P_i` split into the zeros of `x` in the owner block and the
outgoing gates whose target coordinate `x` fails to zero out. -/
theorem violSet_cert_eq (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    (Construction.cert Arc γ i).violSet x =
      (zeroSet x i).image (fun k => ((i, k) : Construction.Coord ι r)) ∪
        (missSet Arc γ (zeroSet x) Finset.univ i).image (Construction.gateCoord γ i) := by
  ext v
  rw [mem_violSet_cert, Finset.mem_union]
  simp only [Finset.mem_image, mem_zeroSet, mem_missSet, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩)
    · refine Or.inl ⟨v.2, ?_, ?_⟩
      · rw [← h1]
        exact h2
      · rw [← h1]
    · refine Or.inr ⟨v.1, ⟨h2, ?_⟩, Construction.gateCoord_fst_eq_self h3⟩
      rw [← h3, h4]
      simp
  · rintro (⟨k, hk, rfl⟩ | ⟨j, ⟨hj1, hj2⟩, rfl⟩)
    · exact Or.inl ⟨rfl, hk⟩
    · refine Or.inr ⟨hT.ne_of_arc' hj1, hj1, rfl, ?_⟩
      simpa [Construction.gateCoord] using hj2

/-- The two halves of the violation set are disjoint: both halves shrink to the two halves
of `Construction.disjoint_block_image_gateCoord`, the owner block and the image of the full
out-neighbourhood. -/
theorem disjoint_zeros_image_gate_image (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    Disjoint ((zeroSet x i).image (fun k => ((i, k) : Construction.Coord ι r)))
      ((missSet Arc γ (zeroSet x) Finset.univ i).image (Construction.gateCoord γ i)) := by
  refine Finset.disjoint_of_subset_left ?_ (Finset.disjoint_of_subset_right ?_
    (Construction.disjoint_block_image_gateCoord (γ := γ) (i := i) hT))
  · exact Finset.image_subset_iff.2 fun k _ ↦ Construction.mem_block.2 rfl
  · exact Finset.image_subset_image fun j hj ↦ mem_outNbrs.2 (mem_missSet.1 hj).2.1

/-- The distance from `x` to `C_i` counts the zeros of `x` in block `i` together with the
gates out of `i` that miss their target zero set. -/
theorem dist_cert_eq (Arc : ι → ι → Bool) (hT : IsTournament Arc)
    (γ : ι → ι → Fin r) (i : ι) (x : Input (Construction.Coord ι r)) :
    (Construction.cert Arc γ i).dist x =
      (zeroSet x i).card + (missSet Arc γ (zeroSet x) Finset.univ i).card := by
  rw [PartialAssign.dist_eq_card_violSet, violSet_cert_eq Arc hT γ i x,
    Finset.card_union_of_disjoint (disjoint_zeros_image_gate_image Arc hT γ i x),
    Finset.card_image_of_injective _ (Prod.mk_right_injective i),
    Finset.card_image_of_injective _ (Construction.gateCoord_injective γ i)]

/-- **Section 7**: a genuine proximity configuration yields an internal obstruction.  Only
external misses have been discarded, so the implication is valid. -/
theorem intObstruction_of_close {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} {ell : ℕ}
    {x : Input (Construction.Coord ι r)} (hx : (Construction.cert Arc γ h).Sat x)
    (hclose : ∀ i ∈ S, i ≠ h → (Construction.cert Arc γ i).dist x ≤ ell) :
    IntObstruction Arc ell S h γ := by
  refine ⟨zeroSet x, zeroSet_owner_eq_empty hx, ?_, ?_⟩
  · intro j hj hary
    have hgates := Construction.sat_cert_iff.1 hx
    exact mem_zeroSet.2 (hgates.2 j (hT.ne_of_arc' hary) hary)
  · intro i his hin
    have hdist := hclose i his hin
    rw [dist_cert_eq Arc hT γ i x] at hdist
    exact le_trans (add_le_add_right (Finset.card_le_card
      (missSet_subset_missSet (Finset.subset_univ S))) _) hdist

/-! ### Radius-one flags (Section 8) -/

/-- The data of a candidate radius-one flag on a five-element support: an owner (`owner`),
an optional second top vertex (`top`) — absent for `Type A`, present for `Type B` — and the
remaining bottom vertices (`bot`) (Section 8). -/
@[ext]
structure Flag1 (ι : Type*) [DecidableEq ι] where
  /-- The proposed owner. -/
  owner : ι
  /-- The second top vertex, for `Type B` patterns. -/
  top : Option ι
  /-- The bottom vertices. -/
  bot : Finset ι

namespace Flag1

/-- A flag *is* a triple `(owner, top, bot)`; both the `DecidableEq` and the `Fintype`
instance are transported along this equivalence.  `deriving DecidableEq` does not work here:
the derived instance builds its own decision procedure for the `Finset` field instead of
using the ambient `Finset.decidableEq`, and Lean rejects it as not definitionally equal. -/
def equivProd : Flag1 ι ≃ ι × Option ι × Finset ι where
  toFun F := (F.owner, F.top, F.bot)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : DecidableEq (Flag1 ι) := equivProd.injective.decidableEq

instance : Fintype (Flag1 ι) := .ofEquiv _ equivProd.symm

/-- The non-owners of a flag. -/
def nonOwners (F : Flag1 ι) : Finset ι :=
  match F.top with
  | none => F.bot
  | some v => insert v F.bot

/-- The five-element support of a flag. -/
def supp (F : Flag1 ι) : Finset ι := insert F.owner F.nonOwners

section Membership

omit [Fintype ι]
variable {F : Flag1 ι} {Arc : ι → ι → Bool} {a j : ι} {p : ι × ι}

theorem nonOwners_of_top_eq_none (ha : F.top = none) : F.nonOwners = F.bot := by
  rw [nonOwners, ha]

theorem nonOwners_of_top_eq_some (ha : F.top = some a) : F.nonOwners = insert a F.bot := by
  rw [nonOwners, ha]

@[simp] theorem mem_nonOwners : j ∈ F.nonOwners ↔ j ∈ F.top ∨ j ∈ F.bot := by
  cases ha : F.top with
  | none => simp [nonOwners_of_top_eq_none ha]
  | some v => simp [nonOwners_of_top_eq_some ha, eq_comm]

@[simp] theorem mem_supp : j ∈ F.supp ↔ j = F.owner ∨ j ∈ F.nonOwners := by
  simp [supp]

/-! #### Activeness -/

/-- **Activeness** of a flag (Section 8): the tournament must realise the pattern.  For
`Type A` the owner dominates four vertices; for `Type B` the second top vertex beats the
owner and both top vertices beat the three bottom ones.

Consumers should use the two unfolding lemmas `Flag1.active_iff_of_top_eq_none` and
`Flag1.active_iff_of_top_eq_some`, or the named accessors in the `Flag1.Active` namespace,
rather than unfolding this definition. -/
def Active (F : Flag1 ι) (Arc : ι → ι → Bool) : Prop :=
  F.owner ∉ F.nonOwners ∧
  match F.top with
  | none => F.bot.card = 4 ∧ ∀ j ∈ F.bot, Arc F.owner j = true
  | some v =>
    v ∉ F.bot ∧ F.bot.card = 3 ∧ Arc v F.owner = true ∧
      ∀ j ∈ F.bot, Arc F.owner j = true ∧ Arc v j = true

/-- Activeness of a `Type A` flag: the owner dominates its four bottom vertices. -/
theorem active_iff_of_top_eq_none (ha : F.top = none) :
    F.Active Arc ↔ F.owner ∉ F.bot ∧ F.bot.card = 4 ∧ ∀ j ∈ F.bot, Arc F.owner j = true := by
  rw [Active, nonOwners_of_top_eq_none ha, ha]

/-- Activeness of a `Type B` flag: the owner, the second top vertex `a` and the three bottom
vertices are distinct, `a` beats the owner, and both top vertices dominate every bottom
vertex. -/
theorem active_iff_of_top_eq_some (ha : F.top = some a) :
    F.Active Arc ↔ F.owner ≠ a ∧ F.owner ∉ F.bot ∧ a ∉ F.bot ∧ F.bot.card = 3 ∧
      Arc a F.owner = true ∧ ∀ j ∈ F.bot, Arc F.owner j = true ∧ Arc a j = true := by
  rw [Active, nonOwners_of_top_eq_some ha, ha, Finset.mem_insert, not_or, and_assoc]

namespace Active

variable (hF : F.Active Arc)
include hF

/-- The owner of an active flag is not one of its non-owners. -/
theorem owner_notMem_nonOwners : F.owner ∉ F.nonOwners := hF.1

/-- The owner of an active flag is not one of its bottom vertices. -/
theorem owner_notMem_bot : F.owner ∉ F.bot := fun hc ↦ hF.1 (mem_nonOwners.2 (Or.inr hc))

/-- An active `Type A` flag has four bottom vertices. -/
theorem card_bot_of_top_eq_none (ha : F.top = none) : F.bot.card = 4 :=
  ((active_iff_of_top_eq_none ha).1 hF).2.1

/-- An active `Type B` flag has three bottom vertices. -/
theorem card_bot_of_top_eq_some (ha : F.top = some a) : F.bot.card = 3 :=
  ((active_iff_of_top_eq_some ha).1 hF).2.2.2.1

/-- The owner of an active flag differs from its second top vertex. -/
theorem owner_ne_top (ha : F.top = some a) : F.owner ≠ a :=
  ((active_iff_of_top_eq_some ha).1 hF).1

/-- The second top vertex of an active flag is not a bottom vertex. -/
theorem top_notMem_bot (ha : F.top = some a) : a ∉ F.bot :=
  ((active_iff_of_top_eq_some ha).1 hF).2.2.1

/-- The second top vertex of an active flag beats the owner. -/
theorem arc_top_owner (ha : F.top = some a) : Arc a F.owner = true :=
  ((active_iff_of_top_eq_some ha).1 hF).2.2.2.2.1

/-- The owner of an active flag dominates every bottom vertex, in both patterns. -/
theorem arc_owner_bot (hj : j ∈ F.bot) : Arc F.owner j = true := by
  cases ha : F.top with
  | none => exact ((active_iff_of_top_eq_none ha).1 hF).2.2 j hj
  | some a => exact (((active_iff_of_top_eq_some ha).1 hF).2.2.2.2.2 j hj).1

/-- The second top vertex of an active flag dominates every bottom vertex. -/
theorem arc_top_bot (ha : F.top = some a) (hj : j ∈ F.bot) : Arc a j = true :=
  (((active_iff_of_top_eq_some ha).1 hF).2.2.2.2.2 j hj).2

/-- An active flag has exactly four non-owners. -/
theorem card_nonOwners : F.nonOwners.card = 4 := by
  cases ha : F.top with
  | none => rw [nonOwners_of_top_eq_none ha, hF.card_bot_of_top_eq_none ha]
  | some a =>
    rw [nonOwners_of_top_eq_some ha, Finset.card_insert_of_notMem (hF.top_notMem_bot ha),
      hF.card_bot_of_top_eq_some ha]

/-- An active flag has a five-element support. -/
theorem card_supp : F.supp.card = 5 := by
  rw [supp, Finset.card_insert_of_notMem hF.owner_notMem_nonOwners, hF.card_nonOwners]

end Active

end Membership

end Flag1

/-! #### The flag event (Section 8.1) -/

omit [Fintype ι] in
/-- An active flag has exactly six internal arcs among its four non-owners: `C(4, 2) = 6`. -/
theorem Flag1.Active.card_arcs {F : Flag1 ι} {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) : (arcSet Arc F.nonOwners).card = 6 := by
  rw [card_arcSet hT, hF.card_nonOwners]
  rfl

omit [Fintype ι] in
/-- Every non-owner arc of an active flag has its head in `F.bot`, so the owner's gate into
that head block is defined; and its tail is not the owner, so its label is a variable
distinct from the conditioned owner gates. -/
theorem Flag1.snd_mem_bot (F : Flag1 ι) {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) : p.2 ∈ F.bot := by
  obtain ⟨⟨hp1, hp2, -⟩, hpArc⟩ := mem_arcSet.1 hp
  have hne : p.1 ≠ p.2 := hT.ne_of_arc hpArc
  refine (Flag1.mem_nonOwners.1 hp2).resolve_left fun ha' ↦ ?_
  have ha : F.top = some p.2 := ha'
  have hb : p.1 ∈ F.bot := (Flag1.mem_nonOwners.1 hp1).resolve_left (by simp [ha, Ne.symm hne])
  rw [hT.arc_eq_not_arc hne, hF.arc_top_bot ha hb] at hpArc
  simp at hpArc

/-- **The active radius-one flag event** (Section 8.1): every internal non-owner arc
selects exactly the zero coordinate forced by the owner's gate in its head block. -/
noncomputable def flagEvent (Arc : ι → ι → Bool) (F : Flag1 ι) :
    Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω => ∀ p ∈ arcSet Arc F.nonOwners, ω p = ω (F.owner, p.2)

theorem mem_flagEvent {Arc : ι → ι → Bool} {F : Flag1 ι} {ω : GateCfg ι r} :
    ω ∈ flagEvent Arc F ↔ ∀ p ∈ arcSet Arc F.nonOwners, ω p = ω (F.owner, p.2) := by
  classical
  simp [flagEvent]

omit [Fintype ι] in
/-- Both variables read by the flag event at an internal arc are variables of its support. -/
theorem Flag1.mem_offDiag_supp {Arc : ι → ι → Bool} (hT : IsTournament Arc) {F : Flag1 ι}
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) :
    p ∈ F.supp.offDiag ∧ (F.owner, p.2) ∈ F.supp.offDiag := by
  obtain ⟨⟨hp1, hp2, -⟩, hp_arc⟩ := mem_arcSet.1 hp
  have hp2_in : p.2 ∈ F.supp := Flag1.mem_supp.2 (Or.inr hp2)
  have hh_ne : F.owner ≠ p.2 := fun heq ↦ hF.owner_notMem_nonOwners (heq ▸ hp2)
  exact ⟨Finset.mem_offDiag.2 ⟨Flag1.mem_supp.2 (Or.inr hp1), hp2_in, hT.ne_of_arc hp_arc⟩,
    Finset.mem_offDiag.2 ⟨Flag1.mem_supp.2 (Or.inl rfl), hp2_in, hh_ne⟩⟩

/-- The flag event is determined by the arc variables inside its support. -/
theorem flagEvent_determined {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    Determined (β := fun _ : ι × ι => Fin r) F.supp.offDiag
      (flagEvent (r := r) Arc F) := fun ω ω' hagree ↦ by
  simp only [mem_flagEvent]
  refine forall₂_congr fun p hp ↦ ?_
  obtain ⟨hp_in, hhead_in⟩ := Flag1.mem_offDiag_supp hT hF hp
  rw [hagree p hp_in, hagree (F.owner, p.2) hhead_in]

omit [Fintype ι] in
/-- The owner gates conditioned on in Section 8.1 are disjoint from the internal arcs, so
the two families of variables are independent. -/
theorem Flag1.disjoint_gates_arcs (F : Flag1 ι) {Arc : ι → ι → Bool} (hF : F.Active Arc) :
    Disjoint (ownerGates F.owner F.bot) (arcSet Arc F.nonOwners) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  exact hF.owner_notMem_nonOwners ((mem_ownerGates.1 hp1).1 ▸ (mem_arcSet.1 hp2).1.1)

omit [Fintype ι] in
/-- The owner gate into the head block of an internal arc is one of the conditioned
gates. -/
theorem Flag1.gate_mem_gates (F : Flag1 ι) {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (hF : F.Active Arc) {p : ι × ι} (hp : p ∈ arcSet Arc F.nonOwners) :
    (F.owner, p.2) ∈ ownerGates F.owner F.bot :=
  mem_ownerGates.2 ⟨rfl, F.snd_mem_bot (p := p) hT hF hp⟩

/-- **Section 8.1**: the flag event pins one uniform label per internal arc, each to a
single value read off the owner gates. -/
theorem pr_flagEvent_le_pow [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    pr (β := fun _ : ι × ι => Fin r) (flagEvent Arc F)
      ≤ ((1 : ℝ) / r) ^ (arcSet Arc F.nonOwners).card := by
  classical
  have key := pr_le_pow_of_pinned (β := fun _ : ι × ι ↦ Fin r)
      (G := ownerGates F.owner F.bot) (T := arcSet Arc F.nonOwners)
      (F.disjoint_gates_arcs hF) r (fun a _ ↦ Fintype.card_fin r)
      (fun c p ↦ if hp : (F.owner, p.2) ∈ ownerGates F.owner F.bot then
        {c (F.owner, p.2) hp} else Finset.univ) 1
      (by
        intro c p hp
        rw [dite_eq_left (F.gate_mem_gates hT hF hp)]
        simp)
      (E := flagEvent Arc F)
      (by
        intro ω hω p hp
        dsimp only
        rw [dite_eq_left (F.gate_mem_gates hT hF hp)]
        simp only [Finset.mem_singleton]
        exact mem_flagEvent.1 hω p hp)
  simpa using key

/-- **Section 8.1**: an active radius-one flag has probability `r ^ (-6)`.  After
conditioning on the owner gates, the six non-owner arc labels are independent and uniform,
and each is pinned to a single value. -/
theorem pr_flagEvent_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {F : Flag1 ι} (hF : F.Active Arc) :
    pr (β := fun _ : ι × ι => Fin r) (flagEvent Arc F) ≤ 1 / (r : ℝ) ^ 6 := by
  have h6 : (arcSet Arc F.nonOwners).card = 6 := hF.card_arcs hT
  have h := pr_flagEvent_le_pow (r := r) hT hF
  rw [h6] at h
  simpa [div_pow] using h

/-! #### The two radius-one patterns -/

omit [Fintype ι] [DecidableEq ι] in
/-- Under a radius-one obstruction centred at `h`, a vertex `j` dominated by `h` has its
zero set pinned to the single owner gate `γ h j`, and hence no internal miss of its own. -/
theorem intObstruction_one_of_owner_arc {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
    {S : Finset ι} {h : ι} {Z : ι → Finset (Fin r)}
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 1)
    {j : ι} (hj : j ∈ S) (hjh : j ≠ h) (harc : Arc h j = true) :
    Z j = {γ h j} ∧ ∀ k ∈ S, Arc j k = true → γ j k ∈ Z k := by
  have hmem : γ h j ∈ Z j := hgate j hj harc
  have hb := hbud j hj hjh
  have hsub : ({γ h j} : Finset (Fin r)) ⊆ Z j := Finset.singleton_subset_iff.mpr hmem
  have hpos : 1 ≤ (Z j).card := Finset.card_pos.mpr ⟨_, hmem⟩
  have hle : (Z j).card ≤ ({γ h j} : Finset (Fin r)).card := by
    simp only [Finset.card_singleton]
    omega
  refine ⟨(Finset.eq_of_subset_of_card_le hsub hle).symm, fun k hk hark ↦ ?_⟩
  have hf : missSet Arc γ Z S j = ∅ := Finset.card_eq_zero.1 (by omega)
  by_contra hcon
  exact absurd (hf ▸ mem_missSet.2 ⟨hk, hark, hcon⟩) (Finset.notMem_empty k)

omit [Fintype ι] [DecidableEq ι] in
/-- Under a radius-one obstruction centred at `h`, a vertex `j` that beats `h` already
spends its whole budget on the miss `j → h`, so `Z j = ∅` and it has no other miss. -/
theorem intObstruction_one_of_arc_to_owner {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}
    {S : Finset ι} {h : ι} (hh : h ∈ S) {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 1)
    {j : ι} (hj : j ∈ S) (hjh : j ≠ h) (harc : Arc j h = true) :
    Z j = ∅ ∧ ∀ k ∈ S, k ≠ h → Arc j k = true → γ j k ∈ Z k := by
  have hb := hbud j hj hjh
  have hhmem : h ∈ missSet Arc γ Z S j := mem_missSet.2 ⟨hh, harc, by simp [hZh]⟩
  have hpos : 1 ≤ (missSet Arc γ Z S j).card := Finset.card_pos.mpr ⟨h, hhmem⟩
  refine ⟨Finset.card_eq_zero.mp (by omega), fun k hk hkh hark ↦ ?_⟩
  by_contra hcon
  exact hkh (Finset.card_le_one.mp (by omega) k (mem_missSet.2 ⟨hk, hark, hcon⟩) h hhmem)

omit [Fintype ι] [DecidableEq ι] in
/-- **Section 8**: at most one vertex of the support beats the centre `h`; two of them
would give one a second internal miss. -/
theorem intObstruction_one_card_beats_le_one {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    (S.filter fun j => Arc j h = true).card ≤ 1 := by
  classical
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  rw [Finset.card_le_one]
  intro a hamem b hbmem
  rw [Finset.mem_filter] at hamem hbmem
  obtain ⟨haS, ha⟩ := hamem
  obtain ⟨hbS, hb⟩ := hbmem
  have hah : a ≠ h := hT.ne_of_arc ha
  have hbh : b ≠ h := hT.ne_of_arc hb
  by_contra hne
  obtain ⟨hZa, hmissa⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud haS hah ha
  obtain ⟨hZb, hmissb⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud hbS hbh hb
  cases hab : Arc a b with
  | true => exact absurd (hZb ▸ hmissa b hbS hbh hab) (Finset.notMem_empty _)
  | false =>
    have hba : Arc b a = true := hT.arc_of_not_arc (Ne.symm hne) hab
    exact absurd (hZa ▸ hmissb a haS hah hba) (Finset.notMem_empty _)

omit [Fintype ι] [DecidableEq ι] in
/-- **Section 8**: a radius-one obstruction realises exactly one of the two patterns —
either `h` dominates the whole support (Type A), or a single `a` beats `h` and the two of
them jointly dominate the rest (Type B). -/
theorem intObstruction_one_pattern {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    (∀ j ∈ S, j ≠ h → Arc h j = true) ∨
      ∃ a ∈ S, a ≠ h ∧ Arc a h = true ∧
        ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true := by
  classical
  have hU := intObstruction_one_card_beats_le_one hT hh hobs
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  by_cases hempty : (S.filter fun j ↦ Arc j h = true) = ∅
  · rw [Finset.eq_empty_iff_forall_notMem] at hempty
    exact Or.inl fun j hj hjh ↦ hT.arc_of_not_arc (Ne.symm hjh)
      (Bool.eq_false_iff.2 fun hx ↦ hempty j (Finset.mem_filter.mpr ⟨hj, hx⟩))
  · obtain ⟨a, hamem⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    obtain ⟨haS, hah⟩ := Finset.mem_filter.1 hamem
    have hahne : a ≠ h := hT.ne_of_arc hah
    refine Or.inr ⟨a, haS, hahne, hah, fun j hj hjh hja ↦ ?_⟩
    -- `j` does not beat `h`, since `a` is the unique such vertex
    have hjf : Arc j h = false := Bool.eq_false_iff.2 fun hx ↦
      hja (Finset.card_le_one.mp hU j (Finset.mem_filter.mpr ⟨hj, hx⟩) a hamem)
    have hhj : Arc h j = true := hT.arc_of_not_arc (Ne.symm hjh) hjf
    refine ⟨hhj, ?_⟩
    -- if `j` beat `a` it would be a second miss for `j`, whose budget is already spent
    by_contra hx
    rw [Bool.not_eq_true] at hx
    obtain ⟨hZa, -⟩ := intObstruction_one_of_arc_to_owner hh hZh hbud haS hahne hah
    obtain ⟨-, hnomiss⟩ := intObstruction_one_of_owner_arc hgate hbud hj hjh hhj
    exact absurd (hZa ▸ hnomiss a haS (hT.arc_of_not_arc hja hx)) (Finset.notMem_empty _)

omit [Fintype ι] [DecidableEq ι] in
/-- **Section 8**: every non-owner arc into a dominated `j` carries the owner's label,
since `Z j` is the singleton `{γ h j}`. -/
theorem intObstruction_one_gate_eq {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) {i j : ι} (hi : i ∈ S) (hj : j ∈ S)
    (hih : i ≠ h) (hjh : j ≠ h) (harc : Arc i j = true) (hhj : Arc h j = true) :
    γ i j = γ h j := by
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  obtain ⟨hZj, -⟩ := intObstruction_one_of_owner_arc hgate hbud hj hjh hhj
  have hmem : γ i j ∈ Z j := by
    cases hhi : Arc h i with
    | true => exact (intObstruction_one_of_owner_arc hgate hbud hi hih hhi).2 j hj harc
    | false =>
      exact (intObstruction_one_of_arc_to_owner hh hZh hbud hi hih
        (hT.arc_of_not_arc hih hhi)).2 j hj hjh harc
  rwa [hZj, Finset.mem_singleton] at hmem

omit [Fintype ι] in
/-- The Type A flag built from a dominating centre is active with support `S`. -/
theorem active_flag_typeA {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h : ι}
    (hh : h ∈ S) (hdom : ∀ j ∈ S, j ≠ h → Arc h j = true) :
    ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := none, bot := S.erase h } : Flag1 ι).supp = S := by
  refine ⟨(Flag1.active_iff_of_top_eq_none rfl).2 ⟨Finset.notMem_erase _ _, ?_, ?_⟩, ?_⟩
  · rw [Finset.card_erase_of_mem hh, hS]
  · intro j hj
    exact hdom j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj)
  · rw [Flag1.supp, Flag1.nonOwners_of_top_eq_none rfl]
    exact Finset.insert_erase hh

omit [Fintype ι] in
/-- The Type B flag built from a centre `h` and the unique `a` beating it is active with
support `S`. -/
theorem active_flag_typeB {Arc : ι → ι → Bool} {S : Finset ι} (hS : S.card = 5) {h a : ι}
    (hh : h ∈ S) (ha : a ∈ S) (hah : a ≠ h) (harc : Arc a h = true)
    (hdom : ∀ j ∈ S, j ≠ h → j ≠ a → Arc h j = true ∧ Arc a j = true) :
    ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).Active Arc ∧
      ({ owner := h, top := some a, bot := (S.erase h).erase a } : Flag1 ι).supp = S := by
  have haE : a ∈ S.erase h := Finset.mem_erase.mpr ⟨hah, ha⟩
  refine ⟨(Flag1.active_iff_of_top_eq_some rfl).2
      ⟨Ne.symm hah, fun hc ↦ Finset.notMem_erase h S (Finset.mem_of_mem_erase hc),
        Finset.notMem_erase _ _, ?_, harc, ?_⟩, ?_⟩
  · rw [Finset.card_erase_of_mem haE, Finset.card_erase_of_mem hh, hS]
  · intro j hj
    have hj' := Finset.mem_of_mem_erase hj
    exact hdom j (Finset.mem_of_mem_erase hj') (Finset.ne_of_mem_erase hj')
      (Finset.ne_of_mem_erase hj)
  · rw [Flag1.supp, Flag1.nonOwners_of_top_eq_some rfl, Finset.insert_erase haE,
      Finset.insert_erase hh]

omit [Fintype ι] in
/-- **Section 8**: all internal arcs of the flag produced from a radius-one obstruction
carry the owner's gate label. -/
theorem gate_eq_of_active_of_intObstruction {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) {F : Flag1 ι} (hF : F.Active Arc)
    (hsupp : F.supp = S) (hFh : F.owner = h) :
    ∀ p ∈ arcSet Arc F.nonOwners, γ p.1 p.2 = γ h p.2 := by
  intro p hp
  have hp2bot : p.2 ∈ F.bot := F.snd_mem_bot hT hF hp
  obtain ⟨⟨hp1, hp2, -⟩, hparc⟩ := mem_arcSet.1 hp
  have hsub : F.nonOwners ⊆ S := fun x hx ↦ hsupp ▸ Flag1.mem_supp.2 (Or.inr hx)
  have hp1h : p.1 ≠ h := by
    rintro rfl
    exact hF.owner_notMem_nonOwners (hFh ▸ hp1)
  have hp2h : p.2 ≠ h := by
    rintro rfl
    exact hF.owner_notMem_nonOwners (hFh ▸ hp2)
  have hhp2 : Arc h p.2 = true := hFh ▸ hF.arc_owner_bot hp2bot
  exact intObstruction_one_gate_eq hT hh hobs (hsub hp1) (hsub hp2) hp1h hp2h hparc hhp2

omit [Fintype ι] in
/-- **Section 8**: on a five-element support a radius-one internal obstruction forces one
of the two patterns.  If `h → j` then `|Z j| = 1` and `j` can have no internal miss; if
`j → h` then the arc `j → h` is automatically a miss, so `Z j = ∅` and again `j` has no
other miss.  Hence any two vertices beating `h` would give one of them a second miss, so at
most one vertex beats `h`. -/
theorem exists_active_flag_of_intObstruction {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {γ : ι → ι → Fin r} {S : Finset ι} (hS : S.card = 5) {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h γ) :
    ∃ F : Flag1 ι, F.Active Arc ∧ F.supp = S ∧ F.owner = h ∧
      ∀ p ∈ arcSet Arc F.nonOwners, γ p.1 p.2 = γ h p.2 := by
  rcases intObstruction_one_pattern hT hh hobs with hA | ⟨a, haS, hah, harc, hdom⟩
  · obtain ⟨hact, hsupp⟩ := active_flag_typeA hS hh hA
    exact ⟨_, hact, hsupp, rfl,
      gate_eq_of_active_of_intObstruction hT hh hobs hact hsupp rfl⟩
  · obtain ⟨hact, hsupp⟩ := active_flag_typeB hS hh haS hah harc hdom
    exact ⟨_, hact, hsupp, rfl,
      gate_eq_of_active_of_intObstruction hT hh hobs hact hsupp rfl⟩

/-- **Section 8**: the flag produced from a radius-one obstruction satisfies its event. -/
theorem mem_flagEvent_of_intObstruction {Arc : ι → ι → Bool}
    (hT : IsTournament Arc)
    {ω : GateCfg ι r} {S : Finset ι} (hS : S.card = 5) {h : ι} (hh : h ∈ S)
    (hobs : IntObstruction Arc 1 S h (toGamma ω)) :
    ∃ F : Flag1 ι, F.Active Arc ∧ F.supp = S ∧ ω ∈ flagEvent Arc F := by
  obtain ⟨F, hact, hsupp, hFh, hgate⟩ :=
    exists_active_flag_of_intObstruction hT hS hh hobs
  refine ⟨F, hact, hsupp, mem_flagEvent.2 fun p hp ↦ ?_⟩
  rw [hFh]
  exact hgate p hp

/-! ### Radius-two obstructions (Section 9) -/

/-- **The consolidated radius-two internal obstruction** on a nine-element support
(Section 9): some vertex of the support owns a radius-two internal obstruction. -/
noncomputable def radiusTwoEvent (Arc : ι → ι → Bool) (S : Finset ι) : Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω => ∃ h ∈ S, IntObstruction Arc 2 S h (toGamma ω)

/-- Membership in the radius-two event. -/
theorem mem_radiusTwoEvent {Arc : ι → ι → Bool} {S : Finset ι} {ω : GateCfg ι r} :
    ω ∈ radiusTwoEvent Arc S ↔ ∃ h ∈ S, IntObstruction Arc 2 S h (toGamma ω) := by
  simp [radiusTwoEvent]

/-- The radius-two event is determined by the arc variables inside its support. -/
theorem radiusTwoEvent_determined {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    (S : Finset ι) :
    Determined (β := fun _ : ι × ι => Fin r) S.offDiag (radiusTwoEvent (r := r) Arc S) := by
  intro ω ω' hagree
  have hg : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → toGamma ω a b = toGamma ω' a b := fun a ha b hb hab ↦
    hagree (a, b) (Finset.mem_offDiag.2 ⟨ha, hb, hab⟩)
  simp only [mem_radiusTwoEvent]
  exact exists_congr fun h ↦ and_congr_right fun hh ↦ ⟨intObstruction_congr hT hh hg,
    intObstruction_congr hT hh fun a ha b hb hab ↦ (hg a ha b hb hab).symm⟩

/-- The Section 9 constant *for a single owner*: `l` of the eight non-owners spend their
residual discrepancy on a discretionary zero (`C(8,l)` choices), at most `C(28, 8-l)` arcs are
exceptional, and each of the remaining `20 + l` arc labels has two admissible values. -/
def radiusTwoOwnerConst : ℕ :=
  2 ^ 20 * ∑ l ∈ Finset.range 9, Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l

/-- The constant `radiusTwoConst = 9 · 2 ^ 20 · ∑_{l=0}^{8} C(8,l) C(28,8-l) 2 ^ l` of Section 9. -/
@[expose]
def radiusTwoConst : ℕ := 1300311466573824

/-- `radiusTwoConst` has one `radiusTwoOwnerConst` for each of the nine possible owners. -/
theorem radiusTwoConst_eq_nine_mul : radiusTwoConst = 9 * radiusTwoOwnerConst := by
  rw [radiusTwoConst, radiusTwoOwnerConst, ← mul_assoc]
  exact Numerics.radiusTwoSum_eq.symm

section MissArcs

omit [Fintype ι]
variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} {T : Finset ι}
  {p : ι × ι}

/-- **The missing arcs of `T`**: the internal arcs whose gate label avoids the target zero
set.  Section 9 covers these by an exceptional set `X`. -/
def missArcs (Arc : ι → ι → Bool) (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r))
    (T : Finset ι) : Finset (ι × ι) :=
  (arcSet Arc T).filter fun p => γ p.1 p.2 ∉ Z p.2

/-- **The discretionary vertices of `T`**: those whose zero set is not just the owner gate,
so that they have spent their residual discrepancy on a zero of their own. -/
def discSet (γ : ι → ι → Fin r) (Z : ι → Finset (Fin r)) (T : Finset ι) (h : ι) : Finset ι :=
  T.filter fun j => ¬ (Z j ⊆ {γ h j})

omit [DecidableEq ι] in
@[simp]
theorem mem_missArcs : p ∈ missArcs Arc γ Z T ↔ p ∈ arcSet Arc T ∧ γ p.1 p.2 ∉ Z p.2 :=
  Finset.mem_filter

omit [DecidableEq ι] in
@[simp]
theorem mem_discSet {h j : ι} : j ∈ discSet γ Z T h ↔ j ∈ T ∧ ¬ (Z j ⊆ {γ h j}) :=
  Finset.mem_filter

omit [DecidableEq ι] in
theorem missArcs_subset : missArcs Arc γ Z T ⊆ arcSet Arc T := Finset.filter_subset _ _

omit [DecidableEq ι] in
theorem discSet_subset {h : ι} : discSet γ Z T h ⊆ T := Finset.filter_subset _ _

omit [DecidableEq ι] in
/-- The discretionary vertices are counted by their indicator. -/
theorem card_discSet_eq_sum (T : Finset ι) (h : ι) :
    (discSet γ Z T h).card = ∑ j ∈ T, if Z j ⊆ {γ h j} then 0 else 1 := by
  rw [discSet, Finset.card_filter]
  exact Finset.sum_congr rfl fun j _ ↦ ite_not _ _ _

omit [DecidableEq ι] in
/-- The missing arcs of `T` fibre over their tails, the fibre above `j` being the misses of
`j` inside `T`. -/
theorem card_missArcs_eq_sum (hT : IsTournament Arc) (T : Finset ι) :
    (missArcs Arc γ Z T).card = ∑ j ∈ T, (missSet Arc γ Z T j).card := by
  classical
  rw [missArcs, Finset.card_eq_sum_card_fiberwise (t := T) (f := Prod.fst)
    fun p hp ↦ (mem_arcSet.1 (Finset.mem_filter.1 hp).1).1.1]
  refine Finset.sum_congr rfl fun j hjT ↦ ?_
  rw [← Finset.card_image_of_injective (missSet Arc γ Z T j) (Prod.mk_right_injective j)]
  congr 1
  ext q
  obtain ⟨a, b⟩ := q
  simp only [Finset.mem_filter, mem_arcSet, mem_missSet, Finset.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨⟨-, hb, -⟩, harc⟩, hmiss⟩, rfl⟩
    exact ⟨b, ⟨hb, harc, hmiss⟩, rfl, rfl⟩
  · rintro ⟨c, ⟨hc, harc, hmiss⟩, rfl, rfl⟩
    exact ⟨⟨⟨⟨hjT, hc, hT.ne_of_arc harc⟩, harc⟩, hmiss⟩, rfl⟩

end MissArcs

/-- **One branch of the Section 9 enumeration**: the owner is `h`, the non-owners in `L`
spend their residual discrepancy on the discretionary zero `w`, the arcs of `X` are the
exceptional (missing) ones, and every other internal non-owner arc hits the two-element
target set of its head block. -/
noncomputable def branch2 (Arc : ι → ι → Bool) (S : Finset ι) (h : ι) (L : Finset ι)
    (w : (j : ι) → j ∈ L → Fin r) (X : Finset (ι × ι)) : Finset (GateCfg ι r) :=
  open scoped Classical in
  Finset.univ.filter fun ω =>
    ∀ p ∈ arcSet Arc (S.erase h), p ∉ X →
      ω p = ω (h, p.2) ∨ ω p = (if hp : p.2 ∈ L then w p.2 hp else ω (h, p.2))

theorem mem_branch2 {Arc : ι → ι → Bool} {S : Finset ι} {h : ι} {L : Finset ι}
    {w : (j : ι) → j ∈ L → Fin r} {X : Finset (ι × ι)} {ω : GateCfg ι r} :
    ω ∈ branch2 Arc S h L w X ↔ ∀ p ∈ arcSet Arc (S.erase h), p ∉ X →
      ω p = ω (h, p.2) ∨ ω p = (if hp : p.2 ∈ L then w p.2 hp else ω (h, p.2)) := by
  classical
  simp [branch2]

open scoped Classical in
/-- **Section 9**: the consolidated event is the union over the nine possible owners. -/
theorem radiusTwoEvent_subset_biUnion_owner (Arc : ι → ι → Bool) (S : Finset ι) :
    radiusTwoEvent (r := r) Arc S ⊆ S.biUnion fun h =>
      Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω) := by
  intro ω hω
  rw [mem_radiusTwoEvent] at hω
  obtain ⟨h, hh, hobs⟩ := hω
  exact Finset.mem_biUnion.mpr ⟨h, hh, (Finset.mem_filter_univ _).mpr hobs⟩

omit [Fintype ι] in
/-- The eight conditioned owner gates are disjoint from the arcs among the non-owners. -/
theorem disjoint_ownerGates_arcSet (Arc : ι → ι → Bool) (S : Finset ι) (h : ι) :
    Disjoint (ownerGates h (S.erase h)) (arcSet Arc (S.erase h)) := by
  rw [Finset.disjoint_left]
  intro p hp1 hp2
  exact Finset.notMem_erase h S ((mem_ownerGates.1 hp1).1 ▸ (mem_arcSet.1 hp2).1.1)

omit [Fintype ι] in
/-- The eight non-owners of a nine-element support span `Q = C(8, 2) = 28` internal arcs. -/
theorem card_arcSet_erase {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι}
    (hh : h ∈ S) : (arcSet Arc (S.erase h)).card = 28 := by
  rw [card_arcSet hT, Finset.card_erase_of_mem hh, hS]
  rfl

/-- A finset with at most one element besides `a` is contained in a pair through `a`. -/
private theorem subset_pair_of_card_erase_le_one {α : Type*} [DecidableEq α] [Nonempty α]
    {s : Finset α} {a : α} (h : (s.erase a).card ≤ 1) : ∃ z, s ⊆ {a, z} := by
  obtain ⟨z, hz⟩ := Finset.card_le_one_iff_subset_singleton.mp h
  refine ⟨z, fun x hx ↦ ?_⟩
  rcases eq_or_ne x a with rfl | hxa
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hz (Finset.mem_erase.mpr ⟨hxa, hx⟩))

omit [Fintype ι] in
/-- **Section 9, budget at one non-owner.**  If `h → j` then `γ h j ∈ Z j`; if `j → h` then
the arc `j → h` is an automatic miss because `Z h = ∅`.  Either way `Z j` is contained in a
two-element set consisting of the owner gate and one discretionary zero, and `j` has at most
one further internal discrepancy, which it loses if it uses the discretionary zero. -/
theorem intObstruction_two_nonowner [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j) {j : ι} (hj : j ∈ S.erase h)
    (hbud : (Z j).card + (missSet Arc γ Z S j).card ≤ 2) :
    (∃ z : Fin r, Z j ⊆ {γ h j, z}) ∧
      (missSet Arc γ Z (S.erase h) j).card + (if Z j ⊆ {γ h j} then 0 else 1) ≤ 1 := by
  have : Nonempty (Fin r) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne r)⟩⟩
  have hjh : j ≠ h := Finset.ne_of_mem_erase hj
  have hle : (missSet Arc γ Z (S.erase h) j).card ≤ (missSet Arc γ Z S j).card :=
    Finset.card_le_card (missSet_subset_missSet (Finset.erase_subset _ _))
  cases hA : Arc h j with
  | true =>
    -- the owner gate already occupies one of the two units of budget
    have hmem : γ h j ∈ Z j := hgate j (Finset.mem_of_mem_erase hj) (by rw [hA])
    have hz1 : 1 ≤ (Z j).card := Finset.card_pos.mpr ⟨_, hmem⟩
    have hce : ((Z j).erase (γ h j)).card = (Z j).card - 1 := Finset.card_erase_of_mem hmem
    refine ⟨subset_pair_of_card_erase_le_one (by omega), ?_⟩
    by_cases hsub : Z j ⊆ {γ h j}
    · rw [ite_eq_left hsub]
      omega
    · rw [ite_eq_right hsub]
      obtain ⟨z, hzZ, hzne⟩ := Finset.not_subset.1 hsub
      have h2 : 2 ≤ (Z j).card := Finset.one_lt_card.2
        ⟨_, hmem, z, hzZ, fun hc ↦ hzne (Finset.mem_singleton.2 hc.symm)⟩
      omega
  | false =>
    -- the automatic miss `j → h` already occupies one of the two units of budget
    have hhM : h ∈ missSet Arc γ Z S j :=
      mem_missSet.2 ⟨hh, hT.arc_of_not_arc hjh hA, by simp [hZh]⟩
    have hM'card : (missSet Arc γ Z (S.erase h) j).card + 1 ≤ (missSet Arc γ Z S j).card := by
      have hsub : missSet Arc γ Z (S.erase h) j ⊆ (missSet Arc γ Z S j).erase h :=
        Finset.subset_erase.2 ⟨missSet_subset_missSet (Finset.erase_subset _ _),
          fun hc ↦ Finset.notMem_erase h S (mem_missSet.1 hc).1⟩
      have hcard := Finset.card_le_card hsub
      have hpos : 1 ≤ (missSet Arc γ Z S j).card := Finset.card_pos.2 ⟨h, hhM⟩
      rw [Finset.card_erase_of_mem hhM] at hcard
      omega
    refine ⟨subset_pair_of_card_erase_le_one (Finset.card_erase_le.trans (by omega)), ?_⟩
    by_cases hsub : Z j ⊆ {γ h j}
    · rw [ite_eq_left hsub]
      omega
    · rw [ite_eq_right hsub]
      obtain ⟨z, hzZ, -⟩ := Finset.not_subset.1 hsub
      have h1 : 1 ≤ (Z j).card := Finset.card_pos.2 ⟨z, hzZ⟩
      omega

omit [Fintype ι] in
/-- **Section 9**: if `l` non-owners take a discretionary zero, the total number of misses
among the twenty-eight internal non-owner arcs is at most `8 - l`. -/
theorem card_miss_add_card_disc_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S)
    {γ : ι → ι → Fin r} {Z : ι → Finset (Fin r)} (hZh : Z h = ∅)
    (hgate : ∀ j ∈ S, Arc h j → γ h j ∈ Z j)
    (hbud : ∀ i ∈ S, i ≠ h → (Z i).card + (missSet Arc γ Z S i).card ≤ 2) :
    (missArcs Arc γ Z (S.erase h)).card + (discSet γ Z (S.erase h) h).card ≤ 8 := by
  have hEcard : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  rw [card_missArcs_eq_sum hT, card_discSet_eq_sum, ← Finset.sum_add_distrib]
  calc ∑ j ∈ S.erase h, ((missSet Arc γ Z (S.erase h) j).card
          + if Z j ⊆ {γ h j} then 0 else 1)
      ≤ ∑ _j ∈ S.erase h, 1 := Finset.sum_le_sum fun j hjE ↦
        (intObstruction_two_nonowner hT hh hZh hgate hjE
          (hbud j (Finset.mem_of_mem_erase hjE) (Finset.ne_of_mem_erase hjE))).2
    _ = 8 := by rw [Finset.sum_const, hEcard, smul_eq_mul, mul_one]

/-- **Section 9**: every radius-two internal obstruction with owner `h` lies in one of the
enumerated branches. -/
theorem intObstruction_two_data [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) {ω : GateCfg ι r}
    (hobs : IntObstruction Arc 2 S h (toGamma ω)) :
    ∃ (L : Finset ι) (w : (j : ι) → j ∈ L → Fin r) (X : Finset (ι × ι)),
      L ⊆ S.erase h ∧ X ⊆ arcSet Arc (S.erase h) ∧ X.card + L.card = 8 ∧
        ω ∈ branch2 Arc S h L w X := by
  classical
  obtain ⟨Z, hZh, hgate, hbud⟩ := hobs
  have hnono : ∀ j ∈ S.erase h, ∃ z : Fin r, Z j ⊆ {toGamma ω h j, z} := fun j hj ↦
    (intObstruction_two_nonowner hT hh hZh hgate hj
      (hbud j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))).1
  refine ⟨discSet (toGamma ω) Z (S.erase h) h,
    fun j hj ↦ (hnono j (discSet_subset hj)).choose, ?_⟩
  have hle := card_miss_add_card_disc_le hT hS hh hZh hgate hbud
  have hcard8 : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  have hAA : (arcSet Arc (S.erase h)).card = 28 := card_arcSet_erase hT hS hh
  obtain ⟨X, hX₀X, hXsub, hXcard⟩ := Finset.exists_subsuperset_card_eq
    (missArcs_subset (Arc := Arc) (γ := toGamma ω) (Z := Z) (T := S.erase h))
    (n := 8 - (discSet (toGamma ω) Z (S.erase h) h).card) (by omega) (by omega)
  refine ⟨X, discSet_subset, hXsub, by omega, mem_branch2.2 fun p hp hpX ↦ ?_⟩
  have hmem : toGamma ω p.1 p.2 ∈ Z p.2 := by
    by_contra hc
    exact hpX (hX₀X (mem_missArcs.2 ⟨hp, hc⟩))
  by_cases hpL : p.2 ∈ discSet (toGamma ω) Z (S.erase h) h
  · rw [dite_eq_left hpL]
    have hspec := (hnono p.2 (discSet_subset hpL)).choose_spec hmem
    rw [Finset.mem_insert, Finset.mem_singleton] at hspec
    simpa [toGamma] using hspec
  · left
    have hsub : Z p.2 ⊆ {toGamma ω h p.2} :=
      not_not.1 fun hc ↦ hpL (mem_discSet.2 ⟨(mem_arcSet.1 hp).1.2.1, hc⟩)
    simpa [toGamma] using Finset.mem_singleton.mp (hsub hmem)

open scoped Classical in
/-- **Section 9**: the radius-two event for a fixed owner is covered by the branches. -/
theorem obs2_subset_branches [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9)
    {h : ι} (hh : h ∈ S) :
    (Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω)) ⊆
      (S.erase h).powerset.biUnion fun L =>
        (L.pi fun _ => (Finset.univ : Finset (Fin r))).biUnion fun w =>
          ((arcSet Arc (S.erase h)).powersetCard (8 - L.card)).biUnion fun X =>
            branch2 Arc S h L w X := by
  intro ω hω
  simp only [Finset.mem_filter_univ] at hω
  obtain ⟨L, w, X, hLsub, hXsub, hcard, hmem⟩ := intObstruction_two_data hT hS hh hω
  refine Finset.mem_biUnion.mpr ⟨L, Finset.mem_powerset.mpr hLsub, ?_⟩
  refine Finset.mem_biUnion.mpr ⟨w, Finset.mem_pi.mpr fun a _ ↦ Finset.mem_univ _, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨X, Finset.mem_powersetCard.mpr ⟨hXsub, by omega⟩, hmem⟩

/-- **Section 9**: in a fixed branch the `28 - |X|` remaining arc labels are independent and
uniform after conditioning on the owner gates, and each must hit a target set of size at
most two. -/
theorem pr_branch2_le [NeZero r] {Arc : ι → ι → Bool} {S : Finset ι} {h : ι}
    {L : Finset ι} (w : (j : ι) → j ∈ L → Fin r)
    {X : Finset (ι × ι)} (hX : X ⊆ arcSet Arc (S.erase h)) :
    pr (β := fun _ : ι × ι => Fin r) (branch2 Arc S h L w X)
      ≤ ((2 : ℝ) / r) ^ ((arcSet Arc (S.erase h)).card - X.card) := by
  classical
  have hsnd : ∀ p ∈ arcSet Arc (S.erase h) \ X,
      (h, p.2) ∈ ownerGates h (S.erase h) := fun p hp ↦
    mem_ownerGates.2 ⟨rfl, (mem_arcSet.1 (Finset.mem_sdiff.1 hp).1).1.2.1⟩
  have hdisj : Disjoint (ownerGates h (S.erase h)) (arcSet Arc (S.erase h) \ X) :=
    Finset.disjoint_of_subset_right Finset.sdiff_subset
      (disjoint_ownerGates_arcSet Arc S h)
  have key := pr_le_pow_of_pinned (β := fun _ : ι × ι ↦ Fin r)
      (G := ownerGates h (S.erase h)) (T := arcSet Arc (S.erase h) \ X)
      hdisj r (fun a _ ↦ Fintype.card_fin r)
      (fun c p ↦ if hp : (h, p.2) ∈ ownerGates h (S.erase h) then
        {c (h, p.2) hp, if hq : p.2 ∈ L then w p.2 hq else c (h, p.2) hp}
      else Finset.univ) 2
      (by
        intro c p hp
        rw [dite_eq_left (hsnd p hp)]
        exact (Finset.card_insert_le _ _).trans (by simp))
      (E := branch2 Arc S h L w X)
      (by
        intro ω hω p hp
        dsimp only
        rw [dite_eq_left (hsnd p hp)]
        obtain ⟨hp1, hp2⟩ := Finset.mem_sdiff.mp hp
        rcases mem_branch2.1 hω p hp1 hp2 with hcase | hcase <;> simp [hcase])
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hX] at key
  simpa using key

omit [Fintype ι] in
/-- The two innermost sums of `sum_branch_pow_eq` are constant: there are `r ^ |L|` choices of
discretionary zeros and `C(28, 8 - |L|)` choices of the exceptional arc set. -/
private theorem sum_pi_sum_powersetCard_const {AA : Finset (ι × ι)} (hAA : AA.card = 28)
    {L : Finset ι} (hL : L.card ≤ 8) :
    (∑ _w ∈ (L.pi fun _ ↦ (Finset.univ : Finset (Fin r))),
        ∑ _X ∈ AA.powersetCard (8 - L.card), ((2 : ℝ) / r) ^ (AA.card - (8 - L.card)))
      = (r : ℝ) ^ L.card * (Nat.choose 28 (8 - L.card) : ℝ) * ((2 : ℝ) / r) ^ (20 + L.card) := by
  have hexp : AA.card - (8 - L.card) = 20 + L.card := by omega
  rw [hexp, Finset.sum_const, Finset.sum_const, Finset.card_powersetCard, hAA, Finset.card_pi]
  simp only [Finset.card_univ, Fintype.card_fin, Finset.prod_const, nsmul_eq_mul]
  push_cast
  ring

/-- The `r ^ l` choices of discretionary zeros cancel `l` of the `n + l` factors of `r`. -/
private theorem pow_mul_div_pow_add (hr : (r : ℝ) ≠ 0) (c : ℝ) (n l : ℕ) :
    (r : ℝ) ^ l * c * ((2 : ℝ) / r) ^ (n + l) = c * 2 ^ n * 2 ^ l / (r : ℝ) ^ n := by
  rw [div_pow, pow_add, pow_add]
  field_simp

omit [Fintype ι] in
/-- **Section 9**: evaluating the triple sum of the branch bounds: collapse the two inner
constant sums, then regroup the outer powerset sum by cardinality. -/
theorem sum_branch_pow_eq [NeZero r] {S : Finset ι} {h : ι} (hh : h ∈ S) (hS : S.card = 9)
    {AA : Finset (ι × ι)} (hAA : AA.card = 28) :
    ∑ L ∈ (S.erase h).powerset, ∑ _w ∈ (L.pi fun _ => (Finset.univ : Finset (Fin r))),
        ∑ _X ∈ AA.powersetCard (8 - L.card), ((2 : ℝ) / r) ^ (AA.card - (8 - L.card))
      = (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by
  classical
  have hr : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hcard8 : (S.erase h).card = 8 := by rw [Finset.card_erase_of_mem hh, hS]
  rw [radiusTwoOwnerConst]
  rw [Finset.sum_congr rfl fun L hL ↦ sum_pi_sum_powersetCard_const hAA
      ((Finset.card_le_card (Finset.mem_powerset.mp hL)).trans hcard8.le),
    Finset.sum_powerset, hcard8]
  have step2 : ∀ l ∈ Finset.range 9,
      (∑ _L ∈ (S.erase h).powersetCard l,
        (r : ℝ) ^ l * (Nat.choose 28 (8 - l) : ℝ) * ((2 : ℝ) / r) ^ (20 + l))
      = (Nat.choose 8 l : ℝ) * (Nat.choose 28 (8 - l) : ℝ) * 2 ^ 20 * 2 ^ l / (r : ℝ) ^ 20 := by
    intro l _
    rw [Finset.sum_const, Finset.card_powersetCard, hcard8, nsmul_eq_mul,
      pow_mul_div_pow_add hr]
    ring
  calc
    (∑ j ∈ Finset.range (8 + 1), ∑ L ∈ (S.erase h).powersetCard j,
        (r : ℝ) ^ L.card * (Nat.choose 28 (8 - L.card) : ℝ) * ((2 : ℝ) / r) ^ (20 + L.card))
        = ∑ l ∈ Finset.range 9, ∑ _L ∈ (S.erase h).powersetCard l,
            (r : ℝ) ^ l * (Nat.choose 28 (8 - l) : ℝ) * ((2 : ℝ) / r) ^ (20 + l) := by
          refine Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun L hL ↦ ?_
          rw [(Finset.mem_powersetCard.mp hL).2]
    _ = ∑ l ∈ Finset.range 9,
          (Nat.choose 8 l : ℝ) * (Nat.choose 28 (8 - l) : ℝ) * 2 ^ 20 * 2 ^ l / (r : ℝ) ^ 20 :=
          Finset.sum_congr rfl step2
    _ = ((2 ^ 20 * ∑ l ∈ Finset.range 9,
          Nat.choose 8 l * Nat.choose 28 (8 - l) * 2 ^ l : ℕ) : ℝ) / (r : ℝ) ^ 20 := by
          rw [eq_div_iff (pow_ne_zero 20 hr), Finset.sum_mul]
          push_cast
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun l _ ↦ ?_
          field_simp
          ring

open scoped Classical in
/-- **Section 9**: the radius-two obstruction for a fixed owner has probability at most
`radiusTwoConst / (9 * r ^ 20)`. -/
theorem pr_intObstruction_owner_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) {h : ι} (hh : h ∈ S) :
    pr (β := fun _ : ι × ι => Fin r)
        (Finset.univ.filter fun ω : GateCfg ι r => IntObstruction Arc 2 S h (toGamma ω))
      ≤ (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 := by
  have hAA : (arcSet Arc (S.erase h)).card = 28 := card_arcSet_erase hT hS hh
  have h1 := pr_le_of_subset_biUnion (β := fun _ : ι × ι ↦ Fin r) _ _
      (obs2_subset_branches hT hS hh)
  apply h1.trans
  rw [← sum_branch_pow_eq (r := r) hh hS hAA]
  refine Finset.sum_le_sum fun L _ ↦ ?_
  apply (pr_biUnion_le _ _).trans
  refine Finset.sum_le_sum fun w _ ↦ ?_
  apply (pr_biUnion_le _ _).trans
  refine Finset.sum_le_sum fun X hX ↦ ?_
  have hXmem := Finset.mem_powersetCard.mp hX
  have hbr := pr_branch2_le (r := r) w hXmem.1
  rwa [hXmem.2] at hbr

open scoped Classical in
/-- **Section 9**: the consolidated radius-two obstruction on a nine-element support has
probability at most `radiusTwoConst / r ^ 20`.  Each non-owner has one residual discrepancy;
if `l` of them spend it on a discretionary zero there are at most `C(8,l) r ^ l` choices, at
most `C(28, 8-l)` choices of an exceptional superset of the missing arcs, and each of the
remaining `20 + l` arc labels must hit a target set of size at most two. -/
theorem pr_radiusTwoEvent_le [NeZero r] {Arc : ι → ι → Bool} (hT : IsTournament Arc)
    {S : Finset ι} (hS : S.card = 9) :
    pr (β := fun _ : ι × ι => Fin r) (radiusTwoEvent Arc S)
      ≤ (radiusTwoConst : ℝ) / (r : ℝ) ^ 20 := by
  have hb := pr_le_of_subset_biUnion (β := fun _ : ι × ι ↦ Fin r) S
    (fun h ↦ Finset.univ.filter fun ω : GateCfg ι r ↦ IntObstruction Arc 2 S h (toGamma ω))
    (radiusTwoEvent_subset_biUnion_owner Arc S)
  have hterm : ∀ h ∈ S, pr (β := fun _ : ι × ι ↦ Fin r)
      (Finset.univ.filter fun ω : GateCfg ι r ↦ IntObstruction Arc 2 S h (toGamma ω))
      ≤ (radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20 :=
    fun h hh ↦ pr_intObstruction_owner_le hT hS hh
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, hS, nsmul_eq_mul] at hsum
  rw [radiusTwoConst_eq_nine_mul]
  calc pr (β := fun _ : ι × ι ↦ Fin r) (radiusTwoEvent Arc S) ≤ _ := hb
    _ ≤ (9 : ℝ) * ((radiusTwoOwnerConst : ℝ) / (r : ℝ) ^ 20) := by exact_mod_cast hsum
    _ = ((9 * radiusTwoOwnerConst : ℕ) : ℝ) / (r : ℝ) ^ 20 := by
        push_cast
        ring

end LLL

end BSLambda
