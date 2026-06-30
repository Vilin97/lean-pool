/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/

import LeanPool.DomainTheory.Neighborhood.FunctionSpace
import LeanPool.DomainTheory.Neighborhood.Definition72
import LeanPool.DomainTheory.Neighborhood.Theorem74

/-!
# Theorem 7.5 (Scott 1981, PRG-19, §7) — `(𝒟₀ → 𝒟₁)` is effectively given

Following Dana Scott, *Lectures on a Mathematical Theory of Computation*, PRG-19,
Lecture VII.

> **Theorem 7.5.** If `𝒟₀` and `𝒟₁` are effectively given, then so is `(𝒟₀ → 𝒟₁)`.
The combinators
> `eval` and `curry` are computable, provided all the domains involved are
effectively given. The
> computable elements `f ∈ |𝒟₀ → 𝒟₁|` are exactly the computable maps `f : 𝒟₀ →
𝒟₁`.

This file builds the theorem in green, audited, **choice-free** milestones (see
`HANDOFF.md`).

## Milestone 1 — Proposition 3.9(i), the consistency condition (forward,
choice-free)

The keystone is Scott's 3.9(i): a function-space neighbourhood `⋂[Xᵢ,Yᵢ]` is
non-empty iff for every
subset `I` of indices with `{Xᵢ ∣ i∈I}` consistent in `𝒟₀`, the outputs `{Yᵢ ∣
i∈I}` are consistent
in `𝒟₁`. We model a subset by a **sublist** `sub ⊑ L` (this is what the eventual
primitive-recursive
decider enumerates, one entry/bit at a time), and the intersection of a finite
list of neighbourhoods
by `interList`. The forward direction — non-empty ⟹ the subset condition — is
choice-free: given a
witness map `f ∈ stepFun L` and a common lower neighbourhood `Z` of the selected
inputs, `f` relates
`Z` to the intersection of the selected outputs (a finite `inter_right` fold over
the *explicit*
selection, so **no undecidable `X ⊆ Xᵢ` case-split is needed**), whence that
intersection is a
neighbourhood by `f.rel_cod`.

(The reverse direction is genuinely decidable only relative to the presentations —
it needs
`𝒟₀`-inclusion to be decidable to single out `{i ∣ X ⊆ Xᵢ}` — and is developed
with the decider.)
-/

namespace Domain.Neighborhood

open NeighborhoodSystem Domain.Recursive ApproximableMap

variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-! ### `interList` — the intersection of a finite list of neighbourhoods (with a
base). -/

/-- The intersection of the sets in `M`, taken inside the base set `base` (so the
empty list gives
`base`, matching the convention 1.1a where the empty intersection is `Δ`). -/
def interList (base : Set β) : List (Set β) → Set β
  | [] => base
  | Y :: M => Y ∩ interList base M

@[simp] theorem interList_nil (base : Set β) : interList base [] = base := rfl

theorem interList_cons (base : Set β) (Y : Set β) (M : List (Set β)) :
    interList base (Y :: M) = Y ∩ interList base M := rfl

theorem mem_interList {base : Set β} {M : List (Set β)} {z : β} :
    z ∈ interList base M ↔ z ∈ base ∧ ∀ Y ∈ M, z ∈ Y := by
  induction M with
  | nil => simp
  | cons Y M ih =>
    rw [interList_cons]
    simp only [Set.mem_inter_iff, ih, List.mem_cons]
    constructor
    · rintro ⟨hY, hbase, hM⟩
      exact ⟨hbase, fun W hW => hW.elim (fun h => h ▸ hY) (hM W)⟩
    · rintro ⟨hbase, hall⟩
      exact ⟨hall Y (Or.inl rfl), hbase, fun W hW => hall W (Or.inr hW)⟩

theorem interList_subset_base {base : Set β} {M : List (Set β)} : interList base M ⊆ base :=
  fun _ hz => (mem_interList.mp hz).1

/-! ### Milestone 1 — the forward direction of 3.9(i), choice-free. -/

/-- A witness map `f ∈ stepFun L` relates a common lower neighbourhood `Z` of the
*selected* inputs
to the intersection of the *selected* outputs. The selection `sub` is processed
entry-by-entry with
`inter_right`, so the proof is choice-free (no inclusion case-split). -/
theorem rel_interList_of_selection {f : ApproximableMap V₀ V₁}
    {Z : Set α} (hZ : V₀.mem Z) {sub : List (Set α × Set β)}
    (hmem : ∀ p ∈ sub, f.rel p.1 p.2) (hZle : ∀ p ∈ sub, Z ⊆ p.1) :
    f.rel Z (interList V₁.master (sub.map Prod.snd)) := by
  induction sub with
  | nil =>
    simp only [List.map_nil, interList_nil]
    exact f.mono f.master_rel (V₀.sub_master hZ) subset_rfl hZ V₁.master_mem
  | cons p sub ih =>
    have hp : f.rel p.1 p.2 := hmem p (List.mem_cons.mpr (Or.inl rfl))
    have hZp : f.rel Z p.2 :=
      f.mono hp (hZle p (List.mem_cons.mpr (Or.inl rfl))) subset_rfl hZ (f.rel_cod hp)
    have htail : f.rel Z (interList V₁.master (sub.map Prod.snd)) :=
      ih (fun q hq => hmem q (List.mem_cons.mpr (Or.inr hq)))
        (fun q hq => hZle q (List.mem_cons.mpr (Or.inr hq)))
    rw [List.map_cons, interList_cons]
    exact f.inter_right hZp htail

/-- **Proposition 3.9(i) (Scott 1981, PRG-19), forward direction — choice-free.**
If the
function-space neighbourhood `stepFun L` is non-empty, then for every selection
`sub ⊑ L` whose
inputs admit a common lower neighbourhood `Z ∈ 𝒟₀`, the intersection of the
selected outputs is a
neighbourhood of `𝒟₁`. -/
theorem interList_mem_of_stepFun_nonempty {L : List (Set α × Set β)}
    (h : (stepFun L : Set (ApproximableMap V₀ V₁)).Nonempty) {sub : List (Set α × Set β)}
    (hsub : sub.Sublist L) {Z : Set α} (hZ : V₀.mem Z) (hZle : ∀ p ∈ sub, Z ⊆ p.1) :
    V₁.mem (interList V₁.master (sub.map Prod.snd)) := by
  obtain ⟨f, hf⟩ := h
  have hmem : ∀ p ∈ sub, f.rel p.1 p.2 := fun p hp => hf p (hsub.subset hp)
  exact f.rel_cod (rel_interList_of_selection hZ hmem hZle)

/-! ### Milestone 2 — the consistency characterization over coded entry-lists.

A function-space neighbourhood is presented by a list `el : List ℕ` of *entry
codes*: each `e ∈ el`
codes a step pair `[X_{e.1}, Y_{e.2}]` via `Nat.pair`. `funListOf` turns `el` into
the list of step
pairs, and `stepFun (funListOf el)` is the neighbourhood `⋂[X_{eᵢ.1}, Y_{eᵢ.2}]`.

The characterization `stepFun_funListOf_nonempty_iff` is Scott's 3.9(i): the
neighbourhood is
non-empty iff for every *sub-selection* `sub ⊑ el` whose inputs have a common
lower neighbourhood
`Z ∈ 𝒟₀`, the intersection of the selected outputs is a neighbourhood of `𝒟₁`. The
reverse direction
builds the least map `leastMap`; its consistency hypothesis is discharged
input-by-input by
**filtering `el` with the (choice-free) decidable `𝒟₀`-inclusion test** supplied
by the presentation
`P₀`, so it stays `⊆ {propext, Quot.sound}`. -/

variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- The step pair coded by an entry `e`: `(X_{e.unpair.1}, Y_{e.unpair.2})`. -/
def funPair (e : ℕ) : Set α × Set β := (P₀.X e.unpair.1, P₁.X e.unpair.2)

@[simp] theorem funPair_fst (e : ℕ) : (funPair P₀ P₁ e).1 = P₀.X e.unpair.1 := rfl
@[simp] theorem funPair_snd (e : ℕ) : (funPair P₀ P₁ e).2 = P₁.X e.unpair.2 := rfl

/-- The list of step pairs coded by an entry-list `el`. -/
def funListOf (el : List ℕ) : List (Set α × Set β) := el.map (funPair P₀ P₁)

theorem funListOf_valid (el : List ℕ) :
    ∀ p ∈ funListOf P₀ P₁ el, V₀.mem p.1 ∧ V₁.mem p.2 := by
  intro p hp
  rw [funListOf, List.mem_map] at hp
  obtain ⟨e, _, rfl⟩ := hp
  exact ⟨P₀.mem_X _, P₁.mem_X _⟩

/-- **Proposition 3.9(i) (Scott 1981, PRG-19), over coded entry-lists —
choice-free.** The
function-space neighbourhood `⋂[X_{eᵢ}, Y_{eᵢ}]` coded by `el` is non-empty iff
for every
sub-selection `sub ⊑ el` whose inputs `{X_{e} ∣ e ∈ sub}` admit a common lower
neighbourhood
`Z ∈ 𝒟₀`, the intersection of the selected outputs `{Y_{e} ∣ e ∈ sub}` is a
neighbourhood of `𝒟₁`.

* (⟹) is `interList_mem_of_stepFun_nonempty` (Milestone 1), pushed through
`funPair`.
* (<=) builds `leastMap`; its consistency hypothesis `hcons` is discharged for each
input `X'` by
  **filtering `el` with the decidable `𝒟₀`-inclusion `X' ⊆ X_e`** (supplied
  choice-free by `P₀`), so
  that `interYs Δ₁ (funListOf el) X'` is exactly the intersection of the selected
  outputs. -/
theorem stepFun_funListOf_nonempty_iff (el : List ℕ) :
    (stepFun (funListOf P₀ P₁ el) : Set (ApproximableMap V₀ V₁)).Nonempty ↔
      ∀ sub : List ℕ, sub.Sublist el →
        (∃ Z, V₀.mem Z ∧ ∀ e ∈ sub, Z ⊆ P₀.X e.unpair.1) →
          V₁.mem (interList V₁.master (sub.map (fun e => P₁.X e.unpair.2))) := by
  constructor
  · -- forward
    intro h sub hsub hcons
    obtain ⟨Z, hZ, hZle⟩ := hcons
    have hsub' : (sub.map (funPair P₀ P₁)).Sublist (funListOf P₀ P₁ el) := hsub.map _
    have hZle' : ∀ p ∈ sub.map (funPair P₀ P₁), Z ⊆ p.1 := by
      intro p hp
      rw [List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact hZle e he
    have hres := interList_mem_of_stepFun_nonempty h hsub' hZ hZle'
    have hlist : (sub.map (funPair P₀ P₁)).map Prod.snd = sub.map (fun e => P₁.X e.unpair.2) := by
      rw [List.map_map]; rfl
    rwa [hlist] at hres
  · -- backward
    intro hcond
    have hL := funListOf_valid P₀ P₁ el
    have hcons : ∀ {X' : Set α}, V₀.mem X' →
        V₁.mem (interYs V₁.master (funListOf P₀ P₁ el) X') := by
      intro X' hX'
      obtain ⟨nx, hnx⟩ := P₀.surj hX'
      obtain ⟨finc, _, hfinc⟩ := P₀.incl_computable
      letI : DecidablePred (fun e : ℕ => X' ⊆ P₀.X e.unpair.1) := fun e =>
        decidable_of_iff (finc (Nat.pair nx e.unpair.1) = 1) (by
          have h := hfinc (Nat.pair nx e.unpair.1)
          simp only [unpair_pair_fst, unpair_pair_snd] at h
          rw [hnx] at h
          exact h.symm)
      set sub : List ℕ := el.filter (fun e => decide (X' ⊆ P₀.X e.unpair.1)) with hsubdef
      have hsub : sub.Sublist el := List.filter_sublist
      have hmem_iff : ∀ e, e ∈ sub ↔ e ∈ el ∧ X' ⊆ P₀.X e.unpair.1 := by
        intro e
        rw [hsubdef, List.mem_filter, decide_eq_true_iff]
      have heq : interYs V₁.master (funListOf P₀ P₁ el) X'
          = interList V₁.master (sub.map (fun e => P₁.X e.unpair.2)) := by
        apply Set.ext; intro z
        rw [mem_interYs, mem_interList]
        constructor
        · rintro ⟨hzb, hall⟩
          refine ⟨hzb, ?_⟩
          intro Y hY
          rw [List.mem_map] at hY
          obtain ⟨e, hesub, rfl⟩ := hY
          have he := (hmem_iff e).mp hesub
          have hpair : funPair P₀ P₁ e ∈ funListOf P₀ P₁ el := List.mem_map.mpr ⟨e, he.1, rfl⟩
          exact hall (funPair P₀ P₁ e) hpair he.2
        · rintro ⟨hzb, hall⟩
          refine ⟨hzb, ?_⟩
          intro p hp hXp
          rw [funListOf, List.mem_map] at hp
          obtain ⟨e, hee, rfl⟩ := hp
          have hesub : e ∈ sub := (hmem_iff e).mpr ⟨hee, hXp⟩
          exact hall (P₁.X e.unpair.2) (List.mem_map.mpr ⟨e, hesub, rfl⟩)
      rw [heq]
      refine hcond sub hsub ⟨X', hX', ?_⟩
      intro e he
      exact ((hmem_iff e).mp he).2
    exact ⟨leastMap (funListOf P₀ P₁ el) hcons, leastMap_mem_stepFun hL hcons⟩

/-! ### Milestone 3a — deciding consistency of a finite index set via the
`inter`-chain.

To decide whether a finite list of neighbourhood indices `js` is *consistent* in
`𝒟` (i.e. whether
`⋂{X_j ∣ j ∈ js}` is a neighbourhood) we fold the presentation's
primitive-recursive `inter` along
`js`, starting from `masterIdx`, to obtain an index `idxchain js`. The crisp
characterization is:

> `js` is consistent **iff** `X_{idxchain js} ⊆ X_j` for every `j ∈ js`.

The point is that `X_{idxchain js}` is *always* a neighbourhood (`mem_X`), so if
it sits inside every
`X_j` it witnesses consistency; conversely, when consistent, `inter`'s spec (and
the fact that a
subset of a consistent set is consistent) makes the chain compute the genuine
intersection. This
replaces any consistency-flag bookkeeping by a single `inter`-fold plus a bounded
inclusion check —
all choice-free. -/

section ConsChain

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- The running intersection of `A` with the neighbourhoods `X_j` (`j ∈ js`),
left-accumulated to
match `List.foldl`. -/
def interFrom (A : Set α) : List ℕ → Set α
  | [] => A
  | j :: js => interFrom (A ∩ P.X j) js

theorem mem_interFrom {A : Set α} {js : List ℕ} {z : α} :
    z ∈ interFrom P A js ↔ z ∈ A ∧ ∀ j ∈ js, z ∈ P.X j := by
  induction js generalizing A with
  | nil => simp [interFrom]
  | cons j js ih =>
    rw [interFrom, ih]
    simp only [Set.mem_inter_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨hA, hj⟩, hrest⟩
      exact ⟨hA, fun j' hj' => hj'.elim (fun h => h ▸ hj) (hrest j')⟩
    · rintro ⟨hA, hall⟩
      exact ⟨⟨hA, hall j (Or.inl rfl)⟩, fun j' hj' => hall j' (Or.inr hj')⟩

theorem interFrom_subset {A : Set α} {js : List ℕ} : interFrom P A js ⊆ A :=
  fun _ hz => (mem_interFrom P |>.mp hz).1

/-- A finite running intersection with a neighbourhood inside it is itself a
neighbourhood. -/
theorem interFrom_mem_of_witness {A : Set α} {js : List ℕ} {Z : Set α}
    (hZ : V.mem Z) (hZsub : Z ⊆ interFrom P A js) (hA : V.mem A) :
    V.mem (interFrom P A js) := by
  induction js generalizing A with
  | nil => simpa [interFrom] using hA
  | cons j js ih =>
    rw [interFrom] at hZsub ⊢
    have hAXj : V.mem (A ∩ P.X j) :=
      V.inter_mem hA (P.mem_X j) hZ (hZsub.trans (interFrom_subset P))
    exact ih hZsub hAXj

/-- The fold of `inter` along `js` (starting from `a`, with `X a = A`) computes
the running
intersection `interFrom A js` — *provided* that intersection is consistent (so
each prefix is too, by
`inter_spec`). -/
theorem interFrom_eq_of_foldl : ∀ (js : List ℕ) (A : Set α) (a : ℕ),
    P.X a = A → V.mem A → V.mem (interFrom P A js) →
    P.X (js.foldl (fun acc j => P.inter acc j) a) = interFrom P A js
  | [], A, a, hXa, _, _ => by simpa [interFrom] using hXa
  | j :: js, A, a, hXa, hA, hmem => by
    have hmem' : V.mem (interFrom P (A ∩ P.X j) js) := by rwa [interFrom] at hmem
    have hAXj : V.mem (A ∩ P.X j) :=
      V.inter_mem hA (P.mem_X j) hmem' (interFrom_subset P)
    have hk : ∃ k, P.X k ⊆ P.X a ∩ P.X j := by
      obtain ⟨k, hk⟩ := P.surj hAXj
      exact ⟨k, by rw [hk, hXa]⟩
    have hXinter : P.X (P.inter a j) = A ∩ P.X j := by rw [P.inter_spec hk, hXa]
    rw [List.foldl_cons, interFrom]
    exact interFrom_eq_of_foldl js (A ∩ P.X j) (P.inter a j) hXinter hAXj hmem'

/-- The `inter`-chain index of `js`: `inter`-fold from `masterIdx`. -/
def idxchain (js : List ℕ) : ℕ := js.foldl (fun acc j => P.inter acc j) P.masterIdx

/-- When `js` is consistent, the `inter`-chain index genuinely indexes `⋂{X_j ∣ j
∈ js}`. -/
theorem idxchain_spec {js : List ℕ} (h : V.mem (interFrom P V.master js)) :
    P.X (idxchain P js) = interFrom P V.master js :=
  interFrom_eq_of_foldl P js V.master P.masterIdx P.masterIdx_spec V.master_mem h

/-- **Consistency via the `inter`-chain (choice-free).** A finite index set `js`
is consistent —
i.e.
`⋂{X_j ∣ j ∈ js}` is a neighbourhood — exactly when the always-a-neighbourhood
`X_{idxchain js}` sits
inside every `X_j` (`j ∈ js`). -/
theorem consChain_iff (js : List ℕ) :
    (∀ j ∈ js, P.X (idxchain P js) ⊆ P.X j) ↔ V.mem (interFrom P V.master js) := by
  constructor
  · intro hle
    have hsub : P.X (idxchain P js) ⊆ interFrom P V.master js := by
      intro z hz
      rw [mem_interFrom]
      exact ⟨V.sub_master (P.mem_X _) hz, fun j hj => hle j hj hz⟩
    exact interFrom_mem_of_witness P (P.mem_X _) hsub V.master_mem
  · intro hmem j hj
    rw [idxchain_spec P hmem]
    exact fun z hz => (mem_interFrom P |>.mp hz).2 j hj

end ConsChain

/-! ### Milestone 3b — bitmask sublist selection.

The eventual decider enumerates the *subsets* of an entry-list one **bit** at a
time: `bitSelect L b`
keeps the entries of `L` whose position is set in the binary expansion of `b` (low
bit = head). Every
sublist arises as some `bitSelect L b` with `b < 2 ^ L.length`
(`exists_bitSelect_lt`), so a
universal statement over sublists is a *bounded* universal statement over bitmasks
(`forall_sublist_iff_forall_bitmask`) — and bounded-`∀` of a recursively decidable
predicate is
recursively decidable (`RecDecidable.bForall`). All choice-free. -/

/-- The sublist of `L` selected by the bitmask `b` (low bit = head). -/
def bitSelect : List ℕ → ℕ → List ℕ
  | [], _ => []
  | e :: L, b => if b % 2 = 1 then e :: bitSelect L (b / 2) else bitSelect L (b / 2)

@[simp] theorem bitSelect_nil (b : ℕ) : bitSelect [] b = [] := rfl

theorem bitSelect_cons (e : ℕ) (L : List ℕ) (b : ℕ) :
    bitSelect (e :: L) b =
      if b % 2 = 1 then e :: bitSelect L (b / 2) else bitSelect L (b / 2) := rfl

theorem bitSelect_sublist (L : List ℕ) (b : ℕ) : (bitSelect L b).Sublist L := by
  induction L generalizing b with
  | nil => simp
  | cons e L ih =>
    rw [bitSelect_cons]
    split
    · exact (ih (b / 2)).cons_cons e
    · exact (ih (b / 2)).cons e

theorem exists_bitSelect_lt {L sub : List ℕ} (hsub : sub.Sublist L) :
    ∃ b, b < 2 ^ L.length ∧ bitSelect L b = sub := by
  induction hsub with
  | slnil => exact ⟨0, by rw [List.length_nil, pow_zero]; exact Nat.one_pos, rfl⟩
  | @cons l₁ l₂ e _h ih =>
    obtain ⟨b, hb, heq⟩ := ih
    refine ⟨2 * b, ?_, ?_⟩
    · have hpow : 2 ^ (l₂.length + 1) = 2 ^ l₂.length * 2 := pow_succ 2 l₂.length
      rw [List.length_cons]; omega
    · rw [bitSelect_cons, if_neg (by omega), show 2 * b / 2 = b by omega]; exact heq
  | @cons_cons l₁ l₂ e _h ih =>
    obtain ⟨b, hb, heq⟩ := ih
    refine ⟨2 * b + 1, ?_, ?_⟩
    · have hpow : 2 ^ (l₂.length + 1) = 2 ^ l₂.length * 2 := pow_succ 2 l₂.length
      rw [List.length_cons]; omega
    · rw [bitSelect_cons, if_pos (by omega), show (2 * b + 1) / 2 = b by omega]; rw [heq]

/-- A universal statement over all sublists of `decodeList c` is a *bounded*
universal over bitmasks
`b < 2 ^ c` (using `(decodeList c).length ≤ c`). -/
theorem forall_sublist_iff_forall_bitmask (c : ℕ) (p : List ℕ → Prop) :
    (∀ sub, sub.Sublist (decodeList c) → p sub) ↔
      ∀ b, b < 2 ^ c → p (bitSelect (decodeList c) b) := by
  constructor
  · intro hall b _; exact hall _ (bitSelect_sublist _ _)
  · intro hall sub hsub
    obtain ⟨b, hb, heq⟩ := exists_bitSelect_lt hsub
    have hb' : b < 2 ^ c :=
      Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (Nat.le_succ 1) (decodeList_length_le c))
    rw [← heq]; exact hall b hb'

/-! ### Milestone 3c — the single-pass consistency fold (`section ConsFold`,
generic over `P`).

To decide whether a *bitmask-selected* sublist of an index list is consistent, we
fold once over the
list threading a state `s = pair b (pair idx flag)`: `b` the remaining bitmask,
`idx` an index of the
running intersection `⋂{X_j ∣ j selected so far}`, and `flag ∈ {0,1}` recording
whether **every
prefix has been consistent**. At a selected entry we set `idx := P.inter idx
(projFn x)` and
`flag := flag ∧ [P.cons_computable says X_idx ∩ X_{projFn x} is consistent]`. The
headline
`consUpd_foldl_spec` shows the final flag is `1` iff the selected intersection is
a neighbourhood
(using `inter_spec` to keep `X_idx` exact along the consistent prefix, and the
fact that the *full*
intersection being a neighbourhood forces every prefix to be one). All
choice-free. -/

section ConsFold

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)

/-- One fold step (see the section doc). `projFn` extracts the relevant component
index from an
entry; `fc` is `P.cons_computable`'s `{0,1}` consistency tester. -/
def consUpd (projFn fc : ℕ → ℕ) (s x : ℕ) : ℕ :=
  selectFn (s.unpair.1 % 2)
    (Nat.pair (s.unpair.1 / 2)
      (Nat.pair (P.inter s.unpair.2.unpair.1 (projFn x))
        (selectFn s.unpair.2.unpair.2 (isOne (fc (Nat.pair s.unpair.2.unpair.1 (projFn x)))) 0)))
    (Nat.pair (s.unpair.1 / 2) (Nat.pair s.unpair.2.unpair.1 s.unpair.2.unpair.2))

theorem consUpd_eval (projFn fc : ℕ → ℕ) (b idx flag x : ℕ) :
    consUpd P projFn fc (Nat.pair b (Nat.pair idx flag)) x =
      selectFn (b % 2)
        (Nat.pair (b / 2)
          (Nat.pair (P.inter idx (projFn x))
            (selectFn flag (isOne (fc (Nat.pair idx (projFn x)))) 0)))
        (Nat.pair (b / 2) (Nat.pair idx flag)) := by
  unfold consUpd
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- Once the flag is `0`, the fold keeps it `0` (inconsistency persists). -/
theorem consUpd_foldl_flag_zero (projFn fc : ℕ → ℕ) (el : List ℕ) (b a : ℕ) :
    (List.foldl (fun s x => consUpd P projFn fc s x)
      (Nat.pair b (Nat.pair a 0)) el).unpair.2.unpair.2 = 0 := by
  induction el generalizing b a with
  | nil => simp only [List.foldl_nil, unpair_pair_snd]
  | cons e el ih =>
    rw [List.foldl_cons, consUpd_eval]
    by_cases hb : b % 2 = 1
    · rw [hb, selectFn_one, selectFn_zero]
      exact ih (b / 2) (P.inter a (projFn e))
    · rw [show b % 2 = 0 by omega, selectFn_zero]
      exact ih (b / 2) a

/-- **Single-pass consistency fold — correctness.** Starting from index `a` (an
index of `X a`) with
flag `1`, the final flag is `1` iff the running intersection of `X a` with the
selected components is
a neighbourhood. Choice-free. -/
theorem consUpd_foldl_spec (projFn fc : ℕ → ℕ)
    (hfc : ∀ s, fc s = 1 ↔ ∃ k, P.X k ⊆ P.X s.unpair.1 ∩ P.X s.unpair.2)
    (el : List ℕ) (b a : ℕ) :
    (List.foldl (fun s x => consUpd P projFn fc s x)
        (Nat.pair b (Nat.pair a 1)) el).unpair.2.unpair.2 = 1 ↔
      V.mem (interFrom P (P.X a) (List.map projFn (bitSelect el b))) := by
  induction el generalizing b a with
  | nil =>
    have hL : (List.foldl (fun s x => consUpd P projFn fc s x)
        (Nat.pair b (Nat.pair a 1)) []).unpair.2.unpair.2 = 1 := by
      simp only [List.foldl_nil, unpair_pair_snd]
    rw [bitSelect_nil, List.map_nil, show interFrom P (P.X a) [] = P.X a from rfl]
    exact iff_of_true hL (P.mem_X a)
  | cons e el ih =>
    rw [List.foldl_cons, consUpd_eval, bitSelect_cons]
    by_cases hb : b % 2 = 1
    · rw [if_pos hb, List.map_cons, hb, selectFn_one, selectFn_one,
        show interFrom P (P.X a) (projFn e :: List.map projFn (bitSelect el (b / 2)))
          = interFrom P (P.X a ∩ P.X (projFn e)) (List.map projFn (bitSelect el (b / 2))) from rfl]
      by_cases hfce : fc (Nat.pair a (projFn e)) = 1
      · have hcons : ∃ k, P.X k ⊆ P.X a ∩ P.X (projFn e) := by
          have h := (hfc (Nat.pair a (projFn e))).mp hfce
          rwa [unpair_pair_fst, unpair_pair_snd] at h
        have hXa' : P.X (P.inter a (projFn e)) = P.X a ∩ P.X (projFn e) := P.inter_spec hcons
        rw [(isOne_eq_one_iff _).mpr hfce, ih (b / 2) (P.inter a (projFn e)), hXa']
      · have his0 : isOne (fc (Nat.pair a (projFn e))) = 0 := by
          have hle := isOne_le_one (fc (Nat.pair a (projFn e)))
          rcases (show isOne (fc (Nat.pair a (projFn e))) = 0 ∨
              isOne (fc (Nat.pair a (projFn e))) = 1 by omega) with h | h
          · exact h
          · exact absurd ((isOne_eq_one_iff _).mp h) hfce
        rw [his0]
        constructor
        · intro h
          rw [consUpd_foldl_flag_zero P projFn fc el (b / 2) (P.inter a (projFn e))] at h
          exact absurd h (by decide)
        · intro h
          exact absurd
            ((hfc (Nat.pair a (projFn e))).mpr (by
              obtain ⟨k, hk⟩ := P.surj h
              rw [unpair_pair_fst, unpair_pair_snd]
              exact ⟨k, by rw [hk]; exact interFrom_subset P⟩))
            hfce
    · rw [if_neg hb, show b % 2 = 0 by omega, selectFn_zero]
      exact ih (b / 2) a

/-- `foldCode`-shaped wrapper of `consUpd` (state lives in `w.unpair.2.unpair.1`,
entry in
`w.unpair.1`). -/
def consStp (projFn fc : ℕ → ℕ) (w : ℕ) : ℕ :=
  consUpd P projFn fc w.unpair.2.unpair.1 w.unpair.1

/-- The `{0,1}` characteristic function of the bitmask-selected-sublist
consistency test, packaged
through `foldCode` so it is primitive recursive. Input `w = pair b c` (bitmask
`b`, list code `c`). -/
def consCharAt (projFn fc : ℕ → ℕ) (w : ℕ) : ℕ :=
  (foldCode (consStp P projFn fc) 0 (Nat.pair w.unpair.1 (Nat.pair P.masterIdx 1))
    w.unpair.2).unpair.2.unpair.2

theorem consCharAt_spec (projFn fc : ℕ → ℕ)
    (hfc : ∀ s, fc s = 1 ↔ ∃ k, P.X k ⊆ P.X s.unpair.1 ∩ P.X s.unpair.2) (w : ℕ) :
    consCharAt P projFn fc w = 1 ↔
      V.mem (interFrom P V.master
        (List.map projFn (bitSelect (decodeList w.unpair.2) w.unpair.1))) := by
  unfold consCharAt
  rw [foldCode_eq']
  have hstep : (fun acc x => consStp P projFn fc (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => consUpd P projFn fc acc x) := by
    funext acc x
    show consStp P projFn fc (Nat.pair x (Nat.pair acc 0)) = _
    unfold consStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, consUpd_foldl_spec P projFn fc hfc (decodeList w.unpair.2) w.unpair.1 P.masterIdx,
    P.masterIdx_spec]

theorem primrec_consStp {projFn fc : ℕ → ℕ} (hprojp : Nat.Primrec projFn) (hfcp : Nat.Primrec fc) :
    Nat.Primrec (consStp P projFn fc) := by
  have hb : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.left.comp Nat.Primrec.right)
  have hidx : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right))
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp (Nat.Primrec.left.comp Nat.Primrec.right))
  have hpx : Nat.Primrec (fun w : ℕ => projFn w.unpair.1) := hprojp.comp Nat.Primrec.left
  have hpair := hidx.pair hpx
  have hinter := P.inter_primrec.comp hpair
  have hfcv := primrec_isOne.comp (hfcp.comp hpair)
  have hsel := primrec_selectFn hflag hfcv (Nat.Primrec.const 0)
  have hyes := (primrec_div2.comp hb).pair (hinter.pair hsel)
  have hno := (primrec_div2.comp hb).pair (hidx.pair hflag)
  refine (primrec_selectFn (primrec_mod2.comp hb) hyes hno).of_eq (fun w => ?_)
  unfold consStp consUpd
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_consCharAt {projFn fc : ℕ → ℕ} (hprojp : Nat.Primrec projFn)
    (hfcp : Nat.Primrec fc) : Nat.Primrec (consCharAt P projFn fc) := by
  have hfold := primrec_foldCode (primrec_consStp P hprojp hfcp) (Nat.Primrec.const 0)
    (Nat.Primrec.left.pair ((Nat.Primrec.const P.masterIdx).pair (Nat.Primrec.const 1)))
    Nat.Primrec.right
  exact ((Nat.Primrec.right.comp Nat.Primrec.right).comp hfold).of_eq (fun _ => rfl)

/-- **Consistency of the bitmask-selected sublist is recursively decidable.**
Choice-free. -/
theorem consFold_decidable (projFn fc : ℕ → ℕ)
    (hfc : ∀ s, fc s = 1 ↔ ∃ k, P.X k ⊆ P.X s.unpair.1 ∩ P.X s.unpair.2)
    (hprojp : Nat.Primrec projFn) (hfcp : Nat.Primrec fc) :
    RecDecidable (fun w =>
      V.mem (interFrom P V.master
        (List.map projFn (bitSelect (decodeList w.unpair.2) w.unpair.1)))) :=
  ⟨consCharAt P projFn fc, primrec_consCharAt P hprojp hfcp,
    fun w => (consCharAt_spec P projFn fc hfc w).symm⟩

end ConsFold

/-! ### Milestone 3d — assembling the function-space consistency decider
`funCons_decidable`.

`stepFun_funListOf_nonempty_iff` (Milestone 2) characterises non-emptiness as a
universal statement
over sublists; `forall_sublist_iff_forall_bitmask` turns it into a *bounded*
universal over bitmasks
`b < 2^c`; `antecedent_cons_iff` / `funConsequent_eq` rewrite the per-bitmask
antecedent and
consequent into the `interFrom` form decided by `consFold_decidable`. The
implication of two
recursively decidable predicates is recursively decidable (`.not`/`.or`/`.em`,
choice-free), and a
bounded universal of a recursively decidable predicate is recursively decidable
(`RecDecidable.bForall`). -/

/-- `interList` over `js.map X` is the same set as the `interFrom`-chain over
`js`. -/
theorem interList_X_eq_interFrom {V : NeighborhoodSystem α} (P : ComputablePresentation V)
    (js : List ℕ) : interList V.master (js.map (fun j => P.X j)) = interFrom P V.master js := by
  apply Set.ext; intro z
  rw [mem_interList, mem_interFrom]
  constructor
  · rintro ⟨hb, hall⟩
    exact ⟨hb, fun j hj => hall (P.X j) (List.mem_map.mpr ⟨j, hj, rfl⟩)⟩
  · rintro ⟨hb, hall⟩
    refine ⟨hb, fun Y hY => ?_⟩
    rw [List.mem_map] at hY
    obtain ⟨j, hj, rfl⟩ := hY
    exact hall j hj

/-- The antecedent of Prop 3.9(i) — `{X_{e.1} ∣ e ∈ sub}` admits a common lower
neighbourhood — is
exactly consistency of `{e.1 ∣ e ∈ sub}` in `𝒟₀` (in `interFrom` form).
Choice-free. -/
theorem antecedent_cons_iff (sub : List ℕ) :
    (∃ Z, V₀.mem Z ∧ ∀ e ∈ sub, Z ⊆ P₀.X e.unpair.1) ↔
      V₀.mem (interFrom P₀ V₀.master (sub.map (fun e => e.unpair.1))) := by
  constructor
  · rintro ⟨Z, hZ, hZle⟩
    refine interFrom_mem_of_witness P₀ hZ (fun z hz => ?_) V₀.master_mem
    rw [mem_interFrom]
    refine ⟨V₀.sub_master hZ hz, fun j hj => ?_⟩
    rw [List.mem_map] at hj
    obtain ⟨e, he, rfl⟩ := hj
    exact hZle e he hz
  · intro hmem
    refine ⟨P₀.X (idxchain P₀ (sub.map (fun e => e.unpair.1))), P₀.mem_X _, fun e he z hz => ?_⟩
    have hj : e.unpair.1 ∈ sub.map (fun e => e.unpair.1) := List.mem_map.mpr ⟨e, he, rfl⟩
    rw [idxchain_spec P₀ hmem] at hz
    exact (mem_interFrom P₀ |>.mp hz).2 _ hj

/-- The consequent of Prop 3.9(i), rewritten from `interList` to `interFrom` form. -/
theorem funConsequent_eq (sub : List ℕ) :
    interList V₁.master (sub.map (fun e => P₁.X e.unpair.2))
      = interFrom P₁ V₁.master (sub.map (fun e => e.unpair.2)) := by
  rw [← interList_X_eq_interFrom P₁, List.map_map]; rfl

/-- **Proposition 3.9(i) as a bounded bitmask quantifier.** The function-space
neighbourhood
coded by
`decodeList c` is non-empty iff for every bitmask `b < 2^c`, consistency of the
selected inputs in
`𝒟₀` forces consistency of the selected outputs in `𝒟₁`. Choice-free. -/
theorem funCons_iff (c : ℕ) :
    (stepFun (funListOf P₀ P₁ (decodeList c)) : Set (ApproximableMap V₀ V₁)).Nonempty ↔
      ∀ b, b < 2 ^ c →
        V₀.mem (interFrom P₀ V₀.master ((bitSelect (decodeList c) b).map (fun e => e.unpair.1))) →
          V₁.mem (interFrom P₁ V₁.master ((bitSelect (decodeList c) b).map (fun e =>
            e.unpair.2))) := by
  rw [stepFun_funListOf_nonempty_iff]
  constructor
  · intro h b hb hant0
    have hsub : (bitSelect (decodeList c) b).Sublist (decodeList c) := bitSelect_sublist _ _
    have hcons := h _ hsub ((antecedent_cons_iff P₀ (bitSelect (decodeList c) b)).mpr hant0)
    rwa [funConsequent_eq P₁] at hcons
  · intro h sub hsub hant
    obtain ⟨b, hb, heq⟩ := exists_bitSelect_lt hsub
    have hb' : b < 2 ^ c :=
      Nat.lt_of_lt_of_le hb (Nat.pow_le_pow_right (Nat.le_succ 1) (decodeList_length_le c))
    have hcons := h b hb' (by rw [heq]; exact (antecedent_cons_iff P₀ sub).mp hant)
    rw [heq, ← funConsequent_eq P₁] at hcons
    exact hcons

/-- **The function-space consistency relation is recursively decidable.** Given
the binary
consistency deciders `fc0`/`fc1` of the two presentations, `(stepFun (funListOf
(decodeList c)))` is
non-empty is recursively decidable in `c`. Choice-free. -/
theorem funCons_decidable (fc0 fc1 : ℕ → ℕ)
    (hfc0 : ∀ s, fc0 s = 1 ↔ ∃ k, P₀.X k ⊆ P₀.X s.unpair.1 ∩ P₀.X s.unpair.2)
    (hfc1 : ∀ s, fc1 s = 1 ↔ ∃ k, P₁.X k ⊆ P₁.X s.unpair.1 ∩ P₁.X s.unpair.2)
    (hfc0p : Nat.Primrec fc0) (hfc1p : Nat.Primrec fc1) :
    RecDecidable (fun c =>
      (stepFun (funListOf P₀ P₁ (decodeList c)) : Set (ApproximableMap V₀ V₁)).Nonempty) := by
  have hc0 := consFold_decidable P₀ (fun e => e.unpair.1) fc0 hfc0 Nat.Primrec.left hfc0p
  have hc1 := consFold_decidable P₁ (fun e => e.unpair.2) fc1 hfc1 Nat.Primrec.right hfc1p
  have himp : RecDecidable (fun w =>
      V₀.mem (interFrom P₀ V₀.master
          (List.map (fun e => e.unpair.1) (bitSelect (decodeList w.unpair.2) w.unpair.1))) →
        V₁.mem (interFrom P₁ V₁.master
          (List.map (fun e => e.unpair.2) (bitSelect (decodeList w.unpair.2) w.unpair.1)))) := by
    refine RecDecidable.of_iff (fun w => ?_) (hc0.not.or hc1)
    constructor
    · intro himp
      rcases hc0.em w with h0 | h0
      · exact Or.inr (himp h0)
      · exact Or.inl h0
    · rintro (h0 | h1) hp0
      · exact absurd hp0 h0
      · exact h1
  refine RecDecidable.of_iff (fun c => ?_)
    (himp.bForall (bound := fun n => 2 ^ n) (primrec_two_pow primrec_id))
  rw [funCons_iff P₀ P₁ c]
  simp only [unpair_pair_fst, unpair_pair_snd]

/-! ### Milestone 4 — `appendCode` (list append on entry codes).

`X n ∩ X m = stepFun (L_n ++ L_m)`, so the presentation's `inter` will splice two
entry-lists. We
fold one code onto another (prepending each entry), giving `appendCode a b` whose
decoded list is
`(decodeList b).reverse ++ decodeList a`; since `stepFun` is an *intersection*
(order- and
duplicate-invariant), this codes `X a ∩ X b` regardless of the reversal. All
choice-free. -/

/-- Prepend the entry `x` onto the list coded by `acc`. -/
def appendStep (acc x : ℕ) : ℕ := Nat.pair x acc + 1

/-- `foldCode`-shaped wrapper of `appendStep`. -/
def appendStp (w : ℕ) : ℕ := appendStep w.unpair.2.unpair.1 w.unpair.1

theorem appendStp_eq (x acc : ℕ) : appendStp (Nat.pair x (Nat.pair acc 0)) = appendStep acc x := by
  unfold appendStp; simp only [unpair_pair_fst, unpair_pair_snd]

theorem decodeList_appendStep (acc x : ℕ) :
    decodeList (appendStep acc x) = x :: decodeList acc := by
  unfold appendStep; rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd]

theorem decodeList_foldl_appendStp (el : List ℕ) (acc : ℕ) :
    decodeList (List.foldl (fun acc x => appendStp (Nat.pair x (Nat.pair acc 0))) acc el)
      = el.reverse ++ decodeList acc := by
  induction el generalizing acc with
  | nil => simp
  | cons e el ih =>
    rw [List.foldl_cons, ih, appendStp_eq, decodeList_appendStep, List.reverse_cons,
      List.append_assoc, List.singleton_append]

/-- **`appendCode a b`** codes `(decodeList b).reverse ++ decodeList a`. -/
def appendCode (a b : ℕ) : ℕ := foldCode appendStp 0 a b

theorem decodeList_appendCode (a b : ℕ) :
    decodeList (appendCode a b) = (decodeList b).reverse ++ decodeList a := by
  unfold appendCode; rw [foldCode_eq']; exact decodeList_foldl_appendStp (decodeList b) a

theorem primrec_appendCode : Nat.Primrec (fun t => appendCode t.unpair.1 t.unpair.2) := by
  have hstp : Nat.Primrec appendStp :=
    (primrec_add₂ (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right))
      (Nat.Primrec.const 1)).of_eq (fun w => rfl)
  exact (primrec_foldCode hstp (Nat.Primrec.const 0) Nat.Primrec.left Nat.Primrec.right).of_eq
    (fun t => rfl)

theorem funListOf_append (la lb : List ℕ) :
    funListOf P₀ P₁ (la ++ lb) = funListOf P₀ P₁ la ++ funListOf P₀ P₁ lb := by
  simp [funListOf, List.map_append]

/-- `stepFun (funListOf (decodeList (appendCode a b)))` is exactly `X a ∩ X b` at
the level of the
underlying step-intersections. -/
theorem stepFun_funListOf_appendCode (a b : ℕ) :
    (stepFun (funListOf P₀ P₁ (decodeList (appendCode a b))) : Set (ApproximableMap V₀ V₁)) =
      stepFun (funListOf P₀ P₁ (decodeList a)) ∩ stepFun (funListOf P₀ P₁ (decodeList b)) := by
  ext f
  rw [decodeList_appendCode]
  simp only [funListOf, List.map_append, List.map_reverse, mem_stepFun, Set.mem_inter_iff,
    List.mem_append, List.mem_reverse]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inr hp), fun p hp => h p (Or.inl hp)⟩
  · rintro ⟨ha, hb⟩ p (hp | hp)
    · exact hb p hp
    · exact ha p hp

/-! ### Milestone 5 — the function-space inclusion characterization (choice-free).

`stepFun La ⊆ stepFun Lb iff ∀ (X',Y') ∈ Lb, ⋂{Y ∣ X' ⊆ X, (X,Y)∈La} ⊆ Y'` (Scott,
via the least map
`leastMap`/3.9(ii)). The forward direction is choice-free (test the least map).
The backward direction
needs `f.rel X' (interYs Δ₁ La X')` for arbitrary `f ∈ stepFun La` — the library
`rel_interYs` proves
this *classically* (`by_cases X' ⊆ Xᵢ`), so we **re-prove it choice-free** for the
presented list
`funListOf el`, replacing the case split by `P₀.incl_computable`'s recursive
decidability (`.em`). -/

theorem funListOf_cons (e : ℕ) (el : List ℕ) :
    funListOf P₀ P₁ (e :: el) = funPair P₀ P₁ e :: funListOf P₀ P₁ el := rfl

/-- **Choice-free `rel_interYs` for a presented list.** Any `f ∈ stepFun
(funListOf el)` relates
each
`X₀_{n'}` to the intersection of the relevant outputs `interYs Δ₁ (funListOf el)
(X₀_{n'})`. The
case split on `X₀_{n'} ⊆ X₀_{e.1}` is discharged by `P₀.incl_computable.em` (no
`Classical.choice`). -/
theorem rel_interYs_funList {f : ApproximableMap V₀ V₁} {el : List ℕ}
    (hf : f ∈ stepFun (funListOf P₀ P₁ el)) (n' : ℕ) :
    f.rel (P₀.X n') (interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n')) := by
  induction el with
  | nil =>
    rw [funListOf, List.map_nil, interYs_nil]
    exact f.mono f.master_rel (V₀.sub_master (P₀.mem_X n')) subset_rfl (P₀.mem_X n') V₁.master_mem
  | cons e el ih =>
    rw [funListOf_cons] at hf
    have hftail : f ∈ stepFun (funListOf P₀ P₁ el) :=
      fun p hp => hf p (List.mem_cons_of_mem _ hp)
    have htail := ih hftail
    rw [funListOf_cons]
    rcases P₀.incl_computable.em (Nat.pair n' e.unpair.1) with hinc | hinc <;>
      simp only [unpair_pair_fst, unpair_pair_snd] at hinc
    · have hp : f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2) :=
        hf (funPair P₀ P₁ e) (List.mem_cons.mpr (Or.inl rfl))
      have hXp2 : f.rel (P₀.X n') (P₁.X e.unpair.2) :=
        f.mono hp hinc subset_rfl (P₀.mem_X n') (f.rel_cod hp)
      have heq : interYs V₁.master (funPair P₀ P₁ e :: funListOf P₀ P₁ el) (P₀.X n')
          = P₁.X e.unpair.2 ∩ interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n') := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, funPair]
        exact ⟨fun ⟨h1, h2⟩ => ⟨h1 hinc, h2⟩, fun ⟨h1, h2⟩ => ⟨fun _ => h1, h2⟩⟩
      rw [heq]; exact f.inter_right hXp2 htail
    · have heq : interYs V₁.master (funPair P₀ P₁ e :: funListOf P₀ P₁ el) (P₀.X n')
          = interYs V₁.master (funListOf P₀ P₁ el) (P₀.X n') := by
        rw [interYs_cons]; ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, funPair]
        exact ⟨fun h => h.2, fun h => ⟨fun hc => absurd hc hinc, h⟩⟩
      rw [heq]; exact htail

/-- If `stepFun (funListOf ea)` is non-empty, then `interYs Δ₁ (funListOf ea) X`
is a
neighbourhood of
`𝒟₁` for every `X ∈ 𝒟₀` (the consistency hypothesis needed by `leastMap`).
Choice-free. -/
theorem interYs_funList_mem_of_nonempty {ea : List ℕ}
    (h : (stepFun (funListOf P₀ P₁ ea) : Set (ApproximableMap V₀ V₁)).Nonempty)
    {X : Set α} (hX : V₀.mem X) :
    V₁.mem (interYs V₁.master (funListOf P₀ P₁ ea) X) := by
  obtain ⟨n', hn'⟩ := P₀.surj hX
  obtain ⟨f, hf⟩ := h
  have hr := rel_interYs_funList P₀ P₁ hf n'
  rw [hn'] at hr
  exact f.rel_cod hr

/-- **Function-space inclusion characterisation (choice-free).** With `ea`
consistent (so the least
map exists), `stepFun (funListOf ea) ⊆ stepFun (funListOf eb)` iff for every entry
`e' ∈ eb`, the
intersection of the `ea`-outputs relevant to the input `X₀_{e'.1}` is contained in
`X₁_{e'.2}`. -/
theorem stepFun_funListOf_subset_iff {ea eb : List ℕ}
    (hcons : ∀ {X : Set α}, V₀.mem X → V₁.mem (interYs V₁.master (funListOf P₀ P₁ ea) X)) :
    (stepFun (funListOf P₀ P₁ ea) : Set (ApproximableMap V₀ V₁)) ⊆ stepFun (funListOf P₀ P₁ eb) ↔
      ∀ e' ∈ eb, interYs V₁.master (funListOf P₀ P₁ ea) (P₀.X e'.unpair.1) ⊆ P₁.X e'.unpair.2 := by
  have hL : ∀ p ∈ funListOf P₀ P₁ ea, V₀.mem p.1 ∧ V₁.mem p.2 := funListOf_valid P₀ P₁ ea
  constructor
  · intro hsub e' he'
    have hmem := hsub (leastMap_mem_stepFun hL hcons)
    have hrel := hmem (funPair P₀ P₁ e') (List.mem_map.mpr ⟨e', he', rfl⟩)
    exact (leastMap_rel.mp hrel).2.2
  · intro hcond f hf p hp
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e', he', rfl⟩ := hp
    change f.rel (P₀.X e'.unpair.1) (P₁.X e'.unpair.2)
    exact f.mono (rel_interYs_funList P₀ P₁ hf e'.unpair.1) subset_rfl (hcond e' he')
      (P₀.mem_X _) (P₁.mem_X _)

/-! ### Milestone 5b — the function-space inclusion / equality / consistency
deciders.

We now turn the choice-free characterization of Milestone 5a into recursive
deciders for the
function-space presentation. Two small generic facts first; then the
`interYs`-index fold (a
*conditional* `inter`-chain over `𝒟₁`, gated by the decidable `𝒟₀`-inclusion
test); then the
deciders themselves. All choice-free. -/

/-- `selectFn` driven by `isOne` is a `Nat`-equality `if` (choice-free; `decEq` on
`ℕ`). -/
theorem selectFn_isOne (v a b : ℕ) : selectFn (isOne v) a b = if v = 1 then a else b := by
  by_cases h : v = 1
  · rw [if_pos h, h, (isOne_eq_one_iff 1).mpr rfl, selectFn_one]
  · rw [if_neg h]
    have h0 : isOne v = 0 := by
      rcases (show isOne v = 0 ∨ isOne v = 1 from by have := isOne_le_one v; omega) with h0 | h1
      · exact h0
      · exact absurd ((isOne_eq_one_iff v).mp h1) h
    rw [h0, selectFn_zero]

/-- `decodeList` inverts `encodeList`: every list is the decoding of its code. -/
theorem decodeList_encodeList (l : List ℕ) : decodeList (encodeList l) = l := by
  induction l with
  | nil => rw [show encodeList ([] : List ℕ) = 0 from rfl, decodeList_zero]
  | cons a l ih =>
    rw [show encodeList (a :: l) = Nat.pair a (encodeList l) + 1 from rfl,
      decodeList_succ, unpair_pair_fst, unpair_pair_snd, ih]

/-! #### The `interYs`-index fold: a conditional `inter`-chain over `𝒟₁`.

For a presented list `funListOf (decodeList a)` and a `𝒟₀`-index `k`, the set
`interYs Δ₁ (funListOf (decodeList a)) (X₀_k)` is the intersection of the outputs
`X₁_{e.2}` over the
entries `e` of `decodeList a` whose input dominates `X₀_k` (`X₀_k ⊆ X₀_{e.1}`). We
compute an index of
it by folding `P₁.inter` over `decodeList a`, intersecting at an entry exactly
when the (decidable)
inclusion test fires. `condSet k A el` is the running set; `interYsFoldl_spec` is
the index
correctness (when the result is consistent), mirroring `interFrom_eq_of_foldl`. -/

/-- The running set of the conditional `inter`-chain: `A` intersected with the
outputs `X₁_{e.2}` of
the entries `e ∈ el` whose input dominates `X₀_k`. -/
def condSet (k : ℕ) (A : Set β) (el : List ℕ) : Set β :=
  {z | z ∈ A ∧ ∀ e ∈ el, P₀.X k ⊆ P₀.X e.unpair.1 → z ∈ P₁.X e.unpair.2}

theorem mem_condSet {k : ℕ} {A : Set β} {el : List ℕ} {z : β} :
    z ∈ condSet P₀ P₁ k A el ↔ z ∈ A ∧ ∀ e ∈ el, P₀.X k ⊆ P₀.X e.unpair.1 → z ∈ P₁.X e.unpair.2 :=
  Iff.rfl

theorem condSet_nil (k : ℕ) (A : Set β) : condSet P₀ P₁ k A [] = A := by
  ext z; simp [condSet]

theorem condSet_subset (k : ℕ) (A : Set β) (el : List ℕ) : condSet P₀ P₁ k A el ⊆ A :=
  fun _ hz => hz.1

/-- `condSet` cons-step when the input dominates the head entry's input: intersect
`A` with the
head's output. -/
theorem condSet_cons_pos {k : ℕ} {A : Set β} {e : ℕ} {el : List ℕ}
    (h : P₀.X k ⊆ P₀.X e.unpair.1) :
    condSet P₀ P₁ k A (e :: el) = condSet P₀ P₁ k (A ∩ P₁.X e.unpair.2) el := by
  ext z
  simp only [mem_condSet, List.mem_cons, Set.mem_inter_iff]
  constructor
  · rintro ⟨hzA, hall⟩
    exact ⟨⟨hzA, hall e (Or.inl rfl) h⟩, fun e' he' hsub => hall e' (Or.inr he') hsub⟩
  · rintro ⟨⟨hzA, hzE⟩, hall⟩
    exact ⟨hzA, fun e' he' hsub => he'.elim (fun heq => heq ▸ hzE) (fun hmem => hall e' hmem hsub)⟩

/-- `condSet` cons-step when the input does not dominate the head entry's input:
drop the head. -/
theorem condSet_cons_neg {k : ℕ} {A : Set β} {e : ℕ} {el : List ℕ}
    (h : ¬ P₀.X k ⊆ P₀.X e.unpair.1) :
    condSet P₀ P₁ k A (e :: el) = condSet P₀ P₁ k A el := by
  ext z
  simp only [mem_condSet, List.mem_cons]
  constructor
  · rintro ⟨hzA, hall⟩
    exact ⟨hzA, fun e' he' hsub => hall e' (Or.inr he') hsub⟩
  · rintro ⟨hzA, hall⟩
    exact ⟨hzA, fun e' he' hsub => he'.elim (fun heq => absurd (heq ▸ hsub) h) (
      fun hmem => hall e' hmem hsub)⟩

/-- `condSet k Δ₁ el` is exactly `interYs Δ₁ (funListOf el) (X₀_k)`. -/
theorem condSet_eq_interYs (k : ℕ) (el : List ℕ) :
    condSet P₀ P₁ k V₁.master el = interYs V₁.master (funListOf P₀ P₁ el) (P₀.X k) := by
  ext z
  rw [mem_interYs, mem_condSet]
  constructor
  · rintro ⟨hz, hall⟩
    refine ⟨hz, ?_⟩
    intro p hp hsub
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact hall e he hsub
  · rintro ⟨hz, hall⟩
    exact ⟨hz, fun e he hsub => hall (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩) hsub⟩

/-- One step of the `interYs`-index fold. State `pair entry (pair acc k)`: entry
`e = w.unpair.1`,
running `𝒟₁`-index `acc = w.unpair.2.unpair.1`, input index `k =
w.unpair.2.unpair.2` (the
`foldCode` parameter). Intersects `acc` with `e`'s output index when the inclusion
test fires. -/
def interYsStp (incl0 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn (isOne (incl0 (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1)))
    (P₁.inter w.unpair.2.unpair.1 w.unpair.1.unpair.2) w.unpair.2.unpair.1

/-- The index of `interYs Δ₁ (funListOf (decodeList a)) (X₀_k)`: a conditional
`inter`-fold over
`decodeList a` from `masterIdx`, with `k` carried as the `foldCode` parameter. -/
def interYsIdx (incl0 : ℕ → ℕ) (a k : ℕ) : ℕ :=
  foldCode (interYsStp P₁ incl0) k P₁.masterIdx a

/-- Correctness of the conditional `inter`-fold (`if`-form). When the running set
is consistent, the
fold computes an index of it, by induction with `inter_spec` (mirrors
`interFrom_eq_of_foldl`). -/
theorem condFoldl_spec (incl0 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (k : ℕ) :
    ∀ (el : List ℕ) (A : Set β) (a : ℕ), P₁.X a = A → V₁.mem A →
      V₁.mem (condSet P₀ P₁ k A el) →
      P₁.X (List.foldl (fun acc x => if incl0 (Nat.pair k x.unpair.1) = 1
              then P₁.inter acc x.unpair.2 else acc) a el) = condSet P₀ P₁ k A el
  | [], A, a, hXa, _, _ => by rw [List.foldl_nil, condSet_nil]; exact hXa
  | e :: el, A, a, hXa, hA, hcons => by
    rw [List.foldl_cons]
    by_cases hpred : incl0 (Nat.pair k e.unpair.1) = 1
    · rw [if_pos hpred]
      have hincl : P₀.X k ⊆ P₀.X e.unpair.1 := by
        have h := (hincl0 (Nat.pair k e.unpair.1)).mp hpred
        rwa [unpair_pair_fst, unpair_pair_snd] at h
      rw [condSet_cons_pos P₀ P₁ hincl] at hcons ⊢
      have hwit : V₁.mem (A ∩ P₁.X e.unpair.2) :=
        V₁.inter_mem hA (P₁.mem_X _) hcons (condSet_subset P₀ P₁ k (A ∩ P₁.X e.unpair.2) el)
      have hk : ∃ j, P₁.X j ⊆ P₁.X a ∩ P₁.X e.unpair.2 := by
        obtain ⟨j, hj⟩ := P₁.surj hwit; exact ⟨j, by rw [hj, hXa]⟩
      have hXinter : P₁.X (P₁.inter a e.unpair.2) = A ∩ P₁.X e.unpair.2 := by
        rw [P₁.inter_spec hk, hXa]
      exact condFoldl_spec incl0 hincl0 k el (A ∩ P₁.X e.unpair.2) (P₁.inter a e.unpair.2)
        hXinter hwit hcons
    · rw [if_neg hpred]
      have hincl : ¬ P₀.X k ⊆ P₀.X e.unpair.1 := fun hc =>
        hpred ((hincl0 (Nat.pair k e.unpair.1)).mpr (by rwa [unpair_pair_fst, unpair_pair_snd]))
      rw [condSet_cons_neg P₀ P₁ hincl] at hcons ⊢
      exact condFoldl_spec incl0 hincl0 k el A a hXa hA hcons

/-- **`interYsIdx` indexes `interYs Δ₁ (funListOf (decodeList a)) (X₀_k)`** (when
that is
consistent,
which it is whenever `stepFun (funListOf (decodeList a))` is non-empty).
Choice-free. -/
theorem interYsIdx_spec (incl0 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (a k : ℕ)
    (hcons : V₁.mem (interYs V₁.master (funListOf P₀ P₁ (decodeList a)) (P₀.X k))) :
    P₁.X (interYsIdx P₁ incl0 a k)
      = interYs V₁.master (funListOf P₀ P₁ (decodeList a)) (P₀.X k) := by
  unfold interYsIdx
  rw [foldCode_eq']
  have hstep : (fun acc x => interYsStp P₁ incl0 (Nat.pair x (Nat.pair acc k)))
      = (fun acc x => if incl0 (Nat.pair k x.unpair.1) = 1
            then P₁.inter acc x.unpair.2 else acc) := by
    funext acc x
    show interYsStp P₁ incl0 (Nat.pair x (Nat.pair acc k)) = _
    unfold interYsStp
    simp only [unpair_pair_fst, unpair_pair_snd]
    exact selectFn_isOne _ _ _
  rw [hstep]
  rw [← condSet_eq_interYs P₀ P₁ k (decodeList a)] at hcons ⊢
  exact condFoldl_spec P₀ P₁ incl0 hincl0 k (decodeList a) V₁.master P₁.masterIdx
    P₁.masterIdx_spec V₁.master_mem hcons

theorem primrec_interYsStp (incl0 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0) :
    Nat.Primrec (interYsStp P₁ incl0) := by
  have he1 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hacc : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcond := primrec_isOne.comp (hincl0p.comp (hk.pair he1))
  have hinter := P₁.inter_primrec.comp (hacc.pair he2)
  refine (primrec_selectFn hcond hinter hacc).of_eq (fun w => ?_)
  unfold interYsStp
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_interYsIdx (incl0 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0) :
    Nat.Primrec (fun t => interYsIdx P₁ incl0 t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_interYsStp P₁ incl0 hincl0p) Nat.Primrec.right
    (Nat.Primrec.const P₁.masterIdx) Nat.Primrec.left).of_eq (fun _ => rfl)

/-! #### A concrete `{0,1}` characteristic function for function-space
consistency.

`funCons_decidable` already shows consistency is recursively decidable, but to use
it in *data* (the
function-space enumeration branches on it) we need a *concrete*
primitive-recursive char rather than
one extracted from an existential (extraction needs choice). We build it
explicitly from the
component presentations' consistency chars `fc0`/`fc1`, and prove its spec via
`funCons_iff`. -/

/-- `selectFn A B 1 = 1` decides the implication `A = 1 → B = 1` for `A ∈ {0,1}`. -/
theorem selectFn_one_iff_imp {A B : ℕ} (hA : A ≤ 1) :
    selectFn A B 1 = 1 ↔ (A = 1 → B = 1) := by
  rcases (show A = 0 ∨ A = 1 by omega) with h | h <;> subst h
  · rw [selectFn_zero]; simp
  · rw [selectFn_one]; simp

/-- The per-bitmask implication char: `cons₀(selected inputs) → cons₁(selected
outputs)`. -/
def funImpChar (fc0 fc1 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn (isOne (consCharAt P₀ (fun e => e.unpair.1) fc0 w))
    (isOne (consCharAt P₁ (fun e => e.unpair.2) fc1 w)) 1

/-- The concrete `{0,1}` characteristic function of function-space consistency. -/
def funConsChar (fc0 fc1 : ℕ → ℕ) (c : ℕ) : ℕ :=
  bForallFn (funImpChar P₀ P₁ fc0 fc1) c (2 ^ c)

theorem funConsChar_spec (fc0 fc1 : ℕ → ℕ)
    (hfc0 : ∀ s, fc0 s = 1 ↔ ∃ k, P₀.X k ⊆ P₀.X s.unpair.1 ∩ P₀.X s.unpair.2)
    (hfc1 : ∀ s, fc1 s = 1 ↔ ∃ k, P₁.X k ⊆ P₁.X s.unpair.1 ∩ P₁.X s.unpair.2) (c : ℕ) :
    funConsChar P₀ P₁ fc0 fc1 c = 1 ↔
      (stepFun (funListOf P₀ P₁ (decodeList c)) : Set (ApproximableMap V₀ V₁)).Nonempty := by
  rw [funCons_iff P₀ P₁ c]
  unfold funConsChar
  rw [bForallFn_eq_one_iff]
  refine forall_congr' (fun b => ?_)
  refine imp_congr_right (fun hb => ?_)
  unfold funImpChar
  rw [selectFn_one_iff_imp (isOne_le_one _), isOne_eq_one_iff, isOne_eq_one_iff,
    consCharAt_spec P₀ (fun e => e.unpair.1) fc0 hfc0,
    consCharAt_spec P₁ (fun e => e.unpair.2) fc1 hfc1]
  simp only [unpair_pair_fst, unpair_pair_snd]

theorem primrec_funImpChar (fc0 fc1 : ℕ → ℕ) (hfc0p : Nat.Primrec fc0) (hfc1p : Nat.Primrec fc1) :
    Nat.Primrec (funImpChar P₀ P₁ fc0 fc1) :=
  primrec_selectFn (primrec_isOne.comp (primrec_consCharAt P₀ Nat.Primrec.left hfc0p))
    (primrec_isOne.comp (primrec_consCharAt P₁ Nat.Primrec.right hfc1p)) (Nat.Primrec.const 1)

theorem primrec_funConsChar (fc0 fc1 : ℕ → ℕ) (hfc0p : Nat.Primrec fc0) (hfc1p : Nat.Primrec fc1) :
    Nat.Primrec (funConsChar P₀ P₁ fc0 fc1) := by
  have hgp := primrec_funImpChar P₀ P₁ fc0 fc1 hfc0p hfc1p
  have hGfn : Nat.Primrec (fun w => selectFn w.unpair.2.unpair.2
      (isOne (funImpChar P₀ P₁ fc0 fc1 (Nat.pair w.unpair.2.unpair.1 w.unpair.1))) 0) :=
    primrec_selectFn (Nat.Primrec.right.comp Nat.Primrec.right)
      (primrec_isOne.comp (hgp.comp
        ((Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left)))
      (Nat.Primrec.const 0)
  have hprec := Nat.Primrec.prec (Nat.Primrec.const 1) hGfn
  refine (hprec.comp (primrec_id.pair (primrec_two_pow primrec_id))).of_eq (fun c => ?_)
  show _ = funConsChar P₀ P₁ fc0 fc1 c
  unfold funConsChar bForallFn
  simp only [Nat.unpaired, unpair_pair_fst, unpair_pair_snd, id_eq]

/-! #### A generic list-`AND` and the `stepFun`-inclusion decider `subChar`. -/

/-- A `{0,1}` left-fold `AND` of `isOne ∘ g` over a list, started from `a ∈
{0,1}`. -/
theorem andFoldl_eq_one_iff (g : ℕ → ℕ) :
    ∀ (el : List ℕ) (a : ℕ), a ≤ 1 →
      (List.foldl (fun acc x => selectFn acc (isOne (g x)) 0) a el = 1 ↔
        a = 1 ∧ ∀ e ∈ el, g e = 1)
  | [], a, _ => by simp
  | e :: el, a, ha => by
    rw [List.foldl_cons]
    have hstep : selectFn a (isOne (g e)) 0 ≤ 1 := by
      rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> subst h
      · rw [selectFn_zero]; exact Nat.zero_le 1
      · rw [selectFn_one]; exact isOne_le_one _
    rw [andFoldl_eq_one_iff g el _ hstep]
    rcases (show a = 0 ∨ a = 1 by omega) with h | h <;> subst h
    · rw [selectFn_zero]; simp
    · rw [selectFn_one, List.forall_mem_cons, isOne_eq_one_iff]
      constructor
      · rintro ⟨hge, hall⟩; exact ⟨rfl, hge, hall⟩
      · rintro ⟨_, hge, hall⟩; exact ⟨hge, hall⟩

theorem andFoldl_one (g : ℕ → ℕ) (el : List ℕ) :
    List.foldl (fun acc x => selectFn acc (isOne (g x)) 0) 1 el = 1 ↔ ∀ e ∈ el, g e = 1 := by
  rw [andFoldl_eq_one_iff g el 1 (le_refl 1)]; simp

/-- One step of the `stepFun`-inclusion fold over `decodeList b`: test
`interYs-index ⊆ output`. -/
def subStp (incl0 incl1 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1
    (isOne (incl1 (Nat.pair (interYsIdx P₁ incl0 w.unpair.2.unpair.2 w.unpair.1.unpair.1)
      w.unpair.1.unpair.2))) 0

/-- The `{0,1}` characteristic function of `stepFun (funListOf (decodeList a)) ⊆
stepFun (funListOf
(decodeList b))` (correct when `a` is consistent). `a` is the `foldCode`
parameter, `b` the code. -/
def subChar (incl0 incl1 : ℕ → ℕ) (a b : ℕ) : ℕ := foldCode (subStp P₁ incl0 incl1) a 1 b

theorem subChar_spec (incl0 incl1 : ℕ → ℕ)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2)
    {a : ℕ}
    (hane : (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)).Nonempty)
    (b : ℕ) :
    subChar P₁ incl0 incl1 a b = 1 ↔
      (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)) ⊆
        stepFun (funListOf P₀ P₁ (decodeList b)) := by
  have hcons : ∀ {X : Set α},
      V₀.mem X → V₁.mem (interYs V₁.master (funListOf P₀ P₁ (decodeList a)) X) :=
    fun {X} hX => interYs_funList_mem_of_nonempty P₀ P₁ hane hX
  rw [stepFun_funListOf_subset_iff P₀ P₁ hcons]
  unfold subChar
  rw [foldCode_eq']
  have hstep : (fun acc x => subStp P₁ incl0 incl1 (Nat.pair x (Nat.pair acc a)))
      = (fun acc x => selectFn acc
          (isOne (incl1 (Nat.pair (interYsIdx P₁ incl0 a x.unpair.1) x.unpair.2))) 0) := by
    funext acc x
    show subStp P₁ incl0 incl1 (Nat.pair x (Nat.pair acc a)) = _
    unfold subStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, andFoldl_one (fun x => incl1 (Nat.pair (interYsIdx P₁ incl0 a x.unpair.1) x.unpair.2))]
  refine forall_congr' (fun e' => ?_)
  refine imp_congr_right (fun he' => ?_)
  rw [hincl1]
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [interYsIdx_spec P₀ P₁ incl0 hincl0 a e'.unpair.1 (hcons (P₀.mem_X e'.unpair.1))]

theorem primrec_subStp (incl0 incl1 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0)
    (hincl1p : Nat.Primrec incl1) : Nat.Primrec (subStp P₁ incl0 incl1) := by
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have ha : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hidx : Nat.Primrec
      (fun w : ℕ => interYsIdx P₁ incl0 w.unpair.2.unpair.2 w.unpair.1.unpair.1) :=
    ((primrec_interYsIdx P₁ incl0 hincl0p).comp (ha.pair hk)).of_eq (fun w => by
      show interYsIdx P₁ incl0 (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1).unpair.1
        (Nat.pair w.unpair.2.unpair.2 w.unpair.1.unpair.1).unpair.2 = _
      rw [unpair_pair_fst, unpair_pair_snd])
  have hincl := hincl1p.comp (hidx.pair he2)
  refine (primrec_selectFn hflag (primrec_isOne.comp hincl) (
    Nat.Primrec.const 0)).of_eq (fun w => ?_)
  unfold subStp
  rfl

theorem primrec_subChar (incl0 incl1 : ℕ → ℕ) (hincl0p : Nat.Primrec incl0)
    (hincl1p : Nat.Primrec incl1) :
    Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.1 t.unpair.2) :=
  (primrec_foldCode (primrec_subStp P₁ incl0 incl1 hincl0p hincl1p) Nat.Primrec.left
    (Nat.Primrec.const 1) Nat.Primrec.right).of_eq (fun _ => rfl)

/-! #### The trivial test: `stepFun (funListOf el) = univ iff every output is `Δ₁`. -/

/-- The least map of the empty step-list — the function-space bottom: it relates
every `𝒟₀`
neighbourhood only to `Δ₁`. -/
def botMap : ApproximableMap V₀ V₁ :=
  leastMap [] (by intro X _; rw [interYs_nil]; exact V₁.master_mem)

theorem botMap_rel {X : Set α} {Y : Set β} :
    (botMap : ApproximableMap V₀ V₁).rel X Y ↔ V₀.mem X ∧ V₁.mem Y ∧ V₁.master ⊆ Y := Iff.rfl

/-- **`stepFun (funListOf el)` is everything iff every output neighbourhood is
`Δ₁`.** Forward:
the bottom map `botMap` lies in `univ`, and `botMap.rel X Y` forces `Y = Δ₁`.
Backward: `[X, Δ₁]`
is satisfied by every map. Choice-free. -/
theorem stepFun_funListOf_eq_univ_iff (el : List ℕ) :
    (stepFun (funListOf P₀ P₁ el) : Set (ApproximableMap V₀ V₁)) = Set.univ ↔
      ∀ e ∈ el, P₁.X e.unpair.2 = V₁.master := by
  constructor
  · intro h e he
    have hbot : (botMap : ApproximableMap V₀ V₁) ∈ stepFun (funListOf P₀ P₁ el) := by
      rw [h]; exact Set.mem_univ _
    have hr := hbot (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    exact Set.Subset.antisymm (V₁.sub_master (P₁.mem_X _)) (botMap_rel.mp hr).2.2
  · intro h
    ext f
    simp only [Set.mem_univ, iff_true, mem_stepFun]
    intro p hp
    rw [funListOf, List.mem_map] at hp
    obtain ⟨e, he, rfl⟩ := hp
    change f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2)
    rw [h e he]
    exact f.mono f.master_rel (V₀.sub_master (P₀.mem_X _)) subset_rfl (P₀.mem_X _) V₁.master_mem

/-- One step of the trivial-test fold: is this entry's output index equal to
`masterIdx`? -/
def trivStp (eq1 : ℕ → ℕ) (w : ℕ) : ℕ :=
  selectFn w.unpair.2.unpair.1
    (isOne (eq1 (Nat.pair w.unpair.1.unpair.2 P₁.masterIdx))) 0

/-- The `{0,1}` characteristic function of `stepFun (funListOf (decodeList a)) =
univ`. -/
def trivialChar (eq1 : ℕ → ℕ) (a : ℕ) : ℕ := foldCode (trivStp P₁ eq1) 0 1 a

theorem trivialChar_spec (eq1 : ℕ → ℕ)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (a : ℕ) :
    trivialChar P₁ eq1 a = 1 ↔
      (stepFun (funListOf P₀ P₁ (decodeList a)) : Set (ApproximableMap V₀ V₁)) = Set.univ := by
  rw [stepFun_funListOf_eq_univ_iff P₀ P₁]
  unfold trivialChar
  rw [foldCode_eq']
  have hstep : (fun acc x => trivStp P₁ eq1 (Nat.pair x (Nat.pair acc 0)))
      = (fun acc x => selectFn acc (isOne (eq1 (Nat.pair x.unpair.2 P₁.masterIdx))) 0) := by
    funext acc x
    show trivStp P₁ eq1 (Nat.pair x (Nat.pair acc 0)) = _
    unfold trivStp
    simp only [unpair_pair_fst, unpair_pair_snd]
  rw [hstep, andFoldl_one (fun x => eq1 (Nat.pair x.unpair.2 P₁.masterIdx))]
  refine forall_congr' (fun e => ?_)
  refine imp_congr_right (fun he => ?_)
  rw [heq1]
  simp only [unpair_pair_fst, unpair_pair_snd, P₁.masterIdx_spec]

theorem primrec_trivStp (eq1 : ℕ → ℕ) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (trivStp P₁ eq1) := by
  have hflag : Nat.Primrec (fun w : ℕ => w.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have he2 : Nat.Primrec (fun w : ℕ => w.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have harg := heq1p.comp (he2.pair (Nat.Primrec.const P₁.masterIdx))
  refine (primrec_selectFn hflag (primrec_isOne.comp harg) (
    Nat.Primrec.const 0)).of_eq (fun w => ?_)
  unfold trivStp
  rfl

theorem primrec_trivialChar (eq1 : ℕ → ℕ) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (trivialChar P₁ eq1) :=
  (primrec_foldCode (primrec_trivStp P₁ eq1 heq1p) (Nat.Primrec.const 0)
    (Nat.Primrec.const 1) primrec_id).of_eq (fun _ => rfl)

/-! #### The function-space enumeration `Xenum` and its consistency-pair decider. -/

/-- The function-space enumeration: a code `c` lists step-pairs; if they are
consistent (`gN c = 1`,
where `gN` is the consistency char) the neighbourhood is `stepFun (funListOf
(decodeList c))`,
otherwise we send the junk code to the master neighbourhood `univ`. Choice-free as
*data* because the
branch is a `Nat`-equality `if`. -/
def Xenum (gN : ℕ → ℕ) (c : ℕ) : Set (ApproximableMap V₀ V₁) :=
  if gN c = 1 then stepFun (funListOf P₀ P₁ (decodeList c)) else Set.univ

theorem Xenum_pos {gN : ℕ → ℕ} {c : ℕ} (h : gN c = 1) :
    Xenum P₀ P₁ gN c = stepFun (funListOf P₀ P₁ (decodeList c)) := if_pos h

theorem Xenum_neg {gN : ℕ → ℕ} {c : ℕ} (h : gN c ≠ 1) : Xenum P₀ P₁ gN c = Set.univ := if_neg h

theorem Xenum_mem (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (c : ℕ) :
    (funSpace V₀ V₁).mem (Xenum P₀ P₁ gN c) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h]
    exact ⟨⟨funListOf P₀ P₁ (decodeList c), funListOf_valid P₀ P₁ _, rfl⟩, (hgN c).mp h⟩
  · rw [Xenum_neg P₀ P₁ h]; exact funSpace_master ▸ (funSpace V₀ V₁).master_mem

theorem Xenum_nonempty (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (c : ℕ) :
    (Xenum P₀ P₁ gN c).Nonempty := (Xenum_mem P₀ P₁ gN hgN c).2

/-- The canonical code of the intersection `Xenum n ∩ Xenum m`: `appendCode` when
both are
consistent, otherwise the consistent side (the other being `univ`). -/
def interIdx (gN : ℕ → ℕ) (n m : ℕ) : ℕ :=
  selectFn (isOne (gN n)) (selectFn (isOne (gN m)) (appendCode n m) n) m

/-- **`interIdx` codes the intersection** whenever it is non-empty (and the result
is in the
enumeration). -/
theorem Xenum_inter_eq (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (n m : ℕ)
    (hne : (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty) :
    Xenum P₀ P₁ gN (interIdx gN n m) = Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m := by
  unfold interIdx
  rw [selectFn_isOne]
  by_cases hn : gN n = 1
  · rw [if_pos hn, selectFn_isOne]
    by_cases hm : gN m = 1
    · rw [if_pos hm, Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm,
      ← stepFun_funListOf_appendCode P₀ P₁ n m]
      rw [Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm] at hne
      have hgne : gN (appendCode n m) = 1 :=
        (hgN _).mpr (by rw [stepFun_funListOf_appendCode P₀ P₁ n m]; exact hne)
      rw [Xenum_pos P₀ P₁ hgne]
    · rw [if_neg hm, Xenum_neg P₀ P₁ hm, Set.inter_univ]
  · rw [if_neg hn, Xenum_neg P₀ P₁ hn, Set.univ_inter]

/-- The `{0,1}` characteristic function of Scott's consistency relation (ii) for
the function space:
`∃ k, Xenum k ⊆ Xenum n ∩ Xenum m`. -/
def consPairChar (gN : ℕ → ℕ) (n m : ℕ) : ℕ :=
  selectFn (isOne (gN n)) (selectFn (isOne (gN m)) (gN (appendCode n m)) 1) 1

theorem consPairChar_spec (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (n m : ℕ) :
    consPairChar gN n m = 1 ↔
      ∃ k, Xenum P₀ P₁ gN k ⊆ Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m := by
  have hcons_iff : (∃ k, Xenum P₀ P₁ gN k ⊆ Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m) ↔
      (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty := by
    constructor
    · rintro ⟨k, hk⟩; exact (Xenum_nonempty P₀ P₁ gN hgN k).mono hk
    · intro hne
      exact ⟨interIdx gN n m, (Xenum_inter_eq P₀ P₁ gN hgN n m hne).subset⟩
  rw [hcons_iff]
  unfold consPairChar
  by_cases hn : gN n = 1
  · rw [selectFn_isOne, if_pos hn, selectFn_isOne]
    by_cases hm : gN m = 1
    · rw [if_pos hm, hgN (appendCode n m), Xenum_pos P₀ P₁ hn, Xenum_pos P₀ P₁ hm,
        ← stepFun_funListOf_appendCode P₀ P₁ n m]
    · rw [if_neg hm, Xenum_pos P₀ P₁ hn, Xenum_neg P₀ P₁ hm, Set.inter_univ]
      exact iff_of_true rfl ((hgN n).mp hn)
  · rw [selectFn_isOne, if_neg hn, Xenum_neg P₀ P₁ hn, Set.univ_inter]
    exact iff_of_true rfl (Xenum_nonempty P₀ P₁ gN hgN m)

theorem primrec_consPairChar (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN) :
    Nat.Primrec (fun t => consPairChar gN t.unpair.1 t.unpair.2) := by
  have hn := hgNp.comp Nat.Primrec.left
  have hm := hgNp.comp Nat.Primrec.right
  have happ := hgNp.comp primrec_appendCode
  have hinner := primrec_selectFn (primrec_isOne.comp hm) happ (Nat.Primrec.const 1)
  exact (primrec_selectFn (primrec_isOne.comp hn) hinner (Nat.Primrec.const 1)).of_eq (fun _ => rfl)

theorem primrec_interIdx (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN) :
    Nat.Primrec (fun t => interIdx gN t.unpair.1 t.unpair.2) := by
  have hn := hgNp.comp Nat.Primrec.left
  have hm := hgNp.comp Nat.Primrec.right
  have hinner := primrec_selectFn (primrec_isOne.comp hm) primrec_appendCode Nat.Primrec.left
  exact (primrec_selectFn (primrec_isOne.comp hn) hinner Nat.Primrec.right).of_eq (fun _ => rfl)

/-! #### The equality decider `eqEnumChar` and Scott's relation (i) `interEqChar`. -/

/-- `selectFn c d 0 = 1` decides the conjunction `c = 1 ∧ d = 1`. -/
theorem selectFn_mul_iff (c d : ℕ) : selectFn c d 0 = 1 ↔ c = 1 ∧ d = 1 := by
  have h : selectFn c d 0 = c * d := by simp only [selectFn, Nat.mul_zero, Nat.add_zero]
  rw [h, nat_mul_eq_one]

/-- The `{0,1}` characteristic function of `Xenum a = Xenum b`. Both consistent →
inclusion both
ways (`subChar`); one consistent, one junk (`univ`) → the consistent side is the
trivial
neighbourhood (`trivialChar`); both junk → equal. -/
def eqEnumChar (gN incl0 incl1 eq1 : ℕ → ℕ) (a b : ℕ) : ℕ :=
  selectFn (isOne (gN a))
    (selectFn (isOne (gN b))
      (selectFn (subChar P₁ incl0 incl1 a b) (subChar P₁ incl0 incl1 b a) 0)
      (trivialChar P₁ eq1 a))
    (selectFn (isOne (gN b)) (trivialChar P₁ eq1 b) 1)

theorem eqEnumChar_spec (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (a b : ℕ) :
    eqEnumChar P₁ gN incl0 incl1 eq1 a b = 1 ↔ Xenum P₀ P₁ gN a = Xenum P₀ P₁ gN b := by
  unfold eqEnumChar
  by_cases ha : gN a = 1
  · rw [selectFn_isOne, if_pos ha, selectFn_isOne]
    have hanea := (hgN a).mp ha
    by_cases hb : gN b = 1
    · rw [if_pos hb, Xenum_pos P₀ P₁ ha, Xenum_pos P₀ P₁ hb, selectFn_mul_iff,
        subChar_spec P₀ P₁ incl0 incl1 hincl0 hincl1 hanea b,
        subChar_spec P₀ P₁ incl0 incl1 hincl0 hincl1 ((hgN b).mp hb) a]
      exact ⟨fun ⟨h1, h2⟩ => Set.Subset.antisymm h1 h2, fun h => ⟨h.subset, h.superset⟩⟩
    · rw [if_neg hb, Xenum_pos P₀ P₁ ha, Xenum_neg P₀ P₁ hb, trivialChar_spec P₀ P₁ eq1 heq1 a]
  · rw [selectFn_isOne, if_neg ha, selectFn_isOne]
    by_cases hb : gN b = 1
    · rw [if_pos hb, Xenum_neg P₀ P₁ ha, Xenum_pos P₀ P₁ hb, trivialChar_spec P₀ P₁ eq1 heq1 b]
      exact eq_comm
    · rw [if_neg hb, Xenum_neg P₀ P₁ ha, Xenum_neg P₀ P₁ hb]
      exact iff_of_true rfl rfl

theorem primrec_eqEnumChar (gN incl0 incl1 eq1 : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hincl0p : Nat.Primrec incl0) (hincl1p : Nat.Primrec incl1) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (fun t => eqEnumChar P₁ gN incl0 incl1 eq1 t.unpair.1 t.unpair.2) := by
  have ha := primrec_isOne.comp (hgNp.comp Nat.Primrec.left)
  have hb := primrec_isOne.comp (hgNp.comp Nat.Primrec.right)
  have hsubab : Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.1 t.unpair.2) :=
    primrec_subChar P₁ incl0 incl1 hincl0p hincl1p
  have hsubba : Nat.Primrec (fun t => subChar P₁ incl0 incl1 t.unpair.2 t.unpair.1) :=
    ((primrec_subChar P₁ incl0 incl1 hincl0p hincl1p).comp
      (Nat.Primrec.right.pair Nat.Primrec.left)).of_eq (fun t => by
        show subChar P₁ incl0 incl1 (Nat.pair t.unpair.2 t.unpair.1).unpair.1
          (Nat.pair t.unpair.2 t.unpair.1).unpair.2 = _
        rw [unpair_pair_fst, unpair_pair_snd])
  have htriva := (primrec_trivialChar P₁ eq1 heq1p).comp Nat.Primrec.left
  have htrivb := (primrec_trivialChar P₁ eq1 heq1p).comp Nat.Primrec.right
  have hbothcons := primrec_selectFn hsubab hsubba (Nat.Primrec.const 0)
  have hacons := primrec_selectFn hb hbothcons htriva
  have hanot := primrec_selectFn hb htrivb (Nat.Primrec.const 1)
  exact (primrec_selectFn ha hacons hanot).of_eq (fun _ => rfl)

/-- The `{0,1}` characteristic function of Scott's relation (i) for the function
space:
`Xenum n ∩ Xenum m = Xenum k`. -/
def interEqChar (gN incl0 incl1 eq1 : ℕ → ℕ) (n m k : ℕ) : ℕ :=
  selectFn (consPairChar gN n m) (eqEnumChar P₁ gN incl0 incl1 eq1 (interIdx gN n m) k) 0

theorem interEqChar_spec (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (n m k : ℕ) :
    interEqChar P₁ gN incl0 incl1 eq1 n m k = 1 ↔
      Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m = Xenum P₀ P₁ gN k := by
  unfold interEqChar
  rw [selectFn_mul_iff, consPairChar_spec P₀ P₁ gN hgN n m,
    eqEnumChar_spec P₀ P₁ gN incl0 incl1 eq1 hgN hincl0 hincl1 heq1 (interIdx gN n m) k]
  constructor
  · rintro ⟨⟨k', hk'⟩, heq⟩
    have hne : (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty :=
      (Xenum_nonempty P₀ P₁ gN hgN k').mono hk'
    rw [← Xenum_inter_eq P₀ P₁ gN hgN n m hne]; exact heq
  · intro heq
    have hne : (Xenum P₀ P₁ gN n ∩ Xenum P₀ P₁ gN m).Nonempty := by
      rw [heq]; exact Xenum_nonempty P₀ P₁ gN hgN k
    exact ⟨⟨k, heq.superset⟩, by rw [Xenum_inter_eq P₀ P₁ gN hgN n m hne]; exact heq⟩

theorem primrec_interEqChar (gN incl0 incl1 eq1 : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hincl0p : Nat.Primrec incl0) (hincl1p : Nat.Primrec incl1) (heq1p : Nat.Primrec eq1) :
    Nat.Primrec (fun t => interEqChar P₁ gN incl0 incl1 eq1 t.unpair.1
      t.unpair.2.unpair.1 t.unpair.2.unpair.2) := by
  have hn : Nat.Primrec (fun t : ℕ => t.unpair.1) := Nat.Primrec.left
  have hm : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.right
  have hk : Nat.Primrec (fun t : ℕ => t.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.right
  have hcons := (primrec_consPairChar gN hgNp).comp (hn.pair hm)
  have hidx := (primrec_interIdx gN hgNp).comp (hn.pair hm)
  have heqc := (primrec_eqEnumChar P₁ gN incl0 incl1 eq1 hgNp hincl0p hincl1p heq1p).comp
    (hidx.pair hk)
  refine (primrec_selectFn hcons heqc (Nat.Primrec.const 0)).of_eq (fun t => ?_)
  show _ = interEqChar P₁ gN incl0 incl1 eq1 t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2
  unfold interEqChar
  simp only [unpair_pair_fst, unpair_pair_snd]

/-! ### Milestone 6 — assembling the function-space presentation.

`Theorem 7.5 (existence part)`: `(𝒟₀ → 𝒟₁)` is effectively given. We package the
deciders above into a
`ComputablePresentation (funSpace V₀ V₁)`, with `X = Xenum`, `inter = interIdx`
and `masterIdx = 0`
(the empty step-list, whose neighbourhood is `univ = Δ`). The concrete
characteristic functions are
obtained choice-free from the component presentations' relations *inside* the
`Nonempty` proof of
`funSpace_isEffectivelyGiven` (extraction into a `Prop` goal needs no choice). -/

/-- Every valid finite step-list is `funListOf` of some entry-list (choice-free:
`Exists.elim` of
`P₀.surj`/`P₁.surj`, entry by entry). -/
theorem exists_funListOf {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2) :
    ∃ el, funListOf P₀ P₁ el = L := by
  induction L with
  | nil => exact ⟨[], rfl⟩
  | cons p L ih =>
    obtain ⟨X, Y⟩ := p
    obtain ⟨i, hi⟩ := P₀.surj (hL (X, Y) (List.mem_cons.mpr (Or.inl rfl))).1
    obtain ⟨j, hj⟩ := P₁.surj (hL (X, Y) (List.mem_cons.mpr (Or.inl rfl))).2
    obtain ⟨el, hel⟩ := ih (fun q hq => hL q (List.mem_cons.mpr (Or.inr hq)))
    refine ⟨Nat.pair i j :: el, ?_⟩
    rw [funListOf_cons, hel]
    congr 1
    change (P₀.X (Nat.pair i j).unpair.1, P₁.X (Nat.pair i j).unpair.2) = (X, Y)
    rw [unpair_pair_fst, unpair_pair_snd, hi, hj]

/-- **The function-space presentation.** Built from explicit characteristic
functions for the
component presentations' relations (`gN` = function-space consistency,
`incl0`/`incl1` = inclusion,
`eq1` = equality), so it is choice-free given those concrete functions. -/
def funPresentation (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    ComputablePresentation (funSpace V₀ V₁) where
  X := Xenum P₀ P₁ gN
  mem_X := Xenum_mem P₀ P₁ gN hgN
  surj := by
    rintro W ⟨⟨L, hL, rfl⟩, hne⟩
    obtain ⟨el, hel⟩ := exists_funListOf P₀ P₁ hL
    have hc : gN (encodeList el) = 1 := by rw [hgN, decodeList_encodeList, hel]; exact hne
    exact ⟨encodeList el, by rw [Xenum_pos P₀ P₁ hc, decodeList_encodeList, hel]⟩
  interEq_computable :=
    ⟨fun t => interEqChar P₁ gN incl0 incl1 eq1 t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2,
      primrec_interEqChar P₁ gN incl0 incl1 eq1 hgNp hincl0p hincl1p heq1p,
      fun t => (interEqChar_spec P₀ P₁ gN incl0 incl1 eq1 hgN hincl0 hincl1 heq1
        t.unpair.1 t.unpair.2.unpair.1 t.unpair.2.unpair.2).symm⟩
  cons_computable :=
    ⟨fun t => consPairChar gN t.unpair.1 t.unpair.2, primrec_consPairChar gN hgNp,
      fun t => (consPairChar_spec P₀ P₁ gN hgN t.unpair.1 t.unpair.2).symm⟩
  inter := interIdx gN
  inter_primrec := primrec_interIdx gN hgNp
  inter_spec := by
    intro n m h
    obtain ⟨k, hk⟩ := h
    exact Xenum_inter_eq P₀ P₁ gN hgN n m ((Xenum_nonempty P₀ P₁ gN hgN k).mono hk)
  masterIdx := 0
  masterIdx_spec := by
    change Xenum P₀ P₁ gN 0 = Set.univ
    unfold Xenum
    rw [decodeList_zero]
    simp only [funListOf, List.map_nil, stepFun_nil, ite_self]

/-- **Theorem 7.5 (existence part) (Scott 1981, PRG-19).** If `𝒟₀` and `𝒟₁` are
effectively given,
then so is the function space `(𝒟₀ → 𝒟₁)`. Choice-free. -/
theorem funSpace_isEffectivelyGiven (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (funSpace V₀ V₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := h₀
  obtain ⟨P₁⟩ := h₁
  obtain ⟨incl0, hincl0p, hincl0s⟩ := P₀.incl_computable
  obtain ⟨incl1, hincl1p, hincl1s⟩ := P₁.incl_computable
  obtain ⟨eq1, heq1p, heq1s⟩ := P₁.eq_computable
  obtain ⟨fc0, hfc0p, hfc0s⟩ := P₀.cons_computable
  obtain ⟨fc1, hfc1p, hfc1s⟩ := P₁.cons_computable
  exact ⟨funPresentation P₀ P₁ (funConsChar P₀ P₁ fc0 fc1) incl0 incl1 eq1
    (funConsChar_spec P₀ P₁ fc0 fc1 (fun s => (hfc0s s).symm) (fun s => (hfc1s s).symm))
    (primrec_funConsChar P₀ P₁ fc0 fc1 hfc0p hfc1p)
    (fun s => (hincl0s s).symm) hincl0p
    (fun s => (hincl1s s).symm) hincl1p
    (fun s => (heq1s s).symm) heq1p⟩

/-! ### Milestone 8 — computable elements of `(𝒟₀ → 𝒟₁)` are exactly the
computable maps.

Scott (Theorem 7.5): *"The computable elements `f ∈ |𝒟₀ → 𝒟₁|` are exactly the
computable maps
`f : 𝒟₀ → 𝒟₁`."* Under the completeness isomorphism `toApproxMap` (Theorem 3.10),
a filter `φ` of the
function space corresponds to the approximable map `f̂ = toApproxMap φ`, and
`φ.mem [X, Y] ↔ X f̂ Y`.
The enumeration `Xenum c` of a *consistent* code is the finite intersection
`⋂[X₀_{eᵢ}, X₁_{eᵢ}]`, so
`φ ∋ Xenum c ↔ ∀ eᵢ, φ ∋ [X₀_{eᵢ}, X₁_{eᵢ}]` (the generation lemma
`mem_stepFun_iff`); junk codes map
to `univ`, always in `φ`. Hence the element index set `{c ∣ Xenum c ∈ φ}` is r.e.
iff the single-step
relation `{⟨n,m⟩ ∣ [X₀ₙ, X₁ₘ] ∈ φ}` is — the map's neighbourhood relation. The map
⟹ element half is
the choice-free *bounded-`∀` over a coded list* closure
`REPred.forall_mem_decodeList`. -/

/-- **Bridge.** `φ ∋ Xenum c` iff, *when `c` is consistent*, `φ` contains every
constituent step. -/
theorem mem_Xenum_iff (gN : ℕ → ℕ) (φ : (funSpace V₀ V₁).Element) (c : ℕ) :
    φ.mem (Xenum P₀ P₁ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c, φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun_iff φ (funListOf_valid P₀ P₁ (decodeList c))]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; rw [← funSpace_master]; exact φ.master_mem

/-- **Theorem 7.5 (Scott 1981, PRG-19) — computable elements = computable maps
(choice-free).** For
the function-space enumeration `Xenum` built from a consistency char `gN`, an
element `φ` has an r.e.
index set iff the corresponding approximable map `toApproxMap φ` is computable. -/
theorem Xenum_isComputableElement_iff (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (φ : (funSpace V₀ V₁).Element) :
    REPred (fun c => φ.mem (Xenum P₀ P₁ gN c)) ↔ IsComputableMap P₀ P₁ (toApproxMap φ) := by
  -- `IsComputableMap` unfolds (def-eq) to r.e.-ness of `R' s = φ ∋ [X₀_{s.1},
  -- X₁_{s.2}]`.
  have hbridge := mem_Xenum_iff P₀ P₁ gN φ
  constructor
  · -- element computable ⟹ map computable: reindex by the single-step code `pair s 0 + 1`.
    intro helem
    have hc0p : Nat.Primrec (fun s => Nat.pair s 0 + 1) :=
      Nat.Primrec.succ.comp (primrec_id.pair (Nat.Primrec.const 0))
    have key : REPred (fun s => φ.mem (Xenum P₀ P₁ gN (Nat.pair s 0 + 1))) := helem.comp hc0p
    change REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2)))
    refine REPred.of_iff (fun s => ?_) key
    have hdec : decodeList (Nat.pair s 0 + 1) = [s] := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
    have hcons : gN (Nat.pair s 0 + 1) = 1 := by
      rw [hgN, hdec]
      change (stepFun [(P₀.X s.unpair.1, P₁.X s.unpair.2)]
        : Set (ApproximableMap V₀ V₁)).Nonempty
      rw [stepFun_singleton]
      exact (step_mem (P₀.mem_X _) (P₁.mem_X _)).2
    rw [hbridge (Nat.pair s 0 + 1), hdec]
    constructor
    · intro hRs _ e he; rw [List.mem_singleton] at he; subst he; exact hRs
    · intro h; exact h hcons s (List.mem_singleton.mpr rfl)
  · -- map computable ⟹ element computable: guard the bounded-`∀` by the decidable `gN c = 1`.
    intro hmap
    have hR' : REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2))) := hmap
    have hforall : REPred (fun c => ∀ e ∈ decodeList c,
        φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := hR'.forall_mem_decodeList
    have hne1 : REPred (fun c => ¬ gN c = 1) :=
      ((RecDecidable.natEq hgNp (Nat.Primrec.const 1)).not).re
    refine REPred.of_iff (fun c => ?_) (hne1.or hforall)
    rw [hbridge c]; exact Decidable.imp_iff_not_or

/-- **Theorem 7.5 (Scott 1981, PRG-19), packaged for `funPresentation`.** An
element of the
function-space presentation is a computable element iff it is (the filter of) a
computable map. -/
theorem isComputableElement_funPresentation_iff (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    (φ : (funSpace V₀ V₁).Element) :
    IsComputableElement (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) φ ↔ IsComputableMap P₀ P₁ (toApproxMap φ) :=
  Xenum_isComputableElement_iff P₀ P₁ gN hgNp hgN φ

/-! ### Milestone 7 — `eval` is computable.

Scott (Theorem 7.5): *"The combinators `eval` and `curry` are computable, provided
all the domains
involved are effectively given."* The evaluation map `eval : (𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁`
sends `(F, X)` to
`Y` iff **every** map `f ∈ F` relates `X` to `Y` (Theorem 3.11), i.e. `F ⊆ [X, Y]`
(the step
neighbourhood, viewed as the set of maps relating `X` to `Y`). On the product
presentation
`prodPresentation funPresentation P₀`, the neighbourhood at index `k` is
`Xenum_{k.1} × X₀_{k.2}`, so

  `(Xenum c, X₀ⱼ) eval Y₁ₘ ↔ Xenum c ⊆ [X₀ⱼ, Y₁ₘ]`.

The single step `[X₀ⱼ, Y₁ₘ]` is itself a one-entry function-space neighbourhood —
`Xenum` of the
(always consistent) code `⟨⟨j, m⟩, 0⟩ + 1` — so the relation is exactly the
**decidable** function-space
inclusion `funPresentation.incl_computable`, re-indexed by a primitive-recursive
code map. This is
Scott's observation that `eval` is a *recursive* set; r.e.-ness (hence
computability) and
choice-freeness follow. -/

/-- **The step neighbourhood `[X₀ⱼ, Y₁ₘ]` as a one-entry `Xenum`.** The code `⟨⟨j,
m⟩, 0⟩ + 1`
decodes to the singleton entry-list `[⟨j, m⟩]`, which is always consistent (the
step map itself is a
witness), so `Xenum` of it is `stepFun [(X₀ⱼ, Y₁ₘ)] = [X₀ⱼ, Y₁ₘ]`. -/
theorem Xenum_singleton (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (j m : ℕ) :
    Xenum P₀ P₁ gN (Nat.pair (Nat.pair j m) 0 + 1) = step (P₀.X j) (P₁.X m) := by
  have hfp : funPair P₀ P₁ (Nat.pair j m) = (P₀.X j, P₁.X m) := by
    change (P₀.X (Nat.pair j m).unpair.1, P₁.X (Nat.pair j m).unpair.2) = (P₀.X j, P₁.X m)
    rw [unpair_pair_fst, unpair_pair_snd]
  have hdec : decodeList (Nat.pair (Nat.pair j m) 0 + 1) = [Nat.pair j m] := by
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  have hstepeq : (stepFun (funListOf P₀ P₁ [Nat.pair j m]) : Set (ApproximableMap V₀ V₁))
      = step (P₀.X j) (P₁.X m) := by
    change stepFun [funPair P₀ P₁ (Nat.pair j m)] = step (P₀.X j) (P₁.X m)
    rw [hfp, stepFun_singleton]
  have hcons : gN (Nat.pair (Nat.pair j m) 0 + 1) = 1 := by
    rw [hgN, hdec, hstepeq]; exact (step_mem (P₀.mem_X j) (P₁.mem_X m)).2
  rw [Xenum_pos P₀ P₁ hcons, hdec, hstepeq]

/-- **Evaluation against a product neighbourhood.** `(F, X) eval Y ↔ F ⊆ [X, Y]`,
for any
function-space neighbourhood `F` and basic neighbourhoods `X, Y`: every map in `F`
relates `X` to `Y`
exactly when `F` is contained in the step set `[X, Y] = {f ∣ f X Y}`. -/
theorem evalMap_rel_prodNbhd_iff {F : Set (ApproximableMap V₀ V₁)} (hF : (funSpace V₀ V₁).mem F)
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) :
    (evalMap V₀ V₁).rel (prodNbhd F X) Y ↔ F ⊆ step X Y := by
  change (prod (funSpace V₀ V₁) V₀).mem (prodNbhd F X) ∧
    (eval V₀ V₁).rel (Sum.inl ⁻¹' prodNbhd F X) (Sum.inr ⁻¹' prodNbhd F X) Y ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, _, _, _, hrel⟩ f hf; exact mem_step.mpr (hrel f hf)
  · intro hsub
    exact ⟨prod_mem_prodNbhd hF hX, hF, hX, hY, fun f hf => mem_step.mp (hsub hf)⟩

/-- **Theorem 7.5 (Scott 1981, PRG-19) — `eval` is computable (choice-free).**
Relative to the
function-space presentation `funPresentation` (and the product/codomain
presentations), the
evaluation map `eval : (𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁` is computable: its neighbourhood
relation is the
*recursively decidable* function-space inclusion `Xenum c ⊆ [X₀ⱼ, Y₁ₘ]`, hence
recursively
enumerable. -/
theorem evalMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    IsComputableMap
      (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀) P₁ (evalMap V₀ V₁) := by
  -- The function-space inclusion is recursively decidable
  -- (`funPresentation.incl_computable`);
  -- `funPresentation.X` is definitionally `Xenum`, so we read it off directly.
  have hsub : RecDecidable (fun s => Xenum P₀ P₁ gN s.unpair.1 ⊆ Xenum P₀ P₁ gN s.unpair.2) :=
    (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p).incl_computable
  -- Re-index `t ↦ ⟨(t.1).1, ⟨⟨(t.1).2, t.2⟩, 0⟩ + 1⟩`: `Xenum_{(t.1).1} ⊆
  -- [X₀_{(t.1).2},
  -- Y₁_{t.2}]`.
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hg : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
      (Nat.pair (Nat.pair t.unpair.1.unpair.2 t.unpair.2) 0 + 1)) :=
    h11.pair (Nat.Primrec.succ.comp ((h12.pair Nat.Primrec.right).pair (Nat.Primrec.const 0)))
  refine (RecDecidable.of_iff (fun t => ?_) (hsub.comp hg)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [Xenum_singleton P₀ P₁ gN hgN t.unpair.1.unpair.2 t.unpair.2,
    show (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀).X t.unpair.1
      = prodNbhd (Xenum P₀ P₁ gN t.unpair.1.unpair.1) (P₀.X t.unpair.1.unpair.2) from rfl,
    evalMap_rel_prodNbhd_iff (Xenum_mem P₀ P₁ gN hgN _) (P₀.mem_X _) (P₁.mem_X _)]

/-! ### Milestone 9 — `curry` is computable.

Scott (Theorem 7.5): *"The combinators `eval` and `curry` are computable."* For a
map
`g : 𝒟₀ × 𝒟₁ → 𝒟₂`, `curry g : 𝒟₀ → (𝒟₁ → 𝒟₂)` sends `X` to the (filter generated
by the) section
map `gᴬ = gSection g X`, with `gᴬ Y Z ↔ X ∪ Y g Z` (Theorem 3.12). On the codomain
presentation
`funPresentation P₁ P₂`, `(X₀ₙ) curry(g) (Xenum c)` holds iff the section map lies
in `Xenum c`, i.e.
(for consistent `c`) `∀ ⟨j, k⟩ ∈ decodeList c, X₀ₙ ∪ X₁ⱼ g X₂ₖ` — a **bounded `∀`
over the coded
list, with the `𝒟₀`-parameter `n`** of the r.e. relation of `g`. This is r.e. by
the parameterised
closure `REPred.forall_mem_decodeList₂`; junk codes go to `univ` (always
satisfied). Choice-free. -/

/-- **Membership in `Xenum` for a single map.** A map `f` lies in `Xenum c` iff
(when `c` is
consistent) it relates every coded step `⟨X₀ᵢ, X₁ⱼ⟩`; junk codes give `univ`. (The
single-map analogue
of `mem_Xenum_iff`.) -/
theorem mem_Xenum_iff_map (gN : ℕ → ℕ) (f : ApproximableMap V₀ V₁) (c : ℕ) :
    f ∈ Xenum P₀ P₁ gN c ↔
      (gN c = 1 → ∀ e ∈ decodeList c, f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2)) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; exact Set.mem_univ f

/-- **Bridge for `curry`.** `(X₀ₙ) curry(g) (Xenum c)` iff, *when `c` is
consistent*, `g` relates
`X₀ₙ ∪ X₁_{e.1}` to `X₂_{e.2}` for every coded entry `e`. -/
theorem curry_rel_Xenum_iff {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty)
    (g : ApproximableMap (prod V₀ V₁) V₂) (n c : ℕ) :
    (curry g).rel (P₀.X n) (Xenum P₁ P₂ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c,
        g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
  rw [curry_rel]
  constructor
  · rintro ⟨hX, _, hmem⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g hX) c] at hmem
    intro hc e he
    have hrel := hmem hc e he
    rwa [gSection_rel] at hrel
  · intro himp
    refine ⟨P₀.mem_X n, Xenum_mem P₁ P₂ gN hgN c, ?_⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g (P₀.mem_X n)) c]
    intro hc e he
    rw [gSection_rel]
    exact himp hc e he

/-- **Theorem 7.5 (Scott 1981, PRG-19) — `curry` is computable (choice-free).** If
`g : 𝒟₀ × 𝒟₁
→ 𝒟₂`
is computable then so is `curry g : 𝒟₀ → (𝒟₁ → 𝒟₂)`: its neighbourhood relation is
the parameterised
bounded `∀` (`REPred.forall_mem_decodeList₂`) over the r.e. relation of `g`,
guarded by the decidable
consistency flag. -/
theorem curry_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₂.X s.unpair.1 ⊆ P₂.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₂.X s.unpair.1 = P₂.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    {g : ApproximableMap (prod V₀ V₁) V₂}
    (hg : IsComputableMap (prodPresentation P₀ P₁) P₂ g) :
    IsComputableMap P₀ (funPresentation P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p) (curry g) := by
  have hg' : REPred (fun s => g.rel ((prodPresentation P₀ P₁).X s.unpair.1) (P₂.X s.unpair.2)) := hg
  have hre : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2.unpair.1)
      s.unpair.2.unpair.2) :=
    (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)).pair
      (Nat.Primrec.right.comp Nat.Primrec.right)
  -- `g`'s relation re-indexed to `(n, e) ↦ X₀ₙ ∪ X₁_{e.1} g X₂_{e.2}` is r.e. in
  -- `(n, e)`.
  have hS : REPred₂ (fun n e =>
      g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
    refine REPred.of_iff (fun s => ?_) (hg'.comp hre)
    simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  -- bounded `∀` over the coded list, with parameter `n = t.1`
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2,
      g.rel (prodNbhd (P₀.X t.unpair.1) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) :=
    REPred.forall_mem_decodeList₂ hS
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  change (curry g).rel (P₀.X t.unpair.1) (Xenum P₁ P₂ gN t.unpair.2) ↔ _
  rw [curry_rel_Xenum_iff P₀ P₁ P₂ gN hgN g t.unpair.1 t.unpair.2]
  exact Decidable.imp_iff_not_or

end Domain.Neighborhood
