/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import Mathlib.Data.List.GetD
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.Baire.BaireMeasurable
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The graphs `G_S(2^ℕ)` and Miller's independence lemma

This file defines the graphs `G_S` on Cantor space associated to a set `S` of finite binary
words, and proves Miller's Proposition 6 ["The graph-theoretic approach to descriptive set
theory", BSL 18(4), 2012]: for *dense* `S` (every word extends into `S`), a non-meager set
with the Baire property contains a `G_S`-edge. Consequently every class of an equivalence
relation avoiding `G_S` is meager (`isMeagre_class_of_gSGraph_disjoint`), and in pullback
form (`isMeagre_pullback_class_of_gSGraph_hom`): a continuous `φ : 2^ℕ → α` that is a graph
homomorphism from `G_S` to the complement of a Borel equivalence relation `E` makes every
section `{b | E (φ a) (φ b)}` meager.

This is step 2 of the classical category route to Silver's theorem
(`InfinitaryLogic/Conditional/SilverCategoryRoute.lean`; see `docs/silver-phase2-route.md`):
combined with Kuratowski–Ulam (`isMeagre_of_isMeagre_sections`) and Mycielski
(`mycielski_cantor`), it reduces `CategoryReductionHypothesis` to exactly the classical
`G₀`-dichotomy.

## Definitions

* `prependWord w x`: the element of Cantor space starting with the word `w` and continuing
  with `x`; `wordCylinder w` is its range, the basic clopen set of sequences extending `w`.
* `GSGraph S y z`: `y = s ⌢ i ⌢ x` and `z = s ⌢ !i ⌢ x` for some `s ∈ S`, `i`, `x` — the
  two sequences extend the same `s ∈ S`, differ at position `s.length`, and share the tail.
* `DenseWords S`: every finite word has an extension in `S`.

## Proof of the independence lemma

By the Baire property, a non-meager `B` is comeager in some nonempty open set, hence in some
word cylinder `wordCylinder r`; pick `s ∈ S` extending `r`. The two injections
`prependWord (s ++ [i]) : 2^ℕ → wordCylinder (s ++ [i])` are continuous open maps, so the
sets of `x` with `prependWord (s ++ [i]) x ∉ B` are meager (`IsMeagre.preimage_of_isOpenMap`
applied to the part of the symmetric difference inside each child cylinder). A common point
`x` outside both meager sets yields the edge
`(prependWord (s ++ [false]) x, prependWord (s ++ [true]) x)` inside `B`.
-/

open Set Filter Topology

/-! ### Words and word cylinders -/

/-- The element of Cantor space that starts with the finite word `w` and continues with `x`. -/
def prependWord (w : List Bool) (x : ℕ → Bool) : ℕ → Bool := fun n =>
  if n < w.length then w.getD n false else x (n - w.length)

theorem prependWord_apply_of_lt {w : List Bool} {n : ℕ} (h : n < w.length) (x : ℕ → Bool) :
    prependWord w x n = w.getD n false := ite_eq_left h

theorem prependWord_apply_of_le {w : List Bool} {n : ℕ} (h : w.length ≤ n) (x : ℕ → Bool) :
    prependWord w x n = x (n - w.length) := ite_eq_right (not_lt.mpr h)

/-- The basic clopen set of sequences extending the word `w`. -/
private def wordCylinder (w : List Bool) : Set (ℕ → Bool) := Set.range (prependWord w)

private theorem mem_wordCylinder_iff {w : List Bool} {y : ℕ → Bool} :
    y ∈ wordCylinder w ↔ ∀ n < w.length, y n = w.getD n false := by
  constructor
  · rintro ⟨x, rfl⟩ n hn
    exact prependWord_apply_of_lt hn x
  · intro h
    refine ⟨fun n => y (n + w.length), funext fun n => ?_⟩
    rcases lt_or_ge n w.length with hn | hn
    · rw [prependWord_apply_of_lt hn]
      exact (h n hn).symm
    · rw [prependWord_apply_of_le hn]
      congr 1
      omega

private theorem prependWord_mem_wordCylinder (w : List Bool) (x : ℕ → Bool) :
    prependWord w x ∈ wordCylinder w := ⟨x, rfl⟩

private theorem wordCylinder_subset_of_prefix {r s : List Bool} (h : r <+: s) :
    wordCylinder s ⊆ wordCylinder r := by
  obtain ⟨t, rfl⟩ := h
  intro y hy
  rw [mem_wordCylinder_iff] at hy ⊢
  intro n hn
  rw [← List.getD_append r t false n hn]
  exact hy n (by rw [List.length_append]; omega)



private theorem continuous_prependWord (w : List Bool) : Continuous (prependWord w) := by
  refine continuous_pi fun n => ?_
  rcases lt_or_ge n w.length with hn | hn
  · have h : (fun x : ℕ → Bool => prependWord w x n) = fun _ => w.getD n false :=
      funext fun x => prependWord_apply_of_lt hn x
    rw [h]
    exact continuous_const
  · have h : (fun x : ℕ → Bool => prependWord w x n) = fun x => x (n - w.length) :=
      funext fun x => prependWord_apply_of_le hn x
    rw [h]
    exact continuous_apply _

private theorem image_prependWord_cylinder (w : List Bool) (x : ℕ → Bool) (n : ℕ) :
    prependWord w '' PiNat.cylinder x n = PiNat.cylinder (prependWord w x) (w.length + n) := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [PiNat.mem_cylinder_iff]
    intro i hi
    rcases lt_or_ge i w.length with hiw | hiw
    · rw [prependWord_apply_of_lt hiw, prependWord_apply_of_lt hiw]
    · rw [prependWord_apply_of_le hiw, prependWord_apply_of_le hiw]
      exact PiNat.mem_cylinder_iff.mp hy _ (by omega)
  · intro hz
    refine ⟨fun k => z (k + w.length), ?_, funext fun i => ?_⟩
    · rw [PiNat.mem_cylinder_iff]
      intro i hi
      have h := PiNat.mem_cylinder_iff.mp hz (i + w.length) (by omega)
      rw [prependWord_apply_of_le (by omega)] at h
      simpa using h
    · rcases lt_or_ge i w.length with hiw | hiw
      · rw [prependWord_apply_of_lt hiw]
        have h := PiNat.mem_cylinder_iff.mp hz i (by omega)
        rw [prependWord_apply_of_lt hiw] at h
        exact h.symm
      · rw [prependWord_apply_of_le hiw]
        congr 1
        omega

private theorem isOpenMap_prependWord (w : List Bool) : IsOpenMap (prependWord w) := by
  rw [(PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).isOpenMap_iff]
  rintro s ⟨x, n, rfl⟩
  rw [image_prependWord_cylinder]
  exact PiNat.isOpen_cylinder _ _ _

/-- The word formed by the first `n` values of `x`. -/
def wordOf (x : ℕ → Bool) (n : ℕ) : List Bool := List.ofFn fun i : Fin n => x i

@[simp] theorem length_wordOf (x : ℕ → Bool) (n : ℕ) : (wordOf x n).length = n :=
  List.length_ofFn

private theorem getD_wordOf {x : ℕ → Bool} {n i : ℕ} (h : i < n) :
    (wordOf x n).getD i false = x i := by
  rw [List.getD_eq_getElem _ _ (by simpa using h)]
  simp [wordOf]

private theorem wordCylinder_wordOf (x : ℕ → Bool) (n : ℕ) :
    wordCylinder (wordOf x n) = PiNat.cylinder x n := by
  ext y
  rw [mem_wordCylinder_iff, PiNat.mem_cylinder_iff]
  constructor
  · intro h i hi
    rw [← getD_wordOf (x := x) hi]
    exact h i (by simpa using hi)
  · intro h i hi
    rw [getD_wordOf (by simpa using hi)]
    exact h i (by simpa using hi)

/-! ### The graphs `G_S` -/

/-- The graph `G_S(2^ℕ)` on Cantor space associated to a set `S` of finite binary words:
edges connect `s ⌢ i ⌢ x` and `s ⌢ !i ⌢ x` for `s ∈ S`. -/
def GSGraph (S : Set (List Bool)) (y z : ℕ → Bool) : Prop :=
  ∃ s ∈ S, ∃ i : Bool, ∃ x : ℕ → Bool,
    y = prependWord (s ++ [i]) x ∧ z = prependWord (s ++ [!i]) x

/-- A set of words is dense if every word has an extension in it. -/
def DenseWords (S : Set (List Bool)) : Prop :=
  ∀ r : List Bool, ∃ s ∈ S, r <+: s

/-- A set of words is sparse if it contains at most one word of each length. The graphs
`G_S` for sparse `S` are acyclic, and the `G₀`-dichotomy holds for them. -/
def SparseWords (S : Set (List Bool)) : Prop :=
  ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ S → s.length = t.length → s = t

/-! ### A canonical dense and sparse set of words -/

/-- An enumeration of all finite binary words. -/
private def wordEnum (n : ℕ) : List Bool := (Encodable.decode (α := List Bool) n).getD []

private theorem wordEnum_encode (w : List Bool) : wordEnum (Encodable.encode w) = w := by
  simp [wordEnum, Encodable.encodek]

/-- Pad a word with `false` up to length `n`. -/
private def padTo (w : List Bool) (n : ℕ) : List Bool := w ++ List.replicate (n - w.length) false

private theorem length_padTo {w : List Bool} {n : ℕ} (h : w.length ≤ n) : (padTo w n).length = n := by
  simp only [padTo, List.length_append, List.length_replicate]
  omega

private theorem prefix_padTo (w : List Bool) (n : ℕ) : w <+: padTo w n := ⟨_, rfl⟩

/-- A strictly increasing length schedule dominating the word enumeration. -/
def canonicalLen : ℕ → ℕ
  | 0 => (wordEnum 0).length
  | n + 1 => max (wordEnum (n + 1)).length (canonicalLen n + 1)

private theorem le_canonicalLen (n : ℕ) : (wordEnum n).length ≤ canonicalLen n := by
  cases n with
  | zero => exact le_rfl
  | succ _ => exact le_max_left _ _

theorem canonicalLen_strictMono : StrictMono canonicalLen :=
  strictMono_nat_of_lt_succ fun _ =>
    lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)

/-- The `n`-th canonical word: the `n`-th word of the enumeration, padded to the `n`-th
length of the schedule. -/
def canonicalWord (n : ℕ) : List Bool := padTo (wordEnum n) (canonicalLen n)

theorem length_canonicalWord (n : ℕ) : (canonicalWord n).length = canonicalLen n :=
  length_padTo (le_canonicalLen n)

/-- The canonical dense and sparse set of finite binary words. -/
def canonicalS : Set (List Bool) := Set.range canonicalWord

theorem denseWords_canonicalS : DenseWords canonicalS := by
  intro r
  refine ⟨canonicalWord (Encodable.encode r), ⟨_, rfl⟩, ?_⟩
  rw [canonicalWord, wordEnum_encode]
  exact prefix_padTo _ _

theorem sparseWords_canonicalS : SparseWords canonicalS := by
  rintro s ⟨m, rfl⟩ t ⟨n, rfl⟩ hlen
  rw [length_canonicalWord, length_canonicalWord] at hlen
  rw [canonicalLen_strictMono.injective hlen]

/-! ### Miller's independence lemma (Prop. 6) -/

/-- **Miller, Prop. 6**: for a dense set `S` of words, a non-meager set with the Baire
property contains a `G_S`-edge (it is not `G_S`-independent). -/
theorem exists_gSGraph_edge_of_not_isMeagre
    {S : Set (List Bool)} (hS : DenseWords S)
    {B : Set (ℕ → Bool)} (hB : BaireMeasurableSet B) (hBnm : ¬ IsMeagre B) :
    ∃ y ∈ B, ∃ z ∈ B, GSGraph S y z := by
  classical
  -- Localization: B is comeager in some word cylinder
  obtain ⟨W, hW_open, hBW⟩ := hB.residualEq_isOpen
  have hsym : IsMeagre {p : ℕ → Bool | ¬(p ∈ B ↔ p ∈ W)} := by
    rw [IsMeagre, compl_ofPred]
    simp only [not_not]
    exact Filter.eventuallyEq_set.mp hBW
  have hW_ne : W.Nonempty := by
    rcases W.eq_empty_or_nonempty with rfl | h
    · exact (hBnm (hsym.mono fun p hp => by simp [hp])).elim
    · exact h
  obtain ⟨x₀, hx₀⟩ := hW_ne
  obtain ⟨V, ⟨x₁, n, rfl⟩, hx₀V, hVW⟩ :=
    (PiNat.isTopologicalBasis_cylinders (fun _ : ℕ => Bool)).exists_subset_of_mem_open
      hx₀ hW_open
  have hrW : wordCylinder (wordOf x₁ n) ⊆ W := by
    rw [wordCylinder_wordOf]
    exact hVW
  -- Extend into S
  obtain ⟨s, hsS, hrs⟩ := hS (wordOf x₁ n)
  -- The set of x missing B through either child injection is meager
  have hkey : ∀ i : Bool,
      IsMeagre (prependWord (s ++ [i]) ⁻¹' (wordCylinder (s ++ [i]) \ B)) := by
    intro i
    refine IsMeagre.preimage_of_isOpenMap (continuous_prependWord _)
      (isOpenMap_prependWord _) (hsym.mono ?_)
    rintro p ⟨hpc, hpB⟩
    have hpW : p ∈ W :=
      hrW (wordCylinder_subset_of_prefix (hrs.trans ⟨[i], rfl⟩) hpc)
    simp only [mem_ofPred_eq]
    intro h
    exact hpB (h.mpr hpW)
  -- A common point avoiding both meager sets
  have hne : ((prependWord (s ++ [false]) ⁻¹' (wordCylinder (s ++ [false]) \ B)) ∪
      (prependWord (s ++ [true]) ⁻¹' (wordCylinder (s ++ [true]) \ B)))ᶜ.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty, compl_empty_iff] at h
    exact not_isMeagre_of_isOpen isOpen_univ univ_nonempty
      (h ▸ (hkey false).union (hkey true))
  obtain ⟨x, hx⟩ := hne
  rw [mem_compl_iff, mem_union, not_or] at hx
  have hmem : ∀ i : Bool, prependWord (s ++ [i]) x ∈ B := by
    intro i
    have hin : prependWord (s ++ [i]) x ∈ wordCylinder (s ++ [i]) :=
      prependWord_mem_wordCylinder _ _
    cases i
    · by_contra hB'
      exact hx.1 ⟨hin, hB'⟩
    · by_contra hB'
      exact hx.2 ⟨hin, hB'⟩
  exact ⟨prependWord (s ++ [false]) x, hmem false, prependWord (s ++ [true]) x, hmem true,
    s, hsS, false, x, rfl, rfl⟩

/-- For dense `S`, every class of an equivalence relation disjoint from `G_S` (with Baire
measurable classes) is meager. -/
private theorem isMeagre_class_of_gSGraph_disjoint
    {S : Set (List Bool)} (hS : DenseWords S) (E : Setoid (ℕ → Bool))
    (hBP : ∀ a : ℕ → Bool, BaireMeasurableSet {b : ℕ → Bool | E.r a b})
    (hhom : ∀ y z : ℕ → Bool, GSGraph S y z → ¬ E.r y z) (a : ℕ → Bool) :
    IsMeagre {b : ℕ → Bool | E.r a b} := by
  by_contra hnm
  obtain ⟨y, hy, z, hz, hedge⟩ := exists_gSGraph_edge_of_not_isMeagre hS (hBP a) hnm
  exact hhom y z hedge (E.iseqv.trans (E.iseqv.symm hy) hz)

/-- **Pullback form (the deliverable for the category route)**: if `φ : 2^ℕ → α` is
continuous and a graph homomorphism from `G_S` (with `S` dense) to the complement of a Borel
equivalence relation `E`, then every pullback section `{b | E (φ a) (φ b)}` is meager.
Combined with Kuratowski–Ulam this makes the pullback relation meager, and with Mycielski it
produces the perfect antichain; the missing input is exactly the classical `G₀`-dichotomy
producing `φ`. -/
theorem isMeagre_pullback_class_of_gSGraph_hom
    {α : Type*} [TopologicalSpace α] [SecondCountableTopology α]
    [MeasurableSpace α] [BorelSpace α]
    (E : Setoid α) (hE : MeasurableSet {p : α × α | E.r p.1 p.2})
    {S : Set (List Bool)} (hS : DenseWords S)
    {φ : (ℕ → Bool) → α} (hφ : Continuous φ)
    (hhom : ∀ y z : ℕ → Bool, GSGraph S y z → ¬ E.r (φ y) (φ z)) (a : ℕ → Bool) :
    IsMeagre {b : ℕ → Bool | E.r (φ a) (φ b)} := by
  let E' : Setoid (ℕ → Bool) :=
    ⟨fun x y => E.r (φ x) (φ y),
      ⟨fun _ => E.iseqv.refl _,
       fun h => E.iseqv.symm h,
       fun h h' => E.iseqv.trans h h'⟩⟩
  have hBP : ∀ a : ℕ → Bool, BaireMeasurableSet {b : ℕ → Bool | E'.r a b} := by
    intro a
    have hmeas : Measurable fun b : ℕ → Bool => (φ a, φ b) :=
      (continuous_const.prodMk hφ).measurable
    exact (hmeas hE).baireMeasurableSet
  exact isMeagre_class_of_gSGraph_disjoint hS E' hBP hhom a
