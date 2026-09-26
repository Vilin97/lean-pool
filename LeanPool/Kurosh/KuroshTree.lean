/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.Kurosh

/-!
# Kurosh Tree

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshTreeDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v w

namespace GraphCoveringTheory.Kurosh

open Monoid.CoprodI

theorem Internal.rightAppendLastIdx {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (w : RightFactorWord (G := G) i)
    (a : G i) (ha : a ≠ 1) :
    wordLastIdx (rightAppendCanonical i w a ha) = some i := by
  unfold rightAppendCanonical rightAppend wordLastIdx
  rw [wordInv_wordInv]
  simp

theorem Internal.factorCentralInjective {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {i i' : ι}
    {w : RightFactorWord (G := G) i} {w' : RightFactorWord (G := G) i'}
    {a : G i} {a' : G i'} (ha : a ≠ 1) (ha' : a' ≠ 1)
    (h : rightAppendCanonical i w a ha =
      rightAppendCanonical i' w' a' ha') :
    i = i' ∧ HEq w w' ∧ HEq a a' := by
  have hlast := congrArg wordLastIdx h
  rw [Internal.rightAppendLastIdx G i w a ha,
    Internal.rightAppendLastIdx G i' w' a' ha'] at hlast
  have hii : i = i' := by injection hlast
  subst i'
  have hp : w.1.prod * Monoid.CoprodI.of a =
      w'.1.prod * Monoid.CoprodI.of a' := by
    have hp' := congrArg Word.prod h
    change (rightAppend i w.1 a ha w.2).prod =
      (rightAppend i w'.1 a' ha' w'.2).prod at hp'
    rw [rightAppend_prod, rightAppend_prod] at hp'
    exact hp'
  have hww : w.1 = w'.1 :=
    rightTail_eq_of_prod_eq_mul_factor i w w' a a' hp
  have hw : w = w' := Subtype.ext hww
  subst w'
  have haa : a = a' := by
    apply factorInclusion_injective G i
    exact (mul_left_cancel_iff.mp hp)
  subst a'
  exact ⟨rfl, HEq.rfl, HEq.rfl⟩

/-- All edges in the word model, bundled with their endpoints. -/
abbrev Internal.bassAllEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :=
  Σ a b : BassSerreVertex G, BassSerreEdge G a b

/-- Nondependent codes for the two constructors of word-model edges. -/
abbrev Internal.bassEdgeCode {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :=
  (Σ w : Word G, {i : ι // wordLastIdx w ≠ some i}) ⊕
    (Σ i : ι, Σ _w : RightFactorWord (G := G) i, {a : G i // a ≠ 1})

/-- Encode a word-model edge without its dependent endpoint indices. -/
def Internal.bassEdgeCodeOf {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Internal.bassAllEdge G → Internal.bassEdgeCode G
  | ⟨_, _, BassSerreEdge.centralFactor w i hw⟩ => Sum.inl ⟨w, ⟨i, hw⟩⟩
  | ⟨_, _, BassSerreEdge.factorCentral i w a ha⟩ => Sum.inr ⟨i, w, ⟨a, ha⟩⟩

/-- Recover a bundled word-model edge from its constructor code. -/
def Internal.bassEdgeOfCode {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Internal.bassEdgeCode G → Internal.bassAllEdge G
  | Sum.inl ⟨w, ⟨i, hw⟩⟩ =>
      ⟨BassSerreVertex.central w, BassSerreVertex.factor i ⟨w, hw⟩,
        BassSerreEdge.centralFactor w i hw⟩
  | Sum.inr ⟨i, w, ⟨a, ha⟩⟩ =>
      ⟨BassSerreVertex.factor i w,
        BassSerreVertex.central (rightAppendCanonical i w a ha),
        BassSerreEdge.factorCentral i w a ha⟩

theorem Internal.bassEdgeCodeOf_ofCode {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (c : Internal.bassEdgeCode G) :
    Internal.bassEdgeCodeOf G (Internal.bassEdgeOfCode G c) = c := by
  cases c using Sum.casesOn with
  | inl c => cases c; rfl
  | inr c => cases c; rfl

theorem Internal.bassEdgeOfCode_of {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (e : Internal.bassAllEdge G) :
    Internal.bassEdgeOfCode G (Internal.bassEdgeCodeOf G e) = e := by
  rcases e with ⟨a, b, e⟩
  cases e using BassSerreEdge.casesOn with
  | centralFactor w i hw => rfl
  | factorCentral i w a ha => rfl

/-- The target of a bundled word-model edge. -/
def Internal.bassEdgeTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Internal.bassAllEdge G → BassSerreVertex G :=
  fun e => e.2.1

/-- Compute the target vertex directly from an edge code. -/
def Internal.bassEdgeCodeTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Internal.bassEdgeCode G → BassSerreVertex G
  | Sum.inl ⟨w, ⟨i, hw⟩⟩ => BassSerreVertex.factor i ⟨w, hw⟩
  | Sum.inr ⟨i, w, ⟨a, ha⟩⟩ =>
      BassSerreVertex.central (rightAppendCanonical i w a ha)

theorem Internal.bassEdgeTarget_ofCode {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (c : Internal.bassEdgeCode G) :
    Internal.bassEdgeTarget G (Internal.bassEdgeOfCode G c) =
      Internal.bassEdgeCodeTarget G c := by
  cases c using Sum.casesOn with
  | inl c => cases c; rfl
  | inr c => cases c; rfl

theorem Internal.bassEdgeCodeTarget_injective {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {c d : Internal.bassEdgeCode G}
    (h : Internal.bassEdgeCodeTarget G c = Internal.bassEdgeCodeTarget G d) : c = d := by
  rcases c with (⟨w, ⟨i, hw⟩⟩ | ⟨i, w, ⟨a, ha⟩⟩)
  · rcases d with (⟨w', ⟨i', hw'⟩⟩ | ⟨i', w', ⟨a', ha'⟩⟩)
    · have hii : i = i' := by injection h
      subst i'
      have hww : w = w' := by
        have hs : (⟨w, hw⟩ : RightFactorWord (G := G) i) =
            ⟨w', hw'⟩ := by injection h
        exact congrArg Subtype.val hs
      subst w'
      congr
    · cases h
  · rcases d with (⟨w', ⟨i', hw'⟩⟩ | ⟨i', w', ⟨a', ha'⟩⟩)
    · cases h
    · have htarget : rightAppendCanonical i w a ha =
          rightAppendCanonical i' w' a' ha' := by
        injection h
      have hlast := congrArg wordLastIdx htarget
      rw [Internal.rightAppendLastIdx G i w a ha,
        Internal.rightAppendLastIdx G i' w' a' ha'] at hlast
      have hii : i = i' := by injection hlast
      subst i'
      have hp := Internal.factorCentralInjective G ha ha' htarget
      have hwi : HEq w w' := hp.2.1
      have hai : HEq a a' := hp.2.2
      cases hwi
      cases hai
      rfl

theorem Internal.bassAllEdge_target_injective {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {e f : Internal.bassAllEdge G}
    (h : Internal.bassEdgeTarget G e = Internal.bassEdgeTarget G f) : e = f := by
  have hc : Internal.bassEdgeCodeOf G e = Internal.bassEdgeCodeOf G f := by
    apply Internal.bassEdgeCodeTarget_injective G
    rw [← Internal.bassEdgeTarget_ofCode G (Internal.bassEdgeCodeOf G e),
      ← Internal.bassEdgeTarget_ofCode G (Internal.bassEdgeCodeOf G f),
      Internal.bassEdgeOfCode_of G e, Internal.bassEdgeOfCode_of G f]
    exact h
  calc
    e = Internal.bassEdgeOfCode G (Internal.bassEdgeCodeOf G e) :=
      (Internal.bassEdgeOfCode_of G e).symm
    _ = Internal.bassEdgeOfCode G (Internal.bassEdgeCodeOf G f) :=
      congrArg (Internal.bassEdgeOfCode G) hc
    _ = f := Internal.bassEdgeOfCode_of G f

theorem Internal.bassUniqueIncoming {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b c : BassSerreVertex G}
    (e : a ⟶ c) (f : b ⟶ c) : a = b ∧ HEq e f := by
  have h_all : (⟨a, c, e⟩ : Internal.bassAllEdge G) = ⟨b, c, f⟩ := by
    apply Internal.bassAllEdge_target_injective G
    rfl
  cases h_all
  exact ⟨rfl, HEq.rfl⟩

theorem Internal.wordLastIdx_exists {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (w : Word G) (hw : w.toList ≠ []) :
    ∃ i, wordLastIdx w = some i := by
  unfold wordLastIdx Word.fstIdx
  change ∃ i, ((wordInv w).toList.head?.map Sigma.fst) = some i
  rw [wordInv_toList]
  have hrev : w.toList.reverse ≠ [] := by
    intro h
    apply hw
    have h' := congrArg List.reverse h
    simpa using h'
  cases h : w.toList.reverse with
  | nil => exact False.elim (hrev h)
  | cons x xs =>
      refine ⟨x.1, ?_⟩
      simp

theorem Internal.bassRootOrArrow {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (b : BassSerreVertex G) :
    b = BassSerreVertex.central Word.empty ∨
      ∃ a, Nonempty (a ⟶ b) := by
  cases b with
  | factor i w =>
      exact Or.inr ⟨BassSerreVertex.central w.1,
        ⟨BassSerreEdge.centralFactor w.1 i w.2⟩⟩
  | central w =>
      by_cases hroot : w = Word.empty
      · exact Or.inl (congrArg BassSerreVertex.central hroot)
      · have hw : w.toList ≠ [] := by
          intro hnil
          apply hroot
          apply Word.ext
          exact hnil
        rcases Internal.wordLastIdx_exists G w hw with ⟨i, hi⟩
        let wt := rightTailCanonical i w
        let a := rightHead i w
        have ha : a ≠ 1 := rightHead_ne_one_of_lastIdx_eq i w hi
        have happend : rightAppendCanonical i wt a ha = w := by
          exact rightAppendCanonical_of_lastIdx_eq i w hi
        refine Or.inr ⟨BassSerreVertex.factor i wt, ?_⟩
        refine ⟨Quiver.Hom.cast rfl (congrArg BassSerreVertex.central happend)
          (BassSerreEdge.factorCentral i wt a ha)⟩

/-- Twice the reduced-word length, plus one at factor vertices. -/
def Internal.bassHeight {ι : Type v} (G : ι → Type u) [∀ i, Group (G i)] :
    BassSerreVertex G → ℕ
  | BassSerreVertex.central w => 2 * w.toList.length
  | BassSerreVertex.factor _ w => 2 * w.1.toList.length + 1

theorem Internal.bassHeight_lt {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G} (e : a ⟶ b) :
    Internal.bassHeight G a < Internal.bassHeight G b := by
  cases e using BassSerreEdge.casesOn with
  | centralFactor w i hw => simp [Internal.bassHeight]
  | factorCentral i w a ha =>
      simp [Internal.bassHeight, rightAppendCanonical, rightAppend, wordInv]
      omega

/-- The directed word model is an arborescence rooted at the empty word. -/
@[instance_reducible] noncomputable def Internal.bassSerreFullArborescence {ι : Type v}
    (G : ι → Type u)
    [∀ i, Group (G i)] :
    @Quiver.Arborescence (BassSerreVertex G) (bassSerreQuiver G) := by
  exact Quiver.arborescenceMk
    (BassSerreVertex.central Word.empty)
    (fun b => match b with
      | BassSerreVertex.central w => 2 * w.toList.length
      | BassSerreVertex.factor _ w => 2 * w.1.toList.length + 1)
    (by
      intro a b e
      exact Internal.bassHeight_lt G e)
    (by
      intro a b c e f
      exact Internal.bassUniqueIncoming G e f)
    (by
      intro b
      exact Internal.bassRootOrArrow G b)

theorem Internal.bassHeight_root {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Internal.bassHeight G (BassSerreVertex.central Word.empty) = 0 := by
  rfl

theorem Internal.bassHeight_edge_eq_succ {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G} (e : a ⟶ b) :
    Internal.bassHeight G b = Internal.bassHeight G a + 1 := by
  cases e using BassSerreEdge.casesOn with
  | centralFactor w i hw => simp [Internal.bassHeight]
  | factorCentral i w a ha =>
      simp [Internal.bassHeight, rightAppendCanonical, rightAppend, wordInv]
      omega

/-- The word-length height function on symmetrified word-model vertices. -/
def Internal.bassSymmHeight {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (x : Quiver.Symmetrify (BassSerreVertex G)) : ℕ :=
  Internal.bassHeight G x

theorem Internal.bassHeight_symm_edge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G}
    (e : @Quiver.Hom (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) a b) :
    Internal.bassSymmHeight G b = Internal.bassSymmHeight G a + 1 ∨
      Internal.bassSymmHeight G a = Internal.bassSymmHeight G b + 1 := by
  cases e using Sum.casesOn with
  | inl e => exact Or.inl (Internal.bassHeight_edge_eq_succ G e)
  | inr e =>
      exact Or.inr (Internal.bassHeight_edge_eq_succ G e)

theorem Internal.bassHeight_path_le {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G}
    (p : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) a b) :
    Internal.bassSymmHeight G b ≤ Internal.bassSymmHeight G a + p.length := by
  induction p with
  | nil => exact le_rfl
  | @cons x y p e ih =>
      have he := Internal.bassHeight_symm_edge G e
      change Internal.bassSymmHeight G _ ≤
        Internal.bassSymmHeight G _ +
          (@Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
            (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p + 1)
      rcases he with he | he <;> omega

theorem Internal.bassHeight_directed_path_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G}
    (p : @Quiver.Path (BassSerreVertex G) (bassSerreQuiver G) a b) :
    Internal.bassHeight G b = Internal.bassHeight G a + p.length := by
  induction p with
  | nil => simp
  | cons p e ih =>
      simp only [Quiver.Path.length_cons]
      rw [Internal.bassHeight_edge_eq_succ G e, ih]
      omega

theorem Internal.bassHeight_zero_iff {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {b : BassSerreVertex G} :
    Internal.bassHeight G b = 0 ↔ b = BassSerreVertex.central Word.empty := by
  constructor
  · cases b with
    | central w =>
        intro h
        have hw : w.toList.length = 0 := by simpa [Internal.bassHeight] using h
        have hw' : w.toList = [] := List.eq_nil_of_length_eq_zero hw
        apply congrArg BassSerreVertex.central
        apply Word.ext
        exact hw'
    | factor i w =>
        intro h
        simp [Internal.bassHeight] at h
  · intro h
    subst h
    exact Internal.bassHeight_root G

/-- Include the directed word model into its symmetrification. -/
def Internal.bassToSymm {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    BassSerreVertex G ⥤q Quiver.Symmetrify (BassSerreVertex G) where
  obj := id
  map e := Quiver.Hom.toPos e

theorem Internal.bassToSymm_mapPath_length {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G}
    (p : @Quiver.Path (BassSerreVertex G) (bassSerreQuiver G) a b) :
    (@Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _
      ((Internal.bassToSymm G).mapPath p)) = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (@Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _
        ((Internal.bassToSymm G).mapPath p) + 1) = p.length + 1
      rw [ih]

theorem Internal.bassSymmPath_of_length_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {b : BassSerreVertex G}
    (p : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G))
      (BassSerreVertex.central Word.empty) b)
    (hp : @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p =
        Internal.bassSymmHeight G b) :
    ∃ q : @Quiver.Path (BassSerreVertex G) (bassSerreQuiver G)
      (BassSerreVertex.central Word.empty) b,
      (Internal.bassToSymm G).mapPath q = p := by
  induction p with
  | nil =>
      exact ⟨Quiver.Path.nil, rfl⟩
  | @cons x y p e ih =>
      have hle := Internal.bassHeight_path_le G p
      have he := Internal.bassHeight_symm_edge G e
      have hroot : Internal.bassSymmHeight G
          (BassSerreVertex.central Word.empty) = 0 := by
        simp [Internal.bassSymmHeight, Internal.bassHeight_root]
      change @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
          (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p + 1 =
        Internal.bassSymmHeight G _ at hp
      have hp' : Internal.bassSymmHeight G y =
          @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
            (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p + 1 := hp.symm
      rcases he with he | he
      · have hprev : @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
            (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p =
            Internal.bassSymmHeight G x := by omega
        rcases ih hprev with ⟨q, hq⟩
        cases e using Sum.casesOn with
        | inl e =>
            refine ⟨q.cons e, ?_⟩
            rw [Prefunctor.mapPath_cons]
            rw [hq]
            rfl
        | inr e =>
            exfalso
            have he' := Internal.bassHeight_edge_eq_succ G e
            have he'' : Internal.bassSymmHeight G x =
                Internal.bassSymmHeight G y + 1 := by
              simpa [Internal.bassSymmHeight] using he'
            omega
      · exfalso
        have hbad' : Internal.bassSymmHeight G x ≤
            @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
              (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p := by
          simpa [Internal.bassSymmHeight, Internal.bassHeight_root] using hle
        have hxy : Internal.bassSymmHeight G y + 1 ≤
            @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
              (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p := by
          exact le_trans (he.symm ▸ le_rfl) hbad'
        have hbad'' :
            @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
                (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p + 1 + 1 ≤
              @Quiver.Path.length (Quiver.Symmetrify (BassSerreVertex G))
                (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ p := by
          simp [hp'] at hxy
        omega

theorem Internal.bass_edge_mem_geodesicTree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G} (e : a ⟶ b) :
    Quiver.Hom.toPos e ∈ bassSerreTree G a b := by
  let : @Quiver.Arborescence (BassSerreVertex G) (bassSerreQuiver G) :=
    Internal.bassSerreFullArborescence G
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (BassSerreVertex G) from
        BassSerreVertex.central Word.empty) := bassSerre_rootedConnected G
  let : Unique (@Quiver.Path (BassSerreVertex G) (bassSerreQuiver G)
      (BassSerreVertex.central Word.empty) a) :=
    @Quiver.Arborescence.uniquePath (BassSerreVertex G) (bassSerreQuiver G)
      (Internal.bassSerreFullArborescence G) a
  let p : @Quiver.Path (BassSerreVertex G) (bassSerreQuiver G)
      (BassSerreVertex.central Word.empty) a := default
  let q := p.cons e
  have hq : q.length = Internal.bassHeight G b := by
    have hp' : Internal.bassHeight G a = p.length := by
      have h := Internal.bassHeight_directed_path_eq G p
      simpa [Internal.bassHeight_root] using h
    have he' := Internal.bassHeight_edge_eq_succ G e
    change p.length + 1 = Internal.bassHeight G b
    omega
  let qSymm : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G))
      (BassSerreVertex.central Word.empty) b :=
    (Internal.bassToSymm G).mapPath q
  have hqSymm : qSymm.length = Internal.bassSymmHeight G b := by
    dsimp [qSymm]
    exact (Internal.bassToSymm_mapPath_length G q).trans
      (by simpa [Internal.bassSymmHeight] using hq)
  let short : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G))
      (BassSerreVertex.central Word.empty) b :=
    @Quiver.shortestPath (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G))
      (BassSerreVertex.central Word.empty) (bassSerre_rootedConnected G) b
  have hshort : short.length = Internal.bassHeight G b := by
    apply le_antisymm
    · exact le_trans (@Quiver.shortest_path_spec
        (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G))
        (BassSerreVertex.central Word.empty) (bassSerre_rootedConnected G) _ qSymm)
        (le_of_eq (by simpa [Internal.bassSymmHeight] using hqSymm))
    · have hroot := Internal.bassHeight_root G
      have hle := Internal.bassHeight_path_le G short
      change Internal.bassHeight G b ≤
        Internal.bassHeight G (BassSerreVertex.central Word.empty) + short.length at hle
      omega
  rcases Internal.bassSymmPath_of_length_eq G short hshort with
    ⟨q', hq'⟩
  let : Unique (@Quiver.Path (BassSerreVertex G) (bassSerreQuiver G)
      (BassSerreVertex.central Word.empty) b) :=
    @Quiver.Arborescence.uniquePath (BassSerreVertex G) (bassSerreQuiver G)
      (Internal.bassSerreFullArborescence G) b
  have hqp : q' = q := Subsingleton.elim _ _
  have hshort' : short = qSymm := by
    rw [← hq']
    rw [hqp]
  change ∃ r : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G))
      (BassSerreVertex.central Word.empty) a,
      short = r.cons (Quiver.Hom.toPos e)
  refine ⟨(Internal.bassToSymm G).mapPath p, ?_⟩
  rw [hshort']
  dsimp [qSymm, q]
  simp [Internal.bassToSymm]
theorem Internal.rightTailCanonical_factorCoset_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (g h : FreeProduct G)
    (hc : factorCosetMk G i g = factorCosetMk G i h) :
    rightTailCanonical i (Word.equiv g) =
      rightTailCanonical i (Word.equiv h) := by
  rw [factorCosetMk, factorCosetMk, rightCosetMk_eq_iff
    (MonoidHom.range (factorInclusion G i)) g h] at hc
  rcases hc with ⟨k, hk⟩
  rcases k.property with ⟨a, ha⟩
  have hga : g * Monoid.CoprodI.of a = h := by
    change Monoid.CoprodI.of a = (k : FreeProduct G) at ha
    rw [← ha] at hk
    exact hk
  have hg : g = (rightTailCanonical i (Word.equiv g)).1.prod *
      Monoid.CoprodI.of (rightHead i (Word.equiv g)) := by
    simpa [rightTailCanonical] using
      (right_syllable_decomposition i (Word.equiv g)).symm.trans
        ((Word.equiv).symm_apply_apply g) |>.symm
  have hh : h = (rightTailCanonical i (Word.equiv h)).1.prod *
      Monoid.CoprodI.of (rightHead i (Word.equiv h)) := by
    simpa [rightTailCanonical] using
      (right_syllable_decomposition i (Word.equiv h)).symm.trans
        ((Word.equiv).symm_apply_apply h) |>.symm
  apply Subtype.ext
  apply rightTail_eq_of_prod_eq_mul_factor i
    (rightTailCanonical i (Word.equiv g))
    (rightTailCanonical i (Word.equiv h))
    (rightHead i (Word.equiv g) * a)
    (rightHead i (Word.equiv h))
  calc
    (rightTailCanonical i (Word.equiv g)).1.prod *
        Monoid.CoprodI.of (rightHead i (Word.equiv g) * a) =
      ((rightTailCanonical i (Word.equiv g)).1.prod *
        Monoid.CoprodI.of (rightHead i (Word.equiv g))) *
          Monoid.CoprodI.of a := by
            rw [map_mul, mul_assoc]
    _ = g * Monoid.CoprodI.of a :=
      congrArg (fun z : FreeProduct G => z * Monoid.CoprodI.of a) hg.symm
    _ = h := hga
    _ = (rightTailCanonical i (Word.equiv h)).1.prod *
        Monoid.CoprodI.of (rightHead i (Word.equiv h)) := hh

/-- Choose the canonical reduced-word representative of a factor coset. -/
noncomputable def Internal.rawCanonicalFactor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (c : FactorCoset G i) :
    RightFactorWord (G := G) i :=
  rightTailCanonical i (Word.equiv (Quotient.out c))

/-- Convert a group-and-coset vertex into its canonical word-model vertex. -/
noncomputable def Internal.rawCanonicalVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : RawBassSerreVertex G → BassSerreVertex G
  | RawBassSerreVertex.central g => BassSerreVertex.central (Word.equiv g)
  | RawBassSerreVertex.factor i c =>
      BassSerreVertex.factor i (Internal.rawCanonicalFactor G i c)

/-- Evaluate a word-model vertex in the group-and-coset model. -/
def Internal.bassToRawVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : BassSerreVertex G → RawBassSerreVertex G
  | BassSerreVertex.central w => RawBassSerreVertex.central w.prod
  | BassSerreVertex.factor i w =>
      RawBassSerreVertex.factor i (factorCosetMk G i w.1.prod)

theorem Internal.rawCanonicalFactor_coset {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (c : FactorCoset G i) :
    factorCosetMk G i (Internal.rawCanonicalFactor G i c).1.prod = c := by
  let g : FreeProduct G := Quotient.out c
  have hc : factorCosetMk G i g = c := by
    simp [g, factorCosetMk, rightCosetMk]
  have hdec : g = (Internal.rawCanonicalFactor G i c).1.prod *
      Monoid.CoprodI.of (rightHead i (Word.equiv g)) := by
    change g = (rightTail i (Word.equiv g)).prod *
      Monoid.CoprodI.of (rightHead i (Word.equiv g))
    calc
      g = (Word.equiv g).prod := ((Word.equiv).symm_apply_apply g).symm
      _ = (rightTail i (Word.equiv g)).prod *
          Monoid.CoprodI.of (rightHead i (Word.equiv g)) :=
        right_syllable_decomposition i (Word.equiv g)
  calc
    factorCosetMk G i (Internal.rawCanonicalFactor G i c).1.prod =
        factorCosetMk G i
          ((Internal.rawCanonicalFactor G i c).1.prod *
            Monoid.CoprodI.of (rightHead i (Word.equiv g))) := by
              symm
              exact factorCoset_mul_factor G i _ _
    _ = factorCosetMk G i g :=
      congrArg (factorCosetMk G i) hdec.symm
    _ = c := hc

theorem Internal.bassToRawVertex_rawCanonicalVertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (x : RawBassSerreVertex G) :
    Internal.bassToRawVertex G (Internal.rawCanonicalVertex G x) = x := by
  cases x with
  | central g =>
      change RawBassSerreVertex.central (Word.equiv g).prod = _
      have hg : (Word.equiv g).prod = g := (Word.equiv).symm_apply_apply g
      rw [hg]
  | factor i c =>
      change RawBassSerreVertex.factor i
        (factorCosetMk G i (Internal.rawCanonicalFactor G i c).1.prod) = _
      rw [Internal.rawCanonicalFactor_coset]

theorem Internal.rawCanonicalVertex_bassToRawVertex {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (x : BassSerreVertex G) :
    Internal.rawCanonicalVertex G (Internal.bassToRawVertex G x) = x := by
  cases x with
  | central w =>
      change BassSerreVertex.central (Word.equiv w.prod) = _
      have hw : Word.equiv w.prod = w := (Word.equiv).apply_symm_apply w
      rw [hw]
  | factor i w =>
      let c := factorCosetMk G i w.1.prod
      have hc : factorCosetMk G i (Quotient.out c) =
          factorCosetMk G i w.1.prod := by
        simp [c, factorCosetMk, rightCosetMk]
      have ht := Internal.rightTailCanonical_factorCoset_eq G i
        (Quotient.out c) w.1.prod hc
      have hw : rightTailCanonical i (Word.equiv w.1.prod) = w := by
        apply Subtype.ext
        have hw' : Word.equiv w.1.prod = w.1 :=
          (Word.equiv).apply_symm_apply w.1
        rw [hw']
        exact rightTail_of_lastIdx_ne i w.1 w.2
      change BassSerreVertex.factor i
        (Internal.rawCanonicalFactor G i c) = BassSerreVertex.factor i w
      apply congrArg (BassSerreVertex.factor i)
      exact ht.trans hw

/-- The chosen word-model spanning tree on the ambient vertex type. -/
@[reducible] def Internal.bassTreeQuiver {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Quiver (BassSerreVertex G) :=
  { Hom := fun a b =>
      { e : @Quiver.Hom (Quiver.Symmetrify (BassSerreVertex G))
          (@Quiver.symmetrifyQuiver (BassSerreVertex G)
            (bassSerreQuiver G)) a b //
        e ∈ bassSerreTree G a b } }

instance Internal.bassTreeQuiverArborescence {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) := by
  change Quiver.Arborescence (bassSerreTree G)
  exact bassSerreTreeArborescence G

/-- The unique path in the chosen word-model tree from the empty word. -/
noncomputable def Internal.bassTreePath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (x : BassSerreVertex G) :
    @Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
      (BassSerreVertex.central Word.empty) x := by
  letI : @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) :=
    Internal.bassTreeQuiverArborescence G
  letI : Unique (@Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
      (BassSerreVertex.central Word.empty) x) :=
    @Quiver.Arborescence.uniquePath (BassSerreVertex G)
      (Internal.bassTreeQuiver G) (Internal.bassTreeQuiverArborescence G) x
  exact default

/-- Forget membership in the chosen word-model spanning tree along a path. -/
def Internal.bassTreePathMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y : BassSerreVertex G} :
    @Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G) x y →
      @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y
  | @Quiver.Path.nil (BassSerreVertex G) (Internal.bassTreeQuiver G) x =>
      @Quiver.Path.nil (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) x
  | @Quiver.Path.cons (BassSerreVertex G) (Internal.bassTreeQuiver G)
      x y z p e =>
      @Quiver.Path.cons (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y z
        (Internal.bassTreePathMap G p) e.1

theorem Internal.bassTreePathMap_cons {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y z : BassSerreVertex G}
    (p : @Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G) x y)
    (e : @Quiver.Hom (BassSerreVertex G) (Internal.bassTreeQuiver G) y z) :
    Internal.bassTreePathMap G (@Quiver.Path.cons (BassSerreVertex G)
      (Internal.bassTreeQuiver G) x y z p e) =
      @Quiver.Path.cons (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y z
        (Internal.bassTreePathMap G p) e.1 := by
  rfl

theorem Internal.bassTreePathMap_edge_pos {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y : BassSerreVertex G}
    (e : x ⟶ y) (he : Quiver.Hom.toPos e ∈ bassSerreTree G x y) :
    Internal.bassTreePathMap G (Internal.bassTreePath G y) =
      (Internal.bassTreePathMap G (Internal.bassTreePath G x)).cons
        (Quiver.Hom.toPos e) := by
  let te : @Quiver.Hom (BassSerreVertex G) (Internal.bassTreeQuiver G) x y :=
    ⟨Quiver.Hom.toPos e, he⟩
  have hp : Internal.bassTreePath G y =
      @Quiver.Path.cons (BassSerreVertex G) (Internal.bassTreeQuiver G) _ _ _
        (Internal.bassTreePath G x) te := by
    let : @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) :=
      Internal.bassTreeQuiverArborescence G
    let : Unique (@Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
        (BassSerreVertex.central Word.empty) y) :=
      @Quiver.Arborescence.uniquePath (BassSerreVertex G)
        (Internal.bassTreeQuiver G) (Internal.bassTreeQuiverArborescence G) y
    exact Subsingleton.elim _ _
  rw [hp]
  rfl

/-- Interpret a symmetrified word-model path in its free groupoid. -/
noncomputable def Internal.bassPathHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x : BassSerreVertex G} :
    ∀ {y : BassSerreVertex G},
      @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y →
        @Quiver.Hom (Quiver.FreeGroupoid (BassSerreVertex G))
          _ ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj x)
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj y)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e =>
      Internal.bassPathHom G p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f))

theorem Internal.bassPathHom_nil {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x : BassSerreVertex G} :
    Internal.bassPathHom G
        (Quiver.Path.nil : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
          (Quiver.symmetrifyQuiver (BassSerreVertex G)) x x) = 𝟙 _ := by
  rfl

theorem Internal.bassPathHom_cons {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y z : BassSerreVertex G}
    (p : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y)
    (e : @Quiver.Hom (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) y z) :
    Internal.bassPathHom G (p.cons e) =
      Internal.bassPathHom G p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f)) := by
  cases p with
  | nil => cases e using Sum.casesOn <;> rfl
  | cons p e' => cases e using Sum.casesOn <;> cases e' using Sum.casesOn <;>
      simp [Internal.bassPathHom, Category.assoc]

theorem Internal.bassQuotientMap_cons {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y z : BassSerreVertex G}
    (p : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y)
    (e : @Quiver.Hom (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) y z) :
    (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (BassSerreVertex G)
          (bassSerreQuiver G))).map
        (@Quiver.Path.cons (Quiver.Symmetrify (BassSerreVertex G))
          (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y z p e) =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (BassSerreVertex G)
          (bassSerreQuiver G))).map p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f)) := by
  cases e using Sum.casesOn with
  | inl e => rfl
  | inr e => rfl

theorem Internal.bassPathHom_eq_quotient_map {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y : BassSerreVertex G}
    (p : @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
      (Quiver.symmetrifyQuiver (BassSerreVertex G)) x y) :
    Internal.bassPathHom G p =
      (CategoryTheory.Quotient.functor
        (@Quiver.FreeGroupoid.redStep (BassSerreVertex G)
          (bassSerreQuiver G))).map p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      have hcons := Internal.bassPathHom_cons G p e
      have hmid :
          Internal.bassPathHom G p ≫
              (match e with
              | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
              | Sum.inr f =>
                  Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f)) =
            (CategoryTheory.Quotient.functor
                (@Quiver.FreeGroupoid.redStep (BassSerreVertex G)
                  (bassSerreQuiver G))).map p ≫
              (match e with
              | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
              | Sum.inr f =>
                  Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f)) := by
        rw [ih]
        cases e using Sum.casesOn <;> rfl
      exact Eq.trans hcons (Eq.trans hmid
        (Internal.bassQuotientMap_cons G p e).symm)

theorem Internal.bassTreePathHom_edge_neg {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x y : BassSerreVertex G}
    (e : x ⟶ y) (he : Quiver.Hom.toPos e ∈ bassSerreTree G x y) :
    Internal.bassPathHom G (Internal.bassTreePathMap G (Internal.bassTreePath G y)) ≫
        Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map e) =
      Internal.bassPathHom G (Internal.bassTreePathMap G (Internal.bassTreePath G x)) := by
  let te : @Quiver.Hom (BassSerreVertex G) (Internal.bassTreeQuiver G) x y :=
    ⟨Quiver.Hom.toPos e, he⟩
  have hp : Internal.bassTreePath G y =
      @Quiver.Path.cons (BassSerreVertex G) (Internal.bassTreeQuiver G) _ _ _
        (Internal.bassTreePath G x) te := by
    let : @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) :=
      Internal.bassTreeQuiverArborescence G
    let : Unique (@Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
        (BassSerreVertex.central Word.empty) y) :=
      @Quiver.Arborescence.uniquePath (BassSerreVertex G)
        (Internal.bassTreeQuiver G) (Internal.bassTreeQuiverArborescence G) y
    exact Subsingleton.elim _ _
  rw [hp, Internal.bassTreePathMap_cons, Internal.bassPathHom_cons]
  simp [te]

theorem Internal.bassPathHom_eq_tree {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {x : BassSerreVertex G} (p :
      @Quiver.Path (Quiver.Symmetrify (BassSerreVertex G))
        (Quiver.symmetrifyQuiver (BassSerreVertex G))
        (BassSerreVertex.central Word.empty) x) :
    Internal.bassPathHom G p =
      Internal.bassPathHom G (Internal.bassTreePathMap G (Internal.bassTreePath G x)) := by
  induction p with
  | nil =>
      let : Quiver (BassSerreVertex G) := Internal.bassTreeQuiver G
      have hp : Internal.bassTreePath G (BassSerreVertex.central Word.empty) =
          (Quiver.Path.nil : @Quiver.Path (BassSerreVertex G)
            (Internal.bassTreeQuiver G) (BassSerreVertex.central Word.empty)
            (BassSerreVertex.central Word.empty)) := by
        let : @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) :=
          Internal.bassTreeQuiverArborescence G
        let : Unique (@Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
            (BassSerreVertex.central Word.empty)
            (BassSerreVertex.central Word.empty)) :=
          @Quiver.Arborescence.uniquePath (BassSerreVertex G)
            (Internal.bassTreeQuiver G) (Internal.bassTreeQuiverArborescence G)
            (BassSerreVertex.central Word.empty)
        exact Subsingleton.elim _ _
      rw [hp]
      rfl
  | @cons y z p e ih =>
      have hcons := Internal.bassPathHom_cons G p e
      calc
        Internal.bassPathHom G (@Quiver.Path.cons (Quiver.Symmetrify (BassSerreVertex G))
            (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ _ p e) =
            Internal.bassPathHom G p ≫
              (match e with
              | Sum.inl f => (Quiver.FreeGroupoid.of (BassSerreVertex G)).map f
              | Sum.inr f =>
                  Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map f)) := hcons
        _ = Internal.bassPathHom G (Internal.bassTreePathMap G (Internal.bassTreePath G z)) := by
          rw [ih]
          cases e using Sum.casesOn with
          | inl e =>
              change Internal.bassPathHom G
                  (Internal.bassTreePathMap G (Internal.bassTreePath G y)) ≫
                (Quiver.FreeGroupoid.of (BassSerreVertex G)).map e =
                Internal.bassPathHom G
                  (Internal.bassTreePathMap G (Internal.bassTreePath G z))
              have he : Quiver.Hom.toPos e ∈ bassSerreTree G y z :=
                Internal.bass_edge_mem_geodesicTree G e
              have hp := Internal.bassTreePathMap_edge_pos G e he
              calc
                Internal.bassPathHom G
                      (Internal.bassTreePathMap G (Internal.bassTreePath G y)) ≫
                    (Quiver.FreeGroupoid.of (BassSerreVertex G)).map e =
                  Internal.bassPathHom G
                    (@Quiver.Path.cons (Quiver.Symmetrify (BassSerreVertex G))
                      (Quiver.symmetrifyQuiver (BassSerreVertex G)) _ _ _
                      (Internal.bassTreePathMap G (Internal.bassTreePath G y))
                      (Quiver.Hom.toPos e)) :=
                  (Internal.bassPathHom_cons G
                    (Internal.bassTreePathMap G (Internal.bassTreePath G y))
                    (Quiver.Hom.toPos e)).symm
                _ = Internal.bassPathHom G
                    (Internal.bassTreePathMap G (Internal.bassTreePath G z)) := by
                  rw [hp]
          | inr e =>
              change Internal.bassPathHom G
                  (Internal.bassTreePathMap G (Internal.bassTreePath G y)) ≫
                Groupoid.inv ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map e) =
                Internal.bassPathHom G
                  (Internal.bassTreePathMap G (Internal.bassTreePath G z))
              have he : Quiver.Hom.toPos e ∈ bassSerreTree G z y :=
                Internal.bass_edge_mem_geodesicTree G e
              exact Internal.bassTreePathHom_edge_neg G e he

theorem Internal.bassFreeGroupoid_end_subsingleton {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Subsingleton (End ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
      (BassSerreVertex.central Word.empty))) := by
  have hid : ∀ f : End ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
      (BassSerreVertex.central Word.empty)), f = 𝟙 _ := by
    intro f
    obtain ⟨p, hp⟩ :=
      (CategoryTheory.Quotient.full_functor
        (@Quiver.FreeGroupoid.redStep (BassSerreVertex G)
          (bassSerreQuiver G))).map_surjective f
    rw [← hp]
    rw [← Internal.bassPathHom_eq_quotient_map G p]
    have htree := Internal.bassPathHom_eq_tree G p
    rw [htree]
    have hroot : Internal.bassTreePath G (BassSerreVertex.central Word.empty) =
        (@Quiver.Path.nil (BassSerreVertex G) (Internal.bassTreeQuiver G)
          (BassSerreVertex.central Word.empty)) := by
      let : Quiver (BassSerreVertex G) := Internal.bassTreeQuiver G
      let : @Quiver.Arborescence (BassSerreVertex G) (Internal.bassTreeQuiver G) :=
        Internal.bassTreeQuiverArborescence G
      let : Unique (@Quiver.Path (BassSerreVertex G) (Internal.bassTreeQuiver G)
          (BassSerreVertex.central Word.empty)
          (BassSerreVertex.central Word.empty)) :=
        @Quiver.Arborescence.uniquePath (BassSerreVertex G)
          (Internal.bassTreeQuiver G) (Internal.bassTreeQuiverArborescence G)
          (BassSerreVertex.central Word.empty)
      exact Subsingleton.elim _ _
    rw [hroot]
    rfl
  exact ⟨fun f g => (hid f).trans (hid g).symm⟩

/-- Interpret a symmetrified quiver path in the quiver's free groupoid. -/
noncomputable def Internal.freePathHom {V : Type u} [q : Quiver.{v} V] {a : V} :
    ∀ {b : V},
      @Quiver.Path (Quiver.Symmetrify V) _ a b →
        @Quiver.Hom (Quiver.FreeGroupoid V) _
          ((Quiver.FreeGroupoid.of V).obj a)
          ((Quiver.FreeGroupoid.of V).obj b)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e =>
      Internal.freePathHom p ≫
        (match e with
        | Sum.inl f => (Quiver.FreeGroupoid.of V).map f
        | Sum.inr f => Groupoid.inv ((Quiver.FreeGroupoid.of V).map f))

theorem Internal.freeGroupoid_isConnected_of_basedPaths {V : Type u}
    [q : Quiver.{v} V] (r : V)
    [Quiver.RootedConnected (show Quiver.Symmetrify V from r)] :
    IsConnected (Quiver.FreeGroupoid V) := by
  let : Nonempty (Quiver.FreeGroupoid V) :=
    ⟨(Quiver.FreeGroupoid.of V).obj r⟩
  apply zigzag_isConnected
  intro a b
  have ha : Nonempty (@Quiver.Path (Quiver.Symmetrify V) _ r a.as) :=
    @Quiver.RootedConnected.nonempty_path (Quiver.Symmetrify V)
      (Quiver.symmetrifyQuiver V) r _ a.as
  have hb : Nonempty (@Quiver.Path (Quiver.Symmetrify V) _ r b.as) :=
    @Quiver.RootedConnected.nonempty_path (Quiver.Symmetrify V)
      (Quiver.symmetrifyQuiver V) r _ b.as
  rcases ha with ⟨pa⟩
  rcases hb with ⟨pb⟩
  exact Zigzag.of_inv_hom
    (Internal.freePathHom pa) (Internal.freePathHom pb)

theorem Internal.bassFreeGroupoid_end_subsingleton_at {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)]
    (x : Quiver.FreeGroupoid (BassSerreVertex G)) :
    Subsingleton (End x) := by
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (BassSerreVertex G) from
        BassSerreVertex.central Word.empty) :=
    bassSerre_rootedConnected G
  let : IsConnected (Quiver.FreeGroupoid (BassSerreVertex G)) :=
    Internal.freeGroupoid_isConnected_of_basedPaths
      (BassSerreVertex.central Word.empty)
  obtain ⟨p⟩ :=
    CategoryTheory.nonempty_hom_of_preconnected_groupoid
      ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
        (BassSerreVertex.central Word.empty)) x
  constructor
  intro f g
  have hroot : p ≫ f ≫ Groupoid.inv p =
      p ≫ g ≫ Groupoid.inv p := by
    exact @Subsingleton.elim _ (Internal.bassFreeGroupoid_end_subsingleton G) _ _
  have hcancel := congrArg
    (fun z => Groupoid.inv p ≫ z ≫ p) hroot
  unfold CategoryTheory.End at f g ⊢
  simpa [Category.assoc] using hcancel

theorem Internal.functor_map_injective_of_eq_id {C : Type u} [Category C]
    (F : C ⥤ C) (hF : F = CategoryTheory.Functor.id C) (x : C) :
    Function.Injective (fun f : End x => F.map f) := by
  intro f g h
  rw [hF] at h
  unfold CategoryTheory.End at f g ⊢
  simpa only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map] using h

theorem Internal.bass_factorCoset_append {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (w : RightFactorWord (G := G) i)
    (a : G i) (ha : a ≠ 1) :
    factorCosetMk G i (rightAppendCanonical i w a ha).prod =
      factorCosetMk G i w.1.prod := by
  unfold rightAppendCanonical
  rw [rightAppend_prod]
  exact factorCoset_mul_factor G i w.1.prod a

theorem Internal.rawCanonicalVertex_factorCosetMk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (i : ι) (g : FreeProduct G) :
    Internal.rawCanonicalVertex G
        (RawBassSerreVertex.factor i (factorCosetMk G i g)) =
      BassSerreVertex.factor i (rightTailCanonical i (Word.equiv g)) := by
  let c : FactorCoset G i := factorCosetMk G i g
  have hc : factorCosetMk G i (Quotient.out c) = factorCosetMk G i g := by
    simp [c, factorCosetMk, rightCosetMk]
  have ht := Internal.rightTailCanonical_factorCoset_eq G i (Quotient.out c) g hc
  change BassSerreVertex.factor i
      (rightTailCanonical i (Word.equiv (Quotient.out c))) = _
  exact congrArg (BassSerreVertex.factor i) ht

/-- Evaluate word-model edges as morphisms in the raw model's free groupoid. -/
noncomputable def Internal.bassToRawPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    BassSerreVertex G ⥤q Quiver.FreeGroupoid (RawBassSerreVertex G) where
  obj x := (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
    (Internal.bassToRawVertex G x)
  map := by
    intro a b e
    cases e using BassSerreEdge.casesOn with
    | centralFactor w i hw =>
        exact (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
          (RawBassSerreEdge.centralFactor w.prod i)
    | factorCentral i w a ha =>
        let q : Word G := rightAppendCanonical i w a ha
        have hc : factorCosetMk G i q.prod = factorCosetMk G i w.1.prod := by
          exact Internal.bass_factorCoset_append G i w a ha
        have hv : RawBassSerreVertex.factor i (factorCosetMk G i q.prod) =
            Internal.bassToRawVertex G (BassSerreVertex.factor i w) := by
          change RawBassSerreVertex.factor i (factorCosetMk G i q.prod) =
            RawBassSerreVertex.factor i (factorCosetMk G i w.1.prod)
          exact congrArg (RawBassSerreVertex.factor i) hc
        have hv' := congrArg
          (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj hv
        exact Groupoid.inv (Quiver.homOfEq
          ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
            (RawBassSerreEdge.centralFactor q.prod i)) rfl hv')

/-- Express group-and-coset edges as paths in the word model's free groupoid. -/
noncomputable def Internal.rawToBassPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    RawBassSerreVertex G ⥤q Quiver.FreeGroupoid (BassSerreVertex G) where
  obj x := (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
    (Internal.rawCanonicalVertex G x)
  map := by
    intro a b e
    cases e using RawBassSerreEdge.casesOn with
    | centralFactor g i =>
        let w : Word G := Word.equiv g
        by_cases hlast : wordLastIdx w = some i
        · let wt : RightFactorWord (G := G) i := rightTailCanonical i w
          let aa : G i := rightHead i w
          have haa : aa ≠ 1 := by
            exact rightHead_ne_one_of_lastIdx_eq i w hlast
          have happend : rightAppendCanonical i wt aa haa = w := by
            exact rightAppendCanonical_of_lastIdx_eq i w hlast
          have hs : BassSerreVertex.central
              (rightAppendCanonical i wt aa haa) =
              Internal.rawCanonicalVertex G (RawBassSerreVertex.central g) := by
            change BassSerreVertex.central
                (rightAppendCanonical i wt aa haa) =
              BassSerreVertex.central (Word.equiv g)
            rw [happend]
          have ht : BassSerreVertex.factor i wt =
              Internal.rawCanonicalVertex G
                (RawBassSerreVertex.factor i (factorCosetMk G i g)) := by
            exact (Internal.rawCanonicalVertex_factorCosetMk G i g).symm
          have hs' := congrArg
            (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj hs
          have ht' := congrArg
            (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj ht
          exact Quiver.homOfEq
            (Groupoid.inv
              ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
                (BassSerreEdge.factorCentral i wt aa haa))) hs' ht'
        · have htail : rightTailCanonical i w =
              ⟨w, hlast⟩ := by
            apply Subtype.ext
            exact rightTail_of_lastIdx_ne i w hlast
          have ht : BassSerreVertex.factor i ⟨w, hlast⟩ =
              Internal.rawCanonicalVertex G
                (RawBassSerreVertex.factor i (factorCosetMk G i g)) := by
            rw [Internal.rawCanonicalVertex_factorCosetMk G i g]
            change BassSerreVertex.factor i ⟨w, hlast⟩ =
              BassSerreVertex.factor i (rightTailCanonical i w)
            exact congrArg (BassSerreVertex.factor i) htail.symm
          have ht' := congrArg
            (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj ht
          exact Quiver.homOfEq
            ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
              (BassSerreEdge.centralFactor w i hlast)) rfl ht'

/-- Extend word evaluation to a functor between the two free groupoids. -/
noncomputable def Internal.bassToRawFunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Quiver.FreeGroupoid (BassSerreVertex G) ⥤
      Quiver.FreeGroupoid (RawBassSerreVertex G) :=
  Quiver.FreeGroupoid.lift (Internal.bassToRawPrefunctor G)

/-- Extend canonical word representatives to a functor between the two free groupoids. -/
noncomputable def Internal.rawToBassFunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Quiver.FreeGroupoid (RawBassSerreVertex G) ⥤
      Quiver.FreeGroupoid (BassSerreVertex G) :=
  Quiver.FreeGroupoid.lift (Internal.rawToBassPrefunctor G)

theorem Internal.rawToBassFunctor_map_of {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) :
    Quiver.homOfEq
        ((Internal.rawToBassFunctor G).map
          ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map e))
        (Prefunctor.congr_obj
          (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G)) a)
        (Prefunctor.congr_obj
          (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G)) b) =
      (Internal.rawToBassPrefunctor G).map e := by
  change Quiver.homOfEq
      ((Quiver.FreeGroupoid.lift (Internal.rawToBassPrefunctor G)).map
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map e))
      _ _ = (Internal.rawToBassPrefunctor G).map e
  exact Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G)) e

theorem Internal.bassToRawFunctor_map_of {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] {a b : BassSerreVertex G}
    (e : @Quiver.Hom (BassSerreVertex G) (bassSerreQuiver G) a b) :
    Quiver.homOfEq
        ((Internal.bassToRawFunctor G).map
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map e))
        (Prefunctor.congr_obj
          (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G)) a)
        (Prefunctor.congr_obj
          (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G)) b) =
      (Internal.bassToRawPrefunctor G).map e := by
  change Quiver.homOfEq
      ((Quiver.FreeGroupoid.lift (Internal.bassToRawPrefunctor G)).map
        ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map e))
      _ _ = (Internal.bassToRawPrefunctor G).map e
  exact Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G)) e

theorem Internal.bassToRawPrefunctor_map_centralFactor {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (g : FreeProduct G) (i : ι)
    (hw : wordLastIdx (Word.equiv g) ≠ some i) :
    (Internal.bassToRawPrefunctor G).map
        (BassSerreEdge.centralFactor (Word.equiv g) i hw) =
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
        (RawBassSerreEdge.centralFactor (Word.equiv g).prod i) := by
  rfl

theorem Internal.bassToRawPrefunctor_map_factorCentral {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (i : ι)
    (w : RightFactorWord (G := G) i) (a : G i) (ha : a ≠ 1)
    (hv : RawBassSerreVertex.factor i
        (factorCosetMk G i (rightAppendCanonical i w a ha).prod) =
      Internal.bassToRawVertex G (BassSerreVertex.factor i w)) :
    (Internal.bassToRawPrefunctor G).map
        (BassSerreEdge.factorCentral i w a ha) =
      Groupoid.inv (Quiver.homOfEq
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
          (RawBassSerreEdge.centralFactor
            (rightAppendCanonical i w a ha).prod i)) rfl
        (congrArg (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj hv)) := by
  rfl

theorem Internal.functor_map_homOfEq {C D : Type*} [Category C] [Category D]
    {X Y X' Y' : C} (F : C ⥤ D) (f : X ⟶ Y)
    (hX : X = X') (hY : Y = Y') :
    F.map (Quiver.homOfEq f hX hY) =
      Quiver.homOfEq (F.map f) (congrArg F.obj hX) (congrArg F.obj hY) := by
  subst hX hY
  rfl

theorem Internal.groupoid_inv_homOfEq {C : Type*} [Groupoid C]
    {X Y X' Y' : C} (f : X ⟶ Y)
    (hX : X = X') (hY : Y = Y') :
    Groupoid.inv (Quiver.homOfEq f hX hY) =
      Quiver.homOfEq (Groupoid.inv f) hY hX := by
  subst hX hY
  rfl

theorem Internal.groupoid_inv_inv {C : Type*} [Groupoid C]
    {X Y : C} (f : X ⟶ Y) :
    Groupoid.inv (Groupoid.inv f) = f := by
  rw [Groupoid.inv_eq_inv, Groupoid.inv_eq_inv]
  simp

theorem Internal.groupoid_inv_inv_homOfEq {C : Type*} [Groupoid C]
    {X Y X' Y' : C} (f : X ⟶ Y)
    (hX : X = X') (hY : Y = Y') :
    Groupoid.inv (Groupoid.inv (Quiver.homOfEq f hX hY)) =
      Quiver.homOfEq f hX hY := by
  exact Internal.groupoid_inv_inv _

theorem Internal.homOfEq_transport {C : Type*} [Quiver C]
    {X Y X' Y' X'' Y'' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') (kX : X' = X'') (kY : Y' = Y'')
    (h : Quiver.homOfEq f hX hY = g) :
    Quiver.homOfEq f (hX.trans kX) (hY.trans kY) =
      Quiver.homOfEq g kX kY := by
  subst hX hY kX kY
  exact h

theorem Internal.homOfEq_transport' {C : Type*} [Quiver C]
    {X Y X' Y' X'' Y'' : C} (f : X ⟶ Y) (g : X' ⟶ Y')
    (hX : X = X') (hY : Y = Y') (kX : X' = X'') (kY : Y' = Y'')
    (lX : X = X'') (lY : Y = Y'')
    (h : Quiver.homOfEq f hX hY = g) :
    Quiver.homOfEq f lX lY = Quiver.homOfEq g kX kY := by
  have ht := Internal.homOfEq_transport f g hX hY kX kY h
  convert ht using 1

theorem Internal.homOfEq_eq_of_heq {C : Type*} [Quiver C]
    {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hX : X = X') (hY : Y = Y') (hfg : HEq f g) :
    Quiver.homOfEq f hX hY = g := by
  subst hX hY
  exact eq_of_heq hfg

/-- All edges of the group-and-coset model, bundled with their endpoints. -/
abbrev Internal.rawEdgeSigma {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :=
  Σ a b : RawBassSerreVertex G, RawBassSerreEdge G a b

theorem Internal.rawEdge_heq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g h : FreeProduct G) (i : ι) (gh : g = h) :
    HEq (RawBassSerreEdge.centralFactor g i)
      (RawBassSerreEdge.centralFactor h i) := by
  cases gh
  rfl

theorem Internal.rawEdgeMap_heq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (g h : FreeProduct G) (i : ι) (gh : g = h) :
    HEq
      ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
        (RawBassSerreEdge.centralFactor g i))
      ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
        (RawBassSerreEdge.centralFactor h i)) := by
  cases gh
  rfl

theorem Internal.rawBassRaw_obj {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (x : RawBassSerreVertex G) :
    (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G).obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x) =
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x := by
  have hR := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G)) x
  have hC := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G))
    (Internal.rawCanonicalVertex G x)
  calc
    (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G).obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x) =
        (Internal.bassToRawFunctor G).obj
          ((Internal.rawToBassFunctor G).obj
            ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x)) := rfl
    _ = (Internal.bassToRawFunctor G).obj
          ((Internal.rawToBassPrefunctor G).obj x) := congrArg _ hR
    _ = (Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (Internal.rawCanonicalVertex G x)) := rfl
    _ = (Internal.bassToRawPrefunctor G).obj
          (Internal.rawCanonicalVertex G x) := hC
    _ = (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (Internal.bassToRawVertex G (Internal.rawCanonicalVertex G x)) := rfl
    _ = (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x := by
      rw [Internal.bassToRawVertex_rawCanonicalVertex]

/-- The composite converting raw edges to word-model paths and evaluating them back. -/
noncomputable def Internal.rawBassRawPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    RawBassSerreVertex G ⥤q Quiver.FreeGroupoid (RawBassSerreVertex G) :=
  Internal.rawToBassPrefunctor G ⋙q (Internal.bassToRawFunctor G).toPrefunctor

/-- The round trip on an edge ending in its factor uses the reversed canonical edge. -/
private theorem rawBassRaw_map_last_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)]
    (hobj : ∀ x : RawBassSerreVertex G,
      (Internal.rawBassRawPrefunctor G).obj x =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x)
    (g : FreeProduct G) (i : ι)
    (hlast : wordLastIdx (Word.equiv g) = some i) :
    (Internal.rawBassRawPrefunctor G).map (RawBassSerreEdge.centralFactor g i) =
      Quiver.homOfEq ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
        (RawBassSerreEdge.centralFactor g i))
        (hobj (RawBassSerreVertex.central g)).symm
        (hobj (RawBassSerreVertex.factor i (factorCosetMk G i g))).symm := by
  dsimp only [Internal.rawBassRawPrefunctor, Prefunctor.comp, Internal.rawToBassPrefunctor]
  simp only [dite_eq_left hlast]
  let w : Word G := Word.equiv g
  let wt : RightFactorWord (G := G) i := rightTailCanonical i w
  let aa : G i := rightHead i w
  have haa : aa ≠ 1 := rightHead_ne_one_of_lastIdx_eq i w hlast
  have happend : rightAppendCanonical i wt aa haa = w :=
    rightAppendCanonical_of_lastIdx_eq i w hlast
  have hs : BassSerreVertex.central
        (rightAppendCanonical i wt aa haa) =
        Internal.rawCanonicalVertex G (RawBassSerreVertex.central g) := by
    change BassSerreVertex.central
        (rightAppendCanonical i wt aa haa) =
      BassSerreVertex.central (Word.equiv g)
    rw [happend]
  have ht : BassSerreVertex.factor i wt =
        Internal.rawCanonicalVertex G
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) := by
    exact (Internal.rawCanonicalVertex_factorCosetMk G i g).symm
  have hs' := congrArg
    (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj hs
  have ht' := congrArg
    (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj ht
  dsimp only [Functor.toPrefunctor]
  erw [Internal.functor_map_homOfEq (Internal.bassToRawFunctor G)]
  let A :
      (Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.central
              (rightAppendCanonical i wt aa haa))) =
        (Internal.rawBassRawPrefunctor G).obj
          (RawBassSerreVertex.central g) :=
    congrArg (Internal.bassToRawFunctor G).obj hs'
  let B :
      (Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.factor i wt)) =
        (Internal.rawBassRawPrefunctor G).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) :=
    congrArg (Internal.bassToRawFunctor G).obj ht'
  have hmapInv := (Internal.bassToRawFunctor G).map_inv
    ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
      (BassSerreEdge.factorCentral i wt aa haa))
  have hmapInv' :
      (Internal.bassToRawFunctor G).map
          (Groupoid.inv
            ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
              (BassSerreEdge.factorCentral i wt aa haa))) =
        Groupoid.inv
          ((Internal.bassToRawFunctor G).map
            ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
              (BassSerreEdge.factorCentral i wt aa haa))) := by
    simpa only [Groupoid.inv_eq_inv] using hmapInv
  have hmapInvCast :
      Quiver.homOfEq
          ((Internal.bassToRawFunctor G).map
            (Groupoid.inv
              ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
                (BassSerreEdge.factorCentral i wt aa haa)))) A B =
        Quiver.homOfEq
          (Groupoid.inv
            ((Internal.bassToRawFunctor G).map
              ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
                (BassSerreEdge.factorCentral i wt aa haa)))) A B := by
    exact congrArg
      (fun z => Quiver.homOfEq z A B) hmapInv'
  have hC := Internal.bassToRawFunctor_map_of G
    (BassSerreEdge.factorCentral i wt aa haa)
  have hv : RawBassSerreVertex.factor i
        (factorCosetMk G i (rightAppendCanonical i wt aa haa).prod) =
        Internal.bassToRawVertex G (BassSerreVertex.factor i wt) := by
    change RawBassSerreVertex.factor i
          (factorCosetMk G i (rightAppendCanonical i wt aa haa).prod) =
        RawBassSerreVertex.factor i (factorCosetMk G i wt.1.prod)
    exact congrArg (RawBassSerreVertex.factor i)
      (Internal.bass_factorCoset_append G i wt aa haa)
  have hQ := Internal.bassToRawPrefunctor_map_factorCentral G i wt aa haa hv
  rw [hQ] at hC
  let hsC := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G))
    (BassSerreVertex.factor i wt)
  let htC := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G))
    (BassSerreVertex.central
      (rightAppendCanonical i wt aa haa))
  let kx := htC.symm.trans A
  let ky := hsC.symm.trans B
  let hv' := congrArg
    (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj hv
  let fraw := Quiver.homOfEq
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor
        (rightAppendCanonical i wt aa haa).prod i)) rfl hv'
  have hCinv' :
      Quiver.homOfEq
          (Groupoid.inv
            ((Internal.bassToRawFunctor G).map
              ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
                (BassSerreEdge.factorCentral i wt aa haa))))
        htC hsC = fraw := by
    apply Eq.trans (Internal.groupoid_inv_homOfEq _ _ _).symm
    apply Eq.trans _ (Internal.groupoid_inv_inv fraw)
    apply congrArg Groupoid.inv
    rw [hC]
  have htransport := Internal.homOfEq_transport'
    (Groupoid.inv
      ((Internal.bassToRawFunctor G).map
        ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
          (BassSerreEdge.factorCentral i wt aa haa))))
    fraw htC hsC kx ky A B hCinv'
  have hg : (Word.equiv g).prod = g :=
    (Word.equiv).symm_apply_apply g
  have hqprod :
      (rightAppendCanonical i wt aa haa).prod = g := by
    calc
      (rightAppendCanonical i wt aa haa).prod =
          (Word.equiv g).prod := congrArg Word.prod happend
      _ = g := hg
  have rX :
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central g) =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central
            (rightAppendCanonical i wt aa haa).prod) := by
    rw [hqprod]
  have rY0 :
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i
            (factorCosetMk G i
              (rightAppendCanonical i wt aa haa).prod)) := by
    rw [hqprod]
  have rY :
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) =
        (Internal.bassToRawPrefunctor G).obj
          (BassSerreVertex.factor i wt) :=
    rY0.trans hv'
  have hraw0 := Internal.homOfEq_eq_of_heq rX rY0
    (Internal.rawEdgeMap_heq G g
      (rightAppendCanonical i wt aa haa).prod i hqprod.symm)
  have hraw := Internal.homOfEq_transport'
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor g i))
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor
        (rightAppendCanonical i wt aa haa).prod i))
    rX rY0 rfl hv' rX rY hraw0
  have hfinal := Internal.homOfEq_transport'
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor g i))
    fraw rX rY kx ky
    (hobj (RawBassSerreVertex.central g)).symm
    (hobj (RawBassSerreVertex.factor i (factorCosetMk G i g))).symm
    hraw
  exact hmapInvCast.trans (htransport.trans hfinal.symm)

/-- For every other final factor, the round trip uses the forward canonical edge. -/
private theorem rawBassRaw_map_last_ne {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)]
    (hobj : ∀ x : RawBassSerreVertex G,
      (Internal.rawBassRawPrefunctor G).obj x =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x)
    (g : FreeProduct G) (i : ι)
    (hlast : wordLastIdx (Word.equiv g) ≠ some i) :
    (Internal.rawBassRawPrefunctor G).map (RawBassSerreEdge.centralFactor g i) =
      Quiver.homOfEq ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
        (RawBassSerreEdge.centralFactor g i))
        (hobj (RawBassSerreVertex.central g)).symm
        (hobj (RawBassSerreVertex.factor i (factorCosetMk G i g))).symm := by
  dsimp only [Internal.rawBassRawPrefunctor, Prefunctor.comp, Internal.rawToBassPrefunctor]
  simp only [dite_eq_right hlast]
  let w : Word G := Word.equiv g
  have ht : BassSerreVertex.factor i ⟨w, hlast⟩ =
        Internal.rawCanonicalVertex G
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) := by
    rw [Internal.rawCanonicalVertex_factorCosetMk G i g]
    change BassSerreVertex.factor i ⟨w, hlast⟩ =
      BassSerreVertex.factor i (rightTailCanonical i w)
    apply congrArg (BassSerreVertex.factor i)
    apply Subtype.ext
    exact (rightTail_of_lastIdx_ne i w hlast).symm
  have ht' := congrArg
    (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj ht
  dsimp only [Functor.toPrefunctor]
  erw [Internal.functor_map_homOfEq (Internal.bassToRawFunctor G)]
  have hC := Internal.bassToRawFunctor_map_of G
    (BassSerreEdge.centralFactor w i hlast)
  have hQ := Internal.bassToRawPrefunctor_map_centralFactor G g i hlast
  rw [hQ] at hC
  let A :
      (Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.central w)) =
        (Internal.rawBassRawPrefunctor G).obj
          (RawBassSerreVertex.central g) :=
    congrArg (Internal.bassToRawFunctor G).obj
      (rfl :
        (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.central w) =
          (Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.central w))
  let B :
      (Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (BassSerreVertex G)).obj
            (BassSerreVertex.factor i ⟨w, hlast⟩)) =
        (Internal.rawBassRawPrefunctor G).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) :=
    congrArg (Internal.bassToRawFunctor G).obj ht'
  let hsC := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G))
    (BassSerreVertex.central w)
  let htC := Prefunctor.congr_obj
    (Quiver.FreeGroupoid.lift_spec (Internal.bassToRawPrefunctor G))
    (BassSerreVertex.factor i ⟨w, hlast⟩)
  let kx := hsC.symm.trans A
  let ky := htC.symm.trans B
  have htransport := Internal.homOfEq_transport'
    ((Internal.bassToRawFunctor G).map
      ((Quiver.FreeGroupoid.of (BassSerreVertex G)).map
        (BassSerreEdge.centralFactor w i hlast)))
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor (Word.equiv g).prod i))
    hsC htC kx ky A B hC
  have hg : (Word.equiv g).prod = g :=
    (Word.equiv).symm_apply_apply g
  have rX :
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central g) =
        (Internal.bassToRawPrefunctor G).obj
          (BassSerreVertex.central w) := by
    change (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central g) =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central (Word.equiv g).prod)
    rw [hg]
  have rY :
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) =
        (Internal.bassToRawPrefunctor G).obj
          (BassSerreVertex.factor i ⟨w, hlast⟩) := by
    change (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i (factorCosetMk G i g)) =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.factor i
            (factorCosetMk G i (Word.equiv g).prod))
    rw [hg]
  have hraw :
      Quiver.homOfEq
          ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
            (RawBassSerreEdge.centralFactor g i)) rX rY =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
          (RawBassSerreEdge.centralFactor (Word.equiv g).prod i) := by
    exact Internal.homOfEq_eq_of_heq rX rY
      (Internal.rawEdgeMap_heq G g (Word.equiv g).prod i hg.symm)
  have hfinal := Internal.homOfEq_transport'
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor g i))
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).map
      (RawBassSerreEdge.centralFactor (Word.equiv g).prod i))
    rX rY kx ky (hobj (RawBassSerreVertex.central g)).symm
    (hobj (RawBassSerreVertex.factor i (factorCosetMk G i g))).symm hraw
  exact hfinal.symm

theorem Internal.rawBassRawPrefunctor_eq_of {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Internal.rawBassRawPrefunctor G =
      Quiver.FreeGroupoid.of (RawBassSerreVertex G) := by
  let hobj : ∀ x : RawBassSerreVertex G,
      (Internal.rawBassRawPrefunctor G).obj x =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x := by
    intro x
    have hR := Prefunctor.congr_obj
      (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G)) x
    calc
      (Internal.rawBassRawPrefunctor G).obj x =
          (Internal.bassToRawFunctor G).obj
            ((Internal.rawToBassPrefunctor G).obj x) := rfl
      _ = (Internal.bassToRawFunctor G).obj
            ((Internal.rawToBassFunctor G).obj
              ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x)) :=
        congrArg (Internal.bassToRawFunctor G).obj hR.symm
      _ = (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G).obj
          ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x) := rfl
      _ = (Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj x :=
        Internal.rawBassRaw_obj G x
  apply Prefunctor.ext' hobj
  intro x y e
  cases e using RawBassSerreEdge.casesOn with
  | centralFactor g i =>
    by_cases hlast : wordLastIdx (Word.equiv g) = some i
    · exact rawBassRaw_map_last_eq G hobj g i hlast
    · exact rawBassRaw_map_last_ne G hobj g i hlast

theorem Internal.rawBassRawFunctor_eq_id {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G =
      CategoryTheory.Functor.id (Quiver.FreeGroupoid (RawBassSerreVertex G)) := by
  have hpre :
      Quiver.FreeGroupoid.of (RawBassSerreVertex G) ⋙q
          (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G).toPrefunctor =
        Quiver.FreeGroupoid.of (RawBassSerreVertex G) := by
    calc
      Quiver.FreeGroupoid.of (RawBassSerreVertex G) ⋙q
          (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G).toPrefunctor =
        (Quiver.FreeGroupoid.of (RawBassSerreVertex G) ⋙q
          (Internal.rawToBassFunctor G).toPrefunctor) ⋙q
            (Internal.bassToRawFunctor G).toPrefunctor := by
          exact (Prefunctor.comp_assoc
            (Quiver.FreeGroupoid.of (RawBassSerreVertex G))
            (Internal.rawToBassFunctor G).toPrefunctor
            (Internal.bassToRawFunctor G).toPrefunctor).symm
      _ = (Internal.rawToBassPrefunctor G) ⋙q
            (Internal.bassToRawFunctor G).toPrefunctor := by
          exact congrArg
            (fun P => P ⋙q (Internal.bassToRawFunctor G).toPrefunctor)
            (Quiver.FreeGroupoid.lift_spec (Internal.rawToBassPrefunctor G))
      _ = Internal.rawBassRawPrefunctor G := rfl
      _ = Quiver.FreeGroupoid.of (RawBassSerreVertex G) :=
        Internal.rawBassRawPrefunctor_eq_of G
  have hF := Quiver.FreeGroupoid.lift_unique
    (Quiver.FreeGroupoid.of (RawBassSerreVertex G))
    (Internal.rawToBassFunctor G ⋙ Internal.bassToRawFunctor G)
    hpre
  have hid :
      Quiver.FreeGroupoid.lift (Quiver.FreeGroupoid.of (RawBassSerreVertex G)) =
        CategoryTheory.Functor.id (Quiver.FreeGroupoid (RawBassSerreVertex G)) := by
    symm
    exact Quiver.FreeGroupoid.lift_unique
      (Quiver.FreeGroupoid.of (RawBassSerreVertex G))
      (CategoryTheory.Functor.id (Quiver.FreeGroupoid (RawBassSerreVertex G))) rfl
  exact hF.trans hid

theorem Internal.rawFreeGroupoid_end_subsingleton {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    Subsingleton (End ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
      (RawBassSerreVertex.central 1))) := by
  constructor
  intro f g
  let : Quiver.RootedConnected
      (show Quiver.Symmetrify (BassSerreVertex G) from
        BassSerreVertex.central Word.empty) :=
    bassSerre_rootedConnected G
  let : IsConnected (Quiver.FreeGroupoid (BassSerreVertex G)) :=
    Internal.freeGroupoid_isConnected_of_basedPaths
      (BassSerreVertex.central Word.empty)
  let R := Internal.rawToBassFunctor G
  let C := Internal.bassToRawFunctor G
  have hRC : R ⋙ C =
      CategoryTheory.Functor.id (Quiver.FreeGroupoid (RawBassSerreVertex G)) :=
    Internal.rawBassRawFunctor_eq_id G
  have hmap : R.map f = R.map g := by
    have : Subsingleton (R.obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central 1)) ⟶ R.obj
        ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central 1))) :=
      Internal.bassFreeGroupoid_end_subsingleton_at G
        (R.obj ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
          (RawBassSerreVertex.central 1)))
    exact Subsingleton.elim _ _
  have hmapC : (R ⋙ C).map f = (R ⋙ C).map g := by
    change C.map (R.map f) = C.map (R.map g)
    exact congrArg (fun z => C.map z) hmap
  exact (Internal.functor_map_injective_of_eq_id
    (R ⋙ C) hRC
    ((Quiver.FreeGroupoid.of (RawBassSerreVertex G)).obj
      (RawBassSerreVertex.central 1))) hmapC

/-- All quotient-graph edges bundled with their endpoints. -/
abbrev Internal.orbitAllEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  Σ a b : RawBassSerreOrbitVertex G H,
    @Quiver.Hom (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H) a b

/-- The union of the vertex stabilizers and the quotient-edge labels inside `H`. -/
def Internal.treeDataGeneratorSet {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) : Set H :=
  {h | ∃ a : RawBassSerreOrbitVertex G H, h ∈ treeVertexStabilizer G H a} ∪
    {h | ∃ e : Internal.orbitAllEdge G H, h = quotientEdgeLabel G H e.2.2}

/-- The subgroup generated by vertex stabilizers and quotient-edge labels. -/
def Internal.treeDataGenerated {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) : Subgroup H :=
  Subgroup.closure (Internal.treeDataGeneratorSet G H)

/-- The raw model's chosen spanning tree on the ambient vertex type. -/
@[reducible] def Internal.rawSpanningTreeQuiver {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] : Quiver (RawBassSerreVertex G) :=
  { Hom := fun a b =>
      { e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreVertex G))
          (@Quiver.symmetrifyQuiver (RawBassSerreVertex G)
            (rawBassSerreQuiver G)) a b //
        e ∈ rawBassSerreTree G a b } }

instance Internal.rawSpanningTreeQuiverArborescence {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] :
    @Quiver.Arborescence (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G) := by
  change Quiver.Arborescence (rawBassSerreTree G)
  exact rawBassSerreTreeArborescence G

theorem Internal.treeDataGenerated_mem_vertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) (x : treeVertexStabilizer G H a) :
    (x : H) ∈ Internal.treeDataGenerated G H := by
  apply Subgroup.subset_closure
  exact Or.inl ⟨a, x.property⟩

theorem Internal.treeDataGenerated_mem_edge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : Internal.orbitAllEdge G H) :
    quotientEdgeLabel G H e.2.2 ∈ Internal.treeDataGenerated G H := by
  apply Subgroup.subset_closure
  exact Or.inr ⟨e, rfl⟩

theorem Internal.rawEdgeMap_dataOf {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) :
    rawBassSerreOrbitEdgeMk G H (rawBassSerreEdgeDataOf G e) =
      (rawBassSerreOrbitEdgeMap G H e).1 := by
  cases e using RawBassSerreEdge.casesOn
  rfl

/-- Choose a group element sending one point to another in the same orbit. -/
noncomputable def Internal.actionOrbitAlign {A X : Type w} [Group A]
    [MulAction A X] {x y : X}
    (h : actionOrbitMk A X x = actionOrbitMk A X y) : A :=
  Classical.choose ((actionOrbitMk_eq_iff A X x y).1 h)

theorem Internal.actionOrbitAlign_spec {A X : Type w} [Group A]
    [MulAction A X] {x y : X}
    (h : actionOrbitMk A X x = actionOrbitMk A X y) :
    Internal.actionOrbitAlign h • x = y :=
  Classical.choose_spec ((actionOrbitMk_eq_iff A X x y).1 h)

theorem Internal.rawEdgeData_rep_orbit_eq {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) :
    actionOrbitMk H (rawBassSerreEdgeData G)
        (quotientEdgeRawData G H (rawBassSerreOrbitEdgeMap G H e)) =
      actionOrbitMk H (rawBassSerreEdgeData G) (rawBassSerreEdgeDataOf G e) := by
  change rawBassSerreOrbitEdgeMk G H
      (quotientEdgeRawData G H (rawBassSerreOrbitEdgeMap G H e)) =
    rawBassSerreOrbitEdgeMk G H (rawBassSerreEdgeDataOf G e)
  rw [quotientEdgeRawData_mk G H (rawBassSerreOrbitEdgeMap G H e)]
  exact (Internal.rawEdgeMap_dataOf G H e).symm

/-- Align a raw edge with the chosen representative of its quotient edge. -/
noncomputable def Internal.rawEdgeOrbitAlign {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) : H :=
  Internal.actionOrbitAlign
    (Internal.rawEdgeData_rep_orbit_eq G H e)

theorem Internal.rawEdgeOrbitAlign_spec {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b) :
    (Internal.rawEdgeOrbitAlign G H e) •
        quotientEdgeRawData G H (rawBassSerreOrbitEdgeMap G H e) =
      rawBassSerreEdgeDataOf G e :=
  Internal.actionOrbitAlign_spec (Internal.rawEdgeData_rep_orbit_eq G H e)

theorem Internal.rawTreeRepresentative_root {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    rawTreeRepresentative G H (rawBassSerreOrbitRoot G H) =
      RawBassSerreVertex.central 1 := by
  have hroot := rawBassSerreOrbitTree_root_eq G H
  cases hroot
  unfold rawTreeRepresentative
  have hp : (rawTreeUniquePath G H (rawBassSerreOrbitRoot G H)).default =
      Quiver.Path.nil := ((rawTreeUniquePath G H _).uniq _).symm
  rw [hp]
  rfl

theorem Internal.conjugate_mem_stabilizer {A X : Type w} [Group A]
    [MulAction A X] (x : X) (s k : A) (hk : k • x = x) :
    s * k * s⁻¹ ∈ MulAction.stabilizer A (s • x) := by
  change (s * k * s⁻¹) • (s • x) = s • x
  rw [smul_smul]
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rw [← smul_smul, hk]

theorem Internal.stabilizer_conjugate_eq {A : Type w} [Group A]
    (s k u r : A) :
    u * (s * k * s⁻¹) * s = r ↔
      k = (u * s)⁻¹ * r := by
  constructor
  · intro h
    have h' := congrArg (fun t => (u * s)⁻¹ * t) h
    simpa [mul_assoc] using h'
  · intro h
    subst k
    simp [mul_assoc]

theorem Internal.positive_step {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) a) = a) :
    ∃ v : treeVertexStabilizer G H
        (actionOrbitMk H (RawBassSerreVertex G) a),
      Internal.rawEdgeOrbitAlign G H e =
          u * v * quotientEdgeCoherentSourceAlign G H
            (rawBassSerreOrbitEdgeMap G H e) ∧
        b = (u * v * (quotientEdgeLabel G H
          (rawBassSerreOrbitEdgeMap G H e))⁻¹).1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) b) := by
  let q := rawBassSerreOrbitEdgeMap G H e
  let d := quotientEdgeRawData G H q
  let r := Internal.rawEdgeOrbitAlign G H e
  let s := quotientEdgeCoherentSourceAlign G H q
  let l := quotientEdgeLabel G H q
  have hr : r • d = rawBassSerreEdgeDataOf G e :=
    Internal.rawEdgeOrbitAlign_spec G H e
  have hsrc : r.1 • rawBassSerreEdgeDataSource G d = a := by
    calc
      r.1 • rawBassSerreEdgeDataSource G d =
          rawBassSerreEdgeDataSource G (r • d) := by
            symm
            exact rawBassSerreEdgeData_source_action G r.1 d
      _ = rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G e) :=
        congrArg (rawBassSerreEdgeDataSource G) hr
      _ = a := rawBassSerreEdgeDataOf_source G e
  have htarget : r.1 • rawBassSerreEdgeDataTarget G d = b := by
    calc
      r.1 • rawBassSerreEdgeDataTarget G d =
          rawBassSerreEdgeDataTarget G (r • d) := by
            symm
            exact rawBassSerreEdgeData_target_action G r.1 d
      _ = rawBassSerreEdgeDataTarget G (rawBassSerreEdgeDataOf G e) :=
        congrArg (rawBassSerreEdgeDataTarget G) hr
      _ = b := rawBassSerreEdgeDataOf_target G e
  have hs : s.1 • rawBassSerreEdgeDataSource G d =
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) a) := by
    exact quotientEdgeCoherentSourceAlign_spec G H q
  have hsl : l.1 • (s.1 • rawBassSerreEdgeDataTarget G d) =
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) b) := by
    exact quotientEdgeLabel_transport_coherent G H q
  let k : H := (u * s)⁻¹ * r
  have hks : k.1 • rawBassSerreEdgeDataSource G d =
      rawBassSerreEdgeDataSource G d := by
    calc
      k.1 • rawBassSerreEdgeDataSource G d =
          (u * s)⁻¹.1 • (r.1 • rawBassSerreEdgeDataSource G d) := by
            apply (smul_smul ((u * s)⁻¹ : H) r
              (rawBassSerreEdgeDataSource G d)).symm
      _ = (u * s)⁻¹.1 • a := by rw [hsrc]
      _ = (u * s)⁻¹.1 • (u.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) a)) := by
        rw [hu]
      _ = rawBassSerreEdgeDataSource G d := by
        rw [← hs]
        rw [smul_smul]
        simp
  let vH : H :=
    ⟨s.1 * k.1 * s.1⁻¹,
      H.mul_mem (H.mul_mem s.property k.property) (H.inv_mem s.property)⟩
  let v : treeVertexStabilizer G H
      (actionOrbitMk H (RawBassSerreVertex G) a) :=
    ⟨vH, by
      change vH.1 • rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) a) = _
      rw [← hs]
      exact Internal.conjugate_mem_stabilizer
        (rawBassSerreEdgeDataSource G d) s.1 k.1 hks⟩
  have hcoef : r = u * v * s := by
    apply Subtype.ext
    calc
      r.1 = u.1 * (s.1 * k.1 * s.1⁻¹) * s.1 := by
        exact (Internal.stabilizer_conjugate_eq s.1 k.1 u.1 r.1).2 rfl |>.symm
      _ = (u * v * s).1 := by
        simp [v, vH, mul_assoc]
  refine ⟨v, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Subtype.val hcoef
  · calc
      b = r.1 • rawBassSerreEdgeDataTarget G d := htarget.symm
      _ = (u * v * s).1 • rawBassSerreEdgeDataTarget G d := by
        rw [← hcoef]
      _ = (u * v).1 • (s.1 • rawBassSerreEdgeDataTarget G d) := by
        simp only [Subgroup.coe_mul]
        rw [smul_smul]
      _ = (u * v).1 • (l.1⁻¹ •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) b)) := by
        congr 1
        apply smul_left_cancel l.1
        rw [hsl]
        simp [smul_smul]
      _ = (u * v * l⁻¹).1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) b) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [smul_smul]

theorem Internal.negative_step {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) b) = b) :
    ∃ v : treeVertexStabilizer G H
        (actionOrbitMk H (RawBassSerreVertex G) b),
      Internal.rawEdgeOrbitAlign G H e =
          u * v * ((quotientEdgeLabel G H
            (rawBassSerreOrbitEdgeMap G H e)) *
            quotientEdgeCoherentSourceAlign G H
              (rawBassSerreOrbitEdgeMap G H e)) ∧
        a = (u * v * quotientEdgeLabel G H
          (rawBassSerreOrbitEdgeMap G H e)).1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) a) := by
  let q := rawBassSerreOrbitEdgeMap G H e
  let d := quotientEdgeRawData G H q
  let r := Internal.rawEdgeOrbitAlign G H e
  let s := quotientEdgeCoherentSourceAlign G H q
  let l := quotientEdgeLabel G H q
  let t := l * s
  have hr : r • d = rawBassSerreEdgeDataOf G e :=
    Internal.rawEdgeOrbitAlign_spec G H e
  have hsource : r.1 • rawBassSerreEdgeDataSource G d = a := by
    calc
      r.1 • rawBassSerreEdgeDataSource G d =
          rawBassSerreEdgeDataSource G (r • d) := by
            symm
            exact rawBassSerreEdgeData_source_action G r.1 d
      _ = rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G e) :=
        congrArg (rawBassSerreEdgeDataSource G) hr
      _ = a := rawBassSerreEdgeDataOf_source G e
  have htarget : r.1 • rawBassSerreEdgeDataTarget G d = b := by
    calc
      r.1 • rawBassSerreEdgeDataTarget G d =
          rawBassSerreEdgeDataTarget G (r • d) := by
            symm
            exact rawBassSerreEdgeData_target_action G r.1 d
      _ = rawBassSerreEdgeDataTarget G (rawBassSerreEdgeDataOf G e) :=
        congrArg (rawBassSerreEdgeDataTarget G) hr
      _ = b := rawBassSerreEdgeDataOf_target G e
  have hsd : s.1 • rawBassSerreEdgeDataTarget G d =
      l.1⁻¹ • rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) b) := by
    apply smul_left_cancel l.1
    rw [quotientEdgeLabel_transport_coherent G H q]
    simp [smul_smul]
  have htd : t.1 • rawBassSerreEdgeDataTarget G d =
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) b) := by
    change (l * s).1 • rawBassSerreEdgeDataTarget G d = _
    calc
      (l * s).1 • rawBassSerreEdgeDataTarget G d =
          l.1 • (s.1 • rawBassSerreEdgeDataTarget G d) :=
        (smul_smul l s (rawBassSerreEdgeDataTarget G d)).symm
      _ = rawTreeRepresentative G H
          (actionOrbitMk H (RawBassSerreVertex G) b) :=
        quotientEdgeLabel_transport_coherent G H q
  have hst : s.1 • rawBassSerreEdgeDataSource G d =
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) a) := by
    exact quotientEdgeCoherentSourceAlign_spec G H q
  let k : H := (u * t)⁻¹ * r
  have hks : k.1 • rawBassSerreEdgeDataTarget G d =
      rawBassSerreEdgeDataTarget G d := by
    calc
      k.1 • rawBassSerreEdgeDataTarget G d =
          (u * t)⁻¹.1 • (r.1 • rawBassSerreEdgeDataTarget G d) := by
            apply (smul_smul ((u * t)⁻¹ : H) r
              (rawBassSerreEdgeDataTarget G d)).symm
      _ = (u * t)⁻¹.1 • b := by rw [htarget]
      _ = (u * t)⁻¹.1 • (u.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) b)) := by
        rw [hu]
      _ = rawBassSerreEdgeDataTarget G d := by
        rw [← htd]
        rw [smul_smul]
        simp
  let vH : H :=
    ⟨t.1 * k.1 * t.1⁻¹,
      H.mul_mem (H.mul_mem t.property k.property) (H.inv_mem t.property)⟩
  let v : treeVertexStabilizer G H
      (actionOrbitMk H (RawBassSerreVertex G) b) :=
    ⟨vH, by
      change vH.1 • rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) b) = _
      rw [← htd]
      exact Internal.conjugate_mem_stabilizer
        (rawBassSerreEdgeDataTarget G d) t.1 k.1 hks⟩
  have hcoef : r = u * v * t := by
    apply Subtype.ext
    calc
      r.1 = u.1 * (t.1 * k.1 * t.1⁻¹) * t.1 := by
        exact (Internal.stabilizer_conjugate_eq t.1 k.1 u.1 r.1).2 rfl |>.symm
      _ = (u * v * t).1 := by
        simp [v, vH, mul_assoc]
  refine ⟨v, ?_, ?_⟩
  · apply Subtype.ext
    exact congrArg Subtype.val hcoef
  · calc
      a = r.1 • rawBassSerreEdgeDataSource G d := hsource.symm
      _ = (u * v * t).1 • rawBassSerreEdgeDataSource G d := by
        rw [← hcoef]
      _ = (u * v).1 • (t.1 • rawBassSerreEdgeDataSource G d) := by
        calc
          (u * v * t).1 • rawBassSerreEdgeDataSource G d =
              ((u * v).1 * t.1) • rawBassSerreEdgeDataSource G d := by
            rw [Subgroup.coe_mul]
          _ = (u * v).1 • (t.1 • rawBassSerreEdgeDataSource G d) :=
            (smul_smul (u * v) t (rawBassSerreEdgeDataSource G d)).symm
      _ = (u * v).1 • (l.1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) a)) := by
        congr 1
        rw [show t.1 • rawBassSerreEdgeDataSource G d =
            l.1 • rawTreeRepresentative G H
              (actionOrbitMk H (RawBassSerreVertex G) a) by
          change (l * s).1 • rawBassSerreEdgeDataSource G d = _
          calc
            (l * s).1 • rawBassSerreEdgeDataSource G d =
                l.1 • (s.1 • rawBassSerreEdgeDataSource G d) :=
              (smul_smul l s (rawBassSerreEdgeDataSource G d)).symm
            _ = l.1 • rawTreeRepresentative G H
                (actionOrbitMk H (RawBassSerreVertex G) a) := by rw [hst]]
      _ = (u * v * l).1 •
          rawTreeRepresentative G H
            (actionOrbitMk H (RawBassSerreVertex G) a) := by
        simp only [Subgroup.coe_mul]
        rw [smul_smul]

/-- The stabilizer correction required when traversing a positive raw edge. -/
noncomputable def Internal.positiveStepVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) a) = a) :
    treeVertexStabilizer G H
      (actionOrbitMk H (RawBassSerreVertex G) a) :=
  Classical.choose (Internal.positive_step G H e u hu)

theorem Internal.positiveStepVertex_endpoint {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) a) = a) :
    b = (u * Internal.positiveStepVertex G H e u hu *
      (quotientEdgeLabel G H
        (rawBassSerreOrbitEdgeMap G H e))⁻¹).1 •
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) b) := by
  simpa [Internal.positiveStepVertex] using
    (Classical.choose_spec (Internal.positive_step G H e u hu)).2

/-- The stabilizer correction required when traversing a negative raw edge. -/
noncomputable def Internal.negativeStepVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) b) = b) :
    treeVertexStabilizer G H
      (actionOrbitMk H (RawBassSerreVertex G) b) :=
  Classical.choose (Internal.negative_step G H e u hu)

theorem Internal.negativeStepVertex_endpoint {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreVertex G}
    (e : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G) a b)
    (u : H)
    (hu : u.1 • rawTreeRepresentative G H
      (actionOrbitMk H (RawBassSerreVertex G) b) = b) :
    a = (u * Internal.negativeStepVertex G H e u hu *
      quotientEdgeLabel G H
        (rawBassSerreOrbitEdgeMap G H e)).1 •
      rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) a) := by
  simpa [Internal.negativeStepVertex] using
    (Classical.choose_spec (Internal.negative_step G H e u hu)).2

/-- Align the endpoint of a rooted raw tree path using the subgroup generated by tree data. -/
noncomputable def Internal.rawPathAlignmentGenerated {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : RawBassSerreVertex G} :
    @Quiver.Path (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      (RawBassSerreVertex.central 1) x →
      {u : H // x = u.1 • rawTreeRepresentative G H
        (actionOrbitMk H (RawBassSerreVertex G) x) ∧
        u ∈ Internal.treeDataGenerated G H}
  | @Quiver.Path.nil (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G) _ => by
      refine ⟨1, ?_, ?_⟩
      · change RawBassSerreVertex.central 1 =
          (1 : H).1 • rawTreeRepresentative G H
            (rawBassSerreOrbitRoot G H)
        rw [Internal.rawTreeRepresentative_root G H]
        change RawBassSerreVertex.central 1 =
          (1 : FreeProduct G) • RawBassSerreVertex.central 1
        exact (one_smul (FreeProduct G)
          (RawBassSerreVertex.central 1)).symm
      · exact (Internal.treeDataGenerated G H).one_mem
  | @Quiver.Path.cons (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      _ _ _ p e => by
      let ih := Internal.rawPathAlignmentGenerated G H p
      let u : H := ih.1
      have hu := ih.2.1.symm
      cases e using Subtype.casesOn with
      | mk e he =>
          cases e using Sum.casesOn with
          | inl f =>
              let v := Internal.positiveStepVertex G H f u hu
              refine ⟨u * v *
                (quotientEdgeLabel G H
                  (rawBassSerreOrbitEdgeMap G H f))⁻¹, ?_, ?_⟩
              · exact Internal.positiveStepVertex_endpoint G H f u hu
              · apply (Internal.treeDataGenerated G H).mul_mem
                · apply (Internal.treeDataGenerated G H).mul_mem
                  · exact ih.2.2
                  · exact Internal.treeDataGenerated_mem_vertex G H _ v
                · exact (Internal.treeDataGenerated G H).inv_mem
                    (Internal.treeDataGenerated_mem_edge G H
                      ⟨_, _, rawBassSerreOrbitEdgeMap G H f⟩)
          | inr f =>
              let v := Internal.negativeStepVertex G H f u hu
              refine ⟨u * v * quotientEdgeLabel G H
                (rawBassSerreOrbitEdgeMap G H f), ?_, ?_⟩
              · exact Internal.negativeStepVertex_endpoint G H f u hu
              · apply (Internal.treeDataGenerated G H).mul_mem
                · apply (Internal.treeDataGenerated G H).mul_mem
                  · exact ih.2.2
                  · exact Internal.treeDataGenerated_mem_vertex G H _ v
                · exact Internal.treeDataGenerated_mem_edge G H
                    ⟨_, _, rawBassSerreOrbitEdgeMap G H f⟩

/-- The element of the tree Kurosh product reconstructed along a rooted raw tree path. -/
noncomputable def Internal.rawPathProduct {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : RawBassSerreVertex G} :
    @Quiver.Path (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      (RawBassSerreVertex.central 1) x → TreeKuroshProduct G H
  | @Quiver.Path.nil (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G) _ => 1
  | @Quiver.Path.cons (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      _ _ _ p e => by
      let ih := Internal.rawPathAlignmentGenerated G H p
      let u : H := ih.1
      have hu := ih.2.1.symm
      let pp := Internal.rawPathProduct G H p
      cases e using Subtype.casesOn with
      | mk e he =>
          cases e using Sum.casesOn with
          | inl f =>
              let v := Internal.positiveStepVertex G H f u hu
              let v' : treeVertexStabilizer G H
                  (actionOrbitMk H (RawBassSerreVertex G)
                    (rawBassSerreEdgeDataSource G
                      (rawBassSerreEdgeDataOf G f))) :=
                ⟨v.1, by
                  change v.1 • rawTreeRepresentative G H
                    (actionOrbitMk H (RawBassSerreVertex G)
                      (rawBassSerreEdgeDataSource G
                        (rawBassSerreEdgeDataOf G f))) = _
                  rw [rawBassSerreEdgeDataOf_source G f]
                  exact v.property⟩
              exact pp * treeKuroshVertexInclusion G H
                (actionOrbitMk H (RawBassSerreVertex G)
                  (rawBassSerreEdgeDataSource G (rawBassSerreEdgeDataOf G f)))
                v' * (treeKuroshFreeInclusion G H
                  (quotientEdgeLoop G H
                    (rawBassSerreOrbitEdgeMap G H f)))⁻¹
          | inr f =>
              let v := Internal.negativeStepVertex G H f u hu
              let v' : treeVertexStabilizer G H
                  (actionOrbitMk H (RawBassSerreVertex G)
                    (rawBassSerreEdgeDataTarget G
                      (rawBassSerreEdgeDataOf G f))) :=
                ⟨v.1, by
                  change v.1 • rawTreeRepresentative G H
                    (actionOrbitMk H (RawBassSerreVertex G)
                      (rawBassSerreEdgeDataTarget G
                        (rawBassSerreEdgeDataOf G f))) = _
                  rw [rawBassSerreEdgeDataOf_target G f]
                  exact v.property⟩
              exact pp * treeKuroshVertexInclusion G H
                (actionOrbitMk H (RawBassSerreVertex G)
                  (rawBassSerreEdgeDataTarget G (rawBassSerreEdgeDataOf G f)))
                v' * treeKuroshFreeInclusion G H
                  (quotientEdgeLoop G H
                    (rawBassSerreOrbitEdgeMap G H f))

theorem treeKuroshProductToH_testRawPathProduct {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x : RawBassSerreVertex G}
    (p : @Quiver.Path (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      (RawBassSerreVertex.central 1) x) :
    treeKuroshProductToH G H (Internal.rawPathProduct G H p) =
      (Internal.rawPathAlignmentGenerated G H p).1 := by
  induction p with
  | nil =>
      simp [Internal.rawPathProduct, Internal.rawPathAlignmentGenerated]
  | @cons y z p e ih =>
      let iha := Internal.rawPathAlignmentGenerated G H p
      let u : H := iha.1
      have hu := iha.2.1.symm
      cases e using Subtype.casesOn with
      | mk e he =>
          cases e using Sum.casesOn with
          | inl f =>
              let v := Internal.positiveStepVertex G H f u hu
              dsimp only [Internal.rawPathProduct]
              rw [map_mul, map_mul,
                ih,
                treeKuroshProductToH_vertex, map_inv,
                treeKuroshProductToH_free,
                kuroshFreePartHom_quotientEdgeLoop]
              dsimp only [Internal.rawPathAlignmentGenerated]
          | inr f =>
              let v := Internal.negativeStepVertex G H f u hu
              dsimp only [Internal.rawPathProduct]
              rw [map_mul, map_mul,
                ih,
                treeKuroshProductToH_vertex,
                treeKuroshProductToH_free,
                kuroshFreePartHom_quotientEdgeLoop]
              dsimp only [Internal.rawPathAlignmentGenerated]

/-- The unique path in the raw spanning tree from the identity vertex. -/
noncomputable def Internal.rawSpanningTreePath {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (x : RawBassSerreVertex G) :
    @Quiver.Path (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      (RawBassSerreVertex.central 1) x := by
  letI : @Quiver.Arborescence (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G) :=
    Internal.rawSpanningTreeQuiverArborescence G
  letI : Unique (@Quiver.Path (RawBassSerreVertex G) (Internal.rawSpanningTreeQuiver G)
      (RawBassSerreVertex.central 1) x) :=
    @Quiver.Arborescence.uniquePath (RawBassSerreVertex G)
      (Internal.rawSpanningTreeQuiver G) (Internal.rawSpanningTreeQuiverArborescence G) x
  exact default

end GraphCoveringTheory.Kurosh
