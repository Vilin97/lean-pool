/-
Copyright (c) 2026 Arthur F. Ramos, David Barros Hulak, Ruy J.G.B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
import LeanPool.MarshallHall.MarshallHall.GrushkoReduction
import Mathlib.Data.List.SplitBy

/-! ### Alternating runs in a factor word

The graph-fold proof uses the following elementary normal-form fact.  If a
labelled path has trivial total label, then one of its maximal monochromatic
runs has trivial label.  We first package the list-theoretic part of that
argument.  The proof is deliberately phrased using `List.splitBy`, so the
maximality and the alternating boundary conditions are explicit.
-/

open Function Monoid.Coprod

noncomputable section

namespace MarshallHall
namespace GeneralGrushko

universe u

variable {G H : Type u} [Group G] [Group H]



/-- Tests whether two labels belong to the same factor of the free product. -/
def sameBinaryFactor (a b : Sum G H) : Bool :=
  decide (binarySumIndex (G := G) (H := H) a =
    binarySumIndex (G := G) (H := H) b)

/-- Splits a word into maximal consecutive runs of labels from the same factor. -/
def binaryRuns (u : List (Sum G H)) : List (List (Sum G H)) :=
  u.splitBy (sameBinaryFactor (G := G) (H := H))

omit [Group G] [Group H] in
theorem binaryRuns_flatten (u : List (Sum G H)) :
    (binaryRuns (G := G) (H := H) u).flatten = u := by
  exact List.flatten_splitBy (sameBinaryFactor (G := G) (H := H)) u

omit [Group G] [Group H] in
theorem binaryRuns_ne_nil {u : List (Sum G H)} {v : List (Sum G H)}
    (hv : v ∈ binaryRuns (G := G) (H := H) u) : v ≠ [] := by
  exact List.ne_nil_of_mem_splitBy hv

omit [Group G] [Group H] in
theorem binaryRuns_isChain {u : List (Sum G H)}
    {v : List (Sum G H)} (hv : v ∈ binaryRuns (G := G) (H := H) u) :
    v.IsChain (fun a b => binarySumIndex (G := G) (H := H) a =
      binarySumIndex (G := G) (H := H) b) := by
  exact (List.isChain_of_mem_splitBy hv).imp (by
    intro a b hab
    simpa [sameBinaryFactor] using hab)

omit [Group G] [Group H] in
theorem binaryRuns_boundary (u : List (Sum G H)) :
    (binaryRuns (G := G) (H := H) u).IsChain (fun v w =>
      v ∈ binaryRuns (G := G) (H := H) u ∧
      w ∈ binaryRuns (G := G) (H := H) u ∧
      ∃ hv hw, binarySumIndex (G := G) (H := H) (v.getLast hv) ≠
        binarySumIndex (G := G) (H := H) (w.head hw)) := by
  apply (List.isChain_getLast_head_splitBy
      (sameBinaryFactor (G := G) (H := H)) u).imp_of_mem_imp
  intro v w hv hw h
  rcases h with ⟨hv', hw', h⟩
  refine ⟨hv, hw, hv', hw', ?_⟩
  simpa [sameBinaryFactor] using h

omit [Group G] [Group H] in
theorem binaryRun_allSame {v : List (Sum G H)} (hv : v ≠ [])
    (hc : v.IsChain (fun a b => binarySumIndex (G := G) (H := H) a =
      binarySumIndex (G := G) (H := H) b)) :
    ∀ a ∈ v, binarySumIndex (G := G) (H := H) a =
      binarySumIndex (G := G) (H := H) (v.head hv) := by
  exact hc.induction
    (p := fun a => binarySumIndex (G := G) (H := H) a =
      binarySumIndex (G := G) (H := H) (v.head hv))
    (carries := by
      intro a b hab ha
      exact hab.symm.trans ha)
    (initial := by intro; rfl)

omit [Group G] [Group H] in
theorem exists_map_inl_of_idx_false {v : List (Sum G H)}
    (hv : ∀ a ∈ v, binarySumIndex (G := G) (H := H) a = false) :
    ∃ l : List G, v = l.map Sum.inl := by
  induction v with
  | nil => exact ⟨[], rfl⟩
  | cons a v ih =>
      have ha := hv a (by simp)
      cases a with
      | inl g =>
          obtain ⟨l, hl⟩ := ih (by
            intro b hb
            exact hv b (by simp [hb]))
          refine ⟨g :: l, ?_⟩
          simp [hl]
      | inr h =>
          simp only [binarySumIndex_inr] at ha
          cases ha

omit [Group G] [Group H] in
theorem exists_map_inr_of_idx_true {v : List (Sum G H)}
    (hv : ∀ a ∈ v, binarySumIndex (G := G) (H := H) a = true) :
    ∃ l : List H, v = l.map Sum.inr := by
  induction v with
  | nil => exact ⟨[], rfl⟩
  | cons a v ih =>
      have ha := hv a (by simp)
      cases a with
      | inl g =>
          simp only [binarySumIndex_inl] at ha
          cases ha
      | inr h =>
          obtain ⟨l, hl⟩ := ih (by
            intro b hb
            exact hv b (by simp [hb]))
          refine ⟨h :: l, ?_⟩
          simp [hl]

theorem factorWordProd_map_inl (l : List G) :
    factorWordProd (G := G) (H := H) (l.map Sum.inl) = inl l.prod := by
  induction l with
  | nil => simp [factorWordProd]
  | cons g l ih =>
      simp only [List.map_cons, factorWordProd, separatedMap]
      rw [ih, ← map_mul (Monoid.Coprod.inl : G →* G ∗ H)]
      rfl

theorem factorWordProd_map_inr (l : List H) :
    factorWordProd (G := G) (H := H) (l.map Sum.inr) = inr l.prod := by
  induction l with
  | nil => simp [factorWordProd]
  | cons h l ih =>
      simp only [List.map_cons, factorWordProd, separatedMap]
      rw [ih, ← map_mul (Monoid.Coprod.inr : H →* G ∗ H)]
      rfl

theorem factorWordProd_eq_prod (u : List (Sum G H)) :
    factorWordProd (G := G) (H := H) u =
      (u.map (separatedMap (G := G) (H := H))).prod := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      simp only [factorWordProd, List.map_cons, List.prod_cons]
      rw [ih]

/-- Multiplies a nonempty monochromatic run and tags its value by its initial factor. -/
def binaryRunTag (v : List (Sum G H)) (hv : v ≠ []) : Sum G H :=
  match _h : v.head hv with
  | Sum.inl _ => Sum.inl (Monoid.Coprod.fst (factorWordProd v))
  | Sum.inr _ => Sum.inr (Monoid.Coprod.snd (factorWordProd v))

/-- The value of a run, with an empty run represented by the left-factor identity. -/
def binaryRunTag' (v : List (Sum G H)) : Sum G H :=
  if hv : v = [] then Sum.inl 1 else binaryRunTag v hv

theorem binaryRunTag'_eq (v : List (Sum G H)) (hv : v ≠ []) :
    binaryRunTag' (G := G) (H := H) v = binaryRunTag v hv := by
  simp [binaryRunTag', hv]

theorem binaryRunTag_index {v : List (Sum G H)} (hv : v ≠ []) :
    binarySumIndex (G := G) (H := H) (binaryRunTag v hv) =
      binarySumIndex (G := G) (H := H) (v.head hv) := by
  unfold binaryRunTag
  split
  · rename_i hhead
    rw [hhead]
    rfl
  · rename_i hhead
    rw [hhead]
    rfl

theorem separatedMap_binaryRunTag {v : List (Sum G H)} (hv : v ≠ [])
    (hc : v.IsChain (fun a b => binarySumIndex (G := G) (H := H) a =
      binarySumIndex (G := G) (H := H) b)) :
    separatedMap (binaryRunTag v hv) = factorWordProd v := by
  have hall := binaryRun_allSame (G := G) (H := H) hv hc
  unfold binaryRunTag
  split
  · rename_i hhead
    have hidx : ∀ a ∈ v, binarySumIndex (G := G) (H := H) a = false := by
      intro a ha
      simpa [hhead] using hall a ha
    obtain ⟨l, hl⟩ := exists_map_inl_of_idx_false hidx
    rw [hl, factorWordProd_map_inl]
    simp [separatedMap]
  · rename_i hhead
    have hidx : ∀ a ∈ v, binarySumIndex (G := G) (H := H) a = true := by
      intro a ha
      simpa [hhead] using hall a ha
    obtain ⟨l, hl⟩ := exists_map_inr_of_idx_true hidx
    rw [hl, factorWordProd_map_inr]
    simp [separatedMap]

theorem separatedMap_binaryRunTag' {v : List (Sum G H)}
    {u : List (Sum G H)} (hv : v ∈ binaryRuns (G := G) (H := H) u) :
    separatedMap (binaryRunTag' (G := G) (H := H) v) = factorWordProd v := by
  have hv' := binaryRuns_ne_nil (G := G) (H := H) hv
  rw [binaryRunTag'_eq v hv']
  exact separatedMap_binaryRunTag hv' (binaryRuns_isChain hv)

theorem factorWordProd_flatten (l : List (List (Sum G H))) :
    factorWordProd (G := G) (H := H) l.flatten =
      (l.map (factorWordProd (G := G) (H := H))).prod := by
  induction l with
  | nil => simp [factorWordProd]
  | cons v l ih =>
      rw [List.flatten_cons, factorWordProd_append, ih]
      simp

/-- The sequence of factor-tagged products of the monochromatic runs of a word. -/
def binaryRunTags (u : List (Sum G H)) : List (Sum G H) :=
  (binaryRuns (G := G) (H := H) u).map binaryRunTag'

theorem binaryRunTags_chain (u : List (Sum G H)) :
    (binaryRunTags (G := G) (H := H) u).IsChain
      (fun a b => binarySumIndex (G := G) (H := H) a ≠
        binarySumIndex (G := G) (H := H) b) := by
  rw [binaryRunTags, List.isChain_map]
  apply (binaryRuns_boundary (G := G) (H := H) u).imp
  rintro v w ⟨hv_mem, hw_mem, hv, hw, hboundary⟩
  rw [binaryRunTag'_eq v hv, binaryRunTag'_eq w hw]
  rw [binaryRunTag_index hv,
    binaryRunTag_index hw]
  have hlast : binarySumIndex (G := G) (H := H) (v.getLast hv) =
      binarySumIndex (G := G) (H := H) (v.head hv) :=
    binaryRun_allSame hv (binaryRuns_isChain hv_mem) _ (List.getLast_mem hv)
  simpa [hlast] using hboundary

theorem factorWordProd_binaryRunTags (u : List (Sum G H)) :
    factorWordProd (G := G) (H := H) (binaryRunTags u) =
      factorWordProd (G := G) (H := H) u := by
  conv_rhs => rw [← binaryRuns_flatten (G := G) (H := H) u]
  rw [factorWordProd_flatten]
  conv_lhs => rw [binaryRunTags, factorWordProd_eq_prod]
  rw [List.map_map]
  apply congrArg List.prod
  apply List.map_congr_left
  intro v hv
  simpa only [Function.comp_apply] using separatedMap_binaryRunTag' hv

theorem binaryRunTag'_ne_one_of_factorWordProd_ne_one
    {v : List (Sum G H)} {u : List (Sum G H)}
    (hv : v ∈ binaryRuns (G := G) (H := H) u)
    (hprod : factorWordProd (G := G) (H := H) v ≠ 1) :
    binaryRunTag' (G := G) (H := H) v ≠ Sum.inl 1 ∧
      binaryRunTag' (G := G) (H := H) v ≠ Sum.inr 1 := by
  have hs := separatedMap_binaryRunTag' (G := G) (H := H) hv
  constructor
  · intro htag
    apply hprod
    rw [← hs, htag]
    simp [separatedMap]
  · intro htag
    apply hprod
    rw [← hs, htag]
    simp [separatedMap]

theorem exists_null_binary_run (u : List (Sum G H))
    (hu : u ≠ []) (hprod : factorWordProd (G := G) (H := H) u = 1) :
    ∃ v ∈ binaryRuns (G := G) (H := H) u,
      factorWordProd (G := G) (H := H) v = 1 := by
  by_contra h
  have hnon : ∀ v ∈ binaryRuns (G := G) (H := H) u,
      factorWordProd (G := G) (H := H) v ≠ 1 := by
    intro v hv hzero
    exact h ⟨v, hv, hzero⟩
  have htags_ne : ∀ a ∈ binaryRunTags (G := G) (H := H) u,
      a ≠ Sum.inl 1 ∧ a ≠ Sum.inr 1 := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact binaryRunTag'_ne_one_of_factorWordProd_ne_one hv (hnon v hv)
  have hruns : binaryRuns (G := G) (H := H) u ≠ [] := by
    intro hruns
    apply hu
    simpa [binaryRuns] using hruns
  have htags : binaryRunTags (G := G) (H := H) u ≠ [] := by
    simp [binaryRunTags, hruns]
  have hne : factorWordProd (G := G) (H := H)
      (binaryRunTags (G := G) (H := H) u) ≠ 1 :=
    factorWordProd_ne_one_of_reduced htags_ne
      (binaryRunTags_chain (G := G) (H := H) u) htags
  apply hne
  rw [factorWordProd_binaryRunTags, hprod]

theorem exists_null_monochromatic_run (u : List (Sum G H))
    (hu : u ≠ []) (hprod : factorWordProd (G := G) (H := H) u = 1) :
    ∃ v ∈ binaryRuns (G := G) (H := H) u, v ≠ [] ∧
      v.IsChain (fun a b => binarySumIndex (G := G) (H := H) a =
        binarySumIndex (G := G) (H := H) b) ∧
      factorWordProd (G := G) (H := H) v = 1 := by
  obtain ⟨v, hv, hvprod⟩ := exists_null_binary_run (G := G) (H := H) u hu hprod
  refine ⟨v, hv, binaryRuns_ne_nil hv, binaryRuns_isChain hv, hvprod⟩

end GeneralGrushko
end MarshallHall
