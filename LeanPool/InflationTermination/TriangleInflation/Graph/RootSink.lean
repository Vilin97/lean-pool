/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Soundness

/-!
# The root-sink expressibility lemma (A2)

Statements split from the original `Statements.lean` skeleton (one file per proving task);
see AUDIT-NOTES A2 and `papers/inflation-nontermination/paper/sections/12-pair-source.tex`
(Lemma `lem:rootsink`) for the mathematics.

`isAISet_iff_decomposition`, `isAISet_glue` and `gExpFeasible_iff_gAIFeasible` are proved.
Two statements of the original skeleton were false as written and have been removed:
`gInjectable_iff_raw` needed `1 ≤ t` (the corrected form is `gInjectable_iff_raw_of_one_le`,
and `not_forall_gInjectable_iff_raw` refutes the unrestricted one), and `expressible_iff_ai`
holds only for targets satisfying the ancestral-independence prescriptions (its intended
content is `Expressible.isAISet` together with `gExpFeasible_iff_gAIFeasible`). The two
consequences `flip_gExpFeasible` and `compatible_gExpFeasible` are proved at the end of this
file from the root-sink lemma. Everything in this file is proved.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## Auxiliary material

Everything in this section is new; the five statements of the task are unchanged and appear
below in their original form. -/

namespace RootSinkAux

/-! ### Incidence, ancestors and the shared-parent relation -/

/-- No vertex is isolated, so every vertex is incident to a source. -/
theorem inc_nonempty (v : Γ.V) : (Γ.inc v).Nonempty := by
  obtain ⟨w, hw⟩ := Γ.no_isolated v
  have hmem : s(v, w) ∈ Γ.G.edgeFinset := by simpa using hw
  exact ⟨⟨s(v, w), hmem⟩, by simp [PairGraph.inc]⟩

/-- Every copied observation has at least one copied latent ancestor. -/
theorem gAncestors_nonempty (o : GObs Γ t) : (gAncestors o).Nonempty := by
  obtain ⟨e, he⟩ := inc_nonempty (Γ := Γ) o.1
  refine ⟨(e, o.2 ⟨e, he⟩), ?_⟩
  simp only [gAncestors, Finset.mem_image]
  exact ⟨⟨e, he⟩, Finset.mem_univ _, rfl⟩

theorem sharesParent_refl (o : GObs Γ t) : SharesParent o o := by
  obtain ⟨x, hx⟩ := gAncestors_nonempty o
  exact fun h => (Finset.disjoint_left.1 h hx) hx

theorem sharesParent_symm {o p : GObs Γ t} (h : SharesParent o p) : SharesParent p o :=
  fun hd => h hd.symm

theorem not_sharesParent_of_ai {S T : Finset (GObs Γ t)} (h : GAncestrallyIndependent S T)
    {o p : GObs Γ t} (ho : o ∈ S) (hp : p ∈ T) : ¬ SharesParent o p := by
  intro hsp
  obtain ⟨x, hx1, hx2⟩ := Finset.not_disjoint_iff.1 hsp
  have h1 : x ∈ gAncestorsOf S := Finset.mem_biUnion.2 ⟨o, ho, hx1⟩
  have h2 : x ∈ gAncestorsOf T := Finset.mem_biUnion.2 ⟨p, hp, hx2⟩
  exact (Finset.disjoint_left.1 h h1) h2

theorem ai_of_not_sharesParent {S T : Finset (GObs Γ t)}
    (h : ∀ o ∈ S, ∀ p ∈ T, ¬ SharesParent o p) : GAncestrallyIndependent S T := by
  rw [GAncestrallyIndependent, Finset.disjoint_left]
  intro x hx hx'
  obtain ⟨o, ho, hxo⟩ := Finset.mem_biUnion.1 hx
  obtain ⟨p, hp, hxp⟩ := Finset.mem_biUnion.1 hx'
  exact h o ho p hp (Finset.not_disjoint_iff.2 ⟨x, hxo, hxp⟩)

theorem gAI_symm {S T : Finset (GObs Γ t)} (h : GAncestrallyIndependent S T) :
    GAncestrallyIndependent T S := Disjoint.symm h

theorem disjoint_of_ai {S T : Finset (GObs Γ t)} (h : GAncestrallyIndependent S T) :
    Disjoint S T := by
  rw [Finset.disjoint_left]
  intro o ho ho'
  exact not_sharesParent_of_ai h ho ho' (sharesParent_refl o)

theorem GInjectable.mono {S T : Finset (GObs Γ t)} (hST : S ⊆ T) (h : GInjectable T) :
    GInjectable S := by
  obtain ⟨ι, hι⟩ := h
  exact ⟨ι, hST.trans hι⟩

/-! ### Connectivity in the shared-parent graph, on the ambient type -/

/-- One step of the shared-parent graph on `S`. -/
def connStep (S : Finset (GObs Γ t)) (x y : GObs Γ t) : Prop :=
  x ∈ S ∧ y ∈ S ∧ SharesParent x y

/-- Connectivity in the shared-parent graph on `S`, phrased on the ambient type rather than
on the subtype, so that the same statement can be read for different ambient sets. -/
def conn (S : Finset (GObs Γ t)) : GObs Γ t → GObs Γ t → Prop :=
  Relation.ReflTransGen (connStep S)

theorem conn_refl (S : Finset (GObs Γ t)) (a : GObs Γ t) : conn S a a :=
  Relation.ReflTransGen.refl

theorem conn_mem_right {S : Finset (GObs Γ t)} {a b : GObs Γ t} (h : conn S a b) (ha : a ∈ S) :
    b ∈ S := by
  induction h with
  | refl => exact ha
  | tail _ hstep _ => exact hstep.2.1

theorem conn_symm {S : Finset (GObs Γ t)} {a b : GObs Γ t} (h : conn S a b) : conn S b a := by
  induction h with
  | refl => exact conn_refl _ _
  | @tail c d _ hcd ih =>
      exact Relation.ReflTransGen.head ⟨hcd.2.1, hcd.1, sharesParent_symm hcd.2.2⟩ ih

theorem conn_trans {S : Finset (GObs Γ t)} {a b c : GObs Γ t} (h : conn S a b)
    (h' : conn S b c) : conn S a c := Relation.ReflTransGen.trans h h'

theorem conn_mono {S T : Finset (GObs Γ t)} (hST : S ⊆ T) {a b : GObs Γ t} (h : conn S a b) :
    conn T a b := by
  induction h with
  | refl => exact conn_refl _ _
  | @tail c d _ hcd ih => exact ih.tail ⟨hST hcd.1, hST hcd.2.1, hcd.2.2⟩

/-- If everything connected to `a` inside `T` already lies in the smaller set `S`, then
connectivity inside `T` from `a` is connectivity inside `S`. -/
theorem conn_restrict {S T : Finset (GObs Γ t)} {a b : GObs Γ t}
    (hcl : ∀ p, conn T a p → p ∈ S) (h : conn T a b) : conn S a b := by
  induction h with
  | refl => exact conn_refl _ _
  | @tail c d hac hcd ih =>
      exact ih.tail ⟨hcl c hac, hcl d (hac.tail hcd), hcd.2.2⟩

theorem conn_of_sharedComponent {S : Finset (GObs Γ t)} {x y : S} (h : sharedComponent S x y) :
    conn S x.1 y.1 := by
  induction h with
  | refl => exact conn_refl _ _
  | @tail b c _ hbc ih => exact ih.tail ⟨b.2, c.2, hbc⟩

theorem sharedComponent_of_conn {S : Finset (GObs Γ t)} {a b : GObs Γ t} (h : conn S a b) :
    ∀ (ha : a ∈ S) (hb : b ∈ S), sharedComponent S ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => intro ha hb; exact Relation.ReflTransGen.refl
  | @tail c d hac hcd ih =>
      intro ha hb
      exact (ih ha hcd.1).tail hcd.2.2

/-- `IsAISet` in terms of `conn`: every component, described by `conn`, is injectable. -/
theorem isAISet_iff_conn (S : Finset (GObs Γ t)) :
    IsAISet S ↔ ∀ o ∈ S, ∃ B : Finset (GObs Γ t), (∀ p, p ∈ B ↔ conn S o p) ∧ GInjectable B := by
  constructor
  · intro h o ho
    obtain ⟨B, hB, hinj⟩ := h ⟨o, ho⟩
    refine ⟨B, fun p => ?_, hinj⟩
    rw [hB p]
    constructor
    · rintro ⟨hp, hc⟩; exact conn_of_sharedComponent hc
    · intro hc; exact ⟨conn_mem_right hc ho, sharedComponent_of_conn hc ho _⟩
  · intro h
    rintro ⟨o, ho⟩
    obtain ⟨B, hB, hinj⟩ := h o ho
    refine ⟨B, fun p => ?_, hinj⟩
    rw [hB p]
    constructor
    · intro hc; exact ⟨conn_mem_right hc ho, sharedComponent_of_conn hc ho _⟩
    · rintro ⟨hp, hc⟩; exact conn_of_sharedComponent hc

/-! ### Components and decompositions -/

/-- Every AI set has an AI decomposition: peel off the component of one member. -/
theorem exists_aiDecomposition_aux : ∀ (n : ℕ) (S : Finset (GObs Γ t)), S.card ≤ n →
    IsAISet S → ∃ D : AIDecomposition S,
      ∀ (m : Fin D.n), ∀ p ∈ D.block m, ∀ q, (q ∈ D.block m ↔ conn S p q) := by
  intro n
  induction n with
  | zero =>
      intro S hcard _
      have hS : S = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
      exact ⟨{ n := 0, block := fun m => m.elim0, inj := fun m => m.elim0,
               ai := fun m => m.elim0, cover := by simp [hS] }, fun m => m.elim0⟩
  | succ n ih =>
      intro S hcard hAI
      rcases Finset.eq_empty_or_nonempty S with rfl | ⟨o, ho⟩
      · exact ⟨{ n := 0, block := fun m => m.elim0, inj := fun m => m.elim0,
                 ai := fun m => m.elim0, cover := by simp }, fun m => m.elim0⟩
      obtain ⟨B, hB, hinj⟩ := (isAISet_iff_conn S).1 hAI o ho
      have hBS : B ⊆ S := fun p hp => conn_mem_right ((hB p).1 hp) ho
      have hoB : o ∈ B := (hB o).2 (conn_refl _ _)
      have hBpos : 1 ≤ B.card := Finset.card_pos.2 ⟨o, hoB⟩
      have hcard' : (S \ B).card ≤ n := by
        have hlt : (S \ B).card < S.card :=
          Finset.card_lt_card (Finset.sdiff_ssubset hBS ⟨o, hoB⟩)
        omega
      -- connectivity inside `S \ B` is connectivity inside `S`, for members of `S \ B`
      have hconn : ∀ p ∈ S \ B, ∀ q, conn (S \ B) p q ↔ conn S p q := by
        intro p hp q
        constructor
        · exact conn_mono Finset.sdiff_subset
        · refine conn_restrict (fun r hr => ?_)
          refine Finset.mem_sdiff.2 ⟨conn_mem_right hr (Finset.mem_sdiff.1 hp).1, fun hrB => ?_⟩
          exact (Finset.mem_sdiff.1 hp).2
            ((hB p).2 (conn_trans ((hB r).1 hrB) (conn_symm hr)))
      have hAI' : IsAISet (S \ B) := by
        rw [isAISet_iff_conn]
        intro p hp
        obtain ⟨C, hC, hCinj⟩ := (isAISet_iff_conn S).1 hAI p (Finset.mem_sdiff.1 hp).1
        exact ⟨C, fun q => (hC q).trans (hconn p hp q).symm, hCinj⟩
      obtain ⟨D', hD'comp⟩ := ih (S \ B) hcard' hAI'
      have hblock : ∀ i : Fin D'.n, D'.block i ⊆ S \ B := by
        intro i p hp
        rw [D'.cover]
        exact Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hp⟩
      have hBai : ∀ i : Fin D'.n, GAncestrallyIndependent B (D'.block i) := by
        intro i
        refine ai_of_not_sharesParent (fun x hx y hy hsp => ?_)
        have hyS : y ∈ S \ B := hblock i hy
        refine (Finset.mem_sdiff.1 hyS).2 ((hB y).2 ?_)
        exact conn_trans ((hB x).1 hx)
          (Relation.ReflTransGen.single ⟨hBS hx, (Finset.mem_sdiff.1 hyS).1, hsp⟩)
      refine ⟨{ n := D'.n + 1, block := Fin.cons B D'.block, inj := ?_, ai := ?_, cover := ?_ }, ?_⟩
      · intro m
        refine Fin.cases ?_ ?_ m
        · simpa using hinj
        · intro i; simpa using D'.inj i
      · intro m m' hmm
        obtain rfl | ⟨i, rfl⟩ := m.eq_zero_or_eq_succ <;>
          obtain rfl | ⟨j, rfl⟩ := m'.eq_zero_or_eq_succ
        · exact absurd rfl hmm
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact hBai j
        · simp only [Fin.cons_zero, Fin.cons_succ]
          exact gAI_symm (hBai i)
        · simp only [Fin.cons_succ]
          exact D'.ai i j (fun h => hmm (congrArg Fin.succ h))
      · ext p
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Fin.exists_fin_succ,
          Fin.cons_zero, Fin.cons_succ]
        constructor
        · intro hp
          by_cases hpB : p ∈ B
          · exact Or.inl hpB
          · have hp' : p ∈ S \ B := Finset.mem_sdiff.2 ⟨hp, hpB⟩
            rw [D'.cover] at hp'
            obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.1 hp'
            exact Or.inr ⟨i, hi⟩
        · rintro (hp | ⟨i, hi⟩)
          · exact hBS hp
          · exact (Finset.mem_sdiff.1 (hblock i hi)).1
      · intro m p hp q
        obtain rfl | ⟨i, rfl⟩ := m.eq_zero_or_eq_succ
        · simp only [Fin.cons_zero] at hp ⊢
          rw [hB q, hB p] at *
          exact ⟨fun hq => conn_trans (conn_symm hp) hq, fun hq => conn_trans hp hq⟩
        · simp only [Fin.cons_succ] at hp ⊢
          have hpS : p ∈ S \ B := hblock i hp
          exact (hD'comp i p hp q).trans (hconn p hpS q)

/-- A set with an AI decomposition is an AI set: the component of a member is contained in
any block containing it, because a step of the shared-parent graph cannot leave a block. -/
theorem isAISet_of_decomposition {S : Finset (GObs Γ t)} (D : AIDecomposition S) : IsAISet S := by
  classical
  rw [isAISet_iff_conn]
  intro o ho
  have hmem : o ∈ (Finset.univ : Finset (Fin D.n)).biUnion D.block := by rw [← D.cover]; exact ho
  obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 hmem
  have key : ∀ p, conn S o p → p ∈ D.block m := by
    intro p hp
    induction hp with
    | refl => exact hm
    | @tail c d _ hcd ih =>
        have hd : d ∈ (Finset.univ : Finset (Fin D.n)).biUnion D.block := by
          rw [← D.cover]; exact hcd.2.1
        obtain ⟨m', -, hm'⟩ := Finset.mem_biUnion.1 hd
        by_cases hmm : m' = m
        · exact hmm ▸ hm'
        · exact absurd hcd.2.2 (not_sharesParent_of_ai (D.ai m m' (Ne.symm hmm)) ih hm')
  refine ⟨(D.block m).filter (fun p => conn S o p), fun p => ?_,
    GInjectable.mono (Finset.filter_subset _ _) (D.inj m)⟩
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨key p h, h⟩⟩

/-! ### Chains, trails and `d`-separation -/

private theorem chain_concat {α : Type*} {R : α → α → Prop} {l : List α} {x y : α}
    (h : List.IsChain R (l ++ [x])) (hxy : R x y) : List.IsChain R (l ++ [x, y]) := by
  have hl : l ++ [x, y] = (l ++ [x]) ++ [y] := by simp
  rw [hl]
  refine h.append (List.isChain_singleton y) ?_
  intro u hu v hv
  rw [List.getLast?_concat] at hu
  simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hu hv
  subst hu; subst hv; exact hxy

/-- Connectivity inside `S` is witnessed by a chain whose interior lies in `S`. -/
theorem exists_chain_of_conn {S : Finset (GObs Γ t)} {a b : GObs Γ t} (h : conn S a b) :
    a = b ∨ ∃ mid : List (GObs Γ t), (∀ c ∈ mid, c ∈ S) ∧
      List.IsChain SharesParent (a :: (mid ++ [b])) := by
  induction h with
  | refl => exact Or.inl rfl
  | @tail c d hac hcd ih =>
      rcases ih with rfl | ⟨mid, hmid, hchain⟩
      · exact Or.inr ⟨[], by simp, by simpa using hcd.2.2⟩
      · refine Or.inr ⟨mid ++ [c], ?_, ?_⟩
        · intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · exact hmid x hx
          · simp only [List.mem_singleton] at hx
            exact hx ▸ hcd.1
        · have h1 : List.IsChain SharesParent ((a :: mid) ++ [c]) := by simpa using hchain
          have h2 := chain_concat h1 hcd.2.2
          simpa using h2

/-- A chain from `X` to `Y` inside `X ∪ Y ∪ Z` yields a trail that is active given `Z`:
cut the chain at the first place where it returns to `X` or reaches `Y`. -/
theorem exists_activeTrail {X Y Z : Finset (GObs Γ t)} :
    ∀ (n : ℕ) (a b : GObs Γ t) (mid : List (GObs Γ t)), mid.length ≤ n →
      a ∈ X → b ∈ Y → (∀ c ∈ mid, c ∈ X ∪ Y ∪ Z) →
      List.IsChain SharesParent (a :: (mid ++ [b])) →
      ∃ o₀ m o₁, ActiveTrail X Y Z o₀ m o₁ := by
  intro n
  induction n with
  | zero =>
      intro a b mid hlen ha hb _ hchain
      have hmid : mid = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.1 hlen)
      subst hmid
      exact ⟨a, [], b, ha, hb, by simp, hchain⟩
  | succ n ih =>
      intro a b mid hlen ha hb hmem hchain
      by_cases hz : ∀ c ∈ mid, c ∈ Z
      · exact ⟨a, mid, b, ha, hb, hz, hchain⟩
      · push Not at hz
        obtain ⟨c, hcmid, hcZ⟩ := hz
        obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hcmid
        have hlen₁ : l₁.length ≤ n := by
          have := hlen; simp only [List.length_append, List.length_cons] at this; omega
        have hlen₂ : l₂.length ≤ n := by
          have := hlen; simp only [List.length_append, List.length_cons] at this; omega
        have hcW : c ∈ X ∪ Y ∪ Z := hmem c hcmid
        rcases Finset.mem_union.1 hcW with hcXY | hcZ'
        · rcases Finset.mem_union.1 hcXY with hcX | hcY
          · refine ih c b l₂ hlen₂ hcX hb (fun x hx => hmem x ?_) ?_
            · exact List.mem_append.2 (Or.inr (List.mem_cons_of_mem _ hx))
            · have hsplit : a :: (l₁ ++ c :: l₂ ++ [b]) = (a :: l₁) ++ (c :: (l₂ ++ [b])) := by
                simp
              rw [hsplit] at hchain
              exact hchain.right_of_append
          · refine ih a c l₁ hlen₁ ha hcY (fun x hx => hmem x ?_) ?_
            · exact List.mem_append.2 (Or.inl hx)
            · have hsplit : a :: (l₁ ++ c :: l₂ ++ [b])
                  = (a :: (l₁ ++ [c])) ++ (l₂ ++ [b]) := by simp
              rw [hsplit] at hchain
              exact hchain.left_of_append
        · exact absurd hcZ' hcZ

/-- `d`-separation forbids connectivity from `X` to `Y` inside `X ∪ Y ∪ Z`. -/
theorem not_conn_of_dsep {X Y Z : Finset (GObs Γ t)} (hXY : Disjoint X Y) (hd : dsep X Y Z)
    {a b : GObs Γ t} (ha : a ∈ X) (hb : b ∈ Y) : ¬ conn (X ∪ Y ∪ Z) a b := by
  intro hc
  rcases exists_chain_of_conn hc with rfl | ⟨mid, hmid, hchain⟩
  · exact (Finset.disjoint_left.1 hXY ha) hb
  · obtain ⟨o₀, m, o₁, htr⟩ := exists_activeTrail mid.length a b mid le_rfl ha hb hmid hchain
    exact hd o₀ m o₁ htr

/-! ### Injectability -/

theorem mem_copySet_iff {ι : Γ.Edge → Fin t} {o : GObs Γ t} :
    o ∈ copySet ι ↔ ∀ e : Γ.inc o.1, o.2 e = ι e.1 := by
  constructor
  · intro h
    obtain ⟨v, -, hv⟩ := Finset.mem_image.1 h
    subst hv
    intro e
    rfl
  · intro h
    refine Finset.mem_image.2 ⟨o.1, Finset.mem_univ _, ?_⟩
    change (⟨o.1, fun e => ι e.1⟩ : GObs Γ t) = o
    have hf : (fun e : Γ.inc o.1 => ι e.1) = o.2 := by funext e; exact (h e).symm
    rw [hf]

/-- AUDIT-NOTES A1/A2: for `1 ≤ t` the working definition of injectability agrees with the
primitive Wolfe–Spekkens–Fritz condition. The hypothesis `1 ≤ t` is needed for the backward
direction: it supplies a copy index for the sources that the set leaves unconstrained. -/
theorem gInjectable_iff_raw_of_one_le (ht : 1 ≤ t) (S : Finset (GObs Γ t)) :
    GInjectable S ↔ GInjectableRaw S := by
  classical
  constructor
  · rintro ⟨ι, hS⟩
    have hmem : ∀ o ∈ S, ∀ e : Γ.inc o.1, o.2 e = ι e.1 :=
      fun o ho => mem_copySet_iff.1 (hS ho)
    refine ⟨?_, ?_⟩
    · rintro ⟨v, f⟩ ho ⟨w, g⟩ hp hv
      simp only at hv
      subst hv
      have hf : f = g := by
        funext e
        exact (hmem ⟨v, f⟩ ho e).trans (hmem ⟨v, g⟩ hp e).symm
      rw [hf]
    · intro o ho p hp e hoe hpe
      exact (hmem o ho ⟨e, hoe⟩).trans (hmem p hp ⟨e, hpe⟩).symm
  · rintro ⟨-, hshare⟩
    refine ⟨fun e => if h : ∃ p : GObs Γ t, p ∈ S ∧ e ∈ Γ.inc p.1 then
      h.choose.2 ⟨e, h.choose_spec.2⟩ else ⟨0, ht⟩, ?_⟩
    intro o ho
    refine mem_copySet_iff.2 (fun e => ?_)
    have hex : ∃ p : GObs Γ t, p ∈ S ∧ (e : Γ.Edge) ∈ Γ.inc p.1 := ⟨o, ho, e.2⟩
    rw [dite_eq_left hex]
    exact hshare o ho _ hex.choose_spec.1 e.1 e.2 hex.choose_spec.2

/-! ### Pushforward helpers -/

private theorem pushforward_comp' {α β γ : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    [DecidableEq γ] (w : α → ℝ) (F : α → β) (G : β → γ) :
    pushforward (pushforward w F) G = pushforward w (fun a => G (F a)) := by
  funext c
  simp only [pushforward]
  have key : ∀ b : β, (if G b = c then ∑ a, (if F a = b then w a else 0) else 0)
      = ∑ a, (if F a = b then (if G b = c then w a else 0) else 0) := by
    intro b
    by_cases h : G b = c <;> simp [h]
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (F a) (fun b => if G b = c then w a else 0)]
  simp

private theorem pushforward_injective {α β : Type*} [Fintype α] [DecidableEq β]
    (w : α → ℝ) {F : α → β} (hF : Function.Injective F) (a : α) :
    pushforward w F (F a) = w a := by
  classical
  have hkey : ∀ x : α, (if F x = F a then w x else 0) = (if x = a then w x else 0) := by
    intro x
    by_cases h : x = a
    · simp [h]
    · rw [ite_eq_right (fun hh => h (hF hh)), ite_eq_right h]
  simp only [pushforward, hkey]
  simp

private theorem sum_pushforward' {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (w : α → ℝ) (F : α → β) : ∑ b, pushforward w F b = ∑ a, w a := by
  simp only [pushforward]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_ite_eq Finset.univ (F a) (fun _ => w a)]
  simp

private theorem pushforward_nonneg {α β : Type*} [Fintype α] [DecidableEq β]
    {w : α → ℝ} (hw : ∀ a, 0 ≤ w a) (F : α → β) (b : β) : 0 ≤ pushforward w F b := by
  refine Finset.sum_nonneg (fun a _ => ?_)
  by_cases h : F a = b <;> simp [h, hw a]

/-- Restricting further can only increase the mass of a fibre: the marginal of a nonnegative
weight on a smaller set dominates the marginal on a larger one. -/
theorem pushforward_mono_of_subset {S T : Finset (GObs Γ t)} (hST : S ⊆ T)
    {Δ : GAssign Γ t → ℝ} (hΔ : ∀ ω, 0 ≤ Δ ω) (φ : T → Bool) :
    pushforward Δ (gRestrict T) φ ≤ pushforward Δ (gRestrict S) (subRestrict hST φ) := by
  simp only [pushforward]
  refine Finset.sum_le_sum (fun ω _ => ?_)
  by_cases h : gRestrict T ω = φ
  · have h' : gRestrict S ω = subRestrict hST φ := by
      funext o
      have := congrFun h ⟨o.1, hST o.2⟩
      exact this
    rw [ite_eq_left h, ite_eq_left h']
  · rw [ite_eq_right h]
    by_cases h' : gRestrict S ω = subRestrict hST φ
    · rw [ite_eq_left h']; exact hΔ ω
    · rw [ite_eq_right h']

/-! ### The marginal of an AI set -/

theorem readOnBlock_self {S : Finset (GObs Γ t)} (φ : S → Bool) :
    readOnBlock S S φ = φ := by
  funext o
  simp only [readOnBlock, dite_eq_left o.2]

theorem readOnBlock_sub {B A W : Finset (GObs Γ t)} (hBA : B ⊆ A) (hAW : A ⊆ W)
    (φ : W → Bool) :
    readOnBlock B A (subRestrict hAW φ) = readOnBlock B W φ := by
  funext o
  have ho : o.1 ∈ A := hBA o.2
  simp only [readOnBlock, dite_eq_left ho, dite_eq_left (hAW ho), subRestrict]

/-- Under a witness satisfying the ancestral-independence prescriptions, the marginal on a
set with an AI decomposition is the product of the injectable marginals of its blocks. -/
theorem marginal_eq_aiProduct {Δ : GAssign Γ t → ℝ} {P : GTarget Γ}
    (hprod : GAncestralProducts t Δ P) {S : Finset (GObs Γ t)} (D : AIDecomposition S) :
    pushforward Δ (gRestrict S) = aiProduct S D P := by
  have hbs : ∀ m : Fin D.n, D.block m ⊆ S := by
    intro m p hp
    rw [D.cover]
    exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hp⟩
  set Φ : (S → Bool) → (∀ m : Fin D.n, (D.block m) → Bool) :=
    fun φ m => readOnBlock (D.block m) S φ with hΦ
  have hfac : (fun ω m => gRestrict (D.block m) ω) = fun ω => Φ (gRestrict S ω) := by
    funext ω m o
    simp only [hΦ, readOnBlock, dite_eq_left (hbs m o.2), gRestrict]
  have hinjΦ : Function.Injective Φ := by
    intro φ φ' h
    funext o
    have hmem : o.1 ∈ (Finset.univ : Finset (Fin D.n)).biUnion D.block := by
      rw [← D.cover]; exact o.2
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 hmem
    have := congrFun (congrFun h m) ⟨o.1, hm⟩
    simpa only [hΦ, readOnBlock, dite_eq_left o.2] using this
  funext φ
  have h1 : pushforward Δ (fun ω m => gRestrict (D.block m) ω) (Φ φ)
      = pushforward (pushforward Δ (gRestrict S)) Φ (Φ φ) := by
    rw [pushforward_comp' Δ (gRestrict S) Φ, hfac]
  rw [hprod D.n D.block D.inj D.ai] at h1
  rw [pushforward_injective _ hinjΦ φ] at h1
  rw [← h1]
  rfl

/-- Under `d`-separation, the component of a member of `X ∪ Y ∪ Z` in the shared-parent graph
lies inside `X ∪ Z` or inside `Y ∪ Z`: a shortest path joining `X` to `Y` inside a component
has all its interior in `Z`, so it is an active trail. -/
theorem conn_component_side {X Y Z : Finset (GObs Γ t)} (hXY : Disjoint X Y) (hd : dsep X Y Z)
    {o : GObs Γ t} (ho : o ∈ X ∪ Y ∪ Z) :
    (∀ p, conn (X ∪ Y ∪ Z) o p → p ∈ X ∪ Z) ∨ (∀ p, conn (X ∪ Y ∪ Z) o p → p ∈ Y ∪ Z) := by
  by_cases hY' : ∃ b, conn (X ∪ Y ∪ Z) o b ∧ b ∈ Y
  · obtain ⟨b, hb, hbY⟩ := hY'
    refine Or.inr (fun p hp => ?_)
    have hpW : p ∈ X ∪ Y ∪ Z := conn_mem_right hp ho
    rcases Finset.mem_union.1 hpW with hp' | hp'
    · rcases Finset.mem_union.1 hp' with hpX | hpY
      · exact absurd (conn_trans (conn_symm hp) hb) (not_conn_of_dsep hXY hd hpX hbY)
      · exact Finset.mem_union_left _ hpY
    · exact Finset.mem_union_right _ hp'
  · refine Or.inl (fun p hp => ?_)
    have hpW : p ∈ X ∪ Y ∪ Z := conn_mem_right hp ho
    rcases Finset.mem_union.1 hpW with hp' | hp'
    · rcases Finset.mem_union.1 hp' with hpX | hpY
      · exact Finset.mem_union_left _ hpX
      · exact absurd ⟨p, hp, hpY⟩ hY'
    · exact Finset.mem_union_right _ hp'

/-- The unrestricted form of `gInjectable_iff_raw_of_one_le` is false: at `t = 0` a scenario
with a vertex has no copied observations at all (every vertex is incident to a source, and
there is no map from a nonempty type to `Fin 0`), so the only set of copied observations is
`∅`. That set satisfies the primitive Wolfe–Spekkens–Fritz condition vacuously, while
`GInjectable ∅` asks for a global index assignment `Γ.Edge → Fin 0`, which does not exist. -/
theorem not_forall_gInjectable_iff_raw :
    ¬ ∀ (Γ : PairGraph) (t : ℕ) (S : Finset (GObs Γ t)), GInjectable S ↔ GInjectableRaw S := by
  intro h
  obtain ⟨ι, -⟩ := (h (path 2 le_rfl) 0 ∅).2 ⟨by simp, by simp⟩
  obtain ⟨e, -⟩ := inc_nonempty (Γ := path 2 le_rfl) (show (path 2 le_rfl).V from ⟨0, by norm_num⟩)
  exact (ι e).elim0

end RootSinkAux

open RootSinkAux

/-! ## A2: the root-sink expressibility lemma -/

/-- An AI set is exactly a set presented as a union of pairwise ancestrally independent
injectable blocks: the blocks may be taken to be the connected components of the
shared-parent graph (AUDIT-NOTES A2). -/
theorem isAISet_iff_decomposition (S : Finset (GObs Γ t)) :
    IsAISet S ↔ Nonempty (AIDecomposition S) :=
  ⟨fun h => ⟨(exists_aiDecomposition_aux S.card S le_rfl h).choose⟩,
    fun ⟨D⟩ => isAISet_of_decomposition D⟩

/-- AUDIT-NOTES A2, the geometric half of the root-sink lemma. If `X ∪ Z` and `Y ∪ Z` are AI
sets and `X` is `d`-separated from `Y` by `Z`, then every connected component of the
shared-parent graph on `X ∪ Y ∪ Z` lies inside `X ∪ Z` or inside `Y ∪ Z`, hence is
injectable, so `X ∪ Y ∪ Z` is again an AI set. (Take a shortest path inside a component from
`X` to `Y`: its internal vertices lie in `Z`, so it is an active trail.) -/
theorem isAISet_glue {X Y Z : Finset (GObs Γ t)} (hX : IsAISet (X ∪ Z)) (hY : IsAISet (Y ∪ Z))
    (hXY : Disjoint X Y) (hd : dsep X Y Z) :
    IsAISet (X ∪ Y ∪ Z) := by
  rw [isAISet_iff_conn]
  intro o ho
  rcases conn_component_side hXY hd ho with hsub | hsub
  · obtain ⟨B, hB, hinj⟩ := (isAISet_iff_conn _).1 hX o (hsub o (conn_refl _ _))
    refine ⟨B, fun p => ?_, hinj⟩
    rw [hB p]
    exact ⟨fun h => conn_mono (sub_left_union X Y Z) h, fun h => conn_restrict hsub h⟩
  · obtain ⟨B, hB, hinj⟩ := (isAISet_iff_conn _).1 hY o (hsub o (conn_refl _ _))
    refine ⟨B, fun p => ?_, hinj⟩
    rw [hB p]
    exact ⟨fun h => conn_mono (sub_right_union X Y Z) h, fun h => conn_restrict hsub h⟩


namespace RootSinkAux

/-! ### Consequences of the glue lemma

Subsets of AI sets are AI sets, so every expressible set is an AI set. -/

theorem isAISet_subset {S S' : Finset (GObs Γ t)} (hS : IsAISet S) (hsub : S' ⊆ S) :
    IsAISet S' := by
  classical
  rw [isAISet_iff_conn]
  intro o ho
  obtain ⟨B, hB, hinj⟩ := (isAISet_iff_conn S).1 hS o (hsub ho)
  refine ⟨S'.filter (fun p => conn S' o p), fun p => ?_, ?_⟩
  · simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨conn_mem_right h ho, h⟩⟩
  · refine GInjectable.mono (fun p hp => ?_) hinj
    rw [Finset.mem_filter] at hp
    exact (hB p).2 (conn_mono hsub hp.2)

theorem isAISet_of_injectable {S : Finset (GObs Γ t)} (hS : GInjectable S) : IsAISet S := by
  classical
  rw [isAISet_iff_conn]
  intro o ho
  refine ⟨S.filter (fun p => conn S o p), fun p => ?_,
    GInjectable.mono (Finset.filter_subset _ _) hS⟩
  simp only [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨conn_mem_right h ho, h⟩⟩

/-- Every recursively expressible set is an AI set (AUDIT-NOTES A2). -/
theorem Expressible.isAISet {P : GTarget Γ} {S : Finset (GObs Γ t)} {μ : (S → Bool) → ℝ}
    (h : Expressible t P S μ) : IsAISet S := by
  induction h with
  | inj hS => exact isAISet_of_injectable hS
  | glue _ _ hXY hXZ hYZ hd ih₁ ih₂ => exact isAISet_glue ih₁ ih₂ hXY hd
  | marg hST _ ih => exact isAISet_subset ih hST

/-! ### From the AI prescriptions to the expressible prescriptions -/

/-- Intersecting the blocks of an AI decomposition of `W` with a subset `A` gives an AI
decomposition of `A`. -/
def restrictDecomp {W : Finset (GObs Γ t)} (D : AIDecomposition W) (A : Finset (GObs Γ t))
    (hA : A ⊆ W) : AIDecomposition A where
  n := D.n
  block := fun m => D.block m ∩ A
  inj := fun m => GInjectable.mono Finset.inter_subset_left (D.inj m)
  ai := fun m m' hmm => ai_of_not_sharesParent (fun _ hx _ hy =>
    not_sharesParent_of_ai (D.ai m m' hmm) (Finset.mem_inter.1 hx).1 (Finset.mem_inter.1 hy).1)
  cover := by
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_inter]
    constructor
    · intro hp
      have hpW : p ∈ (Finset.univ : Finset (Fin D.n)).biUnion D.block := by
        rw [← D.cover]; exact hA hp
      obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 hpW
      exact ⟨m, hm, hp⟩
    · rintro ⟨m, hm, hp⟩
      exact hp

theorem marginal_sub_eq_prod {Δ : GAssign Γ t → ℝ} {P : GTarget Γ}
    (hprod : GAncestralProducts t Δ P) {W A : Finset (GObs Γ t)} (D : AIDecomposition W)
    (hA : A ⊆ W) (φ : W → Bool) :
    pushforward Δ (gRestrict A) (subRestrict hA φ)
      = ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m ∩ A))
          (readOnBlock (D.block m ∩ A) W φ) := by
  rw [marginal_eq_aiProduct hprod (restrictDecomp D A hA)]
  simp only [aiProduct, restrictDecomp]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [readOnBlock_sub (Finset.inter_subset_right) hA φ]
  rfl

/-- AUDIT-NOTES A2: a witness satisfying the injectable and ancestral-independence
prescriptions satisfies every expressible prescription. -/
theorem expPrescriptions_of_ai {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hlaw : IsLaw Δ)
    (hinjm : GInjectableMarginals t Δ P) (hprod : GAncestralProducts t Δ P) :
    ∀ (S : Finset (GObs Γ t)) (μ : (S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ := by
  intro S μ h
  induction h with
  | @inj S hS => exact hinjm S hS
  | @marg S T μ hST _ ih =>
      rw [← ih, pushforward_comp']
      rfl
  | @glue X Y Z μ₁ μ₂ h₁ h₂ hXY hXZ hYZ hd ih₁ ih₂ =>
      classical
      have hXZW : X ∪ Z ⊆ X ∪ Y ∪ Z := sub_left_union X Y Z
      have hYZW : Y ∪ Z ⊆ X ∪ Y ∪ Z := sub_right_union X Y Z
      have hZW : Z ⊆ X ∪ Y ∪ Z := sub_mid_union X Y Z
      obtain ⟨D, hDcomp⟩ := exists_aiDecomposition_aux (X ∪ Y ∪ Z).card (X ∪ Y ∪ Z) le_rfl
        (isAISet_glue (Expressible.isAISet h₁) (Expressible.isAISet h₂) hXY hd)
      have hbs : ∀ m : Fin D.n, D.block m ⊆ X ∪ Y ∪ Z := by
        intro m p hp
        rw [D.cover]
        exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hp⟩
      have hside : ∀ m : Fin D.n, D.block m ⊆ X ∪ Z ∨ D.block m ⊆ Y ∪ Z := by
        intro m
        rcases Finset.eq_empty_or_nonempty (D.block m) with he | ⟨p, hp⟩
        · exact Or.inl (by rw [he]; exact Finset.empty_subset _)
        · rcases conn_component_side hXY hd (hbs m hp) with hs | hs
          · exact Or.inl (fun q hq => hs q ((hDcomp m p hp q).1 hq))
          · exact Or.inr (fun q hq => hs q ((hDcomp m p hp q).1 hq))
      funext φ
      have e1 : μ₁ (subRestrict hXZW φ)
          = ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m ∩ (X ∪ Z)))
              (readOnBlock (D.block m ∩ (X ∪ Z)) (X ∪ Y ∪ Z) φ) := by
        rw [← ih₁]; exact marginal_sub_eq_prod hprod D hXZW φ
      have e2 : μ₂ (subRestrict hYZW φ)
          = ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m ∩ (Y ∪ Z)))
              (readOnBlock (D.block m ∩ (Y ∪ Z)) (X ∪ Y ∪ Z) φ) := by
        rw [← ih₂]; exact marginal_sub_eq_prod hprod D hYZW φ
      have e3 : pushforward Δ (gRestrict Z) (subRestrict hZW φ)
          = ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m ∩ Z))
              (readOnBlock (D.block m ∩ Z) (X ∪ Y ∪ Z) φ) :=
        marginal_sub_eq_prod hprod D hZW φ
      have e4 : pushforward Δ (gRestrict (X ∪ Y ∪ Z)) φ
          = ∏ m : Fin D.n, pushforward P (gPartyRead (D.block m))
              (readOnBlock (D.block m) (X ∪ Y ∪ Z) φ) := by
        have h0 := marginal_sub_eq_prod hprod D (Finset.Subset.refl (X ∪ Y ∪ Z)) φ
        refine h0.trans (Finset.prod_congr rfl (fun m _ => ?_))
        rw [Finset.inter_eq_left.2 (hbs m)]
      have key : ∀ m : Fin D.n,
          (pushforward P (gPartyRead (D.block m ∩ (X ∪ Z)))
              (readOnBlock (D.block m ∩ (X ∪ Z)) (X ∪ Y ∪ Z) φ))
            * (pushforward P (gPartyRead (D.block m ∩ (Y ∪ Z)))
              (readOnBlock (D.block m ∩ (Y ∪ Z)) (X ∪ Y ∪ Z) φ))
          = (pushforward P (gPartyRead (D.block m))
              (readOnBlock (D.block m) (X ∪ Y ∪ Z) φ))
            * (pushforward P (gPartyRead (D.block m ∩ Z))
              (readOnBlock (D.block m ∩ Z) (X ∪ Y ∪ Z) φ)) := by
        intro m
        rcases hside m with hs | hs
        · have h1 : D.block m ∩ (X ∪ Z) = D.block m := Finset.inter_eq_left.2 hs
          have h2 : D.block m ∩ (Y ∪ Z) = D.block m ∩ Z := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hp, hpY | hpZ⟩
              · rcases Finset.mem_union.1 (hs hp) with hpX | hpZ
                · exact absurd hpX (Finset.disjoint_right.1 hXY hpY)
                · exact absurd hpZ (Finset.disjoint_left.1 hYZ hpY)
              · exact ⟨hp, hpZ⟩
            · rintro ⟨hp, hpZ⟩
              exact ⟨hp, Or.inr hpZ⟩
          rw [h1, h2]
        · have h1 : D.block m ∩ (Y ∪ Z) = D.block m := Finset.inter_eq_left.2 hs
          have h2 : D.block m ∩ (X ∪ Z) = D.block m ∩ Z := by
            ext p
            simp only [Finset.mem_inter, Finset.mem_union]
            constructor
            · rintro ⟨hp, hpX | hpZ⟩
              · rcases Finset.mem_union.1 (hs hp) with hpY | hpZ
                · exact absurd hpY (Finset.disjoint_left.1 hXY hpX)
                · exact absurd hpZ (Finset.disjoint_left.1 hXZ hpX)
              · exact ⟨hp, hpZ⟩
            · rintro ⟨hp, hpZ⟩
              exact ⟨hp, Or.inr hpZ⟩
          rw [h1, h2, mul_comm]
      have hprodid : μ₁ (subRestrict hXZW φ) * μ₂ (subRestrict hYZW φ)
          = pushforward Δ (gRestrict (X ∪ Y ∪ Z)) φ
            * pushforward Δ (gRestrict Z) (subRestrict hZW φ) := by
        rw [e1, e2, e3, e4, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl (fun m _ => key m)
      have hmz : pushforward μ₁ (subRestrict (sub_mid_left X Z))
          (subRestrict (sub_mid_union X Y Z) φ)
          = pushforward Δ (gRestrict Z) (subRestrict hZW φ) := by
        rw [← ih₁, pushforward_comp']
        rfl
      have hnn := pushforward_nonneg hlaw.1 (gRestrict Z) (subRestrict hZW φ)
      simp only [glueLaw, hmz]
      rcases lt_or_ge 0 (pushforward Δ (gRestrict Z) (subRestrict hZW φ)) with hpos | hle
      · rw [ite_eq_left hpos, hprodid, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]
      · have hz : pushforward Δ (gRestrict Z) (subRestrict hZW φ) = 0 := le_antisymm hle hnn
        rw [ite_eq_right (by rw [hz]; exact lt_irrefl 0)]
        refine le_antisymm ?_ (pushforward_nonneg hlaw.1 _ _)
        rw [← hz]
        exact pushforward_mono_of_subset hZW hlaw.1 φ

/-! ### From the expressible prescriptions to the AI prescriptions -/

theorem readOnBlock_eq_subRestrict {B W : Finset (GObs Γ t)} (h : B ⊆ W) (φ : W → Bool) :
    readOnBlock B W φ = subRestrict h φ := by
  funext o
  simp only [readOnBlock, dite_eq_left (h o.2), subRestrict]

/-- Transport of membership along an equality of sets. -/
theorem castMem {S T : Finset (GObs Γ t)} (h : S = T) {p : GObs Γ t} (hp : p ∈ S) : p ∈ T := by
  subst h; exact hp

/-- Expressibility transports along an equality of sets. -/
theorem Expressible.reindex {P : GTarget Γ} {S T : Finset (GObs Γ t)} (h : S = T)
    {μ : (S → Bool) → ℝ} (hμ : Expressible t P S μ) :
    Expressible t P T (fun ψ : T → Bool => μ (fun o : S => ψ ⟨o.1, castMem h o.2⟩)) := by
  subst h
  exact hμ

theorem pushforward_gRestrict_reindex {S T : Finset (GObs Γ t)} (h : S = T)
    (Δ : GAssign Γ t → ℝ) (ψ : T → Bool) :
    pushforward Δ (gRestrict S) (fun o : S => ψ ⟨o.1, castMem h o.2⟩)
      = pushforward Δ (gRestrict T) ψ := by
  subst h
  rfl

theorem eq_of_empty_fun (a b : (∅ : Finset (GObs Γ t)) → Bool) : a = b := by
  funext o
  exact absurd o.2 (Finset.notMem_empty _)

theorem pushforward_to_empty {S : Finset (GObs Γ t)} (ν : (S → Bool) → ℝ)
    (h : (∅ : Finset (GObs Γ t)) ⊆ S) (χ : (∅ : Finset (GObs Γ t)) → Bool) :
    pushforward ν (subRestrict h) χ = ∑ ψ, ν ψ := by
  simp only [pushforward]
  exact Finset.sum_congr rfl (fun ψ _ => ite_eq_left (eq_of_empty_fun _ _))

/-- Ancestrally independent sets are `d`-separated by the empty set: a trail between them
would need an interior vertex, which the empty conditioning set cannot supply. -/
theorem dsep_empty_of_ai {A B : Finset (GObs Γ t)} (hAB : GAncestrallyIndependent A B) :
    dsep A B ∅ := by
  rintro o₀ mid o₁ ⟨h0, h1, hmid, hchain⟩
  have hnil : mid = [] := by
    cases mid with
    | nil => rfl
    | cons c l => exact absurd (hmid c List.mem_cons_self) (Finset.notMem_empty _)
  subst hnil
  have : SharesParent o₀ o₁ := by simpa using hchain
  exact not_sharesParent_of_ai hAB h0 h1 this

/-- Two ancestrally independent expressible sets glue, with `Z = ∅`, to their union. -/
theorem expressible_union_of_ai {P : GTarget Γ} {A B : Finset (GObs Γ t)}
    {νA : (A → Bool) → ℝ} {νB : (B → Bool) → ℝ}
    (hA : Expressible t P A νA) (hB : Expressible t P B νB)
    (hAB : GAncestrallyIndependent A B) :
    ∃ μ : ((A ∪ B : Finset (GObs Γ t)) → Bool) → ℝ, Expressible t P (A ∪ B) μ := by
  have h1 := Expressible.reindex (Finset.union_empty A).symm hA
  have h2 := Expressible.reindex (Finset.union_empty B).symm hB
  have hg := Expressible.glue h1 h2 (disjoint_of_ai hAB) (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right B) (dsep_empty_of_ai hAB)
  exact ⟨_, Expressible.reindex (by simp) hg⟩

/-- Under a witness satisfying the expressible prescriptions, ancestrally independent sets
are independent. -/
theorem marginal_union_of_ai {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hlaw : IsLaw Δ)
    (hexp : ∀ (S : Finset (GObs Γ t)) (μ : (S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ)
    {A B : Finset (GObs Γ t)} {νA : (A → Bool) → ℝ} {νB : (B → Bool) → ℝ}
    (hA : Expressible t P A νA) (hB : Expressible t P B νB)
    (hAB : GAncestrallyIndependent A B) (φ : (A ∪ B : Finset (GObs Γ t)) → Bool) :
    pushforward Δ (gRestrict (A ∪ B)) φ
      = pushforward Δ (gRestrict A) (subRestrict Finset.subset_union_left φ)
        * pushforward Δ (gRestrict B) (subRestrict Finset.subset_union_right φ) := by
  have h1 := Expressible.reindex (Finset.union_empty A).symm hA
  have h2 := Expressible.reindex (Finset.union_empty B).symm hB
  have hg := Expressible.glue h1 h2 (disjoint_of_ai hAB) (Finset.disjoint_empty_right A)
    (Finset.disjoint_empty_right B) (dsep_empty_of_ai hAB)
  have hset : A ∪ B ∪ ∅ = A ∪ B := Finset.union_empty _
  have hval := congrFun (hexp _ _ hg)
    (fun o : (A ∪ B ∪ ∅ : Finset (GObs Γ t)) => φ ⟨o.1, castMem hset o.2⟩)
  rw [pushforward_gRestrict_reindex hset Δ φ] at hval
  rw [hval]
  -- the `Z = ∅` fibre mass is the total mass of `Δ`, namely one
  have hmass : pushforward (fun ψ : ((A ∪ ∅ : Finset (GObs Γ t)) → Bool) =>
      νA (fun o : A => ψ ⟨o.1, castMem (Finset.union_empty A).symm o.2⟩))
      (subRestrict (sub_mid_left A ∅))
      (subRestrict (sub_mid_union A B ∅)
        (fun o : (A ∪ B ∪ ∅ : Finset (GObs Γ t)) => φ ⟨o.1, castMem hset o.2⟩)) = 1 := by
    rw [pushforward_to_empty]
    rw [← hexp _ _ h1]
    rw [sum_pushforward']
    exact hlaw.2
  simp only [glueLaw, hmass]
  rw [ite_eq_left one_pos, div_one, hexp A νA hA, hexp B νB hB]
  rfl

/-- Iterated gluing with `Z = ∅`: the marginal on a union of pairwise ancestrally
independent injectable sets is the product of their marginals. -/
theorem marginal_biUnion_prod {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hlaw : IsLaw Δ)
    (hexp : ∀ (S : Finset (GObs Γ t)) (μ : (S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ)
    {n : ℕ} (S : Fin n → Finset (GObs Γ t)) (hinj : ∀ m, GInjectable (S m))
    (hai : ∀ m m', m ≠ m' → GAncestrallyIndependent (S m) (S m'))
    (hempty : GInjectable (∅ : Finset (GObs Γ t))) :
    ∀ (I : Finset (Fin n)) (V : Finset (GObs Γ t)), V = I.biUnion S →
      (∃ μ, Expressible t P V μ) ∧
      ∀ φ : ↥V → Bool, pushforward Δ (gRestrict V) φ
          = ∏ m ∈ I, pushforward Δ (gRestrict (S m)) (readOnBlock (S m) V φ) := by
  intro I
  induction I using Finset.induction_on with
  | empty =>
      intro V hV
      rw [Finset.biUnion_empty] at hV
      subst hV
      refine ⟨⟨_, Expressible.inj (P := P) hempty⟩, fun φ => ?_⟩
      rw [Finset.prod_empty]
      simp only [pushforward]
      rw [Finset.sum_congr rfl (fun ω _ => ite_eq_left (eq_of_empty_fun _ _))]
      exact hlaw.2
  | @insert m₀ I' hm₀ ih =>
      intro V hV
      rw [Finset.biUnion_insert] at hV
      subst hV
      have hsub : ∀ m ∈ I', S m ⊆ I'.biUnion S := fun m hm =>
        Finset.subset_biUnion_of_mem S hm
      have haiU : GAncestrallyIndependent (S m₀) (I'.biUnion S) := by
        refine ai_of_not_sharesParent (fun x hx y hy => ?_)
        obtain ⟨m, hm, hym⟩ := Finset.mem_biUnion.1 hy
        exact not_sharesParent_of_ai (hai m₀ m (fun h => hm₀ (h ▸ hm))) hx hym
      obtain ⟨⟨μ', hμ'⟩, ihprod⟩ := ih (I'.biUnion S) rfl
      refine ⟨expressible_union_of_ai (Expressible.inj (hinj m₀)) hμ' haiU, fun φ => ?_⟩
      rw [Finset.prod_insert hm₀,
        marginal_union_of_ai hlaw hexp (Expressible.inj (hinj m₀)) hμ' haiU φ,
        ihprod (subRestrict Finset.subset_union_right φ)]
      congr 1
      · rw [readOnBlock_eq_subRestrict]
      · refine Finset.prod_congr rfl (fun m hm => ?_)
        rw [readOnBlock_sub (hsub m hm) Finset.subset_union_right φ]

/-- AUDIT-NOTES A2: a witness satisfying the expressible prescriptions satisfies the
ancestral-independence prescriptions. -/
theorem gAncestralProducts_of_exp {Δ : GAssign Γ t → ℝ} {P : GTarget Γ} (hlaw : IsLaw Δ)
    (hexp : ∀ (S : Finset (GObs Γ t)) (μ : (S → Bool) → ℝ), Expressible t P S μ →
      pushforward Δ (gRestrict S) = μ) : GAncestralProducts t Δ P := by
  classical
  have hinjm : ∀ S : Finset (GObs Γ t), GInjectable S →
      pushforward Δ (gRestrict S) = pushforward P (gPartyRead S) :=
    fun S hS => hexp S _ (Expressible.inj hS)
  intro n S hinj hai
  funext ψ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hsub : ∀ a b : (∀ m : Fin 0, (S m) → Bool), a = b := by
      intro a b; funext m; exact m.elim0
    simp only [pushforward]
    rw [Finset.sum_congr rfl (fun ω _ => ite_eq_left (hsub _ _))]
    rw [hlaw.2]
    simp
  · have hempty : GInjectable (∅ : Finset (GObs Γ t)) := by
      obtain ⟨ι, -⟩ := hinj ⟨0, hn⟩
      exact ⟨ι, Finset.empty_subset _⟩
    set U : Finset (GObs Γ t) := (Finset.univ : Finset (Fin n)).biUnion S with hUdef
    have hmain := marginal_biUnion_prod hlaw hexp S hinj hai hempty Finset.univ U hUdef
    set Φ : (U → Bool) → (∀ m : Fin n, (S m) → Bool) :=
      fun φ m => readOnBlock (S m) U φ with hΦ
    have hmem : ∀ (m : Fin n) (p : GObs Γ t), p ∈ S m → p ∈ U := by
      intro m p hp
      exact Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hp⟩
    have hfac : (fun ω (m : Fin n) => gRestrict (S m) ω) = fun ω => Φ (gRestrict U ω) := by
      funext ω m o
      simp only [hΦ, readOnBlock, dite_eq_left (hmem m o.1 o.2), gRestrict]
    have hinjΦ : Function.Injective Φ := by
      intro φ φ' h
      funext o
      obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 o.2
      have := congrFun (congrFun h m) ⟨o.1, hm⟩
      simpa only [hΦ, readOnBlock, dite_eq_left o.2] using this
    -- every tuple comes from a function on the union
    obtain ⟨φ, hφ⟩ : ∃ φ : U → Bool, Φ φ = ψ := by
      refine ⟨fun o => ψ (Finset.mem_biUnion.1 o.2).choose
        ⟨o.1, (Finset.mem_biUnion.1 o.2).choose_spec.2⟩, ?_⟩
      have key : ∀ (q : GObs Γ t) (m₁ m₂ : Fin n) (h₁ : q ∈ S m₁) (h₂ : q ∈ S m₂),
          ψ m₁ ⟨q, h₁⟩ = ψ m₂ ⟨q, h₂⟩ := by
        intro q m₁ m₂ h₁ h₂
        by_cases hmm : m₁ = m₂
        · subst hmm; rfl
        · exact absurd h₂ (Finset.disjoint_left.1 (disjoint_of_ai (hai m₁ m₂ hmm)) h₁)
      funext m p
      have hpU : p.1 ∈ U := hmem m p.1 p.2
      simp only [hΦ, readOnBlock, dite_eq_left hpU]
      exact key p.1 _ m (Finset.mem_biUnion.1 (⟨p.1, hpU⟩ : U).2).choose_spec.2 p.2
    rw [hfac, ← pushforward_comp' Δ (gRestrict U) Φ, ← hφ,
      pushforward_injective _ hinjΦ φ, hmain.2 φ]
    refine Finset.prod_congr rfl (fun m _ => ?_)
    rw [hinjm (S m) (hinj m)]

end RootSinkAux

open RootSinkAux

/-- AUDIT-NOTES A2, the consequence for the hierarchies: for pair-source scenarios, which are
root-sink scenarios, the recursively expressible hierarchy coincides with the
ancestral-independence hierarchy at every order. -/
theorem gExpFeasible_iff_gAIFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) :
    GExpFeasible Γ t P ↔ GAIFeasible Γ t P := by
  constructor
  · rintro ⟨Δ, hlaw, hsym, hdiag, hexp⟩
    exact ⟨Δ, hlaw, hsym, hdiag, fun S hS => hexp S _ (Expressible.inj hS),
      gAncestralProducts_of_exp hlaw hexp⟩
  · rintro ⟨Δ, hlaw, hsym, hdiag, hinjm, hprod⟩
    exact ⟨Δ, hlaw, hsym, hdiag, expPrescriptions_of_ai hlaw hinjm hprod⟩

/-- Local flips preserve the recursively expressible test, via `gExpFeasible_iff_gAIFeasible`
and `flip_gAIFeasible`. (This does not follow from the flip structure alone: flipping the
conditioning coordinates of a glue prescription does not commute with the conditional law;
the identification of the glue prescriptions with products of injectable marginals is what
makes it true.) -/
theorem flip_gExpFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) (η : ℝ) (h0 : 0 ≤ η)
    (h1 : η ≤ 1) (h : GExpFeasible Γ t P) : GExpFeasible Γ t (flipLaw η P) :=
  (gExpFeasible_iff_gAIFeasible Γ t (flipLaw η P)).2
    (flip_gAIFeasible Γ t P η h0 h1 ((gExpFeasible_iff_gAIFeasible Γ t P).1 h))

/-- A genuine model gives a witness satisfying every expressible prescription: run the
inflated model (`compatible_gAIFeasible`) and use the root-sink lemma. -/
theorem compatible_gExpFeasible (Γ : PairGraph) (t : ℕ) (P : GTarget Γ) (h : GCompatible Γ P) :
    GExpFeasible Γ t P :=
  (gExpFeasible_iff_gAIFeasible Γ t P).2 (compatible_gAIFeasible Γ t P h)


end TriangleInflation.Graph
