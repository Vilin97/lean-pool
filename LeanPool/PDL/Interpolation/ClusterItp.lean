/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

import LeanPool.PDL.Interpolation.PreInterpolant

/-! # The interpolant of a cluster root and its correctness

This file continues the development of `Pdl.PreInterpolant` with

* Definition 9.20: the interpolant `θ_r` of the root `r` of the cluster `C`, and
* Lemma 10.1: the vocabulary of the pre-interpolants.

Definition 10.2 and Lemma 10.3 are in `Pdl.ClusterRho`.
-/

namespace PDL

/-! ## Two small vocabulary lemmas -/

lemma Vocab.fromList_singleton (v : Vocab) : Vocab.fromList [v] = v := by
  simp [Vocab.fromList]

@[simp]
lemma Program.voc_steps : ∀ as : List Program, (Program.steps as).voc = as.pdlPvoc
  | [] => by simp [Vocab.fromList]
  | a :: as => by
      simp only [Program.steps, Program.voc, Program.voc_steps as, List.pdlPvoc, List.map_cons,
        Vocab.fromList, List.toFinset_cons, Finset.sup_insert, id_eq]
      rfl

/-! ## Entailment from the left component of a node -/

/-- `Λ₁(t) ⊨ φ`: the formula `φ` follows from the left component of the fine node `t`. -/
def FinePathIn.leftEntails {Hist} {Y : Sequent} {tab : Tableau Hist Y}
    (t : FinePathIn tab) (φ : Formula) : Prop :=
  ∀ (W : Type) (M : KripkeModel W) (w : W),
    (∀ ψ ∈ t.label.left, evaluate M w ψ) → evaluate M w φ


/-! ## The vocabulary of a Q-formula

The pre-interpolants of Definition 9.18 are `QFormula`s, i.e. they contain the internal
variables `q_x` as a separate constructor. Their vocabulary therefore splits into two
parts: the *ordinary* vocabulary `QFormula.voc`, made up of the proposition letters and
atomic programs occurring in the formula, and the internal variables `QFormula.vars`.
Lemma 10.1 below bounds the two parts separately, which is exactly the statement
`voc(ι_x) ⊆ (voc(Γ₁) ∩ voc(Γ₂)) ∪ { q_{c(z)} | z ∈ cycs(x) }` of the paper. -/

namespace QFormula

variable {Var : Type}

/-- The ordinary vocabulary of a Q-formula, i.e. the proposition letters and atomic
programs occurring in it. The internal variables are *not* included; they are given by
`QFormula.vars`. -/
def voc : QFormula Var → Vocab
  | .fma ψ => ψ.voc
  | .var _ => ∅
  | .and ι1 ι2 => ι1.voc ∪ ι2.voc
  | .boxes as ι => as.pdlPvoc ∪ ι.voc

@[simp] lemma voc_fma {ψ} : (fma ψ : QFormula Var).voc = ψ.voc := rfl
@[simp] lemma voc_var {q : Var} : (var q).voc = ∅ := rfl
@[simp] lemma voc_and {ι1 ι2 : QFormula Var} : (ι1.and ι2).voc = ι1.voc ∪ ι2.voc := rfl
@[simp] lemma voc_boxes {as} {ι : QFormula Var} : (ι.boxes as).voc = as.pdlPvoc ∪ ι.voc := rfl

@[simp] lemma vars_fma {ψ} : (fma ψ : QFormula Var).vars = [] := rfl
@[simp] lemma vars_var {q : Var} : (var q).vars = [q] := rfl
@[simp] lemma vars_and {ι1 ι2 : QFormula Var} : (ι1.and ι2).vars = ι1.vars ++ ι2.vars := rfl
@[simp] lemma vars_boxes {as} {ι : QFormula Var} : (ι.boxes as).vars = ι.vars := rfl

/-- Substituting formulas whose vocabulary is inside `V` for the internal variables
gives a formula whose vocabulary is inside `voc(ι) ∪ V`. -/
lemma voc_subst_subset {σ : Var → Formula} {V : Vocab} (hσ : ∀ q, (σ q).voc ⊆ V) :
    ∀ ι : QFormula Var, (ι.subst σ).voc ⊆ ι.voc ∪ V := by
  intro ι
  induction ι with
  | fma ψ => simp
  | var q => simpa using hσ q
  | and ι1 ι2 IH1 IH2 =>
      intro n hn
      simp only [subst_and, Formula.voc, Finset.mem_union, voc_and] at hn ⊢
      rcases hn with hn | hn
      · rcases Finset.mem_union.mp (IH1 hn) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · rcases Finset.mem_union.mp (IH2 hn) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
  | boxes as ι IH =>
      intro n hn
      simp only [subst_boxes, Formula.voc_boxes, Finset.mem_union, voc_boxes] at hn ⊢
      rcases hn with hn | hn
      · exact Or.inl (Or.inl hn)
      · rcases Finset.mem_union.mp (IH hn) with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- Substituting `⊤` for all internal variables does not add anything to the vocabulary. -/
lemma voc_subst_top (ι : QFormula Var) : (ι.subst (fun _ => ⊤)).voc ⊆ ι.voc := by
  have := voc_subst_subset (σ := fun _ : Var => (⊤ : Formula)) (V := ∅) (by simp) ι
  simpa using this

/-! ### The vocabulary of conjunctions, of `Spl` and of the fixpoint `gfp` -/

lemma voc_conj {n} : ∀ L : List (QFormula Var), n ∈ (conj L).voc → ∃ ι ∈ L, n ∈ ι.voc
  | [] => by simp [conj]
  | [ι] => by simp
  | ι1 :: ι2 :: L => by
      intro hn
      simp only [conj, voc_and, Finset.mem_union] at hn
      rcases hn with hn | hn
      · exact ⟨ι1, List.mem_cons_self .., hn⟩
      · obtain ⟨ι, hι, hn⟩ := voc_conj (ι2 :: L) hn
        exact ⟨ι, List.mem_cons_of_mem _ hι, hn⟩

lemma vars_conj {v} : ∀ L : List (QFormula Var), v ∈ (conj L).vars → ∃ ι ∈ L, v ∈ ι.vars
  | [] => by simp [conj]
  | [ι] => by simp
  | ι1 :: ι2 :: L => by
      intro hv
      simp only [conj, vars_and, List.mem_append] at hv
      rcases hv with hv | hv
      · exact ⟨ι1, List.mem_cons_self .., hv⟩
      · obtain ⟨ι, hι, hv⟩ := vars_conj (ι2 :: L) hv
        exact ⟨ι, List.mem_cons_of_mem _ hι, hv⟩

@[simp] lemma voc_toQ_prefixBoxes' (as : List Program) (s : QSimple Var) :
    (QSimple.prefixBoxes as s).toQ.voc = as.pdlPvoc ∪ s.toQ.voc := by
  cases s with
  | fma ψ => simp [QSimple.prefixBoxes, QSimple.toQ, Formula.voc_boxes]
  | boxVar bs q =>
      simp only [QSimple.prefixBoxes, QSimple.toQ, voc_boxes, voc_var, Finset.union_empty,
        List.pdlPvoc, List.map_append, Vocab.fromList, List.toFinset_append]
      exact Finset.sup_union

@[simp] lemma vars_toQ_prefixBoxes (as : List Program) (s : QSimple Var) :
    (QSimple.prefixBoxes as s).toQ.vars = s.toQ.vars := by
  cases s <;> rfl

/-- The ordinary vocabulary of the simple conjuncts of `ι` is inside that of `ι`. -/
lemma voc_of_mem_Spl : ∀ (ι : QFormula Var), ∀ s ∈ ι.Spl, s.toQ.voc ⊆ ι.voc := by
  intro ι
  induction ι with
  | fma ψ => intro s hs; simp only [Spl, List.mem_singleton] at hs; subst hs; simp [QSimple.toQ]
  | var q =>
      intro s hs
      simp only [Spl, List.mem_singleton] at hs
      subst hs
      simp [QSimple.toQ]
  | and ι1 ι2 IH1 IH2 =>
      intro s hs
      simp only [Spl, List.mem_append] at hs
      rcases hs with hs | hs
      · exact (IH1 s hs).trans Finset.subset_union_left
      · exact (IH2 s hs).trans Finset.subset_union_right
  | boxes as ι IH =>
      intro s hs
      simp only [Spl, List.mem_map] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [voc_toQ_prefixBoxes', voc_boxes]
      exact Finset.union_subset_union_right (IH t ht)

/-- The internal variables of the simple conjuncts of `ι` are variables of `ι`. -/
lemma vars_of_mem_Spl : ∀ (ι : QFormula Var), ∀ s ∈ ι.Spl, ∀ v ∈ s.toQ.vars, v ∈ ι.vars := by
  intro ι
  induction ι with
  | fma ψ => intro s hs; simp only [Spl, List.mem_singleton] at hs; subst hs; simp [QSimple.toQ]
  | var q =>
      intro s hs
      simp only [Spl, List.mem_singleton] at hs
      subst hs
      simp [QSimple.toQ, vars]
  | and ι1 ι2 IH1 IH2 =>
      intro s hs v hv
      simp only [Spl, List.mem_append] at hs
      rcases hs with hs | hs
      · exact List.mem_append_left _ (IH1 s hs v hv)
      · exact List.mem_append_right _ (IH2 s hs v hv)
  | boxes as ι IH =>
      intro s hs v hv
      simp only [Spl, List.mem_map] at hs
      obtain ⟨t, ht, rfl⟩ := hs
      rw [vars_toQ_prefixBoxes] at hv
      exact IH t ht v hv

variable [DecidableEq Var]

lemma voc_dropVar (x : Var) (ι : QFormula Var) : (ι.dropVar x).voc ⊆ ι.voc := by
  intro n hn
  obtain ⟨ρ, hρ, hn⟩ := voc_conj _ hn
  simp only [List.mem_map, List.mem_filter] at hρ
  obtain ⟨s, ⟨hs, -⟩, rfl⟩ := hρ
  exact voc_of_mem_Spl ι s hs hn

lemma vars_dropVar (x : Var) (ι : QFormula Var) : ∀ v ∈ (ι.dropVar x).vars, v ∈ ι.vars := by
  intro v hv
  obtain ⟨ρ, hρ, hv⟩ := vars_conj _ hv
  simp only [List.mem_map, List.mem_filter] at hρ
  obtain ⟨s, ⟨hs, -⟩, rfl⟩ := hρ
  exact vars_of_mem_Spl ι s hs v hv

lemma voc_unions : ∀ (L : List Program), ∀ n ∈ (Program.unions L).voc, ∃ α ∈ L, n ∈ α.voc
  | [] => by simp [Program.unions]
  | [α] => by intro n hn; exact ⟨α, by simp, hn⟩
  | α :: β :: L => by
      intro n hn
      simp only [Program.unions, Program.voc, Finset.mem_union] at hn
      rcases hn with hn | hn
      · exact ⟨α, List.mem_cons_self .., hn⟩
      · obtain ⟨γ, hγ, hn⟩ := voc_unions (β :: L) n hn
        exact ⟨γ, List.mem_cons_of_mem _ hγ, hn⟩

lemma voc_loopProgs (x : Var) (ι : QFormula Var) :
    ∀ α ∈ ι.loopProgs x, α.voc ⊆ ι.voc := by
  intro α hα
  simp only [loopProgs, List.mem_filterMap] at hα
  obtain ⟨s, hs, hα⟩ := hα
  cases s with
  | fma ψ => simp [QSimple.progToOpt] at hα
  | boxVar as q =>
      simp only [QSimple.progToOpt] at hα
      split at hα
      · cases hα
        have hsub := voc_of_mem_Spl ι _ hs
        simp only [QSimple.toQ, voc_boxes, voc_var, Finset.union_empty] at hsub
        rw [Program.voc_steps]
        exact hsub
      · simp at hα

/-- The fixpoint used at companion nodes does not add anything to the vocabulary. -/
lemma voc_gfp (x : Var) (ι : QFormula Var) : (ι.gfp x).voc ⊆ ι.voc := by
  intro n hn
  simp only [gfp, voc_boxes, Finset.mem_union] at hn
  rcases hn with hn | hn
  · rw [List.pdlPvoc, List.map_cons, List.map_nil, Vocab.fromList_singleton, Program.voc] at hn
    obtain ⟨α, hα, hn⟩ := voc_unions _ n hn
    exact voc_loopProgs x ι α hα hn
  · exact voc_dropVar x ι hn

/-- The fixpoint used at companion nodes does not add internal variables. -/
lemma vars_gfp (x : Var) (ι : QFormula Var) : ∀ v ∈ (ι.gfp x).vars, v ∈ ι.vars := by
  intro v hv
  simp only [gfp, vars_boxes] at hv
  exact vars_dropVar x ι v hv

end QFormula

/-! ## More facts about the nodes of a quasi-tableau -/

namespace QuasiTab

variable {q : QuasiTab} {x y z c : List Nat}

/-- The companion of a node is a proper ancestor of it. -/
lemma companionOpt_qlt (h : q.companionOpt x = some c) : qlt c x := by
  have hmem : c ∈ x.inits.dropLast := List.mem_of_find?_eq_some h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hlen : i < x.length := by
    rw [List.length_dropLast, List.length_inits] at hi
    omega
  rw [List.getElem_dropLast, List.getElem_inits]
  refine ⟨List.take_prefix _ _, ?_⟩
  intro hcon
  have := congrArg List.length hcon
  rw [List.length_take] at this
  omega

/-- A repeat leaf is one of its own cycles. -/
lemma mem_cycs_self (h : q.isRepeatLeaf x) : x ∈ q.cycs x := by
  rw [mem_cycs_iff]
  refine ⟨List.mem_filter.mpr ⟨?_, h⟩, ?_⟩
  · simp only [isRepeatLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
    exact List.mem_filter.mpr ⟨mem_addresses_of_atOpt q x (isSome_atOpt_of_isLeafAt h.1.1),
      h.1.1⟩
  · simp only [isRepeatLeaf, Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨c, hc⟩ := h.2
    exact ⟨c, hc, companionOpt_qlt hc, List.prefix_refl x⟩

/-- A generalisation of `QuasiTab.cycs_subset_of_qedge`: a cycle of a child `y` of `x` is a
cycle of `x`, unless its companion is `x` itself. -/
lemma mem_cycs_of_qedge_of_companion_ne (hxy : q.qedge x y) (hz : z ∈ q.cycs y)
    (hne : q.companionOpt z ≠ some x) : z ∈ q.cycs x := by
  rw [mem_cycs_iff] at hz ⊢
  obtain ⟨z_in, c, hc, ⟨hcy, hcy'⟩, hyz⟩ := hz
  obtain ⟨i, rfl⟩ : ∃ i, x ++ [i] = y := by
    simp only [qedge, childrenAt] at hxy
    cases h : q.atOpt x with
    | none => rw [h] at hxy; simp at hxy
    | some n =>
      rw [h] at hxy
      simp only [List.mem_map, List.mem_range] at hxy
      obtain ⟨i, -, rfl⟩ := hxy
      exact ⟨i, rfl⟩
  refine ⟨z_in, c, hc, ⟨?_, ?_⟩, (List.prefix_append x [i]).trans hyz⟩
  · rcases (List.prefix_concat_iff.mp hcy) with h | h
    · exact absurd h hcy'
    · exact h
  · rintro rfl
    exact hne hc

/-- The node at address `x` is a leaf of type 1 when it is `QNode one Δ []`. -/
lemma isLeafAt_of_atOpt {Δ k} (h : q.atOpt x = some (.QNode k Δ [])) : q.isLeafAt x := by
  simp [isLeafAt, h, children]

lemma typAt_of_atOpt {n} (h : q.atOpt x = some n) : q.typAt x = some n.typ := by
  simp [typAt, h]

/-- Going to the child with index `i`, at the level of addresses. -/
lemma atOpt_child {Δ k next i} (h : q.atOpt x = some (.QNode k Δ next)) (hi : i < next.length) :
    q.atOpt (x ++ [i]) = some next[i] := by
  rw [atOpt_snoc, h]
  simp [children, List.getElem?_eq_getElem hi]

lemma qedge_snoc {Δ k next i} (h : q.atOpt x = some (.QNode k Δ next)) (hi : i < next.length) :
    q.qedge x (x ++ [i]) := by
  simp only [qedge, childrenAt, h, List.mem_map, List.mem_range, children]
  exact ⟨i, hi, rfl⟩

end QuasiTab

/-! ## Two more unfolding lemmas for Definition 9.18

These are the two cases where the data type allows a node without children although the
definition of the quasi-tableau provides one; see Remark 9.9. -/

namespace QuasiTab

variable {q : QuasiTab} {θ : Sequent → Formula}

lemma iitpAt_two_leaf {Δ x} : iitpAt q θ (.QNode .two Δ []) x = .fma ⊤ := by rw [iitpAt]

lemma iitpAt_three_basic_leaf {Δ x} (h : Δ.basic) :
    iitpAt q θ (.QNode .three Δ []) x = .fma ⊤ := by rw [iitpAt]; simp [h]

end QuasiTab

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}
  {θ : FinePathIn tab → Formula} {x : List Nat}

lemma iitp_two_leaf {Δ} (h : C.Q.atOpt x = some (.QNode .two Δ [])) :
    C.iitp θ x = .fma ⊤ := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_two_leaf]

lemma iitp_three_basic_leaf {Δ} (h : C.Q.atOpt x = some (.QNode .three Δ []))
    (hb : Δ.basic) : C.iitp θ x = .fma ⊤ := by
  rw [iitp_of_atOpt h, QuasiTab.iitpAt_three_basic_leaf hb]

/-! ## Definition 9.20: the interpolant of the root of the cluster -/

/-- Def 9.20: the interpolant `θ_r` of the root `r` of the cluster `C`.

If the left component `Γ₁` of the root is empty then `θ_r := ⊤` (see Remark 9.19),
and otherwise `θ_r` is the pre-interpolant `ι_{r_Q}` of the root of the quasi-tableau.
The latter is a `QFormula`, i.e. it may still contain internal variables; by Lemma 10.1
(`iitp_vars`) it does not, so it does not matter which substitution we use to read it as a
`Formula`, and we simply substitute `⊤`. -/
noncomputable def itp (C : LoadedCluster tab) (θ : FinePathIn tab → Formula) : Formula :=
  if (nodeAt C.root).left = {} then ⊤ else (C.rootIitp θ).subst (fun _ => ⊤)

/-! ## Cluster facts used to construct interpolants -/

/-- Facts about the cluster `C` used in the interpolant construction.
`LoadedCluster.paperFacts` in `ClusterInterpolation` proves these from tableau uniformity
and cluster properness. Collecting them here keeps those later proofs separate from the
construction.

* `exists_right` is Lemma 9.7 (d): if `C_Δ` is non-empty then so is `C^R_Δ`.
* `vocL` and `vocR` are instances of the fact that the vocabulary of both components only
  shrinks along a tableau; here applied to the nodes of `C⁺`, all of which are below the
  root `r` of the cluster.
* `loadedProgVoc` says that the leading atomic program `a` of the loaded formula of a
  basic `Δ ∈ Λ₂[C]` is in the joint vocabulary of the root. That `a ∈ voc(Γ₂)` is again
  vocabulary preservation. That `a ∈ voc(Γ₁)` — which the paper does not mention, but
  which its Lemma 10.1 needs — holds when `Γ₁ ≠ ∅` because by Lemma 9.7 (e) the modal rule
  is applied at some `t ∈ C^R_Δ` and its child `u` is again in `C`, so that
  `Λ₁(u) = (Λ₁(t))_a` is non-empty by Lemma 9.5 (b), which forces a box `⌈a⌉ψ` in `Λ₁(t)`.
  Note that for `Γ₁ = ∅` the claim is false, which is why Definition 9.20 treats that case
  separately. -/
structure PaperFacts (C : LoadedCluster tab) : Prop where
  /-- Lemma 9.7 (d): if `C_Δ ≠ ∅` then `C^R_Δ ≠ ∅`. -/
  exists_right : ∀ Δ ∈ C.lambdaTwo, C.nodesWithFineRight Δ ≠ []
  /-- The vocabulary of the left component only shrinks below the root of the cluster. -/
  vocL : ∀ f ∈ C.fineCLplus, f.label.left.pdlFvoc ⊆ (nodeAt C.root).left.pdlFvoc
  /-- The vocabulary of the right component only shrinks below the root of the cluster. -/
  vocR : ∀ f ∈ C.fineCLplus, f.label.right.pdlFvoc ⊆ (nodeAt C.root).right.pdlFvoc
  /-- The leading atomic program of a basic label of `Λ₂[C]` is in the joint vocabulary. -/
  loadedProgVoc : (nodeAt C.root).left ≠ {} → ∀ Δ ∈ C.lambdaTwo, Δ.basic →
    (Δ.loadedProg).voc ⊆ jvoc (nodeAt C.root)
  /-- The conclusion of the inner induction in the proof of Lemma 10.3: if a formula
  follows from the left component of every node of `C^R_Δ` and of every exit node with
  right component `Δ`, then it follows from the left component of every node of `C⁺_Δ`.
  This packages Lemma 9.7 (a) — every node of `C_Δ` is in `C^L_Δ` or in `C^R_Δ` — with the
  local invertibility of the rules applied at the nodes of `C^L_Δ`. -/
  leftPropagation : ∀ Δ ∈ C.lambdaTwo, ∀ φ : Formula,
    (∀ u ∈ C.nodesWithFineRight Δ, u.leftEntails φ) →
    (∀ u ∈ C.exitsWithFine Δ, u.leftEntails φ) →
    ∀ t ∈ C.plusNodesWithFine Δ, t.leftEntails φ
  /-- For a non-basic `Δ ∈ Λ₂[C]` and every `t ∈ C^R_Δ`, the children of `t` in the
  tableau are the nodes `Λ₁(t);Π` for `Π ∈ stepOf Δ`, and they are in `C⁺_Π`.
  We only record what is used in the proof of Lemma 10.3: the existence of a node of
  `C⁺_Π` with the same left component as `t`. -/
  rightRuleChildren : ∀ Δ ∈ C.lambdaTwo, ¬ Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
    ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi, u.label.left = t.label.left
  /-- For a basic `Δ ∈ Λ₂[C]` the modal rule is applied at every `t ∈ C^R_Δ`, and its
  unique child `u` is in `C` and satisfies `Λ₁(u) = (Λ₁(t))_a` where `a` is the leading
  atomic program of the loaded formula of `Δ`. We only record the semantic consequence
  used in the proof of Lemma 10.3: from `Λ₁(t)` at a state `w` we get `Λ₁(u)` at every
  `a`-successor of `w`. -/
  modalStep : ∀ Δ ∈ C.lambdaTwo, Δ.basic → ∀ t ∈ C.nodesWithFineRight Δ,
    ∀ Pi ∈ C.stepOf Δ, ∃ u ∈ C.plusNodesWithFine Pi,
      ∀ (W : Type) (M : KripkeModel W) (w v : W), (∀ ψ ∈ t.label.left, evaluate M w ψ) →
        relate M Δ.loadedProg w v → ∀ ψ ∈ u.label.left, evaluate M v ψ

/-- The vocabulary of `θ_Δ` is inside the joint vocabulary of the root of the cluster.
This is Lemma 9.14 (c) together with vocabulary preservation. -/
lemma thetaOf_voc_sub_jvoc (C : LoadedCluster tab) (hF : C.PaperFacts)
    (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) (Δ : Sequent) :
    (C.thetaOf θ Δ).voc ⊆ jvoc (nodeAt C.root) := by
  intro n hn
  have hsub := C.thetaOf_voc θ hθ Δ hn
  rw [Finset.mem_inter] at hsub
  obtain ⟨hn1, hn2⟩ := hsub
  simp only [Vocab.fromFinset, Finset.pdlFvoc, Finset.sup_image, Function.id_comp,
    Finset.mem_sup] at hn1
  obtain ⟨f, hf, hn1⟩ := hn1
  have hfE : f ∈ C.fineExits := ((C.mem_exitsWithFine_iff Δ f).mp hf).1
  have hfP : f ∈ C.fineCLplus := Finset.mem_union_right _ hfE
  rw [jvoc, Finset.mem_inter]
  refine ⟨hF.vocL f hfP (by
    simpa only [Finset.pdlFvoc, Vocab.fromFinset, Finset.sup_image, Function.id_comp,
      Finset.mem_sup] using hn1), hF.vocR f hfP ?_⟩
  rw [C.right_of_mem_exitsWithFine hf]
  exact hn2

end LoadedCluster

/-! ## Lemma 10.1: the vocabulary of the pre-interpolants -/

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}
  {θ : FinePathIn tab → Formula} {x : List Nat}

/-- The conjuncts in the case `k(x) = 3` with `Δ_x` not basic are the pre-interpolants of
the children of `x`. -/
lemma mem_iitpList {Δ next} (h : C.Q.atOpt x = some (.QNode .three Δ next))
    {ι : QFormula (List Nat)} (hι : ι ∈ QuasiTab.iitpList C.Q (C.thetaOf θ) next x 0) :
    ∃ i, ∃ _ : i < next.length, ι = C.iitp θ (x ++ [i]) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hι
  rw [QuasiTab.length_iitpList] at hi
  exact ⟨i, hi, C.iitpList_getElem_eq_iitp h hi⟩

/-- Lemma 10.1: the vocabulary of the pre-interpolant of a node `x` of the quasi-tableau
consists of the joint vocabulary of the root of the cluster and of internal variables
`q_{c(z)}` for cycles `z ∈ cycs(x)`.

Here the two parts are stated separately: `voc(ι_x) ⊆ voc(Γ₁) ∩ voc(Γ₂)` for the ordinary
vocabulary, and the internal variables of `ι_x` are companions of elements of `cycs(x)`.

The hypothesis `Γ₁ ≠ ∅` is needed: for `Γ₁ = ∅` the claim would say that `ι_x` has no
ordinary vocabulary at all, which fails at nodes of type 3 with a basic label. Definition
9.20 covers that case separately, see Remark 9.19. -/
theorem iitp_voc_aux (C : LoadedCluster tab) (hF : C.PaperFacts)
    (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hΓ₁ : (nodeAt C.root).left ≠ {}) :
    ∀ (m : Nat) (n : QuasiTab), sizeOf n ≤ m → ∀ x, C.Q.atOpt x = some n →
      (C.iitp θ x).voc ⊆ jvoc (nodeAt C.root) ∧
      ∀ v ∈ (C.iitp θ x).vars, ∃ z ∈ C.Q.cycs x, C.Q.companionOpt z = some v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
  rintro ⟨k, Δ, next⟩ hn x hx
  -- the induction hypothesis for the child with index `i`
  have IHchild : ∀ i, ∀ hi : i < next.length,
      (C.iitp θ (x ++ [i])).voc ⊆ jvoc (nodeAt C.root) ∧
      ∀ v ∈ (C.iitp θ (x ++ [i])).vars, ∃ z ∈ C.Q.cycs (x ++ [i]),
        C.Q.companionOpt z = some v := by
    intro i hi
    have hlt : sizeOf next[i] < sizeOf (QuasiTab.QNode k Δ next) := by
      have h1 : sizeOf next[i] < sizeOf next := List.sizeOf_lt_of_mem (List.getElem_mem hi)
      simp only [QuasiTab.QNode.sizeOf_spec]
      omega
    exact IH (sizeOf next[i]) (lt_of_lt_of_le hlt hn) next[i] le_rfl _
      (QuasiTab.atOpt_child hx hi)
  cases k with
  | one =>
    cases next with
    | nil =>
      cases hc : C.Q.companionOpt x with
      | some c =>
        rw [C.iitp_one_leaf_repeat hx hc]
        refine ⟨by simp, ?_⟩
        intro v hv
        simp only [QFormula.vars_var, List.mem_singleton] at hv
        subst hv
        refine ⟨x, QuasiTab.mem_cycs_self ?_, hc⟩
        simp only [QuasiTab.isRepeatLeaf, Bool.and_eq_true, decide_eq_true_eq,
          QuasiTab.isLeafAt_of_atOpt hx, QuasiTab.typAt_of_atOpt hx, hc, Option.isSome_some,
          true_and]
        exact ⟨rfl, trivial⟩
      | none =>
        rw [C.iitp_one_leaf_exit hx hc]
        exact ⟨by simpa using C.thetaOf_voc_sub_jvoc hF θ hθ Δ, by simp⟩
    | cons y ys =>
      obtain ⟨IHvoc, IHvars⟩ := IHchild 0 (by simp)
      have hqedge : C.Q.qedge x (x ++ [0]) := QuasiTab.qedge_snoc hx (by simp)
      by_cases hcomp : x ∈ C.Q.companions
      · rw [C.iitp_one_companion hx hcomp]
        refine ⟨(QFormula.voc_gfp _ _).trans IHvoc, ?_⟩
        intro v hv
        have hvne : v ≠ x := by rintro rfl; exact QFormula.not_mem_vars_gfp _ _ hv
        obtain ⟨z, hz, hcz⟩ := IHvars v (QFormula.vars_gfp _ _ v hv)
        exact ⟨z, QuasiTab.mem_cycs_of_qedge_of_companion_ne hqedge hz
          (by rw [hcz]; simpa using hvne), hcz⟩
      · rw [C.iitp_one_inner hx hcomp]
        refine ⟨IHvoc, ?_⟩
        intro v hv
        obtain ⟨z, hz, hcz⟩ := IHvars v hv
        exact ⟨z, C.Q.cycs_subset_of_qedge hcomp hqedge z hz, hcz⟩
  | two =>
    have hnc : x ∉ C.Q.companions := by
      intro hmem
      have h1 := C.Q.typAt_of_mem_companions hmem
      rw [QuasiTab.typAt_of_atOpt hx] at h1
      simp [QuasiTab.typ] at h1
    cases next with
    | nil => rw [C.iitp_two_leaf hx]; exact ⟨by simp, by simp⟩
    | cons y ys =>
      obtain ⟨IHvoc, IHvars⟩ := IHchild 0 (by simp)
      have hqedge : C.Q.qedge x (x ++ [0]) := QuasiTab.qedge_snoc hx (by simp)
      rw [C.iitp_two hx]
      constructor
      · intro n hnv
        simp only [QFormula.voc_boxes, Finset.mem_union] at hnv
        rcases hnv with hnv | hnv
        · rw [List.pdlPvoc, List.map_cons, List.map_nil, Vocab.fromList_singleton,
            Program.voc, Formula.voc] at hnv
          exact C.thetaOf_voc_sub_jvoc hF θ hθ Δ hnv
        · exact IHvoc hnv
      · intro v hv
        simp only [QFormula.vars_boxes] at hv
        obtain ⟨z, hz, hcz⟩ := IHvars v hv
        exact ⟨z, C.Q.cycs_subset_of_qedge hnc hqedge z hz, hcz⟩
  | three =>
    have hnc : x ∉ C.Q.companions := by
      intro hmem
      have h1 := C.Q.typAt_of_mem_companions hmem
      rw [QuasiTab.typAt_of_atOpt hx] at h1
      simp [QuasiTab.typ] at h1
    by_cases hb : Δ.basic
    · cases next with
      | nil => rw [C.iitp_three_basic_leaf hx hb]; exact ⟨by simp, by simp⟩
      | cons y ys =>
        obtain ⟨IHvoc, IHvars⟩ := IHchild 0 (by simp)
        have hqedge : C.Q.qedge x (x ++ [0]) := QuasiTab.qedge_snoc hx (by simp)
        have hΔ : Δ ∈ C.lambdaTwo :=
          C.Q_inner_label_mem_lambdaTwo _ (QuasiTab.mem_subtrees_of_atOpt hx)
            (by simp [QuasiTab.children])
        rw [C.iitp_three_basic hx hb]
        constructor
        · intro n hnv
          simp only [QFormula.voc_boxes, Finset.mem_union] at hnv
          rcases hnv with hnv | hnv
          · rw [List.pdlPvoc, List.map_cons, List.map_nil, Vocab.fromList_singleton] at hnv
            exact hF.loadedProgVoc hΓ₁ Δ hΔ hb hnv
          · exact IHvoc hnv
        · intro v hv
          simp only [QFormula.vars_boxes] at hv
          obtain ⟨z, hz, hcz⟩ := IHvars v hv
          exact ⟨z, C.Q.cycs_subset_of_qedge hnc hqedge z hz, hcz⟩
    · rw [C.iitp_three_not_basic hx hb]
      constructor
      · intro n hnv
        obtain ⟨ι, hι, hnv⟩ := QFormula.voc_conj _ hnv
        obtain ⟨i, hi, rfl⟩ := C.mem_iitpList hx hι
        exact (IHchild i hi).1 hnv
      · intro v hv
        obtain ⟨ι, hι, hv⟩ := QFormula.vars_conj _ hv
        obtain ⟨i, hi, rfl⟩ := C.mem_iitpList hx hι
        obtain ⟨z, hz, hcz⟩ := (IHchild i hi).2 v hv
        exact ⟨z, C.Q.cycs_subset_of_qedge hnc (QuasiTab.qedge_snoc hx hi) z hz, hcz⟩


/-- Lemma 10.1, first part: for every node `x` of the quasi-tableau, the ordinary
vocabulary of the pre-interpolant `ι_x` is inside `voc(Γ₁) ∩ voc(Γ₂)`.
See `LoadedCluster.iitp_voc_aux` for the hypothesis `Γ₁ ≠ ∅`. -/
theorem iitp_voc (C : LoadedCluster tab) (hF : C.PaperFacts) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hΓ₁ : (nodeAt C.root).left ≠ {}) (x : List Nat) :
    (C.iitp θ x).voc ⊆ jvoc (nodeAt C.root) := by
  cases hx : C.Q.atOpt x with
  | none => rw [iitp, hx]; simp
  | some n => exact (C.iitp_voc_aux hF θ hθ hΓ₁ (sizeOf n) n le_rfl x hx).1

/-- Lemma 10.1, second part: the internal variables occurring in the pre-interpolant `ι_x`
are the companions `q_{c(z)}` of cycles `z ∈ cycs(x)`. -/
theorem iitp_vars (C : LoadedCluster tab) (hF : C.PaperFacts) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hΓ₁ : (nodeAt C.root).left ≠ {}) (x : List Nat) :
    ∀ v ∈ (C.iitp θ x).vars, ∃ z ∈ C.Q.cycs x, C.Q.companionOpt z = some v := by
  cases hx : C.Q.atOpt x with
  | none => rw [iitp, hx]; simp
  | some n => exact (C.iitp_voc_aux hF θ hθ hΓ₁ (sizeOf n) n le_rfl x hx).2

/-- The pre-interpolant of the root of the quasi-tableau contains no internal variables,
because `cycs(r_Q) = ∅` (Lemma 9.12 (b)). -/
theorem rootIitp_vars (C : LoadedCluster tab) (hF : C.PaperFacts) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f))
    (hΓ₁ : (nodeAt C.root).left ≠ {}) : (C.rootIitp θ).vars = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro v hv
  obtain ⟨z, hz, -⟩ := C.iitp_vars hF θ hθ hΓ₁ QuasiTab.rootAddress v hv
  rw [C.Q.cycs_root] at hz
  simp at hz

/-- Lemma 10.1, the corollary: the interpolant of the root of the cluster only uses the
joint vocabulary of `Γ₁` and `Γ₂`. -/
theorem itp_voc (C : LoadedCluster tab) (hF : C.PaperFacts) (θ : FinePathIn tab → Formula)
    (hθ : ∀ f ∈ C.fineExits, isPartInterpolant f.label (θ f)) :
    (C.itp θ).voc ⊆ jvoc (nodeAt C.root) := by
  rw [itp]
  split
  case isTrue => simp
  case isFalse hΓ₁ =>
    exact (QFormula.voc_subst_top _).trans (C.iitp_voc hF θ hθ hΓ₁ QuasiTab.rootAddress)

end LoadedCluster

end PDL
