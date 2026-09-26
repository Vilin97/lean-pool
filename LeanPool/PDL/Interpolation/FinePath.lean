/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Flip
public import LeanPool.PDL.KeepRight

/-! # Fine paths in local tableaux and in tableaux

This file collects helper definitions and lemmas that are used in `Pdl.InterpolationCluster`
to define interpolants for proper clusters (Section 9 of the paper).

The two main definitions are `LocalPathIn`, for paths to arbitrary (also intermediate) nodes
of a `LocalTableau`, and `FinePathIn`, for the nodes of a whole `Tableau` in the *fine* sense,
i.e. including those nodes inside a local tableau that a `loc` step jumps over.
-/

public section

namespace PDL

/-! ## Paths inside a local tableau

The `Tableau` type applies a whole `LocalTableau` in one `loc` step, and thus the `PathIn`
type — and with it the `edge` relation `⋖_` and the clusters defined via `◃` — "jumps over"
the intermediate nodes inside a local tableau. For the quasi-tableau in Definition 9.8 we
need those intermediate nodes, because it is only there that each rule application is
either a left or a right rule.

We therefore first define `LocalPathIn`, the analogue of `PathIn` for local tableaux, in
the same spirit as `LocalTableau.paths` which is used for the completeness proof.
Note that in contrast to `LocalTableau.paths` we here keep the nodes themselves and not
only the sequents labelling them, so that we can still connect them to `PathIn`. -/

/-- A path inside a `LocalTableau`, pointing at an arbitrary node of it — in contrast to
`LocalTableau.paths` which only goes to the end nodes. -/
inductive LocalPathIn : {X : Sequent} → LocalTableau X → Type
  | nil {X} {lt : LocalTableau X} : LocalPathIn lt
  | cons {X} {lra : LocalRuleApp} {X_def : X = lra.X} {next} {Y} (Y_in : Y ∈ lra.C)
      (tail : LocalPathIn (next Y Y_in)) : LocalPathIn (LocalTableau.byLocalRule lra X_def next)
deriving DecidableEq

/-- The sequent at the node a local path is pointing at. -/
@[expose] def LocalPathIn.last {X} {lt : LocalTableau X} : LocalPathIn lt → Sequent
  | .nil => X
  | .cons _ tail => tail.last

/-- The local tableau rooted at the node a local path is pointing at. -/
def LocalPathIn.ltAt {X} {lt : LocalTableau X} : (lp : LocalPathIn lt) → LocalTableau lp.last
  | .nil => lt
  | .cons _ tail => tail.ltAt

/-- Is this the empty local path, i.e. does it point at the root of the local tableau? -/
def LocalPathIn.isNilB {X} {lt : LocalTableau X} : LocalPathIn lt → Bool
  | .nil => true
  | .cons _ _ => false

/-- Is a local rule applied at the root of this local tableau? -/
@[expose] def LocalTableau.hasRule {X} : LocalTableau X → Prop
  | .byLocalRule .. => True
  | .sim _ => False

instance LocalTableau.instDecidableHasRule {X} (lt : LocalTableau X) : Decidable lt.hasRule := by
  cases lt <;> simp only [hasRule] <;> infer_instance

/-- A local path is *internal* iff a local rule is applied at the node it points at,
i.e. iff that node is not a leaf of the local tableau. -/
@[expose] def LocalPathIn.isInternal {X} {lt : LocalTableau X} (lp : LocalPathIn lt) : Prop :=
  lp.ltAt.hasRule

instance LocalPathIn.instDecidableIsInternal {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    Decidable lp.isInternal := by
  unfold LocalPathIn.isInternal; infer_instance

/-- If the local path points at a leaf then this gives the end node it reaches. -/
def LocalPathIn.endNodeAtOpt {X} {lt : LocalTableau X} :
    (lp : LocalPathIn lt) → Option {Y : Sequent // Y ∈ endNodesOf lt}
  | .nil => match lt with
    | .byLocalRule _ _ _ => none
    | .sim _ => some ⟨X, by simp⟩
  | .cons Y_in tail => (tail.endNodeAtOpt).map
      (fun ⟨Z, hZ⟩ => ⟨Z, mem_endNodesOf_byLocalRule_iff.mpr ⟨_, Y_in, hZ⟩⟩)

lemma LocalPathIn.isInternal_iff_endNodeAtOpt_eq_none {X} {lt : LocalTableau X}
    (lp : LocalPathIn lt) : lp.isInternal ↔ lp.endNodeAtOpt = none := by
  induction lp
  case nil X lt =>
    cases lt <;> simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule,
      LocalPathIn.endNodeAtOpt]
  case cons IH =>
    simpa [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalPathIn.endNodeAtOpt] using! IH

lemma LocalPathIn.last_of_endNodeAtOpt {X} {lt : LocalTableau X} (lp : LocalPathIn lt)
    {Yh : {Y : Sequent // Y ∈ endNodesOf lt}} (h : lp.endNodeAtOpt = some Yh) :
    lp.last = Yh.val := by
  induction lp
  case nil X lt =>
    cases lt
    · simp [LocalPathIn.endNodeAtOpt] at h
    · simp only [LocalPathIn.endNodeAtOpt, Option.some.injEq] at h
      subst h
      rfl
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [LocalPathIn.endNodeAtOpt, Option.map_eq_some_iff] at h
    obtain ⟨Zh, hZ, rfl⟩ := h
    simpa [LocalPathIn.last] using IH hZ

/-- The children of the node a local path points at, inside the same local tableau. -/
def LocalPathIn.children {X} {lt : LocalTableau X} :
    LocalPathIn lt → Finset (LocalPathIn lt)
  | .nil => match lt with
    | .byLocalRule lra _ _ => lra.C.attach.image (fun ⟨_, Y_in⟩ => .cons Y_in .nil)
    | .sim _ => {}
  | .cons Y_in tail => tail.children.image (.cons Y_in)

/-- The sequents labelling the children of the root of a local tableau. -/
@[expose] def LocalTableau.childLabels {X} : LocalTableau X → Finset Sequent
  | .byLocalRule lra _ _ => lra.C
  | .sim _ => {}

lemma LocalPathIn.map_last_children {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    lp.children.image LocalPathIn.last = lp.ltAt.childLabels := by
  induction lp
  case nil X lt =>
    cases lt
    · subst_eqs
      simp only [LocalRuleApp.X, children, LocalTableau.childLabels, ltAt]
      rw [Finset.image_image]
      exact Finset.attach_image_val
    · simp [LocalPathIn.children, LocalPathIn.ltAt, LocalTableau.childLabels]
  case cons X lra X_def next Y Y_in tail IH =>
    rw [LocalPathIn.children, Finset.image_image]
    exact IH

/-- The end nodes of the whole local tableau that are below a given local path. -/
@[expose] def LocalPathIn.endNodesBelow {X} {lt : LocalTableau X} :
    (lp : LocalPathIn lt) → List {Y : Sequent // Y ∈ endNodesOf lt}
  | .nil => (endNodesOf lt).pdlSeqSort.attach.map
      (fun ⟨Z, hZ⟩ => ⟨Z, (Finset.mem_seqSort _).mp hZ⟩)
  | .cons Y_in tail => tail.endNodesBelow.map
      (fun ⟨Z, hZ⟩ => ⟨Z, mem_endNodesOf_byLocalRule_iff.mpr ⟨_, Y_in, hZ⟩⟩)

/-- A leaf of a local tableau is the only end node below itself. -/
lemma LocalPathIn.endNodesBelow_eq_of_endNodeAtOpt : {X : Sequent} → {lt : LocalTableau X} →
    (lp : LocalPathIn lt) → {Yh : {Y : Sequent // Y ∈ endNodesOf lt}} →
      lp.endNodeAtOpt = some Yh → ∀ Yh' ∈ lp.endNodesBelow, Yh' = Yh
  | _, .byLocalRule .., .nil, _, h, _, _ => by simp [LocalPathIn.endNodeAtOpt] at h
  | _, .sim _, .nil, _, h, Yh', _ => by
      simp only [LocalPathIn.endNodeAtOpt, Option.some.injEq] at h
      subst h
      have := Yh'.2
      simp only [endNodesOf, Finset.mem_singleton] at this
      exact Subtype.ext this
  | _, .byLocalRule lra X_def next, .cons Y_in tail, _, h, Yh', h' => by
      simp only [LocalPathIn.endNodeAtOpt, Option.map_eq_some_iff] at h
      obtain ⟨Zh, hZ, rfl⟩ := h
      simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at h'
      obtain ⟨W, hW, hW', rfl⟩ := h'
      have := LocalPathIn.endNodesBelow_eq_of_endNodeAtOpt tail hZ ⟨W, hW⟩ hW'
      simp only [Subtype.mk.injEq]
      exact congrArg Subtype.val this

/-- If an end node is below an internal node of a local tableau, then it is below one of
the children of that node. -/
lemma LocalPathIn.exists_child_endNodesBelow : {X : Sequent} → {lt : LocalTableau X} →
    (lp : LocalPathIn lt) → lp.isInternal → ∀ Yh ∈ lp.endNodesBelow,
      ∃ c ∈ lp.children, Yh ∈ c.endNodesBelow
  | _, .sim _, .nil, h, _, _ => by
      simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule] at h
  | _, .byLocalRule lra X_def next, .nil, _, ⟨Z, hZ⟩, _ => by
      obtain ⟨Y, Y_in, hZ'⟩ := mem_endNodesOf_byLocalRule_iff.mp hZ
      refine ⟨.cons Y_in .nil, ?_, ?_⟩
      · simp only [children, Finset.mem_image, Finset.mem_attach, cons.injEq, true_and,
        Subtype.exists, exists_and_left, exists_eq_left, heq_eq_eq, exists_prop, and_true]
        exact Y_in
      · simp only [LocalPathIn.endNodesBelow]
        rw [List.mem_map]
        simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Finset.mem_seqSort,
          exists_subtype_mk_eq_iff, exists_eq, endNodesOf]
        exact ⟨Z, hZ', rfl⟩
  | _, .byLocalRule lra X_def next, .cons Y_in tail, h, Yh, hYh => by
      simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists] at hYh
      obtain ⟨Z, hZ, hZ', rfl⟩ := hYh
      obtain ⟨c, c_in, hc⟩ := LocalPathIn.exists_child_endNodesBelow tail h ⟨Z, hZ⟩ hZ'
      refine ⟨.cons Y_in c, ?_, ?_⟩
      · simp only [children, Finset.mem_image, cons.injEq, heq_eq_eq, true_and, exists_eq_right]
        exact c_in
      · simp only [LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists]
        exact ⟨Z, hZ, hc, rfl⟩

/-- All internal nodes of a local tableau, i.e. those where a local rule is applied.
Compare `allPaths` for `PathIn`. -/
def internalLocalPaths : {X : Sequent} → (lt : LocalTableau X) →
    List (LocalPathIn lt)
  | _, .sim _ => []
  | _, .byLocalRule lra _ next => .nil ::
      lra.C.pdlSeqSort.attach.flatMap (fun ⟨Y, Y_in⟩ =>
        (internalLocalPaths (next Y ((Finset.mem_seqSort _).mp Y_in))).map
          (LocalPathIn.cons ((Finset.mem_seqSort _).mp Y_in)))

lemma internalLocalPaths_isInternal : {X : Sequent} → {lt : LocalTableau X} →
    ∀ lp ∈ internalLocalPaths lt, LocalPathIn.isInternal lp
  | _, .sim _, lp, h => by simp [internalLocalPaths] at h
  | _, .byLocalRule lra X_def next, lp, h => by
      simp only [internalLocalPaths, List.mem_cons, List.mem_flatMap, List.mem_attach, List.mem_map,
        true_and, Subtype.exists, Finset.mem_seqSort] at h
      rcases h with rfl | ⟨Y, Y_in, lp', lp'_in, rfl⟩
      · simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule]
      · have := internalLocalPaths_isInternal lp' lp'_in
        simpa [LocalPathIn.isInternal, LocalPathIn.ltAt] using! this

lemma LocalPathIn.mem_internalLocalPaths {X} {lt : LocalTableau X} (lp : LocalPathIn lt)
    (h : lp.isInternal) : lp ∈ internalLocalPaths lt := by
  induction lp
  case nil X lt =>
    cases lt
    · simp [internalLocalPaths]
    · simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule] at h
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [internalLocalPaths, List.mem_cons, reduceCtorEq, List.mem_flatMap, List.mem_attach,
      List.mem_map, cons.injEq, true_and, Subtype.exists, Finset.mem_seqSort, false_or]
    exact ⟨Y, Y_in, tail, IH (by simpa [LocalPathIn.isInternal, LocalPathIn.ltAt] using! h),
      rfl, by grind⟩

/-! ## Fine paths: all nodes of a tableau

A `FinePathIn` points at a node of the tableau in the *fine* sense: it may also point at
an intermediate node inside a local tableau. Note that the end nodes of a local tableau
are *not* fine nodes of their own: in the `Tableau` type they are the roots of the tableaux
given by `next`, and that is where they show up here.

Hence a fine node is either
- an internal node of the local tableau applied at a `Tableau.loc` node (`inLoc`),
- a `Tableau.pdl` node (`pdlHere`), or
- a `Tableau.lrep` node, i.e. a loaded-path repeat leaf (`lrepHere`),
possibly below some `loc` and `pdl` steps.
Every node has exactly one representation as a `FinePathIn`. -/

/-- A path in a tableau that may also stop at an intermediate node inside a `LocalTableau`. -/
inductive FinePathIn : ∀ {Hist X}, Tableau Hist X → Type
  | inLoc {Hist X nrep nbas} {lt : LocalTableau X} {next} (lp : LocalPathIn lt)
      (lp_int : lp.isInternal) :
      FinePathIn (@Tableau.loc Hist X nrep nbas lt next)
  | pdlHere {Hist X Y nrep bas} {r : PdlRule X Y} {next} :
      FinePathIn (@Tableau.pdl Hist X Y nrep bas r next)
  | lrepHere {Hist X} {lpr : LoadedPathRepeat Hist X} : FinePathIn (Tableau.lrep lpr)
  | loc {Hist X nrep nbas} {lt : LocalTableau X} {next} {Y} (Y_in : Y ∈ endNodesOf lt)
      (tail : FinePathIn (next Y Y_in)) : FinePathIn (@Tableau.loc Hist X nrep nbas lt next)
  | pdl {Hist X Y nrep bas} {r : PdlRule X Y} {next} (tail : FinePathIn next) :
      FinePathIn (@Tableau.pdl Hist X Y nrep bas r next)
deriving DecidableEq

/-- The fine path pointing at the root of a tableau. -/
def rootFine : {H : History} → {X : Sequent} → (tab : Tableau H X) → FinePathIn tab
  | _, _, .loc _ nbas lt _ => match lt, nbas with
      | .byLocalRule .., _ => .inLoc .nil (by
          simp [LocalPathIn.isInternal, LocalPathIn.ltAt, LocalTableau.hasRule])
      | .sim bas, nbas => absurd bas nbas
  | _, _, .pdl .. => .pdlHere
  | _, _, .lrep _ => .lrepHere

/-- The sequent at the node a fine path points at, i.e. `Λ(t)` for fine nodes `t`. -/
@[expose] def FinePathIn.label : ∀ {Hist X} {tab : Tableau Hist X}, FinePathIn tab → Sequent
  | _, _, _, .inLoc lp _ => lp.last
  | _, X, _, .pdlHere => X
  | _, X, _, .lrepHere => X
  | _, _, _, .loc _ tail => tail.label
  | _, _, _, .pdl tail => tail.label

/-- The `PathIn` node in whose local tableau the given fine node lies. -/
@[expose] def FinePathIn.base : ∀ {Hist X} {tab : Tableau Hist X}, FinePathIn tab → PathIn tab
  | _, _, _, .inLoc _ _ => .nil
  | _, _, _, .pdlHere => .nil
  | _, _, _, .lrepHere => .nil
  | _, _, _, .loc Y_in tail => .loc Y_in tail.base
  | _, _, _, .pdl tail => .pdl tail.base

/-- The children of a fine node. Note that a child of an internal node of a local tableau
may be a node of the tableau in the coarse `PathIn` sense, namely when it is an end node
of that local tableau. -/
@[expose] def FinePathIn.children : ∀ {Hist X} {tab : Tableau Hist X},
    FinePathIn tab → Finset (FinePathIn tab)
  | _, _, _, .inLoc lp _ => lp.children.image (fun lp' =>
      match h : lp'.endNodeAtOpt with
      | some ⟨_, Y_in⟩ => .loc Y_in (rootFine _)
      | none => .inLoc lp' ((LocalPathIn.isInternal_iff_endNodeAtOpt_eq_none lp').mpr h))
  | _, _, _, .pdlHere => { .pdl (rootFine _) }
  | _, _, _, .lrepHere => {}
  | _, _, _, .loc Y_in tail => tail.children.image (.loc Y_in)
  | _, _, _, .pdl tail => tail.children.image (.pdl)

/-- Any node in the coarse sense is also a node in the fine sense. -/
def PathIn.toFine : ∀ {Hist X} {tab : Tableau Hist X}, PathIn tab → FinePathIn tab
  | _, _, _, .nil => rootFine _
  | _, _, _, .loc Y_in tail => .loc Y_in tail.toFine
  | _, _, _, .pdl tail => .pdl tail.toFine

/-- All fine nodes of a tableau. Compare `allPaths`. -/
def allFinePaths : {H : History} → {X : Sequent} → (tab : Tableau H X) →
    List (FinePathIn tab)
  | _, _, .loc _ _ lt next =>
      (internalLocalPaths lt).attach.map
          (fun ⟨lp, lp_in⟩ => .inLoc lp (internalLocalPaths_isInternal lp lp_in))
      ++ (endNodesOf lt).pdlSeqSort.attach.flatMap
          (fun ⟨Y, Y_in⟩ => (allFinePaths (next Y ((Finset.mem_seqSort _).mp Y_in))).map
            (.loc ((Finset.mem_seqSort _).mp Y_in)))
  | _, _, .pdl _ _ _ next => .pdlHere :: (allFinePaths next).map (.pdl)
  | _, _, .lrep _ => [ .lrepHere ]

@[simp]
lemma label_rootFine {H X} (tab : Tableau H X) : (rootFine tab).label = X := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.label, LocalPathIn.last]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.label]
  · simp [rootFine, FinePathIn.label]

@[simp]
lemma base_rootFine {H X} (tab : Tableau H X) : (rootFine tab).base = .nil := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.base]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.base]
  · simp [rootFine, FinePathIn.base]

@[simp]
lemma PathIn.base_toFine {H X} {tab : Tableau H X} (p : PathIn tab) : p.toFine.base = p := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.base]

@[simp]
lemma PathIn.label_toFine {H X} {tab : Tableau H X} (p : PathIn tab) :
    p.toFine.label = nodeAt p := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.label]

theorem FinePathIn.mem_allFinePaths {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    f ∈ allFinePaths tab := by
  induction f
  case inLoc lp lp_int =>
    simp only [allFinePaths, List.mem_append, List.mem_map, List.mem_attach, true_and,
      Subtype.exists]
    exact Or.inl ⟨lp, lp.mem_internalLocalPaths lp_int, rfl⟩
  case pdlHere => simp [allFinePaths]
  case lrepHere => simp [allFinePaths]
  case loc Y_in tail IH =>
    simp only [allFinePaths, List.mem_append, List.mem_map, List.mem_attach, reduceCtorEq,
      and_false, exists_false, List.mem_flatMap, loc.injEq, true_and, Subtype.exists,
      Finset.mem_seqSort, false_or]
    exact ⟨_, Y_in, tail, IH, rfl, by grind⟩
  case pdl tail IH =>
    simp only [allFinePaths, List.mem_cons, List.mem_map]
    exact Or.inr ⟨tail, IH, rfl⟩

/-- Fine children either stay at the same node in the coarse sense, or they are a child
of it. This connects the fine children with the `edge` relation `⋖_`. -/
theorem FinePathIn.base_of_mem_children {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    ∀ g ∈ f.children, g.base = f.base ∨ f.base ⋖_ g.base := by
  induction f
  case inLoc lp lp_int =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨lp', _, rfl⟩ := g_in
    split
    · right; simp [FinePathIn.base]
    · left; rfl
  case pdlHere =>
    intro g g_in
    simp only [children, Finset.mem_singleton] at g_in
    subst g_in
    right
    simp [FinePathIn.base]
  case lrepHere => simp [FinePathIn.children]
  case loc Y_in tail IH =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    rcases IH g' g'_in with h | h
    · left; simp [FinePathIn.base, h]
    · right; simpa [FinePathIn.base] using h
  case pdl tail IH =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    rcases IH g' g'_in with h | h
    · left; simp [FinePathIn.base, h]
    · right; simpa [FinePathIn.base] using h

lemma FinePathIn.map_label_children_inLoc {Hist X nrep nbas} {lt : LocalTableau X} {next}
    (lp : LocalPathIn lt) (h : lp.isInternal) :
    ((@FinePathIn.inLoc Hist X nrep nbas lt next lp h).children).image FinePathIn.label
      = lp.children.image LocalPathIn.last := by
  simp only [children]
  rw [Finset.image_image]
  refine Finset.image_congr ?_
  intro lp' _
  simp only [Function.comp_apply]
  split
  · rename_i Y Y_in heq
    simp only [FinePathIn.label, label_rootFine]
    exact (lp'.last_of_endNodeAtOpt heq).symm
  · simp [FinePathIn.label]

/-- The local rule applied at a fine node, if any. -/
@[expose] def FinePathIn.lraOpt : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Option LocalRuleApp
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => some lra
      | .sim _ => none
  | _, _, _, .pdlHere => none
  | _, _, _, .lrepHere => none
  | _, _, _, .loc _ tail => tail.lraOpt
  | _, _, _, .pdl tail => tail.lraOpt

/-- If a local rule is applied at a fine node then that node is labelled with the premise
and its children are labelled with the conclusions of that rule. -/
lemma FinePathIn.lraOpt_spec {H X} {tab : Tableau H X} (f : FinePathIn tab) {lra : LocalRuleApp}
    (h : f.lraOpt = some lra) :
    f.label = lra.X ∧ f.children.image FinePathIn.label = lra.C := by
  induction f
  case inLoc lp lp_int =>
    simp only [FinePathIn.lraOpt] at h
    rcases hlt : lp.ltAt with ⟨lra', X_def, lnext⟩ | bas
    · rw [hlt] at h
      simp only [Option.some.injEq] at h
      subst h
      refine ⟨X_def, ?_⟩
      rw [FinePathIn.map_label_children_inLoc, LocalPathIn.map_last_children, hlt]
      rfl
    · rw [hlt] at h
      simp at h
  case pdlHere => simp [FinePathIn.lraOpt] at h
  case lrepHere => simp [FinePathIn.lraOpt] at h
  case loc IH =>
    simp only [FinePathIn.lraOpt] at h
    obtain ⟨h1, h2⟩ := IH h
    refine ⟨h1, ?_⟩
    rw [FinePathIn.children, Finset.image_image]
    exact h2
  case pdl IH =>
    simp only [FinePathIn.lraOpt] at h
    obtain ⟨h1, h2⟩ := IH h
    refine ⟨h1, ?_⟩
    rw [FinePathIn.children, Finset.image_image]
    exact h2

open HasSat in
/-- Local soundness and invertibility at the fine level: whenever a local rule is applied
at a fine node, its label is satisfied exactly if the label of one of its children is.
This is the property of the fine tableau that makes the quasi-tableau work. -/
theorem FinePathIn.locally_sound {H X} {tab : Tableau H X} (f : FinePathIn tab)
    {lra : LocalRuleApp} (h : f.lraOpt = some lra) {W} (M : KripkeModel W) (w : W) :
    (M, w) ⊨ f.label ↔ ∃ g ∈ f.children, (M, w) ⊨ g.label := by
  obtain ⟨h1, h2⟩ := f.lraOpt_spec h
  rw [h1, localRuleTruth lra M w]
  constructor
  · rintro ⟨Ci, Ci_in, hCi⟩
    have : Ci ∈ f.children.image FinePathIn.label := by
      rw [h2]; exact Finset.mem_def.mpr Ci_in
    grind
  · rintro ⟨g, g_in, hg⟩
    refine ⟨g.label, ?_, hg⟩
    grind

/-! ## Left and right rules

At the fine level each rule application is a left rule or a right rule or neither
(the latter for closing rules and loaded-path repeats), but never both.
This is what Lemma 9.7 (a) is about, and it is the reason why we needed the fine nodes:
on the `Tableau` level a `loc` step is in general a mix of left and right rules. -/

/-- Is this a local rule applied to the right component? -/
@[expose] def LocalRule.isRightRule {X YS} : LocalRule X YS → Bool
  | .oneSidedR _ _ => true
  | .loadedR _ _ _ => true
  | _ => false

/-- Is this a local rule applied to the left component? -/
@[expose] def LocalRule.isLeftRule {X YS} : LocalRule X YS → Bool
  | .oneSidedL _ _ => true
  | .loadedL _ _ _ => true
  | _ => false

/-- Whether this local rule application acts on the right component. -/
@[expose] def LocalRuleApp.isRightRule (lra : LocalRuleApp) : Bool := lra.lr.isRightRule

/-- Whether this local rule application acts on the left component. -/
@[expose] def LocalRuleApp.isLeftRule (lra : LocalRuleApp) : Bool := lra.lr.isLeftRule

lemma LocalRuleApp.not_left_and_right (lra : LocalRuleApp) :
    ¬ (lra.isLeftRule ∧ lra.isRightRule) := by
  rcases lra with ⟨L, R, O, Lcond, Rcond, Ocond, ress, lr, C, hC, pre⟩
  cases lr <;>
    simp [LocalRuleApp.isLeftRule, LocalRuleApp.isRightRule, LocalRule.isLeftRule,
      LocalRule.isRightRule]

/-- The `(M)`, `(L+)` and `(L-)` rules acting on the right component. -/
@[expose] def PdlRule.isRightRule {X Y} : PdlRule X Y → Bool
  | .loadR _ _ _ => true
  | .freeR _ _ => true
  | .modR _ _ => true
  | _ => false

/-- The `(M)`, `(L+)` and `(L-)` rules acting on the left component. -/
@[expose] def PdlRule.isLeftRule {X Y} : PdlRule X Y → Bool
  | .loadL _ _ _ => true
  | .freeL _ _ => true
  | .modL _ _ => true
  | _ => false

/-- Is a right rule applied at this fine node? -/
@[expose] def FinePathIn.usesRightRule : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => lra.isRightRule
      | .sim _ => false
  | _, _, _, @FinePathIn.pdlHere _ _ _ _ _ r _ => r.isRightRule
  | _, _, _, .lrepHere => false
  | _, _, _, .loc _ tail => tail.usesRightRule
  | _, _, _, .pdl tail => tail.usesRightRule

/-- Is a left rule applied at this fine node? -/
@[expose] def FinePathIn.usesLeftRule : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => match lp.ltAt with
      | .byLocalRule lra _ _ => lra.isLeftRule
      | .sim _ => false
  | _, _, _, @FinePathIn.pdlHere _ _ _ _ _ r _ => r.isLeftRule
  | _, _, _, .lrepHere => false
  | _, _, _, .loc _ tail => tail.usesLeftRule
  | _, _, _, .pdl tail => tail.usesLeftRule

/-- No node uses a left and a right rule at the same time. -/
lemma FinePathIn.not_left_and_right {H Y} {tab : Tableau H Y} (f : FinePathIn tab) :
    ¬ (f.usesLeftRule ∧ f.usesRightRule) := by
  induction f
  case inLoc lp lp_int =>
    rintro ⟨hl, hr⟩
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] at hl hr
    rcases h : lp.ltAt with ⟨lra, X_def, lnext⟩ | bas
    · rw [h] at hl hr
      simp only at hl hr
      exact lra.not_left_and_right ⟨hl, hr⟩
    · rw [h] at hl
      simp at hl
  case pdlHere _ _ _ _ _ r _ =>
    rintro ⟨hl, hr⟩
    simp only [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] at hl hr
    cases r <;> simp_all [PdlRule.isLeftRule, PdlRule.isRightRule]
  case lrepHere => simp [FinePathIn.usesLeftRule]
  case loc IH => simpa [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] using IH
  case pdl IH => simpa [FinePathIn.usesLeftRule, FinePathIn.usesRightRule] using IH

/-- A node where a right rule is applied is not a loaded-path repeat, and neither is the
coarse node it belongs to. -/
lemma FinePathIn.not_isLrep_base_of_usesRightRule {H X} {tab : Tableau H X} (f : FinePathIn tab)
    (h : f.usesRightRule) : ¬ f.base.isLrep := by
  induction f with
  | inLoc lp lp_int => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep]
  | pdlHere => simp [FinePathIn.base, PathIn.isLrep, tabAt, Tableau.isLrep]
  | lrepHere => simp [FinePathIn.usesRightRule] at h
  | loc Y_in tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simpa [FinePathIn.base, PathIn.isLrep, tabAt] using IH h
  | pdl tail IH =>
    simp only [FinePathIn.usesRightRule] at h
    simpa [FinePathIn.base, PathIn.isLrep, tabAt] using IH h

/-- Is this fine node also a node in the coarse sense, i.e. the root of the local tableau
at its base? -/
@[expose] def FinePathIn.atBigRoot : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Bool
  | _, _, _, .inLoc lp _ => lp.isNilB
  | _, _, _, .pdlHere => true
  | _, _, _, .lrepHere => true
  | _, _, _, .loc _ tail => tail.atBigRoot
  | _, _, _, .pdl tail => tail.atBigRoot

@[simp]
lemma atBigRoot_rootFine {H X} (tab : Tableau H X) : (rootFine tab).atBigRoot = true := by
  rcases tab with ⟨nrep, nbas, lt, next⟩ | _ | _
  · rcases lt with ⟨lra, X_def, lnext⟩ | bas
    · simp [rootFine, FinePathIn.atBigRoot, LocalPathIn.isNilB]
    · exact absurd bas nbas
  · simp [rootFine, FinePathIn.atBigRoot]
  · simp [rootFine, FinePathIn.atBigRoot]

@[simp]
lemma PathIn.atBigRoot_toFine {H X} {tab : Tableau H X} (p : PathIn tab) :
    p.toFine.atBigRoot = true := by
  induction p <;> simp_all [PathIn.toFine, FinePathIn.atBigRoot]

/-- The labels of those end nodes of the local tableau at `f.base` that are below `f`.
These are the labels of the children of `f.base` that can be reached from `f`. -/
def FinePathIn.endLabelsBelow : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → Finset Sequent
  | _, _, _, .inLoc lp _ => endNodesOf lp.ltAt
  | _, _, _, .pdlHere => {}
  | _, _, _, .lrepHere => {}
  | _, _, _, .loc _ tail => tail.endLabelsBelow
  | _, _, _, .pdl tail => tail.endLabelsBelow

/-- The children of `f.base` in the coarse sense that are below the fine node `f`.
Note that when `f` is a coarse node itself, i.e. `f.atBigRoot`, then these are *all*
children of `f.base`, and that they get further restricted the deeper `f` sits inside the
local tableau at `f.base`. -/
@[expose] def FinePathIn.coarseChildrenBelow : ∀ {H X} {tab : Tableau H X},
    FinePathIn tab → List (PathIn tab)
  | _, _, _, .inLoc lp _ => lp.endNodesBelow.map (fun ⟨_, Y_in⟩ => PathIn.loc Y_in .nil)
  | _, _, _, .pdlHere => [PathIn.pdl .nil]
  | _, _, _, .lrepHere => []
  | _, _, _, .loc Y_in tail => tail.coarseChildrenBelow.map (PathIn.loc Y_in)
  | _, _, _, .pdl tail => tail.coarseChildrenBelow.map (PathIn.pdl)

/-- If a coarse child `q` is below the fine node `f`, then `f` has a fine child `g` that
is either still at the same coarse node and has `q` below it, or `g` *is* `q`. -/
lemma FinePathIn.exists_child_coarseChildrenBelow {H X} {tab : Tableau H X}
    (f : FinePathIn tab) (q : PathIn tab) (hq : q ∈ f.coarseChildrenBelow) :
    ∃ g ∈ f.children,
      (g.base = f.base ∧ q ∈ g.coarseChildrenBelow) ∨ (g.base = q ∧ g.atBigRoot) := by
  induction f with
  | inLoc lp lp_int =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists] at hq
    obtain ⟨Y, Y_in, hYin, rfl⟩ := hq
    obtain ⟨c, c_in, hc⟩ := LocalPathIn.exists_child_endNodesBelow lp lp_int ⟨Y, Y_in⟩ hYin
    refine ⟨_, Finset.mem_image_of_mem _ c_in, ?_⟩
    split
    case _ W W_in h =>
      refine Or.inr ⟨?_, by simp [FinePathIn.atBigRoot]⟩
      have := LocalPathIn.endNodesBelow_eq_of_endNodeAtOpt c h ⟨Y, Y_in⟩ hc
      simp only [Subtype.mk.injEq] at this
      simp only [FinePathIn.base, base_rootFine]
      subst this
      rfl
    case _ h =>
      refine Or.inl ⟨rfl, ?_⟩
      simp only [FinePathIn.coarseChildrenBelow, List.mem_map, Subtype.exists]
      exact ⟨Y, Y_in, hc, rfl⟩
  | @pdlHere _ _ _ _ _ _ next =>
    refine ⟨.pdl (rootFine next), by simp [FinePathIn.children], Or.inr ⟨?_, ?_⟩⟩
    · simp only [FinePathIn.coarseChildrenBelow, List.mem_singleton] at hq
      subst hq
      simp [FinePathIn.base]
    · simp [FinePathIn.atBigRoot]
  | lrepHere => simp [FinePathIn.coarseChildrenBelow] at hq
  | loc Y_in tail IH =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨g, g_in, hg⟩ := IH q' hq'
    refine ⟨.loc Y_in g, by
      simp only [children, Finset.mem_image, loc.injEq, heq_eq_eq, true_and,
        exists_eq_right]; grind, ?_⟩
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [FinePathIn.base, h1], by
        simp only [FinePathIn.coarseChildrenBelow, List.mem_map]; exact ⟨q', h2, rfl⟩⟩
    · exact Or.inr ⟨by simp [FinePathIn.base, h1], by simpa [FinePathIn.atBigRoot] using h2⟩
  | pdl tail IH =>
    simp only [FinePathIn.coarseChildrenBelow, List.mem_map] at hq
    obtain ⟨q', hq', rfl⟩ := hq
    obtain ⟨g, g_in, hg⟩ := IH q' hq'
    refine ⟨.pdl g, by simp only [children, Finset.mem_image, pdl.injEq,
      exists_eq_right]; grind, ?_⟩
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by simp [FinePathIn.base, h1], by
        simp only [FinePathIn.coarseChildrenBelow, List.mem_map]; exact ⟨q', h2, rfl⟩⟩
    · exact Or.inr ⟨by simp [FinePathIn.base, h1], by simpa [FinePathIn.atBigRoot] using h2⟩

/-- A fine node that is a coarse node is the image of that coarse node under `toFine`. -/
lemma FinePathIn.eq_toFine_base_of_atBigRoot {H X} {tab : Tableau H X} (f : FinePathIn tab)
    (h : f.atBigRoot) : f = f.base.toFine := by
  induction f with
  | @inLoc Hist X nrep nbas lt next lp lp_int =>
    cases lp with
    | nil =>
      rcases lt with ⟨lra, X_def, lnext⟩ | bas
      · rfl
      · exact absurd bas nbas
    | cons => simp [FinePathIn.atBigRoot, LocalPathIn.isNilB] at h
  | pdlHere => rfl
  | lrepHere => rfl
  | loc Y_in tail IH =>
    simp only [FinePathIn.atBigRoot] at h
    simp only [FinePathIn.base, PathIn.toFine]
    exact congrArg _ (IH h)
  | pdl tail IH =>
    simp only [FinePathIn.atBigRoot] at h
    simp only [FinePathIn.base, PathIn.toFine]
    exact congrArg _ (IH h)

/-- All children of a coarse node are below it in the fine sense. This is the converse of
`FinePathIn.base_of_mem_children` for coarse nodes. -/
lemma PathIn.mem_coarseChildrenBelow_toFine {H X} {tab : Tableau H X} :
    ∀ (p q : PathIn tab), p ⋖_ q → q ∈ p.toFine.coarseChildrenBelow := by
  intro p
  induction p with
  | nil =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · simp only [tabAt] at hh
      obtain ⟨rfl, hh2⟩ := Sigma.mk.injEq .. ▸ hh
      obtain ⟨rfl, -⟩ := hh2
      change PathIn.loc Y_in PathIn.nil ∈ _
      rcases lt with ⟨lra, X_def, lnext⟩ | bas
      · simp only [PathIn.toFine, rootFine, FinePathIn.coarseChildrenBelow,
          LocalPathIn.endNodesBelow, List.mem_map, Subtype.exists, Finset.mem_seqSort]
        refine ⟨Y, Y_in, ?_, rfl⟩
        grind
      · exact absurd bas nbas
    · simp only [tabAt] at hh
      obtain ⟨rfl, hh2⟩ := Sigma.mk.injEq .. ▸ hh
      obtain ⟨rfl, -⟩ := hh2
      change PathIn.pdl PathIn.nil ∈ _
      simp [PathIn.toFine, rootFine, FinePathIn.coarseChildrenBelow]
  | loc Y_in tail IH =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.loc Y'_in .nil)) :=
        Or.inl ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
      change PathIn.loc Y_in (tail.append (hh ▸ PathIn.loc Y'_in .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.pdl .nil)) :=
        Or.inr ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
      change PathIn.loc Y_in (tail.append (hh ▸ PathIn.pdl .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
  | pdl tail IH =>
    intro q h
    rcases h with ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
                | ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.loc Y'_in .nil)) :=
        Or.inl ⟨Hist, X', nrep, nbas, lt, next, Y, Y'_in, hh, rfl⟩
      change PathIn.pdl (tail.append (hh ▸ PathIn.loc Y'_in .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)
    · have step : tail ⋖_ (tail.append (hh ▸ PathIn.pdl .nil)) :=
        Or.inr ⟨Hist, X', nrep, bas, Y, r, next, hh, rfl⟩
      change PathIn.pdl (tail.append (hh ▸ PathIn.pdl .nil)) ∈ _
      simp only [PathIn.toFine, FinePathIn.coarseChildrenBelow]
      exact List.mem_map_of_mem (IH _ step)

/-- The right component of a sequent, again as a sequent but with empty left component.
This is `Λ₂` from the paper; we use it to label the nodes of the quasi-tableau. -/
@[expose] def Sequent.rightOnly (X : Sequent) : Sequent := ⟨{}, X.2.1, X.2.2⟩

/-! ## Well-founded descent for fine paths

The children of a fine node (`FinePathIn.children`) are *not* structurally smaller than the
node itself: a child of an internal node of a local tableau is again a path in the *same*
local tableau, and a child of the last internal node is a `FinePathIn.loc` step, hence even
structurally bigger. So there is no induction principle for `FinePathIn` that follows the
child relation for free.

Below we provide one, in the same way as `PathIn.strong_upwards_inductionOn` is obtained
from `flipEdge.wellFounded` for the coarse `PathIn` nodes: we equip fine paths with a
`FinePathIn.length`, bound it by a size measure `Tableau.fineSize` of the tableau, and
conclude that there is no infinite chain of fine children — the child relation `fineEdge`
has a well-founded flip. From that we get

* `FinePathIn.edge_upwards_inductionOn` — induction from the leaves to the root, and
* `FinePathIn.strong_upwards_inductionOn` — its strong version, where the inductive
  hypothesis is available at all fine *descendants*, not only at the children.

Dually, `FinePathIn.descent` states the descent principle in the contrapositive form in
which it is used: if a property holds somewhere and always propagates to *some* child,
then it holds at a node without children.
-/

/-! ## A length for local paths -/

/-- The number of steps of a local path. -/
def LocalPathIn.length {X} {lt : LocalTableau X} : LocalPathIn lt → ℕ
  | .nil => 0
  | .cons _ tail => tail.length + 1

/-- The number of nodes of a local tableau. -/
def LocalTableau.nodeCount {X} : LocalTableau X → ℕ
  | .byLocalRule lra _ next =>
      1 + (lra.C.pdlSeqSort.attach.map
        (fun ⟨Y, Y_in⟩ => (next Y ((Finset.mem_seqSort _).mp Y_in)).nodeCount)).sum
  | .sim _ => 1

lemma LocalTableau.nodeCount_pos {X} (lt : LocalTableau X) : 0 < lt.nodeCount := by
  cases lt <;> simp [LocalTableau.nodeCount]

lemma LocalPathIn.length_lt_nodeCount {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    lp.length < lt.nodeCount := by
  induction lp
  case nil X lt => exact lt.nodeCount_pos
  case cons X lra X_def next Y Y_in tail IH =>
    simp only [LocalPathIn.length, LocalTableau.nodeCount]
    have key : ∀ s : ℕ, (next Y Y_in).nodeCount ≤ s → tail.length + 1 < 1 + s := by omega
    apply key
    apply List.le_sum_of_mem
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Finset.mem_seqSort]
    exact ⟨Y, Y_in, rfl⟩

/-- Going to a child inside a local tableau increases the length. -/
lemma LocalPathIn.length_lt_of_mem_children {X} {lt : LocalTableau X} (lp : LocalPathIn lt) :
    ∀ lp' ∈ lp.children, lp.length < lp'.length := by
  induction lp
  case nil X lt =>
    intro lp' h
    cases lt
    · simp only [children, Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists] at h
      obtain ⟨Y, Y_in, rfl⟩ := h
      simp [LocalPathIn.length]
    · simp [LocalPathIn.children] at h
  case cons X lra X_def next Y Y_in tail IH =>
    intro lp' h
    simp only [children, Finset.mem_image] at h
    obtain ⟨lp'', h'', rfl⟩ := h
    have := IH lp'' h''
    simp only [LocalPathIn.length]
    omega

/-! ## A length for fine paths -/

/-- A size measure for tableaux that also counts the intermediate nodes of the local
tableaux, i.e. an upper bound for the length of any `FinePathIn`. -/
def Tableau.fineSize : ∀ {H X}, Tableau H X → ℕ
  | _, _, .loc _ _ lt next =>
      lt.nodeCount +
        (((endNodesOf lt).pdlSeqSort.attach.map
          (fun ⟨Y, Y_in⟩ => (next Y ((Finset.mem_seqSort _).mp Y_in)).fineSize)).sum)
  | _, _, .pdl _ _ _ next => 1 + next.fineSize
  | _, _, .lrep _ => 1

/-- The number of steps of a fine path, where a whole local tableau counts with its
`LocalTableau.nodeCount` so that leaving it strictly increases the length. -/
def FinePathIn.length : ∀ {H X} {tab : Tableau H X}, FinePathIn tab → ℕ
  | _, _, _, .inLoc lp _ => lp.length
  | _, _, _, .pdlHere => 0
  | _, _, _, .lrepHere => 0
  | _, _, .loc _ _ lt _, .loc _ tail => lt.nodeCount + tail.length
  | _, _, _, .pdl tail => 1 + tail.length

lemma FinePathIn.length_lt_fineSize {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    f.length < tab.fineSize := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    have := lp.length_lt_nodeCount
    simp only [FinePathIn.length, Tableau.fineSize]
    omega
  case pdlHere => simp [FinePathIn.length, Tableau.fineSize]
  case lrepHere => simp [FinePathIn.length, Tableau.fineSize]
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    simp only [FinePathIn.length, Tableau.fineSize]
    have key : ∀ s : ℕ, (next Y Y_in).fineSize ≤ s →
        lt.nodeCount + tail.length < lt.nodeCount + s := by omega
    apply key
    apply List.le_sum_of_mem
    simp only [List.mem_map, List.mem_attach, true_and, Subtype.exists, Finset.mem_seqSort]
    exact ⟨Y, Y_in, rfl⟩
  case pdl tail IH =>
    simp only [FinePathIn.length, Tableau.fineSize]
    omega

/-- Going to a fine child strictly increases the length of a fine path. -/
theorem FinePathIn.length_lt_of_mem_children {H X} {tab : Tableau H X} (f : FinePathIn tab) :
    ∀ g ∈ f.children, f.length < g.length := by
  induction f
  case inLoc Hist X nrep nbas lt next lp lp_int =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨lp', lp'_in, rfl⟩ := g_in
    have hlp := lp.length_lt_of_mem_children lp' lp'_in
    split
    · have := lp.length_lt_nodeCount
      simp only [FinePathIn.length]
      omega
    · simpa [FinePathIn.length] using hlp
  case pdlHere Hist X Y nrep bas r next =>
    intro g g_in
    simp only [children, Finset.mem_singleton] at g_in
    subst g_in
    simp [FinePathIn.length]
  case lrepHere => simp [FinePathIn.children]
  case loc Hist X nrep nbas lt next Y Y_in tail IH =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    have := IH g' g'_in
    simp only [FinePathIn.length]
    omega
  case pdl Hist X Y nrep bas r next tail IH =>
    intro g g_in
    simp only [children, Finset.mem_image] at g_in
    obtain ⟨g', g'_in, rfl⟩ := g_in
    have := IH g' g'_in
    simp only [FinePathIn.length]
    omega

/-! ## The child relation on fine nodes and its well-founded flip -/

/-- The child relation on fine nodes, the fine analogue of `edge`. -/
def fineEdge {H X} {tab : Tableau H X} (f g : FinePathIn tab) : Prop := g ∈ f.children

@[inherit_doc] infixl:50 " ⋖f " => fineEdge

lemma fineEdge_then_length_lt {H X} {tab : Tableau H X} {f g : FinePathIn tab} (h : f ⋖f g) :
    f.length < g.length :=
  f.length_lt_of_mem_children g h

/-- The flipped child relation on fine nodes is well-founded. Compare `flipEdge.wellFounded`. -/
theorem flipFineEdge.wellFounded {H X} {tab : Tableau H X} :
    WellFounded (flip (@fineEdge H X tab)) := by
  rw [wellFounded_iff_isEmpty_descending_chain]
  by_contra hChain
  simp only [not_isEmpty_iff, nonempty_subtype] at hChain
  rcases hChain with ⟨f, all_rel⟩
  have all_lt : ∀ n : ℕ, (f n).length < tab.fineSize := fun n => (f n).length_lt_fineSize
  have increasing : ∀ n : ℕ, (f n).length < (f (n + 1)).length :=
    fun n => fineEdge_then_length_lt (all_rel n)
  have big : ∀ n : ℕ, n < (f (n + 1)).length := by
    intro n
    induction n with
    | zero => exact lt_of_le_of_lt (Nat.zero_le _) (increasing 0)
    | succ k IH => have := increasing (k + 1); omega
  have := big tab.fineSize
  have := all_lt (tab.fineSize + 1)
  omega

/-! ## The induction principles -/

/-- Induction on fine nodes going from the leaves (= childless fine nodes) to the root.
Compare `PathIn.edge_upwards_inductionOn`. -/
theorem FinePathIn.edge_upwards_inductionOn {H X} {tab : Tableau H X}
    {motive : FinePathIn tab → Prop}
    (up : ∀ {u}, (∀ {s}, u ⋖f s → motive s) → motive u)
    (t : FinePathIn tab) : motive t := by
  apply WellFounded.induction flipFineEdge.wellFounded t
  intro u IH
  exact up fun {s} u_s => IH s u_s

/-- Strong induction on fine nodes going from the leaves to the root: the motive may be
assumed at *all* fine descendants. Compare `PathIn.strong_upwards_inductionOn`. -/
theorem FinePathIn.strong_upwards_inductionOn {H X} {tab : Tableau H X}
    {motive : FinePathIn tab → Prop}
    (ups : ∀ {u}, (∀ {s}, Relation.TransGen fineEdge u s → motive s) → motive u)
    (t : FinePathIn tab) : motive t := by
  apply WellFounded.induction (WellFounded.transGen (@flipFineEdge.wellFounded H X tab)) t
  intro u IH
  exact ups fun {s} u_s => IH s (by rw [Relation.TransGen_flip_iff]; exact u_s)

/-- The descent principle for fine nodes: if a property holds at some fine node and, at
every fine node where it holds and which has a child, it also holds at some child, then it
holds at some *childless* fine node.

This is the form in which the well-foundedness is used when following a path downwards in
the fine sense, cf. Lemma 9.7 (d) of the paper. -/
theorem FinePathIn.descent {H X} {tab : Tableau H X} {P : FinePathIn tab → Prop}
    (down : ∀ u, P u → u.children ≠ {} → ∃ g ∈ u.children, P g)
    (t : FinePathIn tab) (ht : P t) :
    ∃ u, P u ∧ u.children = {} := by
  have main : ∀ u : FinePathIn tab, P u → ∃ v, P v ∧ v.children = {} := by
    intro u
    induction u using FinePathIn.edge_upwards_inductionOn with
    | @up u IH =>
      intro hu
      by_cases hc : u.children = {}
      · exact ⟨u, hu, hc⟩
      · obtain ⟨g, g_in, hg⟩ := down u hu hc
        exact IH g_in hg
  exact main t ht

/-- The descent principle in the strong form: the property is only required to propagate to
some fine *descendant* (not necessarily a child) as long as the node is not childless. -/
theorem FinePathIn.strong_descent {H X} {tab : Tableau H X} {P : FinePathIn tab → Prop}
    (down : ∀ u, P u → u.children ≠ {} → ∃ g, Relation.TransGen fineEdge u g ∧ P g)
    (t : FinePathIn tab) (ht : P t) :
    ∃ u, P u ∧ u.children = {} := by
  have main : ∀ u : FinePathIn tab, P u → ∃ v, P v ∧ v.children = {} := by
    intro u
    induction u using FinePathIn.strong_upwards_inductionOn with
    | @ups u IH =>
      intro hu
      by_cases hc : u.children = {}
      · exact ⟨u, hu, hc⟩
      · obtain ⟨g, hug, hg⟩ := down u hu hc
        exact IH hug hg
  exact main t ht

end PDL
