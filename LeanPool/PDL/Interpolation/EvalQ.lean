/-
Copyright (c) 2023 PDL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PDL formalization contributors (see project card)
-/

module

public import LeanPool.PDL.Interpolation.ClusterItp

/-! # Evaluating Q-formulas, the witness distance, and basic nodes

This file collects the notions needed for Lemmas 10.6, 10.7 and 10.8 in
`Pdl.ClusterSatDown`:

* `QFormula.evalQ`, the evaluation of a Q-formula with an assignment for the internal
  variables, together with `QFormula.evalQ_gfp_unfold`, the unfolding of the fixpoint used
  at a companion node,
* `Sequent.loadedSplit` and friends, which read off the loaded formula `¬⌊δs⌋ψ` of a
  sequent,
* `witDist`, the witness distance `wd_M(v,x)` of the proof of Lemma 10.7, and
* `QuasiTab.BasicBetween`, the paper's "there is a basic node between `x` and `z`".

## Internal variables

The pre-interpolants `ι_x` are `QFormula`s, i.e. they may contain internal variables `q_z`.
The proof of Lemma 10.7 modifies the *valuation* of the internal variable `q_x` at a
companion node `x`, keeping the relational structure of the model fixed. Instead of
substituting a formula for `q_x` (and then appealing to the substitution lemma) we
therefore evaluate a Q-formula directly with respect to an assignment
`g : Var → W → Prop` of the internal variables. Changing the assignment leaves the model,
and hence all distances, untouched, which is exactly the "`M` and `M'` have the same
relational structure" of the paper.
-/

public section

namespace PDL

/-! ## Evaluating Q-formulas with an assignment for the internal variables -/

namespace QFormula

variable {Var : Type} {W : Type}

/-- Evaluate a Q-formula in a model `M` where the internal variables are interpreted by
the assignment `g`. -/
def evalQ (M : KripkeModel W) (g : Var → W → Prop) : W → QFormula Var → Prop
  | v, .fma ψ => evaluate M v ψ
  | v, .var q => g q v
  | v, .and ι1 ι2 => evalQ M g v ι1 ∧ evalQ M g v ι2
  | v, .boxes as ι => ∀ u, relateSeq M as v u → evalQ M g u ι

@[simp] lemma evalQ_fma {M : KripkeModel W} {g : Var → W → Prop} {v ψ} :
    evalQ M g v (fma ψ : QFormula Var) ↔ evaluate M v ψ := Iff.rfl
@[simp] lemma evalQ_var {M : KripkeModel W} {g : Var → W → Prop} {v q} :
    evalQ M g v (var q : QFormula Var) ↔ g q v := Iff.rfl
@[simp] lemma evalQ_and {M : KripkeModel W} {g : Var → W → Prop} {v} {ι1 ι2 : QFormula Var} :
    evalQ M g v (ι1.and ι2) ↔ evalQ M g v ι1 ∧ evalQ M g v ι2 := Iff.rfl
@[simp] lemma evalQ_boxes {M : KripkeModel W} {g : Var → W → Prop} {v as} {ι : QFormula Var} :
    evalQ M g v (ι.boxes as) ↔ ∀ u, relateSeq M as v u → evalQ M g u ι := Iff.rfl

/-- Evaluating a Q-formula with the assignment given by a substitution is the same as
evaluating the substituted formula. -/
lemma evalQ_iff_evaluate_subst {M : KripkeModel W} {σ : Var → Formula} :
    ∀ (ι : QFormula Var) (v : W),
      evalQ M (fun q u => evaluate M u (σ q)) v ι ↔ evaluate M v (ι.subst σ)
  | .fma _, _ => Iff.rfl
  | .var _, _ => Iff.rfl
  | .and ι1 ι2, v => by
      simp only [evalQ_and, subst_and, evaluate]
      rw [evalQ_iff_evaluate_subst ι1 v, evalQ_iff_evaluate_subst ι2 v]
  | .boxes as ι, v => by
      simp only [evalQ_boxes, subst_boxes]
      rw [evalBoxes]
      exact forall_congr' fun u => imp_congr_right fun _ => evalQ_iff_evaluate_subst ι u

/-- Two assignments that agree on the internal variables of a Q-formula give the same
value. -/
lemma evalQ_congr {M : KripkeModel W} {g h : Var → W → Prop} :
    ∀ (ι : QFormula Var) (v : W), (∀ q ∈ ι.vars, g q = h q) →
      (evalQ M g v ι ↔ evalQ M h v ι)
  | .fma _, _, _ => Iff.rfl
  | .var q, v, hgh => by
      simp only [evalQ_var]
      rw [hgh q (by simp [vars])]
  | .and ι1 ι2, v, hgh => by
      simp only [evalQ_and]
      rw [evalQ_congr ι1 v (fun q hq => hgh q (by simp [vars, hq])),
        evalQ_congr ι2 v (fun q hq => hgh q (by simp [vars, hq]))]
  | .boxes as ι, v, hgh => by
      simp only [evalQ_boxes]
      exact forall_congr' fun u => imp_congr_right fun _ =>
        evalQ_congr ι u (fun q hq => hgh q (by simpa [vars] using hq))

/-- Evaluating a conjunction of Q-formulas. -/
lemma evalQ_conj {M : KripkeModel W} {g : Var → W → Prop} {v : W} :
    ∀ L : List (QFormula Var), (evalQ M g v (conj L) ↔ ∀ ι ∈ L, evalQ M g v ι)
  | [] => by simp [conj, evaluate]
  | [ι] => by simp [conj]
  | ι1 :: ι2 :: L => by
      have IH := evalQ_conj (M := M) (g := g) (v := v) (ι2 :: L)
      simp only [conj, evalQ_and, IH, List.mem_cons, forall_eq_or_imp]

/-- Prefixing a simple Q-formula with boxes, for `evalQ`. -/
lemma evalQ_toQ_prefixBoxes {M : KripkeModel W} {g : Var → W → Prop} {v : W}
    (as : List Program) (s : QSimple Var) :
    evalQ M g v (QSimple.prefixBoxes as s).toQ ↔
      ∀ u, relateSeq M as v u → evalQ M g u s.toQ := by
  cases s with
  | fma ψ =>
      simp only [QSimple.prefixBoxes, QSimple.toQ, evalQ_fma]
      exact evalBoxes as ψ
  | boxVar bs q =>
      simp only [QSimple.prefixBoxes, QSimple.toQ, evalQ_boxes]
      constructor
      · intro h u hu u' hu'
        exact h u' (relateSeq_append.mpr ⟨u, hu, hu'⟩)
      · intro h u hu
        obtain ⟨u', hu1, hu2⟩ := relateSeq_append.mp hu
        exact h u' hu1 u hu2

/-- Evaluating the normal form of a Q-formula: this is Fact 9.17 for `evalQ`. -/
lemma evalQ_nf {M : KripkeModel W} {g : Var → W → Prop} {v : W} (ι : QFormula Var) :
    evalQ M g v ι.nf ↔ ∀ s ∈ ι.Spl, evalQ M g v s.toQ := by
  rw [nf, evalQ_conj]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h s hs; exact h _ s hs rfl
  · rintro h _ s hs rfl; exact h s hs

/-- A Q-formula is equivalent to its normal form, for `evalQ`. -/
lemma evalQ_nf_iff {M : KripkeModel W} {g : Var → W → Prop} :
    ∀ (ι : QFormula Var) (v : W), evalQ M g v ι.nf ↔ evalQ M g v ι := by
  intro ι v
  induction ι generalizing v with
  | fma ψ => simp [evalQ_nf, Spl, QSimple.toQ]
  | var q => simp [evalQ_nf, Spl, QSimple.toQ, relateSeq, relate, evaluate]
  | and ι1 ι2 IH1 IH2 =>
      rw [evalQ_nf]
      simp only [Spl, List.mem_append, evalQ_and]
      rw [← IH1 v, ← IH2 v, evalQ_nf, evalQ_nf]
      constructor
      · intro h; exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
      · rintro ⟨h1, h2⟩ s (hs | hs)
        · exact h1 s hs
        · exact h2 s hs
  | boxes as ι IH =>
      rw [evalQ_nf]
      simp only [Spl, List.mem_map, evalQ_boxes, forall_exists_index, and_imp]
      constructor
      · intro h u hu
        rw [← IH u, evalQ_nf]
        intro s hs
        have := h _ s hs rfl
        rw [evalQ_toQ_prefixBoxes] at this
        exact this u hu
      · rintro h _ s hs rfl
        rw [evalQ_toQ_prefixBoxes]
        intro u hu
        have hu' := h u hu
        rw [← IH u, evalQ_nf] at hu'
        exact hu' s hs

/-! ### Unfolding the fixpoint of the companion case

The pre-interpolant of a companion node `x` is `gfp x ι` for the pre-interpolant `ι` of
its child. Interpreting the internal variable `q_x` by `gfp x ι` itself turns `gfp x ι`
into `ι`; this is the semantic counterpart of the paper's observation that
`ι_x ≡ ι_y[q_x := ι_x]`. -/

lemma evalQ_gfp_unfold [DecidableEq Var] {M : KripkeModel W} {g : Var → W → Prop}
    {v : W} {q : Var} (ι : QFormula Var) (h : evalQ M g v (ι.gfp q)) :
    evalQ M (Function.update g q (fun u => evalQ M g u (ι.gfp q))) v ι := by
  have hbox : ∀ u, relate M (∗ (Program.unions (ι.loopProgs q))) v u →
      evalQ M g u (ι.dropVar q) := by
    intro u hu
    have h' := h
    rw [gfp, evalQ_boxes] at h'
    exact h' u (by rw [relateSeq_singleton]; exact hu)
  have hstar : ∀ u, relate M (∗ (Program.unions (ι.loopProgs q))) v u →
      evalQ M g u (ι.gfp q) := by
    intro u hu
    rw [gfp, evalQ_boxes]
    intro u' hu'
    rw [relateSeq_singleton] at hu'
    exact hbox u' (hu.trans hu')
  have hdrop := hbox v Relation.ReflTransGen.refl
  rw [dropVar, evalQ_conj] at hdrop
  rw [← evalQ_nf_iff, evalQ_nf]
  intro s hs
  by_cases hm : s.mentions q
  · cases s with
    | fma ψ => simp [QSimple.mentions] at hm
    | boxVar as p =>
        simp only [QSimple.mentions, decide_eq_true_eq] at hm
        subst hm
        rw [QSimple.toQ, evalQ_boxes]
        intro u hu
        rw [evalQ_var, Function.update_self]
        refine hstar u (Relation.ReflTransGen.single ?_)
        rw [relate_unions]
        refine ⟨Program.steps as, ?_, (relate_steps_iff_relateSeq _ _ _ _).mpr hu⟩
        simp only [loopProgs, List.mem_filterMap]
        exact ⟨QSimple.boxVar as p, hs, by simp [QSimple.progToOpt]⟩
  · have hmem : s.toQ ∈ (ι.Spl.filter (fun s => !s.mentions q)).map QSimple.toQ :=
      List.mem_map_of_mem (List.mem_filter.mpr ⟨hs, by simp [hm]⟩)
    refine (evalQ_congr s.toQ v ?_).mp (hdrop _ hmem)
    intro p hp
    cases s with
    | fma ψ => simp [QSimple.toQ] at hp
    | boxVar as p' =>
        simp only [QSimple.toQ, vars, List.mem_singleton] at hp
        subst hp
        rw [Function.update_of_ne]
        rintro rfl
        simp [QSimple.mentions] at hm

end QFormula

/-! ## The loaded formula of a sequent

For a node `x` of the quasi-tableau the paper writes the unique loaded formula of `Δ_x` as
`¬⌊δ_x⌋ψ_x` with `ψ_x` unloaded. Here `δ_x` and `ψ_x` are `Sequent.loadedProgs` and
`Sequent.loadedFma`, read off with `LoadFormula.split`. -/

namespace Sequent

/-- The loaded formula of a sequent, split into its list of programs and its final,
unloaded formula. For a free sequent we return `([], ⊥)`, which is never used. -/
@[expose] def loadedSplit : Sequent → List Program × Formula
  | ⟨_, _, none⟩ => ([], ⊥)
  | ⟨_, _, some (Sum.inl (~'χ))⟩ => χ.split
  | ⟨_, _, some (Sum.inr (~'χ))⟩ => χ.split

/-- The programs `δ_x` of the loaded formula `¬⌊δ_x⌋ψ_x`. -/
@[expose] def loadedProgs (X : Sequent) : List Program := X.loadedSplit.1

/-- The unloaded formula `ψ_x` of the loaded formula `¬⌊δ_x⌋ψ_x`. -/
@[expose] def loadedFma (X : Sequent) : Formula := X.loadedSplit.2

/-- The sequent has its loaded formula on the right, as all `Δ ∈ Λ₂[C]` do. -/
def isRightLoaded (X : Sequent) : Prop := ∃ nlf, X.O = some (Sum.inr nlf)

end Sequent

/-- Unloading a loaded formula gives the boxes of its split. -/
lemma LoadFormula.unload_eq_boxes_split :
    ∀ χ : LoadFormula, χ.unload = ⌈⌈χ.split.1⌉⌉χ.split.2
  | .box _ (.normal _) => by simp [LoadFormula.unload, Formula.boxes]
  | .box α (.loaded χ') => by
      have IH := LoadFormula.unload_eq_boxes_split χ'
      simp only [LoadFormula.unload, IH, LoadFormula.split, AnyFormula.split,
        Formula.boxes_cons]

/-- If the loaded formula of a sequent is on the right then the right component contains
its unloading `¬⌈⌈δ⌉⌉ψ`. -/
lemma Sequent.negBoxes_mem_right {X : Sequent} (h : X.isRightLoaded) :
    (~⌈⌈X.loadedProgs⌉⌉X.loadedFma) ∈ X.right := by
  obtain ⟨⟨χ⟩, hO⟩ := h
  obtain ⟨L, R, O⟩ := X
  simp only [Sequent.O] at hO
  subst hO
  have hu : (~⌈⌈Sequent.loadedProgs (L, R, some (Sum.inr (~'χ)))⌉⌉
        (Sequent.loadedFma (L, R, some (Sum.inr (~'χ))))) = ~χ.unload := by
    rw [LoadFormula.unload_eq_boxes_split χ]
    rfl
  rw [hu]
  simp [Sequent.right]

/-! ## The witness distance

For a state `v` and a node `x` of the quasi-tableau, `witDist M v Δ_x` is the least
`δ_x`-distance from `v` to a state satisfying `¬ψ_x`, i.e. the paper's `wd_M(v,x)` in the
case where `M, v ⊨ Δ_x, ι_x`. (In the other case the paper sets `wd_M(v,x) := ∞`; we do
not need that, because we only ever use the value under that assumption.)

Note that `witDist` does not depend on the valuation of the internal variables — this is
the paper's observation that `M` and `M'` have the same relational structure. -/

/-- The witness distance `wd_M(v,x)` of Lemma 10.7, as a function of the label `Δ_x`. -/
@[expose] noncomputable def witDist {W : Type} (M : KripkeModel W) (v : W) (Δ : Sequent) : ℕ∞ :=
  ⨅ w : {w : W // evaluate M w (~ Δ.loadedFma)}, distanceList M v w Δ.loadedProgs

lemma witDist_congr {W : Type} {M : KripkeModel W} {v : W} {Δ Y : Sequent}
    (h : Δ.loadedSplit = Y.loadedSplit) : witDist M v Δ = witDist M v Y := by
  unfold witDist Sequent.loadedFma Sequent.loadedProgs
  rw [h]

/-! ## Basic nodes between two nodes of the quasi-tableau

The paper's "there is a basic node between `x` and `z`" means: a node of type 3 with a
basic label on the path from `x` to `z`. Requiring type 3 is harmless (the label of a node
of type 1 or 2 is the label of the node of type 3 below it) and it makes the property
invariant under passing from a node of type 1 or 2 to its unique child. -/

/-- There is a node of type 3 with a basic label on the path from `x` to `z`. -/
def QuasiTab.BasicBetween (q : QuasiTab) (x z : List Nat) : Prop :=
  ∃ y Δ, x <+: y ∧ y <+: z ∧ q.typAt y = some Typ.three ∧ q.labelAt y = some Δ ∧ Δ.basic

/-- `BasicBetween` only grows when we move the left end towards the root. -/
lemma QuasiTab.BasicBetween.mono {q : QuasiTab} {x x' z : List Nat} (h : q.BasicBetween x' z)
    (hx : x <+: x') : q.BasicBetween x z := by
  obtain ⟨y, Δ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨y, Δ, hx.trans h1, h2, h3, h4, h5⟩

/-- If the left end `x` is not itself a basic node of type 3 then any basic node between
`x` and `z` is also between the child of `x` on the path to `z` and `z`. -/
lemma QuasiTab.BasicBetween.child {q : QuasiTab} {x y z : List Nat}
    (h : q.BasicBetween x z) (hy : y <+: z) (hlen : y.length = x.length + 1)
    (hx : ∀ Δ, q.typAt x = some Typ.three → q.labelAt x = some Δ → ¬ Δ.basic) :
    q.BasicBetween y z := by
  obtain ⟨b, Δ, h1, h2, h3, h4, h5⟩ := h
  refine ⟨b, Δ, ?_, h2, h3, h4, h5⟩
  have hbx : x.length < b.length := by
    rcases Nat.lt_or_ge x.length b.length with hlt | hge
    · exact hlt
    · exfalso
      have hxb : x = b := h1.eq_of_length (le_antisymm h1.length_le hge)
      subst hxb
      exact hx Δ h3 h4 h5
  exact List.prefix_of_prefix_length_le hy h2 (by omega)

/-- The node at address `x` is not a basic node of type 3, because its type is not 3. -/
lemma QuasiTab.notBasic_of_typ_ne {q : QuasiTab} {x : List Nat} {k Δ next}
    (h : q.atOpt x = some (.QNode k Δ next)) (hk : k ≠ Typ.three) :
    ∀ Y, q.typAt x = some Typ.three → q.labelAt x = some Y → ¬ Y.basic := by
  intro Y htyp _ _
  rw [QuasiTab.typAt, h] at htyp
  simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at htyp
  exact hk htyp

/-- The node at address `x` is not a basic node of type 3, because its label is not
basic. -/
lemma QuasiTab.notBasic_of_label {q : QuasiTab} {x : List Nat} {k Δ next}
    (h : q.atOpt x = some (.QNode k Δ next)) (hb : ¬ Δ.basic) :
    ∀ Y, q.typAt x = some Typ.three → q.labelAt x = some Y → ¬ Y.basic := by
  intro Y _ hlab
  rw [QuasiTab.labelAt, h] at hlab
  simp only [Option.map_some, Option.some.injEq, QuasiTab.label] at hlab
  exact hlab ▸ hb

/-- A repeat leaf is a childless node of type 1. -/
lemma QuasiTab.atOpt_of_isRepeatLeaf {q : QuasiTab} {z : List Nat} (h : q.isRepeatLeaf z) :
    ∃ Z, q.atOpt z = some (.QNode .one Z []) := by
  simp only [QuasiTab.isRepeatLeaf, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hleaf, htyp⟩, -⟩ := h
  cases hz : q.atOpt z with
  | none => rw [QuasiTab.isLeafAt, hz] at hleaf; simp at hleaf
  | some n =>
    obtain ⟨k, Z, next⟩ := n
    rw [QuasiTab.isLeafAt, hz] at hleaf
    simp only [QuasiTab.children, List.isEmpty_iff] at hleaf
    subst hleaf
    rw [QuasiTab.typAt, hz] at htyp
    simp only [Option.map_some, Option.some.injEq, QuasiTab.typ] at htyp
    subst htyp
    exact ⟨Z, rfl⟩

/-- A cycle of `y` lies below `y`. -/
lemma QuasiTab.prefix_of_mem_cycs {q : QuasiTab} {y z : List Nat} (hz : z ∈ q.cycs y) :
    y <+: z := ((q.mem_cycs_iff y z).mp hz).2.choose_spec.2.2

end PDL
