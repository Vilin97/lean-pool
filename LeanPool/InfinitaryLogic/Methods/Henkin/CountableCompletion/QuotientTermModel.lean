/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.ConsistencyPropertyEqOn
import LeanPool.InfinitaryLogic.Methods.Henkin.CountableCompletion.GeneratedUniverse
/-!
# The quotient term model and its atomic semantics (issue #8, commit 5a)

From a Henkin-complete set `S` (the output of commit 4b's `exists_henkinComplete_of_root`) over the
relational core `L[[ℕ]]`, this file builds the **closed-term quotient model** and establishes its
atomic semantics — everything the forward truth lemma (commit 5b) needs *below* formula induction.

Over a relational base every closed `L[[ℕ]]`-term collapses to a constant (`exists_eq_constTerm`),
so the equality relation on closed terms is the constant equality `constEq · · ∈ S`, and the
`HenkinComplete` atomic fields (`eq_refl`/`eq_symm`/`eq_trans`, `rel_congr`) supply exactly the
constant-specialized equality and congruence laws.

## Acceptance lemmas

* `qRel_equiv`: the equality-membership relation on closed terms is an equivalence.
* `qmk_eq_iff` / `qmk_constTerm_eq_iff`: `mk t = mk u` iff the collapsed constants are `S`-equal.
* `relInst_congr` / `relInst_congr_iff`: relation membership is invariant, coordinatewise, under
  `S`-equal arguments — the iterated tuple congruence, with the iff via equality symmetry.
* `qModelStructure`: the `L[[ℕ]]`-structure; `RelMap` on quotient tuples is well-defined by
  construction.
* `qterm_realize_eq_mk`: a closed term evaluates to its own quotient class.
* Positive/negative atomic realization: `qmk_eq_of_mem` / `qmk_ne_of_neg_mem` (equality) and
  `relMap_of_mem` / `not_relMap_of_neg_mem` (relations). The negative lemmas *reflect* through the
  representatives chosen by the quotient relation map (`relMap_qmk_iff`) and close with `C0`
  (`no_contradiction`) — not by any decisiveness or maximality of `S`.

**These atomic biconditionals are legitimate** — they follow from the quotient definition, atomic
congruence, and `C0` alone. There is no `M ⊨ φ ↔ φ ∈ S` for arbitrary `φ`.
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} [L.IsRelational] {U S : Set L[[ℕ]].Sentenceω}

/-! ## The relational collapse of closed terms -/

/-- The constant a closed term collapses to over the relational core. -/
noncomputable def qtConst (t : L[[ℕ]].Term Empty) : ℕ := (exists_eq_constTerm t).choose

theorem eq_constTerm_qtConst (t : L[[ℕ]].Term Empty) : t = constTerm (qtConst t) :=
  (exists_eq_constTerm t).choose_spec

omit [L.IsRelational] in
theorem constTerm_injective {a b : ℕ}
    (h : (constTerm (L' := L) (J := ℕ) a) = constTerm b) : a = b := by
  simp only [constTerm] at h
  -- `Term.func.injEq` cannot fire: the goal spells the head symbol as `Sum.inr a`, typed
  -- `(constantsOn ℕ).Functions 0`, so it is not type-correct at `implicit` transparency.
  injection h with _ hf _
  exact Sum.inr.inj hf

theorem qtConst_constTerm (c : ℕ) : qtConst (constTerm (L' := L) (J := ℕ) c) = c :=
  constTerm_injective (eq_constTerm_qtConst (constTerm c)).symm

/-! ## The quotient carrier -/

/-- The equality relation on closed terms: their collapsed constants are `S`-equal. -/
def qRel (t u : L[[ℕ]].Term Empty) : Prop := constEq (L := L) (qtConst t) (qtConst u) ∈ S

/-- The equality relation is an equivalence (from the atomic equality fields of `S`). -/
theorem qRel_equiv (hsc : HenkinComplete U S) : Equivalence (qRel (L := L) (S := S)) where
  refl t := HenkinComplete.eq_refl hsc (qtConst t)
  symm {_ _} h := HenkinComplete.eq_symm hsc _ _ h
  trans {_ _ _} h1 h2 := HenkinComplete.eq_trans hsc _ _ _ h1 h2

/-- The setoid on closed terms. -/
def qSetoid (hsc : HenkinComplete U S) : Setoid (L[[ℕ]].Term Empty) :=
  ⟨qRel (S := S), qRel_equiv hsc⟩

/-- The quotient term model. -/
def QModel (hsc : HenkinComplete U S) := Quotient (qSetoid hsc)

/-- The class of a closed term. -/
def qmk (hsc : HenkinComplete U S) (t : L[[ℕ]].Term Empty) : QModel hsc :=
  Quotient.mk (qSetoid hsc) t

theorem qmk_eq_iff (hsc : HenkinComplete U S) (t u : L[[ℕ]].Term Empty) :
    qmk hsc t = qmk hsc u ↔ constEq (qtConst t) (qtConst u) ∈ S :=
  Quotient.eq (r := qSetoid hsc)

theorem qmk_constTerm_eq_iff (hsc : HenkinComplete U S) (a b : ℕ) :
    qmk hsc (constTerm a) = qmk hsc (constTerm b) ↔ constEq a b ∈ S := by
  rw [qmk_eq_iff, qtConst_constTerm, qtConst_constTerm]

/-! ## Iterated tuple congruence for relation instances -/

omit [L.IsRelational] in
/-- **Coordinatewise relation congruence**: `S`-equal argument tuples give the same relation
membership. Iterates the atomic one-coordinate congruence `HenkinComplete.rel_congr`. -/
theorem relInst_congr (hsc : HenkinComplete U S) {l : ℕ} (R : L.Relations l) (g g' : Fin l → ℕ)
    (h : ∀ i, constEq (g i) (g' i) ∈ S) (hg : relInst R g ∈ S) : relInst R g' ∈ S := by
  suffices H : ∀ k : ℕ, relInst R (fun i : Fin l => if (i : ℕ) < k then g' i else g i) ∈ S by
    have hl := H l
    simpa using hl
  intro k
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    by_cases hk : k < l
    · have key := HenkinComplete.rel_congr hsc l R
        (fun i : Fin l => if (i : ℕ) < k then g' i else g i) ⟨k, hk⟩ (g' ⟨k, hk⟩) ih
        (by simpa using h ⟨k, hk⟩)
      have hupd : Function.update (fun i : Fin l => if (i : ℕ) < k then g' i else g i)
            (⟨k, hk⟩ : Fin l) (g' ⟨k, hk⟩)
            = (fun i : Fin l => if (i : ℕ) < k + 1 then g' i else g i) := by
        funext i
        by_cases hik : i = ⟨k, hk⟩
        · subst hik; simp
        · rw [Function.update_of_ne hik]
          have hne : (i : ℕ) ≠ k := fun hc => hik (Fin.ext hc)
          by_cases hlt : (i : ℕ) < k
          · rw [ite_eq_left hlt, ite_eq_left (by omega)]
          · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      rw [hupd] at key
      exact key
    · have hstep : (fun i : Fin l => if (i : ℕ) < k + 1 then g' i else g i)
          = (fun i : Fin l => if (i : ℕ) < k then g' i else g i) := by
        funext i
        have hil : (i : ℕ) < l := i.2
        by_cases hlt : (i : ℕ) < k
        · rw [ite_eq_left hlt, ite_eq_left (by omega)]
        · rw [ite_eq_right hlt, ite_eq_right (by omega)]
      rw [hstep]; exact ih

omit [L.IsRelational] in
/-- The tuple congruence as an iff (using equality symmetry for the reverse). -/
theorem relInst_congr_iff (hsc : HenkinComplete U S) {l : ℕ} (R : L.Relations l) (g g' : Fin l → ℕ)
    (h : ∀ i, constEq (g i) (g' i) ∈ S) : relInst R g ∈ S ↔ relInst R g' ∈ S :=
  ⟨relInst_congr hsc R g g' h,
    relInst_congr hsc R g' g fun i => HenkinComplete.eq_symm hsc _ _ (h i)⟩

/-! ## The `L[[ℕ]]`-structure on the quotient -/

instance qfuncSuccIsEmpty (n : ℕ) : IsEmpty (L[[ℕ]].Functions (n + 1)) := by
  have : IsEmpty (L.Functions (n + 1)) := ‹L.IsRelational› (n + 1)
  have : IsEmpty ((constantsOn ℕ).Functions (n + 1)) := isEmpty_functions_constantsOn_succ
  exact instIsEmptySum

/-- The quotient term model as an `L[[ℕ]]`-structure. Function interpretation is the constant
embedding (higher arities are empty over the relational core); `RelMap` on a quotient tuple holds
iff some constant representatives make the atomic relation instance a member of `S`. -/
noncomputable instance qModelStructure (hsc : HenkinComplete U S) :
    L[[ℕ]].Structure (QModel hsc) where
  funMap {n} f _ :=
    match n, f with
    | 0, f => qmk hsc (Term.func f Fin.elim0)
    | (_ + 1), f => isEmptyElim f
  RelMap {n} R ts := ∃ g : Fin n → ℕ,
    (∀ i, ts i = qmk hsc (constTerm (g i))) ∧
    BoundedFormulaω.rel R (fun i => constTermS (g i)) ∈ S

/-- **Closed-term evaluation is its quotient class.** -/
theorem qterm_realize_eq_mk (hsc : HenkinComplete U S) (t : L[[ℕ]].Term Empty) :
    @Term.realize L[[ℕ]] (QModel hsc) (qModelStructure hsc) Empty Empty.elim t = qmk hsc t := by
  obtain ⟨c, rfl⟩ := exists_eq_constTerm t
  show @Structure.funMap L[[ℕ]] (QModel hsc) (qModelStructure hsc) 0 (Sum.inr c) _
    = qmk hsc (constTerm c)
  rfl

/-! ## Positive and negative atomic realization -/

/-- **`RelMap` of a constant tuple reflects to atomic membership.** Forward reflects through the
representatives chosen by the relation map (via the tuple congruence); backward is the identity
representative. -/
theorem relMap_qmk_iff (hsc : HenkinComplete U S) {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ) :
    (qModelStructure hsc).RelMap (Sum.inl R) (fun i => qmk hsc (constTerm (g i)))
      ↔ relInst R g ∈ S := by
  constructor
  · rintro ⟨g', hqmk, hmem⟩
    have hcong : ∀ i, constEq (g i) (g' i) ∈ S :=
      fun i => (qmk_constTerm_eq_iff hsc _ _).mp (hqmk i)
    exact (relInst_congr_iff hsc R g' g
      fun i => HenkinComplete.eq_symm hsc _ _ (hcong i)).mp hmem
  · intro hmem
    exact ⟨g, fun _ => rfl, hmem⟩

/-- **Positive atomic (equality).** -/
theorem qmk_eq_of_mem (hsc : HenkinComplete U S) (a b : ℕ) (hmem : constEq a b ∈ S) :
    qmk hsc (constTerm a) = qmk hsc (constTerm b) :=
  (qmk_constTerm_eq_iff hsc a b).mpr hmem

/-- **Negative atomic (equality).** Closes with `C0` — not maximality. -/
theorem qmk_ne_of_neg_mem (hsc : HenkinComplete U S) (a b : ℕ)
    (hmem : (constEq a b).not ∈ S) :
    qmk hsc (constTerm a) ≠ qmk hsc (constTerm b) := fun heq =>
  HenkinComplete.no_contradiction hsc (constEq a b)
    ⟨(qmk_constTerm_eq_iff hsc a b).mp heq, hmem⟩

/-- **Positive atomic (relation).** -/
theorem relMap_of_mem (hsc : HenkinComplete U S) {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ)
    (hmem : relInst R g ∈ S) :
    (qModelStructure hsc).RelMap (Sum.inl R) (fun i => qmk hsc (constTerm (g i))) :=
  (relMap_qmk_iff hsc R g).mpr hmem

/-- **Negative atomic (relation).** Reflects through the relation map's chosen representatives, then
closes with `C0` — not maximality. -/
theorem not_relMap_of_neg_mem (hsc : HenkinComplete U S) {l : ℕ} (R : L.Relations l) (g : Fin l → ℕ)
    (hmem : (relInst R g).not ∈ S) :
    ¬ (qModelStructure hsc).RelMap (Sum.inl R) (fun i => qmk hsc (constTerm (g i))) := fun hrel =>
  HenkinComplete.no_contradiction hsc (relInst R g) ⟨(relMap_qmk_iff hsc R g).mp hrel, hmem⟩

end FirstOrder.Language
