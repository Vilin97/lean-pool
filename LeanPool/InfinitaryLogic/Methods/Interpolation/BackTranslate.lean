/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.Interpolation.Relationalize
/-!
# Back-translation from the graph language (Craig Layer 3, Unit 6)

The translation back into `L`: `G_f(xs, y) ↦ f(xs) = y`, base relation atoms recover the
original relations, and — separately — **native equality stays equality** after term erasure
(a relational interpolant may introduce equality even when no `G_f` occurs, and its
back-translation then correctly uses no function symbol).

Everything here holds for **every** `L`-structure over its graph expansion — no symbol set,
graph axioms, choice, or reconstruction enters.

## Main Results

* `realize_backTranslateFormula` — over the graph expansion, the back-translation realizes
  exactly as the graph-language formula.
* `functionsIn_backTranslateFormula` / `relationsIn_backTranslateFormula` — the **exact**
  occurrence identities in preimage form: the back-translation's function symbols are
  `graphRelSym L ⁻¹' θ.relationsIn`, its relation symbols `baseRelSym L ⁻¹' θ.relationsIn`.
* `functionsIn_backTranslate_subset` / `relationsIn_backTranslate_subset` — the two
  consumer lemmas Unit 7 wants: an interpolant with `relationsIn ⊆ relSym L F R` back-translates
  with function symbols in `F` and relation symbols in `R` (via the embeddings' injectivity and
  cross-disjointness; no Sigma bookkeeping leaks to the Craig endpoint).
* `realize_backTranslate_relationalize` — acceptance corollary: back-translating a
  relationalization is semantically the original formula (no syntactic identity claimed).
-/

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}} {α : Type}

/-! ## Term erasure -/

/-- Erase a graph-language term to an `L`-term: the graph language has no function symbols, so
this is variable-preserving with the function case impossible. -/
def ungraphTerm {β : Type*} : (graphLanguage L).Term β → L.Term β
  | .var z => .var z
  | .func f _ => isEmptyElim f

@[simp] theorem realize_ungraphTerm {M : Type} [L.Structure M]
    (S : (graphLanguage L).Structure M) {β : Type*} (t : (graphLanguage L).Term β)
    (env : β → M) :
    (ungraphTerm t).realize env = @Term.realize (graphLanguage L) M S β env t := by
  cases t with
  | var z => rfl
  | func f ts => exact isEmptyElim f

@[simp] theorem functionsIn_ungraphTerm_eq_empty (t : (graphLanguage L).Term α) :
    (ungraphTerm t).functionsIn = ∅ := by
  cases t with
  | var z => rfl
  | func f ts => exact isEmptyElim f

/-! ## The back-translation -/

/-- Back-translate a graph-language formula to `L`: native equality stays equality (after term
erasure), a base atom recovers the original relation, a graph atom `G_f(xs, y)` becomes
`f(xs) = y`, and all connectives and quantifiers are structural. -/
def backTranslateFormula : ∀ {n : ℕ}, (graphLanguage L).BoundedFormulaω α n →
    L.BoundedFormulaω α n
  | _, .falsum => .falsum
  | _, .equal t u => .equal (ungraphTerm t) (ungraphTerm u)
  | _, .rel (GraphRelation.base R₀) ts => .rel R₀ fun i => ungraphTerm (ts i)
  | _, .rel (GraphRelation.graph f) ts =>
    .equal (Term.func f (Fin.init fun i => ungraphTerm (ts i)))
      (ungraphTerm (ts (Fin.last _)))
  | _, .imp φ ψ => (backTranslateFormula φ).imp (backTranslateFormula ψ)
  | _, .all φ => (backTranslateFormula φ).all
  | _, .iSup φs => .iSup fun i => backTranslateFormula (φs i)
  | _, .iInf φs => .iInf fun i => backTranslateFormula (φs i)

/-! ## Semantics over the graph expansion -/

section Semantics

variable {M : Type} [L.Structure M]

/-- **The back-translation semantics**: over the graph expansion of any `L`-structure, the
back-translation realizes exactly as the graph-language formula. No symbol set, graph axioms,
choice, or reconstruction. -/
theorem realize_backTranslateFormula :
    ∀ {n : ℕ} (θ : (graphLanguage L).BoundedFormulaω α n) (v : α → M) (xs : Fin n → M),
      (backTranslateFormula θ).Realize v xs ↔
        @BoundedFormulaω.Realize (graphLanguage L) M (graphExpansion L M) α n θ v xs
  | _, .falsum, _, _ => Iff.rfl
  | _, .equal t u, v, xs => by
    change (ungraphTerm t).realize _ = (ungraphTerm u).realize _ ↔ _
    rw [realize_ungraphTerm (graphExpansion L M) t, realize_ungraphTerm (graphExpansion L M) u]
    exact Iff.rfl
  | _, .rel (GraphRelation.base R₀) ts, v, xs => by
    change RelMap R₀ _ ↔ (graphExpansion L M).RelMap (GraphRelation.base R₀) _
    rw [graphExpansion_relMap_base]
    rw [show (fun i => @Term.realize (graphLanguage L) M (graphExpansion L M) _
        (Sum.elim v xs) (ts i)) = fun i => (ungraphTerm (ts i)).realize (Sum.elim v xs) from
      funext fun i => (realize_ungraphTerm (graphExpansion L M) (ts i) _).symm]
  | _, .rel (GraphRelation.graph f) ts, v, xs => by
    have hinit : (fun i => Term.realize (Sum.elim v xs)
        ((Fin.init fun j => ungraphTerm (ts j)) i)) =
        Fin.init (fun j => @Term.realize (graphLanguage L) M (graphExpansion L M) _
          (Sum.elim v xs) (ts j)) :=
      funext fun i => realize_ungraphTerm (graphExpansion L M) (ts (Fin.castSucc i)) _
    have hL : (backTranslateFormula (.rel (GraphRelation.graph f) ts)).Realize v xs ↔
        (funMap f (Fin.init fun j => @Term.realize (graphLanguage L) M (graphExpansion L M) _
            (Sum.elim v xs) (ts j)) =
          @Term.realize (graphLanguage L) M (graphExpansion L M) _
            (Sum.elim v xs) (ts (Fin.last _))) := by
      change (Term.func f (Fin.init fun i => ungraphTerm (ts i))).realize (Sum.elim v xs) =
          (ungraphTerm (ts (Fin.last _))).realize (Sum.elim v xs) ↔ _
      rw [Term.realize_func, hinit,
        realize_ungraphTerm (graphExpansion L M) (ts (Fin.last _))]
    rw [hL]
    change _ ↔ (graphExpansion L M).RelMap (GraphRelation.graph f) fun i =>
      @Term.realize (graphLanguage L) M (graphExpansion L M) _ (Sum.elim v xs) (ts i)
    rw [graphExpansion_relMap_graph]
  | _, .imp φ ψ, v, xs =>
    -- apply the recursive call rather than rewriting with it: the statement is through the
    -- reducible `BoundedFormulaω.Realize` alias, which `rw` cannot key against the unfolded goal
    imp_congr (realize_backTranslateFormula φ v xs) (realize_backTranslateFormula ψ v xs)
  | _, .all φ, v, xs =>
    forall_congr' fun x => realize_backTranslateFormula φ v (Fin.snoc xs x)
  | _, .iSup φs, v, xs => exists_congr fun i => realize_backTranslateFormula (φs i) v xs
  | _, .iInf φs, v, xs => forall_congr' fun i => realize_backTranslateFormula (φs i) v xs

end Semantics

/-! ## The exact occurrence identities, in preimage form -/

/-- The back-translation's function symbols are exactly the `graphRelSym`-preimage of the
formula's relation symbols (native equality contributes nothing — term erasure is
function-free). -/
private theorem functionsIn_backTranslateFormula :
    ∀ {n : ℕ} (θ : (graphLanguage L).BoundedFormulaω α n),
      (backTranslateFormula θ).functionsIn = graphRelSym L ⁻¹' θ.relationsIn
  | _, .falsum => (Set.preimage_empty).symm
  | _, .equal t u => by
    change (ungraphTerm t).functionsIn ∪ (ungraphTerm u).functionsIn = graphRelSym L ⁻¹' ∅
    rw [functionsIn_ungraphTerm_eq_empty, functionsIn_ungraphTerm_eq_empty,
      Set.union_empty, Set.preimage_empty]
  | _, .rel (GraphRelation.base R₀) ts => by
    change (⋃ i, (ungraphTerm (ts i)).functionsIn) = graphRelSym L ⁻¹' {baseRelSym L ⟨_, R₀⟩}
    rw [graphRelSym_preimage_base_singleton]
    simp [functionsIn_ungraphTerm_eq_empty]
  | _, .rel (GraphRelation.graph f) ts => by
    change insert (⟨_, f⟩ : Σ n, L.Functions n) (⋃ i, (ungraphTerm _).functionsIn) ∪
        (ungraphTerm (ts (Fin.last _))).functionsIn =
      graphRelSym L ⁻¹' {graphRelSym L ⟨_, f⟩}
    rw [graphRelSym_preimage_graph_singleton, functionsIn_ungraphTerm_eq_empty, Set.union_empty]
    simp [functionsIn_ungraphTerm_eq_empty]
  | _, .imp φ ψ => by
    change (backTranslateFormula φ).functionsIn ∪ (backTranslateFormula ψ).functionsIn = _
    rw [functionsIn_backTranslateFormula φ, functionsIn_backTranslateFormula ψ,
      ← Set.preimage_union]
    rfl
  | _, .all φ => functionsIn_backTranslateFormula φ
  | _, .iSup φs => by
    change (⋃ i, (backTranslateFormula (φs i)).functionsIn) = _
    rw [Set.iUnion_congr fun i => functionsIn_backTranslateFormula (φs i),
      ← Set.preimage_iUnion]
    rfl
  | _, .iInf φs => by
    change (⋃ i, (backTranslateFormula (φs i)).functionsIn) = _
    rw [Set.iUnion_congr fun i => functionsIn_backTranslateFormula (φs i),
      ← Set.preimage_iUnion]
    rfl

/-- The back-translation's relation symbols are exactly the `baseRelSym`-preimage of the
formula's relation symbols. -/
private theorem relationsIn_backTranslateFormula :
    ∀ {n : ℕ} (θ : (graphLanguage L).BoundedFormulaω α n),
      (backTranslateFormula θ).relationsIn = baseRelSym L ⁻¹' θ.relationsIn
  | _, .falsum => (Set.preimage_empty).symm
  | _, .equal t u => (Set.preimage_empty).symm
  | _, .rel (GraphRelation.base R₀) ts => by
    change {(⟨_, R₀⟩ : Σ n, L.Relations n)} = baseRelSym L ⁻¹' {baseRelSym L ⟨_, R₀⟩}
    rw [baseRelSym_preimage_base_singleton]
  | _, .rel (GraphRelation.graph f) ts => by
    change (∅ : Set (Σ n, L.Relations n)) = baseRelSym L ⁻¹' {graphRelSym L ⟨_, f⟩}
    rw [baseRelSym_preimage_graph_singleton]
  | _, .imp φ ψ => by
    change (backTranslateFormula φ).relationsIn ∪ (backTranslateFormula ψ).relationsIn = _
    rw [relationsIn_backTranslateFormula φ, relationsIn_backTranslateFormula ψ,
      ← Set.preimage_union]
    rfl
  | _, .all φ => relationsIn_backTranslateFormula φ
  | _, .iSup φs => by
    change (⋃ i, (backTranslateFormula (φs i)).relationsIn) = _
    rw [Set.iUnion_congr fun i => relationsIn_backTranslateFormula (φs i),
      ← Set.preimage_iUnion]
    rfl
  | _, .iInf φs => by
    change (⋃ i, (backTranslateFormula (φs i)).relationsIn) = _
    rw [Set.iUnion_congr fun i => relationsIn_backTranslateFormula (φs i),
      ← Set.preimage_iUnion]
    rfl

/-! ## The consumer lemmas for the Craig assembly (Unit 7) -/

/-- An interpolant whose relation symbols lie in `relSym L F R` back-translates with function
symbols in `F`. -/
theorem functionsIn_backTranslate_subset {n : ℕ} {θ : (graphLanguage L).BoundedFormulaω α n}
    {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    (h : θ.relationsIn ⊆ relSym L F R) :
    (backTranslateFormula θ).functionsIn ⊆ F := by
  rw [functionsIn_backTranslateFormula]
  intro q hq
  rcases h hq with ⟨p, _, heq⟩ | ⟨p, hp, heq⟩
  · exact absurd heq (baseRelSym_ne_graphRelSym p q)
  · exact graphRelSym_injective heq ▸ hp

/-- An interpolant whose relation symbols lie in `relSym L F R` back-translates with relation
symbols in `R`. -/
theorem relationsIn_backTranslate_subset {n : ℕ} {θ : (graphLanguage L).BoundedFormulaω α n}
    {F : Set (Σ n, L.Functions n)} {R : Set (Σ n, L.Relations n)}
    (h : θ.relationsIn ⊆ relSym L F R) :
    (backTranslateFormula θ).relationsIn ⊆ R := by
  rw [relationsIn_backTranslateFormula]
  intro q hq
  rcases h hq with ⟨p, hp, heq⟩ | ⟨p, _, heq⟩
  · exact baseRelSym_injective heq ▸ hp
  · exact absurd heq.symm (baseRelSym_ne_graphRelSym q p)

end FirstOrder.Language
