/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
import LeanPool.InfinitaryLogic.Util
/-!
# Semantics of `openBounds` and of relabeling by `insertLastBound`

Two semantic round-trip lemmas about the bound/free variable bookkeeping of
`Lomega1omega/Operations`, in a neutral module so that consumers below the Henkin construction and
the Scott analysis can use them without importing either:

* `realize_relabel_insertLastBound_zero` — relabeling a formula with `n + 1` free variables by
  `insertLastBound` binds the last one; evaluating with `v` and a one-element bound tuple `xs` is
  evaluating the original at `snoc v (xs 0)`;
* `realize_openBounds` — `openBounds` preserves semantics: evaluating `φ.openBounds` at a free
  assignment `xs` is evaluating `φ` with bound assignment `xs`.

Both were previously proved inside `Scott/Formula.lean` and `Methods/Henkin/Construction.lean`
respectively; the statements and names are unchanged.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {N : Type w} [L.Structure N] {n : ℕ}

open FirstOrder Structure Fin BoundedFormulaω

/-- Maps `j : Fin k` to `⟨j.val + 1, ...⟩ : Fin (1 + k)`. Used for bound variable shifting. -/
private def finSuccShift {k : ℕ} : Fin k → Fin (1 + k) :=
  fun j => ⟨j.val + 1, by omega⟩

/-- Helper lemma: the composition of `Sum.elim v xs` with `relabelAux insertLastBound k`
equals `Sum.elim (snoc v (xs 0)) (xs ∘ finSuccShift)`. This is the key for proving
semantics of relabeling for formulas with k bound variables. -/
private lemma sum_elim_relabelAux_insertLastBound {k : ℕ} (v : Fin n → N) (xs : Fin (1 + k) → N) :
    Sum.elim v xs ∘ BoundedFormulaω.relabelAux insertLastBound k =
    Sum.elim (snoc v (xs 0)) (xs ∘ finSuccShift) := by
  funext x
  cases x with
  | inl i =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inl, Sum.elim_inl,
      insertLastBound]
    split_ifs with h
    · simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, Sum.elim_inl, snoc, h, dite_true]
      congr 1
    · simp only [Equiv.sumAssoc_apply_inl_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_left]
      have hi : i = last n := by ext; simp only [last]; omega
      rw [hi, snoc_last]; rfl
  | inr j =>
    simp only [Function.comp_apply, BoundedFormulaω.relabelAux, Sum.map_inr, Sum.elim_inr]
    simp only [Equiv.sumAssoc_apply_inr, Sum.map_inr, Sum.elim_inr, finSumFinEquiv_apply_right,
      finSuccShift]
    congr 1; ext; simp only [Fin.natAdd, id_eq]; omega

/-- Helper: composition of snoc with succShift. -/
private lemma snoc_comp_succShift_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    snoc xs y ∘ finSuccShift = snoc (xs ∘ finSuccShift) y := by
  funext j
  simp only [Function.comp_apply]
  cases j using lastCases with
  | last =>
    simp only [snoc_last]
    have hsuc : finSuccShift (last k) = last (1 + k) := by
      ext; simp only [finSuccShift, last]; omega
    simp only [hsuc, snoc_last]
  | cast j' =>
    simp only [snoc_castSucc]; unfold snoc
    have hlt : (finSuccShift (castSucc j')).val < 1 + k := by simp [finSuccShift, castSucc]; omega
    simp only [hlt, dite_true]
    have heq : castLT (finSuccShift (castSucc j')) hlt = finSuccShift j' := by
      ext; simp [castLT, finSuccShift, castSucc]
    rw [heq]; rfl

/-- Helper: snoc xs y at position 0 equals xs at position 0. -/
private lemma snoc_zero_eq {k : ℕ} (xs : Fin (1 + k) → N) (y : N) :
    (snoc (α := fun _ => N) xs y) (0 : Fin (1 + k + 1)) = xs (0 : Fin (1 + k)) := by
  simp only [snoc]
  have h0 : (0 : Fin (1 + k + 1)).val < 1 + k := by simp only [Fin.val_zero]; omega
  simp only [h0, dite_true, castLT, cast_eq]
  have h_eq : (⟨(0 : Fin (1 + k + 1)).val, h0⟩ : Fin (1 + k)) = (0 : Fin (1 + k)) := by
    ext; simp only [Fin.val_zero]
  rw [h_eq]

/-- The general semantics lemma for relabeling with `insertLastBound`:
    For a formula with k bound variables, relabeling shifts the last free variable
    to bound position 0, while bound variables shift up by 1.

This handles all cases including `all`, which appears in Scott formulas due to
`forallLastVar` applications at earlier stages. -/
private theorem realize_relabel_insertLastBound {n : ℕ} :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω (Fin (n + 1)) k) (v : Fin n → N) (xs : Fin (1 + k) → N),
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) (xs ∘ finSuccShift) := by
  intro k φ
  induction φ with
  | falsum => intro v xs; simp only [relabel, realize_falsum]
  | equal t₁ t₂ =>
    intro v xs
    simp only [relabel, realize_equal, Term.realize_relabel, sum_elim_relabelAux_insertLastBound]
  | rel R ts =>
    intro v xs; simp only [relabel, realize_rel]
    have key := sum_elim_relabelAux_insertLastBound (k := _) v xs
    constructor <;> intro h <;> simp only [Term.realize_relabel, key] at h ⊢ <;> exact h
  | imp φ ψ ih_φ ih_ψ =>
    intro v xs; simp only [relabel, realize_imp]; exact Iff.imp (ih_φ v xs) (ih_ψ v xs)
  | all φ ih =>
    intro v xs; simp only [relabel, realize_all]
    constructor <;> intro hall y
    -- Use realize_castLE_self which handles any proof of n ≤ n, not just le_refl
    · specialize hall y
      rw [realize_castLE_self] at hall
      rw [ih v (snoc xs y)] at hall
      rw [snoc_zero_eq, snoc_comp_succShift_eq] at hall
      exact hall
    · rw [realize_castLE_self, ih v (snoc xs y), snoc_zero_eq, snoc_comp_succShift_eq]; exact hall y
  | iSup φs ih =>
    intro v xs; simp only [relabel, realize_iSup]; exact exists_congr (fun i => ih i v xs)
  | iInf φs ih =>
    intro v xs; simp only [relabel, realize_iInf]; exact forall_congr' (fun i => ih i v xs)

/-- The key semantics lemma for formulas with 0 bound variables: relabeling with `insertLastBound`
    shifts the last free variable to a bound variable position.

For `φ : L.Formulaω (Fin (n+1))` (a formula with n+1 free vars and 0 bound vars):
- `φ.relabel insertLastBound : L.BoundedFormulaω (Fin n) 1` has n free vars and 1 bound var
- When we evaluate with free var assignment `v : Fin n → N` and bound var assignment
  `xs : Fin 1 → N`, this corresponds to evaluating the original formula with
  `snoc v (xs 0) : Fin (n+1) → N` -/
theorem realize_relabel_insertLastBound_zero {n : ℕ} (φ : L.Formulaω (Fin (n + 1)))
    (v : Fin n → N) (xs : Fin 1 → N) :
    (φ.relabel insertLastBound).Realize v xs ↔ φ.Realize (snoc v (xs 0)) := by
  have h := realize_relabel_insertLastBound (k := 0) φ v xs
  rwa [show (xs ∘ finSuccShift : Fin 0 → N) = Fin.elim0 from Fin.eq_elim0 _] at h


/-- Term-level semantic roundtrip: evaluating a relabeled term with `Sum.elim xs Fin.elim0`
equals evaluating the original term with `Sum.elim Empty.elim xs`. -/
private theorem term_realize_openBounds {M : Type*} [L.Structure M]
    (t : L.Term (Empty ⊕ Fin n)) (xs : Fin n → M) :
    (t.relabel (Sum.elim Empty.elim Sum.inl)).realize (Sum.elim xs Fin.elim0) =
    t.realize (Sum.elim Empty.elim xs) := by
  simp only [Term.realize_relabel]
  congr 1
  funext x; rcases x with e | i
  · exact Empty.elim e
  · simp [Sum.elim, Function.comp]

/-- Helper: `snoc Fin.elim0 x` evaluated at `0 : Fin 1` gives `x`. -/
lemma snoc_elim0_zero_eq {M : Type*} (x : M) :
    (Fin.snoc (α := fun _ => M) Fin.elim0 x) (0 : Fin 1) = x :=
  congrFun (Fin.snoc_elim0_eq x) 0

/-- Semantic roundtrip: `openBounds` preserves semantics.
For `φ : BoundedFormulaω Empty n`, evaluating `openBounds φ` with free variable assignment
`xs : Fin n → M` is equivalent to evaluating `φ` with bound variable assignment `xs`. -/
theorem realize_openBounds {M : Type*} [L.Structure M] :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω Empty n) (xs : Fin n → M),
    Formulaω.Realize (φ.openBounds) xs ↔ φ.Realize Empty.elim xs := by
  intro n φ
  induction φ with
  | falsum => intro xs; rfl
  | equal t₁ t₂ =>
    intro xs
    show (t₁.relabel (Sum.elim Empty.elim Sum.inl)).realize (Sum.elim xs Fin.elim0) =
         (t₂.relabel (Sum.elim Empty.elim Sum.inl)).realize (Sum.elim xs Fin.elim0) ↔
         t₁.realize (Sum.elim Empty.elim xs) = t₂.realize (Sum.elim Empty.elim xs)
    rw [term_realize_openBounds, term_realize_openBounds]
  | rel R ts =>
    intro xs
    show (Structure.RelMap R fun i =>
         (Term.relabel (Sum.elim Empty.elim Sum.inl) (ts i)).realize (Sum.elim xs Fin.elim0)) ↔
         Structure.RelMap R fun i => (ts i).realize (Sum.elim Empty.elim xs)
    simp_rw [term_realize_openBounds]
  | imp φ ψ ihφ ihψ =>
    intro xs
    simp only [BoundedFormulaω.openBounds, Formulaω.realize_def, BoundedFormulaω.realize_imp]
    exact Iff.imp (ihφ xs) (ihψ xs)
  | iSup φs ih =>
    intro xs
    simp only [BoundedFormulaω.openBounds, Formulaω.realize_def, BoundedFormulaω.realize_iSup]
    exact exists_congr (fun i => ih i xs)
  | iInf φs ih =>
    intro xs
    simp only [BoundedFormulaω.openBounds, Formulaω.realize_def, BoundedFormulaω.realize_iInf]
    exact forall_congr' (fun i => ih i xs)
  | all φ ih =>
    intro xs
    -- `φ` is induction-bound, so it carries the inductive type and needs the qualified name
    show Formulaω.Realize (((BoundedFormulaω.openBounds φ).relabel insertLastBound).all) xs ↔
         (BoundedFormulaω.all φ).Realize Empty.elim xs
    -- `FormulaInf.Realize` is a plain definition upstream, not a reducible abbreviation, so a
    -- lemma stated at the bounded-formula level cannot be `rw`-keyed against this goal; both
    -- sides are `all`-quantified, so bridge the bodies by application instead
    refine forall_congr' fun x => ?_
    have hz : (Fin.snoc (α := fun _ => M) (default : Fin 0 → M) x) (0 : Fin 1) = x :=
      snoc_elim0_zero_eq x
    refine (realize_relabel_insertLastBound_zero (BoundedFormulaω.openBounds φ) xs
      (Fin.snoc default x)).trans ?_
    rw [hz]
    exact ih (Fin.snoc xs x)

end Language

end FirstOrder
