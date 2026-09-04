/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Methods.ConstantSupport
/-!
# Constant instances: `instConst`, `closeBy`, and their substitution algebra

The two closing operations by the auxiliary constants of `L[[ℕ]]`, in a neutral module below
both the interpolation layer and the countable-completion kernel:

* `instConst c ψ` — open the single bound variable of `ψ : BoundedFormulaω Empty 1` and substitute
  the constant `c_c`;
* `closeBy φ τ` — open all `n` bound variables of `φ : BoundedFormulaω Empty n` and substitute the
  constants `c_{τ i}`.

Their semantic consumer lemmas (`realize_instConst`, `realize_closeBy`, …) stay in the modules
that own the structures they realize in.  This module holds only syntax: the
**connective/universal** algebra of `closeBy` — how it commutes with the connectives, what the
arity-one remainder of a closed universal is, and that the constant instance of that remainder is
`closeBy` at the extended tuple.  Atomic template lemmas (closing an equality or relation template
gives `constEq` / `relInst`) belong with those atoms, above this module.

The public surface is deliberately small: `instConst`, `closeBy`, the `closeBy_*` commutations,
`closeBy_zero`, `instConst_eq_closeBy`, `instConst_closeBy_all_remainder`, and the generic
substitution laws `Term.subst_subst` / `Term.subst_relabel` / `Term.relabel_subst` /
`BoundedFormulaω.subst_subst`.  Everything else is proof scaffolding and is private.

## The `all` case

`closeBy φ.all τ` is `(remainder).all`, where the remainder is `φ` opened, relabeled so that the
last bound variable stays bound, and closed by `τ`.  The instance of that remainder at a constant
`c` must be `closeBy φ (Fin.snoc τ c)` — this is what makes universal-instance closure of a
constants-expanded universe follow from a fragment's `all_mem`.  Proving it directly fights
`castLE` inside `BoundedFormulaω.relabel`, so instead:

* a private `closeWith ρ φ` closes bound variables by a term assignment `ρ`, by structural
  recursion with **no** `relabel` of formulas; it depends on `ρ` only pointwise and composes;
* one private bridge lemma identifies `((openBounds φ).relabel g).subst τ'` with a `closeWith` for
  the standard splitting `g`, using the two relabel-composition lemmas of `Operations.lean`;
* `closeBy`, its remainder, and `instConst` are then all `closeWith`s, and
  `instConst_closeBy_all_remainder` is the composition law plus a pointwise check.
-/

universe u v u'

namespace FirstOrder.Language

open FirstOrder Structure

/-! ## Term-level substitution algebra -/

namespace Term

variable {L : Language.{u, v}} {α β γ : Type u'}

/-- Substituting after substituting is substituting the composite. -/
theorem subst_subst (t : L.Term α) (f : α → L.Term β) (g : β → L.Term γ) :
    (t.subst f).subst g = t.subst fun a => (f a).subst g := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [subst]
    congr 1; funext i; exact ih i

/-- Substituting after relabeling is substituting along the relabeling. -/
theorem subst_relabel (t : L.Term α) (f : α → β) (g : β → L.Term γ) :
    (t.relabel f).subst g = t.subst (g ∘ f) := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [relabel, subst]
    congr 1; funext i; exact ih i

/-- Relabeling after substituting is substituting the relabeled terms. -/
theorem relabel_subst (t : L.Term α) (f : α → L.Term β) (g : β → γ) :
    (t.subst f).relabel g = t.subst fun a => (f a).relabel g := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [relabel, subst]
    congr 1; funext i; exact ih i

/-- Substituting variables for themselves does nothing. -/
theorem subst_var_eq (t : L.Term α) : t.subst Term.var = t := by
  induction t with
  | var a => rfl
  | func F ts ih =>
    simp only [subst]
    congr 1; funext i; exact ih i

end Term

/-! ## Formula-level substitution composition -/

namespace BoundedFormulaω

variable {L : Language.{u, v}} {α β γ : Type u'} {n : ℕ}

/-- The bound-variable-aware term substitution used by `BoundedFormulaω.subst`, composed. -/
private theorem substAux_comp (f : α → L.Term β) (g : β → L.Term γ)
    (t : L.Term (α ⊕ Fin n)) :
    (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (Term.var ∘ Sum.inr))).subst
        (Sum.elim (Term.relabel Sum.inl ∘ g) (Term.var ∘ Sum.inr)) =
      t.subst (Sum.elim (Term.relabel Sum.inl ∘ fun a => (f a).subst g) (Term.var ∘ Sum.inr)) := by
  rw [Term.subst_subst]
  congr 1
  funext x
  rcases x with a | i
  · simp only [Sum.elim_inl, Function.comp_apply, Term.subst_relabel, Term.relabel_subst]
    rfl
  · rfl

/-- **Composition of substitutions**: substituting `f` and then `g` is substituting
`a ↦ (f a).subst g`.  No side condition: `subst` never touches bound variables. -/
theorem subst_subst : ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (f : α → L.Term β)
    (g : β → L.Term γ), (φ.subst f).subst g = φ.subst fun a => (f a).subst g
  | _, falsum, _, _ => rfl
  | _, equal t₁ t₂, f, g => by
    simp only [subst, substAux_comp]
  | _, rel R ts, f, g => by
    simp only [subst]
    congr 1; funext i; exact substAux_comp f g (ts i)
  | _, imp φ ψ, f, g => by
    simp only [subst, subst_subst φ, subst_subst ψ]
  | _, all φ, f, g => by
    simp only [subst, subst_subst φ]
  | _, iSup φs, f, g => by
    simp only [subst]
    congr 1; funext i; exact subst_subst (φs i) f g
  | _, iInf φs, f, g => by
    simp only [subst]
    congr 1; funext i; exact subst_subst (φs i) f g

end BoundedFormulaω

variable {L : Language.{0, 0}}

/-! ## The closing operations -/

/-- The constant instance `ψ(c)`: open the bound variable of `ψ` and substitute the constant
`c_c`. -/
def instConst (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) : L[[ℕ]].Sentenceω :=
  (ψ.openBounds).subst (fun _ => constTerm c)

/-- The closing substitution of a bounded formula by constants. -/
noncomputable def closeBy {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    L[[ℕ]].Sentenceω :=
  (φ.openBounds).subst (fun i => constTerm (τ i))

/-! ## Definitional commutations of `closeBy`

Each holds by unfolding `openBounds` and `subst` on the constructor.  The `all` case exhibits the
arity-one remainder explicitly; relating its `instConst` to `closeBy` at the extended parameter
tuple is a separate lemma about `openBounds`, proved where it is consumed. -/

section CloseBy

variable {n : ℕ}

@[simp]
theorem closeBy_falsum (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.falsum : L[[ℕ]].BoundedFormulaω Empty n) τ = BoundedFormulaω.falsum :=
  rfl

@[simp]
theorem closeBy_imp (φ ψ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (φ.imp ψ) τ = (closeBy φ τ).imp (closeBy ψ τ) :=
  rfl

@[simp]
theorem closeBy_not (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy φ.not τ = (closeBy φ τ).not :=
  rfl

@[simp]
theorem closeBy_iInf (φs : ℕ → L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.iInf φs) τ = BoundedFormulaω.iInf fun k => closeBy (φs k) τ :=
  rfl

@[simp]
theorem closeBy_iSup (φs : ℕ → L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy (BoundedFormulaω.iSup φs) τ = BoundedFormulaω.iSup fun k => closeBy (φs k) τ :=
  rfl

/-- The arity-one remainder of closing a universal: `closeBy φ.all τ` is the universal closure of
`φ` opened, relabeled so that the last bound variable stays bound, and closed by `τ`. -/
theorem closeBy_all (φ : L[[ℕ]].BoundedFormulaω Empty (n + 1)) (τ : Fin n → ℕ) :
    closeBy φ.all τ =
      (((φ.openBounds).relabel insertLastBound).subst fun i => constTerm (τ i)).all :=
  rfl

/-- `instConst` is `closeBy` at arity one. -/
theorem instConst_eq_closeBy (c : ℕ) (ψ : L[[ℕ]].BoundedFormulaω Empty 1) :
    instConst c ψ = closeBy ψ (fun _ => c) :=
  rfl

end CloseBy

/-! ## `closeWith`: closing bound variables by a term assignment, without relabeling formulas -/

/-- Extend a bound-variable assignment to one more bound variable, which stays bound. -/
private def extendAssign {m k : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k)) :
    Fin (m + 1) → L.Term (Empty ⊕ Fin (k + 1)) :=
  Fin.lastCases (Term.var (Sum.inr (Fin.last k)))
    (fun j => (ρ j).relabel (Sum.map id Fin.castSucc))

/-- The term action of a bound-variable assignment. -/
private def assignTerm {m k : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k)) (t : L.Term (Empty ⊕ Fin m)) :
    L.Term (Empty ⊕ Fin k) :=
  t.subst (Sum.elim (Term.var ∘ Sum.inl) ρ)

/-- **Closing by an assignment**: replace the `m` bound variables of `φ` by the terms `ρ`, which
may mention `k` bound variables that stay bound.  Purely structural: no `relabel`, no `castLE`. -/
private def closeWith : ∀ {m k : ℕ}, (Fin m → L.Term (Empty ⊕ Fin k)) → L.BoundedFormulaω Empty m →
    L.BoundedFormulaω Empty k
  | _, _, _, .falsum => .falsum
  | _, _, ρ, .equal t₁ t₂ => .equal (assignTerm ρ t₁) (assignTerm ρ t₂)
  | _, _, ρ, .rel R ts => .rel R fun i => assignTerm ρ (ts i)
  | _, _, ρ, .imp φ ψ => (closeWith ρ φ).imp (closeWith ρ ψ)
  | _, _, ρ, .all φ => (closeWith (extendAssign ρ) φ).all
  | _, _, ρ, .iSup φs => .iSup fun i => closeWith ρ (φs i)
  | _, _, ρ, .iInf φs => .iInf fun i => closeWith ρ (φs i)

private theorem extendAssign_castSucc {m k : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k)) (j : Fin m) :
    extendAssign ρ (Fin.castSucc j) = (ρ j).relabel (Sum.map id Fin.castSucc) := by
  simp [extendAssign]

private theorem extendAssign_last {m k : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k)) :
    extendAssign ρ (Fin.last m) = Term.var (Sum.inr (Fin.last k)) := by
  simp [extendAssign]

/-- `closeWith` depends on the assignment only pointwise. -/
private theorem closeWith_congr : ∀ {m k : ℕ} {ρ ρ' : Fin m → L.Term (Empty ⊕ Fin k)}
    (_ : ∀ j, ρ j = ρ' j) (φ : L.BoundedFormulaω Empty m), closeWith ρ φ = closeWith ρ' φ
  | _, _, ρ, ρ', h, .falsum => rfl
  | _, _, ρ, ρ', h, .equal t₁ t₂ => by
    have : ρ = ρ' := funext h
    subst this; rfl
  | _, _, ρ, ρ', h, .rel R ts => by
    have : ρ = ρ' := funext h
    subst this; rfl
  | _, _, ρ, ρ', h, .imp φ ψ => by
    simp only [closeWith, closeWith_congr h φ, closeWith_congr h ψ]
  | _, _, ρ, ρ', h, .all φ => by
    have : ρ = ρ' := funext h
    subst this; rfl
  | _, _, ρ, ρ', h, .iSup φs => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_congr h (φs i)
  | _, _, ρ, ρ', h, .iInf φs => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_congr h (φs i)

/-! ## Composition -/

/-- The composite assignment: first `ρ`, then `ρ'` on what stayed bound. -/
private def composeAssign {m k l : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k))
    (ρ' : Fin k → L.Term (Empty ⊕ Fin l)) : Fin m → L.Term (Empty ⊕ Fin l) :=
  fun j => (ρ j).subst (Sum.elim (Term.var ∘ Sum.inl) ρ')

private theorem assignTerm_assignTerm {m k l : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k))
    (ρ' : Fin k → L.Term (Empty ⊕ Fin l)) (t : L.Term (Empty ⊕ Fin m)) :
    assignTerm ρ' (assignTerm ρ t) = assignTerm (composeAssign ρ ρ') t := by
  unfold assignTerm composeAssign
  rw [Term.subst_subst]
  congr 1
  funext x
  rcases x with e | j
  · rfl
  · rfl

private theorem relabel_castSucc_subst {k l : ℕ} (ρ' : Fin k → L.Term (Empty ⊕ Fin l))
    (t : L.Term (Empty ⊕ Fin k)) :
    (t.relabel (Sum.map id Fin.castSucc)).subst (Sum.elim (Term.var ∘ Sum.inl) (extendAssign ρ'))
      = (t.subst (Sum.elim (Term.var ∘ Sum.inl) ρ')).relabel (Sum.map id Fin.castSucc) := by
  rw [Term.subst_relabel, Term.relabel_subst]
  congr 1
  funext x
  rcases x with e | j
  · rfl
  · simp [extendAssign_castSucc]

private theorem extendAssign_compose {m k l : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k))
    (ρ' : Fin k → L.Term (Empty ⊕ Fin l)) (j : Fin (m + 1)) :
    composeAssign (extendAssign ρ) (extendAssign ρ') j = extendAssign (composeAssign ρ ρ') j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [composeAssign, extendAssign_last]
  · simp only [composeAssign, extendAssign_castSucc]
    exact relabel_castSucc_subst ρ' (ρ j)

/-- **Composition law**: closing twice is closing by the composite assignment. -/
private theorem closeWith_closeWith : ∀ {m k l : ℕ} (ρ : Fin m → L.Term (Empty ⊕ Fin k))
    (ρ' : Fin k → L.Term (Empty ⊕ Fin l)) (φ : L.BoundedFormulaω Empty m),
    closeWith ρ' (closeWith ρ φ) = closeWith (composeAssign ρ ρ') φ
  | _, _, _, ρ, ρ', .falsum => rfl
  | _, _, _, ρ, ρ', .equal t₁ t₂ => by
    simp only [closeWith, assignTerm_assignTerm]
  | _, _, _, ρ, ρ', .rel R ts => by
    simp only [closeWith]; congr 1; funext i; exact assignTerm_assignTerm ρ ρ' (ts i)
  | _, _, _, ρ, ρ', .imp φ ψ => by
    simp only [closeWith, closeWith_closeWith ρ ρ' φ, closeWith_closeWith ρ ρ' ψ]
  | _, _, _, ρ, ρ', .all φ => by
    simp only [closeWith, closeWith_closeWith (extendAssign ρ) (extendAssign ρ') φ]
    congr 1
    exact closeWith_congr (extendAssign_compose ρ ρ') φ
  | _, _, _, ρ, ρ', .iSup φs => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_closeWith ρ ρ' (φs i)
  | _, _, _, ρ, ρ', .iInf φs => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_closeWith ρ ρ' (φs i)

/-! ## The bridge to `openBounds`

`closeBy`, `instConst`, and the arity-one remainder of `closeBy_all` are all
`((openBounds φ).relabel g).subst τ'` for a splitting `g`.  This is the one place where
`relabel` of a formula — and hence `castLE` — is met; it is discharged by the two composition
lemmas of `Operations.lean`, exactly as in `openBounds_relabel_sumInr`. -/

/-- `relabelAux g 0` on a free variable is `g`, with the bound part cast to `Fin (k + 0)`. -/
private theorem relabelAux_zero_inl {α β : Type} {k : ℕ} (g : α → β ⊕ Fin k) (a : α) :
    BoundedFormulaω.relabelAux g 0 (Sum.inl a) = Sum.map id (Fin.castAdd 0) (g a) := by
  rcases hg : g a with b | j
  · simp [BoundedFormulaω.relabelAux, hg, Equiv.sumAssoc]
  · simp [BoundedFormulaω.relabelAux, hg, Equiv.sumAssoc, finSumFinEquiv]

private theorem Term.subst_empty_eq_relabel {β : Type} (t : L.Term Empty) (f : Empty → L.Term β)
    (g : Empty → β) : t.subst f = t.relabel g := by
  induction t with
  | var e => exact e.elim
  | func F ts ih => simp only [Term.relabel, Term.subst]; congr 1; funext i; exact ih i

private theorem Term.relabel_empty_eq {β : Type} (t : L.Term Empty) (f g : Empty → β) :
    t.relabel f = t.relabel g := by
  induction t with
  | var e => exact e.elim
  | func F ts ih => simp only [Term.relabel]; congr 1; funext i; exact ih i

/-- The assignment induced by a splitting `g` and closed terms `τ'`. -/
private def splitAssign {m n k : ℕ} (g : Fin m → Fin n ⊕ Fin k) (τ' : Fin n → L.Term Empty) :
    Fin m → L.Term (Empty ⊕ Fin k) :=
  fun j => Sum.elim (Term.relabel Sum.inl ∘ τ') (Term.var ∘ Sum.inr) (g j)

private theorem term_bridge {m n k : ℕ} (g : Fin m → Fin n ⊕ Fin k) (τ' : Fin n → L.Term Empty)
    (t : L.Term (Empty ⊕ Fin m)) :
    (((t.relabel (Sum.elim Empty.elim Sum.inl : Empty ⊕ Fin m → Fin m ⊕ Fin 0)).relabel
        (BoundedFormulaω.relabelAux g 0)).subst
      (Sum.elim (Term.relabel Sum.inl ∘ τ') (Term.var ∘ Sum.inr))) =
    assignTerm (splitAssign g τ') t := by
  unfold assignTerm
  rw [Term.subst_relabel, Term.subst_relabel]
  congr 1
  funext x
  rcases x with e | j
  · exact e.elim
  · simp only [Function.comp_apply, Sum.elim_inr, relabelAux_zero_inl, splitAssign]
    rcases g j with i | j'
    · rfl
    · rfl

/-- The pointwise identity that lets the `all` case step from `k` to `k + 1`. -/
private theorem splitAssign_succ (n k : ℕ) (τ' : Fin n → L.Term Empty) (j : Fin (n + k + 1)) :
    splitAssign (fun i => finSumFinEquiv.symm i : Fin (n + k + 1) → Fin n ⊕ Fin (k + 1)) τ' j
      = extendAssign
          (splitAssign (fun i => finSumFinEquiv.symm i : Fin (n + k) → Fin n ⊕ Fin k) τ') j := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [extendAssign_last]
    simp only [splitAssign]
    have hl : (Fin.last (n + k)) = Fin.natAdd n (Fin.last k) := Fin.ext (by simp)
    rw [hl, finSumFinEquiv_symm_apply_natAdd]
    rfl
  · rw [extendAssign_castSucc]
    simp only [splitAssign]
    refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
    · have hc : Fin.castSucc (Fin.castAdd k i) = Fin.castAdd (k + 1) i := Fin.ext (by simp)
      rw [hc, finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd]
      simp only [Sum.elim_inl, Function.comp_apply, Term.relabel_relabel]
      exact Term.relabel_empty_eq _ _ _
    · have hc : Fin.castSucc (Fin.natAdd n j') = Fin.natAdd n (Fin.castSucc j') := Fin.ext (by simp)
      rw [hc, finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd]
      rfl

/-- **The bridge**: opening, relabeling by the standard splitting, and substituting is closing by
the induced assignment. -/
private theorem relabel_openBounds_subst_eq_closeWith {m : ℕ} (φ : L.BoundedFormulaω Empty m) :
    ∀ {n k : ℕ} (h : m = n + k) (τ' : Fin n → L.Term Empty),
      ((φ.openBounds).relabel
          (fun i => finSumFinEquiv.symm (Fin.cast h i) : Fin m → Fin n ⊕ Fin k)).subst τ'
        = closeWith (splitAssign (fun i => finSumFinEquiv.symm (Fin.cast h i)) τ') φ := by
  induction φ with
  | falsum => intro n k h τ'; rfl
  | equal t₁ t₂ =>
    intro n k h τ'
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith]
    rw [term_bridge, term_bridge]
  | rel R ts =>
    intro n k h τ'
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith]
    congr 1; funext i; exact term_bridge _ _ (ts i)
  | imp φ ψ ihφ ihψ =>
    intro n k h τ'
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith, ihφ h τ', ihψ h τ']
  | all φ ih =>
    intro n k h τ'
    subst h
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith, Fin.cast_eq_self, BoundedFormulaω.castLE_self]
    congr 1
    have comp := BoundedFormulaω.relabel_insertLastBound_comp_finSumFinEquiv n k
      (BoundedFormulaω.openBounds φ)
    simp only [BoundedFormulaω.castLE_self] at comp
    rw [comp]
    have this := ih (n := n) (k := k + 1) rfl τ'
    simp only [Fin.cast_eq_self] at this
    rw [this]
    exact closeWith_congr (splitAssign_succ n k τ') φ
  | iSup φs ih =>
    intro n k h τ'
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith]
    congr 1; funext i; exact ih i h τ'
  | iInf φs ih =>
    intro n k h τ'
    simp only [BoundedFormulaω.openBounds, BoundedFormulaω.relabel, BoundedFormulaω.subst,
      closeWith]
    congr 1; funext i; exact ih i h τ'

/-! ## `closeBy`, its arity-one remainder, and `instConst`, as `closeWith` -/

/-- The assignment closing every bound variable by the constants `τ`. -/
private def constAssign {n : ℕ} (τ : Fin n → ℕ) : Fin n → L[[ℕ]].Term (Empty ⊕ Fin 0) :=
  fun j => (constTerm (τ j)).relabel Sum.inl

/-- `closeBy` closes every variable by its constant. -/
private theorem closeBy_eq_closeWith {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty n) (τ : Fin n → ℕ) :
    closeBy φ τ = closeWith (constAssign τ) φ := by
  have h := relabel_openBounds_subst_eq_closeWith φ (n := n) (k := 0) rfl
    (fun i => constTerm (τ i))
  simp only [Fin.cast_eq_self] at h
  have h0 := BoundedFormulaω.relabel_finSumFinEquiv_symm_zero (BoundedFormulaω.openBounds φ)
  erw [h0] at h
  rw [closeBy, h]
  refine closeWith_congr (fun j => ?_) φ
  simp only [splitAssign, constAssign]
  have hj : (j : Fin (n + 0)) = Fin.castAdd 0 j := Fin.ext rfl
  rw [hj, finSumFinEquiv_symm_apply_castAdd]
  rfl

/-- The assignment closing the first `n` variables by constants and keeping the last bound. -/
private def constAssignSucc {n : ℕ} (τ : Fin n → ℕ) : Fin (n + 1) → L[[ℕ]].Term (Empty ⊕ Fin 1) :=
  Fin.lastCases (Term.var (Sum.inr 0)) (fun j => (constTerm (τ j)).relabel Sum.inl)

/-- The arity-one remainder of `closeBy_all` is `closeWith` by `constAssignSucc`. -/
private theorem closeBy_all_remainder_eq_closeWith {n : ℕ}
    (φ : L[[ℕ]].BoundedFormulaω Empty (n + 1)) (τ : Fin n → ℕ) :
    ((φ.openBounds).relabel insertLastBound).subst (fun i => constTerm (τ i))
      = closeWith (constAssignSucc τ) φ := by
  have h := relabel_openBounds_subst_eq_closeWith φ (n := n) (k := 1) rfl
    (fun i => constTerm (τ i))
  simp only [Fin.cast_eq_self] at h
  rw [BoundedFormulaω.insertLastBound_eq_finSumFinEquiv_symm, h]
  refine closeWith_congr (fun j => ?_) φ
  simp only [splitAssign, constAssignSucc]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have hl : (Fin.last n) = Fin.natAdd n (0 : Fin 1) := Fin.ext (by simp)
    conv_lhs => rw [hl, finSumFinEquiv_symm_apply_natAdd]
    simp [Fin.lastCases_last]
  · have hc : (Fin.castSucc j) = Fin.castAdd 1 j := rfl
    conv_lhs => rw [hc, finSumFinEquiv_symm_apply_castAdd]
    simp [Fin.lastCases_castSucc]

/-- Closing by the identity assignment does nothing. -/
private theorem closeWith_id : ∀ {m : ℕ} (φ : L.BoundedFormulaω Empty m)
    (ρ : Fin m → L.Term (Empty ⊕ Fin m)) (_ : ∀ j, ρ j = Term.var (Sum.inr j)),
    closeWith ρ φ = φ
  | _, .falsum, _, _ => rfl
  | _, .equal t₁ t₂, ρ, h => by
    have hρ : Sum.elim (Term.var ∘ Sum.inl) ρ = Term.var := by
      funext x; rcases x with e | j
      · rfl
      · exact h j
    simp only [closeWith, assignTerm, hρ, Term.subst_var_eq]
  | _, .rel R ts, ρ, h => by
    have hρ : Sum.elim (Term.var ∘ Sum.inl) ρ = Term.var := by
      funext x; rcases x with e | j
      · rfl
      · exact h j
    simp only [closeWith, assignTerm, hρ, Term.subst_var_eq]
  | _, .imp φ ψ, ρ, h => by
    simp only [closeWith, closeWith_id φ ρ h, closeWith_id ψ ρ h]
  | _, .all φ, ρ, h => by
    simp only [closeWith]
    congr 1
    refine closeWith_id φ _ fun j => ?_
    refine Fin.lastCases ?_ (fun j => ?_) j
    · exact extendAssign_last ρ
    · rw [extendAssign_castSucc, h j]; rfl
  | _, .iSup φs, ρ, h => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_id (φs i) ρ h
  | _, .iInf φs, ρ, h => by
    simp only [closeWith]; congr 1; funext i; exact closeWith_id (φs i) ρ h

/-- Closing a sentence by the empty tuple does nothing. -/
theorem closeBy_zero (φ : L[[ℕ]].Sentenceω) (τ : Fin 0 → ℕ) : closeBy φ τ = φ := by
  rw [closeBy_eq_closeWith]
  exact closeWith_id φ _ fun j => j.elim0

/-- **The instance of the remainder is the closure at the extended tuple.** -/
theorem instConst_closeBy_all_remainder {n : ℕ} (φ : L[[ℕ]].BoundedFormulaω Empty (n + 1))
    (τ : Fin n → ℕ) (c : ℕ) :
    instConst c (((φ.openBounds).relabel insertLastBound).subst fun i => constTerm (τ i))
      = closeBy φ (Fin.snoc τ c) := by
  rw [instConst_eq_closeBy, closeBy_all_remainder_eq_closeWith, closeBy_eq_closeWith,
    closeBy_eq_closeWith, closeWith_closeWith]
  refine closeWith_congr (fun j => ?_) φ
  simp only [composeAssign, constAssign, constAssignSucc]
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Fin.snoc_last, constAssign]
  · simp only [Fin.lastCases_castSucc, Fin.snoc_castSucc]
    rw [Term.subst_relabel]
    exact Term.subst_empty_eq_relabel _ _ _

end FirstOrder.Language
