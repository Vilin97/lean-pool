/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
import LeanPool.InfinitaryLogic.Lomega1omega.Operations
/-!
# The universal and existential quantifier classes (issue #15, Unit 0)

The `∀₁`/`∃₁` classes of Harrison-Trainor–Kretschmer §2 (their hierarchy for counting quantifier
alternations in infinitary formulas), realized as a **signed quantifier traversal** on the existing
syntax:

* atomic formulas lie in **both** classes (they have no quantifier);
* an antecedent **flips** the class — `¬φ` is universal exactly when `φ` is existential;
* countable conjunctions and disjunctions **preserve** the class and are *not* counted as
  quantifiers (the source's clause 3, which is what distinguishes `∀n`/`∃n` from `Πn`/`Σn`);
* `∀` is **universal only**: in this syntax `ex φ = (φ.not.all).not`, so an existential quantifier
  *is* an `all` occurring negatively.

One `Bool`-parameterised recursion carries both classes, so their mutual dependence through negation
is definitional rather than a second induction — the same design as `Lomega1omega/Polarity.lean`,
and, as there, **no negation-normal form is constructed anywhere**.

This module is deliberately neutral: it depends only on the syntax layer and is intended to be
reused by any preservation theorem (issue #15's interpolation and relative preservation, and issue
#16's end extensions), not to live inside the interpolation development.
-/

namespace FirstOrder.Language

namespace BoundedFormulaω

variable {L : Language.{0, 0}} {α β : Type}

/-- **The signed quantifier class.**  `universalSigned true φ` says `φ` is *universal* (`∀₁`) and
`universalSigned false φ` says `φ` is *existential* (`∃₁`).  An antecedent flips the sign, the
countable connectives preserve it, and `all` is admissible only at the universal sign. -/
def universalSigned : ∀ {n : ℕ}, Bool → L.BoundedFormulaω α n → Prop
  | _, _, .falsum => True
  | _, _, .equal _ _ => True
  | _, _, .rel _ _ => True
  | _, s, .imp φ ψ => universalSigned (!s) φ ∧ universalSigned s ψ
  | _, s, .all φ => s = true ∧ universalSigned s φ
  | _, s, .iSup φs => ∀ i, universalSigned s (φs i)
  | _, s, .iInf φs => ∀ i, universalSigned s (φs i)

/-- `φ` is **universal** (`∀₁`): every quantifier occurrence is a positive `∀`. -/
abbrev IsUniversal {n : ℕ} (φ : L.BoundedFormulaω α n) : Prop := universalSigned true φ

/-- `φ` is **existential** (`∃₁`): no quantifier occurrence is a positive `∀`, i.e. every one is an
existential. -/
abbrev IsExistential {n : ℕ} (φ : L.BoundedFormulaω α n) : Prop := universalSigned false φ

/-! ## Constructor equations -/

@[simp] theorem universalSigned_falsum {n : ℕ} (s : Bool) :
    universalSigned s (BoundedFormulaω.falsum : L.BoundedFormulaω α n) := trivial



@[simp] theorem universalSigned_equal {n : ℕ} (s : Bool) (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.equal t₁ t₂) := trivial

@[simp] theorem universalSigned_rel {n l : ℕ} (s : Bool) (R : L.Relations l)
    (ts : Fin l → L.Term (α ⊕ Fin n)) :
    universalSigned s (BoundedFormulaω.rel R ts) := trivial

@[simp] theorem universalSigned_imp {n : ℕ} (s : Bool) (φ ψ : L.BoundedFormulaω α n) :
    universalSigned s (φ.imp ψ) ↔ universalSigned (!s) φ ∧ universalSigned s ψ := Iff.rfl

@[simp] theorem universalSigned_all {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α (n + 1)) :
    universalSigned s φ.all ↔ s = true ∧ universalSigned s φ := Iff.rfl

@[simp] theorem universalSigned_iSup {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iSup φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

@[simp] theorem universalSigned_iInf {n : ℕ} (s : Bool) (φs : ℕ → L.BoundedFormulaω α n) :
    universalSigned s (BoundedFormulaω.iInf φs) ↔ ∀ i, universalSigned s (φs i) := Iff.rfl

/-! ## The acceptance equations -/

/-- Negation **exchanges** the two classes. -/
@[simp] theorem universalSigned_not {n : ℕ} (s : Bool) (φ : L.BoundedFormulaω α n) :
    universalSigned s φ.not ↔ universalSigned (!s) φ := by
  show universalSigned (!s) φ ∧ universalSigned s
    (BoundedFormulaω.falsum : L.BoundedFormulaω α n) ↔ _
  simp















theorem not_isUniversal_ex {n : ℕ} (φ : L.BoundedFormulaω α (n + 1)) :
    ¬ IsUniversal φ.ex := by
  show ¬ universalSigned true (φ.not.all).not
  simp

/-! ## The derived connectives -/











/-! ## Stability under the variable operations -/

private theorem universalSigned_castLE (s : Bool) :
    ∀ {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormulaω α m),
      universalSigned s (φ.castLE h) ↔ universalSigned s φ
  | _, _, _, .falsum => Iff.rfl
  | _, _, _, .equal _ _ => Iff.rfl
  | _, _, _, .rel _ _ => Iff.rfl
  | _, _, h, .imp φ ψ => by
    show universalSigned (!s) (φ.castLE h) ∧ universalSigned s (ψ.castLE h) ↔ _
    rw [universalSigned_castLE _ h φ, universalSigned_castLE s h ψ]
    exact Iff.rfl
  | _, _, h, .all φ => by
    show s = true ∧ universalSigned s (φ.castLE (Nat.succ_le_succ h)) ↔ _
    rw [universalSigned_castLE s (Nat.succ_le_succ h) φ]
    exact Iff.rfl
  | _, _, h, .iSup φs => by
    show (∀ i, universalSigned s ((φs i).castLE h)) ↔ _
    exact forall_congr' fun i => universalSigned_castLE s h (φs i)
  | _, _, h, .iInf φs => by
    show (∀ i, universalSigned s ((φs i).castLE h)) ↔ _
    exact forall_congr' fun i => universalSigned_castLE s h (φs i)

/-- **Quantifier class is invariant under language maps.**  `mapLanguage` rewrites terms and symbol
tags only; every quantifier node is preserved, so the signed universal class is exact. -/
theorem universalSigned_mapLanguage {L' : Language.{0, 0}} (g : L →ᴸ L') (s : Bool) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      universalSigned s (φ.mapLanguage g) ↔ universalSigned s φ := by
  intro k φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    show universalSigned (!s) _ ∧ universalSigned s _ ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    show s = true ∧ universalSigned s _ ↔ _
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s

theorem universalSigned_relabel (s : Bool) (g : α → β ⊕ Fin n) :
    ∀ {k : ℕ} (φ : L.BoundedFormulaω α k),
      universalSigned s (φ.relabel g) ↔ universalSigned s φ := by
  intro k φ
  induction φ generalizing s with
  | falsum => exact Iff.rfl
  | equal => exact Iff.rfl
  | rel => exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    show universalSigned (!s) _ ∧ universalSigned s _ ↔ _
    exact and_congr (ihφ (!s)) (ihψ s)
  | all φ ih =>
    show s = true ∧ universalSigned s _ ↔ _
    rw [universalSigned_castLE]
    exact and_congr_right fun _ => ih s
  | iSup φs ih =>
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s
  | iInf φs ih =>
    show (∀ i, universalSigned s _) ↔ _
    exact forall_congr' fun i => ih i s

theorem universalSigned_subst (s : Bool) :
    ∀ {n : ℕ} (φ : L.BoundedFormulaω α n) (tf : α → L.Term β),
      universalSigned s (φ.subst tf) ↔ universalSigned s φ
  | _, .falsum, _ => Iff.rfl
  | _, .equal _ _, _ => Iff.rfl
  | _, .rel _ _, _ => Iff.rfl
  | _, .imp φ ψ, tf => by
    show universalSigned (!s) (φ.subst tf) ∧ universalSigned s (ψ.subst tf) ↔ _
    rw [universalSigned_subst _ φ tf, universalSigned_subst s ψ tf]
    exact Iff.rfl
  | _, .all φ, tf => by
    show s = true ∧ universalSigned s (φ.subst tf) ↔ _
    rw [universalSigned_subst s φ tf]
    exact Iff.rfl
  | _, .iSup φs, tf => by
    show (∀ i, universalSigned s ((φs i).subst tf)) ↔ _
    exact forall_congr' fun i => universalSigned_subst s (φs i) tf
  | _, .iInf φs, tf => by
    show (∀ i, universalSigned s ((φs i).subst tf)) ↔ _
    exact forall_congr' fun i => universalSigned_subst s (φs i) tf

end BoundedFormulaω

end FirstOrder.Language
