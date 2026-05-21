/-
Copyright (c) 2026 Tetsuya Ishiu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tetsuya Ishiu
-/

import LeanPool.FoZfc.Basic
import LeanPool.FoZfc.BoundedFormulaOps

/-!
# To string for LZFC.Term and LZFC.BoundedFormula

Converts terms and bounded formulas in the language `LZFC` to readable
strings, with two flavors (with and without depth information).

-/

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula
open FirstOrder.ZFC

namespace FirstOrder.ZFC

universe u v

variable {V : Type u}
variable {α : Type*}

/-- Converts a term into a string. -/
def TermToString [ToString α] {n : ℕ} (t : Language.LZFC.Term (α ⊕ Fin n)) :=
  match t with
  | Language.Term.var (Sum.inl a) => s!"fv{toString a}"
  | Language.Term.var (Sum.inr k) => s!"bv{k}"
  | _ => "error"

-- When k≥n, it returns TermToString (ts 0).
-- Probably, in that case, they go to the default value.
/-- Converts a tuple of terms into a string. -/
def TermTupleToString [ToString α] {n : ℕ} {m : ℕ}
    (ts : Fin m → Language.LZFC.Term (α ⊕ Fin n)) (k : ℕ) : String :=
  match m with
  | 0 => "error"
  | m' + 1 => TermToString (ts (Fin.ofNat (m' + 1) k))

/-- Converts a formula into a string. -/
def FormulaToString [ToString α] {n : ℕ}
    (ϕ : Language.LZFC.BoundedFormula α n) : String :=
  match ϕ with
  | Language.BoundedFormula.falsum => "⊥"
  | Language.BoundedFormula.ex ϕ1 => s!"∃'bv{n}({FormulaToString ϕ1})"
  | Language.BoundedFormula.all ϕ1 => s!"∀'bv{n}({FormulaToString ϕ1})"
  | Language.BoundedFormula.or ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ∨ {FormulaToString ϕ2}"
  | Language.BoundedFormula.and ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ∧ {FormulaToString ϕ2}"
  | ∼ϕ1 => s!"∼{FormulaToString ϕ1}"
  | Language.BoundedFormula.equal t1 t2 => s!"{TermToString t1} = {TermToString t2}"
  | Language.BoundedFormula.rel _R ts =>
      s!"{TermTupleToString ts 0} ∈ {TermTupleToString ts 1}"
  | Language.BoundedFormula.imp ϕ1 ϕ2 => s!"{FormulaToString ϕ1} ⟹ {FormulaToString ϕ2}"

/-- Converts a term into a string with depth -/
def TermToString' {n : ℕ} (t : Language.LZFC.Term (ℕ ⊕ Fin n)) :=
match t with
| Term.var (Sum.inl k) => s!"fv {n} {k}"
| Term.var (Sum.inr k) => s!"bv {n} {k}"
| _ => "error"

/-- Converts the first term of a pair into a string with depth -/
def TermPairFirstToString' {n : ℕ} {m : ℕ}
    (ts : Fin m → Language.LZFC.Term (ℕ ⊕ Fin n)) : String :=
  match m with
  | 2 => TermToString' (ts 0)
  | _ => ""

/-- Converts the second term of a pair into a string with depth -/
def TermPairSecondToString' {n : ℕ} {m : ℕ}
    (ts : Fin m → Language.LZFC.Term (ℕ ⊕ Fin n)) : String :=
  match m with
  | 2 => TermToString' (ts 1)
  | _ => ""

/-- Converts a formula into a string with depath -/
def FormulaToString' {n : ℕ} (ϕ : Language.LZFC.BoundedFormula ℕ n) : String :=
match ϕ with
| BoundedFormula.falsum => "⊥"
| BoundedFormula.ex ϕ1 => s!"∃'bv{n}({FormulaToString' ϕ1})"
| BoundedFormula.all ϕ1 => s!"∀'bv{n}({FormulaToString' ϕ1})"
| BoundedFormula.not (BoundedFormula.imp ϕ1 (BoundedFormula.not ϕ2)) =>
    s!"({FormulaToString' ϕ1} ∧ {FormulaToString' ϕ2})"
| BoundedFormula.imp (BoundedFormula.not ϕ1) ϕ2 =>
    s!"({FormulaToString' ϕ1} ∨ {FormulaToString' ϕ2})"
| ∼ϕ1 => s!"∼{FormulaToString' ϕ1}"
| BoundedFormula.equal t1 t2 => s!"{TermToString' t1} = {TermToString' t2}"
| BoundedFormula.rel _R ts =>
    s!"{TermPairFirstToString' ts} ∈ {TermPairSecondToString' ts}"
| BoundedFormula.imp ϕ1 ϕ2 => s!"({FormulaToString' ϕ1} ⟹ {FormulaToString' ϕ2})"

end FirstOrder.ZFC
