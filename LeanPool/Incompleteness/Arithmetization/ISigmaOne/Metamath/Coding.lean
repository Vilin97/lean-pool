/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Formula.Typed
import LeanPool.Incompleteness.Arithmetization.Definability.Absoluteness
import Mathlib.Combinatorics.Colex

/-! # Coding -/


namespace LO
namespace FirstOrder

variable {L : Language}

variable {ξ : Type*}

open Encodable

namespace Semiterm

variable [Encodable ξ] [(k : ℕ) → Encodable (L.Func k)]

lemma encode_eq_toNat (t : Semiterm L ξ n) : Encodable.encode t = toNat t := rfl

lemma toNat_func {k} (f : L.Func k) (v : Fin k → Semiterm L ξ n) :
    toNat (func f v) = (Nat.pair 2 <| Nat.pair k <| Nat.pair (encode f) <|
        Matrix.vecToNat fun i ↦ toNat (v i)) + 1 :=
      rfl

@[simp] lemma encode_emb (t : Semiterm L Empty n) : Encodable.encode (Rew.emb t :
    Semiterm L ξ n) = Encodable.encode t := by
  simp only [encode_eq_toNat]
  induction t
  · simp [toNat]
  · contradiction
  · simp [Rew.func, toNat_func, *]

end Semiterm

namespace  Semiformula

/-! TODO: move to Foundation-/
lemma embedding_rel [IsEmpty ο] {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ο n) :
    (Rewriting.embedding (rel R v) : Semiformula L ξ n) = (rel R fun i ↦ Rew.emb (v i)) := by rfl

lemma embedding_nrel [IsEmpty ο] {k : ℕ} (R : L.Rel k) (v : Fin k → Semiterm L ο n) :
    (Rewriting.embedding (nrel R v) : Semiformula L ξ n) = (nrel R fun i ↦ Rew.emb (v i)) := by rfl

open Encodable

variable [Encodable ξ] [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

lemma encode_eq_toNat
    (φ : Semiformula L ξ n) : Encodable.encode φ = toNat φ := rfl

lemma encode_rel {arity : ℕ} (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    encode (Semiformula.rel R v) =
        (Nat.pair 0 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1 :=
      rfl

lemma encode_nrel {arity : ℕ} (R : L.Rel arity) (v : Fin arity → Semiterm L ξ n) :
    encode (Semiformula.nrel R v) =
        (Nat.pair 1 <| arity.pair <| (encode R).pair <| Matrix.vecToNat fun i ↦ encode (v i)) + 1 :=
      rfl

lemma encode_verum : encode (⊤ : Semiformula L ξ n) = (Nat.pair 2 0) + 1 := rfl

lemma encode_falsum : encode (⊥ : Semiformula L ξ n) = (Nat.pair 3 0) + 1 := rfl

lemma encode_and (φ ψ : Semiformula L ξ n) :
    encode (φ ⋏ ψ) = (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1 :=
  rfl

lemma encode_or (φ ψ : Semiformula L ξ n) :
    encode (φ ⋎ ψ) = (Nat.pair 5 <| φ.toNat.pair ψ.toNat) + 1 :=
  rfl

lemma encode_all (φ : Semiformula L ξ (n + 1)) : encode (∀' φ) = (Nat.pair 6 <| φ.toNat) + 1 := rfl

lemma encode_ex (φ : Semiformula L ξ (n + 1)) : encode (∃' φ) = (Nat.pair 7 <| φ.toNat) + 1 := rfl

@[simp] lemma encode_emb
    (φ : Semisentence L n) : Encodable.encode (Rewriting.embedding φ : Semiformula L ξ n) =
        Encodable.encode φ := by
  induction φ using rec' <;>
    simp [embedding_rel, embedding_nrel,
      encode_rel, encode_nrel, encode_verum, encode_falsum, encode_and, encode_or, encode_all,
        encode_ex,
      ← encode_eq_toNat, *]

end Semiformula

namespace Semiformula
namespace Operator

lemma lt_eq [L.LT] (t u : Semiterm L ξ n) :
    LT.lt.operator ![t, u] = Semiformula.rel Language.LT.lt ![t, u] := by
      simp [operator, LT.sentence_eq, rew_rel]

end Operator
end Semiformula

end FirstOrder
end LO

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

lemma nat_cast_empty : ((∅ : ℕ) : V) = ∅ := rfl

/-- Imported declaration from the Incompleteness formalization. -/
def finArrowToVec : {k : ℕ} → (Fin k → V) → V
  | 0,     _ => 0
  | k + 1, v => v 0 ∷ finArrowToVec (k := k) (v ·.succ)

/-- quasi-quotation rather than Godel quotation -/
instance : GoedelQuote (Fin k → V) V := ⟨finArrowToVec⟩

lemma quote_matrix_def (v : Fin k → V) : ⌜v⌝ = finArrowToVec v := rfl

@[simp] lemma quote_nil : (⌜(![] : Fin 0 → V)⌝ : V) = 0 := rfl

@[simp] lemma quote_singleton (a : V) : (⌜![a]⌝ : V) = ?[a] := rfl

@[simp] lemma quote_doubleton (a b : V) : (⌜![a, b]⌝ : V) = ?[a, b] := rfl

@[simp] lemma quote_matrix_empty (v : Fin 0 → V) :
    (⌜v⌝ : V) = 0 := by rfl

lemma quote_matrix_succ (v : Fin (k + 1) → V) :
    (⌜v⌝ : V) = v 0 ∷ ⌜fun i : Fin k ↦ v i.succ⌝ := by simp [quote_matrix_def, finArrowToVec]

@[simp] lemma quote_cons (v : Fin k → V) (a : V) :
    (⌜a :> v⌝ : V) = a ∷ ⌜v⌝  := by simp [quote_matrix_succ]

@[simp] lemma quote_matrix_inj (v w : Fin k → V) : (⌜v⌝ : V) = ⌜w⌝ ↔ v = w := by
  induction k with
  | zero => simp [Matrix.empty_eq]
  | succ k ih =>
    simp only [quote_matrix_succ, cons_inj, ih]
    constructor
    · rintro ⟨h0, hs⟩
      funext x
      cases x using Fin.cases with
      | zero => exact h0
      | succ x => exact congr_fun hs x
    · rintro rfl; simp

@[simp] lemma quote_lh (v : Fin k → V) : len (⌜v⌝ : V) = k := by
  induction k with
  | zero => simp [Matrix.empty_eq]
  | succ k ih => simp [quote_matrix_succ, *]

@[simp] lemma quote_nth_fin (v : Fin k → V) (i : Fin k) : (⌜v⌝ : V).[i] = v i := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    simp only [quote_matrix_succ]
    cases i using Fin.cases with
    | zero => simp
    | succ i => simp [ih]

@[simp] lemma quote_matrix_absolute (v : Fin k → ℕ) : ((⌜v⌝ : ℕ) : V) = ⌜fun i ↦ (v i : V)⌝ := by
  induction k with
  | zero => simp
  | succ k ih => simp [quote_matrix_succ, ih, cons_absolute]

lemma quote_eq_vecToNat (v : Fin k → ℕ) : ⌜v⌝ = Matrix.vecToNat v := by
  induction k
  case zero => simp
  case succ k ih =>
    simp [quote_matrix_succ, Matrix.vecToNat, cons, nat_pair_eq, Function.comp_def, ih]

section «lp_section_1»

variable {α : Type*} [Encodable α]

instance : GoedelQuote α V := ⟨fun x ↦ Encodable.encode x⟩

lemma quote_eq_coe_encode (x : α) : (⌜x⌝ : V) = Encodable.encode x := rfl

@[simp 1100] lemma quote_nat (n : ℕ) : (⌜n⌝ : V) = n := rfl

lemma coe_quote (x : α) : ↑(⌜x⌝ : ℕ) = (⌜x⌝ : V) := by simp [quote_eq_coe_encode]

lemma quote_quote (x : α) : (⌜(⌜x⌝ : ℕ)⌝ : V) = ⌜x⌝ := by simp [quote_eq_coe_encode]

lemma quote_eq_encode (x : α) : (⌜x⌝ : ℕ) = Encodable.encode x := by simp [quote_eq_coe_encode]

@[simp] lemma val_quote {ξ n e ε} (x : α) : Semiterm.valm V e ε (⌜x⌝ : Semiterm ℒₒᵣ ξ n) = ⌜x⌝ := by
  simp [goedelNumber'_def, quote_eq_coe_encode, numeral_eq_natCast]

lemma numeral_quote (x : α) : Semiterm.Operator.numeral ℒₒᵣ (⌜x⌝ : ℕ) = (⌜x⌝ :
    Semiterm ℒₒᵣ ξ n) := by
  simp [quote_eq_coe_encode]; rfl

@[simp] lemma quote_inj_iff {x y : α} : (⌜x⌝ : V) = ⌜y⌝ ↔ x = y := by simp [quote_eq_coe_encode]

end «lp_section_1»

end Arith
end LO

namespace LO
namespace FirstOrder
namespace Semiterm

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language}

variable (V)

variable [(k : ℕ) → Encodable (L.Func k)]

lemma quote_eq_toNat (t : SyntacticSemiterm L n) : (⌜t⌝ : V) = toNat t := rfl

@[simp] lemma quote_bvar (z : Fin n) : ⌜(#z : SyntacticSemiterm L n)⌝ = ^#(z : V) := by
  simp [quote_eq_toNat, toNat, qqBvar, ←nat_pair_eq, nat_cast_pair]

@[simp] lemma quote_fvar (x : ℕ) : ⌜(&x : SyntacticSemiterm L n)⌝ = ^&(x : V) := by
  simp [quote_eq_toNat, toNat, qqFvar, ←nat_pair_eq, nat_cast_pair]

lemma quote_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    ⌜func f v⌝ = ^func (k : V) ⌜f⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [quote_eq_toNat, toNat, qqFunc, ←nat_pair_eq, nat_cast_pair, quote_func_def,
    quote_eq_vecToNat, ←quote_matrix_absolute]

@[simp 1100] lemma codeIn_inj {n} {t u : SyntacticSemiterm L n} : (⌜t⌝ : V) = ⌜u⌝ ↔ t = u := by
  induction t generalizing u
  case bvar z =>
    rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc, Fin.val_inj]
  case fvar x => rcases u <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc]
  case func k f v ih =>
    rcases u <;>
      simp only [quote_func, qqFunc, quote_bvar, qqBvar, quote_fvar, qqFvar, add_left_inj,
        pair_ext_iff, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_and, reduceCtorEq,
        Nat.cast_inj, true_and, func.injEq, and_congr_right_iff]
    rintro rfl
    simp only [quote_inj_iff, quote_matrix_inj, heq_eq_eq, and_congr_right_iff]
    rintro rfl
    constructor
    · intro h; funext i; exact (ih i).mp (congr_fun h i)
    · rintro rfl; rfl

@[simp 1100] lemma quote_zero (n) :
    (⌜(Semiterm.func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = qqZero := by
  simp [FirstOrder.Semiterm.quote_func, Formalized.zero, Formalized.qqFunc_absolute]; rfl

@[simp 1100] lemma quote_zero' (n) : (⌜(‘0’ : SyntacticSemiterm ℒₒᵣ n)⌝ :
    V) = qqZero :=
  quote_zero V n

@[simp 1100] lemma quote_one (n) :
    (⌜(Semiterm.func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = qqOne := by
  simp [FirstOrder.Semiterm.quote_func, Formalized.one, Formalized.qqFunc_absolute]; rfl

@[simp 1100] lemma quote_one' (n) : (⌜(‘1’ : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = qqOne := quote_one V n

@[simp] lemma quote_add (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Add.add ![t, u]⌝ : V) = (⌜t⌝ ^+ ⌜u⌝) := by
      simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_add' (t u : SyntacticSemiterm ℒₒᵣ n) : (⌜‘!!t + !!u’⌝ :
    V) = (⌜t⌝ ^+ ⌜u⌝) :=
  quote_add V t u

@[simp] lemma quote_mul (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiterm.func Language.Mul.mul ![t, u]⌝ : V) = (⌜t⌝ ^* ⌜u⌝) := by
      simp [FirstOrder.Semiterm.quote_func]; rfl

@[simp] lemma quote_mul' (t u : SyntacticSemiterm ℒₒᵣ n) : (⌜‘!!t * !!u’⌝ :
    V) = (⌜t⌝ ^* ⌜u⌝) :=
  quote_mul V t u

@[simp] lemma quote_absolute (t : SyntacticSemiterm L n) :
    ((⌜t⌝ : ℕ) : V) = ⌜t⌝ := by
  induction t <;> simp [quote_bvar, quote_fvar, quote_func, qqBvar, qqFvar, qqFunc,
    nat_cast_pair, *];
    rfl

lemma quote_eq_encode (t : SyntacticSemiterm L n) : ⌜t⌝ = Encodable.encode t := by
  induction t
  case bvar z => simp [encode_eq_toNat, toNat, quote_bvar, qqBvar, nat_pair_eq]
  case fvar z => simp [encode_eq_toNat, toNat, quote_fvar, qqFvar, nat_pair_eq]
  case func k f v ih =>
    simp [encode_eq_toNat, toNat, quote_func, qqFunc, nat_pair_eq, quote_func_def,
      quote_eq_vecToNat, ih]

end Semiterm
end FirstOrder
end LO

namespace LO
namespace Arith

open FirstOrder FirstOrder.Semiterm FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

/-- TODO: move -/
lemma eq_fin_of_lt_nat {n : ℕ} {x : V} (hx : x < n) : ∃ i : Fin n, x = i := by
  rcases eq_nat_of_lt_nat hx with ⟨x, rfl⟩
  exact ⟨⟨x, by simpa using hx⟩, by simp⟩

@[simp] lemma semiterm_codeIn {n} (t : SyntacticSemiterm L n) :
    (L.codeIn V).IsSemiterm n ⌜t⌝ := by
  induction t <;>
    simp only [quote_bvar, Language.IsSemiterm.bvar, Nat.cast_lt, Fin.is_lt, quote_fvar,
      Language.IsSemiterm.fvar, quote_func, Language.IsSemiterm.func, codeIn_func_quote,
      true_and]
  case func k f v ih =>
    apply Language.IsSemitermVec.iff.mpr
    exact ⟨by simp, by
      rintro i hi
      rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
      simpa using ih i⟩

@[simp] lemma semitermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := Language.IsSemitermVec.iff.mpr
  ⟨by simp, by intro i hi; rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩; simp⟩

@[simp] lemma isUTermVec_codeIn {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).IsUTermVec k ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v |>.isUTerm

@[simp] lemma quote_termSubst {n m} (t : SyntacticSemiterm L n) (w :
    Fin n → SyntacticSemiterm L m) :
    ⌜Rew.substs w t⌝ = (L.codeIn V).termSubst ⌜fun i ↦ ⌜w i⌝⌝ ⌜t⌝ := by
  induction t
  case bvar z => simp [quote_bvar]
  case fvar x => simp [quote_fvar]
  case func k f v ih =>
    have Hw : (L.codeIn V).IsSemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, Language.termSubst_func (codeIn_func_quote f)
      Hv.isUTerm]
    congr
    apply nth_ext (by simp [(Hw.termSubstVec Hv).lh])
    intro i hi
    have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termSubstVec Hv.isUTerm hi]
    simpa using ih i

lemma quote_termSubstVec {k n m} (w : Fin n → SyntacticSemiterm L m) (v :
    Fin k → SyntacticSemiterm L n) :
    ⌜fun i ↦ ⌜(Rew.substs w) (v i)⌝⌝ = (L.codeIn V).termSubstVec ↑k ⌜fun i ↦ ⌜w i⌝⌝ ⌜fun i =>
      ⌜v i⌝⌝ := by
  have Hw : (L.codeIn V).IsSemitermVec n m ⌜fun i ↦ ⌜w i⌝⌝ := semitermVec_codeIn w
  have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hw.termSubstVec Hv |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hw.termSubstVec Hv |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simp [nth_termSubstVec Hv.isUTerm hi]

@[simp] lemma quote_termShift {n} (t : SyntacticSemiterm L n) :
    ⌜Rew.shift t⌝ = (L.codeIn V).termShift ⌜t⌝ := by
  induction t
  case bvar => simp [quote_bvar]
  case fvar => simp [quote_fvar]
  case func k f v ih =>
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, Language.termShift_func (codeIn_func_quote f)
      Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termShiftVec Hv.isUTerm hi]
    simpa using ih i

lemma quote_termShiftVec {k n} (v : Fin k → SyntacticSemiterm L n) :
    ⌜fun i ↦ ⌜Rew.shift (v i)⌝⌝ = (L.codeIn V).termShiftVec k ⌜fun i ↦ ⌜v i⌝⌝ := by
  have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
  apply nth_ext (by simp [Hv.termShiftVec |>.lh])
  intro i hi
  have hi : i < k := by simpa [Hv.termShiftVec |>.lh] using hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simp [nth_termShiftVec Hv.isUTerm hi]

@[simp] lemma quote_termBShift {n} (t : SyntacticSemiterm L n) :
    ⌜Rew.bShift t⌝ = (L.codeIn V).termBShift ⌜t⌝ := by
  induction t
  case bvar => simp [quote_bvar]
  case fvar => simp [quote_fvar]
  case func k f v ih =>
    have Hv : (L.codeIn V).IsSemitermVec k n ⌜fun i ↦ ⌜v i⌝⌝ := semitermVec_codeIn v
    simp only [Rew.func, Semiterm.quote_func, Language.termBShift_func (codeIn_func_quote f)
      Hv.isUTerm]
    congr
    apply nth_ext (by simp [Hv.termBShiftVec |>.lh])
    intro i hi
    have hi : i < k := by simpa [Hv.termBShiftVec |>.lh] using hi
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    rw [nth_termBShiftVec Hv.isUTerm hi]
    simpa using ih i

@[simp] lemma _root_.LO.Arith.Formalized.quote_numeral_eq_numeral (k : ℕ) :
    (⌜(‘↑k’ : SyntacticSemiterm ℒₒᵣ n)⌝ : V) = Formalized.numeral (k : V) := by
  induction k
  case zero => simp
  case succ k ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    cases k with
    | zero => simp
    | succ k =>
      calc
        ⌜(‘↑(k + 1 + 1)’ : SyntacticSemiterm ℒₒᵣ n)⌝
        _ = ⌜(Operator.operator (Operator.numeral ℒₒᵣ (k + 1)) ![] : SyntacticSemiterm ℒₒᵣ n)⌝
          ^+ ⌜(Operator.operator op(1) ![] : SyntacticSemiterm ℒₒᵣ n)⌝ := by
          unfold Semiterm.numeral
          simp [Operator.numeral_succ, Matrix.fun_eq_vec₂]
        _ = Formalized.numeral ((k + 1 : ℕ) : V) ^+ ↑qqOne := by
          rw [←FirstOrder.Semiterm.quote_one']
          congr
        _ = Formalized.numeral ((k : V) + 1) ^+ ↑qqOne := by rfl
        _ = Formalized.numeral ((k + 1 : V) + 1) := by
          simp []

omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
lemma quote_eterm_eq_quote_emb (t : Semiterm L Empty n) : (⌜t⌝ : V) = (⌜Rew.embs t⌝ : V) := by
  simp [quote_eq_coe_encode]

@[simp] lemma _root_.LO.Arith.Formalized.quote_numeral_eq_numeral' (k : ℕ) :
    (⌜(‘↑k’ : Semiterm ℒₒᵣ Empty n)⌝ : V) = Formalized.numeral (k : V) := by
  simp [quote_eterm_eq_quote_emb]

@[simp] lemma quote_quote_eq_numeral {α : Type*} [Encodable α] {x : α} : (⌜(⌜x⌝ :
    Semiterm ℒₒᵣ ℕ n)⌝ :
    V) = Formalized.numeral ⌜x⌝ := by
  simp only [goedelNumber'_def, Formalized.quote_numeral_eq_numeral]
  rw [quote_eq_coe_encode]

end Arith
end LO

namespace LO
namespace FirstOrder
namespace Semiformula

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]

lemma quote_eq_toNat (φ : SyntacticSemiformula L n) : (⌜φ⌝ : V) = toNat φ := rfl

lemma quote_rel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) : (⌜rel R v⌝ :
    V) = ^rel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [Semiterm.quote_eq_toNat, quote_eq_toNat, toNat, qqRel, ←nat_pair_eq, nat_cast_pair,
    quote_rel_def, ←quote_eq_vecToNat]; rfl
lemma quote_nrel {k} (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) : (⌜nrel R v⌝ :
    V) = ^nrel ↑k ⌜R⌝ ⌜fun i ↦ ⌜v i⌝⌝ := by
  simp [Semiterm.quote_eq_toNat, quote_eq_toNat, toNat, ←nat_pair_eq, nat_cast_pair,
    quote_rel_def, ←quote_eq_vecToNat]; rfl
@[simp] lemma quote_verum (n : ℕ) : ⌜(⊤ : SyntacticSemiformula L n)⌝ = (^⊤ : V) := by
  simp [quote_eq_toNat, toNat, qqVerum, ←pair_coe_eq_coe_pair, nat_cast_pair]
@[simp] lemma quote_falsum (n : ℕ) : ⌜(⊥ : SyntacticSemiformula L n)⌝ = (^⊥ : V) := by
  simp [quote_eq_toNat, toNat, qqFalsum, ←pair_coe_eq_coe_pair, nat_cast_pair]
@[simp] lemma quote_and (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := by
  simp [quote_eq_toNat, toNat, qqAnd, ←pair_coe_eq_coe_pair, nat_cast_pair]
@[simp] lemma quote_or (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := by
  simp [quote_eq_toNat, toNat, qqOr, ←pair_coe_eq_coe_pair, nat_cast_pair]
@[simp] lemma quote_all (φ : SyntacticSemiformula L (n + 1)) : (⌜∀' φ⌝ : V) = ^∀ ⌜φ⌝ := by
  simp [quote_eq_toNat, toNat, qqAll, ←pair_coe_eq_coe_pair, nat_cast_pair]
@[simp] lemma quote_ex (φ : SyntacticSemiformula L (n + 1)) : (⌜∃' φ⌝ : V) = ^∃ ⌜φ⌝ := by
  simp [quote_eq_toNat, toNat, qqEx, ←pair_coe_eq_coe_pair, nat_cast_pair]

@[simp] lemma quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^= ⌜u⌝) := by
      simp [FirstOrder.Semiformula.quote_rel]; rfl
@[simp] lemma quote_neq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.Eq.eq ![t, u]⌝ : V) = (⌜t⌝ ^≠ ⌜u⌝) := by
      simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp] lemma quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.rel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^< ⌜u⌝) := by
      simp [FirstOrder.Semiformula.quote_rel]; rfl

@[simp 1100] lemma quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜Semiformula.nrel Language.LT.lt ![t, u]⌝ : V) = (⌜t⌝ ^</ ⌜u⌝) := by
      simp [FirstOrder.Semiformula.quote_nrel]; rfl

@[simp 1100] lemma quote_neq' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t ≠ !!u”⌝ : V) = (⌜t⌝ ^≠ ⌜u⌝) := by simp [Semiformula.Operator.eq_def]

@[simp] lemma quote_eq' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t = !!u”⌝ : V) = (⌜t⌝ ^= ⌜u⌝) := by simp [Semiformula.Operator.eq_def]

@[simp 1100] lemma quote_lt' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t < !!u”⌝ : V) = (⌜t⌝ ^< ⌜u⌝) := by simp [Semiformula.Operator.lt_def]

@[simp 1100] lemma quote_nlt' (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜“!!t </ !!u”⌝ : V) = (⌜t⌝ ^</ ⌜u⌝) := by simp [Semiformula.Operator.lt_def]

@[simp] lemma quote_semisentence_def (φ : Semisentence L n) : ⌜(Rewriting.embedding φ :
    SyntacticSemiformula L n)⌝ = (⌜φ⌝ :
    V) := by
  simp [quote_eq_coe_encode]

lemma sentence_goedelNumber_def (σ : Sentence L) :
  (⌜σ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜σ⌝ := by
    simp [Arith.goedelNumber'_def, quote_eq_encode]

lemma syntacticformula_goedelNumber_def (φ : SyntacticFormula L) :
  (⌜φ⌝ : Semiterm ℒₒᵣ ξ n) = Semiterm.Operator.numeral ℒₒᵣ ⌜φ⌝ := by
    simp [Arith.goedelNumber'_def, quote_eq_encode]

@[simp] lemma quote_weight (n : ℕ) : ⌜(weight k : SyntacticSemiformula L n)⌝ = (qqVerums k :
    V) := by
  unfold weight
  induction k <;> simp [quote_verum, quote_and, List.replicate, *]

end Semiformula
end FirstOrder
end LO

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith FirstOrder.Semiformula

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

@[simp] lemma semiformula_quote {n} (φ : SyntacticSemiformula L n) :
    (L.codeIn V).IsSemiformula n ⌜φ⌝ := by
  induction φ using Semiformula.rec'
  case hrel n k r v => simp [Semiformula.quote_rel]
  case hnrel n k r v => simp [Semiformula.quote_nrel]
  case hverum n => simp [Semiformula.quote_verum]
  case hfalsum n => simp [Semiformula.quote_falsum]
  case hand n φ ψ ihp ihq => simp [Semiformula.quote_and, ihp, ihq]
  case hor n φ ψ ihp ihq => simp [Semiformula.quote_or, ihp, ihq]
  case hall n φ ihp => simpa [Semiformula.quote_all] using ihp
  case hex n φ ihp => simpa [Semiformula.quote_ex] using ihp

@[simp] lemma semiformula_quote0 (φ : SyntacticFormula L) :
    (L.codeIn V).IsFormula ⌜φ⌝ := by simpa using semiformula_quote φ

@[simp] lemma semiformula_quote1 (φ : SyntacticSemiformula L 1) :
    (L.codeIn V).IsSemiformula 1 ⌜φ⌝ := by simpa using semiformula_quote (V := V) φ

@[simp] lemma semiformula_quote2 (φ : SyntacticSemiformula L 2) :
    (L.codeIn V).IsSemiformula 2 ⌜φ⌝ := by simpa using semiformula_quote (V := V) φ

@[simp] lemma isUFormula_quote {n} (φ : SyntacticSemiformula L n) :
    (L.codeIn V).IsUFormula ⌜φ⌝ := semiformula_quote φ |>.isUFormula

@[simp] lemma semiformula_quote_succ {n} (φ : SyntacticSemiformula L (n + 1)) :
    (L.codeIn V).IsSemiformula (n + 1) ⌜φ⌝ := by simpa using semiformula_quote φ

@[simp] lemma quote_neg {n} (φ : SyntacticSemiformula L n) :
    ⌜∼φ⌝ = (L.codeIn V).neg ⌜φ⌝ := by
  induction φ using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all,
      quote_ex]

@[simp] lemma quote_imply {n} (φ ψ : SyntacticSemiformula L n) :
    ⌜φ ==> ψ⌝ = (L.codeIn V).imp ⌜φ⌝ ⌜ψ⌝ := by
  simp [Semiformula.imp_eq, Semiformula.quote_or, quote_neg]; rfl

@[simp] lemma quote_iff {n} (φ ψ : SyntacticSemiformula L n) :
    ⌜φ <=> ψ⌝ = (L.codeIn V).iff ⌜φ⌝ ⌜ψ⌝ := by
  simp [Semiformula.imp_eq, LogicalConnective.iff, Semiformula.quote_or, quote_neg]; rfl

@[simp] lemma quote_shift {n} (φ : SyntacticSemiformula L n) :
    ⌜Rewriting.shift φ⌝ = (L.codeIn V).shift ⌜φ⌝ := by
  induction φ using Semiformula.rec' <;>
    simp [*, quote_rel, quote_nrel, quote_verum, quote_falsum, quote_and, quote_or, quote_all,
      quote_ex,
      rew_rel, rew_nrel, ←quote_termShiftVec]

lemma qVec_quote (w : Fin n → SyntacticSemiterm L m) :
    (L.codeIn V).qVec ⌜fun i => ⌜w i⌝⌝ = ⌜^#0 :> fun i ↦ (⌜Rew.bShift (w i)⌝ : V)⌝ := by
  have Hw :
      (L.codeIn V).IsSemitermVec ↑n (↑m + 1) ((L.codeIn V).termBShiftVec ↑n ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).termBShiftVec
  have HqVec : (L.codeIn V).IsSemitermVec (↑n + 1) (↑m + 1) ((L.codeIn V).qVec ⌜fun i ↦ ⌜w i⌝⌝) :=
    (semitermVec_codeIn w).qVec
  apply nth_ext (by simp [←HqVec.lh])
  intro i hi
  have : i < ↑(n + 1) := by simpa [Language.qVec, Hw.lh] using hi
  rcases eq_fin_of_lt_nat this with ⟨i, rfl⟩
  cases i using Fin.cases with
  | zero => simp [Language.qVec]
  | succ i => simp [Language.qVec, quote_termBShift]

@[simp] lemma quote_substs {n m} (w : Fin n → SyntacticSemiterm L m) (φ :
    SyntacticSemiformula L n) :
    ⌜φ <~ w⌝  = (L.codeIn V).substs ⌜fun i ↦ ⌜w i⌝⌝ ⌜φ⌝ := by
  induction φ using Semiformula.rec' generalizing m <;>
    simp_all only [LogicalConnective.HomClass.map_top, quote_verum, substs_verum,
      LogicalConnective.HomClass.map_bot, quote_falsum, substs_falsum, rew_rel, quote_rel,
      quote_termSubst, codeIn_rel_quote, isUTermVec_codeIn, substs_rel, ←quote_termSubstVec,
      rew_nrel, quote_nrel, substs_nrel, LogicalConnective.HomClass.map_and, quote_and,
      isUFormula_quote, substs_and, LogicalConnective.HomClass.map_or, quote_or, substs_or,
      Rewriting.app_all, Rew.q_substs, Nat.succ_eq_add_one, quote_all, Matrix.comp_vecCons',
      Semiterm.quote_bvar, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_zero, Function.comp_apply,
      quote_termBShift, quote_cons, substs_all, Rewriting.app_ex, quote_ex, substs_ex, qVec_quote]

omit [DefinableLanguage L] in
lemma quote_sentence_eq_quote_emb (σ : Semisentence L n) : (⌜σ⌝ :
    V) = ⌜Rew.embs ▹ σ⌝ := by
  simp [quote_eq_coe_encode]

lemma quote_substs' {n m} (w : Fin n → Semiterm L Empty m) (σ : Semisentence L n) :
    ⌜σ <~ w⌝ = (L.codeIn V).substs ⌜fun i ↦ ⌜w i⌝⌝ ⌜σ⌝ := by
  let w' : Fin n → SyntacticSemiterm L m := fun i ↦ Rew.emb (w i)
  have : (⌜fun i ↦ ⌜w i⌝⌝ : V) = ⌜fun i ↦ ⌜w' i⌝⌝ := by
    apply nth_ext' (↑n) (by simp) (by simp)
    intro i hi;
    rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
    simp [w', quote_eterm_eq_quote_emb]
  symm
  rw [quote_sentence_eq_quote_emb, this, ←quote_substs, quote_sentence_eq_quote_emb]
  congr 1
  simp only [← TransitiveRewriting.comp_app]; congr 2;
  ext x <;> simp only [Rew.comp_app, Rew.emb_bvar, Rew.substs_bvar, Rew.substs_fvar, w']
  contradiction

@[simp] lemma free_quote (φ : SyntacticSemiformula L 1) :
    ⌜Rewriting.free φ⌝ = (L.codeIn V).free ⌜φ⌝ := by
  rw [← LawfulSyntacticRewriting.app_substs_fbar_zero_comp_shift_eq_free, quote_substs, quote_shift]
  simp [Language.free, Language.substs₁, Semiterm.quote_fvar,
    Matrix.constant_eq_singleton]

end Arith
end LO


namespace LO
namespace FirstOrder
namespace Derivation2

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]
  [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

-- def codeIn : {Γ : Finset (SyntacticFormula L)} → Derivation2 Γ → V

end Derivation2
end FirstOrder
end LO

/-!

### Typed

-/

namespace LO
namespace FirstOrder

open LO.Arith FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

variable (V)

variable {n : ℕ}

namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def codeIn' (t : SyntacticSemiterm L n) : (L.codeIn V).Semiterm n := ⟨⌜t⌝, by simp⟩

instance : GoedelQuote (SyntacticSemiterm L n) ((L.codeIn V).Semiterm n) := ⟨Semiterm.codeIn' V⟩

@[simp] lemma codeIn'_val (t : SyntacticSemiterm L n) : (⌜t⌝ :
    (L.codeIn V).Semiterm n).val = ⌜t⌝ :=
  rfl

/-- Imported declaration from the Incompleteness formalization. -/
def vCodeIn' {k n} (v : Fin k → SyntacticSemiterm L n) :
    (L.codeIn V).SemitermVec k n :=
  ⟨⌜fun i ↦ ⌜v i⌝⌝, by simp⟩

instance {k n} :
    GoedelQuote (Fin k → SyntacticSemiterm L n) ((L.codeIn V).SemitermVec k n) :=
  ⟨Semiterm.vCodeIn' V⟩

@[simp] lemma vCodeIn'_val (v : Fin k → SyntacticSemiterm L n) : (⌜v⌝ :
    (L.codeIn V).SemitermVec k n).val = ⌜fun i ↦ ⌜v i⌝⌝ :=
  rfl

@[simp] lemma codeIn'_bvar (z : Fin n) : (⌜(#z : SyntacticSemiterm L n)⌝ :
    (L.codeIn V).Semiterm n) = (L.codeIn V).bvar z := by
  ext; simp [quote_bvar]
@[simp] lemma codeIn'_fvar (x : ℕ) : (⌜(&x : SyntacticSemiterm L n)⌝ :
    (L.codeIn V).Semiterm n) = (L.codeIn V).fvar x := by
  ext; simp [quote_fvar]
lemma codeIn'_func {k} (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜func f v⌝ : (L.codeIn V).Semiterm n) =
        (L.codeIn V).func (k := k) (f := ⌜f⌝) (by simp) ⌜v⌝ := by
      ext; simp [quote_func, Language.func]
@[simp] lemma codeIn'_zero (n : ℕ) :
    (⌜(func Language.Zero.zero ![] : SyntacticSemiterm ℒₒᵣ n)⌝ :
      (Language.codeIn ℒₒᵣ V).Semiterm n) = ↑(0 : V) := by
      ext; simp
@[simp] lemma codeIn'_one (n : ℕ) :
    (⌜(func Language.One.one ![] : SyntacticSemiterm ℒₒᵣ n)⌝ :
      (Language.codeIn ℒₒᵣ V).Semiterm n) = ↑(1 : V) := by
      ext; simp
@[simp] lemma codeIn'_add (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Add.add v⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ⌜v 0⌝ + ⌜v 1⌝ := by
      ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp [quote_add]
@[simp] lemma codeIn'_mul (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜func Language.Mul.mul v⌝ : (Language.codeIn ℒₒᵣ V).Semiterm n) = ⌜v 0⌝ * ⌜v 1⌝ := by
      ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp []

end Semiterm

namespace Semiformula

/-- Imported declaration from the Incompleteness formalization. -/
def codeIn' (φ : SyntacticSemiformula L n) : (L.codeIn V).Semiformula n := ⟨⌜φ⌝, by simp⟩

instance goedelQuoteSyntacticSemiformulaToCodedSemiformula :
    GoedelQuote (SyntacticSemiformula L n) ((L.codeIn V).Semiformula n) :=
  ⟨Semiformula.codeIn' V⟩

instance goedelQuoteSyntacticFormulaToCodedFormula :
    GoedelQuote (SyntacticFormula L) ((L.codeIn V).Formula) :=
  ⟨Semiformula.codeIn' V⟩

@[simp] lemma codeIn'_val (φ : SyntacticSemiformula L n) : (⌜φ⌝ :
    (L.codeIn V).Semiformula n).val = ⌜φ⌝ :=
  rfl

@[simp] lemma codeIn'_verum (n : ℕ) : (⌜(⊤ : SyntacticSemiformula L n)⌝ :
    (L.codeIn V).Semiformula n) = ⊤ := by
  ext; simp [quote_verum]
@[simp] lemma codeIn'_falsum (n : ℕ) : (⌜(⊥ : SyntacticSemiformula L n)⌝ :
    (L.codeIn V).Semiformula n) = ⊥ := by
  ext; simp [quote_falsum]
@[simp] lemma codeIn'_and (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋏ ψ⌝ :
    (L.codeIn V).Semiformula n) = ⌜φ⌝ ⋏ ⌜ψ⌝ := by
  ext; simp [quote_and]
@[simp] lemma codeIn'_or (φ ψ : SyntacticSemiformula L n) : (⌜φ ⋎ ψ⌝ :
    (L.codeIn V).Semiformula n) = ⌜φ⌝ ⋎ ⌜ψ⌝ := by
  ext; simp [quote_or]
@[simp] lemma codeIn'_all (φ : SyntacticSemiformula L (n + 1)) : (⌜∀' φ⌝ :
    (L.codeIn V).Semiformula n) = .all (.cast (n := ↑(n + 1)) ⌜φ⌝) := by
  ext; simp [quote_all]
@[simp] lemma codeIn'_ex (φ : SyntacticSemiformula L (n + 1)) : (⌜∃' φ⌝ :
    (L.codeIn V).Semiformula n) = .ex (.cast (n := ↑(n + 1)) ⌜φ⌝) := by
  ext; simp [quote_ex]
@[simp] lemma codeIn'_neg (φ : SyntacticSemiformula L n) : (⌜∼φ⌝ :
    (L.codeIn V).Semiformula n) = ∼⌜φ⌝ := by
  ext; simp
@[simp] lemma codeIn'_imp (φ ψ : SyntacticSemiformula L n) : (⌜φ ==> ψ⌝ :
    (L.codeIn V).Semiformula n) = ⌜φ⌝ ==> ⌜ψ⌝ := by
  simp [Semiformula.imp_eq, Language.Semiformula.imp_def]

@[simp] lemma codeIn'_weight (k n : ℕ) :
    (⌜(weight k : SyntacticSemiformula L n)⌝ : (L.codeIn V).Semiformula n) =
        (verums (L := L.codeIn V) k) := by
  ext; simp

open LO.Arith Formalized

@[simp] lemma codeIn'_eq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ =' ⌜v 1⌝) := by
  ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp [Language.Semiterm.equals]
@[simp] lemma codeIn'_neq (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.Eq.eq v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ ≠' ⌜v 1⌝) := by
  ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp [Language.Semiterm.notEquals]
@[simp] lemma codeIn'_lt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜rel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ <' ⌜v 1⌝) := by
  ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp [Language.Semiterm.lessThan]
@[simp] lemma codeIn'_nlt (v : Fin 2 → SyntacticSemiterm ℒₒᵣ n) :
    (⌜nrel Language.LT.lt v⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) = (⌜v 0⌝ </' ⌜v 1⌝) := by
  ext; rw [Matrix.fun_eq_vec₂ (v := v)]; simp [Language.Semiterm.notLessThan]
@[simp] lemma codeIn'_ball (t : SyntacticSemiterm ℒₒᵣ n) (φ : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∀[“#0 < !!(Rew.bShift t)”] φ⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) =
        Language.Semiformula.ball ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜φ⌝) := by
  ext; simp [LO.ball, imp_eq, Language.Semiformula.cast,
    Language.Semiformula.ball, Semiformula.Operator.lt_eq]
@[simp] lemma codeIn'_bex (t : SyntacticSemiterm ℒₒᵣ n) (φ : SyntacticSemiformula ℒₒᵣ (n + 1)) :
    (⌜∃[“#0 < !!(Rew.bShift t)”] φ⌝ : (Language.codeIn ℒₒᵣ V).Semiformula n) =
        Language.Semiformula.bex ⌜t⌝ (.cast (n := ↑(n + 1)) ⌜φ⌝) := by
  ext; simp [LO.bex, Language.Semiformula.cast, Semiformula.Operator.lt_eq]

instance : GoedelQuote (Sentence L) ((L.codeIn V).Formula) :=
  ⟨fun σ ↦ (⌜Rew.embs ▹ σ⌝ : (Language.codeIn L V).Semiformula (0 :
    ℕ))⟩

lemma quote_sentence_def' (σ : Sentence L) : (⌜σ⌝ : (L.codeIn V).Formula) = (⌜Rew.embs ▹ σ⌝ :
    (Language.codeIn L V).Semiformula (0 :
    ℕ)) :=
  rfl

@[simp] lemma quote_sentence_val (σ : Sentence L) : (⌜σ⌝ : (L.codeIn V).Formula).val = ⌜σ⌝ := by
  simp [quote_sentence_def', quote_eq_coe_encode]

@[simp] lemma codeIn''_imp (σ π : Sentence L) : (⌜σ ==> π⌝ :
    (L.codeIn V).Formula) = ⌜σ⌝ ==> ⌜π⌝ := by
  simp [quote_sentence_def']
  rfl

end Semiformula

end FirstOrder
end LO


namespace LO
namespace Arith

open FirstOrder Encodable

lemma mem_iff_mem_bitIndices {x s : ℕ} : x ∈ s ↔ x ∈ s.bitIndices := by
  induction s using Nat.binaryRec generalizing x
  case zero => simp
  case bit b s ih =>
    cases b
    · cases x with
      | zero =>
        simp only [Nat.bit, cond_false, Nat.bitIndices_two_mul, List.mem_map,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, exists_const, iff_false]
        exact zero_not_mem s
      | succ x =>
        simp only [Nat.bit, cond_false, Nat.bitIndices_two_mul, List.mem_map,
          Nat.add_right_cancel_iff, exists_eq_right]
        exact Iff.trans (succ_mem_two_mul_iff (i := x) (a := s) (V := ℕ)) ih
    · cases x with
      | zero =>
        simp only [Nat.bit, cond_true, Nat.bitIndices_two_mul_add_one, List.mem_cons,
          List.mem_map, Nat.add_eq_zero_iff, one_ne_zero, and_false, exists_const, or_false,
          iff_true]
        exact zero_mem_double_add_one s
      | succ x =>
        simp only [Nat.bit, cond_true, Nat.bitIndices_two_mul_add_one, List.mem_cons,
          Nat.add_eq_zero_iff, one_ne_zero, and_false, List.mem_map, Nat.add_right_cancel_iff,
          exists_eq_right, false_or]
        exact Iff.trans (succ_mem_two_mul_succ_iff (i := x) (a := s) (V := ℕ)) ih

variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) →
  Encodable (L.Rel k)] [DefinableLanguage L]

lemma _root_.LO.Arith.Language.IsSemiterm.sound {n t : ℕ} (ht : (L.codeIn ℕ).IsSemiterm n t) : ∃ T :
    FirstOrder.SyntacticSemiterm L n, ⌜T⌝ = t := by
  induction t using Nat.strongRec
  case ind t ih =>
    rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · exact ⟨#⟨z, hz⟩, by simp [Semiterm.quote_bvar]⟩
    · exact ⟨&x, by simp [Semiterm.quote_fvar]⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦
        ih v.[i] (nth_lt_qqFunc_of_lt (by simp [hv.lh])) (hv.nth i.prop)
      choose v' hv' using this
      have : ∃ F, encode F = f :=
        codeIn_func_quote_iff (V := ℕ) (L := L) (x := f) (k := k) |>.mp (by simp [hf])
      rcases this with ⟨f, rfl⟩
      refine ⟨Semiterm.func f v', ?_⟩
      simp only [Semiterm.quote_func, natCast_nat, quote_func_def, qqFunc_inj, true_and]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩

lemma _root_.LO.Arith.Language.IsSemiformula.sound {n φ : ℕ} (h : (L.codeIn ℕ).IsSemiformula n φ) :
    ∃ F :
    FirstOrder.SyntacticSemiformula L n, ⌜F⌝ = φ := by
  induction φ using Nat.strongRec generalizing n
  case ind φ ih =>
    rcases Language.IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, hp, rfl⟩ | ⟨φ, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] :=
      fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r :=
        codeIn_rel_quote_iff (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.rel R v', ?_⟩
      simp only [Semiformula.quote_rel, natCast_nat, quote_rel_def, qqRel_inj, true_and]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] :=
      fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r :=
        codeIn_rel_quote_iff (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨Semiformula.nrel R v', ?_⟩
      simp only [Semiformula.quote_nrel, natCast_nat, quote_rel_def, qqNRel_inj, true_and]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hi; simpa [hv'] using quote_nth_fin (fun i : Fin k ↦ v.[i]) ⟨i, hi⟩
    · exact ⟨⊤, by simp⟩
    · exact ⟨⊥, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋏ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋎ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∀' φ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∃' φ, by simp⟩

end Arith
end LO
