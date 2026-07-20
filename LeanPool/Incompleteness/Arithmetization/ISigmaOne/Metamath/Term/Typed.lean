/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/

import LeanPool.Incompleteness.Arithmetization.ISigmaOne.Metamath.Term.Functions

/-!

# Typed Formalized IsSemiterm/Term

-/

noncomputable section «lp_nc_section_1»

namespace LO
namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]


section «lp_section_1»

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.Semiterm (n : V) where
  /-- Imported declaration from the Incompleteness formalization. -/
  val : V
  prop : L.IsSemiterm n val

/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.Arith.Language.SemitermVec (m n : V) where
  /-- Imported declaration from the Incompleteness formalization. -/
  val : V
  prop : L.IsSemitermVec m n val

attribute [simp] Language.Semiterm.prop Language.SemitermVec.prop

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.Term := L.Semiterm 0

@[ext]
lemma _root_.LO.Arith.Language.Semiterm.ext {t u : L.Semiterm n}
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h

@[simp] lemma _root_.LO.Arith.Language.Semiterm.isUTerm (t : L.Semiterm n) : L.IsUTerm t.val :=
  t.prop.isUTerm

@[simp] lemma _root_.LO.Arith.Language.SemitermVec.isUTerm (v : L.SemitermVec k n) :
    L.IsUTermVec k v.val :=
  v.prop.isUTerm

@[ext]
lemma _root_.LO.Arith.Language.SemitermVec.ext {v w : L.SemitermVec k n}
    (h : v.val = w.val) : v = w := by rcases v; rcases w; simpa using h

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.bvar {n : V} (z : V) (hz : z < n := by simp) : L.Semiterm n :=
  ⟨^#z, by simp [hz]⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.fvar {n : V} (x : V) : L.Semiterm n := ⟨^&x, by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.func {n k f : V} (hf : L.Func k f) (v : L.SemitermVec k n) :
    L.Semiterm n := ⟨^func k f v.val , by simp [hf]⟩

variable {L}

/-- Imported declaration from the Incompleteness formalization. -/
abbrev bv {n : V} (x : V) (h : x < n := by simp) : L.Semiterm n := L.bvar x h
/-- Imported declaration from the Incompleteness formalization. -/
abbrev fv {n : V} (x : V) : L.Semiterm n := L.fvar x

/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "#'" => bv
/-- Imported declaration from the Incompleteness formalization. -/
scoped prefix:max "&'" => fv

@[simp] lemma _root_.LO.Arith.Language.val_bvar {n : V} (z : V) (hz : z < n) :
    (L.bvar z hz).val = ^#z :=
  rfl
@[simp] lemma _root_.LO.Arith.Language.val_fvar {n : V} (x : V) : (L.fvar x :
    L.Semiterm n).val = ^&x :=
  rfl

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.Semiterm.cons {m n} (t : L.Semiterm n) (v : L.SemitermVec m n) :
    L.SemitermVec (m + 1) n := ⟨t.val ∷ v.val, by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
scoped infixr:67 " ∷ᵗ " => Language.Semiterm.cons

@[simp] lemma _root_.LO.Arith.Language.Semitermvec.val_cons {m n : V} (t : L.Semiterm n) (v :
    L.SemitermVec m n) : (t ∷ᵗ v).val = t.val ∷ v.val := by simp [Language.Semiterm.cons]

variable (L)

/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Language.SemitermVec.nil (n) : L.SemitermVec 0 n := ⟨0, by simp⟩

variable {L}

@[simp] lemma _root_.LO.Arith.Language.Semitermvec.val_nil (n : V) :
    (Language.SemitermVec.nil L n).val = 0 := rfl

/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Language.Semiterm.sing {n} (t : L.Semiterm n) : L.SemitermVec (0 + 1) n :=
  t ∷ᵗ .nil L n

namespace Language
namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def shift (t : L.Semiterm n) : L.Semiterm n :=
  ⟨L.termShift t.val, Language.IsSemiterm.termShift t.prop⟩

/-- Imported declaration from the Incompleteness formalization. -/
def bShift (t : L.Semiterm n) : L.Semiterm (n + 1) :=
  ⟨L.termBShift t.val, Language.IsSemiterm.termBShift t.prop⟩

/-- Imported declaration from the Incompleteness formalization. -/
def substs (t : L.Semiterm n) (w : L.SemitermVec n m) : L.Semiterm m :=
  ⟨L.termSubst w.val t.val, w.prop.termSubst t.prop⟩

@[simp] lemma val_shift (t : L.Semiterm n) : t.shift.val = L.termShift t.val := rfl
@[simp] lemma val_bShift (t : L.Semiterm n) : t.bShift.val = L.termBShift t.val := rfl
@[simp] lemma val_substs (w : L.SemitermVec n m) (t : L.Semiterm n) :
    (t.substs w).val = L.termSubst w.val t.val :=
  rfl

end Semiterm
end Language

/-- Imported declaration from the Incompleteness formalization. -/
notation t:max "^ᵗ/[" w "]" => Language.Semiterm.substs t w

namespace Language
namespace SemitermVec

/-- Imported declaration from the Incompleteness formalization. -/
def shift (v : L.SemitermVec k n) : L.SemitermVec k n :=
  ⟨L.termShiftVec k v.val, Language.IsSemitermVec.termShiftVec v.prop⟩

/-- Imported declaration from the Incompleteness formalization. -/
def bShift (v : L.SemitermVec k n) : L.SemitermVec k (n + 1) :=
  ⟨L.termBShiftVec k v.val, Language.IsSemitermVec.termBShiftVec v.prop⟩

/-- Imported declaration from the Incompleteness formalization. -/
def substs (v : L.SemitermVec k n) (w : L.SemitermVec n m) : L.SemitermVec k m :=
  ⟨L.termSubstVec k w.val v.val, Language.IsSemitermVec.termSubstVec w.prop v.prop⟩

@[simp] lemma val_shift (v : L.SemitermVec k n) : v.shift.val = L.termShiftVec k v.val := rfl
@[simp] lemma val_bShift (v : L.SemitermVec k n) : v.bShift.val = L.termBShiftVec k v.val := rfl
@[simp] lemma val_substs (v : L.SemitermVec k n) (w : L.SemitermVec n m) :
    (v.substs w).val = L.termSubstVec k w.val v.val :=
  rfl

@[simp] lemma bShift_nil (n : V) : (nil L n).bShift = nil L (n + 1) := by ext; simp [bShift]

@[simp] lemma bShift_cons (t : L.Semiterm n) (v : L.SemitermVec k n) :
    (t ∷ᵗ v).bShift = t.bShift ∷ᵗ v.bShift := by
  ext; simp [bShift, Language.Semiterm.bShift, termBShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma shift_nil (n : V) : (nil L n).shift = nil L n := by ext; simp [shift]

@[simp] lemma shift_cons (t : L.Semiterm n) (v : L.SemitermVec k n) :
    (t ∷ᵗ v).shift = t.shift ∷ᵗ v.shift := by
  ext; simp [shift, Language.Semiterm.shift, termShiftVec_cons t.prop.isUTerm v.prop.isUTerm]

@[simp] lemma substs_nil (w : L.SemitermVec n m) : (nil L n).substs w = nil L m := by
  ext; simp [substs]

@[simp] lemma substs_cons (w : L.SemitermVec n m) (t : L.Semiterm n) (v : L.SemitermVec k n) :
    (t ∷ᵗ v).substs w = t.substs w ∷ᵗ v.substs w := by
  ext; simp [substs, Language.Semiterm.substs, termSubstVec_cons t.prop.isUTerm v.prop.isUTerm]

/-- Imported declaration from the Incompleteness formalization. -/
def nth (t : L.SemitermVec k n) (i : V) (hi : i < k := by simp) : L.Semiterm n :=
  ⟨t.val.[i], t.prop.nth hi⟩

@[simp] lemma nth_val (v : L.SemitermVec k n) (i : V) (hi : i < k) :
    (v.nth i hi).val = v.val.[i] := by
  simp [nth]

@[simp] lemma nth_zero (t : L.Semiterm n) (v : L.SemitermVec k n) : (t ∷ᵗ v).nth 0 = t := by
  ext; simp [nth]

@[simp] lemma nth_succ (t : L.Semiterm n) (v : L.SemitermVec k n) (i : V) (hi : i < k) :
    (t ∷ᵗ v).nth (i + 1) (by simp [hi]) = v.nth i hi := by ext; simp [nth]

@[simp] lemma nth_one (t : L.Semiterm n) (v : L.SemitermVec (k + 1) n) :
    (t ∷ᵗ v).nth 1 (by simp) = v.nth 0 (by simp) := by ext; simp [nth]

lemma nth_of_pos (t : L.Semiterm n) (v : L.SemitermVec k n) (i : V) (ipos : 0 < i) (hi :
    i < k + 1) : (t ∷ᵗ v).nth i (by simp [hi]) =
        v.nth (i - 1) (tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi) := by
  ext; simp only [nth, Semitermvec.val_cons]
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp

/-- Imported declaration from the Incompleteness formalization. -/
def q (w : L.SemitermVec k n) : L.SemitermVec (k + 1) (n + 1) := L.bvar (0 : V) ∷ᵗ w.bShift

@[simp] lemma q_zero (w : L.SemitermVec k n) : w.q.nth 0 = L.bvar 0 := by simp [q]

@[simp] lemma q_succ (w : L.SemitermVec k n) {i} (hi : i < k) :
    w.q.nth (i + 1) (by simp [hi]) = (w.nth i hi).bShift := by
  simp only [q, hi, nth_succ]
  ext; simp [bShift, nth, Language.Semiterm.bShift, hi]

@[simp] lemma q_one (w : L.SemitermVec k n) (h : 0 < k) :
    w.q.nth 1 (by simp [h]) = (w.nth 0 h).bShift := by
  simpa using q_succ w h

lemma q_of_pos (w : L.SemitermVec k n) (i) (ipos : 0 < i) (hi : i < k + 1) :
    w.q.nth i (by simp [hi]) =
        (w.nth (i - 1) (tsub_lt_iff_left (one_le_of_zero_lt i ipos) |>.mpr hi)).bShift := by
  rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
  · simp at ipos
  · simp [q_succ w (by simpa using hi)]

@[simp] lemma q_val_eq_qVec (w : L.SemitermVec k n) : w.q.val = L.qVec w.val := by
  simp [q, Language.qVec, Language.bvar, bShift, w.prop.lh]

end SemitermVec
end Language

namespace Language
namespace Semiterm

@[simp] lemma shift_bvar {z n : V} (hz : z < n) :
    shift (L.bvar z hz) = L.bvar z hz := by ext; simp [Language.bvar, shift]

@[simp] lemma shift_fvar (x : V) :
    shift (L.fvar x : L.Semiterm n) = L.fvar (x + 1) := by ext; simp [Language.fvar, shift]

@[simp] lemma shift_func {k f} (hf : L.Func k f) (v : L.SemitermVec k n) :
    shift (L.func hf v) = L.func hf v.shift := by
      ext; simp [Language.func, shift, SemitermVec.shift, hf]

@[simp] lemma bShift_bvar {z n : V} (hz : z < n) :
    bShift (L.bvar z hz) = L.bvar (z + 1) (by simpa using hz) := by
      ext; simp [Language.bvar, bShift]

@[simp] lemma bShift_fvar (x : V) :
    bShift (L.fvar x : L.Semiterm n) = L.fvar x := by ext; simp [Language.fvar, bShift]

@[simp] lemma bShift_func {k f} (hf : L.Func k f) (v : L.SemitermVec k n) :
    bShift (L.func hf v) = L.func hf v.bShift := by
      ext; simp [Language.func, bShift, SemitermVec.bShift, hf]

@[simp] lemma substs_bvar {z m : V} (w : L.SemitermVec n m) (hz : z < n) :
    (L.bvar z hz).substs w = w.nth z hz := by
      ext; simp [Language.bvar, substs, Language.SemitermVec.nth]

@[simp] lemma substs_fvar (w : L.SemitermVec n m) (x : V) :
    (L.fvar x : L.Semiterm n).substs w = L.fvar x := by ext; simp [Language.fvar, substs]

@[simp] lemma substs_func {k f} (w : L.SemitermVec n m) (hf : L.Func k f) (v : L.SemitermVec k n) :
    (L.func hf v).substs w = L.func hf (v.substs w) := by
  ext; simp [Language.func, substs, SemitermVec.substs, hf]

@[simp] lemma bShift_substs_q (t : L.Semiterm n) (w : L.SemitermVec n m) :
    t.bShift.substs w.q = (t.substs w).bShift := by
  ext; simp only [substs, SemitermVec.q_val_eq_qVec, bShift, substs_qVec_bShift t.prop w.prop]

@[simp] lemma bShift_substs_sing (t u : L.Term) : t.bShift.substs u.sing = t := by
  ext; simp only [val_substs, Semitermvec.val_cons, Semitermvec.val_nil, val_bShift]
  rw [substs_cons_bShift t.prop]; simp

lemma bShift_shift_comm (t : L.Semiterm n) : t.shift.bShift = t.bShift.shift := by
  ext; simp [termBShift_termShift t.prop]

end Semiterm
end Language

end «lp_section_1»

section «lp_section_2»

namespace Language
namespace Semiterm

/-- Imported declaration from the Incompleteness formalization. -/
def FVFree (t : L.Semiterm n) : Prop := L.IsTermFVFree n t.val

lemma _root_.LO.Arith.Language.Semiterm.FVFree.iff {t : L.Semiterm n} : t.FVFree ↔ t.shift = t := by
  simp [FVFree, Language.IsTermFVFree, Semiterm.ext_iff]

@[simp] lemma _root_.LO.Arith.Language.Semiterm.FVFree.bvar (z : V) (h : z < n) :
    (L.bvar z h).FVFree := by
  simp [FVFree, h]

@[simp] lemma _root_.LO.Arith.Language.Semiterm.FVFree.bShift (t : L.Semiterm n) (ht : t.FVFree) :
    t.bShift.FVFree := by simp [FVFree.iff, ←bShift_shift_comm, FVFree.iff.mp ht]

end Semiterm
end Language

end «lp_section_2»

namespace Formalized

/-- Imported declaration from the Incompleteness formalization. -/
def typedNumeral (n m : V) : ⌜ℒₒᵣ⌝.Semiterm n := ⟨numeral m, by simp⟩

/-- Imported declaration from the Incompleteness formalization. -/
def add {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiterm n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩

/-- Imported declaration from the Incompleteness formalization. -/
def mul {n : V} (t u : ⌜ℒₒᵣ⌝.Semiterm n) : ⌜ℒₒᵣ⌝.Semiterm n := ⟨t.val ^* u.val, by simp [qqMul]⟩

instance (n : V) : Add (⌜ℒₒᵣ⌝.Semiterm n) := ⟨add⟩

instance (n : V) : Mul (⌜ℒₒᵣ⌝.Semiterm n) := ⟨mul⟩

instance coeNumeral (n : V) : Coe V (⌜ℒₒᵣ⌝.Semiterm n) := ⟨typedNumeral n⟩

variable {n : V}

@[simp] lemma val_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.Semiterm n).val = numeral x := rfl

@[simp] lemma val_add (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl

@[simp] lemma val_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl

@[simp] lemma add_inj_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    t₁ + t₂ = u₁ + u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Language.Semiterm.ext_iff, qqAdd]

@[simp] lemma mul_inj_iff {t₁ t₂ u₁ u₂ : ⌜ℒₒᵣ⌝.Semiterm n} :
    t₁ * t₂ = u₁ * u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Language.Semiterm.ext_iff, qqMul]

@[simp] lemma subst_numeral {m n : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (x : V) :
    (↑x : ⌜ℒₒᵣ⌝.Semiterm n).substs w = ↑x := by
  ext; simp [Language.Semiterm.substs, numeral_substs w.prop]

@[simp] lemma subst_add {m n : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ + t₂).substs w = t₁.substs w + t₂.substs w := by
  ext; simp [qqAdd, Language.Semiterm.substs]

@[simp] lemma subst_mul {m n : V} (w : ⌜ℒₒᵣ⌝.SemitermVec n m) (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ * t₂).substs w = t₁.substs w * t₂.substs w := by
  ext; simp [qqMul, Language.Semiterm.substs]

@[simp] lemma shift_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.Semiterm n).shift = ↑x := by
  ext; simp [Language.Semiterm.shift]

@[simp] lemma shift_add (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ + t₂).shift = t₁.shift + t₂.shift := by
  ext; simp [qqAdd, Language.Semiterm.shift]

@[simp] lemma shift_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ * t₂).shift = t₁.shift * t₂.shift := by
  ext; simp [qqMul, Language.Semiterm.shift]

@[simp] lemma bShift_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.Semiterm n).bShift = ↑x := by
  ext; simp [Language.Semiterm.bShift]

@[simp] lemma bShift_add (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ + t₂).bShift = t₁.bShift + t₂.bShift := by
  ext; simp [qqAdd, Language.Semiterm.bShift]

@[simp] lemma bShift_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) : (t₁ * t₂).bShift = t₁.bShift * t₂.bShift := by
  ext; simp [qqMul, Language.Semiterm.bShift]

@[simp] lemma fvFree_numeral (x : V) : (↑x : ⌜ℒₒᵣ⌝.Semiterm n).FVFree := by
  simp [Language.Semiterm.FVFree.iff]

@[simp] lemma fvFree_add (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ + t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Language.Semiterm.FVFree.iff]

@[simp] lemma fvFree_mul (t₁ t₂ : ⌜ℒₒᵣ⌝.Semiterm n) :
    (t₁ * t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Language.Semiterm.FVFree.iff]


end Formalized

end Arith
end LO
