/-
Copyright (c) 2026 Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gregory Morse
-/
module

public import LeanPool.BooleanMultiplication.N4.NormalizedConstruction

/-!
# The degree-two Reed--Muller minimum word

This file supplies the algebraic flattening ingredient for quadratic Boolean
circuits.  Quadratic functions are stored recursively as

`q(x₀,x') = q₀(x') + x₀ a(x')`,

where `a` is affine.  The minimum-weight proof is therefore an induction on
variables, not an enumeration of eight-variable truth tables.
-/

public section

namespace UnrestrictedBooleanMul
namespace N4

noncomputable section

/-- Recursive squarefree encoding of an affine polynomial over the two-element field. -/
inductive AffineCode : Nat → Type
  | nil (c : F₂) : AffineCode 0
  | cons {n : Nat} (tail : AffineCode n) (head : F₂) : AffineCode (n + 1)
  deriving DecidableEq

/-- Recursive squarefree encoding of a polynomial of degree at most two. -/
inductive QuadraticCode : Nat → Type
  | nil (c : F₂) : QuadraticCode 0
  | cons {n : Nat} (tail : QuadraticCode n) (cross : AffineCode n) :
      QuadraticCode (n + 1)
  deriving DecidableEq

/-- Remove the first coordinate of a Boolean assignment. -/
def assignmentTail {n : Nat} (x : Fin (n + 1) → F₂) : Fin n → F₂ :=
  fun i => x i.succ

/-- Prepend one field element to a Boolean assignment. -/
@[expose]
def assignmentCons {n : Nat} (b : F₂) (x : Fin n → F₂) :
    Fin (n + 1) → F₂ := Fin.cases b x

@[simp] theorem assignmentCons_zero {n : Nat} (b : F₂) (x : Fin n → F₂) :
    assignmentCons b x 0 = b := rfl

@[simp] theorem assignmentCons_succ {n : Nat} (b : F₂) (x : Fin n → F₂)
    (i : Fin n) : assignmentCons b x i.succ = x i := rfl

@[simp] theorem assignmentTail_cons {n : Nat} (b : F₂) (x : Fin n → F₂) :
    assignmentTail (assignmentCons b x) = x := by
  funext i
  rfl

/-- Split a Boolean assignment into its first coordinate and its tail. -/
@[expose]
def assignmentEquiv (n : Nat) :
    (Fin (n + 1) → F₂) ≃ F₂ × (Fin n → F₂) where
  toFun x := (x 0, assignmentTail x)
  invFun z := assignmentCons z.1 z.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  right_inv z := by
    rcases z with ⟨b, x⟩
    rfl

/-- Evaluate a recursively encoded affine polynomial on a Boolean assignment. -/
@[expose]
def AffineCode.eval : {n : Nat} → AffineCode n → (Fin n → F₂) → F₂
  | 0, .nil c, _ => c
  | _ + 1, .cons tail head, x =>
      AffineCode.eval tail (assignmentTail x) + x 0 * head

/-- Evaluate a recursively encoded quadratic polynomial on a Boolean assignment. -/
@[expose]
def QuadraticCode.eval : {n : Nat} → QuadraticCode n → (Fin n → F₂) → F₂
  | 0, .nil c, _ => c
  | _ + 1, .cons tail cross, x =>
      QuadraticCode.eval tail (assignmentTail x) +
        x 0 * AffineCode.eval cross (assignmentTail x)

@[simp] theorem AffineCode.eval_nil (c : F₂) (x : Fin 0 → F₂) :
    (AffineCode.nil c).eval x = c := rfl

@[simp] theorem AffineCode.eval_cons {n : Nat} (a : AffineCode n) (d : F₂)
    (b : F₂) (x : Fin n → F₂) :
    (AffineCode.cons a d).eval (assignmentCons b x) =
      a.eval x + b * d := by
  rfl

@[simp] theorem QuadraticCode.eval_nil (c : F₂) (x : Fin 0 → F₂) :
    (QuadraticCode.nil c).eval x = c := rfl

@[simp] theorem QuadraticCode.eval_cons {n : Nat}
    (q : QuadraticCode n) (a : AffineCode n)
    (b : F₂) (x : Fin n → F₂) :
    (QuadraticCode.cons q a).eval (assignmentCons b x) =
      q.eval x + b * a.eval x := by
  rfl

/-- The natural-number indicator of a nonzero field element. -/
@[expose] def truthBit (a : F₂) : Nat := if a = 0 then 0 else 1

/-- The number of inputs on which a field-valued function is nonzero. -/
@[expose] def truthWeight {X : Type*} [Fintype X] (f : X → F₂) : Nat :=
  ∑ x, truthBit (f x)

theorem truthBit_zero : truthBit (0 : F₂) = 0 := by simp [truthBit]

theorem truthBit_one : truthBit (1 : F₂) = 1 := by simp [truthBit]

theorem truthWeight_assignment_split {n : Nat}
    (f : (Fin (n + 1) → F₂) → F₂) :
    truthWeight f =
      truthWeight (fun x => f (assignmentCons 0 x)) +
      truthWeight (fun x => f (assignmentCons 1 x)) := by
  unfold truthWeight
  rw [show (∑ x, truthBit (f x)) =
      ∑ z : F₂ × (Fin n → F₂),
        truthBit (f ((assignmentEquiv n).symm z)) by
    exact Fintype.sum_equiv (assignmentEquiv n)
      (fun x => truthBit (f x))
      (fun z => truthBit (f ((assignmentEquiv n).symm z)))
      (fun x => congrArg (fun y => truthBit (f y))
        ((assignmentEquiv n).symm_apply_apply x).symm)]
  rw [Fintype.sum_prod_type]
  rw [show (Finset.univ : Finset F₂) = {0, 1} by decide]
  simp [assignmentEquiv]

/-- The recursively encoded zero affine polynomial. -/
def AffineCode.zero : (n : Nat) → AffineCode n
  | 0 => .nil 0
  | _ + 1 => .cons (AffineCode.zero _) 0

/-- The recursively encoded constant affine polynomial. -/
def AffineCode.const : (n : Nat) → F₂ → AffineCode n
  | 0, c => .nil c
  | _ + 1, c => .cons (AffineCode.const _ c) 0

/-- Coefficientwise addition of recursively encoded affine polynomials. -/
def AffineCode.add : {n : Nat} → AffineCode n → AffineCode n → AffineCode n
  | 0, .nil a, .nil b => .nil (a + b)
  | _ + 1, .cons a x, .cons b y => .cons (a.add b) (x + y)

/-- The recursively encoded zero quadratic polynomial. -/
def QuadraticCode.zero : (n : Nat) → QuadraticCode n
  | 0 => .nil 0
  | _ + 1 => .cons (QuadraticCode.zero _) (AffineCode.zero _)

/-- Coefficientwise addition of recursively encoded quadratic polynomials. -/
def QuadraticCode.add : {n : Nat} →
    QuadraticCode n → QuadraticCode n → QuadraticCode n
  | 0, .nil a, .nil b => .nil (a + b)
  | _ + 1, .cons q a, .cons r b => .cons (q.add r) (a.add b)

/-- View an affine polynomial as a quadratic polynomial. -/
def AffineCode.toQuadratic : {n : Nat} → AffineCode n → QuadraticCode n
  | 0, .nil a => .nil a
  | _ + 1, .cons a d =>
      .cons a.toQuadratic (AffineCode.const _ d)

@[simp] theorem AffineCode.eval_zero {n : Nat} (x : Fin n → F₂) :
    (AffineCode.zero n).eval x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.zero, ih]

@[simp] theorem AffineCode.eval_const {n : Nat} (c : F₂) (x : Fin n → F₂) :
    (AffineCode.const n c).eval x = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.const, ih]

@[simp] theorem AffineCode.eval_add {n : Nat} (a b : AffineCode n)
    (x : Fin n → F₂) : (a.add b).eval x = a.eval x + b.eval x := by
  induction n with
  | zero =>
      rcases a with ⟨a⟩
      rcases b with ⟨b⟩
      rfl
  | succ n ih =>
      rcases a with ⟨a, da⟩
      rcases b with ⟨b, db⟩
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.add, ih]
      ring

@[simp] theorem QuadraticCode.eval_zero {n : Nat} (x : Fin n → F₂) :
    (QuadraticCode.zero n).eval x = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [QuadraticCode.zero, ih]

@[simp] theorem QuadraticCode.eval_add {n : Nat} (q r : QuadraticCode n)
    (x : Fin n → F₂) : (q.add r).eval x = q.eval x + r.eval x := by
  induction n with
  | zero =>
      rcases q with ⟨q⟩
      rcases r with ⟨r⟩
      rfl
  | succ n ih =>
      rcases q with ⟨q, a⟩
      rcases r with ⟨r, b⟩
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [QuadraticCode.add, ih]
      ring

@[simp] theorem AffineCode.eval_toQuadratic {n : Nat} (a : AffineCode n)
    (x : Fin n → F₂) : a.toQuadratic.eval x = a.eval x := by
  induction n with
  | zero =>
      rcases a with ⟨a⟩
      rfl
  | succ n ih =>
      rcases a with ⟨a, d⟩
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.toQuadratic, ih]

theorem AffineCode.eval_injective {n : Nat} :
    Function.Injective (fun a : AffineCode n => a.eval) := by
  intro a
  induction a with
  | nil c =>
      intro b h
      cases b with
      | nil d =>
          congr
          exact congrFun h (fun i => Fin.elim0 i)
  | @cons n a da ih =>
      intro b h
      cases b with
      | cons b db =>
          have hab : a = b := ih (by
            funext x
            have hx := congrFun h (assignmentCons 0 x)
            simpa using hx)
          subst b
          congr
          have hx := congrFun h (assignmentCons 1 (fun _ => 0))
          simpa using hx

/-- At least one linear coefficient of the affine code is nonzero. -/
def AffineCode.Nonconstant : {n : Nat} → AffineCode n → Prop
  | 0, _ => False
  | _ + 1, .cons a d => a.Nonconstant ∨ d ≠ 0

theorem AffineCode.exists_eval_zero_of_nonconstant {n : Nat}
    {a : AffineCode n} (ha : a.Nonconstant) :
    ∃ x : Fin n → F₂, a.eval x = 0 := by
  induction a with
  | nil c => simp [AffineCode.Nonconstant] at ha
  | @cons n a d ih =>
      rcases ha with ha | hd
      · rcases ih ha with ⟨x, hx⟩
        exact ⟨assignmentCons 0 x, by simp [hx]⟩
      · have hd1 : d = 1 := (f2_eq_zero_or_one d).resolve_left hd
        let x : Fin n → F₂ := fun _ => 0
        exact ⟨assignmentCons (a.eval x) x, by
          change a.eval x + a.eval x * d = 0
          rw [hd1, mul_one]
          exact CharTwo.add_self_eq_zero _⟩

theorem AffineCode.weight_nonconstant {n : Nat} {a : AffineCode n}
    (ha : a.Nonconstant) :
    truthWeight a.eval = 2 ^ (n - 1) := by
  induction a with
  | nil c => simp [AffineCode.Nonconstant] at ha
  | @cons n a d ih =>
      rw [truthWeight_assignment_split]
      simp only [AffineCode.eval_cons, zero_mul, add_zero, one_mul]
      rcases f2_eq_zero_or_one d with rfl | rfl
      · have ha' : a.Nonconstant := by
          simpa [AffineCode.Nonconstant] using ha
        simp only [add_zero]
        rw [ih ha']
        have hn : 0 < n := by
          by_contra hn
          have : n = 0 := Nat.eq_zero_of_not_pos hn
          subst n
          simp [AffineCode.Nonconstant] at ha'
        calc
          2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n - 1) * 2 := by omega
          _ = 2 ^ ((n - 1) + 1) := (pow_succ 2 (n - 1)).symm
          _ = 2 ^ n := by congr; omega
      · have hpoint (x : Fin n → F₂) :
            truthBit (a.eval x) + truthBit (a.eval x + 1) = 1 := by
          have h11 : (1 : F₂) + 1 = 0 := CharTwo.add_self_eq_zero 1
          rcases f2_eq_zero_or_one (a.eval x) with hx | hx <;>
            simp [hx, h11, truthBit]
        unfold truthWeight
        rw [← Finset.sum_add_distrib]
        simp_rw [hpoint]
        simp

theorem truthWeight_pos_of_exists {X : Type*} [Fintype X]
    {f : X → F₂} (h : ∃ x, f x ≠ 0) :
    0 < truthWeight f := by
  rcases h with ⟨x, hx⟩
  unfold truthWeight
  apply Finset.sum_pos' (fun _ _ => Nat.zero_le _)
  exact ⟨x, Finset.mem_univ x, by simp [truthBit, hx]⟩

theorem AffineCode.eval_eq_of_not_nonconstant {n : Nat} {a : AffineCode n}
    (ha : ¬ a.Nonconstant) (x y : Fin n → F₂) :
    a.eval x = a.eval y := by
  induction a with
  | nil c => rfl
  | @cons n a d ih =>
      have ha0 : ¬ a.Nonconstant := by
        intro h
        exact ha (Or.inl h)
      have hd0 : d = 0 := by
        by_contra hd
        exact ha (Or.inr hd)
      simp only [AffineCode.eval, hd0, mul_zero, add_zero]
      exact ih ha0 (assignmentTail x) (assignmentTail y)

theorem AffineCode.weight_nonzero_lower {n : Nat} {a : AffineCode n}
    (ha : ∃ x, a.eval x ≠ 0) :
    2 ^ (n - 1) ≤ truthWeight a.eval := by
  by_cases hnc : a.Nonconstant
  · rw [a.weight_nonconstant hnc]
  · rcases ha with ⟨x, hx⟩
    have hall (y : Fin n → F₂) : a.eval y ≠ 0 := by
      intro hy
      apply hx
      calc
        a.eval x = a.eval y := a.eval_eq_of_not_nonconstant hnc x y
        _ = 0 := hy
    unfold truthWeight
    simp only [truthBit, ite_eq_right (hall _), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    simp only [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    exact Nat.pow_le_pow_right (by omega) (Nat.sub_le n 1)

theorem f2_eq_iff_add_eq_zero (u v : F₂) : u = v ↔ u + v = 0 := by
  decide +revert

theorem AffineCode.eq_zero_or_eq_of_vanishes {n : Nat}
    {a c : AffineCode n} (ha : a.Nonconstant)
    (h : ∀ x, a.eval x = 0 → c.eval x = 0) :
    c = AffineCode.zero n ∨ c = a := by
  induction a with
  | nil k => simp [AffineCode.Nonconstant] at ha
  | @cons n a d ih =>
      cases c with
      | cons c e =>
          rcases f2_eq_zero_or_one d with rfl | rfl
          · have ha' : a.Nonconstant := by
              simpa [AffineCode.Nonconstant] using ha
            have htail : ∀ x, a.eval x = 0 → c.eval x = 0 := by
              intro x hx
              have hc := h (assignmentCons 0 x) (by simp [hx])
              simpa using hc
            rcases ih ha' htail with hc | hc
            · have he : e = 0 := by
                rcases a.exists_eval_zero_of_nonconstant ha' with ⟨x, hx⟩
                have hz := h (assignmentCons 1 x) (by simp [hx])
                subst c
                simpa [hx] using hz
              left
              subst c
              subst e
              simp [AffineCode.zero]
            · have he : e = 0 := by
                rcases a.exists_eval_zero_of_nonconstant ha' with ⟨x, hx⟩
                have hz := h (assignmentCons 1 x) (by simp [hx])
                subst c
                simpa [hx] using hz
              right
              subst c
              subst e
              rfl
          · have hzero (x : Fin n → F₂) :
                (AffineCode.cons a 1).eval
                    (assignmentCons (a.eval x) x) = 0 := by
              simp only [AffineCode.eval_cons, mul_one]
              exact CharTwo.add_self_eq_zero _
            have hrel (x : Fin n → F₂) :
                c.eval x + a.eval x * e = 0 := by
              simpa using h (assignmentCons (a.eval x) x) (hzero x)
            rcases f2_eq_zero_or_one e with rfl | rfl
            · left
              have hc : c = AffineCode.zero n := AffineCode.eval_injective (by
                funext x
                simpa using hrel x)
              subst c
              simp [AffineCode.zero]
            · right
              have hc : c = a := AffineCode.eval_injective (by
                funext x
                exact (f2_eq_iff_add_eq_zero _ _).2 (by simpa using hrel x))
              subst c
              rfl

theorem QuadraticCode.factor_of_vanishes {n : Nat}
    {a : AffineCode n} (ha : a.Nonconstant) {q : QuadraticCode n}
    (h : ∀ x, a.eval x = 0 → q.eval x = 0) :
    ∃ b : AffineCode n, ∀ x, q.eval x = a.eval x * b.eval x := by
  induction a with
  | nil k => simp [AffineCode.Nonconstant] at ha
  | @cons n a d ih =>
      cases q with
      | cons q c =>
          rcases f2_eq_zero_or_one d with rfl | rfl
          · have ha' : a.Nonconstant := by
              simpa [AffineCode.Nonconstant] using ha
            have hq : ∀ x, a.eval x = 0 → q.eval x = 0 := by
              intro x hx
              simpa using h (assignmentCons 0 x) (by simp [hx])
            rcases ih ha' hq with ⟨b, hb⟩
            have hc : ∀ x, a.eval x = 0 → c.eval x = 0 := by
              intro x hx
              have hz := h (assignmentCons 1 x) (by simp [hx])
              have hqx : q.eval x = 0 := by simp [hb x, hx]
              simpa [hqx] using hz
            rcases a.eq_zero_or_eq_of_vanishes ha' hc with hc | hc
            · refine ⟨AffineCode.cons b 0, ?_⟩
              intro x
              rw [show x = assignmentCons (x 0) (assignmentTail x) by
                exact (assignmentEquiv n).symm_apply_apply x |>.symm]
              subst c
              simp [hb]
            · refine ⟨AffineCode.cons b 1, ?_⟩
              intro x
              rw [show x = assignmentCons (x 0) (assignmentTail x) by
                exact (assignmentEquiv n).symm_apply_apply x |>.symm]
              subst c
              simp [hb]
              ring
          · have hrel (x : Fin n → F₂) :
                q.eval x = a.eval x * c.eval x := by
              have haZero : (AffineCode.cons a 1).eval
                    (assignmentCons (a.eval x) x) = 0 := by
                simp only [AffineCode.eval_cons, mul_one]
                exact CharTwo.add_self_eq_zero _
              have hqc := h (assignmentCons (a.eval x) x) haZero
              exact (f2_eq_iff_add_eq_zero _ _).2 (by simpa [mul_comm] using hqc)
            refine ⟨AffineCode.cons c 0, ?_⟩
            intro x
            rw [show x = assignmentCons (x 0) (assignmentTail x) by
              exact (assignmentEquiv n).symm_apply_apply x |>.symm]
            simp [hrel]
            ring

theorem truthBit_pair_identity (u v : F₂) :
    truthBit u + truthBit (u + v) =
      truthBit v + 2 * (if v = 0 then truthBit u else 0) := by
  decide +revert

theorem truthWeight_pair_identity {X : Type*} [Fintype X]
    (f g : X → F₂) :
    truthWeight f + truthWeight (fun x => f x + g x) =
      truthWeight g +
        2 * ∑ x, if g x = 0 then truthBit (f x) else 0 := by
  unfold truthWeight
  rw [← Finset.sum_add_distrib]
  simp_rw [truthBit_pair_identity]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum]

theorem truthWeight_pair_ge {X : Type*} [Fintype X]
    (f g : X → F₂) :
    truthWeight g ≤ truthWeight f + truthWeight (fun x => f x + g x) := by
  rw [truthWeight_pair_identity]
  omega

theorem vanishes_of_truthWeight_pair_eq {X : Type*} [Fintype X]
    {f g : X → F₂}
    (h : truthWeight f + truthWeight (fun x => f x + g x) =
      truthWeight g) :
    ∀ x, g x = 0 → f x = 0 := by
  have hid := truthWeight_pair_identity f g
  have hextra : (∑ x, if g x = 0 then truthBit (f x) else 0) = 0 := by
    omega
  intro x hg
  have hx := (Finset.sum_eq_zero_iff_of_nonneg
    (fun _ _ => Nat.zero_le _)).mp hextra x (Finset.mem_univ x)
  by_contra hf
  simp [hg, truthBit, hf] at hx

theorem QuadraticCode.minimum_weight {n : Nat} (hn : 2 ≤ n)
    {q : QuadraticCode n} (hq : ∃ x, q.eval x ≠ 0) :
    2 ^ (n - 2) ≤ truthWeight q.eval := by
  induction q with
  | nil c => omega
  | @cons n q a ih =>
      rw [truthWeight_assignment_split]
      simp only [QuadraticCode.eval_cons, zero_mul, add_zero, one_mul]
      by_cases hn1 : n = 1
      · subst n
        have hpos : 0 < truthWeight (QuadraticCode.cons q a).eval :=
          truthWeight_pos_of_exists hq
        have hsplit : truthWeight (QuadraticCode.cons q a).eval =
            truthWeight q.eval + truthWeight (fun x => q.eval x + a.eval x) := by
          rw [truthWeight_assignment_split]
          simp
        calc
          1 ≤ truthWeight (QuadraticCode.cons q a).eval := hpos
          _ = truthWeight q.eval +
              truthWeight (fun x => q.eval x + a.eval x) := hsplit
      · have hn2 : 2 ≤ n := by omega
        by_cases ha : ∃ x, a.eval x ≠ 0
        · have halow := a.weight_nonzero_lower ha
          have hpair := truthWeight_pair_ge q.eval a.eval
          have hexp : n + 1 - 2 = n - 1 := by omega
          rw [hexp]
          exact halow.trans hpair
        · push Not at ha
          have hqnz : ∃ x, q.eval x ≠ 0 := by
            rcases hq with ⟨x, hx⟩
            refine ⟨assignmentTail x, ?_⟩
            intro hzero
            apply hx
            rw [show x = assignmentCons (x 0) (assignmentTail x) by
              exact (assignmentEquiv n).symm_apply_apply x |>.symm]
            simp [hzero, ha]
          have hlow := ih hn2 hqnz
          simp_rw [ha, add_zero]
          calc
            2 ^ (n + 1 - 2) = 2 ^ (n - 1) :=
              congrArg (fun k : Nat => 2 ^ k) (by omega)
            _ = 2 ^ ((n - 2) + 1) :=
              congrArg (fun k : Nat => 2 ^ k) (by omega)
            _ = 2 ^ (n - 2) * 2 := pow_succ 2 (n - 2)
            _ ≤ truthWeight q.eval + truthWeight q.eval := by
              simpa [mul_two] using Nat.add_le_add hlow hlow

theorem AffineCode.weight_eq_full_of_not_nonconstant {n : Nat}
    {a : AffineCode n} (hnc : ¬ a.Nonconstant)
    (ha : ∃ x, a.eval x ≠ 0) :
    truthWeight a.eval = 2 ^ n := by
  rcases ha with ⟨x, hx⟩
  have hall (y : Fin n → F₂) : a.eval y ≠ 0 := by
    intro hy
    apply hx
    calc
      a.eval x = a.eval y := a.eval_eq_of_not_nonconstant hnc x y
      _ = 0 := hy
  unfold truthWeight
  simp only [truthBit, ite_eq_right (hall _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, Fintype.card_fun, Fintype.card_fin, ZMod.card]
  norm_num

theorem QuadraticCode.minimum_word_factor {n : Nat} (hn : 2 ≤ n)
    {q : QuadraticCode n} (hq : ∃ x, q.eval x ≠ 0)
    (hweight : truthWeight q.eval = 2 ^ (n - 2)) :
    ∃ a b : AffineCode n, ∀ x, q.eval x = a.eval x * b.eval x := by
  induction q with
  | nil c => omega
  | @cons n q c ih =>
      have hnpos : 1 ≤ n := by omega
      have hsplit : truthWeight (QuadraticCode.cons q c).eval =
          truthWeight q.eval + truthWeight (fun x => q.eval x + c.eval x) := by
        rw [truthWeight_assignment_split]
        simp
      have hexp : n + 1 - 2 = n - 1 := by omega
      have htotal :
          truthWeight q.eval + truthWeight (fun x => q.eval x + c.eval x) =
            2 ^ (n - 1) := by
        calc
          _ = truthWeight (QuadraticCode.cons q c).eval := hsplit.symm
          _ = 2 ^ (n + 1 - 2) := hweight
          _ = 2 ^ (n - 1) := congrArg (fun k : Nat => 2 ^ k) hexp
      by_cases hc : ∃ x, c.eval x ≠ 0
      · have hclow := c.weight_nonzero_lower hc
        have hpair := truthWeight_pair_ge q.eval c.eval
        have hcweight : truthWeight c.eval = 2 ^ (n - 1) := by omega
        have hpairsame :
            truthWeight q.eval + truthWeight (fun x => q.eval x + c.eval x) =
              truthWeight c.eval := by omega
        have hcnc : c.Nonconstant := by
          by_contra hnc
          have hcfull := c.weight_eq_full_of_not_nonconstant hnc hc
          have hnform : n = (n - 1) + 1 := by omega
          have hp : 0 < 2 ^ (n - 1) := pow_pos (by omega : (0 : Nat) < 2) _
          have hpow : 2 ^ n = 2 ^ (n - 1) * 2 := by
            calc
              2 ^ n = 2 ^ ((n - 1) + 1) :=
                congrArg (fun k : Nat => 2 ^ k) hnform
              _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
          omega
        have hvanish : ∀ x, c.eval x = 0 → q.eval x = 0 :=
          vanishes_of_truthWeight_pair_eq hpairsame
        rcases QuadraticCode.factor_of_vanishes hcnc hvanish with ⟨b, hb⟩
        refine ⟨AffineCode.cons c 0, AffineCode.cons b 1, ?_⟩
        intro x
        rw [show x = assignmentCons (x 0) (assignmentTail x) by
          exact (assignmentEquiv n).symm_apply_apply x |>.symm]
        simp [hb]
        ring
      · push Not at hc
        have hqnz : ∃ x, q.eval x ≠ 0 := by
          rcases hq with ⟨x, hx⟩
          refine ⟨assignmentTail x, ?_⟩
          intro hzero
          apply hx
          rw [show x = assignmentCons (x 0) (assignmentTail x) by
            exact (assignmentEquiv n).symm_apply_apply x |>.symm]
          simp [hzero, hc]
        have hzeroPair :
            truthWeight q.eval + truthWeight (fun x => q.eval x + c.eval x) =
              truthWeight q.eval + truthWeight q.eval := by
          congr 1
          congr 1
          funext x
          rw [hc x, add_zero]
        by_cases hn1 : n = 1
        · subst n
          norm_num at htotal
          omega
        · have hn2 : 2 ≤ n := by omega
          have hqweight : truthWeight q.eval = 2 ^ (n - 2) := by
            have hpow : 2 ^ (n - 1) = 2 ^ (n - 2) * 2 := by
              calc
                2 ^ (n - 1) = 2 ^ ((n - 2) + 1) :=
                  congrArg (fun k : Nat => 2 ^ k) (by omega)
                _ = 2 ^ (n - 2) * 2 := pow_succ 2 (n - 2)
            omega
          rcases ih hn2 hqnz hqweight with ⟨a, b, hab⟩
          refine ⟨AffineCode.cons a 0, AffineCode.cons b 0, ?_⟩
          intro x
          rw [show x = assignmentCons (x 0) (assignmentTail x) by
            exact (assignmentEquiv n).symm_apply_apply x |>.symm]
          simp [hc, hab]

theorem QuadraticCode.eval_injective {n : Nat} :
    Function.Injective (fun q : QuadraticCode n => q.eval) := by
  intro q
  induction q with
  | nil c =>
      intro r h
      cases r with
      | nil d =>
          congr
          exact congrFun h (fun i => Fin.elim0 i)
  | @cons n q a ih =>
      intro r h
      cases r with
      | cons r b =>
          have hqr : q = r := ih (by
            funext x
            have hx := congrFun h (assignmentCons 0 x)
            simpa using hx)
          subst r
          congr
          apply AffineCode.eval_injective
          funext x
          have hx := congrFun h (assignmentCons 1 x)
          simpa using add_left_cancel hx

/-- Multiply every affine coefficient by a field scalar. -/
def AffineCode.smul (k : F₂) : {n : Nat} → AffineCode n → AffineCode n
  | 0, .nil c => .nil (k * c)
  | _ + 1, .cons a d => .cons (a.smul k) (k * d)

/-- Multiply every quadratic coefficient by a field scalar. -/
def QuadraticCode.smul (k : F₂) : {n : Nat} →
    QuadraticCode n → QuadraticCode n
  | 0, .nil c => .nil (k * c)
  | _ + 1, .cons q a => .cons (q.smul k) (a.smul k)

@[simp] theorem AffineCode.eval_smul {n : Nat} (k : F₂)
    (a : AffineCode n) (x : Fin n → F₂) :
    (a.smul k).eval x = k * a.eval x := by
  induction a with
  | nil c => rfl
  | @cons n a d ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [AffineCode.smul, ih]
      ring

@[simp] theorem QuadraticCode.eval_smul {n : Nat} (k : F₂)
    (q : QuadraticCode n) (x : Fin n → F₂) :
    (q.smul k).eval x = k * q.eval x := by
  induction q with
  | nil c => rfl
  | @cons n q a ih =>
      rw [show x = assignmentCons (x 0) (assignmentTail x) by
        exact (assignmentEquiv n).symm_apply_apply x |>.symm]
      simp [QuadraticCode.smul, ih]
      ring

theorem f2_mul_self (u : F₂) : u * u = u := by
  decide +revert

/-- Encode the Boolean product of two affine polynomials as a quadratic polynomial. -/
def QuadraticCode.mulAffine : {n : Nat} →
    AffineCode n → AffineCode n → QuadraticCode n
  | 0, .nil a, .nil b => .nil (a * b)
  | _ + 1, .cons a d, .cons b e =>
      .cons (QuadraticCode.mulAffine a b)
        ((b.smul d).add ((a.smul e).add (AffineCode.const _ (d * e))))

@[simp] theorem QuadraticCode.eval_mulAffine {n : Nat}
    (a b : AffineCode n) (x : Fin n → F₂) :
    (QuadraticCode.mulAffine a b).eval x = a.eval x * b.eval x := by
  induction a with
  | nil c =>
      cases b
      rfl
  | @cons n a d ih =>
      cases b with
      | cons b e =>
          rw [show x = assignmentCons (x 0) (assignmentTail x) by
            exact (assignmentEquiv n).symm_apply_apply x |>.symm]
          simp only [mulAffine, eval_cons, ih, AffineCode.eval_add, AffineCode.eval_smul,
            AffineCode.eval_const, AffineCode.eval_cons]
          have hx : x 0 * x 0 = x 0 := f2_mul_self (x 0)
          calc
            a.eval (assignmentTail x) * b.eval (assignmentTail x) +
                x 0 * (d * b.eval (assignmentTail x) +
                  (e * a.eval (assignmentTail x) + d * e)) =
              a.eval (assignmentTail x) * b.eval (assignmentTail x) +
                x 0 * d * b.eval (assignmentTail x) +
                x 0 * e * a.eval (assignmentTail x) + x 0 * d * e := by ring
            _ = a.eval (assignmentTail x) * b.eval (assignmentTail x) +
                x 0 * d * b.eval (assignmentTail x) +
                x 0 * e * a.eval (assignmentTail x) +
                  (x 0 * x 0) * d * e := by rw [hx]
            _ = (a.eval (assignmentTail x) + x 0 * d) *
                (b.eval (assignmentTail x) + x 0 * e) := by ring


end

end N4
end UnrestrictedBooleanMul
