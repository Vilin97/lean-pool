/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Kernel-checked affine covering certificates

This module is the arithmetic trust boundary for the external cone-covering
kernel.  An affine form has integral coefficients and is evaluated only on an
integral point.  A cone is a finite conjunction of inequalities `a(x) >= 0`.

The external program may emit a passive contradiction tree.  Branching on a
form `a` adds its exact integral complement

`-a(x) - 1 >= 0`.

Leaves carry sparse rational Farkas multipliers.  The executable checker
verifies their signs, the vanishing of every variable coefficient, and a
strictly negative constant sum.  The soundness theorem proves that an accepted
tree covers every integral point of the advertised base region by at least one
advertised cone.  No linear-programming algorithm is trusted or implemented
here.

Row numbering agrees directly with the external C emitter: base-region rows
come first, followed by asserted violation rows in root-to-leaf branch order.
Thus a branch extends the active row list by appending its violation, rather
than prepending it.

This layer deliberately gives no graph, subdivision, or divisor semantics to
the cones.  Those belong in a separate local-certificate checker.
-/

namespace Utilities.Certificate.AffineCover

open Finset

/-! ## Proof-free finite Boolean folds -/

/-- Boolean universal quantification over `Fin k`, implemented as a list fold
rather than a proof-producing `Decidable` computation. -/
def allFin {k : ℕ} (test : Fin k → Bool) : Bool :=
  (List.ofFn test).all id

@[simp] theorem allFin_eq_true_iff {k : ℕ} (test : Fin k → Bool) :
    allFin test = true ↔ ∀ index : Fin k, test index = true := by
  simp [allFin, List.all_eq_true]

/-- Boolean universal quantification over an arbitrary finite set.  `Finset.fold`
keeps kernel evaluation proof-free even when the element type itself is a
finite combinatorial object such as `Finset (Fin n)`. -/
def allFinset {α : Type*} [DecidableEq α]
    (elements : Finset α) (test : α → Bool) : Bool :=
  elements.fold (fun left right => left && right) true test

@[simp] theorem allFinset_eq_true_iff {α : Type*} [DecidableEq α]
    (elements : Finset α) (test : α → Bool) :
    allFinset elements test = true ↔
      ∀ element ∈ elements, test element = true := by
  induction elements using Finset.induction_on with
  | empty => simp [allFinset]
  | @insert element elements hNotMem inductionHypothesis =>
      rw [allFinset, Finset.fold_insert hNotMem]
      change (test element && allFinset elements test) = true ↔ _
      rw [Bool.and_eq_true, inductionHypothesis]
      simp

/-- An integral affine form in `m` variables. -/
structure AffineForm (m : ℕ) where
  fixedValue : ℤ
  coefficient : Fin m → ℤ
  deriving DecidableEq

namespace AffineForm

variable {m : ℕ}

instance : Zero (AffineForm m) where
  zero := ⟨0, fun _ => 0⟩

/-- Proof-free extensional equality for integral affine forms.  In particular,
this avoids asking `Decidable` to construct an equality proof between two
function-valued coefficient fields while a large generated certificate is
being reduced by the kernel. -/
def equal (left right : AffineForm m) : Bool :=
  decide (left.fixedValue = right.fixedValue) &&
    allFin fun coordinate =>
      decide (left.coefficient coordinate = right.coefficient coordinate)

@[simp] theorem equal_eq_true_iff (left right : AffineForm m) :
    equal left right = true ↔ left = right := by
  constructor
  · intro hEqual
    simp only [equal, Bool.and_eq_true] at hEqual
    rcases hEqual with ⟨hConstant, hCoefficient⟩
    rcases left with ⟨leftConstant, leftCoefficient⟩
    rcases right with ⟨rightConstant, rightCoefficient⟩
    have hConstant' : leftConstant = rightConstant :=
      of_decide_eq_true hConstant
    have hCoefficient' : leftCoefficient = rightCoefficient := by
      funext coordinate
      exact of_decide_eq_true
        ((allFin_eq_true_iff _).mp hCoefficient coordinate)
    cases hConstant'
    cases hCoefficient'
    rfl
  · rintro rfl
    simp [equal]

/-- Proof-free list membership for integral affine forms. -/
def mem (form : AffineForm m) (forms : List (AffineForm m)) : Bool :=
  forms.any fun candidate => equal form candidate

@[simp] theorem mem_eq_true_iff (form : AffineForm m)
    (forms : List (AffineForm m)) :
    mem form forms = true ↔ form ∈ forms := by
  simp [mem]

/-- Evaluation of an integral affine form at an integral point. -/
def eval (form : AffineForm m) (point : Fin m → ℤ) : ℤ :=
  form.fixedValue + ∑ i, form.coefficient i * point i

/-- The closed integral inequality represented by an affine form. -/
def Holds (form : AffineForm m) (point : Fin m → ℤ) : Prop :=
  0 ≤ form.eval point

/-- The exact closed complement of `form.Holds` on integral points.

If `a(x) >= 0` fails and `a(x)` is integral, then `a(x) <= -1`, equivalently
`-a(x)-1 >= 0`. -/
def violation (form : AffineForm m) : AffineForm m where
  fixedValue := -form.fixedValue - 1
  coefficient := fun i => -form.coefficient i

@[simp] theorem eval_zero (point : Fin m → ℤ) :
    (0 : AffineForm m).eval point = 0 := by
  change 0 + ∑ _i : Fin m, 0 * point _i = 0
  simp

@[simp] theorem eval_violation (form : AffineForm m)
    (point : Fin m → ℤ) :
    form.violation.eval point = -form.eval point - 1 := by
  simp only [violation, eval, neg_mul]
  rw [Finset.sum_neg_distrib]
  ring

@[simp] theorem holds_violation_iff_not (form : AffineForm m)
    (point : Fin m → ℤ) :
    form.violation.Holds point ↔ ¬form.Holds point := by
  rw [Holds, Holds, eval_violation]
  omega

/-- Rational evaluation, used only in the proof of Farkas soundness. -/
def evalRat (form : AffineForm m) (point : Fin m → ℤ) : ℚ :=
  (form.fixedValue : ℚ) +
    ∑ i, (form.coefficient i : ℚ) * (point i : ℚ)

@[simp] theorem evalRat_eq_cast_eval (form : AffineForm m)
    (point : Fin m → ℤ) :
    form.evalRat point = (form.eval point : ℚ) := by
  simp [evalRat, eval]

end AffineForm

/-- A finite conjunction of affine inequalities.  This is used for base
regions and for individual proof cones. -/
def FormsHold {m : ℕ} (forms : List (AffineForm m))
    (point : Fin m → ℤ) : Prop :=
  ∀ form ∈ forms, form.Holds point

/-- A family of cones covers a base region at every integral point. -/
def Covers {m : ℕ} (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Prop :=
  ∀ point : Fin m → ℤ, FormsHold base point →
    ∃ cone ∈ cones, FormsHold cone point

/-- One sparse rational multiplier names a row of the current region. -/
structure FarkasTerm where
  row : ℕ
  weight : ℚ
  deriving DecidableEq, Repr

/-- Passive sparse Farkas data.  Repeated row indices are permitted. -/
structure FarkasData where
  terms : List FarkasTerm
  deriving DecidableEq, Repr

namespace FarkasData

variable {m : ℕ}

def rowAt (rows : List (AffineForm m)) (index : ℕ) : AffineForm m :=
  rows.getD index 0

/-- Sum of the constant coefficients in the proposed Farkas combination. -/
def constantSum (data : FarkasData) (rows : List (AffineForm m)) : ℚ :=
  (data.terms.map fun term =>
    term.weight * ((rowAt rows term.row).fixedValue : ℚ)).sum

/-- Sum of one variable coefficient in the proposed Farkas combination. -/
def coefficientSum (data : FarkasData) (rows : List (AffineForm m))
    (coordinate : Fin m) : ℚ :=
  (data.terms.map fun term =>
    term.weight *
      ((rowAt rows term.row).coefficient coordinate : ℚ)).sum

/-- Mathematical validity of sparse Farkas data for the displayed rows. -/
def Valid (data : FarkasData) (rows : List (AffineForm m)) : Prop :=
  (∀ term ∈ data.terms,
    term.row < rows.length ∧ 0 ≤ term.weight) ∧
  (∀ coordinate : Fin m, data.coefficientSum rows coordinate = 0) ∧
  data.constantSum rows < 0

/-- Whether every sparse multiplier is integral.  External emitters may always
clear denominators within one homogeneous Farkas contradiction. -/
def integralWeights (data : FarkasData) : Bool :=
  data.terms.all fun term => decide (term.weight.den = 1)

@[simp] theorem integralWeights_eq_true_iff (data : FarkasData) :
    data.integralWeights = true ↔
      ∀ term ∈ data.terms, term.weight.den = 1 := by
  simp [integralWeights, List.all_eq_true]

/-- Integer coefficient sum used by the kernel-reduction fast path. -/
def coefficientSumInt (data : FarkasData)
    (rows : List (AffineForm m)) (coordinate : Fin m) : ℤ :=
  (data.terms.map fun term =>
    term.weight.num * (rowAt rows term.row).coefficient coordinate).sum

/-- Integer constant sum used by the kernel-reduction fast path. -/
def constantSumInt (data : FarkasData) (rows : List (AffineForm m)) : ℤ :=
  (data.terms.map fun term =>
    term.weight.num * (rowAt rows term.row).fixedValue).sum

/-- Proof-free arithmetic replay for a leaf whose multipliers have denominator
one.  Unlike rational multiplication and addition, these integer operations
are transparent to ordinary kernel reduction. -/
def integralCheck (data : FarkasData)
    (rows : List (AffineForm m)) : Bool :=
  (data.terms.all fun term =>
    decide (term.row < rows.length ∧ 0 ≤ term.weight.num)) &&
  (allFin fun coordinate : Fin m =>
    decide (data.coefficientSumInt rows coordinate = 0)) &&
  decide (data.constantSumInt rows < 0)

private theorem weight_eq_intCast_of_den_eq_one (weight : ℚ)
    (hDenominator : weight.den = 1) :
    weight = (weight.num : ℚ) := by
  apply Rat.ext
  · rfl
  · simpa using hDenominator

private theorem coefficientSumInt_aux
    (terms : List FarkasTerm) (rows : List (AffineForm m))
    (coordinate : Fin m)
    (hIntegral : ∀ term ∈ terms, term.weight.den = 1) :
    (terms.map fun term =>
      term.weight * ((rowAt rows term.row).coefficient coordinate : ℚ)).sum =
    ((terms.map fun term =>
      term.weight.num * (rowAt rows term.row).coefficient coordinate).sum :
        ℚ) := by
  induction terms with
  | nil => simp
  | cons term terms inductionHypothesis =>
      have hHead : term.weight.den = 1 := hIntegral term (by simp)
      have hTail : ∀ candidate ∈ terms, candidate.weight.den = 1 := by
        intro candidate hMember
        exact hIntegral candidate (by simp [hMember])
      simp only [List.map_cons, List.sum_cons]
      rw [weight_eq_intCast_of_den_eq_one term.weight hHead,
        inductionHypothesis hTail]
      norm_cast

private theorem constantSumInt_aux
    (terms : List FarkasTerm) (rows : List (AffineForm m))
    (hIntegral : ∀ term ∈ terms, term.weight.den = 1) :
    (terms.map fun term =>
      term.weight * ((rowAt rows term.row).fixedValue : ℚ)).sum =
    ((terms.map fun term =>
      term.weight.num * (rowAt rows term.row).fixedValue).sum : ℚ) := by
  induction terms with
  | nil => simp
  | cons term terms inductionHypothesis =>
      have hHead : term.weight.den = 1 := hIntegral term (by simp)
      have hTail : ∀ candidate ∈ terms, candidate.weight.den = 1 := by
        intro candidate hMember
        exact hIntegral candidate (by simp [hMember])
      simp only [List.map_cons, List.sum_cons]
      rw [weight_eq_intCast_of_den_eq_one term.weight hHead,
        inductionHypothesis hTail]
      norm_cast

private theorem coefficientSum_eq_intCast (data : FarkasData)
    (rows : List (AffineForm m)) (coordinate : Fin m)
    (hIntegral : ∀ term ∈ data.terms, term.weight.den = 1) :
    data.coefficientSum rows coordinate =
      (data.coefficientSumInt rows coordinate : ℚ) := by
  unfold coefficientSum coefficientSumInt
  exact coefficientSumInt_aux data.terms rows coordinate hIntegral

private theorem constantSum_eq_intCast (data : FarkasData)
    (rows : List (AffineForm m))
    (hIntegral : ∀ term ∈ data.terms, term.weight.den = 1) :
    data.constantSum rows = (data.constantSumInt rows : ℚ) := by
  unfold constantSum constantSumInt
  exact constantSumInt_aux data.terms rows hIntegral

private theorem coefficientSum_num_eq (data : FarkasData)
    (rows : List (AffineForm m)) (coordinate : Fin m)
    (hIntegral : ∀ term ∈ data.terms, term.weight.den = 1) :
    (data.coefficientSum rows coordinate).num =
      data.coefficientSumInt rows coordinate := by
  have hNumerator := congrArg Rat.num
    (coefficientSum_eq_intCast data rows coordinate hIntegral)
  simpa using hNumerator

private theorem constantSum_num_eq (data : FarkasData)
    (rows : List (AffineForm m))
    (hIntegral : ∀ term ∈ data.terms, term.weight.den = 1) :
    (data.constantSum rows).num = data.constantSumInt rows := by
  have hNumerator := congrArg Rat.num
    (constantSum_eq_intCast data rows hIntegral)
  simpa using hNumerator

private theorem num_neg_iff (value : ℚ) :
    value.num < 0 ↔ value < 0 := by
  rw [Rat.lt_iff]
  simp

private theorem integralCheck_eq_true_iff (data : FarkasData)
    (rows : List (AffineForm m))
    (hIntegral : ∀ term ∈ data.terms, term.weight.den = 1) :
    data.integralCheck rows = true ↔ data.Valid rows := by
  unfold integralCheck Valid
  simp only [Bool.and_eq_true, List.all_eq_true, allFin_eq_true_iff]
  constructor
  · rintro ⟨⟨hTerms, hCoefficients⟩, hConstant⟩
    have hConstant' := of_decide_eq_true hConstant
    refine ⟨?_, ?_, ?_⟩
    · intro term hTerm
      obtain ⟨hRow, hWeight⟩ :=
        of_decide_eq_true (hTerms term hTerm)
      exact ⟨hRow, Rat.num_nonneg.mp hWeight⟩
    · intro coordinate
      have hCoefficient := of_decide_eq_true (hCoefficients coordinate)
      apply Rat.num_eq_zero.mp
      exact (coefficientSum_num_eq data rows coordinate hIntegral).trans
        hCoefficient
    · apply (num_neg_iff (data.constantSum rows)).mp
      exact lt_of_eq_of_lt (constantSum_num_eq data rows hIntegral) hConstant'
  · rintro ⟨hTerms, hCoefficients, hConstant⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro term hTerm
      obtain ⟨hRow, hWeight⟩ := hTerms term hTerm
      apply decide_eq_true
      exact ⟨hRow, Rat.num_nonneg.mpr hWeight⟩
    · intro coordinate
      have hNumerator := Rat.num_eq_zero.mpr (hCoefficients coordinate)
      apply decide_eq_true
      exact (coefficientSum_num_eq data rows coordinate hIntegral).symm.trans
        hNumerator
    · have hNumerator := (num_neg_iff (data.constantSum rows)).mpr hConstant
      apply decide_eq_true
      exact lt_of_eq_of_lt (constantSum_num_eq data rows hIntegral).symm
        hNumerator

/-- General rational checker retained as the fallback for hand-written or
legacy certificates whose denominators have not been cleared. -/
private def rationalCheck (data : FarkasData)
    (rows : List (AffineForm m)) : Bool :=
  (data.terms.all fun term =>
    decide (term.row < rows.length ∧ 0 ≤ term.weight)) &&
  (allFin fun coordinate : Fin m =>
    decide (data.coefficientSum rows coordinate = 0)) &&
  decide (data.constantSum rows < 0)

private theorem rationalCheck_eq_true_iff (data : FarkasData)
    (rows : List (AffineForm m)) :
    data.rationalCheck rows = true ↔ data.Valid rows := by
  simp [rationalCheck, Valid, and_assoc]

/-- Executable exact checker for a Farkas leaf.  Integral multipliers take a
kernel-transparent fast path; arbitrary rationals retain the original exact
checker. -/
def check (data : FarkasData) (rows : List (AffineForm m)) : Bool :=
  match data.integralWeights with
  | true => data.integralCheck rows
  | false => data.rationalCheck rows

@[simp] theorem check_eq_true_iff (data : FarkasData)
    (rows : List (AffineForm m)) :
    data.check rows = true ↔ data.Valid rows := by
  cases hIntegral : data.integralWeights with
  | false =>
      simpa [check, hIntegral] using data.rationalCheck_eq_true_iff rows
  | true =>
      have hWeights := (data.integralWeights_eq_true_iff).mp hIntegral
      simpa [check, hIntegral] using data.integralCheck_eq_true_iff rows hWeights

private theorem rowAt_mem (rows : List (AffineForm m)) (index : ℕ)
    (hindex : index < rows.length) :
    rowAt rows index ∈ rows := by
  rw [rowAt, List.getD_eq_getElem _ _ hindex]
  exact List.getElem_mem hindex

private theorem weighted_eval_expansion
    (terms : List FarkasTerm) (rows : List (AffineForm m))
    (point : Fin m → ℤ) :
    (terms.map fun term =>
      term.weight * (rowAt rows term.row).evalRat point).sum =
      (terms.map fun term =>
        term.weight * ((rowAt rows term.row).fixedValue : ℚ)).sum +
      ∑ coordinate : Fin m,
        (terms.map fun term =>
          term.weight *
            ((rowAt rows term.row).coefficient coordinate : ℚ)).sum *
          (point coordinate : ℚ) := by
  induction terms with
  | nil => simp
  | cons term terms ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [ih, AffineForm.evalRat, mul_add, Finset.mul_sum]
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      ring_nf

private theorem weighted_eval_eq_constantSum
    (data : FarkasData) (rows : List (AffineForm m))
    (point : Fin m → ℤ)
    (hCoefficients : ∀ coordinate : Fin m,
      data.coefficientSum rows coordinate = 0) :
    (data.terms.map fun term =>
      term.weight * (rowAt rows term.row).evalRat point).sum =
      data.constantSum rows := by
  have hCoefficients' : ∀ coordinate : Fin m,
      (data.terms.map fun term =>
        term.weight *
          ((rowAt rows term.row).coefficient coordinate : ℚ)).sum = 0 := by
    intro coordinate
    simpa [coefficientSum] using hCoefficients coordinate
  rw [weighted_eval_expansion]
  simp [constantSum, hCoefficients']

/-- A valid Farkas leaf proves that its current affine region is empty. -/
theorem not_formsHold_of_valid
    (data : FarkasData) (rows : List (AffineForm m)) {point : Fin m → ℤ}
    (hValid : data.Valid rows) :
    ¬FormsHold rows point := by
  intro hRows
  have hTermNonnegative :
      ∀ term ∈ data.terms,
        0 ≤ term.weight * (rowAt rows term.row).evalRat point := by
    intro term hTermMem
    have hIndex := (hValid.1 term hTermMem).1
    have hWeight := (hValid.1 term hTermMem).2
    have hRowInt :
        0 ≤ (rowAt rows term.row).eval point :=
      hRows _ (rowAt_mem rows _ hIndex)
    have hRowRat :
        0 ≤ (rowAt rows term.row).evalRat point := by
      rw [AffineForm.evalRat_eq_cast_eval]
      exact_mod_cast hRowInt
    exact mul_nonneg hWeight hRowRat
  have hSumNonnegative :
      0 ≤ (data.terms.map fun term =>
        term.weight * (rowAt rows term.row).evalRat point).sum := by
    apply List.sum_nonneg
    intro value hValue
    simp only [List.mem_map] at hValue
    obtain ⟨term, hTermMem, rfl⟩ := hValue
    exact hTermNonnegative term hTermMem
  rw [weighted_eval_eq_constantSum data rows point hValid.2.1] at hSumNonnegative
  exact (not_lt_of_ge hSumNonnegative) hValid.2.2

end FarkasData

/-- Passive contradiction tree emitted by an external covering search.

`branch cone arity children` has one child for every form of the named cone;
the checker adds that form's exact integral violation in the corresponding
child.  `skip` mirrors the external kernel's shared-form compression, while
`empty` closes immediately when one advertised cone has no inequalities.

Active rows are ordered exactly as the C certificate numbers them: the base
rows first, then branch violations appended in root-to-leaf order. -/
inductive CoverTree (m : ℕ) where
  | leaf (farkas : FarkasData)
  | empty (cone : ℕ)
  | skip (cone form : ℕ) (next : CoverTree m)
  | branch (cone arity : ℕ) (children : Fin arity → CoverTree m)

namespace CoverTree

variable {m : ℕ}

def coneAt (cones : List (List (AffineForm m))) (index : ℕ) :
    List (AffineForm m) :=
  cones.getD index []

def formAt (cone : List (AffineForm m)) (index : ℕ) : AffineForm m :=
  cone.getD index 0

/-- Mathematical validity of a contradiction tree under the currently active
affine rows. -/
def Valid (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : CoverTree m → Prop
  | .leaf farkas => farkas.Valid active
  | .empty cone => cone < cones.length ∧ coneAt cones cone = []
  | .skip cone form next =>
      cone < cones.length ∧
      form < (coneAt cones cone).length ∧
      AffineForm.violation (formAt (coneAt cones cone) form) ∈ active ∧
      next.Valid cones active
  | .branch cone arity children =>
      cone < cones.length ∧
      arity = (coneAt cones cone).length ∧
      ∀ i : Fin arity,
        (children i).Valid cones
          (active ++
            [AffineForm.violation (formAt (coneAt cones cone) i.val)])

/-- Recursive Boolean replay of a contradiction tree under active rows. -/
private def checkActive (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) : CoverTree m → Bool
  | .leaf farkas => farkas.check active
  | .empty cone =>
      decide (cone < cones.length) && (coneAt cones cone).isEmpty
  | .skip cone form next =>
      decide (cone < cones.length) &&
      decide (form < (coneAt cones cone).length) &&
      AffineForm.mem
        (AffineForm.violation (formAt (coneAt cones cone) form)) active &&
      checkActive cones active next
  | .branch cone arity children =>
      decide (cone < cones.length) &&
      decide (arity = (coneAt cones cone).length) &&
      allFin fun i : Fin arity =>
        checkActive cones
            (active ++
              [AffineForm.violation (formAt (coneAt cones cone) i.val)])
            (children i)

/-- The Boolean replay implements exactly the mathematical tree validity
predicate. -/
private theorem checkActive_eq_true_iff
    (tree : CoverTree m) (cones : List (List (AffineForm m)))
    (active : List (AffineForm m)) :
    checkActive cones active tree = true ↔ tree.Valid cones active := by
  induction tree generalizing active with
  | leaf farkas => simp [checkActive, Valid]
  | empty cone => simp [checkActive, Valid]
  | skip cone form next ih =>
      simp [checkActive, Valid, ih, and_assoc]
  | branch cone arity children ih =>
      simp [checkActive, Valid, ih, and_assoc]

/-- Executable exact checker for a complete covering tree. -/
def check (tree : CoverTree m) (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) : Bool :=
  checkActive cones base tree

@[simp] theorem check_eq_true_iff (tree : CoverTree m)
    (base : List (AffineForm m))
    (cones : List (List (AffineForm m))) :
    tree.check base cones = true ↔ tree.Valid cones base := by
  exact checkActive_eq_true_iff tree cones base

private theorem coneAt_eq_getElem
    (cones : List (List (AffineForm m))) (index : ℕ)
    (hindex : index < cones.length) :
    coneAt cones index = cones[index] := by
  exact List.getD_eq_getElem _ _ hindex

private theorem formAt_eq_getElem
    (cone : List (AffineForm m)) (index : ℕ)
    (hindex : index < cone.length) :
    formAt cone index = cone[index] := by
  exact List.getD_eq_getElem _ _ hindex

private theorem no_escape_of_valid
    (tree : CoverTree m) (cones : List (List (AffineForm m)))
    (active : List (AffineForm m))
    (hValid : tree.Valid cones active)
    (point : Fin m → ℤ) (hActive : FormsHold active point)
    (hEscape : ∀ cone ∈ cones, ¬FormsHold cone point) : False := by
  induction tree generalizing active with
  | leaf farkas =>
      exact farkas.not_formsHold_of_valid active hValid hActive
  | empty cone =>
      obtain ⟨hCone, hEmpty⟩ := hValid
      let advertised := cones[cone]
      have hAdvertised : advertised ∈ cones := List.getElem_mem hCone
      have hAdvertisedEmpty : advertised = [] := by
        simpa [advertised, coneAt_eq_getElem cones cone hCone] using hEmpty
      apply hEscape advertised hAdvertised
      simp [hAdvertisedEmpty, FormsHold]
  | skip cone form next ih =>
      exact ih active hValid.2.2.2 hActive
  | branch cone arity children ih =>
      obtain ⟨hCone, hArity, hChildren⟩ := hValid
      let advertised := cones[cone]
      have hAdvertised : advertised ∈ cones := List.getElem_mem hCone
      have hNot : ¬FormsHold advertised point :=
        hEscape advertised hAdvertised
      rw [FormsHold, not_forall] at hNot
      obtain ⟨formValue, hNot⟩ := hNot
      rw [Classical.not_imp] at hNot
      obtain ⟨hFormMem, hFormFails⟩ := hNot
      obtain ⟨index, hIndex, hFormEq⟩ := List.getElem_of_mem hFormMem
      have hIndexArity : index < arity := by
        rw [hArity]
        simpa [advertised, coneAt_eq_getElem cones cone hCone] using hIndex
      let childIndex : Fin arity := ⟨index, hIndexArity⟩
      have hConeAt : coneAt cones cone = advertised :=
        coneAt_eq_getElem cones cone hCone
      have hFormAt :
          formAt (coneAt cones cone) childIndex.val = formValue := by
        rw [formAt_eq_getElem]
        · simpa [hConeAt] using hFormEq
        · simpa [hConeAt] using hIndex
      apply ih childIndex
        (active ++
          [AffineForm.violation
            (formAt (coneAt cones cone) childIndex.val)])
        (hChildren childIndex)
      · intro row hRow
        simp only [List.mem_append, List.mem_singleton] at hRow
        rcases hRow with hRow | rfl
        · exact hActive row hRow
        · rw [hFormAt, AffineForm.holds_violation_iff_not]
          exact hFormFails

/-- Soundness of the passive checker: an accepted contradiction tree proves
integral coverage of the base region by the advertised union of cones. -/
theorem covers_of_check_eq_true
    (tree : CoverTree m) (base : List (AffineForm m))
    (cones : List (List (AffineForm m)))
    (hCheck : tree.check base cones = true) :
    Covers base cones := by
  have hValid : tree.Valid cones base :=
    (tree.check_eq_true_iff base cones).mp hCheck
  intro point hBase
  by_contra hCovered
  have hEscape : ∀ cone ∈ cones, ¬FormsHold cone point := by
    intro cone hCone hConeHolds
    exact hCovered ⟨cone, hCone, hConeHolds⟩
  exact tree.no_escape_of_valid cones base hValid point hBase hEscape

end CoverTree

/-! ## Proof-carrying cone reduction

The search layer is allowed to delete an inequality from a local proof cone
when that inequality follows from the base region and the other inequalities
still present at that stage.  This can make the global covering tree orders of
magnitude smaller.  It must not, however, enlarge the trusted interface.

Every deletion therefore carries a Farkas contradiction for

`base ++ remaining ++ [violation removed]`.

The checker below replays those contradictions.  Its soundness theorem runs
the deletion chain backwards: the final reduced cone implies the last deleted
row, then the preceding row, and eventually the complete original local cone.
-/

/-- Passive data for one proof-carrying deletion from a cone. -/
structure ReductionStep (m : ℕ) where
  removed : AffineForm m
  farkas : FarkasData
  deriving DecidableEq

/-- A sequence of row deletions used to reduce a local proof cone. -/
structure ReductionChain (m : ℕ) where
  steps : List (ReductionStep m)
  deriving DecidableEq

namespace ReductionChain

variable {m : ℕ}

/-- The cone left after applying all named deletions.  A missing row makes the
chain structurally invalid and returns `none`. -/
def resultRows : List (AffineForm m) → List (ReductionStep m) →
    Option (List (AffineForm m))
  | rows, [] => some rows
  | rows, step :: steps =>
      if step.removed ∈ rows then
        resultRows (rows.erase step.removed) steps
      else
        none

/-- Mathematical validity of rows deleted in the exact forward order in which
they disappear from the cone. -/
private def ValidRows (base : List (AffineForm m)) :
    List (AffineForm m) → List (ReductionStep m) → Prop
  | _rows, [] => True
  | rows, step :: steps =>
      step.removed ∈ rows ∧
      step.farkas.Valid
        (base ++ rows.erase step.removed ++ [step.removed.violation]) ∧
      ValidRows base (rows.erase step.removed) steps

/-- Mathematical validity of every deletion in a chain. -/
def Valid (chain : ReductionChain m) (base full : List (AffineForm m)) : Prop :=
  ValidRows base full chain.steps

/-- Boolean replay of row deletions from `rows` down to the claimed result. -/
private def checkRows (base reduced : List (AffineForm m)) :
    List (AffineForm m) → List (ReductionStep m) → Bool
  | rows, [] => decide (rows = reduced)
  | rows, step :: steps =>
      decide (step.removed ∈ rows) &&
      step.farkas.check
        (base ++ rows.erase step.removed ++ [step.removed.violation]) &&
      checkRows base reduced (rows.erase step.removed) steps

/-- Executable exact replay of a reduction chain, including its claimed final
reduced cone. -/
def check (chain : ReductionChain m) (base full reduced : List (AffineForm m)) :
    Bool :=
  checkRows base reduced full chain.steps

private theorem checkRows_eq_true_iff
    (base reduced rows : List (AffineForm m))
    (steps : List (ReductionStep m)) :
    checkRows base reduced rows steps = true ↔
      ValidRows base rows steps ∧ resultRows rows steps = some reduced := by
  induction steps generalizing rows with
  | nil => simp [checkRows, ValidRows, resultRows]
  | cons step steps ih =>
      by_cases hMem : step.removed ∈ rows
      · simp [checkRows, ValidRows, resultRows, hMem, ih, and_assoc]
      · simp [checkRows, ValidRows, resultRows, hMem]

@[simp] theorem check_eq_true_iff
    (chain : ReductionChain m) (base full reduced : List (AffineForm m)) :
    chain.check base full reduced = true ↔
      chain.Valid base full ∧
        resultRows full chain.steps = some reduced := by
  exact checkRows_eq_true_iff base reduced full chain.steps

private theorem removed_holds_of_valid_step
    (base rows : List (AffineForm m)) (step : ReductionStep m)
    (hFarkas : step.farkas.Valid
      (base ++ rows.erase step.removed ++ [step.removed.violation]))
    (point : Fin m → ℤ)
    (hBase : FormsHold base point)
    (hRemaining : FormsHold (rows.erase step.removed) point) :
    step.removed.Holds point := by
  by_contra hRemoved
  apply step.farkas.not_formsHold_of_valid
    (base ++ rows.erase step.removed ++ [step.removed.violation]) hFarkas
  intro form hForm
  simp only [List.mem_append, List.mem_singleton] at hForm
  rcases hForm with hForm | rfl
  · rcases hForm with hForm | hForm
    · exact hBase form hForm
    · exact hRemaining form hForm
  · rw [AffineForm.holds_violation_iff_not]
    exact hRemoved

private theorem formsHold_insert_erased
    (rows : List (AffineForm m)) (removed : AffineForm m)
    (_hMem : removed ∈ rows) (point : Fin m → ℤ)
    (hRemaining : FormsHold (rows.erase removed) point)
    (hRemoved : removed.Holds point) :
    FormsHold rows point := by
  intro form hForm
  by_cases hEq : form = removed
  · simpa [hEq] using hRemoved
  · exact hRemaining form ((List.mem_erase_of_ne hEq).2 hForm)

/-- Soundness of a valid deletion chain: if the final rows hold in the base
region, then every row of the original local proof cone holds. -/
theorem formsHold_full_of_valid
    (chain : ReductionChain m) (base full reduced : List (AffineForm m))
    (hValid : chain.Valid base full)
    (hResult : resultRows full chain.steps = some reduced)
    (point : Fin m → ℤ) (hBase : FormsHold base point)
    (hReduced : FormsHold reduced point) :
    FormsHold full point := by
  rcases chain with ⟨steps⟩
  change ValidRows base full steps at hValid
  change resultRows full steps = some reduced at hResult
  induction steps generalizing full with
  | nil =>
      simp only [resultRows, Option.some.injEq] at hResult
      simpa [hResult] using hReduced
  | cons step steps ih =>
      simp only [ValidRows] at hValid
      obtain ⟨hMem, hFarkas, hTail⟩ := hValid
      simp only [resultRows, hMem, if_true] at hResult
      have hRemaining : FormsHold (full.erase step.removed) point :=
        ih (full.erase step.removed) hTail hResult
      exact formsHold_insert_erased full step.removed hMem point hRemaining
        (removed_holds_of_valid_step base full step hFarkas point hBase
          hRemaining)

/-- A successful Boolean reduction replay proves the semantic implication from
the reduced search cone back to the full local proof cone. -/
theorem formsHold_full_of_check_eq_true
    (chain : ReductionChain m) (base full reduced : List (AffineForm m))
    (hCheck : chain.check base full reduced = true)
    (point : Fin m → ℤ) (hBase : FormsHold base point)
    (hReduced : FormsHold reduced point) :
    FormsHold full point := by
  obtain ⟨hValid, hResult⟩ :=
    (chain.check_eq_true_iff base full reduced).mp hCheck
  exact chain.formsHold_full_of_valid base full reduced hValid hResult
    point hBase hReduced

end ReductionChain

/-! ## Small closed examples -/

namespace Examples

/-- The affine form `constant + a*x`. -/
private def form1 (fixedValue a : ℤ) : AffineForm 1 where
  fixedValue := fixedValue
  coefficient := ![a]

/-- The affine form `constant + a*x + b*y`. -/
private def form2 (fixedValue a b : ℤ) : AffineForm 2 where
  fixedValue := fixedValue
  coefficient := ![a, b]

/-- The two cones `x-y >= 1` and `y-x >= 0`.  Their use of constants `-1`
and `0` is the strict integer partition required by the C kernel grammar. -/
def strictPartitionCones : List (List (AffineForm 2)) := [
  [form2 (-1) 1 (-1)],
  [form2 0 (-1) 1]
]

/-- If both one-row cones were violated, the active rows would be
`x-y-1 >= 0` and `y-x >= 0`; adding them gives `-1 >= 0`. -/
def strictPartitionTree : CoverTree 2 :=
  .branch 0 1 fun _ =>
    .branch 1 1 fun _ =>
      .leaf { terms := [⟨0, 1⟩, ⟨1, 1⟩] }

theorem strictPartitionTree_check :
    strictPartitionTree.check [] strictPartitionCones = true := by
  rw [CoverTree.check_eq_true_iff]
  simp only [strictPartitionTree, CoverTree.Valid]
  norm_num [strictPartitionCones, CoverTree.coneAt, CoverTree.formAt,
    form2, AffineForm.violation, FarkasData.Valid,
    FarkasData.constantSum, FarkasData.coefficientSum,
    FarkasData.rowAt]

/-- Kernel-checked exact coverage of every integral pair by the strict
partition `x-y >= 1` or `y-x >= 0`. -/
theorem strictPartitionCovers :
    Covers [] strictPartitionCones :=
  strictPartitionTree.covers_of_check_eq_true
    [] strictPartitionCones strictPartitionTree_check

/-- A direct human-readable specialization of `strictPartitionCovers`. -/
theorem strictPartition (x y : ℤ) :
    x - y ≥ 1 ∨ y - x ≥ 0 := by
  obtain ⟨cone, hCone, hHolds⟩ :=
    strictPartitionCovers ![x, y] (by simp [FormsHold])
  simp only [strictPartitionCones, form2, Int.reduceNeg, List.mem_cons, List.not_mem_nil, or_false,
    FormsHold, AffineForm.Holds, AffineForm.eval, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hCone hHolds
  rcases hCone with rfl | rfl
  · left
    simp only [Int.reduceNeg, List.mem_cons, List.not_mem_nil, or_false, Fin.isValue, forall_eq,
      Matrix.cons_val_zero, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one, neg_mul,
      le_neg_add_iff_add_le, add_zero, le_add_neg_iff_add_le] at hHolds
    omega
  · right
    simp only [Int.reduceNeg, List.mem_cons, List.not_mem_nil, or_false, Fin.isValue, forall_eq,
      Matrix.cons_val_zero, neg_mul, one_mul, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      zero_add, le_neg_add_iff_add_le, add_zero] at hHolds
    omega

/-! The base row `x - 1 >= 0` implies the local row `x >= 0`.  The reduction
step checks this by contradicting `-x - 1 >= 0`; adding the two active rows
gives the impossible constant `-2`. -/

def implicationReductionBase : List (AffineForm 1) :=
  [form1 (-1) 1]

def implicationReductionFull : List (AffineForm 1) :=
  [form1 0 1]

def implicationReduction : ReductionChain 1 :=
  { steps := [{
      removed := form1 0 1
      farkas := { terms := [⟨0, 1⟩, ⟨1, 1⟩] }
    }] }

theorem implicationReduction_check :
    implicationReduction.check implicationReductionBase
      implicationReductionFull [] = true := by
  rw [ReductionChain.check_eq_true_iff]
  constructor
  · norm_num [implicationReduction, ReductionChain.Valid,
      ReductionChain.ValidRows, implicationReductionBase,
      implicationReductionFull, form1, AffineForm.violation,
      FarkasData.Valid, FarkasData.constantSum,
      FarkasData.coefficientSum, FarkasData.rowAt]
  · decide

/-- The checked reduction really reconstructs its omitted local inequality. -/
theorem implicationReduction_sound (x : ℤ) (hx : 1 ≤ x) : 0 ≤ x := by
  have hBase : FormsHold implicationReductionBase ![x] := by
    simpa [FormsHold, implicationReductionBase, AffineForm.Holds,
      AffineForm.eval, form1] using hx
  have hFull := implicationReduction.formsHold_full_of_check_eq_true
    implicationReductionBase implicationReductionFull []
    implicationReduction_check ![x] hBase (by simp [FormsHold])
  simpa [FormsHold, implicationReductionFull, AffineForm.Holds,
    AffineForm.eval, form1] using hFull

end Examples

end Utilities.Certificate.AffineCover
