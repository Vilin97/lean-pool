/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import Mathlib.Algebra.Group.Translate
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Computability.Language
import Mathlib.Computability.TuringMachine.Computable

/-! # GapCVP proof, part 01 -/

noncomputable section

open StateTransition (EvalsToInTime)

/-- Executes the `compactMachineStepTac` machine-step simplifier. -/
macro "compactMachineStepTac" "[" definitions:term,* "]" : tactic =>
  `(tactic|
    (first
      | rfl
      | (simp [$[$definitions:term],*, Turing.haltList, Turing.FinTM2.step,
          Turing.TM2.step, Turing.TM2.stepAux] <;>
          try { congr 2; funext stack; fin_cases stack <;>
            (first | rfl | simp [Function.update]) } <;>
          try rfl)))

namespace GapCVP

namespace TraceGolf

/-- GapCVP reduction support. -/
def oneStep {α : Type*} {step : α → Option α} (source target : α)
    (transition : step source = some target) :
    EvalsToInTime step source (some target) 1 where
  steps := 1
  evals_in_steps := transition
  steps_le_m := Nat.le_refl 1

/-- GapCVP reduction support. -/
def rebound {α : Type*} {step : α → Option α}
    {source : α} {target : Option α} {oldBudget newBudget : ℕ}
    (trace : EvalsToInTime step source target oldBudget)
    (budget : oldBudget ≤ newBudget) :
    EvalsToInTime step source target newBudget where
  steps := trace.steps
  evals_in_steps := trace.evals_in_steps
  steps_le_m := trace.steps_le_m.trans budget

end TraceGolf

open GapCVP.TraceGolf (oneStep rebound)

namespace Core

section

theorem odd_integer_distance_gt_half (z : ℤ) :
    (1 / 2 : ℝ) < |(1 : ℝ) - 2 * z| := by
  have hz : Odd (1 - 2 * z : ℤ) := by
    exact ⟨-z, by ring⟩
  have hne : (1 - 2 * z : ℤ) ≠ 0 := by
    intro h
    rw [h] at hz
    simp only [Int.not_odd_zero] at hz
  have habs : (1 : ℤ) ≤ |(1 - 2 * z : ℤ)| := Int.one_le_abs hne
  have hreal : (1 : ℝ) ≤ |(1 : ℝ) - 2 * z| := by
    exact_mod_cast habs
  linarith

/-- GapCVP reduction support. -/
structure GapCVPInstance where
  /-- GapCVP reduction support. -/
  dimension : ℕ
  dimension_pos : 0 < dimension
  /-- GapCVP reduction support. -/
  basis : Matrix (Fin dimension) (Fin dimension) ℤ
  basis_nonsingular : basis.det ≠ 0
  /-- GapCVP reduction support. -/
  target : Fin dimension → ℚ
  /-- GapCVP reduction support. -/
  radius : ℚ
  radius_pos : 0 < radius

namespace GapCVPInstance

/-- GapCVP reduction support. -/
noncomputable def latticePoint (I : GapCVPInstance)
    (z : Fin I.dimension → ℤ) : EuclideanSpace ℝ (Fin I.dimension) :=
  WithLp.toLp 2 fun i => (↑(∑ j, I.basis i j * z j) : ℝ)

/-- GapCVP reduction support. -/
noncomputable def targetPoint (I : GapCVPInstance) :
    EuclideanSpace ℝ (Fin I.dimension) :=
  WithLp.toLp 2 fun i => (↑(I.target i) : ℝ)

/-- GapCVP reduction support. -/
noncomputable def latticeDistance (I : GapCVPInstance) : ℝ :=
  Metric.infDist I.targetPoint (Set.range I.latticePoint)

/-- GapCVP reduction support. -/
noncomputable def IsYes (I : GapCVPInstance) : Bool :=
  @decide (
  I.latticeDistance ≤ (I.radius : ℝ)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def IsNo (c : ℝ) (I : GapCVPInstance) : Bool :=
  @decide (
  ((I.dimension : ℝ) ^ c) * (I.radius : ℝ) < I.latticeDistance
  ) (Classical.propDecidable _)
end GapCVPInstance

end

section

open scoped BigOperators

/-- GapCVP reduction support. -/
def squaredDistance (I : GapCVPInstance)
    (z : Fin I.dimension → ℤ) : ℝ :=
  ∑ i : Fin I.dimension,
    (((I.target i : ℚ) : ℝ) -
      ∑ j : Fin I.dimension,
        (I.basis i j : ℝ) * (z j : ℝ)) ^ 2

/-- GapCVP reduction support. -/
noncomputable def SquaredYes (I : GapCVPInstance) : Bool :=
  @decide (
  ∃ z : Fin I.dimension → ℤ,
    squaredDistance I z ≤ (I.radius : ℝ) ^ 2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def SquaredNoAt (c : ℝ) (I : GapCVPInstance) : Bool :=
  @decide (
  ∀ z : Fin I.dimension → ℤ,
    (((I.dimension : ℝ) ^ c) * (I.radius : ℝ)) ^ 2 <
      squaredDistance I z
  ) (Classical.propDecidable _)
theorem squaredDistance_eq_dist_sq
    (I : GapCVPInstance) (z : Fin I.dimension → ℤ) :
    squaredDistance I z =
      dist I.targetPoint (I.latticePoint z) ^ 2 := by
  rw [EuclideanSpace.dist_sq_eq]
  simp only [squaredDistance, GapCVPInstance.targetPoint, GapCVPInstance.latticePoint,
      Int.cast_sum,
      Int.cast_mul, Real.dist_eq, sq_abs]

private theorem isClosed_of_subset_euclidean_integer_grid
    {n : ℕ}
    (s : Set (EuclideanSpace ℝ (Fin n)))
    (hsub : s ⊆
      (Submodule.span ℤ
        (Set.range (EuclideanSpace.basisFun (Fin n) ℝ).toBasis) :
          Set (EuclideanSpace ℝ (Fin n)))) :
    IsClosed s := by
  let b : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let G : Submodule ℤ (EuclideanSpace ℝ (Fin n)) :=
    Submodule.span ℤ (Set.range b)
  have hclosed : IsClosed (G : Set (EuclideanSpace ℝ (Fin n))) := by
    change IsClosed (G.toAddSubgroup : Set (EuclideanSpace ℝ (Fin n)))
    exact AddSubgroup.isClosed_of_discrete
  have hsub' : s ⊆ (G : Set (EuclideanSpace ℝ (Fin n))) := hsub
  let inside : Set G := ((↑) : G → EuclideanSpace ℝ (Fin n)) ⁻¹' s
  have hinside : IsClosed inside := isClosed_discrete inside
  have himage : IsClosed
      (((↑) : G → EuclideanSpace ℝ (Fin n)) '' inside) :=
    hclosed.isClosedMap_subtype_val inside hinside
  have heq :
      (((↑) : G → EuclideanSpace ℝ (Fin n)) '' inside) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hsub' hx⟩, hx, rfl⟩
  rwa [heq] at himage

private theorem instance_latticePoint_range_isClosed (I : GapCVPInstance) :
    IsClosed (Set.range I.latticePoint) := by
  apply isClosed_of_subset_euclidean_integer_grid
  rintro x ⟨z, rfl⟩
  let b : Module.Basis (Fin I.dimension) ℝ
      (EuclideanSpace ℝ (Fin I.dimension)) :=
    (EuclideanSpace.basisFun (Fin I.dimension) ℝ).toBasis
  apply (b.mem_span_iff_repr_mem ℤ (I.latticePoint z)).mpr
  intro i
  refine ⟨∑ j : Fin I.dimension, I.basis i j * z j, ?_⟩
  simp only [algebraMap_int_eq, map_sum, eq_intCast, Int.cast_mul, GapCVPInstance.latticePoint,
      Int.cast_sum,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr, b]

theorem exists_latticePoint_eq_latticeDistance
    (I : GapCVPInstance) :
    ∃ z : Fin I.dimension → ℤ,
      I.latticeDistance = dist I.targetPoint (I.latticePoint z) := by
  have hnonempty :
      (Set.range I.latticePoint).Nonempty :=
    ⟨I.latticePoint 0, ⟨0, rfl⟩⟩
  obtain ⟨x, ⟨z, rfl⟩, hdistance⟩ :=
    (instance_latticePoint_range_isClosed I).exists_infDist_eq_dist
      hnonempty I.targetPoint
  exact ⟨z, hdistance⟩

theorem yes_of_squaredYes (I : GapCVPInstance) :
    SquaredYes I → I.IsYes := by
  simp only [GapCVP.Core.SquaredYes, GapCVP.Core.GapCVPInstance.IsYes, decide_eq_true_eq] at *
  rintro ⟨z, hz⟩
  unfold GapCVPInstance.latticeDistance
  calc
    Metric.infDist I.targetPoint (Set.range I.latticePoint) ≤
        dist I.targetPoint (I.latticePoint z) :=
      Metric.infDist_le_dist_of_mem ⟨z, rfl⟩
    _ ≤ (I.radius : ℝ) := by
      have hdist :
          dist I.targetPoint (I.latticePoint z) ^ 2 ≤
            (I.radius : ℝ) ^ 2 := by
        rwa [squaredDistance_eq_dist_sq] at hz
      have hnonneg : 0 ≤ (I.radius : ℝ) := by
        exact_mod_cast (le_of_lt I.radius_pos)
      nlinarith [dist_nonneg (x := I.targetPoint)
        (y := I.latticePoint z)]

theorem no_of_squaredNoAt
    (c : ℝ) (I : GapCVPInstance) :
    SquaredNoAt c I → I.IsNo c := by
  simp only [GapCVP.Core.SquaredNoAt, GapCVP.Core.GapCVPInstance.IsNo, decide_eq_true_eq] at *
  intro hsquared
  obtain ⟨z, hnearest⟩ := exists_latticePoint_eq_latticeDistance I
  have hsq := hsquared z
  rw [squaredDistance_eq_dist_sq] at hsq
  have hfactor : 0 ≤ (I.dimension : ℝ) ^ c :=
    Real.rpow_nonneg (by positivity) _
  have hradius : 0 ≤ (I.radius : ℝ) := by
    exact_mod_cast (le_of_lt I.radius_pos)
  rw [hnearest]
  nlinarith [dist_nonneg (x := I.targetPoint)
    (y := I.latticePoint z), mul_nonneg hfactor hradius]

theorem squaredNoAt_of_metricNo
    (c : ℝ) (I : GapCVPInstance) (hno : I.IsNo c) :
    SquaredNoAt c I := by
  simp only [GapCVP.Core.SquaredNoAt, GapCVP.Core.GapCVPInstance.IsNo, decide_eq_true_eq] at *
  intro z
  have hpoint :
      ((I.dimension : ℝ) ^ c) * (I.radius : ℝ) <
        dist I.targetPoint (I.latticePoint z) :=
    lt_of_lt_of_le hno
      (Metric.infDist_le_dist_of_mem ⟨z, rfl⟩)
  have hfactor : 0 ≤ (I.dimension : ℝ) ^ c :=
    Real.rpow_nonneg (by positivity) _
  have hradius : 0 ≤ (I.radius : ℝ) := by
    exact_mod_cast le_of_lt I.radius_pos
  rw [squaredDistance_eq_dist_sq]
  nlinarith [mul_nonneg hfactor hradius,
    dist_nonneg (x := I.targetPoint) (y := I.latticePoint z)]

theorem squaredNoAt_iff_metricNo
    (c : ℝ) (I : GapCVPInstance) :
    SquaredNoAt c I ↔ I.IsNo c :=
  ⟨no_of_squaredNoAt c I, squaredNoAt_of_metricNo c I⟩

end

section

/-- GapCVP reduction support. -/
abbrev canonicalNoInstance : GapCVPInstance where
  dimension := 1
  dimension_pos := by norm_num
  basis := Matrix.of fun _ _ => 2
  basis_nonsingular := by
    rw [Matrix.det_fin_one]
    norm_num
  target := fun _ => 1
  radius := 1 / 2
  radius_pos := by norm_num

end

end Core

section

/-- GapCVP reduction support. -/
abbrev Literal := ℕ × Bool

/-- GapCVP reduction support. -/
abbrev ThreeClause := Fin 3 → Literal

/-- GapCVP reduction support. -/
abbrev ThreeCNF := List ThreeClause

/-- GapCVP reduction support. -/
noncomputable def clauseHasDistinctVariables (c : ThreeClause) : Bool :=
  @decide (
  Function.Injective (fun i : Fin 3 => (c i).1)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def literalSatisfied (assignment : ℕ → Bool) (l : Literal) : Bool :=
  @decide (
  assignment l.1 = l.2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def clauseSatisfied (assignment : ℕ → Bool) (c : ThreeClause) : Bool :=
  @decide (
  ∃ i : Fin 3, literalSatisfied assignment (c i)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def threeCNFSatisfiable (φ : ThreeCNF) : Bool :=
  @decide (
  (∀ c ∈ φ, clauseHasDistinctVariables c) ∧
    ∃ assignment : ℕ → Bool, ∀ c ∈ φ, clauseSatisfied assignment c
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
structure GapCVPInstance where
  /-- GapCVP reduction support. -/
  dimension : ℕ
  /-- GapCVP reduction support. -/
  basis : Matrix (Fin dimension) (Fin dimension) ℤ
  /-- GapCVP reduction support. -/
  target : Fin dimension → ℚ
  /-- GapCVP reduction support. -/
  radius : ℚ

/-- GapCVP reduction support. -/
noncomputable def gapCVPWellFormed (I : GapCVPInstance) : Bool :=
  @decide (
  0 < I.dimension ∧ I.basis.det ≠ 0 ∧ 0 < I.radius
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def distanceSquared (I : GapCVPInstance)
    (z : Fin I.dimension → ℤ) : ℝ :=
  ∑ i : Fin I.dimension,
    (((∑ j : Fin I.dimension,
      (I.basis i j : ℝ) * (z j : ℝ)) - (I.target i : ℝ)) ^ 2)

/-- GapCVP reduction support. -/
class BinaryBitCodec (α : Type*) where
  /-- GapCVP reduction support. -/
  encode : α → List Bool
  /-- GapCVP reduction support. -/
  decode : List Bool → Option α
  decode_encode : ∀ a : α, decode (encode a) = some a

namespace BinaryEncoding

/-- GapCVP reduction support. -/
def lengthPrefixedWord (word : List Bool) : List Bool :=
  List.replicate word.length true ++ false :: word

@[simp] theorem lengthPrefixedWord_length (word : List Bool) :
    (lengthPrefixedWord word).length = 2 * word.length + 1 := by
  simp only [lengthPrefixedWord, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- GapCVP reduction support. -/
def readUnaryPrefix : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: rest => some (0, rest)
  | true :: rest =>
      match readUnaryPrefix rest with
      | none => none
      | some (n, tail) => some (n + 1, tail)

@[simp] theorem readUnaryPrefix_replicate
    (n : ℕ) (tail : List Bool) :
    readUnaryPrefix (List.replicate n true ++ false :: tail) =
      some (n, tail) := by
  induction n with
  | zero => simp only [List.replicate_zero, List.nil_append, readUnaryPrefix]
  | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, readUnaryPrefix, ih]

/-- GapCVP reduction support. -/
def readLengthPrefixedWord (bits : List Bool) :
    Option (List Bool × List Bool) :=
  match readUnaryPrefix bits with
  | none => none
  | some (n, tail) =>
      if n ≤ tail.length then
        some (tail.take n, tail.drop n)
      else
        none

@[simp] theorem readLengthPrefixedWord_append
    (word suffix : List Bool) :
    readLengthPrefixedWord (lengthPrefixedWord word ++ suffix) =
      some (word, suffix) := by
  simp only [readLengthPrefixedWord, lengthPrefixedWord, List.append_assoc, List.cons_append,
      readUnaryPrefix_replicate, List.length_append, le_add_iff_nonneg_right, zero_le, ↓reduceIte,
          List.take_left',
      List.drop_left']

/-- GapCVP reduction support. -/
def encodeLiteral (literal : Literal) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat literal.1) ++ [literal.2]

/-- GapCVP reduction support. -/
def readLiteral (bits : List Bool) : Option (Literal × List Bool) :=
  match readLengthPrefixedWord bits with
  | some (word, sign :: rest) =>
      some ((Computability.decodeNat word, sign), rest)
  | _ => none

@[simp] theorem readLiteral_append
    (literal : Literal) (suffix : List Bool) :
    readLiteral (encodeLiteral literal ++ suffix) =
      some (literal, suffix) := by
  rcases literal with ⟨index, sign⟩
  simp only [readLiteral, encodeLiteral, List.append_assoc, List.cons_append, List.nil_append,
      readLengthPrefixedWord_append, Computability.decode_encodeNat]

/-- GapCVP reduction support. -/
def encodeThreeClause (clause : ThreeClause) : List Bool :=
  encodeLiteral (clause 0) ++
    encodeLiteral (clause 1) ++ encodeLiteral (clause 2)

private def readThreeClause (bits : List Bool) :
    Option (ThreeClause × List Bool) :=
  match readLiteral bits with
  | some (a, rest₁) =>
      match readLiteral rest₁ with
      | some (b, rest₂) =>
          match readLiteral rest₂ with
          | some (c, rest₃) => some (![a, b, c], rest₃)
          | none => none
      | none => none
  | none => none

@[simp] private theorem readThreeClause_append
    (clause : ThreeClause) (suffix : List Bool) :
    readThreeClause (encodeThreeClause clause ++ suffix) =
      some (clause, suffix) := by
  have hclause : ![clause 0, clause 1, clause 2] = clause := by
    funext i
    fin_cases i <;> rfl
  simp only [readThreeClause, encodeThreeClause, Fin.isValue, List.append_assoc,
      readLiteral_append, hclause]

private def readThreeClauses : ℕ → List Bool → Option (ThreeCNF × List Bool)
  | 0, bits => some ([], bits)
  | n + 1, bits =>
      match readThreeClause bits with
      | none => none
      | some (clause, rest) =>
          match readThreeClauses n rest with
          | none => none
          | some (clauses, suffix) => some (clause :: clauses, suffix)

@[simp] private theorem readThreeClauses_append
    (clauses : ThreeCNF) (suffix : List Bool) :
    readThreeClauses clauses.length
      (clauses.flatMap encodeThreeClause ++ suffix) =
        some (clauses, suffix) := by
  induction clauses with
  | nil => simp only [List.length_nil, List.flatMap_nil, List.nil_append, readThreeClauses]
  | cons clause clauses ih =>
      simp only [List.length_cons, List.flatMap_cons, List.append_assoc, readThreeClauses,
          readThreeClause_append,
          ih]

/-- GapCVP reduction support. -/
def encodeThreeCNF (clauses : ThreeCNF) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat clauses.length) ++
    clauses.flatMap encodeThreeClause

/-- GapCVP reduction support. -/
def decodeThreeCNF (bits : List Bool) : Option ThreeCNF :=
  match readLengthPrefixedWord bits with
  | none => none
  | some (word, rest) =>
      match readThreeClauses (Computability.decodeNat word) rest with
      | some (clauses, []) => some clauses
      | _ => none

@[simp] theorem decodeThreeCNF_encode (clauses : ThreeCNF) :
    decodeThreeCNF (encodeThreeCNF clauses) = some clauses := by
  have hclauses :
      readThreeClauses clauses.length
        (clauses.flatMap encodeThreeClause) = some (clauses, []) := by
    simpa only [List.append_nil] using readThreeClauses_append clauses []
  simp only [decodeThreeCNF, encodeThreeCNF, readLengthPrefixedWord_append,
      Computability.decode_encodeNat,
      hclauses]

end BinaryEncoding

noncomputable instance (priority := 2000) instBinaryBitCodecThreeCNF :
    BinaryBitCodec ThreeCNF where
  encode := BinaryEncoding.encodeThreeCNF
  decode := BinaryEncoding.decodeThreeCNF
  decode_encode := BinaryEncoding.decodeThreeCNF_encode

end

namespace BinaryEncoding

/-- GapCVP reduction support. -/
def encodeAtomic {α : Type*} [Encodable α] (a : α) : List Bool :=
  lengthPrefixedWord (Computability.encodeNat (Encodable.encode a))

/-- GapCVP reduction support. -/
def readAtomic {α : Type*} [Encodable α] (bits : List Bool) :
    Option (α × List Bool) :=
  match readLengthPrefixedWord bits with
  | none => none
  | some (word, suffix) =>
      match (Encodable.decode (Computability.decodeNat word) : Option α) with
      | none => none
      | some a => some (a, suffix)

@[simp] theorem readAtomic_append
    {α : Type*} [Encodable α] (a : α) (suffix : List Bool) :
    readAtomic (encodeAtomic a ++ suffix) = some (a, suffix) := by
  simp only [readAtomic, encodeAtomic, readLengthPrefixedWord_append,
      Computability.decode_encodeNat,
      Encodable.encodek]

/-- GapCVP reduction support. -/
def encodeFinValues {α : Type*} [Encodable α] :
    (n : ℕ) → (Fin n → α) → List Bool
  | 0, _ => []
  | n + 1, values =>
      encodeAtomic (values 0) ++
        encodeFinValues n (fun i => values i.succ)

/-- GapCVP reduction support. -/
def readFinValues {α : Type*} [Encodable α] :
    (n : ℕ) → List Bool → Option ((Fin n → α) × List Bool)
  | 0, bits => some (Fin.elim0, bits)
  | n + 1, bits =>
      match (readAtomic bits : Option (α × List Bool)) with
      | none => none
      | some (head, rest) =>
          match readFinValues n rest with
          | none => none
          | some (tail, suffix) => some (Fin.cases head tail, suffix)

@[simp] theorem readFinValues_append
    {α : Type*} [Encodable α]
    {n : ℕ} (values : Fin n → α) (suffix : List Bool) :
    readFinValues n (encodeFinValues n values ++ suffix) =
      some (values, suffix) := by
  induction n with
  | zero =>
      have hvalues : values = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp only [readFinValues, encodeFinValues, List.nil_append, hvalues]
  | succ n ih =>
      have hvalues :
          Fin.cases (values 0) (fun i : Fin n => values i.succ) =
            values := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp only [readFinValues, encodeFinValues, List.append_assoc, readAtomic_append, ih, hvalues]

/-- GapCVP reduction support. -/
def encodeMatrixRows :
    (m n : ℕ) → (Fin m → Fin n → ℤ) → List Bool
  | 0, _, _ => []
  | m + 1, n, matrix =>
      encodeFinValues n (matrix 0) ++
        encodeMatrixRows m n (fun i => matrix i.succ)

/-- GapCVP reduction support. -/
def readMatrixRows :
    (m n : ℕ) → List Bool →
      Option ((Fin m → Fin n → ℤ) × List Bool)
  | 0, _, bits => some (Fin.elim0, bits)
  | m + 1, n, bits =>
      match (readFinValues n bits :
        Option ((Fin n → ℤ) × List Bool)) with
      | none => none
      | some (row, rest) =>
          match readMatrixRows m n rest with
          | none => none
          | some (rows, suffix) => some (Fin.cases row rows, suffix)

@[simp] theorem readMatrixRows_append
    {m n : ℕ} (matrix : Fin m → Fin n → ℤ)
    (suffix : List Bool) :
    readMatrixRows m n (encodeMatrixRows m n matrix ++ suffix) =
      some (matrix, suffix) := by
  induction m with
  | zero =>
      have hmatrix : matrix = Fin.elim0 := by
        funext i
        exact Fin.elim0 i
      simp only [readMatrixRows, encodeMatrixRows, List.nil_append, hmatrix]
  | succ m ih =>
      have hmatrix :
          Fin.cases (matrix 0) (fun i : Fin m => matrix i.succ) =
            matrix := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · rfl
        · rfl
      simp only [readMatrixRows, encodeMatrixRows, List.append_assoc, readFinValues_append, ih,
          hmatrix]

/-- GapCVP reduction support. -/
def encodeGapCVPInstance (I : GapCVPInstance) : List Bool :=
  encodeAtomic I.dimension ++
    encodeAtomic I.radius ++
    encodeFinValues I.dimension I.target ++
    encodeMatrixRows I.dimension I.dimension (Matrix.of.symm I.basis)

private def decodeGapCVPInstance (bits : List Bool) : Option GapCVPInstance :=
  match (readAtomic bits : Option (ℕ × List Bool)) with
  | none => none
  | some (n, afterDimension) =>
      match (readAtomic afterDimension : Option (ℚ × List Bool)) with
      | none => none
      | some (radius, afterRadius) =>
          match (readFinValues n afterRadius :
            Option ((Fin n → ℚ) × List Bool)) with
          | none => none
          | some (target, afterTarget) =>
              match readMatrixRows n n afterTarget with
              | some (basis, []) =>
                  some {
                    dimension := n
                    basis := basis
                    target := target
                    radius := radius
                  }
              | _ => none

@[simp] private theorem decodeGapCVPInstance_encode
    (I : GapCVPInstance) :
    decodeGapCVPInstance (encodeGapCVPInstance I) =
      some I := by
  cases I with
  | mk n basis target radius =>
      have hmatrix :
          readMatrixRows n n
              (encodeMatrixRows n n (Matrix.of.symm basis)) =
            some (Matrix.of.symm basis, []) := by
        simpa only [List.append_nil] using
          (readMatrixRows_append (Matrix.of.symm basis) [])
      simp only [decodeGapCVPInstance, encodeGapCVPInstance, List.append_assoc, readAtomic_append,
          readFinValues_append, hmatrix]
      rfl

end BinaryEncoding

section

noncomputable instance (priority := 2000) instBinaryBitCodecGapCVPInstance :
    BinaryBitCodec GapCVPInstance where
  encode := BinaryEncoding.encodeGapCVPInstance
  decode := BinaryEncoding.decodeGapCVPInstance
  decode_encode := BinaryEncoding.decodeGapCVPInstance_encode

open Computability

/-- GapCVP reduction support. -/
noncomputable def binaryFinEncoding (α : Type*)
    [BinaryBitCodec α] : Encoding α Bool where
  encode := BinaryBitCodec.encode
  decode := BinaryBitCodec.decode
  decode_encode := BinaryBitCodec.decode_encode

/-- GapCVP reduction support. -/
abbrev BitLanguage := List Bool → Bool

/-- GapCVP reduction support. -/
abbrev bitEncoding : List Bool → List Bool := id

/-- GapCVP reduction support. -/
def pairBitEncoding : (List Bool × List Bool) →
    List (Bool ⊕ Bool) :=
  (Computability.encodingProd
    (Computability.encodingList Bool)
    (Computability.encodingList Bool)).encode

/-- GapCVP reduction support. -/
abbrev BitTM (f : List Bool → List Bool) :=
  Turing.TM2ComputableInPolyTime bitEncoding bitEncoding f

/-- GapCVP reduction support. -/
abbrev VerifierTM (verifier : List Bool × List Bool → Bool) :=
  Turing.TM2ComputableInPolyTime
    pairBitEncoding Computability.encodeBool verifier

/-- GapCVP reduction support. -/
noncomputable def IsNP (L : BitLanguage) : Bool :=
  @decide (
  ∃ (bound : Polynomial ℕ) (verifier : List Bool × List Bool → Bool),
    Nonempty (VerifierTM verifier) ∧
      ∀ x : List Bool,
        L x ↔ ∃ certificate : List Bool,
          certificate.length ≤ bound.eval x.length ∧
            verifier (x, certificate) = true
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
structure PolynomialReduction (A B : BitLanguage) where
  /-- GapCVP reduction support. -/
  map : List Bool → List Bool
  polynomial_time : Nonempty
    (BitTM map)
  correct : ∀ x, A x ↔ B (map x)

private noncomputable def PolynomialTimeClosedUnderComposition : Bool :=
  @decide (
  ∀ (f g : List Bool → List Bool),
    Nonempty (BitTM f) →
    Nonempty (BitTM g) →
    Nonempty (BitTM (g ∘ f))
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def NPHard (L : BitLanguage) : Bool :=
  @decide (
  ∀ A : BitLanguage, IsNP A → Nonempty (PolynomialReduction A L)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def threeSATLanguage : BitLanguage := fun bits =>
  @decide (
  ∃ φ : ThreeCNF,
    (binaryFinEncoding ThreeCNF).encode φ = bits ∧
      threeCNFSatisfiable φ
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
structure PromiseProblem where
  /-- GapCVP reduction support. -/
  yes : BitLanguage
  /-- GapCVP reduction support. -/
  no : BitLanguage
  disjoint : ∀ x, yes x → no x → False

/-- GapCVP reduction support. -/
structure PromiseReduction (A : BitLanguage) (P : PromiseProblem) where
  /-- GapCVP reduction support. -/
  map : List Bool → List Bool
  polynomial_time : Nonempty
    (BitTM map)
  completeness : ∀ x, A x → P.yes (map x)
  soundness : ∀ x, ¬ A x → P.no (map x)

/-- GapCVP reduction support. -/
noncomputable def NPHardPromise (P : PromiseProblem) : Bool :=
  @decide (
  ∀ A : BitLanguage, IsNP A → Nonempty (PromiseReduction A P)
  ) (Classical.propDecidable _)
end

section

/-- GapCVP reduction support. -/
noncomputable def gapYES (I : GapCVPInstance) : Bool :=
  @decide (
  gapCVPWellFormed I ∧
    ∃ z : Fin I.dimension → ℤ,
      distanceSquared I z ≤ (I.radius : ℝ) ^ 2
  ) (Classical.propDecidable _)

namespace TMComposition

open Turing

private abbrev Stack (first second : FinTM2) :=
  first.K ⊕ { k : second.K // k ≠ second.k₀ }

/-- GapCVP reduction support. -/
abbrev alphabet (first second : FinTM2) : Stack first second → Type
  | .inl k => first.Γ k
  | .inr k => second.Γ k.val

private abbrev Label (first second : FinTM2) := first.Λ ⊕ second.Λ

private abbrev InternalState (first second : FinTM2) := first.σ × second.σ

private def statementPushCount {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => statementPushCount q + 1
  | .peek _ _ q => statementPushCount q
  | .pop _ _ q => statementPushCount q
  | .load _ q => statementPushCount q
  | .branch _ yes no =>
      max (statementPushCount yes) (statementPushCount no)
  | .goto _ => 0
  | .halt => 0

private theorem stepAux_stack_length_le
    {K : Type} {Γ : K → Type} {Λ σ : Type} [DecidableEq K]
    (q : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (sourceStacks : ∀ k, List (Γ k)) (target : K) :
    ((Turing.TM2.stepAux q v sourceStacks).stk target).length ≤
      (sourceStacks target).length + statementPushCount q := by
  induction q generalizing v sourceStacks with
  | push k p q ih =>
      have h := ih v (Function.update sourceStacks k
        (p v :: sourceStacks k))
      by_cases hk : target = k
      · subst target
        simp only [Function.update_self, List.length_cons, TM2.stepAux, statementPushCount,
            ge_iff_le] at h ⊢
        omega
      · simp only [Function.update, hk, ↓reduceDIte, TM2.stepAux, statementPushCount, ge_iff_le]
          at h ⊢
        omega
  | peek k p q ih =>
      simpa only [TM2.stepAux, statementPushCount] using ih (p v (sourceStacks k).head?)
          sourceStacks
  | pop k p q ih =>
      have h := ih (p v (sourceStacks k).head?)
        (Function.update sourceStacks k (sourceStacks k).tail)
      by_cases hk : target = k
      · subst target
        simp only [Function.update_self, List.length_tail, TM2.stepAux, statementPushCount,
            ge_iff_le] at h ⊢
        omega
      · simpa only [TM2.stepAux, statementPushCount, ge_iff_le, Function.update, hk, ↓reduceDIte]
          using h
  | load p q ih =>
      simpa only [TM2.stepAux, statementPushCount] using ih (p v) sourceStacks
  | branch p yes no ihYes ihNo =>
      cases hp : p v with
      | false =>
          have h := ihNo v sourceStacks
          simp only [TM2.stepAux, hp, Bool.cond_false, statementPushCount, ge_iff_le] at h ⊢
          omega
      | true =>
          have h := ihYes v sourceStacks
          simp only [TM2.stepAux, hp, Bool.cond_true, statementPushCount, ge_iff_le] at h ⊢
          omega
  | goto p => simp only [TM2.stepAux, statementPushCount, add_zero, Std.le_refl]
  | halt => simp only [TM2.stepAux, statementPushCount, add_zero, Std.le_refl]

/-- GapCVP reduction support. -/
noncomputable def maxPushPerStep (tm : Turing.FinTM2) : ℕ := by
  classical
  letI : Fintype tm.Λ := tm.ΛFin
  exact Finset.univ.sup fun label => statementPushCount (tm.m label)

private theorem statementPushCount_le_max
    (tm : Turing.FinTM2) (label : tm.Λ) :
    statementPushCount (tm.m label) ≤ maxPushPerStep tm := by
  classical
  let : Fintype tm.Λ := tm.ΛFin
  change statementPushCount (tm.m label) ≤
    (Finset.univ : Finset tm.Λ).sup
      (fun q => statementPushCount (tm.m q))
  exact Finset.le_sup
    (f := fun q : tm.Λ => statementPushCount (tm.m q))
    (Finset.mem_univ label)

private theorem step_stack_length_le (tm : Turing.FinTM2)
    (c c' : tm.Cfg) (h : tm.step c = some c') (target : tm.K) :
    (c'.stk target).length ≤
      (c.stk target).length + maxPushPerStep tm := by
  rcases c with ⟨l, v, sourceStacks⟩
  cases l with
  | none => simp only [FinTM2.step, TM2.step, reduceCtorEq] at h
  | some label =>
      simp only [FinTM2.step, TM2.step] at h
      have hc := Option.some.inj h
      subst c'
      exact (stepAux_stack_length_le (tm.m label) v
        sourceStacks target).trans
        (Nat.add_le_add_left (statementPushCount_le_max tm label) _)

private theorem iterate_stack_length_le (tm : Turing.FinTM2)
    (steps : ℕ) (c c' : tm.Cfg)
    (h : ((fun state : Option tm.Cfg => state.bind tm.step)^[steps])
      (some c) = some c') (target : tm.K) :
    (c'.stk target).length ≤
      (c.stk target).length + steps * maxPushPerStep tm := by
  induction steps generalizing c with
  | zero =>
      have hc : c = c' := Option.some.inj (by simpa only [Option.some.injEq, FinTM2.step,
          Function.iterate_zero, id_eq] using h)
      subst c'
      simp only [zero_mul, add_zero, Std.le_refl]
  | succ steps ih =>
      have hnext :
          ((fun state : Option tm.Cfg => state.bind tm.step)^[steps])
            (tm.step c) = some c' := by
        simpa only [Function.iterate_succ_apply, Option.bind_some] using h
      cases hs : tm.step c with
      | none =>
          rw [hs] at hnext
          have hfixed :
              ((fun state : Option tm.Cfg => state.bind tm.step)^[steps])
                none = none :=
            Function.iterate_fixed (by rfl) steps
          rw [hfixed] at hnext
          cases hnext
      | some middle =>
          have htail :
              ((fun state : Option tm.Cfg => state.bind tm.step)^[steps])
                (some middle) = some c' := by
            simpa only [hs] using hnext
          have hfirst := step_stack_length_le tm c middle hs target
          have hrest := ih middle htail
          simpa only [Nat.succ_mul, Nat.add_comm, Nat.add_assoc, ge_iff_le, Nat.add_left_comm]
              using
              hrest.trans (Nat.add_le_add_right hfirst _)

private theorem evals_stack_length_le (tm : Turing.FinTM2)
    (c c' : tm.Cfg)
    (h : StateTransition.EvalsTo tm.step c (some c'))
    (target : tm.K) :
    (c'.stk target).length ≤
      (c.stk target).length + h.steps * maxPushPerStep tm := by
  apply iterate_stack_length_le tm h.steps c c' _ target
  exact h.evals_in_steps

private theorem iterate_map_of_some
    {α β : Type} (stepA : α → Option α) (stepB : β → Option β)
    (translate : α → β)
    (hstep : ∀ a a', stepA a = some a' →
      stepB (translate a) = some (translate a'))
    (steps : ℕ) (a a' : α)
    (h : ((fun state : Option α => state.bind stepA)^[steps])
      (some a) = some a') :
    ((fun state : Option β => state.bind stepB)^[steps])
      (some (translate a)) = some (translate a') := by
  induction steps generalizing a with
  | zero =>
      have ha : a = a' := Option.some.inj (by simpa only [Option.some.injEq, Function.iterate_zero,
          id_eq] using h)
      subst a'
      simp only [Function.iterate_zero, id_eq]
  | succ steps ih =>
      have hnext :
          ((fun state : Option α => state.bind stepA)^[steps])
            (stepA a) = some a' := by
        simpa only [Function.iterate_succ_apply, Option.bind_some] using h
      cases hs : stepA a with
      | none =>
          rw [hs] at hnext
          have hfixed :
              ((fun state : Option α => state.bind stepA)^[steps])
                none = none :=
            Function.iterate_fixed (by rfl) steps
          rw [hfixed] at hnext
          cases hnext
      | some middle =>
          have htail :
              ((fun state : Option α => state.bind stepA)^[steps])
                (some middle) = some a' := by
            simpa only [hs] using hnext
          have htranslated := hstep a middle hs
          simpa only [Function.iterate_succ_apply,
            Option.bind_some, htranslated] using ih middle htail

/-- GapCVP reduction support. -/
def evalsToInTimeMapOfStep
    {α β : Type} (stepA : α → Option α) (stepB : β → Option β)
    (translate : α → β)
    (hstep : ∀ a a', stepA a = some a' →
      stepB (translate a) = some (translate a'))
    {a a' : α} {budget : ℕ}
    (h : EvalsToInTime stepA a (some a') budget) :
    EvalsToInTime stepB (translate a) (some (translate a')) budget where
  steps := h.steps
  evals_in_steps :=
    iterate_map_of_some stepA stepB translate hstep
      h.steps a a' h.evals_in_steps
  steps_le_m := h.steps_le_m

@[simp] private theorem cast_list_length {α β : Type}
    (h : α = β) (xs : List α) :
    (cast (congrArg List h) xs).length = xs.length := by
  cases h
  rfl

private theorem outputsInTime_length_le (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀)) (output : List (tm.Γ tm.k₁))
    (budget : ℕ)
    (h : Turing.TM2OutputsInTime tm input (some output) budget) :
    output.length ≤ input.length + budget * maxPushPerStep tm := by
  have hrun := evals_stack_length_le tm
    (Turing.initList tm input) (Turing.haltList tm output)
    h.toEvalsTo tm.k₁
  have hsteps : h.steps * maxPushPerStep tm ≤
      budget * maxPushPerStep tm :=
    Nat.mul_le_mul_right _ h.steps_le_m
  by_cases hk : tm.k₁ = tm.k₀
  · simp only [haltList, hk, eq_mpr_eq_cast, ↓reduceDIte, cast_eq, initList, cast_list_length,
      FinTM2.step,
        Option.map_some] at hrun
    exact hrun.trans (Nat.add_le_add_left hsteps _)
  · simp only [haltList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq, initList, hk, List.length_nil,
      FinTM2.step,
        Option.map_some, zero_add] at hrun
    exact hrun.trans (by omega)

theorem natPolynomial_eval_monotone (p : Polynomial ℕ) :
    Monotone p.eval := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      intro a b hab
      simpa only [Polynomial.eval_add] using Nat.add_le_add (hp hab) (hq hab)
  | monomial n a =>
      intro x y hxy
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul_left a (Nat.pow_le_pow_left hxy n)

private theorem polynomialComputer_output_length_le
    {f : List Bool → List Bool}
    (first : BitTM f)
    (x : List Bool) :
    (f x).length ≤
      x.length + first.time.eval x.length * maxPushPerStep first.tm := by
  have h := outputsInTime_length_le first.tm
    (List.map first.inputAlphabet.invFun (bitEncoding x))
    (List.map first.outputAlphabet.invFun (bitEncoding (f x)))
    (first.time.eval (bitEncoding x).length)
    (first.outputsFun x)
  simpa only [bitEncoding, ge_iff_le, Equiv.invFun_as_coe, id_eq, List.length_map] using h

/-- GapCVP reduction support. -/
noncomputable def outputLengthPolynomial
    {f : List Bool → List Bool}
    (first : BitTM f) :
    Polynomial ℕ :=
  Polynomial.X + Polynomial.C (maxPushPerStep first.tm) * first.time

theorem outputLengthPolynomial_bounds
    {f : List Bool → List Bool}
    (first : BitTM f)
    (x : List Bool) :
    (f x).length ≤ (outputLengthPolynomial first).eval x.length := by
  simpa only [outputLengthPolynomial, eq_natCast, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_mul,
      Polynomial.eval_natCast, Nat.cast_id, Nat.mul_comm] using polynomialComputer_output_length_le
          first x

private noncomputable def compositeTimePolynomial
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    Polynomial ℕ :=
  first.time + second.time.comp (outputLengthPolynomial first)

private theorem compositeTimePolynomial_bounds
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (x : List Bool) :
    first.time.eval x.length + second.time.eval (f x).length ≤
      (compositeTimePolynomial first second).eval x.length := by
  have hmiddle := outputLengthPolynomial_bounds first x
  have hsecond := natPolynomial_eval_monotone second.time hmiddle
  simpa only [compositeTimePolynomial, Polynomial.eval_add, Polynomial.eval_comp,
      add_le_add_iff_left,
      ge_iff_le] using Nat.add_le_add_left hsecond (first.time.eval x.length)

private noncomputable def secondStack (first second : FinTM2) (k : second.K) :
    Stack first second :=
  if h : k = second.k₀ then .inl first.k₁ else .inr ⟨k, h⟩

private noncomputable def secondAlphabetEquiv
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (k : second.tm.K) :
    second.tm.Γ k ≃
      alphabet first.tm second.tm (secondStack first.tm second.tm k) := by
  classical
  unfold secondStack
  split_ifs with h
  · subst k
    exact second.inputAlphabet.trans first.outputAlphabet.symm
  · exact Equiv.refl (second.tm.Γ k)

private def liftFirstStmt (first second : FinTM2) :
    Turing.TM2.Stmt first.Γ first.Λ first.σ →
      Turing.TM2.Stmt (alphabet first second)
        (Label first second) (InternalState first second)
  | .push k f q =>
      .push (.inl k) (fun s => f s.1) (liftFirstStmt first second q)
  | .peek k f q =>
      .peek (.inl k) (fun s x => (f s.1 x, s.2))
        (liftFirstStmt first second q)
  | .pop k f q =>
      .pop (.inl k) (fun s x => (f s.1 x, s.2))
        (liftFirstStmt first second q)
  | .load f q =>
      .load (fun s => (f s.1, s.2)) (liftFirstStmt first second q)
  | .branch f yes no =>
      .branch (fun s => f s.1)
        (liftFirstStmt first second yes) (liftFirstStmt first second no)
  | .goto f => .goto (fun s => .inl (f s.1))
  | .halt => .goto (fun _ => .inr second.main)

private noncomputable def liftSecondStmt
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    Turing.TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ →
      Turing.TM2.Stmt (alphabet first.tm second.tm)
        (Label first.tm second.tm) (InternalState first.tm second.tm)
  | .push k p q => by
      classical
      by_cases hk : k = second.tm.k₀
      · subst k
        exact .push (.inl first.tm.k₁)
          (fun s => (second.inputAlphabet.trans first.outputAlphabet.symm)
            (p s.2))
          (liftSecondStmt first second q)
      · exact .push (.inr ⟨k, hk⟩) (fun s => p s.2)
          (liftSecondStmt first second q)
  | .peek k p q => by
      classical
      by_cases hk : k = second.tm.k₀
      · subst k
        exact .peek (.inl first.tm.k₁)
          (fun s x => (s.1, p s.2
            (x.map (first.outputAlphabet.trans second.inputAlphabet.symm))))
          (liftSecondStmt first second q)
      · exact .peek (.inr ⟨k, hk⟩)
          (fun s x => (s.1, p s.2 x))
          (liftSecondStmt first second q)
  | .pop k p q => by
      classical
      by_cases hk : k = second.tm.k₀
      · subst k
        exact .pop (.inl first.tm.k₁)
          (fun s x => (s.1, p s.2
            (x.map (first.outputAlphabet.trans second.inputAlphabet.symm))))
          (liftSecondStmt first second q)
      · exact .pop (.inr ⟨k, hk⟩)
          (fun s x => (s.1, p s.2 x))
          (liftSecondStmt first second q)
  | .load p q =>
      .load (fun s => (s.1, p s.2)) (liftSecondStmt first second q)
  | .branch p yes no =>
      .branch (fun s => p s.2)
        (liftSecondStmt first second yes) (liftSecondStmt first second no)
  | .goto p => .goto (fun s => .inr (p s.2))
  | .halt => .halt

/-- GapCVP reduction support. -/
noncomputable def machine
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    Turing.FinTM2 := by
  classical
  letI : Fintype first.tm.K := first.tm.kFin
  letI : Fintype second.tm.K := second.tm.kFin
  letI : Fintype first.tm.Λ := first.tm.ΛFin
  letI : Fintype second.tm.Λ := second.tm.ΛFin
  letI : Fintype first.tm.σ := first.tm.σFin
  letI : Fintype second.tm.σ := second.tm.σFin
  letI : Fintype (first.tm.Γ first.tm.k₀) := first.tm.Γk₀Fin
  letI : Fintype
      (alphabet first.tm second.tm (.inl first.tm.k₀)) :=
    first.tm.Γk₀Fin
  exact {
    K := Stack first.tm second.tm
    k₀ := .inl first.tm.k₀
    k₁ := secondStack first.tm second.tm second.tm.k₁
    Γ := alphabet first.tm second.tm
    Λ := Label first.tm second.tm
    main := .inl first.tm.main
    σ := InternalState first.tm second.tm
    initialState := (first.tm.initialState, second.tm.initialState)
    m := fun
      | .inl label => liftFirstStmt first.tm second.tm (first.tm.m label)
      | .inr label => liftSecondStmt first second (second.tm.m label)
  }

/-- GapCVP reduction support. -/
noncomputable def auxiliary
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    Turing.TM2ComputableAux Bool Bool where
  tm := machine first second
  inputAlphabet := first.inputAlphabet
  outputAlphabet :=
    (secondAlphabetEquiv first second second.tm.k₁).symm.trans
      second.outputAlphabet

private def firstStacks (first second : FinTM2)
    (sourceStacks : ∀ k, List (first.Γ k)) :
    (k : Stack first second) → List (alphabet first second k)
  | .inl k => sourceStacks k
  | .inr _ => []

private theorem firstStacks_update (first second : FinTM2)
    (sourceStacks : ∀ k, List (first.Γ k))
    (k : first.K) (value : List (first.Γ k)) :
    firstStacks first second (Function.update sourceStacks k value) =
      Function.update (firstStacks first second sourceStacks)
        (.inl k) value := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases h : j = k
      · subst j
        simp only [ne_eq, firstStacks, Function.update_self]
      · simp only [ne_eq, firstStacks, Function.update, h, ↓reduceDIte, Sum.inl.injEq]
  | inr j =>
      simp only [ne_eq, firstStacks, Function.update, reduceCtorEq, ↓reduceDIte]

private noncomputable def firstConfiguration
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (c : first.tm.Cfg) : (machine first second).Cfg where
  l := match c.l with
    | some label => some (.inl label)
    | none => some (.inr second.tm.main)
  var := (c.var, second.tm.initialState)
  stk := firstStacks first.tm second.tm c.stk

private theorem liftFirstStmt_stepAux
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (q : Turing.TM2.Stmt first.tm.Γ first.tm.Λ first.tm.σ)
    (v : first.tm.σ)
    (sourceStacks : ∀ k, List (first.tm.Γ k)) :
    Turing.TM2.stepAux (liftFirstStmt first.tm second.tm q)
        (v, second.tm.initialState)
        (firstStacks first.tm second.tm sourceStacks) =
      firstConfiguration first second
        (Turing.TM2.stepAux q v sourceStacks) := by
  classical
  induction q generalizing v sourceStacks with
  | push k p q ih =>
      change
        Turing.TM2.stepAux (liftFirstStmt first.tm second.tm q)
            (v, second.tm.initialState)
            (Function.update (firstStacks first.tm second.tm sourceStacks)
              (.inl k) (p v :: sourceStacks k)) =
          firstConfiguration first second
            (Turing.TM2.stepAux q v
              (Function.update sourceStacks k (p v :: sourceStacks k)))
      rw [← firstStacks_update]
      exact ih (v := v)
        (sourceStacks := Function.update sourceStacks k
          (p v :: sourceStacks k))
  | peek k p q ih =>
      exact ih (v := p v (sourceStacks k).head?)
        (sourceStacks := sourceStacks)
  | pop k p q ih =>
      change
        Turing.TM2.stepAux (liftFirstStmt first.tm second.tm q)
            (p v (sourceStacks k).head?, second.tm.initialState)
            (Function.update (firstStacks first.tm second.tm sourceStacks)
              (.inl k) (sourceStacks k).tail) =
          firstConfiguration first second
            (Turing.TM2.stepAux q (p v (sourceStacks k).head?)
              (Function.update sourceStacks k (sourceStacks k).tail))
      rw [← firstStacks_update]
      exact ih (v := p v (sourceStacks k).head?)
        (sourceStacks := Function.update sourceStacks k
          (sourceStacks k).tail)
  | load p q ih =>
      exact ih (v := p v) (sourceStacks := sourceStacks)
  | branch p yes no ihYes ihNo =>
      cases hp : p v with
      | false =>
          simpa only [liftFirstStmt, TM2.stepAux, hp, Bool.cond_false] using ihNo (v := v)
              (sourceStacks
              := sourceStacks)
      | true =>
          simpa only [liftFirstStmt, TM2.stepAux, hp, Bool.cond_true] using ihYes (v := v)
              (sourceStacks
              := sourceStacks)
  | goto p => rfl
  | halt => rfl

private theorem firstConfiguration_step
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (c c' : first.tm.Cfg)
    (h : first.tm.step c = some c') :
    (machine first second).step (firstConfiguration first second c) =
      some (firstConfiguration first second c') := by
  rcases c with ⟨l, v, sourceStacks⟩
  cases l with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at h
  | some label =>
      change some (Turing.TM2.stepAux (first.tm.m label)
        v sourceStacks) = some c' at h
      have hc := Option.some.inj h
      subst c'
      change
        some (Turing.TM2.stepAux
          (liftFirstStmt first.tm second.tm (first.tm.m label))
          (v, second.tm.initialState)
          (firstStacks first.tm second.tm sourceStacks)) =
          some (firstConfiguration first second
            (Turing.TM2.stepAux (first.tm.m label) v sourceStacks))
      rw [liftFirstStmt_stepAux]
      rfl

private noncomputable def firstConfiguration_evalsToInTime
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    {c c' : first.tm.Cfg} {budget : ℕ}
    (h : EvalsToInTime
      first.tm.step c (some c') budget) :
    EvalsToInTime (machine first second).step
      (firstConfiguration first second c)
      (some (firstConfiguration first second c')) budget :=
  evalsToInTimeMapOfStep first.tm.step
    (machine first second).step (firstConfiguration first second)
    (firstConfiguration_step first second) h

private theorem firstConfiguration_init
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (x : List Bool) :
    firstConfiguration first second
        (Turing.initList first.tm
          (List.map first.inputAlphabet.invFun (bitEncoding x))) =
      Turing.initList (machine first second)
        (List.map (auxiliary first second).inputAlphabet.invFun
          (bitEncoding x)) := by
  classical
  simp only [machine, ne_eq, firstConfiguration, initList, Equiv.invFun_as_coe, id_eq,
      eq_mpr_eq_cast,
      auxiliary]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = first.tm.k₀
      · subst k
        simp only [ne_eq, firstStacks, ↓reduceDIte, cast_eq]
        rfl
      · simp only [ne_eq, firstStacks, hk, ↓reduceDIte, Sum.inl.injEq]
  | inr k =>
      simp only [ne_eq, firstStacks, reduceCtorEq, ↓reduceDIte]

private noncomputable def secondStacks
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k)) :
    (k : Stack first.tm second.tm) →
      List (alphabet first.tm second.tm k)
  | .inl k =>
      if h : k = first.tm.k₁ then
        h.symm ▸
          List.map (second.inputAlphabet.trans first.outputAlphabet.symm)
            (sourceStacks second.tm.k₀)
      else []
  | .inr k => sourceStacks k.val

@[simp] private theorem secondStacks_shared
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k)) :
    secondStacks first second sourceStacks (.inl first.tm.k₁) =
      List.map (second.inputAlphabet.trans first.outputAlphabet.symm)
        (sourceStacks second.tm.k₀) := by
  classical
  simp only [ne_eq, secondStacks, ↓reduceDIte, Equiv.coe_trans]

@[simp] private theorem secondStacks_private
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k))
    (k : {k : second.tm.K // k ≠ second.tm.k₀}) :
    secondStacks first second sourceStacks (.inr k) =
      sourceStacks k.val := rfl

private theorem secondStacks_shared_update
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k))
    (value : List (second.tm.Γ second.tm.k₀)) :
    secondStacks first second
        (Function.update sourceStacks second.tm.k₀ value) =
      Function.update (secondStacks first second sourceStacks)
        (.inl first.tm.k₁)
        (List.map (second.inputAlphabet.trans first.outputAlphabet.symm)
          value) := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases hj : j = first.tm.k₁
      · subst j
        simp only [ne_eq, secondStacks, ↓reduceDIte, Equiv.coe_trans, Function.update_self]
      · simp only [ne_eq, secondStacks, hj, ↓reduceDIte, Function.update, Sum.inl.injEq]
  | inr j =>
      simp only [ne_eq, secondStacks, Function.update, j.property, ↓reduceDIte, reduceCtorEq]

private theorem secondStacks_private_update
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k))
    (k : second.tm.K) (hk : k ≠ second.tm.k₀)
    (value : List (second.tm.Γ k)) :
    secondStacks first second (Function.update sourceStacks k value) =
      Function.update (secondStacks first second sourceStacks)
        (.inr ⟨k, hk⟩) value := by
  classical
  funext j
  cases j with
  | inl j =>
      by_cases hj : j = first.tm.k₁
      · subst j
        simp only [ne_eq, secondStacks, ↓reduceDIte, Equiv.coe_trans, Function.update, Ne.symm hk,
            reduceCtorEq]
      · simp only [ne_eq, secondStacks, hj, ↓reduceDIte, Function.update, reduceCtorEq]
  | inr j =>
      rcases j with ⟨j, hj₀⟩
      by_cases hj : j = k
      · subst j
        simp only [ne_eq, secondStacks, Function.update_self]
      · simp only [ne_eq, secondStacks, Function.update, hj, ↓reduceDIte, Sum.inr.injEq,
          Subtype.mk.injEq]

private noncomputable def secondConfiguration
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (c : second.tm.Cfg) : (machine first second).Cfg where
  l := c.l.map Sum.inr
  var := (first.tm.initialState, c.var)
  stk := secondStacks first second c.stk

private theorem liftSecondStmt_stepAux
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (q : Turing.TM2.Stmt second.tm.Γ second.tm.Λ second.tm.σ)
    (v : second.tm.σ)
    (sourceStacks : ∀ k, List (second.tm.Γ k)) :
    Turing.TM2.stepAux (liftSecondStmt first second q)
        (first.tm.initialState, v)
        (secondStacks first second sourceStacks) =
      secondConfiguration first second
        (Turing.TM2.stepAux q v sourceStacks) := by
  classical
  induction q generalizing v sourceStacks with
  | push k p q ih =>
      by_cases hk : k = second.tm.k₀
      · subst k
        simp only [liftSecondStmt, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState, v)
              (Function.update (secondStacks first second sourceStacks)
                (.inl first.tm.k₁)
                ((second.inputAlphabet.trans first.outputAlphabet.symm)
                    (p v) ::
                  secondStacks first second sourceStacks
                    (.inl first.tm.k₁))) =
            secondConfiguration first second
              (Turing.TM2.stepAux q v
                (Function.update sourceStacks second.tm.k₀
                  (p v :: sourceStacks second.tm.k₀)))
        have hupdate :
            Function.update (secondStacks first second sourceStacks)
                (.inl first.tm.k₁)
                ((second.inputAlphabet.trans first.outputAlphabet.symm)
                    (p v) :: secondStacks first second sourceStacks
                      (.inl first.tm.k₁)) =
              secondStacks first second
                (Function.update sourceStacks second.tm.k₀
                  (p v :: sourceStacks second.tm.k₀)) := by
          simpa only [secondStacks_shared, List.map_cons] using
            (secondStacks_shared_update first second
              sourceStacks (p v :: sourceStacks second.tm.k₀)).symm
        rw [hupdate]
        exact ih (v := v) (sourceStacks := Function.update sourceStacks
          second.tm.k₀ (p v :: sourceStacks second.tm.k₀))
      · simp only [liftSecondStmt, dite_eq_right hk, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState, v)
              (Function.update (secondStacks first second sourceStacks)
                (.inr ⟨k, hk⟩)
                (p v :: secondStacks first second sourceStacks
                  (.inr ⟨k, hk⟩))) =
            secondConfiguration first second
              (Turing.TM2.stepAux q v
                (Function.update sourceStacks k (p v :: sourceStacks k)))
        rw [secondStacks_private,
          ← secondStacks_private_update first second sourceStacks k hk]
        exact ih (v := v) (sourceStacks := Function.update sourceStacks
          k (p v :: sourceStacks k))
  | peek k p q ih =>
      by_cases hk : k = second.tm.k₀
      · subst k
        have hhead :
            (secondStacks first second sourceStacks
              (.inl first.tm.k₁)).head?.map
                (first.outputAlphabet.trans second.inputAlphabet.symm) =
              (sourceStacks second.tm.k₀).head? := by
          rw [secondStacks_shared]
          cases h : sourceStacks second.tm.k₀ with
          | nil =>
              simp only [List.map_nil, List.head?_nil, Option.map_none]
          | cons a as =>
              simp only [List.map_cons, List.head?_cons,
                Option.map_some, Equiv.trans_apply,
                Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        simp only [liftSecondStmt, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState,
                p v ((secondStacks first second sourceStacks
                  (.inl first.tm.k₁)).head?.map
                    (first.outputAlphabet.trans
                      second.inputAlphabet.symm)))
              (secondStacks first second sourceStacks) =
            secondConfiguration first second
              (Turing.TM2.stepAux q
                (p v (sourceStacks second.tm.k₀).head?) sourceStacks)
        rw [hhead]
        exact ih (v := p v (sourceStacks second.tm.k₀).head?)
          (sourceStacks := sourceStacks)
      · simp only [liftSecondStmt, dite_eq_right hk, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState,
                p v (secondStacks first second sourceStacks
                  (.inr ⟨k, hk⟩)).head?)
              (secondStacks first second sourceStacks) =
            secondConfiguration first second
              (Turing.TM2.stepAux q (p v (sourceStacks k).head?)
                sourceStacks)
        rw [secondStacks_private]
        exact ih (v := p v (sourceStacks k).head?)
          (sourceStacks := sourceStacks)
  | pop k p q ih =>
      by_cases hk : k = second.tm.k₀
      · subst k
        have hhead :
            (secondStacks first second sourceStacks
              (.inl first.tm.k₁)).head?.map
                (first.outputAlphabet.trans second.inputAlphabet.symm) =
              (sourceStacks second.tm.k₀).head? := by
          rw [secondStacks_shared]
          cases h : sourceStacks second.tm.k₀ with
          | nil =>
              simp only [List.map_nil, List.head?_nil, Option.map_none]
          | cons a as =>
              simp only [List.map_cons, List.head?_cons,
                Option.map_some, Equiv.trans_apply,
                Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        simp only [liftSecondStmt, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState,
                p v ((secondStacks first second sourceStacks
                  (.inl first.tm.k₁)).head?.map
                    (first.outputAlphabet.trans
                      second.inputAlphabet.symm)))
              (Function.update (secondStacks first second sourceStacks)
                (.inl first.tm.k₁)
                (secondStacks first second sourceStacks
                  (.inl first.tm.k₁)).tail) =
            secondConfiguration first second
              (Turing.TM2.stepAux q
                (p v (sourceStacks second.tm.k₀).head?)
                (Function.update sourceStacks second.tm.k₀
                  (sourceStacks second.tm.k₀).tail))
        have htail :
            (secondStacks first second sourceStacks
              (.inl first.tm.k₁)).tail =
              List.map (second.inputAlphabet.trans
                first.outputAlphabet.symm)
                (sourceStacks second.tm.k₀).tail := by
          rw [secondStacks_shared]
          exact List.map_tail.symm
        rw [hhead, htail, ← secondStacks_shared_update]
        exact ih (v := p v (sourceStacks second.tm.k₀).head?)
          (sourceStacks := Function.update sourceStacks second.tm.k₀
            (sourceStacks second.tm.k₀).tail)
      · simp only [liftSecondStmt, dite_eq_right hk, Turing.TM2.stepAux]
        change
          Turing.TM2.stepAux (liftSecondStmt first second q)
              (first.tm.initialState,
                p v (secondStacks first second sourceStacks
                  (.inr ⟨k, hk⟩)).head?)
              (Function.update (secondStacks first second sourceStacks)
                (.inr ⟨k, hk⟩)
                (secondStacks first second sourceStacks
                  (.inr ⟨k, hk⟩)).tail) =
            secondConfiguration first second
              (Turing.TM2.stepAux q (p v (sourceStacks k).head?)
                (Function.update sourceStacks k
                  (sourceStacks k).tail))
        rw [secondStacks_private,
          ← secondStacks_private_update first second sourceStacks k hk]
        exact ih (v := p v (sourceStacks k).head?)
          (sourceStacks := Function.update sourceStacks k
            (sourceStacks k).tail)
  | load p q ih =>
      exact ih (v := p v) (sourceStacks := sourceStacks)
  | branch p yes no ihYes ihNo =>
      cases hp : p v with
      | false =>
          simpa only [liftSecondStmt, TM2.stepAux, hp, Bool.cond_false] using ihNo (v := v)
              (sourceStacks := sourceStacks)
      | true =>
          simpa only [liftSecondStmt, TM2.stepAux, hp, Bool.cond_true] using ihYes (v := v)
              (sourceStacks := sourceStacks)
  | goto p => rfl
  | halt => rfl

private theorem secondConfiguration_step
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (c c' : second.tm.Cfg)
    (h : second.tm.step c = some c') :
    (machine first second).step (secondConfiguration first second c) =
      some (secondConfiguration first second c') := by
  rcases c with ⟨l, v, sourceStacks⟩
  cases l with
  | none =>
      simp only [FinTM2.step, TM2.step, reduceCtorEq] at h
  | some label =>
      change some (Turing.TM2.stepAux (second.tm.m label)
        v sourceStacks) = some c' at h
      have hc := Option.some.inj h
      subst c'
      change
        some (Turing.TM2.stepAux
          (liftSecondStmt first second (second.tm.m label))
          (first.tm.initialState, v)
          (secondStacks first second sourceStacks)) =
          some (secondConfiguration first second
            (Turing.TM2.stepAux (second.tm.m label) v sourceStacks))
      rw [liftSecondStmt_stepAux]
      rfl

private theorem phaseConfiguration
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (x : List Bool) :
    firstConfiguration first second
        (Turing.haltList first.tm
          (List.map first.outputAlphabet.invFun (bitEncoding (f x)))) =
      secondConfiguration first second
        (Turing.initList second.tm
          (List.map second.inputAlphabet.invFun (bitEncoding (f x)))) := by
  classical
  simp only [machine, ne_eq, firstConfiguration, haltList, Equiv.invFun_as_coe, id_eq,
      eq_mpr_eq_cast,
      secondConfiguration, initList, Option.map_some]
  congr 1
  funext k
  cases k with
  | inl k =>
      by_cases hk : k = first.tm.k₁
      · subst k
        simp only [bitEncoding, ne_eq, firstStacks, ↓reduceDIte, cast_eq, secondStacks,
            Equiv.coe_trans, List.map_map,
            List.map_inj_left, Function.comp_apply, Equiv.apply_symm_apply, implies_true]
      · simp only [ne_eq, firstStacks, hk, ↓reduceDIte, secondStacks]
  | inr k =>
      simp only [ne_eq, firstStacks, secondStacks, k.property, ↓reduceDIte]

@[simp] theorem haltList_stk_self
    (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₁)) :
    (Turing.haltList tm xs).stk tm.k₁ = xs := by
  classical
  simp only [haltList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq]

private theorem haltList_stk_of_ne
    (tm : Turing.FinTM2) (xs : List (tm.Γ tm.k₁))
    (j : tm.K) (hj : j ≠ tm.k₁) :
    (Turing.haltList tm xs).stk j = [] := by
  classical
  simp only [haltList, eq_mpr_eq_cast, hj, ↓reduceDIte]

private theorem secondStacks_secondStack
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (sourceStacks : ∀ k, List (second.tm.Γ k))
    (k : second.tm.K) :
    secondStacks first second sourceStacks
        (secondStack first.tm second.tm k) =
      List.map (secondAlphabetEquiv first second k) (sourceStacks k) := by
  classical
  cases hdec : second.tm.decidableEqK k second.tm.k₀ with
  | isTrue hk =>
      subst k
      unfold secondAlphabetEquiv secondStack
      rw! (castMode := .all) [hdec]
      simp only [↓dreduceDIte, ne_eq, secondStacks, ↓reduceDIte, Equiv.coe_trans, eq_mpr_eq_cast,
          cast_eq, id_eq]
  | isFalse hk =>
      unfold secondAlphabetEquiv secondStack
      rw! (castMode := .all) [hdec]
      simp only [hk, ↓dreduceDIte, ne_eq, secondStacks, ↓reduceDIte, eq_mpr_eq_cast, cast_eq,
          id_eq]
      induction sourceStacks k with
      | nil => rfl
      | cons a rest ih =>
          exact congrArg (List.cons a) ih

private theorem secondConfiguration_halt
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    (y : List Bool) :
    secondConfiguration first second
        (Turing.haltList second.tm
          (List.map second.outputAlphabet.invFun (bitEncoding y))) =
      Turing.haltList (machine first second)
        (List.map (auxiliary first second).outputAlphabet.invFun
          (bitEncoding y)) := by
  classical
  change
    (⟨none, (first.tm.initialState, second.tm.initialState),
      secondStacks first second
        (Turing.haltList second.tm
          (List.map second.outputAlphabet.invFun (bitEncoding y))).stk⟩ :
      (machine first second).Cfg) =
    (⟨none, (first.tm.initialState, second.tm.initialState),
      (Turing.haltList (machine first second)
        (List.map (auxiliary first second).outputAlphabet.invFun
          (bitEncoding y))).stk⟩ : (machine first second).Cfg)
  congr 1
  funext j
  by_cases hj : j = (machine first second).k₁
  · subst j
    rw [haltList_stk_self]
    change
      secondStacks first second
          (Turing.haltList second.tm
            (List.map second.outputAlphabet.invFun (bitEncoding y))).stk
          (secondStack first.tm second.tm second.tm.k₁) =
        List.map
          ((secondAlphabetEquiv first second second.tm.k₁).symm.trans
            second.outputAlphabet).invFun (bitEncoding y)
    rw [secondStacks_secondStack, haltList_stk_self]
    simp only [Equiv.invFun_as_coe, id_eq, List.map_map, Equiv.symm_trans, Equiv.symm_symm,
        Equiv.coe_trans]
  · have hhalt :
        (Turing.haltList (machine first second)
          (List.map (auxiliary first second).outputAlphabet.invFun
            (bitEncoding y))).stk j = [] :=
      haltList_stk_of_ne (machine first second) _ j hj
    rw [hhalt]
    cases j with
    | inl j =>
        by_cases hshared : j = first.tm.k₁
        · subst j
          rw [secondStacks_shared]
          have hinput : second.tm.k₀ ≠ second.tm.k₁ := by
            intro h
            apply hj
            change Sum.inl first.tm.k₁ =
              secondStack first.tm second.tm second.tm.k₁
            simp only [ne_eq, secondStack, h.symm, ↓reduceDIte]
          rw [haltList_stk_of_ne _ _ _ hinput, List.map_nil]
          rfl
        · simp only [ne_eq, secondStacks, hshared, ↓reduceDIte]
          rfl
    | inr j =>
        rw [secondStacks_private]
        have hout : j.val ≠ second.tm.k₁ := by
          intro h
          have hprivate : second.tm.k₁ ≠ second.tm.k₀ := by
            intro hinput
            exact j.property (h.trans hinput)
          apply hj
          change Sum.inr j = secondStack first.tm second.tm second.tm.k₁
          simp only [ne_eq, secondStack, hprivate, ↓reduceDIte, Sum.inr.injEq, Subtype.ext_iff, h]
        exact haltList_stk_of_ne _ _ _ hout

private noncomputable def computableInPolyTimeOfSeam
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g)
    :
    BitTM (g ∘ f) where
  toTM2ComputableAux := auxiliary first second
  time := compositeTimePolynomial first second
  outputsFun := by
    intro x
    have hfirst := firstConfiguration_evalsToInTime
      first second (first.outputsFun x)
    rw [firstConfiguration_init first second x,
      phaseConfiguration first second x] at hfirst
    have hsecond := evalsToInTimeMapOfStep
      second.tm.step (machine first second).step
      (secondConfiguration first second)
      (secondConfiguration_step first second)
      (second.outputsFun (f x))
    rw [secondConfiguration_halt first second (g (f x))] at hsecond
    have hboth := EvalsToInTime.trans (machine first second).step
      (first.time.eval x.length)
      (second.time.eval (f x).length)
      _ _ _ hfirst hsecond
    have hbudget :
        second.time.eval (f x).length + first.time.eval x.length ≤
          (compositeTimePolynomial first second).eval x.length := by
      simpa only [Nat.add_comm] using compositeTimePolynomial_bounds first second x
    exact {
      steps := hboth.steps
      evals_in_steps := hboth.evals_in_steps
      steps_le_m := hboth.steps_le_m.trans hbudget
    }

/-- GapCVP reduction support. -/
noncomputable def computableInPolyTime
    {f g : List Bool → List Bool}
    (first : BitTM f)
    (second : BitTM g) :
    BitTM (g ∘ f) :=
  computableInPolyTimeOfSeam first second

end TMComposition

theorem polynomialTimeClosedUnderComposition :
    PolynomialTimeClosedUnderComposition := by
  simp only [GapCVP.PolynomialTimeClosedUnderComposition, decide_eq_true_eq] at *
  intro first second firstMachine secondMachine
  exact ⟨TMComposition.computableInPolyTime
    firstMachine.some secondMachine.some⟩

namespace PromiseReduction

private def compWithCertificate {A B : BitLanguage} {P : PromiseProblem}
    (first : PolynomialReduction A B)
    (second : PromiseReduction B P)
    (certificate : Nonempty
      (BitTM
        (second.map ∘ first.map))) : PromiseReduction A P where
  map := second.map ∘ first.map
  polynomial_time := certificate
  completeness x hx :=
    second.completeness (first.map x) ((first.correct x).mp hx)
  soundness x hx := by
    apply second.soundness (first.map x)
    intro h
    exact hx ((first.correct x).mpr h)

/-- GapCVP reduction support. -/
def comp {A B : BitLanguage} {P : PromiseProblem}
    (first : PolynomialReduction A B)
    (second : PromiseReduction B P)
    (closed : PolynomialTimeClosedUnderComposition) :
    PromiseReduction A P := by
  have hclosed := closed
  simp only [PolynomialTimeClosedUnderComposition, decide_eq_true_eq] at hclosed
  exact compWithCertificate first second
    (hclosed first.map second.map first.polynomial_time second.polynomial_time)

end PromiseReduction

theorem nphardPromise_of_nphard_of_promiseReduction
    {A : BitLanguage} {P : PromiseProblem} (hard : NPHard A)
    (reduction : PromiseReduction A P)
    (closed : PolynomialTimeClosedUnderComposition) : NPHardPromise P := by
  apply @decide_eq_true _ (Classical.propDecidable _)
  intro L hL
  obtain ⟨first⟩ :=
    (@of_decide_eq_true _ (Classical.propDecidable _) hard) L hL
  exact ⟨PromiseReduction.comp first reduction closed⟩

end

namespace CL

/-- GapCVP reduction support. -/
abbrev Time (T : ℕ) := Fin (T + 1)
/-- GapCVP reduction support. -/
abbrev Position (T : ℕ) := Fin (T + 1)
/-- GapCVP reduction support. -/
abbrev Symbol (S : ℕ) := Fin (S + 1)

/-- GapCVP reduction support. -/
abbrev Variable (T S : ℕ) := Time T × Position T × Symbol S
/-- GapCVP reduction support. -/
abbrev SignedLiteral (T S : ℕ) := Variable T S × Bool
/-- GapCVP reduction support. -/
abbrev Clause (T S : ℕ) := Finset (SignedLiteral T S)
/-- GapCVP reduction support. -/
abbrev Formula (T S : ℕ) := Finset (Clause T S)

/-- GapCVP reduction support. -/
def positive {T S : ℕ} (v : Variable T S) : SignedLiteral T S :=
  (v, true)

/-- GapCVP reduction support. -/
def negative {T S : ℕ} (v : Variable T S) : SignedLiteral T S :=
  (v, false)

private noncomputable def satisfiesClause {T S : ℕ}
    (assignment : Variable T S → Bool) (clause : Clause T S) : Bool :=
  @decide (
  ∃ literal ∈ clause, assignment literal.1 = literal.2
  ) (Classical.propDecidable _)
private noncomputable def satisfiesFormula {T S : ℕ}
    (assignment : Variable T S → Bool) (formula : Formula T S) : Bool :=
  @decide (
  ∀ clause ∈ formula, satisfiesClause assignment clause
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def atLeastOneClause {T S : ℕ}
    (t : Time T) (i : Position T) : Clause T S :=
  Finset.univ.image (fun s : Symbol S => positive (t, i, s))

/-- GapCVP reduction support. -/
def atMostOneClause {T S : ℕ}
    (t : Time T) (i : Position T) (a b : Symbol S) : Clause T S :=
  {negative (t, i, a), negative (t, i, b)}

/-- GapCVP reduction support. -/
def initialClause {T S : ℕ}
    (input : Position T → Symbol S) (i : Position T) : Clause T S :=
  {positive ((0 : Time T), i, input i)}

/-- GapCVP reduction support. -/
def acceptanceClause {T S : ℕ} (accept : Symbol S) : Clause T S :=
  Finset.univ.image
    (fun i : Position T => positive ((Fin.last T), i, accept))

/-- GapCVP reduction support. -/
abbrev Window (T : ℕ) :=
  { ti : Time T × Position T // ti.1.val + 1 < T + 1 }

/-- GapCVP reduction support. -/
def nextTime {T : ℕ} (w : Window T) : Time T :=
  ⟨w.1.1.val + 1, w.2⟩

/-- GapCVP reduction support. -/
def leftPosition {T : ℕ} (w : Window T) : Position T :=
  ⟨w.1.2.val - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) w.1.2.isLt⟩

/-- GapCVP reduction support. -/
def rightPosition {T : ℕ} (w : Window T) : Position T :=
  ⟨min (w.1.2.val + 1) T,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

/-- GapCVP reduction support. -/
def windowAt {T : ℕ} (t : Fin T) (i : Position T) : Window T :=
  ⟨(⟨t.val, Nat.lt_trans t.isLt (Nat.lt_succ_self T)⟩, i),
    Nat.add_lt_add_right t.isLt 1⟩

/-- GapCVP reduction support. -/
abbrev WindowSymbols (S : ℕ) :=
  Symbol S × Symbol S × Symbol S × Symbol S

/-- GapCVP reduction support. -/
def transitionClause {T S : ℕ}
    (w : Window T) (symbols : WindowSymbols S) : Clause T S :=
  { negative (w.1.1, leftPosition w, symbols.1),
    negative (w.1.1, w.1.2, symbols.2.1),
    negative (w.1.1, rightPosition w, symbols.2.2.1),
    negative (nextTime w, w.1.2, symbols.2.2.2) }

/-- GapCVP reduction support. -/
structure Specification (T S : ℕ) where
  /-- GapCVP reduction support. -/
  input : Position T → Symbol S
  /-- GapCVP reduction support. -/
  accept : Symbol S
  /-- GapCVP reduction support. -/
  allowed : WindowSymbols S → Bool

/-- GapCVP reduction support. -/
def structuralClauses (T S : ℕ) : Formula T S :=
  (Finset.univ.image fun p : Time T × Position T =>
      atLeastOneClause p.1 p.2) ∪
    ((Finset.univ.filter fun p :
      (Time T × Position T) × (Symbol S × Symbol S) =>
        p.2.1 < p.2.2).image fun p =>
          atMostOneClause p.1.1 p.1.2 p.2.1 p.2.2)

/-- GapCVP reduction support. -/
def initialClauses {T S : ℕ} (spec : Specification T S) : Formula T S :=
  Finset.univ.image fun i : Position T => initialClause spec.input i

/-- GapCVP reduction support. -/
def transitionClauses {T S : ℕ}
    (spec : Specification T S) : Formula T S :=
  ((Finset.univ.filter fun p : Window T × WindowSymbols S =>
      spec.allowed p.2 = false).image fun p => transitionClause p.1 p.2)

/-- GapCVP reduction support. -/
def tableauFormula {T S : ℕ} (spec : Specification T S) : Formula T S :=
  structuralClauses T S ∪ initialClauses spec ∪
    {acceptanceClause spec.accept} ∪ transitionClauses spec

/-- GapCVP reduction support. -/
noncomputable def ValidTrace {T S : ℕ} (spec : Specification T S)
    (trace : Time T → Position T → Symbol S) : Bool :=
  @decide (
  (∀ i, trace 0 i = spec.input i) ∧
    (∃ i, trace (Fin.last T) i = spec.accept) ∧
    ∀ w : Window T,
      spec.allowed
        (trace w.1.1 (leftPosition w),
         trace w.1.1 w.1.2,
         trace w.1.1 (rightPosition w),
         trace (nextTime w) w.1.2) = true
  ) (Classical.propDecidable _)
private def assignmentOfTrace {T S : ℕ}
    (trace : Time T → Position T → Symbol S) : Variable T S → Bool :=
  fun v => decide (trace v.1 v.2.1 = v.2.2)

private theorem atLeastOneClause_satisfied {T S : ℕ}
    (trace : Time T → Position T → Symbol S)
    (t : Time T) (i : Position T) :
    satisfiesClause (assignmentOfTrace trace) (atLeastOneClause t i) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  refine ⟨positive (t, i, trace t i), ?_, ?_⟩
  · simp only [atLeastOneClause, Finset.mem_image, Finset.mem_univ, true_and,
      exists_apply_eq_apply]
  · simp only [assignmentOfTrace, positive, decide_true]

private theorem atMostOneClause_satisfied {T S : ℕ}
    (trace : Time T → Position T → Symbol S)
    (t : Time T) (i : Position T) (a b : Symbol S)
    (hab : a < b) :
    satisfiesClause (assignmentOfTrace trace) (atMostOneClause t i a b) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  by_cases ha : trace t i = a
  · refine ⟨negative (t, i, b), by simp only [atMostOneClause, Finset.mem_insert,
      Finset.mem_singleton, or_true], ?_⟩
    simp only [assignmentOfTrace, negative, ha, ne_of_lt hab, decide_false]
  · refine ⟨negative (t, i, a), by simp only [atMostOneClause, Finset.mem_insert,
      Finset.mem_singleton, true_or], ?_⟩
    simp only [assignmentOfTrace, negative, ha, decide_false]

private theorem initialClause_satisfied {T S : ℕ}
    (spec : Specification T S)
    (trace : Time T → Position T → Symbol S)
    (hinit : ∀ i, trace 0 i = spec.input i) (i : Position T) :
    satisfiesClause (assignmentOfTrace trace) (initialClause spec.input i) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  refine ⟨positive ((0 : Time T), i, spec.input i), by simp only [initialClause,
      Finset.mem_singleton], ?_⟩
  simp only [assignmentOfTrace, positive, hinit i, decide_true]

private theorem acceptanceClause_satisfied {T S : ℕ}
    (spec : Specification T S)
    (trace : Time T → Position T → Symbol S)
    (haccept : ∃ i, trace (Fin.last T) i = spec.accept) :
    satisfiesClause (assignmentOfTrace trace)
      (acceptanceClause spec.accept) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  obtain ⟨i, hi⟩ := haccept
  refine ⟨positive ((Fin.last T), i, spec.accept), ?_, ?_⟩
  · simp only [acceptanceClause, Finset.mem_image, Finset.mem_univ, true_and,
      exists_apply_eq_apply]
  · simp only [assignmentOfTrace, positive, hi, decide_true]

private theorem transitionClause_satisfied {T S : ℕ}
    (spec : Specification T S)
    (trace : Time T → Position T → Symbol S)
    (htransition : ∀ w : Window T,
      spec.allowed
        (trace w.1.1 (leftPosition w),
         trace w.1.1 w.1.2,
         trace w.1.1 (rightPosition w),
         trace (nextTime w) w.1.2) = true)
    (w : Window T) (symbols : WindowSymbols S)
    (hforbidden : spec.allowed symbols = false) :
    satisfiesClause (assignmentOfTrace trace) (transitionClause w symbols) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  by_cases h₁ : trace w.1.1 (leftPosition w) = symbols.1
  · by_cases h₂ : trace w.1.1 w.1.2 = symbols.2.1
    · by_cases h₃ : trace w.1.1 (rightPosition w) = symbols.2.2.1
      · have h₄ : trace (nextTime w) w.1.2 ≠ symbols.2.2.2 := by
          intro h₄
          have hgood := htransition w
          rw [h₁, h₂, h₃, h₄, hforbidden] at hgood
          contradiction
        refine ⟨negative (nextTime w, w.1.2, symbols.2.2.2),
          by simp only [transitionClause, Finset.mem_insert, Finset.mem_singleton, or_true], ?_⟩
        simp only [assignmentOfTrace, negative, h₄, decide_false]
      · refine ⟨negative (w.1.1, rightPosition w, symbols.2.2.1),
          by simp only [transitionClause, Finset.mem_insert, Finset.mem_singleton, true_or,
              or_true], ?_⟩
        simp only [assignmentOfTrace, negative, h₃, decide_false]
    · refine ⟨negative (w.1.1, w.1.2, symbols.2.1),
        by simp only [transitionClause, Finset.mem_insert, Finset.mem_singleton, true_or, or_true],
            ?_⟩
      simp only [assignmentOfTrace, negative, h₂, decide_false]
  · refine ⟨negative (w.1.1, leftPosition w, symbols.1),
      by simp only [transitionClause, Finset.mem_insert, Finset.mem_singleton, true_or], ?_⟩
    simp only [assignmentOfTrace, negative, h₁, decide_false]

private theorem tableau_completeness {T S : ℕ}
    (spec : Specification T S)
    (trace : Time T → Position T → Symbol S)
    (htrace : ValidTrace spec trace) :
    satisfiesFormula (assignmentOfTrace trace) (tableauFormula spec) := by
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq]
  have htrace' := htrace
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq] at htrace'
  intro clause hclause
  simp only [tableauFormula, Finset.mem_union, Finset.mem_singleton] at hclause
  rcases hclause with ((hstruct | hinit) | haccept) | htransition
  · simp only [structuralClauses, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at hstruct
    rcases hstruct with ⟨p, rfl⟩ | ⟨p, hp, rfl⟩
    · exact atLeastOneClause_satisfied trace p.1 p.2
    · exact atMostOneClause_satisfied trace p.1.1 p.1.2
        p.2.1 p.2.2 hp
  · simp only [initialClauses, Finset.mem_image,
      Finset.mem_univ, true_and] at hinit
    obtain ⟨i, rfl⟩ := hinit
    exact initialClause_satisfied spec trace htrace'.1 i
  · subst clause
    exact acceptanceClause_satisfied spec trace htrace'.2.1
  · simp only [transitionClauses, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and] at htransition
    obtain ⟨p, hp, rfl⟩ := htransition
    exact transitionClause_satisfied spec trace htrace'.2.2 p.1 p.2 hp

theorem atLeastOneClause_mem_tableauFormula {T S : ℕ}
    (spec : Specification T S) (t : Time T) (i : Position T) :
    atLeastOneClause t i ∈ tableauFormula spec := by
  have h : atLeastOneClause t i ∈ structuralClauses T S := by
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(t, i), Finset.mem_univ _, rfl⟩
  simp only [tableauFormula, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl h))

theorem atMostOneClause_mem_tableauFormula {T S : ℕ}
    (spec : Specification T S) (t : Time T) (i : Position T)
    (a b : Symbol S) (hab : a < b) :
    atMostOneClause t i a b ∈ tableauFormula spec := by
  have h : atMostOneClause t i a b ∈ structuralClauses T S := by
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨((t, i), (a, b)), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, hab, and_self]
  simp only [tableauFormula, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inl h))

theorem initialClause_mem_tableauFormula {T S : ℕ}
    (spec : Specification T S) (i : Position T) :
    initialClause spec.input i ∈ tableauFormula spec := by
  have h : initialClause spec.input i ∈ initialClauses spec :=
    Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  simp only [tableauFormula, Finset.mem_union]
  exact Or.inl (Or.inl (Or.inr h))

theorem acceptanceClause_mem_tableauFormula {T S : ℕ}
    (spec : Specification T S) :
    acceptanceClause spec.accept ∈ tableauFormula spec := by
  simp only [tableauFormula, Finset.union_assoc, Finset.union_singleton, Finset.insert_union,
    Finset.mem_insert, Finset.mem_union, true_or]

theorem transitionClause_mem_tableauFormula {T S : ℕ}
    (spec : Specification T S) (w : Window T)
    (symbols : WindowSymbols S)
    (hforbidden : spec.allowed symbols = false) :
    transitionClause w symbols ∈ tableauFormula spec := by
  have h : transitionClause w symbols ∈ transitionClauses spec := by
    apply Finset.mem_image.mpr
    refine ⟨(w, symbols), ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, hforbidden, and_self]
  exact Finset.mem_union_right _ h

private theorem symbol_exists_of_satisfiesFormula {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T) :
    ∃ s : Symbol S, assignment (t, i, s) = true := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  obtain ⟨literal, hliteral, hvalue⟩ :=
    hsat' (atLeastOneClause t i)
      (atLeastOneClause_mem_tableauFormula spec t i)
  simp only [atLeastOneClause, Finset.mem_image,
    Finset.mem_univ, true_and] at hliteral
  obtain ⟨s, rfl⟩ := hliteral
  exact ⟨s, hvalue⟩

private theorem symbol_unique_of_satisfiesFormula {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T)
    (a b : Symbol S)
    (ha : assignment (t, i, a) = true)
    (hb : assignment (t, i, b) = true) : a = b := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  have exclude (a b : Symbol S) (hab : a < b)
      (ha : assignment (t, i, a) = true)
      (hb : assignment (t, i, b) = true) : False := by
    obtain ⟨literal, hliteral, hvalue⟩ :=
      hsat' (atMostOneClause t i a b)
        (atMostOneClause_mem_tableauFormula spec t i a b hab)
    simp only [atMostOneClause, Finset.mem_insert,
      Finset.mem_singleton] at hliteral
    rcases hliteral with hleft | hright
    · subst literal
      have hfalse : assignment (t, i, a) = false := by
        simpa only [negative] using hvalue
      simp only [ha, Bool.true_eq_false] at hfalse
    · subst literal
      have hfalse : assignment (t, i, b) = false := by
        simpa only [negative] using hvalue
      simp only [hb, Bool.true_eq_false] at hfalse
  rcases lt_trichotomy a b with hab | hab | hab
  · exact (exclude a b hab ha hb).elim
  · exact hab
  · exact (exclude b a hab hb ha).elim

private noncomputable def traceOfAssignment {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec)) :
    Time T → Position T → Symbol S :=
  fun t i => Classical.choose
    (symbol_exists_of_satisfiesFormula spec assignment hsat t i)

private theorem traceOfAssignment_selected {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T) :
    assignment (t, i, traceOfAssignment spec assignment hsat t i) = true :=
  Classical.choose_spec
    (symbol_exists_of_satisfiesFormula spec assignment hsat t i)

private theorem traceOfAssignment_eq_of_selected {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (t : Time T) (i : Position T) (s : Symbol S)
    (hs : assignment (t, i, s) = true) :
    traceOfAssignment spec assignment hsat t i = s :=
  symbol_unique_of_satisfiesFormula spec assignment hsat t i
    (traceOfAssignment spec assignment hsat t i) s
    (traceOfAssignment_selected spec assignment hsat t i) hs

private theorem traceOfAssignment_initial {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (i : Position T) :
    traceOfAssignment spec assignment hsat 0 i = spec.input i := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  obtain ⟨literal, hliteral, hvalue⟩ :=
    hsat' (initialClause spec.input i)
      (initialClause_mem_tableauFormula spec i)
  simp only [initialClause, Finset.mem_singleton] at hliteral
  subst literal
  apply traceOfAssignment_eq_of_selected spec assignment hsat 0 i
  simpa only [positive] using hvalue

private theorem traceOfAssignment_accepting {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec)) :
    ∃ i : Position T,
      traceOfAssignment spec assignment hsat (Fin.last T) i = spec.accept := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  obtain ⟨literal, hliteral, hvalue⟩ :=
    hsat' (acceptanceClause spec.accept)
      (acceptanceClause_mem_tableauFormula spec)
  simp only [acceptanceClause, Finset.mem_image,
    Finset.mem_univ, true_and] at hliteral
  obtain ⟨i, rfl⟩ := hliteral
  refine ⟨i, traceOfAssignment_eq_of_selected spec assignment hsat
    (Fin.last T) i spec.accept ?_⟩
  simpa only [positive] using hvalue

private theorem traceOfAssignment_transition {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec))
    (w : Window T) :
    spec.allowed
      (traceOfAssignment spec assignment hsat w.1.1 (leftPosition w),
       traceOfAssignment spec assignment hsat w.1.1 w.1.2,
       traceOfAssignment spec assignment hsat w.1.1 (rightPosition w),
       traceOfAssignment spec assignment hsat (nextTime w) w.1.2) = true := by
  have hsat' := hsat
  simp only [GapCVP.CL.satisfiesFormula, GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsat'
  let symbols : WindowSymbols S :=
    (traceOfAssignment spec assignment hsat w.1.1 (leftPosition w),
     traceOfAssignment spec assignment hsat w.1.1 w.1.2,
     traceOfAssignment spec assignment hsat w.1.1 (rightPosition w),
     traceOfAssignment spec assignment hsat (nextTime w) w.1.2)
  change spec.allowed symbols = true
  cases hallowed : spec.allowed symbols with
  | true => rfl
  | false =>
    exfalso
    obtain ⟨literal, hliteral, hvalue⟩ :=
      hsat' (transitionClause w symbols)
        (transitionClause_mem_tableauFormula spec w symbols hallowed)
    simp only [transitionClause, Finset.mem_insert,
      Finset.mem_singleton] at hliteral
    rcases hliteral with h₁ | h₂ | h₃ | h₄
    · subst literal
      have hfalse : assignment
          (w.1.1, leftPosition w, symbols.1) = false := by
        simpa only [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 (leftPosition w)
      change assignment
        (w.1.1, leftPosition w,
          traceOfAssignment spec assignment hsat w.1.1 (leftPosition w))
          = false at hfalse
      simp only [htrue, Bool.true_eq_false] at hfalse
    · subst literal
      have hfalse : assignment (w.1.1, w.1.2, symbols.2.1) = false := by
        simpa only [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 w.1.2
      change assignment
        (w.1.1, w.1.2,
          traceOfAssignment spec assignment hsat w.1.1 w.1.2)
          = false at hfalse
      simp only [htrue, Bool.true_eq_false] at hfalse
    · subst literal
      have hfalse : assignment
          (w.1.1, rightPosition w, symbols.2.2.1) = false := by
        simpa only [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        w.1.1 (rightPosition w)
      change assignment
        (w.1.1, rightPosition w,
          traceOfAssignment spec assignment hsat w.1.1 (rightPosition w))
          = false at hfalse
      simp only [htrue, Bool.true_eq_false] at hfalse
    · subst literal
      have hfalse : assignment
          (nextTime w, w.1.2, symbols.2.2.2) = false := by
        simpa only [negative] using hvalue
      have htrue := traceOfAssignment_selected spec assignment hsat
        (nextTime w) w.1.2
      change assignment
        (nextTime w, w.1.2,
          traceOfAssignment spec assignment hsat (nextTime w) w.1.2)
          = false at hfalse
      simp only [htrue, Bool.true_eq_false] at hfalse

private theorem tableau_soundness {T S : ℕ}
    (spec : Specification T S)
    (assignment : Variable T S → Bool)
    (hsat : satisfiesFormula assignment (tableauFormula spec)) :
    ValidTrace spec (traceOfAssignment spec assignment hsat) := by
  simp only [GapCVP.CL.ValidTrace, decide_eq_true_eq]
  exact ⟨traceOfAssignment_initial spec assignment hsat,
    traceOfAssignment_accepting spec assignment hsat,
    traceOfAssignment_transition spec assignment hsat⟩

private theorem tableau_satisfiable_iff_validTrace {T S : ℕ}
    (spec : Specification T S) :
    (∃ assignment : Variable T S → Bool,
      satisfiesFormula assignment (tableauFormula spec)) ↔
      ∃ trace : Time T → Position T → Symbol S, ValidTrace spec trace := by
  constructor
  · rintro ⟨assignment, hs⟩
    exact ⟨traceOfAssignment spec assignment hs,
      tableau_soundness spec assignment hs⟩
  · rintro ⟨trace, ht⟩
    exact ⟨assignmentOfTrace trace, tableau_completeness spec trace ht⟩

end CL

namespace ThreeCNFReduction

open GapCVP.CL

/-- GapCVP reduction support. -/
def sortedElements {α : Type} [Encodable α] (s : Finset α) : List α := by
  letI : IsTrans α
    (fun a b : α => Encodable.encode a ≤ Encodable.encode b) :=
    ⟨fun _ _ _ hab hbc => Nat.le_trans hab hbc⟩
  letI : Std.Antisymm
    (fun a b : α => Encodable.encode a ≤ Encodable.encode b) :=
    ⟨fun _ _ hab hba =>
      Encodable.encode_injective (Nat.le_antisymm hab hba)⟩
  letI : Std.Total
    (fun a b : α => Encodable.encode a ≤ Encodable.encode b) :=
    ⟨fun _ _ => Nat.le_total _ _⟩
  exact s.sort (fun a b : α => Encodable.encode a ≤ Encodable.encode b)

@[simp] theorem mem_sortedElements {α : Type} [Encodable α]
    (s : Finset α) (a : α) :
    a ∈ sortedElements s ↔ a ∈ s := by
  simp only [sortedElements, Finset.mem_sort]

@[simp] theorem sortedElements_length {α : Type} [Encodable α]
    (s : Finset α) :
    (sortedElements s).length = s.card := by
  simp only [sortedElements, Finset.length_sort]

private noncomputable def satisfies (assignment : ℕ → Bool) (formula : ThreeCNF) : Bool :=
  @decide (
  ∀ clause ∈ formula, clauseSatisfied assignment clause
  ) (Classical.propDecidable _)
@[simp] private theorem satisfies_nil (assignment : ℕ → Bool) :
    satisfies assignment [] := by
  simp only [satisfies, List.not_mem_nil, IsEmpty.forall_iff, implies_true, decide_true]

@[simp] private theorem satisfies_append (assignment : ℕ → Bool)
    (left right : ThreeCNF) :
    satisfies assignment (left ++ right) ↔
      satisfies assignment left ∧ satisfies assignment right := by
  simp only [satisfies, List.mem_append, or_imp, forall_and, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq]

@[simp] private theorem satisfies_singleton (assignment : ℕ → Bool)
    (clause : ThreeClause) :
    satisfies assignment [clause] ↔ clauseSatisfied assignment clause := by
  simp only [satisfies, List.mem_cons, List.not_mem_nil, or_false, forall_eq, Bool.decide_eq_true]

/-- GapCVP reduction support. -/
noncomputable def allDistinct (formula : ThreeCNF) : Bool :=
  @decide (
  ∀ clause ∈ formula, clauseHasDistinctVariables clause
  ) (Classical.propDecidable _)
@[simp] private theorem allDistinct_nil : allDistinct [] := by
  simp only [allDistinct, List.not_mem_nil, IsEmpty.forall_iff, implies_true, decide_true]

@[simp] private theorem allDistinct_append (left right : ThreeCNF) :
    allDistinct (left ++ right) ↔
      allDistinct left ∧ allDistinct right := by
  simp only [allDistinct, List.mem_append, or_imp, forall_and, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq]

@[simp] private theorem allDistinct_singleton (clause : ThreeClause) :
    allDistinct [clause] ↔ clauseHasDistinctVariables clause := by
  simp only [allDistinct, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      Bool.decide_eq_true]

private theorem threeCNFSatisfiable_iff (formula : ThreeCNF) :
    threeCNFSatisfiable formula ↔
      allDistinct formula ∧
        ∃ assignment : ℕ → Bool, satisfies assignment formula := by
  simp only [GapCVP.threeCNFSatisfiable, GapCVP.ThreeCNFReduction.allDistinct,
      GapCVP.ThreeCNFReduction.satisfies, decide_eq_true_eq]

/-- GapCVP reduction support. -/
def sourceVariable {T S : ℕ} (v : Variable T S) : ℕ :=
  4 * Encodable.encode v

/-- GapCVP reduction support. -/
def accumulatorVariable (clauseIndex prefixIndex : ℕ) : ℕ :=
  4 * Encodable.encode (clauseIndex, prefixIndex) + 1

private theorem accumulatorVariable_injective :
    Function.Injective
      (fun p : ℕ × ℕ => accumulatorVariable p.1 p.2) := by
  intro a b h
  apply Encodable.encode_injective
  change 4 * Encodable.encode a + 1 =
    4 * Encodable.encode b + 1 at h
  omega

private theorem sourceVariable_ne_accumulatorVariable {T S : ℕ}
    (v : Variable T S) (clauseIndex prefixIndex : ℕ) :
    sourceVariable v ≠ accumulatorVariable clauseIndex prefixIndex := by
  unfold sourceVariable accumulatorVariable
  omega

private theorem sourceVariable_ne_paddingVariable₀ {T S : ℕ}
    (v : Variable T S) :
    sourceVariable v ≠ 2 := by
  unfold sourceVariable
  omega

private theorem accumulatorVariable_ne_paddingVariable₀
    (clauseIndex prefixIndex : ℕ) :
    accumulatorVariable clauseIndex prefixIndex ≠ 2 := by
  unfold accumulatorVariable
  omega

private theorem accumulatorVariable_ne_paddingVariable₁
    (clauseIndex prefixIndex : ℕ) :
    accumulatorVariable clauseIndex prefixIndex ≠ 3 := by
  unfold accumulatorVariable
  omega

private theorem consecutive_accumulatorVariables_ne
    (clauseIndex prefixIndex : ℕ) :
    accumulatorVariable clauseIndex prefixIndex ≠
      accumulatorVariable clauseIndex (prefixIndex + 1) := by
  intro h
  have hp := accumulatorVariable_injective
    (show accumulatorVariable
      (clauseIndex, prefixIndex).1 (clauseIndex, prefixIndex).2 =
      accumulatorVariable
      (clauseIndex, prefixIndex + 1).1
      (clauseIndex, prefixIndex + 1).2 from h)
  have := congrArg Prod.snd hp
  omega

/-- GapCVP reduction support. -/
def triple (a b c : Literal) : ThreeClause := ![a, b, c]

@[simp] private theorem clauseSatisfied_triple (assignment : ℕ → Bool)
    (a b c : Literal) :
    clauseSatisfied assignment (triple a b c) ↔
      literalSatisfied assignment a ∨
        literalSatisfied assignment b ∨
        literalSatisfied assignment c := by
  simp only [clauseSatisfied, triple, Fin.exists_fin_succ, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_fin_one, exists_const, Bool.decide_or,
          Bool.decide_eq_true, Bool.or_eq_true]

private theorem triple_distinct (a b c : Literal)
    (hab : a.1 ≠ b.1) (hac : a.1 ≠ c.1) (hbc : b.1 ≠ c.1) :
    clauseHasDistinctVariables (triple a b c) := by
  simp only [GapCVP.clauseHasDistinctVariables, decide_eq_true_eq]
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [triple]

/-- GapCVP reduction support. -/
def paddedBinary (a b : Literal) : ThreeCNF :=
  [triple a b (2, true),
   triple a b (2, false)]

@[simp] private theorem paddedBinary_satisfied (assignment : ℕ → Bool)
    (a b : Literal) :
    satisfies assignment (paddedBinary a b) ↔
      literalSatisfied assignment a ∨ literalSatisfied assignment b := by
  cases h : assignment 2 <;>
    simp [satisfies, paddedBinary, literalSatisfied, h]

private theorem paddedBinary_allDistinct (a b : Literal)
    (hab : a.1 ≠ b.1)
    (ha : a.1 ≠ 2)
    (hb : b.1 ≠ 2) :
    allDistinct (paddedBinary a b) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq]
  intro clause hclause
  simp only [paddedBinary, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with h | h
  · subst clause
    exact triple_distinct _ _ _ hab ha hb
  · subst clause
    exact triple_distinct _ _ _ hab ha hb

/-- GapCVP reduction support. -/
def paddedUnary (a : Literal) : ThreeCNF :=
  [triple a (2, false) (3, false),
   triple a (2, false) (3, true),
   triple a (2, true) (3, false),
   triple a (2, true) (3, true)]

@[simp] private theorem paddedUnary_satisfied (assignment : ℕ → Bool)
    (a : Literal) :
    satisfies assignment (paddedUnary a) ↔
      literalSatisfied assignment a := by
  cases h₀ : assignment 2 <;>
    cases h₁ : assignment 3 <;>
    simp [satisfies, paddedUnary, literalSatisfied, h₀, h₁]

private theorem paddedUnary_allDistinct (a : Literal)
    (ha₀ : a.1 ≠ 2)
    (ha₁ : a.1 ≠ 3) :
    allDistinct (paddedUnary a) := by
  simp only [GapCVP.ThreeCNFReduction.allDistinct, decide_eq_true_eq]
  intro clause hclause
  simp only [paddedUnary, List.mem_cons, List.not_mem_nil, or_false] at hclause
  rcases hclause with h | h | h | h
  all_goals
    subst clause
    exact triple_distinct _ _ _ ha₀ ha₁ (by decide)

/-- GapCVP reduction support. -/
def negate (a : Literal) : Literal := (a.1, !a.2)

@[simp] private theorem literalSatisfied_negate (assignment : ℕ → Bool)
    (a : Literal) :
    literalSatisfied assignment (negate a) ↔
      ¬ literalSatisfied assignment a := by
  obtain ⟨n, b⟩ := a
  cases b <;> cases assignment n <;>
    simp [negate, literalSatisfied]

/-- GapCVP reduction support. -/
def orGate (a b output : Literal) : ThreeCNF :=
  paddedBinary (negate a) output ++
    paddedBinary (negate b) output ++
    [triple a b (negate output)]

private theorem orGate_satisfied (assignment : ℕ → Bool)
    (a b output : Literal) :
    satisfies assignment (orGate a b output) ↔
      (literalSatisfied assignment output ↔
        literalSatisfied assignment a ∨ literalSatisfied assignment b) := by
  simp only [orGate, satisfies_append, paddedBinary_satisfied,
    satisfies_singleton, clauseSatisfied_triple, literalSatisfied_negate]
  tauto

private theorem orGate_allDistinct (a b output : Literal)
    (hab : a.1 ≠ b.1)
    (hao : a.1 ≠ output.1)
    (hbo : b.1 ≠ output.1)
    (ha : a.1 ≠ 2)
    (hb : b.1 ≠ 2)
    (ho : output.1 ≠ 2) :
    allDistinct (orGate a b output) := by
  rw [orGate, allDistinct_append, allDistinct_append,
    allDistinct_singleton]
  refine ⟨⟨paddedBinary_allDistinct _ _ ?_ ?_ ho,
    paddedBinary_allDistinct _ _ ?_ ?_ ho⟩,
    triple_distinct _ _ _ hab ?_ ?_⟩
  · exact hao
  · exact ha
  · exact hbo
  · exact hb
  · exact hao
  · exact hbo

@[simp] private theorem paddedBinary_length (a b : Literal) :
    (paddedBinary a b).length = 2 := by
  rfl

@[simp] theorem paddedUnary_length (a : Literal) :
    (paddedUnary a).length = 4 := by
  rfl

@[simp] theorem orGate_length (a b output : Literal) :
    (orGate a b output).length = 5 := by
  simp only [orGate, List.append_assoc, List.length_append, paddedBinary_length, List.length_cons,
      List.length_nil, zero_add, Nat.reduceAdd]

/-- GapCVP reduction support. -/
def sourceLiteral {T S : ℕ}
    (literal : SignedLiteral T S) : Literal :=
  (sourceVariable literal.1, literal.2)

/-- GapCVP reduction support. -/
def accumulatorLiteral
    (clauseIndex prefixIndex : ℕ) (value : Bool) : Literal :=
  (accumulatorVariable clauseIndex prefixIndex, value)

/-- GapCVP reduction support. -/
def gateList {T S : ℕ} (clauseIndex : ℕ) :
    ℕ → List (SignedLiteral T S) → ThreeCNF
  | _, [] => []
  | prefixIndex, literal :: remaining =>
    orGate (sourceLiteral literal)
      (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
      (accumulatorLiteral clauseIndex prefixIndex true) ++
      gateList clauseIndex (prefixIndex + 1) remaining

private theorem gateList_allDistinct {T S : ℕ}
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S)) :
    allDistinct (gateList clauseIndex prefixIndex literals) := by
  induction literals generalizing prefixIndex with
  | nil => simp only [gateList, allDistinct_nil]
  | cons literal remaining ih =>
    rw [gateList, allDistinct_append]
    refine ⟨orGate_allDistinct _ _ _ ?_ ?_ ?_ ?_ ?_ ?_,
      ih (prefixIndex + 1)⟩
    · exact sourceVariable_ne_accumulatorVariable
        literal.1 clauseIndex (prefixIndex + 1)
    · exact sourceVariable_ne_accumulatorVariable
        literal.1 clauseIndex prefixIndex
    · exact Ne.symm
        (consecutive_accumulatorVariables_ne clauseIndex prefixIndex)
    · exact sourceVariable_ne_paddingVariable₀ literal.1
    · exact accumulatorVariable_ne_paddingVariable₀
        clauseIndex (prefixIndex + 1)
    · exact accumulatorVariable_ne_paddingVariable₀
        clauseIndex prefixIndex

/-- GapCVP reduction support. -/
def encodeClause {T S : ℕ}
    (clauseIndex : ℕ) (clause : Clause T S) : ThreeCNF :=
  paddedUnary (accumulatorLiteral clauseIndex 0 true) ++
    gateList clauseIndex 0 (sortedElements clause) ++
    paddedUnary
      (accumulatorLiteral clauseIndex (sortedElements clause).length false)

private theorem encodeClause_allDistinct {T S : ℕ}
    (clauseIndex : ℕ) (clause : Clause T S) :
    allDistinct (encodeClause clauseIndex clause) := by
  rw [encodeClause, allDistinct_append, allDistinct_append]
  exact ⟨⟨paddedUnary_allDistinct _
    (accumulatorVariable_ne_paddingVariable₀ clauseIndex 0)
    (accumulatorVariable_ne_paddingVariable₁ clauseIndex 0),
    gateList_allDistinct clauseIndex 0 (sortedElements clause)⟩,
    paddedUnary_allDistinct _
      (accumulatorVariable_ne_paddingVariable₀
        clauseIndex (sortedElements clause).length)
      (accumulatorVariable_ne_paddingVariable₁
        clauseIndex (sortedElements clause).length)⟩

/-- GapCVP reduction support. -/
def encodeFormulaFrom {T S : ℕ} :
    ℕ → List (Clause T S) → ThreeCNF
  | _, [] => []
  | clauseIndex, clause :: remaining =>
    encodeClause clauseIndex clause ++
      encodeFormulaFrom (clauseIndex + 1) remaining

private theorem encodeFormulaFrom_allDistinct {T S : ℕ}
    (clauseIndex : ℕ) (clauses : List (Clause T S)) :
    allDistinct (encodeFormulaFrom clauseIndex clauses) := by
  induction clauses generalizing clauseIndex with
  | nil => simp only [encodeFormulaFrom, allDistinct_nil]
  | cons clause remaining ih =>
    rw [encodeFormulaFrom, allDistinct_append]
    exact ⟨encodeClause_allDistinct clauseIndex clause,
      ih (clauseIndex + 1)⟩

private def encodeFormula {T S : ℕ} (formula : Formula T S) : ThreeCNF :=
  encodeFormulaFrom 0 (sortedElements formula)

theorem encodeFormula_allDistinct {T S : ℕ} (formula : Formula T S) :
    allDistinct (encodeFormula formula) :=
  encodeFormulaFrom_allDistinct 0 (sortedElements formula)

theorem signedLiteral_card (T S : ℕ) :
    Fintype.card (SignedLiteral T S) =
      2 * ((T + 1) ^ 2 * (S + 1)) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  ring

private def liftAssignment {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool) (n : ℕ) : Bool :=
  if n % 4 = 0 then
    match (Encodable.decode (n / 4) : Option (Variable T S)) with
    | some v => assignment v
    | none => false
  else if n % 4 = 1 then
    match (Encodable.decode (n / 4) : Option (ℕ × ℕ)) with
    | some p =>
      match clauses[p.1]? with
      | some clause =>
        ((sortedElements clause).drop p.2).any
          (fun literal => assignment literal.1 == literal.2)
      | none => false
    | none => false
  else
    false

/-- GapCVP reduction support. -/
def restrictAssignment {T S : ℕ}
    (assignment : ℕ → Bool) : Variable T S → Bool :=
  fun v => assignment (sourceVariable v)

@[simp] private theorem liftAssignment_sourceVariable {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (v : Variable T S) :
    liftAssignment clauses assignment (sourceVariable v) = assignment v := by
  simp only [liftAssignment, sourceVariable, Nat.mul_mod_right, ↓reduceIte, ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true, mul_div_cancel_left₀, Encodable.encodek]

@[simp] private theorem liftAssignment_accumulatorVariable {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex prefixIndex : ℕ)
    (clause : Clause T S)
    (hclause : clauses[clauseIndex]? = some clause) :
    liftAssignment clauses assignment
      (accumulatorVariable clauseIndex prefixIndex) =
        ((sortedElements clause).drop prefixIndex).any
          (fun literal => assignment literal.1 == literal.2) := by
  have hone :
      (4 * Encodable.encode (clauseIndex, prefixIndex) + 1) % 4 = 1 := by
    omega
  have hdiv :
      (4 * Encodable.encode (clauseIndex, prefixIndex) + 1) / 4 =
        Encodable.encode (clauseIndex, prefixIndex) := by
    omega
  simp only [liftAssignment, accumulatorVariable, ↓reduceIte,
    hone, hdiv, Encodable.encodek, hclause, Nat.one_ne_zero]

private theorem gateList_sound {T S : ℕ}
    (assignment : ℕ → Bool)
    (clauseIndex prefixIndex : ℕ)
    (literals : List (SignedLiteral T S))
    (hgates : satisfies assignment
      (gateList clauseIndex prefixIndex literals))
    (hstart : assignment
      (accumulatorVariable clauseIndex prefixIndex) = true)
    (hfinish : assignment
      (accumulatorVariable clauseIndex
        (prefixIndex + literals.length)) = false) :
    ∃ literal ∈ literals,
      assignment (sourceVariable literal.1) = literal.2 := by
  induction literals generalizing prefixIndex with
  | nil =>
    simp only [List.length_nil, add_zero] at hfinish
    simp only [hstart, Bool.true_eq_false] at hfinish
  | cons literal remaining ih =>
    simp only [gateList, satisfies_append] at hgates
    obtain ⟨hgate, hremaining⟩ := hgates
    have hchoice :=
      (orGate_satisfied assignment
        (sourceLiteral literal)
        (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
        (accumulatorLiteral clauseIndex prefixIndex true)).mp hgate
    have houtput : literalSatisfied assignment
        (accumulatorLiteral clauseIndex prefixIndex true) := by
      apply @decide_eq_true _ (Classical.propDecidable _)
      exact hstart
    rcases hchoice.mp houtput with hsatisfied | hnext
    · refine ⟨literal, by simp only [List.mem_cons, true_or], ?_⟩
      simpa only [sourceLiteral] using
        @of_decide_eq_true _ (Classical.propDecidable _) hsatisfied
    · have hnext' : assignment
          (accumulatorVariable clauseIndex (prefixIndex + 1)) = true := by
        simpa only [accumulatorLiteral] using
          @of_decide_eq_true _ (Classical.propDecidable _) hnext
      have hindex :
          prefixIndex + 1 + remaining.length =
            prefixIndex + (literal :: remaining).length := by
        simp only [List.length_cons]
        omega
      have hfinish' : assignment
          (accumulatorVariable clauseIndex
            (prefixIndex + 1 + remaining.length)) = false := by
        rw [hindex]
        exact hfinish
      obtain ⟨witness, hwitness, hvalue⟩ :=
        ih (prefixIndex + 1) hremaining hnext' hfinish'
      exact ⟨witness, by simp only [List.mem_cons, hwitness, or_true], hvalue⟩

private theorem encodeClause_sound {T S : ℕ}
    (assignment : ℕ → Bool)
    (clauseIndex : ℕ) (clause : Clause T S)
    (hsatisfied : satisfies assignment
      (encodeClause clauseIndex clause)) :
    CL.satisfiesClause (restrictAssignment assignment) clause := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq]
  simp only [encodeClause, satisfies_append] at hsatisfied
  obtain ⟨⟨hfirst, hgates⟩, hlast⟩ := hsatisfied
  have hstart : assignment (accumulatorVariable clauseIndex 0) = true := by
    exact @of_decide_eq_true _ (Classical.propDecidable _)
      ((paddedUnary_satisfied assignment _).mp hfirst)
  have hfinish : assignment
      (accumulatorVariable clauseIndex
        (0 + (sortedElements clause).length)) = false := by
    simpa only [sortedElements_length, zero_add, literalSatisfied, accumulatorLiteral,
        Bool.decide_eq_false,
        Bool.not_eq_eq_eq_not, Bool.not_true] using (paddedUnary_satisfied assignment _).mp hlast
  obtain ⟨literal, hmem, hvalue⟩ :=
    gateList_sound assignment clauseIndex 0
      (sortedElements clause) hgates hstart hfinish
  exact ⟨literal, (mem_sortedElements clause literal).mp hmem, hvalue⟩

private theorem encodeFormulaFrom_sound {T S : ℕ}
    (assignment : ℕ → Bool)
    (clauseIndex : ℕ) (clauses : List (Clause T S))
    (hsatisfied : satisfies assignment
      (encodeFormulaFrom clauseIndex clauses)) :
    ∀ clause ∈ clauses,
      CL.satisfiesClause (restrictAssignment assignment) clause := by
  induction clauses generalizing clauseIndex with
  | nil => simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true]
  | cons clause remaining ih =>
    simp only [encodeFormulaFrom, satisfies_append] at hsatisfied
    obtain ⟨hclause, hremaining⟩ := hsatisfied
    intro candidate hcandidate
    simp only [List.mem_cons] at hcandidate
    rcases hcandidate with rfl | hcandidate
    · exact encodeClause_sound assignment clauseIndex _ hclause
    · exact ih (clauseIndex + 1) hremaining candidate hcandidate

private theorem encodeFormula_sound {T S : ℕ}
    (formula : Formula T S)
    (assignment : ℕ → Bool)
    (hsatisfied : satisfies assignment (encodeFormula formula)) :
    satisfiesFormula (restrictAssignment assignment) formula := by
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq]
  intro clause hclause
  exact encodeFormulaFrom_sound assignment 0 (sortedElements formula)
    hsatisfied clause ((mem_sortedElements formula clause).mpr hclause)

private theorem drop_succ_of_drop_cons {α : Type}
    (literals : List α) (prefixIndex : ℕ)
    (literal : α) (remaining : List α)
    (hdrop : literals.drop prefixIndex = literal :: remaining) :
    literals.drop (prefixIndex + 1) = remaining := by
  have h := congrArg (List.drop 1) hdrop
  simpa only [List.drop_drop, List.drop_succ_cons, List.drop_zero] using h

private theorem gateList_complete {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex : ℕ) (clause : Clause T S)
    (hclause : clauses[clauseIndex]? = some clause)
    (prefixIndex : ℕ)
    (literals : List (SignedLiteral T S))
    (hdrop : (sortedElements clause).drop prefixIndex = literals) :
    satisfies (liftAssignment clauses assignment)
      (gateList clauseIndex prefixIndex literals) := by
  induction literals generalizing prefixIndex with
  | nil => simp only [gateList, satisfies_nil]
  | cons literal remaining ih =>
    have hnext := drop_succ_of_drop_cons
      (sortedElements clause) prefixIndex literal remaining hdrop
    rw [gateList, satisfies_append]
    refine ⟨?_, ih (prefixIndex + 1) hnext⟩
    apply (orGate_satisfied (liftAssignment clauses assignment)
      (sourceLiteral literal)
      (accumulatorLiteral clauseIndex (prefixIndex + 1) true)
      (accumulatorLiteral clauseIndex prefixIndex true)).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change
      liftAssignment clauses assignment
          (accumulatorVariable clauseIndex prefixIndex) = true ↔
        liftAssignment clauses assignment
            (sourceVariable literal.1) = literal.2 ∨
          liftAssignment clauses assignment
            (accumulatorVariable clauseIndex (prefixIndex + 1)) = true
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex prefixIndex clause hclause,
      liftAssignment_sourceVariable clauses assignment literal.1,
      liftAssignment_accumulatorVariable clauses assignment
        clauseIndex (prefixIndex + 1) clause hclause,
      hdrop, hnext]
    simp only [List.any_cons, Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Prod.exists,
        exists_eq_right']

private theorem encodeClause_complete {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex : ℕ) (clause : Clause T S)
    (hclause : clauses[clauseIndex]? = some clause)
    (hsatisfied : CL.satisfiesClause assignment clause) :
    satisfies (liftAssignment clauses assignment)
      (encodeClause clauseIndex clause) := by
  simp only [GapCVP.CL.satisfiesClause, decide_eq_true_eq] at hsatisfied
  obtain ⟨literal, hmem, hvalue⟩ := hsatisfied
  have hany :
      (sortedElements clause).any
        (fun candidate => assignment candidate.1 == candidate.2) = true := by
    apply List.any_eq_true.mpr
    refine ⟨literal, (mem_sortedElements clause literal).mpr hmem, ?_⟩
    simpa only [beq_iff_eq] using hvalue
  rw [encodeClause, satisfies_append, satisfies_append]
  refine ⟨⟨?_, gateList_complete clauses assignment clauseIndex clause
    hclause 0 (sortedElements clause) (by simp only [List.drop_zero])⟩, ?_⟩
  · apply (paddedUnary_satisfied (liftAssignment clauses assignment) _).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change liftAssignment clauses assignment
      (accumulatorVariable clauseIndex 0) = true
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex 0 clause hclause]
    simpa only [List.drop_zero, List.any_eq_true, mem_sortedElements, beq_iff_eq, Prod.exists,
        exists_eq_right'] using hany
  · apply (paddedUnary_satisfied (liftAssignment clauses assignment) _).mpr
    simp only [GapCVP.literalSatisfied, decide_eq_true_eq]
    change liftAssignment clauses assignment
      (accumulatorVariable clauseIndex (sortedElements clause).length) = false
    rw [liftAssignment_accumulatorVariable clauses assignment
      clauseIndex (sortedElements clause).length clause hclause]
    simp only [List.drop_length, List.any_nil]

private theorem encodeFormulaFrom_complete {T S : ℕ}
    (clauses : List (Clause T S))
    (assignment : Variable T S → Bool)
    (clauseIndex : ℕ) (remaining : List (Clause T S))
    (hdrop : clauses.drop clauseIndex = remaining)
    (hsatisfied : ∀ clause ∈ clauses,
      CL.satisfiesClause assignment clause) :
    satisfies (liftAssignment clauses assignment)
      (encodeFormulaFrom clauseIndex remaining) := by
  induction remaining generalizing clauseIndex with
  | nil => simp only [encodeFormulaFrom, satisfies_nil]
  | cons clause tail ih =>
    have hlookup : clauses[clauseIndex]? = some clause := by
      have hhead := congrArg List.head? hdrop
      simpa only [List.head?_drop, List.head?_cons] using hhead
    have hmem : clause ∈ clauses := by
      obtain ⟨hbound, hget⟩ :=
        List.getElem?_eq_some_iff.mp hlookup
      exact hget ▸ List.getElem_mem hbound
    have htail := drop_succ_of_drop_cons
      clauses clauseIndex clause tail hdrop
    rw [encodeFormulaFrom, satisfies_append]
    exact ⟨encodeClause_complete clauses assignment clauseIndex clause
      hlookup (hsatisfied clause hmem),
      ih (clauseIndex + 1) htail⟩

private theorem encodeFormula_complete {T S : ℕ}
    (formula : Formula T S)
    (assignment : Variable T S → Bool)
    (hsatisfied : satisfiesFormula assignment formula) :
    satisfies (liftAssignment (sortedElements formula) assignment)
      (encodeFormula formula) := by
  have hsatisfaction := hsatisfied
  simp only [GapCVP.CL.satisfiesFormula, decide_eq_true_eq] at hsatisfaction
  apply encodeFormulaFrom_complete
    (sortedElements formula) assignment 0 (sortedElements formula) (by simp only [List.drop_zero])
  intro clause hclause
  exact hsatisfaction clause ((mem_sortedElements formula clause).mp hclause)

private theorem encodeFormula_satisfiable_iff {T S : ℕ}
    (formula : Formula T S) :
    threeCNFSatisfiable (encodeFormula formula) ↔
      ∃ assignment : Variable T S → Bool,
        satisfiesFormula assignment formula := by
  rw [threeCNFSatisfiable_iff]
  constructor
  · rintro ⟨_, assignment, hsatisfied⟩
    exact ⟨restrictAssignment assignment,
      encodeFormula_sound formula assignment hsatisfied⟩
  · rintro ⟨assignment, hsatisfied⟩
    exact ⟨encodeFormula_allDistinct formula,
      liftAssignment (sortedElements formula) assignment,
      encodeFormula_complete formula assignment hsatisfied⟩

/-- GapCVP reduction support. -/
def encodeTableau {T S : ℕ} (spec : Specification T S) : ThreeCNF :=
  encodeFormula (tableauFormula spec)

private theorem encodeTableau_satisfiable_iff_validTrace {T S : ℕ}
    (spec : Specification T S) :
    threeCNFSatisfiable (encodeTableau spec) ↔
      ∃ trace : Time T → Position T → Symbol S,
        ValidTrace spec trace := by
  exact (encodeFormula_satisfiable_iff (tableauFormula spec)).trans
    (tableau_satisfiable_iff_validTrace spec)

end ThreeCNFReduction

namespace CLVerifier

open Computability GapCVP.CL

@[simp] theorem pairBitEncoding_apply
    (x certificate : List Bool) :
    pairBitEncoding (x, certificate) =
      x.map Sum.inl ++ certificate.map Sum.inr := by
  rfl

theorem pairBitEncoding_length
    (x certificate : List Bool) :
    (pairBitEncoding (x, certificate)).length =
      x.length + certificate.length := by
  simp only [pairBitEncoding_apply, List.length_append, List.length_map]

private theorem encodePosNum_length_eq_natSize (n : PosNum) :
    (Computability.encodePosNum n).length = n.natSize := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp only [encodePosNum, List.length_cons, ih, PosNum.natSize, Nat.succ_eq_add_one]
  | bit1 n ih =>
      simp only [encodePosNum, List.length_cons, ih, PosNum.natSize, Nat.succ_eq_add_one]

theorem encodeNat_length_eq_size (n : ℕ) :
    (Computability.encodeNat n).length = Nat.size n := by
  change (Computability.encodeNum (n : Num)).length = Nat.size n
  have hnum : ∀ m : Num,
      (Computability.encodeNum m).length = m.natSize := by
    intro m
    cases m with
    | zero => rfl
    | pos m => exact encodePosNum_length_eq_natSize m
  rw [hnum, Num.natSize_to_nat]
  simp only [Num.of_natCast, Nat.cast_id]

/-- GapCVP reduction support. -/
def verifierInput
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool) : List (machine.tm.Γ machine.tm.k₀) :=
  (pairBitEncoding (x, certificate)).map machine.inputAlphabet.invFun

/-- GapCVP reduction support. -/
def verifierOutput
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (value : Bool) : List (machine.tm.Γ machine.tm.k₁) :=
  (Computability.encodeBool value).map machine.outputAlphabet.invFun

@[simp] theorem verifierInput_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool) :
    (verifierInput machine x certificate).length =
      x.length + certificate.length := by
  simp only [verifierInput, Equiv.invFun_as_coe, pairBitEncoding_apply, List.map_append,
      List.map_map,
    List.length_append, List.length_map]

@[simp] theorem verifierOutput_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (value : Bool) :
    (verifierOutput machine value).length = 1 := by
  simp only [encodeBool, verifierOutput, Equiv.invFun_as_coe, List.pure_def, List.map_cons,
      List.map_nil,
      List.length_cons, List.length_nil, zero_add]

theorem verifierOutput_injective
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) :
    Function.Injective (verifierOutput machine) := by
  intro a b h
  have hs : machine.outputAlphabet.invFun a =
      machine.outputAlphabet.invFun b := by
    simpa only [encodeBool, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq, verifierOutput,
        List.pure_def,
        List.map_cons, List.map_nil, List.cons.injEq, and_true] using h
  exact machine.outputAlphabet.symm.injective hs

/-- GapCVP reduction support. -/
noncomputable def witnessTimePolynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) : Polynomial ℕ :=
  machine.time.comp (Polynomial.X + bound)

private theorem witnessTimePolynomial_bounds
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hcertificate : certificate.length ≤ bound.eval x.length) :
    machine.time.eval (pairBitEncoding (x, certificate)).length ≤
      (witnessTimePolynomial bound machine).eval x.length := by
  rw [pairBitEncoding_length]
  calc
    machine.time.eval (x.length + certificate.length) ≤
        machine.time.eval (x.length + bound.eval x.length) :=
      TMComposition.natPolynomial_eval_monotone machine.time
        (Nat.add_le_add_left hcertificate x.length)
    _ = (witnessTimePolynomial bound machine).eval x.length := by
      simp only [witnessTimePolynomial, Polynomial.eval_comp, Polynomial.eval_add,
          Polynomial.eval_X]

/-- GapCVP reduction support. -/
def boundedVerifierRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hcertificate : certificate.length ≤ bound.eval x.length) :
    Turing.TM2OutputsInTime machine.tm
      (verifierInput machine x certificate)
      (some (verifierOutput machine (verifier (x, certificate))))
      ((witnessTimePolynomial bound machine).eval x.length) := by
  have h := machine.outputsFun (x, certificate)
  change EvalsToInTime machine.tm.step
    (Turing.initList machine.tm (verifierInput machine x certificate))
    (some (Turing.haltList machine.tm
      (verifierOutput machine (verifier (x, certificate)))))
    (machine.time.eval (pairBitEncoding (x, certificate)).length) at h
  exact {
    toEvalsTo := h.toEvalsTo
    steps_le_m := h.steps_le_m.trans
      (witnessTimePolynomial_bounds bound machine x certificate hcertificate)
  }

/-- GapCVP reduction support. -/
structure ConfigurationTrace
    (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁))
    (steps : ℕ) where
  /-- GapCVP reduction support. -/
  configuration : Fin (steps + 1) → tm.Cfg
  initial : configuration 0 = Turing.initList tm input
  final : configuration (Fin.last steps) = Turing.haltList tm output
  transition : ∀ i : Fin steps,
    tm.step (configuration (Fin.castSucc i)) =
      some (configuration i.succ)

private theorem iterate_some_of_le
    (tm : Turing.FinTM2) (initial final : tm.Cfg)
    (steps : ℕ)
    (h : ((flip bind tm.step)^[steps])
      (some initial) = some final)
    {i : ℕ} (hi : i ≤ steps) :
    ∃ configuration : tm.Cfg,
      ((flip bind tm.step)^[i])
        (some initial) = some configuration := by
  let advance : Option tm.Cfg → Option tm.Cfg :=
    flip bind tm.step
  have hsplit : steps = (steps - i) + i := by omega
  cases hp : (advance^[i]) (some initial) with
  | some configuration =>
      exact ⟨configuration, rfl⟩
  | none =>
      have hfixed : (advance^[steps - i]) none = none :=
        Function.iterate_fixed (by rfl) (steps - i)
      change (advance^[steps]) (some initial) = some final at h
      rw [hsplit, Function.iterate_add_apply, hp, hfixed] at h
      cases h

private def configurationAt
    (tm : Turing.FinTM2) (initial : tm.Cfg) (i : ℕ) : tm.Cfg :=
  (((flip bind tm.step)^[i])
    (some initial)).getD initial

private def traceOfEvalsTo
    (tm : Turing.FinTM2)
    (input : List (tm.Γ tm.k₀))
    (output : List (tm.Γ tm.k₁))
    (h : StateTransition.EvalsTo tm.step
      (Turing.initList tm input) (some (Turing.haltList tm output))) :
    ConfigurationTrace tm input output h.steps := by
  let initial := Turing.initList tm input
  refine {
    configuration := fun i => configurationAt tm initial i.val
    initial := ?_
    final := ?_
    transition := ?_
  }
  · simp only [configurationAt, Option.bind_eq_bind, Turing.FinTM2.step, Fin.coe_ofNat_eq_mod,
      Nat.zero_mod,
        Function.iterate_zero, id_eq, Option.getD_some, initial]
  · simpa only [configurationAt, Option.bind_eq_bind, Turing.FinTM2.step, Fin.val_last,
      Option.getD_some] using
        congrArg (fun state : Option tm.Cfg => state.getD initial) h.evals_in_steps
  · intro i
    obtain ⟨current, hcurrent⟩ := iterate_some_of_le
      tm initial (Turing.haltList tm output) h.steps h.evals_in_steps
      (show i.val ≤ h.steps by omega)
    obtain ⟨following, hfollowing⟩ := iterate_some_of_le
      tm initial (Turing.haltList tm output) h.steps h.evals_in_steps
      (show i.val + 1 ≤ h.steps by omega)
    have hstep : tm.step current = some following := by
      rw [Function.iterate_succ_apply', hcurrent] at hfollowing
      change tm.step current = some following at hfollowing
      exact hfollowing
    change tm.step (configurationAt tm initial i.val) =
      some (configurationAt tm initial (i.val + 1))
    unfold configurationAt
    rw [hcurrent, hfollowing]
    exact hstep

theorem ConfigurationTrace.iterate_configuration
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : List (tm.Γ tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace tm input output steps)
    (i : Fin (steps + 1)) :
    ((flip bind tm.step)^[i.val]) (some (Turing.initList tm input)) =
      some (trace.configuration i) := by
  let advance : Option tm.Cfg → Option tm.Cfg :=
    flip bind tm.step
  have hprefix : ∀ (i : ℕ) (hi : i ≤ steps),
      (advance^[i]) (some (Turing.initList tm input)) =
        some (trace.configuration ⟨i, by omega⟩) := by
    intro i hi
    induction i with
    | zero =>
        simp only [Function.iterate_zero, id_eq, Fin.zero_eta, trace.initial]
    | succ i ih =>
        have hip : i ≤ steps := by omega
        have hilt : i < steps := by omega
        rw [Function.iterate_succ_apply', ih hip]
        change tm.step (trace.configuration ⟨i, by omega⟩) =
          some (trace.configuration ⟨i + 1, by omega⟩)
        exact trace.transition ⟨i, hilt⟩
  have hi : i.val ≤ steps := by omega
  simpa only [advance] using hprefix i.val hi

/-- GapCVP reduction support. -/
def ConfigurationTrace.evalsToAt
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : List (tm.Γ tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace tm input output steps)
    (i : Fin (steps + 1)) :
    StateTransition.EvalsTo tm.step (Turing.initList tm input)
      (some (trace.configuration i)) where
  steps := i.val
  evals_in_steps := trace.iterate_configuration i

/-- GapCVP reduction support. -/
def ConfigurationTrace.evalsTo
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : List (tm.Γ tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace tm input output steps) :
    StateTransition.EvalsTo tm.step (Turing.initList tm input)
      (some (Turing.haltList tm output)) := by
  exact {
    steps := steps
    evals_in_steps := by
      exact (trace.iterate_configuration (Fin.last steps)).trans
        (congrArg some trace.final)
  }

theorem ConfigurationTrace.stack_length_le
    {tm : Turing.FinTM2}
    {input : List (tm.Γ tm.k₀)}
    {output : List (tm.Γ tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace tm input output steps)
    (i : Fin (steps + 1)) (stack : tm.K) :
    ((trace.configuration i).stk stack).length ≤
      input.length + i.val * TMComposition.maxPushPerStep tm := by
  calc
    ((trace.configuration i).stk stack).length ≤
        (((Turing.initList tm input).stk stack).length +
          i.val * TMComposition.maxPushPerStep tm) :=
      TMComposition.evals_stack_length_le tm
        (Turing.initList tm input) (trace.configuration i)
        (trace.evalsToAt i) stack
    _ ≤ input.length + i.val * TMComposition.maxPushPerStep tm := by
      apply Nat.add_le_add_right
      by_cases hstack : stack = tm.k₀
      · simp only [Turing.initList, eq_mpr_eq_cast, hstack, ↓reduceDIte,
          TMComposition.cast_list_length, Std.le_refl]
      · simp only [Turing.initList, eq_mpr_eq_cast, hstack, ↓reduceDIte, List.length_nil, zero_le]

theorem haltList_step
    (tm : Turing.FinTM2) (output : List (tm.Γ tm.k₁)) :
    tm.step (Turing.haltList tm output) = none := by
  rfl

private theorem haltList_injective (tm : Turing.FinTM2) :
    Function.Injective (Turing.haltList tm) := by
  intro a b h
  have hs := congrArg (fun c : tm.Cfg => c.stk tm.k₁) h
  simpa only [Turing.haltList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq] using hs

theorem evalsTo_terminal_unique_of_steps_le
    {α : Type} (step : α → Option α) (initial a b : α)
    (ha : StateTransition.EvalsTo step initial (some a))
    (hb : StateTransition.EvalsTo step initial (some b))
    (hterminal : step a = none)
    (hle : ha.steps ≤ hb.steps) : a = b := by
  let advance : Option α → Option α := flip bind step
  let extra : ℕ := hb.steps - ha.steps
  have hsplit : hb.steps = extra + ha.steps := by
    dsimp [extra]
    omega
  have ha_run : (advance^[ha.steps]) (some initial) = some a := by
    simpa only [advance] using ha.evals_in_steps
  have hb_run : (advance^[hb.steps]) (some initial) = some b := by
    simpa only [advance] using hb.evals_in_steps
  have hrun : (advance^[extra]) (some a) = some b := by
    calc
      (advance^[extra]) (some a) =
          (advance^[extra])
            ((advance^[ha.steps]) (some initial)) := by
              rw [ha_run]
      _ = (advance^[extra + ha.steps]) (some initial) :=
        (Function.iterate_add_apply advance extra ha.steps
          (some initial)).symm
      _ = some b := by
        rw [← hsplit]
        exact hb_run
  cases he : extra with
  | zero =>
      rw [he] at hrun
      exact Option.some.inj (by simpa only [Option.some.injEq, Function.iterate_zero, id_eq]
          using hrun)
  | succ n =>
      have hnone : (advance^[extra]) (some a) = none := by
        rw [he, Function.iterate_succ_apply]
        change (advance^[n]) ((some a).bind step) = none
        rw [Option.bind_some, hterminal]
        exact Function.iterate_fixed (by rfl) n
      rw [hnone] at hrun
      cases hrun

private theorem evalsTo_haltList_unique
    (tm : Turing.FinTM2) (initial : tm.Cfg)
    (a b : List (tm.Γ tm.k₁))
    (ha : StateTransition.EvalsTo tm.step initial
      (some (Turing.haltList tm a)))
    (hb : StateTransition.EvalsTo tm.step initial
      (some (Turing.haltList tm b))) : a = b := by
  apply haltList_injective tm
  rcases le_total ha.steps hb.steps with hle | hle
  · exact evalsTo_terminal_unique_of_steps_le tm.step initial
      (Turing.haltList tm a) (Turing.haltList tm b)
      ha hb (haltList_step tm a) hle
  · exact (evalsTo_terminal_unique_of_steps_le tm.step initial
      (Turing.haltList tm b) (Turing.haltList tm a)
      hb ha (haltList_step tm b) hle).symm

/-- GapCVP reduction support. -/
structure AcceptedExecution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) where
  /-- GapCVP reduction support. -/
  certificate : List Bool
  certificate_le : certificate.length ≤ bound.eval x.length
  /-- GapCVP reduction support. -/
  steps : ℕ
  steps_le : steps ≤ (witnessTimePolynomial bound machine).eval x.length
  /-- GapCVP reduction support. -/
  trace : ConfigurationTrace machine.tm
    (verifierInput machine x certificate)
    (verifierOutput machine true) steps

private theorem acceptedExecution_iff
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    Nonempty (AcceptedExecution bound machine x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by
  constructor
  · rintro ⟨execution⟩
    refine ⟨execution.certificate, execution.certificate_le, ?_⟩
    have htrace := execution.trace.evalsTo
    have hactual := (machine.outputsFun
      (x, execution.certificate)).toEvalsTo
    change StateTransition.EvalsTo machine.tm.step
      (Turing.initList machine.tm
        (verifierInput machine x execution.certificate))
      (some (Turing.haltList machine.tm
        (verifierOutput machine
          (verifier (x, execution.certificate))))) at hactual
    have hout := evalsTo_haltList_unique machine.tm
      (Turing.initList machine.tm
        (verifierInput machine x execution.certificate))
      (verifierOutput machine true)
      (verifierOutput machine (verifier (x, execution.certificate)))
      htrace hactual
    exact (verifierOutput_injective machine hout).symm
  · rintro ⟨certificate, hcertificate, haccept⟩
    have hrun := boundedVerifierRun bound machine x certificate hcertificate
    change EvalsToInTime machine.tm.step
      (Turing.initList machine.tm (verifierInput machine x certificate))
      (some (Turing.haltList machine.tm
        (verifierOutput machine (verifier (x, certificate)))))
      ((witnessTimePolynomial bound machine).eval x.length) at hrun
    rw [haccept] at hrun
    exact ⟨{
      certificate := certificate
      certificate_le := hcertificate
      steps := hrun.steps
      steps_le := hrun.steps_le_m
      trace := traceOfEvalsTo machine.tm
        (verifierInput machine x certificate)
        (verifierOutput machine true) hrun.toEvalsTo
    }⟩

/-- GapCVP reduction support. -/
structure TableauSimulation
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) where
  /-- GapCVP reduction support. -/
  time : Polynomial ℕ
  /-- GapCVP reduction support. -/
  symbols : ℕ
  /-- GapCVP reduction support. -/
  specification : (x : List Bool) →
    Specification (time.eval x.length) symbols
  correct : ∀ x : List Bool,
    (∃ trace : Time (time.eval x.length) →
        Position (time.eval x.length) → Symbol symbols,
      ValidTrace (specification x) trace) ↔
      Nonempty (AcceptedExecution bound machine x)

/-- GapCVP reduction support. -/
noncomputable def encodedTableau
    {bound : Polynomial ℕ}
    {verifier : List Bool × List Bool → Bool}
    {machine : VerifierTM verifier}
    (simulation : TableauSimulation bound machine)
    (x : List Bool) : List Bool :=
  (binaryFinEncoding ThreeCNF).encode
    (ThreeCNFReduction.encodeTableau (simulation.specification x))

theorem threeSATLanguage_encode_iff (formula : ThreeCNF) :
    threeSATLanguage ((binaryFinEncoding ThreeCNF).encode formula) ↔
      threeCNFSatisfiable formula := by
  simp only [GapCVP.threeSATLanguage, decide_eq_true_eq]
  constructor
  · rintro ⟨candidate, hencoding, hsatisfied⟩
    have heq : candidate = formula :=
      (binaryFinEncoding ThreeCNF).encode_injective hencoding
    simpa only [heq] using hsatisfied
  · intro hsatisfied
    exact ⟨formula, rfl, hsatisfied⟩

private theorem encodedTableau_mem_threeSAT_iff
    {bound : Polynomial ℕ}
    {verifier : List Bool × List Bool → Bool}
    {machine : VerifierTM verifier}
    (simulation : TableauSimulation bound machine)
    (x : List Bool) :
    threeSATLanguage (encodedTableau simulation x) ↔
      Nonempty (AcceptedExecution bound machine x) := by
  unfold encodedTableau
  exact
    (threeSATLanguage_encode_iff
      (ThreeCNFReduction.encodeTableau (simulation.specification x))).trans
      ((ThreeCNFReduction.encodeTableau_satisfiable_iff_validTrace
        (simulation.specification x)).trans (simulation.correct x))

end CLVerifier

namespace CLNondeterminism

open Computability GapCVP.CLVerifier

/-- GapCVP reduction support. -/
inductive FiniteRun {α : Type} (transition : α → α → Type) :
    α → α → ℕ → Type where
  | refl (state : α) : FiniteRun transition state state 0
  | tail {first middle last : α} {steps : ℕ} :
      FiniteRun transition first middle steps →
      transition middle last →
      FiniteRun transition first last (steps + 1)

namespace FiniteRun

/-- GapCVP reduction support. -/
noncomputable def single {α : Type} {transition : α → α → Type}
    {first last : α} (h : transition first last) :
    FiniteRun transition first last 1 :=
  .tail (.refl first) h

/-- GapCVP reduction support. -/
noncomputable def trans {α : Type} {transition : α → α → Type}
    {first middle last : α} {leftSteps rightSteps : ℕ}
    (left : FiniteRun transition first middle leftSteps)
    (right : FiniteRun transition middle last rightSteps) :
    FiniteRun transition first last (leftSteps + rightSteps) := by
  induction right with
  | refl => simpa only [add_zero] using left
  | tail prior hstep ih =>
      simpa only [Nat.add_assoc] using FiniteRun.tail ih hstep

end FiniteRun

/-- GapCVP reduction support. -/
inductive GuessState (tm : Turing.FinTM2) where
  | guessing (certificate : List Bool)
  | verifying (certificate : List Bool) (configuration : tm.Cfg)

/-- GapCVP reduction support. -/
inductive GuessStep
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    GuessState machine.tm → GuessState machine.tm → Type where
  | guess (certificate : List Bool) (bit : Bool)
      (hbound : certificate.length < bound.eval x.length) :
      GuessStep bound machine x
        (.guessing certificate)
        (.guessing (certificate ++ [bit]))
  | begin (certificate : List Bool)
      (hbound : certificate.length ≤ bound.eval x.length) :
      GuessStep bound machine x
        (.guessing certificate)
        (.verifying certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate)))
  | execute (certificate : List Bool)
      (configuration next : machine.tm.Cfg)
      (hstep : machine.tm.step configuration = some next) :
      GuessStep bound machine x
        (.verifying certificate configuration)
        (.verifying certificate next)

/-- GapCVP reduction support. -/
def oneStepEvalsTo
    (tm : Turing.FinTM2)
    (configuration next : tm.Cfg)
    (hstep : tm.step configuration = some next) :
    StateTransition.EvalsTo tm.step configuration (some next) where
  steps := 1
  evals_in_steps := by
    change tm.step configuration = some next
    exact hstep

private noncomputable def GuessInvariant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) : GuessState machine.tm → Bool
  | .guessing certificate =>
    @decide (
      certificate.length ≤ bound.eval x.length
    ) (Classical.propDecidable _)
  | .verifying certificate configuration =>
    @decide (
      certificate.length ≤ bound.eval x.length ∧
        Nonempty (StateTransition.EvalsTo machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          (some configuration))
    ) (Classical.propDecidable _)
private theorem guessInvariant_step
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    {first next : GuessState machine.tm}
    (hfirst : GuessInvariant bound machine x first)
    (hstep : GuessStep bound machine x first next) :
    GuessInvariant bound machine x next := by
  cases hstep with
  | guess certificate bit hbound =>
      simp only [GuessInvariant, decide_eq_true_eq] at hfirst ⊢
      simp only [List.length_append, List.length_singleton]
      omega
  | begin certificate hbound =>
      simp only [GuessInvariant, decide_eq_true_eq] at hfirst ⊢
      exact ⟨hbound,
        ⟨StateTransition.EvalsTo.refl machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))⟩⟩
  | execute certificate configuration next hstep =>
      simp only [GuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨hbound, ⟨hrun⟩⟩
      exact ⟨hbound,
        ⟨StateTransition.EvalsTo.trans machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          configuration (some next) hrun
          (oneStepEvalsTo machine.tm configuration next hstep)⟩⟩

private theorem guessInvariant_run
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    {first last : GuessState machine.tm}
    {steps : ℕ}
    (run : FiniteRun (GuessStep bound machine x) first last steps)
    (hfirst : GuessInvariant bound machine x first) :
    GuessInvariant bound machine x last := by
  induction run with
  | refl => exact hfirst
  | tail prior hstep ih =>
      exact guessInvariant_step bound machine x ih hstep

private noncomputable def TimedGuessInvariant
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) (elapsed : ℕ) : GuessState machine.tm → Bool
  | .guessing certificate =>
    @decide (
      certificate.length ≤ bound.eval x.length ∧
        certificate.length ≤ elapsed
    ) (Classical.propDecidable _)
  | .verifying certificate configuration =>
    @decide (
      certificate.length ≤ bound.eval x.length ∧
        ∃ run : StateTransition.EvalsTo machine.tm.step
          (Turing.initList machine.tm
            (verifierInput machine x certificate))
          (some configuration),
          run.steps + certificate.length + 1 ≤ elapsed
    ) (Classical.propDecidable _)
private theorem timedGuessInvariant_step
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) {elapsed : ℕ}
    {first next : GuessState machine.tm}
    (hfirst : TimedGuessInvariant bound machine x elapsed first)
    (hstep : GuessStep bound machine x first next) :
    TimedGuessInvariant bound machine x (elapsed + 1) next := by
  cases hstep with
  | guess certificate bit hbound =>
      simp only [TimedGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨_, helapsed⟩
      simp only [List.length_append, List.length_singleton]
      constructor <;> omega
  | begin certificate hbound =>
      simp only [TimedGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨_, helapsed⟩
      refine ⟨hbound, StateTransition.EvalsTo.refl machine.tm.step
        (Turing.initList machine.tm
          (verifierInput machine x certificate)), ?_⟩
      change 0 + certificate.length + 1 ≤ elapsed + 1
      omega
  | execute certificate configuration next hstep =>
      simp only [TimedGuessInvariant, decide_eq_true_eq] at hfirst ⊢
      rcases hfirst with ⟨hbound, run, hruntime⟩
      let nextRun := StateTransition.EvalsTo.trans machine.tm.step
        (Turing.initList machine.tm
          (verifierInput machine x certificate))
        configuration (some next) run
        (oneStepEvalsTo machine.tm configuration next hstep)
      refine ⟨hbound, nextRun, ?_⟩
      change 1 + run.steps + certificate.length + 1 ≤ elapsed + 1
      omega

private theorem timedGuessInvariant_run
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    {state : GuessState machine.tm} {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing []) state elapsed) :
    TimedGuessInvariant bound machine x elapsed state := by
  have hinitial : TimedGuessInvariant bound machine x 0
      (.guessing []) := by
    simp only [TimedGuessInvariant, decide_eq_true_eq]
    exact ⟨Nat.zero_le _, le_refl 0⟩
  induction run with
  | refl => exact hinitial
  | tail prior hstep ih =>
      exact timedGuessInvariant_step bound machine x ih hstep

private noncomputable def guessingRunFrom
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool)
    (start suffix : List Bool)
    (hbound : (start ++ suffix).length ≤ bound.eval x.length) :
    FiniteRun (GuessStep bound machine x)
      (.guessing start) (.guessing (start ++ suffix)) suffix.length := by
  induction suffix generalizing start with
  | nil =>
      simpa only [List.append_nil, List.length_nil] using
          FiniteRun.refl (GuessState.guessing (tm := machine.tm) start)
  | cons bit rest ih =>
      have hfirst : start.length < bound.eval x.length := by
        simp only [List.length_append, List.length_cons] at hbound
        omega
      have hrest : ((start ++ [bit]) ++ rest).length ≤
          bound.eval x.length := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append, List.length_append,
            List.length_cons] using
            hbound
      have hguess : FiniteRun (GuessStep bound machine x)
          (.guessing start) (.guessing (start ++ [bit])) 1 :=
        FiniteRun.single
          (GuessStep.guess start bit hfirst)
      have hremaining := ih (start ++ [bit]) hrest
      simpa only [List.length_cons, List.append_assoc, List.cons_append, List.nil_append,
          Nat.add_comm] using
          hguess.trans hremaining

private noncomputable def guessingRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (hbound : certificate.length ≤ bound.eval x.length) :
    FiniteRun (GuessStep bound machine x)
      (.guessing []) (.guessing certificate) certificate.length := by
  simpa only [List.nil_append] using guessingRunFrom bound machine x [] certificate hbound

private noncomputable def configurationTraceRun
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {output : List (machine.tm.Γ machine.tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace machine.tm
      (verifierInput machine x certificate) output steps) :
    FiniteRun (GuessStep bound machine x)
      (.verifying certificate
        (Turing.initList machine.tm
          (verifierInput machine x certificate)))
      (.verifying certificate
        (Turing.haltList machine.tm output)) steps := by
  have hprefix : ∀ (i : ℕ) (hi : i ≤ steps),
      FiniteRun (GuessStep bound machine x)
        (.verifying certificate
          (Turing.initList machine.tm
            (verifierInput machine x certificate)))
        (.verifying certificate
          (trace.configuration ⟨i, by omega⟩)) i := by
    intro i hi
    induction i with
    | zero =>
        simpa only [Fin.zero_eta, trace.initial] using
            FiniteRun.refl (GuessState.verifying certificate (Turing.initList machine.tm
                (verifierInput machine x certificate)))
    | succ i ih =>
        have hip : i ≤ steps := by omega
        have hilt : i < steps := by omega
        have hrun := ih hip
        have hstep := GuessStep.execute
          (bound := bound) (machine := machine) (x := x)
          certificate
          (trace.configuration ⟨i, by omega⟩)
          (trace.configuration ⟨i + 1, by omega⟩)
          (trace.transition ⟨i, hilt⟩)
        exact FiniteRun.tail hrun hstep
  have hlast : trace.configuration ⟨steps, by omega⟩ =
      Turing.haltList machine.tm output := trace.final
  rw [← hlast]
  exact hprefix steps (le_refl steps)

/-- GapCVP reduction support. -/
noncomputable def guessTimePolynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) : Polynomial ℕ :=
  bound + 1 + witnessTimePolynomial bound machine

/-- GapCVP reduction support. -/
noncomputable def nondeterministicTableauDimensionPolynomial
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) : Polynomial ℕ :=
  Polynomial.X + bound +
    guessTimePolynomial bound machine *
      Polynomial.C (TMComposition.maxPushPerStep machine.tm) +
    guessTimePolynomial bound machine + 1

theorem verifying_stack_length_le
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    (configuration : machine.tm.Cfg)
    {elapsed : ℕ}
    (run : FiniteRun (GuessStep bound machine x)
      (.guessing []) (.verifying certificate configuration) elapsed)
    (hruntime : elapsed ≤ (guessTimePolynomial bound machine).eval x.length)
    (stack : machine.tm.K) :
    (configuration.stk stack).length ≤
      (nondeterministicTableauDimensionPolynomial bound machine).eval
        x.length := by
  have hinvariant := timedGuessInvariant_run bound machine x run
  simp only [TimedGuessInvariant, decide_eq_true_eq] at hinvariant
  obtain ⟨hcertificate, hmachine, hsteps⟩ := hinvariant
  have hmachineSteps : hmachine.steps ≤ elapsed := by omega
  have hinput :
      (((Turing.initList machine.tm
        (verifierInput machine x certificate)).stk stack).length) ≤
        x.length + bound.eval x.length := by
    calc
      (((Turing.initList machine.tm
          (verifierInput machine x certificate)).stk stack).length) ≤
        (verifierInput machine x certificate).length := by
          by_cases hstack : stack = machine.tm.k₀
          · simp only [Turing.initList, eq_mpr_eq_cast, hstack, ↓reduceDIte,
              TMComposition.cast_list_length,
                verifierInput_length, Std.le_refl]
          · simp only [Turing.initList, eq_mpr_eq_cast, hstack, ↓reduceDIte, List.length_nil,
              verifierInput_length,
                zero_le]
      _ = x.length + certificate.length :=
        verifierInput_length machine x certificate
      _ ≤ x.length + bound.eval x.length :=
        Nat.add_le_add_left hcertificate x.length
  have hstack := TMComposition.evals_stack_length_le machine.tm
    (Turing.initList machine.tm (verifierInput machine x certificate))
    configuration hmachine stack
  have htime : hmachine.steps ≤
      (guessTimePolynomial bound machine).eval x.length :=
    hmachineSteps.trans hruntime
  calc
    (configuration.stk stack).length ≤
      (((Turing.initList machine.tm
        (verifierInput machine x certificate)).stk stack).length) +
        hmachine.steps * TMComposition.maxPushPerStep machine.tm :=
      hstack
    _ ≤ (x.length + bound.eval x.length) +
        (guessTimePolynomial bound machine).eval x.length *
          TMComposition.maxPushPerStep machine.tm :=
      Nat.add_le_add hinput
        (Nat.mul_le_mul_right
          (TMComposition.maxPushPerStep machine.tm) htime)
    _ ≤ (nondeterministicTableauDimensionPolynomial bound machine).eval
        x.length := by
      simp only [nondeterministicTableauDimensionPolynomial,
        Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C, Polynomial.eval_one]
      omega

/-- GapCVP reduction support. -/
structure GuessingExecution
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) where
  /-- GapCVP reduction support. -/
  certificate : List Bool
  /-- GapCVP reduction support. -/
  steps : ℕ
  steps_le : steps ≤ (guessTimePolynomial bound machine).eval x.length
  /-- GapCVP reduction support. -/
  run : FiniteRun (GuessStep bound machine x)
    (.guessing [])
    (.verifying certificate
      (Turing.haltList machine.tm (verifierOutput machine true)))
    steps

private noncomputable def guessingExecutionOfAccepted
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x) :
    GuessingExecution bound machine x := by
  have hguess := guessingRun bound machine x execution.certificate
    execution.certificate_le
  have hbegin : FiniteRun (GuessStep bound machine x)
      (.guessing execution.certificate)
      (.verifying execution.certificate
        (Turing.initList machine.tm
          (verifierInput machine x execution.certificate))) 1 :=
    FiniteRun.single
      (GuessStep.begin execution.certificate execution.certificate_le)
  have hverify := configurationTraceRun bound machine x
    execution.certificate execution.trace
  refine {
    certificate := execution.certificate
    steps := (execution.certificate.length + 1) + execution.steps
    steps_le := ?_
    run := (hguess.trans hbegin).trans hverify
  }
  have hcertificate := execution.certificate_le
  have hsteps := execution.steps_le
  simp only [guessTimePolynomial, Polynomial.eval_add,
    Polynomial.eval_one]
  omega

theorem guessingExecution_accepted
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : GuessingExecution bound machine x) :
    Nonempty (AcceptedExecution bound machine x) := by
  have hinitial : GuessInvariant bound machine x (.guessing []) := by
    simp only [GuessInvariant, decide_eq_true_eq]
    change 0 ≤ bound.eval x.length
    exact Nat.zero_le _
  have hfinal := guessInvariant_run bound machine x
    execution.run hinitial
  simp only [GuessInvariant, decide_eq_true_eq] at hfinal
  rcases hfinal with ⟨hcertificate, ⟨hrun⟩⟩
  have hactual := (machine.outputsFun
    (x, execution.certificate)).toEvalsTo
  change StateTransition.EvalsTo machine.tm.step
    (Turing.initList machine.tm
      (verifierInput machine x execution.certificate))
    (some (Turing.haltList machine.tm
      (verifierOutput machine
        (verifier (x, execution.certificate))))) at hactual
  have houtput := evalsTo_haltList_unique machine.tm
    (Turing.initList machine.tm
      (verifierInput machine x execution.certificate))
    (verifierOutput machine true)
    (verifierOutput machine (verifier (x, execution.certificate)))
    hrun hactual
  apply (acceptedExecution_iff bound machine x).mpr
  exact ⟨execution.certificate, hcertificate,
    (verifierOutput_injective machine houtput).symm⟩

/-- GapCVP reduction support. -/
structure LocalTableauCompiler
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier) where
  /-- GapCVP reduction support. -/
  symbols : ℕ
  /-- GapCVP reduction support. -/
  specification : (x : List Bool) →
    CL.Specification
      ((nondeterministicTableauDimensionPolynomial bound machine).eval
        x.length) symbols
  encode : ∀ (x : List Bool),
    GuessingExecution bound machine x →
      ∃ trace :
        CL.Time
          ((nondeterministicTableauDimensionPolynomial bound machine).eval
            x.length) →
        CL.Position
          ((nondeterministicTableauDimensionPolynomial bound machine).eval
            x.length) →
        CL.Symbol symbols,
        CL.ValidTrace (specification x) trace
  /-- GapCVP reduction support. -/
  decode : ∀ (x : List Bool)
    (trace :
      CL.Time
        ((nondeterministicTableauDimensionPolynomial bound machine).eval
          x.length) →
      CL.Position
        ((nondeterministicTableauDimensionPolynomial bound machine).eval
          x.length) →
      CL.Symbol symbols),
    CL.ValidTrace (specification x) trace →
      GuessingExecution bound machine x

/-- GapCVP reduction support. -/
noncomputable def tableauSimulationOfLocalCompiler
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (compiler : LocalTableauCompiler bound machine) :
    CLVerifier.TableauSimulation bound machine where
  time := nondeterministicTableauDimensionPolynomial bound machine
  symbols := compiler.symbols
  specification := compiler.specification
  correct x := by
    constructor
    · rintro ⟨trace, htrace⟩
      exact guessingExecution_accepted bound machine
        (compiler.decode x trace htrace)
    · rintro ⟨execution⟩
      exact compiler.encode x
        (guessingExecutionOfAccepted bound machine execution)

theorem compiledTableau_iff_verifier
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (compiler : LocalTableauCompiler bound machine)
    (x : List Bool) :
    threeSATLanguage
      (encodedTableau
        (tableauSimulationOfLocalCompiler bound machine compiler) x) ↔
      ∃ certificate : List Bool,
        certificate.length ≤ bound.eval x.length ∧
          verifier (x, certificate) = true := by
  exact (encodedTableau_mem_threeSAT_iff
    (tableauSimulationOfLocalCompiler bound machine compiler) x).trans
    (acceptedExecution_iff bound machine x)

end CLNondeterminism

namespace CLBoundedStates

open Computability GapCVP.CLVerifier GapCVP.CLNondeterminism

private def statementPushSlots
    {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ next => statementPushSlots next + 1
  | .peek _ _ next => statementPushSlots next
  | .pop _ _ next => statementPushSlots next
  | .load _ next => statementPushSlots next
  | .branch _ yes no =>
      statementPushSlots yes + statementPushSlots no
  | .goto _ => 0
  | .halt => 0

private abbrev PushSlot (tm : Turing.FinTM2) :=
  Σ label : tm.Λ, Fin (statementPushSlots (tm.m label))

noncomputable instance instFintypePushSlot
    (tm : Turing.FinTM2) : Fintype (PushSlot tm) := by
  letI : Fintype tm.Λ := tm.ΛFin
  infer_instance

/-- GapCVP reduction support. -/
abbrev PushTag (tm : Turing.FinTM2) := PushSlot tm × tm.σ

noncomputable instance instFintypePushTag
    (tm : Turing.FinTM2) : Fintype (PushTag tm) := by
  letI : Fintype tm.σ := tm.σFin
  infer_instance

/-- GapCVP reduction support. -/
abbrev CellAtom (tm : Turing.FinTM2) :=
  Option ((Bool ⊕ Bool) ⊕ PushTag tm)

noncomputable instance instFintypeCellAtom
    (tm : Turing.FinTM2) : Fintype (CellAtom tm) := by
  infer_instance

/-- GapCVP reduction support. -/
inductive PhaseTag where
  | guessing
  | verifying
  | accepting
  deriving DecidableEq

noncomputable instance : Fintype PhaseTag where
  elems := {.guessing, .verifying, .accepting}
  complete tag := by cases tag <;> simp

/-- GapCVP reduction support. -/
abbrev LocalCellSymbol (tm : Turing.FinTM2) :=
  PhaseTag × Option (tm.Λ × tm.σ) ×
    (tm.K → CellAtom tm) × Bool

noncomputable instance instFintypeLocalCellSymbol
    (tm : Turing.FinTM2) : Fintype (LocalCellSymbol tm) := by
  letI : Fintype tm.K := tm.kFin
  letI : Fintype tm.Λ := tm.ΛFin
  letI : Fintype tm.σ := tm.σFin
  infer_instance

end CLBoundedStates

namespace CLPushAlphabet

open Computability GapCVP.CLVerifier GapCVP.CLBoundedStates

private abbrev PushSource (tm : Turing.FinTM2) :=
  Σ stack : tm.K, tm.σ → tm.Γ stack

private def statementPushSources
    {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → List (Σ stack : K, σ → Γ stack)
  | .push stack value next =>
      ⟨stack, value⟩ :: statementPushSources next
  | .peek _ _ next => statementPushSources next
  | .pop _ _ next => statementPushSources next
  | .load _ next => statementPushSources next
  | .branch _ yes no =>
      statementPushSources yes ++ statementPushSources no
  | .goto _ => []
  | .halt => []

@[simp] private theorem statementPushSources_length
    {K : Type} {Γ : K → Type} {Λ σ : Type}
    (statement : Turing.TM2.Stmt Γ Λ σ) :
    (statementPushSources statement).length =
      statementPushSlots statement := by
  induction statement with
  | push stack value next ih =>
      simp only [statementPushSources, List.length_cons, ih, statementPushSlots]
  | peek stack value next ih =>
      simpa only [statementPushSources, statementPushSlots] using ih
  | pop stack value next ih =>
      simpa only [statementPushSources, statementPushSlots] using ih
  | load value next ih =>
      simpa only [statementPushSources, statementPushSlots] using ih
  | branch test yes no ihyes ihno =>
      simp only [statementPushSources, List.length_append, ihyes, ihno, statementPushSlots]
  | goto value => rfl
  | halt => rfl

private def pushSourceOfSlot (tm : Turing.FinTM2)
    (slot : PushSlot tm) : PushSource tm :=
  (statementPushSources (tm.m slot.1)).get
    ⟨slot.2.val, by
      rw [statementPushSources_length]
      exact slot.2.isLt⟩

/-- GapCVP reduction support. -/
def cellAtomValue
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K) :
    CellAtom machine.tm → Option (machine.tm.Γ stack)
  | none => none
  | some (.inl bit) =>
      if h : stack = machine.tm.k₀ then
        some (h.symm ▸ machine.inputAlphabet.invFun bit)
      else none
  | some (.inr (slot, state)) =>
      if h : (pushSourceOfSlot machine.tm slot).1 = stack then
        some (h ▸ (pushSourceOfSlot machine.tm slot).2 state)
      else none

@[simp] theorem cellAtomValue_blank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K) :
    cellAtomValue machine stack none = none := rfl

@[simp] theorem cellAtomValue_input
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (bit : Bool ⊕ Bool) :
    cellAtomValue machine machine.tm.k₀
      (some (.inl bit)) = some (machine.inputAlphabet.invFun bit) := by
  simp only [cellAtomValue, ↓reduceDIte, Equiv.invFun_as_coe]

@[simp] private theorem cellAtomValue_pushed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (slot : PushSlot machine.tm) (state : machine.tm.σ) :
    cellAtomValue machine
      (pushSourceOfSlot machine.tm slot).1
      (some (.inr (slot, state))) =
      some ((pushSourceOfSlot machine.tm slot).2 state) := by
  simp only [cellAtomValue, ↓reduceDIte]

/-- GapCVP reduction support. -/
noncomputable def StackAtomSupported
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (configuration : machine.tm.Cfg) : Bool :=
  @decide (
  ∀ (stack : machine.tm.K) (value : machine.tm.Γ stack),
    value ∈ configuration.stk stack →
      ∃ atom : CellAtom machine.tm,
        cellAtomValue machine stack atom = some value
  ) (Classical.propDecidable _)
theorem initialConfiguration_stackAtomSupported
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool) :
    StackAtomSupported machine
      (Turing.initList machine.tm
        (verifierInput machine x certificate)) := by
  simp only [GapCVP.CLPushAlphabet.StackAtomSupported, decide_eq_true_eq] at *
  intro stack value hvalue
  by_cases hstack : stack = machine.tm.k₀
  · subst stack
    have hinput : value ∈ verifierInput machine x certificate := by
      simpa only [Turing.initList, eq_mpr_eq_cast, ↓reduceDIte, cast_eq] using hvalue
    obtain ⟨bit, _, hbit⟩ := List.mem_map.mp hinput
    subst value
    exact ⟨some (.inl bit), cellAtomValue_input machine bit⟩
  · simp only [Turing.initList, eq_mpr_eq_cast, hstack, ↓reduceDIte, List.not_mem_nil] at hvalue

end CLPushAlphabet

namespace CLStackSupport

open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet

private theorem pushSourceOfSlot_exists
    (tm : Turing.FinTM2) (label : tm.Λ)
    (source : PushSource tm)
    (hsource : source ∈ statementPushSources (tm.m label)) :
    ∃ slot : PushSlot tm,
      slot.1 = label ∧ pushSourceOfSlot tm slot = source := by
  obtain ⟨index, hindex⟩ := List.get_of_mem hsource
  have hindexBound : index.val < statementPushSlots (tm.m label) := by
    simpa only [← statementPushSources_length] using index.isLt
  let slot : PushSlot tm := ⟨label, ⟨index.val, hindexBound⟩⟩
  refine ⟨slot, rfl, ?_⟩
  exact hindex

private theorem pushedValue_has_cellAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (label : machine.tm.Λ)
    (stack : machine.tm.K)
    (value : machine.tm.σ → machine.tm.Γ stack)
    (state : machine.tm.σ)
    (hsource : (⟨stack, value⟩ : PushSource machine.tm) ∈
      statementPushSources (machine.tm.m label)) :
    ∃ atom : CellAtom machine.tm,
      cellAtomValue machine stack atom = some (value state) := by
  obtain ⟨slot, _, hslot⟩ :=
    pushSourceOfSlot_exists machine.tm label ⟨stack, value⟩ hsource
  have hsigma :
      (⟨(pushSourceOfSlot machine.tm slot).1,
        (pushSourceOfSlot machine.tm slot).2⟩ : PushSource machine.tm) =
      ⟨stack, value⟩ := by
    exact hslot
  obtain ⟨hstack, hvalue⟩ := Sigma.mk.inj_iff.mp hsigma
  subst stack
  have hfunction : (pushSourceOfSlot machine.tm slot).2 = value :=
    eq_of_heq hvalue
  refine ⟨some (.inr (slot, state)), ?_⟩
  simpa only [hfunction] using
    cellAtomValue_pushed machine slot state

private noncomputable def StacksAtomSupported
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (values : ∀ stack : machine.tm.K, List (machine.tm.Γ stack)) : Bool :=
  @decide (
  ∀ (stack : machine.tm.K) (value : machine.tm.Γ stack),
    value ∈ values stack →
      ∃ atom : CellAtom machine.tm,
        cellAtomValue machine stack atom = some value
  ) (Classical.propDecidable _)
private theorem stacksAtomSupported_push
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (values : ∀ stack : machine.tm.K, List (machine.tm.Γ stack))
    (hvalues : StacksAtomSupported machine values)
    (stack : machine.tm.K) (value : machine.tm.Γ stack)
    (hatom : ∃ atom : CellAtom machine.tm,
      cellAtomValue machine stack atom = some value) :
    StacksAtomSupported machine
      (Function.update values stack (value :: values stack)) := by
  simp only [GapCVP.CLStackSupport.StacksAtomSupported, decide_eq_true_eq] at *
  intro target candidate hcandidate
  by_cases htarget : target = stack
  · subst target
    have hmem : candidate = value ∨ candidate ∈ values stack := by
      simpa only [Function.update_self, List.mem_cons] using hcandidate
    rcases hmem with rfl | hold
    · exact hatom
    · exact hvalues stack candidate hold
  · have hold : candidate ∈ values target := by
      simpa only [Function.update, htarget, ↓reduceDIte] using hcandidate
    exact hvalues target candidate hold

private theorem stacksAtomSupported_pop
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (values : ∀ stack : machine.tm.K, List (machine.tm.Γ stack))
    (hvalues : StacksAtomSupported machine values)
    (stack : machine.tm.K) :
    StacksAtomSupported machine
      (Function.update values stack (values stack).tail) := by
  simp only [GapCVP.CLStackSupport.StacksAtomSupported, decide_eq_true_eq] at *
  intro target candidate hcandidate
  by_cases htarget : target = stack
  · subst target
    have htail : candidate ∈ (values stack).tail := by
      simpa only [Function.update_self] using hcandidate
    exact hvalues stack candidate (List.mem_of_mem_tail htail)
  · have hold : candidate ∈ values target := by
      simpa only [Function.update, htarget, ↓reduceDIte] using hcandidate
    exact hvalues target candidate hold

private theorem stacksAtomSupported_stepAux
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (label : machine.tm.Λ)
    (statement : Turing.TM2.Stmt machine.tm.Γ
      machine.tm.Λ machine.tm.σ)
    (state : machine.tm.σ)
    (values : ∀ stack : machine.tm.K,
      List (machine.tm.Γ stack))
    (hincluded : ∀ source ∈ statementPushSources statement,
      source ∈ statementPushSources (machine.tm.m label))
    (hvalues : StacksAtomSupported machine values) :
    StacksAtomSupported machine
      (Turing.TM2.stepAux statement state values).stk := by
  induction statement generalizing state values with
  | push stack value next ih =>
      have hpush : (⟨stack, value⟩ : PushSource machine.tm) ∈
          statementPushSources (machine.tm.m label) := by
        apply hincluded
        simp only [statementPushSources, List.mem_cons, true_or]
      have hatom := pushedValue_has_cellAtom
        machine label stack value state hpush
      have hnext : ∀ source ∈ statementPushSources next,
          source ∈ statementPushSources (machine.tm.m label) := by
        intro source hsource
        apply hincluded
        simp only [statementPushSources, List.mem_cons, hsource, or_true]
      have hupdated := stacksAtomSupported_push
        machine values hvalues stack (value state) hatom
      simpa only [Turing.TM2.stepAux] using
          ih state (Function.update values stack (value state :: values stack)) hnext hupdated
  | peek stack update next ih =>
      have hnext : ∀ source ∈ statementPushSources next,
          source ∈ statementPushSources (machine.tm.m label) := by
        intro source hsource
        exact hincluded source hsource
      simpa only [Turing.TM2.stepAux] using ih (update state (values stack).head?) values hnext
          hvalues
  | pop stack update next ih =>
      have hnext : ∀ source ∈ statementPushSources next,
          source ∈ statementPushSources (machine.tm.m label) := by
        intro source hsource
        exact hincluded source hsource
      have hupdated := stacksAtomSupported_pop
        machine values hvalues stack
      simpa only [Turing.TM2.stepAux] using
          ih (update state (values stack).head?) (Function.update values stack (values stack).tail)
              hnext hupdated
  | load update next ih =>
      have hnext : ∀ source ∈ statementPushSources next,
          source ∈ statementPushSources (machine.tm.m label) := by
        intro source hsource
        exact hincluded source hsource
      simpa only [Turing.TM2.stepAux] using ih (update state) values hnext hvalues
  | branch test yes no ihyes ihno =>
      cases htest : test state with
      | false =>
          have hno : ∀ source ∈ statementPushSources no,
              source ∈ statementPushSources (machine.tm.m label) := by
            intro source hsource
            apply hincluded
            simp only [statementPushSources, List.mem_append, hsource, or_true]
          simpa only [Turing.TM2.stepAux, htest, Bool.cond_false] using ihno state values hno
              hvalues
      | true =>
          have hyes : ∀ source ∈ statementPushSources yes,
              source ∈ statementPushSources (machine.tm.m label) := by
            intro source hsource
            apply hincluded
            simp only [statementPushSources, List.mem_append, hsource, true_or]
          simpa only [Turing.TM2.stepAux, htest, Bool.cond_true] using ihyes state values hyes
              hvalues
  | goto update =>
      simpa only [Turing.TM2.stepAux] using hvalues
  | halt =>
      simpa only [Turing.TM2.stepAux] using hvalues

private theorem step_stackAtomSupported
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (configuration next : machine.tm.Cfg)
    (hstep : machine.tm.step configuration = some next)
    (hsupported : StackAtomSupported machine configuration) :
    StackAtomSupported machine next := by
  rcases configuration with ⟨label, state, values⟩
  cases label with
  | none =>
      simp only [Turing.FinTM2.step, Turing.TM2.step, reduceCtorEq] at hstep
  | some label =>
      have heq :
          Turing.TM2.stepAux (machine.tm.m label) state values =
            next := by
        have hsome :
            some (Turing.TM2.stepAux
              (machine.tm.m label) state values) = some next := by
          exact hstep
        exact Option.some.inj hsome
      subst next
      change StacksAtomSupported machine
        (Turing.TM2.stepAux (machine.tm.m label) state values).stk
      apply stacksAtomSupported_stepAux machine label
        (machine.tm.m label) state values
      · intro source hsource
        exact hsource
      · exact hsupported

end CLStackSupport

namespace CLCellRows

open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet

/-- GapCVP reduction support. -/
def paddedAtom {tm : Turing.FinTM2}
    (atoms : List (CellAtom tm)) (index : ℕ) : CellAtom tm :=
  (atoms[index]?).getD none

theorem paddedAtom_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    {atoms : List (CellAtom machine.tm)}
    {values : List (machine.tm.Γ stack)}
    (h : List.Forall₂
      (fun atom value =>
        cellAtomValue machine stack atom = some value)
      atoms values)
    (index : ℕ) :
    cellAtomValue machine stack (paddedAtom atoms index) = values[index]? := by
  induction h generalizing index with
  | nil =>
      simp only [cellAtomValue, paddedAtom, List.length_nil, not_lt_zero, not_false_eq_true,
          getElem?_neg,
          Option.getD_none]
  | @cons atom value atoms values hatom htail ih =>
      cases index with
      | zero => simpa only [paddedAtom, List.length_cons, lt_add_iff_pos_left,
          Order.lt_add_one_iff, zero_le, getElem?_pos,
                    List.getElem_cons_zero, Option.getD_some] using hatom
      | succ index => simpa only [paddedAtom, List.getElem?_cons_succ] using ih index

/-- GapCVP reduction support. -/
def certificatePhase (certificate : List Bool) (index : ℕ) : PhaseTag :=
  if h : index < certificate.length then
    if certificate.get ⟨index, h⟩ then
      .verifying
    else
      .guessing
  else if index = certificate.length then
    .accepting
  else
    .guessing

@[simp] private theorem certificatePhase_end (certificate : List Bool) :
    certificatePhase certificate certificate.length = .accepting := by
  simp only [certificatePhase, lt_self_iff_false, ↓reduceDIte, ↓reduceIte]

theorem certificatePhase_accepting_iff
    (certificate : List Bool) (index : ℕ) :
    certificatePhase certificate index = .accepting ↔
      index = certificate.length := by
  by_cases hindex : index < certificate.length
  · have hne : index ≠ certificate.length := Nat.ne_of_lt hindex
    cases hbit : certificate[index] <;>
      simp [certificatePhase, hindex, hbit, hne]
  · simp only [certificatePhase, hindex, ↓reduceDIte, ite_eq_left_iff, reduceCtorEq, imp_false,
      Decidable.not_not]

private theorem certificatePhase_bit
    (certificate : List Bool) (index : ℕ)
    (hindex : index < certificate.length) :
    certificatePhase certificate index =
      if certificate.get ⟨index, hindex⟩ then
        PhaseTag.verifying
      else
        PhaseTag.guessing := by
  simp only [certificatePhase, hindex, ↓reduceDIte, List.get_eq_getElem]

private abbrev CellRow (tm : Turing.FinTM2) (width : ℕ) :=
  Fin (width + 1) → LocalCellSymbol tm

/-- GapCVP reduction support. -/
def guessingRow (tm : Turing.FinTM2) (width : ℕ)
    (certificate : List Bool) : CellRow tm width :=
  fun index =>
    (certificatePhase certificate index.val,
      none,
      fun _ => none,
      false)

/-- GapCVP reduction support. -/
def configurationControl (tm : Turing.FinTM2)
    (configuration : tm.Cfg) : tm.Λ × tm.σ :=
  (configuration.l.getD tm.main, configuration.var)

end CLCellRows

namespace CLCellRowBounds

open Computability GapCVP.CLNondeterminism

/-- GapCVP reduction support. -/
abbrev rowWidth
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) : ℕ :=
  (nondeterministicTableauDimensionPolynomial bound machine).eval x.length

theorem certificateBound_le_rowWidth
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x : List Bool) :
    bound.eval x.length ≤ rowWidth bound machine x := by
  simp only [rowWidth, nondeterministicTableauDimensionPolynomial,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  omega

end CLCellRowBounds

namespace CLLocalWindows

open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows

/-- GapCVP reduction support. -/
def statementStackActions
    {K : Type} {Γ : K → Type} {Λ σ : Type} :
    Turing.TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ next => statementStackActions next + 1
  | .peek _ _ next => statementStackActions next
  | .pop _ _ next => statementStackActions next + 1
  | .load _ next => statementStackActions next
  | .branch _ yes no =>
      max (statementStackActions yes) (statementStackActions no)
  | .goto _ => 0
  | .halt => 0

private def maxStackEditsPerStep (tm : Turing.FinTM2) : ℕ := by
  classical
  letI : Fintype tm.Λ := tm.ΛFin
  exact Finset.univ.sup fun label =>
    statementStackActions (tm.m label)

private theorem statementStackActions_le_max
    (tm : Turing.FinTM2) (label : tm.Λ) :
    statementStackActions (tm.m label) ≤ maxStackEditsPerStep tm := by
  classical
  let : Fintype tm.Λ := tm.ΛFin
  change statementStackActions (tm.m label) ≤
    (Finset.univ : Finset tm.Λ).sup
      (fun candidate => statementStackActions (tm.m candidate))
  exact Finset.le_sup
    (f := fun candidate : tm.Λ =>
      statementStackActions (tm.m candidate))
    (Finset.mem_univ label)

/-- GapCVP reduction support. -/
def blockSize (tm : Turing.FinTM2) : ℕ :=
  maxStackEditsPerStep tm + 1

theorem blockSize_pos (tm : Turing.FinTM2) : 0 < blockSize tm := by
  simp only [blockSize, lt_add_iff_pos_left, Order.lt_add_one_iff, zero_le]

private theorem statementStackActions_lt_blockSize
    (tm : Turing.FinTM2) (label : tm.Λ) :
    statementStackActions (tm.m label) < blockSize tm := by
  have hbound := statementStackActions_le_max tm label
  simp only [blockSize]
  omega

/-- GapCVP reduction support. -/
abbrev BlockCell (tm : Turing.FinTM2) :=
  Fin (blockSize tm) → LocalCellSymbol tm

instance instFintypeBlockCell (tm : Turing.FinTM2) :
    Fintype (BlockCell tm) := by
  infer_instance

/-- GapCVP reduction support. -/
def blankCell (tm : Turing.FinTM2) : LocalCellSymbol tm :=
  (.guessing, none, fun _ => none, false)

private abbrev BlockRow (tm : Turing.FinTM2) (width : ℕ) :=
  Fin (width + 1) → BlockCell tm

/-- GapCVP reduction support. -/
def packRow (tm : Turing.FinTM2) (width : ℕ)
    (row : CellRow tm width) : BlockRow tm width :=
  fun block offset =>
    if h : block.val * blockSize tm + offset.val < width + 1 then
      row ⟨block.val * blockSize tm + offset.val, h⟩
    else
      blankCell tm

/-- GapCVP reduction support. -/
def coordinateBlock (tm : Turing.FinTM2) (width : ℕ)
    (index : Fin (width + 1)) : Fin (width + 1) :=
  ⟨index.val / blockSize tm,
    Nat.lt_of_le_of_lt
      (Nat.div_le_self index.val (blockSize tm)) index.isLt⟩

/-- GapCVP reduction support. -/
def coordinateOffset (tm : Turing.FinTM2) (width : ℕ)
    (index : Fin (width + 1)) : Fin (blockSize tm) :=
  ⟨index.val % blockSize tm,
    Nat.mod_lt index.val (blockSize_pos tm)⟩

theorem packRow_cell
    (tm : Turing.FinTM2) (width : ℕ)
    (row : CellRow tm width) (index : Fin (width + 1)) :
    packRow tm width row
      (coordinateBlock tm width index)
      (coordinateOffset tm width index) = row index := by
  have hcoordinate :
      index.val / blockSize tm * blockSize tm +
        index.val % blockSize tm = index.val :=
    Nat.div_add_mod' index.val (blockSize tm)
  have hbound :
      index.val / blockSize tm * blockSize tm +
        index.val % blockSize tm < width + 1 := by
    omega
  have hbound' :
      (coordinateBlock tm width index).val * blockSize tm +
        (coordinateOffset tm width index).val < width + 1 := by
    simpa only [coordinateBlock, coordinateOffset] using hbound
  simp only [packRow]
  rw [dite_eq_left hbound']
  apply congrArg row
  apply Fin.ext
  simpa only [coordinateBlock, coordinateOffset] using hcoordinate

/-- GapCVP reduction support. -/
def leftBlock (width : ℕ)
    (index : Fin (width + 1)) : Fin (width + 1) :=
  ⟨index.val - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) index.isLt⟩

/-- GapCVP reduction support. -/
def rightBlock (width : ℕ)
    (index : Fin (width + 1)) : Fin (width + 1) :=
  ⟨min (index.val + 1) width,
    Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩

@[simp] theorem leftBlock_zero (width : ℕ) :
    leftBlock width (0 : Fin (width + 1)) = 0 := by
  apply Fin.ext
  rfl

end CLLocalWindows

namespace CLLocalRules

open Computability GapCVP.CLLocalWindows

/-- GapCVP reduction support. -/
abbrev SummaryBlockCell (tm : Turing.FinTM2) :=
  BlockCell tm × BlockCell tm

instance instFintypeSummaryBlockCell (tm : Turing.FinTM2) :
    Fintype (SummaryBlockCell tm) := by
  infer_instance

end CLLocalRules

namespace CLTableauStitching

open Computability GapCVP.CLLocalWindows

theorem leftBlock_succ (width : ℕ) (index : Fin width) :
    leftBlock width index.succ = index.castSucc := by
  apply Fin.ext
  simp only [leftBlock, Fin.val_succ, add_tsub_cancel_right, Fin.val_castSucc]

end CLTableauStitching

namespace CLExactLocalRules

open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows

/-- GapCVP reduction support. -/
abbrev GuessPhaseWindow := PhaseTag × PhaseTag × PhaseTag × PhaseTag

/-- GapCVP reduction support. -/
noncomputable def GuessPhaseAllowed (window : GuessPhaseWindow) : Bool :=
  @decide (
  (window.2.1 = .accepting ∧
    window.2.2.1 = .guessing ∧
      (window.2.2.2 = .guessing ∨
       window.2.2.2 = .verifying)) ∨
  (window.2.1 ≠ .accepting ∧
    window.1 = .accepting ∧
    window.2.2.2 = .accepting) ∨
  (window.2.1 ≠ .accepting ∧
    window.1 ≠ .accepting ∧
    window.2.2.2 = window.2.1)
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def guessPhaseWindowAt (width : ℕ)
    (first next : List Bool)
    (index : Fin (width + 1)) : GuessPhaseWindow :=
  (certificatePhase first (leftBlock width index).val,
    certificatePhase first index.val,
    certificatePhase first (rightBlock width index).val,
    certificatePhase next index.val)

theorem certificatePhase_append_before
    (certificate : List Bool) (bit : Bool) (index : ℕ)
    (hindex : index < certificate.length) :
    certificatePhase (certificate ++ [bit]) index =
      certificatePhase certificate index := by
  have happend : index < (certificate ++ [bit]).length := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [certificatePhase_bit (certificate ++ [bit]) index happend,
    certificatePhase_bit certificate index hindex]
  simp only [List.get_eq_getElem, List.getElem_append_left hindex]

theorem certificatePhase_append_old_marker
    (certificate : List Bool) (bit : Bool) :
    certificatePhase (certificate ++ [bit]) certificate.length =
      if bit then PhaseTag.verifying else PhaseTag.guessing := by
  cases bit <;>
    simp [certificatePhase]

theorem certificatePhase_append_new_marker
    (certificate : List Bool) (bit : Bool) :
    certificatePhase (certificate ++ [bit])
      (certificate.length + 1) = .accepting := by
  have hlength : (certificate ++ [bit]).length =
      certificate.length + 1 := by simp only [List.length_append, List.length_cons,
          List.length_nil,
                                     zero_add]
  rw [← hlength]
  exact certificatePhase_end (certificate ++ [bit])

theorem certificatePhase_after
    (certificate : List Bool) (index : ℕ)
    (hindex : certificate.length < index) :
    certificatePhase certificate index = .guessing := by
  have hnot : ¬ index < certificate.length := by omega
  have hne : index ≠ certificate.length := by omega
  simp only [certificatePhase, hnot, ↓reduceDIte, hne, ↓reduceIte]

theorem certificatePhase_append_after
    (certificate : List Bool) (bit : Bool) (index : ℕ)
    (hindex : certificate.length + 1 < index) :
    certificatePhase (certificate ++ [bit]) index =
      certificatePhase certificate index := by
  have hfirst : certificate.length < index := by omega
  have hnext : (certificate ++ [bit]).length < index := by
    simp only [List.length_append, List.length_singleton]
    omega
  rw [certificatePhase_after (certificate ++ [bit]) index hnext,
    certificatePhase_after certificate index hfirst]

theorem guessPhaseWindow_of_append
    (width : ℕ) (certificate : List Bool) (bit : Bool)
    (hspace : certificate.length < width)
    (index : Fin (width + 1)) :
    GuessPhaseAllowed
      (guessPhaseWindowAt width certificate
        (certificate ++ [bit]) index) := by
  simp only [GapCVP.CLExactLocalRules.GuessPhaseAllowed, decide_eq_true_eq] at *
  by_cases hmarker : index.val = certificate.length
  · have hright :
        (rightBlock width index).val = certificate.length + 1 := by
      change min (index.val + 1) width = certificate.length + 1
      rw [Nat.min_eq_left (by omega)]
      omega
    refine Or.inl ⟨?_, ?_, ?_⟩
    · change certificatePhase certificate index.val = .accepting
      rw [hmarker]
      exact certificatePhase_end certificate
    · change
        certificatePhase certificate
          (rightBlock width index).val = .guessing
      rw [hright]
      exact certificatePhase_after certificate
        (certificate.length + 1) (by omega)
    · change
        certificatePhase (certificate ++ [bit]) index.val = .guessing ∨
          certificatePhase (certificate ++ [bit]) index.val = .verifying
      rw [hmarker, certificatePhase_append_old_marker]
      cases bit <;> simp
  · by_cases hsuccessor : index.val = certificate.length + 1
    · have hleft :
          (leftBlock width index).val = certificate.length := by
        change index.val - 1 = certificate.length
        omega
      refine Or.inr (Or.inl ⟨?_, ?_, ?_⟩)
      · change certificatePhase certificate index.val ≠ .accepting
        intro haccept
        exact hmarker
          ((certificatePhase_accepting_iff
            certificate index.val).mp haccept)
      · change
          certificatePhase certificate
            (leftBlock width index).val = .accepting
        rw [hleft]
        exact certificatePhase_end certificate
      · change
          certificatePhase (certificate ++ [bit]) index.val = .accepting
        rw [hsuccessor]
        exact certificatePhase_append_new_marker certificate bit
    · have hleftNe :
          (leftBlock width index).val ≠ certificate.length := by
        change index.val - 1 ≠ certificate.length
        intro heq
        omega
      refine Or.inr (Or.inr ⟨?_, ?_, ?_⟩)
      · change certificatePhase certificate index.val ≠ .accepting
        intro haccept
        exact hmarker
          ((certificatePhase_accepting_iff
            certificate index.val).mp haccept)
      · change
          certificatePhase certificate
            (leftBlock width index).val ≠ .accepting
        intro haccept
        exact hleftNe
          ((certificatePhase_accepting_iff certificate
            (leftBlock width index).val).mp haccept)
      · change
          certificatePhase (certificate ++ [bit]) index.val =
            certificatePhase certificate index.val
        by_cases hbefore : index.val < certificate.length
        · exact certificatePhase_append_before
            certificate bit index.val hbefore
        · have hafter : certificate.length + 1 < index.val := by
            omega
          exact certificatePhase_append_after
            certificate bit index.val hafter

end CLExactLocalRules

namespace CLExactStackRules

open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet

/-- GapCVP reduction support. -/
noncomputable def SupportedStackValue
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (value : machine.tm.Γ stack) : Bool :=
  @decide (
  ∃ atom : CellAtom machine.tm,
    cellAtomValue machine stack atom = some value
  ) (Classical.propDecidable _)

theorem stackAtomSupported_supportedValues
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (configuration : machine.tm.Cfg)
    (supported : StackAtomSupported machine configuration)
    (stack : machine.tm.K) :
    ∀ value ∈ configuration.stk stack,
      SupportedStackValue machine stack value := by
  have raw := supported
  simp only [StackAtomSupported, decide_eq_true_eq] at raw
  intro value membership
  simpa only [SupportedStackValue, decide_eq_true_eq] using
    raw stack value membership

/-- GapCVP reduction support. -/
def canonicalCellAtom
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (value : machine.tm.Γ stack)
    (hsupported : SupportedStackValue machine stack value) :
    CellAtom machine.tm :=
  Classical.choose
    (by simpa only [SupportedStackValue, decide_eq_true_eq] using hsupported)

theorem canonicalCellAtom_decode
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (value : machine.tm.Γ stack)
    (hsupported : SupportedStackValue machine stack value) :
    cellAtomValue machine stack
      (canonicalCellAtom machine stack value hsupported) =
      some value := by
  unfold canonicalCellAtom
  exact Classical.choose_spec
    (by simpa only [SupportedStackValue, decide_eq_true_eq] using hsupported)

/-- GapCVP reduction support. -/
def canonicalStackAtoms
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value) :
    List (CellAtom machine.tm) :=
  List.pmap (canonicalCellAtom machine stack) values hsupported

theorem canonicalStackAtoms_length
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value) :
    (canonicalStackAtoms machine stack values hsupported).length =
      values.length := by
  simp only [canonicalStackAtoms, List.length_pmap]

theorem canonicalStackAtoms_forall₂
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value) :
    List.Forall₂
      (fun atom value =>
        cellAtomValue machine stack atom = some value)
      (canonicalStackAtoms machine stack values hsupported)
      values := by
  induction values with
  | nil =>
      exact .nil
  | cons value values ih =>
      have hhead : SupportedStackValue machine stack value :=
        hsupported value (by simp only [List.mem_cons, true_or])
      have htail : ∀ candidate ∈ values,
          SupportedStackValue machine stack candidate := by
        intro candidate hcandidate
        exact hsupported candidate (by simp only [List.mem_cons, hcandidate, or_true])
      change List.Forall₂
        (fun atom candidate =>
          cellAtomValue machine stack atom = some candidate)
        (canonicalCellAtom machine stack value hhead ::
          canonicalStackAtoms machine stack values htail)
        (value :: values)
      exact .cons
        (canonicalCellAtom_decode machine stack value hhead)
        (ih htail)

private theorem supportedStackValue_of_mem_drop
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value)
    (count : ℕ) :
    ∀ value ∈ values.drop count,
      SupportedStackValue machine stack value := by
  intro value hvalue
  exact hsupported value (List.mem_of_mem_drop hvalue)

private theorem canonicalStackAtoms_drop
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value)
    (count : ℕ) :
    (canonicalStackAtoms machine stack values hsupported).drop count =
      canonicalStackAtoms machine stack (values.drop count)
        (supportedStackValue_of_mem_drop
          machine stack values hsupported count) := by
  induction count generalizing values with
  | zero =>
      simp only [List.drop_zero]
  | succ count ih =>
      cases values with
      | nil =>
          simp only [canonicalStackAtoms, List.pmap_nil, List.drop_nil]
      | cons value values =>
          have htail : ∀ candidate ∈ values,
              SupportedStackValue machine stack candidate := by
            intro candidate hcandidate
            exact hsupported candidate (by simp only [List.mem_cons, hcandidate, or_true])
          simpa only [canonicalStackAtoms, List.pmap, List.drop_succ_cons] using ih values htail

private theorem canonicalStackAtoms_congr
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (first next : List (machine.tm.Γ stack))
    (hfirst : ∀ value ∈ first,
      SupportedStackValue machine stack value)
    (hnext : ∀ value ∈ next,
      SupportedStackValue machine stack value)
    (heq : first = next) :
    canonicalStackAtoms machine stack first hfirst =
      canonicalStackAtoms machine stack next hnext := by
  subst next
  rfl

private theorem canonicalStackAtoms_common_suffix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (first next : List (machine.tm.Γ stack))
    (hfirst : ∀ value ∈ first,
      SupportedStackValue machine stack value)
    (hnext : ∀ value ∈ next,
      SupportedStackValue machine stack value)
    (firstDrop nextDrop : ℕ)
    (hcommon : first.drop firstDrop = next.drop nextDrop) :
    (canonicalStackAtoms machine stack first hfirst).drop firstDrop =
      (canonicalStackAtoms machine stack next hnext).drop nextDrop := by
  rw [canonicalStackAtoms_drop, canonicalStackAtoms_drop]
  exact canonicalStackAtoms_congr machine stack
    (first.drop firstDrop) (next.drop nextDrop)
    (supportedStackValue_of_mem_drop
      machine stack first hfirst firstDrop)
    (supportedStackValue_of_mem_drop
      machine stack next hnext nextDrop)
    hcommon

end CLExactStackRules

namespace CLExactVerifierRules

open Computability GapCVP.CLLocalWindows

/-- GapCVP reduction support. -/
noncomputable def StackPrefixAgreement
    {K : Type} {Γ : K → Type}
    (radius : ℕ)
    (first next : ∀ stack : K, List (Γ stack)) : Bool :=
  @decide (
  ∀ stack : K,
    (first stack).take radius = (next stack).take radius
  ) (Classical.propDecidable _)
theorem stackPrefixAgreement_mono
    {K : Type} {Γ : K → Type}
    {small large : ℕ}
    {first next : ∀ stack : K, List (Γ stack)}
    (hbound : small ≤ large)
    (hagreement : StackPrefixAgreement large first next) :
    StackPrefixAgreement small first next := by
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq] at *
  intro stack
  have h := congrArg (List.take small) (hagreement stack)
  simpa only [List.take_take, Nat.min_eq_left hbound] using h

private theorem stackPrefixAgreement_head
    {K : Type} {Γ : K → Type}
    {radius : ℕ}
    {first next : ∀ stack : K, List (Γ stack)}
    (hpositive : 0 < radius)
    (hagreement : StackPrefixAgreement radius first next)
    (stack : K) :
    (first stack).head? = (next stack).head? := by
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq] at *
  have h := congrArg List.head? (hagreement stack)
  have hnonzero : radius ≠ 0 := by omega
  simpa only [List.head?_take, hnonzero, ↓reduceIte] using h

private theorem stackPrefixAgreement_push
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (radius : ℕ)
    (first next : ∀ stack : K, List (Γ stack))
    (stack : K) (value : Γ stack)
    (hagreement : StackPrefixAgreement radius first next) :
    StackPrefixAgreement radius
      (Function.update first stack (value :: first stack))
      (Function.update next stack (value :: next stack)) := by
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq]
  have hraw := hagreement
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq] at hraw
  intro target
  by_cases htarget : target = stack
  · subst target
    cases radius with
    | zero => simp only [Function.update_self, List.take_zero]
    | succ radius =>
        have hsmaller :
            StackPrefixAgreement radius first next :=
          stackPrefixAgreement_mono (by omega) hagreement
        have hsmaller' := hsmaller
        simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq]
            at hsmaller'
        simpa only [Function.update_self, List.take_succ_cons, List.cons.injEq, true_and]
            using hsmaller' stack
  · simpa only [Function.update, htarget, ↓reduceDIte] using hraw target

private theorem stackPrefixAgreement_pop
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (radius : ℕ)
    (first next : ∀ stack : K, List (Γ stack))
    (stack : K)
    (hagreement : StackPrefixAgreement (radius + 1) first next) :
    StackPrefixAgreement radius
      (Function.update first stack (first stack).tail)
      (Function.update next stack (next stack).tail) := by
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq]
  have hraw := hagreement
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq] at hraw
  intro target
  by_cases htarget : target = stack
  · subst target
    have h := congrArg List.tail (hraw stack)
    simpa only [Function.update_self, List.tail_take_eq_take_tail, add_tsub_cancel_right] using h
  · have hsmaller : StackPrefixAgreement radius first next :=
      stackPrefixAgreement_mono (by omega) hagreement
    have hsmaller' := hsmaller
    simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq] at hsmaller'
    simpa only [Function.update, htarget, ↓reduceDIte] using hsmaller' target

theorem statementLookahead_le_blockSize
    (tm : Turing.FinTM2) (label : tm.Λ) :
    statementStackActions (tm.m label) + 1 ≤ blockSize tm := by
  have h := statementStackActions_le_max tm label
  simp only [blockSize]
  omega

end CLExactVerifierRules

namespace CLCompleteLocalCompiler

open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows

private theorem paddedAtom_common_suffix
    (tm : Turing.FinTM2)
    (first next : List (CellAtom tm))
    (firstDrop nextDrop index : ℕ)
    (hcommon : first.drop firstDrop = next.drop nextDrop)
    (hindex : nextDrop ≤ index) :
    paddedAtom next index =
      paddedAtom first (index - nextDrop + firstDrop) := by
  have h := congrArg
    (fun values : List (CellAtom tm) =>
      values[index - nextDrop]?) hcommon
  simp only [List.getElem?_drop] at h
  have hleft : nextDrop + (index - nextDrop) = index := by
    omega
  have hright :
      firstDrop + (index - nextDrop) =
        index - nextDrop + firstDrop := by omega
  rw [hright, hleft] at h
  exact congrArg
    (fun value : Option (CellAtom tm) => value.getD none)
    h.symm

/-- GapCVP reduction support. -/
abbrev AtomBlock (tm : Turing.FinTM2) :=
  Fin (blockSize tm) → CellAtom tm

instance instFintypeAtomBlock (tm : Turing.FinTM2) :
    Fintype (AtomBlock tm) := by
  infer_instance

/-- GapCVP reduction support. -/
abbrev SingleStackHint (tm : Turing.FinTM2) :=
  Fin (blockSize tm) × Fin (blockSize tm) × AtomBlock tm

instance instFintypeSingleStackHint (tm : Turing.FinTM2) :
    Fintype (SingleStackHint tm) := by
  infer_instance

/-- GapCVP reduction support. -/
def atomBlockAt (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm)) (index : ℕ) : AtomBlock tm :=
  fun offset =>
    paddedAtom atoms (index * blockSize tm + offset.val)

/-- GapCVP reduction support. -/
abbrev StackShiftWindow (tm : Turing.FinTM2) :=
  AtomBlock tm × AtomBlock tm × AtomBlock tm × AtomBlock tm × Bool

/-- GapCVP reduction support. -/
def stackShiftWindowAt (tm : Turing.FinTM2) (width : ℕ)
    (first next : List (CellAtom tm))
    (index : Fin (width + 1)) : StackShiftWindow tm :=
  (atomBlockAt tm first (leftBlock width index).val,
    atomBlockAt tm first index.val,
    atomBlockAt tm first (rightBlock width index).val,
    atomBlockAt tm next index.val,
    decide (index.val = 0))

/-- GapCVP reduction support. -/
def shiftedWindowAtom (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (window : StackShiftWindow tm)
    (offset : Fin (blockSize tm)) : CellAtom tm :=
  if window.2.2.2.2 = true ∧ offset.val < hint.2.1.val then
    hint.2.2 offset
  else if hleft : offset.val + hint.1.val < hint.2.1.val then
    window.1
      ⟨blockSize tm + (offset.val + hint.1.val) - hint.2.1.val,
        by
          have hnext := hint.2.1.isLt
          omega⟩
  else
    let shifted := offset.val + hint.1.val - hint.2.1.val
    if hcenter : shifted < blockSize tm then
      window.2.1 ⟨shifted, hcenter⟩
    else
      window.2.2.1
        ⟨shifted - blockSize tm, by
          have hoffset := offset.isLt
          have hdrop := hint.1.isLt
          omega⟩

/-- GapCVP reduction support. -/
noncomputable def StackShiftAllowed (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (window : StackShiftWindow tm) : Bool :=
  @decide (
  ∀ offset : Fin (blockSize tm),
    window.2.2.2.1 offset = shiftedWindowAtom tm hint window offset
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def stackShiftAllowed (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (window : StackShiftWindow tm) : Bool := by
  classical
  exact decide (StackShiftAllowed tm hint window)

theorem stackShiftAllowed_iff (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (window : StackShiftWindow tm) :
    stackShiftAllowed tm hint window = true ↔
      StackShiftAllowed tm hint window := by
  classical
  simp only [stackShiftAllowed, Bool.decide_eq_true]

end CLCompleteLocalCompiler

namespace CLStackShiftSoundness2

open Computability GapCVP.CLBoundedStates GapCVP.CLPushAlphabet GapCVP.CLCellRows
open GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler

/-- GapCVP reduction support. -/
noncomputable def NoBlankAtoms (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm)) : Bool :=
  @decide (
  ∀ atom ∈ atoms, atom ≠ none
  ) (Classical.propDecidable _)
private theorem canonicalCellAtom_ne_blank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (value : machine.tm.Γ stack)
    (hsupported : SupportedStackValue machine stack value) :
    canonicalCellAtom machine stack value hsupported ≠ none := by
  intro hblank
  have hdecode :=
    canonicalCellAtom_decode machine stack value hsupported
  rw [hblank, cellAtomValue_blank] at hdecode
  cases hdecode

private theorem canonicalStackAtoms_no_blank
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value) :
    NoBlankAtoms machine.tm
      (canonicalStackAtoms machine stack values hsupported) := by
  simp only [GapCVP.CLStackShiftSoundness2.NoBlankAtoms, decide_eq_true_eq]
  intro atom hmem
  change atom ∈
    List.pmap (canonicalCellAtom machine stack)
      values hsupported at hmem
  obtain ⟨value, hvalue, heq⟩ := List.mem_pmap.mp hmem
  subst atom
  exact canonicalCellAtom_ne_blank
    machine stack value (hsupported value hvalue)

private theorem paddedAtom_eq_iff_getElem
    (tm : Turing.FinTM2)
    (first next : List (CellAtom tm))
    (hfirst : NoBlankAtoms tm first)
    (hnext : NoBlankAtoms tm next)
    (firstIndex nextIndex : ℕ) :
    paddedAtom first firstIndex = paddedAtom next nextIndex ↔
      first[firstIndex]? = next[nextIndex]? := by
  simp only [GapCVP.CLStackShiftSoundness2.NoBlankAtoms, decide_eq_true_eq] at *
  constructor
  · intro heq
    cases hfirstEntry : first[firstIndex]? with
    | none =>
        cases hnextEntry : next[nextIndex]? with
        | none => rfl
        | some atom =>
            have hmem := List.mem_of_getElem? hnextEntry
            have hnonblank := hnext atom hmem
            have hblank : none = atom := by
              simpa only [paddedAtom, hfirstEntry, Option.getD_none, hnextEntry, Option.getD_some]
                  using heq
            exact False.elim (hnonblank hblank.symm)
    | some atom =>
        cases hnextEntry : next[nextIndex]? with
        | none =>
            have hmem := List.mem_of_getElem? hfirstEntry
            have hnonblank := hfirst atom hmem
            have hblank : atom = none := by
              simpa only [paddedAtom, hfirstEntry, Option.getD_some, hnextEntry, Option.getD_none]
                  using heq
            exact False.elim (hnonblank hblank)
        | some candidate =>
            have hvalue : atom = candidate := by
              simpa only [paddedAtom, hfirstEntry, Option.getD_some, hnextEntry] using heq
            simp only [hvalue]
  · intro heq
    exact congrArg
      (fun value : Option (CellAtom tm) => value.getD none)
      heq

theorem atomSuffix_iff_paddedShift
    (tm : Turing.FinTM2)
    (first next : List (CellAtom tm))
    (hfirst : NoBlankAtoms tm first)
    (hnext : NoBlankAtoms tm next)
    (firstDrop nextDrop : ℕ) :
    first.drop firstDrop = next.drop nextDrop ↔
      ∀ index : ℕ,
        paddedAtom first (firstDrop + index) =
          paddedAtom next (nextDrop + index) := by
  constructor
  · intro hcommon index
    have h := paddedAtom_common_suffix tm first next
      firstDrop nextDrop (nextDrop + index)
      hcommon (by omega)
    have harith :
        nextDrop + index - nextDrop + firstDrop =
          firstDrop + index := by omega
    simpa only [add_tsub_cancel_left, Nat.add_comm] using h.symm
  · intro hshift
    apply List.ext_getElem?
    intro index
    simp only [List.getElem?_drop]
    exact (paddedAtom_eq_iff_getElem tm first next
      hfirst hnext (firstDrop + index)
      (nextDrop + index)).mp (hshift index)

end CLStackShiftSoundness2

namespace CLFiniteShiftWindows

open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows
open GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler

theorem paddedAtom_none_of_length_le
    (tm : Turing.FinTM2)
    (atoms : List (CellAtom tm))
    (index : ℕ)
    (hindex : atoms.length ≤ index) :
    paddedAtom atoms index = none := by
  simp only [paddedAtom, List.getElem?_eq_none hindex, Option.getD_none]

/-- GapCVP reduction support. -/
noncomputable def AllStackShiftWindows (tm : Turing.FinTM2) (width : ℕ)
    (hint : SingleStackHint tm)
    (first next : List (CellAtom tm)) : Bool :=
  @decide (
  ∀ index : Fin (width + 1),
    stackShiftAllowed tm hint
      (stackShiftWindowAt tm width first next index) = true
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
noncomputable def PrefixHintCorrect (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (next : List (CellAtom tm)) : Bool :=
  @decide (
  ∀ offset : Fin (blockSize tm),
    offset.val < hint.2.1.val →
      hint.2.2 offset = paddedAtom next offset.val
  ) (Classical.propDecidable _)
theorem width_le_block_capacity
    (tm : Turing.FinTM2) (width : ℕ) :
    width ≤ width * blockSize tm := by
  have h := Nat.mul_le_mul_left width (blockSize_pos tm)
  simpa only [ge_iff_le, Nat.succ_eq_add_one, zero_add, mul_one] using h

theorem shiftedWindowAtom_eq_old
    (tm : Turing.FinTM2) (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirstLength : first.length ≤ width)
    (hint : SingleStackHint tm)
    (index : Fin (width + 1))
    (offset : Fin (blockSize tm))
    (hnotPrefix : ¬
      (index.val = 0 ∧ offset.val < hint.2.1.val)) :
    shiftedWindowAtom tm hint
      (stackShiftWindowAt tm width first next index)
      offset =
      paddedAtom first
        (index.val * blockSize tm + offset.val -
          hint.2.1.val + hint.1.val) := by
  have hguard : ¬
      ((stackShiftWindowAt tm width first next index).2.2.2.2 = true ∧
        offset.val < hint.2.1.val) := by
    simpa only [stackShiftWindowAt, Fin.val_eq_zero_iff, decide_eq_true_eq, Fin.val_fin_lt,
        not_and, not_lt] using
        hnotPrefix
  have hglobal :
      hint.2.1.val ≤
        index.val * blockSize tm + offset.val := by
    by_cases hzero : index.val = 0
    · have hoffset : hint.2.1.val ≤ offset.val := by
        by_contra hsmall
        exact hnotPrefix ⟨hzero, by omega⟩
      simp only [hzero, zero_mul, zero_add, hoffset]
    · have hpositive : 1 ≤ index.val := by omega
      have hcapacity :=
        Nat.mul_le_mul_right (blockSize tm) hpositive
      have hdrop := hint.2.1.isLt
      simp only [Nat.one_mul] at hcapacity
      omega
  simp only [shiftedWindowAtom, hguard, ↓reduceIte]
  by_cases hleft : offset.val + hint.1.val < hint.2.1.val
  · simp only [dite_eq_left hleft, stackShiftWindowAt, atomBlockAt]
    have hnonzero : index.val ≠ 0 := by
      intro hzero
      exact hnotPrefix ⟨hzero, by omega⟩
    have hindex : 0 < index.val := by omega
    have hmul :
        (index.val - 1) * blockSize tm + blockSize tm =
          index.val * blockSize tm := by
      have hsucc : index.val - 1 + 1 = index.val := by omega
      have h := congrArg
        (fun value : ℕ => value * blockSize tm) hsucc
      simpa only [Nat.add_mul, one_mul] using h
    congr 1
    change
      (index.val - 1) * blockSize tm +
        (blockSize tm + (offset.val + hint.1.val) -
          hint.2.1.val) =
      index.val * blockSize tm + offset.val -
        hint.2.1.val + hint.1.val
    omega
  · simp only [dite_eq_right hleft]
    let shifted := offset.val + hint.1.val - hint.2.1.val
    have hglobalShift :
        index.val * blockSize tm + offset.val -
          hint.2.1.val + hint.1.val =
        index.val * blockSize tm + shifted := by
      dsimp [shifted]
      omega
    by_cases hcenter : shifted < blockSize tm
    · have hcenter' :
          offset.val + hint.1.val - hint.2.1.val <
            blockSize tm := by
        simpa only using hcenter
      simp only [dite_eq_left hcenter', stackShiftWindowAt,
        atomBlockAt]
      congr 1
      exact hglobalShift.symm
    · have hcenter' :
          ¬ offset.val + hint.1.val - hint.2.1.val <
            blockSize tm := by
        simpa only [not_lt] using hcenter
      simp only [dite_eq_right hcenter', stackShiftWindowAt,
        atomBlockAt]
      by_cases hlast : index.val = width
      · have hcapacity := width_le_block_capacity tm width
        have hleftBlank :
            first.length ≤
              (rightBlock width index).val * blockSize tm +
                (shifted - blockSize tm) := by
          have hright : (rightBlock width index).val = width := by
            change min (index.val + 1) width = width
            simp only [hlast, le_add_iff_nonneg_right, zero_le, inf_of_le_right]
          rw [hright]
          omega
        have hrightBlank :
            first.length ≤
              index.val * blockSize tm + offset.val -
                hint.2.1.val + hint.1.val := by
          rw [hglobalShift]
          rw [hlast]
          omega
        rw [paddedAtom_none_of_length_le tm first _ hleftBlank,
          paddedAtom_none_of_length_le tm first _ hrightBlank]
      · have hright :
            (rightBlock width index).val = index.val + 1 := by
          change min (index.val + 1) width = index.val + 1
          exact Nat.min_eq_left (by
            have hbound := index.isLt
            omega)
        rw [hright]
        congr 1
        have hmul :
            (index.val + 1) * blockSize tm =
              index.val * blockSize tm + blockSize tm := by
          simp only [Nat.add_mul, one_mul]
        rw [hglobalShift]
        omega

end CLFiniteShiftWindows

namespace CLStackWindowEquivalence

open Computability GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows

private theorem not_first_prefix_implies_drop_le
    (tm : Turing.FinTM2)
    (hint : SingleStackHint tm)
    (index : ℕ)
    (offset : Fin (blockSize tm))
    (hnot : ¬ (index = 0 ∧ offset.val < hint.2.1.val)) :
    hint.2.1.val ≤ index * blockSize tm + offset.val := by
  by_cases hzero : index = 0
  · have hoffset : hint.2.1.val ≤ offset.val := by
      by_contra hsmall
      exact hnot ⟨hzero, by omega⟩
    simp only [hzero, zero_mul, zero_add, hoffset]
  · have hpositive : 1 ≤ index := by omega
    have hcapacity :=
      Nat.mul_le_mul_right (blockSize tm) hpositive
    have hdrop := hint.2.1.isLt
    simp only [Nat.one_mul] at hcapacity
    omega

private theorem stackShiftWindow_of_common_suffix
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirstLength : first.length ≤ width)
    (hint : SingleStackHint tm)
    (hcommon : first.drop hint.1.val = next.drop hint.2.1.val)
    (hprefix : PrefixHintCorrect tm hint next)
    (index : Fin (width + 1)) :
    StackShiftAllowed tm hint
      (stackShiftWindowAt tm width first next index) := by
  simp only [GapCVP.CLFiniteShiftWindows.PrefixHintCorrect,
      GapCVP.CLCompleteLocalCompiler.StackShiftAllowed, decide_eq_true_eq] at *
  intro offset
  change
    paddedAtom next (index.val * blockSize tm + offset.val) =
      shiftedWindowAtom tm hint
        (stackShiftWindowAt tm width first next index) offset
  by_cases hprefixPosition :
      index.val = 0 ∧ offset.val < hint.2.1.val
  · have hguard :
        (stackShiftWindowAt tm width first next index).2.2.2.2 = true ∧
          offset.val < hint.2.1.val := by
      simpa only [stackShiftWindowAt, Fin.val_eq_zero_iff, decide_eq_true_eq, Fin.val_fin_lt]
          using hprefixPosition
    rw [shiftedWindowAtom, ite_eq_left hguard]
    have hcorrect := hprefix offset hprefixPosition.2
    simpa only [hprefixPosition.1, zero_mul, zero_add] using hcorrect.symm
  · rw [shiftedWindowAtom_eq_old tm width first next
      hfirstLength hint index offset hprefixPosition]
    exact paddedAtom_common_suffix tm first next
      hint.1.val hint.2.1.val
      (index.val * blockSize tm + offset.val) hcommon
      (not_first_prefix_implies_drop_le tm hint index.val
        offset hprefixPosition)

private theorem allStackShiftWindows_of_common_suffix
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirstLength : first.length ≤ width)
    (hint : SingleStackHint tm)
    (hcommon : first.drop hint.1.val = next.drop hint.2.1.val)
    (hprefix : PrefixHintCorrect tm hint next) :
    AllStackShiftWindows tm width hint first next := by
  simp only [GapCVP.CLFiniteShiftWindows.AllStackShiftWindows, decide_eq_true_eq]
  intro index
  exact (stackShiftAllowed_iff tm hint
    (stackShiftWindowAt tm width first next index)).mpr
    (stackShiftWindow_of_common_suffix tm width first next
      hfirstLength hint hcommon hprefix index)

private theorem paddedShift_of_allStackShiftWindows
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirstLength : first.length ≤ width)
    (hnextLength : next.length ≤ width)
    (hint : SingleStackHint tm)
    (hwindows : AllStackShiftWindows tm width hint first next) :
    ∀ position : ℕ,
      paddedAtom first (hint.1.val + position) =
        paddedAtom next (hint.2.1.val + position) := by
  simp only [GapCVP.CLFiniteShiftWindows.AllStackShiftWindows, decide_eq_true_eq] at hwindows
  intro position
  let global := hint.2.1.val + position
  by_cases hcovered :
      global < (width + 1) * blockSize tm
  · let index : Fin (width + 1) :=
      ⟨global / blockSize tm,
        (Nat.div_lt_iff_lt_mul (blockSize_pos tm)).mpr hcovered⟩
    let offset : Fin (blockSize tm) :=
      ⟨global % blockSize tm,
        Nat.mod_lt global (blockSize_pos tm)⟩
    have hcoordinate :
        index.val * blockSize tm + offset.val = global := by
      dsimp [index, offset]
      simpa only [Nat.mul_comm, Nat.add_comm] using Nat.mod_add_div global (blockSize tm)
    have hnotPrefix :
        ¬ (index.val = 0 ∧ offset.val < hint.2.1.val) := by
      rintro ⟨hzero, hsmall⟩
      have hactual :
          index.val * blockSize tm + offset.val =
            hint.2.1.val + position := by
        simpa only using hcoordinate
      rw [hzero, Nat.zero_mul, Nat.zero_add] at hactual
      omega
    have hallowed :
        StackShiftAllowed tm hint
          (stackShiftWindowAt tm width first next index) :=
      (stackShiftAllowed_iff tm hint
        (stackShiftWindowAt tm width first next index)).mp
        (hwindows index)
    simp only [GapCVP.CLCompleteLocalCompiler.StackShiftAllowed, decide_eq_true_eq] at hallowed
    have hlocal := hallowed offset
    change
      paddedAtom next
        (index.val * blockSize tm + offset.val) =
        shiftedWindowAtom tm hint
          (stackShiftWindowAt tm width first next index) offset
      at hlocal
    rw [shiftedWindowAtom_eq_old tm width first next
      hfirstLength hint index offset hnotPrefix] at hlocal
    rw [hcoordinate] at hlocal
    have holdCoordinate :
        global - hint.2.1.val + hint.1.val =
          hint.1.val + position := by
      dsimp [global]
      omega
    rw [holdCoordinate] at hlocal
    simpa only using hlocal.symm
  · have hbeyond :
        (width + 1) * blockSize tm ≤ global := by omega
    have hcapacity := width_le_block_capacity tm width
    have hdrop := hint.2.1.isLt
    have hcapacityForm :
        (width + 1) * blockSize tm =
          width * blockSize tm + blockSize tm := by
      simp only [Nat.add_mul, one_mul]
    rw [hcapacityForm] at hbeyond
    dsimp [global] at hbeyond
    have hfirstEnd : first.length ≤ hint.1.val + position := by
      omega
    have hnextEnd : next.length ≤ hint.2.1.val + position := by
      omega
    rw [paddedAtom_none_of_length_le tm first _ hfirstEnd,
      paddedAtom_none_of_length_le tm next _ hnextEnd]

private theorem allStackShiftWindows_iff_common_suffix
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hfirstLength : first.length ≤ width)
    (hnextLength : next.length ≤ width)
    (hfirstNoBlank : NoBlankAtoms tm first)
    (hnextNoBlank : NoBlankAtoms tm next)
    (hint : SingleStackHint tm)
    (hprefix : PrefixHintCorrect tm hint next) :
    AllStackShiftWindows tm width hint first next ↔
      first.drop hint.1.val = next.drop hint.2.1.val := by
  constructor
  · intro hwindows
    exact (atomSuffix_iff_paddedShift tm first next
      hfirstNoBlank hnextNoBlank
      hint.1.val hint.2.1.val).mpr
      (paddedShift_of_allStackShiftWindows tm width first next
        hfirstLength hnextLength hint hwindows)
  · intro hcommon
    exact allStackShiftWindows_of_common_suffix tm width first next
      hfirstLength hint hcommon hprefix

end CLStackWindowEquivalence

namespace CLExactVerifierTransition

open Computability GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLExactStackRules
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows

/-- GapCVP reduction support. -/
abbrev FiniteVerifierHint (tm : Turing.FinTM2) :=
  ∀ _ : tm.K, SingleStackHint tm

instance instFintypeFiniteVerifierHint (tm : Turing.FinTM2) :
    Fintype (FiniteVerifierHint tm) := by
  letI : Fintype tm.K := tm.kFin
  infer_instance

/-- GapCVP reduction support. -/
noncomputable def AllVerifierStackWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hint : FiniteVerifierHint machine.tm) : Bool :=
  @decide (
  ∀ stack : machine.tm.K,
    AllStackShiftWindows machine.tm width (hint stack)
      (canonicalStackAtoms machine stack (first.stk stack)
        (stackAtomSupported_supportedValues machine first hfirst stack))
      (canonicalStackAtoms machine stack (next.stk stack)
        (stackAtomSupported_supportedValues machine next hnext stack))
  ) (Classical.propDecidable _)
private theorem canonicalStackAtoms_injective
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (first next : List (machine.tm.Γ stack))
    (hfirst : ∀ value ∈ first,
      SupportedStackValue machine stack value)
    (hnext : ∀ value ∈ next,
      SupportedStackValue machine stack value)
    (hatoms : canonicalStackAtoms machine stack first hfirst =
      canonicalStackAtoms machine stack next hnext) :
    first = next := by
  apply List.ext_getElem?
  intro index
  have hfirstDecode := paddedAtom_decode machine stack
    (canonicalStackAtoms_forall₂ machine stack first hfirst) index
  have hnextDecode := paddedAtom_decode machine stack
    (canonicalStackAtoms_forall₂ machine stack next hnext) index
  rw [hatoms] at hfirstDecode
  exact hfirstDecode.symm.trans hnextDecode

end CLExactVerifierTransition

namespace CLEmittedCNFTM

open Computability Turing

private abbrev LookupMemory (limit : ℕ) :=
  Fin (limit + 1) × (Fin limit → Bool) × Bool

private def initialLookupMemory (limit : ℕ) : LookupMemory limit :=
  (0, fun _ => false, false)

private def advanceLookupMemory (limit : ℕ)
    (memory : LookupMemory limit) (bit : Bool) :
    LookupMemory limit :=
  if h : memory.1.val < limit then
    (⟨memory.1.val + 1, by omega⟩,
      Function.update memory.2.1 ⟨memory.1.val, h⟩ bit,
      memory.2.2)
  else
    (memory.1, memory.2.1, true)

private def lookupMemoryBits (limit : ℕ)
    (memory : LookupMemory limit) : List Bool :=
  (List.ofFn memory.2.1).take memory.1.val

private def lookupMemoryOutput (limit : ℕ)
    (table : List Bool → Bool)
    (memory : LookupMemory limit) : Bool :=
  if memory.2.2 then false else table (lookupMemoryBits limit memory)

private abbrev boundedLookupMachine (limit : ℕ)
    (table : List Bool → Bool) : Turing.FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := LookupMemory limit × Option Bool
  initialState := (initialLookupMemory limit, none)
  m _ :=
    .peek false (fun state symbol => (state.1, symbol))
      (.branch (fun state => state.2.isSome)
        (.pop false
          (fun state _ =>
            (advanceLookupMemory limit state.1
              (state.2.getD false), none))
          (.goto (fun _ => ())))
        (.push true
          (fun state => lookupMemoryOutput limit table state.1)
          (.load (fun _ => (initialLookupMemory limit, none))
            .halt)))

private def lookupConfiguration (limit : ℕ)
    (table : List Bool → Bool)
    (remaining : List Bool)
    (memory : LookupMemory limit) :
    (boundedLookupMachine limit table).Cfg where
  l := some ()
  var := (memory, none)
  stk
    | false => remaining
    | true => []

private theorem boundedLookupMachine_step_cons
    (limit : ℕ)
    (table : List Bool → Bool)
    (bit : Bool)
    (remaining : List Bool)
    (memory : LookupMemory limit) :
    (boundedLookupMachine limit table).step
        (lookupConfiguration limit table (bit :: remaining) memory) =
      some (lookupConfiguration limit table remaining
        (advanceLookupMemory limit memory bit)) := by
  cases bit <;>
    simp only [boundedLookupMachine, lookupConfiguration,
      Turing.FinTM2.step, Turing.TM2.step,
      Turing.TM2.stepAux, List.head?_cons, Option.isSome_some,
      Option.getD_some, List.tail_cons, Bool.cond_true] <;>
    congr 2 <;>
    funext stack <;>
    cases stack <;>
    simp [Function.update]

private theorem boundedLookupMachine_step_nil
    (limit : ℕ)
    (table : List Bool → Bool)
    (memory : LookupMemory limit) :
    (boundedLookupMachine limit table).step
        (lookupConfiguration limit table [] memory) =
      some (Turing.haltList (boundedLookupMachine limit table)
        [lookupMemoryOutput limit table memory]) := by
  simp only [boundedLookupMachine, FinTM2.step, TM2.step, lookupConfiguration, TM2.stepAux,
      List.head?_nil,
      Option.isSome_none, Option.getD_none, List.tail_nil, Function.update_eq_self,
          Bool.cond_false,
          haltList, eq_mpr_eq_cast,
      cast_eq, dite_eq_ite]
  congr 2
  funext stack
  cases stack <;> simp [Function.update]

/-- GapCVP reduction support. -/
def boundedLookupOutput (limit : ℕ)
    (table : List Bool → Bool)
    (input : List Bool) : Bool :=
  lookupMemoryOutput limit table
    (input.foldl (advanceLookupMemory limit)
      (initialLookupMemory limit))

private theorem boundedLookupMachine_iterate
    (limit : ℕ)
    (table : List Bool → Bool)
    (input : List Bool)
    (memory : LookupMemory limit) :
    ((flip Option.bind (boundedLookupMachine limit table).step)^[
      input.length + 1])
        (some (lookupConfiguration limit table input memory)) =
      some (Turing.haltList (boundedLookupMachine limit table)
        [lookupMemoryOutput limit table
          (input.foldl (advanceLookupMemory limit) memory)]) := by
  induction input generalizing memory with
  | nil =>
      change
        (boundedLookupMachine limit table).step
          (lookupConfiguration limit table [] memory) = _
      exact boundedLookupMachine_step_nil limit table memory
  | cons bit remaining ih =>
      change
        ((flip Option.bind (boundedLookupMachine limit table).step)^[
          remaining.length + 1 + 1])
            (some (lookupConfiguration limit table
              (bit :: remaining) memory)) = _
      rw [Function.iterate_succ_apply]
      change
        ((flip Option.bind (boundedLookupMachine limit table).step)^[
          remaining.length + 1])
            ((boundedLookupMachine limit table).step
              (lookupConfiguration limit table
                (bit :: remaining) memory)) = _
      rw [boundedLookupMachine_step_cons]
      exact ih (advanceLookupMemory limit memory bit)

private theorem boundedLookupMachine_init
    (limit : ℕ)
    (table : List Bool → Bool)
    (input : List Bool) :
    Turing.initList (boundedLookupMachine limit table) input =
      lookupConfiguration limit table input
        (initialLookupMemory limit) := by
  simp only [boundedLookupMachine, initList, eq_mpr_eq_cast, cast_eq, dite_eq_ite,
      lookupConfiguration]
  congr 1
  funext stack
  cases stack <;> simp

/-- GapCVP reduction support. -/
noncomputable def boundedLookupComputable
    (limit : ℕ)
    (table : List Bool → Bool) :
    BitTM
      (fun input : List Bool =>
        [boundedLookupOutput limit table input]) where
  tm := boundedLookupMachine limit table
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.X + 1
  outputsFun input := {
    steps := input.length + 1
    evals_in_steps := by
      have hinput :
          List.map (Equiv.refl Bool).invFun (bitEncoding input) =
            input := by
        change List.map (fun bit : Bool => bit) input = input
        simp only [List.map_id_fun', id_eq]
      have houtput :
          List.map (Equiv.refl Bool).invFun
              (bitEncoding [boundedLookupOutput limit table input]) =
            [boundedLookupOutput limit table input] := by
        change
          List.map (fun bit : Bool => bit)
            [boundedLookupOutput limit table input] =
              [boundedLookupOutput limit table input]
        simp only [List.map_cons, List.map_nil]
      rw [hinput, houtput, boundedLookupMachine_init]
      exact boundedLookupMachine_iterate limit table input
        (initialLookupMemory limit)
    steps_le_m := by
      simp only [bitEncoding, id_eq, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one,
          Std.le_refl]
  }

end CLEmittedCNFTM

namespace CLWindowTruthTable

open Computability Turing GapCVP.CLEmittedCNFTM

private theorem lookupMemoryBits_advance
    (limit : ℕ)
    (memory : LookupMemory limit)
    (bit : Bool)
    (hcapacity : memory.1.val < limit) :
    lookupMemoryBits limit
        (advanceLookupMemory limit memory bit) =
      lookupMemoryBits limit memory ++ [bit] := by
  have hcountLe : memory.1.val ≤ limit := by omega
  apply List.ext_getElem?
  intro index
  by_cases hbefore : index < memory.1.val
  · have hlimit : index < limit := Nat.lt_trans hbefore hcapacity
    have hne :
        (⟨index, hlimit⟩ : Fin limit) ≠
          ⟨memory.1.val, hcapacity⟩ := by
      intro heq
      have hval := congrArg Fin.val heq
      change index = memory.1.val at hval
      omega
    have hle : index ≤ memory.1.val := by omega
    simp only [lookupMemoryBits, advanceLookupMemory, hcapacity, ↓reduceDIte, List.length_take,
        List.length_ofFn,
        Order.add_one_le_iff, inf_of_le_left, Order.lt_add_one_iff, hle, getElem?_pos,
            List.getElem_take, List.getElem_ofFn,
        Function.update, hne, List.length_append, Nat.min_eq_left hcountLe, List.length_cons,
            List.length_nil, zero_add,
        hbefore, List.getElem_append_left]
  · by_cases hat : index = memory.1.val
    · subst index
      simp only [lookupMemoryBits, advanceLookupMemory, hcapacity, ↓reduceDIte, List.length_take,
          List.length_ofFn,
          Order.add_one_le_iff, inf_of_le_left, lt_add_iff_pos_right, Order.lt_one_iff,
              getElem?_pos, List.getElem_take,
          List.getElem_ofFn, Function.update, List.length_append, Nat.min_eq_left hcountLe,
              List.length_cons, List.length_nil,
          zero_add, Std.le_refl, List.getElem_append_right, tsub_self, List.getElem_cons_zero]
    · have hafter : memory.1.val + 1 ≤ index := by omega
      have hnotNew : ¬ index < memory.1.val + 1 := by omega
      simp only [lookupMemoryBits, advanceLookupMemory, hcapacity, ↓reduceDIte, List.length_take,
          List.length_ofFn,
          Order.add_one_le_iff, inf_of_le_left, hnotNew, not_false_eq_true, getElem?_neg,
              List.length_append,
          Nat.min_eq_left hcountLe, List.length_cons, List.length_nil, zero_add]

private theorem lookupMemory_fold_exact
    (limit : ℕ)
    (memory : LookupMemory limit)
    (input : List Bool)
    (hcapacity : memory.1.val + input.length ≤ limit)
    (hoverflow : memory.2.2 = false) :
    lookupMemoryBits limit
        (input.foldl (advanceLookupMemory limit) memory) =
          lookupMemoryBits limit memory ++ input ∧
      (input.foldl (advanceLookupMemory limit) memory).2.2 = false := by
  induction input generalizing memory with
  | nil =>
      simp only [List.foldl_nil, List.append_nil, hoverflow, and_self]
  | cons bit remaining ih =>
      have hhead : memory.1.val < limit := by
        simp only [List.length_cons] at hcapacity
        omega
      let nextMemory := advanceLookupMemory limit memory bit
      have hnextCount : nextMemory.1.val = memory.1.val + 1 := by
        simp only [advanceLookupMemory, hhead, ↓reduceDIte, nextMemory]
      have hnextOverflow : nextMemory.2.2 = false := by
        simp only [advanceLookupMemory, hhead, ↓reduceDIte, hoverflow, nextMemory]
      have hnextCapacity :
          nextMemory.1.val + remaining.length ≤ limit := by
        simp only [List.length_cons] at hcapacity
        rw [hnextCount]
        omega
      have htail := ih nextMemory hnextCapacity hnextOverflow
      simp only [List.foldl_cons]
      constructor
      · calc
          lookupMemoryBits limit
              (remaining.foldl (advanceLookupMemory limit) nextMemory) =
            lookupMemoryBits limit nextMemory ++ remaining := htail.1
          _ = (lookupMemoryBits limit memory ++ [bit]) ++
              remaining := by
                rw [show
                  lookupMemoryBits limit nextMemory =
                    lookupMemoryBits limit memory ++ [bit] from
                  lookupMemoryBits_advance limit memory bit hhead]
          _ = lookupMemoryBits limit memory ++ (bit :: remaining) := by
                simp only [List.append_assoc, List.cons_append, List.nil_append]
      · exact htail.2

theorem boundedLookupOutput_of_length_le
    (limit : ℕ)
    (table : List Bool → Bool)
    (input : List Bool)
    (hinput : input.length ≤ limit) :
    boundedLookupOutput limit table input = table input := by
  have hcapacity :
      (initialLookupMemory limit).1.val + input.length ≤ limit := by
    simpa only [initialLookupMemory, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add] using hinput
  have hoverflow :
      (initialLookupMemory limit).2.2 = false := rfl
  obtain ⟨hbits, hnotOverflow⟩ :=
    lookupMemory_fold_exact limit (initialLookupMemory limit)
      input hcapacity hoverflow
  have hbits' :
      lookupMemoryBits limit
        (input.foldl (advanceLookupMemory limit)
          (initialLookupMemory limit)) = input := by
    simpa only [lookupMemoryBits, initialLookupMemory, Fin.coe_ofNat_eq_mod, Nat.zero_mod,
        List.ofFn_const,
        List.take_replicate, zero_le, inf_of_le_left, List.replicate_zero, List.nil_append]
            using hbits
  simp only [boundedLookupOutput, lookupMemoryOutput, hnotOverflow, Bool.false_eq_true, ↓reduceIte,
      hbits']

end CLWindowTruthTable

namespace CLLocalTableauCompiler

open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLExactVerifierRules GapCVP.CLCompleteLocalCompiler

theorem filterMap_ofFn_getElem
    {α : Type}
    (values : List α)
    (width : ℕ) :
    (List.ofFn (fun index : Fin width =>
      values[index.val]?)).filterMap id =
      values.take width := by
  induction width generalizing values with
  | zero => simp only [id_eq, List.ofFn_zero, List.filterMap_nil, List.take_zero]
  | succ width ih =>
      cases values with
      | nil =>
          simp only [id_eq, List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg,
              List.ofFn_succ,
              List.ofFn_const, List.filterMap_cons_none, List.filterMap_replicate_of_none,
                  List.take_nil]
      | cons value rest =>
          simpa only [id_eq, List.ofFn_succ, Fin.coe_ofNat_eq_mod, Nat.zero_mod, List.length_cons,
              lt_add_iff_pos_left,
              Order.lt_add_one_iff, zero_le, getElem?_pos, List.getElem_cons_zero, Fin.val_succ,
                  List.getElem?_cons_succ,
              Option.some.injEq, List.filterMap_cons_some, List.take_succ_cons, List.cons.injEq,
                  true_and] using ih rest

/-- GapCVP reduction support. -/
def decodedAtomBlock
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (block : AtomBlock machine.tm) :
    List (machine.tm.Γ stack) :=
  (List.ofFn (fun index : Fin (blockSize machine.tm) =>
    cellAtomValue machine stack (block index))).filterMap id

theorem decodedAtomBlock_canonical
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (stack : machine.tm.K)
    (values : List (machine.tm.Γ stack))
    (hsupported : ∀ value ∈ values,
      SupportedStackValue machine stack value) :
    decodedAtomBlock machine stack
        (atomBlockAt machine.tm
          (canonicalStackAtoms machine stack values hsupported) 0) =
      values.take (blockSize machine.tm) := by
  have hpointwise :
      (fun index : Fin (blockSize machine.tm) =>
        cellAtomValue machine stack
          ((atomBlockAt machine.tm
            (canonicalStackAtoms machine stack values hsupported) 0)
            index)) =
        (fun index : Fin (blockSize machine.tm) =>
          values[index.val]?) := by
    funext index
    simpa only [atomBlockAt, zero_mul, zero_add] using
        paddedAtom_decode machine stack (canonicalStackAtoms_forall₂ machine stack values
            hsupported) index.val
  unfold decodedAtomBlock
  rw [hpointwise]
  exact filterMap_ofFn_getElem values (blockSize machine.tm)

/-- GapCVP reduction support. -/
abbrev FiniteVerifierHeadQuery (tm : Turing.FinTM2) :=
  (Option tm.Λ × tm.σ) ×
    (tm.K → AtomBlock tm) ×
    (Option tm.Λ × tm.σ)

/-- GapCVP reduction support. -/
def finiteHeadConfiguration
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (control : Option machine.tm.Λ × machine.tm.σ)
    (heads : machine.tm.K → AtomBlock machine.tm) :
    machine.tm.Cfg where
  l := control.1
  var := control.2
  stk stack := decodedAtomBlock machine stack (heads stack)

private def finiteHeadQueryOf
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first) :
    FiniteVerifierHeadQuery machine.tm :=
  ((first.l, first.var),
    (fun stack => atomBlockAt machine.tm
      (canonicalStackAtoms machine stack
        (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)) 0),
    (next.l, next.var))

private theorem finiteHeadConfiguration_prefix
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration) :
    StackPrefixAgreement (blockSize machine.tm)
      configuration.stk
      (finiteHeadConfiguration machine
        (configuration.l, configuration.var)
        (fun stack => atomBlockAt machine.tm
          (canonicalStackAtoms machine stack
            (configuration.stk stack) (stackAtomSupported_supportedValues machine configuration
                hsupported stack)) 0)).stk := by
  simp only [GapCVP.CLExactVerifierRules.StackPrefixAgreement, decide_eq_true_eq]
  intro stack
  change
    (configuration.stk stack).take (blockSize machine.tm) =
      (decodedAtomBlock machine stack
        (atomBlockAt machine.tm
          (canonicalStackAtoms machine stack
            (configuration.stk stack) (stackAtomSupported_supportedValues machine configuration
                hsupported stack)) 0)).take
        (blockSize machine.tm)
  rw [decodedAtomBlock_canonical]
  simp only [List.take_self_eq_iff, List.length_take, inf_le_left]

end CLLocalTableauCompiler

namespace CLVerifierTableauEmission

open Computability Turing GapCVP.CLBoundedStates GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLCompleteLocalCompiler GapCVP.CLFiniteShiftWindows

theorem prefixHintCorrect_of_allStackShiftWindows
    (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : List (CellAtom tm))
    (hint : SingleStackHint tm)
    (hwindows : AllStackShiftWindows tm width hint first next) :
    PrefixHintCorrect tm hint next := by
  simp only [GapCVP.CLFiniteShiftWindows.PrefixHintCorrect, decide_eq_true_eq]
  simp only [GapCVP.CLFiniteShiftWindows.AllStackShiftWindows, decide_eq_true_eq] at hwindows
  intro offset hoffset
  let firstIndex : Fin (width + 1) := 0
  have hallowed :
      StackShiftAllowed tm hint
        (stackShiftWindowAt tm width first next firstIndex) :=
    (stackShiftAllowed_iff tm hint
      (stackShiftWindowAt tm width first next firstIndex)).mp
      (hwindows firstIndex)
  simp only [GapCVP.CLCompleteLocalCompiler.StackShiftAllowed, decide_eq_true_eq] at hallowed
  have hcell := hallowed offset
  change
    paddedAtom next
        (firstIndex.val * blockSize tm + offset.val) =
      shiftedWindowAtom tm hint
        (stackShiftWindowAt tm width first next firstIndex)
        offset at hcell
  have hguard :
      (stackShiftWindowAt tm width first next firstIndex).2.2.2.2 =
          true ∧
        offset.val < hint.2.1.val := by
    simp [stackShiftWindowAt, firstIndex, hoffset]
  rw [shiftedWindowAtom, ite_eq_left hguard] at hcell
  simpa [firstIndex] using hcell.symm

end CLVerifierTableauEmission

namespace CLUnconditionalTableau

open Computability Turing GapCVP.CLLocalWindows GapCVP.CLExactVerifierRules

/-- GapCVP reduction support. -/
structure PrefixScript {K : Type} (Γ : K → Type) where
  /-- GapCVP reduction support. -/
  dropped : K → ℕ
  /-- GapCVP reduction support. -/
  pushed : ∀ stack : K, List (Γ stack)

/-- GapCVP reduction support. -/
def scriptStacks {K : Type} {Γ : K → Type}
    (original : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ) :
    ∀ stack : K, List (Γ stack) :=
  fun stack =>
    script.pushed stack ++
      (original stack).drop (script.dropped stack)

/-- GapCVP reduction support. -/
def emptyPrefixScript {K : Type} (Γ : K → Type) :
    PrefixScript Γ where
  dropped _ := 0
  pushed _ := []

@[simp] theorem scriptStacks_empty
    {K : Type} {Γ : K → Type}
    (original : ∀ stack : K, List (Γ stack)) :
    scriptStacks original (emptyPrefixScript Γ) = original := by
  funext stack
  simp only [scriptStacks, emptyPrefixScript, List.drop_zero, List.nil_append]

private def pushPrefixScript
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (script : PrefixScript Γ)
    (stack : K) (value : Γ stack) : PrefixScript Γ where
  dropped := script.dropped
  pushed := Function.update script.pushed stack
    (value :: script.pushed stack)

private theorem scriptStacks_push
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (original : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ)
    (stack : K) (value : Γ stack) :
    scriptStacks original (pushPrefixScript script stack value) =
      Function.update (scriptStacks original script)
        stack (value :: scriptStacks original script stack) := by
  funext target
  by_cases htarget : target = stack
  · subst target
    simp only [scriptStacks, pushPrefixScript, Function.update_self, List.cons_append]
  · simp only [scriptStacks, pushPrefixScript, Function.update, htarget, ↓reduceDIte]

private def popPrefixScript
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (script : PrefixScript Γ)
    (stack : K) : PrefixScript Γ :=
  match script.pushed stack with
  | [] =>
      { dropped := Function.update script.dropped stack
          (script.dropped stack + 1)
        pushed := script.pushed }
  | _ :: tail =>
      { dropped := script.dropped
        pushed := Function.update script.pushed stack tail }

private theorem scriptStacks_pop
    {K : Type} {Γ : K → Type} [DecidableEq K]
    (original : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ)
    (stack : K) :
    scriptStacks original (popPrefixScript script stack) =
      Function.update (scriptStacks original script)
        stack (scriptStacks original script stack).tail := by
  funext target
  by_cases htarget : target = stack
  · subst target
    cases hhead : script.pushed stack with
    | nil =>
        simp only [scriptStacks, popPrefixScript, hhead, Function.update_self, List.nil_append,
            List.tail_drop]
    | cons head tail =>
        simp only [scriptStacks, popPrefixScript, hhead, Function.update_self, List.cons_append,
            List.tail_cons]
  · cases hhead : script.pushed stack with
    | nil =>
        simp only [scriptStacks, popPrefixScript, hhead, Function.update, htarget, ↓reduceDIte]
    | cons head tail =>
        simp only [scriptStacks, popPrefixScript, hhead, Function.update, htarget, ↓reduceDIte]

/-- GapCVP reduction support. -/
def executePrefixScript
    {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K] :
    Turing.TM2.Stmt Γ Λ σ → σ →
      (∀ stack : K, List (Γ stack)) →
      PrefixScript Γ →
      Option Λ × σ × PrefixScript Γ
  | .push stack value continuation, state, original, script =>
      executePrefixScript continuation state original
        (pushPrefixScript script stack (value state))
  | .peek stack update continuation, state, original, script =>
      executePrefixScript continuation
        (update state (scriptStacks original script stack).head?)
        original script
  | .pop stack update continuation, state, original, script =>
      executePrefixScript continuation
        (update state (scriptStacks original script stack).head?)
        original (popPrefixScript script stack)
  | .load update continuation, state, original, script =>
      executePrefixScript continuation (update state) original script
  | .branch test yes no, state, original, script =>
      if test state then
        executePrefixScript yes state original script
      else
        executePrefixScript no state original script
  | .goto update, state, _, script =>
      (some (update state), state, script)
  | .halt, state, _, script =>
      (none, state, script)

theorem executePrefixScript_correct
    {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K]
    (statement : Turing.TM2.Stmt Γ Λ σ)
    (state : σ)
    (original : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ) :
    Turing.TM2.stepAux statement state
        (scriptStacks original script) =
      { l := (executePrefixScript statement state original script).1
        var :=
          (executePrefixScript statement state original script).2.1
        stk := scriptStacks original
          (executePrefixScript statement state original script).2.2 } := by
  induction statement generalizing state script with
  | push stack value continuation ih =>
      simpa only [TM2.stepAux, executePrefixScript, scriptStacks_push] using
          ih state (pushPrefixScript script stack (value state))
  | peek stack update continuation ih =>
      simpa only [TM2.stepAux, executePrefixScript] using
          ih (update state (scriptStacks original script stack).head?) script
  | pop stack update continuation ih =>
      simpa only [TM2.stepAux, executePrefixScript, scriptStacks_pop] using
          ih (update state (scriptStacks original script stack).head?) (popPrefixScript script
              stack)
  | load update continuation ih =>
      simpa only [TM2.stepAux, executePrefixScript] using ih (update state) script
  | branch test yes no ihyes ihno =>
      cases htest : test state with
      | false =>
          simpa only [TM2.stepAux, htest, Bool.cond_false, executePrefixScript, Bool.false_eq_true,
              ↓reduceIte] using
              ihno state script
      | true =>
          simpa only [TM2.stepAux, htest, Bool.cond_true, executePrefixScript, ↓reduceIte]
              using ihyes
              state script
  | goto update =>
      rfl
  | halt =>
      rfl

theorem executePrefixScript_of_prefix
    {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K]
    (statement : Turing.TM2.Stmt Γ Λ σ)
    (state : σ)
    (first second : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ)
    (hagreement : StackPrefixAgreement
      (statementStackActions statement + 1)
      (scriptStacks first script)
      (scriptStacks second script)) :
    executePrefixScript statement state first script =
      executePrefixScript statement state second script := by
  induction statement generalizing state first second script with
  | push stack value continuation ih =>
      change StackPrefixAgreement
        (statementStackActions continuation + 1 + 1)
        (scriptStacks first script)
        (scriptStacks second script) at hagreement
      have hsmaller : StackPrefixAgreement
          (statementStackActions continuation + 1)
          (scriptStacks first script)
          (scriptStacks second script) :=
        stackPrefixAgreement_mono (by omega) hagreement
      have hupdated := stackPrefixAgreement_push
        (statementStackActions continuation + 1)
        (scriptStacks first script)
        (scriptStacks second script)
        stack (value state) hsmaller
      rw [← scriptStacks_push first script stack (value state),
        ← scriptStacks_push second script stack (value state)]
        at hupdated
      simpa only [executePrefixScript] using
          ih state first second (pushPrefixScript script stack (value state)) hupdated
  | peek stack update continuation ih =>
      have hhead :
          (scriptStacks first script stack).head? =
            (scriptStacks second script stack).head? :=
        stackPrefixAgreement_head (by omega) hagreement stack
      have hnext := ih
        (update state (scriptStacks first script stack).head?)
        first second script hagreement
      simpa only [executePrefixScript, hhead] using hnext
  | pop stack update continuation ih =>
      change StackPrefixAgreement
        (statementStackActions continuation + 1 + 1)
        (scriptStacks first script)
        (scriptStacks second script) at hagreement
      have hhead :
          (scriptStacks first script stack).head? =
            (scriptStacks second script stack).head? :=
        stackPrefixAgreement_head (by omega) hagreement stack
      have hupdated := stackPrefixAgreement_pop
        (statementStackActions continuation + 1)
        (scriptStacks first script)
        (scriptStacks second script)
        stack hagreement
      rw [← scriptStacks_pop first script stack,
        ← scriptStacks_pop second script stack] at hupdated
      have hnext := ih
        (update state (scriptStacks first script stack).head?)
        first second (popPrefixScript script stack) hupdated
      simpa only [executePrefixScript, hhead] using hnext
  | load update continuation ih =>
      simpa only [executePrefixScript] using ih (update state) first second script hagreement
  | branch test yes no ihyes ihno =>
      change StackPrefixAgreement
        (max (statementStackActions yes)
          (statementStackActions no) + 1)
        (scriptStacks first script)
        (scriptStacks second script) at hagreement
      cases htest : test state with
      | false =>
          have hsmaller : StackPrefixAgreement
              (statementStackActions no + 1)
              (scriptStacks first script)
              (scriptStacks second script) :=
            stackPrefixAgreement_mono
              (Nat.add_le_add_right
                (Nat.le_max_right
                  (statementStackActions yes)
                  (statementStackActions no)) 1)
              hagreement
          simpa only [executePrefixScript, htest, Bool.false_eq_true, ↓reduceIte] using
              ihno state first second script hsmaller
      | true =>
          have hsmaller : StackPrefixAgreement
              (statementStackActions yes + 1)
              (scriptStacks first script)
              (scriptStacks second script) :=
            stackPrefixAgreement_mono
              (Nat.add_le_add_right
                (Nat.le_max_left
                  (statementStackActions yes)
                  (statementStackActions no)) 1)
              hagreement
          simpa only [executePrefixScript, htest, ↓reduceIte] using ihyes state first second script
              hsmaller
  | goto update =>
      rfl
  | halt =>
      rfl

end CLUnconditionalTableau

namespace CLGlobalTableauSimulation

open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLExactStackRules GapCVP.CLExactVerifierRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLStackShiftSoundness2 GapCVP.CLFiniteShiftWindows GapCVP.CLStackWindowEquivalence
open GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLVerifierTableauEmission GapCVP.CLUnconditionalTableau

private theorem executePrefixScript_bounds
    {K : Type} {Γ : K → Type} {Λ σ : Type}
    [DecidableEq K]
    (statement : Turing.TM2.Stmt Γ Λ σ)
    (state : σ)
    (original : ∀ stack : K, List (Γ stack))
    (script : PrefixScript Γ)
    (target : K) :
    (executePrefixScript statement state original script).2.2.dropped
          target ≤
        script.dropped target + statementStackActions statement ∧
      ((executePrefixScript statement state original script).2.2.pushed
          target).length ≤
        (script.pushed target).length +
          statementStackActions statement := by
  induction statement generalizing state script with
  | push stack value continuation ih =>
      have hnext := ih state
        (pushPrefixScript script stack (value state))
      by_cases htarget : target = stack
      · subst target
        simp only [pushPrefixScript, Function.update_self, List.length_cons, executePrefixScript,
            statementStackActions] at hnext ⊢
        omega
      · simp [executePrefixScript, pushPrefixScript,
          statementStackActions, Function.update, htarget]
          at hnext ⊢
        omega
  | peek stack update continuation ih =>
      simpa only [executePrefixScript, statementStackActions] using
          ih (update state (scriptStacks original script stack).head?) script
  | pop stack update continuation ih =>
      have hnext := ih
        (update state (scriptStacks original script stack).head?)
        (popPrefixScript script stack)
      by_cases htarget : target = stack
      · subst target
        cases hhead : script.pushed stack with
        | nil =>
            simp only [popPrefixScript, hhead, Function.update_self, List.length_nil, zero_add,
                executePrefixScript,
                statementStackActions] at hnext ⊢
            omega
        | cons head tail =>
            simp only [popPrefixScript, hhead, Function.update_self, executePrefixScript,
                statementStackActions,
                List.length_cons] at hnext ⊢
            omega
      · cases hhead : script.pushed stack with
        | nil =>
            simp only [popPrefixScript, hhead, Function.update, htarget, ↓reduceDIte,
                executePrefixScript,
                statementStackActions] at hnext ⊢
            omega
        | cons head tail =>
            simp only [popPrefixScript, hhead, Function.update, htarget, ↓reduceDIte,
                executePrefixScript,
                statementStackActions] at hnext ⊢
            omega
  | load update continuation ih =>
      simpa only [executePrefixScript, statementStackActions] using ih (update state) script
  | branch test yes no ihyes ihno =>
      cases htest : test state with
      | false =>
          have hnext := ihno state script
          simp only [executePrefixScript, htest, Bool.false_eq_true, ↓reduceIte,
              statementStackActions] at hnext ⊢
          omega
      | true =>
          have hnext := ihyes state script
          simp only [executePrefixScript, htest, ↓reduceIte, statementStackActions] at hnext ⊢
          omega
  | goto update =>
      simp only [executePrefixScript, statementStackActions, add_zero, Std.le_refl, and_self]
  | halt =>
      simp only [executePrefixScript, statementStackActions, add_zero, Std.le_refl, and_self]

private theorem emptyPrefixScript_bounds
    (tm : Turing.FinTM2)
    (label : tm.Λ)
    (state : tm.σ)
    (original : ∀ stack : tm.K, List (tm.Γ stack))
    (target : tm.K) :
    (executePrefixScript (tm.m label) state original
        (emptyPrefixScript tm.Γ)).2.2.dropped target <
        blockSize tm ∧
      ((executePrefixScript (tm.m label) state original
        (emptyPrefixScript tm.Γ)).2.2.pushed target).length <
        blockSize tm := by
  have hbound := executePrefixScript_bounds
    (tm.m label) state original
    (emptyPrefixScript tm.Γ) target
  have hstatement := statementStackActions_lt_blockSize tm label
  have hdrop :
      (executePrefixScript (tm.m label) state original
        (emptyPrefixScript tm.Γ)).2.2.dropped target ≤
        statementStackActions (tm.m label) := by
    simpa only [emptyPrefixScript, zero_add] using hbound.1
  have hpush :
      ((executePrefixScript (tm.m label) state original
        (emptyPrefixScript tm.Γ)).2.2.pushed target).length ≤
        statementStackActions (tm.m label) := by
    simpa only [emptyPrefixScript, List.length_nil, zero_add] using hbound.2
  exact ⟨hdrop.trans_lt hstatement, hpush.trans_lt hstatement⟩

/-- GapCVP reduction support. -/
def finiteHeadScriptRun
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (label : machine.tm.Λ)
    (state : machine.tm.σ)
    (heads : machine.tm.K → AtomBlock machine.tm) :
    Option machine.tm.Λ × machine.tm.σ ×
      PrefixScript machine.tm.Γ :=
  executePrefixScript (machine.tm.m label) state
    (finiteHeadConfiguration machine (some label, state) heads).stk
    (emptyPrefixScript machine.tm.Γ)

/-- GapCVP reduction support. -/
abbrev ScriptVerifierQuery (tm : Turing.FinTM2) :=
  FiniteVerifierHeadQuery tm ×
    (tm.K → AtomBlock tm) ×
    FiniteVerifierHint tm

/-- GapCVP reduction support. -/
def scriptVerifierAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (query : ScriptVerifierQuery machine.tm) : Bool := by
  classical
  exact match query.1.1.1 with
    | none => false
    | some label =>
        let run := finiteHeadScriptRun machine label
          query.1.1.2 query.1.2.1
        decide
          (run.1 = query.1.2.2.1 ∧
            run.2.1 = query.1.2.2.2 ∧
            ∀ stack : machine.tm.K,
              (query.2.2 stack).1.val = run.2.2.dropped stack ∧
                (query.2.2 stack).2.1.val =
                  (run.2.2.pushed stack).length ∧
                (decodedAtomBlock machine stack
                  (query.2.1 stack)).take
                    (run.2.2.pushed stack).length =
                  run.2.2.pushed stack)

theorem scriptVerifierAllowed_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (query : ScriptVerifierQuery machine.tm) :
    scriptVerifierAllowed machine query = true ↔
      ∃ label : machine.tm.Λ,
        query.1.1.1 = some label ∧
        let run := finiteHeadScriptRun machine label
          query.1.1.2 query.1.2.1
        run.1 = query.1.2.2.1 ∧
          run.2.1 = query.1.2.2.2 ∧
          ∀ stack : machine.tm.K,
            (query.2.2 stack).1.val = run.2.2.dropped stack ∧
              (query.2.2 stack).2.1.val =
                (run.2.2.pushed stack).length ∧
              (decodedAtomBlock machine stack
                (query.2.1 stack)).take
                  (run.2.2.pushed stack).length =
                run.2.2.pushed stack := by
  classical
  cases hlabel : query.1.1.1 with
  | none => simp only [scriptVerifierAllowed, hlabel, Bool.false_eq_true, reduceCtorEq, false_and,
      exists_false]
  | some label => simp only [scriptVerifierAllowed, hlabel, Bool.decide_and, Bool.and_eq_true,
      decide_eq_true_eq,
                      Option.some.injEq, exists_eq_left']

private theorem actualStep_eq_stepAux
    (tm : Turing.FinTM2)
    (first next : tm.Cfg)
    (label : tm.Λ)
    (hlabel : first.l = some label)
    (hstep : tm.step first = some next) :
    Turing.TM2.stepAux (tm.m label) first.var first.stk = next := by
  rcases first with ⟨sourceLabel, sourceState, sourceStacks⟩
  cases sourceLabel with
  | none =>
      simp only [reduceCtorEq] at hlabel
  | some sourceLabel =>
      have heq : sourceLabel = label := Option.some.inj hlabel
      subst sourceLabel
      exact Option.some.inj hstep

private theorem finiteHeadScriptRun_eq_actual
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (first : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (label : machine.tm.Λ)
    (hlabel : first.l = some label) :
    finiteHeadScriptRun machine label first.var
        (fun stack => atomBlockAt machine.tm
          (canonicalStackAtoms machine stack
            (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)) 0) =
      executePrefixScript (machine.tm.m label) first.var first.stk
        (emptyPrefixScript machine.tm.Γ) := by
  let heads : machine.tm.K → AtomBlock machine.tm :=
    fun stack => atomBlockAt machine.tm
      (canonicalStackAtoms machine stack
        (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)) 0
  let finite :=
    finiteHeadConfiguration machine (some label, first.var) heads
  have hblock : StackPrefixAgreement (blockSize machine.tm)
      first.stk finite.stk := by
    have h := finiteHeadConfiguration_prefix machine first hfirst
    simpa only [hlabel] using h
  have hlookahead : StackPrefixAgreement
      (statementStackActions (machine.tm.m label) + 1)
      first.stk finite.stk :=
    stackPrefixAgreement_mono
      (statementLookahead_le_blockSize machine.tm label) hblock
  have hscript := executePrefixScript_of_prefix
    (machine.tm.m label) first.var first.stk finite.stk
    (emptyPrefixScript machine.tm.Γ) (by
      simpa only [scriptStacks_empty] using hlookahead)
  change
    executePrefixScript (machine.tm.m label) first.var finite.stk
        (emptyPrefixScript machine.tm.Γ) = _
  exact hscript.symm

/-- GapCVP reduction support. -/
def scriptVerifierQueryOf
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hint : FiniteVerifierHint machine.tm) :
    ScriptVerifierQuery machine.tm :=
  (finiteHeadQueryOf machine first next hfirst,
    (fun stack => atomBlockAt machine.tm
      (canonicalStackAtoms machine stack
        (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack)) 0),
    hint)

theorem configuration_eq_of_components
    (tm : Turing.FinTM2)
    (first next : tm.Cfg)
    (hlabel : first.l = next.l)
    (hstate : first.var = next.var)
    (hstacks : first.stk = next.stk) :
    first = next := by
  rcases first with ⟨firstLabel, firstState, firstStacks⟩
  rcases next with ⟨nextLabel, nextState, nextStacks⟩
  change firstLabel = nextLabel at hlabel
  change firstState = nextState at hstate
  change firstStacks = nextStacks at hstacks
  cases hlabel
  cases hstate
  cases hstacks
  rfl

private theorem realStackSuffix_of_allVerifierWindows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width)
    (hint : FiniteVerifierHint machine.tm)
    (hwindows : AllVerifierStackWindows machine width
      first next hfirst hnext hint)
    (stack : machine.tm.K) :
    (first.stk stack).drop (hint stack).1.val =
      (next.stk stack).drop (hint stack).2.1.val := by
  have windows := hwindows
  simp only [GapCVP.CLExactVerifierTransition.AllVerifierStackWindows, decide_eq_true_eq]
      at windows
  let firstAtoms := canonicalStackAtoms machine stack
    (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)
  let nextAtoms := canonicalStackAtoms machine stack
    (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack)
  have hfirstBound : firstAtoms.length ≤ width := by
    simpa [firstAtoms, canonicalStackAtoms_length] using
      hfirstLength stack
  have hnextBound : nextAtoms.length ≤ width := by
    simpa [nextAtoms, canonicalStackAtoms_length] using
      hnextLength stack
  have hprefix :
      PrefixHintCorrect machine.tm (hint stack) nextAtoms :=
    prefixHintCorrect_of_allStackShiftWindows machine.tm
      width firstAtoms nextAtoms (hint stack)
      (windows stack)
  have hfirstNoBlank : NoBlankAtoms machine.tm firstAtoms := by
    simpa [firstAtoms] using
      canonicalStackAtoms_no_blank machine stack
        (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)
  have hnextNoBlank : NoBlankAtoms machine.tm nextAtoms := by
    simpa [nextAtoms] using
      canonicalStackAtoms_no_blank machine stack
        (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack)
  have hatoms :=
    (allStackShiftWindows_iff_common_suffix machine.tm width
      firstAtoms nextAtoms hfirstBound hnextBound
      hfirstNoBlank hnextNoBlank
      (hint stack) hprefix).mp (windows stack)
  change
    (canonicalStackAtoms machine stack
      (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)).drop
        (hint stack).1.val =
      (canonicalStackAtoms machine stack
        (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack)).drop
          (hint stack).2.1.val at hatoms
  rw [canonicalStackAtoms_drop, canonicalStackAtoms_drop] at hatoms
  exact canonicalStackAtoms_injective machine stack
    ((first.stk stack).drop (hint stack).1.val)
    ((next.stk stack).drop (hint stack).2.1.val)
    (supportedStackValue_of_mem_drop machine stack
      (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack) (hint
          stack).1.val)
    (supportedStackValue_of_mem_drop machine stack
      (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack) (hint
          stack).2.1.val)
    hatoms

theorem actualStep_of_stepAux
    (tm : Turing.FinTM2)
    (first next : tm.Cfg)
    (label : tm.Λ)
    (hlabel : first.l = some label)
    (haux : Turing.TM2.stepAux (tm.m label)
      first.var first.stk = next) :
    tm.step first = some next := by
  rcases first with ⟨sourceLabel, sourceState, sourceStacks⟩
  cases sourceLabel with
  | none =>
      simp only [reduceCtorEq] at hlabel
  | some sourceLabel =>
      have heq : sourceLabel = label := Option.some.inj hlabel
      subst sourceLabel
      exact congrArg some haux

private theorem actualStep_of_finite_script_and_windows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width)
    (hint : FiniteVerifierHint machine.tm)
    (hscript : scriptVerifierAllowed machine
      (scriptVerifierQueryOf machine first next
        hfirst hnext hint) = true)
    (hwindows : AllVerifierStackWindows machine width
      first next hfirst hnext hint) :
    machine.tm.step first = some next := by
  obtain ⟨label, hlabel, hcontrol, hstate, hchecks⟩ :=
    (scriptVerifierAllowed_iff machine
      (scriptVerifierQueryOf machine first next
        hfirst hnext hint)).mp hscript
  change first.l = some label at hlabel
  let heads : machine.tm.K → AtomBlock machine.tm :=
    fun stack => atomBlockAt machine.tm
      (canonicalStackAtoms machine stack
        (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)) 0
  let run := finiteHeadScriptRun machine label first.var heads
  change run.1 = next.l at hcontrol
  change run.2.1 = next.var at hstate
  have hstacks :
      scriptStacks first.stk run.2.2 = next.stk := by
    funext stack
    have hcheck := hchecks stack
    change
      (hint stack).1.val = run.2.2.dropped stack ∧
        (hint stack).2.1.val =
          (run.2.2.pushed stack).length ∧
        (decodedAtomBlock machine stack
          (atomBlockAt machine.tm
            (canonicalStackAtoms machine stack
              (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
                  0)).take
            (run.2.2.pushed stack).length =
          run.2.2.pushed stack at hcheck
    have hprefix := hcheck.2.2
    rw [decodedAtomBlock_canonical] at hprefix
    have hprefixBound :
        (run.2.2.pushed stack).length ≤ blockSize machine.tm := by
      have hfin := (hint stack).2.1.isLt
      omega
    simp only [List.take_take, Nat.min_eq_left hprefixBound]
      at hprefix
    have hsuffix := realStackSuffix_of_allVerifierWindows
      machine width first next hfirst hnext
      hfirstLength hnextLength hint hwindows stack
    rw [hcheck.1, hcheck.2.1] at hsuffix
    have hnextStack :
        next.stk stack = scriptStacks first.stk run.2.2 stack := by
      calc
        next.stk stack =
            (next.stk stack).take
                (run.2.2.pushed stack).length ++
              (next.stk stack).drop
                (run.2.2.pushed stack).length :=
          (List.take_append_drop
            (run.2.2.pushed stack).length (next.stk stack)).symm
        _ = run.2.2.pushed stack ++
              (first.stk stack).drop
                (run.2.2.dropped stack) := by
              rw [hprefix, ← hsuffix]
        _ = scriptStacks first.stk run.2.2 stack := rfl
    exact hnextStack.symm
  have hrun := finiteHeadScriptRun_eq_actual
    machine first hfirst label hlabel
  change
    run = executePrefixScript (machine.tm.m label)
      first.var first.stk (emptyPrefixScript machine.tm.Γ)
    at hrun
  have hexecution := executePrefixScript_correct
    (machine.tm.m label) first.var first.stk
    (emptyPrefixScript machine.tm.Γ)
  simp only [scriptStacks_empty] at hexecution
  rw [← hrun] at hexecution
  have hconfiguration :
      ({ l := run.1
         var := run.2.1
         stk := scriptStacks first.stk run.2.2 } : machine.tm.Cfg) =
        next :=
    configuration_eq_of_components machine.tm _ next
      hcontrol hstate hstacks
  exact actualStep_of_stepAux machine.tm first next label hlabel
    (hexecution.trans hconfiguration)

private theorem actualStep_has_finite_script_and_windows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hstep : machine.tm.step first = some next) :
    ∃ hint : FiniteVerifierHint machine.tm,
      scriptVerifierAllowed machine
          (scriptVerifierQueryOf machine first next
            hfirst hnext hint) = true ∧
        AllVerifierStackWindows machine width
          first next hfirst hnext hint := by
  cases hlabel : first.l with
  | none =>
      have hnone : machine.tm.step first = none := by
        rcases first with ⟨sourceLabel, sourceState, sourceStacks⟩
        cases sourceLabel with
        | none => rfl
        | some sourceLabel => simp only [reduceCtorEq] at hlabel
      rw [hnone] at hstep
      cases hstep
  | some label =>
      let heads : machine.tm.K → AtomBlock machine.tm :=
        fun stack => atomBlockAt machine.tm
          (canonicalStackAtoms machine stack
            (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack)) 0
      let run := finiteHeadScriptRun machine label first.var heads
      have hbounds (stack : machine.tm.K) :
          run.2.2.dropped stack < blockSize machine.tm ∧
            (run.2.2.pushed stack).length <
              blockSize machine.tm := by
        exact emptyPrefixScript_bounds machine.tm label first.var
          (finiteHeadConfiguration machine
            (some label, first.var) heads).stk stack
      let hint : FiniteVerifierHint machine.tm := fun stack =>
        (⟨run.2.2.dropped stack, (hbounds stack).1⟩,
          ⟨(run.2.2.pushed stack).length, (hbounds stack).2⟩,
          fun offset => paddedAtom
            (canonicalStackAtoms machine stack
              (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
                  offset.val)
      have hrun := finiteHeadScriptRun_eq_actual
        machine first hfirst label hlabel
      change
        run = executePrefixScript (machine.tm.m label)
          first.var first.stk (emptyPrefixScript machine.tm.Γ)
        at hrun
      have hexecution := executePrefixScript_correct
        (machine.tm.m label) first.var first.stk
        (emptyPrefixScript machine.tm.Γ)
      simp only [scriptStacks_empty] at hexecution
      rw [← hrun] at hexecution
      have hactual := actualStep_eq_stepAux
        machine.tm first next label hlabel hstep
      have hconfiguration :
          next =
            ({ l := run.1
               var := run.2.1
               stk := scriptStacks first.stk run.2.2 }
             : machine.tm.Cfg) :=
        hactual.symm.trans hexecution
      have hrunLabel : run.1 = next.l := by
        have h := congrArg
          (fun configuration : machine.tm.Cfg => configuration.l)
          hconfiguration
        exact h.symm
      have hrunState : run.2.1 = next.var := by
        have h := congrArg
          (fun configuration : machine.tm.Cfg => configuration.var)
          hconfiguration
        exact h.symm
      have hrunStacks (stack : machine.tm.K) :
          next.stk stack =
            scriptStacks first.stk run.2.2 stack := by
        have h := congrArg
          (fun configuration : machine.tm.Cfg =>
            configuration.stk stack) hconfiguration
        exact h
      have hscriptAllowed :
          scriptVerifierAllowed machine
            (scriptVerifierQueryOf machine first next
              hfirst hnext hint) = true := by
        apply (scriptVerifierAllowed_iff machine
          (scriptVerifierQueryOf machine first next
            hfirst hnext hint)).mpr
        refine ⟨label, hlabel, hrunLabel, hrunState, ?_⟩
        intro stack
        refine ⟨rfl, rfl, ?_⟩
        change
          (decodedAtomBlock machine stack
            (atomBlockAt machine.tm
              (canonicalStackAtoms machine stack
                (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
                    0)).take
              (run.2.2.pushed stack).length =
            run.2.2.pushed stack
        rw [decodedAtomBlock_canonical]
        have hle :
            (run.2.2.pushed stack).length ≤
              blockSize machine.tm :=
          Nat.le_of_lt (hbounds stack).2
        simp only [List.take_take, Nat.min_eq_left hle]
        rw [hrunStacks stack]
        simp only [scriptStacks, List.take_left']
      have hallWindows :
          AllVerifierStackWindows machine width
            first next hfirst hnext hint := by
        simp only [GapCVP.CLExactVerifierTransition.AllVerifierStackWindows, decide_eq_true_eq]
        intro stack
        have hfirstBound :
            (canonicalStackAtoms machine stack
              (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst
                  stack)).length ≤ width := by
          simpa only [canonicalStackAtoms_length] using hfirstLength stack
        have hrealSuffix :
            (first.stk stack).drop (run.2.2.dropped stack) =
              (next.stk stack).drop
                (run.2.2.pushed stack).length := by
          rw [hrunStacks stack]
          simp only [scriptStacks, List.drop_left']
        have hcanonicalSuffix := canonicalStackAtoms_common_suffix
          machine stack (first.stk stack) (next.stk stack)
          (stackAtomSupported_supportedValues machine first hfirst stack)
              (stackAtomSupported_supportedValues machine next hnext stack)
          (run.2.2.dropped stack)
          (run.2.2.pushed stack).length hrealSuffix
        have hprefix :
            PrefixHintCorrect machine.tm (hint stack)
              (canonicalStackAtoms machine stack
                (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
                    := by
          simp only [GapCVP.CLFiniteShiftWindows.PrefixHintCorrect, decide_eq_true_eq]
          intro offset hoffset
          rfl
        exact allStackShiftWindows_of_common_suffix
          machine.tm width
          (canonicalStackAtoms machine stack
            (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack))
          (canonicalStackAtoms machine stack
            (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack))
          hfirstBound (hint stack)
          (by simpa only [hint] using hcanonicalSuffix)
          hprefix
      exact ⟨hint, hscriptAllowed, hallWindows⟩

theorem actualStep_iff_finite_script_and_windows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width) :
    machine.tm.step first = some next ↔
      ∃ hint : FiniteVerifierHint machine.tm,
        scriptVerifierAllowed machine
            (scriptVerifierQueryOf machine first next
              hfirst hnext hint) = true ∧
          AllVerifierStackWindows machine width
            first next hfirst hnext hint := by
  constructor
  · exact actualStep_has_finite_script_and_windows
      machine width first next hfirst hnext hfirstLength
  · rintro ⟨hint, hscript, hwindows⟩
    exact actualStep_of_finite_script_and_windows
      machine width first next hfirst hnext
      hfirstLength hnextLength hint hscript hwindows

end CLGlobalTableauSimulation

namespace CLTableauSimulationCert

open Computability Turing GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLLocalWindows
open GapCVP.CLLocalRules GapCVP.CLExactStackRules GapCVP.CLCompleteLocalCompiler
open GapCVP.CLFiniteShiftWindows GapCVP.CLExactVerifierTransition GapCVP.CLLocalTableauCompiler
open GapCVP.CLGlobalTableauSimulation

/-- GapCVP reduction support. -/
def stackAtomsOfBlock (tm : Turing.FinTM2)
    (block : BlockCell tm)
    (stack : tm.K) : AtomBlock tm :=
  fun offset => (block offset).2.2.1 stack

/-- GapCVP reduction support. -/
def machineControlOfBlock (tm : Turing.FinTM2)
    (block : BlockCell tm) : Option (Option tm.Λ × tm.σ) :=
  match (block ⟨0, blockSize_pos tm⟩).2.1 with
  | none => none
  | some (label, state) =>
      some
        ((if (block ⟨0, blockSize_pos tm⟩).2.2.2 then
            some label
          else
            none), state)

/-- GapCVP reduction support. -/
abbrev ScriptBlockCell (tm : Turing.FinTM2) :=
  SummaryBlockCell tm × FiniteVerifierHint tm × Bool

instance instFintypeScriptBlockCell
    (tm : Turing.FinTM2) : Fintype (ScriptBlockCell tm) := by
  infer_instance

/-- Internal support shared across GapCVP continuation modules. -/
abbrev ScriptBlockRow (tm : Turing.FinTM2) (width : ℕ) :=
  Fin (width + 1) → ScriptBlockCell tm

/-- GapCVP reduction support. -/
abbrev ScriptBlockWindow (tm : Turing.FinTM2) :=
  ScriptBlockCell tm × ScriptBlockCell tm ×
    ScriptBlockCell tm × ScriptBlockCell tm

/-- GapCVP reduction support. -/
def scriptBlockWindowAt (tm : Turing.FinTM2)
    (width : ℕ)
    (first next : ScriptBlockRow tm width)
    (index : Fin (width + 1)) : ScriptBlockWindow tm :=
  (first (leftBlock width index),
    first index,
    first (rightBlock width index),
    next index)

/-- GapCVP reduction support. -/
def canonicalVerifyingRow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration) :
    CellRow machine.tm width :=
  fun index =>
    (certificatePhase certificate index.val,
      some (configurationControl machine.tm configuration),
      fun stack => paddedAtom
        (canonicalStackAtoms machine stack
          (configuration.stk stack) (stackAtomSupported_supportedValues machine configuration
              hsupported stack)) index.val,
      configuration.l.isSome)

theorem stackAtomsOfBlock_pack_canonical
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration)
    (hstackLength : ∀ stack : machine.tm.K,
      (configuration.stk stack).length ≤ width)
    (index : Fin (width + 1))
    (stack : machine.tm.K) :
    stackAtomsOfBlock machine.tm
        (packRow machine.tm width
          (canonicalVerifyingRow machine width
            certificate configuration hsupported) index) stack =
      atomBlockAt machine.tm
        (canonicalStackAtoms machine stack
          (configuration.stk stack) (stackAtomSupported_supportedValues machine configuration
              hsupported stack)) index.val := by
  funext offset
  by_cases hposition :
      index.val * blockSize machine.tm + offset.val < width + 1
  · simp only [stackAtomsOfBlock, packRow, hposition, ↓reduceDIte, canonicalVerifyingRow,
      atomBlockAt]
  · have hbound :
        (canonicalStackAtoms machine stack
          (configuration.stk stack) (stackAtomSupported_supportedValues machine configuration
              hsupported stack)).length ≤
            index.val * blockSize machine.tm + offset.val := by
        have hlength := hstackLength stack
        rw [canonicalStackAtoms_length]
        omega
    simp only [stackAtomsOfBlock, packRow, hposition, ↓reduceDIte, blankCell, atomBlockAt,
        paddedAtom_none_of_length_le machine.tm
            (canonicalStackAtoms machine stack (configuration.stk stack)
              (stackAtomSupported_supportedValues machine configuration hsupported stack))
            (index.val * blockSize machine.tm + offset.val) hbound]

/-- GapCVP reduction support. -/
def canonicalScriptBlockRow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration)
    (hint : FiniteVerifierHint machine.tm) :
    ScriptBlockRow machine.tm width :=
  fun index =>
    ((packRow machine.tm width
        (canonicalVerifyingRow machine width certificate
          configuration hsupported) index,
      packRow machine.tm width
        (canonicalVerifyingRow machine width certificate
          configuration hsupported) 0),
      hint, decide (index.val = 0))

theorem machineControlOfBlock_pack_canonical
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (configuration : machine.tm.Cfg)
    (hsupported : StackAtomSupported machine configuration) :
    machineControlOfBlock machine.tm
      (packRow machine.tm width
        (canonicalVerifyingRow machine width
          certificate configuration hsupported) 0) =
      some (configuration.l, configuration.var) := by
  cases hlabel : configuration.l with
  | none =>
      simp only [machineControlOfBlock, packRow, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul,
          add_zero,
          Order.lt_add_one_iff, zero_le, ↓reduceDIte, canonicalVerifyingRow, configurationControl,
              hlabel, Option.getD_none,
          Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  | some label =>
      simp only [machineControlOfBlock, packRow, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul,
          add_zero,
          Order.lt_add_one_iff, zero_le, ↓reduceDIte, canonicalVerifyingRow, configurationControl,
              hlabel, Option.getD_some,
          Option.isSome_some, ↓reduceIte]

/-- GapCVP reduction support. -/
def scriptQueryOfBlockWindow
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : ScriptBlockWindow machine.tm) :
    Option (ScriptVerifierQuery machine.tm) :=
  match
    machineControlOfBlock machine.tm window.2.1.1.2,
    machineControlOfBlock machine.tm window.2.2.2.1.2
  with
  | some firstControl, some nextControl =>
      some
        ((firstControl,
          (fun stack => stackAtomsOfBlock machine.tm
            window.2.1.1.2 stack), nextControl),
          (fun stack => stackAtomsOfBlock machine.tm
            window.2.2.2.1.2 stack),
          window.2.1.2.1)
  | _, _ => none

/-- GapCVP reduction support. -/
def stackWindowOfScriptBlock
    (tm : Turing.FinTM2)
    (window : ScriptBlockWindow tm)
    (stack : tm.K) : StackShiftWindow tm :=
  (stackAtomsOfBlock tm window.1.1.1 stack,
    stackAtomsOfBlock tm window.2.1.1.1 stack,
    stackAtomsOfBlock tm window.2.2.1.1.1 stack,
    stackAtomsOfBlock tm window.2.2.2.1.1 stack,
    window.2.1.2.2)

/-- GapCVP reduction support. -/
noncomputable def ScriptBlockCoherent (tm : Turing.FinTM2)
    (window : ScriptBlockWindow tm) : Bool :=
  @decide (
  window.1.1.2 = window.2.1.1.2 ∧
    window.2.2.1.1.2 = window.2.1.1.2 ∧
    window.1.2.1 = window.2.1.2.1 ∧
    window.2.2.1.2.1 = window.2.1.2.1 ∧
    window.2.1.2.2 = window.2.2.2.2.2
  ) (Classical.propDecidable _)
/-- GapCVP reduction support. -/
def scriptBlockAllowed
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : ScriptBlockWindow machine.tm) : Bool := by
  classical
  exact match scriptQueryOfBlockWindow machine window with
    | none => false
    | some query =>
        decide
          (ScriptBlockCoherent machine.tm window ∧
            scriptVerifierAllowed machine query = true ∧
            ∀ stack : machine.tm.K,
              stackShiftAllowed machine.tm
                (window.2.1.2.1 stack)
                (stackWindowOfScriptBlock machine.tm
                  window stack) = true)

theorem scriptBlockAllowed_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (window : ScriptBlockWindow machine.tm) :
    scriptBlockAllowed machine window = true ↔
      ScriptBlockCoherent machine.tm window ∧
        ∃ query : ScriptVerifierQuery machine.tm,
          scriptQueryOfBlockWindow machine window = some query ∧
          scriptVerifierAllowed machine query = true ∧
          ∀ stack : machine.tm.K,
            stackShiftAllowed machine.tm
              (window.2.1.2.1 stack)
              (stackWindowOfScriptBlock machine.tm
                window stack) = true := by
  classical
  cases hquery : scriptQueryOfBlockWindow machine window with
  | none => simp only [scriptBlockAllowed, hquery, Bool.false_eq_true, reduceCtorEq, false_and,
      exists_false, and_false]
  | some query => simp only [scriptBlockAllowed, hquery, Bool.decide_and, Bool.decide_eq_true,
      Bool.and_eq_true,
                      decide_eq_true_eq, Option.some.injEq, exists_eq_left']

private theorem canonicalScriptBlockWindow_coherent
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (index : Fin (width + 1)) :
    ScriptBlockCoherent machine.tm
      (scriptBlockWindowAt machine.tm width
        (canonicalScriptBlockRow machine width certificate
          first hfirst firstHint)
        (canonicalScriptBlockRow machine width certificate
          next hnext nextHint)
        index) := by
  simp only [ScriptBlockCoherent, scriptBlockWindowAt, canonicalScriptBlockRow,
      Fin.val_eq_zero_iff, and_self,
      decide_true]

private theorem scriptQueryOfBlockWindow_canonical
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (index : Fin (width + 1)) :
    scriptQueryOfBlockWindow machine
        (scriptBlockWindowAt machine.tm width
          (canonicalScriptBlockRow machine width certificate
            first hfirst firstHint)
          (canonicalScriptBlockRow machine width certificate
            next hnext nextHint)
          index) =
      some (scriptVerifierQueryOf machine first next
        hfirst hnext firstHint) := by
  simp only [scriptQueryOfBlockWindow, scriptBlockWindowAt, canonicalScriptBlockRow,
      Fin.val_eq_zero_iff,
      machineControlOfBlock_pack_canonical, scriptVerifierQueryOf, finiteHeadQueryOf,
          Option.some.injEq, Prod.mk.injEq,
      and_true, true_and]
  constructor
  · funext stack
    exact stackAtomsOfBlock_pack_canonical machine width certificate
      first hfirst hfirstLength 0 stack
  · funext stack
    exact stackAtomsOfBlock_pack_canonical machine width certificate
      next hnext hnextLength 0 stack

private theorem stackWindowOfScriptBlock_canonical
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width)
    (firstHint nextHint : FiniteVerifierHint machine.tm)
    (index : Fin (width + 1))
    (stack : machine.tm.K) :
    stackWindowOfScriptBlock machine.tm
        (scriptBlockWindowAt machine.tm width
          (canonicalScriptBlockRow machine width certificate
            first hfirst firstHint)
          (canonicalScriptBlockRow machine width certificate
            next hnext nextHint)
          index) stack =
      stackShiftWindowAt machine.tm width
        (canonicalStackAtoms machine stack
          (first.stk stack) (stackAtomSupported_supportedValues machine first hfirst stack))
        (canonicalStackAtoms machine stack
          (next.stk stack) (stackAtomSupported_supportedValues machine next hnext stack)) index
              := by
  simp only [stackWindowOfScriptBlock, scriptBlockWindowAt,
    canonicalScriptBlockRow, stackShiftWindowAt]
  rw [stackAtomsOfBlock_pack_canonical machine width certificate
    first hfirst hfirstLength (leftBlock width index) stack]
  rw [stackAtomsOfBlock_pack_canonical machine width certificate
    first hfirst hfirstLength index stack]
  rw [stackAtomsOfBlock_pack_canonical machine width certificate
    first hfirst hfirstLength (rightBlock width index) stack]
  rw [stackAtomsOfBlock_pack_canonical machine width certificate
    next hnext hnextLength index stack]

theorem canonicalScriptBlockWindows_iff
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width)
    (firstHint nextHint : FiniteVerifierHint machine.tm) :
    (∀ index : Fin (width + 1),
      scriptBlockAllowed machine
        (scriptBlockWindowAt machine.tm width
          (canonicalScriptBlockRow machine width certificate
            first hfirst firstHint)
          (canonicalScriptBlockRow machine width certificate
            next hnext nextHint)
          index) = true) ↔
      scriptVerifierAllowed machine
          (scriptVerifierQueryOf machine first next
            hfirst hnext firstHint) = true ∧
        AllVerifierStackWindows machine width
          first next hfirst hnext firstHint := by
  constructor
  · intro hallowed
    have hzero :=
      (scriptBlockAllowed_iff machine
        (scriptBlockWindowAt machine.tm width
          (canonicalScriptBlockRow machine width certificate
            first hfirst firstHint)
          (canonicalScriptBlockRow machine width certificate
            next hnext nextHint) 0)).mp (hallowed 0)
    obtain ⟨_, query, hquery, hscript, _⟩ := hzero
    rw [scriptQueryOfBlockWindow_canonical machine width
      certificate first next hfirst hnext
      hfirstLength hnextLength firstHint nextHint 0] at hquery
    have hqueryEq :
        scriptVerifierQueryOf machine first next
          hfirst hnext firstHint = query :=
      Option.some.inj hquery
    subst query
    refine ⟨hscript, ?_⟩
    apply @decide_eq_true _ (Classical.propDecidable _)
    intro stack
    apply @decide_eq_true _ (Classical.propDecidable _)
    intro index
    have hlocal :=
      (scriptBlockAllowed_iff machine
        (scriptBlockWindowAt machine.tm width
          (canonicalScriptBlockRow machine width certificate
            first hfirst firstHint)
          (canonicalScriptBlockRow machine width certificate
            next hnext nextHint) index)).mp (hallowed index)
    obtain ⟨_, _, _, _, hstack⟩ := hlocal
    have hchecked := hstack stack
    change
      stackShiftAllowed machine.tm (firstHint stack)
        (stackWindowOfScriptBlock machine.tm
          (scriptBlockWindowAt machine.tm width
            (canonicalScriptBlockRow machine width certificate
              first hfirst firstHint)
            (canonicalScriptBlockRow machine width certificate
              next hnext nextHint) index) stack) = true
      at hchecked
    rw [stackWindowOfScriptBlock_canonical machine width
      certificate first next hfirst hnext
      hfirstLength hnextLength firstHint nextHint
      index stack] at hchecked
    exact hchecked
  · rintro ⟨hscript, hwindows⟩ index
    have hwindows' :=
      @of_decide_eq_true _ (Classical.propDecidable _) hwindows
    apply (scriptBlockAllowed_iff machine
      (scriptBlockWindowAt machine.tm width
        (canonicalScriptBlockRow machine width certificate
          first hfirst firstHint)
        (canonicalScriptBlockRow machine width certificate
          next hnext nextHint) index)).mpr
    refine ⟨canonicalScriptBlockWindow_coherent
      machine width certificate first next hfirst hnext
      firstHint nextHint index,
      scriptVerifierQueryOf machine first next
        hfirst hnext firstHint,
      scriptQueryOfBlockWindow_canonical
        machine width certificate first next hfirst hnext
        hfirstLength hnextLength firstHint nextHint index,
      hscript, ?_⟩
    intro stack
    change
      stackShiftAllowed machine.tm (firstHint stack)
        (stackWindowOfScriptBlock machine.tm
          (scriptBlockWindowAt machine.tm width
            (canonicalScriptBlockRow machine width certificate
              first hfirst firstHint)
            (canonicalScriptBlockRow machine width certificate
              next hnext nextHint) index) stack) = true
    rw [stackWindowOfScriptBlock_canonical machine width
      certificate first next hfirst hnext
      hfirstLength hnextLength firstHint nextHint index stack]
    exact (@of_decide_eq_true _ (Classical.propDecidable _)
      (hwindows' stack)) index

theorem actualStep_iff_canonical_block_windows
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (width : ℕ)
    (certificate : List Bool)
    (first next : machine.tm.Cfg)
    (hfirst : StackAtomSupported machine first)
    (hnext : StackAtomSupported machine next)
    (hfirstLength : ∀ stack : machine.tm.K,
      (first.stk stack).length ≤ width)
    (hnextLength : ∀ stack : machine.tm.K,
      (next.stk stack).length ≤ width) :
    machine.tm.step first = some next ↔
      ∃ (firstHint nextHint : FiniteVerifierHint machine.tm),
        ∀ index : Fin (width + 1),
          scriptBlockAllowed machine
            (scriptBlockWindowAt machine.tm width
              (canonicalScriptBlockRow machine width certificate
                first hfirst firstHint)
              (canonicalScriptBlockRow machine width certificate
                next hnext nextHint) index) = true := by
  constructor
  · intro hstep
    obtain ⟨hint, hscript, hwindows⟩ :=
      (actualStep_iff_finite_script_and_windows machine width
        first next hfirst hnext hfirstLength hnextLength).mp hstep
    refine ⟨hint, hint, ?_⟩
    exact (canonicalScriptBlockWindows_iff machine width
      certificate first next hfirst hnext
      hfirstLength hnextLength hint hint).mpr
      ⟨hscript, hwindows⟩
  · rintro ⟨firstHint, nextHint, hwindows⟩
    obtain ⟨hscript, hstacks⟩ :=
      (canonicalScriptBlockWindows_iff machine width
        certificate first next hfirst hnext
        hfirstLength hnextLength firstHint nextHint).mp hwindows
    exact (actualStep_iff_finite_script_and_windows machine width
      first next hfirst hnext hfirstLength hnextLength).mpr
      ⟨firstHint, hscript, hstacks⟩

end CLTableauSimulationCert

namespace CLFullTableauEmitter

open Computability Turing GapCVP.CLLocalWindows GapCVP.CLCompleteLocalCompiler
open GapCVP.CLExactVerifierTransition GapCVP.CLTableauSimulationCert

private def defaultSingleStackHint (tm : Turing.FinTM2) :
    SingleStackHint tm :=
  (⟨0, blockSize_pos tm⟩,
    ⟨0, blockSize_pos tm⟩,
    fun _ => none)

/-- GapCVP reduction support. -/
def defaultVerifierHint (tm : Turing.FinTM2) :
    FiniteVerifierHint tm :=
  fun _ => defaultSingleStackHint tm

/-- Internal support shared across GapCVP continuation modules. -/
def defaultScriptBlockCell (tm : Turing.FinTM2) :
    ScriptBlockCell tm :=
  (((fun _ => blankCell tm),
      (fun _ => blankCell tm)),
    defaultVerifierHint tm, false)

end CLFullTableauEmitter

namespace CLVerifierPhaseCert

open Computability Turing GapCVP.CLVerifier GapCVP.CLNondeterminism
open GapCVP.CLPushAlphabet GapCVP.CLStackSupport GapCVP.CLCellRowBounds

theorem configurationTrace_stackAtomSupported
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    (x certificate : List Bool)
    {output : List (machine.tm.Γ machine.tm.k₁)}
    {steps : ℕ}
    (trace : ConfigurationTrace machine.tm
      (verifierInput machine x certificate) output steps) :
    ∀ time : Fin (steps + 1),
      StackAtomSupported machine (trace.configuration time) := by
  have hprefix : ∀ (time : ℕ) (htime : time ≤ steps),
      StackAtomSupported machine
        (trace.configuration ⟨time, by omega⟩) := by
    intro time htime
    induction time with
    | zero =>
        have hzero :
            trace.configuration (⟨0, by omega⟩ : Fin (steps + 1)) =
              Turing.initList machine.tm
                (verifierInput machine x certificate) := by
          simpa only [Fin.zero_eta] using trace.initial
        rw [hzero]
        exact initialConfiguration_stackAtomSupported
          machine x certificate
    | succ time ih =>
        have hprior : time ≤ steps := by omega
        have hlt : time < steps := by omega
        exact step_stackAtomSupported machine
          (trace.configuration ⟨time, by omega⟩)
          (trace.configuration ⟨time + 1, by omega⟩)
          (trace.transition ⟨time, hlt⟩)
          (ih hprior)
  intro time
  simpa only [Fin.eta] using hprefix time.val (by omega)

theorem acceptedExecution_stack_length_le_rowWidth
    (bound : Polynomial ℕ)
    {verifier : List Bool × List Bool → Bool}
    (machine : VerifierTM verifier)
    {x : List Bool}
    (execution : AcceptedExecution bound machine x)
    (time : Fin (execution.steps + 1))
    (stack : machine.tm.K) :
    ((execution.trace.configuration time).stk stack).length ≤
      rowWidth bound machine x := by
  have htime : time.val ≤
      (guessTimePolynomial bound machine).eval x.length := by
    have hstep : time.val ≤ execution.steps := by omega
    have hwitness := execution.steps_le
    simp only [guessTimePolynomial, Polynomial.eval_add,
      Polynomial.eval_one]
    omega
  calc
    ((execution.trace.configuration time).stk stack).length ≤
        (verifierInput machine x execution.certificate).length +
          time.val * TMComposition.maxPushPerStep machine.tm :=
      execution.trace.stack_length_le time stack
    _ ≤ (x.length + bound.eval x.length) +
          (guessTimePolynomial bound machine).eval x.length *
            TMComposition.maxPushPerStep machine.tm := by
      rw [verifierInput_length]
      exact Nat.add_le_add
        (Nat.add_le_add_left execution.certificate_le x.length)
        (Nat.mul_le_mul_right
          (TMComposition.maxPushPerStep machine.tm) htime)
    _ ≤ rowWidth bound machine x := by
      simp only [rowWidth, nondeterministicTableauDimensionPolynomial,
        Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
      omega

end CLVerifierPhaseCert

namespace CLCompleteVerifierSimulation

open Computability Turing GapCVP.CL GapCVP.CLVerifier GapCVP.CLBoundedStates
open GapCVP.CLPushAlphabet GapCVP.CLCellRows GapCVP.CLCellRowBounds GapCVP.CLLocalWindows
open GapCVP.CLExactLocalRules GapCVP.CLExactStackRules GapCVP.CLExactVerifierTransition
open GapCVP.CLTableauSimulationCert GapCVP.CLFullTableauEmitter

/-- GapCVP reduction support. -/
inductive PairedInputTag where
  | bit (value : Bool ⊕ Bool)
  | marker
  | blank
  deriving DecidableEq, Fintype

/-- GapCVP reduction support. -/
def pairedInputTagAt (x certificate : List Bool)
    (index : ℕ) : PairedInputTag :=
  match (pairBitEncoding (x, certificate))[index]? with
  | some value => .bit value
  | none =>
      if index = (pairBitEncoding (x, certificate)).length then
        .marker
      else
        .blank

@[simp] theorem pairedInputTagAt_marker
    (x certificate : List Bool) :
    pairedInputTagAt x certificate (x.length + certificate.length) =
      .marker := by
  simp only [pairedInputTagAt, pairBitEncoding_apply, List.length_append, List.length_map,
      lt_self_iff_false,
    not_false_eq_true, getElem?_neg, ↓reduceIte]

theorem pairBitEncoding_append_guess
    (x certificate : List Bool) (bit : Bool) :
    pairBitEncoding (x, certificate ++ [bit]) =
      pairBitEncoding (x, certificate) ++ [Sum.inr bit] := by
  simp only [pairBitEncoding_apply, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc]

end CLCompleteVerifierSimulation

end GapCVP

end
