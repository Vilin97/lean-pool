/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# Coherent-gap certificates

This file formalizes the algebraic certificate mechanism behind normalized
chamber rigidity for a fixed coherent Boolean term order.  The motivating
order is the Conway--Guy order from:

* Tom Bohman, "A sum packing problem of Erdős and the Conway--Guy sequence,"
  Proceedings of the AMS 124 (1996), 3627--3636.

The definitions below do not assume Bohman's distinct-subset-sum theorem.
That theorem is needed only to identify integral unit relations with
consecutive gaps in the Conway--Guy subset-sum order.

The open-problem context and the exact boundary of this formalization are
recorded separately in the Construct research notes.
-/

open scoped BigOperators

namespace BooleanIsoperimetry.CoherentGap

/-- An integer relation in dimension `n`. -/
abbrev Relation (n : ℕ) := Fin n → ℤ

/-- The coordinate sum of an integer relation. -/
def coordinateSum {n : ℕ} (relation : Relation n) : ℤ :=
  ∑ i, relation i

/-- The scalar product of an integer relation with an integer weight row. -/
def dot {n : ℕ} (relation weights : Relation n) : ℤ :=
  ∑ i, relation i * weights i

/-- The standard coordinate vector. -/
def basis {n : ℕ} (coordinate : Fin n) : Relation n :=
  fun i => if i = coordinate then 1 else 0

/-- A relation whose entries and coordinate sum lie in `{-1, 0, 1}` and
whose value on the weight row is one. -/
def IsLiftableUnit {n : ℕ} (weights relation : Relation n) : Prop :=
  (∀ i, relation i = -1 ∨ relation i = 0 ∨ relation i = 1) ∧
    dot relation weights = 1 ∧
    (coordinateSum relation = -1 ∨
      coordinateSum relation = 0 ∨ coordinateSum relation = 1)

/-- Pointwise sum of a list of relations. -/
def aggregate {n : ℕ} (relations : List (Relation n)) : Relation n :=
  relations.sum

/-- A nonnegative integral dual certificate, represented as a list so that
multiplicity is the coefficient of a relation. -/
structure Certificate {n : ℕ} (weights target : Relation n) where
  /-- Relations listed with their certificate multiplicities. -/
  relations : List (Relation n)
  /-- Every listed relation is a liftable unit relation. -/
  valid : ∀ relation ∈ relations, IsLiftableUnit weights relation
  /-- The listed relations sum to the certificate target. -/
  target_eq : aggregate relations = target

lemma coordinateSum_add {n : ℕ} (first second : Relation n) :
    coordinateSum (first + second) =
      coordinateSum first + coordinateSum second := by
  simp [coordinateSum, Finset.sum_add_distrib]

lemma dot_add {n : ℕ} (first second weights : Relation n) :
    dot (first + second) weights = dot first weights + dot second weights := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_aggregate {n : ℕ} (relations : List (Relation n)) (weights : Relation n) :
    dot (aggregate relations) weights =
      (relations.map fun relation => dot relation weights).sum := by
  induction relations with
  | nil =>
      simp [aggregate, dot]
  | cons relation relations inductionHypothesis =>
      change dot (relation + aggregate relations) weights =
        dot relation weights +
          (relations.map fun tailRelation => dot tailRelation weights).sum
      rw [dot_add, inductionHypothesis]

@[simp]
lemma dot_basis {n : ℕ} (coordinate : Fin n) (weights : Relation n) :
    dot (basis coordinate) weights = weights coordinate := by
  classical
  simp [dot, basis]

/-- The mass of a certificate equals the value of its target on the weights. -/
lemma Certificate.length_eq_dot_target {n : ℕ} {weights target : Relation n}
    (certificate : Certificate weights target) :
    (certificate.relations.length : ℤ) = dot target weights := by
  have hmass : ∀ relations : List (Relation n),
      (∀ relation ∈ relations, IsLiftableUnit weights relation) →
        (relations.map fun relation => dot relation weights).sum =
          (relations.length : ℤ) := by
    intro relations
    induction relations with
    | nil =>
        intro
        simp
    | cons relation relations inductionHypothesis =>
        intro hvalid
        have hunit := (hvalid relation List.mem_cons_self).2.1
        have htail :
            ∀ tailRelation ∈ relations,
              IsLiftableUnit weights tailRelation := by
          intro tailRelation htailRelation
          exact hvalid tailRelation (List.mem_cons_of_mem relation htailRelation)
        simp only [List.map_cons, List.sum_cons, hunit, List.length_cons,
          Nat.cast_add, Nat.cast_one]
        simpa [add_comm] using inductionHypothesis htail
  have hcertificateMass := hmass certificate.relations certificate.valid
  calc
    (certificate.relations.length : ℤ) =
        (certificate.relations.map fun relation => dot relation weights).sum :=
      hcertificateMass.symm
    _ = dot (aggregate certificate.relations) weights :=
      (dot_aggregate certificate.relations weights).symm
    _ = dot target weights := congrArg (fun relation => dot relation weights)
      certificate.target_eq

/-- A one-relation certificate. -/
def Certificate.singleton {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) :
    Certificate weights relation where
  relations := [relation]
  valid := by simpa
  target_eq := by simp [aggregate]

/-- Add two certificates. -/
def Certificate.add {n : ℕ} {weights firstTarget secondTarget : Relation n}
    (first : Certificate weights firstTarget)
    (second : Certificate weights secondTarget) :
    Certificate weights (firstTarget + secondTarget) where
  relations := first.relations ++ second.relations
  valid := by
    intro relation hrelation
    rcases List.mem_append.mp hrelation with hfirst | hsecond
    · exact first.valid relation hfirst
    · exact second.valid relation hsecond
  target_eq := by
    unfold aggregate
    rw [List.sum_append]
    simpa only [aggregate] using
      congrArg₂ (fun firstRelation secondRelation =>
        firstRelation + secondRelation) first.target_eq second.target_eq

/-- Reinterpret the target of a certificate along an equality. -/
def Certificate.castTarget {n : ℕ} {weights firstTarget secondTarget : Relation n}
    (certificate : Certificate weights firstTarget)
    (htarget : firstTarget = secondTarget) :
    Certificate weights secondTarget := by
  subst secondTarget
  exact certificate

/-- The sum of a list of dependently packaged certificates. -/
def Certificate.sum {n : ℕ} {weights : Relation n} :
    (certificates : List (Σ target, Certificate weights target)) →
      Certificate weights (certificates.map Sigma.fst).sum
  | [] =>
      { relations := []
        valid := by simp
        target_eq := by simp [aggregate] }
  | ⟨target, certificate⟩ :: certificates => by
      simpa using certificate.add (Certificate.sum certificates)

/-- Add one coordinate at the front of a weight row. -/
def extendWeights {n : ℕ} (head : ℤ) (weights : Relation n) : Relation (n + 1) :=
  Fin.cases head fun i => head + weights i

/-- Lift a relation by adding the negative coordinate sum at the front. -/
def lift {n : ℕ} (relation : Relation n) : Relation (n + 1) :=
  Fin.cases (-coordinateSum relation) relation

@[simp]
lemma coordinateSum_lift {n : ℕ} (relation : Relation n) :
    coordinateSum (lift relation) = 0 := by
  simp [coordinateSum, lift, Fin.sum_univ_succ]

lemma lift_add {n : ℕ} (first second : Relation n) :
    lift (first + second) = lift first + lift second := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [lift, coordinateSum_add, add_comm]
  · simp [lift]

lemma lift_aggregate {n : ℕ} (relations : List (Relation n)) :
    aggregate (relations.map lift) = lift (aggregate relations) := by
  induction relations with
  | nil =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;>
        simp [aggregate, lift, coordinateSum]
  | cons relation relations inductionHypothesis =>
      change lift relation + aggregate (relations.map lift) =
        lift (relation + aggregate relations)
      rw [inductionHypothesis, lift_add]

/-- Iterate the dimension lift. -/
def iteratedLift {n : ℕ} (relation : Relation n) :
    (steps : ℕ) → Relation (n + steps)
  | 0 => relation
  | steps + 1 => lift (iteratedLift relation steps)

/-- Transport a relation through an equality of dimensions. -/
def castRelation {firstDimension secondDimension : ℕ}
    (hdimension : firstDimension = secondDimension)
    (relation : Relation firstDimension) : Relation secondDimension := by
  subst secondDimension
  exact relation

lemma dot_lift_extendWeights {n : ℕ} (head : ℤ)
    (weights relation : Relation n) :
    dot (lift relation) (extendWeights head weights) = dot relation weights := by
  simp only [dot, lift, extendWeights, Fin.sum_univ_succ, Fin.cases_zero,
    Fin.cases_succ, neg_mul, Finset.sum_add_distrib, mul_add]
  rw [← Finset.sum_mul]
  simp [coordinateSum]

lemma IsLiftableUnit.lift {n : ℕ} {weights relation : Relation n}
    (hrelation : IsLiftableUnit weights relation) (head : ℤ) :
    IsLiftableUnit (extendWeights head weights) (lift relation) := by
  refine ⟨?_, dot_lift_extendWeights head weights relation ▸ hrelation.2.1, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rcases hrelation.2.2 with hsum | hsum | hsum
      · right
        right
        change -coordinateSum relation = 1
        rw [hsum]
        norm_num
      · right
        left
        change -coordinateSum relation = 0
        rw [hsum]
        norm_num
      · left
        change -coordinateSum relation = -1
        rw [hsum]
    · change relation j = -1 ∨ relation j = 0 ∨ relation j = 1
      exact hrelation.1 j
  · simp [coordinateSum_lift]

/-- Lift every relation in a certificate by one dimension. -/
def Certificate.lift {n : ℕ} {weights target : Relation n}
    (certificate : Certificate weights target) (head : ℤ) :
    Certificate (extendWeights head weights) (lift target) where
  relations := certificate.relations.map CoherentGap.lift
  valid := by
    intro relation hrelation
    obtain ⟨source, hsource, rfl⟩ := List.mem_map.mp hrelation
    exact (certificate.valid source hsource).lift head
  target_eq := by
    rw [lift_aggregate, certificate.target_eq]

@[simp]
lemma lift_basis {n : ℕ} (coordinate : Fin n) :
    lift (basis coordinate) =
      basis coordinate.succ - basis (0 : Fin (n + 1)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have hne : (0 : Fin (n + 1)) ≠ coordinate.succ := by
      intro heq
      have hval := congrArg Fin.val heq
      simp at hval
    simp [lift, coordinateSum, basis, hne]
  · simp [lift, basis]

/-- A tower of rows obtained by adjoining one new positive-linear coordinate
at the front at each dimension. -/
structure WeightTower where
  /-- The reference row in each dimension. -/
  weights : (n : ℕ) → Relation n
  /-- The coordinate adjoined when passing from dimension `n` to `n + 1`. -/
  head : ℕ → ℤ
  /-- Every row is obtained from the preceding row by the dimension lift. -/
  step : ∀ n, weights (n + 1) = extendWeights (head n) (weights n)

/-- Transport a certificate through one step of a weight tower. -/
def WeightTower.liftCertificate (tower : WeightTower) {n : ℕ}
    {target : Relation n} (certificate : Certificate (tower.weights n) target) :
    Certificate (tower.weights (n + 1)) (lift target) := by
  rw [tower.step]
  exact certificate.lift (tower.head n)

/-- Repeatedly transport a certificate through a weight tower. -/
def WeightTower.iteratedLiftCertificate (tower : WeightTower) {n : ℕ}
    {target : Relation n} (certificate : Certificate (tower.weights n) target) :
    (steps : ℕ) →
      Certificate (tower.weights (n + steps)) (iteratedLift target steps)
  | 0 => certificate
  | steps + 1 =>
      tower.liftCertificate
        (tower.iteratedLiftCertificate certificate steps)

/-- Reinterpret a certificate along an equality of dimensions. -/
def Certificate.castDimension {firstDimension secondDimension : ℕ}
    (tower : WeightTower) {target : Relation firstDimension}
    (certificate : Certificate (tower.weights firstDimension) target)
    (hdimension : firstDimension = secondDimension) :
    Certificate (tower.weights secondDimension)
      (castRelation hdimension target) := by
  subst secondDimension
  exact certificate

/-- One correction in the strong-induction construction of a first-coordinate
certificate. -/
structure Correction (dimension : ℕ) where
  /-- The source dimension is `sourceOffset + 1`. -/
  sourceOffset : ℕ
  /-- The smaller-dimensional coordinate whose certificate is lifted. -/
  sourceCoordinate : Fin (sourceOffset + 1)
  /-- Number of dimension lifts. -/
  steps : ℕ
  /-- Every correction comes from a strictly smaller dimension. -/
  steps_pos : 0 < steps
  /-- Lifting reaches the target dimension exactly. -/
  dimension_eq : (sourceOffset + 1) + steps = dimension

lemma Correction.sourceDimension_lt {dimension : ℕ}
    (correction : Correction dimension) :
    correction.sourceOffset + 1 < dimension := by
  calc
    correction.sourceOffset + 1 <
        (correction.sourceOffset + 1) + correction.steps :=
      Nat.lt_add_of_pos_right correction.steps_pos
    _ = dimension := correction.dimension_eq

lemma Correction.sourceOffset_lt {offset : ℕ}
    (correction : Correction (offset + 2)) :
    correction.sourceOffset < offset + 1 := by
  have := correction.sourceDimension_lt
  omega

/-- The target contributed by a lifted smaller-dimensional basis certificate. -/
def Correction.target {dimension : ℕ}
    (correction : Correction dimension) : Relation dimension :=
  castRelation correction.dimension_eq
    (iteratedLift (basis correction.sourceCoordinate) correction.steps)

/-- Realize a correction from a certificate in its source dimension. -/
def Correction.liftCertificate {dimension : ℕ}
    (correction : Correction dimension) (tower : WeightTower)
    (certificate : Certificate (tower.weights (correction.sourceOffset + 1))
      (basis correction.sourceCoordinate)) :
    Certificate (tower.weights dimension) correction.target := by
  unfold Correction.target
  exact Certificate.castDimension tower
    (tower.iteratedLiftCertificate certificate correction.steps)
    correction.dimension_eq

/-- Exact data needed at each dimension for the principal-relation
strong-induction step.  Every load-bearing input is a field: the principal
relation must be a liftable unit relation, and its sum with the explicitly
listed lifted corrections must be the first basis vector. -/
structure FirstCoordinateRecurrence (tower : WeightTower) where
  /-- First-coordinate certificate in dimension one. -/
  base : Certificate (tower.weights 1) (basis 0)
  /-- The new principal relation in dimension `offset + 2`. -/
  principal : ∀ offset, Relation (offset + 2)
  /-- Every principal relation belongs to the liftable unit system. -/
  principal_valid :
    ∀ offset, IsLiftableUnit (tower.weights (offset + 2)) (principal offset)
  /-- Smaller-dimensional certificate lifts used to cancel the principal relation. -/
  corrections : ∀ offset, List (Correction (offset + 2))
  /-- The principal relation plus all correction targets is the first basis vector. -/
  decomposition : ∀ offset,
    principal offset +
      ((corrections offset).map Correction.target).sum = basis 0

/-- If the first coordinate has a certificate in every positive dimension,
the dimension lift supplies certificates for every coordinate. -/
def allCoordinatesOfFirst (tower : WeightTower)
    (first : ∀ n, Certificate (tower.weights (n + 1)) (basis 0)) :
    ∀ n (coordinate : Fin n), Certificate (tower.weights n) (basis coordinate)
  | 0, coordinate => Fin.elim0 coordinate
  | n + 1, coordinate => by
      refine Fin.cases (first n) (fun previous => ?_) coordinate
      have shifted := tower.liftCertificate
        (allCoordinatesOfFirst tower first n previous)
      exact (first n).add shifted |>.castTarget (by
        rw [lift_basis]
        simp)

/-- Strong induction on dimension constructs all coordinate certificates from
the explicit principal relations and correction chains. -/
theorem recurrenceCertificate_exists (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) :
    ∀ dimension (coordinate : Fin dimension),
      Nonempty (Certificate (tower.weights dimension) (basis coordinate)) := by
  intro dimension
  induction dimension using Nat.strong_induction_on with
  | h dimension inductionHypothesis =>
      intro coordinate
      rcases dimension with _ | dimension
      · exact Fin.elim0 coordinate
      rcases dimension with _ | offset
      · change Fin 1 at coordinate
        have hcoordinate : coordinate = 0 := Fin.eq_zero coordinate
        subst coordinate
        exact ⟨recurrence.base⟩
      · let correctionCertificates :
            List (Σ target, Certificate (tower.weights (offset + 2)) target) :=
          (recurrence.corrections offset).map fun correction =>
            ⟨correction.target,
              correction.liftCertificate tower
                (Classical.choice
                  (inductionHypothesis (correction.sourceOffset + 1)
                    correction.sourceDimension_lt correction.sourceCoordinate))⟩
        let combined :=
          (Certificate.singleton (recurrence.principal_valid offset)).add
            (Certificate.sum correctionCertificates)
        have htarget :
            recurrence.principal offset +
              (correctionCertificates.map Sigma.fst).sum = basis 0 := by
          have hcorrections :
              correctionCertificates.map Sigma.fst =
                (recurrence.corrections offset).map Correction.target := by
            simp [correctionCertificates]
          rw [hcorrections]
          exact recurrence.decomposition offset
        let first : Certificate (tower.weights (offset + 2)) (basis 0) :=
          combined.castTarget htarget
        refine Fin.cases ⟨first⟩ (fun previous => ?_) coordinate
        have previousCertificate :=
          Classical.choice
            (inductionHypothesis (offset + 1) (by omega) previous)
        have shifted := tower.liftCertificate previousCertificate
        refine ⟨(first.add shifted).castTarget ?_⟩
        rw [lift_basis]
        simp

/-- The full certificate family generated by an explicit principal/correction
recurrence. -/
noncomputable def recurrenceCertificates (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) :
    ∀ n (coordinate : Fin n),
      Certificate (tower.weights n) (basis coordinate) :=
  fun n coordinate =>
    Classical.choice (recurrenceCertificate_exists tower recurrence n coordinate)

/-- Pair an integer relation with a real candidate row. -/
def realDot {n : ℕ} (relation : Relation n) (candidate : Fin n → ℝ) : ℝ :=
  ∑ i, (relation i : ℝ) * candidate i

lemma realDot_add {n : ℕ} (first second : Relation n)
    (candidate : Fin n → ℝ) :
    realDot (first + second) candidate =
      realDot first candidate + realDot second candidate := by
  simp [realDot, add_mul, Finset.sum_add_distrib]

lemma realDot_aggregate {n : ℕ} (relations : List (Relation n))
    (candidate : Fin n → ℝ) :
    realDot (aggregate relations) candidate =
      (relations.map fun relation => realDot relation candidate).sum := by
  induction relations with
  | nil =>
      simp [aggregate, realDot]
  | cons relation relations inductionHypothesis =>
      change realDot (relation + aggregate relations) candidate =
        realDot relation candidate +
          (relations.map fun tailRelation => realDot tailRelation candidate).sum
      rw [realDot_add, inductionHypothesis]

@[simp]
lemma realDot_basis {n : ℕ} (coordinate : Fin n) (candidate : Fin n → ℝ) :
    realDot (basis coordinate) candidate = candidate coordinate := by
  classical
  simp [realDot, basis]

/-- Abstract normalized-chamber rigidity.  A certificate for a coordinate
forces every real row satisfying all its unit-relation inequalities to dominate
the corresponding reference weight. -/
theorem coordinate_lower_bound {n : ℕ} {weights : Relation n}
    {coordinate : Fin n} (certificate : Certificate weights (basis coordinate))
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation, IsLiftableUnit weights relation →
      1 ≤ realDot relation candidate) :
    (weights coordinate : ℝ) ≤ candidate coordinate := by
  have hsumGeneral : ∀ relations : List (Relation n),
      (∀ relation ∈ relations, IsLiftableUnit weights relation) →
        (relations.length : ℝ) ≤
          (relations.map fun relation => realDot relation candidate).sum := by
    intro relations
    induction relations with
    | nil =>
        intro
        simp
    | cons relation relations inductionHypothesis =>
        intro hvalid
        have hhead := hgap relation (hvalid relation List.mem_cons_self)
        have htail :
            ∀ tailRelation ∈ relations,
              IsLiftableUnit weights tailRelation := by
          intro tailRelation htailRelation
          exact hvalid tailRelation (List.mem_cons_of_mem relation htailRelation)
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons,
          List.sum_cons]
        simpa [add_comm] using add_le_add hhead (inductionHypothesis htail)
  have hsum := hsumGeneral certificate.relations certificate.valid
  have hlength :
      (certificate.relations.length : ℝ) = (weights coordinate : ℝ) := by
    exact_mod_cast certificate.length_eq_dot_target.trans (dot_basis coordinate weights)
  rw [hlength] at hsum
  calc
    (weights coordinate : ℝ) ≤
        (certificate.relations.map fun relation =>
          realDot relation candidate).sum := hsum
    _ = realDot (aggregate certificate.relations) candidate :=
      (realDot_aggregate certificate.relations candidate).symm
    _ = realDot (basis coordinate) candidate :=
      congrArg (fun relation => realDot relation candidate) certificate.target_eq
    _ = candidate coordinate := realDot_basis coordinate candidate

/-- Every recurrence certificate has mass equal to its Conway--Guy-style
reference coordinate. -/
theorem recurrenceCertificate_mass (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) {n : ℕ}
    (coordinate : Fin n) :
    ((recurrenceCertificates tower recurrence n coordinate).relations.length : ℤ) =
      tower.weights n coordinate := by
  exact (recurrenceCertificates tower recurrence n coordinate).length_eq_dot_target.trans
    (dot_basis coordinate (tower.weights n))

/-- **Normalized chamber rigidity.** An explicit principal/correction
recurrence makes the reference row a coordinatewise lower bound for every row
satisfying its unit-relation inequalities.

For the Conway--Guy order, the remaining concrete instantiation consists of:

1. the recurrence `W_(n+1) = (d_(n+1), d_(n+1) + W_n)`;
2. the block identity proving that each published principal relation has
   value one;
3. the triangular-index correction list and its basis-vector decomposition.

Bohman's distinct-subset-sum theorem is then used outside this algebraic
statement to identify the unit relations with consecutive order gaps. -/
theorem normalizedChamberRigidity (tower : WeightTower)
    (recurrence : FirstCoordinateRecurrence tower) {n : ℕ}
    (candidate : Fin n → ℝ)
    (hgap : ∀ relation, IsLiftableUnit (tower.weights n) relation →
      1 ≤ realDot relation candidate) :
    ∀ coordinate, (tower.weights n coordinate : ℝ) ≤ candidate coordinate := by
  intro coordinate
  exact coordinate_lower_bound
    (recurrenceCertificates tower recurrence n coordinate) candidate hgap

end BooleanIsoperimetry.CoherentGap
