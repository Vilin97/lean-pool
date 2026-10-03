/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.SupInf
public import LeanPool.ViscositySolutionTheory.ViscositySolns.Operators.Examples

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Operator hypotheses for comparison

This file contains operator-level hypotheses that are designed for the
doubling-of-variables comparison proof. The exact matrix inequality supplied by
Ishii's lemma is kept as a parameter here; the comparison infrastructure will
later instantiate that parameter with the block-matrix relation obtained from
the maximum principle for semicontinuous functions.
-/

@[expose] public noncomputable section

open Filter
open scoped MatrixOrder

namespace ViscositySolns

variable {n : Nat}

/--
A comparison modulus is a nonnegative real-valued function `ω` such that
`ω t -> 0` as `t -> 0` with `t > 0`.
-/
def ComparisonModulus (ω : Real -> Real) : Prop :=
  (∀ t : Real, 0 <= t -> 0 <= ω t) ∧
    Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)

/-- The zero function is a comparison modulus. -/
theorem ComparisonModulus.zero : ComparisonModulus (fun _t : Real => 0) := by
  constructor
  · intro _t _ht
    rfl
  · simp

theorem ComparisonModulus.nonneg {ω : Real -> Real} (hω : ComparisonModulus ω)
    {t : Real} (ht : 0 <= t) :
    0 <= ω t :=
  hω.1 t ht

theorem ComparisonModulus.tendsto_zero {ω : Real -> Real} (hω : ComparisonModulus ω) :
    Tendsto ω (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
  hω.2

/--
If `ω` is a comparison modulus and `ε > 0`, then there exists `t > 0` such
that `ω t < ε`.
-/
theorem ComparisonModulus.exists_pos_apply_lt {ω : Real -> Real}
    (hω : ComparisonModulus ω) {ε : Real} (hε : 0 < ε) :
    ∃ t : Real, 0 < t ∧ ω t < ε := by
  have hball :
      {t : Real | dist (ω t) 0 < ε} ∈ nhdsWithin (0 : Real) (Set.Ioi 0) :=
    hω.tendsto_zero (Metric.ball_mem_nhds 0 hε)
  rw [mem_nhdsWithin] at hball
  rcases hball with ⟨U, hUopen, h0U, hU⟩
  rcases Metric.mem_nhds_iff.1 (hUopen.mem_nhds h0U) with ⟨δ, hδ, hδU⟩
  refine ⟨δ / 2, by linarith, ?_⟩
  have htU : δ / 2 ∈ U := by
    apply hδU
    have hdist : dist (δ / 2) 0 < δ := by
      rw [Real.dist_eq]
      have hδ2 : 0 < δ / 2 := by linarith
      rw [sub_zero, abs_of_pos hδ2]
      linarith
    exact hdist
  have htIoi : δ / 2 ∈ Set.Ioi (0 : Real) := by
    exact half_pos hδ
  have hdist : dist (ω (δ / 2)) 0 < ε := hU ⟨htU, htIoi⟩
  simpa [Real.dist_eq] using (abs_lt.mp hdist).2

/--
No positive number can be bounded above by `ω t` for every `t > 0`, when `ω`
is a comparison modulus.
-/
theorem ComparisonModulus.not_forall_pos_le_apply {ω : Real -> Real}
    (hω : ComparisonModulus ω) {ε : Real} (hε : 0 < ε) :
    ¬ ∀ t : Real, 0 < t -> ε <= ω t := by
  rintro h
  rcases hω.exists_pos_apply_lt hε with ⟨t, htpos, htlt⟩
  exact (not_le_of_gt htlt) (h t htpos)

/--
Let `ω` be a comparison modulus and let `ε > 0`. It is impossible that for
every `t > 0` there exists a real number `g` with
`ε ≤ g ≤ ω t`.
-/
theorem ComparisonModulus.not_forall_pos_exists_between_apply
    {ω : Real -> Real} (hω : ComparisonModulus ω) {ε : Real} (hε : 0 < ε) :
    ¬ ∀ t : Real, 0 < t -> ∃ g : Real, ε <= g ∧ g <= ω t := by
  intro h
  exact hω.not_forall_pos_le_apply hε fun t ht =>
    let ⟨g, hεg, hgω⟩ := h t ht
    le_trans hεg hgω

/--
Let `ω a`, for `a` in a nonempty finite type, be comparison moduli. Then the
function

`t ↦ max_{a} ω a t`

is also a comparison modulus.
-/
theorem ComparisonModulus.finset_sup'
    {ι : Type*} [Fintype ι] [Nonempty ι] {ω : ι -> Real -> Real}
    (hω : ∀ a : ι, ComparisonModulus (ω a)) :
    ComparisonModulus
      (fun t : Real => Finset.univ.sup' Finset.univ_nonempty fun a : ι => ω a t) := by
  constructor
  · intro t ht
    let a0 : ι := Classical.choice ‹Nonempty ι›
    exact (hω a0).nonneg ht |>.trans
      (Finset.le_sup' (fun a : ι => ω a t) (Finset.mem_univ a0))
  · have htend :
        Tendsto
          (fun t : Real => Finset.univ.sup' Finset.univ_nonempty
            (fun a : ι => ω a t))
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (Finset.univ.sup' Finset.univ_nonempty
            (fun _a : ι => (0 : Real)))) := by
      exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
        (fun a _ha => (hω a).tendsto_zero)
    simpa using htend

/--
If `ω` and `η` are comparison moduli, then `t ↦ ω t + η t` is a comparison
modulus.
-/
theorem ComparisonModulus.add {ω η : Real -> Real}
    (hω : ComparisonModulus ω) (hη : ComparisonModulus η) :
    ComparisonModulus (fun t : Real => ω t + η t) := by
  constructor
  · intro t ht
    exact add_nonneg (hω.nonneg ht) (hη.nonneg ht)
  · simpa using hω.tendsto_zero.add hη.tendsto_zero

/--
If `ω` is a comparison modulus and `0 ≤ a`, then `t ↦ a * ω t` is a
comparison modulus.
-/
theorem ComparisonModulus.const_mul_nonneg {ω : Real -> Real} {a : Real}
    (ha : 0 <= a) (hω : ComparisonModulus ω) :
    ComparisonModulus (fun t : Real => a * ω t) := by
  constructor
  · intro t ht
    exact mul_nonneg ha (hω.nonneg ht)
  · have ha_tend : Tendsto (fun _t : Real => a)
        (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds a) :=
      tendsto_const_nhds
    simpa using ha_tend.mul hω.tendsto_zero

/--
The type of matrix relations used in comparison hypotheses.

The arguments are the penalty parameter `α`, the two spatial points `x` and
`y`, and the two Hessian matrices `X` and `Y` produced by the maximum principle.
-/
abbrev ComparisonMatrixRelation (n : Nat) : Type :=
  Real -> Point n -> Point n -> Hessian n -> Hessian n -> Prop

/--
Structural continuity condition for comparison on a set of spatial points `C`
and scalar values `R`.

For every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every pair of matrices
`X, Y` satisfying the supplied matrix relation, the difference
`F y r (α • (x - y)) Y - F x r (α • (x - y)) X` is bounded above by a modulus
evaluated at `α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
def OperatorComparisonConditionOn (C : Set (Point n)) (R : Set Real)
    (matrixRel : ComparisonMatrixRelation n) (F : Operator n) : Prop :=
  ∃ ω : Real -> Real, ComparisonModulus ω ∧
    ∀ α : Real, 0 < α ->
    ∀ x : Point n, x ∈ C ->
    ∀ y : Point n, y ∈ C ->
    ∀ r : Real, r ∈ R ->
    ∀ X Y : Hessian n, matrixRel α x y X Y ->
      F y r (α • (x - y)) Y - F x r (α • (x - y)) X <=
        ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)

theorem OperatorComparisonConditionOn.mono_scalar_set
    {C : Set (Point n)} {R S : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : Operator n}
    (hF : OperatorComparisonConditionOn C S matrixRel F) (hRS : R ⊆ S) :
    OperatorComparisonConditionOn C R matrixRel F := by
  rcases hF with ⟨ω, hω, hbound⟩
  exact ⟨ω, hω, fun α hα x hx y hy r hr X Y hXY =>
    hbound α hα x hx y hy r (hRS hr) X Y hXY⟩

theorem OperatorComparisonConditionOn.mono_spatial_set
    {C D : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : Operator n}
    (hF : OperatorComparisonConditionOn D R matrixRel F) (hCD : C ⊆ D) :
    OperatorComparisonConditionOn C R matrixRel F := by
  rcases hF with ⟨ω, hω, hbound⟩
  exact ⟨ω, hω, fun α hα x hx y hy r hr X Y hXY =>
    hbound α hα x (hCD hx) y (hCD hy) r hr X Y hXY⟩

/--
Let `ω` be a comparison modulus which is monotone on real numbers. Suppose
that for every `α > 0`, every `x, y ∈ C`, every `r ∈ R`, and every `X`, `Y`
satisfying `matrixRel α x y X Y`,

`F y r (α • (x - y)) Y - F x r (α • (x - y)) X ≤ ω ‖x - y‖`.

Then `F` satisfies `OperatorComparisonConditionOn C R matrixRel`, because
`‖x - y‖ ≤ α * ‖x - y‖ ^ 2 + ‖x - y‖`.
-/
theorem OperatorComparisonConditionOn.of_norm_bound
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω) (hmono : Monotone ω)
    (hbound :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, matrixRel α x y X Y ->
        F y r (α • (x - y)) Y - F x r (α • (x - y)) X <= ω ‖x - y‖) :
    OperatorComparisonConditionOn C R matrixRel F := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  refine le_trans (hbound α hα x hx y hy r hr X Y hXY) ?_
  apply hmono
  have hsq : 0 <= ‖x - y‖ ^ 2 := sq_nonneg ‖x - y‖
  have hmul : 0 <= α * ‖x - y‖ ^ 2 := mul_nonneg hα.le hsq
  linarith

/--
If the operator difference in the structural comparison condition is always
nonpositive, then the structural comparison condition holds with the zero
comparison modulus.
-/
theorem OperatorComparisonConditionOn.of_nonpositive_difference
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : Operator n}
    (hF :
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, matrixRel α x y X Y ->
        F y r (α • (x - y)) Y - F x r (α • (x - y)) X <= 0) :
    OperatorComparisonConditionOn C R matrixRel F := by
  refine ⟨fun _t : Real => 0, ComparisonModulus.zero, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  simpa using hF α hα x hx y hy r hr X Y hXY

/--
Every constant operator satisfies the structural comparison condition, for any
spatial set, scalar set, and matrix relation.
-/
theorem OperatorComparisonConditionOn.constOperator
    (C : Set (Point n)) (R : Set Real) (matrixRel : ComparisonMatrixRelation n)
    (c : Real) :
    OperatorComparisonConditionOn C R matrixRel (constOperator (n := n) c) := by
  refine OperatorComparisonConditionOn.of_nonpositive_difference ?_
  intro α _hα x _hx y _hy r _hr X Y _hXY
  simp

/--
If two operators satisfy the structural comparison condition on the same set
`C`, scalar set `R`, and matrix relation, then their pointwise sum satisfies
the same condition. The comparison modulus for the sum is the sum of the two
comparison moduli.
-/
theorem OperatorComparisonConditionOn.addOperator
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F G : Operator n}
    (hF : OperatorComparisonConditionOn C R matrixRel F)
    (hG : OperatorComparisonConditionOn C R matrixRel G) :
    OperatorComparisonConditionOn C R matrixRel (addOperator F G) := by
  rcases hF with ⟨ω, hω, hFbound⟩
  rcases hG with ⟨η, hη, hGbound⟩
  refine ⟨fun t : Real => ω t + η t, hω.add hη, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  have hFxy := hFbound α hα x hx y hy r hr X Y hXY
  have hGxy := hGbound α hα x hx y hy r hr X Y hXY
  dsimp [addOperator]
  linarith

/--
If an operator satisfies the structural comparison condition on `C`, `R`, and
`matrixRel`, then every nonnegative scalar multiple of it satisfies the same
condition.
-/
theorem OperatorComparisonConditionOn.smulOperator_nonneg
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : Operator n} {a : Real}
    (ha : 0 <= a) (hF : OperatorComparisonConditionOn C R matrixRel F) :
    OperatorComparisonConditionOn C R matrixRel (smulOperator a F) := by
  rcases hF with ⟨ω, hω, hFbound⟩
  refine ⟨fun t : Real => a * ω t, hω.const_mul_nonneg ha, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  have hFxy := hFbound α hα x hx y hy r hr X Y hXY
  have hmul :
      a * (F y r (α • (x - y)) Y - F x r (α • (x - y)) X) <=
        a * ω (α * ‖x - y‖ ^ 2 + ‖x - y‖) :=
    mul_le_mul_of_nonneg_left hFxy ha
  dsimp [smulOperator]
  linarith

/--
Let `F a` be a nonempty finite family of operators. Suppose there is a single
comparison modulus `ω` such that, for every index `a`, every `α > 0`, every
`x, y ∈ C`, every `r ∈ R`, and every `X`, `Y` satisfying `matrixRel α x y X Y`,

`F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X
 ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.

Then the pointwise supremum operator `supOperator F` satisfies
`OperatorComparisonConditionOn C R matrixRel`.
-/
theorem OperatorComparisonConditionOn.supOperator_of_common_modulus
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : ι -> Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hbound :
      ∀ a : ι,
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, matrixRel α x y X Y ->
        F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    OperatorComparisonConditionOn C R matrixRel (supOperator F) := by
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  let p : Point n := α • (x - y)
  let t : Real := α * ‖x - y‖ ^ 2 + ‖x - y‖
  have hsup :
      (Finset.univ.sup' Finset.univ_nonempty fun a : ι => F a y r p Y) <=
        (Finset.univ.sup' Finset.univ_nonempty fun a : ι => F a x r p X) + ω t := by
    refine Finset.sup'_le Finset.univ_nonempty _ ?_
    intro a _ha
    have hbranch : F a y r p Y <= F a x r p X + ω t := by
      have h := hbound a α hα x hx y hy r hr X Y hXY
      dsimp [p, t] at h ⊢
      linarith
    have hle_sup :
        F a x r p X <=
          Finset.univ.sup' Finset.univ_nonempty (fun b : ι => F b x r p X) :=
      Finset.le_sup' (fun b : ι => F b x r p X) (Finset.mem_univ a)
    linarith
  dsimp [supOperator, p, t]
  linarith

/--
Let `F a` be a nonempty finite family of operators. Suppose there is a single
comparison modulus `ω` such that, for every index `a`, every `α > 0`, every
`x, y ∈ C`, every `r ∈ R`, and every `X`, `Y` satisfying `matrixRel α x y X Y`,

`F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X
 ≤ ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)`.

Then the pointwise infimum operator `infOperator F` satisfies
`OperatorComparisonConditionOn C R matrixRel`. The proof chooses an index
where `F a x r (α • (x - y)) X` is minimal.
-/
theorem OperatorComparisonConditionOn.infOperator_of_common_modulus
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : ι -> Operator n} {ω : Real -> Real}
    (hω : ComparisonModulus ω)
    (hbound :
      ∀ a : ι,
      ∀ α : Real, 0 < α ->
      ∀ x : Point n, x ∈ C ->
      ∀ y : Point n, y ∈ C ->
      ∀ r : Real, r ∈ R ->
      ∀ X Y : Hessian n, matrixRel α x y X Y ->
        F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X <=
          ω (α * ‖x - y‖ ^ 2 + ‖x - y‖)) :
    OperatorComparisonConditionOn C R matrixRel (infOperator F) := by
  classical
  refine ⟨ω, hω, ?_⟩
  intro α hα x hx y hy r hr X Y hXY
  let p : Point n := α • (x - y)
  let t : Real := α * ‖x - y‖ ^ 2 + ‖x - y‖
  rcases Finset.exists_mem_eq_inf' Finset.univ_nonempty
      (fun a : ι => F a x r p X) with
    ⟨a0, _ha0, hmin⟩
  have hle_y :
      (Finset.univ.inf' Finset.univ_nonempty fun a : ι => F a y r p Y) <=
        F a0 y r p Y :=
    Finset.inf'_le (fun a : ι => F a y r p Y) (Finset.mem_univ a0)
  have hbranch : F a0 y r p Y <= F a0 x r p X + ω t := by
    have h := hbound a0 α hα x hx y hy r hr X Y hXY
    dsimp [p, t] at h ⊢
    linarith
  dsimp [infOperator, p, t]
  linarith

/--
Let `F a` be a nonempty finite family of operators. Suppose that for every
index `a`, the operator `F a` satisfies `OperatorComparisonConditionOn C R
matrixRel`. Then the pointwise supremum operator `supOperator F` also
satisfies `OperatorComparisonConditionOn C R matrixRel`.

The proof takes the pointwise maximum of the finitely many comparison moduli
associated to the branches `F a`.
-/
theorem OperatorComparisonConditionOn.supOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : ι -> Operator n}
    (hF : ∀ a : ι, OperatorComparisonConditionOn C R matrixRel (F a)) :
    OperatorComparisonConditionOn C R matrixRel (supOperator F) := by
  classical
  choose ω hω hbound using hF
  refine OperatorComparisonConditionOn.supOperator_of_common_modulus
    (F := F) (hω := ComparisonModulus.finset_sup' hω) ?_
  intro a α hα x hx y hy r hr X Y hXY
  let t : Real := α * ‖x - y‖ ^ 2 + ‖x - y‖
  have ha : F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X <= ω a t := by
    simpa [t] using hbound a α hα x hx y hy r hr X Y hXY
  exact ha.trans
    (Finset.le_sup' (fun b : ι => ω b t) (Finset.mem_univ a))

/--
Let `F a` be a nonempty finite family of operators. Suppose that for every
index `a`, the operator `F a` satisfies `OperatorComparisonConditionOn C R
matrixRel`. Then the pointwise infimum operator `infOperator F` also satisfies
`OperatorComparisonConditionOn C R matrixRel`.

The proof takes the pointwise maximum of the finitely many comparison moduli
associated to the branches `F a`.
-/
theorem OperatorComparisonConditionOn.infOperator
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : Set (Point n)} {R : Set Real} {matrixRel : ComparisonMatrixRelation n}
    {F : ι -> Operator n}
    (hF : ∀ a : ι, OperatorComparisonConditionOn C R matrixRel (F a)) :
    OperatorComparisonConditionOn C R matrixRel (infOperator F) := by
  classical
  choose ω hω hbound using hF
  refine OperatorComparisonConditionOn.infOperator_of_common_modulus
    (F := F) (hω := ComparisonModulus.finset_sup' hω) ?_
  intro a α hα x hx y hy r hr X Y hXY
  let t : Real := α * ‖x - y‖ ^ 2 + ‖x - y‖
  have ha : F a y r (α • (x - y)) Y - F a x r (α • (x - y)) X <= ω a t := by
    simpa [t] using hbound a α hα x hx y hy r hr X Y hXY
  exact ha.trans
    (Finset.le_sup' (fun b : ι => ω b t) (Finset.mem_univ a))

end ViscositySolns
