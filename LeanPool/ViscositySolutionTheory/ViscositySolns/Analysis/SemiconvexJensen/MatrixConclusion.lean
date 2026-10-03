/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.ContactSelection

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Aleksandrov--Jensen theorem for semiconvex functions (MatrixConclusion)

Part of the Aleksandrov--Jensen development assembling the localized Jensen
contact-set theorem with Aleksandrov differentiability. Split from
`SemiconvexJensen.lean`; see the umbrella module docstring.
-/
@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped Convolution
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}
/--
Selected data along the sequence `1 / (k + 1)`, retaining ordinary two-sided
jets of the original function.

In quantified mathematical form, under the hypotheses of the localized
Aleksandrov--Jensen selected-data theorem, there exist sequences `x_k`,
`a_k`, `X_k`, and `J_k` such that, for every natural number `k`,

* `‖x_k‖ ≤ 1 / (k + 1)`;
* `‖a_k‖ < 1 / (k + 1)`;
* `X_k` and `(J_k).hessian` are Hermitian;
* `(a_k, X_k)` is an ordinary two-sided second-order jet of
  `x ↦ g x - (1 / 2) * ⟪B x, x⟫ - (∑ i, x_i^2)^2` at `x_k`;
* `J_k` is obtained from `(a_k, X_k)` by adding the coordinate-quartic jet at
  `x_k` and the recentered quadratic jet at `x_k`;
* `J_k` belongs to the closed superjet of `g` at `x_k`;
* `(J_k).hessian ≤ B + (coordinate-quartic Hessian at x_k)`;
* `(J_k).gradient` and `(J_k).hessian` form an ordinary two-sided
  second-order jet of `g` at `x_k`.

Moreover `x_k -> 0` and `a_k -> 0` as `k -> ∞`.
-/
theorem exists_strictifiedQuadraticObjective_twoSidedJet_sequence_norm_bounds_hessian
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) ∧
      (∀ k : Nat, HasSecondOrderJet g (xSeq k)
        (JSeq k).gradient (JSeq k).hessian) := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_norm_bounds_hessian
      hJensen hAleksandrov hB hconv hmax with
    ⟨xSeq, aSeq, XSeq, JSeq, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
      hXherm, hJherm, hjet, hJ, hclosed, hupper⟩
  have htwoSided :
      ∀ k : Nat, HasSecondOrderJet g (xSeq k)
        (JSeq k).gradient (JSeq k).hessian := by
    intro k
    exact (hjet k).of_eq_strictifiedQuadraticObjectiveJet (hJ k)
  exact ⟨xSeq, aSeq, XSeq, JSeq, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
    hXherm, hJherm, hjet, hJ, hclosed, hupper, htwoSided⟩

/--
Selected closed-superjet data together with a convergent Hessian subsequence.

In standard mathematical terms, under the hypotheses of the localized
Aleksandrov--Jensen selected-data theorem, one may choose selected points
`x_k`, first-order vectors `a_k`, auxiliary Hessians `X_k`, and closed
superjets `J_k ∈ \overline J^{2,+}_{R^n} g(x_k)` as in
`exists_strictifiedQuadraticObjective_closedSuperjet_sequence_norm_bounds_hessian`.
Moreover, the Hessian matrices `(J_k).hessian` have a convergent subsequence.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_sequence_hessian_subsequence
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (𝓝 Z) := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_norm_bounds_hessian
      hJensen hAleksandrov hB hconv hmax with
    ⟨xSeq, aSeq, XSeq, JSeq, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
      hXherm, hJherm, hjet, hJ, hclosed, hupper⟩
  have hpsd : ∀ k : Nat, ((JSeq k).hessian).PosSemidef := by
    intro k
    rw [← Matrix.nonneg_iff_posSemidef]
    exact ClosedSuperjet.hessian_nonneg_of_convexOn hconv (hclosed k) (hJherm k)
  have hquartic_tendsto :
      Filter.Tendsto
        (fun k : Nat => (coordinateQuarticJetAt (xSeq k)).hessian)
        Filter.atTop (𝓝 (0 : Hessian n)) :=
    tendsto_coordinateQuarticJetAt_hessian_zero.comp hx_tendsto
  rcases exists_eventually_entrywise_abs_le_of_posSemidef_le_add_tendsto_zero
      (A := fun k : Nat => (JSeq k).hessian)
      (Q := fun k : Nat => (coordinateQuarticJetAt (xSeq k)).hessian)
      (B := B) hpsd hupper hquartic_tendsto with
    ⟨_R, hentry⟩
  rcases exists_hessian_subsequence_tendsto_of_eventually_entrywise_abs_le
      (A := fun k : Nat => (JSeq k).hessian) hentry with
    ⟨Z, φ, hφ, hZ⟩
  exact ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto,
    ha_tendsto, hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ⟩

/--
Selected closed-superjet data with a Hessian subsequential limit satisfying
the matrix-order bounds required in the Aleksandrov--Jensen theorem.

In standard mathematical terms, the selected Hessians admit a subsequential
limit `Z`, and this limit is Hermitian, nonnegative, and bounded above by the
quadratic matrix `B`.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_sequence_hessian_subsequence_order
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (𝓝 Z) ∧
      Z.IsHermitian ∧
      0 <= Z ∧
      Z <= B := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_hessian_subsequence
      hJensen hAleksandrov hB hconv hmax with
    ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
      hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ⟩
  have hZherm : Z.IsHermitian :=
    hessian_isHermitian_of_tendsto_isHermitian hZ (fun k => hJherm (φ k))
  have hZnonneg : 0 <= Z := by
    refine hessian_nonneg_of_tendsto_nonneg hZ hZherm ?_
    exact Filter.Eventually.of_forall fun k =>
      ClosedSuperjet.hessian_nonneg_of_convexOn hconv (hclosed (φ k)) (hJherm (φ k))
  have hx_subseq :
      Filter.Tendsto (fun k : Nat => xSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) :=
    hx_tendsto.comp hφ.tendsto_atTop
  have hquartic_subseq :
      Filter.Tendsto
        (fun k : Nat => (coordinateQuarticJetAt (xSeq (φ k))).hessian)
        Filter.atTop (𝓝 (0 : Hessian n)) :=
    tendsto_coordinateQuarticJetAt_hessian_zero.comp hx_subseq
  have hupper_tendsto :
      Filter.Tendsto
        (fun k : Nat => (coordinateQuarticJetAt (xSeq (φ k))).hessian + B)
        Filter.atTop (𝓝 B) := by
    simpa using hquartic_subseq.add tendsto_const_nhds
  have hZleB : Z <= B := by
    refine hessian_le_of_tendsto_le hZ hupper_tendsto hZherm hB ?_
    exact Filter.Eventually.of_forall fun k => hupper (φ k)
  exact ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto,
    ha_tendsto, hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ, hZherm,
    hZnonneg, hZleB⟩

/--
The gradient components of the selected closed-superjet sequence converge to
zero along every strictly increasing subsequence.

In standard mathematical terms, if
`J_k = (a_k, X_k) + coordinateQuarticJetAt x_k + quadraticModelJetAt 0 0 B x_k`,
`x_k -> 0`, and `a_k -> 0`, then `(J_{φ(k)}).gradient -> 0` for every
strictly increasing `φ : Nat -> Nat`.
-/
theorem tendsto_strictifiedQuadraticObjective_closedSuperjet_sequence_gradient_zero
    {xSeq aSeq : Nat -> Point n} {XSeq : Nat -> Hessian n}
    {JSeq : Nat -> Jet n} {B : Hessian n} {φ : Nat -> Nat}
    (hx : Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)))
    (ha : Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)))
    (hφ : StrictMono φ)
    (hJ : ∀ k : Nat,
      JSeq k =
        (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
            coordinateQuarticJetAt (xSeq k)) +
          quadraticModelJetAt 0 0 B (xSeq k)) :
    Filter.Tendsto (fun k : Nat => (JSeq (φ k)).gradient)
      Filter.atTop (𝓝 (0 : Point n)) := by
  have hx_subseq :
      Filter.Tendsto (fun k : Nat => xSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) :=
    hx.comp hφ.tendsto_atTop
  have ha_subseq :
      Filter.Tendsto (fun k : Nat => aSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) :=
    ha.comp hφ.tendsto_atTop
  have hquartic :
      Filter.Tendsto
        (fun k : Nat => (coordinateQuarticJetAt (xSeq (φ k))).gradient)
        Filter.atTop (𝓝 (0 : Point n)) :=
    tendsto_coordinateQuarticJetAt_gradient_zero.comp hx_subseq
  have hquadratic :
      Filter.Tendsto
        (fun k : Nat => (quadraticModelJetAt 0 0 B (xSeq (φ k))).gradient)
        Filter.atTop (𝓝 (0 : Point n)) :=
    (tendsto_quadraticModelJetAt_zero_zero_gradient_zero (n := n) B).comp hx_subseq
  have hsum :
      Filter.Tendsto
        (fun k : Nat =>
          (aSeq (φ k) + (coordinateQuarticJetAt (xSeq (φ k))).gradient) +
            (quadraticModelJetAt 0 0 B (xSeq (φ k))).gradient)
        Filter.atTop (𝓝 ((0 + 0) + (0 : Point n))) :=
    (ha_subseq.add hquartic).add hquadratic
  have hsum_zero :
      Filter.Tendsto
        (fun k : Nat =>
          (aSeq (φ k) + (coordinateQuarticJetAt (xSeq (φ k))).gradient) +
            (quadraticModelJetAt 0 0 B (xSeq (φ k))).gradient)
        Filter.atTop (𝓝 (0 : Point n)) := by
    simpa using hsum
  refine hsum_zero.congr' ?_
  exact Filter.Eventually.of_forall fun k => by
    change
      (aSeq (φ k) + (coordinateQuarticJetAt (xSeq (φ k))).gradient) +
          (quadraticModelJetAt 0 0 B (xSeq (φ k))).gradient =
        (JSeq (φ k)).gradient
    rw [hJ (φ k)]
    rfl

/--
Convergence of jets follows from convergence of their gradient and Hessian
components.
-/
theorem tendsto_jet_of_tendsto_gradient_hessian
    {ι : Type*} {l : Filter ι} {JSeq : ι -> Jet n} {J : Jet n}
    (hgrad : Filter.Tendsto (fun i : ι => (JSeq i).gradient) l (𝓝 J.gradient))
    (hhess : Filter.Tendsto (fun i : ι => (JSeq i).hessian) l (𝓝 J.hessian)) :
    Filter.Tendsto JSeq l (𝓝 J) := by
  rw [nhds_induced]
  rw [Filter.tendsto_comap_iff]
  exact hgrad.prodMk_nhds hhess

/--
Selected closed-superjet data with convergence of the graph coordinates needed
for the closed-superjet graph argument.

In standard mathematical terms, the selected subsequence may be chosen so that
`x_{φ(k)} -> 0`, `g(x_{φ(k)}) -> g(0)`, and
`J_{φ(k)} -> (0, Z)`, where `Z` is Hermitian and satisfies `0 ≤ Z ≤ B`.
-/
theorem exists_strictifiedQuadraticObjective_closedSuperjet_sequence_subsequence_graph_tendsto
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} (hg : Continuous g) {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (𝓝 Z) ∧
      Z.IsHermitian ∧
      0 <= Z ∧
      Z <= B ∧
      Filter.Tendsto (fun k : Nat => xSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto (fun k : Nat => g (xSeq (φ k))) Filter.atTop (𝓝 (g 0)) ∧
      Filter.Tendsto (fun k : Nat => JSeq (φ k)) Filter.atTop
        (𝓝 ({ gradient := 0, hessian := Z } : Jet n)) := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_hessian_subsequence_order
      hJensen hAleksandrov hB hconv hmax with
    ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
      hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ, hZherm, hZnonneg, hZleB⟩
  have hx_subseq :
      Filter.Tendsto (fun k : Nat => xSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) :=
    hx_tendsto.comp hφ.tendsto_atTop
  have hvalue :
      Filter.Tendsto (fun k : Nat => g (xSeq (φ k))) Filter.atTop (𝓝 (g 0)) :=
    hg.continuousAt.tendsto.comp hx_subseq
  have hgrad :
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).gradient)
        Filter.atTop (𝓝 (0 : Point n)) :=
    tendsto_strictifiedQuadraticObjective_closedSuperjet_sequence_gradient_zero
      hx_tendsto ha_tendsto hφ hJ
  have hJtendsto :
      Filter.Tendsto (fun k : Nat => JSeq (φ k)) Filter.atTop
        (𝓝 ({ gradient := 0, hessian := Z } : Jet n)) :=
    tendsto_jet_of_tendsto_gradient_hessian hgrad hZ
  exact ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto,
    ha_tendsto, hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ, hZherm,
    hZnonneg, hZleB, hx_subseq, hvalue, hJtendsto⟩

/--
Selected closed-superjet data with graph convergence and ordinary two-sided
jets of the original function.

In quantified mathematical form, under the hypotheses of
`exists_strictifiedQuadraticObjective_closedSuperjet_sequence_subsequence_graph_tendsto`,
the selected sequences may also be chosen so that, for every natural number
`k`, `(J_k).gradient` and `(J_k).hessian` form an ordinary two-sided
second-order jet of `g` at `x_k`.
-/
theorem exists_strictifiedQuadraticObjective_twoSidedJet_sequence_subsequence_graph_tendsto
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {g : Point n -> Real} (hg : Continuous g) {B : Hessian n}
    (hB : B.IsHermitian)
    (hconv : ConvexOn Real Set.univ g)
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ aSeq : Nat -> Point n,
    ∃ XSeq : Nat -> Hessian n, ∃ JSeq : Nat -> Jet n,
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat,
      (∀ k : Nat, ‖xSeq k‖ <= (1 : Real) / ((k : Real) + 1)) ∧
      (∀ k : Nat, ‖aSeq k‖ < (1 : Real) / ((k : Real) + 1)) ∧
      Filter.Tendsto xSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto aSeq Filter.atTop (𝓝 (0 : Point n)) ∧
      (∀ k : Nat, (XSeq k).IsHermitian) ∧
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat,
        HasSecondOrderJet (strictifiedQuadraticObjective g B)
          (xSeq k) (aSeq k) (XSeq k)) ∧
      (∀ k : Nat,
        JSeq k =
          (({ gradient := aSeq k, hessian := XSeq k } : Jet n) +
              coordinateQuarticJetAt (xSeq k)) +
            quadraticModelJetAt 0 0 B (xSeq k)) ∧
      (∀ k : Nat, JSeq k ∈ ClosedSuperjet Set.univ g (xSeq k)) ∧
      (∀ k : Nat,
        (JSeq k).hessian <= (coordinateQuarticJetAt (xSeq k)).hessian + B) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian) Filter.atTop (𝓝 Z) ∧
      Z.IsHermitian ∧
      0 <= Z ∧
      Z <= B ∧
      Filter.Tendsto (fun k : Nat => xSeq (φ k)) Filter.atTop (𝓝 (0 : Point n)) ∧
      Filter.Tendsto (fun k : Nat => g (xSeq (φ k))) Filter.atTop (𝓝 (g 0)) ∧
      Filter.Tendsto (fun k : Nat => JSeq (φ k)) Filter.atTop
        (𝓝 ({ gradient := 0, hessian := Z } : Jet n)) ∧
      (∀ k : Nat, HasSecondOrderJet g (xSeq k)
        (JSeq k).gradient (JSeq k).hessian) := by
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_subsequence_graph_tendsto
      hJensen hAleksandrov hg hB hconv hmax with
    ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto, ha_tendsto,
      hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ, hZherm, hZnonneg,
      hZleB, hx_subseq, hvalue, hJtendsto⟩
  have htwoSided :
      ∀ k : Nat, HasSecondOrderJet g (xSeq k)
        (JSeq k).gradient (JSeq k).hessian := by
    intro k
    exact (hjet k).of_eq_strictifiedQuadraticObjectiveJet (hJ k)
  exact ⟨xSeq, aSeq, XSeq, JSeq, Z, φ, hx_bound, ha_bound, hx_tendsto,
    ha_tendsto, hXherm, hJherm, hjet, hJ, hclosed, hupper, hφ, hZ, hZherm,
    hZnonneg, hZleB, hx_subseq, hvalue, hJtendsto, htwoSided⟩

/--
Selected ordinary two-sided jets for a semiconvex function.

In quantified mathematical form, let `f : R^n -> R` be continuous and suppose
that `f` satisfies the coordinate semiconvexity inequality on all of `R^n`
with constant `lambda ≥ 0`. Let `B` be a symmetric matrix, and suppose that

`x ↦ f x - (1 / 2) * ⟪B x, x⟫`

has a maximum at `0` on all of `R^n`. Then there are points `x_k`, jets
`J_k`, a matrix `Z`, and a strictly increasing map `φ : Nat -> Nat` such that:

* for every `k`, `J_k` is an ordinary two-sided second-order jet of `f` at
  `x_k`;
* the Hessians `(J_{φ(k)}).hessian` converge to `Z`;
* `(0, Z)` belongs to the closed superjet of `f` at `0`;
* `-lambda I ≤ Z ≤ B`.
-/
theorem exists_semiconvex_twoSidedJet_sequence_subsequence_graph_tendsto
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n)
    {lambda : Real} (_hlambda : 0 <= lambda)
    {f : Point n -> Real} (hf : Continuous f) {B : Hessian n}
    (hB : B.IsHermitian)
    (hsemi : CoordinateSemiconvexOn lambda Set.univ f)
    (hmax : IsMaxOn (semiconvexQuadraticObjective f B) Set.univ 0) :
    ∃ xSeq : Nat -> Point n, ∃ JSeq : Nat -> Jet n,
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat,
      (∀ k : Nat, (JSeq k).hessian.IsHermitian) ∧
      (∀ k : Nat, HasSecondOrderJet f (xSeq k)
        (JSeq k).gradient (JSeq k).hessian) ∧
      StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian)
        Filter.atTop (𝓝 Z) ∧
      Z.IsHermitian ∧
      (-lambda) • (1 : Hessian n) <= Z ∧
      Z <= B ∧
      ({ gradient := 0, hessian := Z } : Jet n) ∈ ClosedSuperjet Set.univ f 0 := by
  let g : Point n -> Real := semiconvexConvexification lambda f
  let B' : Hessian n := B + lambda • (1 : Hessian n)
  have hcontQ :
      Continuous fun x : Point n => quadraticModel 0 0 0 (lambda • (1 : Hessian n)) x :=
    continuous_quadraticModel 0 0 0 (lambda • (1 : Hessian n))
  have hg : Continuous g := by
    exact hf.add hcontQ
  have hlambdaI : (lambda • (1 : Hessian n)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)
  have hB' : B'.IsHermitian := by
    exact hB.add hlambdaI
  have hconv : ConvexOn Real Set.univ g := by
    simpa [g] using hsemi.convexOn_semiconvexConvexification (C := Set.univ) convex_univ
  have hmaxg : IsMaxOn (semiconvexQuadraticObjective g B') Set.univ 0 := by
    exact
      (isMaxOn_semiconvexQuadraticObjective_convexification_add_scalar_identity_iff
        lambda f B Set.univ 0).2 hmax
  rcases exists_strictifiedQuadraticObjective_twoSidedJet_sequence_subsequence_graph_tendsto
      hJensen hAleksandrov hg hB' hconv hmaxg with
    ⟨xSeq, _aSeq, _XSeq, JSeqConv, ZConv, φ, _hx_bound, _ha_bound,
      _hx_tendsto, _ha_tendsto, _hXherm, hJhermConv, _hjet, _hJdef,
      hclosedConvSeq, _hupper, hφ, hZConv, hZConvHerm, hZConvNonneg,
      hZConvLe, hx_subseq, hvalueConv, hJConvTendsto, htwoSidedConv⟩
  let QJet : Point n -> Jet n :=
    fun x => quadraticModelJetAt 0 0 (lambda • (1 : Hessian n)) x
  let JSeq : Nat -> Jet n := fun k => JSeqConv k - QJet (xSeq k)
  let Z : Hessian n := ZConv - lambda • (1 : Hessian n)
  have hJherm : ∀ k : Nat, (JSeq k).hessian.IsHermitian := by
    intro k
    simpa [JSeq, QJet, quadraticModelJetAt] using (hJhermConv k).sub hlambdaI
  have htwoSided : ∀ k : Nat,
      HasSecondOrderJet f (xSeq k) (JSeq k).gradient (JSeq k).hessian := by
    intro k
    simpa [JSeq, QJet, g] using
      (htwoSidedConv k).of_semiconvexConvexification (lambda := lambda)
  have hZ :
      Filter.Tendsto (fun k : Nat => (JSeq (φ k)).hessian)
        Filter.atTop (𝓝 Z) := by
    have hsub :
        Filter.Tendsto
          (fun k : Nat => (JSeqConv (φ k)).hessian - lambda • (1 : Hessian n))
          Filter.atTop (𝓝 (ZConv - lambda • (1 : Hessian n))) :=
      hZConv.sub tendsto_const_nhds
    simpa [JSeq, QJet, Z, quadraticModelJetAt] using hsub
  have hclosedConv :
      ({ gradient := 0, hessian := ZConv } : Jet n) ∈ ClosedSuperjet Set.univ g 0 :=
    closedSuperjet_of_tendsto_closedSuperjet
      (C := Set.univ) (u := g)
      (xᵢ := fun k : Nat => xSeq (φ k))
      (Jᵢ := fun k : Nat => JSeqConv (φ k))
      hx_subseq hvalueConv hJConvTendsto
      (Filter.Eventually.of_forall fun k => hclosedConvSeq (φ k))
  have hclosed :
      ({ gradient := 0, hessian := Z } : Jet n) ∈ ClosedSuperjet Set.univ f 0 := by
    simpa [Z, g] using
      closedSuperjet_of_closedSuperjet_semiconvexConvexification_at_zero
        lambda f ZConv hclosedConv
  have hZHerm : Z.IsHermitian := by
    exact hZConvHerm.sub hlambdaI
  have hlower : (-lambda) • (1 : Hessian n) <= Z := by
    calc
      (-lambda) • (1 : Hessian n) = (0 : Hessian n) - lambda • (1 : Hessian n) := by
        simp
      _ <= ZConv - lambda • (1 : Hessian n) := sub_le_sub_right hZConvNonneg _
  have hupper : Z <= B := by
    calc
      ZConv - lambda • (1 : Hessian n) <=
          (B + lambda • (1 : Hessian n)) - lambda • (1 : Hessian n) :=
        sub_le_sub_right hZConvLe _
      _ = B := by
        abel
  exact ⟨xSeq, JSeq, Z, φ, hJherm, htwoSided, hφ, hZ, hZHerm, hlower, hupper,
    hclosed⟩

/--
The convex-function form of the Aleksandrov--Jensen matrix theorem.

In quantified mathematical form, this says that for every continuous convex
function `g : R^n -> R` and every Hermitian matrix `B`, if
`x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0` on all of `R^n`, then
there exists a Hermitian matrix `Z` such that
`(0, Z) ∈ \overline J^{2,+}_{R^n} g(0)` and `0 ≤ Z ≤ B`.
-/
def AleksandrovJensenConvexMatrixTheorem (n : Nat) : Prop :=
  ∀ g : Point n -> Real, Continuous g ->
  ∀ B : Hessian n, B.IsHermitian ->
    ConvexOn Real Set.univ g ->
      IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0 ->
        SemiconvexMatrixConclusion 0 g B

/--
The localized Jensen contact-set theorem and localized Aleksandrov
second-differentiability theorem imply the convex Aleksandrov--Jensen matrix
theorem.
-/
theorem AleksandrovJensenConvexMatrixTheorem.of_localized_jensen_aleksandrov
    (hJensen : JensenContactSetPositiveMeasureOnClosedBallTheorem n)
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n) :
    AleksandrovJensenConvexMatrixTheorem n := by
  intro g hg B hB hconv hmax
  rcases exists_strictifiedQuadraticObjective_closedSuperjet_sequence_subsequence_graph_tendsto
      hJensen hAleksandrov hg hB hconv hmax with
    ⟨xSeq, _aSeq, _XSeq, JSeq, Z, φ, _hx_bound, _ha_bound, _hx_tendsto,
      _ha_tendsto, _hXherm, _hJherm, _hjet, _hJ, hclosed, _hupper, _hφ, _hZ,
      _hZherm, hZnonneg, hZleB, hx_subseq, hvalue, hJtendsto⟩
  have hZclosed :
      ({ gradient := 0, hessian := Z } : Jet n) ∈ ClosedSuperjet Set.univ g 0 :=
    closedSuperjet_of_tendsto_closedSuperjet
      (C := Set.univ) (u := g)
      (xᵢ := fun k : Nat => xSeq (φ k))
      (Jᵢ := fun k : Nat => JSeq (φ k))
      hx_subseq hvalue hJtendsto
      (Filter.Eventually.of_forall fun k => hclosed (φ k))
  refine ⟨Z, hZclosed, ?_, hZleB⟩
  simpa using hZnonneg

/--
The localized Jensen contact-set theorem has already been proved in this
file, so the convex Aleksandrov--Jensen matrix theorem follows from the
localized Aleksandrov second-differentiability theorem alone.
-/
theorem AleksandrovJensenConvexMatrixTheorem.of_aleksandrov
    (hAleksandrov : AleksandrovSecondDifferentiabilityByJetsOnClosedBallTheorem n) :
    AleksandrovJensenConvexMatrixTheorem n :=
  AleksandrovJensenConvexMatrixTheorem.of_localized_jensen_aleksandrov
    (n := n)
    (JensenContactSetPositiveMeasureOnClosedBallTheorem.proof (n := n))
    hAleksandrov

/--
The Aleksandrov--Jensen semiconvex matrix theorem in the convexified form.

In quantified mathematical form, this is the statement: for every continuous
`f : R^n -> R` and every Hermitian matrix `B`, if `0 ≤ lambda`, if
`x ↦ f x + (lambda / 2) * ∑ i, x_i^2` is convex on all of `R^n`, and if
`x ↦ f x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0` on all of `R^n`, then
there exists a Hermitian matrix `X` such that
`(0, X) ∈ \overline J^{2,+}_{R^n} f(0)` and `-lambda I ≤ X ≤ B`.
-/
def AleksandrovJensenSemiconvexMatrixTheoremOn (lambda : Real) : Prop :=
  ConvexifiedSemiconvexMatrixLemmaOn (n := n) lambda

/--
The convex-function Aleksandrov--Jensen theorem implies the semiconvex
Aleksandrov--Jensen theorem for each constant `lambda`.

In quantified mathematical form, apply the convex theorem to
`g x = f x + (lambda / 2) * ∑ i, x_i^2` and the matrix `B + lambda I`. The
closed-superjet conclusion for `g` is then transformed into the corresponding
closed-superjet conclusion for `f` by subtracting the quadratic jet.
-/
theorem AleksandrovJensenConvexMatrixTheorem.to_semiconvexMatrixTheoremOn
    (hconvex : AleksandrovJensenConvexMatrixTheorem n) (lambda : Real) :
    AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda := by
  intro _hlambda f hf B hB hconv hmax
  have hgcont : Continuous (semiconvexConvexification lambda f) := by
    exact hf.add (continuous_quadraticModel 0 0 0 (lambda • (1 : Hessian n)))
  have hlambdaI : (lambda • (1 : Hessian n)).IsHermitian :=
    Matrix.isHermitian_one.smul (IsSelfAdjoint.all lambda)
  have hBadd : (B + lambda • (1 : Hessian n)).IsHermitian :=
    hB.add hlambdaI
  have hmaxg :
      IsMaxOn
        (semiconvexQuadraticObjective (semiconvexConvexification lambda f)
          (B + lambda • (1 : Hessian n)))
        Set.univ 0 :=
    (isMaxOn_semiconvexQuadraticObjective_convexification_add_scalar_identity_iff
      lambda f B Set.univ 0).2 hmax
  exact SemiconvexMatrixConclusion.of_convexification_zero
    (hconvex (semiconvexConvexification lambda f) hgcont
      (B + lambda • (1 : Hessian n)) hBadd hconv hmaxg)

/--
The convex-function Aleksandrov--Jensen theorem implies the family of
semiconvex theorem statements for all constants.
-/
theorem AleksandrovJensenConvexMatrixTheorem.to_forall_semiconvexMatrixTheoremOn
    (hconvex : AleksandrovJensenConvexMatrixTheorem n) :
    ∀ lambda : Real, AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda :=
  fun lambda => hconvex.to_semiconvexMatrixTheoremOn lambda

/--
The public Aleksandrov--Jensen theorem target implies the coordinate
semiconvex formulation used in the comparison files.
-/
theorem AleksandrovJensenSemiconvexMatrixTheoremOn.to_semiconvexMatrixLemmaOn
    {lambda : Real}
    (h : AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda) :
    SemiconvexMatrixLemmaOn (n := n) lambda :=
  SemiconvexMatrixLemmaOn.of_convexified h

/--
The coordinate semiconvex formulation and the public convexified
Aleksandrov--Jensen formulation are equivalent.
-/
theorem semiconvexMatrixLemmaOn_iff_aleksandrovJensenSemiconvexMatrixTheoremOn
    {lambda : Real} :
    SemiconvexMatrixLemmaOn (n := n) lambda ↔
      AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda :=
  semiconvexMatrixLemmaOn_iff_convexifiedSemiconvexMatrixLemmaOn

/--
Apply the public Aleksandrov--Jensen theorem target to a compact
sup-convolution.
-/
theorem AleksandrovJensenSemiconvexMatrixTheoremOn.compactSupConvolution_of_isCompact
    {lambda : Real}
    (hAJ : AleksandrovJensenSemiconvexMatrixTheoremOn (n := n) lambda)
    (hlambda : 0 <= lambda) {K : Set (Point n)} {v : Point n -> Real}
    (hKne : K.Nonempty) (hKcompact : IsCompact K)
    (hv : UpperSemicontinuousOn v K) {B : Hessian n}
    (hB : B.IsHermitian)
    (hmax : IsMaxOn
      (semiconvexQuadraticObjective
        (fun ξ : Point n => compactSupConvolution lambda K v ξ) B)
      Set.univ 0) :
    SemiconvexMatrixConclusion lambda
      (fun ξ : Point n => compactSupConvolution lambda K v ξ) B := by
  exact hAJ.to_semiconvexMatrixLemmaOn.compactSupConvolution_of_isCompact
    hlambda hKne hKcompact hv hB hmax

end ViscositySolns
