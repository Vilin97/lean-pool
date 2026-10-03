/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import LeanPool.ViscositySolutionTheory.ViscositySolns.Analysis.SemiconvexJensen.Aleksandrov.JetCalculus.Strictification.CoordinateQuartic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Strictification and jet bridges for the Aleksandrov--Jensen argument (StrictifiedObjective)

Part of the quartic strictification, compact Hessian, and jet transport
development used before the contact-set and approximation arguments in
`SemiconvexJensen`. Split from `Strictification.lean`; see the umbrella
module docstring.
-/

@[expose] public noncomputable section

open scoped ContDiff MatrixOrder Topology
open scoped ENNReal

open ContinuousLinearMap MeasureTheory

namespace ViscositySolns

variable {n : Nat}

/--
The entrywise closed box of Hessian matrices with entries in `[-R, R]`.
-/
def hessianEntryBox (n : Nat) (R : Real) : Set (Hessian n) :=
  {A | ∀ i j : Fin n, A i j ∈ Set.Icc (-R) R}

/--
The entrywise closed box of Hessian matrices is compact.
-/
theorem isCompact_hessianEntryBox (R : Real) :
    IsCompact (hessianEntryBox n R) := by
  have hcompact :
      IsCompact
        (Set.pi Set.univ fun _i : Fin n =>
          Set.pi Set.univ fun _j : Fin n => Set.Icc (-R) R) :=
    isCompact_univ_pi fun _i : Fin n =>
      isCompact_univ_pi fun _j : Fin n => isCompact_Icc
  have hset :
      hessianEntryBox n R =
        (Set.pi Set.univ fun _i : Fin n =>
          Set.pi Set.univ fun _j : Fin n => Set.Icc (-R) R) := by
    ext A
    constructor
    · intro hA i _hi j _hj
      exact hA i j
    · intro hA i j
      exact hA i (Set.mem_univ i) j (Set.mem_univ j)
  rw [hset]
  exact hcompact

/--
Every eventually entrywise-bounded sequence of Hessian matrices has a
convergent subsequence.

In standard mathematical terms, if there is a real number `R` such that
`|A_k i j| ≤ R` for every pair of coordinates `(i,j)` and all sufficiently
large `k`, then there exist a Hessian `Z` and a strictly increasing sequence
of indices `φ : Nat -> Nat` such that `A_{φ(k)} -> Z`.
-/
theorem exists_hessian_subsequence_tendsto_of_eventually_entrywise_abs_le
    {A : Nat -> Hessian n} {R : Real}
    (hbound : ∀ᶠ k in Filter.atTop, ∀ i j : Fin n, |A k i j| <= R) :
    ∃ Z : Hessian n, ∃ φ : Nat -> Nat, StrictMono φ ∧
      Filter.Tendsto (fun k : Nat => A (φ k)) Filter.atTop (𝓝 Z) := by
  have : FirstCountableTopology (Hessian n) :=
    inferInstanceAs (FirstCountableTopology (Fin n -> Fin n -> Real))
  have hevent :
      ∀ᶠ k in Filter.atTop, A k ∈ hessianEntryBox n R := by
    filter_upwards [hbound] with k hk
    intro i j
    exact abs_le.mp (hk i j)
  rcases (isCompact_hessianEntryBox (n := n) R).tendsto_subseq'
      hevent.frequently with
    ⟨Z, _hZ, φ, hφ, hlim⟩
  exact ⟨Z, φ, hφ, hlim⟩

/--
For a positive semidefinite Hessian matrix, every off-diagonal entry is
bounded in absolute value by half the sum of the corresponding diagonal
entries.

In standard mathematical terms, if `A` is positive semidefinite, then
`|A_{ij}| ≤ (A_{ii} + A_{jj}) / 2`. This follows by applying nonnegativity
of the quadratic form associated to `A` to the two vectors `e_i + e_j` and
`e_i - e_j`.
-/
theorem abs_hessian_entry_le_half_diag_sum_of_posSemidef
    {A : Hessian n} (hA : A.PosSemidef) (i j : Fin n) :
    |A i j| <= (A i i + A j j) / 2 := by
  have hplus :=
    hA.dotProduct_mulVec_nonneg (coordinateVector i + coordinateVector j)
  have hminus :=
    hA.dotProduct_mulVec_nonneg (coordinateVector i - coordinateVector j)
  have hsym : A j i = A i j := by
    simpa using hA.isHermitian.apply i j
  have hplus' : 0 <= A i i + A j i + (A i j + A j j) := by
    simpa [dotProduct, Matrix.mulVec, coordinateVector, Finset.sum_add_distrib,
      add_mul, mul_add] using hplus
  have hminus' : A i j <= A i i - A j i + A j j := by
    simpa [dotProduct, Matrix.mulVec, coordinateVector, Finset.sum_sub_distrib,
      sub_mul, mul_sub] using hminus
  rw [hsym] at hplus' hminus'
  rw [abs_le]
  constructor <;> nlinarith

/--
If `0 ≤ A` and all diagonal entries of `A` are bounded above by `R`, then
all entries of `A` are bounded in absolute value by `R`.
-/
theorem abs_hessian_entry_le_of_posSemidef_of_diag_le
    {A : Hessian n} {R : Real} (hA : A.PosSemidef)
    (hdiag : ∀ i : Fin n, A i i <= R) :
    ∀ i j : Fin n, |A i j| <= R := by
  intro i j
  have hentry := abs_hessian_entry_le_half_diag_sum_of_posSemidef hA i j
  have hii : A i i <= R := hdiag i
  have hjj : A j j <= R := hdiag j
  linarith

/--
Uniform Loewner lower and upper bounds give eventual entrywise boundedness
when the upper-error matrices converge entrywise to zero.

In standard mathematical terms, if `A_k` is positive semidefinite for every
`k`, if `A_k ≤ Q_k + B` for every `k`, and if `Q_k -> 0`, then there is a real
number `R` such that `|A_k i j| ≤ R` for every pair of coordinates `(i,j)` and
all sufficiently large `k`.
-/
theorem exists_eventually_entrywise_abs_le_of_posSemidef_le_add_tendsto_zero
    {A Q : Nat -> Hessian n} {B : Hessian n}
    (hA : ∀ k : Nat, (A k).PosSemidef)
    (hupper : ∀ k : Nat, A k <= Q k + B)
    (hQ : Filter.Tendsto Q Filter.atTop (𝓝 (0 : Hessian n))) :
    ∃ R : Real, ∀ᶠ k in Filter.atTop, ∀ i j : Fin n, |A k i j| <= R := by
  classical
  let R : Real := (∑ i : Fin n, |B i i|) + 1
  refine ⟨R, ?_⟩
  have hQsmall :
      ∀ᶠ k in Filter.atTop, ∀ i j : Fin n, |Q k i j| < 1 := by
    have hnear :
        ∀ᶠ Y in 𝓝 (0 : Hessian n), ∀ i j : Fin n, |(Y - 0) i j| < 1 :=
      hessian_eventually_entrywise_abs_sub_lt (n := n) (0 : Hessian n) zero_lt_one
    have hnear' :
        ∀ᶠ Y in 𝓝 (0 : Hessian n), ∀ i j : Fin n, |Y i j| < 1 := by
      filter_upwards [hnear] with Y hY i j
      simpa using hY i j
    exact hQ hnear'
  filter_upwards [hQsmall] with k hk
  have hdiag : ∀ i : Fin n, A k i i <= R := by
    intro i
    have hdiffpsd : ((Q k + B) - A k).PosSemidef :=
      Matrix.le_iff.mp (hupper k)
    have hdiagdiff : 0 <= ((Q k + B) - A k) i i :=
      hdiffpsd.diag_nonneg
    have hQii_abs : |Q k i i| <= 1 := (hk i i).le
    have hBii_le_sum : |B i i| <= ∑ j : Fin n, |B j j| :=
      Finset.single_le_sum (fun j _ => abs_nonneg (B j j)) (Finset.mem_univ i)
    have hQii_le : Q k i i <= 1 := (le_abs_self (Q k i i)).trans hQii_abs
    have hBii_le : B i i <= ∑ j : Fin n, |B j j| :=
      (le_abs_self (B i i)).trans hBii_le_sum
    simp only [Matrix.sub_apply, Matrix.add_apply] at hdiagdiff
    dsimp [R]
    linarith
  exact abs_hessian_entry_le_of_posSemidef_of_diag_le (hA k) hdiag

/-- The quadratic form associated to a Hessian matrix is continuous in the matrix. -/
theorem continuous_hessian_quadraticForm (v : Point n) :
    Continuous fun A : Hessian n => dotProduct v (Matrix.mulVec A v) :=
  continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)

/--
Hermitian Hessian matrices are closed under sequential limits.

In standard mathematical terms, if `A_k -> Z` entrywise and every `A_k` is
Hermitian, then `Z` is Hermitian.
-/
theorem hessian_isHermitian_of_tendsto_isHermitian
    {A : Nat -> Hessian n} {Z : Hessian n}
    (hA : Filter.Tendsto A Filter.atTop (𝓝 Z))
    (hHerm : ∀ k : Nat, (A k).IsHermitian) :
    Z.IsHermitian := by
  refine Matrix.IsHermitian.ext ?_
  intro i j
  have hji :
      Filter.Tendsto (fun k : Nat => A k j i) Filter.atTop (𝓝 (Z j i)) :=
    (continuous_hessian_apply_apply (n := n) j i).continuousAt.tendsto.comp hA
  have hij :
      Filter.Tendsto (fun k : Nat => A k j i) Filter.atTop (𝓝 (Z i j)) := by
    have hij_raw :
        Filter.Tendsto (fun k : Nat => A k i j) Filter.atTop (𝓝 (Z i j)) :=
      (continuous_hessian_apply_apply (n := n) i j).continuousAt.tendsto.comp hA
    convert hij_raw using 1
    ext k
    simpa using (hHerm k).apply i j
  have hlim : Z i j = Z j i := tendsto_nhds_unique hij hji
  simp [hlim]

/--
Loewner inequalities are closed under sequential limits.

In standard mathematical terms, if `A_k -> Z`, `C_k -> W`, and
`A_k ≤ C_k` for all sufficiently large `k`, then `Z ≤ W`, provided `Z` and
`W` are Hermitian.
-/
theorem hessian_le_of_tendsto_le
    {A C : Nat -> Hessian n} {Z W : Hessian n}
    (hA : Filter.Tendsto A Filter.atTop (𝓝 Z))
    (hC : Filter.Tendsto C Filter.atTop (𝓝 W))
    (hZ : Z.IsHermitian) (hW : W.IsHermitian)
    (hle : ∀ᶠ k in Filter.atTop, A k <= C k) :
    Z <= W := by
  rw [Matrix.le_iff]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hW.sub hZ) ?_
  intro v
  have hdiff :
      Filter.Tendsto (fun k : Nat => C k - A k) Filter.atTop (𝓝 (W - Z)) :=
    hC.sub hA
  have hquad :
      Filter.Tendsto
        (fun k : Nat => dotProduct v (Matrix.mulVec (C k - A k) v))
        Filter.atTop
        (𝓝 (dotProduct v (Matrix.mulVec (W - Z) v))) :=
    (continuous_hessian_quadraticForm (n := n) v).continuousAt.tendsto.comp hdiff
  have hnonneg :
      ∀ᶠ k in Filter.atTop, 0 <= dotProduct v (Matrix.mulVec (C k - A k) v) := by
    filter_upwards [hle] with k hk
    have hpsd : (C k - A k).PosSemidef := Matrix.le_iff.mp hk
    simpa using hpsd.dotProduct_mulVec_nonneg v
  exact isClosed_Ici.mem_of_tendsto hquad hnonneg

/--
Positive semidefiniteness is closed under sequential limits of Hermitian
Hessian matrices.
-/
theorem hessian_nonneg_of_tendsto_nonneg
    {A : Nat -> Hessian n} {Z : Hessian n}
    (hA : Filter.Tendsto A Filter.atTop (𝓝 Z))
    (hZ : Z.IsHermitian)
    (hnonneg : ∀ᶠ k in Filter.atTop, 0 <= A k) :
    0 <= Z := by
  have hzero : Filter.Tendsto (fun _k : Nat => (0 : Hessian n))
      Filter.atTop (𝓝 (0 : Hessian n)) :=
    tendsto_const_nhds
  exact hessian_le_of_tendsto_le hzero hA Matrix.isHermitian_zero hZ hnonneg

/--
Subtract the coordinate quartic from a function.
-/
def quarticStrictification (f : Point n -> Real) : Point n -> Real :=
  fun x => f x - coordinateQuartic x

/--
If `f` has a global maximum at the origin, then
`x ↦ f x - (∑ i, x_i^2)^2` has a strict local maximum at the origin.
-/
theorem strictLocalMax_quarticStrictification_of_isMaxOn_univ
    {f : Point n -> Real} (hmax : IsMaxOn f Set.univ 0) :
    StrictLocalMax (quarticStrictification f) 0 := by
  refine ⟨Set.univ, Filter.univ_mem, ?_⟩
  intro x _hx hxne
  have hle : f x <= f 0 := hmax trivial
  have hquartic_pos : 0 < coordinateQuartic x := coordinateQuartic_pos_of_ne_zero hxne
  have hstrict : f x - coordinateQuartic x < f 0 - 0 := by linarith
  simpa [quarticStrictification] using hstrict

/--
The strictified quadratic objective used in the proof of the convex matrix
theorem.

In quantified mathematical form, this is
`x ↦ g x - (1 / 2) * ⟪B x, x⟫ - (∑ i, x_i^2)^2`.
-/
def strictifiedQuadraticObjective (g : Point n -> Real) (B : Hessian n) :
    Point n -> Real :=
  quarticStrictification (semiconvexQuadraticObjective g B)

/--
The strictified quadratic objective is semiconvex on every closed ball, with
an explicit constant from an entrywise bound on the quadratic matrix.

In quantified mathematical form, suppose `g` is convex on `R^n`, `0 ≤ r`,
`0 ≤ η`, and `|Bᵢⱼ| ≤ η` for every matrix entry. Then

`x ↦ g x - (1 / 2) * ⟪B x, x⟫ - (∑ i x_i^2)^2`

satisfies the coordinate semiconvexity inequality on `closedBall 0 r` with
constant

`η n^2 + 2 * (4 n^2 r^2 + 2 n r^2)`.
-/
theorem coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall_of_entrywise_abs_le
    {g : Point n -> Real} {B : Hessian n} {r eta : Real}
    (hconv : ConvexOn Real Set.univ g) (hr : 0 <= r) (heta : 0 <= eta)
    (hB : ∀ i j : Fin n, |B i j| <= eta) :
    CoordinateSemiconvexOn
      (eta * (n : Real) * (n : Real) +
        2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2))
      (Metric.closedBall (0 : Point n) r)
      (strictifiedQuadraticObjective g B) := by
  let C : Set (Point n) := Metric.closedBall (0 : Point n) r
  have hg :
      CoordinateSemiconvexOn (0 : Real) C g :=
    (ConvexOn.coordinateSemiconvexOn_zero (n := n) hconv).mono_set
      (by intro x _hx; trivial)
  have hquad :
      CoordinateSemiconvexOn (eta * (n : Real) * (n : Real)) C
        (fun x : Point n => -quadraticModel 0 0 0 B x) :=
    coordinateSemiconvexOn_neg_quadraticModel_of_entrywise_abs_le
      (n := n) (C := C) B heta hB
  have hquartic :
      CoordinateSemiconvexOn
        (2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2)) C
        (fun x : Point n => -coordinateQuartic x) :=
    coordinateSemiconvexOn_neg_coordinateQuartic_closedBall (n := n) hr
  have hsum := (hg.add hquad).add hquartic
  have htarget :
      CoordinateSemiconvexOn
        (eta * (n : Real) * (n : Real) +
          2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2))
        C (strictifiedQuadraticObjective g B) := by
    simpa using hsum.congr fun x _hx => by
      unfold strictifiedQuadraticObjective quarticStrictification semiconvexQuadraticObjective
      ring
  simpa [C] using htarget

/--
The strictified quadratic objective is semiconvex on every closed ball.

In quantified mathematical form, if `g` is convex on `R^n` and `0 ≤ r`, then
there exists a real number `lambda` such that

`x ↦ g x - (1 / 2) * ⟪B x, x⟫ - (∑ i x_i^2)^2`

satisfies the coordinate semiconvexity inequality with constant `lambda` on
`closedBall 0 r`.
-/
theorem exists_coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall
    {g : Point n -> Real} (B : Hessian n) {r : Real}
    (hconv : ConvexOn Real Set.univ g) (hr : 0 <= r) :
    ∃ lambda : Real,
      CoordinateSemiconvexOn lambda (Metric.closedBall (0 : Point n) r)
        (strictifiedQuadraticObjective g B) := by
  let eta : Real := ∑ i : Fin n, ∑ j : Fin n, |B i j|
  have heta : 0 <= eta := by
    exact Finset.sum_nonneg fun i _hi =>
      Finset.sum_nonneg fun j _hj => abs_nonneg (B i j)
  have hB : ∀ i j : Fin n, |B i j| <= eta := by
    intro i j
    calc
      |B i j| <= ∑ j : Fin n, |B i j| := by
        exact Finset.single_le_sum (fun k _hk => abs_nonneg (B i k)) (Finset.mem_univ j)
      _ <= eta := by
        exact Finset.single_le_sum
          (fun k _hk => Finset.sum_nonneg fun l _hl => abs_nonneg (B k l))
          (Finset.mem_univ i)
  exact ⟨eta * (n : Real) * (n : Real) +
      2 * (4 * (n : Real) ^ 2 * r ^ 2 + 2 * (n : Real) * r ^ 2),
    coordinateSemiconvexOn_strictifiedQuadraticObjective_closedBall_of_entrywise_abs_le
      (n := n) (B := B) hconv hr heta hB⟩

/--
If `x ↦ g x - (1 / 2) * ⟪B x, x⟫` has a maximum at `0` on all of `R^n`, then
the strictified quadratic objective has a strict local maximum at `0`.
-/
theorem strictLocalMax_strictifiedQuadraticObjective_of_isMaxOn_univ
    {g : Point n -> Real} {B : Hessian n}
    (hmax : IsMaxOn (semiconvexQuadraticObjective g B) Set.univ 0) :
    StrictLocalMax (strictifiedQuadraticObjective g B) 0 :=
  strictLocalMax_quarticStrictification_of_isMaxOn_univ hmax

/--
Adding back the coordinate quartic converts a superjet of the strictified
quadratic objective into a superjet of the unstrictified quadratic objective.
-/
theorem HasSecondOrderJet.superjet_semiconvexQuadraticObjective_of_strictified
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    ({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x ∈
      Superjet Set.univ (semiconvexQuadraticObjective g B) x := by
  have hraw :=
    superjet_add_hasSecondOrderExpansionWithin
      (C := Set.univ)
      (u := strictifiedQuadraticObjective g B)
      (φ := coordinateQuartic (n := n))
      (x := x)
      (J := ({ gradient := a, hessian := X } : Jet n))
      (A := coordinateQuarticJetAt x)
      h.1
      (hasSecondOrderExpansionWithin_coordinateQuartic_univ (n := n) x)
  have hfun :
      (fun y : Point n => strictifiedQuadraticObjective g B y + coordinateQuartic y) =
        semiconvexQuadraticObjective g B := by
    funext y
    simp [strictifiedQuadraticObjective, quarticStrictification]
  simpa [hfun] using hraw

/--
Adding back the coordinate quartic converts a subjet of the strictified
quadratic objective into a subjet of the unstrictified quadratic objective.
-/
theorem HasSecondOrderJet.subjet_semiconvexQuadraticObjective_of_strictified
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    ({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x ∈
      Subjet Set.univ (semiconvexQuadraticObjective g B) x := by
  have hraw :=
    subjet_add_hasSecondOrderExpansionWithin
      (C := Set.univ)
      (u := strictifiedQuadraticObjective g B)
      (φ := coordinateQuartic (n := n))
      (x := x)
      (J := ({ gradient := a, hessian := X } : Jet n))
      (A := coordinateQuarticJetAt x)
      h.2
      (hasSecondOrderExpansionWithin_coordinateQuartic_univ (n := n) x)
  have hfun :
      (fun y : Point n => strictifiedQuadraticObjective g B y + coordinateQuartic y) =
        semiconvexQuadraticObjective g B := by
    funext y
    simp [strictifiedQuadraticObjective, quarticStrictification]
  simpa [hfun] using hraw

/--
Adding back both smooth terms converts a two-sided jet of the strictified
quadratic objective into a superjet of the original function.
-/
theorem HasSecondOrderJet.superjet_of_strictifiedQuadraticObjective
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x ∈ Superjet Set.univ g x := by
  have hsemi :=
    h.superjet_semiconvexQuadraticObjective_of_strictified
      (g := g) (B := B) (x := x) (a := a) (X := X)
  have hraw :=
    superjet_add_hasSecondOrderExpansionWithin
      (C := Set.univ)
      (u := semiconvexQuadraticObjective g B)
      (φ := fun y : Point n => quadraticModel 0 0 0 B y)
      (x := x)
      (J := ({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x)
      (A := quadraticModelJetAt 0 0 B x)
      hsemi
      (hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := Set.univ) (x0 := 0) (r := 0) (p := 0) (X := B) x)
  have hfun :
      (fun y : Point n => semiconvexQuadraticObjective g B y +
        quadraticModel 0 0 0 B y) = g := by
    funext y
    simp [semiconvexQuadraticObjective]
  simpa [hfun] using hraw

/--
Adding back both smooth terms converts a two-sided jet of the strictified
quadratic objective into a subjet of the original function.
-/
theorem HasSecondOrderJet.subjet_of_strictifiedQuadraticObjective
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x ∈ Subjet Set.univ g x := by
  have hsemi :=
    h.subjet_semiconvexQuadraticObjective_of_strictified
      (g := g) (B := B) (x := x) (a := a) (X := X)
  have hraw :=
    subjet_add_hasSecondOrderExpansionWithin
      (C := Set.univ)
      (u := semiconvexQuadraticObjective g B)
      (φ := fun y : Point n => quadraticModel 0 0 0 B y)
      (x := x)
      (J := ({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x)
      (A := quadraticModelJetAt 0 0 B x)
      hsemi
      (hasSecondOrderExpansionWithin_quadraticModel_recenter
        (C := Set.univ) (x0 := 0) (r := 0) (p := 0) (X := B) x)
  have hfun :
      (fun y : Point n => semiconvexQuadraticObjective g B y +
        quadraticModel 0 0 0 B y) = g := by
    funext y
    simp [semiconvexQuadraticObjective]
  simpa [hfun] using hraw

/--
Adding back the quartic and quadratic terms converts a two-sided jet of the
strictified quadratic objective into a two-sided jet of the original function.
-/
theorem HasSecondOrderJet.of_strictifiedQuadraticObjective
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    HasSecondOrderJet g x
      (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
          quadraticModelJetAt 0 0 B x).gradient)
      (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
          quadraticModelJetAt 0 0 B x).hessian) := by
  exact ⟨h.superjet_of_strictifiedQuadraticObjective,
    h.subjet_of_strictifiedQuadraticObjective⟩

/--
The selected jet obtained by adding back the quartic and quadratic terms is
an ordinary two-sided jet of the original function.
-/
theorem HasSecondOrderJet.of_eq_strictifiedQuadraticObjectiveJet
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    {J : Jet n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X)
    (hJ : J =
      (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x) :
    HasSecondOrderJet g x J.gradient J.hessian := by
  rw [hJ]
  exact h.of_strictifiedQuadraticObjective

/--
A two-sided jet of the strictified quadratic objective gives a closed superjet
of the original function after adding back the quartic and quadratic jets.
-/
theorem HasSecondOrderJet.closedSuperjet_of_strictifiedQuadraticObjective
    {g : Point n -> Real} {B : Hessian n} {x a : Point n} {X : Hessian n}
    (h : HasSecondOrderJet (strictifiedQuadraticObjective g B) x a X) :
    (({ gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x ∈ ClosedSuperjet Set.univ g x :=
  superjet_subset_closedSuperjet (C := Set.univ) (x := x) trivial
    h.superjet_of_strictifiedQuadraticObjective

/--
The Hessian component of the closed-superjet jet obtained by adding back the
quartic and quadratic terms.
-/
theorem strictifiedQuadraticObjective_closedSuperjetJet_hessian
    (B : Hessian n) (x a : Point n) (X : Hessian n) :
    (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x).hessian) =
      X + (coordinateQuarticJetAt x).hessian + B := by
  simp [quadraticModelJetAt]

/--
If the Hessian from the two-sided jet and the quadratic matrix are Hermitian,
then the Hessian component of the resulting closed-superjet jet is Hermitian.
-/
theorem strictifiedQuadraticObjective_closedSuperjetJet_hessian_isHermitian
    {B : Hessian n} {x a : Point n} {X : Hessian n}
    (hX : X.IsHermitian) (hB : B.IsHermitian) :
    (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x).hessian).IsHermitian := by
  rw [strictifiedQuadraticObjective_closedSuperjetJet_hessian]
  exact (hX.add (coordinateQuarticJetAt_hessian_isHermitian (n := n) x)).add hB

/--
The local-maximum inequality `X ≤ 0` gives the upper bound for the Hessian of
the closed-superjet jet obtained from the strictified quadratic objective.
-/
theorem strictifiedQuadraticObjective_closedSuperjetJet_hessian_le
    {B : Hessian n} {x a : Point n} {X : Hessian n} (hX : X <= 0) :
    (((( { gradient := a, hessian := X } : Jet n) + coordinateQuarticJetAt x) +
        quadraticModelJetAt 0 0 B x).hessian) <=
      (coordinateQuarticJetAt x).hessian + B := by
  rw [strictifiedQuadraticObjective_closedSuperjetJet_hessian]
  rw [Matrix.le_iff] at hX ⊢
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hX
end ViscositySolns
