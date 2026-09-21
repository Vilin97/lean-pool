/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismGenericityNonzero
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.FiniteMultivariateGenericPerturbation
/-!
# Simultaneous generic perturbation of the equivariant refined prism

The orbit-parameter construction already enforces shared-face compatibility and prime equivariance.
The polynomial layer records all local facet determinants and codimension-two deviation minors, and
all of those polynomials are nonzero.  This module applies the finite multivariate perturbation
mechanism at the assignment obtained by sampling a zero-free equivariant homotopy.

There is one quantitative subtlety.  The parameter `t` in
`FiniteMultivariateGenericPerturbation.exists_small_positive_generic` is small, but its target
assignment is not a priori bounded, so that statement alone does not imply that the resulting
assignment is close to the base assignment.  We therefore use it once to obtain a generic target,
then apply the finite univariate root-avoidance theorem on the line from the base assignment to that
generic target.  The second parameter is chosen using the finite `L¹` size of the direction.  The
result is genuinely coordinatewise close to the homotopy assignment.

The final theorem assumes a positive coordinate form of the zero-free norm margin for the affine
interpolation of the unperturbed homotopy samples.  This is the exact quantitative hypothesis that
must later be supplied by sufficiently fine spatial and staircase subdivision.  The perturbation
retains half of that margin, while polynomial nonvanishing gives facet regularity and
codimension-two avoidance on every refined prism simplex.
-/

namespace NRR

open scoped BigOperators
open MvPolynomial Polynomial
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismGenericPerturbation

open AffinePositiveRayBoundary
open EquivariantCoordinateHomotopy
open EquivariantPrismVertexParameters
open EquivariantPrismGenericityPolynomials
open EquivariantPrismGenericityNonzero
open SubdivisionPrismCharts

variable {p : Nat}

/-! ## A genuinely small generic multivariate perturbation -/

/-- Pointwise coordinate closeness of two finite parameter assignments. -/
def AssignmentClose {J : Type*} (a b : J → Real) (eps : Real) : Prop :=
  ∀ j, |a j - b j| < eps

/-- A finite family of nonzero multivariate polynomials admits a simultaneously nonvanishing
assignment which is genuinely pointwise close to any prescribed base assignment.

The first application of `exists_small_positive_generic` supplies a generic assignment.  A second,
univariate root-avoidance step moves an arbitrarily small positive distance from the base assignment
toward that generic point. -/
theorem exists_generic_assignment_close
    {J I : Type*} [Fintype J] [Fintype I]
    (P : I → MvPolynomial J Real) (hP : ∀ i, P i ≠ 0)
    (a : J → Real) {eps : Real} (heps : 0 < eps) :
    ∃ a' : J → Real,
      AssignmentClose a' a eps ∧
        ∀ i, MvPolynomial.eval a' (P i) ≠ 0 := by
  classical
  obtain ⟨b, t₀, ht₀, ht₀one, hgeneric₀⟩ :=
    FiniteMultivariateGenericPerturbation.exists_small_positive_generic
      P hP a (show (0 : Real) < 1 by positivity)
  let c : J → Real := fun j => a j + t₀ * (b j - a j)
  have hc : ∀ i, MvPolynomial.eval c (P i) ≠ 0 := by
    intro i
    simpa [c] using hgeneric₀ i
  let Q : I → Real[X] := fun i =>
    FiniteMultivariateGenericPerturbation.linePolynomial a c (P i)
  have hQ : ∀ i, Q i ≠ 0 := by
    intro i
    exact FiniteMultivariateGenericPerturbation.linePolynomial_ne_zero_of_target
      a c (P i) (hc i)
  let D : Real := (∑ j : J, |c j - a j|) + 1
  have hD : 0 < D := by
    dsimp [D]
    have : 0 ≤ ∑ j : J, |c j - a j| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  let delta : Real := min 1 (eps / D)
  have hdelta : 0 < delta := by
    dsimp [delta]
    exact lt_min_iff.mpr ⟨zero_lt_one, div_pos heps hD⟩
  obtain ⟨s, hs0, hsdelta, hsavoid⟩ :=
    FiniteGenericPerturbation.exists_small_positive_avoiding Q hQ hdelta
  let a' : J → Real := fun j => a j + s * (c j - a j)
  refine ⟨a', ?_, ?_⟩
  · intro j
    have hjle : |c j - a j| ≤ ∑ k : J, |c k - a k| := by
      exact Finset.single_le_sum
        (fun k _ => abs_nonneg (c k - a k)) (Finset.mem_univ j)
    have hjD : |c j - a j| < D := by
      dsimp [D]
      linarith
    have hsratio : s < eps / D :=
      lt_of_lt_of_le hsdelta (min_le_right _ _)
    have hfirst : s * |c j - a j| < s * D :=
      mul_lt_mul_of_pos_left hjD hs0
    have hsecond : s * D < (eps / D) * D :=
      mul_lt_mul_of_pos_right hsratio hD
    have hcancel : (eps / D) * D = eps := by
      field_simp [ne_of_gt hD]
    calc
      |a' j - a j| = s * |c j - a j| := by
        simp [a', abs_mul, abs_of_pos hs0]
      _ < s * D := hfirst
      _ < (eps / D) * D := hsecond
      _ = eps := hcancel
  · intro i
    have hi := hsavoid i
    simpa [Q, a',
      FiniteMultivariateGenericPerturbation.eval_linePolynomial] using hi


/-- A local scalar coordinate is exactly the corresponding global orbit parameter. -/
@[simp] theorem localVertexValue_apply_eq_assignment_localParameter
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L)
    (i : Fin (p + 1)) (j : Fin p) :
    localVertexValue hp N L a q i j =
      a (localParameter hp N L q i j) := rfl

/-! ## From polynomial nonvanishing to local general position -/

/-- All ordered codimension-two deviation minors of one reconstructed local vertex map are
nonsingular. -/
def CodimTwoMinorRegular
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) : Prop :=
  ∀ f : CodimTwoFace p,
    Matrix.det (codimTwoDeviationMatrix hp N L a q f) ≠ 0

/-- Nonvanishing of the facet part of the combined polynomial family gives facet regularity on
one local refined prism simplex. -/
theorem facetRegular_of_generic
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgeneric : ∀ i : GenericityIndex hp N L,
      MvPolynomial.eval a (genericityPolynomial hp N L i) ≠ 0)
    (q : PrismCell hp N L) :
    AffinePositiveRayBoundary.VertexMap.FacetRegular hp (localVertexMap hp N L a q) := by
  intro k
  have h := hgeneric (Sum.inl (q, k))
  rw [eval_genericityPolynomial] at h
  exact h

/-- Nonvanishing of the minor part of the combined polynomial family gives nonsingularity of every
ordered codimension-two deviation matrix on one local refined prism simplex. -/
theorem codimTwoMinorRegular_of_generic
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgeneric : ∀ i : GenericityIndex hp N L,
      MvPolynomial.eval a (genericityPolynomial hp N L i) ≠ 0)
    (q : PrismCell hp N L) :
    CodimTwoMinorRegular hp N L a q := by
  intro f
  have h := hgeneric (Sum.inr (q, f))
  rw [eval_genericityPolynomial] at h
  exact h

/-- The index of `j` after omitting the distinct index `i`. -/
noncomputable def omittedIndex
    (i j : Fin (p + 1)) (hij : i ≠ j) : Fin p :=
  Classical.choose (Fin.exists_succAbove_eq hij.symm)

@[simp] theorem succAbove_omittedIndex
    (i j : Fin (p + 1)) (hij : i ≠ j) :
    i.succAbove (omittedIndex i j hij) = j :=
  Classical.choose_spec (Fin.exists_succAbove_eq hij.symm)

/-- The ordered codimension-two vertex enumeration exhausts all vertices except the two omitted
ones.  This sum identity is the bridge from the minor determinant to barycentric avoidance. -/
theorem sum_codimTwoVertex
    (hp : Nat.Prime p)
    (F : Fin (p + 1) → Real)
    (i j : Fin (p + 1)) (hij : i ≠ j)
    (hi : F i = 0) (hj : F j = 0) :
    ∑ k : Fin (p + 1), F k =
      ∑ c : Fin (p - 1),
        F (codimTwoVertex hp (i, omittedIndex i j hij) c) := by
  classical
  rw [Fin.sum_univ_succAbove F i, hi, zero_add]
  let e : Fin p ≃ Fin ((p - 1) + 1) :=
    (Fin.castOrderIso (Nat.sub_add_cancel hp.pos).symm).toEquiv
  let G : Fin ((p - 1) + 1) → Real := fun k =>
    F (i.succAbove (Fin.cast (Nat.sub_add_cancel hp.pos) k))
  calc
    (∑ k : Fin p, F (i.succAbove k)) = ∑ k : Fin p, G (e k) := by
      apply Finset.sum_congr rfl
      intro k _
      simp [G, e]
    _ = ∑ k : Fin ((p - 1) + 1), G k := Equiv.sum_comp e G
    _ = G (secondOmissionIndex hp (i, omittedIndex i j hij)) +
        ∑ c : Fin (p - 1),
          G ((secondOmissionIndex hp (i, omittedIndex i j hij)).succAbove c) :=
      Fin.sum_univ_succAbove G _
    _ = ∑ c : Fin (p - 1),
        F (codimTwoVertex hp (i, omittedIndex i j hij) c) := by
      simp [G, secondOmissionIndex, codimTwoVertex,
        succAbove_omittedIndex, hj]

/-- Nonsingularity of every ordered codimension-two deviation matrix rules out a deviation-zero
point on a codimension-two face. -/
theorem avoidsCodimTwo_of_minorRegular
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L)
    (hminor : CodimTwoMinorRegular hp N L a q) :
    AffinePositiveRayBoundary.VertexMap.AvoidsCodimTwoDeviationZero hp
      (localVertexMap hp N L a q) := by
  intro w i j hij hdev hzeros
  let f : CodimTwoFace p := (i, omittedIndex i j hij)
  let x : Fin (p - 1) → Real :=
    fun c => w (codimTwoVertex hp f c)
  have hmul :
      (codimTwoDeviationMatrix hp N L a q f).mulVec x = 0 := by
    funext r
    change (codimTwoDeviationMatrix hp N L a q f).mulVec x r = (0 : Real)
    have hsum :
        ∑ k : Fin (p + 1),
          w k * VertexMap.deviation hp
            ((localVertexMap hp N L a q).value k) r = 0 := by
      rw [← VertexMap.deviation_affineValue_eq_weighted_sum]
      exact hdev r
    have hreindex := sum_codimTwoVertex hp
      (fun k : Fin (p + 1) =>
        w k * VertexMap.deviation hp
          ((localVertexMap hp N L a q).value k) r)
      i j hij (by simp [hzeros.1]) (by simp [hzeros.2])
    rw [hreindex] at hsum
    simpa only [Matrix.mulVec, dotProduct, x, f,
      codimTwoDeviationMatrix, localVertexMap, mul_comm] using hsum
  have hx : x = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (hminor f) hmul
  have hsumw := sum_codimTwoVertex hp (fun k : Fin (p + 1) => w k)
    i j hij hzeros.1 hzeros.2
  have hright : (∑ c : Fin (p - 1), w (codimTwoVertex hp f c)) = 0 := by
    have := congrArg (fun y : Fin (p - 1) → Real => ∑ c, y c) hx
    simpa [x] using this
  have : (1 : Real) = 0 := by
    calc
      (1 : Real) = ∑ k : Fin (p + 1), w k := w.sum_eq_one.symm
      _ = ∑ c : Fin (p - 1), w (codimTwoVertex hp f c) := hsumw
      _ = 0 := hright
  norm_num at this

/-- Combined polynomial nonvanishing gives the two combinatorial general-position conditions on
every local refined prism simplex. -/
theorem local_regular_and_avoidsCodimTwo_of_generic
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    (hgeneric : ∀ i : GenericityIndex hp N L,
      MvPolynomial.eval a (genericityPolynomial hp N L i) ≠ 0)
    (q : PrismCell hp N L) :
    AffinePositiveRayBoundary.VertexMap.FacetRegular hp (localVertexMap hp N L a q) ∧
      AffinePositiveRayBoundary.VertexMap.AvoidsCodimTwoDeviationZero hp (localVertexMap hp N L a q) := by
  refine ⟨facetRegular_of_generic hp N L a hgeneric q, ?_⟩
  exact avoidsCodimTwo_of_minorRegular hp N L a q
    (codimTwoMinorRegular_of_generic hp N L a hgeneric q)

/-! ## Quantitative retention of the zero-free affine margin -/

/-- A coordinate witness for a lower bound on the sup norm of every affine value.  For the finite
function space `Fin p → Real`, this is the concrete form needed to retain a zero-free norm margin
under coordinatewise perturbation. -/
def LocalAffineCoordinateNormMargin
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (m : Real) : Prop :=
  ∀ (q : PrismCell hp N L) (w : StandardSimplex p),
    ∃ j : Fin p,
      m ≤ |VertexMap.affineValue (localVertexMap hp N L a q) w j|

/-- Coordinatewise assignment closeness bounds every coordinate of every local affine value. -/
theorem affineValue_coordinate_sub_abs_le_of_assignmentClose
    (hp : Nat.Prime p) (N L : Nat)
    (a' a : Assignment hp N L) {eps : Real}
    (hclose : AssignmentClose a' a eps)
    (q : PrismCell hp N L) (w : StandardSimplex p) (j : Fin p) :
    |VertexMap.affineValue (localVertexMap hp N L a' q) w j -
      VertexMap.affineValue (localVertexMap hp N L a q) w j| ≤ eps := by
  unfold VertexMap.affineValue
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i : Fin (p + 1),
        (w i * (localVertexMap hp N L a' q).value i j -
          w i * (localVertexMap hp N L a q).value i j)|
        ≤ ∑ i : Fin (p + 1),
          |w i * (localVertexMap hp N L a' q).value i j -
            w i * (localVertexMap hp N L a q).value i j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i : Fin (p + 1),
        w i * |a' (localParameter hp N L q i j) -
          a (localParameter hp N L q i j)| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show
        w i * (localVertexMap hp N L a' q).value i j -
            w i * (localVertexMap hp N L a q).value i j =
          w i * ((localVertexMap hp N L a' q).value i j -
            (localVertexMap hp N L a q).value i j) by ring]
      simp [localVertexMap, abs_mul, abs_of_nonneg (w.nonneg i)]
    _ ≤ ∑ i : Fin (p + 1), w i * eps := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left
        (le_of_lt (hclose (localParameter hp N L q i j))) (w.nonneg i)
    _ = eps := by
      rw [← Finset.sum_mul, w.sum_eq_one, one_mul]

/-- A perturbation by less than `eps` in every parameter coordinate retains the affine coordinate
norm margin, reduced from `m` to `m - eps`. -/
theorem retain_localAffineCoordinateNormMargin
    (hp : Nat.Prime p) (N L : Nat)
    (a' a : Assignment hp N L) {m eps : Real}
    (hmargin : LocalAffineCoordinateNormMargin hp N L a m)
    (hclose : AssignmentClose a' a eps) :
    LocalAffineCoordinateNormMargin hp N L a' (m - eps) := by
  intro q w
  obtain ⟨j, hj⟩ := hmargin q w
  refine ⟨j, ?_⟩
  have hdiff := affineValue_coordinate_sub_abs_le_of_assignmentClose
    hp N L a' a hclose q w j
  have htriangle :
      |VertexMap.affineValue (localVertexMap hp N L a q) w j| ≤
        |VertexMap.affineValue (localVertexMap hp N L a' q) w j -
          VertexMap.affineValue (localVertexMap hp N L a q) w j| +
        |VertexMap.affineValue (localVertexMap hp N L a' q) w j| := by
    calc
      |VertexMap.affineValue (localVertexMap hp N L a q) w j| =
          |-(VertexMap.affineValue (localVertexMap hp N L a' q) w j -
              VertexMap.affineValue (localVertexMap hp N L a q) w j) +
            VertexMap.affineValue (localVertexMap hp N L a' q) w j| := by
              congr 1
              ring
      _ ≤ |-(VertexMap.affineValue (localVertexMap hp N L a' q) w j -
              VertexMap.affineValue (localVertexMap hp N L a q) w j)| +
            |VertexMap.affineValue (localVertexMap hp N L a' q) w j| :=
          abs_add_le _ _
      _ = |VertexMap.affineValue (localVertexMap hp N L a' q) w j -
              VertexMap.affineValue (localVertexMap hp N L a q) w j| +
            |VertexMap.affineValue (localVertexMap hp N L a' q) w j| := by
          rw [abs_neg]
  linarith

/-- A positive retained coordinate norm margin implies origin avoidance on every local affine
simplex. -/
theorem avoidsOrigin_of_coordinateNormMargin
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) {m : Real} (hm : 0 < m)
    (hmargin : LocalAffineCoordinateNormMargin hp N L a m)
    (q : PrismCell hp N L) :
    AffinePositiveRayBoundary.VertexMap.AvoidsOrigin (localVertexMap hp N L a q) := by
  intro w hzero
  obtain ⟨j, hj⟩ := hmargin q w
  have hjzero : VertexMap.affineValue (localVertexMap hp N L a q) w j = 0 := by
    exact congrFun hzero j
  simp [hjzero] at hj
  linarith

/-! ## The prism perturbation theorem -/

/-- Output of the compatible equivariant generic perturbation.  Shared-face compatibility and prime
equivariance are inherited automatically from the orbit parameter space. -/
structure Result
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (m : Real) where
  assignment : Assignment hp N L
  closeToHomotopy : AssignmentClose assignment (homotopyAssignment hp N L H) (m / 2)
  facetRegular : ∀ q : PrismCell hp N L,
    AffinePositiveRayBoundary.VertexMap.FacetRegular hp (localVertexMap hp N L assignment q)
  avoidsCodimTwo : ∀ q : PrismCell hp N L,
    AffinePositiveRayBoundary.VertexMap.AvoidsCodimTwoDeviationZero hp (localVertexMap hp N L assignment q)
  retainedMargin :
    LocalAffineCoordinateNormMargin hp N L assignment (m / 2)
  avoidsOrigin : ∀ q : PrismCell hp N L,
    AffinePositiveRayBoundary.VertexMap.AvoidsOrigin (localVertexMap hp N L assignment q)
  generalPosition : ∀ q : PrismCell hp N L,
    AffinePositiveRayBoundary.VertexMap.GeneralPosition hp (localVertexMap hp N L assignment q)

/-- Apply finite multivariate generic perturbation at the homotopy assignment.  If the unperturbed
piecewise-affine interpolation has positive coordinate norm margin `m`, the resulting compatible
equivariant assignment has all facet determinants and codimension-two minors nonzero and retains
margin `m/2`; hence every local prism simplex satisfies the full affine general-position interface. -/
theorem exists_generic_perturbation
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {m : Real} (hm : 0 < m)
    (hmargin : LocalAffineCoordinateNormMargin hp N L
      (homotopyAssignment hp N L H) m) :
    Nonempty (Result hp N L H m) := by
  classical
  have hm2 : 0 < m / 2 := by positivity
  obtain ⟨a, hclose, hgeneric⟩ :=
    exists_generic_assignment_close
      (genericityPolynomial hp N L)
      (EquivariantPrismGenericityPolynomials.genericityPolynomial_ne_zero hp N L)
      (homotopyAssignment hp N L H) hm2
  have hretained :
      LocalAffineCoordinateNormMargin hp N L a (m / 2) := by
    have := retain_localAffineCoordinateNormMargin hp N L a
      (homotopyAssignment hp N L H) hmargin hclose
    convert this using 1 ; ring
  have hregular : ∀ q : PrismCell hp N L,
      AffinePositiveRayBoundary.VertexMap.FacetRegular hp (localVertexMap hp N L a q) :=
    fun q => facetRegular_of_generic hp N L a hgeneric q
  have hcodim : ∀ q : PrismCell hp N L,
      AffinePositiveRayBoundary.VertexMap.AvoidsCodimTwoDeviationZero hp (localVertexMap hp N L a q) :=
    fun q => (local_regular_and_avoidsCodimTwo_of_generic hp N L a hgeneric q).2
  have horigin : ∀ q : PrismCell hp N L,
      AffinePositiveRayBoundary.VertexMap.AvoidsOrigin (localVertexMap hp N L a q) :=
    fun q => avoidsOrigin_of_coordinateNormMargin hp N L a hm2 hretained q
  refine ⟨{
    assignment := a
    closeToHomotopy := hclose
    facetRegular := hregular
    avoidsCodimTwo := hcodim
    retainedMargin := hretained
    avoidsOrigin := horigin
    generalPosition := fun q =>
      ⟨hregular q, hcodim q, horigin q⟩
  }⟩

end EquivariantPrismGenericPerturbation
end FoxNeuwirthOrderComplex
end NRR
