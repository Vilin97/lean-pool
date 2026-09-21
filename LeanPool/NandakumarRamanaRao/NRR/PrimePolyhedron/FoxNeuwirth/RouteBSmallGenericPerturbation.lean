/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBFullBadSetNullity
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
/-!
# Route B, Step 6: small generic relative perturbation

The incidence analysis is organized by positive support:

* if a positive-weight retained vertex has a movable scalar coordinate, the
  incidence belongs to one of the finite null bad sets;
* otherwise every positive-weight vertex is frozen, and the incidence is
  excluded by a support-level frozen safety hypothesis inherited exactly from
  the base assignment.

Step 5 supplies the bad-set nullity certificates internally.
-/

namespace NRR

open FoxNeuwirthOrderComplex
open MeasureTheory

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open RelativeGenericity
open ExplicitAffineRelativeCollar.Parameters
open ExplicitAffineRelativeCollar.Polynomials
open EquivariantPrismGenericPerturbation

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Monotonicity of coordinatewise assignment closeness in its radius. -/
theorem assignmentClose_mono
    {J : Type*} {a b : J → Real} {r s : Real}
    (h : AssignmentClose a b r) (hrs : r ≤ s) :
    AssignmentClose a b s := by
  intro j
  exact lt_of_lt_of_le (h j) hrs

/-- Coordinatewise control radius used for both the requested perturbation size and retention of
half of the origin margin.  The geometric radius of a neighborhood around a generic center is kept
separate: a displaced center cannot in general have a ball of radius `r` entirely contained in the
radius-`r` ball around the base assignment. -/
noncomputable def perturbationControlRadius (eps margin : Real) : Real :=
  min eps (margin / 2)

theorem perturbationControlRadius_pos
    {eps margin : Real}
    (heps : 0 < eps) (hmargin : 0 < margin) :
    0 < perturbationControlRadius eps margin := by
  exact lt_min heps (half_pos hmargin)

theorem perturbationControlRadius_le_eps
    (eps margin : Real) :
    perturbationControlRadius eps margin ≤ eps :=
  min_le_left _ _

theorem perturbationControlRadius_le_half_margin
    (eps margin : Real) :
    perturbationControlRadius eps margin ≤ margin / 2 :=
  min_le_right _ _

/-- Facet regularity of every local vertex map reconstructed from one movable
assignment. -/
def AllCellsFacetRegular
    (base : Assignment hp C) (x : MovableParameterSpace hp C) : Prop :=
  ∀ q : C.Cell,
    FacetRegular hp
      (localVertexMap hp C (assignmentOfMovableParameters hp C base x) q)

/-- Support-level endpoint safety.  It is invoked only when every vertex with
positive barycentric weight is frozen.  Zero-weight nonhorizontal vertices do
not affect this condition. -/
def FrozenPositiveSupportRaySafe
    (a : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (w : StandardSimplex p)
      (i j : Fin (p + 1)), i ≠ j →
    (∀ r : Fin (p - 1),
      deviation hp (affineValue (localVertexMap hp C a q) w) r = 0) →
    0 < mean hp (affineValue (localVertexMap hp C a q) w) →
    (∀ k : Fin (p + 1), 0 < w k →
      ∀ c : Fin p, IsFrozenParameter hp C (localParameter hp C q k c)) →
    ¬ (w i = 0 ∧ w j = 0)

/-- Replacing movable parameters leaves an affine value unchanged whenever all
positive-weight local vertices are frozen. -/
theorem affineValue_assignmentOfMovableParameters_eq_base_of_frozenSupport
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (q : C.Cell) (w : StandardSimplex p)
    (hsupport : ∀ k : Fin (p + 1), 0 < w k →
      ∀ c : Fin p, IsFrozenParameter hp C (localParameter hp C q k c)) :
    affineValue
      (localVertexMap hp C (assignmentOfMovableParameters hp C base x) q) w =
      affineValue (localVertexMap hp C base q) w := by
  funext c
  unfold affineValue
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hw : 0 < w k
  · have hfrozen := hsupport k hw c
    simp [localVertexMap_value_apply_eq_assignment_localParameter,
      assignmentOfMovableParameters_frozen hp C base x hfrozen]
  · have hwzero : w k = 0 := by
      exact le_antisymm (le_of_not_gt hw) (w.nonneg k)
    simp [hwzero]

/-- Frozen-support safety is inherited exactly by every movable replacement. -/
theorem frozenPositiveSupportRaySafe_assignmentOfMovableParameters
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (hsafe : FrozenPositiveSupportRaySafe hp C base) :
    FrozenPositiveSupportRaySafe hp C
      (assignmentOfMovableParameters hp C base x) := by
  intro q w i j hij hdev hmean hsupport
  have heq :=
    affineValue_assignmentOfMovableParameters_eq_base_of_frozenSupport
      hp C base x q w hsupport
  apply hsafe q w i j hij
  · simpa only [heq] using hdev
  · simpa only [heq] using hmean
  · exact hsupport

/-- Avoidance of all mixed-face bad sets plus frozen-support safety gives the
direct codimension-two positive-ray condition. -/
theorem avoidsPositiveRayCodimTwo_of_avoids_all_mixedFaceBadSets
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (hfrozen : FrozenPositiveSupportRaySafe hp C
      (assignmentOfMovableParameters hp C base x))
    (havoid : ∀ κ : MixedFaceCase hp C,
      x ∉ mixedFaceBadSet hp C base κ)
    (q : C.Cell) :
    AvoidsPositiveRayCodimTwo hp
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base x) q) := by
  intro w i j hij hdev hmean hzeros
  by_cases hmovable : HasPositiveMovableWitness hp C q w i j
  · obtain ⟨κ, hκ⟩ :=
      mem_mixedFaceBadSet_of_incidence hp C base x q w i j hij
        hzeros.1 hzeros.2 hdev hmean hmovable
    exact havoid κ hκ
  · apply hfrozen q w i j hij hdev hmean
    · intro k hk c
      have hki : k ≠ i := by
        intro h
        subst k
        exact (ne_of_gt hk) hzeros.1
      have hkj : k ≠ j := by
        intro h
        subst k
        exact (ne_of_gt hk) hzeros.2
      by_contra hnot
      apply hmovable
      exact ⟨k, hki, hkj, hk, c, hnot⟩
    · exact hzeros

/-- A positive-volume perturbation neighborhood on which full-assignment closeness and facet
regularity are controlled.  `radius` is the radius around the generic center; the assignment
closeness conclusion uses the independent control radius `min eps (margin / 2)`. -/
structure SafePerturbationBall
    (base : Assignment hp C) (eps margin : Real) where
  /-- The center of a ball of admissible movable parameters. -/
  center : MovableParameterSpace hp C
  /-- The positive radius on which the perturbation bounds and genericity remain valid. -/
  radius : Real
  radius_pos : 0 < radius
  closeToBase : ∀ x ∈ Metric.ball center radius,
    AssignmentClose
      (assignmentOfMovableParameters hp C base x) base
      (perturbationControlRadius eps margin)
  facetRegular : ∀ x ∈ Metric.ball center radius,
    AllCellsFacetRegular hp C base x


/-- Nontriviality of every boundary-restricted facet determinant polynomial.  This is the exact
algebraic input needed to find a nearby facet-regular center; codimension-two minors are handled by
the Route B bad-set argument and are intentionally absent. -/
def AllRestrictedFacetPolynomialsNonzero
    (base : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (k : Fin (p + 1)),
    restrictedFacetDeterminantPolynomial hp C base q k ≠ 0


/-- Geometric form of facet-polynomial nontriviality.  Different local facets may use different
movable assignments. -/
def AllFacetRegularityWitnesses
    (base : Assignment hp C) : Prop :=
  ∀ (q : C.Cell) (k : Fin (p + 1)),
    ∃ x : MovableParameterSpace hp C,
      facetDeterminant hp
        (localVertexMap hp C (assignmentOfMovableParameters hp C base x) q) k ≠ 0

/-- Pointwise facet witnesses prove nontriviality of every restricted facet polynomial. -/
theorem allRestrictedFacetPolynomialsNonzero_of_witnesses
    (base : Assignment hp C)
    (h : AllFacetRegularityWitnesses hp C base) :
    AllRestrictedFacetPolynomialsNonzero hp C base := by
  intro q k hzero
  obtain ⟨x, hx⟩ := h q k
  have heval := congrArg (MvPolynomial.eval x) hzero
  rw [eval_restrictedFacetDeterminantPolynomial] at heval
  exact hx (by simpa [assignmentOfMovableParameters] using heval)

/-- Evaluation of every restricted facet determinant is continuous in the finite movable parameter
space. -/
theorem continuous_restrictedFacetDeterminant_eval
    (base : Assignment hp C) (q : C.Cell) (k : Fin (p + 1)) :
    Continuous (fun x : MovableParameterSpace hp C =>
      MvPolynomial.eval x
        (restrictedFacetDeterminantPolynomial hp C base q k)) := by
  exact MvPolynomial.continuous_eval
    (restrictedFacetDeterminantPolynomial hp C base q k)

/-- Facet regularity is an open condition in the movable parameter space. -/
theorem isOpen_allCellsFacetRegular
    (base : Assignment hp C) :
    IsOpen {x : MovableParameterSpace hp C |
      AllCellsFacetRegular hp C base x} := by
  have hset :
      {x : MovableParameterSpace hp C |
        AllCellsFacetRegular hp C base x} =
      {x : MovableParameterSpace hp C |
        ∀ q : C.Cell, ∀ k : Fin (p + 1),
          MvPolynomial.eval x
            (restrictedFacetDeterminantPolynomial hp C base q k) ≠ 0} := by
    ext x
    simp only [Set.mem_ofPred_eq, AllCellsFacetRegular]
    constructor
    · intro h q k
      rw [eval_restrictedFacetDeterminantPolynomial]
      simpa [assignmentOfMovableParameters] using h q k
    · intro h q k
      have hx := h q k
      rw [eval_restrictedFacetDeterminantPolynomial] at hx
      simpa [assignmentOfMovableParameters] using hx
  rw [hset]
  rw [show {x : MovableParameterSpace hp C |
      ∀ q : C.Cell, ∀ k : Fin (p + 1),
        MvPolynomial.eval x
          (restrictedFacetDeterminantPolynomial hp C base q k) ≠ 0} =
      ⋂ q : C.Cell, ⋂ k : Fin (p + 1),
        {x : MovableParameterSpace hp C |
          MvPolynomial.eval x
            (restrictedFacetDeterminantPolynomial hp C base q k) ≠ 0} by
    ext x
    simp]
  apply isOpen_iInter_of_finite
  intro q
  apply isOpen_iInter_of_finite
  intro k
  exact isOpen_ne.preimage
    (continuous_restrictedFacetDeterminant_eval hp C base q k)

/-- Nonzero restricted facet polynomials produce a genuine positive-radius safe neighborhood.
The center is chosen close to the base movable parameters, then the neighborhood radius is shrunk
both to remain facet-regular and to keep every reconstructed full assignment inside the independent
control radius. -/
theorem exists_safePerturbationBall
    (base : Assignment hp C)
    {eps margin : Real}
    (heps : 0 < eps) (hmargin : 0 < margin)
    (hfacetPoly : AllRestrictedFacetPolynomialsNonzero hp C base) :
    Nonempty (SafePerturbationBall hp C base eps margin) := by
  let control := perturbationControlRadius eps margin
  have hcontrol : 0 < control :=
    perturbationControlRadius_pos heps hmargin
  let quarter := control / 4
  have hquarter : 0 < quarter := by
    dsimp [quarter]
    positivity
  let P : (C.Cell × Fin (p + 1)) → MovablePolynomialRing hp C :=
    fun qk => restrictedFacetDeterminantPolynomial hp C base qk.1 qk.2
  have hP : ∀ qk, P qk ≠ 0 := by
    intro qk
    exact hfacetPoly qk.1 qk.2
  obtain ⟨center, hcenterClose, hcenterGeneric⟩ :=
    exists_generic_assignment_close P hP
      (baseMovableParameters hp C base) hquarter
  have hcenterFacet : AllCellsFacetRegular hp C base center := by
    intro q k
    have h := hcenterGeneric (q, k)
    simpa [P, eval_restrictedFacetDeterminantPolynomial, assignmentOfMovableParameters,
      AllCellsFacetRegular] using h
  obtain ⟨openRadius, hopenPos, hopen⟩ :=
    (Metric.isOpen_iff.mp (isOpen_allCellsFacetRegular hp C base))
      center hcenterFacet
  let radius := min openRadius quarter
  have hradius : 0 < radius := lt_min hopenPos hquarter
  refine ⟨{
    center := center
    radius := radius
    radius_pos := hradius
    closeToBase := ?_
    facetRegular := ?_ }⟩
  · intro x hx
    have hxc : dist x center < quarter :=
      lt_of_lt_of_le hx (min_le_right openRadius quarter)
    intro s
    by_cases hs : IsFrozenParameter hp C s
    · simpa [assignmentOfMovableParameters_frozen hp C base, hs] using hcontrol
    · let sm : MovableParameter hp C := ⟨s, hs⟩
      have hcoord : |x sm - center sm| < quarter := by
        have hle : dist (x sm) (center sm) ≤ dist x center :=
          (dist_pi_le_iff (dist_nonneg : 0 ≤ dist x center)).mp le_rfl sm
        simpa [Real.dist_eq] using lt_of_le_of_lt hle hxc
      have hcb : |center sm - baseMovableParameters hp C base sm| < quarter :=
        hcenterClose sm
      have hbase : baseMovableParameters hp C base sm = base s := rfl
      have htri : |x sm - base s| ≤
          |x sm - center sm| + |center sm - base s| := by
        calc
          |x sm - base s| = |(x sm - center sm) + (center sm - base s)| := by ring_nf
          _ ≤ |x sm - center sm| + |center sm - base s| := abs_add_le _ _
      have hsum : |x sm - center sm| + |center sm - base s| < control := by
        rw [← hbase]
        change |x sm - center sm| +
          |center sm - baseMovableParameters hp C base sm| < control
        dsimp [quarter] at hcoord hcb
        linarith
      simpa [assignmentOfMovableParameters, replaceMovable, hs, sm] using
        lt_of_le_of_lt htri hsum
  · intro x hx
    apply hopen
    exact lt_of_lt_of_le hx (min_le_left openRadius quarter)

/-- Complete Step 6 output. -/
structure SmallGenericPerturbationResult
    (base : Assignment hp C) (eps margin : Real) where
  /-- The chosen movable parameters realizing the small generic perturbation. -/
  move : MovableParameterSpace hp C
  closeToBase : AssignmentClose
    (assignmentOfMovableParameters hp C base move) base eps
  fixesFrozen : ∀ {s : Parameter hp C}, IsFrozenParameter hp C s →
    assignmentOfMovableParameters hp C base move s = base s
  equivariant : ∀ (g : PrimeSymmetry hp) (v : GlobalVertex hp C),
    vectorValue hp C (assignmentOfMovableParameters hp C base move) (g • v) =
      g • vectorValue hp C (assignmentOfMovableParameters hp C base move) v
  retainedMargin : LocalAffineCoordinateNormMargin hp C
    (assignmentOfMovableParameters hp C base move) (margin / 2)
  facetRegular : ∀ q : C.Cell,
    FacetRegular hp
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base move) q)
  avoidsPositiveRayCodimTwo : ∀ q : C.Cell,
    AvoidsPositiveRayCodimTwo hp
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base move) q)
  avoidsOrigin : ∀ q : C.Cell,
    AvoidsOrigin
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base move) q)
  positiveRayGeneralPosition : ∀ q : C.Cell,
    PositiveRayGeneralPosition hp
      (localVertexMap hp C
        (assignmentOfMovableParameters hp C base move) q)

/-- Step 6 selection theorem.  Full mixed-face bad-set nullity is supplied by
Step 5 and is no longer an external hypothesis. -/
theorem exists_smallGenericPerturbation
    (base : Assignment hp C)
    {eps margin : Real}
    (hmargin : 0 < margin)
    (hbaseMargin : LocalAffineCoordinateNormMargin hp C base margin)
    (hfrozenBase : FrozenPositiveSupportRaySafe hp C base)
    (B : SafePerturbationBall hp C base eps margin) :
    Nonempty (SmallGenericPerturbationResult hp C base eps margin) := by
  have hball : volume (Metric.ball B.center B.radius) ≠ 0 :=
    ne_of_gt (Metric.measure_ball_pos volume B.center B.radius_pos)
  obtain ⟨x, hxball, havoid⟩ :=
    exists_mem_ball_avoiding_all_mixedFaceBadSets_unconditional
      hp C base B.center B.radius hball
  have hcloseControl : AssignmentClose
      (assignmentOfMovableParameters hp C base x) base
        (perturbationControlRadius eps margin) :=
    B.closeToBase x hxball
  have hcloseEps : AssignmentClose
      (assignmentOfMovableParameters hp C base x) base eps :=
    assignmentClose_mono hcloseControl
      (perturbationControlRadius_le_eps eps margin)
  have hcloseHalf : AssignmentClose
      (assignmentOfMovableParameters hp C base x) base (margin / 2) :=
    assignmentClose_mono hcloseControl
      (perturbationControlRadius_le_half_margin eps margin)
  have hretainedRaw := retain_localAffineCoordinateNormMargin hp C
    (assignmentOfMovableParameters hp C base x) base hbaseMargin hcloseHalf
  have hretained : LocalAffineCoordinateNormMargin hp C
      (assignmentOfMovableParameters hp C base x) (margin / 2) := by
    convert hretainedRaw using 1; ring
  have horigin : ∀ q : C.Cell,
      AvoidsOrigin
        (localVertexMap hp C
          (assignmentOfMovableParameters hp C base x) q) := by
    intro q
    exact avoidsOrigin_of_localAffineCoordinateNormMargin hp C
      (assignmentOfMovableParameters hp C base x) (half_pos hmargin)
      hretained q
  have hfrozen : FrozenPositiveSupportRaySafe hp C
      (assignmentOfMovableParameters hp C base x) :=
    frozenPositiveSupportRaySafe_assignmentOfMovableParameters
      hp C base x hfrozenBase
  have hfacet : AllCellsFacetRegular hp C base x := B.facetRegular x hxball
  have hcodim : ∀ q : C.Cell,
      AvoidsPositiveRayCodimTwo hp
        (localVertexMap hp C
          (assignmentOfMovableParameters hp C base x) q) := by
    intro q
    exact avoidsPositiveRayCodimTwo_of_avoids_all_mixedFaceBadSets
      hp C base x hfrozen havoid q
  refine ⟨{
    move := x
    closeToBase := hcloseEps
    fixesFrozen := ?_
    equivariant := ?_
    retainedMargin := hretained
    facetRegular := hfacet
    avoidsPositiveRayCodimTwo := hcodim
    avoidsOrigin := horigin
    positiveRayGeneralPosition := ?_ }⟩
  · intro s hs
    exact assignmentOfMovableParameters_frozen hp C base x hs
  · intro g v
    exact vectorValue_assignmentOfMovableParameters_smul hp C base x g v
  · intro q
    exact {
      facetRegular := hfacet q
      avoidsPositiveRayCodimTwo := hcodim q
      avoidsOrigin := horigin q }

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
