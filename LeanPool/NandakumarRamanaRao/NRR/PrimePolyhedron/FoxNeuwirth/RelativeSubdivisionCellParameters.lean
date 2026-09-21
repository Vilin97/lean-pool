/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.StableCollarRelativeSubdivision
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantPrismVertexParameters
import LeanPool.NandakumarRamanaRao.NRR.OddSphereDegree.AlgebraicTopology.IteratedSubdivisionSmallChains
/-!
# Finite relative-collar cells and boundary-frozen parameters

A relative subdivision collar is stored as a singular chain.  Before determinant polynomials can be
restricted to its movable data, one needs a finite set of cell occurrences and one global quotient
of all of their vertex-coordinate sites.

This module supplies that bridge in two stages.

* Every singular chain is represented by a finite list of scalar multiples of singular-simplex
  generators.  Applying this to the relative collar gives a finite occurrence type.
* For a collar in the realization cylinder, all local vertex occurrences are identified by actual
  geometric equality and then quotiented by diagonal prime symmetry.  Parameters represented by a
  point on either horizontal boundary are marked frozen; all remaining parameter orbits are the
  movable interior/side parameters.

The construction is deliberately independent of a particular generic perturbation.  A base scalar
assignment can be restricted relative to the boundary by replacing only values on the movable
parameter subtype.  Shared-vertex compatibility and prime equivariance continue to hold by
construction.

The affine-cell layer upgrades the finite singular cells to explicit affine cell charts for the
specific Fox--Neuwirth orbit cycle and identify their horizontal chains with the two supplied stable
approximations.
-/

namespace NRR

open CategoryTheory AlgebraicTopology Simplicial SimplexCategory Limits
open FoxNeuwirthOrderComplex
open SphereOddDegree
open SphereOddDegree.AffineBarycentricSubdivision

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace RelativeSubdivisionCellParameters

open EquivariantCoordinateHomotopy
open RefinedAffineMap
open EquivariantPrismVertexParameters
open StableCollarRelativeSubdivision

variable {p : Nat}

section FiniteSupport

variable {R : Type} [CommRing R] {X : TopCat.{0}} {n : Nat}

/-- Value of a finite list of coefficient/simplex terms in the singular chain group. -/
noncomputable def expansionValue
    (terms : List (R × singularSimplices X n)) : singularChainGroup R X n :=
  terms.foldr
    (fun t c => t.1 • chainGenerator R X n t.2 + c) 0

@[simp] theorem expansionValue_nil :
    expansionValue (R := R) (X := X) (n := n) [] = 0 := rfl

@[simp] theorem expansionValue_cons
    (t : R × singularSimplices X n)
    (terms : List (R × singularSimplices X n)) :
    expansionValue (R := R) (X := X) (n := n) (t :: terms) =
      t.1 • chainGenerator R X n t.2 +
        expansionValue (R := R) (X := X) (n := n) terms := rfl

/-- Concatenating term lists adds the represented chains. -/
theorem expansionValue_append
    (a b : List (R × singularSimplices X n)) :
    expansionValue (R := R) (X := X) (n := n) (a ++ b) =
      expansionValue (R := R) (X := X) (n := n) a +
        expansionValue (R := R) (X := X) (n := n) b := by
  induction a with
  | nil => simp
  | cons t a ih =>
      simp only [List.cons_append, expansionValue_cons, ih]
      abel

/-- Scale every coefficient in a finite generator expansion. -/
def scaleExpansion
    (r : R) (terms : List (R × singularSimplices X n)) :
    List (R × singularSimplices X n) :=
  terms.map (fun t => (r * t.1, t.2))

/-- Scaling all coefficients scales the represented chain. -/
theorem expansionValue_scaleExpansion
    (r : R) (terms : List (R × singularSimplices X n)) :
    expansionValue (R := R) (X := X) (n := n) (scaleExpansion r terms) =
      r • expansionValue (R := R) (X := X) (n := n) terms := by
  induction terms with
  | nil => simp [scaleExpansion]
  | cons t terms ih =>
      simp only [scaleExpansion, List.map_cons, expansionValue_cons] at ih ⊢
      rw [mul_smul, smul_add, ih]

/-- A proof-carrying finite generator representation of a singular chain. -/
structure FiniteChainRealization (c : singularChainGroup R X n) where
  /-- A finite list of coefficient–simplex terms representing the singular chain. -/
  terms : List (R × singularSimplices X n)
  value_eq : expansionValue terms = c

/-- Every singular chain has finite support in the singular-simplex generators. -/
theorem exists_finiteChainRealization
    (c : singularChainGroup R X n) :
    Nonempty (FiniteChainRealization c) := by
  have hspan :
      Submodule.span R (Set.range (chainGenerator R X n)) = ⊤ :=
    chainGenerator_span_top (X := X) R n
  have hc : c ∈ Submodule.span R (Set.range (chainGenerator R X n)) := by
    rw [hspan]
    exact Submodule.mem_top
  refine Submodule.span_induction
    (p := fun x _ => Nonempty (FiniteChainRealization x)) ?_ ?_ ?_ ?_ hc
  · rintro x ⟨σ, rfl⟩
    exact ⟨{
      terms := [(1, σ)]
      value_eq := by simp [expansionValue]
    }⟩
  · exact ⟨{
      terms := []
      value_eq := by simp
    }⟩
  · intro x y hx hy hX hY
    let Xr := Classical.choice hX
    let Yr := Classical.choice hY
    exact ⟨{
      terms := Xr.terms ++ Yr.terms
      value_eq := by
        rw [expansionValue_append, Xr.value_eq, Yr.value_eq]
    }⟩
  · intro r x hx hX
    let Xr := Classical.choice hX
    exact ⟨{
      terms := scaleExpansion r Xr.terms
      value_eq := by
        rw [expansionValue_scaleExpansion, Xr.value_eq]
    }⟩

/-- A chosen finite generator representation of a singular chain. -/
noncomputable def finiteChainRealization
    (c : singularChainGroup R X n) : FiniteChainRealization c :=
  Classical.choice (exists_finiteChainRealization c)

namespace FiniteChainRealization

/-- Finite occurrence type of the terms in a chain realization. -/
abbrev Occurrence {c : singularChainGroup R X n}
    (S : FiniteChainRealization c) := Fin S.terms.length

/-- Coefficient of a finite chain occurrence. -/
def coefficient {c : singularChainGroup R X n}
    (S : FiniteChainRealization c) (i : S.Occurrence) : R :=
  (S.terms.get i).1

/-- Singular simplex carried by a finite chain occurrence. -/
def simplex {c : singularChainGroup R X n}
    (S : FiniteChainRealization c) (i : S.Occurrence) : singularSimplices X n :=
  (S.terms.get i).2

end FiniteChainRealization

/-- Chosen finite support of the relative collar chain. -/
noncomputable def RelativeSubdivisionBoundary.collarRealization
    (B : RelativeSubdivisionBoundary R X n) :
    FiniteChainRealization B.collarChain :=
  finiteChainRealization B.collarChain

end FiniteSupport

section RelativeCylinderParameters

/-- The topological realization cylinder used by the relative affine cobordism. -/
noncomputable abbrev RelativeCylinder (p : Nat) :=
  TopCat.of (Realization p × Set.Icc (0 : Real) 1)

/-- A singular cylinder simplex is affine when every spatial barycentric coordinate and its time
coordinate are the barycentric interpolation of their values at the simplex vertices. -/
def IsAffineCylinderSimplex
    {n : Nat} (σ : singularSimplices (RelativeCylinder p) n) : Prop :=
  ∀ w : Delta n,
    (∀ c : BarredPermutation p,
      (singularSimplexAsContinuousMap (RelativeCylinder p) n σ w).1 c =
        ∑ i : Fin (n + 1), w i *
          (singularSimplexAsContinuousMap (RelativeCylinder p) n σ
            (stdSimplex.vertex i)).1 c) ∧
    (singularSimplexAsContinuousMap (RelativeCylinder p) n σ w).2.1 =
      ∑ i : Fin (n + 1), w i *
        (singularSimplexAsContinuousMap (RelativeCylinder p) n σ
          (stdSimplex.vertex i)).2.1

/-- The geometric realization condition for a relative subdivision boundary.
Unlike a generic finite support, every represented collar simplex is required to be affine in the
realization-cylinder barycentric coordinates. -/
structure AffineCollarRealization
    {n : Nat}
    (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n) where
  /-- A finite singular-generator representation of the collar chain. -/
  support : FiniteChainRealization B.collarChain
  affine : ∀ i : support.Occurrence, IsAffineCylinderSimplex (support.simplex i)

/-- Existence of an explicit affine finite-cell realization of the relative collar chain. -/
def AffineCollarRealizationExists
    {n : Nat}
    (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n) : Prop :=
  Nonempty (AffineCollarRealization B)

variable (hp : Nat.Prime p) {n : Nat}
variable (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n)

/-- Chosen finite singular-cell support of a relative cylinder collar. -/
noncomputable abbrev CollarSupport (hp : Nat.Prime p)
    (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n) :=
  RelativeSubdivisionBoundary.collarRealization B

/-- One vertex occurrence of one singular `(n+1)`-simplex in the finite collar support. -/
abbrev VertexSlot (hp : Nat.Prime p)
    (B : RelativeSubdivisionBoundary (ZMod p) (RelativeCylinder p) n) :=
  (CollarSupport hp B).Occurrence × Fin (n + 2)

noncomputable instance vertexSlotFintype : Fintype (VertexSlot hp B) := inferInstance
noncomputable instance vertexSlotDecidableEq : DecidableEq (VertexSlot hp B) :=
  Classical.decEq _

/-- Geometric cylinder point at a vertex of one finite collar cell occurrence. -/
noncomputable def slotPoint (s : VertexSlot hp B) : CylinderPoint p :=
  CylinderPoint.ofProd
    ((singularSimplexAsContinuousMap (RelativeCylinder p) (n + 1)
      ((CollarSupport hp B).simplex s.1)) (stdSimplex.vertex s.2))

/-- Symmetry-decorated finite collar vertex occurrences. -/
abbrev CoverVertexSlot := PrimeSymmetry hp × VertexSlot hp B

noncomputable instance coverVertexSlotFintype : Fintype (CoverVertexSlot hp B) := inferInstance
noncomputable instance coverVertexSlotDecidableEq : DecidableEq (CoverVertexSlot hp B) :=
  Classical.decEq _

/-- Geometric point represented by a symmetry-decorated collar vertex occurrence. -/
noncomputable def coverPoint (s : CoverVertexSlot hp B) : CylinderPoint p :=
  s.1 • slotPoint hp B s.2

/-- Decorated occurrences represent one global sampled vertex exactly when their cylinder points
are equal. -/
noncomputable def coverVertexSetoid : Setoid (CoverVertexSlot hp B) where
  r a b := coverPoint hp B a = coverPoint hp B b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Finite global vertices of the relative collar support. -/
abbrev GlobalVertex := Quotient (coverVertexSetoid hp B)

noncomputable instance globalVertexFintype : Fintype (GlobalVertex hp B) :=
  Fintype.ofFinite _

noncomputable instance globalVertexDecidableEq : DecidableEq (GlobalVertex hp B) :=
  Classical.decEq _

/-- Left multiplication on the symmetry decoration. -/
def actCoverVertex
    (g : PrimeSymmetry hp) (s : CoverVertexSlot hp B) : CoverVertexSlot hp B :=
  (g * s.1, s.2)

@[simp] theorem coverPoint_actCoverVertex
    (g : PrimeSymmetry hp) (s : CoverVertexSlot hp B) :
    coverPoint hp B (actCoverVertex hp B g s) = g • coverPoint hp B s := by
  simp [coverPoint, actCoverVertex, mul_smul]

/-- Prime symmetry acts on the global relative-collar vertices. -/
noncomputable instance globalVertexAction :
    MulAction (PrimeSymmetry hp) (GlobalVertex hp B) where
  smul g := Quotient.map (actCoverVertex hp B g) (by
    intro a b hab
    change coverPoint hp B (actCoverVertex hp B g a) =
      coverPoint hp B (actCoverVertex hp B g b)
    simpa using congrArg (fun z : CylinderPoint p => g • z) hab)
  one_smul x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp B (actCoverVertex hp B 1 s) = coverPoint hp B s
    simp
  mul_smul g h x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp B (actCoverVertex hp B (g * h) s) =
      coverPoint hp B (actCoverVertex hp B g (actCoverVertex hp B h s))
    simp [mul_smul]

/-- Actual cylinder point represented by a global relative-collar vertex. -/
noncomputable def globalPoint : GlobalVertex hp B → CylinderPoint p :=
  Quotient.lift (coverPoint hp B) (by
    intro a b hab
    exact hab)

@[simp] theorem globalPoint_mk (s : CoverVertexSlot hp B) :
    globalPoint hp B (Quotient.mk _ s) = coverPoint hp B s := rfl

@[simp] theorem globalPoint_smul
    (g : PrimeSymmetry hp) (x : GlobalVertex hp B) :
    globalPoint hp B (g • x) = g • globalPoint hp B x := by
  refine Quotient.inductionOn x ?_
  intro s
  show coverPoint hp B (actCoverVertex hp B g s) = g • coverPoint hp B s
  simp

/-- Global sampled vertex represented by an undecorated local collar slot. -/
noncomputable def sampleVertex (s : VertexSlot hp B) : GlobalVertex hp B :=
  Quotient.mk _ ((1 : PrimeSymmetry hp), s)

@[simp] theorem globalPoint_sampleVertex (s : VertexSlot hp B) :
    globalPoint hp B (sampleVertex hp B s) = slotPoint hp B s := by
  change (1 : PrimeSymmetry hp) • slotPoint hp B s = _
  exact one_smul _ _

/-- Local copies of one geometric collar vertex determine the same global sampled vertex. -/
theorem sampleVertex_eq_of_slotPoint_eq
    {s t : VertexSlot hp B} (h : slotPoint hp B s = slotPoint hp B t) :
    sampleVertex hp B s = sampleVertex hp B t := by
  apply Quotient.sound
  change coverPoint hp B ((1 : PrimeSymmetry hp), s) =
    coverPoint hp B ((1 : PrimeSymmetry hp), t)
  simpa [coverPoint] using h

/-- Point-coordinate sites before quotienting by diagonal prime symmetry. -/
abbrev ScalarSite := GlobalVertex hp B × Fin p

/-- One scalar parameter per diagonal prime orbit of relative-collar vertex-coordinate sites. -/
abbrev Parameter :=
  MulAction.orbitRel.Quotient (PrimeSymmetry hp) (ScalarSite hp B)

noncomputable instance parameterFintype : Fintype (Parameter hp B) := Fintype.ofFinite _
noncomputable instance parameterDecidableEq : DecidableEq (Parameter hp B) := Classical.decEq _

/-- A cylinder point lies on one of the two fixed horizontal boundaries. -/
def IsHorizontalPoint (z : CylinderPoint p) : Prop :=
  z.time.1 = 0 ∨ z.time.1 = 1

@[simp] theorem isHorizontalPoint_smul
    (g : PrimeSymmetry hp) (z : CylinderPoint p) :
    IsHorizontalPoint (g • z) ↔ IsHorizontalPoint z := by
  rfl

/-- A global relative-collar vertex lies on a fixed horizontal boundary. -/
def IsFrozenVertex (x : GlobalVertex hp B) : Prop :=
  IsHorizontalPoint (globalPoint hp B x)

@[simp] theorem isFrozenVertex_smul
    (g : PrimeSymmetry hp) (x : GlobalVertex hp B) :
    IsFrozenVertex hp B (g • x) ↔ IsFrozenVertex hp B x := by
  simp [IsFrozenVertex]

/-- Frozen status is well-defined on diagonal parameter orbits. -/
noncomputable def IsFrozenParameter : Parameter hp B → Prop :=
  Quotient.lift
    (fun s : ScalarSite hp B => IsFrozenVertex hp B s.1)
    (by
      intro a b hab
      obtain ⟨g, rfl⟩ : ∃ g : PrimeSymmetry hp, g • b = a := hab
      exact propext (isFrozenVertex_smul hp B g b.1))

/-- Parameter orbits represented on the two fixed horizontal boundaries. -/
abbrev FrozenParameter := {q : Parameter hp B // IsFrozenParameter hp B q}

/-- Parameter orbits represented only by movable interior or spatial-side vertices. -/
abbrev MovableParameter := {q : Parameter hp B // ¬ IsFrozenParameter hp B q}

noncomputable instance frozenParameterFintype : Fintype (FrozenParameter hp B) :=
  Fintype.ofFinite _

noncomputable instance movableParameterFintype : Fintype (MovableParameter hp B) :=
  Fintype.ofFinite _

/-- A scalar assignment on all relative-collar parameter orbits. -/
abbrev Assignment := Parameter hp B → Real

open Classical in
/-- Replace only movable parameter values, leaving every horizontal-boundary orbit fixed. -/
noncomputable def replaceMovable
    (base : Assignment hp B) (move : MovableParameter hp B → Real) : Assignment hp B :=
  fun q => if h : IsFrozenParameter hp B q then base q else move ⟨q, h⟩

/-- Relative replacement agrees with the base assignment on every frozen parameter. -/
theorem replaceMovable_eq_base
    (base : Assignment hp B) (move : MovableParameter hp B → Real)
    {q : Parameter hp B} (hq : IsFrozenParameter hp B q) :
    replaceMovable hp B base move q = base q := by
  simp [replaceMovable, hq]

/-- Relative replacement takes the prescribed value on every movable parameter. -/
theorem replaceMovable_eq_move
    (base : Assignment hp B) (move : MovableParameter hp B → Real)
    (q : MovableParameter hp B) :
    replaceMovable hp B base move q.1 = move q := by
  simp [replaceMovable, q.2]

/-- Full polynomial ring before imposing the fixed-horizontal-boundary condition. -/
abbrev FullPolynomialRing := MvPolynomial (Parameter hp B) Real

/-- Polynomial ring in only the movable interior and spatial-side parameter orbits. -/
abbrev MovablePolynomialRing := MvPolynomial (MovableParameter hp B) Real

open Classical in
/-- Substitute a horizontal variable by its fixed base value and retain a movable variable as an
indeterminate. -/
noncomputable def relativeVariable
    (base : Assignment hp B) (q : Parameter hp B) : MovablePolynomialRing hp B :=
  if h : IsFrozenParameter hp B q then MvPolynomial.C (base q)
  else MvPolynomial.X ⟨q, h⟩

/-- Restriction homomorphism from all collar variables to movable variables with fixed horizontal
boundary values. -/
noncomputable def restrictPolynomial
    (base : Assignment hp B) : FullPolynomialRing hp B →+* MovablePolynomialRing hp B :=
  MvPolynomial.eval₂Hom
    (MvPolynomial.C : Real →+* MovablePolynomialRing hp B) (relativeVariable hp B base)

@[simp] theorem eval_relativeVariable
    (base : Assignment hp B) (move : MovableParameter hp B → Real)
    (q : Parameter hp B) :
    MvPolynomial.eval move (relativeVariable hp B base q) =
      replaceMovable hp B base move q := by
  by_cases hq : IsFrozenParameter hp B q
  · simp [relativeVariable, replaceMovable, hq]
  · simp [relativeVariable, replaceMovable, hq]

/-- Evaluating a restricted polynomial at movable data is the same as evaluating the original
polynomial at the boundary-relative full assignment. -/
theorem eval_restrictPolynomial
    (base : Assignment hp B) (move : MovableParameter hp B → Real)
    (P : FullPolynomialRing hp B) :
    MvPolynomial.eval move (restrictPolynomial hp B base P) =
      MvPolynomial.eval (replaceMovable hp B base move) P := by
  refine MvPolynomial.induction_on (motive := fun P =>
    MvPolynomial.eval move (restrictPolynomial hp B base P) =
      MvPolynomial.eval (replaceMovable hp B base move) P) P ?_ ?_ ?_
  · intro a
    simp [restrictPolynomial]
  · intro P Q hP hQ
    simp [map_add, hP, hQ]
  · intro P q hP
    have hmul : restrictPolynomial hp B base (P * MvPolynomial.X q) =
        restrictPolynomial hp B base P * relativeVariable hp B base q := by
      simp [restrictPolynomial]
    rw [hmul, map_mul, hP, eval_relativeVariable, map_mul, MvPolynomial.eval_X]

/-- Scalar value reconstructed at a global relative-collar vertex and coordinate. -/
noncomputable def scalarValue
    (a : Assignment hp B) (x : GlobalVertex hp B) (j : Fin p) : Real :=
  a (Quotient.mk _ (x, j))

/-- Full coordinate vector reconstructed at a global relative-collar vertex. -/
noncomputable def vectorValue
    (a : Assignment hp B) (x : GlobalVertex hp B) : Fin p → Real :=
  fun j => scalarValue hp B a x j

/-- Relative-collar assignments are prime-equivariant by the diagonal orbit quotient. -/
theorem vectorValue_smul
    (a : Assignment hp B) (g : PrimeSymmetry hp) (x : GlobalVertex hp B) :
    vectorValue hp B a (g • x) = g • vectorValue hp B a x := by
  funext j
  rw [PrimeSymmetry.smul_coordinate_apply]
  let j₀ : Fin p := g⁻¹ • j
  have hsite :
      Quotient.mk (MulAction.orbitRel (PrimeSymmetry hp) (ScalarSite hp B))
          (g • x, j) =
        Quotient.mk (MulAction.orbitRel (PrimeSymmetry hp) (ScalarSite hp B))
          (x, j₀) := by
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · simp [j₀]
  exact congrArg a hsite

/-- Values at geometrically equal local collar vertices agree. -/
theorem localValue_eq_of_slotPoint_eq
    (a : Assignment hp B) {s t : VertexSlot hp B}
    (h : slotPoint hp B s = slotPoint hp B t) :
    vectorValue hp B a (sampleVertex hp B s) =
      vectorValue hp B a (sampleVertex hp B t) := by
  rw [sampleVertex_eq_of_slotPoint_eq hp B h]

/-- Replacing movable parameters leaves every horizontal local vertex value unchanged. -/
theorem replaceMovable_horizontal_localValue
    (base : Assignment hp B) (move : MovableParameter hp B → Real)
    (s : VertexSlot hp B) (hs : IsHorizontalPoint (slotPoint hp B s)) :
    vectorValue hp B (replaceMovable hp B base move) (sampleVertex hp B s) =
      vectorValue hp B base (sampleVertex hp B s) := by
  funext j
  apply replaceMovable_eq_base hp B
  show IsFrozenVertex hp B (sampleVertex hp B s)
  simpa [IsFrozenVertex] using hs

end RelativeCylinderParameters

end RelativeSubdivisionCellParameters
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
