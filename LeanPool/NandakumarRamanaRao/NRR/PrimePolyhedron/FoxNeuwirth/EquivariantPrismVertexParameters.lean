/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.SubdivisionPrismCharts
import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.EquivariantCoordinateHomotopy
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Finite equivariant parameter space for refined prism vertices

A perturbation used in the refined S6 prism argument must satisfy two compatibility conditions before
any determinant or minor polynomial is considered:

* local copies of one geometric prism vertex must receive the same coordinate values;
* prime-symmetry translates must receive relabelled coordinate values.

This module builds a finite scalar parameter type on which both conditions hold by construction.
First take the finite set of all symmetry translates of all local refined-prism vertex slots and
identify translates which represent the same point of the realization cylinder.  Then quotient the
resulting point-coordinate pairs by the diagonal prime action.  A real-valued function on that final
orbit type reconstructs a globally shared, prime-equivariant vector value at every sampled prism
vertex.

The zero-free homotopy itself determines the distinguished base assignment in this parameter space.
Later genericity modules only need to define their determinant and codimension-two polynomials on
this finite type.
-/

namespace NRR

open Geometry
open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismVertexParameters

open EquivariantCoordinateHomotopy
open SubdivisionPrismCharts

variable {p : Nat}

/-- The realization cylinder, bundled so that prime symmetry acts only on the spatial coordinate. -/
structure CylinderPoint (p : Nat) where
  spatial : Realization p
  time : Set.Icc (0 : Real) 1

namespace CylinderPoint

/-- Convert the product representation used by the homotopy and prism charts. -/
def ofProd (z : Realization p × Set.Icc (0 : Real) 1) : CylinderPoint p :=
  ⟨z.1, z.2⟩

/-- Convert back to the product representation used by the homotopy. -/
def toProd (z : CylinderPoint p) : Realization p × Set.Icc (0 : Real) 1 :=
  (z.spatial, z.time)

@[simp] theorem toProd_ofProd
    (z : Realization p × Set.Icc (0 : Real) 1) :
    toProd (ofProd z) = z := rfl

@[simp] theorem ofProd_toProd (z : CylinderPoint p) :
    ofProd (toProd z) = z := by
  cases z
  rfl

instance (hp : Nat.Prime p) : MulAction (PrimeSymmetry hp) (CylinderPoint p) where
  smul g z := ⟨g • z.spatial, z.time⟩
  one_smul z := by
    cases z
    rfl
  mul_smul g h z := by
    cases z with
    | mk spatial time =>
      cases mul_smul g h spatial
      rfl

@[simp] theorem smul_spatial
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (z : CylinderPoint p) :
    (g • z).spatial = g • z.spatial := rfl

@[simp] theorem smul_time
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (z : CylinderPoint p) :
    (g • z).time = z.time := rfl

@[simp] theorem toProd_smul
    (hp : Nat.Prime p) (g : PrimeSymmetry hp) (z : CylinderPoint p) :
    toProd (g • z) = (g • z.spatial, z.time) := rfl

end CylinderPoint

/-- One local vertex occurrence in the fully refined prism triangulation. -/
abbrev VertexSlot (hp : Nat.Prime p) (N L : Nat) :=
  PrismCell hp N L × Fin (p + 1)

noncomputable instance (hp : Nat.Prime p) (N L : Nat) : Fintype (VertexSlot hp N L) := inferInstance
noncomputable instance (hp : Nat.Prime p) (N L : Nat) : DecidableEq (VertexSlot hp N L) := inferInstance

/-- A local prism vertex occurrence as an actual point of the realization cylinder. -/
noncomputable def slotPoint
    (hp : Nat.Prime p) (N L : Nat) (s : VertexSlot hp N L) : CylinderPoint p :=
  CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L s.1 s.2)

/-- Add a symmetry element to a local vertex occurrence.  This finite covering type contains all
prime translates of the selected quotient-cell representatives. -/
abbrev CoverVertexSlot (hp : Nat.Prime p) (N L : Nat) :=
  PrimeSymmetry hp × VertexSlot hp N L

noncomputable instance (hp : Nat.Prime p) (N L : Nat) : Fintype (CoverVertexSlot hp N L) := inferInstance
noncomputable instance (hp : Nat.Prime p) (N L : Nat) : DecidableEq (CoverVertexSlot hp N L) := inferInstance

/-- Geometric point represented by one symmetry-decorated local vertex occurrence. -/
noncomputable def coverPoint
    (hp : Nat.Prime p) (N L : Nat) (s : CoverVertexSlot hp N L) : CylinderPoint p :=
  s.1 • slotPoint hp N L s.2

/-- Two decorated local slots represent the same global sampled vertex when their cylinder points
are equal. -/
noncomputable def coverVertexSetoid
    (hp : Nat.Prime p) (N L : Nat) : Setoid (CoverVertexSlot hp N L) where
  r a b := coverPoint hp N L a = coverPoint hp N L b
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- Finite global sampled vertices of the prism, after identifying all local copies of one geometric
point. -/
abbrev GlobalVertex (hp : Nat.Prime p) (N L : Nat) :=
  Quotient (coverVertexSetoid hp N L)

noncomputable instance globalVertexFintype
    (hp : Nat.Prime p) (N L : Nat) : Fintype (GlobalVertex hp N L) :=
  Fintype.ofFinite _

noncomputable instance globalVertexDecidableEq
    (hp : Nat.Prime p) (N L : Nat) : DecidableEq (GlobalVertex hp N L) :=
  Classical.decEq _

/-- Left multiplication on the symmetry decoration. -/
def actCoverVertex
    (g : PrimeSymmetry hp) (s : CoverVertexSlot hp N L) : CoverVertexSlot hp N L :=
  (g * s.1, s.2)

@[simp] theorem coverPoint_actCoverVertex
    (hp : Nat.Prime p) (N L : Nat)
    (g : PrimeSymmetry hp) (s : CoverVertexSlot hp N L) :
    coverPoint hp N L (actCoverVertex g s) = g • coverPoint hp N L s := by
  simp [coverPoint, actCoverVertex, mul_smul]

/-- Prime symmetry acts on global sampled vertices. -/
noncomputable instance globalVertexAction
    (hp : Nat.Prime p) (N L : Nat) :
    MulAction (PrimeSymmetry hp) (GlobalVertex hp N L) where
  smul g := Quotient.map (actCoverVertex g) (by
    intro a b hab
    change coverPoint hp N L (actCoverVertex g a) =
      coverPoint hp N L (actCoverVertex g b)
    simpa using congrArg (fun z : CylinderPoint p => g • z) hab)
  one_smul x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp N L (actCoverVertex 1 s) = coverPoint hp N L s
    simp
  mul_smul g h x := by
    refine Quotient.inductionOn x ?_
    intro s
    apply Quotient.sound
    change coverPoint hp N L (actCoverVertex (g * h) s) =
      coverPoint hp N L (actCoverVertex g (actCoverVertex h s))
    simp [mul_smul]

/-- Actual cylinder point represented by a global sampled vertex. -/
noncomputable def globalPoint
    (hp : Nat.Prime p) (N L : Nat) : GlobalVertex hp N L → CylinderPoint p :=
  Quotient.lift (coverPoint hp N L) (by
    intro a b hab
    exact hab)

@[simp] theorem globalPoint_mk
    (hp : Nat.Prime p) (N L : Nat) (s : CoverVertexSlot hp N L) :
    globalPoint hp N L (Quotient.mk _ s) = coverPoint hp N L s := rfl

@[simp] theorem globalPoint_smul
    (hp : Nat.Prime p) (N L : Nat)
    (g : PrimeSymmetry hp) (x : GlobalVertex hp N L) :
    globalPoint hp N L (g • x) = g • globalPoint hp N L x := by
  refine Quotient.inductionOn x ?_
  intro s
  change coverPoint hp N L (actCoverVertex g s) = g • coverPoint hp N L s
  exact coverPoint_actCoverVertex hp N L g s

/-- The global sampled vertex represented by an undecorated local slot. -/
noncomputable def sampleVertex
    (hp : Nat.Prime p) (N L : Nat) (s : VertexSlot hp N L) : GlobalVertex hp N L :=
  Quotient.mk _ ((1 : PrimeSymmetry hp), s)

@[simp] theorem globalPoint_sampleVertex
    (hp : Nat.Prime p) (N L : Nat) (s : VertexSlot hp N L) :
    globalPoint hp N L (sampleVertex hp N L s) = slotPoint hp N L s := by
  change globalPoint hp N L (Quotient.mk _ ((1 : PrimeSymmetry hp), s)) = _
  rw [globalPoint_mk]
  change (1 : PrimeSymmetry hp) • slotPoint hp N L s = slotPoint hp N L s
  exact one_smul _ _

/-- Local copies of one geometric prism vertex determine the same global sampled vertex. -/
theorem sampleVertex_eq_of_vertex_eq
    (hp : Nat.Prime p) (N L : Nat)
    {q q' : PrismCell hp N L} {i i' : Fin (p + 1)}
    (h : SubdivisionPrismCharts.vertex hp N L q i =
      SubdivisionPrismCharts.vertex hp N L q' i') :
    sampleVertex hp N L (q, i) = sampleVertex hp N L (q', i') := by
  apply Quotient.sound
  change coverPoint hp N L ((1 : PrimeSymmetry hp), (q, i)) =
    coverPoint hp N L ((1 : PrimeSymmetry hp), (q', i'))
  simpa [coverPoint, slotPoint] using congrArg CylinderPoint.ofProd h

/-- Point-coordinate pairs on which prime symmetry acts diagonally. -/
abbrev ScalarSite (hp : Nat.Prime p) (N L : Nat) :=
  GlobalVertex hp N L × Fin p

/-- One independent real parameter per diagonal prime orbit of sampled point-coordinate pairs. -/
abbrev Parameter (hp : Nat.Prime p) (N L : Nat) :=
  MulAction.orbitRel.Quotient (PrimeSymmetry hp) (ScalarSite hp N L)

noncomputable instance parameterFintype
    (hp : Nat.Prime p) (N L : Nat) : Fintype (Parameter hp N L) :=
  Fintype.ofFinite _

noncomputable instance parameterDecidableEq
    (hp : Nat.Prime p) (N L : Nat) : DecidableEq (Parameter hp N L) :=
  Classical.decEq _

/-- A global compatible equivariant assignment is an arbitrary scalar function on the finite orbit
parameter type. -/
abbrev Assignment (hp : Nat.Prime p) (N L : Nat) :=
  Parameter hp N L → Real

/-- Scalar value reconstructed at a sampled global vertex and coordinate label. -/
noncomputable def scalarValue
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (x : GlobalVertex hp N L) (j : Fin p) : Real :=
  a (Quotient.mk _ (x, j))

/-- Full coordinate vector reconstructed at a sampled global vertex. -/
noncomputable def vectorValue
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (x : GlobalVertex hp N L) : Fin p → Real :=
  fun j => scalarValue hp N L a x j

/-- Scalar values are invariant under the diagonal action. -/
theorem scalarValue_smul
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (g : PrimeSymmetry hp)
    (x : GlobalVertex hp N L) (j : Fin p) :
    scalarValue hp N L a (g • x) (g • j) = scalarValue hp N L a x j := by
  unfold scalarValue
  apply congrArg a
  apply Quotient.sound
  exact ⟨g, rfl⟩

/-- Every parameter assignment reconstructs a prime-equivariant vector assignment. -/
theorem vectorValue_smul
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (g : PrimeSymmetry hp)
    (x : GlobalVertex hp N L) :
    vectorValue hp N L a (g • x) = g • vectorValue hp N L a x := by
  funext j
  rw [PrimeSymmetry.smul_coordinate_apply]
  let j₀ : Fin p := g⁻¹ • j
  have hsite :
      Quotient.mk (MulAction.orbitRel (PrimeSymmetry hp) (ScalarSite hp N L))
          (g • x, j) =
        Quotient.mk (MulAction.orbitRel (PrimeSymmetry hp) (ScalarSite hp N L))
          (x, j₀) := by
    apply Quotient.sound
    refine ⟨g, ?_⟩
    apply Prod.ext
    · rfl
    · simp [j₀]
  exact congrArg a hsite

/-- Vector value attached to one local prism vertex occurrence. -/
noncomputable def localVertexValue
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L) (q : PrismCell hp N L) (i : Fin (p + 1)) :
    Fin p → Real :=
  vectorValue hp N L a (sampleVertex hp N L (q, i))

/-- Shared geometric prism vertices receive identical local vector values. -/
theorem localVertexValue_eq_of_vertex_eq
    (hp : Nat.Prime p) (N L : Nat)
    (a : Assignment hp N L)
    {q q' : PrismCell hp N L} {i i' : Fin (p + 1)}
    (h : SubdivisionPrismCharts.vertex hp N L q i =
      SubdivisionPrismCharts.vertex hp N L q' i') :
    localVertexValue hp N L a q i = localVertexValue hp N L a q' i' := by
  unfold localVertexValue
  rw [sampleVertex_eq_of_vertex_eq hp N L h]

/-- The scalar function on sites obtained by sampling an equivariant zero-free homotopy. -/
noncomputable def homotopySiteValue
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (s : ScalarSite hp N L) : Real :=
  H.map (CylinderPoint.toProd (globalPoint hp N L s.1)) s.2

/-- Homotopy samples are constant on diagonal prime orbits. -/
theorem homotopySiteValue_eq_of_orbitRel
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    {a b : ScalarSite hp N L}
    (hab : MulAction.orbitRel (PrimeSymmetry hp) (ScalarSite hp N L) a b) :
    homotopySiteValue hp N L H a = homotopySiteValue hp N L H b := by
  rw [MulAction.orbitRel_apply] at hab
  rcases hab with ⟨g, hgab⟩
  subst a
  change H.map (CylinderPoint.toProd (globalPoint hp N L (g • b.1))) (g • b.2) =
    H.map (CylinderPoint.toProd (globalPoint hp N L b.1)) b.2
  rw [globalPoint_smul]
  have heq := H.equivariant g (globalPoint hp N L b.1).spatial
    (globalPoint hp N L b.1).time
  have hj := congrFun heq (g • b.2)
  simpa [CylinderPoint.toProd, PrimeSymmetry.smul_coordinate_apply,
    PrimeSymmetry.smul_label] using hj

/-- Distinguished parameter assignment given by the original homotopy values at sampled vertices. -/
noncomputable def homotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁) :
    Assignment hp N L :=
  fun q => Quotient.liftOn q (homotopySiteValue hp N L H) (by
    intro a b hab
    exact homotopySiteValue_eq_of_orbitRel hp N L H hab)

/-- Reconstructing the homotopy assignment gives the original homotopy value at every sampled
global vertex. -/
theorem vectorValue_homotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (x : GlobalVertex hp N L) :
    vectorValue hp N L (homotopyAssignment hp N L H) x =
      H.map (CylinderPoint.toProd (globalPoint hp N L x)) := by
  funext j
  rfl

/-- On each local refined-prism vertex, the distinguished assignment is exactly the original
homotopy sample. -/
theorem localVertexValue_homotopyAssignment
    (hp : Nat.Prime p) (N L : Nat)
    {F₀ F₁ : ZeroFreeMap hp} (H : ZeroFreeHomotopy hp F₀ F₁)
    (q : PrismCell hp N L) (i : Fin (p + 1)) :
    localVertexValue hp N L (homotopyAssignment hp N L H) q i =
      H.map (SubdivisionPrismCharts.vertex hp N L q i) := by
  rw [localVertexValue, vectorValue_homotopyAssignment]
  change H.map (CylinderPoint.toProd
      (CylinderPoint.ofProd (SubdivisionPrismCharts.vertex hp N L q i))) = _
  rw [CylinderPoint.toProd_ofProd]

end EquivariantPrismVertexParameters
end FoxNeuwirthOrderComplex
end NRR
