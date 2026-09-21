/-
Copyright (c) 2026 Arseniy Akopyan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arseniy Akopyan
-/

import LeanPool.NandakumarRamanaRao.NRR.PrimePolyhedron.FoxNeuwirth.RouteBMovableParameterSpace
/-!
# Route B, Step 3: decomposition of mixed-face positive-ray incidence

For a nonhorizontal codimension-two face, a positive-ray failure is split into
finitely many cases by choosing a retained movable vertex whose barycentric
coefficient is positive.  The next stages will prove that each resulting bad
parameter set is null.
-/

namespace NRR

open FoxNeuwirthOrderComplex

namespace FoxNeuwirthOrderComplex
namespace EquivariantPrismStableRelativeBoundary
namespace ExplicitAffineRelativeCollar
namespace RouteB

open AffinePositiveRayBoundary
open AffinePositiveRayBoundary.VertexMap
open Parameters
open Polynomials
open RelativeGenericity

variable {p N₀ N₁ M L : Nat}
variable (hp : Nat.Prime p)
variable (C : RelativeAffineCellSystem hp N₀ N₁ M L)

/-- Data selecting one codimension-two face and one retained local vertex whose
scalar orbit is movable.  The selected coordinate `j` is only used to certify
that the vertex is genuinely movable; once one scalar coordinate at a vertex is
movable, the corresponding vector value is controlled by movable orbit data. -/
structure MixedFaceCase where
  cell : C.Cell
  omitted₀ : Fin (p + 1)
  omitted₁ : Fin (p + 1)
  omitted_ne : omitted₀ ≠ omitted₁
  retained : Fin (p + 1)
  retained_ne₀ : retained ≠ omitted₀
  retained_ne₁ : retained ≠ omitted₁
  coordinate : Fin p
  movable : ¬ IsFrozenParameter hp C
    (localParameter hp C cell retained coordinate)

noncomputable instance mixedFaceCaseFintype : Fintype (MixedFaceCase hp C) := by
  let encode : MixedFaceCase hp C →
      C.Cell × Fin (p + 1) × Fin (p + 1) × Fin (p + 1) × Fin p :=
    fun κ => (κ.cell, κ.omitted₀, κ.omitted₁, κ.retained, κ.coordinate)
  exact Fintype.ofInjective encode (by
    intro a b hab
    have hcell : a.cell = b.cell := congrArg (fun z => z.1) hab
    have h0 : a.omitted₀ = b.omitted₀ := congrArg (fun z => z.2.1) hab
    have h1 : a.omitted₁ = b.omitted₁ := congrArg (fun z => z.2.2.1) hab
    have hret : a.retained = b.retained := congrArg (fun z => z.2.2.2.1) hab
    have hcoord : a.coordinate = b.coordinate := congrArg (fun z => z.2.2.2.2) hab
    cases a
    cases b
    simp_all)

noncomputable instance mixedFaceCaseDecidableEq : DecidableEq (MixedFaceCase hp C) :=
  Classical.decEq _

/-- The bad set attached to one distinguished positive movable vertex. -/
def mixedFaceBadSet
    (base : Assignment hp C) (κ : MixedFaceCase hp C) :
    Set (MovableParameterSpace hp C) :=
  {x | ∃ w : StandardSimplex p,
      w κ.omitted₀ = 0 ∧
      w κ.omitted₁ = 0 ∧
      0 < w κ.retained ∧
      (∀ r : Fin (p - 1),
        deviation hp
          (affineValue
            (Polynomials.localVertexMap hp C
              (assignmentOfMovableParameters hp C base x) κ.cell) w) r = 0) ∧
      0 < mean hp
        (affineValue
          (Polynomials.localVertexMap hp C
            (assignmentOfMovableParameters hp C base x) κ.cell) w)}

/-- A positive-ray incidence on a codimension-two face has a positive movable
witness when at least one retained vertex with positive barycentric weight has a
movable local scalar parameter. -/
def HasPositiveMovableWitness
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (q : C.Cell) (w : StandardSimplex p)
    (i j : Fin (p + 1)) : Prop :=
  ∃ k : Fin (p + 1), k ≠ i ∧ k ≠ j ∧ 0 < w k ∧
    ∃ r : Fin p, ¬ IsFrozenParameter hp C (localParameter hp C q k r)

/-- Every codimension-two positive-ray failure with a positive movable witness
belongs to one of the finite bad sets. -/
theorem mem_mixedFaceBadSet_of_incidence
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (q : C.Cell) (w : StandardSimplex p)
    (i j : Fin (p + 1)) (hij : i ≠ j)
    (hi : w i = 0) (hj : w j = 0)
    (hdev : ∀ r : Fin (p - 1),
      deviation hp
        (affineValue
          (Polynomials.localVertexMap hp C
            (assignmentOfMovableParameters hp C base x) q) w) r = 0)
    (hmean : 0 < mean hp
      (affineValue
        (Polynomials.localVertexMap hp C
          (assignmentOfMovableParameters hp C base x) q) w))
    (hmovable : HasPositiveMovableWitness hp C base x q w i j) :
    ∃ κ : MixedFaceCase hp C, x ∈ mixedFaceBadSet hp C base κ := by
  rcases hmovable with ⟨k, hki, hkj, hkpos, r, hrmovable⟩
  let κ : MixedFaceCase hp C :=
    { cell := q
      omitted₀ := i
      omitted₁ := j
      omitted_ne := hij
      retained := k
      retained_ne₀ := hki
      retained_ne₁ := hkj
      coordinate := r
      movable := hrmovable }
  refine ⟨κ, ?_⟩
  exact ⟨w, hi, hj, hkpos, hdev, hmean⟩

/-- Membership in a case bad set reconstructs an explicit positive-ray
codimension-two incidence. -/
theorem incidence_of_mem_mixedFaceBadSet
    (base : Assignment hp C) (x : MovableParameterSpace hp C)
    (κ : MixedFaceCase hp C)
    (hx : x ∈ mixedFaceBadSet hp C base κ) :
    ∃ w : StandardSimplex p,
      w κ.omitted₀ = 0 ∧
      w κ.omitted₁ = 0 ∧
      (∀ r : Fin (p - 1),
        deviation hp
          (affineValue
            (Polynomials.localVertexMap hp C
              (assignmentOfMovableParameters hp C base x) κ.cell) w) r = 0) ∧
      0 < mean hp
        (affineValue
          (Polynomials.localVertexMap hp C
            (assignmentOfMovableParameters hp C base x) κ.cell) w) := by
  rcases hx with ⟨w, h0, h1, hk, hdev, hmean⟩
  exact ⟨w, h0, h1, hdev, hmean⟩

/-- Exact finite-union characterization, under the geometric assertion that
all relevant mixed incidences possess a positive movable witness. -/
theorem exists_badCase_iff_incidence_with_movableWitness
    (base : Assignment hp C) (x : MovableParameterSpace hp C) :
    (∃ κ : MixedFaceCase hp C, x ∈ mixedFaceBadSet hp C base κ) ↔
      ∃ (q : C.Cell) (w : StandardSimplex p)
        (i j : Fin (p + 1)),
        i ≠ j ∧ w i = 0 ∧ w j = 0 ∧
        (∀ r : Fin (p - 1),
          deviation hp
            (affineValue
              (Polynomials.localVertexMap hp C
                (assignmentOfMovableParameters hp C base x) q) w) r = 0) ∧
        0 < mean hp
          (affineValue
            (Polynomials.localVertexMap hp C
              (assignmentOfMovableParameters hp C base x) q) w) ∧
        HasPositiveMovableWitness hp C base x q w i j := by
  constructor
  · rintro ⟨κ, hκ⟩
    rcases hκ with ⟨w, h0, h1, hkpos, hdev, hmean⟩
    refine ⟨κ.cell, w, κ.omitted₀, κ.omitted₁, κ.omitted_ne,
      h0, h1, hdev, hmean, ?_⟩
    exact ⟨κ.retained, κ.retained_ne₀, κ.retained_ne₁, hkpos,
      κ.coordinate, κ.movable⟩
  · rintro ⟨q, w, i, j, hij, hi, hj, hdev, hmean, hmovable⟩
    exact mem_mixedFaceBadSet_of_incidence hp C base x q w i j hij hi hj
      hdev hmean hmovable

end RouteB
end ExplicitAffineRelativeCollar
end EquivariantPrismStableRelativeBoundary
end FoxNeuwirthOrderComplex
end NRR
