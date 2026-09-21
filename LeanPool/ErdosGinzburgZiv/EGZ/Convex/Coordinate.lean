/-
Copyright (c) 2026 Dmitrii Zakharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitrii Zakharov
-/

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Topology
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Topology.DiscreteSubset

/-!
# Coordinate models for the convex part of the paper

The paper works with rational affine spaces inside their real affine spans:
convex coefficients are real, while lattice and transition data are rational.
We make that distinction explicit.  A rank-`n` fibre has real point space
`RealCoord n`, integer lattice coordinates `IntCoord n`, and reduction modulo
`p` in `FpCoord p n`.

Choosing affine lattice coordinates at each node loses no information and is
particularly useful later: an integral-affine transition has compatible real,
integer, and modulo-`p` realizations.  This is the compatibility needed in the
proof of Proposition 7.1.
-/

open scoped BigOperators

namespace EGZ

/-- Real points in a chosen rank-`n` affine-lattice coordinate system. -/
abbrev RealCoord (n : ℕ) := Fin n → ℝ

/-- Integer points in a chosen rank-`n` affine-lattice coordinate system. -/
abbrev IntCoord (n : ℕ) := Fin n → ℤ

/-- Reduction of lattice coordinates modulo `p`. -/
abbrev FpCoord (p n : ℕ) := Fin n → ZMod p

namespace IntCoord

/-- Realification of an integer coordinate vector. -/
def real {n : ℕ} (z : IntCoord n) : RealCoord n := fun i ↦ (z i : ℝ)

/-- Coordinatewise reduction modulo `p`. -/
def mod (p : ℕ) {n : ℕ} (z : IntCoord n) : FpCoord p n := fun i ↦ (z i : ZMod p)

@[simp]
theorem real_apply {n : ℕ} (z : IntCoord n) (i : Fin n) : z.real i = (z i : ℝ) := rfl

@[simp]
theorem mod_apply (p : ℕ) {n : ℕ} (z : IntCoord n) (i : Fin n) :
    z.mod p i = (z i : ZMod p) := rfl

/-- Coordinatewise realification embeds the integer lattice as a closed
discrete subset of finite-dimensional real coordinate space. -/
theorem isClosedEmbedding_real {n : ℕ} :
    Topology.IsClosedEmbedding (@real n) := by
  let f : IntCoord n → RealCoord n :=
    Pi.map (fun _ : Fin n ↦ ((↑) : ℤ → ℝ))
  have hf : Topology.IsClosedEmbedding f :=
    Topology.IsClosedEmbedding.piMap
      (fun _ : Fin n ↦ Real.isClosedEmbedding_intCast)
  have hfr : f = @real n := by
    funext z i
    rfl
  rw [← hfr]
  exact hf

theorem isClosed_range_real {n : ℕ} :
    IsClosed (Set.range (@real n)) :=
  isClosedEmbedding_real.isClosed_range

theorem isDiscrete_range_real {n : ℕ} :
    IsDiscrete (Set.range (@real n)) :=
  isClosedEmbedding_real.isEmbedding.isDiscrete_range

end IntCoord

/-- A real coordinate vector represents a point of the distinguished affine
integer lattice. -/
def IsIntegral {n : ℕ} (q : RealCoord n) : Prop := ∃ z : IntCoord n, z.real = q

/-- A real point has rational coordinate data. -/
def IsRational {n : ℕ} (q : RealCoord n) : Prop :=
  ∀ i, ∃ a : ℚ, (a : ℝ) = q i

/-- An integral affine map in chosen affine-lattice coordinates.

The integer realization makes preservation of the affine lattice explicit;
the last two fields say that the real and modular realizations are obtained
from it by scalar extension and reduction.  In particular, the target modulo
`p` is an affine space: no canonical origin for the original affine lattice is
being assumed. -/
structure IntegralAffineMap (m n : ℕ) where
  /-- Affine map on the real coordinate spaces. -/
  real : RealCoord m →ᵃ[ℝ] RealCoord n
  /-- Map induced on integer coordinates. -/
  integer : IntCoord m → IntCoord n
  /-- Affine map induced on coordinates modulo each natural modulus. -/
  modp : (p : ℕ) → FpCoord p m →ᵃ[ZMod p] FpCoord p n
  real_integer : ∀ z, real z.real = (integer z).real
  mod_integer : ∀ p z, modp p (z.mod p) = (integer z).mod p

namespace IntegralAffineMap

/-- The identity integral-affine map. -/
def id (n : ℕ) : IntegralAffineMap n n where
  real := AffineMap.id ℝ (RealCoord n)
  integer := _root_.id
  modp p := AffineMap.id (ZMod p) (FpCoord p n)
  real_integer _ := rfl
  mod_integer _ _ := rfl

/-- Composition of integral-affine maps. -/
def comp {l m n : ℕ} (f : IntegralAffineMap m n) (g : IntegralAffineMap l m) :
    IntegralAffineMap l n where
  real := f.real.comp g.real
  integer := f.integer ∘ g.integer
  modp p := (f.modp p).comp (g.modp p)
  real_integer z := by simp [f.real_integer, g.real_integer]
  mod_integer p z := by simp [f.mod_integer, g.mod_integer]

@[simp]
theorem id_real (n : ℕ) : (id n).real = AffineMap.id ℝ (RealCoord n) := rfl

@[simp]
theorem id_integer (n : ℕ) : (id n).integer = _root_.id := rfl

@[simp]
theorem id_modp (p n : ℕ) :
    (id n).modp p = AffineMap.id (ZMod p) (FpCoord p n) := rfl

end IntegralAffineMap

/-- A nonempty rational polytope in chosen affine-lattice coordinates.

`finite_integral` is mathematically redundant (bounded rational polytopes have
finitely many lattice points), but recording it here keeps the Helly-constant
API independent of analytic boundedness infrastructure.  It can later be
discharged once, by the constructor for a finite rational vertex set. -/
structure RationalPolytope (n : ℕ) where
  /-- Underlying convex set of the rational polytope. -/
  carrier : Set (RealCoord n)
  /-- Finite rational generating set of the polytope. -/
  generators : Finset (RealCoord n)
  generators_nonempty : generators.Nonempty
  generators_rational : ∀ q ∈ generators, IsRational q
  carrier_eq_convexHull : carrier = convexHull ℝ (↑generators : Set (RealCoord n))
  finite_integral : Set.Finite {q | q ∈ carrier ∧ IsIntegral q}

namespace RationalPolytope

/-- Intersecting a finite convex hull with a supporting level set simply
takes the convex hull of the generators on that level.  This is the finite
polytope fact that makes exposed faces combinatorially finite. -/
theorem convexHull_supportingLevel_eq {n : ℕ}
    (generators : Finset (RealCoord n))
    (functional : RealCoord n →ᵃ[ℝ] ℝ) (level : ℝ)
    (hle : ∀ q ∈ generators, functional q ≤ level) :
    {q | q ∈ convexHull ℝ (↑generators : Set (RealCoord n)) ∧
        functional q = level} =
      convexHull ℝ
        (↑(generators.filter (fun q ↦ functional q = level)) :
          Set (RealCoord n)) := by
  classical
  apply Set.Subset.antisymm
  · intro q hq
    obtain ⟨weight, hweight, hsum, hbary⟩ :=
      Finset.mem_convexHull'.mp hq.1
    have hbary_affine :
        generators.affineCombination ℝ id weight = q := by
      rw [generators.affineCombination_eq_linear_combination id weight hsum]
      exact hbary
    have heval :
        functional q = ∑ y ∈ generators, weight y * functional y := by
      calc
        functional q =
            functional (generators.affineCombination ℝ id weight) := by
              rw [hbary_affine]
        _ = generators.affineCombination ℝ (functional ∘ id) weight :=
          generators.map_affineCombination id weight hsum functional
        _ = ∑ y ∈ generators, weight y • functional y := by
          rw [generators.affineCombination_eq_linear_combination
            (functional ∘ id) weight hsum]
          rfl
        _ = ∑ y ∈ generators, weight y * functional y := by
          simp only [smul_eq_mul]
    have hgap_nonneg : ∀ y ∈ generators,
        0 ≤ weight y * (level - functional y) := by
      intro y hy
      exact mul_nonneg (hweight y hy) (sub_nonneg.mpr (hle y hy))
    have hgap_sum :
        (∑ y ∈ generators, weight y * (level - functional y)) = 0 := by
      calc
        (∑ y ∈ generators, weight y * (level - functional y)) =
            (∑ y ∈ generators, weight y) * level -
              ∑ y ∈ generators, weight y * functional y := by
                simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
        _ = 0 := by rw [hsum, ← heval, hq.2]; ring
    have hgap_zero : ∀ y ∈ generators,
        weight y * (level - functional y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hgap_nonneg).mp hgap_sum
    have hweight_zero : ∀ y ∈ generators,
        functional y ≠ level → weight y = 0 := by
      intro y hy hne
      rcases mul_eq_zero.mp (hgap_zero y hy) with hw | hdiff
      · exact hw
      · exact (hne (sub_eq_zero.mp hdiff).symm).elim
    rw [Finset.mem_convexHull']
    refine ⟨weight, ?_, ?_, ?_⟩
    · intro y hy
      exact hweight y (Finset.mem_filter.mp hy).1
    · calc
        (∑ y ∈ generators.filter (fun y ↦ functional y = level),
            weight y) = ∑ y ∈ generators, weight y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hyfilter
          apply hweight_zero y hy
          simpa only [Finset.mem_filter, hy, true_and] using hyfilter
        _ = 1 := hsum
    · calc
        (∑ y ∈ generators.filter (fun y ↦ functional y = level),
            weight y • y) = ∑ y ∈ generators, weight y • y := by
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro y hy hyfilter
          have hw : weight y = 0 := hweight_zero y hy (by
            simpa only [Finset.mem_filter, hy, true_and] using hyfilter)
          simp [hw]
        _ = q := hbary
  · apply convexHull_min
    · intro q hq
      obtain ⟨hqgen, hqlevel⟩ := Finset.mem_filter.mp hq
      exact ⟨subset_convexHull ℝ _ (by exact hqgen), hqlevel⟩
    · intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ _ hx.1 hy.1 ha hb hab), ?_⟩
      rw [Convex.combo_affine_apply hab, hx.2, hy.2]
      simp only [smul_eq_mul, ← add_mul, hab, one_mul]

/-- A compact subset of finite-dimensional real coordinate space contains
only finitely many points of the standard integer lattice. -/
theorem finite_integral_of_isCompact {n : ℕ} {S : Set (RealCoord n)}
    (hS : IsCompact S) : Set.Finite {q | q ∈ S ∧ IsIntegral q} := by
  have hcompact : IsCompact (S ∩ Set.range (@IntCoord.real n)) :=
    hS.inter_right IntCoord.isClosed_range_real
  have hdiscrete : IsDiscrete (S ∩ Set.range (@IntCoord.real n)) :=
    IntCoord.isDiscrete_range_real.mono Set.inter_subset_right
  have hfinite := hcompact.finite hdiscrete
  have heq : {q | q ∈ S ∧ IsIntegral q} =
      S ∩ Set.range (@IntCoord.real n) := by
    ext q
    constructor
    · rintro ⟨hqS, z, hz⟩
      exact ⟨hqS, ⟨z, hz⟩⟩
    · rintro ⟨hqS, z, hz⟩
      exact ⟨hqS, ⟨z, hz⟩⟩
  rw [heq]
  exact hfinite

/-- The convex hull of a finite set contains only finitely many standard
integer points. -/
theorem finite_integral_convexHull {n : ℕ}
    (generators : Finset (RealCoord n)) :
    Set.Finite {q | q ∈ convexHull ℝ (↑generators : Set (RealCoord n)) ∧
      IsIntegral q} :=
  finite_integral_of_isCompact
    (generators.finite_toSet.isCompact_convexHull ℝ)

/-- A nonempty finite rational set, presented as a finset, determines a
`RationalPolytope` with exactly its ordinary real convex hull as carrier. -/
def ofFinsetConvexHull {n : ℕ} (generators : Finset (RealCoord n))
    (hnonempty : generators.Nonempty)
    (hrational : ∀ q ∈ generators, IsRational q) : RationalPolytope n where
  carrier := convexHull ℝ (↑generators : Set (RealCoord n))
  generators := generators
  generators_nonempty := hnonempty
  generators_rational := hrational
  carrier_eq_convexHull := rfl
  finite_integral := finite_integral_convexHull generators

@[simp]
theorem ofFinsetConvexHull_carrier {n : ℕ}
    (generators : Finset (RealCoord n)) (hnonempty : generators.Nonempty)
    (hrational : ∀ q ∈ generators, IsRational q) :
    (ofFinsetConvexHull generators hnonempty hrational).carrier =
      convexHull ℝ (↑generators : Set (RealCoord n)) := rfl

/-- Set-based constructor used for the support hull in Theorem 1.12. -/
noncomputable def ofFiniteConvexHull {n : ℕ} (S : Set (RealCoord n))
    (hfinite : S.Finite) (hnonempty : S.Nonempty)
    (hrational : ∀ q ∈ S, IsRational q) : RationalPolytope n :=
  ofFinsetConvexHull hfinite.toFinset
    (hfinite.toFinset_nonempty.mpr hnonempty)
    (by
      intro q hq
      exact hrational q (by simpa using hq))

@[simp]
theorem ofFiniteConvexHull_carrier {n : ℕ} (S : Set (RealCoord n))
    (hfinite : S.Finite) (hnonempty : S.Nonempty)
    (hrational : ∀ q ∈ S, IsRational q) :
    (ofFiniteConvexHull S hfinite hnonempty hrational).carrier =
      convexHull ℝ S := by
  simp only [ofFiniteConvexHull, ofFinsetConvexHull_carrier,
    hfinite.coe_toFinset]

/-- The finite convex hull is contained in every convex set containing its
generating set. -/
theorem ofFiniteConvexHull_subset {n : ℕ} (S : Set (RealCoord n))
    (hfinite : S.Finite) (hnonempty : S.Nonempty)
    (hrational : ∀ q ∈ S, IsRational q)
    {C : Set (RealCoord n)} (hSC : S ⊆ C) (hC : Convex ℝ C) :
    (ofFiniteConvexHull S hfinite hnonempty hrational).carrier ⊆ C := by
  rw [ofFiniteConvexHull_carrier]
  exact convexHull_min hSC hC

/-- The carrier of a rational polytope is convex. -/
theorem convex {n : ℕ} (P : RationalPolytope n) : Convex ℝ P.carrier := by
  rw [P.carrier_eq_convexHull]
  exact convex_convexHull ℝ _

/-- A rational polytope is nonempty. -/
theorem nonempty {n : ℕ} (P : RationalPolytope n) : P.carrier.Nonempty := by
  rw [P.carrier_eq_convexHull]
  obtain ⟨q, hq⟩ := P.generators_nonempty
  exact ⟨q, subset_convexHull ℝ _ (by simpa using hq)⟩

/-- The actual vertices are the extreme points of the carrier.  They are kept
separate from an arbitrary finite generating set, which may be redundant. -/
def vertexSet {n : ℕ} (P : RationalPolytope n) : Set (RealCoord n) :=
  P.carrier.extremePoints ℝ

theorem vertexSet_subset_generators {n : ℕ} (P : RationalPolytope n) :
    P.vertexSet ⊆ (↑P.generators : Set (RealCoord n)) := by
  rw [vertexSet, P.carrier_eq_convexHull]
  exact extremePoints_convexHull_subset

theorem finite_vertexSet {n : ℕ} (P : RationalPolytope n) : P.vertexSet.Finite :=
  P.generators.finite_toSet.subset P.vertexSet_subset_generators

theorem rational_of_mem_vertexSet {n : ℕ} (P : RationalPolytope n)
    {q : RealCoord n} (hq : q ∈ P.vertexSet) : IsRational q := by
  have hgen := P.vertexSet_subset_generators hq
  exact P.generators_rational q (by simpa using hgen)

/-- A (nonempty) face, represented as an exposed face.  Every face of a
polytope has such a presentation. -/
structure Face {n : ℕ} (P : RationalPolytope n) where
  /-- Underlying set of points in the exposed face. -/
  carrier : Set (RealCoord n)
  is_exposed : ∃ (functional : RealCoord n →ᵃ[ℝ] ℝ) (level : ℝ),
    (∀ q ∈ P.carrier, functional q ≤ level) ∧
      carrier = {q | q ∈ P.carrier ∧ functional q = level}
  nonempty : carrier.Nonempty

namespace Face

theorem subset_polytope {n : ℕ} {P : RationalPolytope n} (F : P.Face) :
    F.carrier ⊆ P.carrier := by
  obtain ⟨functional, level, _hle, hcarrier⟩ := F.is_exposed
  intro q hq
  rw [hcarrier] at hq
  exact hq.1

@[ext]
theorem ext {n : ℕ} {P : RationalPolytope n} {F G : P.Face}
    (h : F.carrier = G.carrier) : F = G := by
  cases F
  cases G
  simp_all

/-- Relative interior, called simply "interior of a face" in the paper. -/
def relInterior {n : ℕ} {P : RationalPolytope n} (F : P.Face) : Set (RealCoord n) :=
  intrinsicInterior ℝ F.carrier

end Face

end RationalPolytope

end EGZ
