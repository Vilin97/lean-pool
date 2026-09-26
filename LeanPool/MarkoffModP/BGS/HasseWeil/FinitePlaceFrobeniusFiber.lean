/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteExtensionPlaceTower

/-!
# Local place actions in a Frobenius fiber

This file supplies the local ideal-theoretic bridge used by the
Frobenius-coset step of the Hasse--Weil argument.

First, if a maximal ideal has residue degree one over a constant field `S`,
then the kernel of the constant restriction map on its decomposition group is
exactly its inertia group.  This is proved directly from the induced action on
the residue field; it assumes no point-count estimate.

Second, relative Galois conjugation preserves absolute place degree, so it
acts on places of any prescribed degree.  On each finite or infinity
restriction fiber, the stabilizer of a point is identified with the existing
decomposition group.
-/

@[expose] public section

open scoped Pointwise Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier
open IsDedekindDomain

section ResidueDegreeOne

variable {C S A G : Type*}
  [Field C] [Field S] [CommRing A]
  [Algebra C S] [Algebra S A]
  [Group G] [MulSemiringAction G A]

/-- If a maximal ideal has residue degree one over `S`, and the action on the
ambient ring restricts along `π` to the stated action on `S`, then the kernel
of `π` on the decomposition group is exactly the inertia group. -/
theorem stabilizerRestriction_ker_eq_inertia_of_residue_finrank_one
    (q : Ideal A) [q.IsMaximal]
    (π : G →* (S ≃ₐ[C] S))
    (hcompat : ∀ (g : G) (s : S),
      g • algebraMap S A s = algebraMap S A (π g s))
    (hdegree : Module.finrank S q.ResidueField = 1) :
    (π.comp (MulAction.stabilizer G q).subtype).ker =
      q.inertia (MulAction.stabilizer G q) := by
  ext g
  change π g.1 = 1 ↔ ∀ x : A, g.1 • x - x ∈ q
  constructor
  · intro hg x
    have hsurj : Function.Surjective (algebraMap S q.ResidueField) :=
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hdegree).2
    obtain ⟨s, hs⟩ := hsurj (algebraMap A q.ResidueField x)
    have hx : x - algebraMap S A s ∈ q := by
      rw [← Ideal.algebraMap_residueField_eq_zero]
      rw [map_sub, ← IsScalarTower.algebraMap_apply S A q.ResidueField, hs,
        sub_self]
    have hgx : g.1 • (x - algebraMap S A s) ∈ q := by
      have hmem := Ideal.smul_mem_pointwise_smul g.1
        (x - algebraMap S A s) q hx
      rw [g.2] at hmem
      exact hmem
    have hfixs : g.1 • algebraMap S A s = algebraMap S A s := by
      rw [hcompat, hg]
      rfl
    simpa [smul_sub, hfixs] using q.sub_mem hgx hx
  · intro hg
    apply AlgEquiv.ext
    intro s
    have hsMem : algebraMap S A (π g.1 s) - algebraMap S A s ∈ q := by
      simpa [hcompat] using hg (algebraMap S A s)
    have hAZero : algebraMap A q.ResidueField
        (algebraMap S A (π g.1 s - s)) = 0 :=
      Ideal.algebraMap_residueField_eq_zero.mpr (by
        simpa only [map_sub] using hsMem)
    have hsZero : algebraMap S q.ResidueField (π g.1 s - s) = 0 := by
      calc
        algebraMap S q.ResidueField (π g.1 s - s) =
            algebraMap A q.ResidueField
              (algebraMap S A (π g.1 s - s)) :=
          IsScalarTower.algebraMap_apply S A q.ResidueField _
        _ = 0 := hAZero
    have : π g.1 s - s = 0 := by
      apply (algebraMap S q.ResidueField).injective
      simpa using hsZero
    simpa using sub_eq_zero.mp this

end ResidueDegreeOne

section FunctionFieldPlaces

variable (K : Type*) [Field K] [DecidableEq K] [DecidableEq (RatFunc K)]
variable (M : Type*) [Field M] [Algebra (RatFunc K) M]
  [FiniteDimensional (RatFunc K) M]
  [Algebra.IsSeparable (RatFunc K) M]
variable (L : Type*) [Field L] [Algebra (RatFunc K) L]
  [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L]
  [Algebra M L] [IsScalarTower (RatFunc K) M L]
  [IsGalois M L]

omit [Algebra.IsSeparable (RatFunc K) M] [Algebra.IsSeparable (RatFunc K) L] in
/-- Relative Galois conjugation preserves the absolute degree of a finite
place. -/
theorem finiteExtensionFinitePlace_degree_finitePlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionFinitePlace K L) :
    finiteExtensionPlaceDegree K L
        (.inl (finitePlaceGalSmul K M L g P)) =
      finiteExtensionPlaceDegree K L (.inl P) := by
  rw [finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L,
    finiteExtensionPlaceDegree_inl_eq_mul_relativeInertiaDeg K M L]
  rw [finitePlaceUnder_finitePlaceGalSmul]
  have hlocal :=
    finitePlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
      K M L (finitePlaceGalSmul K M L g P) P
      (finitePlaceUnder_finitePlaceGalSmul K M L g P)
  rw [hlocal.2]

omit [Algebra.IsSeparable (RatFunc K) L] in
/-- Relative Galois conjugation preserves the absolute degree of a place
above infinity. -/
theorem finiteExtensionInfinityPlace_degree_infinityPlaceGalSmul
    (g : Gal(L/M)) (P : FiniteExtensionInfinityPlace K L) :
    finiteExtensionPlaceDegree K L
        (.inr (infinityPlaceGalSmul K M L g P)) =
      finiteExtensionPlaceDegree K L (.inr P) := by
  rw [finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M L,
    finiteExtensionPlaceDegree_inr_eq_mul_relativeInertiaDeg K M L]
  rw [infinityPlaceUnder_infinityPlaceGalSmul]
  have hlocal :=
    infinityPlaceRelative_ramificationIdx_inertiaDeg_eq_of_same_under
      K M L (infinityPlaceGalSmul K M L g P) P
      (infinityPlaceUnder_infinityPlaceGalSmul K M L g P)
  rw [hlocal.2]

/-- Finite places of a prescribed absolute degree. -/
abbrev FiniteExtensionFinitePlaceOfDegree (d : ℕ) :=
  {P : FiniteExtensionFinitePlace K L //
    finiteExtensionPlaceDegree K L (.inl P) = d}

/-- Places above infinity of a prescribed absolute degree. -/
abbrev FiniteExtensionInfinityPlaceOfDegree (d : ℕ) :=
  {P : FiniteExtensionInfinityPlace K L //
    finiteExtensionPlaceDegree K L (.inr P) = d}

/-- The relative Galois action on finite places restricts to places of any
prescribed absolute degree. -/
@[implicit_reducible]
noncomputable def finitePlaceOfDegreeGalAction (d : ℕ) :
    MulAction Gal(L/M) (FiniteExtensionFinitePlaceOfDegree K L d) := by
  letI := finitePlaceGalAction K M L
  exact
    { smul := fun g P => ⟨finitePlaceGalSmul K M L g P.1, by
        rw [finiteExtensionFinitePlace_degree_finitePlaceGalSmul K M L g P.1,
          P.2]⟩
      one_smul := fun P => by
        apply Subtype.ext
        exact one_smul Gal(L/M) P.1
      mul_smul := fun g h P => by
        apply Subtype.ext
        exact mul_smul g h P.1 }

/-- The relative Galois action on places above infinity restricts to places
of any prescribed absolute degree. -/
@[implicit_reducible]
noncomputable def infinityPlaceOfDegreeGalAction (d : ℕ) :
    MulAction Gal(L/M) (FiniteExtensionInfinityPlaceOfDegree K L d) := by
  letI := infinityPlaceGalAction K M L
  exact
    { smul := fun g P => ⟨infinityPlaceGalSmul K M L g P.1, by
        rw [finiteExtensionInfinityPlace_degree_infinityPlaceGalSmul
          K M L g P.1, P.2]⟩
      one_smul := fun P => by
        apply Subtype.ext
        exact one_smul Gal(L/M) P.1
      mul_smul := fun g h P => by
        apply Subtype.ext
        exact mul_smul g h P.1 }

omit [DecidableEq K] [DecidableEq (RatFunc K)]
    [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
    [Algebra.IsSeparable (RatFunc K) L] in
/-- On a finite-place restriction fiber, the point stabilizer is the usual
decomposition group of the underlying place. -/
theorem finitePlaceUnderFiber_stabilizer_eq_decompositionGroup
    (P : FiniteExtensionFinitePlace K M)
    (Q : FinitePlaceUnderFiber K M L P) :
    letI := finitePlaceUnderFiberGalAction K M L P
    MulAction.stabilizer Gal(L/M) Q =
      finitePlaceDecompositionGroup K M L Q.1 := by
  let := finiteIntegralClosureGalAction K M L
  let := finitePlaceUnderFiberGalAction K M L P
  ext g
  change (g • Q = Q) ↔ g • Q.1.asIdeal = Q.1.asIdeal
  constructor
  · intro hg
    have hplace : finitePlaceGalSmul K M L g Q.1 = Q.1 :=
      congrArg Subtype.val hg
    exact congrArg HeightOneSpectrum.asIdeal hplace
  · intro hg
    apply Subtype.ext
    apply HeightOneSpectrum.ext
    exact hg

omit [DecidableEq K] [Algebra.IsSeparable (RatFunc K) M] [FiniteDimensional (RatFunc K) L]
  [Algebra.IsSeparable (RatFunc K) L] in
/-- On an infinity-place restriction fiber, the point stabilizer is the
usual decomposition group of the underlying place. -/
theorem infinityPlaceUnderFiber_stabilizer_eq_decompositionGroup
    (P : FiniteExtensionInfinityPlace K M)
    (Q : InfinityPlaceUnderFiber K M L P) :
    letI := infinityPlaceUnderFiberGalAction K M L P
    MulAction.stabilizer Gal(L/M) Q =
      infinityPlaceDecompositionGroup K M L Q.1 := by
  let := infinityIntegralClosureGalAction K M L
  let := infinityPlaceUnderFiberGalAction K M L P
  ext g
  change (g • Q = Q) ↔ g • Q.1.1 = Q.1.1
  constructor
  · intro hg
    have hplace : infinityPlaceGalSmul K M L g Q.1 = Q.1 :=
      congrArg Subtype.val hg
    exact congrArg Subtype.val hplace
  · intro hg
    apply Subtype.ext
    apply Subtype.ext
    exact hg

end FunctionFieldPlaces

end


end BGS.HasseWeil
