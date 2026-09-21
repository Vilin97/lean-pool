/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.Stafford38.FixedSourceStatement
import Mathlib.Order.Lattice.Nat

/-!
# Transport for the Mathlib-only exact-source challenge

`FixedSourceChallenge.lean` states the exact fixed-source theorem using only
Mathlib: the Weyl algebra is the `RingQuot` of the free algebra by the Weyl
commutator relation, the Bernstein filtration is the span of the images of the
ordered PBW words of bounded total degree, and the Bernstein degree of an
element is the least filtration level containing it.

This file repeats those definitions verbatim in the namespace
`Stafford38FixedSourceChallenge`, without importing the challenge file, and
proves that they agree with the substantive development:

* the challenge quotient is definitionally the presented Weyl algebra
  `Stafford38.WeylIteratedEquivalence.PresentedWeyl`;
* the challenge ordered words are the development's
  `Stafford38.WeylPBW.presentedOrderedMonomial`;
* the challenge filtration is the development's Bernstein filtration
  `Stafford38.WeylFiltration.bernsteinPiece`;
* the challenge degree is the development's checked PBW normal-form degree
  `Stafford38.FixedSource.bernsteinDegree`;
* the two linear-coordinate predicates are definitionally the same.

`FixedSourceSolution.lean` combines these identifications with the proved
theorem `Stafford38.universalFixedSourceStatement`. No degree and no
normal-form datum is supplied as a hypothesis anywhere.
-/

namespace Stafford38FixedSourceChallenge

universe u

/-- The disjoint coordinate and momentum indices for `n` Weyl pairs. -/
abbrev PhaseVar (n : ℕ) := Fin n ⊕ Fin n

/-- The free-algebra relation imposing the commutators prescribed by a matrix. -/
def relation {k : Type u} [Field k] {n : ℕ}
    (omega : Matrix (PhaseVar n) (PhaseVar n) k)
    (a b : FreeAlgebra k (PhaseVar n)) : Prop :=
  ∃ i j,
    a = FreeAlgebra.ι k i * FreeAlgebra.ι k j -
      FreeAlgebra.ι k j * FreeAlgebra.ι k i ∧
    b = algebraMap k (FreeAlgebra k (PhaseVar n)) (omega i j)

/-- The Weyl algebra presented by the standard coordinate-momentum commutator relations. -/
abbrev WeylAlg (k : Type u) [Field k] (n : ℕ) :=
  RingQuot (relation (k := k) (n := n) (Matrix.J (Fin n) k))

/-- The image of a formal coordinate or momentum generator in the Weyl quotient. -/
def generator (k : Type u) [Field k] (n : ℕ) (i : PhaseVar n) : WeylAlg k n :=
  RingQuot.mkAlgHom k (relation (k := k) (n := n) (Matrix.J (Fin n) k))
    (FreeAlgebra.ι k i)

/-- The inclusion of the old phase indices after adjoining a new first Weyl pair. -/
def oldIndex {n : ℕ} : PhaseVar n → PhaseVar (n + 1)
  | .inl i => .inl i.succ
  | .inr i => .inr i.succ

/-- The free-algebra map shifting all generators past the newly adjoined pair. -/
def freeOldMap (k : Type u) [Field k] (n : ℕ) :
    FreeAlgebra k (PhaseVar n) →ₐ[k] FreeAlgebra k (PhaseVar (n + 1)) :=
  FreeAlgebra.lift k (fun i => FreeAlgebra.ι k (oldIndex i))

/-- The recursively ordered free-algebra monomial with prescribed coordinate and momentum
exponents. -/
def freeOrderedMonomial (k : Type u) [Field k] :
    (n : ℕ) → (Fin n → ℕ) → (Fin n → ℕ) → FreeAlgebra k (PhaseVar n)
  | 0, _, _ => 1
  | n + 1, a, p =>
      freeOldMap k n
          (freeOrderedMonomial k n (fun i => a i.succ) (fun i => p i.succ)) *
        FreeAlgebra.ι k (.inl (0 : Fin (n + 1))) ^ a 0 *
        FreeAlgebra.ι k (.inr (0 : Fin (n + 1))) ^ p 0

/-- The Weyl-algebra image of the recursively ordered monomial. -/
def orderedMonomial (k : Type u) [Field k] (n : ℕ)
    (a p : Fin n → ℕ) : WeylAlg k n :=
  RingQuot.mkAlgHom k (relation (k := k) (n := n) (Matrix.J (Fin n) k))
    (freeOrderedMonomial k n a p)

/-- The total coordinate and momentum degree of an exponent pair. -/
def phaseDegree {n : ℕ} (a p : Fin n → ℕ) : ℕ :=
  (∑ i, a i) + ∑ i, p i

/-- The span of ordered monomials of total phase degree at most `N`. -/
def bernsteinPiece (k : Type u) [Field k] (n N : ℕ) :
    Submodule k (WeylAlg k n) :=
  Submodule.span k
    {z | ∃ a p : Fin n → ℕ,
      phaseDegree a p ≤ N ∧ z = orderedMonomial k n a p}

/-- The least Bernstein filtration degree containing the specified Weyl element. -/
noncomputable def bernsteinDegree (k : Type u) [Field k] {n : ℕ}
    (d : WeylAlg k n) : ℕ :=
  sInf {N : ℕ | d ∈ bernsteinPiece k n N}

/-- The matrix-weighted linear combination of a family of Weyl elements. -/
def linearCombination (k : Type u) [Field k] {n : ℕ}
    (M : Matrix (PhaseVar n) (PhaseVar n) k)
    (z : PhaseVar n → WeylAlg k n) (i : PhaseVar n) : WeylAlg k n :=
  ∑ j, algebraMap k (WeylAlg k n) (M i j) * z j

/-- The standard symplectic form on the coordinate and momentum indices. -/
abbrev standardForm (k : Type u) [Field k] (n : ℕ) :
    Matrix (PhaseVar n) (PhaseVar n) k := Matrix.J (Fin n) k

/-- A coordinate obtained from the standard first coordinate by an invertible symplectic linear
change. -/
def IsLinearWeylCoordinate (k : Type u) [Field k] (n : ℕ)
    (ell : WeylAlg k (n + 1)) : Prop :=
  ∃ (M N : Matrix (PhaseVar (n + 1)) (PhaseVar (n + 1)) k)
      (_hM : M * standardForm k (n + 1) * Matrix.transpose M =
        standardForm k (n + 1))
      (_hN : N * standardForm k (n + 1) * Matrix.transpose N =
        standardForm k (n + 1))
      (_hMN : M * N = 1) (_hNM : N * M = 1),
      ell = linearCombination k N (generator k (n + 1))
        (.inl (0 : Fin (n + 1)))

/-- The Stafford identity using a linear Weyl coordinate raised to the input element’s Bernstein
degree. -/
def UniversalFixedSourceStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (n : ℕ)
    (d : WeylAlg k (n + 1)), d ≠ 0 →
      ∃ ell R S : WeylAlg k (n + 1),
        IsLinearWeylCoordinate k n ell ∧
          (1 : WeylAlg k (n + 1)) =
            d * R + ell ^ bernsteinDegree k d * d * S

end Stafford38FixedSourceChallenge

namespace Stafford38FixedSourceChallengeTransport

open Stafford
open Stafford38.WeylPBW
open Stafford38.WeylFiltration
open Stafford38.WeylIteratedEquivalence

universe u

variable (k : Type u) [Field k]

/-- The challenge quotient is the presented Weyl algebra, definitionally. -/
theorem weylAlg_eq (n : ℕ) :
    Stafford38FixedSourceChallenge.WeylAlg k n = PresentedWeyl k n := rfl

/-- The challenge generators are the presented generators, definitionally. -/
theorem generator_eq (n : ℕ) (i : Stafford38FixedSourceChallenge.PhaseVar n) :
    Stafford38FixedSourceChallenge.generator k n i =
      freeWeylGenerator (Matrix.J (Fin n) k) i := rfl

theorem oldIndex_eq {n : ℕ} (i : Stafford38FixedSourceChallenge.PhaseVar n) :
    Stafford38FixedSourceChallenge.oldIndex i =
      Stafford38.WeylIteratedEquivalence.oldIndex i := by
  cases i <;> rfl

/-- Inserting an old free word and passing to the quotient agrees with the
development's rank-shift embedding of the old quotient. -/
theorem mkAlgHom_freeOldMap (n : ℕ)
    (x : FreeAlgebra k (Stafford38FixedSourceChallenge.PhaseVar n)) :
    RingQuot.mkAlgHom k
        (Stafford38FixedSourceChallenge.relation (k := k) (n := n + 1)
          (Matrix.J (Fin (n + 1)) k))
        (Stafford38FixedSourceChallenge.freeOldMap k n x) =
      previousWeylEmbedding k n
        (RingQuot.mkAlgHom k
          (Stafford38FixedSourceChallenge.relation (k := k) (n := n)
            (Matrix.J (Fin n) k)) x) := by
  have h :
      (RingQuot.mkAlgHom k
          (Stafford38FixedSourceChallenge.relation (k := k) (n := n + 1)
            (Matrix.J (Fin (n + 1)) k))).comp
          (Stafford38FixedSourceChallenge.freeOldMap k n) =
        (previousWeylEmbedding k n).comp
          (RingQuot.mkAlgHom k
            (Stafford38FixedSourceChallenge.relation (k := k) (n := n)
              (Matrix.J (Fin n) k))) := by
    apply FreeAlgebra.hom_ext
    funext i
    simp only [Function.comp_apply, AlgHom.comp_apply,
      Stafford38FixedSourceChallenge.freeOldMap, FreeAlgebra.lift_ι_apply]
    change freeWeylGenerator (Matrix.J (Fin (n + 1)) k)
        (Stafford38FixedSourceChallenge.oldIndex i) =
      previousWeylEmbedding k n (freeWeylGenerator (Matrix.J (Fin n) k) i)
    rw [previousWeylEmbedding_generator, oldIndex_eq]
    rfl
  exact DFunLike.congr_fun h x

/-- The challenge ordered words are the development's ordered PBW words. -/
theorem orderedMonomial_eq :
    ∀ (n : ℕ) (a p : Fin n → ℕ),
      Stafford38FixedSourceChallenge.orderedMonomial k n a p =
        presentedOrderedMonomial k n a p := by
  intro n
  induction n with
  | zero =>
      intro a p
      simp only [Stafford38FixedSourceChallenge.orderedMonomial,
        Stafford38FixedSourceChallenge.freeOrderedMonomial,
        presentedOrderedMonomial, map_one]
      rfl
  | succ n ih =>
      intro a p
      have htail := ih (fun i => a i.succ) (fun i => p i.succ)
      rw [Stafford38FixedSourceChallenge.orderedMonomial] at htail
      simp only [Stafford38FixedSourceChallenge.orderedMonomial,
        Stafford38FixedSourceChallenge.freeOrderedMonomial, map_mul, map_pow,
        presentedOrderedMonomial]
      rw [mkAlgHom_freeOldMap, htail]
      rfl

/-- The Bernstein weight of a split exponent is the challenge's total phase
degree. -/
theorem monomialWeight_bernstein_phaseExponent {n : ℕ} (a p : Fin n → ℕ) :
    monomialWeight (@bernsteinWeight n) (phaseExponent a p) =
      Stafford38FixedSourceChallenge.phaseDegree a p := by
  unfold monomialWeight bernsteinWeight Stafford38FixedSourceChallenge.phaseDegree
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
  simp [Fintype.sum_sum_type]

/-- The challenge filtration is the development's Bernstein filtration. -/
theorem bernsteinPiece_eq (n N : ℕ) :
    Stafford38FixedSourceChallenge.bernsteinPiece k n N =
      Stafford38.WeylFiltration.bernsteinPiece k n N := by
  rw [Stafford38FixedSourceChallenge.bernsteinPiece,
    Stafford38.WeylFiltration.bernsteinPiece, presentedWeightPiece_eq_span]
  congr 1
  ext z
  simp only [presentedWeightBasisSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a, p, hdeg, rfl⟩
    refine ⟨phaseExponent a p, ?_, ?_⟩
    · rw [monomialWeight_bernstein_phaseExponent]
      exact hdeg
    · rw [presentedPBWBasis_apply, orderedMonomial_eq]
      rfl
  · rintro ⟨m, hdeg, rfl⟩
    refine ⟨fun i => m (.inl i), fun i => m (.inr i), ?_, ?_⟩
    · rw [← monomialWeight_bernstein_phaseExponent, phaseExponent_split]
      exact hdeg
    · rw [presentedPBWBasis_apply, orderedMonomial_eq]

/-- The challenge's intrinsic degree is the development's checked PBW
normal-form degree. -/
theorem bernsteinDegree_eq {n : ℕ} (d : PresentedWeyl k n) :
    Stafford38FixedSourceChallenge.bernsteinDegree k d =
      Stafford38.FixedSource.bernsteinDegree k d := by
  have hmem' : d ∈ presentedWeightPiece k (@bernsteinWeight n)
      (Stafford38.FixedSource.bernsteinDegree k d) :=
    (mem_presentedWeightPiece k _ _ d).mpr fun m hm =>
      MvPolynomial.le_weightedTotalDegree _
        (MvPolynomial.mem_support_iff.mpr hm)
  have hmem : d ∈ Stafford38FixedSourceChallenge.bernsteinPiece k n
      (Stafford38.FixedSource.bernsteinDegree k d) := by
    rw [bernsteinPiece_eq]
    exact hmem'
  have hle : ∀ N, d ∈ Stafford38FixedSourceChallenge.bernsteinPiece k n N →
      Stafford38.FixedSource.bernsteinDegree k d ≤ N := by
    intro N hN
    rw [bernsteinPiece_eq] at hN
    have hN' : d ∈ presentedWeightPiece k (@bernsteinWeight n) N := hN
    rw [mem_presentedWeightPiece] at hN'
    apply Finset.sup_le
    intro m hm
    exact hN' m (MvPolynomial.mem_support_iff.mp hm)
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · exact le_csInf ⟨_, hmem⟩ hle

/-- The two linear symplectic coordinate predicates are definitionally the
same. -/
theorem isLinearWeylCoordinate_iff (n : ℕ)
    (ell : Stafford38FixedSourceChallenge.WeylAlg k (n + 1)) :
    Stafford38FixedSourceChallenge.IsLinearWeylCoordinate k n ell ↔
      Stafford38.FixedSource.IsLinearWeylCoordinate k n ell :=
  Iff.rfl


end Stafford38FixedSourceChallengeTransport
