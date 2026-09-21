/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import LeanPool.Stafford38.AlgebraicAnalysis.Ore.Associativity
import LeanPool.Stafford38.Stafford38.Ore.IteratedPairStage
import LeanPool.Stafford38.Stafford38.Ore.PairUniversal
import LeanPool.Stafford38.Stafford38.Weyl.Universal

/-!
# The presented Weyl algebra maps to the iterated Ore construction

This file constructs mutually inverse algebra maps between the quotient
presentation and the recursively iterated `PairStage`.  The proof uses only
the two checked universal properties; it does not assume a PBW theorem for
the quotient presentation.
-/

namespace Stafford38.WeylIteratedEquivalence

open Stafford
open AlgebraicAnalysis
open Stafford38.OrePairStage
open Stafford38.OrePairUniversal
open Stafford38.OreIteratedPairStage
open Stafford38.WeylUniversal

noncomputable section

universe u

variable (k : Type u) [Field k]

/-- The scalar algebra structure inherited recursively by the iterated Ore
tower. -/
@[instance_reducible]
def iteratedPairStageAlgebra :
    (n : Nat) → Algebra k (IteratedPairStage k n)
  | 0 => by
      change Algebra k k
      infer_instance
  | n + 1 => by
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra n
      change Algebra k (PairStage (B := IteratedPairStage k n))
      exact pairStageAlgebra

instance (n : Nat) : Algebra k (IteratedPairStage k n) :=
  iteratedPairStageAlgebra k n

/-- The canonical successor embedding as a scalar-preserving algebra map. -/
def stageAlgHom (n : Nat) :
    IteratedPairStage k n →ₐ[k] IteratedPairStage k (n + 1) where
  toRingHom := stageEmbedding k n
  commutes' c := by
    change pairCoefficient (algebraMap k (IteratedPairStage k n) c) =
      @algebraMap k (PairStage (B := IteratedPairStage k n)) _ _
        (pairStageAlgebra (k := k) (B := IteratedPairStage k n)) c
    rw [pairStageAlgebra_algebraMap
      (k := k) (B := IteratedPairStage k n)]
    rfl

/-- Coordinates in the final stage, ordered from newest to oldest. -/
def iteratedCoordinate :
    (n : Nat) → Fin n → IteratedPairStage k n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      Fin.cases (stageCoordinate k n)
        (fun j => stageAlgHom k n (iteratedCoordinate n j)) i

/-- Momenta in the final stage, ordered from newest to oldest. -/
def iteratedMomentum :
    (n : Nat) → Fin n → IteratedPairStage k n
  | 0, i => Fin.elim0 i
  | n + 1, i =>
      Fin.cases (stageMomentum k n)
        (fun j => stageAlgHom k n (iteratedMomentum n j)) i

/-- The combined coordinate-momentum generator family. -/
def iteratedGenerator (n : Nat) :
    (Fin n ⊕ Fin n) → IteratedPairStage k n :=
  Sum.elim (iteratedCoordinate k n) (iteratedMomentum k n)

@[simp]
theorem iteratedCoordinate_zero (n : Nat) :
    iteratedCoordinate k (n + 1) 0 = stageCoordinate k n := rfl

@[simp]
theorem iteratedCoordinate_succ (n : Nat) (i : Fin n) :
    iteratedCoordinate k (n + 1) i.succ =
      stageAlgHom k n (iteratedCoordinate k n i) := rfl

@[simp]
theorem iteratedMomentum_zero (n : Nat) :
    iteratedMomentum k (n + 1) 0 = stageMomentum k n := rfl

@[simp]
theorem iteratedMomentum_succ (n : Nat) (i : Fin n) :
    iteratedMomentum k (n + 1) i.succ =
      stageAlgHom k n (iteratedMomentum k n i) := rfl

theorem map_commutator {A C : Type*} [Ring A] [Ring C]
    (f : A →+* C) (a b : A) :
    f (commutator a b) = commutator (f a) (f b) := by
  simp [AlgebraicAnalysis.ringCommutator]

theorem commutator_swap {A : Type*} [Ring A] (a b : A) :
    commutator b a = -commutator a b := by
  simp [AlgebraicAnalysis.ringCommutator]

/-- An element commuting with the image of every presented Weyl generator
commutes with the image of the whole presented algebra. -/
theorem commutes_freeWeyl_image_of_generators
    {ι A : Type*} [Ring A] [Algebra k A]
    (omega : Matrix ι ι k)
    (f : FreeWeyl k ι omega →ₐ[k] A) (a : A)
    (h : ∀ i, a * f (freeWeylGenerator omega i) =
      f (freeWeylGenerator omega i) * a) :
    ∀ w, a * f w = f w * a := by
  intro w
  rcases RingQuot.mkAlgHom_surjective k (freeWeylRelation omega) w with
    ⟨q, rfl⟩
  let g : FreeAlgebra k ι →ₐ[k] A :=
    f.comp (RingQuot.mkAlgHom k (freeWeylRelation omega))
  change a * g q = g q * a
  induction q using FreeAlgebra.induction k ι with
  | grade0 c =>
      rw [g.commutes]
      exact (Algebra.commutes c a).symm
  | grade1 i =>
      change a * f (freeWeylGenerator omega i) =
        f (freeWeylGenerator omega i) * a
      exact h i
  | mul u v hu hv =>
      rw [map_mul]
      calc
        a * (g u * g v) = (a * g u) * g v := by rw [mul_assoc]
        _ = (g u * a) * g v := by rw [hu]
        _ = g u * (a * g v) := by rw [mul_assoc]
        _ = g u * (g v * a) := by rw [hv]
        _ = (g u * g v) * a := by rw [mul_assoc]
  | add u v hu hv =>
      rw [map_add, mul_add, add_mul, hu, hv]

/-- All recursively adjoined coordinates commute. -/
theorem iteratedCoordinate_commutator (n : Nat) :
    ∀ i j : Fin n,
      commutator (iteratedCoordinate k n i) (iteratedCoordinate k n j) = 0 := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [AlgebraicAnalysis.ringCommutator]
        · simp only [iteratedCoordinate_zero, iteratedCoordinate_succ]
          exact sub_eq_zero.mpr (stageCoordinate_mul_embedding k n _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [iteratedCoordinate_zero, iteratedCoordinate_succ]
          exact sub_eq_zero.mpr (stageCoordinate_mul_embedding k n _).symm
        · simp only [iteratedCoordinate_succ]
          calc
            commutator
                (stageAlgHom k n (iteratedCoordinate k n i))
                (stageAlgHom k n (iteratedCoordinate k n j)) =
              stageAlgHom k n
                (commutator (iteratedCoordinate k n i)
                  (iteratedCoordinate k n j)) :=
                (map_commutator (stageAlgHom k n).toRingHom _ _).symm
            _ = 0 := by rw [ih i j, map_zero]

/-- All recursively adjoined momenta commute. -/
theorem iteratedMomentum_commutator (n : Nat) :
    ∀ i j : Fin n,
      commutator (iteratedMomentum k n i) (iteratedMomentum k n j) = 0 := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp [AlgebraicAnalysis.ringCommutator]
        · simp only [iteratedMomentum_zero, iteratedMomentum_succ]
          exact sub_eq_zero.mpr (stageMomentum_mul_embedding k n _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [iteratedMomentum_zero, iteratedMomentum_succ]
          exact sub_eq_zero.mpr (stageMomentum_mul_embedding k n _).symm
        · simp only [iteratedMomentum_succ]
          calc
            commutator
                (stageAlgHom k n (iteratedMomentum k n i))
                (stageAlgHom k n (iteratedMomentum k n j)) =
              stageAlgHom k n
                (commutator (iteratedMomentum k n i)
                  (iteratedMomentum k n j)) :=
                (map_commutator (stageAlgHom k n).toRingHom _ _).symm
            _ = 0 := by rw [ih i j, map_zero]

/-- Coordinate-momentum commutators are the negative Kronecker delta, in
the convention used by `Matrix.J`. -/
theorem iteratedCoordinate_momentum_commutator (n : Nat) :
    ∀ i j : Fin n,
      commutator (iteratedCoordinate k n i) (iteratedMomentum k n j) =
        if i = j then -1 else 0 := by
  induction n with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ n ih =>
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · change stageCoordinate k n * stageMomentum k n -
              stageMomentum k n * stageCoordinate k n = -1
          rw [stageMomentum_mul_coordinate]
          noncomm_ring
        · simp only [iteratedCoordinate_zero, iteratedMomentum_succ]
          exact sub_eq_zero.mpr (stageCoordinate_mul_embedding k n _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · simp only [iteratedCoordinate_succ, iteratedMomentum_zero]
          simp only [Fin.succ_ne_zero, ↓reduceIte]
          exact sub_eq_zero.mpr (stageMomentum_mul_embedding k n _).symm
        · simp only [iteratedCoordinate_succ, iteratedMomentum_succ]
          calc
            commutator
                (stageAlgHom k n (iteratedCoordinate k n i))
                (stageAlgHom k n (iteratedMomentum k n j)) =
              stageAlgHom k n
                (commutator (iteratedCoordinate k n i)
                  (iteratedMomentum k n j)) :=
                (map_commutator (stageAlgHom k n).toRingHom _ _).symm
            _ = if i.succ = j.succ then -1 else 0 := by
              rw [ih i j]
              by_cases h : i = j <;> simp [h]

/-- The combined generator family realizes the standard symplectic
commutator matrix. -/
theorem iteratedGenerator_commutator (n : Nat) :
    ∀ a b : Fin n ⊕ Fin n,
      commutator (iteratedGenerator k n a) (iteratedGenerator k n b) =
        algebraMap k (IteratedPairStage k n) (Matrix.J (Fin n) k a b) := by
  intro a b
  cases a with
  | inl i =>
      cases b with
      | inl j =>
          change commutator (iteratedCoordinate k n i)
              (iteratedCoordinate k n j) = _
          rw [iteratedCoordinate_commutator]
          simp [Matrix.J]
      | inr j =>
          change commutator (iteratedCoordinate k n i)
              (iteratedMomentum k n j) = _
          rw [iteratedCoordinate_momentum_commutator]
          by_cases h : i = j <;> simp [Matrix.J, h]
  | inr i =>
      cases b with
      | inl j =>
          change commutator (iteratedMomentum k n i)
              (iteratedCoordinate k n j) = _
          rw [commutator_swap,
            iteratedCoordinate_momentum_commutator]
          by_cases h : j = i
          · simp [Matrix.J, h]
          · have hij : i ≠ j := fun e => h e.symm
            simp [Matrix.J, h, hij]
      | inr j =>
          change commutator (iteratedMomentum k n i)
              (iteratedMomentum k n j) = _
          rw [iteratedMomentum_commutator]
          simp [Matrix.J]

/-- The canonical map from the presented rank-`n` Weyl algebra to the
recursively iterated Ore construction. -/
def presentedToIterated (n : Nat) :
    FreeWeyl k (Fin n ⊕ Fin n) (Matrix.J (Fin n) k) →ₐ[k]
      IteratedPairStage k n :=
  freeWeylLift (Matrix.J (Fin n) k) (iteratedGenerator k n)
    (iteratedGenerator_commutator k n)

@[simp]
theorem presentedToIterated_generator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    presentedToIterated k n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) =
      iteratedGenerator k n i := by
  exact freeWeylLift_generator (Matrix.J (Fin n) k)
    (iteratedGenerator k n) (iteratedGenerator_commutator k n) i

/-- The quotient presentation of the rank-`n` Weyl algebra. -/
abbrev PresentedWeyl (n : Nat) :=
  FreeWeyl k (Fin n ⊕ Fin n) (Matrix.J (Fin n) k)

/-- Insert an old index after the newly adjoined coordinate or momentum. -/
def oldIndex {n : Nat} :
    (Fin n ⊕ Fin n) → (Fin (n + 1) ⊕ Fin (n + 1))
  | .inl i => .inl i.succ
  | .inr i => .inr i.succ

/-- The old rank-`n` generators inside the rank-`n+1` presentation. -/
def oldGenerator (n : Nat) (i : Fin n ⊕ Fin n) : PresentedWeyl k (n + 1) :=
  freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (oldIndex i)

theorem oldGenerator_commutator (n : Nat) (i j : Fin n ⊕ Fin n) :
    commutator (oldGenerator k n i) (oldGenerator k n j) =
      algebraMap k (PresentedWeyl k (n + 1)) (Matrix.J (Fin n) k i j) := by
  rw [oldGenerator, oldGenerator, freeWeylGenerator_commutator]
  cases i with
  | inl i =>
      cases j with
      | inl j => (simp [oldIndex, Matrix.J]; rfl)
      | inr j =>
          by_cases h : i = j
          · subst j
            simp? [oldIndex, Matrix.J]
            calc
              _ = -algebraMap k (PresentedWeyl k (n + 1)) 1 :=
                map_neg (algebraMap k (PresentedWeyl k (n + 1))) 1
              _ = -1 := by rw [map_one]
          · (simp [oldIndex, Matrix.J, h]; rfl)
  | inr i =>
      cases j with
      | inl j =>
          by_cases h : i = j <;>
            (simp [oldIndex, Matrix.J, h]; rfl)
      | inr j => (simp [oldIndex, Matrix.J]; rfl)

/-- The canonical rank-shift embedding preserving the old generators. -/
def previousWeylEmbedding (n : Nat) :
    PresentedWeyl k n →ₐ[k] PresentedWeyl k (n + 1) :=
  freeWeylLift (Matrix.J (Fin n) k) (oldGenerator k n)
    (oldGenerator_commutator k n)

@[simp]
theorem previousWeylEmbedding_generator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    previousWeylEmbedding k n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) = oldGenerator k n i := by
  exact freeWeylLift_generator (Matrix.J (Fin n) k) (oldGenerator k n)
    (oldGenerator_commutator k n) i

/-- The newest coordinate in the rank-`n+1` presentation. -/
def presentedCoordinate (n : Nat) : PresentedWeyl k (n + 1) :=
  freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl 0)

/-- The newest momentum in the rank-`n+1` presentation. -/
def presentedMomentum (n : Nat) : PresentedWeyl k (n + 1) :=
  freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr 0)

theorem presentedCoordinate_commutes_oldGenerator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    presentedCoordinate k n * oldGenerator k n i =
      oldGenerator k n i * presentedCoordinate k n := by
  apply sub_eq_zero.mp
  have h := freeWeylGenerator_commutator
    (k := k) (Matrix.J (Fin (n + 1)) k)
    (.inl (0 : Fin (n + 1))) (oldIndex i)
  cases i with
  | inl i =>
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl i.succ)) =
          algebraMap k (PresentedWeyl k (n + 1)) 0 at h
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl i.succ)) = 0
      rw [map_zero] at h
      exact h
  | inr i =>
      have hi : (0 : Fin (n + 1)) ≠ i.succ := i.succ_ne_zero.symm
      simp only [oldIndex] at h
      have hJ : Matrix.J (Fin (n + 1)) k (.inl 0) (.inr i.succ) = 0 := by
        simp [Matrix.J, hi]
      rw [hJ] at h
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr i.succ)) = 0
      rw [map_zero] at h
      exact h

theorem presentedMomentum_commutes_oldGenerator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    presentedMomentum k n * oldGenerator k n i =
      oldGenerator k n i * presentedMomentum k n := by
  apply sub_eq_zero.mp
  have h := freeWeylGenerator_commutator
    (k := k) (Matrix.J (Fin (n + 1)) k)
    (.inr (0 : Fin (n + 1))) (oldIndex i)
  cases i with
  | inl i =>
      have hi : (0 : Fin (n + 1)) ≠ i.succ := i.succ_ne_zero.symm
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl i.succ)) =
          algebraMap k (PresentedWeyl k (n + 1)) 0 at h
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inl i.succ)) = 0
      rw [map_zero] at h
      exact h
  | inr i =>
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr i.succ)) =
          algebraMap k (PresentedWeyl k (n + 1)) 0 at h
      change Stafford.commutator
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr 0))
        (freeWeylGenerator (Matrix.J (Fin (n + 1)) k) (.inr i.succ)) = 0
      rw [map_zero] at h
      exact h

theorem presentedCoordinate_commutes_previous (n : Nat) :
    ∀ w : PresentedWeyl k n,
      presentedCoordinate k n * previousWeylEmbedding k n w =
        previousWeylEmbedding k n w * presentedCoordinate k n :=
  commutes_freeWeyl_image_of_generators k (Matrix.J (Fin n) k)
    (previousWeylEmbedding k n) (presentedCoordinate k n) (by
      intro i
      simpa using presentedCoordinate_commutes_oldGenerator k n i)

theorem presentedMomentum_commutes_previous (n : Nat) :
    ∀ w : PresentedWeyl k n,
      presentedMomentum k n * previousWeylEmbedding k n w =
        previousWeylEmbedding k n w * presentedMomentum k n :=
  commutes_freeWeyl_image_of_generators k (Matrix.J (Fin n) k)
    (previousWeylEmbedding k n) (presentedMomentum k n) (by
      intro i
      simpa using presentedMomentum_commutes_oldGenerator k n i)

theorem presentedMomentum_mul_coordinate (n : Nat) :
    presentedMomentum k n * presentedCoordinate k n =
      presentedCoordinate k n * presentedMomentum k n + 1 := by
  have h := freeWeylGenerator_commutator
    (k := k) (Matrix.J (Fin (n + 1)) k)
    (.inr (0 : Fin (n + 1))) (.inl (0 : Fin (n + 1)))
  change Stafford.commutator (presentedMomentum k n)
    (presentedCoordinate k n) = algebraMap k (PresentedWeyl k (n + 1)) 1 at h
  rw [map_one] at h
  change presentedMomentum k n * presentedCoordinate k n -
    presentedCoordinate k n * presentedMomentum k n = 1 at h
  calc
    presentedMomentum k n * presentedCoordinate k n =
        (presentedMomentum k n * presentedCoordinate k n -
          presentedCoordinate k n * presentedMomentum k n) +
            presentedCoordinate k n * presentedMomentum k n := by noncomm_ring
    _ = 1 + presentedCoordinate k n * presentedMomentum k n := by rw [h]
    _ = presentedCoordinate k n * presentedMomentum k n + 1 := add_comm _ _

/-- The recursive map from the Ore tower back to the quotient presentation. -/
def iteratedToPresented :
    (n : Nat) → IteratedPairStage k n →ₐ[k] PresentedWeyl k n
  | 0 => Algebra.ofId k (PresentedWeyl k 0)
  | n + 1 => by
      letI : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      letI : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      change PairStage (B := IteratedPairStage k n) →ₐ[k]
        PresentedWeyl k (n + 1)
      let f : IteratedPairStage k n →ₐ[k] PresentedWeyl k (n + 1) :=
        (previousWeylEmbedding k n).comp (iteratedToPresented n)
      exact pairLiftAlgHom f (presentedCoordinate k n) (presentedMomentum k n)
        (fun b => presentedCoordinate_commutes_previous k n
          (iteratedToPresented n b))
        (fun b => presentedMomentum_commutes_previous k n
          (iteratedToPresented n b))
        (presentedMomentum_mul_coordinate k n)

@[simp]
theorem iteratedToPresented_coefficient (n : Nat)
    (b : IteratedPairStage k n) :
    iteratedToPresented k (n + 1) (stageEmbedding k n b) =
      previousWeylEmbedding k n (iteratedToPresented k n b) := by
  let : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  let : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  change pairLiftAlgHom _ _ _ _ _ _ (pairCoefficient b) = _
  exact pairLiftAlgHom_coefficient _ _ _ _ _ _ b

@[simp]
theorem iteratedToPresented_coordinate (n : Nat) :
    iteratedToPresented k (n + 1) (stageCoordinate k n) =
      presentedCoordinate k n := by
  let : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  let : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  change pairLiftAlgHom _ _ _ _ _ _ pairCoordinate = _
  exact pairLiftAlgHom_coordinate _ _ _ _ _ _

@[simp]
theorem iteratedToPresented_momentum (n : Nat) :
    iteratedToPresented k (n + 1) (stageMomentum k n) =
      presentedMomentum k n := by
  let : Algebra k (IteratedPairStage k n) := iteratedPairStageAlgebra k n
  let : Algebra k (PairStage (B := IteratedPairStage k n)) := pairStageAlgebra
  change pairLiftAlgHom _ _ _ _ _ _ pairMomentum = _
  exact pairLiftAlgHom_momentum _ _ _ _ _ _

theorem presentedToIterated_previous (n : Nat) :
    (presentedToIterated k (n + 1)).comp (previousWeylEmbedding k n) =
      (stageAlgHom k n).comp (presentedToIterated k n) := by
  apply freeWeyl_algHom_ext
  intro i
  simp only [AlgHom.comp_apply, previousWeylEmbedding_generator,
    presentedToIterated_generator]
  cases i <;> unfold oldGenerator oldIndex <;>
    rw [presentedToIterated_generator] <;> rfl

@[simp]
theorem presentedToIterated_coordinate (n : Nat) :
    presentedToIterated k (n + 1) (presentedCoordinate k n) =
      stageCoordinate k n := by
  unfold presentedCoordinate
  rw [presentedToIterated_generator]
  rfl

@[simp]
theorem presentedToIterated_momentum (n : Nat) :
    presentedToIterated k (n + 1) (presentedMomentum k n) =
      stageMomentum k n := by
  unfold presentedMomentum
  rw [presentedToIterated_generator]
  rfl

/-- Mapping from the Ore tower to the presentation and back is the identity. -/
theorem presentedToIterated_comp_iteratedToPresented :
    ∀ n : Nat,
      (presentedToIterated k n).comp (iteratedToPresented k n) =
        AlgHom.id k (IteratedPairStage k n) := by
  intro n
  induction n with
  | zero =>
      apply AlgHom.ext
      intro c
      change k at c
      change presentedToIterated k 0
        (algebraMap k (PresentedWeyl k 0) c) = c
      rw [(presentedToIterated k 0).commutes]
      rfl
  | succ n ih =>
      let : Algebra k (IteratedPairStage k n) :=
        iteratedPairStageAlgebra k n
      let : Algebra k (PairStage (B := IteratedPairStage k n)) :=
        pairStageAlgebra
      let f : IteratedPairStage k n →ₐ[k] IteratedPairStage k (n + 1) :=
        stageAlgHom k n
      let X : IteratedPairStage k (n + 1) := stageCoordinate k n
      let P : IteratedPairStage k (n + 1) := stageMomentum k n
      let g : IteratedPairStage k (n + 1) →ₐ[k]
          IteratedPairStage k (n + 1) :=
        (presentedToIterated k (n + 1)).comp
          (iteratedToPresented k (n + 1))
      have hgCoefficient : ∀ b, g (stageEmbedding k n b) = f b := by
        intro b
        dsimp [g, f]
        rw [iteratedToPresented_coefficient]
        have hp := DFunLike.congr_fun (presentedToIterated_previous k n)
          (iteratedToPresented k n b)
        calc
          presentedToIterated k (n + 1)
              (previousWeylEmbedding k n (iteratedToPresented k n b)) =
              stageAlgHom k n
                (presentedToIterated k n (iteratedToPresented k n b)) := hp
          _ = stageAlgHom k n b := by
            have hib : presentedToIterated k n (iteratedToPresented k n b) = b := by
              change ((presentedToIterated k n).comp
                (iteratedToPresented k n)) b = b
              rw [ih]
              rfl
            rw [hib]
      have hgCoordinate : g (stageCoordinate k n) = X := by
        dsimp [g, X]
        rw [iteratedToPresented_coordinate, presentedToIterated_coordinate]
      have hgMomentum : g (stageMomentum k n) = P := by
        dsimp [g, P]
        rw [iteratedToPresented_momentum, presentedToIterated_momentum]
      have hg : g = pairLiftAlgHom f X P
          (stageCoordinate_mul_embedding k n)
          (stageMomentum_mul_embedding k n)
          (stageMomentum_mul_coordinate k n) :=
        pairLiftAlgHom_unique f X P
          (stageCoordinate_mul_embedding k n)
          (stageMomentum_mul_embedding k n)
          (stageMomentum_mul_coordinate k n) g
          hgCoefficient hgCoordinate hgMomentum
      have hid : AlgHom.id k (IteratedPairStage k (n + 1)) =
          pairLiftAlgHom f X P
            (stageCoordinate_mul_embedding k n)
            (stageMomentum_mul_embedding k n)
            (stageMomentum_mul_coordinate k n) :=
        pairLiftAlgHom_unique f X P
          (stageCoordinate_mul_embedding k n)
          (stageMomentum_mul_embedding k n)
          (stageMomentum_mul_coordinate k n)
          (AlgHom.id k (IteratedPairStage k (n + 1)))
          (fun _ => rfl) rfl rfl
      exact hg.trans hid.symm

/-- The recursive inverse sends every iterated generator back to its named
generator in the quotient presentation. -/
theorem iteratedToPresented_generator :
    ∀ (n : Nat) (i : Fin n ⊕ Fin n),
      iteratedToPresented k n (iteratedGenerator k n i) =
        freeWeylGenerator (Matrix.J (Fin n) k) i := by
  intro n
  induction n with
  | zero =>
      intro i
      exact Sum.elim Fin.elim0 Fin.elim0 i
  | succ n ih =>
      intro i
      cases i with
      | inl i =>
          refine Fin.cases ?_ (fun j => ?_) i
          · change iteratedToPresented k (n + 1) (stageCoordinate k n) = _
            rw [iteratedToPresented_coordinate]
            rfl
          · change iteratedToPresented k (n + 1)
              (stageEmbedding k n (iteratedCoordinate k n j)) = _
            rw [iteratedToPresented_coefficient]
            change previousWeylEmbedding k n
              (iteratedToPresented k n (iteratedGenerator k n (.inl j))) = _
            rw [ih (.inl j), previousWeylEmbedding_generator]
            rfl
      | inr i =>
          refine Fin.cases ?_ (fun j => ?_) i
          · change iteratedToPresented k (n + 1) (stageMomentum k n) = _
            rw [iteratedToPresented_momentum]
            rfl
          · change iteratedToPresented k (n + 1)
              (stageEmbedding k n (iteratedMomentum k n j)) = _
            rw [iteratedToPresented_coefficient]
            change previousWeylEmbedding k n
              (iteratedToPresented k n (iteratedGenerator k n (.inr j))) = _
            rw [ih (.inr j), previousWeylEmbedding_generator]
            rfl

/-- Mapping from the quotient presentation to the Ore tower and back is the
identity. -/
theorem iteratedToPresented_comp_presentedToIterated (n : Nat) :
    (iteratedToPresented k n).comp (presentedToIterated k n) =
      AlgHom.id k (PresentedWeyl k n) := by
  apply freeWeyl_algHom_ext
  intro i
  rw [AlgHom.comp_apply, presentedToIterated_generator,
    iteratedToPresented_generator]
  rfl

/-- The quotient presentation is canonically equivalent to the recursive
Ore construction, without using PBW independence for the quotient. -/
def presentedIteratedEquiv (n : Nat) :
    PresentedWeyl k n ≃ₐ[k] IteratedPairStage k n :=
  AlgEquiv.ofAlgHom (presentedToIterated k n) (iteratedToPresented k n)
    (presentedToIterated_comp_iteratedToPresented k n)
    (iteratedToPresented_comp_presentedToIterated k n)

@[simp]
theorem presentedIteratedEquiv_generator (n : Nat)
    (i : Fin n ⊕ Fin n) :
    presentedIteratedEquiv k n
        (freeWeylGenerator (Matrix.J (Fin n) k) i) =
      iteratedGenerator k n i := by
  exact presentedToIterated_generator k n i


end

end Stafford38.WeylIteratedEquivalence
