/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
import Mathlib.Algebra.Ring.Basic
import Mathlib.RingTheory.NonUnitalSubring.Defs
import Mathlib.Algebra.Ring.Equiv
import LeanPool.ArtinWedderburn.CornerRing
import LeanPool.ArtinWedderburn.Idempotents

/-!
# Iterated corner rings

If `e : R` is idempotent and `f ∈ CornerSubring idem_e` is idempotent, then the
corner subring of `f` inside `eRe` agrees (as a ring) with the corner subring of
`f` viewed in `R`.
-/

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]

lemma val_mul_subring (S : NonUnitalSubring R) (a b : S) : (a * b : S) = a.val * b.val := by
  simp only [NonUnitalSubring.val_mul]

-- theorem: if we have a non unital subring S of R and a non unital subring A of S, and a non
-- unital subring B of R that has the same elements as A, then A is isomorphic to B
/-- A non-unital subring `A` of `S ⊆ R` is isomorphic to any non-unital subring `B` of `R`
whose carrier matches the image of `A` under `S.val`. -/
def non_unital_subring_eq
    {S : NonUnitalSubring R}
    [Ring S]
    (ha : ∀ x y : ↥S, (x + y : ↥S) = x.val + y.val)
    (hs : ∀ x y : ↥S, (x * y : ↥S) = x.val * y.val)
    {A : NonUnitalSubring S}
    {B : NonUnitalSubring R}
    (h : (Subtype.val '' A.carrier) = B.carrier) : A ≃+* B := by
  have h' (x : R) : x ∈ B ↔ x ∈ Subtype.val '' A.carrier := by rw [h]; rfl
  have h'' (b : B) : b.val ∈ S := by
    have hx : b.val ∈ Subtype.val '' A.carrier := by rw [← h']; exact b.property
    obtain ⟨w, ⟨_, weqb⟩⟩ := hx
    rw [← weqb]
    exact w.property
  have h''' (b : B) : ⟨b.val, h'' b⟩ ∈ A := by
    have hx : b.val ∈ Subtype.val '' A.carrier := by rw [← h']; exact b.property
    obtain ⟨w, ⟨ca, weqb⟩⟩ := hx
    simp only [← weqb, Subtype.coe_eta]
    exact ca
  exact
    { toFun := fun a => ⟨a.val, by rw [h']; simp⟩
      invFun := fun b => ⟨⟨b, by apply h''⟩, by apply h'''⟩
      left_inv := by intro a; simp,
      right_inv := by intro b; simp,
      map_mul' := by
        intro a b
        simp only [NonUnitalSubring.val_mul, MulMemClass.mk_mul_mk, Subtype.mk.injEq]
        rw [hs a b]
      map_add' := by
        simp [ha] }

variable {R : Type*} [Ring R]
variable {e : R}
variable {idem_e : IsIdempotentElem e}
variable (f : CornerSubring idem_e)

-- we want to prove: if e is an idempotent element of R, and f is an idempotent element of the
-- corner ring of e, then the CornerSubringNonUnital of f.val is isomorphic to the
-- CornerSubringNonUnital of f of the corner ring of e

-- the next theorem states that this is indeed true on the level of sets
theorem double_corner_set_eq :
    (Subtype.val '' (CornerSubringNonUnital f).carrier) =
      (CornerSubringNonUnital (f : R)).carrier := by
  rw [corner_ring_carrier, corner_ring_carrier]
  ext x
  constructor
  · intro hx
    obtain ⟨y, ⟨hy, rfl⟩⟩ := hx
    obtain ⟨z, ⟨hz, rfl⟩⟩ := hy
    simp only [NonUnitalSubring.val_mul]
    exact ⟨z, rfl⟩
  · intro hx
    obtain ⟨y, ⟨hy, rfl⟩⟩ := hx
    let a : CornerSubring idem_e := ⟨e * y * e, ⟨y, rfl⟩⟩
    refine ⟨f * a * f, ⟨a, rfl⟩, ?_⟩
    simp only [NonUnitalSubring.val_mul]
    have h1f : f = 1 * f := by simp
    have heff : e * (f : R) = f := by nth_rewrite 2 [h1f]; rfl
    have hf1 : f = f * 1 := by simp
    have hffe : f = f * e := by nth_rewrite 1 [hf1]; rfl
    rw [mul_assoc, mul_assoc, heff, ← mul_assoc, ← mul_assoc, ← hffe]

-- auxiliary lemma since there is a problem with direct application
/-- Specialisation of `non_unital_subring_eq` to the corner subrings of `f` and `f.val`,
isolated to work around an elaboration issue with direct application. -/
def corner_ring_eq_lemma
    (h : (Subtype.val '' (CornerSubringNonUnital f).carrier) =
      (CornerSubringNonUnital (f : R)).carrier) :
    CornerSubringNonUnital f ≃+* CornerSubringNonUnital (f : R) :=
  @non_unital_subring_eq R _ (CornerSubring idem_e) _ (by simp) (by simp)
    (CornerSubringNonUnital f) (CornerSubringNonUnital (f : R)) h

-- what we wanted to prove
/-- The non-unital corner subring of `f` inside the corner ring `eRe` is isomorphic to the
non-unital corner subring of `f.val` inside `R`. -/
def corner_ring_non_unital_eq : CornerSubringNonUnital f ≃+* CornerSubringNonUnital (f : R) := by
  apply corner_ring_eq_lemma
  apply double_corner_set_eq

variable {f : CornerSubring idem_e}
variable (idem_f : IsIdempotentElem f)

-- another auxiliary lemma for easier application
/-- Unital variant of `corner_ring_non_unital_eq`: the corner subring of `f` inside `eRe` is
isomorphic to the corner subring of `f.val` in `R`. -/
def corner_ring_unital_eq :
    CornerSubring idem_f ≃+* CornerSubring (e_idem_to_e_val_idem idem_f) := by
  unfold CornerSubring
  apply corner_ring_non_unital_eq

end LeanPool.ArtinWedderburn
