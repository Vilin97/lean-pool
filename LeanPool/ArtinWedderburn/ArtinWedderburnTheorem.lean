/-
Copyright (c) 2026 Matevz Miščič, Maša Žaucer, Job Petrovčič. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matevz Miščič, Maša Žaucer, Job Petrovčič
-/
module

public import LeanPool.ArtinWedderburn.PrimeRing
public import Mathlib.Data.Matrix.Mul
public import Mathlib.RingTheory.Artinian.Defs
import LeanPool.ArtinWedderburn.MatrixUnits
import LeanPool.ArtinWedderburn.NiceIdeals
import Mathlib.Data.Rat.Cast.Order
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

/-!
# The Artin–Wedderburn theorem

The classical Artin–Wedderburn theorem: a nontrivial prime artinian ring is
ring-isomorphic to a matrix ring over a division ring. Specialised to a simple
ring it yields the same conclusion.
-/

@[expose] public section

namespace LeanPool.ArtinWedderburn

variable {R : Type*} [Ring R]

universe u

theorem ArtinWedderburnForPrime {R : Type u} [Ring R] [h_nontriv : Nontrivial R]
    (h_prime : IsPrimeRing R) (h_artinian : IsArtinian R R) :
    ∃ (n : ℕ) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  have top_acc : Acc (fun x y => x < y) (⊤ : Ideal R) :=
    IsWellFounded.apply (fun x y ↦ x < y) ⊤
  have top_nice := accIdealNice h_prime h_artinian ⊤ top_acc
  have top_idem : IdemIdeal (⊤ : Ideal R) := by
    refine ⟨1, IsIdempotentElem.one, ?_⟩
    exact Eq.symm Ideal.span_singleton_one
  have R_ort_idem : OrtIdemDiv R := by
    specialize top_nice top_idem 1 IsIdempotentElem.one (Eq.symm Ideal.span_singleton_one)
    apply isomorphicOrtIdemDiv isoCornerOne
    exact top_nice
  have n_pos : 0 < R_ort_idem.n := nontrivial_ortidem_n_pos R h_nontriv R_ort_idem
  let ⟨mu, h⟩ := lemma_2_20' R h_prime R_ort_idem n_pos
  refine ⟨R_ort_idem.n, (CornerSubring (R_ort_idem.h ⟨0, n_pos⟩)),
    (IsDivisionRingToDivisionRing (R_ort_idem.div ⟨0, n_pos⟩)), ?_⟩
  apply Nonempty.intro
  have iso := ringWithMatrixUnitsIsomorphicToMatrixRing R R_ort_idem.n n_pos mu
  unfold e00Cornerring at iso
  unfold CornerSubring at iso ⊢
  apply iso.trans
  apply equalElIsoMatrixRings
  · unfold IsIdempotentElem
    exact mu.mul_ij_kl_eq_kron_delta_jk_mul_es_il ⟨0, n_pos⟩ ⟨0, n_pos⟩ ⟨0, n_pos⟩ ⟨0, n_pos⟩
  · exact R_ort_idem.h ⟨0, n_pos⟩
  · exact h

-- Just an application
theorem ArtinWedderburnForSimple {R : Type u} [Ring R] [IsSimpleRing R] [h_art : IsArtinian R R] :
    ∃ (n : ℕ) (D : Type u) (_ : DivisionRing D),
      Nonempty (R ≃+* Matrix (Fin n) (Fin n) D) := by
  apply ArtinWedderburnForPrime
  · exact simple_ring_is_prime
  · exact h_art

end LeanPool.ArtinWedderburn
