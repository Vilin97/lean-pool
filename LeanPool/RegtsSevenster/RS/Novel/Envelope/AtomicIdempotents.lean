/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.MathlibDeps

/-!
# Atomic idempotents in semisimple complex algebras

Every finite-dimensional semisimple ℂ-algebra has a complete
orthogonal family of idempotents whose corners are the scalar
lines they span: pull back the diagonal matrix units through
Wedderburn–Artin.  These are the atoms along which Karoubi
objects split into simples.
-/

namespace RS

universe u

variable {A : Type u}

/-- An idempotent is *atomic* if it is nonzero and its corner is
the scalar line it spans. -/
structure IsAtomicIdempotent
    [Ring A] [Algebra ℂ A]
    (e : A) : Prop where
  idem : IsIdempotentElem e
  ne_zero : e ≠ 0
  corner_scalar : ∀ x : A, ∃ c : ℂ, e * x * e = c • e

section PiMatrix

/-- The diagonal matrix-unit family in a product of matrix
algebras. -/
private noncomputable def matUnit {n : ℕ} {d : Fin n → ℕ}
    (p : (i : Fin n) × Fin (d i)) :
    Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ :=
  Pi.single p.1 (Matrix.single p.2 p.2 1)

private theorem matUnit_mul_matUnit {n : ℕ} {d : Fin n → ℕ}
    (p q : (i : Fin n) × Fin (d i)) :
    matUnit p * matUnit q =
      if p = q then matUnit p else 0 := by
  classical
  funext k
  rw [Pi.mul_apply]
  rcases eq_or_ne p.1 q.1 with hij | hij
  · obtain ⟨pi, pr⟩ := p
    obtain ⟨qi, qr⟩ := q
    dsimp at hij
    subst hij
    rcases eq_or_ne pr qr with rfl | hr
    · rw [if_pos rfl]
      unfold matUnit
      rcases eq_or_ne k pi with rfl | hk
      · simp
      · simp [Pi.single_eq_of_ne hk]
    · rw [if_neg (by
        intro h
        exact hr (by
          have := Sigma.mk.inj_iff.mp h
          exact eq_of_heq this.2))]
      unfold matUnit
      rcases eq_or_ne k pi with rfl | hk
      · simp [hr]
      · simp [Pi.single_eq_of_ne hk]
  · rw [if_neg (fun h => hij (congrArg Sigma.fst h))]
    unfold matUnit
    rcases eq_or_ne k p.1 with rfl | hk
    · rw [Pi.single_eq_same, Pi.single_eq_of_ne hij,
        Matrix.mul_zero]
      simp
    · rw [Pi.single_eq_of_ne hk, Matrix.zero_mul]
      simp

private theorem matUnit_sum {n : ℕ} {d : Fin n → ℕ} :
    ∑ p : (i : Fin n) × Fin (d i), matUnit p = 1 := by
  classical
  funext k
  rw [Finset.sum_apply, Pi.one_apply]
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  rw [show (∑ i : Fin n, ∑ r : Fin (d i),
      matUnit ⟨i, r⟩ k) =
    ∑ i : Fin n, ∑ r : Fin (d i),
      Pi.single (M := fun j =>
        Matrix (Fin (d j)) (Fin (d j)) ℂ) i
        (Matrix.single r r 1) k from rfl]
  rw [Finset.sum_eq_single k
    (fun i _ hi => by
      rw [Finset.sum_eq_zero]
      intro r _
      rw [Pi.single_eq_of_ne (Ne.symm hi)])
    (fun h => absurd (Finset.mem_univ k) h)]
  rw [show (∑ r : Fin (d k),
      Pi.single (M := fun j =>
        Matrix (Fin (d j)) (Fin (d j)) ℂ) k
        (Matrix.single r r 1) k) =
    ∑ r : Fin (d k), Matrix.single r r (1 : ℂ) from by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Pi.single_eq_same]]
  ext r s
  rw [Matrix.sum_apply]
  rcases eq_or_ne r s with rfl | hrs
  · rw [Matrix.one_apply_eq]
    rw [Finset.sum_eq_single r
      (fun b _ hb => by
        simp only [Matrix.single, Matrix.of_apply]
        rw [if_neg (by simp [hb])])
      (fun h => absurd (Finset.mem_univ r) h)]
    simp [Matrix.single]
  · rw [Matrix.one_apply_ne hrs]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp only [Matrix.single, Matrix.of_apply]
    rw [if_neg (by
      rintro ⟨hbr, hbs⟩
      exact hrs (hbr ▸ hbs))]

private theorem matUnit_corner {n : ℕ} {d : Fin n → ℕ}
    (p : (i : Fin n) × Fin (d i))
    (x : Π i, Matrix (Fin (d i)) (Fin (d i)) ℂ) :
    matUnit p * x * matUnit p =
      (x p.1 p.2 p.2) • matUnit p := by
  classical
  funext k
  rw [Pi.mul_apply, Pi.mul_apply, Pi.smul_apply]
  unfold matUnit
  rcases eq_or_ne k p.1 with rfl | hk
  · rw [show (Pi.single (M := fun j =>
        Matrix (Fin (d j)) (Fin (d j)) ℂ) p.1
        (Matrix.single p.2 p.2 1) p.1) =
      Matrix.single p.2 p.2 1 from Pi.single_eq_same _ _]
    rw [Matrix.single_mul_mul_single, Matrix.smul_single]
    congr 1
    rw [smul_eq_mul]
    ring
  · simp [Pi.single_eq_of_ne hk]

private theorem matUnit_ne_zero {n : ℕ} {d : Fin n → ℕ}
    [∀ i, NeZero (d i)]
    (p : (i : Fin n) × Fin (d i)) : matUnit p ≠ 0 := by
  intro h
  have h2 := congrFun h p.1
  simp only [matUnit, Pi.single_eq_same, Pi.zero_apply] at h2
  have h3 := congrFun (congrFun h2 p.2) p.2
  simp [Matrix.single] at h3

end PiMatrix

/-- **Atomic decomposition** of a finite-dimensional semisimple
complex algebra: the identity splits into a complete orthogonal
family of atomic idempotents. -/
theorem exists_completeOrthogonal_atomic [Ring A] [Algebra ℂ A]
    [FiniteDimensional ℂ A] [IsSemisimpleRing A] :
    ∃ (ι : Type) (_ : Fintype ι) (e : ι → A),
      CompleteOrthogonalIdempotents e ∧
        ∀ i, IsAtomicIdempotent (e i) := by
  classical
  obtain ⟨n, d, hd, ⟨Φ⟩⟩ :=
    IsSemisimpleRing.exists_algEquiv_pi_matrix_of_isAlgClosed
      (F := ℂ) (R := A)
  refine ⟨(i : Fin n) × Fin (d i), inferInstance,
    fun p => Φ.symm (matUnit p), ⟨⟨fun p => ?_, ?_⟩, ?_⟩, ?_⟩
  · show IsIdempotentElem _
    rw [IsIdempotentElem, ← map_mul, matUnit_mul_matUnit,
      if_pos rfl]
  · intro p q hpq
    rw [← map_mul, matUnit_mul_matUnit, if_neg hpq, map_zero]
  · rw [← map_sum, matUnit_sum, map_one]
  · intro p
    refine ⟨?_, ?_, ?_⟩
    · show IsIdempotentElem _
      rw [IsIdempotentElem, ← map_mul, matUnit_mul_matUnit,
        if_pos rfl]
    · intro h
      exact matUnit_ne_zero p (by
        have := congrArg Φ h
        rw [AlgEquiv.apply_symm_apply, map_zero] at this
        exact this)
    · intro x
      refine ⟨(Φ x) p.1 p.2 p.2, ?_⟩
      rw [show Φ.symm (matUnit p) * x * Φ.symm (matUnit p) =
        Φ.symm (matUnit p * Φ x * matUnit p) from by
          rw [map_mul, map_mul, AlgEquiv.symm_apply_apply]]
      rw [matUnit_corner, map_smul]

end RS
