/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvGenerator
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.Growth

/-!
# Moderate growth of the envelope

The Deligne moderate-growth hypothesis: the endomorphism algebras
of tensor powers grow at most exponentially.  The dimension of an
envelope Hom-space is bounded by the underlying matrix Hom-space,
which is a finite product of skein Hom-spaces of dimension at
most `(R+1)^(2m)`; tensor powers multiply index cardinalities and
add arities, so the total bound is exponential in the power.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.Limits MonoidalCategory

universe v u

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### The envelope Hom bound -/

/-- Envelope Hom-spaces are no larger than the underlying matrix
Hom-spaces. -/
theorem env_hom_finrank_le (P Q : Env f) :
    Module.finrank ℂ (P ⟶ Q) ≤ Module.finrank ℂ (P.X ⟶ Q.X) :=
  LinearMap.finrank_le_finrank_of_injective
    (f := ⟨⟨fun (x : P ⟶ Q) => x.f, fun _ _ => rfl⟩,
      fun _ _ => rfl⟩)
    (fun _ _ h => Karoubi.Hom.ext h)

/-! ### The matrix Hom bound -/

/-- The entrywise reading of a matrix morphism into skein
Hom-spaces. -/
noncomputable def matHomEntries
    (M N : Mat_ (Karoubi (SkeinObj f))) :
    (M ⟶ N) →ₗ[ℂ] ((p : M.ι × N.ι) →
      HomSpace f.val
        ((M.X p.1).X.arity + (N.X p.2).X.arity)) where
  toFun φ := fun p => (φ p.1 p.2).f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A matrix of morphisms is determined by its entries, so the
hom-space dimension is bounded by their total. -/
theorem matHomEntries_injective
    (M N : Mat_ (Karoubi (SkeinObj f))) :
    Function.Injective (matHomEntries f M N) := by
  intro φ ψ h
  apply Mat_.hom_ext
  intro i j
  apply Karoubi.hom_ext
  exact congrFun h (i, j)

/-- The dimension of a matrix Hom-space, bounded by index counts
and a uniform arity bound. -/
theorem mat_hom_finrank_le (M N : Mat_ (Karoubi (SkeinObj f)))
    (m : ℕ) (hM : ∀ i, (M.X i).X.arity ≤ m)
    (hN : ∀ j, (N.X j).X.arity ≤ m) :
    Module.finrank ℂ (M ⟶ N) ≤
      Fintype.card M.ι * Fintype.card N.ι * (R + 1) ^ (2 * m) := by
  have : ∀ p : M.ι × N.ι, Module.Finite ℂ
      (HomSpace f.val
        ((M.X p.1).X.arity + (N.X p.2).X.arity)) :=
    fun p => inferInstance
  calc Module.finrank ℂ (M ⟶ N)
      ≤ Module.finrank ℂ ((p : M.ι × N.ι) →
          HomSpace f.val
            ((M.X p.1).X.arity + (N.X p.2).X.arity)) :=
        LinearMap.finrank_le_finrank_of_injective
          (f := matHomEntries f M N)
          (matHomEntries_injective f M N)
    _ = ∑ p : M.ι × N.ι, Module.finrank ℂ
          (HomSpace f.val
            ((M.X p.1).X.arity + (N.X p.2).X.arity)) :=
        Module.finrank_pi_fintype ℂ
    _ ≤ ∑ _p : M.ι × N.ι, (R + 1) ^ (2 * m) := by
        refine Finset.sum_le_sum fun p _ => ?_
        refine le_trans (homSpace_finrank_le f _) ?_
        refine le_trans
          (Nat.pow_le_pow_left (Nat.le_succ R) _) ?_
        refine Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le R)) ?_
        have h1 := hM p.1
        have h2 := hN p.2
        omega
    _ = Fintype.card M.ι * Fintype.card N.ι *
          (R + 1) ^ (2 * m) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul,
          Fintype.card_prod]

/-! ### Tensor powers of matrix objects -/

/-- The underlying matrix object of an envelope tensor power. -/
theorem env_pow_X (Y : Env f) : ∀ N : ℕ,
    (tensorPow (Env f) Y N).X =
      tensorPow (Mat_ (Karoubi (SkeinObj f))) Y.X N
  | 0 => rfl
  | N + 1 => congrArg (· ⊗ Y.X) (env_pow_X Y N)

/-- The index cardinality of a matrix tensor power. -/
theorem mat_pow_card (A : Mat_ (Karoubi (SkeinObj f))) :
    ∀ N : ℕ,
      Fintype.card
        ((tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).ι) =
        Fintype.card A.ι ^ N
  | 0 => by
      rw [pow_zero]
      exact (Fintype.card_congr
        (Equiv.refl PUnit)).trans Fintype.card_punit
  | N + 1 => by
      rw [pow_succ, ← mat_pow_card A N]
      exact (Fintype.card_congr (Equiv.refl _)).trans
        (Fintype.card_prod _ _)

/-- The arity bound of a matrix tensor power. -/
theorem mat_pow_arity (A : Mat_ (Karoubi (SkeinObj f))) (m : ℕ)
    (hA : ∀ i, ((A.X i).X).arity ≤ m) : ∀ N : ℕ,
    ∀ p : (tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).ι,
      (((tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).X p).X).arity
        ≤ N * m
  | 0, p => Nat.le_of_eq (by rw [Nat.zero_mul]; rfl)
  | N + 1, p => by
      change (((tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).X
          p.1).X).arity + ((A.X p.2).X).arity ≤ (N + 1) * m
      have h1 := mat_pow_arity A m hA N p.1
      have h2 := hA p.2
      nlinarith

/-! ### The moderate-growth field -/

/-- **Moderate growth of the envelope**: endomorphism algebras of
tensor powers grow at most exponentially. -/
theorem env_deligneModerateGrowth :
    ModerateEndGrowth (Env f) := by
  intro Y
  classical
  set A := Y.X with hA
  set mA : ℕ := Finset.univ.sup fun i => ((A.X i).X).arity
    with hmA
  refine ⟨1, Fintype.card A.ι ^ 2 * (R + 1) ^ (2 * mA),
    fun N => ?_⟩
  rw [one_mul]
  have harity : ∀ i, ((A.X i).X).arity ≤ mA := fun i => by
    rw [hmA]
    exact Finset.le_sup (f := fun i => ((A.X i).X).arity)
      (Finset.mem_univ i)
  calc Module.finrank ℂ
        (tensorPow (Env f) Y N ⟶ tensorPow (Env f) Y N)
      ≤ Module.finrank ℂ
          ((tensorPow (Env f) Y N).X ⟶
            (tensorPow (Env f) Y N).X) :=
        env_hom_finrank_le f _ _
    _ ≤ Fintype.card
          ((tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).ι) *
        Fintype.card
          ((tensorPow (Mat_ (Karoubi (SkeinObj f))) A N).ι) *
          (R + 1) ^ (2 * (N * mA)) := by
        rw [env_pow_X f Y N]
        exact mat_hom_finrank_le f _ _ (N * mA)
          (mat_pow_arity f A mA harity N)
          (mat_pow_arity f A mA harity N)
    _ = (Fintype.card A.ι ^ 2 * (R + 1) ^ (2 * mA)) ^ N := by
        rw [mat_pow_card f A N, mul_pow, ← pow_mul, ← pow_mul,
          ← pow_add]
        ring_nf

end RS
