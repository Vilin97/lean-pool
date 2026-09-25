/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Extraction.StdDuality

/-!
# Self-duality of the standard super space

The copairing `C = Σ e_i ⊗ e_i + Σ f_i ⊗ g_i` as a morphism
`𝟙 ⟶ stdSuperPair ⊗ stdSuperPair`, and the snake identities pairing it
against the standard form: `stdSuperPair` is exactly self-dual in
SuperVect.  This is the categorical form of the §5.2 conventions —
the contraction identities `L_C = id` distributed over the graded
blocks.
-/

@[expose] public section

namespace RS

open CategoryTheory
open scoped TensorProduct

/-- The even copairing element `Σ e_i ⊗ e_i`. -/
noncomputable def stdCopairEvenElem (k : ℕ) :
    (Fin k → ℂ) ⊗[ℂ] (Fin k → ℂ) :=
  ∑ i, stdE k i ⊗ₜ[ℂ] stdE k i

/-- The odd copairing element `Σ f_i ⊗ g_i`. -/
noncomputable def stdCopairOddElem (ℓ : ℕ) :
    (Fin (2 * ℓ) → ℂ) ⊗[ℂ] (Fin (2 * ℓ) → ℂ) :=
  ∑ i, stdF ℓ i ⊗ₜ[ℂ] stdG ℓ i

private lemma mk_smul_left {A B : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [Module ℂ A] [Module ℂ B] (c : ℂ) (a : A) :
    ((c • a, (0 : B)) : A × B) = c • ((a, 0) : A × B) := by
  rw [Prod.smul_mk, smul_zero]

private lemma mk_smul_right {A B : Type*} [AddCommMonoid A]
    [AddCommMonoid B] [Module ℂ A] [Module ℂ B] (c : ℂ) (b : B) :
    (((0 : A), c • b) : A × B) = c • (((0 : A), b) : A × B) := by
  rw [Prod.smul_mk, smul_zero]

/-- `map_zero` for a bound linear equivalence. -/
private lemma equiv_zero {M N : Type*} [AddCommMonoid M] [Module ℂ M]
    [AddCommMonoid N] [Module ℂ N] (e : M ≃ₗ[ℂ] N) : e 0 = 0 :=
  map_zero e

/-- The standard copairing as an even morphism
`𝟙 ⟶ stdSuperPair ⊗ stdSuperPair`. -/
noncomputable def stdCopair (k ℓ : ℕ) :
    SuperVect.Hom SuperVect.tensorUnit
      (SuperVect.tensorObj (stdSuperPair k ℓ) (stdSuperPair k ℓ)) := by
  refine ⟨?_, ?_⟩
  · change ℂ →ₗ[ℂ]
      ((Fin k → ℂ) ⊗[ℂ] (Fin k → ℂ)) ×
        ((Fin (2 * ℓ) → ℂ) ⊗[ℂ] (Fin (2 * ℓ) → ℂ))
    exact LinearMap.toSpanSingleton ℂ _
      (stdCopairEvenElem k, stdCopairOddElem ℓ)
  · change PUnit →ₗ[ℂ]
      ((Fin k → ℂ) ⊗[ℂ] (Fin (2 * ℓ) → ℂ)) ×
        ((Fin (2 * ℓ) → ℂ) ⊗[ℂ] (Fin k → ℂ))
    exact 0

-- The snake identities unfold the associator, both unitors and the
-- graded copairing on every block, so the elaborated term is large.
open MonoidalCategory in
/-- The first snake identity for the standard pairing. -/
private theorem std_coev_ev (k ℓ : ℕ) :
    stdSuperPair k ℓ ◁ (show 𝟙_ SuperVect ⟶ stdSuperPair k ℓ ⊗ stdSuperPair k ℓ
      from stdCopair k ℓ) ≫
      (α_ (stdSuperPair k ℓ) (stdSuperPair k ℓ) (stdSuperPair k ℓ)).inv ≫
      (show stdSuperPair k ℓ ⊗ stdSuperPair k ℓ ⟶ 𝟙_ SuperVect from
        stdForm k ℓ) ▷
        stdSuperPair k ℓ =
    (ρ_ (stdSuperPair k ℓ)).hom ≫ (λ_ (stdSuperPair k ℓ)).inv := by
  apply SuperVect.Hom.ext
  · change
      (LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
            (TensorProduct.lift (stdFormOddBilin ℓ)))
          LinearMap.id)
        (TensorProduct.map (0 : _ →ₗ[ℂ] PUnit) LinearMap.id) ∘ₗ
        (SuperVect.assocAux (Fin k → ℂ) (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ)).symm.toLinearMap) ∘ₗ
      LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (LinearMap.toSpanSingleton ℂ _
            (stdCopairEvenElem k, stdCopairOddElem ℓ)))
        (TensorProduct.map LinearMap.id (0 : PUnit →ₗ[ℂ] _)) =
      (LinearMap.inl ℂ _ _ ∘ₗ
        (TensorProduct.lid ℂ (Fin k → ℂ)).symm.toLinearMap) ∘ₗ
      ((TensorProduct.rid ℂ (Fin k → ℂ)).toLinearMap ∘ₗ LinearMap.fst ℂ _ _)
    ext x
    all_goals simp? [-Prod.mk_add_mk, -Prod.smul_mk, stdCopairEvenElem,
      stdCopairOddElem,
      mk_sum_split, mk_sum_left, mk_add_left,
       mk_smul_left, mk_smul_right,
      equiv_zero, lmap_zero,
      TensorProduct.tmul_add, TensorProduct.tmul_sum,
       TensorProduct.sum_tmul,
      TensorProduct.tmul_smul,
      Prod.fst_sum, Prod.snd_sum, Prod.fst_add, Prod.snd_add,
      stdFormEvenBilin, stdFormOddBilin,
      stdFormEven, stdE, stdF, stdG]
    simp only [← TensorProduct.sum_tmul]
    have hcollapse : ∀ i : Fin k,
        (∑ a, (Pi.single x (1 : ℂ)) a * (Pi.single i (1 : ℂ)) a) =
          (if x = i then (1 : ℂ) else 0) :=
      fun i => stdFormEven_stdE k x i
    simp only [hcollapse, TensorProduct.ite_tmul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_eq_left]
  · change
      (LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
            (TensorProduct.lift (stdFormOddBilin ℓ)))
          LinearMap.id)
        (TensorProduct.map (0 : _ →ₗ[ℂ] PUnit) LinearMap.id) ∘ₗ
        (SuperVect.assocAux (Fin k → ℂ) (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ) (Fin (2 * ℓ) → ℂ)
          (Fin k → ℂ)).symm.toLinearMap) ∘ₗ
      LinearMap.prodMap
        (TensorProduct.map LinearMap.id (0 : PUnit →ₗ[ℂ] _))
        (TensorProduct.map LinearMap.id
          (LinearMap.toSpanSingleton ℂ _
            (stdCopairEvenElem k, stdCopairOddElem ℓ))) =
      (LinearMap.inl ℂ _ _ ∘ₗ
        (TensorProduct.lid ℂ (Fin (2 * ℓ) → ℂ)).symm.toLinearMap) ∘ₗ
      ((TensorProduct.rid ℂ (Fin (2 * ℓ) → ℂ)).toLinearMap ∘ₗ LinearMap.snd ℂ _
        _)
    ext x
    all_goals simp? [-Prod.mk_add_mk, -Prod.smul_mk, stdCopairEvenElem,
      stdCopairOddElem,
      mk_sum_split, mk_sum_left, mk_sum_right,
      mk_add_right, mk_smul_left, mk_smul_right,
      equiv_zero, lmap_zero,
      TensorProduct.tmul_add, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul,
      Prod.fst_sum, Prod.snd_sum, Prod.fst_add, Prod.snd_add,
      stdFormEvenBilin, stdFormOddBilin,
       stdFormOdd, stdE, stdF, stdG]
    have hinner : ∀ m : Fin (2 * ℓ),
        (-∑ n, (oddPartnerSign ℓ n : ℂ) *
            (Pi.single x (1 : ℂ) : Fin (2 * ℓ) → ℂ) n *
            (Pi.single m (1 : ℂ) : Fin (2 * ℓ) → ℂ) (oddPartner ℓ n)) =
          stdFormOdd ℓ (stdF ℓ x) (stdF ℓ m) := by
      intro m
      unfold stdFormOdd stdF
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    simp only [hinner, stdFormOdd_stdF]
    rw [Finset.sum_eq_single (oddPartner ℓ x)]
    · rw [ite_eq_left rfl, oddPartner_invol, oddPartnerSign_oddPartner,
        TensorProduct.smul_tmul', smul_eq_mul]
      push_cast
      rw [show (-(oddPartnerSign ℓ x : ℂ)) * -(oddPartnerSign ℓ x : ℂ) =
          ((oddPartnerSign ℓ x * oddPartnerSign ℓ x : ℤ) : ℂ) from by
        push_cast; ring, oddPartnerSign_mul_self, Int.cast_one]
    · intro m _ hm
      rw [ite_eq_right (fun hh : m = oddPartner ℓ x => hm hh),
        TensorProduct.zero_tmul, smul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

-- As for the first identity: the whole graded associator and both
-- unitors are unfolded on each block.
open MonoidalCategory in
/-- The second snake identity for the standard pairing. -/
private theorem std_ev_coev (k ℓ : ℕ) :
    (show 𝟙_ SuperVect ⟶ stdSuperPair k ℓ ⊗ stdSuperPair k ℓ from
      stdCopair k ℓ) ▷
      stdSuperPair k ℓ ≫
      (α_ (stdSuperPair k ℓ) (stdSuperPair k ℓ) (stdSuperPair k ℓ)).hom ≫
      stdSuperPair k ℓ ◁
        (show stdSuperPair k ℓ ⊗ stdSuperPair k ℓ ⟶ 𝟙_ SuperVect
        from stdForm k ℓ) =
    (λ_ (stdSuperPair k ℓ)).hom ≫ (ρ_ (stdSuperPair k ℓ)).inv := by
  apply SuperVect.Hom.ext
  · change
      (LinearMap.prodMap
        (TensorProduct.map LinearMap.id
          (LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
            (TensorProduct.lift (stdFormOddBilin ℓ))))
        (TensorProduct.map LinearMap.id (0 : _ →ₗ[ℂ] PUnit)) ∘ₗ
        (SuperVect.assocAux (Fin k → ℂ) (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ)).toLinearMap) ∘ₗ
      LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.toSpanSingleton ℂ _
            (stdCopairEvenElem k, stdCopairOddElem ℓ))
          LinearMap.id)
        (TensorProduct.map (0 : PUnit →ₗ[ℂ] _) LinearMap.id) =
      (LinearMap.inl ℂ _ _ ∘ₗ
        (TensorProduct.rid ℂ (Fin k → ℂ)).symm.toLinearMap) ∘ₗ
      ((TensorProduct.lid ℂ (Fin k → ℂ)).toLinearMap ∘ₗ LinearMap.fst ℂ _ _)
    ext x
    all_goals simp? [-Prod.mk_add_mk, -Prod.smul_mk, stdCopairEvenElem,
      stdCopairOddElem,
      mk_sum_split, mk_sum_left, mk_add_left,
       mk_smul_left, mk_smul_right,
      equiv_zero, lmap_zero,
       TensorProduct.tmul_sum,
      TensorProduct.add_tmul, TensorProduct.sum_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul,
      Prod.fst_sum, Prod.snd_sum, Prod.fst_add, Prod.snd_add,
      stdFormEvenBilin, stdFormOddBilin,
      stdFormEven, stdE, stdF, stdG]
    simp only [← TensorProduct.tmul_sum]
    have hcollapse : ∀ i : Fin k,
        (∑ a, (Pi.single i (1 : ℂ)) a * (Pi.single x (1 : ℂ)) a) =
          (if i = x then (1 : ℂ) else 0) :=
      fun i => stdFormEven_stdE k i x
    simp only [hcollapse, TensorProduct.tmul_ite, Finset.sum_ite_eq',
      Finset.mem_univ, ite_eq_left]
  · change
      (LinearMap.prodMap
        (TensorProduct.map LinearMap.id (0 : _ →ₗ[ℂ] PUnit))
        (TensorProduct.map LinearMap.id
          (LinearMap.coprod (TensorProduct.lift (stdFormEvenBilin k))
            (TensorProduct.lift (stdFormOddBilin ℓ)))) ∘ₗ
        (SuperVect.assocAux (Fin k → ℂ) (Fin (2 * ℓ) → ℂ) (Fin k → ℂ)
          (Fin (2 * ℓ) → ℂ) (Fin (2 * ℓ) → ℂ)
          (Fin k → ℂ)).toLinearMap) ∘ₗ
      LinearMap.prodMap
        (TensorProduct.map
          (LinearMap.toSpanSingleton ℂ _
            (stdCopairEvenElem k, stdCopairOddElem ℓ))
          LinearMap.id)
        (TensorProduct.map (0 : PUnit →ₗ[ℂ] _) LinearMap.id) =
      (LinearMap.inr ℂ _ _ ∘ₗ
        (TensorProduct.rid ℂ (Fin (2 * ℓ) → ℂ)).symm.toLinearMap) ∘ₗ
      ((TensorProduct.lid ℂ (Fin (2 * ℓ) → ℂ)).toLinearMap ∘ₗ LinearMap.fst ℂ _
        _)
    ext x
    all_goals simp? [-Prod.mk_add_mk, -Prod.smul_mk, stdCopairEvenElem,
      stdCopairOddElem,
      mk_sum_split, mk_sum_left, mk_sum_right, mk_add_left,
       mk_smul_left, mk_smul_right,
      equiv_zero, lmap_zero,
      TensorProduct.add_tmul, TensorProduct.sum_tmul,
      TensorProduct.tmul_smul, TensorProduct.smul_tmul,
      Prod.fst_sum, Prod.snd_sum, Prod.fst_add, Prod.snd_add,
      stdFormEvenBilin, stdFormOddBilin,
       stdFormOdd, stdE, stdF, stdG]
    have hinner : ∀ m : Fin (2 * ℓ),
        (-∑ n, (oddPartnerSign ℓ n : ℂ) *
            (Pi.single (oddPartner ℓ m) (1 : ℂ) : Fin (2 * ℓ) → ℂ) n *
            (Pi.single x (1 : ℂ) : Fin (2 * ℓ) → ℂ) (oddPartner ℓ n)) =
          stdFormOdd ℓ (stdF ℓ (oddPartner ℓ m)) (stdF ℓ x) := by
      intro m
      unfold stdFormOdd stdF
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun n _ => by ring)
    simp only [hinner, stdFormOdd_stdF, oddPartner_invol,
      oddPartnerSign_oddPartner, Int.cast_neg, neg_neg]
    rw [Finset.sum_eq_single x]
    · rw [ite_eq_left rfl, ← TensorProduct.tmul_smul, smul_eq_mul,
        show (oddPartnerSign ℓ x : ℂ) * (oddPartnerSign ℓ x : ℂ) =
          ((oddPartnerSign ℓ x * oddPartnerSign ℓ x : ℤ) : ℂ) from by
          push_cast; ring,
        oddPartnerSign_mul_self, Int.cast_one]
    · intro m _ hm
      rw [ite_eq_right (fun hh : x = m => hm hh.symm),
        TensorProduct.tmul_zero, smul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem

/-- **Self-duality of the standard super space**: the standard form
and copairing are an exact pairing. -/
noncomputable instance stdExactPairing (k ℓ : ℕ) :
    ExactPairing (stdSuperPair k ℓ) (stdSuperPair k ℓ) where
  coevaluation' := stdCopair k ℓ
  evaluation' := stdForm k ℓ
  coevaluation_evaluation' := std_coev_ev k ℓ
  evaluation_coevaluation' := std_ev_coev k ℓ

end RS
