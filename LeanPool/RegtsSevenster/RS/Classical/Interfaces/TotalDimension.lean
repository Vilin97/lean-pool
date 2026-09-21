/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Common.ExponentialGrowth
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.WordCommutant
import LeanPool.RegtsSevenster.RS.Classical.Super.ColourTotal
import LeanPool.RegtsSevenster.RS.Classical.Interfaces.OmegaTensorPower
import LeanPool.RegtsSevenster.RS.Novel.Envelope.Frobenius
import LeanPool.RegtsSevenster.RS.Novel.Envelope.RankDimension

/-!
# The total dimension bound for the standard model

The fibre action on colour words factors through the skein
endomorphism algebra, whose dimension is at most `R ^ (2 * n)`.
The monomial word action has polynomial commutant dimension. Native
block faithfulness therefore bounds `(k + 2 * ℓ) ^ n` by `R ^ n`
times a fixed polynomial, forcing `k + 2 * ℓ ≤ R`.
-/

namespace RS

open CategoryTheory Representation

noncomputable section

private def stdOmegaIso {R k ℓ : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P) (n : ℕ) :
    superPow (stdSuperPair k ℓ) n ≅ P.ω.obj (SkeinObj.mk n) where
  hom := stdToOmega f P e.hom n
  inv := stdFromOmega f P e.inv n
  hom_inv_id := stdToOmega_stdFromOmega f P e.hom e.inv
    e.hom_inv_id n
  inv_hom_id := stdFromOmega_stdToOmega f P e.hom e.inv
    e.inv_hom_id n

private theorem stdOmegaIso_perm {R k ℓ : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P) (n : ℕ)
    (σ : Equiv.Perm (Fin n)) :
    letI := P.braided
    (stdOmegaIso f P e n).hom ≫
      P.ω.map (permClass f n σ) ≫ (stdOmegaIso f P e n).inv =
      modelPermMap σ := by
  letI := P.braided
  change stdToOmega f P e.hom n ≫ P.ω.map (permClass f n σ) ≫
    stdFromOmega f P e.inv n = _
  rw [permClass_eq_bundleMapClass, ← Category.assoc,
    stdToOmega_bmc_perm_all, Category.assoc,
    stdToOmega_stdFromOmega f P e.hom e.inv e.hom_inv_id n,
    Category.comp_id]

/-- At every tensor power the standard model's squared dimension
is bounded by connection rank times a fixed polynomial. -/
theorem stdModel_pow_le_connectionRank {R k ℓ : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P) (n : ℕ) :
    (k + 2 * ℓ) ^ (2 * n) ≤ connectionRank f.val (2 * n) *
      (n + 1) ^ (2 * (k + 2 * ℓ) ^ 2) := by
  classical
  letI := P.additive
  letI := P.linear
  letI := P.braided
  let C := MixedColouring k ℓ n → ℂ
  let c : Tot (P.ω.obj (SkeinObj.mk n)) ≃ₗ[ℂ] C :=
    (totIso (stdOmegaIso f P e n)).symm.trans (colourTotalEquiv k ℓ n)
  let ψ : SymGroupAlgebra n →ₐ[ℂ] Module.End ℂ C :=
    (c.conjAlgEquiv ℂ).toAlgHom.comp
      ((totAlgHom (P.ω.obj (SkeinObj.mk n))).comp (omegaSkeinRep f P n))
  let ρ : Representation ℂ (Equiv.Perm (Fin n)) C :=
    ψ.toMonoidHom.comp (MonoidAlgebra.of ℂ _)
  have hρ : ρ.asAlgebraHom = ψ := by
    apply MonoidAlgebra.algHom_ext
    intro σ
    rw [Representation.asAlgebraHom_single, one_smul]
    rfl
  have hker : ∀ x, skeinRep f n x = 0 → ρ.asAlgebraHom x = 0 := by
    intro x hx
    rw [hρ]
    change (c.conjAlgEquiv ℂ)
      (totAlgHom (P.ω.obj (SkeinObj.mk n)) (omegaSkeinRep f P n x)) = 0
    have hz : omegaSkeinRep f P n x = 0 := by
      rw [omegaSkeinRep_eq, hx]
      exact P.ω.map_zero _ _
    rw [hz, map_zero, map_zero]
  have haction (σ : Equiv.Perm (Fin n)) (v : C) :
      ρ σ v = colourTotalEquiv k ℓ n
        (tot (modelPermMap σ) ((colourTotalEquiv k ℓ n).symm v)) := by
    change c (tot (omegaSkeinRep f P n
      (MonoidAlgebra.of ℂ _ σ)) (c.symm v)) = _
    rw [omegaSkeinRep_of]
    change colourTotalEquiv k ℓ n
      (tot (stdOmegaIso f P e n).inv
        (tot (P.ω.map (permClass f n σ))
          (tot (stdOmegaIso f P e n).hom
            ((colourTotalEquiv k ℓ n).symm v)))) = _
    rw [← LinearMap.comp_apply, ← tot_comp,
      ← LinearMap.comp_apply, ← tot_comp, stdOmegaIso_perm]
  let M : MonomialWordAction ρ := {
    weight := fun σ c => (-1 : ℂ) ^ oddInversions σ c
    weight_ne_zero := fun _ _ => pow_ne_zero _ (by norm_num)
    apply_eq := fun σ v c => by
      rw [haction]
      exact colourTotalEquiv_modelPermMap σ v c
  }
  have hdim := finrank_sq_le_mul_commutant_sq ρ (skeinRep f n) hker
  have hcomm := finrank_commutant_le_word_counts M
  have h := hdim.trans (Nat.mul_le_mul_left _
    (Nat.pow_le_pow_left hcomm 2))
  rw [connectionRank_eq_skeinEnd_finrank]
  simpa [C, MixedColouring, Module.finrank_pi, Fintype.card_fun,
    ← pow_mul, Nat.mul_comm] using h

/-- The standard model's total dimension is bounded by every
edge-rank base for the same parameter. -/
theorem stdModel_total_dimension_le_of_rank_bound {R k ℓ B : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P)
    (hB : EdgeRankBounded f.val B) : k + 2 * ℓ ≤ B := by
  have h := le_of_pow_le_pow_mul_polynomial
    ((k + 2 * ℓ) ^ 2) (B ^ 2) (2 * (k + 2 * ℓ) ^ 2) (fun n => by
      have hdim := (stdModel_pow_le_connectionRank f P e n).trans
        (Nat.mul_le_mul_right _ (connectionRank_le_pow hB (2 * n)))
      simpa only [← pow_mul] using hdim)
  nlinarith

/-- The standard model supplied by any Deligne package has total
dimension at most the original edge-rank base. -/
theorem stdModel_total_dimension_le {R k ℓ : ℕ}
    (f : EdgeRankParameter R) (P : DelignePackage (SkeinObj f))
    (e : stdSuperPair k ℓ ≅ strandImage f P) : k + 2 * ℓ ≤ R :=
  stdModel_total_dimension_le_of_rank_bound f P e f.rank_bounded

end

end RS
