/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PackageAssembly

/-!
# Branching from the restriction pairing

If the mixed character pairing of `lam` against the restriction of
`mu` does not vanish, the branching sandwich is nonzero: apply the
block representation of `mu`, use that its projector acts as the
identity, and compute the trace of the cast idempotent as the
pairing.
-/

namespace RS

open Finset

open scoped Classical in
/-- The mixed restriction pairing. -/
noncomputable def restrPairing (lam mu : YoungDiagram)
    (h : lam.card ≤ mu.card) : ℂ :=
  ∑ σ : Equiv.Perm (Fin lam.card),
    jtChar lam σ *
      jtChar mu (Equiv.Perm.viaEmbeddingHom
        (Fin.castLEEmb h) σ)

open scoped Classical in
/-- The trace of the block representation on the cast idempotent
is the normalized restriction pairing. -/
theorem trace_symCast_charIdempotent (lam mu : YoungDiagram)
    (h : lam.card ≤ mu.card) :
    LinearMap.trace ℂ (subCarrier (jtSimple mu))
      ((rhoS (jtSimple mu)).asAlgebraHom
        (symCast h
          (charIdempotent (nDim (jtSimple lam)) (jtChar lam)))) =
    ((nDim (jtSimple lam) : ℂ) / (lam.card.factorial : ℂ)) *
      restrPairing lam mu h := by
  classical
  set L : MonoidAlgebra ℂ (Equiv.Perm (Fin lam.card)) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ (subCarrier (jtSimple mu))).comp
      ((((rhoS (jtSimple mu)).asAlgebraHom :
          MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₐ[ℂ]
            Module.End ℂ (subCarrier (jtSimple mu))).toLinearMap
        ).comp
        ((symCast h :
          SymGroupAlgebra lam.card →ₐ[ℂ]
            SymGroupAlgebra mu.card).toLinearMap)) with hLdef
  have hsingle : ∀ σ : Equiv.Perm (Fin lam.card),
      L (MonoidAlgebra.of ℂ (Equiv.Perm (Fin lam.card)) σ) =
      jtChar mu (Equiv.Perm.viaEmbeddingHom
        (Fin.castLEEmb h) σ) := by
    intro σ
    rw [hLdef]
    rw [LinearMap.comp_apply, LinearMap.comp_apply]
    rw [show ((symCast h :
        SymGroupAlgebra lam.card →ₐ[ℂ]
          SymGroupAlgebra mu.card).toLinearMap)
        (MonoidAlgebra.of ℂ (Equiv.Perm (Fin lam.card)) σ) =
      MonoidAlgebra.of ℂ (Equiv.Perm (Fin mu.card))
        (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) from by
      show symCast h (MonoidAlgebra.of ℂ _ σ) = _
      rw [symCast, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply]
      show MonoidAlgebra.mapDomain
        (⇑(Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h)))
        (MonoidAlgebra.single σ (1 : ℂ)) = _
      rw [MonoidAlgebra.mapDomain_single]]
    rw [show (((rhoS (jtSimple mu)).asAlgebraHom :
        MonoidAlgebra ℂ (Equiv.Perm (Fin mu.card)) →ₐ[ℂ]
          Module.End ℂ (subCarrier (jtSimple mu))).toLinearMap)
        (MonoidAlgebra.of ℂ (Equiv.Perm (Fin mu.card))
          (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ)) =
      rhoS (jtSimple mu)
        (Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb h) σ) from by
      show (rhoS (jtSimple mu)).asAlgebraHom
        (MonoidAlgebra.of ℂ _ _) = _
      rw [MonoidAlgebra.of_apply,
        Representation.asAlgebraHom_single, one_smul]]
    rw [jtSimple_char mu]
    rfl
  have hL : LinearMap.trace ℂ (subCarrier (jtSimple mu))
      ((rhoS (jtSimple mu)).asAlgebraHom
        (symCast h
          (charIdempotent (nDim (jtSimple lam))
            (jtChar lam)))) =
      L (charIdempotent (nDim (jtSimple lam)) (jtChar lam)) := by
    rw [hLdef]
    rfl
  rw [hL, charIdempotent, map_smul, map_sum]
  rw [Finset.sum_congr rfl
    (fun (σ : Equiv.Perm (Fin lam.card))
      (_ : σ ∈ Finset.univ) => map_smul L (jtChar lam σ) _)]
  rw [Finset.sum_congr rfl
    (fun (σ : Equiv.Perm (Fin lam.card))
      (_ : σ ∈ Finset.univ) => by rw [hsingle σ])]
  rw [restrPairing, smul_eq_mul, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [smul_eq_mul]

open scoped Classical in
/-- **Branching from a nonvanishing pairing.** -/
theorem branching_of_pairing (lam mu : YoungDiagram)
    (h : lam.card ≤ mu.card)
    (HB : restrPairing lam mu h ≠ 0) :
    charIdempotent (nDim (jtSimple mu)) (jtChar mu) *
      symCast h
        (charIdempotent (nDim (jtSimple lam)) (jtChar lam)) *
      charIdempotent (nDim (jtSimple mu)) (jtChar mu) ≠ 0 := by
  classical
  intro hzero
  set y := symCast h
    (charIdempotent (nDim (jtSimple lam)) (jtChar lam)) with hy
  have hproj := charIdempotent_jtSimple mu
  have hψ : (rhoS (jtSimple mu)).asAlgebraHom
      (charIdempotent (nDim (jtSimple mu)) (jtChar mu) * y *
        charIdempotent (nDim (jtSimple mu)) (jtChar mu)) = 0 := by
    rw [hzero, map_zero]
  rw [map_mul, map_mul, hproj,
    nPsi_projector_eq_one (jtSimple mu) (jtSimple_simple mu),
    one_mul, mul_one] at hψ
  have htr := trace_symCast_charIdempotent lam mu h
  rw [← hy, hψ, map_zero] at htr
  have hd : ((nDim (jtSimple lam) : ℂ)) ≠ 0 := by
    haveI := jtSimple_simple lam
    haveI := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (Equiv.Perm (Fin lam.card)))
      (jtSimple lam)
    haveI : Nontrivial (subCarrier (jtSimple lam)) :=
      inferInstanceAs (Nontrivial (jtSimple lam))
    have := Module.finrank_pos
      (R := ℂ) (M := subCarrier (jtSimple lam))
    exact_mod_cast Nat.cast_ne_zero.mpr this.ne'
  have hf : ((lam.card.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero lam.card
  have hcoef : ((nDim (jtSimple lam) : ℂ) /
      (lam.card.factorial : ℂ)) ≠ 0 := div_ne_zero hd hf
  apply HB
  rcases mul_eq_zero.mp htr.symm with h1 | h1
  · exact absurd h1 hcoef
  · exact h1

end RS
