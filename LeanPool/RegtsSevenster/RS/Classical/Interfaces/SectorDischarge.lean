/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Interfaces.SectorIntertwine
import LeanPool.RegtsSevenster.RS.Classical.SymFun.BinomialDet
import LeanPool.RegtsSevenster.RS.QuantSector

/-!
# Sector discharge: the last gap of the quantitative Regts–Sevenster theorem

Given `SquareBinomialDetPos` (the Lindström–Gessel–Viennot core: the
binomial Toeplitz determinant for `squareDiagram s` at `−m` is nonzero
whenever `1 ≤ s ≤ m`), we discharge `SquareSectorBound`: when the
super permutation action kills the square-block idempotent at every
side `s' ≥ s`, both sector dimensions `k` (even) and `2l` (odd) of the
standard model `stdSuperPair k l` lie strictly below `s`.

The proof transports the abstract `superPermAction` on
`superPow (strandImage f P) n` to the model action `modelPermMap` on
`superPow (stdSuperPair k l) n` via the iterated iso built from the
standard-model extraction `(e, e')`, then feeds the sector traces
`evenSectorTr` / `oddSectorTr` through `sector_bound_of_dead` /
`sector_bound_of_dead_signed`.

## Main result

* `squareSectorBound_of_detPos` — the last gap of the quantitative theorem.
-/

noncomputable section

namespace RS

open CategoryTheory MonoidalCategory Category MonoidAlgebra
open Functor.LaxMonoidal Functor.OplaxMonoidal



/-! ## Transport identification

The iterated standard-model transport `stdToOmega ≫ omegaPowInv`
conjugates `superPermAction` to `modelPermMap`.
-/

/-- The transport of the permutation action through the standard-model
iso equals the model permutation map.  The chain:

  `stdToOmega ≫ omegaPowInv ≫ superPermAction(σ) ≫ omegaPowHom ≫ stdFromOmega`
  = `stdToOmega ≫ ω.map(permClass σ) ≫ stdFromOmega`   [omegaPow cancellation]
  = `stdToOmega ≫ ω.map(bundleMapClass σ) ≫ stdFromOmega`
      [permClass = bundleMapClass]
  = `modelPermMap σ ≫ stdToOmega ≫ stdFromOmega`  [intertwining]
  = `modelPermMap σ`  [stdToOmega ≫ stdFromOmega = 𝟙] -/
private theorem transport_perm_eq {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (he'e : SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuperPair k l))
    (_hee' : SuperVect.Hom.comp e e' =
      SuperVect.Hom.id (strandImage f P))
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    letI := P.additive; letI := P.linear; letI := P.braided
    (stdToOmega f P e n ≫ omegaPowInv f P n) ≫
      (superPermAction f P n (MonoidAlgebra.of ℂ _ σ)) ≫
      (omegaPowHom f P n ≫ stdFromOmega f P e' n) =
    modelPermMap σ := by
  let := P.additive
  let := P.linear
  let := P.braided
  -- Step 1: unfold superPermAction to isoConj(omegaPow)(ω.map(permClass σ))
  rw [superPermAction_perm]
  -- Step 2: unfold isoConj and omegaPow projections
  simp only [isoConj_unfold,
    show (omegaPow f P n).hom = omegaPowHom f P n from rfl,
    show (omegaPow f P n).inv = omegaPowInv f P n from rfl]
  -- Step 3: fully right-associate
  simp only [assoc]
  -- Step 4: cancel first omegaPowInv ≫ omegaPowHom
  rw [← assoc (omegaPowInv f P n) (omegaPowHom f P n)]
  rw [show (omegaPowInv f P n ≫ omegaPowHom f P n :
      P.ω.obj (SkeinObj.mk n) ⟶ _) = 𝟙 _ from
    omegaPow_inv_hom f P n]
  rw [id_comp]
  -- Step 5: cancel second omegaPowInv ≫ omegaPowHom
  rw [← assoc (omegaPowInv f P n) (omegaPowHom f P n)]
  rw [show (omegaPowInv f P n ≫ omegaPowHom f P n :
      P.ω.obj (SkeinObj.mk n) ⟶ _) = 𝟙 _ from
    omegaPow_inv_hom f P n]
  rw [id_comp]
  -- Now LHS = stdToOmega ≫ ω.map(permClass σ) ≫ stdFromOmega
  -- Step 6: permClass = bundleMapClass
  rw [permClass_eq_bundleMapClass]
  -- Step 7: intertwining
  rw [← assoc (stdToOmega f P e n)]
  rw [stdToOmega_bmc_perm_all f P e n σ]
  -- Now LHS = modelPermMap σ ≫ stdToOmega ≫ stdFromOmega
  rw [assoc]
  -- Step 8: stdToOmega ≫ stdFromOmega = 𝟙
  rw [stdToOmega_stdFromOmega f P e e' he'e n]
  -- Step 9: comp_id
  exact comp_id _

/-! ## Even sector bound -/

/-- The conjugation of an even-part endomorphism through the
transport: sends `Module.End ℂ (strandImage power).even` to
`Module.End ℂ (stdSuperPair power).even`. -/
private def evenConjTransport {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (n : ℕ) :
    letI := P.braided
    Module.End ℂ (superPow (strandImage f P) n).even →ₗ[ℂ]
      Module.End ℂ (superPow (stdSuperPair k l) n).even := by
  letI := P.braided
  exact {
    toFun := fun T =>
      (omegaPowHom f P n ≫ stdFromOmega f P e' n :
        SuperVect.Hom _ _).evenMap.comp
        (T.comp (stdToOmega f P e n ≫ omegaPowInv f P n :
          SuperVect.Hom _ _).evenMap)
    map_add' := fun T₁ T₂ => by
      simp only [LinearMap.add_comp, LinearMap.comp_add]
    map_smul' := fun r T => by
      simp only [RingHom.id_apply, LinearMap.smul_comp,
        LinearMap.comp_smul]
  }

/-- The even sector trace transported to the abstract strand power:
composes conjugation-by-transport with `evenSectorTr`. -/
private def evenSectorTrTransport {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (n : ℕ) :
    letI := P.braided
    Module.End ℂ (superPow (strandImage f P) n).even →ₗ[ℂ] ℂ := by
  letI := P.braided
  exact (evenSectorTr k l n).comp (evenConjTransport f P e e' n)

/-- The odd sector trace transported to the abstract strand power
(for even `n`). -/
private def oddSectorTrTransport {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (n : ℕ) (hn : Even n) :
    letI := P.braided
    Module.End ℂ (superPow (strandImage f P) n).even →ₗ[ℂ] ℂ := by
  letI := P.braided
  exact (oddSectorTr k l n hn).comp (evenConjTransport f P e e' n)

/-- **Even character formula through the transport**: the even sector
trace of the transported even representation equals
`cycleProd (const k)`. -/
private theorem evenSectorTrTransport_perm
    {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (he'e : SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuperPair k l))
    (hee' : SuperVect.Hom.comp e e' =
      SuperVect.Hom.id (strandImage f P))
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    letI := P.additive; letI := P.linear; letI := P.braided
    evenSectorTrTransport f P e e' n
      (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) =
    cycleProd (fun _ => (k : ℂ)) σ := by
  let := P.additive
  let := P.linear
  let := P.braided
  change (evenSectorTr k l n).comp (evenConjTransport f P e e' n)
    (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) = _
  simp only [LinearMap.comp_apply]
  -- The argument of evenSectorTr equals (modelPermMap σ).evenMap
  -- by the transport identification
  have hkey : evenConjTransport f P e e' n
      (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) =
      ((modelPermMap σ : SuperVect.Hom
        (superPow (stdSuperPair k l) n)
          (superPow (stdSuperPair k l) n))).evenMap :=
    congrArg SuperVect.Hom.evenMap
      (transport_perm_eq f P e e' he'e hee' n σ)
  rw [hkey]
  exact evenSectorTr_perm k l n σ

/-- **Odd character formula through the transport**: the odd sector
trace of the transported even representation equals
`sign(σ) · cycleProd (const (2l))` (for even `n`). -/
private theorem oddSectorTrTransport_perm
    {R : ℕ} (f : EdgeRankParameter R)
    (P : DelignePackage (SkeinObj f))
    {k l : ℕ}
    (e : SuperVect.Hom (stdSuperPair k l) (strandImage f P))
    (e' : SuperVect.Hom (strandImage f P) (stdSuperPair k l))
    (he'e : SuperVect.Hom.comp e' e = SuperVect.Hom.id (stdSuperPair k l))
    (hee' : SuperVect.Hom.comp e e' =
      SuperVect.Hom.id (strandImage f P))
    (n : ℕ) (hn : Even n)
    (σ : Equiv.Perm (Fin n)) :
    letI := P.additive; letI := P.linear; letI := P.braided
    oddSectorTrTransport f P e e' n hn
      (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) =
    ((Equiv.Perm.sign σ : ℤ) : ℂ) *
      cycleProd (fun _ => ((2 * l : ℕ) : ℂ)) σ := by
  let := P.additive
  let := P.linear
  let := P.braided
  change (oddSectorTr k l n hn).comp (evenConjTransport f P e e' n)
    (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) = _
  simp only [LinearMap.comp_apply]
  have hkey : evenConjTransport f P e e' n
      (evenPermRep f P n (MonoidAlgebra.of ℂ _ σ)) =
      ((modelPermMap σ : SuperVect.Hom
        (superPow (stdSuperPair k l) n)
          (superPow (stdSuperPair k l) n))).evenMap :=
    congrArg SuperVect.Hom.evenMap
      (transport_perm_eq f P e e' he'e hee' n σ)
  rw [hkey]
  exact oddSectorTr_perm k l n hn σ

/-! ## Even (s²) is equivalent to even s -/

private theorem even_sq_of_even {s : ℕ} (hs : Even s) :
    Even (s ^ 2) := by
  obtain ⟨a, rfl⟩ := hs
  exact ⟨2 * a ^ 2, by ring⟩

private theorem even_squareDiagram_card_of_even {s : ℕ} (hs : Even s) :
    Even (squareDiagram s).card := by
  rw [squareDiagram_card]; exact even_sq_of_even hs

/-! ## The main theorem -/

/-- **Discharge of `SquareSectorBound`**: the last gap of the
quantitative Regts–Sevenster theorem.

Given `SquareBinomialDetPos` (the binomial determinant nonvanishing),
we show that when `superPermAction` kills the square-block idempotent
at every side `s' ≥ s` with `1 ≤ s`, both sector dimensions `k`
(even) and `2l` (odd) of the standard model lie below `s`. -/
theorem squareSectorBound_of_detPos (H : SquareBinomialDetPos) :
    SquareSectorBound := by
  intro R f P k l s hs1 e e' he'e hee' hdead
  let := P.additive
  let := P.linear
  let := P.braided
  constructor
  · -- **k < s** via the even sector
    -- Apply sector_bound_of_dead with:
    -- M = Module.End ℂ (superPow (strandImage f P) (squareDiagram s).card).even
    --   ρ = evenPermRep f P (squareDiagram s).card
    --   tr = evenSectorTrTransport f P e e' (squareDiagram s).card
    exact sector_bound_of_dead
      (evenPermRep f P (squareDiagram s).card)
      (evenSectorTrTransport f P e e' (squareDiagram s).card)
      -- Character: tr(ρ(of π)) = cycleProd(const k) π
      (fun π => evenSectorTrTransport_perm f P e e' he'e hee'
        (squareDiagram s).card π)
      -- Schur nonvanishing: s ≤ k → diagramSchur ≠ 0
      (fun hm => diagramSchur_square_const_ne_zero s k hm)
      -- Kill: evenPermRep(charIdempotent) = 0
      (superPermAction_zero_imp_evenPermRep_zero f P _ _
        (hdead s (le_refl s)))
  · -- **2 * l < s** via the odd sector with parity trick
    -- Pick s'' ≥ s with Even s''
    set s'' := if Even s then s else s + 1 with hs''_def
    have hs''_ge : s ≤ s'' := by
      simp only [hs''_def]; split <;> omega
    have hs''_even : Even s'' := by
      simp only [hs''_def]
      split
      · assumption
      · next h =>
        rw [Nat.even_add_one]
        exact h
    have hs''1 : 1 ≤ s'' := le_trans hs1 hs''_ge
    have hn_even : Even (squareDiagram s'').card :=
      even_squareDiagram_card_of_even hs''_even
    -- Apply sector_bound_of_dead_signed with:
    --   s := s'', m := 2 * l
    --   ρ = evenPermRep at s''
    --   tr = oddSectorTrTransport
    have h2l_lt_s'' : 2 * l < s'' :=
      sector_bound_of_dead_signed
        (evenPermRep f P (squareDiagram s'').card)
        (oddSectorTrTransport f P e e' (squareDiagram s'').card hn_even)
        -- Character: tr(ρ(of π)) = sign(π) * cycleProd(const (2l)) π
        (fun π => oddSectorTrTransport_perm f P e e' he'e hee'
          (squareDiagram s'').card hn_even π)
        -- Schur nonvanishing: s'' ≤ 2*l → diagramSchur(−(2l)) ≠ 0
        (fun hm => diagramSchur_square_neg_const_ne_zero H s'' (2 * l) hm)
        -- Kill: evenPermRep(charIdempotent at s'') = 0
        (superPermAction_zero_imp_evenPermRep_zero f P _ _
          (hdead s'' hs''_ge))
    -- Conclude 2 * l < s from 2 * l < s'' by parity analysis
    by_cases hes : Even s
    · -- Even s: s'' = s, immediate
      rw [show s'' = s from by simp [hs''_def, hes]] at h2l_lt_s''
      exact h2l_lt_s''
    · -- Odd s: s'' = s + 1, so 2l < s+1, i.e. 2l ≤ s.
      -- Since 2l is even and s is odd, 2l ≠ s, hence 2l < s.
      rw [show s'' = s + 1 from by simp [hs''_def, hes]] at h2l_lt_s''
      -- h2l_lt_s'' : 2 * l < s + 1, i.e. 2 * l ≤ s
      have h2l_le : 2 * l ≤ s := by omega
      -- 2l is even, s is odd, so 2l ≠ s
      have h2l_ne_s : 2 * l ≠ s := by
        intro h_eq
        have : Even s := h_eq ▸ ⟨l, by ring⟩
        exact hes this
      omega

end RS

end
