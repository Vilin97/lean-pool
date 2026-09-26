/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/
module


/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadReduced
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.AdicNakayama

/-!
# Transport of completed local rings

([hrw-decomposition] endgame blocks B/C, shared engine.)  Completed local
rings transport along ring isomorphisms, and are invariant under an
intermediate localization: for a prime `p` of `Localization M`, the completed
local ring of the base at the contraction of `p` agrees with the completed
local ring of `Localization M` at `p` (mathlib's
`localizationLocalizationAtPrimeIsoLocalization` at each finite level).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open IsLocalRing

section LocalRingCongr

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Maximal-adic completions transport along isomorphisms of local rings. -/
noncomputable def AdicCompletion.localRingCongr [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    AdicCompletion (maximalIdeal A) A ≃+* AdicCompletion (maximalIdeal B) B :=
  AdicCompletion.congrPow (maximalIdeal A) (maximalIdeal B)
    (fun n => Ideal.quotientEquiv ((maximalIdeal A) ^ n)
      ((maximalIdeal B) ^ n) e
      (by rw [Ideal.map_pow, IsLocalRing.map_maximalIdeal_of_surjective
        (e : A →+* B) e.surjective]))
    (fun {a b} hab x => by
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.quotientEquiv_mk, Ideal.Quotient.factor_mk,
        Ideal.Quotient.factor_mk, Ideal.quotientEquiv_mk])

/-- Prime complements map to prime complements under ring isomorphisms. -/
theorem primeCompl_map_equiv (e : A ≃+* B) (𝔭 : Ideal A) [𝔭.IsPrime]
    [(𝔭.map (e : A →+* B)).IsPrime] :
    Submonoid.map (e : A ≃* B) 𝔭.primeCompl =
      (𝔭.map (e : A →+* B)).primeCompl := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    intro hmem
    rw [Ideal.map_comap_of_equiv, SetLike.mem_coe, Ideal.mem_comap] at hmem
    exact ha (by simpa using hmem)
  · intro hx
    refine ⟨e.symm x, fun hmem => hx ?_, by simp⟩
    rw [Ideal.map_comap_of_equiv, SetLike.mem_coe, Ideal.mem_comap]
    exact hmem

/-- **`completedLocal` transports along ring isomorphisms.** -/
noncomputable def completedLocalCongr (e : A ≃+* B) (𝔭 : Ideal A) [𝔭.IsPrime]
    [(𝔭.map (e : A →+* B)).IsPrime] :
    completedLocal A 𝔭 ≃+* completedLocal B (𝔭.map (e : A →+* B)) :=
  AdicCompletion.localRingCongr
    (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime 𝔭)
      (Localization.AtPrime (𝔭.map (e : A →+* B))) e
      (primeCompl_map_equiv e 𝔭))

end LocalRingCongr

section LocalizationInvariance

variable {A : Type*} [CommRing A]

/-- **Completed locals are invariant under an intermediate localization**: for
a prime `p` of `Localization M`, the completed local ring of the base at the
contraction agrees with the completed local ring of the localization at `p`. -/
noncomputable def completedLocalLocalizationEquiv (M : Submonoid A)
    (p : Ideal (Localization M)) [p.IsPrime] :
    completedLocal A (Ideal.comap (algebraMap A (Localization M)) p) ≃+*
      completedLocal (Localization M) p :=
  AdicCompletion.localRingCongr
    ((IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      M p).toRingEquiv)

end LocalizationInvariance

section CongrOfEq

variable {A : Type*} [CommRing A]

/-- Transport of completed locals along an equality of primes (the prime
instances are proof-irrelevant). -/
noncomputable def completedLocalCongrOfEq {𝔭 𝔮 : Ideal A}
    [𝔭.IsPrime] [𝔮.IsPrime] (h : 𝔭 = 𝔮) :
    completedLocal A 𝔭 ≃+* completedLocal A 𝔮 := by
  subst h
  exact RingEquiv.refl _

end CongrOfEq

end WeightedParity
