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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateTaylor
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateScalarExtension
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateNullstellensatz
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.SpectralExtension
public import Mathlib.FieldTheory.Normal.Defs

/-!
# Identification of the wall factors as point ideals

([hrw-decomposition] endgame item 1.) Over a finite normal extension `L/K`
splitting the residue field of a maximal `𝔮` of `Q = P K m`, every maximal
ideal of `Q_L = P L m` lying over `𝔮` has residue field exactly `L` (minimal
polynomials of the generating residues split in `L`, and a root in a domain
picks out an element of `L`), hence is a point ideal of the closed polydisc
by the translated-span identification.
-/

@[expose] public section

@[expose] public section

open scoped Classical

open Polynomial

namespace FiniteJet.GraphKoszul

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {L : Type*} [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
variable [Algebra K L] [FiniteDimensional K L]
variable {m : ℕ}

section RootPick

variable {M : Type*} [CommRing M] [IsDomain M] [Algebra K M]

/-- **Root picking**: a root in a domain of a minimal polynomial that splits
in `L` is the image of an element of `L`. -/
theorem exists_eq_algebraMap_of_splits (φ : L →ₐ[K] M) {w : M}
    (p : Polynomial K) (hmonic : p.Monic)
    (hsplit : Splits (p.map (algebraMap K L)))
    (hroot : Polynomial.aeval w p = 0) :
    ∃ l : L, w = φ l := by
  have hfact := hsplit.eq_prod_roots_of_monic (hmonic.map _)
  have hmap : (p.map (algebraMap K L)).map (φ : L →+* M) =
      p.map (algebraMap K M) := by
    rw [Polynomial.map_map]
    congr 1
    exact (φ.comp_algebraMap).symm ▸ rfl
  have hevM : Polynomial.eval w (p.map (algebraMap K M)) = 0 := by
    rw [Polynomial.eval_map]
    exact hroot
  rw [← hmap, hfact, Polynomial.map_multiset_prod,
    Polynomial.eval_multiset_prod] at hevM
  have h0 := Multiset.prod_eq_zero_iff.mp hevM
  rw [Multiset.mem_map] at h0
  obtain ⟨q, hq, hq0⟩ := h0
  rw [Multiset.mem_map] at hq
  obtain ⟨r, hr, rfl⟩ := hq
  rw [Multiset.mem_map] at hr
  obtain ⟨l, -, rfl⟩ := hr
  refine ⟨l, ?_⟩
  have h2 : Polynomial.eval w
      ((Polynomial.X - Polynomial.C l).map (φ : L →+* M)) = 0 := hq0
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
  exact sub_eq_zero.mp h2

end RootPick

section Residue

variable (hext : ∀ c : K, ‖algebraMap K L c‖ = ‖c‖)

/-- Base change commutes with the constants. -/
theorem mapP_constP (c : K) :
    mapP (m := m) hext (polyToP (MvPolynomial.C c)) =
      constP (m := m) (algebraMap K L c) := by
  refine Subtype.ext ?_
  rw [mapP_coe]
  show MvPowerSeries.map (algebraMap K L)
    ((MvPolynomial.C c : MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) =
    ((MvPolynomial.C (algebraMap K L c) : MvPolynomial (Fin m) L) :
      MvPowerSeries (Fin m) L)
  rw [MvPolynomial.coe_C, MvPolynomial.coe_C]
  exact MvPowerSeries.map_C _ _

variable [Normal K L]

include hext in
/-- **The residue field of a wall factor is the base extension**: for a
maximal `𝔫` of `P L m` lying over a maximal `𝔮` of `P K m` whose residue
embeds in the normal extension `L`, the constants map onto the residue ring
of `𝔫`. -/
theorem constP_residue_surjective (𝔮 : Ideal (P K m)) [h𝔮 : 𝔮.IsMaximal]
    (𝔫 : Ideal (P L m)) [h𝔫 : 𝔫.IsMaximal]
    (hover : Ideal.comap (mapP (m := m) hext) 𝔫 = 𝔮)
    (ψ : (P K m ⧸ 𝔮) →+* L)
    (hψK : ∀ c : K, ψ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) =
      algebraMap K L c)
    (hfinq :
      letI : Algebra K (P K m ⧸ 𝔮) :=
        (constantsToResidue 𝔮).toAlgebra
      Module.Finite K (P K m ⧸ 𝔮)) :
    Function.Surjective
      ((Ideal.Quotient.mk 𝔫).comp (constP (m := m) : L →+* P L m)) := by
  letI : Algebra K (P K m ⧸ 𝔮) :=
    (constantsToResidue 𝔮).toAlgebra
  haveI := hfinq
  haveI : IsDomain (P L m ⧸ 𝔫) :=
    Ideal.Quotient.isDomain 𝔫
  letI φ : L →+* (P L m ⧸ 𝔫) :=
    (Ideal.Quotient.mk 𝔫).comp (constP (m := m))
  letI : Algebra K (P L m ⧸ 𝔫) := (φ.comp (algebraMap K L)).toAlgebra
  -- the induced map on residues
  have hkill : ∀ a ∈ 𝔮, (Ideal.Quotient.mk 𝔫).comp
      (mapP (m := m) hext) a = 0 := by
    intro a ha
    rw [← hover, Ideal.mem_comap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  letI ρ : (P K m ⧸ 𝔮) →+* (P L m ⧸ 𝔫) :=
    Ideal.Quotient.lift 𝔮 ((Ideal.Quotient.mk 𝔫).comp
      (mapP (m := m) hext)) hkill
  -- ρ and ψ as K-algebra homs
  have hρK : ∀ c : K, ρ (algebraMap K (P K m ⧸ 𝔮) c) =
      algebraMap K (P L m ⧸ 𝔫) c := by
    intro c
    show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) = _
    rw [show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) =
      (Ideal.Quotient.mk 𝔫) (mapP (m := m) hext
        (polyToP (MvPolynomial.C c))) from rfl]
    rw [mapP_constP]
    rfl
  letI ρₐ : (P K m ⧸ 𝔮) →ₐ[K] (P L m ⧸ 𝔫) := { ρ with commutes' := hρK }
  letI ψₐ : (P K m ⧸ 𝔮) →ₐ[K] L := { ψ with commutes' := fun c => hψK c }
  letI φₐ : L →ₐ[K] (P L m ⧸ 𝔫) := { φ with commutes' := fun c => rfl }
  letI : Field (P K m ⧸ 𝔮) := Ideal.Quotient.field 𝔮
  haveI : Algebra.IsIntegral K (P K m ⧸ 𝔮) :=
    Algebra.IsIntegral.of_finite _ _
  -- root picking for the images of the base residues
  have hgen : ∀ G : P K m, ∃ l : L,
      ρ (Ideal.Quotient.mk 𝔮 G) = φ l := by
    intro G
    set Gq := Ideal.Quotient.mk 𝔮 G with hGq
    have hint : IsIntegral K Gq := Algebra.IsIntegral.isIntegral Gq
    have hmono := minpoly.monic hint
    have hroot0 := minpoly.aeval K Gq
    have haev : Polynomial.aeval (ρₐ Gq) (minpoly K Gq) = 0 := by
      rw [Polynomial.aeval_algHom_apply, hroot0, map_zero]
    have hminψ : minpoly K (ψₐ Gq) = minpoly K Gq :=
      minpoly.algHom_eq ψₐ ψₐ.toRingHom.injective Gq
    have hsplit : Splits ((minpoly K Gq).map (algebraMap K L)) := by
      rw [← hminψ]
      exact Normal.splits ‹Normal K L› (ψₐ Gq)
    obtain ⟨l, hl⟩ := exists_eq_algebraMap_of_splits φₐ
      (minpoly K Gq) hmono hsplit haev
    exact ⟨l, hl⟩
  -- assemble: every residue class is a constants image
  intro z
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective z
  letI : Algebra (P K m) (P L m) := (mapP (m := m) hext).toAlgebra
  obtain ⟨G, hG⟩ := piToP_surjective (m := m) hext (Module.finBasis K L) F
  choose l hl using fun j => hgen (G j)
  refine ⟨∑ j, l j * (Module.finBasis K L) j, ?_⟩
  show φ (∑ j, l j * (Module.finBasis K L) j) = Ideal.Quotient.mk 𝔫 F
  rw [map_sum]
  rw [← hG]
  show ∑ j, φ (l j * (Module.finBasis K L) j) =
    Ideal.Quotient.mk 𝔫 (∑ j, mapP (m := m) hext (G j) *
      polyToP (MvPolynomial.C ((Module.finBasis K L) j)))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul]
  congr 1
  exact (hl j).symm

/-- Base change carries the variables to the variables. -/
theorem mapP_polyToP_X (i : Fin m) :
    mapP (m := m) hext (polyToP (MvPolynomial.X i)) =
      polyToP (MvPolynomial.X i) := by
  refine Subtype.ext ?_
  rw [mapP_coe]
  show MvPowerSeries.map (algebraMap K L)
    ((MvPolynomial.X i : MvPolynomial (Fin m) K) : MvPowerSeries (Fin m) K) =
    ((MvPolynomial.X i : MvPolynomial (Fin m) L) : MvPowerSeries (Fin m) L)
  rw [MvPolynomial.coe_X, MvPolynomial.coe_X]
  exact MvPowerSeries.map_X _ _

include hext in
/-- The generic ultrametric ball bound along a norm-extending embedding. -/
theorem norm_le_one_of_monic_poly_hext {x : L}
    {p : Polynomial ↥(FiniteJet.unitBall K)} (hp : p.Monic)
    (hev : Polynomial.eval₂
      ((algebraMap K L).comp (FiniteJet.unitBall K).subtype) x p = 0) :
    ‖x‖ ≤ 1 := by
  set f : ↥(FiniteJet.unitBall K) →+* L :=
    (algebraMap K L).comp (FiniteJet.unitBall K).subtype with hf
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | hn
  · exfalso
    have hone : p = 1 := hp.natDegree_eq_zero.mp h0
    rw [hone, Polynomial.eval₂_one] at hev
    exact one_ne_zero hev
  have hsum := Polynomial.eval₂_eq_sum_range (p := p) f x
  rw [hev] at hsum
  rw [Finset.sum_range_succ, hp.coeff_natDegree, map_one, one_mul] at hsum
  have hx : x ^ p.natDegree = ∑ i ∈ Finset.range p.natDegree,
      (f (-(p.coeff i))) * x ^ i := by
    have h4 : x ^ p.natDegree =
        -∑ i ∈ Finset.range p.natDegree, f (p.coeff i) * x ^ i := by
      linear_combination -hsum
    rw [h4, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [map_neg]; ring
  refine FiniteJet.SpectralExtension.norm_le_one_of_pow_eq_sum hn
    (fun i => ?_) hx
  have h5 : f (-(p.coeff i)) = algebraMap K L
      (((-(p.coeff i) : ↥(FiniteJet.unitBall K)) : K)) := rfl
  rw [h5, hext]
  exact (FiniteJet.mem_unitBall_iff _ _).mp (-(p.coeff i)).2

include hext in
/-- **The wall factors are point ideals**: every maximal of `P L m` over a
finite-residue maximal of `P K m`, with `L` normal splitting the residue and
the variable images integral over the unit ball, is the point ideal of its
coordinate images. -/
theorem exists_pointIdeal_of_isMaximal_over
    (𝔮 : Ideal (P K m)) [h𝔮 : 𝔮.IsMaximal]
    (𝔫 : Ideal (P L m)) [h𝔫 : 𝔫.IsMaximal]
    (hover : Ideal.comap (mapP (m := m) hext) 𝔫 = 𝔮)
    (ψ : (P K m ⧸ 𝔮) →+* L)
    (hψK : ∀ c : K, ψ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C c))) =
      algebraMap K L c)
    (hfinq :
      letI : Algebra K (P K m ⧸ 𝔮) := (constantsToResidue 𝔮).toAlgebra
      Module.Finite K (P K m ⧸ 𝔮))
    (hint : ∀ i : Fin m, ∃ p : Polynomial ↥(FiniteJet.unitBall K),
      p.Monic ∧ Polynomial.eval₂
        (((constantsToResidue 𝔮 : K →+* (P K m ⧸ 𝔮))).comp
          (FiniteJet.unitBall K).subtype)
        (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) p = 0) :
    ∃ (x : Fin m → L) (hx : ∀ i, ‖x i‖ ≤ 1),
      𝔫 = pointIdeal (m := m) x hx := by
  have hsurj := constP_residue_surjective (m := m) hext 𝔮 𝔫 hover ψ hψK hfinq
  -- coordinates
  have hcoord : ∀ i : Fin m, ∃ xi : L,
      (Ideal.Quotient.mk 𝔫) (constP (m := m) xi) =
        (Ideal.Quotient.mk 𝔫) (polyToP (MvPolynomial.X i)) := by
    intro i
    obtain ⟨xi, hxi⟩ := hsurj ((Ideal.Quotient.mk 𝔫)
      (polyToP (MvPolynomial.X i)))
    exact ⟨xi, hxi⟩
  choose x hxeq using hcoord
  -- norm bounds via the transported integral relations
  have hkill : ∀ a ∈ 𝔮, (Ideal.Quotient.mk 𝔫).comp
      (mapP (m := m) hext) a = 0 := by
    intro a ha
    rw [← hover, Ideal.mem_comap] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
  have hchi_inj : Function.Injective
      ((Ideal.Quotient.mk 𝔫).comp (constP (m := m) : L →+* P L m)) := by
    letI : Field (P L m ⧸ 𝔫) := Ideal.Quotient.field 𝔫
    exact RingHom.injective _
  have hx : ∀ i, ‖x i‖ ≤ 1 := by
    intro i
    obtain ⟨p, hpmono, hpev⟩ := hint i
    refine norm_le_one_of_monic_poly_hext hext (p := p) hpmono ?_
    set χ : L →+* (P L m ⧸ 𝔫) :=
      (Ideal.Quotient.mk 𝔫).comp (constP (m := m)) with hχ
    set ρ : (P K m ⧸ 𝔮) →+* (P L m ⧸ 𝔫) :=
      Ideal.Quotient.lift 𝔮 ((Ideal.Quotient.mk 𝔫).comp
        (mapP (m := m) hext)) hkill with hρdef
    refine hchi_inj ?_
    rw [map_zero]
    have h6 : χ (Polynomial.eval₂
        ((algebraMap K L).comp (FiniteJet.unitBall K).subtype) (x i) p) =
        Polynomial.eval₂ (χ.comp ((algebraMap K L).comp
          (FiniteJet.unitBall K).subtype)) (χ (x i)) p :=
      Polynomial.hom_eval₂ _ _ _ _
    have h7 : ρ (Polynomial.eval₂
        (((constantsToResidue 𝔮 : K →+* (P K m ⧸ 𝔮))).comp
          (FiniteJet.unitBall K).subtype)
        (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) p) =
        Polynomial.eval₂ (ρ.comp (((constantsToResidue 𝔮 :
          K →+* (P K m ⧸ 𝔮))).comp (FiniteJet.unitBall K).subtype))
          (ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i)))) p :=
      Polynomial.hom_eval₂ _ _ _ _
    have hcomp : ρ.comp (((constantsToResidue 𝔮 :
        K →+* (P K m ⧸ 𝔮))).comp (FiniteJet.unitBall K).subtype) =
        χ.comp ((algebraMap K L).comp (FiniteJet.unitBall K).subtype) := by
      refine RingHom.ext fun c => ?_
      show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C (c : K)))) =
        χ (algebraMap K L (c : K))
      rw [show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.C (c : K)))) =
        (Ideal.Quotient.mk 𝔫) (mapP (m := m) hext
          (polyToP (MvPolynomial.C (c : K)))) from rfl, mapP_constP]
      rfl
    have hXtrans : ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) =
        χ (x i) := by
      rw [show ρ (Ideal.Quotient.mk 𝔮 (polyToP (MvPolynomial.X i))) =
        (Ideal.Quotient.mk 𝔫) (mapP (m := m) hext
          (polyToP (MvPolynomial.X i))) from rfl, mapP_polyToP_X]
      exact (hxeq i).symm
    rw [h6, ← hcomp, ← hXtrans, ← h7, hpev, map_zero]
  refine ⟨x, hx, ?_⟩
  refine eq_pointIdeal_of_isMaximal_of_span_le 𝔫 x hx ?_
  intro i
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  exact (hxeq i).symm

end Residue

end FiniteJet.GraphKoszul
