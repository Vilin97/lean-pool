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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.GraphFibreBeta
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.QuotientPowFlat

/-!
# The level-one comparison of the graph model (L1 assembly)

([hrw-decomposition] L1.)  BETA — the triviality of the special fibre of the
graph model at the contraction of a maximal ideal — is packaged here in the
form the adic-completion engine consumes: the level-one map
`A/𝔭 → Q/𝔭Q` is bijective, and consequently `𝔭Q = 𝔮`.
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver FiniteJet.GraphKoszul

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable {w : ℕ → ℕ} {N : ℕ}

/-- The extension of the contraction is contained in the ideal it came from. -/
theorem map_comap_headToQ_le (DH : RationalLocData (WPHead K w N))
    (𝔮 : Ideal (QHead DH)) :
    Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)) ≤ 𝔮 :=
  Ideal.map_le_iff_le_comap.mpr le_rfl

/-- **The special fibre is the residue field**: `Q/𝔭Q ≅ κ(𝔭)`, so the extended
contraction is maximal — and therefore equal to `𝔮`. -/
theorem map_comap_headToQ_eq (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)) = 𝔮 := by
  classical
  haveI h𝔭 : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  set 𝔟 : Ideal (QHead DH) := Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))
    with h𝔟def
  have hle : 𝔟 ≤ 𝔮 := map_comap_headToQ_le DH 𝔮
  have hsurj := headToQ_surjective_mod_map ϖ hK₀ DH hDH 𝔮 h𝔮
  set φ : WPHead K w N →+* QHead DH ⧸ 𝔟 :=
    (Ideal.Quotient.mk 𝔟).comp (headToQ DH) with hφdef
  -- the kernel of `φ` is exactly `𝔭`
  have hntQ : Nontrivial (QHead DH ⧸ 𝔟) := by
    refine ⟨⟨1, 0, fun h => h𝔮.ne_top ?_⟩⟩
    have h1 : (1 : QHead DH) ∈ 𝔟 := by
      rw [show (1 : QHead DH ⧸ 𝔟) =
        Ideal.Quotient.mk 𝔟 1 from (map_one _).symm,
        Ideal.Quotient.eq_zero_iff_mem] at h
      exact h
    exact Ideal.eq_top_iff_one 𝔮 |>.mpr (hle h1)
  have hker : RingHom.ker φ = 𝔮.comap (headToQ DH) := by
    refine (h𝔭.eq_of_le ?_ ?_).symm
    · intro htop
      have h1 : φ 1 = 0 := by
        rw [← RingHom.mem_ker, htop]
        trivial
      rw [map_one] at h1
      exact one_ne_zero h1
    · intro a ha
      rw [RingHom.mem_ker, hφdef]
      show Ideal.Quotient.mk 𝔟 (headToQ DH a) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ ha
  -- hence the special fibre is a field
  have hequiv : (WPHead K w N ⧸ 𝔮.comap (headToQ DH)) ≃+* (QHead DH ⧸ 𝔟) :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hsurj)
  have hisfieldA : IsField (WPHead K w N ⧸ 𝔮.comap (headToQ DH)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp h𝔭
  have hisfield : IsField (QHead DH ⧸ 𝔟) :=
    MulEquiv.isField hisfieldA hequiv.symm.toMulEquiv
  haveI h𝔟max : 𝔟.IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hisfield
  exact h𝔟max.eq_of_le h𝔮.ne_top hle

/-- The special-fibre surjectivity in the form the level-one map needs. -/
theorem headToQ_surjective_mod_of_eq (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) {J : Ideal (QHead DH)}
    (hJ : J = Ideal.map (headToQ DH) (𝔮.comap (headToQ DH))) :
    Function.Surjective ((Ideal.Quotient.mk J).comp (headToQ DH)) := by
  subst hJ
  exact headToQ_surjective_mod_map ϖ hK₀ DH hDH 𝔮 h𝔮

/-- **L1 level one**: the level-one map of the graph model at the contraction
of a maximal ideal is bijective. -/
theorem levelOne_bijective_headToQ (ϖ : Uniformizer K)
    [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    letI : Algebra (WPHead K w N) (QHead DH) := (headToQ DH).toAlgebra
    Function.Bijective
      (levelMap (A := WPHead K w N) (B := QHead DH)
        (𝔮.comap (headToQ DH)) 1) := by
  letI : Algebra (WPHead K w N) (QHead DH) := (headToQ DH).toAlgebra
  have halg : (algebraMap (WPHead K w N) (QHead DH)) = headToQ DH := rfl
  have hpow : (Ideal.map (algebraMap (WPHead K w N) (QHead DH))
      (𝔮.comap (headToQ DH))) ^ 1 =
      Ideal.map (headToQ DH) (𝔮.comap (headToQ DH)) := by
    rw [pow_one, halg]
  constructor
  · refine Ideal.quotientMap_injective' ?_
    intro x hx
    rw [Ideal.mem_comap, hpow] at hx
    rw [pow_one]
    exact map_comap_headToQ_le DH 𝔮 hx
  · intro y
    obtain ⟨a, ha⟩ :=
      headToQ_surjective_mod_of_eq ϖ hK₀ DH hDH 𝔮 h𝔮 hpow y
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [levelMap_mk]
    exact ha

end WeightedParity
