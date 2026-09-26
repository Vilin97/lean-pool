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
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadAwayW
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.CompletedLocalTransport
public import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.TateReducedLocal

/-!
# The completed local rings of the head at maximals off `W` are reduced

([hrw-decomposition] block B, the `W ∉ 𝔭` case at maximal ideals.)  The chain:
localize the head away from `W` (completed locals are localization-invariant),
collapse the parity constraint (`headAwayEquiv`), come back down to the
zero-weight head, identify it with the Tate algebra (`zeroHeadTateEquiv`), and
apply the block-A reducedness of Tate completed locals.  The contraction to
the zero-weight head stays maximal because the zero-weight head is a finite
module over the weighted head (`module_finite_zero_head`).
-/

@[expose] public section

@[expose] public section

namespace WeightedParity

open FiniteJetOver IsLocalRing

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

section Maximality

/-- Extensions of maximals avoiding the inverted element are maximal. -/
theorem map_isMaximal_of_away {A : Type*} [CommRing A] (s : A)
    (𝔭 : Ideal A) (h𝔭 : 𝔭.IsMaximal) (hs : s ∉ 𝔭) :
    (𝔭.map (algebraMap A (Localization.Away s))).IsMaximal := by
  have hdisj : Disjoint ((Submonoid.powers s) : Set A) (𝔭 : Set A) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hxp
    exact hs (h𝔭.isPrime.mem_of_pow_mem k hxp)
  haveI hp : (𝔭.map (algebraMap A (Localization.Away s))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) _ 𝔭
      h𝔭.isPrime hdisj
  refine ⟨⟨hp.ne_top, ?_⟩⟩
  intro I hI
  by_contra hne
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := Ideal.exists_le_maximal I hne
  haveI := h𝔪
  have h1 : 𝔭 ≤ 𝔪.comap (algebraMap A (Localization.Away s)) :=
    le_trans Ideal.le_comap_map (Ideal.comap_mono (le_of_lt (hI.trans_le hI𝔪)))
  have h2 : (𝔪.comap (algebraMap A (Localization.Away s))) ≠ ⊤ := by
    intro htop
    have h3 : (1 : A) ∈ 𝔪.comap (algebraMap A (Localization.Away s)) := by
      rw [htop]; exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h3
    exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  have h4 : 𝔭 = 𝔪.comap (algebraMap A (Localization.Away s)) :=
    h𝔭.eq_of_le h2 h1
  have h5 : 𝔪 = 𝔭.map (algebraMap A (Localization.Away s)) := by
    rw [h4, IsLocalization.map_comap (Submonoid.powers s)]
  exact (hI.trans_le hI𝔪).ne' h5

/-- Contractions along the finite extension into the zero-weight head are
maximal. -/
theorem comap_zeroHead_isMaximal (𝔫 : Ideal (WPHead K (fun _ => 0) N))
    (h𝔫 : 𝔫.IsPrime) (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal)
    (hcomap : 𝔫.comap (headToZeroHead w N) = 𝔭) : 𝔫.IsMaximal := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  haveI hfin : Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    module_finite_zero_head (K := K) (w := w) N
  letI : Field (WPHead K w N ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  letI : Algebra (WPHead K w N ⧸ 𝔭) (WPHead K (fun _ => 0) N ⧸ 𝔫) :=
    (Ideal.quotientMap 𝔫 (headToZeroHead w N) (le_of_eq hcomap.symm)).toAlgebra
  haveI hfin2 : Module.Finite (WPHead K w N ⧸ 𝔭)
      (WPHead K (fun _ => 0) N ⧸ 𝔫) := by
    obtain ⟨T, hT⟩ := hfin.fg_top
    refine ⟨⟨T.image (Ideal.Quotient.mk 𝔫), ?_⟩⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    have hb : b ∈ Submodule.span (WPHead K w N) (T : Set _) := by
      rw [hT]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hb
    · intro t ht
      exact Submodule.subset_span (Finset.mem_coe.mpr
        (Finset.mem_image_of_mem _ ht))
    · rw [_root_.map_zero]
      exact Submodule.zero_mem _
    · intro u v _ _ hu hv
      rw [_root_.map_add]
      exact Submodule.add_mem _ hu hv
    · intro a x _ hx
      have h5 : Ideal.Quotient.mk 𝔫 (a • x) =
          (Ideal.Quotient.mk 𝔭 a) • (Ideal.Quotient.mk 𝔫 x) := by
        show Ideal.Quotient.mk 𝔫 (headToZeroHead w N a * x) = _
        rw [map_mul]
        rfl
      rw [h5]
      exact Submodule.smul_mem _ _ hx
  haveI : Algebra.IsIntegral (WPHead K w N ⧸ 𝔭)
      (WPHead K (fun _ => 0) N ⧸ 𝔫) := Algebra.IsIntegral.of_finite _ _
  have hfield : IsField (WPHead K (fun _ => 0) N ⧸ 𝔫) :=
    isField_of_isIntegral_of_isField' (Field.toIsField (WPHead K w N ⧸ 𝔭))
  exact Ideal.Quotient.maximal_of_isField _ hfield

end Maximality

section Assembly

open scoped NormedField Valued

/-- **Block B, the `W ∉ 𝔭` case**: the completed local ring of the weighted
head at a maximal ideal not containing `W` is reduced. -/
theorem head_completedLocal_reduced_of_isMaximal_of_wa_notMem
    (ϖ : Uniformizer K) [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal)
    (hW : WaHead K w N ∉ 𝔭) :
    haveI := h𝔭.isPrime
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  haveI := h𝔭.isPrime
  classical
  -- step 1: extend to the W-localization of the head
  set p : Ideal (Localization.Away (WaHead K w N)) :=
    𝔭.map (algebraMap (WPHead K w N)
      (Localization.Away (WaHead K w N))) with hpdef
  haveI hpmax : p.IsMaximal := map_isMaximal_of_away _ 𝔭 h𝔭 hW
  haveI hpprime : p.IsPrime := hpmax.isPrime
  have hdisj : Disjoint
      ((Submonoid.powers (WaHead K w N)) : Set (WPHead K w N))
      (𝔭 : Set (WPHead K w N)) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hxp
    exact hW (h𝔭.isPrime.mem_of_pow_mem k hxp)
  have hcomap1 : Ideal.comap (algebraMap (WPHead K w N)
      (Localization.Away (WaHead K w N))) p = 𝔭 :=
    IsLocalization.comap_map_of_isPrime_disjoint
      (Submonoid.powers (WaHead K w N))
      (Localization.Away (WaHead K w N)) h𝔭.isPrime hdisj
  -- step 2: collapse the parity constraint
  set p' : Ideal (Localization.Away (WaHead K (fun _ => 0) N)) :=
    p.map ((headAwayEquiv w N :
      Localization.Away (WaHead K w N) ≃+*
        Localization.Away (WaHead K (fun _ => 0) N)) :
      Localization.Away (WaHead K w N) →+*
        Localization.Away (WaHead K (fun _ => 0) N)) with hp'def
  haveI hp'max : p'.IsMaximal := by
    rw [hp'def, Ideal.map_comap_of_equiv]
    exact Ideal.comap_isMaximal_of_surjective _
      (headAwayEquiv w N).symm.surjective
  haveI hp'prime : p'.IsPrime := hp'max.isPrime
  -- step 3: contract to the zero-weight head
  set 𝔫 : Ideal (WPHead K (fun _ => 0) N) :=
    p'.comap (algebraMap (WPHead K (fun _ => 0) N)
      (Localization.Away (WaHead K (fun _ => 0) N))) with h𝔫def
  haveI h𝔫prime : 𝔫.IsPrime := Ideal.IsPrime.comap _
  -- the contraction of `𝔫` to the head is `𝔭`
  have hcomap2 : 𝔫.comap (headToZeroHead w N) = 𝔭 := by
    letI : Algebra (WPHead K w N)
        (Localization.Away (WaHead K (fun _ => 0) N)) :=
      headAwayAlgebra w N
    haveI : IsLocalization.Away (WaHead K w N)
        (Localization.Away (WaHead K (fun _ => 0) N)) :=
      isLocalization_away_headW w N
    have hcommute : ((headAwayEquiv w N :
        Localization.Away (WaHead K w N) ≃+*
          Localization.Away (WaHead K (fun _ => 0) N)) :
        Localization.Away (WaHead K w N) →+*
          Localization.Away (WaHead K (fun _ => 0) N)).comp
        (algebraMap (WPHead K w N) (Localization.Away (WaHead K w N))) =
        (algebraMap (WPHead K (fun _ => 0) N)
          (Localization.Away (WaHead K (fun _ => 0) N))).comp
          (headToZeroHead w N) := by
      refine RingHom.ext fun x => ?_
      show (IsLocalization.algEquiv (Submonoid.powers (WaHead K w N))
        (Localization.Away (WaHead K w N))
        (Localization.Away (WaHead K (fun _ => 0) N)))
        (algebraMap (WPHead K w N) (Localization.Away (WaHead K w N)) x) = _
      rw [AlgEquiv.commutes]
      rfl
    have hcm : Ideal.comap ((headAwayEquiv w N :
        Localization.Away (WaHead K w N) ≃+*
          Localization.Away (WaHead K (fun _ => 0) N)) :
        Localization.Away (WaHead K w N) →+*
          Localization.Away (WaHead K (fun _ => 0) N))
        (Ideal.map ((headAwayEquiv w N :
          Localization.Away (WaHead K w N) ≃+*
            Localization.Away (WaHead K (fun _ => 0) N)) :
          Localization.Away (WaHead K w N) →+*
            Localization.Away (WaHead K (fun _ => 0) N)) p) = p :=
      Ideal.comap_map_of_bijective _ (headAwayEquiv w N).bijective
    rw [h𝔫def, Ideal.comap_comap, ← hcommute, ← Ideal.comap_comap, hp'def,
      hcm, hcomap1]
  haveI h𝔫max : 𝔫.IsMaximal :=
    comap_zeroHead_isMaximal w N 𝔫 h𝔫prime 𝔭 h𝔭 hcomap2
  -- step 4: over to the Tate algebra
  set 𝔮P : Ideal (FiniteJet.GraphKoszul.P K (N + 1)) :=
    𝔫.map (((zeroHeadTateEquiv N).symm :
      WPHead K (fun _ => 0) N ≃+* FiniteJet.GraphKoszul.P K (N + 1)) :
      WPHead K (fun _ => 0) N →+* FiniteJet.GraphKoszul.P K (N + 1))
    with h𝔮Pdef
  haveI h𝔮Pmax : 𝔮P.IsMaximal := by
    rw [h𝔮Pdef, Ideal.map_comap_of_equiv]
    exact Ideal.comap_isMaximal_of_surjective _
      ((zeroHeadTateEquiv N).symm.symm.surjective)
  haveI h𝔮Pprime : 𝔮P.IsPrime := h𝔮Pmax.isPrime
  -- block A: the Tate completed local is reduced
  haveI hredP : IsReduced (completedLocal
      (FiniteJet.GraphKoszul.P K (N + 1)) 𝔮P) :=
    FiniteJet.GraphKoszul.isReduced_adicCompletion_localization ϖ 𝔮P hK₀
  -- transport back along the chain
  haveI hredZ : IsReduced (completedLocal (WPHead K (fun _ => 0) N) 𝔫) := by
    have e₄ := completedLocalCongr ((zeroHeadTateEquiv N).symm :
      WPHead K (fun _ => 0) N ≃+* FiniteJet.GraphKoszul.P K (N + 1)) 𝔫
    exact isReduced_of_injective e₄.toRingHom e₄.injective
  haveI hredAwayZ : IsReduced (completedLocal
      (Localization.Away (WaHead K (fun _ => 0) N)) p') := by
    have e₃ := completedLocalLocalizationEquiv
      (Submonoid.powers (WaHead K (fun _ => 0) N)) p'
    exact isReduced_of_injective e₃.symm.toRingHom e₃.symm.injective
  haveI hredAwayW : IsReduced (completedLocal
      (Localization.Away (WaHead K w N)) p) := by
    have e₂ := completedLocalCongr (headAwayEquiv w N) p
    exact isReduced_of_injective e₂.toRingHom e₂.injective
  have hred : IsReduced (completedLocal (WPHead K w N)
      (Ideal.comap (algebraMap (WPHead K w N)
        (Localization.Away (WaHead K w N))) p)) := by
    have e₁ := completedLocalLocalizationEquiv
      (Submonoid.powers (WaHead K w N)) p
    exact isReduced_of_injective e₁.toRingHom e₁.injective
  have e₀ := completedLocalCongrOfEq (A := WPHead K w N) hcomap1
  exact isReduced_of_injective e₀.symm.toRingHom e₀.symm.injective

end Assembly

end WeightedParity
