/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadReducedNotMem
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.HeadTResidue
import LeanPool.UniformSheafyTateDomains.AdicSpaces.FJP.CDVFDichotomy

/-!
# Head-localization reducedness through maximal ideals

([hrw-decomposition] block D: the maximal-only rewire, per the L3
adjudication — the all-primes forms need Rees's analytically-unramified
theorem and stay parked; the consumer only needs contractions of maximals.)

`headLocsReduced'` re-proves the `HeadLocsReduced` hypothesis through the
maximal-ideal route: contractions of `QHead`-maximals are maximal
(`comap_headToQ_isMaximal`, WIP: residue finiteness through the
`T_N⟨T⟩`-tower), and the completed locals of the head at maximals are
reduced — the `W ∉ 𝔭` case is fully proven
(`head_completedLocal_reduced_of_isMaximal_of_wa_notMem`), the `W ∈ 𝔭`
quadratic-tower case is the remaining deep leaf.
-/

@[expose] public section

namespace WeightedParity

open ValuationSpectrum FiniteJetOver IsLocalRing

open scoped NormedField Valued

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

section FiniteEmbedding

/-- The fibre of the zero-weight head over a head-maximal is Artinian. -/
theorem isArtinianRing_zeroHead_fibre (𝔪 : Ideal (WPHead K w N))
    [h𝔪 : 𝔪.IsMaximal] :
    letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
      (headToZeroHead w N).toAlgebra
    IsArtinianRing (WPHead K (fun _ => 0) N ⧸
      Ideal.map (headToZeroHead w N) 𝔪) := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  letI : Field (WPHead K w N ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI hfin : Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    module_finite_zero_head (K := K) (w := w) N
  letI : Algebra (WPHead K w N ⧸ 𝔪)
      (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪) :=
    (Ideal.quotientMap (Ideal.map (headToZeroHead w N) 𝔪)
      (headToZeroHead w N) Ideal.le_comap_map).toAlgebra
  haveI h2 : Module.Finite (WPHead K w N ⧸ 𝔪)
      (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪) := by
    obtain ⟨T, hT⟩ := hfin.fg_top
    refine ⟨⟨T.image (Ideal.Quotient.mk
      (Ideal.map (headToZeroHead w N) 𝔪)), ?_⟩⟩
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
      have h5 : Ideal.Quotient.mk (Ideal.map (headToZeroHead w N) 𝔪)
          (a • x) = (Ideal.Quotient.mk 𝔪 a) •
            (Ideal.Quotient.mk (Ideal.map (headToZeroHead w N) 𝔪) x) := by
        show Ideal.Quotient.mk _ (headToZeroHead w N a * x) = _
        rw [map_mul]
        rfl
      rw [h5]
      exact Submodule.smul_mem _ _ hx
  exact IsArtinianRing.of_finite (WPHead K w N ⧸ 𝔪)
    (WPHead K (fun _ => 0) N ⧸ Ideal.map (headToZeroHead w N) 𝔪)

/-- Maximals of the zero-weight head over the pushed maximal contract to it. -/
theorem comap_eq_of_le_map (𝔪 : Ideal (WPHead K w N)) [h𝔪 : 𝔪.IsMaximal]
    (𝔫 : Ideal (WPHead K (fun _ => 0) N)) (h𝔫 : 𝔫.IsMaximal)
    (hge : Ideal.map (headToZeroHead w N) 𝔪 ≤ 𝔫) :
    Ideal.comap (headToZeroHead w N) 𝔫 = 𝔪 := by
  have h1 : 𝔪 ≤ Ideal.comap (headToZeroHead w N) 𝔫 :=
    le_trans Ideal.le_comap_map (Ideal.comap_mono hge)
  have h2 : Ideal.comap (headToZeroHead w N) 𝔫 ≠ ⊤ := by
    intro htop
    have h3 : (1 : WPHead K w N) ∈ Ideal.comap (headToZeroHead w N) 𝔫 := by
      rw [htop]
      exact Submodule.mem_top
    rw [Ideal.mem_comap, map_one] at h3
    exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h3 isUnit_one)
  exact (h𝔪.eq_of_le h2 h1).symm

/-- **Artin–Rees pullback**: an element of the head whose image lies in a
deep power of the extended ideal lies in a controlled power of the ideal. -/
theorem exists_artinRees_pullback (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔪 : Ideal (WPHead K w N)) :
    ∃ k : ℕ, ∀ n, ∀ a : WPHead K w N,
      headToZeroHead w N a ∈ (Ideal.map (headToZeroHead w N) 𝔪) ^ (n + k) →
      a ∈ 𝔪 ^ n := by
  classical
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  haveI hfin : Module.Finite (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    module_finite_zero_head (K := K) (w := w) N
  haveI hstr : IsStronglyNoetherian (WPHead K w N) :=
    isStronglyNoetherian_WPHead (w := w) (N := N) ϖ hK₀
  haveI hnoeth : IsNoetherianRing (WPHead K w N) :=
    IsStronglyNoetherian.isNoetherianRing (WPHead K w N)
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (I := 𝔪)
    (M := WPHead K (fun _ => 0) N)
    (LinearMap.range (Algebra.linearMap (WPHead K w N)
      (WPHead K (fun _ => 0) N)))
  refine ⟨k, fun n a ha => ?_⟩
  have h1 : headToZeroHead w N a ∈
      (𝔪 ^ (n + k) • ⊤ : Submodule (WPHead K w N)
        (WPHead K (fun _ => 0) N)) := by
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
      Ideal.map_pow]
    exact ha
  have h2 : headToZeroHead w N a ∈
      ((𝔪 ^ (n + k) • ⊤ : Submodule (WPHead K w N)
        (WPHead K (fun _ => 0) N)) ⊓
        LinearMap.range (Algebra.linearMap (WPHead K w N)
          (WPHead K (fun _ => 0) N))) :=
    ⟨h1, ⟨a, rfl⟩⟩
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h2
  have h3 : headToZeroHead w N a ∈
      (𝔪 ^ n • LinearMap.range (Algebra.linearMap (WPHead K w N)
        (WPHead K (fun _ => 0) N)) : Submodule (WPHead K w N)
          (WPHead K (fun _ => 0) N)) :=
    Submodule.smul_mono le_rfl inf_le_right h2
  rw [LinearMap.range_eq_map, ← Submodule.map_smul''] at h3
  obtain ⟨y, hy, hya⟩ := h3
  have hy2 : y ∈ 𝔪 ^ n := by
    have hle : (𝔪 ^ n • ⊤ : Submodule (WPHead K w N) (WPHead K w N)) ≤
        Submodule.restrictScalars (WPHead K w N) (𝔪 ^ n) := by
      refine Submodule.smul_le.mpr fun r hr x _ => ?_
      exact Ideal.mul_mem_right x _ hr
    exact hle hy
  have hae : a = y := headToZeroHead_injective w N hya.symm
  rw [hae]
  exact hy2

end FiniteEmbedding

/-- **L3.b at maximals — resolved by the finite-embedding semilocal route**
(the [hrw-decomposition] L3-rearchitecture; uniform in `W`): block-A mirror
along `headToZeroHead` with Artin–Rees cofinality. -/
theorem head_completedLocal_reduced_of_isMaximal_of_wa_mem
    (ϖ : Uniformizer K) [hdvr : IsDiscreteValuationRing 𝒪[K]]
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal)
    (hW : WaHead K w N ∈ 𝔭) :
    haveI := h𝔭.isPrime
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  classical
  haveI := h𝔭.isPrime
  letI : Algebra (WPHead K w N) (WPHead K (fun _ => 0) N) :=
    (headToZeroHead w N).toAlgebra
  haveI hart : IsArtinianRing (WPHead K (fun _ => 0) N ⧸
      Ideal.map (headToZeroHead w N) 𝔭) :=
    isArtinianRing_zeroHead_fibre w N 𝔭
  haveI hmaxN : ∀ 𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭),
      (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫).IsMaximal :=
    fun 𝔫 => overMaximal_isMaximal _ 𝔫
  -- notation: E-maps for the localization levels
  -- the levelwise family into the fibre-maximal localizations
  set g : ∀ r : ℕ,
      (Localization.AtPrime 𝔭 ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)) ^ r) →+*
      ∀ 𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭),
        (Localization.AtPrime
            (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫) ⧸
          (IsLocalRing.maximalIdeal (Localization.AtPrime
            (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫))) ^ r) :=
    fun r =>
    (RingHom.pi fun 𝔫 =>
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
          (Localization.AtPrime
            (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫))
          r).toRingEquiv.toRingHom.comp
        ((Ideal.Quotient.factor
          (pow_le_pow_left' (le_overMaximal _ 𝔫) r)).comp
          (levelMap (B := WPHead K (fun _ => 0) N) 𝔭 r)))).comp
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) r).symm.toRingEquiv.toRingHom)
    with hgdef
  -- the levelMap mk-law in the inclusion spelling
  have hlm : ∀ (n : ℕ) (a : WPHead K w N),
      levelMap (B := WPHead K (fun _ => 0) N) 𝔭 n
        (Ideal.Quotient.mk (𝔭 ^ n) a) =
      Ideal.Quotient.mk ((Ideal.map (headToZeroHead w N) 𝔭) ^ n)
        (headToZeroHead w N a) := fun n a =>
    levelMap_mk (B := WPHead K (fun _ => 0) N) 𝔭 n a
  -- component evaluation on mk-representatives
  have hcomp_mk : ∀ (r : ℕ) (a : WPHead K w N)
      (𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭)),
      g r (IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) r (Ideal.Quotient.mk _ a)) 𝔫 =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow
        (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
        (Localization.AtPrime
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)) r
        (Ideal.Quotient.mk _ (headToZeroHead w N a)) := by
    intro r a 𝔫
    rw [hgdef]
    show (IsLocalization.AtPrime.equivQuotMaximalIdealPow
        (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
        (Localization.AtPrime
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)) r)
      ((Ideal.Quotient.factor
        (pow_le_pow_left' (le_overMaximal _ 𝔫) r))
        ((levelMap (B := WPHead K (fun _ => 0) N) 𝔭 r)
          ((IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
            (Localization.AtPrime 𝔭) r).symm
            (IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
              (Localization.AtPrime 𝔭) r
              (Ideal.Quotient.mk _ a))))) = _
    rw [AlgEquiv.symm_apply_apply, hlm, Ideal.Quotient.factor_mk]
  -- localization equivalences commute with factor maps (both levels)
  have hEfacP : ∀ {a b : ℕ} (hab : a ≤ b) (c : WPHead K w N),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
          (Localization.AtPrime 𝔭) b (Ideal.Quotient.mk _ c)) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) a (Ideal.Quotient.mk _ c) := by
    intro a b hab c
    rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
      Ideal.Quotient.factor_mk,
      IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
  have hEfacN : ∀ (𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭))
      {a b : ℕ} (hab : a ≤ b) (c : WPHead K (fun _ => 0) N),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab)
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
          (Localization.AtPrime
            (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)) b
          (Ideal.Quotient.mk _ c)) =
      IsLocalization.AtPrime.equivQuotMaximalIdealPow
        (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
        (Localization.AtPrime
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)) a
        (Ideal.Quotient.mk _ c) := by
    intro 𝔫 a b hab c
    rw [IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk,
      Ideal.Quotient.factor_mk,
      IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk]
  -- transition compatibility
  have hcompat : ∀ {a b : ℕ} (hab : a ≤ b)
      (x : Localization.AtPrime 𝔭 ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)) ^ b)
      (𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭)),
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) (g b x 𝔫) =
        g a (Ideal.Quotient.factor (Ideal.pow_le_pow_right hab) x) 𝔫 := by
    intro a b hab x 𝔫
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) b).symm x)
    have hx : x = IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) b (Ideal.Quotient.mk _ c) := by
      rw [hc, AlgEquiv.apply_symm_apply]
    rw [hx, hcomp_mk, hEfacP hab, hcomp_mk]
    exact hEfacN 𝔫 hab (headToZeroHead w N c)
  -- cofinality: fibre nilpotence + Artin-Rees
  obtain ⟨e, he1, hpow⟩ := exists_pow_iInf_overMaximal_le
    (Ideal.map (headToZeroHead w N) 𝔭)
  obtain ⟨k, hAR⟩ := exists_artinRees_pullback w N ϖ hK₀ 𝔭
  have hcof : ∀ r : ℕ, ∃ s : ℕ, ∃ hrs : r ≤ s,
      ∀ y : Localization.AtPrime 𝔭 ⧸
        (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭)) ^ s,
      g s y = 0 →
        Ideal.Quotient.factor (Ideal.pow_le_pow_right hrs) y = 0 := by
    intro r
    refine ⟨e * (r + k), le_trans (Nat.le_add_right r k)
      (Nat.le_mul_of_pos_left (r + k) he1), ?_⟩
    intro y hy
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective
      ((IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) (e * (r + k))).symm y)
    have hyeq : y = IsLocalization.AtPrime.equivQuotMaximalIdealPow 𝔭
        (Localization.AtPrime 𝔭) (e * (r + k))
        (Ideal.Quotient.mk _ c) := by
      rw [hc, AlgEquiv.apply_symm_apply]
    have hmem : ∀ 𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭),
        headToZeroHead w N c ∈
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫) ^
            (e * (r + k)) := by
      intro 𝔫
      have h1 : g (e * (r + k)) y 𝔫 = 0 := congrFun hy 𝔫
      rw [hyeq, hcomp_mk] at h1
      have h2 := congrArg
        (IsLocalization.AtPrime.equivQuotMaximalIdealPow
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
          (Localization.AtPrime
            (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫))
          (e * (r + k))).symm h1
      rw [AlgEquiv.symm_apply_apply, _root_.map_zero,
        Ideal.Quotient.eq_zero_iff_mem] at h2
      exact h2
    have hiInf : headToZeroHead w N c ∈
        ((⨅ 𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭),
          overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫) ^ e) ^
          (r + k) := by
      rw [← pow_mul, Ideal.iInf_pow_eq_iInf_pow _
        (fun p q hpq => pairwise_coprime_overMaximal _ hpq)]
      exact (Submodule.mem_iInf _).mpr hmem
    have hQr : headToZeroHead w N c ∈
        (Ideal.map (headToZeroHead w N) 𝔭) ^ (r + k) :=
      pow_le_pow_left' hpow (r + k) hiInf
    have h6 : c ∈ 𝔭 ^ r := hAR r c hQr
    rw [hyeq, hEfacP (le_trans (Nat.le_add_right r k)
      (Nat.le_mul_of_pos_left (r + k) he1)),
      Ideal.Quotient.eq_zero_iff_mem.mpr h6, _root_.map_zero]
  -- the factors are reduced: zero-head completed locals via block A
  haveI hredF : ∀ 𝔫 : fibreMaximals (Ideal.map (headToZeroHead w N) 𝔭),
      IsReduced (AdicCompletion
        (IsLocalRing.maximalIdeal (Localization.AtPrime
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)))
        (Localization.AtPrime
          (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫))) := by
    intro 𝔫
    haveI := (hmaxN 𝔫).isPrime
    set 𝔮P : Ideal (FiniteJet.GraphKoszul.P K (N + 1)) :=
      (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫).map
        (((zeroHeadTateEquiv N).symm :
          WPHead K (fun _ => 0) N ≃+* FiniteJet.GraphKoszul.P K (N + 1)) :
          WPHead K (fun _ => 0) N →+* FiniteJet.GraphKoszul.P K (N + 1))
      with h𝔮Pdef
    haveI h𝔮Pmax : 𝔮P.IsMaximal := by
      rw [h𝔮Pdef, Ideal.map_comap_of_equiv]
      exact Ideal.comap_isMaximal_of_surjective _
        ((zeroHeadTateEquiv N).symm.symm.surjective)
    haveI h𝔮Pprime : 𝔮P.IsPrime := h𝔮Pmax.isPrime
    haveI hredP : IsReduced (completedLocal
        (FiniteJet.GraphKoszul.P K (N + 1)) 𝔮P) :=
      FiniteJet.GraphKoszul.isReduced_adicCompletion_localization ϖ 𝔮P hK₀
    have e₄ := completedLocalCongr ((zeroHeadTateEquiv N).symm :
      WPHead K (fun _ => 0) N ≃+* FiniteJet.GraphKoszul.P K (N + 1))
      (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫)
    exact isReduced_of_injective e₄.toRingHom e₄.injective
  exact AdicCompletion.isReduced_of_levelwisePi_cofinal
    (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭))
    (fun 𝔫 => IsLocalRing.maximalIdeal (Localization.AtPrime
      (overMaximal (Ideal.map (headToZeroHead w N) 𝔭) 𝔫))) g
    (fun {a b} hab x 𝔫 => hcompat hab x 𝔫) hcof

/-- **L3 at maximals**: every completed local ring of the head at a maximal
ideal is reduced. -/
theorem head_completedLocal_reduced_of_isMaximal
    (ϖ : Uniformizer K) (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (𝔭 : Ideal (WPHead K w N)) (h𝔭 : 𝔭.IsMaximal) :
    haveI := h𝔭.isPrime
    IsReduced (completedLocal (WPHead K w N) 𝔭) := by
  haveI hdvr : IsDiscreteValuationRing 𝒪[K] :=
    ϖ.isDiscreteValuationRing hK₀
  by_cases hW : WaHead K w N ∈ 𝔭
  · exact head_completedLocal_reduced_of_isMaximal_of_wa_mem
      w N ϖ hK₀ 𝔭 h𝔭 hW
  · exact head_completedLocal_reduced_of_isMaximal_of_wa_notMem
      w N ϖ hK₀ 𝔭 h𝔭 hW

/-- **D-prep — contraction maximality**: the contraction of a
`QHead`-maximal to the head is maximal (residue finiteness through the
`T_N⟨T⟩`-tower Nullstellensatz and the restricted Fubini). -/
theorem comap_headToQ_isMaximal (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K))
    (DH : RationalLocData (WPHead K w N)) (hDH : DH.IsRational)
    (𝔮 : Ideal (QHead DH)) (h𝔮 : 𝔮.IsMaximal) :
    (𝔮.comap (headToQ DH)).IsMaximal := by
  classical
  haveI hdvr : IsDiscreteValuationRing 𝒪[K] :=
    ϖ.isDiscreteValuationRing hK₀
  -- move into the unfolded quotient ring once and for all
  set 𝔮' : Ideal (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
      headGraphIdeal DH) := 𝔮 with h𝔮'def
  have h𝔮'max : 𝔮'.IsMaximal := h𝔮
  haveI := h𝔮'max
  set 𝔮₀ : Ideal (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card) :=
    𝔮'.comap (Ideal.Quotient.mk (headGraphIdeal DH)) with h𝔮₀def
  haveI h𝔮₀max : 𝔮₀.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  letI : Algebra K
      (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀) :=
    ((Ideal.Quotient.mk 𝔮₀).comp
      (((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
        (m := DH.T.card)).comp MvPolynomial.C).comp
        (constHead K w N))).toAlgebra
  haveI hfinT : Module.Finite K
      (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀) :=
    module_finite_residue_headT w N DH.T.card ϖ hK₀ 𝔮₀
  -- the residue rings agree
  set φ : FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card →+*
      ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
        headGraphIdeal DH) ⧸ 𝔮') :=
    (Ideal.Quotient.mk 𝔮').comp
      (Ideal.Quotient.mk (headGraphIdeal DH)) with hφdef
  have hφsurj : Function.Surjective φ := by
    rw [hφdef]
    show Function.Surjective
      (⇑(Ideal.Quotient.mk 𝔮') ∘ ⇑(Ideal.Quotient.mk (headGraphIdeal DH)))
    exact Function.Surjective.comp Ideal.Quotient.mk_surjective
      Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = 𝔮₀ := by
    refine Ideal.ext fun x => ?_
    constructor
    · intro hx
      rw [RingHom.mem_ker] at hx
      have hx2 : Ideal.Quotient.mk 𝔮'
          (Ideal.Quotient.mk (headGraphIdeal DH) x) = 0 := hx
      rw [Ideal.Quotient.eq_zero_iff_mem] at hx2
      rw [h𝔮₀def]
      exact Ideal.mem_comap.mpr hx2
    · intro hx
      rw [h𝔮₀def, Ideal.mem_comap] at hx
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk 𝔮'
        (Ideal.Quotient.mk (headGraphIdeal DH) x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hx
  letI : Algebra K ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
      headGraphIdeal DH) ⧸ 𝔮') :=
    ((Ideal.Quotient.mk 𝔮').comp
      ((Ideal.Quotient.mk (headGraphIdeal DH)).comp
        (((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
          (m := DH.T.card)).comp MvPolynomial.C).comp
          (constHead K w N)))).toAlgebra
  set E : (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀) ≃+*
      ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
        headGraphIdeal DH) ⧸ 𝔮') :=
    (Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hφsurj) with hEdef
  have hEc : ∀ c : K,
      E (algebraMap K
        (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀) c) =
      algebraMap K ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
        headGraphIdeal DH) ⧸ 𝔮') c := by
    intro c
    show E (Ideal.Quotient.mk 𝔮₀
      (FiniteJet.GraphKoszul.polyToP
        (MvPolynomial.C (constHead K w N c)))) = _
    rw [hEdef]
    show (RingHom.quotientKerEquivOfSurjective hφsurj)
      ((Ideal.quotEquivOfEq hker.symm)
        (Ideal.Quotient.mk 𝔮₀ (FiniteJet.GraphKoszul.polyToP
          (MvPolynomial.C (constHead K w N c))))) = _
    rw [Ideal.quotEquivOfEq_mk,
      RingHom.quotientKerEquivOfSurjective_apply_mk]
    rfl
  have hlin : ∀ (c : K)
      (x : FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀),
      E (c • x) = c • E x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hEc]
  haveI hfinQ : Module.Finite K
      ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
        headGraphIdeal DH) ⧸ 𝔮') :=
    Module.Finite.equiv
      ({ toFun := ⇑E,
         invFun := ⇑E.symm,
         left_inv := E.left_inv,
         right_inv := E.right_inv,
         map_add' := fun a b => map_add E a b,
         map_smul' := fun c x => by
           rw [RingHom.id_apply]
           exact hlin c x } :
        (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸ 𝔮₀) ≃ₗ[K]
          ((FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
            headGraphIdeal DH) ⧸ 𝔮'))
  letI : Algebra K (WPHead K w N) := (constHead K w N).toAlgebra
  letI : Algebra K (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
      headGraphIdeal DH) :=
    ((Ideal.Quotient.mk (headGraphIdeal DH)).comp
      (((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
        (m := DH.T.card)).comp MvPolynomial.C).comp
        (constHead K w N))).toAlgebra
  have hfinal : (𝔮'.comap ((Ideal.Quotient.mk (headGraphIdeal DH)).comp
      (((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
        (m := DH.T.card)).comp MvPolynomial.C)))).IsMaximal := by
    have h9 := FiniteJet.GraphKoszul.comap_isMaximal_of_finite_residue
      (h𝔫 := h𝔮'max) (hfin := hfinQ)
      ({ (Ideal.Quotient.mk (headGraphIdeal DH)).comp
          (((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
            (m := DH.T.card)).comp MvPolynomial.C)) with
         commutes' := fun c => rfl } :
        WPHead K w N →ₐ[K]
          (FiniteJet.GraphKoszul.P (WPHead K w N) DH.T.card ⧸
            headGraphIdeal DH)) 𝔮'
    exact h9
  have hid : 𝔮.comap (headToQ DH) =
      𝔮'.comap ((Ideal.Quotient.mk (headGraphIdeal DH)).comp
        ((FiniteJet.GraphKoszul.polyToP (E := WPHead K w N)
          (m := DH.T.card)).comp MvPolynomial.C)) :=
    Ideal.ext fun x => Iff.rfl
  rw [hid]
  exact hfinal

/-- **L4 through maximals**: the head-localization reducedness hypothesis,
by the maximal-ideal route. -/
theorem headLocsReduced' (ϖ : Uniformizer K)
    (hK₀ : IsNoetherianRing (FiniteJet.unitBall K)) :
    HeadLocsReduced K w := by
  intro N DH hDH
  haveI hQnoeth : IsNoetherianRing (QHead DH) :=
    isNoetherianRing_qHead ϖ hK₀ hDH
  suffices h : IsReduced (QHead DH) by
    exact isReduced_of_injective
      (headLocEquiv ϖ hK₀ DH hDH).toRingHom
      (headLocEquiv ϖ hK₀ DH hDH).injective
  refine isReduced_of_forall_completedLocal_reduced _ ?_
  intro 𝔮 h𝔮
  haveI := h𝔮.isPrime
  haveI hcm : (𝔮.comap (headToQ DH)).IsMaximal :=
    comap_headToQ_isMaximal w N ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI hcp : (𝔮.comap (headToQ DH)).IsPrime := hcm.isPrime
  obtain ⟨e⟩ := qHead_completedLocal_comparison ϖ hK₀ DH hDH 𝔮 h𝔮
  haveI : IsReduced
      (completedLocal (WPHead K w N) (𝔮.comap (headToQ DH))) :=
    head_completedLocal_reduced_of_isMaximal w N ϖ hK₀ _ hcm
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

end WeightedParity
