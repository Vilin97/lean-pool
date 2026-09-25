/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.AffineReduction
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralSwap
public import LeanPool.BrillNoetherGraphs.Utilities.Iso.GraphContractionFibreTree
public import LeanPool.BrillNoetherGraphs.Bananas.Wedge.WedgeSubmodularity
public import LeanPool.BrillNoetherGraphs.Bananas.Transmission.KGeneralBNGeneral
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.ChainGluing

/-!
# Chains with a common general-transmission period

The corollary following Proposition 6.1 cites Theorem A of Pflueger 2022:
vertex-gluing twice-marked graphs with the same `k`-general transmission
period preserves `k`-general transmission.  This file proves the required
affine Coxeter-length inequality directly from the periodic simple-reflection
reduction already developed for Proposition 6.13, then records the two-factor
and iterated graph statements and the resulting Brill--Noether generality
criterion.
-/

@[expose] public section

namespace Bananas

open Utilities

/-! ## Affine Coxeter length and the Demazure product -/

theorem IsKAffine.aspPerm_mul
    {k : ℕ} {α β : AspPerm}
    (hα : IsKAffine k α.func) (hβ : IsKAffine k β.func) :
    IsKAffine k (α * β).func := by
  intro n
  simp only [AspPerm.mul_apply]
  rw [hβ n, hα (β n)]

theorem kInversionCount_aspPerm_inv
    {k : ℕ} (hk : 0 < k) (α : AspPerm)
    (hα : IsKAffine k α.func) :
    kInversionCount k (α⁻¹).func = kInversionCount k α.func := by
  have hraw : rawInverse α.func = (α⁻¹).func := by
    funext n
    apply α.injective
    rw [apply_rawInverse_apply α.func α.bijective]
    exact (α.mul_inv_cancel_eval n).symm
  rw [← hraw, kInversionCount_rawInverse hk α.bijective hα]

private def translatePair (c : ℤ) (p : ℤ × ℤ) : ℤ × ℤ :=
  (p.1 + c, p.2 + c)

private theorem normalize_translate_neg_normalize_translate
    {k : ℕ} (hk : 0 < k) (c : ℤ) (p : ℤ × ℤ)
    (hp0 : 0 ≤ p.1) (hpk : p.1 < k) :
    normalizeFirstPair k
        (translatePair (-c) (normalizeFirstPair k (translatePair c p))) = p := by
  let q : ℤ := -((p.1 + c) / (k : ℤ))
  have hInner :
      normalizeFirstPair k (translatePair c p) =
        shiftPair k q (translatePair c p) := by
    exact normalizeFirstPair_eq_shiftPair k (translatePair c p)
  rw [hInner]
  have hTranslate :
      translatePair (-c) (shiftPair k q (translatePair c p)) =
        shiftPair k q p := by
    apply Prod.ext <;> simp only [translatePair, shiftPair]
    <;> ring
  rw [hTranslate]
  exact normalizeFirstPair_shiftPair_of_fundamental hk p hp0 hpk q

private theorem kInversionCount_comp_intShift_le
    {k : ℕ} (hk : 0 < k) (α : AspPerm)
    (hα : IsKAffine k α.func) (c : ℤ) :
    kInversionCount k (fun n => α (n + c)) ≤
      kInversionCount k α.func := by
  unfold kInversionCount
  have hfin := kInversions_finite_of_isKAffine hk hα
  refine Set.ncard_le_ncard_of_injOn
    (fun p => normalizeFirstPair k (translatePair c p)) ?_ ?_ hfin
  · rintro p hp
    have hInv : translatePair c p ∈ invSet α.func := by
      rcases hp with ⟨hlt, hinv, -, -⟩
      refine ⟨?_, hinv⟩
      omega
    simpa only [normalizeFirstPair, translatePair] using
      inversion_normalize_first_coordinate hk hα hInv
  · intro p hp q hq heq
    have h := congrArg
      (fun r => normalizeFirstPair k (translatePair (-c) r)) heq
    rw [normalize_translate_neg_normalize_translate hk c p hp.2.2.1 hp.2.2.2,
      normalize_translate_neg_normalize_translate hk c q hq.2.2.1 hq.2.2.2] at h
    exact h

private theorem eq_intShift_of_inv_set_eq_empty
    (β : AspPerm) (hinv : invSet β.func = ∅) :
    ∀ n : ℤ, β n = n + β 0 := by
  have hStrict : ∀ a b : ℤ, a < b → β a < β b := by
    intro a b hab
    by_contra hnot
    have hne : β a ≠ β b := fun h => (by omega : a ≠ b) (β.injective h)
    have hInv : (a, b) ∈ invSet β.func := ⟨hab, by omega⟩
    rw [hinv] at hInv
    exact hInv
  have hStep : ∀ n : ℤ, β (n + 1) = β n + 1 := by
    intro n
    have hlt := hStrict n (n + 1) (by omega)
    by_contra hne
    have hgap : β n + 1 < β (n + 1) := by omega
    obtain ⟨m, hm⟩ := β.surjective (β n + 1)
    have hnm : n < m := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hmn | rfl
      · have := hStrict m n hmn
        rw [hm] at this
        omega
      · rw [hm] at hgap
        omega
    have hmn : m < n + 1 := by
      by_contra h
      rcases lt_or_eq_of_le (le_of_not_gt h) with hnm' | heq
      · have := hStrict (n + 1) m hnm'
        rw [hm] at this
        omega
      · subst m
        rw [hm] at hgap
        omega
    omega
  intro n
  refine Int.induction_on n (by simp) ?_ ?_
  · intro m ih
    rw [hStep, ih]
    ring
  · intro m ih
    have h := hStep (-((m : ℤ)) - 1)
    have hArg : -((m : ℤ)) - 1 + 1 = -(m : ℤ) := by ring
    rw [hArg, ih] at h
    omega

private theorem affineReflectionSupport_rising_uniform
    {k : ℕ} {α : AspPerm} (hα : IsKAffine k α.func)
    (i : ℤ) (_hk : 2 ≤ k) :
    Transpositions.risingSet α (affineReflectionSupport k i) =
      if α i < α (i + 1) then affineReflectionSupport k i else ∅ := by
  ext n
  simp only [Transpositions.risingSet, Set.mem_ofPred_eq]
  by_cases hasi : α i < α (i + 1)
  · rw [if_pos hasi]
    constructor
    · exact fun h => h.1
    · intro hn
      refine ⟨hn, ?_⟩
      obtain ⟨q, hq⟩ := hn
      have hnEq : n = i + q * (k : ℤ) := by
        rw [mul_comm (k : ℤ) q] at hq
        omega
      have hαn := hα.iterate_int i q
      have hαsucc := hα.iterate_int (i + 1) q
      rw [hnEq, hαn,
        show i + q * (k : ℤ) + 1 = (i + 1) + q * (k : ℤ) by ring,
        hαsucc]
      omega
  · rw [if_neg hasi]
    simp only [Set.mem_empty_iff_false, iff_false, not_and]
    intro hn
    obtain ⟨q, hq⟩ := hn
    have hnEq : n = i + q * (k : ℤ) := by
      rw [mul_comm (k : ℤ) q] at hq
      omega
    have hαn := hα.iterate_int i q
    have hαsucc := hα.iterate_int (i + 1) q
    rw [hnEq, hαn,
      show i + q * (k : ℤ) + 1 = (i + 1) + q * (k : ℤ) by ring,
      hαsucc]
    omega

private theorem kInversionCount_mul_affineReflection_add_one
    {k : ℕ} {α : AspPerm} (hα : IsKAffine k α.func)
    (i : ℤ) (hk : 2 ≤ k) (hRise : α i < α (i + 1)) :
    kInversionCount k (α * affineReflection k i hk).func =
      kInversionCount k α.func + 1 := by
  let s := affineReflection k i hk
  let γ := α * s
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hsAffine : IsKAffine k s.func :=
    affineReflection_isKAffine k i hk
  have hγAffine : IsKAffine k γ.func := hα.aspPerm_mul hsAffine
  have hFall : γ (i + 1) < γ i := by
    have hi : i ∈ affineReflectionSupport k i := by
      refine ⟨0, ?_⟩
      ring
    have hsi := affineReflection_apply_of_mem k i hk hi
    have hipred : (i + 1 : ℤ) - 1 ∈ affineReflectionSupport k i := by
      simpa only [add_sub_cancel_right] using hi
    have hsip := affineReflection_apply_of_pred_mem k i hk hipred
    simp only [γ, s, AspPerm.mul_apply]
    rw [hsi, hsip]
    simpa only [add_sub_cancel_right] using hRise
  have hInvAffine : IsKAffine k (γ⁻¹).func := hγAffine.aspPerm_inv
  have hRemove := kInversionCount_left_mul_affineReflection_add_one
    hInvAffine i hk (by simpa only [inv_inv] using hFall)
  have hProduct : affineReflection k i hk * γ⁻¹ = α⁻¹ := by
    simp only [γ, s, mul_inv_rev]
    group
  rw [hProduct, kInversionCount_aspPerm_inv hkpos α hα,
    kInversionCount_aspPerm_inv hkpos γ hγAffine] at hRemove
  change kInversionCount k γ.func = kInversionCount k α.func + 1
  omega

/-- Right Demazure multiplication by one periodic simple reflection preserves
`k`-affinity and raises affine inversion length by at most one. -/
theorem affineReflection_star_affine_and_count_le
    {k : ℕ} {α : AspPerm} (hα : IsKAffine k α.func)
    (i : ℤ) (hk : 2 ≤ k) :
    IsKAffine k (α ⋆ affineReflection k i hk).func ∧
      kInversionCount k (α ⋆ affineReflection k i hk).func ≤
        kInversionCount k α.func + 1 := by
  let S := affineReflectionSupport k i
  let hS := affineReflectionSupport_noConsecutive k hk i
  have hsEq : affineReflection k i hk = Transpositions.sigma S hS := rfl
  by_cases hRise : α i < α (i + 1)
  · have hR : Transpositions.risingSet α S = S := by
      simpa only [S, if_pos hRise] using
        affineReflectionSupport_rising_uniform hα i hk
    have hStar : α ⋆ affineReflection k i hk = α * affineReflection k i hk := by
      rw [hsEq, Transpositions.starSigma]
      apply congrArg (fun t : AspPerm => α * t)
      apply AspPerm.ext.mpr
      funext n
      change Transpositions.sigmaFun (Transpositions.risingSet α S) n =
        Transpositions.sigmaFun S n
      rw [hR]
    rw [hStar]
    exact ⟨hα.aspPerm_mul (affineReflection_isKAffine k i hk),
      by rw [kInversionCount_mul_affineReflection_add_one hα i hk hRise]⟩
  · have hR : Transpositions.risingSet α S = ∅ := by
      simpa only [S, if_neg hRise] using
        affineReflectionSupport_rising_uniform hα i hk
    have hStar : α ⋆ affineReflection k i hk = α := by
      rw [hsEq, Transpositions.starSigma]
      apply AspPerm.ext.mpr
      funext n
      simp only [AspPerm.mul_apply]
      change α (Transpositions.sigmaFun (Transpositions.risingSet α S) n) = α n
      rw [hR]
      simp [Transpositions.sigmaFun]
    rw [hStar]
    exact ⟨hα, by omega⟩

/-- Affine Coxeter length is subadditive under the Demazure product.  This is
the combinatorial content of the same-period gluing theorem cited from
Pflueger 2022. -/
theorem kInversionCount_star_le
    (k : ℕ) (α β : AspPerm)
    (hα : IsKAffine k α.func) (hβ : IsKAffine k β.func) :
    IsKAffine k (α ⋆ β).func ∧
      kInversionCount k (α ⋆ β).func ≤
        kInversionCount k α.func + kInversionCount k β.func := by
  by_cases hkzero : k = 0
  · subst k
    constructor
    · intro n
      simp
    · have hzeroCount : ∀ τ : ℤ → ℤ, kInversionCount 0 τ = 0 := by
        intro τ
        unfold kInversionCount
        have hempty : kInversions 0 τ = ∅ := by
          ext p
          simp [kInversions]
        rw [hempty, Set.ncard_empty]
      rw [hzeroCount, hzeroCount, hzeroCount]
  have hkpos : 0 < k := Nat.pos_of_ne_zero hkzero
  suffices H : ∀ n : ℕ, ∀ α β : AspPerm,
      IsKAffine k α.func → IsKAffine k β.func →
      kInversionCount k β.func = n →
      IsKAffine k (α ⋆ β).func ∧
        kInversionCount k (α ⋆ β).func ≤ kInversionCount k α.func + n by
    exact H _ α β hα hβ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro α β hα hβ hcount
      rcases Nat.eq_zero_or_pos n with hzero | hpos
      · subst hzero
        have hinv := inv_set_eq_empty_of_kInversionCount_eq_zero
          k hkpos β hβ hcount
        have hInv : invSet (β⁻¹).func = ∅ := by
          ext p
          simp only [Set.mem_empty_iff_false, iff_false]
          intro hp
          rcases p with ⟨u, v⟩
          have hback := ((β⁻¹).inv_set_inverse u v).mp hp
          simp only [inv_inv] at hback
          rw [hinv] at hback
          exact hback
        have hred : AspPerm.ReducedProduct α β := by
          unfold AspPerm.ReducedProduct
          rw [hInv]
          simp
        have hStar := (ReducedProducts.star_eq_mul_iff_reducedProduct α β).2 hred
        rw [hStar]
        refine ⟨hα.aspPerm_mul hβ, ?_⟩
        have hShift := eq_intShift_of_inv_set_eq_empty β hinv
        have hFunc : (α * β).func = fun n => α (n + β 0) := by
          funext n
          simp only [AspPerm.mul_apply]
          rw [hShift n]
        rw [hFunc]
        exact kInversionCount_comp_intShift_le hkpos α hα (β 0)
      · obtain ⟨i, hk, β', hfact, hβ', hcount'⟩ :=
          exists_affineReflection_reduction hβ (by omega)
        obtain ⟨hαsAffine, hαsCount⟩ :=
          affineReflection_star_affine_and_count_le hα i hk
        have hrec := ih (kInversionCount k β'.func) (by omega)
          (α ⋆ affineReflection k i hk) β' hαsAffine hβ' rfl
        have hassoc : α ⋆ β = (α ⋆ affineReflection k i hk) ⋆ β' := by
          rw [hfact]
          exact (AspPerm.star_assoc α _ β').symm
        rw [hassoc]
        constructor
        · exact hrec.1
        · omega

/-! ## Common-period general transmission across wedges and chains -/

/-- A common torsion witness glues across an opposite-side vertex wedge. -/
theorem torsionWitness_vertexWedge_opposite
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (k : ℕ)
    (hG : TorsionWitness (mark G u x) k)
    (hH : TorsionWitness (mark H y v) k) :
    TorsionWitness
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k := by
  refine ⟨hG.1, ?_⟩
  have hGlue :
      wedgeAddDivisor G H x y ((k : ℤ) • oneChip x) 0 =
        wedgeAddDivisor G H x y 0 ((k : ℤ) • oneChip y) := by
    have hLeft := wedgeAddDivisor_zsmul G H x y (oneChip x)
      (0 : CFDiv H) (k : ℤ)
    have hRight := wedgeAddDivisor_zsmul G H x y (0 : CFDiv G)
      (oneChip y) (k : ℤ)
    simp only [smul_zero] at hLeft hRight
    rw [← hLeft, ← hRight, wedgeAddDivisor_one_chip_left,
      wedgeAddDivisor_one_chip_right, wedgeRightVertex_marked]
  have hZero : wedgeAddDivisor G H x y (0 : CFDiv G) (0 : CFDiv H) = 0 := by
    funext z
    cases z with
    | inl a =>
        rw [wedgeAddDivisor_left]
        change (0 : ℤ) + (if a = x then 0 else 0) = (0 : ℤ)
        simp
    | inr b =>
        rw [wedgeAddDivisor_right]
        rfl
  have hTarget :
      (k : ℤ) •
          (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
            oneChip (G := vertexWedge G H x y)
              (wedgeRightVertex G H x y v)) =
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
          (-((k : ℤ) • oneChip v)) := by
    simpa [smul_sub, hZero] using
      (wedgeAddDivisor_transmissionTwist G H x y
        (0 : CFDiv G) (0 : CFDiv H) u v (k : ℤ) (k : ℤ))
  have hFactor :
      wedgeAddDivisor G H x y
          ((k : ℤ) • (oneChip u - oneChip x))
          ((k : ℤ) • (oneChip y - oneChip v)) =
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
          (-((k : ℤ) • oneChip v)) := by
    rw [smul_sub, smul_sub, ← wedgeAddDivisor_sub]
    have hLeft :
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
            ((k : ℤ) • oneChip y) =
          wedgeAddDivisor G H x y ((k : ℤ) • oneChip u) 0 +
            wedgeAddDivisor G H x y 0 ((k : ℤ) • oneChip y) := by
      rw [wedgeAddDivisor_add]
      simp
    have hRight :
        wedgeAddDivisor G H x y ((k : ℤ) • oneChip x)
            ((k : ℤ) • oneChip v) =
          wedgeAddDivisor G H x y ((k : ℤ) • oneChip x) 0 +
            wedgeAddDivisor G H x y 0 ((k : ℤ) • oneChip v) := by
      rw [wedgeAddDivisor_add]
      simp
    rw [hLeft, hRight, ← hGlue]
    calc
      wedgeAddDivisor G H x y ((k : ℤ) • oneChip u) 0 +
          wedgeAddDivisor G H x y ((k : ℤ) • oneChip x) 0 -
          (wedgeAddDivisor G H x y ((k : ℤ) • oneChip x) 0 +
            wedgeAddDivisor G H x y 0 ((k : ℤ) • oneChip v)) =
          wedgeAddDivisor G H x y ((k : ℤ) • oneChip u) 0 -
            wedgeAddDivisor G H x y 0 ((k : ℤ) • oneChip v) := by abel
      _ = wedgeAddDivisor G H x y
          (((k : ℤ) • oneChip u) - 0)
          (0 - ((k : ℤ) • oneChip v)) := by
          rw [wedgeAddDivisor_sub]
      _ = wedgeAddDivisor G H x y ((k : ℤ) • oneChip u)
          (-((k : ℤ) • oneChip v)) := by simp
  have hWedge := linear_equiv_wedgeAddDivisor G H x y
    ((k : ℤ) • (oneChip u - oneChip x)) 0
    ((k : ℤ) • (oneChip y - oneChip v)) 0 hG.2 hH.2
  rw [hFactor] at hWedge
  change linearEquiv (vertexWedge G H x y)
    ((k : ℤ) •
      (oneChip (G := vertexWedge G H x y) (Sum.inl u) -
        oneChip (G := vertexWedge G H x y)
          (wedgeRightVertex G H x y v))) 0
  rw [hTarget]
  rw [hZero] at hWedge
  exact hWedge

/-- Two opposite-side marked graphs with the same `k`-general transmission
period have `k`-general transmission after vertex gluing. -/
theorem kGeneralTransmission_vertexWedge_opposite
    (G H : CFGraph) (x : G.V) (y : H.V) (u : G.V) (v : H.V)
    (k : ℕ)
    (hGconn : _root_.graphConnected G) (hHconn : _root_.graphConnected H)
    (hG : KGeneralTransmission (mark G u x) k)
    (hH : KGeneralTransmission (mark H y v) k) :
    KGeneralTransmission
      (mark (vertexWedge G H x y) (Sum.inl u)
        (wedgeRightVertex G H x y v)) k := by
  let W := mark (vertexWedge G H x y) (Sum.inl u)
    (wedgeRightVertex G H x y v)
  refine ⟨torsionWitness_vertexWedge_opposite G H x y u v k hG.1 hH.1,
    allSubmodular_vertexWedge_opposite G H x y hGconn hHconn u v hG.2.1 hH.2.1,
    ?_⟩
  intro Q
  let D := wedgeRestrictLeftDivisor G H x y Q
  let E := wedgeRestrictRightDivisor G H x y Q
  obtain ⟨tau, hTau, hTauAffine, hTauFinite, hTauCount⟩ := hG.2.2 D
  obtain ⟨sigma, hSigma, hSigmaAffine, hSigmaFinite, hSigmaCount⟩ := hH.2.2 E
  obtain ⟨alpha, beta, hAlpha, hBeta, hWedge⟩ :=
    exists_isTransmissionPermutation_wedgeAddDivisor_star
      G H x y hGconn hHconn D E u v tau sigma hTau hSigma
  have hQ : wedgeAddDivisor G H x y D E = Q :=
    wedgeAddDivisor_restrict G H x y Q
  refine ⟨(alpha ⋆ beta).func, ?_, ?_, ?_, ?_⟩
  · simpa [W, hQ] using hWedge
  · simpa [hAlpha] using (kInversionCount_star_le k alpha beta
      (by simpa [hAlpha] using hTauAffine)
      (by simpa [hBeta] using hSigmaAffine)).1
  · exact kInversions_finite_of_torsionWitness_and_isKAffine
      (torsionWitness_vertexWedge_opposite G H x y u v k hG.1 hH.1)
      (by simpa [hAlpha] using (kInversionCount_star_le k alpha beta
        (by simpa [hAlpha] using hTauAffine)
        (by simpa [hBeta] using hSigmaAffine)).1)
  · have hCount := (kInversionCount_star_le k alpha beta
        (by simpa [hAlpha] using hTauAffine)
        (by simpa [hBeta] using hSigmaAffine)).2
    rw [hAlpha, hBeta] at hCount
    change kInversionCount k (alpha ⋆ beta).func ≤
      (genus (vertexWedge G H x y)).toNat
    rw [genus_vertexWedge]
    rw [Int.toNat_add (genus_nonneg_of_graph_connected G hGconn)
      (genus_nonneg_of_graph_connected H hHconn)]
    exact hCount.trans (Nat.add_le_add hTauCount hSigmaCount)

/-- Common-period general transmission is preserved by a left-associated
marked chain. -/
theorem kGeneralTransmission_markedChain_of_commonPeriod
    (M : MarkedGraph) (L : List MarkedGraph) (k : ℕ)
    (hMconn : _root_.graphConnected M.graph)
    (hMK : KGeneralTransmission (mark M.graph M.left M.right) k)
    (hLconn : ∀ N ∈ L, _root_.graphConnected N.graph)
    (hLK : ∀ N ∈ L, KGeneralTransmission (mark N.graph N.left N.right) k) :
    KGeneralTransmission
      (mark (M.chain L).graph (M.chain L).left (M.chain L).right) k := by
  induction L generalizing M with
  | nil => simpa using hMK
  | cons N rest ih =>
      rw [MarkedGraph.chain_cons]
      apply ih (M.wedge N)
      · exact graph_connected_vertexWedge M.graph N.graph M.right N.left
          hMconn (hLconn N (by simp))
      · simpa [MarkedGraph.wedge] using
          kGeneralTransmission_vertexWedge_opposite M.graph N.graph
            M.right N.left M.left N.right k hMconn (hLconn N (by simp))
            hMK (hLK N (by simp))
      · intro P hP
        exact hLconn P (by simp [hP])
      · intro P hP
        exact hLK P (by simp [hP])

/-- Connectivity is preserved along a marked chain. -/
theorem graph_connected_markedChain
    (M : MarkedGraph) (L : List MarkedGraph)
    (hMconn : _root_.graphConnected M.graph)
    (hLconn : ∀ N ∈ L, _root_.graphConnected N.graph) :
    _root_.graphConnected (M.chain L).graph := by
  induction L generalizing M with
  | nil => simpa using hMconn
  | cons N rest ih =>
      rw [MarkedGraph.chain_cons]
      apply ih (M.wedge N)
      · exact graph_connected_vertexWedge M.graph N.graph M.right N.left
          hMconn (hLconn N (by simp))
      · intro P hP
        exact hLconn P (by simp [hP])

/-- The equal-period chain corollary following Proposition 6.1.  A chain of
connected graphs with common `k`-general transmission is Brill--Noether
general whenever its total genus satisfies the corrected natural threshold
`g + 2 ≤ 2k`. -/
theorem brillNoetherGeneral_markedChain_of_commonPeriod
    (M : MarkedGraph) (L : List MarkedGraph) (k : ℕ)
    (hMconn : _root_.graphConnected M.graph)
    (hMK : KGeneralTransmission (mark M.graph M.left M.right) k)
    (hLconn : ∀ N ∈ L, _root_.graphConnected N.graph)
    (hLK : ∀ N ∈ L, KGeneralTransmission (mark N.graph N.left N.right) k)
    (hthreshold : (genus (M.chain L).graph).toNat + 2 ≤ 2 * k) :
    BrillNoetherGeneral (M.chain L).graph := by
  let T := mark (M.chain L).graph (M.chain L).left (M.chain L).right
  have hTconn : _root_.graphConnected T.graph :=
    graph_connected_markedChain M L hMconn hLconn
  have hTK : KGeneralTransmission T k :=
    kGeneralTransmission_markedChain_of_commonPeriod M L k hMconn hMK hLconn hLK
  have hGenus : genus T.graph = (genus (M.chain L).graph).toNat :=
    (Int.toNat_of_nonneg (genus_nonneg_of_graph_connected T.graph hTconn)).symm
  have hBN := kGeneralTransmission_brillNoetherGeneral hTconn hGenus hTK hthreshold
  exact hBN

end Bananas
