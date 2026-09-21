/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Bananas.CrossOneOff.SignChangingInversions
import LeanPool.BrillNoetherGraphs.Utilities.Transmission.DemazureFactorization

/-!
# Affine simple-reflection reduction

This file supplies the affine Coxeter reduction input isolated in
`AffineReductionData`.  A positive `k`-inversion count gives an adjacent
descent of the inverse permutation.  Simultaneously swapping that adjacent
pair in every residue-period removes exactly one normalized inversion class.
-/

namespace Bananas

open Utilities

/-- The support of the affine simple reflection indexed by `i` modulo `k`. -/
def affineReflectionSupport (k : ℕ) (i : ℤ) : Set ℤ :=
  {n | (k : ℤ) ∣ n - i}

@[simp] theorem mem_affineReflectionSupport_iff (k : ℕ) (i n : ℤ) :
    n ∈ affineReflectionSupport k i ↔ (k : ℤ) ∣ n - i := Iff.rfl

theorem affineReflectionSupport_noConsecutive
    (k : ℕ) (hk : 2 ≤ k) (i : ℤ) :
    Transpositions.NoConsecutive (affineReflectionSupport k i) := by
  intro n hn hsucc
  have hkz : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have : (k : ℤ) ∣ 1 := by
    simpa only [sub_sub_sub_cancel_right, add_sub_cancel_left] using
      (dvd_sub hsucc hn)
  have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) this
  omega

theorem affineReflectionSupport_congr
    (k : ℕ) (i : ℤ) {l₁ l₂ : ℤ}
    (h₁ : l₁ ∈ affineReflectionSupport k i)
    (h₂ : l₂ ∈ affineReflectionSupport k i) :
    (k : ℤ) ∣ l₂ - l₁ := by
  simpa only [sub_sub_sub_cancel_right] using (dvd_sub h₂ h₁)

/-- The ASP permutation implementing one affine simple reflection. -/
noncomputable def affineReflection (k : ℕ) (i : ℤ) (hk : 2 ≤ k) : AspPerm :=
  Transpositions.sigma (affineReflectionSupport k i)
    (affineReflectionSupport_noConsecutive k hk i)

theorem affineReflection_apply_of_mem
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) {n : ℤ}
    (hn : n ∈ affineReflectionSupport k i) :
    affineReflection k i hk n = n + 1 := by
  change Transpositions.sigmaFun (affineReflectionSupport k i) n = n + 1
  simp [Transpositions.sigmaFun, hn]

theorem affineReflection_apply_of_pred_mem
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) {n : ℤ}
    (hn : n - 1 ∈ affineReflectionSupport k i) :
    affineReflection k i hk n = n - 1 := by
  have hnot : n ∉ affineReflectionSupport k i := by
    intro hmem
    exact affineReflectionSupport_noConsecutive k hk i (n - 1) hn
      (by simpa only [sub_add_cancel] using hmem)
  change Transpositions.sigmaFun (affineReflectionSupport k i) n = n - 1
  simp [Transpositions.sigmaFun, hnot, hn]

theorem affineReflection_apply_of_neither
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) {n : ℤ}
    (hn : n ∉ affineReflectionSupport k i)
    (hpred : n - 1 ∉ affineReflectionSupport k i) :
    affineReflection k i hk n = n := by
  change Transpositions.sigmaFun (affineReflectionSupport k i) n = n
  simp [Transpositions.sigmaFun, hn, hpred]

theorem affineReflection_inversion_iff
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) {a b : ℤ} (hab : a < b) :
    affineReflection k i hk b < affineReflection k i hk a ↔
      a ∈ affineReflectionSupport k i ∧ b = a + 1 := by
  by_cases ha : a ∈ affineReflectionSupport k i
  · have hsa : affineReflection k i hk a = a + 1 :=
      affineReflection_apply_of_mem k i hk ha
    by_cases hba : b = a + 1
    · subst b
      have hsb : affineReflection k i hk (a + 1) = a := by
        have := affineReflection_apply_of_pred_mem k i hk
          (n := a + 1) (by simpa only [add_sub_cancel_right] using ha)
        simpa only [add_sub_cancel_right] using this
      constructor
      · intro _
        exact ⟨ha, rfl⟩
      · intro _
        rw [hsa, hsb]
        omega
    · have hbgt : a + 1 < b := by omega
      have hsblower : b - 1 ≤ affineReflection k i hk b := by
        by_cases hb : b ∈ affineReflectionSupport k i
        · rw [affineReflection_apply_of_mem k i hk hb]
          omega
        · by_cases hbpred : b - 1 ∈ affineReflectionSupport k i
          · rw [affineReflection_apply_of_pred_mem k i hk hbpred]
          · rw [affineReflection_apply_of_neither k i hk hb hbpred]
            omega
      constructor
      · intro hbad
        rw [hsa] at hbad
        omega
      · rintro ⟨-, h⟩
        exact False.elim (hba h)
  · have hsaUpper : affineReflection k i hk a ≤ a := by
      by_cases hapred : a - 1 ∈ affineReflectionSupport k i
      · rw [affineReflection_apply_of_pred_mem k i hk hapred]
        omega
      · rw [affineReflection_apply_of_neither k i hk ha hapred]
    have hsbLower : b - 1 ≤ affineReflection k i hk b := by
      by_cases hb : b ∈ affineReflectionSupport k i
      · rw [affineReflection_apply_of_mem k i hk hb]
        omega
      · by_cases hbpred : b - 1 ∈ affineReflectionSupport k i
        · rw [affineReflection_apply_of_pred_mem k i hk hbpred]
        · rw [affineReflection_apply_of_neither k i hk hb hbpred]
          omega
    constructor
    · intro hbad
      have hba : a ≤ b - 1 := by omega
      omega
    · rintro ⟨h, -⟩
      exact False.elim (ha h)

private theorem affineReflection_involutive
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) (n : ℤ) :
    affineReflection k i hk (affineReflection k i hk n) = n := by
  by_cases hn : n ∈ affineReflectionSupport k i
  · rw [affineReflection_apply_of_mem k i hk hn]
    have hpred : (n + 1 : ℤ) - 1 ∈ affineReflectionSupport k i := by
      simpa only [add_sub_cancel_right] using hn
    rw [affineReflection_apply_of_pred_mem k i hk hpred]
    omega
  · by_cases hpred : n - 1 ∈ affineReflectionSupport k i
    · rw [affineReflection_apply_of_pred_mem k i hk hpred]
      rw [affineReflection_apply_of_mem k i hk hpred]
      omega
    · rw [affineReflection_apply_of_neither k i hk hn hpred]
      exact affineReflection_apply_of_neither k i hk hn hpred

private theorem affineReflectionSupport_add_period_iff
    (k : ℕ) (i n : ℤ) :
    n + k ∈ affineReflectionSupport k i ↔
      n ∈ affineReflectionSupport k i := by
  constructor <;> intro h
  · have hkDvd : (k : ℤ) ∣ (k : ℤ) := dvd_refl _
    have hdiff := dvd_sub h hkDvd
    have heq : (n + (k : ℤ) - i) - k = n - i := by ring
    rw [heq] at hdiff
    exact hdiff
  · have hkDvd : (k : ℤ) ∣ (k : ℤ) := dvd_refl _
    have hsum := dvd_add h hkDvd
    have heq : (n - i) + (k : ℤ) = n + k - i := by ring
    rw [heq] at hsum
    exact hsum

theorem affineReflection_isKAffine
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) :
    IsKAffine k (affineReflection k i hk).func := by
  intro n
  by_cases hn : n ∈ affineReflectionSupport k i
  · have hnk : n + k ∈ affineReflectionSupport k i :=
      (affineReflectionSupport_add_period_iff k i n).2 hn
    rw [affineReflection_apply_of_mem k i hk hn,
      affineReflection_apply_of_mem k i hk hnk]
    omega
  · by_cases hpred : n - 1 ∈ affineReflectionSupport k i
    · have hpredk : (n + k) - 1 ∈ affineReflectionSupport k i := by
        have := (affineReflectionSupport_add_period_iff k i (n - 1)).2 hpred
        convert this using 1
        omega
      rw [affineReflection_apply_of_pred_mem k i hk hpred,
        affineReflection_apply_of_pred_mem k i hk hpredk]
      omega
    · have hnk : n + k ∉ affineReflectionSupport k i := by
        intro h
        exact hn ((affineReflectionSupport_add_period_iff k i n).1 h)
      have hpredk : (n + k) - 1 ∉ affineReflectionSupport k i := by
        intro h
        apply hpred
        have := (affineReflectionSupport_add_period_iff k i (n - 1)).1
          (by
            convert h using 1
            omega)
        exact this
      rw [affineReflection_apply_of_neither k i hk hn hpred,
        affineReflection_apply_of_neither k i hk hnk hpredk]

theorem IsKAffine.aspPerm_inv {k : ℕ} {β : AspPerm}
    (hβ : IsKAffine k β.func) : IsKAffine k (β⁻¹).func := by
  intro n
  apply β.injective
  rw [β.mul_inv_cancel_eval, hβ, β.mul_inv_cancel_eval]

/-- A single periodic affine simple reflection has at most one normalized
inversion class. -/
theorem kInversionCount_affineReflection_le_one
    (k : ℕ) (i : ℤ) (hk : 2 ≤ k) :
    kInversionCount k (affineReflection k i hk).func ≤ 1 := by
  have hkpos : 0 < k := by omega
  have hfinite := kInversions_finite_of_isKAffine hkpos
    (affineReflection_isKAffine k i hk)
  apply (Set.ncard_le_one hfinite).mpr
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd
  change a < b ∧ affineReflection k i hk a > affineReflection k i hk b ∧
    0 ≤ a ∧ a < k at hab
  change c < d ∧ affineReflection k i hk c > affineReflection k i hk d ∧
    0 ≤ c ∧ c < k at hcd
  obtain ⟨hAB, hInvAB, ha0, hak⟩ := hab
  obtain ⟨hCD, hInvCD, hc0, hck⟩ := hcd
  obtain ⟨ha, hb⟩ := (affineReflection_inversion_iff k i hk hAB).mp hInvAB
  obtain ⟨hc, hd⟩ := (affineReflection_inversion_iff k i hk hCD).mp hInvCD
  have hDvd : (k : ℤ) ∣ a - c := by
    have h := affineReflectionSupport_congr k i ha hc
    rw [show a - c = -(c - a) by ring]
    exact dvd_neg.mpr h
  have hAbsLt : (a - c).natAbs < (k : ℤ).natAbs := by
    have hCast : |a - c| < |(k : ℤ)| := by
      have hKabs : |(k : ℤ)| = (k : ℤ) :=
        abs_of_pos (by exact_mod_cast hkpos)
      rw [hKabs, abs_lt]
      omega
    have hCast' : ((a - c).natAbs : ℤ) < (k : ℤ) := by
      calc
        ((a - c).natAbs : ℤ) = |a - c| := Int.natCast_natAbs _
        _ < |(k : ℤ)| := hCast
        _ = (k : ℤ) := abs_of_pos (by exact_mod_cast hkpos)
    have hNat : (a - c).natAbs < k := by exact_mod_cast hCast'
    simpa using hNat
  have hzero : a - c = 0 :=
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hDvd hAbsLt
  have hac : a = c := by omega
  subst c
  subst b
  subst d
  rfl

private theorem IsKAffine.left_mul_affineReflection
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) :
    IsKAffine k (affineReflection k i hk * β).func := by
  intro n
  simp only [AspPerm.mul_apply]
  rw [hβ n]
  exact affineReflection_isKAffine k i hk (β n)

/-- The normalized inversion class removed by a chosen affine left descent. -/
def affineExceptionalInversions
    (k : ℕ) (i : ℤ) (β : AspPerm) : Set (ℤ × ℤ) :=
  {p | p ∈ kInversions k β.func ∧
    β p.2 ∈ affineReflectionSupport k i ∧ β p.1 = β p.2 + 1}

private theorem inverse_descent_on_affineReflectionSupport
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hi : β⁻¹ (i + 1) < β⁻¹ i)
    {l : ℤ} (hl : l ∈ affineReflectionSupport k i) :
    β⁻¹ (l + 1) < β⁻¹ l := by
  obtain ⟨q, hq⟩ := hl
  rw [mul_comm (k : ℤ) q] at hq
  have hlEq : l = i + q * (k : ℤ) := by omega
  have hInvAffine := hβ.aspPerm_inv
  have h1 := hInvAffine.iterate_int (i + 1) q
  have h0 := hInvAffine.iterate_int i q
  rw [show l + 1 = (i + 1) + q * (k : ℤ) by omega,
    hlEq, h1, h0]
  omega

private theorem kInversions_left_mul_affineReflection
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) (hi : β⁻¹ (i + 1) < β⁻¹ i) :
    kInversions k (affineReflection k i hk * β).func =
      kInversions k β.func \ affineExceptionalInversions k i β := by
  ext p
  rcases p with ⟨x, y⟩
  simp only [kInversions, Set.mem_ofPred_eq, AspPerm.mul_apply,
    Set.mem_sdiff, affineExceptionalInversions]
  constructor
  · rintro ⟨hxy, hnew, hx0, hxk⟩
    have hβne : β x ≠ β y := by
      intro h
      exact (by omega : x ≠ y) (β.injective h)
    have hold : β y < β x := by
      rcases lt_or_gt_of_ne hβne with hlt | hlt
      · have href := (affineReflection_inversion_iff k i hk hlt).1 hnew
        have hdesc := inverse_descent_on_affineReflectionSupport hβ i hi href.1
        rw [← href.2, β.inv_mul_cancel_eval, β.inv_mul_cancel_eval] at hdesc
        omega
      · exact hlt
    refine ⟨⟨hxy, hold, hx0, hxk⟩, ?_⟩
    rintro ⟨-, hsupport, hadj⟩
    have href := (affineReflection_inversion_iff k i hk hold).2
      ⟨hsupport, hadj⟩
    omega
  · rintro ⟨⟨hxy, hold, hx0, hxk⟩, hnotExceptional⟩
    refine ⟨hxy, ?_, hx0, hxk⟩
    have hne : affineReflection k i hk (β x) ≠
        affineReflection k i hk (β y) := by
      intro h
      have h' := congrArg (affineReflection k i hk) h
      rw [affineReflection_involutive, affineReflection_involutive] at h'
      exact (by omega : β x ≠ β y) h'
    by_contra hnot
    have hrev : affineReflection k i hk (β x) <
        affineReflection k i hk (β y) := by omega
    have href := (affineReflection_inversion_iff k i hk hold).1 hrev
    apply hnotExceptional
    exact ⟨⟨hxy, hold, hx0, hxk⟩, href.1, href.2⟩

private theorem affineExceptionalInversions_subsingleton
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) :
    (affineExceptionalInversions k i β).Subsingleton := by
  rintro ⟨x₁, y₁⟩ h₁ ⟨x₂, y₂⟩ h₂
  rcases h₁ with ⟨⟨hx₁y₁, -, hx₁0, hx₁k⟩, hs₁, hadj₁⟩
  rcases h₂ with ⟨⟨hx₂y₂, -, hx₂0, hx₂k⟩, hs₂, hadj₂⟩
  change β y₁ ∈ affineReflectionSupport k i at hs₁
  change β x₁ = β y₁ + 1 at hadj₁
  change β y₂ ∈ affineReflectionSupport k i at hs₂
  change β x₂ = β y₂ + 1 at hadj₂
  have hkz : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hdvd := affineReflectionSupport_congr k i hs₁ hs₂
  obtain ⟨q, hq⟩ := hdvd
  rw [mul_comm (k : ℤ) q] at hq
  have hyVal : β (y₁ + q * (k : ℤ)) = β y₂ := by
    rw [hβ.iterate_int y₁ q]
    omega
  have hy : y₂ = y₁ + q * (k : ℤ) := (β.injective hyVal).symm
  have hxVal : β (x₁ + q * (k : ℤ)) = β x₂ := by
    rw [hβ.iterate_int x₁ q]
    omega
  have hx : x₂ = x₁ + q * (k : ℤ) := (β.injective hxVal).symm
  have hqzero : q = 0 := by
    rcases lt_trichotomy q 0 with hneg | hzero | hpos
    · have hprod : q * (k : ℤ) ≤ -(k : ℤ) := by nlinarith
      omega
    · exact hzero
    · have hprod : (k : ℤ) ≤ q * (k : ℤ) := by nlinarith
      omega
  subst q
  simp only [zero_mul, add_zero] at hx hy
  exact Prod.ext hx.symm hy.symm

private theorem affineExceptionalInversions_nonempty
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) (hi : β⁻¹ (i + 1) < β⁻¹ i) :
    (affineExceptionalInversions k i β).Nonempty := by
  let a : ℤ := β⁻¹ (i + 1)
  let b : ℤ := β⁻¹ i
  let q : ℤ := -(a / (k : ℤ))
  let x : ℤ := a + q * (k : ℤ)
  let y : ℤ := b + q * (k : ℤ)
  have hkz : (0 : ℤ) < k := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hk)
  have hxmod : x = a % (k : ℤ) := by
    dsimp only [x, q]
    rw [Int.emod_def]
    ring
  have hx0 : 0 ≤ x := by
    rw [hxmod]
    exact Int.emod_nonneg a (ne_of_gt hkz)
  have hxk : x < (k : ℤ) := by
    rw [hxmod]
    exact Int.emod_lt_of_pos a hkz
  have hxy : x < y := by
    dsimp only [x, y, a, b]
    omega
  have hβx : β x = i + 1 + q * (k : ℤ) := by
    dsimp only [x, a]
    rw [hβ.iterate_int, β.mul_inv_cancel_eval]
  have hβy : β y = i + q * (k : ℤ) := by
    dsimp only [y, b]
    rw [hβ.iterate_int, β.mul_inv_cancel_eval]
  refine ⟨(x, y), ⟨⟨hxy, ?_, hx0, hxk⟩, ?_, ?_⟩⟩
  · rw [hβx, hβy]
    omega
  · rw [hβy]
    refine ⟨q, ?_⟩
    ring
  · rw [hβx, hβy]
    omega

theorem kInversionCount_left_mul_affineReflection_add_one
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) (hi : β⁻¹ (i + 1) < β⁻¹ i) :
    kInversionCount k (affineReflection k i hk * β).func + 1 =
      kInversionCount k β.func := by
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hfin := kInversions_finite_of_isKAffine hkpos hβ
  obtain ⟨e, he⟩ := affineExceptionalInversions_nonempty hβ i hk hi
  have hsub := affineExceptionalInversions_subsingleton hβ i hk
  have hE : affineExceptionalInversions k i β = {e} := by
    ext p
    constructor
    · intro hp
      exact Set.mem_singleton_iff.mpr (hsub hp he)
    · rintro rfl
      exact he
  rw [kInversionCount, kInversionCount,
    kInversions_left_mul_affineReflection hβ i hk hi, hE]
  exact Set.ncard_sdiff_singleton_add_one he.1 hfin

private theorem two_le_of_kInversionCount_pos
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (hpos : 0 < kInversionCount k β.func) : 2 ≤ k := by
  have hkpos : 0 < k := by
    by_contra h
    have hk : k = 0 := by omega
    subst k
    unfold kInversionCount kInversions at hpos
    change 0 < ({p : ℤ × ℤ | p.1 < p.2 ∧ β p.2 < β p.1 ∧
      0 ≤ p.1 ∧ p.1 < (0 : ℤ)} : Set (ℤ × ℤ)).ncard at hpos
    have hempty :
        ({p : ℤ × ℤ | p.1 < p.2 ∧ β p.2 < β p.1 ∧
          0 ≤ p.1 ∧ p.1 < (0 : ℤ)} : Set (ℤ × ℤ)) = ∅ := by
      ext p
      simp
    rw [hempty, Set.ncard_empty] at hpos
    omega
  have hfin := kInversions_finite_of_isKAffine hkpos hβ
  have hnonempty : (kInversions k β.func).Nonempty :=
    (Set.ncard_pos hfin).mp hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hnonempty
  rcases hxy with ⟨hxy, hinv, hx0, hxk⟩
  by_contra hnot
  have hkone : k = 1 := by omega
  subst k
  have hx : x = 0 := by omega
  subst x
  have hiter := hβ.iterate_int 0 y
  norm_num at hiter
  change β y < β 0 at hinv
  rw [hiter] at hinv
  omega

private theorem affineReflection_star_remainder
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (i : ℤ) (hk : 2 ≤ k) (hi : β⁻¹ (i + 1) < β⁻¹ i) :
    β = affineReflection k i hk ⋆ (affineReflection k i hk * β) := by
  let s := affineReflection k i hk
  let β' := s * β
  have hss : s * s = 1 := by
    apply (AspPerm.ext).2
    funext n
    change affineReflection k i hk (affineReflection k i hk n) = n
    exact affineReflection_involutive k i hk n
  have hmul : s * β' = β := by
    calc
      s * β' = (s * s) * β := by simp only [β', mul_assoc]
      _ = β := by rw [hss, one_mul]
  have hred : AspPerm.ReducedProduct s β' := by
    unfold AspPerm.ReducedProduct
    apply Set.disjoint_left.mpr
    rintro ⟨a, b⟩ hs hβinv
    have hsMem := (affineReflection_inversion_iff k i hk hs.1).1 hs.2
    have hdesc := inverse_descent_on_affineReflectionSupport hβ i hi hsMem.1
    have hβ'inv : β'⁻¹ = β⁻¹ * s := by
      simp only [β', mul_inv_rev]
      have hsInv : s⁻¹ = s := by
        apply (AspPerm.ext).2
        funext n
        apply s.injective
        rw [s.mul_inv_cancel_eval]
        change n = affineReflection k i hk (affineReflection k i hk n)
        exact (affineReflection_involutive k i hk n).symm
      rw [hsInv]
    have hbad := hβinv.2
    rw [hβ'inv] at hbad
    simp only [AspPerm.mul_apply] at hbad
    have hsa : s a = a + 1 :=
      affineReflection_apply_of_mem k i hk hsMem.1
    have hsb : s b = a := by
      rw [hsMem.2]
      have hpred : (a + 1 : ℤ) - 1 ∈ affineReflectionSupport k i := by
        simpa only [add_sub_cancel_right] using hsMem.1
      have := affineReflection_apply_of_pred_mem k i hk hpred
      simpa only [add_sub_cancel_right] using this
    rw [hsa, hsb] at hbad
    omega
  have hstar :=
    (ReducedProducts.star_eq_mul_iff_reducedProduct s β').2 hred
  rw [hstar, hmul]

/-- A positive affine inversion count admits a direct reduction by one
periodic affine simple reflection.  This is the concrete version of the
`AffineReductionData.reduce` field; exposing the residue index is useful when
the other factor in a Demazure product must be compared with the same
reflection. -/
theorem exists_affineReflection_reduction
    {k : ℕ} {β : AspPerm} (hβ : IsKAffine k β.func)
    (hpos : 0 < kInversionCount k β.func) :
    ∃ (i : ℤ) (hk : 2 ≤ k) (β' : AspPerm),
      β = affineReflection k i hk ⋆ β' ∧
      IsKAffine k β'.func ∧
      kInversionCount k β'.func + 1 = kInversionCount k β.func := by
  have hk : 2 ≤ k := two_le_of_kInversionCount_pos hβ hpos
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hfin := kInversions_finite_of_isKAffine hkpos hβ
  have hnonempty : (kInversions k β.func).Nonempty :=
    (Set.ncard_pos hfin).mp hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hnonempty
  have hinv : (x, y) ∈ inv_set β.func := ⟨hxy.1, hxy.2.1⟩
  have hinvInv := (β.inv_set_inverse x y).mp hinv
  obtain ⟨i, -, -, hi⟩ :=
    AspPerm.exists_adjacent_descent_of_mem_invSet (β⁻¹) hinvInv
  let β' := affineReflection k i hk * β
  refine ⟨i, hk, β', ?_, ?_, ?_⟩
  · exact affineReflection_star_remainder hβ i hk hi
  · exact hβ.left_mul_affineReflection i hk
  · exact kInversionCount_left_mul_affineReflection_add_one hβ i hk hi

/-- The affine simple-reflection reduction required by Proposition 6.13. -/
theorem affineReductionData (k : ℕ) : AffineReductionData k := by
  refine ⟨?_⟩
  intro β hβ hpos
  have hk : 2 ≤ k := two_le_of_kInversionCount_pos hβ hpos
  have hkpos : 0 < k := lt_of_lt_of_le (by omega) hk
  have hfin := kInversions_finite_of_isKAffine hkpos hβ
  have hnonempty : (kInversions k β.func).Nonempty :=
    (Set.ncard_pos hfin).mp hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hnonempty
  have hinv : (x, y) ∈ inv_set β.func := ⟨hxy.1, hxy.2.1⟩
  have hinvInv := (β.inv_set_inverse x y).mp hinv
  obtain ⟨i, -, -, hi⟩ :=
    AspPerm.exists_adjacent_descent_of_mem_invSet (β⁻¹) hinvInv
  let S := affineReflectionSupport k i
  let hS := affineReflectionSupport_noConsecutive k hk i
  let β' := affineReflection k i hk * β
  refine ⟨S, hS, β', ?_, ?_, ?_, ?_⟩
  · intro l₁ hl₁ l₂ hl₂
    exact affineReflectionSupport_congr k i hl₁ hl₂
  · change β = affineReflection k i hk ⋆ β'
    exact affineReflection_star_remainder hβ i hk hi
  · exact hβ.left_mul_affineReflection i hk
  · exact kInversionCount_left_mul_affineReflection_add_one hβ i hk hi

/-- Paper Proposition 6.13 (`prop:sciInvStar`), with the affine Coxeter
reduction discharged unconditionally. -/
theorem sci_star_le
    (k : ℕ) (α β : AspPerm)
    (hβ : IsKAffine k β.func)
    (hbudget : (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) < (k : ℤ)) :
    (sci (α ⋆ β).func : ℤ) ≤
      (sci α.func : ℤ) + (kInversionCount k β.func : ℤ) :=
  sci_star_le_of_affineReductionData k (affineReductionData k) α β hβ hbudget


end Bananas
