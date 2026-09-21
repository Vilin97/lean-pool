/-
Copyright (c) 2026 Christopher Birkbeck, Alex Torzewski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Birkbeck, Alex Torzewski
-/

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.ZeroHeadTate
import LeanPool.UniformSheafyTateDomains.AdicSpaces.WP.Tail

/-!
# Inverting `W` collapses the parity constraint

([hrw-decomposition] block B, the `W ∉ 𝔭` route.)  The parity weight of any
head multi-index is at most `M := ∑_{n ≤ N} w n`, so `W^M · 𝒜_N⁰ ⊆ 𝒜_N`
(zero-weight head shifted into the weighted head).  Consequently the
`W`-inverted weighted head and the `W`-inverted zero-weight head agree: the
canonical `Localization.Away` of the zero-weight head at `W` satisfies the
universal property of the `W`-localization of the weighted head along the
support inclusion, giving
`Localization.Away (WaHead K w N) ≃ Localization.Away (WaHead K 0 N)`.
-/

@[expose] public section

namespace WeightedParity

open FiniteJetOver

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
  [CompleteSpace K]
variable (w : ℕ → ℕ) (N : ℕ)

/-- The weighted head support sits inside the zero-weight head support. -/
theorem wpHeadSupport_le_zeroWeight :
    wpHeadSupport K w N ≤ wpHeadSupport K (fun _ => 0) N := by
  intro f hf t ht
  refine hf t fun hh => ht ⟨?_, hh.2⟩
  show WPMem (fun _ => 0) t
  simp [WPMem, wpWeight]

/-- The uniform weight bound of the `N`-th head. -/
noncomputable def headWeightBound : ℕ := ∑ n ∈ Finset.Icc 1 N, w n

/-- Any multi-index supported in `{0,…,N}` has parity weight at most the
uniform bound. -/
theorem wpWeight_le_headWeightBound {t : ℕ →₀ ℕ}
    (ht : ∀ n, N < n → t n = 0) :
    wpWeight w t ≤ headWeightBound w N := by
  classical
  rw [wpWeight, headWeightBound]
  have h1 : ∀ n ∈ t.support, n ∉ Finset.Icc 1 N →
      (if t n % 2 = 1 ∧ n ≠ 0 then w n else 0) = 0 := by
    intro n hn hnI
    rw [Finset.mem_Icc, not_and_or] at hnI
    rcases hnI with h | h
    · rw [if_neg]
      rintro ⟨-, hne⟩
      omega
    · rw [Finsupp.mem_support_iff] at hn
      exact absurd (ht n (by omega)) hn
  calc ∑ n ∈ t.support, (if t n % 2 = 1 ∧ n ≠ 0 then w n else 0)
      = ∑ n ∈ t.support ∩ Finset.Icc 1 N,
          (if t n % 2 = 1 ∧ n ≠ 0 then w n else 0) := by
        refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
        intro n hn hni
        exact h1 n hn fun hI => hni (Finset.mem_inter.mpr ⟨hn, hI⟩)
    _ ≤ ∑ n ∈ t.support ∩ Finset.Icc 1 N, w n :=
        Finset.sum_le_sum fun n _ => by split <;> omega
    _ ≤ ∑ n ∈ Finset.Icc 1 N, w n :=
        Finset.sum_le_sum_of_subset Finset.inter_subset_right

/-- The parity weight only depends on the exponents away from index `0`. -/
theorem wpWeight_eq_of_eq_off_zero {t s : ℕ →₀ ℕ}
    (h : ∀ n, n ≠ 0 → t n = s n) : wpWeight w t = wpWeight w s := by
  classical
  rw [wpWeight_eq_sum_subset w (Finset.subset_union_left
    (s₂ := s.support)), wpWeight_eq_sum_subset w (Finset.subset_union_right
    (s₁ := t.support))]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [h n hn]

/-- **The uniform shift**: `W^M` times a zero-weight head element lies in the
weighted head. -/
noncomputable def shiftIntoHead (f : WPHead K (fun _ => 0) N) :
    WPHead K w N :=
  ⟨(WaHead K w N).1 ^ headWeightBound w N * f.1, by
    intro t ht
    have hW : ((WaHead K w N).1 ^ headWeightBound w N : Amb K).1 =
        MvPowerSeries.monomial
          (Finsupp.single 0 (headWeightBound w N)) (1 : K) := by
      have hstep : ∀ m : ℕ, ((WaHead K w N).1 ^ m : Amb K).1 =
          MvPowerSeries.monomial (Finsupp.single 0 m) (1 : K) := by
        intro m
        induction m with
        | zero =>
          rw [pow_zero, Finsupp.single_zero]
          exact (MvPowerSeries.monomial_zero_one (R := K)).symm
        | succ k ih =>
          rw [pow_succ]
          show (((WaHead K w N).1 ^ k : Amb K).1 *
            ((WaHead K w N).1 : Amb K).1) = _
          rw [ih, show ((WaHead K w N).1 : Amb K).1 =
            MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K) from rfl,
            MvPowerSeries.monomial_mul_monomial, ← Finsupp.single_add,
            one_mul]
      exact hstep _
    show MvPowerSeries.coeff t
      (((WaHead K w N).1 ^ headWeightBound w N : Amb K).1 * f.1.1) = 0
    rw [hW, MvPowerSeries.coeff_monomial_mul]
    by_cases hle : Finsupp.single 0 (headWeightBound w N) ≤ t
    · rw [if_pos hle, one_mul]
      by_cases hz : HeadMem (fun _ => 0) N
          (t - Finsupp.single 0 (headWeightBound w N))
      · exfalso
        refine ht ⟨?_, fun n hn => ?_⟩
        · show wpWeight w t ≤ t 0
          have hoff : ∀ n, n ≠ 0 →
              t n = (t - Finsupp.single 0 (headWeightBound w N) :
                ℕ →₀ ℕ) n := by
            intro n hn
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg
              (fun h => hn h.symm), Nat.sub_zero]
          have hwt : wpWeight w t =
              wpWeight w (t - Finsupp.single 0 (headWeightBound w N)) :=
            wpWeight_eq_of_eq_off_zero w hoff
          have hb : wpWeight w
              (t - Finsupp.single 0 (headWeightBound w N)) ≤
              headWeightBound w N :=
            wpWeight_le_headWeightBound w N hz.2
          have ht0 : headWeightBound w N ≤ t 0 := by
            have := hle 0
            simpa using this
          omega
        · have h2 := hz.2 n hn
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg
            (fun h => (by omega : n ≠ 0) h.symm), Nat.sub_zero] at h2
          exact h2
      · exact f.2 _ hz
    · rw [if_neg hle]⟩

theorem shiftIntoHead_val (f : WPHead K (fun _ => 0) N) :
    ((shiftIntoHead w N f : WPHead K w N) : Amb K) =
      (WaHead K w N).1 ^ headWeightBound w N * f.1 := rfl

/-- The inclusion of the weighted head into the zero-weight head. -/
noncomputable def headToZeroHead : WPHead K w N →+* WPHead K (fun _ => 0) N :=
  Subring.inclusion (wpHeadSupport_le_zeroWeight w N)

theorem headToZeroHead_injective :
    Function.Injective (headToZeroHead (K := K) w N) :=
  Subring.inclusion_injective _

@[simp] theorem headToZeroHead_waHead :
    headToZeroHead w N (WaHead K w N) = WaHead K (fun _ => 0) N := rfl

theorem headToZeroHead_shiftIntoHead (f : WPHead K (fun _ => 0) N) :
    headToZeroHead w N (shiftIntoHead w N f) =
      WaHead K (fun _ => 0) N ^ headWeightBound w N * f := by
  refine Subtype.ext ?_
  show (WaHead K w N).1 ^ headWeightBound w N * f.1 =
    ((WaHead K (fun _ => 0) N ^ headWeightBound w N *
      f : WPHead K (fun _ => 0) N) : Amb K)
  rfl

/-- The `W`-variable of the zero-weight head is nonzero. -/
theorem waHead_zero_ne_zero : (WaHead K (fun _ => 0) N) ≠ 0 := by
  intro h
  have h1 : MvPowerSeries.coeff (Finsupp.single 0 1)
      ((WaHead K (fun _ => 0) N : WPHead K (fun _ => 0) N) : Amb K).1 =
      MvPowerSeries.coeff (Finsupp.single 0 1)
        (((0 : WPHead K (fun _ => 0) N) : Amb K)).1 := by
    rw [h]
  rw [show ((WaHead K (fun _ => 0) N : WPHead K (fun _ => 0) N) :
      Amb K).1 = MvPowerSeries.monomial (Finsupp.single 0 1) (1 : K)
      from rfl,
    show (((0 : WPHead K (fun _ => 0) N) : Amb K)).1 = 0 from rfl,
    MvPowerSeries.coeff_monomial_same, _root_.map_zero] at h1
  exact one_ne_zero h1

section AwayEquiv

/-- The zero-head `W`-localization as a weighted-head algebra: include, then
localize. -/
noncomputable def headAwayAlgebra :
    Algebra (WPHead K w N) (Localization.Away (WaHead K (fun _ => 0) N)) :=
  ((algebraMap (WPHead K (fun _ => 0) N)
    (Localization.Away (WaHead K (fun _ => 0) N))).comp
    (headToZeroHead w N)).toAlgebra

/-- **The zero-head `W`-localization is the weighted head's `W`-localization**
(the uniform shift provides the fractions). -/
theorem isLocalization_away_headW :
    letI : Algebra (WPHead K w N)
        (Localization.Away (WaHead K (fun _ => 0) N)) :=
      headAwayAlgebra w N
    IsLocalization.Away (WaHead K w N)
      (Localization.Away (WaHead K (fun _ => 0) N)) := by
  letI : Algebra (WPHead K w N)
      (Localization.Away (WaHead K (fun _ => 0) N)) :=
    headAwayAlgebra w N
  refine ⟨fun y => ?_, fun z => ?_, fun {a b} h => ?_⟩
  · -- images of powers of W are units
    obtain ⟨k, hk⟩ := y.2
    have h1 : algebraMap (WPHead K w N)
        (Localization.Away (WaHead K (fun _ => 0) N)) y.1 =
        algebraMap (WPHead K (fun _ => 0) N)
          (Localization.Away (WaHead K (fun _ => 0) N))
          (WaHead K (fun _ => 0) N ^ k) := by
      show algebraMap (WPHead K (fun _ => 0) N)
        (Localization.Away (WaHead K (fun _ => 0) N))
        (headToZeroHead w N y.1) = _
      rw [← hk, map_pow, headToZeroHead_waHead]
    rw [h1]
    exact IsLocalization.map_units
      (M := Submonoid.powers (WaHead K (fun _ => 0) N)) _
      ⟨WaHead K (fun _ => 0) N ^ k, k, rfl⟩
  · -- surjectivity: the uniform shift clears denominators
    obtain ⟨⟨f, s⟩, hz⟩ := IsLocalization.surj
      (M := Submonoid.powers (WaHead K (fun _ => 0) N)) z
    obtain ⟨k, hk⟩ := s.2
    refine ⟨⟨shiftIntoHead w N f,
      ⟨WaHead K w N ^ (k + headWeightBound w N),
        k + headWeightBound w N, rfl⟩⟩, ?_⟩
    show z * algebraMap (WPHead K (fun _ => 0) N)
        (Localization.Away (WaHead K (fun _ => 0) N))
        (headToZeroHead w N (WaHead K w N ^ (k + headWeightBound w N))) =
      algebraMap (WPHead K (fun _ => 0) N)
        (Localization.Away (WaHead K (fun _ => 0) N))
        (headToZeroHead w N (shiftIntoHead w N f))
    rw [map_pow, headToZeroHead_waHead, headToZeroHead_shiftIntoHead,
      pow_add, map_mul, map_mul, ← mul_assoc]
    have hk' : WaHead K (fun _ => 0) N ^ k = s.1 := hk
    have h2 : z * algebraMap (WPHead K (fun _ => 0) N)
        (Localization.Away (WaHead K (fun _ => 0) N))
        (WaHead K (fun _ => 0) N ^ k) =
        algebraMap (WPHead K (fun _ => 0) N)
          (Localization.Away (WaHead K (fun _ => 0) N)) f := by
      rw [hk']
      exact hz
    rw [h2, mul_comm]
  · -- injectivity up to powers: the zero-head is a domain
    haveI hdom : IsDomain (WPHead K (fun _ => 0) N) := by
      haveI : IsDomain (MvPowerSeries ℕ K) := NoZeroDivisors.to_isDomain _
      let φ : WPHead K (fun _ => 0) N →+* MvPowerSeries ℕ K :=
        { toFun := fun x => (x : Amb K).1
          map_one' := rfl
          map_mul' := fun a b => rfl
          map_zero' := rfl
          map_add' := fun a b => rfl }
      exact Function.Injective.isDomain φ (fun a b h =>
        Subtype.ext (Subtype.ext h))
    have hinj2 : Function.Injective (algebraMap (WPHead K (fun _ => 0) N)
        (Localization.Away (WaHead K (fun _ => 0) N))) := by
      exact IsLocalization.injective
        (M := Submonoid.powers (WaHead K (fun _ => 0) N))
        (Localization.Away (WaHead K (fun _ => 0) N))
        (powers_le_nonZeroDivisors_of_noZeroDivisors
          (waHead_zero_ne_zero N))
    have h3 : headToZeroHead w N a = headToZeroHead w N b := by
      apply hinj2
      exact h
    exact ⟨1, by rw [headToZeroHead_injective w N h3]⟩

/-- **Inverting `W` collapses the parity constraint** — the `W`-localizations
of the weighted head and the zero-weight head agree. -/
noncomputable def headAwayEquiv :
    Localization.Away (WaHead K w N) ≃+*
      Localization.Away (WaHead K (fun _ => 0) N) :=
  letI : Algebra (WPHead K w N)
      (Localization.Away (WaHead K (fun _ => 0) N)) :=
    headAwayAlgebra w N
  haveI : IsLocalization.Away (WaHead K w N)
      (Localization.Away (WaHead K (fun _ => 0) N)) :=
    isLocalization_away_headW w N
  (IsLocalization.algEquiv (Submonoid.powers (WaHead K w N))
    (Localization.Away (WaHead K w N))
    (Localization.Away (WaHead K (fun _ => 0) N))).toRingEquiv

end AwayEquiv

end WeightedParity
