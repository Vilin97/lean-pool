/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.Completeness
public import Mathlib.RingTheory.AdicCompletion.Basic
/-!
# Principal adic filtrations in complete nonarchimedean valuation rings

For a complete nonarchimedean absolute value, a nonzero element of the open
unit ball generates a separated and precomplete principal filtration on the
closed unit ball.  These facts are shared by the coefficientwise Hensel
construction and the irreducible-polynomial coefficient estimate.
-/

@[expose] public section

noncomputable
section

namespace AlgebraicNumberTheory
namespace Valuations

/-- Membership in the `π`-adic principal power is exactly the corresponding
absolute-value bound on the closed unit ball of a nonarchimedean valued field. -/
theorem principal_pow_mem_iff_abs_le
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) (n : ℕ) :
    x ∈ (Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n ↔
      v (x : K) ≤ v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  constructor
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx
    rcases hx with ⟨c, hc⟩
    have hc_abs : v ((c : V) : K) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        v hnonarch ((c : V) : K)).1 c.property
    calc
      v (x : K) = v ((((π : V) : K) ^ n) * ((c : V) : K)) := by
        exact congrArg (fun y : V => v ((y : V) : K)) hc
      _ = v (((π : V) : K) ^ n) * v ((c : V) : K) := by rw [v.map_mul]
      _ = v ((π : V) : K) ^ n * v ((c : V) : K) := by rw [map_pow]
      _ ≤ v ((π : V) : K) ^ n * 1 :=
        mul_le_mul_of_nonneg_left hc_abs (pow_nonneg (v.nonneg _) n)
      _ = v ((π : V) : K) ^ n := by rw [mul_one]
  · intro hx
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    let cK : K := (x : K) / (((π : V) : K) ^ n)
    have hπpow_pos : 0 < v (((π : V) : K) ^ n) := by
      exact v.pos (pow_ne_zero n hπK_ne)
    have hcK_mem : cK ∈ V := by
      rw [mem_absoluteValueValuationSubring_iff]
      have hdiv :
          v cK = v (x : K) / v (((π : V) : K) ^ n) := by
        change v ((x : K) / (((π : V) : K) ^ n)) =
          v (x : K) / v (((π : V) : K) ^ n)
        rw [div_eq_mul_inv, v.map_mul, map_inv₀, div_eq_mul_inv]
      rw [hdiv]
      exact div_le_one_of_le₀ (by simpa [map_pow] using hx) (le_of_lt hπpow_pos)
    refine ⟨⟨cK, hcK_mem⟩, ?_⟩
    apply Subtype.ext
    change (x : K) = (((π : V) : K) ^ n) * cK
    change (x : K) =
      (((π : V) : K) ^ n) * ((x : K) / (((π : V) : K) ^ n))
    rw [mul_comm, div_mul_cancel₀]
    exact pow_ne_zero n hπK_ne

/-- Principal congruence modulo `(π)^n` is exactly an absolute-value bound for
the difference. -/
theorem principal_smodEq_iff_abs_sub_le
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x y : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) {n : ℕ} :
    x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))] ↔
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n := by
  let V := absoluteValueValuationSubring v hnonarch
  constructor
  · intro hxy
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      have h := SModEq.sub_mem.mp hxy
      simpa [smul_eq_mul, Ideal.mul_top, V] using h
    simpa using
      (principal_pow_mem_iff_abs_le
        v hnonarch (π := π) (x := x - y) hπne n).1 hmem
  · intro hxy
    rw [SModEq.sub_mem]
    have hmem : (x - y : V) ∈ (Ideal.span ({π} : Set V)) ^ n := by
      rw [principal_pow_mem_iff_abs_le
        v hnonarch (π := π) (x := x - y) hπne n]
      simpa using hxy
    simpa [smul_eq_mul, Ideal.mul_top, V] using hmem

/-- Forward direction of
`principal_smodEq_iff_abs_sub_le`. -/
theorem abs_sub_le_of_principal_smodEq
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π x y : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0) {n : ℕ}
    (hxy : x ≡ y [SMOD
      ((Ideal.span ({π} : Set
        (absoluteValueValuationSubring v hnonarch))) ^ n •
          ⊤ : Submodule
            (absoluteValueValuationSubring v hnonarch)
            (absoluteValueValuationSubring v hnonarch))]) :
    v ((x : K) - (y : K)) ≤
      v ((π : absoluteValueValuationSubring v hnonarch) : K) ^ n :=
  (principal_smodEq_iff_abs_sub_le
    v hnonarch (π := π) (x := x) (y := y) hπne).1 hxy

/-- Principal separatedness for the element `π` chosen in the proof, as
soon as `π` is a nonzero element of the open unit ball. -/
theorem principalHausdorff_of_nonzero_mem_maximalIdeal
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsHausdorff (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  refine ⟨?_⟩
  intro x hx
  have hπ_abs_lt : v ((π : V) : K) < 1 :=
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      v hnonarch π).1 hπmem
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  by_contra hxne
  have hxK_ne : (x : K) ≠ 0 := by
    intro hxzero
    exact hxne (Subtype.ext hxzero)
  have hx_abs_pos : 0 < v (x : K) := v.pos hxK_ne
  rcases exists_pow_lt_of_lt_one hx_abs_pos hπ_abs_lt with ⟨n, hn⟩
  have hxmem : x ∈ (Ideal.span ({π} : Set V)) ^ n := by
    have h := (SModEq.zero.mp (hx n))
    simpa [smul_eq_mul, Ideal.mul_top, V] using h
  have hx_abs_le :=
    (principal_pow_mem_iff_abs_le
      v hnonarch (π := π) (x := x) hπne n).1 hxmem
  exact not_lt_of_ge hx_abs_le hn

/-- Principal precompleteness for the element `π` chosen in the proof,
deduced from completeness of the valued field. -/
theorem principalPrecomplete_of_complete
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v)
    (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {π : absoluteValueValuationSubring v hnonarch}
    (hπne : π ≠ 0)
    (hπmem : π ∈ IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch)) :
    IsPrecomplete (Ideal.span ({π} : Set
      (absoluteValueValuationSubring v hnonarch)))
      (absoluteValueValuationSubring v hnonarch) := by
  let V := absoluteValueValuationSubring v hnonarch
  let I : Ideal V := Ideal.span ({π} : Set V)
  have hπ_abs_lt : v ((π : V) : K) < 1 :=
    (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
      v hnonarch π).1 hπmem
  have hπK_ne : ((π : V) : K) ≠ 0 := by
    intro hzero
    exact hπne (Subtype.ext hzero)
  have hπ_abs_pos : 0 < v ((π : V) : K) := v.pos hπK_ne
  refine ⟨?_⟩
  intro f hf
  let u : ℕ → WithAbs v := fun n => (WithAbs.equiv v).symm ((f n : V) : K)
  have hu : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    rcases exists_pow_lt_of_lt_one hε hπ_abs_lt with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro m hm n hn
    wlog hmn : m ≤ n generalizing m n with H
    · have hnm : n ≤ m := le_of_not_ge hmn
      simpa [dist_comm] using H n hn m hm hnm
    have hsub_le :
        v (((f m : V) : K) - ((f n : V) : K)) ≤
          v ((π : V) : K) ^ m :=
      abs_sub_le_of_principal_smodEq
        v hnonarch (π := π) hπne (hf hmn)
    have hpow_le : v ((π : V) : K) ^ m ≤ v ((π : V) : K) ^ N :=
      pow_le_pow_of_le_one (le_of_lt hπ_abs_pos) hπ_abs_lt.le hm
    have hdist_le :
        dist (u m) (u n) ≤ v ((π : V) : K) ^ N := by
      calc
        dist (u m) (u n) =
            v (((f m : V) : K) - ((f n : V) : K)) := by
          simp [u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs]
        _ ≤ v ((π : V) : K) ^ m := hsub_le
        _ ≤ v ((π : V) : K) ^ N := hpow_le
    exact hdist_le.trans_lt hN
  rcases (absoluteValueCompleteness_complete_iff_cauchySeq_converges v).1
      hcomplete u hu with
    ⟨a, ha⟩
  let aK : K := WithAbs.equiv v a
  have ha_dist_lt_one : ∃ N : ℕ, dist (u N) a < 1 := by
    rcases Filter.eventually_atTop.1
        ((Metric.tendsto_nhds.mp ha) 1 zero_lt_one) with
      ⟨N, hN⟩
    exact ⟨N, hN N le_rfl⟩
  rcases ha_dist_lt_one with ⟨N₁, hN₁⟩
  have ha_sub_lt_one :
      v (aK - ((f N₁ : V) : K)) < 1 := by
    have hfa : v (((f N₁ : V) : K) - aK) < 1 := by
      simpa [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] using hN₁
    have hneg : aK - ((f N₁ : V) : K) = -(((f N₁ : V) : K) - aK) := by
      ring
    rw [hneg]
    rw [v.map_neg]
    simpa using hfa
  have ha_mem : aK ∈ V := by
    rw [mem_absoluteValueValuationSubring_iff]
    have hfN_mem : v (((f N₁ : V) : K)) ≤ 1 :=
      (mem_absoluteValueValuationSubring_iff
        v hnonarch (((f N₁ : V) : K))).1 (f N₁).property
    calc
      v aK = v (((f N₁ : V) : K) + (aK - ((f N₁ : V) : K))) := by
        ring_nf
      _ ≤ max (v (((f N₁ : V) : K))) (v (aK - ((f N₁ : V) : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch (((f N₁ : V) : K)) (aK - ((f N₁ : V) : K))
      _ ≤ 1 := max_le hfN_mem ha_sub_lt_one.le
  let L : V := ⟨aK, ha_mem⟩
  refine ⟨L, ?_⟩
  intro n
  have hπpow_pos : 0 < v ((π : V) : K) ^ n :=
    pow_pos hπ_abs_pos n
  rcases Filter.eventually_atTop.1
      ((Metric.tendsto_nhds.mp ha) (v ((π : V) : K) ^ n) hπpow_pos) with
    ⟨N₀, hN₀⟩
  let N : ℕ := max n N₀
  have hnN : n ≤ N := le_max_left n N₀
  have hN₀N : N₀ ≤ N := le_max_right n N₀
  have hsub_le :
      v (((f n : V) : K) - ((f N : V) : K)) ≤
        v ((π : V) : K) ^ n :=
    abs_sub_le_of_principal_smodEq
      v hnonarch (π := π) hπne (hf hnN)
  have hN_lim :
      v (((f N : V) : K) - aK) ≤ v ((π : V) : K) ^ n := by
    have hdist := hN₀ N hN₀N
    exact le_of_lt (by
      simpa [aK, u, dist_eq_norm, WithAbs.norm_eq_apply_ofAbs] using hdist)
  have hdiff_le :
      v (((f n : V) : K) - (L : K)) ≤ v ((π : V) : K) ^ n := by
    calc
      v (((f n : V) : K) - (L : K)) =
          v ((((f n : V) : K) - ((f N : V) : K)) +
              (((f N : V) : K) - (L : K))) := by
        ring_nf
      _ ≤ max
          (v (((f n : V) : K) - ((f N : V) : K)))
          (v (((f N : V) : K) - (L : K))) :=
        LubinTate.Valuations.strong_triangle_of_nonarchimedean
          v hnonarch
          (((f n : V) : K) - ((f N : V) : K))
          (((f N : V) : K) - (L : K))
      _ ≤ v ((π : V) : K) ^ n := max_le hsub_le hN_lim
  exact
    (principal_smodEq_iff_abs_sub_le
      v hnonarch (π := π) (x := f n) (y := L) hπne).2
      (by simpa [L] using hdiff_le)

end Valuations
end AlgebraicNumberTheory

end
