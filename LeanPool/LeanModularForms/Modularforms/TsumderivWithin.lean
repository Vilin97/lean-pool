/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import Mathlib.Analysis.Calculus.UniformLimitsDeriv
public import Mathlib.Analysis.Normed.Group.FunctionSeries
public import Mathlib.Topology.Algebra.Module.ModuleTopology
public import Mathlib.Topology.ContinuousMap.Compact
public import LeanPool.LeanModularForms.Modularforms.ExpLems
public import LeanPool.LeanModularForms.Modularforms.Iteratedderivs

/-! # TsumderivWithin -/


@[expose] public section


open UpperHalfPlane TopologicalSpace Set
  Metric Filter Function Complex

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat


/-- The open upper half-plane as a subset of `ℂ`. -/
abbrev ℍ' := {z : ℂ | 0 < z.im}

lemma upper_half_plane_isOpen :
    IsOpen ℍ' := by apply isOpen_lt (by fun_prop) (by fun_prop)

theorem derivWithin_tsum_fun' {α : Type _} (f : α → ℂ → ℂ) {s : Set ℂ}
    (hs : IsOpen s) (x : ℂ) (hx : x ∈ s) (hf : ∀ y ∈ s, Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ n (k : K), ‖derivWithin (f n) s k‖ ≤ u n)
    (hf2 : ∀ n (r : s), DifferentiableAt ℂ (f n) r) :
    derivWithin (fun z => ∑' n : α, f n z) s x = ∑' n : α, derivWithin (fun z => f n z) s x := by
  apply HasDerivWithinAt.derivWithin
  · apply HasDerivAt.hasDerivWithinAt
    have A :
      ∀ x : ℂ,
        x ∈ s →
          Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
            (𝓝 (∑' n : α, (fun z => f n z) x)) :=
          fun y hy ↦ Summable.hasSum <| hf y hy
    apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
    · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
    · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
      intro K hK1 hK2
      obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
      exact tendstoUniformlyOn_tsum hu1 (fun n x hx => hu2 n ⟨x, hx⟩)
    filter_upwards
    intro t r hr
    exact HasDerivAt.fun_sum (fun q _ => HasDerivWithinAt.hasDerivAt
      (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt (IsOpen.mem_nhds hs hr))
  exact IsOpen.uniqueDiffWithinAt hs hx


theorem der_iter_eq_der_aux2 (k n : ℕ) (r : ℍ') :
  DifferentiableAt ℂ
    (fun z : ℂ =>
      iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' z) ↑r := by
  apply DifferentiableOn.differentiableAt
  · exact DifferentiableOn.congr (by fun_prop) (fun x hx => exp_iter_deriv_within k n hx)
  exact IsOpen.mem_nhds (isOpen_lt (by fun_prop) (by fun_prop)) r.2

theorem der_iter_eq_der2 (k n : ℕ) (r : ℍ') :
    deriv (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ↑r =
      derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
        ℍ'
        ↑r := by
  simp only [mem_setOf_eq]
  apply symm
  apply DifferentiableAt.derivWithin
  · apply der_iter_eq_der_aux2
  apply IsOpen.uniqueDiffOn upper_half_plane_isOpen
  apply r.2

theorem der_iter_eq_der2' (k n : ℕ) (r : ℍ') :
    derivWithin (iteratedDerivWithin k (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ')
      ℍ' ↑r =
      iteratedDerivWithin (k + 1)
        (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ' ↑r := by
  rw [iteratedDerivWithin_succ]


/-- The continuous map `z ↦ exp (2π i z)` restricted to a subset `K` of `ℂ`. -/
noncomputable def ctsExpTwoPiN (K : Set ℂ) : ContinuousMap K ℂ where
  toFun := fun r : K => Complex.exp (2 * ↑π * Complex.I * r)

private lemma summable_two_pi_pow_geometric (r : ℝ) (hr : ‖r‖ < 1) (K : ℕ) :
    Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ K * r ^ n)‖ := by
  have heq : ∀ (n : ℕ), ((2 * ↑π) ^ K) * ‖((n) ^ K * (r ^ n))‖ =
      ‖((2 * ↑π * Complex.I * n) ^ K * r ^ n)‖ := by
    intro n
    norm_cast
    simp only [Nat.cast_pow, norm_mul, norm_pow, Real.norm_eq_abs,
      ofReal_mul, ofReal_ofNat, ofReal_pow, norm_ofNat, norm_real, norm_I,
      mul_one, norm_natCast]
    norm_cast
    simp only [Nat.cast_pow]
    have hh : |π| = π := by simp [Real.pi_pos.le]
    rw [hh]
    ring
  apply Summable.congr _ heq
  rw [summable_mul_left_iff]
  · exact summable_norm_pow_mul_geometric_of_norm_lt_one K hr
  norm_cast
  apply pow_ne_zero
  apply mul_ne_zero
  · linarith [Real.pi_pos]
  apply Real.pi_ne_zero

theorem iter_deriv_comp_bound2 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
        ‖(derivWithin (iteratedDerivWithin k
          (fun s : ℂ => Complex.exp (2 * ↑π * Complex.I * n * s)) ℍ') ℍ' r)‖ ≤ u n := by
  haveI : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hK2)
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K )‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    · intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [ctsExpTwoPiN]
      simp only [ContinuousMap.coe_mk]
      apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖ :=
    summable_two_pi_pow_geometric r (by rwa [Real.norm_of_nonneg hr2]) (k + 1)
  · use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k + 1) * r ^ n)‖, hu
    intro n t
    have go := der_iter_eq_der2' k n ⟨t.1, hK1 t.2⟩
    simp only [Complex.norm_mul, norm_pow, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
      RCLike.norm_natCast, ge_iff_le] at *
    simp_rw [go]
    have h1 := exp_iter_deriv_within (k + 1) n (hK1 t.2)
    norm_cast at *
    simp only [ofReal_mul, ofReal_ofNat, ge_iff_le] at *
    rw [h1]
    simp only [Complex.norm_mul, norm_pow, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
      RCLike.norm_natCast]
    have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n := by
      have hw1 :
        ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
          ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
            norm_cast
            rw [← Complex.norm_pow];
            congr;
            rw [← exp_nat_mul];
            ring_nf
      rw [hw1]
      norm_cast
      apply pow_le_pow_left₀
      · simp only [norm_nonneg]
      have :=
        BoundedContinuousFunction.norm_coe_le_norm
          (BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K)) t
      rw [norm_norm]
      simpa [ctsExpTwoPiN] using this
    apply mul_le_mul
    · simp
    · simp only [Real.norm_eq_abs] at ineqe
      convert ineqe
    · positivity
    positivity


theorem hasDerivAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) x := by
  have A : ∀ x : ℂ, x ∈ s → Tendsto (fun t : Finset α => ∑ n ∈ t, (fun z => f n z) x) atTop
        (𝓝 (∑' n : α, (fun z => f n z) x)) := fun y hy => (hf y hy).hasSum
  apply hasDerivAt_of_tendstoLocallyUniformlyOn hs _ _ A hx
  · use fun n : Finset α => fun a => ∑ i ∈ n, derivWithin (fun z => f i z) s a
  · rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hs]
    intro K hK1 hK2
    obtain ⟨u, hu1, hu2⟩ := hu K hK1 hK2
    exact tendstoUniformlyOn_tsum hu1 (fun n x hx => hu2 n ⟨x, hx⟩)
  filter_upwards
  intro t r hr
  exact HasDerivAt.fun_sum (fun q _ => HasDerivWithinAt.hasDerivAt
    (hf2 q ⟨r, hr⟩).differentiableWithinAt.hasDerivWithinAt (IsOpen.mem_nhds hs hr))


theorem hasDerivWithinAt_tsum_fun {α : Type _} (f : α → ℂ → ℂ)
    {s : Set ℂ} (hs : IsOpen s) (x : ℂ) (hx : x ∈ s)
    (hf : ∀ y : ℂ, y ∈ s → Summable fun n : α => f n y)
    (hu :
      ∀ K ⊆ s, IsCompact K →
          ∃ u : α → ℝ, Summable u ∧ ∀ (n : α) (k : K), ‖(derivWithin (f n) s k)‖ ≤ u n)
    (hf2 : ∀ (n : α) (r : s), DifferentiableAt ℂ (f n) r) :
    HasDerivWithinAt (fun z => ∑' n : α, f n z) (∑' n : α, derivWithin (fun z => f n z) s x) s x :=
  (hasDerivAt_tsum_fun f hs x hx hf hu hf2).hasDerivWithinAt




theorem iter_deriv_comp_bound3 (K : Set ℂ) (hK1 : K ⊆ ℍ') (hK2 : IsCompact K) (k : ℕ) :
    ∃ u : ℕ → ℝ,
      Summable u ∧
        ∀ (n : ℕ) (r : K),
          (2 * |π| * n) ^ k * ‖(Complex.exp (2 * ↑π * Complex.I * n * r))‖ ≤ u n := by
  haveI : CompactSpace K := isCompact_univ_iff.mp (isCompact_iff_isCompact_univ.mp hK2)
  set r : ℝ := ‖BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K )‖
  have hr : ‖BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K )‖ < 1 := by
    rw [BoundedContinuousFunction.norm_lt_iff_of_compact]
    · intro x; rw [BoundedContinuousFunction.mkOfCompact_apply]; simp_rw [ctsExpTwoPiN]
      simp only [ContinuousMap.coe_mk]
      apply exp_upperHalfPlane_lt_one ⟨x.1, hK1 x.2⟩
    linarith
  have hr2 : 0 ≤ r := by apply norm_nonneg _
  have hu : Summable fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖ :=
    summable_two_pi_pow_geometric r (by rwa [Real.norm_of_nonneg hr2]) k
  use fun n : ℕ => ‖((2 * ↑π * Complex.I * n) ^ (k) * r ^ n)‖, hu
  intro n t
  simp only [Complex.norm_mul, norm_pow, norm_ofNat, norm_real, Real.norm_eq_abs, norm_I, mul_one,
    RCLike.norm_natCast]
  have ineqe : ‖(Complex.exp (2 * π * Complex.I * n * t))‖ ≤ ‖r‖ ^ n := by
    have hw1 :
      ‖ (Complex.exp (2 * π * Complex.I * n * t))‖ =
        ‖ (Complex.exp (2 * π * Complex.I * t))‖ ^ n := by
          norm_cast
          rw [← Complex.norm_pow]
          congr
          rw [← exp_nat_mul]
          ring_nf
    rw [hw1]
    norm_cast
    apply pow_le_pow_left₀
    · simp only [norm_nonneg]
    have :=
      BoundedContinuousFunction.norm_coe_le_norm
        (BoundedContinuousFunction.mkOfCompact (ctsExpTwoPiN K)) t
    rw [norm_norm]
    simpa [ctsExpTwoPiN] using this
  apply mul_le_mul
  · simp
  · simp only [Real.norm_eq_abs] at ineqe
    convert ineqe
  · positivity
  positivity
