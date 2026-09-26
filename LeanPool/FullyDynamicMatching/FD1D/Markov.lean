/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Basic

/-! # Markov -/

@[expose] public section

namespace FD1D

noncomputable section

/-!
# Finite inventory Markov chains

This file uses elementary finite sums throughout. A `FiniteKernel` is a
row-stochastic matrix, and `FiniteLaw.step` is left multiplication by that
matrix. The inventory chain near the end of the file removes one item and
then adds an independent uniformly distributed item.
-/

open scoped BigOperators Topology
open Filter Matrix

/-! ## Finite laws and stochastic kernels -/

namespace FiniteLaw

variable {α β : Type*} [Fintype α] [Fintype β]

@[ext]
theorem ext {μ ν : FiniteLaw α} (h : ∀ x, μ.mass x = ν.mass x) : μ = ν := by
  cases μ with
  | mk mass hnon hsum =>
      cases ν with
      | mk mass' hnon' hsum' =>
          have hm : mass = mass' := funext h
          subst mass'
          rfl

/-- The point mass at `x`. -/
def dirac [DecidableEq α] (x : α) : FiniteLaw α where
  mass y := if y = x then 1 else 0
  mass_nonneg y := by split_ifs <;> positivity
  sum_mass := by simp

@[simp]
theorem mass_dirac [DecidableEq α] (x y : α) :
    (dirac x : FiniteLaw α).mass y = if y = x then 1 else 0 :=
  rfl

/-- The uniform law on a nonempty finite type. -/
def uniform [Nonempty α] : FiniteLaw α where
  mass _ := 1 / Fintype.card α
  mass_nonneg _ := by positivity
  sum_mass := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card α : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp

@[simp]
theorem mass_uniform [Nonempty α] (x : α) :
    (uniform : FiniteLaw α).mass x = 1 / Fintype.card α :=
  rfl

/-- Push a finite law forward along a map. -/
def map [DecidableEq β] (f : α → β) (μ : FiniteLaw α) : FiniteLaw β where
  mass y := ∑ x with f x = y, μ.mass x
  mass_nonneg y := Finset.sum_nonneg fun x _ => μ.mass_nonneg x
  sum_mass := by
    classical
    rw [Finset.sum_fiberwise_of_maps_to (t := Finset.univ) (s := Finset.univ)
      (g := f) (f := μ.mass) (by simp)]
    exact μ.sum_mass

@[simp]
theorem mass_map [DecidableEq β] (f : α → β) (μ : FiniteLaw α) (y : β) :
    (μ.map f).mass y = ∑ x with f x = y, μ.mass x :=
  rfl

end FiniteLaw

/-- A stochastic kernel on a finite state space. -/
structure FiniteKernel (α : Type*) [Fintype α] where
  /-- One-step transition probability from the first state to the second. -/
  trans : α → α → ℝ
  trans_nonneg : ∀ x y, 0 ≤ trans x y
  sum_trans : ∀ x, ∑ y, trans x y = 1

namespace FiniteKernel

variable {α β : Type*} [Fintype α] [Fintype β]

instance : CoeFun (FiniteKernel α) fun _ => α → α → ℝ :=
  ⟨FiniteKernel.trans⟩

/-- The row-stochastic matrix of a finite kernel. -/
def matrix (K : FiniteKernel α) : Matrix α α ℝ := K.trans

theorem matrix_rowStochastic [DecidableEq α] (K : FiniteKernel α) :
    K.matrix ∈ Matrix.rowStochastic ℝ α := by
  rw [Matrix.mem_rowStochastic_iff_sum]
  exact ⟨K.trans_nonneg, K.sum_trans⟩

/-- Advance a law by one step of the kernel. -/
def step (K : FiniteKernel α) (μ : FiniteLaw α) : FiniteLaw α where
  mass y := ∑ x, μ.mass x * K x y
  mass_nonneg y :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.mass_nonneg x) (K.trans_nonneg x y)
  sum_mass := by
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, K.sum_trans, mul_one]
    exact μ.sum_mass

@[simp]
theorem mass_step (K : FiniteKernel α) (μ : FiniteLaw α) (y : α) :
    (K.step μ).mass y = ∑ x, μ.mass x * K x y :=
  rfl

/-- The law after `n` steps. -/
def iterate (K : FiniteKernel α) : ℕ → FiniteLaw α → FiniteLaw α
  | 0, μ => μ
  | n + 1, μ => K.step (K.iterate n μ)

@[simp]
theorem iterate_zero (K : FiniteKernel α) (μ : FiniteLaw α) :
    K.iterate 0 μ = μ :=
  rfl

@[simp]
theorem iterate_succ (K : FiniteKernel α) (n : ℕ) (μ : FiniteLaw α) :
    K.iterate (n + 1) μ = K.step (K.iterate n μ) :=
  rfl

theorem iterate_add (K : FiniteKernel α) (m n : ℕ) (μ : FiniteLaw α) :
    K.iterate (m + n) μ = K.iterate m (K.iterate n μ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, iterate_succ, ih, iterate_succ]

/-- The `n`-step transition probability. -/
def pow [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) : ℝ :=
  (K.matrix ^ n) x y

@[simp]
theorem pow_zero [DecidableEq α] (K : FiniteKernel α) (x y : α) :
    K.pow 0 x y = if x = y then 1 else 0 := by
  simp [pow, Matrix.one_apply]

@[simp]
theorem pow_one [DecidableEq α] (K : FiniteKernel α) (x y : α) :
    K.pow 1 x y = K x y := by
  change (K.matrix ^ 1) x y = K x y
  rw [_root_.pow_one]
  rfl

theorem pow_nonneg [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x y : α) :
    0 ≤ K.pow n x y := by
  have hpow : K.matrix ^ n ∈ Matrix.rowStochastic ℝ α :=
    (Matrix.rowStochastic ℝ α).pow_mem K.matrix_rowStochastic n
  exact Matrix.nonneg_of_mem_rowStochastic
    hpow

theorem sum_pow [DecidableEq α] (K : FiniteKernel α) (n : ℕ) (x : α) :
    ∑ y, K.pow n x y = 1 := by
  have hpow : K.matrix ^ n ∈ Matrix.rowStochastic ℝ α :=
    (Matrix.rowStochastic ℝ α).pow_mem K.matrix_rowStochastic n
  exact Matrix.sum_row_of_mem_rowStochastic hpow x

theorem pow_add [DecidableEq α] (K : FiniteKernel α) (m n : ℕ) (x z : α) :
    K.pow (m + n) x z = ∑ y, K.pow m x y * K.pow n y z := by
  change (K.matrix ^ (m + n)) x z =
    ∑ y, (K.matrix ^ m) x y * (K.matrix ^ n) y z
  rw [_root_.pow_add, Matrix.mul_apply]

theorem mass_iterate [DecidableEq α] (K : FiniteKernel α)
    (n : ℕ) (μ : FiniteLaw α) (y : α) :
    (K.iterate n μ).mass y = ∑ x, μ.mass x * K.pow n x y := by
  induction n generalizing y with
  | zero =>
      simp [pow_zero]
  | succ n ih =>
      rw [iterate_succ, mass_step]
      simp_rw [ih]
      have hpow (x : α) :
          K.pow (n + 1) x y = ∑ z, K.pow n x z * K z y := by
        rw [K.pow_add n 1]
        simp only [FiniteKernel.pow_one]
      simp_rw [hpow]
      simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      rw [Finset.sum_comm]

theorem iterate_dirac [DecidableEq α] (K : FiniteKernel α)
    (n : ℕ) (x y : α) :
    (K.iterate n (FiniteLaw.dirac x)).mass y = K.pow n x y := by
  rw [mass_iterate]
  simp [FiniteLaw.mass_dirac]

/-- A law is stationary when one step leaves it unchanged. -/
def IsStationary (K : FiniteKernel α) (μ : FiniteLaw α) : Prop :=
  K.step μ = μ

theorem IsStationary.iterate {K : FiniteKernel α} {μ : FiniteLaw α}
    (h : K.IsStationary μ) (n : ℕ) : K.iterate n μ = μ := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate_succ, ih, h]

/-! ### Existence of a stationary law -/

/-- The mass vector after `n` steps, written as a matrix product. -/
def orbit [DecidableEq α] (K : FiniteKernel α) (μ : FiniteLaw α)
    (n : ℕ) : α → ℝ :=
  μ.mass ᵥ* K.matrix ^ n

theorem orbit_eq_iterate [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    K.orbit μ n x = (K.iterate n μ).mass x := by
  rw [mass_iterate]
  rfl

theorem orbit_nonneg [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    0 ≤ K.orbit μ n x := by
  rw [orbit_eq_iterate]
  exact (K.iterate n μ).mass_nonneg x

theorem orbit_le_one [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) (x : α) :
    K.orbit μ n x ≤ 1 := by
  rw [orbit_eq_iterate, ← (K.iterate n μ).sum_mass]
  exact Finset.single_le_sum
    (fun y _ => (K.iterate n μ).mass_nonneg y) (Finset.mem_univ x)

theorem sum_orbit [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    ∑ x, K.orbit μ n x = 1 := by
  simpa only [orbit_eq_iterate] using (K.iterate n μ).sum_mass

theorem orbit_succ [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    K.orbit μ (n + 1) = K.orbit μ n ᵥ* K.matrix := by
  simp only [orbit, _root_.pow_succ, Matrix.vecMul_vecMul]

/-- The average of the first `n+1` orbit vectors. -/
def cesaroVec [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) : α → ℝ :=
  ((n + 1 : ℕ) : ℝ)⁻¹ •
    ∑ k ∈ Finset.range (n + 1), K.orbit μ k

/-- Cesaro averages remain probability laws. -/
def cesaroLaw [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) : FiniteLaw α where
  mass := K.cesaroVec μ n
  mass_nonneg x := by
    apply mul_nonneg
    · positivity
    · simp only [Finset.sum_apply]
      exact Finset.sum_nonneg fun k _ => K.orbit_nonneg μ k x
  sum_mass := by
    simp only [cesaroVec, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp_rw [K.sum_orbit μ]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by positivity)

/-- The one-step error of a Cesaro average is its final endpoint minus its
initial endpoint, divided by the averaging length. -/
theorem cesaro_step_sub [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) (n : ℕ) :
    K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n =
      ((n + 1 : ℕ) : ℝ)⁻¹ •
        (K.orbit μ (n + 1) - K.orbit μ 0) := by
  simp only [cesaroVec, Matrix.smul_vecMul, Matrix.sum_vecMul]
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  simp_rw [← K.orbit_succ μ]
  rw [Finset.sum_range_sub]

theorem tendsto_cesaro_error [DecidableEq α] (K : FiniteKernel α)
    (μ : FiniteLaw α) :
    Tendsto (fun n =>
      K.cesaroVec μ n ᵥ* K.matrix - K.cesaroVec μ n)
      atTop (𝓝 0) := by
  rw [tendsto_pi_nhds]
  intro x
  refine squeeze_zero_norm' (a := fun n : ℕ => 1 / (n + 1 : ℝ))
    (Eventually.of_forall fun n => ?_) ?_
  · rw [K.cesaro_step_sub μ, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      Real.norm_eq_abs]
    have hd :
        |K.orbit μ (n + 1) x - K.orbit μ 0 x| ≤ 1 := by
      rw [abs_le]
      constructor <;>
        linarith [K.orbit_nonneg μ (n + 1) x,
          K.orbit_le_one μ (n + 1) x,
          K.orbit_nonneg μ 0 x, K.orbit_le_one μ 0 x]
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
    calc
      ((↑(n + 1))⁻¹ : ℝ) *
          |K.orbit μ (n + 1) x - K.orbit μ 0 x| ≤
          (↑(n + 1))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = 1 / (n + 1 : ℝ) := by simp [one_div]
  · simpa only [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The finite probability vectors form a compact subset of Euclidean space. -/
private theorem compact_probability_vectors :
    IsCompact {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
  have hclosed : IsClosed {w : α → ℝ | (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1} := by
    have hnonneg : IsClosed {w : α → ℝ | ∀ i, 0 ≤ w i} :=
      by
        simpa only [Set.ofPred_forall] using
          (isClosed_iInter fun i : α =>
            isClosed_le continuous_const (continuous_apply i) :
              IsClosed (⋂ i : α, {w : α → ℝ | 0 ≤ w i}))
    exact hnonneg.inter (isClosed_eq (by fun_prop) continuous_const)
  refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc hclosed ?_
  intro w hw
  refine ⟨hw.1, fun i => ?_⟩
  exact (Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)).trans_eq hw.2

/-- Every finite stochastic kernel on a nonempty state space has a stationary
law. The proof takes a convergent subsequence of Cesaro averages in the
compact finite probability simplex. -/
theorem exists_stationary [Nonempty α]
    (K : FiniteKernel α) :
    ∃ μ : FiniteLaw α, K.IsStationary μ := by
  classical
  let μ0 : FiniteLaw α := FiniteLaw.dirac (Classical.arbitrary α)
  let A : ℕ → α → ℝ := fun n => (K.cesaroLaw μ0 n).mass
  have hA (n : ℕ) : (∀ i, 0 ≤ A n i) ∧ ∑ i, A n i = 1 :=
    ⟨(K.cesaroLaw μ0 n).mass_nonneg, (K.cesaroLaw μ0 n).sum_mass⟩
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    compact_probability_vectors.tendsto_subseq hA
  let π : FiniteLaw α := ⟨v, hv.1, hv.2⟩
  refine ⟨π, ?_⟩
  have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
    simpa only [Function.comp_def] using hlim
  have hcont : Continuous (fun w : α → ℝ => w ᵥ* K.matrix) := by
    fun_prop
  have hstep :
      Tendsto (fun n => A (φ n) ᵥ* K.matrix) atTop
        (𝓝 (v ᵥ* K.matrix)) :=
    (hcont.tendsto v).comp hlim'
  have hdiff :
      Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
        (𝓝 (v ᵥ* K.matrix - v)) :=
    hstep.sub hlim'
  have herr :
      Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
        (𝓝 0) := by
    simpa [A, cesaroLaw, Function.comp_def] using
      (K.tendsto_cesaro_error μ0).comp hφ.tendsto_atTop
  have hz : v ᵥ* K.matrix - v = 0 :=
    tendsto_nhds_unique hdiff herr
  have hvec : v ᵥ* K.matrix = v := sub_eq_zero.mp hz
  apply FiniteLaw.ext
  intro y
  have hy := congrFun hvec y
  simpa [IsStationary, step, π, Matrix.vecMul, dotProduct, matrix] using hy

/-- Reachability by a positive-probability path. -/
def Reaches [DecidableEq α] (K : FiniteKernel α) (x y : α) : Prop :=
  ∃ n : ℕ, 0 < K.pow n x y

/-- Every state can be reached from every other state. -/
def Irreducible [DecidableEq α] (K : FiniteKernel α) : Prop :=
  ∀ x y, K.Reaches x y

theorem reaches_refl [DecidableEq α] (K : FiniteKernel α) (x : α) :
    K.Reaches x x := by
  exact ⟨0, by simp [pow_zero]⟩

theorem reaches_of_pos [DecidableEq α] (K : FiniteKernel α)
    {x y : α} (h : 0 < K x y) : K.Reaches x y := by
  exact ⟨1, by simpa using h⟩

theorem reaches_trans [DecidableEq α] (K : FiniteKernel α)
    {x y z : α} (hxy : K.Reaches x y) (hyz : K.Reaches y z) :
    K.Reaches x z := by
  obtain ⟨m, hm⟩ := hxy
  obtain ⟨n, hn⟩ := hyz
  refine ⟨m + n, lt_of_lt_of_le (mul_pos hm hn) ?_⟩
  rw [pow_add]
  exact Finset.single_le_sum
    (fun w _ => mul_nonneg (K.pow_nonneg m x w) (K.pow_nonneg n w z))
    (Finset.mem_univ y)

/-- Every state has positive mass under a stationary law of an irreducible
finite kernel. -/
theorem stationary_mass_pos [DecidableEq α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ : FiniteLaw α} (hμ : K.IsStationary μ) (y : α) :
    0 < μ.mass y := by
  have hex : ∃ x, 0 < μ.mass x := by
    by_contra h
    push Not at h
    have hz : ∀ x, μ.mass x = 0 :=
      fun x => le_antisymm (h x) (μ.mass_nonneg x)
    have : ∑ x, μ.mass x = 0 := by simp [hz]
    linarith [μ.sum_mass]
  obtain ⟨x, hx⟩ := hex
  obtain ⟨n, hxy⟩ := hirr x y
  have hterm : 0 < μ.mass x * K.pow n x y :=
    mul_pos hx hxy
  calc
    0 < μ.mass x * K.pow n x y := hterm
    _ ≤ ∑ z, μ.mass z * K.pow n z y :=
      Finset.single_le_sum
        (fun z _ => mul_nonneg (μ.mass_nonneg z) (K.pow_nonneg n z y))
        (Finset.mem_univ x)
    _ = (K.iterate n μ).mass y := (K.mass_iterate n μ y).symm
    _ = μ.mass y := by rw [hμ.iterate n]

/-- An irreducible finite kernel has at most one stationary law. -/
theorem stationary_unique [DecidableEq α] [Nonempty α]
    {K : FiniteKernel α} (hirr : K.Irreducible)
    {μ ν : FiniteLaw α}
    (hμ : K.IsStationary μ) (hν : K.IsStationary ν) :
    μ = ν := by
  let ratio : α → ℝ := fun x => μ.mass x / ν.mass x
  obtain ⟨x₀, _, hx₀⟩ :=
    Finset.exists_max_image (Finset.univ : Finset α) ratio
      Finset.univ_nonempty
  have hνpos (x : α) : 0 < ν.mass x :=
    stationary_mass_pos hirr hν x
  have hratio_le (x : α) : ratio x ≤ ratio x₀ :=
    hx₀ x (Finset.mem_univ x)
  have hmass_le (x : α) :
      μ.mass x ≤ ratio x₀ * ν.mass x :=
    (div_le_iff₀ (hνpos x)).mp (hratio_le x)
  have hratio_eq (y : α) : ratio y = ratio x₀ := by
    apply le_antisymm (hratio_le y)
    by_contra hnot
    have hylt : ratio y < ratio x₀ := lt_of_not_ge hnot
    obtain ⟨n, hyn⟩ := hirr y x₀
    have hle (z : α) :
        μ.mass z * K.pow n z x₀ ≤
          (ratio x₀ * ν.mass z) * K.pow n z x₀ :=
      mul_le_mul_of_nonneg_right (hmass_le z) (K.pow_nonneg n z x₀)
    have hyMass : μ.mass y < ratio x₀ * ν.mass y :=
      (div_lt_iff₀ (hνpos y)).mp hylt
    have hyterm :
        μ.mass y * K.pow n y x₀ <
          (ratio x₀ * ν.mass y) * K.pow n y x₀ :=
      mul_lt_mul_of_pos_right hyMass hyn
    have hsumlt :
        (∑ z, μ.mass z * K.pow n z x₀) <
          ∑ z, (ratio x₀ * ν.mass z) * K.pow n z x₀ :=
      Finset.sum_lt_sum
        (fun z _ => hle z)
        ⟨y, Finset.mem_univ y, hyterm⟩
    have hμsum :
        ∑ z, μ.mass z * K.pow n z x₀ = μ.mass x₀ := by
      rw [← K.mass_iterate n μ x₀, hμ.iterate n]
    have hνsum :
        ∑ z, ν.mass z * K.pow n z x₀ = ν.mass x₀ := by
      rw [← K.mass_iterate n ν x₀, hν.iterate n]
    have hcontra : μ.mass x₀ < μ.mass x₀ := by
      calc
        μ.mass x₀ = ∑ z, μ.mass z * K.pow n z x₀ := hμsum.symm
        _ < ∑ z, (ratio x₀ * ν.mass z) * K.pow n z x₀ := hsumlt
        _ = ratio x₀ * ∑ z, ν.mass z * K.pow n z x₀ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = ratio x₀ * ν.mass x₀ := by rw [hνsum]
        _ = μ.mass x₀ := by
          exact div_mul_cancel₀ _ (ne_of_gt (hνpos x₀))
    exact (lt_irrefl _ hcontra).elim
  have hmass (x : α) : μ.mass x = ratio x₀ * ν.mass x := by
    have hx := hratio_eq x
    exact (div_eq_iff (ne_of_gt (hνpos x))).mp hx
  have hsum : (1 : ℝ) = ratio x₀ := by
    calc
      1 = ∑ x, μ.mass x := μ.sum_mass.symm
      _ = ∑ x, ratio x₀ * ν.mass x := by
        apply Finset.sum_congr rfl
        intro x _
        exact hmass x
      _ = ratio x₀ * ∑ x, ν.mass x := (Finset.mul_sum _ _ _).symm
      _ = ratio x₀ := by rw [ν.sum_mass, mul_one]
  apply FiniteLaw.ext
  intro x
  rw [hmass x, ← hsum, one_mul]

/-- Strictly positive one-step self-loops. -/
def HasPositiveLoops (K : FiniteKernel α) : Prop :=
  ∀ x, 0 < K x x

/-! ## Equivariance and invariant laws -/

/-- Equivariance of a kernel under a permutation of its state space. -/
def Equivariant (K : FiniteKernel α) (e : Equiv.Perm α) : Prop :=
  ∀ x y, K (e x) (e y) = K x y

/-- Invariance of a law under a permutation of its state space. -/
def LawInvariant (μ : FiniteLaw α) (e : Equiv.Perm α) : Prop :=
  ∀ x, μ.mass (e x) = μ.mass x

theorem step_lawInvariant {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) :
    LawInvariant (K.step μ) e := by
  intro y
  rw [mass_step, mass_step,
    ← Equiv.sum_comp (e : α ≃ α) (fun x => μ.mass x * K x (e y))]
  apply Finset.sum_congr rfl
  intro x _
  rw [hμ, hK]

theorem iterate_lawInvariant {K : FiniteKernel α}
    {μ : FiniteLaw α} {e : Equiv.Perm α}
    (hK : K.Equivariant e) (hμ : LawInvariant μ e) (n : ℕ) :
    LawInvariant (K.iterate n μ) e := by
  induction n with
  | zero => exact hμ
  | succ n ih =>
      rw [iterate_succ]
      exact step_lawInvariant hK ih

/-- A finite group action preserves a law. -/
def GroupInvariant {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (μ : FiniteLaw α) : Prop :=
  ∀ g, LawInvariant μ (ρ g)

/-- A finite kernel is equivariant for a group action. -/
def GroupEquivariant {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (K : FiniteKernel α) : Prop :=
  ∀ g, K.Equivariant (ρ g)

theorem step_groupInvariant
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) :
    GroupInvariant ρ (K.step μ) :=
  fun g => step_lawInvariant (hK g) (hμ g)

theorem iterate_groupInvariant
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) (n : ℕ) :
    GroupInvariant ρ (K.iterate n μ) :=
  fun g => iterate_lawInvariant (hK g) (hμ g) n

theorem uniform_groupInvariant [Nonempty α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α) :
    GroupInvariant ρ (FiniteLaw.uniform : FiniteLaw α) := by
  intro g x
  rfl

theorem cesaroLaw_groupInvariant [DecidableEq α]
    {G : Type*} [Group G] (ρ : G →* Equiv.Perm α)
    {K : FiniteKernel α} {μ : FiniteLaw α}
    (hK : GroupEquivariant ρ K) (hμ : GroupInvariant ρ μ) (n : ℕ) :
    GroupInvariant ρ (K.cesaroLaw μ n) := by
  intro g x
  simp only [cesaroLaw, cesaroVec, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]
  apply congrArg (fun z : ℝ => ((↑(n + 1))⁻¹ : ℝ) * z)
  apply Finset.sum_congr rfl
  intro k _
  rw [K.orbit_eq_iterate μ, K.orbit_eq_iterate μ]
  exact iterate_groupInvariant ρ hK hμ k g x

/-- A finite equivariant Markov kernel has a stationary law invariant under
the entire finite group action. -/
theorem exists_stationary_groupInvariant [Nonempty α]
    {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm α) (K : FiniteKernel α)
    (hK : GroupEquivariant ρ K) :
    ∃ μ : FiniteLaw α, K.IsStationary μ ∧ GroupInvariant ρ μ := by
  classical
  let μ0 : FiniteLaw α := FiniteLaw.uniform
  let A : ℕ → α → ℝ := fun n => (K.cesaroLaw μ0 n).mass
  have hμ0 : GroupInvariant ρ μ0 :=
    uniform_groupInvariant ρ
  have hA (n : ℕ) : (∀ i, 0 ≤ A n i) ∧ ∑ i, A n i = 1 :=
    ⟨(K.cesaroLaw μ0 n).mass_nonneg, (K.cesaroLaw μ0 n).sum_mass⟩
  have hAinv (n : ℕ) : GroupInvariant ρ (K.cesaroLaw μ0 n) :=
    cesaroLaw_groupInvariant ρ hK hμ0 n
  obtain ⟨v, hv, φ, hφ, hlim⟩ :=
    compact_probability_vectors.tendsto_subseq hA
  let π : FiniteLaw α := ⟨v, hv.1, hv.2⟩
  refine ⟨π, ?_, ?_⟩
  · have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
      simpa only [Function.comp_def] using hlim
    have hcont : Continuous (fun w : α → ℝ => w ᵥ* K.matrix) := by
      fun_prop
    have hstep :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix) atTop
          (𝓝 (v ᵥ* K.matrix)) :=
      (hcont.tendsto v).comp hlim'
    have hdiff :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
          (𝓝 (v ᵥ* K.matrix - v)) :=
      hstep.sub hlim'
    have herr :
        Tendsto (fun n => A (φ n) ᵥ* K.matrix - A (φ n)) atTop
          (𝓝 0) := by
      simpa [A, cesaroLaw, Function.comp_def] using
        (K.tendsto_cesaro_error μ0).comp hφ.tendsto_atTop
    have hz : v ᵥ* K.matrix - v = 0 :=
      tendsto_nhds_unique hdiff herr
    have hvec : v ᵥ* K.matrix = v := sub_eq_zero.mp hz
    apply FiniteLaw.ext
    intro y
    have hy := congrFun hvec y
    simpa [IsStationary, step, π, Matrix.vecMul, dotProduct, matrix] using hy
  · intro g x
    have hlim' : Tendsto (fun n => A (φ n)) atTop (𝓝 v) := by
      simpa only [Function.comp_def] using hlim
    have hleft :=
      (tendsto_pi_nhds.mp hlim') ((ρ g) x)
    have hright :=
      (tendsto_pi_nhds.mp hlim') x
    have hseq :
        (fun n => A (φ n) ((ρ g) x)) =
          (fun n => A (φ n) x) := by
      funext n
      exact hAinv (φ n) g x
    rw [hseq] at hleft
    exact tendsto_nhds_unique hleft hright

end FiniteKernel

/-! ## Inventory vectors and delete/arrive dynamics -/

/-- Leaf-count vectors with fixed total inventory `m`. -/
abbrev InventoryState (ι : Type*) [Fintype ι] (m : ℕ) :=
  {x : ι → ℕ // ∑ i, x i = m}

namespace InventoryState

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
@[ext]
theorem ext {m : ℕ} {x y : InventoryState ι m}
    (h : ∀ i, x.1 i = y.1 i) : x = y :=
  Subtype.ext (funext h)

instance (m : ℕ) : Fintype (InventoryState ι m) := by
  let encode : InventoryState ι m → (ι → Fin (m + 1)) := fun x i =>
    ⟨x.1 i, by
      rw [Nat.lt_succ_iff]
      calc
        x.1 i ≤ ∑ j, x.1 j :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        _ = m := x.2⟩
  exact Fintype.ofInjective encode fun x y h => by
    apply ext
    intro i
    exact congrArg Fin.val (congrFun h i)

instance (m : ℕ) : DecidableEq (InventoryState ι m) :=
  Classical.decEq _

/-- The count vector after deleting at `d` and arriving at `a`.
If `d` is empty, this is defined to be the original state. -/
def move {m : ℕ} (x : InventoryState ι m) (d a : ι) : InventoryState ι m :=
  if hd : 0 < x.1 d then
    let removed := Function.update x.1 d (x.1 d - 1)
    ⟨Function.update removed a (removed a + 1), by
      have hremoved : ∑ i, removed i = m - 1 := by
        rw [Finset.sum_update_of_mem (Finset.mem_univ d)]
        have hx :=
          Finset.sum_erase_add Finset.univ x.1 (Finset.mem_univ d)
        rw [x.2] at hx
        simp only [Finset.sdiff_singleton_eq_erase]
        omega
      rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
      have hr :=
        Finset.sum_erase_add Finset.univ removed (Finset.mem_univ a)
      rw [hremoved] at hr
      simp only [Finset.sdiff_singleton_eq_erase]
      have hmpos : 0 < m := by
        calc
          0 < x.1 d := hd
          _ ≤ ∑ i, x.1 i :=
            Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
          _ = m := x.2
      omega⟩
  else x

@[simp]
theorem move_empty {m : ℕ} (x : InventoryState ι m) {d a : ι}
    (hd : x.1 d = 0) : move x d a = x := by
  simp [move, hd]

@[simp]
theorem move_self {m : ℕ} (x : InventoryState ι m) (d : ι) :
    move x d d = x := by
  by_cases hd : 0 < x.1 d
  · rw [move, dite_eq_left hd]
    apply ext
    intro i
    by_cases hi : i = d
    · subst i
      simp
      omega
    · simp [hi]
  · simp [move, hd]

theorem move_apply_of_pos {m : ℕ} (x : InventoryState ι m) {d a i : ι}
    (hd : 0 < x.1 d) :
    (move x d a).1 i =
      x.1 i + (if i = a then 1 else 0) - (if i = d then 1 else 0) := by
  rw [move, dite_eq_left hd]
  by_cases hia : i = a
  · subst i
    by_cases had : a = d
    · subst d
      simp
      omega
    · have hda : d ≠ a := Ne.symm had
      simp [had]
  · by_cases hid : i = d
    · subst i
      have hda : d ≠ a := hia
      simp [Function.update_apply, hia]
    · simp [Function.update_apply, hia, hid]

end InventoryState

/-- A deletion rule chooses an occupied leaf, assigning every occupied leaf
strictly positive probability. -/
structure DeletionRule (ι : Type*) [Fintype ι] (m : ℕ) where
  /-- Probability of deleting an item from each occupied inventory coordinate. -/
  prob : InventoryState ι m → ι → ℝ
  nonneg : ∀ x i, 0 ≤ prob x i
  empty : ∀ x i, x.1 i = 0 → prob x i = 0
  occupied_pos : ∀ x i, 0 < x.1 i → 0 < prob x i
  sum_prob : ∀ x, ∑ i, prob x i = 1

namespace DeletionRule

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {m : ℕ}

/-- Transition probability: delete according to `R`, then independently
arrive at a uniformly chosen leaf. -/
def kernel (R : DeletionRule ι m) : FiniteKernel (InventoryState ι m) where
  trans x y :=
    ∑ d, ∑ a, if InventoryState.move x d a = y then
      R.prob x d * (1 / Fintype.card ι : ℝ) else 0
  trans_nonneg x y := by
    apply Finset.sum_nonneg
    intro d _
    apply Finset.sum_nonneg
    intro a _
    split_ifs
    · exact mul_nonneg (R.nonneg x d) (by positivity)
    · positivity
  sum_trans x := by
    classical
    calc
      ∑ y, ∑ d, ∑ a, (if InventoryState.move x d a = y then
          R.prob x d * (1 / Fintype.card ι : ℝ) else 0) =
          ∑ d, ∑ a, ∑ y, (if InventoryState.move x d a = y then
            R.prob x d * (1 / Fintype.card ι : ℝ) else 0) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
      _ = ∑ d, ∑ a, R.prob x d * (1 / Fintype.card ι : ℝ) := by
        exact Finset.sum_congr rfl fun d _ =>
          Finset.sum_congr rfl fun a _ => by simp
      _ = 1 := by
        have hinner (d : ι) :
            (∑ _a : ι, R.prob x d * (1 / Fintype.card ι : ℝ)) =
              R.prob x d := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (Fintype.card ι : ℝ) ≠ 0 := by
            exact_mod_cast Fintype.card_ne_zero
          field_simp
        simp_rw [hinner]
        exact R.sum_prob x

@[simp]
theorem kernel_apply (R : DeletionRule ι m) (x y : InventoryState ι m) :
    R.kernel x y =
      ∑ d, ∑ a, if InventoryState.move x d a = y then
        R.prob x d * (1 / Fintype.card ι : ℝ) else 0 :=
  rfl

/-- Every legal delete/arrive move has positive one-step probability. -/
theorem kernel_move_pos (R : DeletionRule ι m)
    (x : InventoryState ι m) {d a : ι} (hd : 0 < x.1 d) :
    0 < R.kernel x (InventoryState.move x d a) := by
  classical
  let c : ℝ := 1 / Fintype.card ι
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hterm : 0 < R.prob x d * c := mul_pos (R.occupied_pos x d hd) hc
  rw [kernel_apply]
  have hinner :
      R.prob x d * c ≤
        ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
          then R.prob x d * c else 0 := by
    calc
      R.prob x d * c =
          (if InventoryState.move x d a = InventoryState.move x d a
            then R.prob x d * c else 0) := by simp
      _ ≤ ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
            then R.prob x d * c else 0 :=
        Finset.single_le_sum
          (f := fun a' => if InventoryState.move x d a' = InventoryState.move x d a
            then R.prob x d * c else 0)
          (fun a' _ => by
            split_ifs
            · exact mul_nonneg (R.nonneg x d) hc.le
            · exact le_rfl)
          (Finset.mem_univ a)
  calc
    0 < R.prob x d * c := hterm
    _ ≤ ∑ a', if InventoryState.move x d a' = InventoryState.move x d a
          then R.prob x d * c else 0 := hinner
    _ ≤ ∑ d', ∑ a', if InventoryState.move x d' a' = InventoryState.move x d a
          then R.prob x d' * c else 0 := by
      exact Finset.single_le_sum
        (f := fun d' => ∑ a', if
          InventoryState.move x d' a' = InventoryState.move x d a
            then R.prob x d' * c else 0)
        (fun d' _ => Finset.sum_nonneg fun a' _ => by
          split_ifs
          · exact mul_nonneg (R.nonneg x d') hc.le
          · exact le_rfl)
        (Finset.mem_univ d)

/-- The self-loop probability is at least the uniform arrival mass. -/
theorem one_div_card_le_kernel_self (R : DeletionRule ι m)
    (x : InventoryState ι m) :
    (1 / Fintype.card ι : ℝ) ≤ R.kernel x x := by
  classical
  let c : ℝ := 1 / Fintype.card ι
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  rw [kernel_apply]
  calc
    c = ∑ d, R.prob x d * c := by
      rw [← Finset.sum_mul, R.sum_prob]
      simp
    _ ≤ ∑ d, ∑ a, if InventoryState.move x d a = x
          then R.prob x d * c else 0 := by
      apply Finset.sum_le_sum
      intro d _
      calc
        R.prob x d * c ≤
            (if InventoryState.move x d d = x then R.prob x d * c else 0) := by
          simp
        _ ≤ ∑ a, if InventoryState.move x d a = x
              then R.prob x d * c else 0 := by
          exact Finset.single_le_sum
            (f := fun a => if InventoryState.move x d a = x
              then R.prob x d * c else 0)
            (fun a _ => by
              split_ifs
              · exact mul_nonneg (R.nonneg x d) hc
              · exact le_rfl)
            (Finset.mem_univ d)

theorem kernel_hasPositiveLoops (R : DeletionRule ι m) :
    R.kernel.HasPositiveLoops := by
  intro x
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < 1 / Fintype.card ι)
    (R.one_div_card_le_kernel_self x)

/-- Integrating against a deletion kernel amounts to summing over its two moves. -/
theorem kernel_expectation_eq_delete_arrive (R : DeletionRule ι m)
    (x : InventoryState ι m) (f : InventoryState ι m → ℝ) :
    ∑ y, R.kernel x y * f y =
      ∑ deleted, ∑ arrived,
        R.prob x deleted * (1 / Fintype.card ι : ℝ) *
          f (InventoryState.move x deleted arrived) := by
  simp only [DeletionRule.kernel_apply]
  calc
    ∑ y, (∑ deleted, ∑ arrived,
          if InventoryState.move x deleted arrived = y then
            R.prob x deleted *
              (1 / Fintype.card ι : ℝ)
          else 0) * f y =
        ∑ deleted, ∑ arrived, ∑ y,
          (if InventoryState.move x deleted arrived = y then
            R.prob x deleted *
              (1 / Fintype.card ι : ℝ)
          else 0) * f y := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro deleted _
            rw [Finset.sum_comm]
    _ = ∑ deleted, ∑ arrived,
          R.prob x deleted *
            (1 / Fintype.card ι : ℝ) *
              f (InventoryState.move x deleted arrived) := by
            apply Finset.sum_congr rfl
            intro deleted _
            apply Finset.sum_congr rfl
            intro arrived _
            simp

end DeletionRule

end

end FD1D
