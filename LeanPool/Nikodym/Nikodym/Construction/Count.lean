/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/
module


public import LeanPool.Nikodym.Nikodym.Construction.Fibers
public import LeanPool.Nikodym.Nikodym.Construction.Tangent

/-!
# Counting: the size of the product set

This file implements blueprint nodes E01 and E02 of `docs/nikodym_construction_lean_blueprint.md`.

Everything is parametrised as in `Nikodym.Construction.Fibers`: `k = h - 1` is the number of
digits, `n` and `q` are the integer parameters of Q01, the number of real embeddings is
`Fintype.card ι` and we assume `Fintype.card ι = n`. The threshold is `q ≥ 2 ^ (n * 2 ^ k)`, the
digit radius is `ρ = 1 / (100 (k+1) √n)` and the trace-fiber radius is `T = γ M` with `γ = 1/10`.

* `Scaffold.card_digitSpace_ge`: `|W| ≥ (ρ / (2 n K₀))^(n k) q^(1 - 2⁻¹^k)` (S03 + Q02).
* `Scaffold.card_energyFiber_ge`: for `B` as produced by C02,
  `|B| ≥ (ρ / (2 n K₀))^(n k) 2⁻¹^k q^(1 - 2⁻¹^k - 2k/n)`.
* `Scaffold.card_traceFiber_ge`: for `A` as produced by C01 with `T = γ M`,
  `|A| ≥ (γ / (2 n K₀))^n / ((2n+1) γ) · q^(1 - 1/n)`.
* `Scaffold.card_prod_ge`: `|A|^k |B| ≥ E01const n k K₀ · q^((k+1) - 2⁻¹^k - 3(k+1)/n)`, with the
  explicit constant `E01const n k K₀ > 0` (`E01const_pos`), independent of `q` and of the scaffold
  beyond `K₀`.
* `Scaffold.exists_isNikodym_of_scaffold` (E02): for every scaffold of rank `n` into `F` with
  `|F| = q ≥ 2^(n 2^k)` and `10 ≤ M`, there is a Nikodym set `N ⊆ F^(k+1)` with
  `q^(k+1) - |N| ≥ E01const n k K₀ · q^((k+1) - 2⁻¹^k - 3(k+1)/n)`.
-/

@[expose] public section

open Finset Real

namespace Nikodym

namespace Scaffold

/-! ### Blueprint E01: the explicit constants -/

/-- Blueprint E01: the digit radius `ρ = 1 / (100 (k+1) √n)` of T01. -/
noncomputable def rho (n k : ℕ) : ℝ := 1 / (100 * (k + 1) * Real.sqrt n)

/-- Blueprint E01: the trace-fiber radius ratio `γ = 1/10` of T01. -/
noncomputable def gamma : ℝ := 1 / 10

/-- Blueprint E01: the constant `(ρ / (2 n K₀))^(n k)` in the lower bound for the digit space. -/
noncomputable def digitConst (n k : ℕ) (K₀ : ℝ) : ℝ := (rho n k / (2 * n * K₀)) ^ (n * k)

/-- Blueprint E01: the constant `(ρ / (2 n K₀))^(n k) 2⁻¹^k` in the lower bound for the energy
fiber `B`. -/
noncomputable def energyConst (n k : ℕ) (K₀ : ℝ) : ℝ := digitConst n k K₀ * (2 : ℝ)⁻¹ ^ k

/-- Blueprint E01: the constant `(γ / (2 n K₀))^n / ((2 n + 1) γ)` in the lower bound for the
trace fiber `A`. -/
noncomputable def traceConst (n : ℕ) (K₀ : ℝ) : ℝ :=
  (gamma / (2 * n * K₀)) ^ n / ((2 * n + 1) * gamma)

/-- Blueprint E01: the constant `c(n, h, K₀) = traceConst^k · energyConst` in
`|A|^k |B| ≥ c q^((k+1) - 2⁻¹^k - 3(k+1)/n)`. It depends only on `n`, `k = h - 1` and `K₀`. -/
noncomputable def E01const (n k : ℕ) (K₀ : ℝ) : ℝ := traceConst n K₀ ^ k * energyConst n k K₀

/-- Blueprint E01: `ρ > 0` for `n ≥ 1`. (Named `rho_pos'` because `Scaffold.rho_pos` of T01 is the
same statement for an arbitrary `ρ` given by the defining equation.) -/
theorem rho_pos' {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : 0 < rho n k := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  unfold rho
  positivity

/-- Blueprint E01: `γ > 0`. -/
theorem gamma_pos : 0 < gamma := by norm_num [gamma]

/-- Blueprint E01: `digitConst > 0` for `K₀ > 0`, `n ≥ 1`. -/
theorem digitConst_pos {n k : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀) (hn : 1 ≤ n) :
    0 < digitConst n k K₀ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  have := rho_pos' hn k
  unfold digitConst
  positivity

/-- Blueprint E01: `energyConst > 0` for `K₀ > 0`, `n ≥ 1`. -/
theorem energyConst_pos {n k : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀) (hn : 1 ≤ n) :
    0 < energyConst n k K₀ := by
  have := digitConst_pos (k := k) hK₀ hn
  unfold energyConst
  positivity

/-- Blueprint E01: `traceConst > 0` for `K₀ > 0`, `n ≥ 1`. -/
theorem traceConst_pos {n : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀) (hn : 1 ≤ n) : 0 < traceConst n K₀ := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  have := gamma_pos
  unfold traceConst
  positivity

/-- Blueprint E01: `E01const > 0` for `K₀ > 0`, `n ≥ 1`. -/
theorem E01const_pos {n k : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀) (hn : 1 ≤ n) : 0 < E01const n k K₀ := by
  have := traceConst_pos hK₀ hn
  have := energyConst_pos (k := k) hK₀ hn
  unfold E01const
  positivity

/-! ### Auxiliary reindexing lemmas -/

/-- Reindex a product over `Ico 1 (k + 1)` as a product over `Fin k`. -/
theorem prod_Ico_one_eq_prod_fin (f : ℕ → ℝ) (k : ℕ) :
    ∏ i ∈ Ico 1 (k + 1), f i = ∏ i : Fin k, f (i.val + 1) := by
  rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel, ← Fin.prod_univ_eq_prod_range (fun i ↦ f (1 + i))]
  exact prod_congr rfl fun i _ ↦ by rw [add_comm]

/-- The exponent `2 * (h - 1) / n` of `Params.prod_D_sq_le` with `h = k + 1`. -/
theorem two_mul_sub_one_div {n k : ℕ} :
    2 * (((k + 1 : ℕ) : ℝ) - 1) / (n : ℝ) = 2 * k / n := by
  push_cast
  ring

section Count

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ} {ρ γ : ℝ}

/-! ### Blueprint E01: the digit space -/

/-- Blueprint E01: the size of the digit space,
`|W| ≥ (ρ / (2 n K₀))^(n k) q^(1 - 2⁻¹^k)` for `q ≥ 2^(n 2^k)` and `ρ ≥ 0`. -/
theorem card_digitSpace_ge (S : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀) (hcard : Fintype.card ι = n)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hq : 2 ^ (n * 2 ^ k) ≤ q) (hρ : 0 ≤ ρ) :
    (ρ / (2 * n * K₀)) ^ (n * k) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) ≤
      ((digitSpace S n q k ρ).card : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  -- S03 for each factor
  have hbox : ∀ i : Fin k,
      (ρ * radix n q k i / (n * K₀)) ^ n ≤ ((S.boxFinset (ρ * radix n q k i)).card : ℝ) := by
    intro i
    have := S.le_card_boxFinset hK₀ (T := ρ * radix n q k i) (by positivity)
    rwa [hcard] at this
  -- Q02 for the product of the radices
  have hprodQ : 2 ^ (-(n : ℝ) * k) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k) ≤
      ∏ i : Fin k, (Params.Q n q (i.val + 1) : ℝ) ^ n := by
    have h := Params.prod_Q_pow_ge (n := n) (q := q) (h := k + 1) hn (by omega) hq
    rw [Nat.add_sub_cancel, prod_Ico_one_eq_prod_fin (fun i ↦ (Params.Q n q i : ℝ) ^ n)] at h
    have hcast : (((k + 1 : ℕ) : ℝ) - 1) = k := by push_cast; ring
    rw [hcast] at h
    exact h
  have h2 : (2 : ℝ) ^ (-(n : ℝ) * k) = ((2 : ℝ) ^ (n * k))⁻¹ := by
    rw [neg_mul, rpow_neg zero_le_two, ← Nat.cast_mul, rpow_natCast]
  calc (ρ / (2 * n * K₀)) ^ (n * k) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k)
      = (ρ / (n * K₀)) ^ (n * k) * (2 ^ (-(n : ℝ) * k) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k)) := by
        rw [h2, show ρ / (2 * n * K₀) = ρ / (n * K₀) / 2 by ring, div_pow]
        ring
    _ ≤ (ρ / (n * K₀)) ^ (n * k) * ∏ i : Fin k, (Params.Q n q (i.val + 1) : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hprodQ (by positivity)
    _ = ∏ i : Fin k, (ρ * radix n q k i / (n * K₀)) ^ n := by
        simp_rw [radix_apply, mul_div_right_comm, mul_pow, prod_mul_distrib, prod_const,
          card_univ, Fintype.card_fin, ← pow_mul]
    _ ≤ ∏ i : Fin k, ((S.boxFinset (ρ * radix n q k i)).card : ℝ) :=
        prod_le_prod₀ (fun i _ ↦ by positivity) (fun i _ ↦ hbox i)
    _ = ((digitSpace S n q k ρ).card : ℝ) := by rw [card_digitSpace, Nat.cast_prod]

/-! ### Blueprint E01: the energy fiber -/

/-- Blueprint E01: the size of the energy fiber. If `B` satisfies the C02 bound
`|W| / (2^k ∏ D_{i+2}^2) ≤ |B|` (as produced by `exists_energy_fiber`), then
`|B| ≥ (ρ / (2 n K₀))^(n k) 2⁻¹^k q^(1 - 2⁻¹^k - 2k/n)`. -/
theorem card_energyFiber_ge (S : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀)
    (hcard : Fintype.card ι = n) (hn : 1 ≤ n) (hk : 1 ≤ k) (hq : 2 ^ (n * 2 ^ k) ≤ q) (hρ : 0 ≤ ρ)
    {B : Finset (Fin k → R)}
    (hB : ((digitSpace S n q k ρ).card : ℝ) /
      (2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2) ≤ B.card) :
    (ρ / (2 * n * K₀)) ^ (n * k) * (2 : ℝ)⁻¹ ^ k *
      (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n) ≤ (B.card : ℝ) := by
  have hq1 : 1 ≤ q := Params.one_le_q_of_threshold (h := k + 1) hq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.succ_le_iff.mp hq1)
  have hW := card_digitSpace_ge S hK₀ hcard hn hk hq hρ
  -- Q02 for the product of the `D`s
  have hD : ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2 ≤ (q : ℝ) ^ (2 * k / (n : ℝ)) := by
    have h := Params.prod_D_sq_le (n := n) (q := q) (h := k + 1) hn (by omega) hq
    rw [prod_Ico_one_eq_prod_fin (fun i ↦ (Params.D n q (i + 1) : ℝ) ^ 2), two_mul_sub_one_div] at h
    exact h
  have hDpos : (0 : ℝ) < 2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2 := by
    refine mul_pos (by positivity) (prod_pos fun i _ ↦ ?_)
    have : (1 : ℝ) ≤ Params.D n q (i.val + 2) := by exact_mod_cast Params.D_pos hq1 _
    positivity
  calc (ρ / (2 * n * K₀)) ^ (n * k) * (2 : ℝ)⁻¹ ^ k * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n)
      = ((ρ / (2 * n * K₀)) ^ (n * k) * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k)) /
          (2 ^ k * (q : ℝ) ^ (2 * k / (n : ℝ))) := by
        rw [rpow_sub hq0, inv_pow]
        field_simp
    _ ≤ ((digitSpace S n q k ρ).card : ℝ) /
          (2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2) :=
        div_le_div₀ (Nat.cast_nonneg _) hW hDpos
          (mul_le_mul_of_nonneg_left hD (by positivity))
    _ ≤ (B.card : ℝ) := hB

/-! ### Blueprint E01: the trace fiber -/

omit [CommRing R] in
/-- Blueprint E01: the size of the trace fiber. If `A` satisfies the C01 bound with
`T = γ M` (as produced by `exists_trace_fiber`), then
`|A| ≥ (γ / (2 n K₀))^n / ((2 n + 1) γ) · q^(1 - 1/n)`. -/
theorem card_traceFiber_ge (hK₀ : 0 < K₀) (hcard : Fintype.card ι = n) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (hq : 2 ^ (n * 2 ^ k) ≤ q) (hγ : 0 < γ) {A : Finset R}
    (hA : (γ * Params.M n q / (Fintype.card ι * K₀)) ^ Fintype.card ι /
      ((2 * Fintype.card ι + 1) * (γ * Params.M n q)) ≤ (A.card : ℝ)) :
    (γ / (2 * n * K₀)) ^ n / ((2 * n + 1) * γ) * (q : ℝ) ^ (1 - 1 / (n : ℝ)) ≤ (A.card : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  have hn0 : n ≠ 0 := Params.ne_zero_of_one_le hn
  have hq1 : 1 ≤ q := Params.one_le_q_of_threshold (h := k + 1) hq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.succ_le_iff.mp hq1)
  rw [hcard] at hA
  set r : ℝ := (q : ℝ) ^ (1 / (n : ℝ)) with hr
  have hr2 : 2 ≤ r := Params.two_le_rpow_M (n := n) (q := q) (h := k + 1) hn (by omega) hq
  have hr0 : 0 < r := by linarith
  have hMr : r / 2 ≤ (Params.M n q : ℝ) :=
    Params.M_ge_half_rpow (n := n) (q := q) (h := k + 1) hn (by omega) hq
  have hrM : (Params.M n q : ℝ) ≤ r := Params.M_le_rpow
  have hM0 : (0 : ℝ) < Params.M n q := by linarith
  have hrn : r ^ n = q := by
    rw [hr, one_div]
    exact rpow_inv_natCast_pow (Nat.cast_nonneg q) hn0
  have hqr : (q : ℝ) ^ (1 - 1 / (n : ℝ)) = q / r := by
    rw [rpow_sub hq0, rpow_one]
  -- the key comparison `M^n / M ≥ (r/2)^n / r`
  have hkey : (r / 2) ^ n / r ≤ (Params.M n q : ℝ) ^ n / Params.M n q :=
    div_le_div₀ (by positivity) (pow_le_pow_left₀ (by positivity) hMr n) hM0 hrM
  calc (γ / (2 * n * K₀)) ^ n / ((2 * n + 1) * γ) * (q : ℝ) ^ (1 - 1 / (n : ℝ))
      = (γ / (n * K₀)) ^ n / ((2 * n + 1) * γ) * ((r / 2) ^ n / r) := by
        rw [hqr, ← hrn, show γ / (2 * n * K₀) = γ / (n * K₀) / 2 by ring, div_pow r,
          div_pow (γ / (n * K₀))]
        ring
    _ ≤ (γ / (n * K₀)) ^ n / ((2 * n + 1) * γ) * ((Params.M n q : ℝ) ^ n / Params.M n q) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = (γ * Params.M n q / (n * K₀)) ^ n / ((2 * n + 1) * (γ * Params.M n q)) := by
        rw [div_pow, div_pow, mul_pow]
        field_simp
        ring
    _ ≤ (A.card : ℝ) := hA

/-! ### Blueprint E01: the main statement -/

/-- Blueprint E01 (main statement): the size of the product set. Under `Scaffold`, `K₀ > 0`,
`Fintype.card ι = n ≥ 1`, `k = h - 1 ≥ 1`, `q ≥ 2^(n 2^k)`, with `ρ = rho n k` and `γ = gamma`,
if `A` satisfies the C01 bound with `T = γ M` and `B` satisfies the C02 bound (as produced by
`exists_trace_fiber` and `exists_energy_fiber`), then

`|A|^k |B| ≥ E01const n k K₀ · q^((k+1) - 2⁻¹^k - 3(k+1)/n)`,

where `E01const n k K₀ > 0` depends only on `n`, `k` and `K₀`. -/
theorem card_prod_ge (S : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀) (hcard : Fintype.card ι = n)
    (hn : 1 ≤ n) (hk : 1 ≤ k) (hq : 2 ^ (n * 2 ^ k) ≤ q) {A : Finset R}
    (hA : (gamma * Params.M n q / (Fintype.card ι * K₀)) ^ Fintype.card ι /
      ((2 * Fintype.card ι + 1) * (gamma * Params.M n q)) ≤ (A.card : ℝ))
    {B : Finset (Fin k → R)}
    (hB : ((digitSpace S n q k (rho n k)).card : ℝ) /
      (2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2) ≤ B.card) :
    E01const n k K₀ * (q : ℝ) ^ ((k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - 3 * (k + 1) / n) ≤
      (A.card : ℝ) ^ k * B.card := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.succ_le_iff.mp hn)
  have hq1 : 1 ≤ q := Params.one_le_q_of_threshold (h := k + 1) hq
  have hq0 : (0 : ℝ) < q := Nat.cast_pos.2 (Nat.succ_le_iff.mp hq1)
  have hq1' : (1 : ℝ) ≤ q := Nat.one_le_cast.2 hq1
  have hA' := card_traceFiber_ge hK₀ hcard hn hk hq gamma_pos hA
  have hB' := card_energyFiber_ge S hK₀ hcard hn hk hq (rho_pos' hn k).le hB
  have hcA : 0 < traceConst n K₀ := traceConst_pos hK₀ hn
  have hcB : 0 < energyConst n k K₀ := energyConst_pos (k := k) hK₀ hn
  -- rewrite the two bounds with the named constants
  have hA'' : traceConst n K₀ * (q : ℝ) ^ (1 - 1 / (n : ℝ)) ≤ (A.card : ℝ) := hA'
  have hB'' : energyConst n k K₀ * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n) ≤ (B.card : ℝ) := by
    simpa only [energyConst, digitConst] using hB'
  -- the exponent bookkeeping
  have hexp : (k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - 3 * (k + 1) / n ≤
      (1 - 1 / (n : ℝ)) * k + (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n) := by
    have : 3 * (k : ℝ) / n ≤ 3 * (k + 1) / n := by
      gcongr
      linarith
    have h3 : (1 - 1 / (n : ℝ)) * k + (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n) =
        (k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - 3 * k / n := by ring
    linarith
  calc E01const n k K₀ * (q : ℝ) ^ ((k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - 3 * (k + 1) / n)
      ≤ E01const n k K₀ *
          (q : ℝ) ^ ((1 - 1 / (n : ℝ)) * k + (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n)) :=
        mul_le_mul_of_nonneg_left (rpow_le_rpow_of_exponent_le hq1' hexp)
          (E01const_pos hK₀ hn).le
    _ = (traceConst n K₀ * (q : ℝ) ^ (1 - 1 / (n : ℝ))) ^ k *
          (energyConst n k K₀ * (q : ℝ) ^ (1 - (2 : ℝ)⁻¹ ^ k - 2 * k / n)) := by
        rw [rpow_add hq0, rpow_mul hq0.le, rpow_natCast, E01const, mul_pow]
        ring
    _ ≤ (A.card : ℝ) ^ k * B.card :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) hA'' k) hB'' (by positivity)
          (by positivity)

end Count

/-! ### Blueprint E02: the fixed-scaffold theorem -/

section FixedScaffold

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}
variable {n q k : ℕ}

/-- Blueprint E02: the C02 hypothesis `n ρ² (k+1)² ≤ 1` for `ρ = rho n k`. -/
theorem card_mul_rho_sq_le (hcard : Fintype.card ι = n) (hn : 1 ≤ n) :
    Fintype.card ι * rho n k ^ 2 * (k + 1) ^ 2 ≤ 1 := by
  rw [hcard]
  have h := rho_mul_eq hn (rfl : rho n k = 1 / (100 * (k + 1) * Real.sqrt n))
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
  calc (n : ℝ) * rho n k ^ 2 * (k + 1) ^ 2 = (rho n k * (k + 1) * Real.sqrt n) ^ 2 := by
        rw [mul_pow, mul_pow, hsq]
        ring
    _ = (1 / 100) ^ 2 := by rw [h]
    _ ≤ 1 := by norm_num

/-- Blueprint E02 (fixed-scaffold theorem): under `Scaffold`, `K₀ > 0`, `Fintype.card ι = n ≥ 1`,
`k = h - 1 ≥ 1`, `Fintype.card F = q ≥ 2^(n 2^k)` and `10 ≤ M`, there is a Nikodym set
`N ⊆ F^(k+1)` with

`q^(k+1) - |N| ≥ E01const n k K₀ · q^((k+1) - 2⁻¹^k - 3(k+1)/n)`.

The set is `univ \ ptSet` for a trace fiber `A` (C01, `T = γ M`) and an energy fiber `B` (C02,
`ρ = rho n k`); `IsNikodym` is T01 + P01 and the count is T01 + E01. -/
theorem exists_isNikodym_of_scaffold (S : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀)
    (hcard : Fintype.card ι = n) (hn : 1 ≤ n) (hk : 1 ≤ k) (hqF : Fintype.card F = q)
    (hq : 2 ^ (n * 2 ^ k) ≤ q) (hM : 10 ≤ Params.M n q) :
    ∃ N : Finset (Fin (k + 1) → F), IsNikodym N ∧
      E01const n k K₀ * (q : ℝ) ^ ((k + 1 : ℝ) - (2 : ℝ)⁻¹ ^ k - 3 * (k + 1) / n) ≤
        (Fintype.card F : ℝ) ^ (k + 1) - N.card := by
  classical
  have hq1 : 1 ≤ q := Params.one_le_q_of_threshold (h := k + 1) hq
  -- C01 with `T = γ M`
  have hT : 1 ≤ gamma * Params.M n q := by
    have : (10 : ℝ) ≤ Params.M n q := by exact_mod_cast hM
    rw [gamma]
    linarith
  obtain ⟨s, A, hA, hAs, hAcard⟩ := S.exists_trace_fiber hK₀ hT
  -- C02 with `ρ = rho n k`
  obtain ⟨B, hB, hBc, hBcard⟩ :=
    S.exists_energy_fiber hq1 (rho_pos' hn k).le (card_mul_rho_sq_le hcard hn)
  refine ⟨Finset.univ \ ptSet φ n q k A B,
    S.isNikodym_univ_sdiff_ptSet hk hcard hn hqF hq1 rfl rfl hA hAs hB hBc, ?_⟩
  rw [card_univ_sdiff_real, S.card_ptSet hcard hn hqF hq1 rfl rfl hA hB]
  push_cast
  rw [sub_sub_cancel]
  exact card_prod_ge S hK₀ hcard hn hk hq hAcard hBcard

end FixedScaffold

end Scaffold

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
