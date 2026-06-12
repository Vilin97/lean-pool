/-
Copyright (c) 2026 Susanna Bertolini, Jaume de Dios Pont. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Susanna Bertolini, Jaume de Dios Pont
-/
/-
  # BlockDecomposition.lean
  Frequency-block decomposition of polynomials.
  Scaffolding notes: BlockDecomposition/block_definitions.md

  Dependencies: Definitions

  Public API:
  - `freqBlock`             (Def 5.1: I_ℓ)
  - `blockPoly`             (Def 5.2: U_ℓ)
  - `maxBlockIndex`         (Def 5.3: Λ)
  - `localPoly` / `remainderPoly` (Def 5.4: V_j, R_j)
  - `blocks_disjoint`       (Theorem 5.1)
  - `blocks_cover`          (Theorem 5.2)
  - `fockNorm_decomposes`   (Theorem 5.3)
  - `blocks_orthogonal_circle` (Theorem 5.4)
  - `freq_support_localPoly`   (Theorem 5.5)
  - `monomial_peak_localization` (Theorem 5.6)
-/
import LeanPool.PhaseRetrieval.Constant.Internal.Definitions

/-! # BlockDecomposition -/


open Finset Nat Real MeasureTheory

noncomputable section

namespace FockSPR

/-! ## Def 5.1: Frequency blocks

`I_ℓ = { n : ℕ | ℓ² ≤ n ∧ n < (ℓ+1)² }` for `ℓ ≥ 1`.
Note: `|I_ℓ| = 2ℓ + 1`.
-/

/-- The frequency block `I_ℓ = [ℓ², (ℓ+1)² − 1]`. -/
def freqBlock (ℓ : ℕ) : Finset ℕ :=
  Finset.Icc (ℓ ^ 2) ((ℓ + 1) ^ 2 - 1)

/-! ## Def 5.2: Block polynomials

`U_ℓ(z) = ∑_{n ∈ I_ℓ, n ≤ D} a_n z^n`.
-/

/-- The block polynomial: restriction of `U` to frequencies in `I_ℓ`. -/
def blockPoly {D : ℕ} (a : Fin D → ℂ) (ℓ : ℕ) (z : ℂ) : ℂ :=
  ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ then a k * z ^ (k.val + 1) else 0

/-! ## Def 5.3: Maximum block index

`Λ = ⌊√D⌋`.
-/

/-- `Λ = Nat.sqrt D` — the index of the last complete block. -/
def maxBlockIndex (D : ℕ) : ℕ := Nat.sqrt D

/-! ## Def 5.4: Local and remainder pieces

For fixed `M ≥ 1` and `j : ℕ`:
  `V_j = ∑_{ℓ : max(1,j−M) ≤ ℓ ≤ min(Λ,j+M)} U_ℓ`
  `R_j = U − V_j`
-/

/-- The local polynomial around annulus `j`, collecting blocks within distance `M`. -/
def localPoly {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (z : ℂ) : ℂ :=
  ∑ ℓ ∈ Finset.Icc (max 1 (j - M)) (min (maxBlockIndex D) (j + M)),
    blockPoly a ℓ z

/-- The remainder polynomial: `R_j = U − V_j`. -/
def remainderPoly {D : ℕ} (a : Fin D → ℂ) (M j : ℕ) (z : ℂ) : ℂ :=
  polyEval a z - localPoly a M j z

/-! ### Helper lemmas -/

/-- An element belongs to at most one frequency block. -/
private lemma freqBlock_unique {n ℓ₁ ℓ₂ : ℕ}
    (h1 : n ∈ freqBlock ℓ₁) (h2 : n ∈ freqBlock ℓ₂) : ℓ₁ = ℓ₂ := by
  simp only [freqBlock, Finset.mem_Icc] at h1 h2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hsq : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₁ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega
  · have hsq : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have hpos : 0 < (ℓ₂ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
    omega

/-- Every natural number belongs to `freqBlock (Nat.sqrt n)`. -/
private lemma mem_freqBlock_sqrt (n : ℕ) : n ∈ freqBlock (Nat.sqrt n) := by
  simp only [freqBlock, Finset.mem_Icc]
  exact ⟨by have := Nat.sqrt_le n; nlinarith,
         by have h1 := Nat.lt_succ_sqrt' n; simp only [Nat.succ_eq_add_one] at h1; omega⟩

/-- The cardinality of `freqBlock ℓ` is `2ℓ + 1`. -/
lemma freqBlock_card (ℓ : ℕ) : (freqBlock ℓ).card = 2 * ℓ + 1 := by
  simp only [freqBlock]; rw [Nat.card_Icc]
  have h : (ℓ + 1) ^ 2 = ℓ ^ 2 + 2 * ℓ + 1 := by ring
  omega

/-! ### Fourier analysis helpers -/

-- to_mathlib: Mathlib.Analysis.Fourier.AddCircle
/-- Power of `fourier 1` equals the corresponding Fourier mode. -/
private lemma fourier_pow (t : AddCircle T) (n : ℕ) :
    ((fourier 1 t : ℂ)) ^ n = (fourier (↑n : ℤ) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ih, ← fourier_add]; push_cast; ring_nf

-- to_mathlib: Mathlib.Analysis.Fourier.AddCircle
/-- Power of `fourier (-1)` equals the corresponding negative Fourier mode. -/
private lemma fourier_neg_pow (t : AddCircle T) (n : ℕ) :
    ((fourier (-1 : ℤ) t : ℂ)) ^ n = (fourier (-(↑n : ℤ)) t : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, ← fourier_add]; congr 1; push_cast; ring_nf

-- to_mathlib: Mathlib.Analysis.Fourier.AddCircle
/-- The integral of a nonzero Fourier mode vanishes. -/
private lemma integral_fourier_ne_zero (k : ℤ) (hk : k ≠ 0) :
    ∫ t : AddCircle T, (fourier k t : ℂ) ∂AddCircle.haarAddCircle = 0 := by
  have h := congr_fun (fourierCoeff_fourier (T := T) 0) (-k)
  simp only [fourierCoeff, fourier_zero, Pi.single_apply, neg_neg, smul_eq_mul, mul_one] at h
  rwa [if_neg (by omega)] at h

/-- Continuous functions on `AddCircle T` are integrable w.r.t. Haar measure. -/
private lemma addCircle_integrable {f : AddCircle T → ℂ} (hf : Continuous f) :
    Integrable f AddCircle.haarAddCircle :=
  integrableOn_univ.mp (hf.continuousOn.integrableOn_compact isCompact_univ)

/-- A monomial term `c * (r * fourier 1 t) ^ n` is continuous in `t`. -/
private lemma continuous_term (c : ℂ) (r : ℝ) (n : ℕ) :
    Continuous (fun t : AddCircle T => c * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ n) :=
  continuous_const.mul (continuous_const.mul (fourier 1).continuous |>.pow n)

/-- Each summand in the double-sum expansion of blockPoly products is integrable. -/
private lemma integrable_term {D : ℕ} (a : Fin D → ℂ) (ℓ₁ ℓ₂ : ℕ) (r : ℝ)
    (i j : Fin D) :
    Integrable (fun t : AddCircle T =>
      (if (i.val + 1) ∈ freqBlock ℓ₁
        then a i * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (i.val + 1) else 0) *
      starRingEnd ℂ (if (j.val + 1) ∈ freqBlock ℓ₂
        then a j * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (j.val + 1) else 0))
    AddCircle.haarAddCircle := by
  apply addCircle_integrable; apply Continuous.mul
  · split_ifs <;> [exact continuous_term _ _ _; exact continuous_const]
  · exact Complex.continuous_conj.comp
      (by split_ifs <;> [exact continuous_term _ _ _; exact continuous_const])

/-- When both frequency conditions hold, the integrand is a constant times a Fourier mode
    with nonzero index, hence integrates to zero. -/
private lemma integral_cross_term_eq_zero {D : ℕ} (a : Fin D → ℂ) (r : ℝ)
    (k₁ k₂ : Fin D) (hne_k : (k₁.val + 1 : ℕ) ≠ k₂.val + 1) :
    ∫ t : AddCircle T,
      a k₁ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₁.val + 1) *
      (starRingEnd ℂ) (a k₂ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₂.val + 1))
      ∂AddCircle.haarAddCircle = 0 := by
  set c := a k₁ * starRingEnd ℂ (a k₂) *
    (↑r : ℂ) ^ (k₁.val + 1 + (k₂.val + 1))
  set m := (↑(k₁.val + 1) - ↑(k₂.val + 1) : ℤ) with hm_def
  have key : ∀ t : AddCircle T,
      a k₁ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₁.val + 1) *
      (starRingEnd ℂ) (a k₂ * ((↑r : ℂ) * (fourier 1 t : ℂ)) ^ (k₂.val + 1)) =
      c * (fourier m t : ℂ) := by
    intro t
    rw [map_mul (f := starRingEnd ℂ), map_pow (f := starRingEnd ℂ),
        map_mul (f := starRingEnd ℂ) (x := (↑r : ℂ)), Complex.conj_ofReal,
        ← fourier_neg (n := (1 : ℤ)),
        mul_pow (a := (↑r : ℂ)) (b := (fourier 1 t : ℂ)),
        mul_pow (a := (↑r : ℂ)) (b := (fourier (-1 : ℤ) t : ℂ)),
        fourier_pow t (k₁.val + 1), fourier_neg_pow t (k₂.val + 1)]
    simp only [c, m]
    calc a k₁ * ((↑r : ℂ) ^ (k₁.val + 1) *
            (fourier (↑(k₁.val + 1) : ℤ) t : ℂ)) *
          (starRingEnd ℂ (a k₂) * ((↑r : ℂ) ^ (k₂.val + 1) *
            (fourier (-(↑(k₂.val + 1) : ℤ)) t : ℂ)))
        = (a k₁ * starRingEnd ℂ (a k₂) *
            ((↑r : ℂ) ^ (k₁.val + 1) * (↑r : ℂ) ^ (k₂.val + 1))) *
          ((fourier (↑(k₁.val + 1) : ℤ) t : ℂ) *
            (fourier (-(↑(k₂.val + 1) : ℤ)) t : ℂ)) := by ring
      _ = (a k₁ * starRingEnd ℂ (a k₂) *
            (↑r : ℂ) ^ (k₁.val + 1 + (k₂.val + 1))) *
          (fourier (↑(k₁.val + 1) - ↑(k₂.val + 1) : ℤ) t : ℂ) := by
            rw [pow_add, ← fourier_add]; congr 1; ring
  simp_rw [key]
  have hm : m ≠ 0 := by simp only [m]; push_cast; omega
  have h_eq : ∫ t : AddCircle T, c * (fourier m t : ℂ)
      ∂AddCircle.haarAddCircle =
      c * ∫ t : AddCircle T, (fourier m t : ℂ) ∂AddCircle.haarAddCircle :=
    integral_const_mul c _
  rw [h_eq, integral_fourier_ne_zero m hm, mul_zero]

/-! ## Theorem 5.1: Blocks are frequency-disjoint

For `ℓ₁ ≠ ℓ₂` with `ℓ₁, ℓ₂ ≥ 1`: `I_{ℓ₁} ∩ I_{ℓ₂} = ∅`.
-/
theorem blocks_disjoint {ℓ₁ ℓ₂ : ℕ} (h₁ : 1 ≤ ℓ₁) (h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) :
    Disjoint (freqBlock ℓ₁) (freqBlock ℓ₂) := by
  rw [Finset.disjoint_left]
  intro a ha₁ ha₂
  simp only [freqBlock, Finset.mem_Icc] at ha₁ ha₂
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have hle : ℓ₁ + 1 ≤ ℓ₂ := h
    have hsq : (ℓ₁ + 1) ^ 2 ≤ ℓ₂ ^ 2 := Nat.pow_le_pow_left hle 2
    have ha_upper : a + 1 ≤ (ℓ₁ + 1) ^ 2 := by
      have : 0 < (ℓ₁ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    omega
  · have hle : ℓ₂ + 1 ≤ ℓ₁ := h
    have hsq : (ℓ₂ + 1) ^ 2 ≤ ℓ₁ ^ 2 := Nat.pow_le_pow_left hle 2
    have ha_upper : a + 1 ≤ (ℓ₂ + 1) ^ 2 := by
      have : 0 < (ℓ₂ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    omega

/-! ## Theorem 5.2: Blocks partition {1, …, D}

Every `n ∈ {1, …, D}` belongs to exactly one block `I_ℓ`.
-/
theorem blocks_cover (D : ℕ) (n : ℕ) (hn : 1 ≤ n) (_hnD : n ≤ D) :
    ∃ ℓ, 1 ≤ ℓ ∧ n ∈ freqBlock ℓ := by
  refine ⟨Nat.sqrt n, ?_, ?_⟩
  · exact Nat.sqrt_pos.mpr (by omega)
  · simp only [freqBlock, Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have := Nat.sqrt_le n; nlinarith
    · have h1 := Nat.lt_succ_sqrt' n
      simp only [Nat.succ_eq_add_one] at h1; omega

/-! ## Theorem 5.3: Fock norm decomposes

`fockNormSq(U) = ∑_{ℓ=1}^Λ fockNormSq(U_ℓ)` (up to tail).

**Proof**: The blocks are frequency-disjoint, and `fockNormSq` is a sum over frequencies.
-/
theorem fockNorm_decomposes {D : ℕ} (a : Fin D → ℂ) :
    fockNormSq a = ∑ ℓ ∈ Finset.Icc 1 (maxBlockIndex D),
      ∑ k : Fin D, if (k.val + 1) ∈ freqBlock ℓ
        then ‖a k‖ ^ 2 * (Nat.factorial (k.val + 1) : ℝ) else 0 := by
  unfold fockNormSq
  rw [← Finset.sum_comm]
  congr 1; ext k
  have hk_mem : (k.val + 1) ∈ freqBlock (Nat.sqrt (k.val + 1)) :=
    mem_freqBlock_sqrt _
  have hℓ_mem : Nat.sqrt (k.val + 1) ∈ Finset.Icc 1 (maxBlockIndex D) := by
    simp only [maxBlockIndex, Finset.mem_Icc]
    exact ⟨Nat.sqrt_pos.mpr (by omega), Nat.sqrt_le_sqrt (by omega)⟩
  rw [Finset.sum_eq_single_of_mem _ hℓ_mem]
  · simp [hk_mem]
  · intro b _ hbne
    have : (k.val + 1) ∉ freqBlock b :=
      fun hmem => hbne (freqBlock_unique hmem hk_mem)
    simp [this]

/-! ## Theorem 5.4: Orthogonality on circles

For `ℓ₁ ≠ ℓ₂`, `r ≥ 0`:
  `∫ U_{ℓ₁}(r e^{it}) * conj(U_{ℓ₂}(r e^{it})) d(haar)(t) = 0`

**Proof**: Disjoint frequency supports ⟹ orthogonality of exponentials.
-/
theorem blocks_orthogonal_circle {D : ℕ} (a : Fin D → ℂ) {ℓ₁ ℓ₂ : ℕ}
    (_h₁ : 1 ≤ ℓ₁) (_h₂ : 1 ≤ ℓ₂) (hne : ℓ₁ ≠ ℓ₂) (r : ℝ) (_hr : 0 ≤ r) :
    ∫ t : AddCircle T,
      (blockPoly a ℓ₁ (↑r * (fourier 1 t : ℂ))) *
      starRingEnd ℂ (blockPoly a ℓ₂ (↑r * (fourier 1 t : ℂ)))
      ∂AddCircle.haarAddCircle = 0 := by
  simp_rw [blockPoly, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (fun k₁ _ =>
    integrable_finsetSum _ (fun k₂ _ => integrable_term a ℓ₁ ℓ₂ r k₁ k₂))]
  apply Finset.sum_eq_zero; intro k₁ _
  rw [integral_finsetSum Finset.univ
    (fun k₂ _ => integrable_term a ℓ₁ ℓ₂ r k₁ k₂)]
  apply Finset.sum_eq_zero; intro k₂ _
  split_ifs with h₁' h₂'
  · -- Both conditions hold: use Fourier orthogonality
    exact integral_cross_term_eq_zero a r k₁ k₂
      (fun heq => hne (freqBlock_unique (heq ▸ h₁') h₂'))
  · simp [map_zero]
  · simp
  · simp

/-! ## Theorem 5.5: Frequency support of V_j

For `j ≥ M + 1`:
- Frequency support of `V_j` ⊆ `[(j−M)², (j+M+1)²)`.
- All frequencies ≥ 1.
- Number of frequencies: `L_j = (2M+1)(2j+1)`.

For `0 ≤ j ≤ M`:
- Frequency support ⊆ `[1, (j+M+1)²)`.
- Number of frequencies ≤ `(j+M+1)² − 1`.
-/
/-- Frequencies of `V_j` are all ≥ `(j−M)²` when `j ≥ M + 1`. -/
theorem freq_support_localPoly_lower {M j : ℕ} (_hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    ∀ n ∈ freqBlock ℓ,
      ℓ ∈ Finset.Icc (max 1 (j - M)) (j + M) → (j - M) ^ 2 ≤ n := by
  intro n hn hℓ
  simp only [freqBlock, Finset.mem_Icc] at hn hℓ
  calc (j - M) ^ 2 ≤ ℓ ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ ≤ n := hn.1

/-- Telescoping sum of odd numbers: `∑_{ℓ=a}^{a+n} (2ℓ+1) = (a+n+1)² − a²`. -/
private lemma sum_odd_Icc_eq (a : ℕ) :
    ∀ n : ℕ, (Finset.Icc a (a + n)).sum (fun ℓ => 2 * ℓ + 1) =
      (a + n + 1) ^ 2 - a ^ 2 := by
  intro n; induction n with
  | zero => simp [Finset.Icc_self]; ring_nf; omega
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from by omega]
    rw [Finset.sum_Icc_succ_top (by omega)]; rw [ih]; ring_nf; omega

/-- The number of frequencies in `V_j` for `j ≥ M + 1` is `(2M+1)(2j+1)`. -/
theorem freq_count_localPoly {M j : ℕ} (hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    (Finset.Icc (max 1 (j - M)) (j + M)).sum
      (fun ℓ => (freqBlock ℓ).card) =
      (2 * M + 1) * (2 * j + 1) := by
  rw [show max 1 (j - M) = j - M from by omega]
  simp_rw [freqBlock_card]
  rw [show j + M = (j - M) + (2 * M) from by omega,
      sum_odd_Icc_eq (j - M) (2 * M),
      show j - M + 2 * M + 1 = j + M + 1 from by omega]
  have hle : (j - M) ^ 2 ≤ (j + M + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  zify [hle, show M ≤ j from by omega]; ring

/-! ## Theorem 5.6: Monomial peak localization

For `n ∈ I_ℓ` with `ℓ ≥ 1`:
  `ℓ < √(n + 1/2) < ℓ + 1`
i.e., `r_n = √(n + 1/2) ∈ (ℓ, ℓ+1)`.

**Proof**: `n ≥ ℓ²` gives `n + 1/2 > ℓ²`, so `√(n+1/2) > ℓ`.
`n < (ℓ+1)²` gives `n + 1/2 < (ℓ+1)²`, so `√(n+1/2) < ℓ+1`.
-/
theorem monomial_peak_localization {n ℓ : ℕ} (hℓ : 1 ≤ ℓ)
    (hn : n ∈ freqBlock ℓ) :
    (ℓ : ℝ) < Real.sqrt (n + 1 / 2) ∧
      Real.sqrt (n + 1 / 2) < (ℓ + 1 : ℝ) := by
  simp only [freqBlock, Finset.mem_Icc] at hn
  constructor
  · rw [show (ℓ : ℝ) = Real.sqrt ((ℓ : ℝ) ^ 2) from by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_lt_sqrt (by positivity)
    have : (ℓ : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast hn.1
    linarith
  · rw [show (ℓ + 1 : ℝ) = Real.sqrt ((ℓ + 1 : ℝ) ^ 2) from by
      rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_lt_sqrt
      (by linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])
    have h1 : n + 1 ≤ (ℓ + 1) ^ 2 := by
      have : 0 < (ℓ + 1) ^ 2 := Nat.pos_of_ne_zero (by positivity)
      omega
    have : (n : ℝ) + 1 ≤ ((ℓ + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast h1
    push_cast at this ⊢; linarith

end FockSPR
