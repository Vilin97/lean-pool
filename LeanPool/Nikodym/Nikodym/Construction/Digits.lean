/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import LeanPool.Nikodym.Nikodym.Construction.Scaffold

/-!
# Mixed-radix digits and the decoding inequality

This file implements blueprint nodes D01 and D02 of
`docs/nikodym_construction_lean_blueprint.md`.

* D01: for radices `Q : Fin k → ℕ` the mixed-radix weights `Scaffold.D Q i = ∏_{j < i} Q j`
  (so `D Q 0 = 1` and `D Q (i+1) = D Q i * Q i`), and the digit lemma `Scaffold.digits_eq_zero`:
  if `θ √n < 1`, `β i ∈ box (θ * Q i)` for all `i` and `∑ i, D Q i * β i = 0`, then `β = 0`.
  Consequently `w ↦ ∑ i, D Q i * w i` is injective on `∏ i, box (ρ * Q i)` whenever
  `2 ρ √n < 1` (`Scaffold.digitMap_injOn`, `Scaffold.digitMap_injOn_piFinset`).
* D02: the decoding inequality `Scaffold.decoding`: with `x = u + Q w` and `x' = u' + Q w'`, if
  `trace (x ^ 2) = trace (x' ^ 2)` and `trace (w (x' - x)) = 0` then
  `|Q| ‖emb (w' - w)‖ ≤ ‖emb u‖ + ‖emb u'‖`; and `Scaffold.decoding_eq`: if moreover
  `‖emb u‖ + ‖emb u'‖ < Q` then `w = w'`.

Throughout, `n` denotes `Fintype.card ι`.
-/

namespace Nikodym

namespace Scaffold

/-! ### Blueprint D02: the decoding inequality -/

section Decoding

variable {R ι : Type*} [CommRing R] [Fintype ι] {σ : ι → R →+* ℝ}

/-- Blueprint D02: the decoding inequality. With `x = u + Q w` and `x' = u' + Q w'`, if
`trace (x ^ 2) = trace (x' ^ 2)` and `trace (w (x' - x)) = 0`, then
`|Q| ‖emb (w' - w)‖ ≤ ‖emb u‖ + ‖emb u'‖`. -/
theorem decoding (Q : ℤ) (u u' w w' : R)
    (hx : trace σ ((u + (Q : R) * w) ^ 2) = trace σ ((u' + (Q : R) * w') ^ 2))
    (hw : trace σ (w * ((u' + (Q : R) * w') - (u + (Q : R) * w))) = 0) :
    |Q| * ‖emb σ (w' - w)‖ ≤ ‖emb σ u‖ + ‖emb σ u'‖ := by
  set v : R := u' + (Q : R) * (w' - w) with hv
  -- `trace (v ^ 2) = trace (u ^ 2)`
  have hring : v ^ 2 = u ^ 2 + ((u' + (Q : R) * w') ^ 2 - (u + (Q : R) * w) ^ 2)
      - ((2 * Q : ℤ) : R) * (w * ((u' + (Q : R) * w') - (u + (Q : R) * w))) := by
    rw [hv]; push_cast; ring
  have htr : trace σ (v ^ 2) = trace σ (u ^ 2) := by
    rw [hring, trace_sub, trace_add, trace_sub, trace_intCast_mul, hx, hw]
    ring
  -- hence `‖emb v‖ = ‖emb u‖`
  have hnorm : ‖emb σ v‖ = ‖emb σ u‖ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_emb_sq, norm_emb_sq, htr]
  -- and `Q (w' - w) = v - u'`
  have hQ : (Q : R) * (w' - w) = v - u' := by rw [hv]; ring
  calc |Q| * ‖emb σ (w' - w)‖ = ‖emb σ ((Q : R) * (w' - w))‖ := (norm_emb_intCast_mul Q _).symm
    _ = ‖emb σ v - emb σ u'‖ := by rw [hQ, emb_sub]
    _ ≤ ‖emb σ v‖ + ‖emb σ u'‖ := norm_sub_le _ _
    _ = ‖emb σ u‖ + ‖emb σ u'‖ := by rw [hnorm]

end Decoding

section DecodingScaffold

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint D02: decoding. If `0 < Q`, `trace ((u + Q w) ^ 2) = trace ((u' + Q w') ^ 2)`,
`trace (w ((u' + Q w') - (u + Q w))) = 0` and `‖emb u‖ + ‖emb u'‖ < Q`, then `w = w'`. -/
theorem decoding_eq (h : Scaffold b σ φ K₀ K₁) {Q : ℤ} (hQ : 0 < Q) {u u' w w' : R}
    (hx : trace σ ((u + (Q : R) * w) ^ 2) = trace σ ((u' + (Q : R) * w') ^ 2))
    (hw : trace σ (w * ((u' + (Q : R) * w') - (u + (Q : R) * w))) = 0)
    (hsmall : ‖emb σ u‖ + ‖emb σ u'‖ < Q) : w = w' := by
  by_contra hne
  have hne' : w' - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have h1 := h.one_le_norm_emb hne'
  have h2 := decoding Q u u' w w' hx hw
  have hQ' : ((|Q| : ℤ) : ℝ) = Q := by rw [abs_of_pos hQ]
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [hQ'] at h2
  nlinarith

end DecodingScaffold

/-! ### Blueprint D01: mixed-radix weights -/

section Weights

/-- Blueprint D01: the mixed-radix weight `D Q i = ∏_{j < i} Q j` of the radices
`Q : Fin k → ℕ`; so `D Q 0 = 1` and `D Q (i + 1) = D Q i * Q i`. -/
def D {k : ℕ} (Q : Fin k → ℕ) (i : Fin k) : ℕ := ∏ j ∈ Finset.univ.filter (· < i), Q j

variable {k : ℕ}

/-- Blueprint D01: `D` as a product over `Finset.Iio`. -/
theorem D_eq_prod_Iio (Q : Fin k → ℕ) (i : Fin k) : D Q i = ∏ j ∈ Finset.Iio i, Q j := by
  unfold D
  congr 1
  ext j
  simp

/-- Blueprint D01: `D` as a product over the filter `{j | j < i}`. -/
theorem D_eq_prod_filter (Q : Fin k → ℕ) (i : Fin k) :
    D Q i = ∏ j ∈ Finset.univ.filter (· < i), Q j := rfl

/-- Blueprint D01: `D Q 0 = 1`. -/
@[simp] theorem D_zero (Q : Fin (k + 1) → ℕ) : D Q 0 = 1 := by
  unfold D
  refine Finset.prod_eq_one fun j hj ↦ ?_
  simp at hj

/-- Blueprint D01: `D Q i = 1` for `i = ⟨0, _⟩`. -/
theorem D_mk_zero (Q : Fin k → ℕ) (hk : 0 < k) : D Q ⟨0, hk⟩ = 1 := by
  unfold D
  refine Finset.prod_eq_one fun j hj ↦ ?_
  simp [Fin.lt_def] at hj

/-- Blueprint D01: the recursion `D Q (i + 1) = D Q i * Q i` (with `i` viewed in `Fin (k + 1)`
via `Fin.castSucc`). -/
theorem D_succ_eq_mul (Q : Fin (k + 1) → ℕ) (i : Fin k) :
    D Q i.succ = D Q i.castSucc * Q i.castSucc := by
  unfold D
  have hset : Finset.univ.filter (· < i.succ) =
      insert i.castSucc (Finset.univ.filter (· < i.castSucc)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Fin.lt_def, Fin.ext_iff, Fin.val_succ, Fin.val_castSucc]
    omega
  rw [hset, Finset.prod_insert (by simp), mul_comm]

/-- Blueprint D01: shifting the radices, `D Q i.succ = Q 0 * D (Fin.tail Q) i`. -/
theorem D_succ (Q : Fin (k + 1) → ℕ) (i : Fin k) : D Q i.succ = Q 0 * D (Fin.tail Q) i := by
  unfold D
  rw [Finset.prod_filter, Finset.prod_filter, Fin.prod_univ_succ]
  simp only [Fin.succ_pos, ite_true, Fin.succ_lt_succ_iff]
  rfl

/-- Blueprint D01: `D (Fin.cons q Q) 0 = 1`. -/
 theorem D_cons_zero (q : ℕ) (Q : Fin k → ℕ) : D (Fin.cons q Q) 0 = 1 := D_zero _

/-- Blueprint D01: `D (Fin.cons q Q) i.succ = q * D Q i`. -/
@[simp] theorem D_cons_succ (q : ℕ) (Q : Fin k → ℕ) (i : Fin k) :
    D (Fin.cons q Q) i.succ = q * D Q i := by
  rw [D_succ, Fin.cons_zero, Fin.tail_cons]

/-- Blueprint D01: `Q j ∣ D Q i` for `j < i`. -/
theorem Q_dvd_D (Q : Fin k → ℕ) {i j : Fin k} (hji : j < i) : Q j ∣ D Q i :=
  Finset.dvd_prod_of_mem _ (by simpa using hji)

/-- Blueprint D01: `D Q i ∣ D Q j` for `i ≤ j`. -/
theorem D_dvd_D (Q : Fin k → ℕ) {i j : Fin k} (hij : i ≤ j) : D Q i ∣ D Q j := by
  unfold D
  refine Finset.prod_dvd_prod_of_subset _ _ _ fun l hl ↦ ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
  exact lt_of_lt_of_le hl hij

/-- Blueprint D01: `D Q i > 0` when all radices are `≥ 1`. -/
theorem D_pos (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i) (i : Fin k) : 0 < D Q i :=
  Finset.prod_pos fun j _ ↦ hQ j

/-- Blueprint D01: `1 ≤ D Q i` when all radices are `≥ 1`. -/
theorem one_le_D (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i) (i : Fin k) : 1 ≤ D Q i :=
  D_pos Q hQ i

/-- Blueprint D01: `D` is monotone when all radices are `≥ 1`. -/
theorem D_le_D (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i) {i j : Fin k} (hij : i ≤ j) :
    D Q i ≤ D Q j :=
  Nat.le_of_dvd (D_pos Q hQ j) (D_dvd_D Q hij)

end Weights

/-! ### Blueprint D01: the digit lemma -/

section Digits

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint D01: mixed-radix digit lemma. If `θ √n < 1`, all radices are `≥ 1`,
`β i ∈ box (θ * Q i)` for all `i` and `∑ i, D Q i * β i = 0`, then `β = 0`. -/
theorem digits_eq_zero (h : Scaffold b σ φ K₀ K₁) {θ : ℝ}
    (hθ : θ * Real.sqrt (Fintype.card ι) < 1) {k : ℕ} (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i)
    (β : Fin k → R) (hβ : ∀ i, β i ∈ box σ (θ * Q i))
    (hsum : ∑ i, (D Q i : R) * β i = 0) : β = 0 := by
  induction k with
  | zero => funext i; exact i.elim0
  | succ k ih =>
    -- split off the head term
    rw [Fin.sum_univ_succ, D_zero, Nat.cast_one, one_mul] at hsum
    simp only [D_succ, Nat.cast_mul, mul_assoc, ← Finset.mul_sum] at hsum
    set S : R := ∑ i : Fin k, (D (Fin.tail Q) i : R) * β i.succ with hS
    have hβ0 : β 0 = (Q 0 : R) * (-S) := by rw [mul_neg, eq_neg_iff_add_eq_zero]; exact hsum
    -- the head coefficient forces `S = 0`
    have hS0 : S = 0 := by
      by_contra hne
      have h1 : 1 ≤ ‖emb σ (-S)‖ := h.one_le_norm_emb (neg_ne_zero.mpr hne)
      have hQ0 : (1 : ℝ) ≤ Q 0 := by exact_mod_cast hQ 0
      have hle : ‖emb σ (β 0)‖ ≤ Real.sqrt (Fintype.card ι) * (θ * Q 0) := norm_emb_le (hβ 0)
      rw [hβ0, norm_emb_natCast_mul] at hle
      have hsq : 0 ≤ Real.sqrt (Fintype.card ι) := Real.sqrt_nonneg _
      nlinarith
    have hβ0' : β 0 = 0 := by rw [hβ0, hS0, neg_zero, mul_zero]
    -- the tail vanishes by the induction hypothesis
    have htail : Fin.tail β = 0 :=
      ih (Fin.tail Q) (fun i ↦ hQ i.succ) (Fin.tail β) (fun i ↦ hβ i.succ) hS0
    funext i
    induction i using Fin.cases with
    | zero => exact hβ0'
    | succ j => exact congrFun htail j

/-- Blueprint D01: the digit map `w ↦ ∑ i, D Q i * w i` is injective on `∏ i, box (ρ * Q i)`
whenever `2 ρ √n < 1`. -/
theorem digitMap_injOn (h : Scaffold b σ φ K₀ K₁) {ρ : ℝ}
    (hρ : 2 * ρ * Real.sqrt (Fintype.card ι) < 1) {k : ℕ} (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i) :
    Set.InjOn (fun w : Fin k → R ↦ ∑ i, (D Q i : R) * w i)
      {w | ∀ i, w i ∈ box σ (ρ * Q i)} := by
  intro w hw w' hw' heq
  have hβ : ∀ i, w i - w' i ∈ box σ (2 * ρ * Q i) := fun i ↦ by
    have := box_sub (hw i) (hw' i)
    rwa [show ρ * Q i + ρ * Q i = 2 * ρ * Q i by ring] at this
  have hsum : ∑ i, (D Q i : R) * (w i - w' i) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr heq
  have := h.digits_eq_zero hρ Q hQ (w - w') hβ hsum
  exact sub_eq_zero.mp this

/-- Blueprint D01: the digit map `w ↦ ∑ i, D Q i * w i` is injective on the finite product
`Fintype.piFinset fun i ↦ boxFinset (ρ * Q i)` whenever `2 ρ √n < 1`. -/
theorem digitMap_injOn_piFinset (h : Scaffold b σ φ K₀ K₁) {ρ : ℝ}
    (hρ : 2 * ρ * Real.sqrt (Fintype.card ι) < 1) {k : ℕ} (Q : Fin k → ℕ) (hQ : ∀ i, 1 ≤ Q i) :
    Set.InjOn (fun w : Fin k → R ↦ ∑ i, (D Q i : R) * w i)
      ↑(Fintype.piFinset fun i ↦ h.boxFinset (ρ * Q i)) := by
  refine (h.digitMap_injOn hρ Q hQ).mono fun w hw ↦ ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset] at hw
  intro i
  exact (h.mem_boxFinset).mp (hw i)

end Digits

end Scaffold

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
