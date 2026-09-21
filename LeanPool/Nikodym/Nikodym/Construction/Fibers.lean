/-
Copyright (c) 2026 Shengtong Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shengtong Zhang
-/

import Mathlib.Combinatorics.Pigeonhole
import LeanPool.Nikodym.Nikodym.Construction.Digits
import LeanPool.Nikodym.Nikodym.Construction.Parameters

/-!
# Fibers: the trace fiber and the energy fiber

This file implements blueprint nodes C01 and C02 of `docs/nikodym_construction_lean_blueprint.md`.

* C01: `Scaffold.exists_trace_fiber`: under `Scaffold` with `K₀ > 0`, for every real `T ≥ 1` there
  is an integer `s` and a `Finset` `A ⊆ boxFinset T` on which the trace is constantly `s`, with
  `(T / (n * K₀)) ^ n / ((2 * n + 1) * T) ≤ #A`.
* C02: the energy fiber of the digit space. Everything is parametrised by `k = h - 1`, the
  number of digits. `Scaffold.radix n q k : Fin k → ℕ` is the radix vector `(Q₁, …, Q_k)` of
  Q01, and `Scaffold.D_radix` identifies the mixed-radix weights of D01 with the products `Dᵢ` of
  Q01: `D (radix n q k) i = Params.D n q (i + 1)`. The digit space is
  `Scaffold.digitSpace S n q k ρ = ∏ i, boxFinset (ρ * Qᵢ₊₁)`, the prefix sums are
  `Scaffold.prefixSum n q k w i = ∑_{j ≤ i} Dⱼ wⱼ` (`= yᵢ(w)`), the base point is
  `Scaffold.base n q k w = ∑ j, Dⱼ wⱼ` (`= b(w)`), and the color is
  `Scaffold.color σ n q k w i = trace (yᵢ(w) ^ 2)` (an integer). The main results are the prefix
  bound `Scaffold.abs_prefixSum_le`, the base bounds `Scaffold.abs_base_le`,
  `Scaffold.abs_base_le_M`, the color bound `Scaffold.color_mem_colorBox`, the pigeonhole
  theorem `Scaffold.exists_energy_fiber` producing a color class `B ⊆ digitSpace` with
  `#digitSpace / (2 ^ k * ∏ i, D_{i+2} ^ 2) ≤ #B`, and injectivity of `base` on the digit space
  (`Scaffold.base_injOn`, `Scaffold.card_image_base`).

Throughout, `n` denotes `Fintype.card ι` in Layer S/D statements; in Layer C, `n` and `q` are the
integer parameters of Q01 and the number of embeddings is written `Fintype.card ι`.
-/

namespace Nikodym

namespace Scaffold

section TraceFiber

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint C01: the trace of an element of the box of radius `T` lies in
`Finset.Icc (-⌊n * T⌋) ⌊n * T⌋`. -/
theorem floor_trace_mem_Icc (h : Scaffold b σ φ K₀ K₁) {T : ℝ} {x : R}
    (hx : ∀ i, |σ i x| ≤ T) :
    ⌊trace σ x⌋ ∈ Finset.Icc (-⌊(Fintype.card ι : ℝ) * T⌋) ⌊(Fintype.card ι : ℝ) * T⌋ := by
  obtain ⟨z, hz⟩ := h.trace_int x
  have hz' : trace σ x = z := hz
  have habs := abs_trace_le σ hx
  rw [hz', abs_le] at habs
  rw [hz', Int.floor_intCast, Finset.mem_Icc]
  constructor
  · rw [neg_le]
    exact Int.le_floor.mpr (by push_cast; linarith [habs.1])
  · exact Int.le_floor.mpr habs.2

/-- Blueprint C01: the trace fiber. Under `Scaffold` with `K₀ > 0`, for every real `T ≥ 1` there is
an integer `s` and a `Finset` `A ⊆ boxFinset T` on which the trace is constantly `s`, with
`(T / (n * K₀)) ^ n / ((2 * n + 1) * T) ≤ #A`. -/
theorem exists_trace_fiber (h : Scaffold b σ φ K₀ K₁) (hK₀ : 0 < K₀) {T : ℝ} (hT : 1 ≤ T) :
    ∃ (s : ℤ) (A : Finset R), A ⊆ h.boxFinset T ∧ (∀ a ∈ A, trace σ a = s) ∧
      (T / (Fintype.card ι * K₀)) ^ Fintype.card ι / ((2 * Fintype.card ι + 1) * T) ≤
        (A.card : ℝ) := by
  classical
  set n := Fintype.card ι with hn
  set N : ℤ := ⌊(n : ℝ) * T⌋ with hN
  set t : Finset ℤ := Finset.Icc (-N) N with ht
  set s : Finset R := h.boxFinset T with hs
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hN0 : 0 ≤ N := Int.floor_nonneg.mpr (by positivity)
  -- the size of the target set
  have ht_card : (t.card : ℝ) = 2 * (N : ℝ) + 1 := by
    have := Int.card_Icc_of_le (a := -N) (b := N) (by omega)
    have h' : ((t.card : ℤ) : ℝ) = ((N + 1 - -N : ℤ) : ℝ) := by rw [ht, this]
    push_cast at h'
    linarith
  have ht_pos : (0 : ℝ) < t.card := by rw [ht_card]; positivity
  have ht_le : (t.card : ℝ) ≤ (2 * n + 1) * T := by
    rw [ht_card]
    have := Int.floor_le ((n : ℝ) * T)
    rw [← hN] at this
    nlinarith
  have ht_ne : t.Nonempty := ⟨0, by rw [ht, Finset.mem_Icc]; omega⟩
  -- the floor of the trace maps the box into `t`
  have hmaps : ∀ a ∈ s, ⌊trace σ a⌋ ∈ t := fun a ha ↦
    h.floor_trace_mem_Icc ((h.mem_boxFinset).mp ha)
  -- pigeonhole
  obtain ⟨y, -, hy⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (s.card : ℝ) / t.card) hmaps ht_ne
    (by rw [nsmul_eq_mul, mul_div_cancel₀ _ ht_pos.ne'])
  refine ⟨y, s.filter (fun a ↦ ⌊trace σ a⌋ = y), Finset.filter_subset _ _, ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨z, hz⟩ := h.trace_int a
    have hz' : trace σ a = z := hz
    rw [hz', Int.floor_intCast] at ha
    rw [hz', ha.2]
  · refine le_trans ?_ hy
    have hbox := h.le_card_boxFinset hK₀ hT0
    rw [← hn, ← hs] at hbox
    exact div_le_div₀ (Nat.cast_nonneg _) hbox (by positivity) ht_le

end TraceFiber

/-! ### Blueprint C02: the radix vector and the bridge between the two `D`s -/

section Radix

/-- Blueprint C02: the radix vector `(Q₁, …, Q_k)` of Q01, as a function on `Fin k`
(here `k = h - 1`): `radix n q k i = Params.Q n q (i + 1)`. -/
noncomputable def radix (n q k : ℕ) : Fin k → ℕ := fun i ↦ Params.Q n q (i.val + 1)

variable {n q k : ℕ}

/-- Blueprint C02: `radix n q k i = Params.Q n q (i + 1)`. -/
@[simp] theorem radix_apply (i : Fin k) : radix n q k i = Params.Q n q (i.val + 1) := rfl

/-- Blueprint C02: all radices are `≥ 1` when `q ≥ 1`. -/
theorem radix_pos (hq : 1 ≤ q) (i : Fin k) : 1 ≤ radix n q k i :=
  Params.Q_pos hq _

/-- Blueprint C02: the bridge between the mixed-radix weights of D01 and the products of Q01:
`D (radix n q k) i = Params.D n q (i + 1)` (both are `∏_{j=1}^{i} Q_j`). -/
theorem D_radix (i : Fin k) : D (radix n q k) i = Params.D n q (i.val + 1) := by
  rw [D_eq_prod_Iio, Params.D, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel,
    ← Nat.Iio_eq_range, ← Fin.map_valEmbedding_Iio, Finset.prod_map]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  simp only [radix_apply, Fin.valEmbedding_apply, add_comm]

/-- Blueprint C02: `D (radix n q k) j * Q_{j+1} = Params.D n q (j + 2)`. -/
theorem D_radix_mul_radix (i : Fin k) :
    D (radix n q k) i * radix n q k i = Params.D n q (i.val + 2) := by
  rw [D_radix, radix_apply, ← Params.D_succ (by omega)]

end Radix

/-! ### Blueprint C02: the digit space, prefix sums, base point and colors -/

section DigitSpace

variable {R ι κ F : Type*} [CommRing R] [Fintype ι] [Fintype κ] [Field F] [Fintype F]
variable {b : Module.Basis κ ℤ R} {σ : ι → R →+* ℝ} {φ : R →+* F} {K₀ K₁ : ℝ}

/-- Blueprint C02: the digit space `W = ∏ i, boxFinset (ρ * Q_{i+1})` as a `Finset` of digit
vectors `Fin k → R`. -/
noncomputable def digitSpace (S : Scaffold b σ φ K₀ K₁) (n q k : ℕ) (ρ : ℝ) :
    Finset (Fin k → R) :=
  Fintype.piFinset fun i ↦ S.boxFinset (ρ * radix n q k i)

/-- Blueprint C02: the prefix sum `yᵢ(w) = ∑_{j ≤ i} Dⱼ wⱼ`. -/
noncomputable def prefixSum (n q k : ℕ) (w : Fin k → R) (i : Fin k) : R :=
  ∑ j ∈ Finset.Iic i, (D (radix n q k) j : R) * w j

/-- Blueprint C02: the base point `b(w) = ∑ j, Dⱼ wⱼ`. -/
noncomputable def base (n q k : ℕ) (w : Fin k → R) : R := ∑ j, (D (radix n q k) j : R) * w j

/-- Blueprint C02: the energy color `c(w)ᵢ = trace (yᵢ(w) ^ 2)`, landed in `ℤ` via the floor
(see `Scaffold.color_eq`: the trace is an integer). -/
noncomputable def color (σ : ι → R →+* ℝ) (n q k : ℕ) (w : Fin k → R) : Fin k → ℤ :=
  fun i ↦ ⌊trace σ (prefixSum n q k w i ^ 2)⌋

/-- Blueprint C02: the finite set of admissible colors `∏ i, Icc 0 (D_{i+2} ^ 2)`. -/
noncomputable def colorBox (n q k : ℕ) : Finset (Fin k → ℤ) :=
  Fintype.piFinset fun i ↦ Finset.Icc (0 : ℤ) ((Params.D n q (i.val + 2) : ℤ) ^ 2)

variable {n q k : ℕ} {ρ : ℝ}

/-- Blueprint C02: membership in the digit space. -/
theorem mem_digitSpace (S : Scaffold b σ φ K₀ K₁) {w : Fin k → R} :
    w ∈ digitSpace S n q k ρ ↔ ∀ i ε, |σ ε (w i)| ≤ ρ * radix n q k i := by
  simp only [digitSpace, Fintype.mem_piFinset, mem_boxFinset]

/-- Blueprint C02: `|W| = ∏ i, |boxFinset (ρ * Q_{i+1})|`. -/
theorem card_digitSpace (S : Scaffold b σ φ K₀ K₁) :
    (digitSpace S n q k ρ).card = ∏ i, (S.boxFinset (ρ * radix n q k i)).card :=
  Fintype.card_piFinset _

/-- Blueprint C02: the prefix sum as a sum over the filter `{j | j ≤ i}`. -/
theorem prefixSum_eq_sum_filter (w : Fin k → R) (i : Fin k) :
    prefixSum n q k w i = ∑ j ∈ Finset.univ.filter (· ≤ i), (D (radix n q k) j : R) * w j := by
  unfold prefixSum
  congr 1
  ext j
  simp

/-- Blueprint C02: `b(w) = y_{k-1}(w)` for `k ≥ 1`. -/
theorem base_eq_prefixSum_last (hk : 0 < k) (w : Fin k → R) :
    base n q k w = prefixSum n q k w ⟨k - 1, by omega⟩ := by
  unfold base prefixSum
  congr 1
  ext j
  simp only [Finset.mem_univ, Finset.mem_Iic, true_iff, Fin.le_def]
  exact Nat.le_sub_one_of_lt j.isLt

/-- Blueprint C02: the digit term `Dⱼ wⱼ` of a digit vector satisfies
`|σ (Dⱼ wⱼ)| ≤ ρ * Dⱼ Q_{j+1} = ρ * Params.D n q (j + 2)`. -/
theorem abs_term_le (S : Scaffold b σ φ K₀ K₁) {w : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) (j : Fin k) (ε : ι) :
    |σ ε ((D (radix n q k) j : R) * w j)| ≤ ρ * Params.D n q (j.val + 2) := by
  rw [mem_digitSpace] at hw
  rw [map_mul, map_natCast, abs_mul, Nat.abs_cast, ← D_radix_mul_radix, Nat.cast_mul]
  calc (D (radix n q k) j : ℝ) * |σ ε (w j)|
      ≤ D (radix n q k) j * (ρ * radix n q k j) :=
        mul_le_mul_of_nonneg_left (hw j ε) (Nat.cast_nonneg _)
    _ = ρ * (D (radix n q k) j * radix n q k j) := by ring

/-- Blueprint C02 (prefix bound): for `w ∈ W`, `yᵢ(w) ∈ box (ρ (i+1) D_{i+2})`. -/
theorem abs_prefixSum_le (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ) {w : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) (i : Fin k) (ε : ι) :
    |σ ε (prefixSum n q k w i)| ≤ ρ * (i.val + 1) * Params.D n q (i.val + 2) := by
  unfold prefixSum
  rw [map_sum]
  calc |∑ j ∈ Finset.Iic i, σ ε ((D (radix n q k) j : R) * w j)|
      ≤ ∑ j ∈ Finset.Iic i, |σ ε ((D (radix n q k) j : R) * w j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.Iic i).card • (ρ * Params.D n q (i.val + 2)) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j hj ↦ ?_
        refine (abs_term_le S hw j ε).trans ?_
        have hji : j ≤ i := Finset.mem_Iic.mp hj
        have hji' : j.val ≤ i.val := hji
        have hD := Params.D_mono (n := n) (q := q) hq (j := j.val + 2) (i := i.val + 2)
          (by omega) (by omega)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) hρ
    _ = ρ * (i.val + 1) * Params.D n q (i.val + 2) := by
        rw [Fin.card_Iic, nsmul_eq_mul]
        push_cast
        ring

/-- Blueprint C02 (prefix bound for the base point): for `w ∈ W`, `b(w) ∈ box (ρ k D_{k+1})`. -/
theorem abs_base_le (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ) {w : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) (ε : ι) :
    |σ ε (base n q k w)| ≤ ρ * k * Params.D n q (k + 1) := by
  unfold base
  rw [map_sum]
  calc |∑ j, σ ε ((D (radix n q k) j : R) * w j)|
      ≤ ∑ j, |σ ε ((D (radix n q k) j : R) * w j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.univ : Finset (Fin k)).card • (ρ * Params.D n q (k + 1)) := by
        refine Finset.sum_le_card_nsmul _ _ _ fun j _ ↦ ?_
        refine (abs_term_le S hw j ε).trans ?_
        have hjk := j.isLt
        have hD := Params.D_mono (n := n) (q := q) hq (j := j.val + 2) (i := k + 1)
          (by omega) (by omega)
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hD) hρ
    _ = ρ * k * Params.D n q (k + 1) := by
        rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Blueprint C02: for `w ∈ W`, `b(w) ∈ box (ρ k M)` (using `D_{k+1} ≤ M` from Q01). -/
theorem abs_base_le_M (S : Scaffold b σ φ K₀ K₁) (hn : 1 ≤ n) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    {w : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (ε : ι) :
    |σ ε (base n q k w)| ≤ ρ * k * Params.M n q := by
  refine (abs_base_le S hq hρ hw ε).trans ?_
  have hM : (Params.D n q (k + 1) : ℝ) ≤ Params.M n q := by
    exact_mod_cast Params.D_le_M hn hq (i := k + 1) (by omega)
  exact mul_le_mul_of_nonneg_left hM (mul_nonneg hρ (Nat.cast_nonneg _))

/-- Blueprint C02: for `w ∈ W`, `b(w) ∈ box (ρ h M)` with `h = k + 1`. -/
theorem abs_base_le_M' (S : Scaffold b σ φ K₀ K₁) (hn : 1 ≤ n) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    {w : Fin k → R} (hw : w ∈ digitSpace S n q k ρ) (ε : ι) :
    |σ ε (base n q k w)| ≤ ρ * (k + 1) * Params.M n q := by
  refine (abs_base_le_M S hn hq hρ hw ε).trans ?_
  have hM : (0 : ℝ) ≤ Params.M n q := Nat.cast_nonneg _
  nlinarith

/-- Blueprint C02: on the box of radius `T`, `trace (x ^ 2) ≤ n * T ^ 2`. -/
theorem trace_sq_le {x : R} {T : ℝ} (hx : ∀ i, |σ i x| ≤ T) :
    trace σ (x ^ 2) ≤ Fintype.card ι * T ^ 2 := by
  unfold trace
  calc ∑ i, σ i (x ^ 2) = ∑ i, (σ i x) ^ 2 := by simp [map_pow]
    _ ≤ ∑ _i : ι, T ^ 2 := Finset.sum_le_sum fun i _ ↦ by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hx i) 2
    _ = Fintype.card ι * T ^ 2 := by simp

variable (n q k)

/-- Blueprint C02: the color is the trace of the squared prefix sum (an integer). -/
theorem color_eq (S : Scaffold b σ φ K₀ K₁) (w : Fin k → R) (i : Fin k) :
    (color σ n q k w i : ℝ) = trace σ (prefixSum n q k w i ^ 2) := by
  obtain ⟨z, hz⟩ := S.trace_int (prefixSum n q k w i ^ 2)
  have hz' : trace σ (prefixSum n q k w i ^ 2) = z := hz
  simp only [color, hz', Int.floor_intCast]

/-- Blueprint C02: equal colors give equal energies `trace (yᵢ(w) ^ 2) = trace (yᵢ(w') ^ 2)`. -/
theorem trace_prefixSum_eq_of_color_eq (S : Scaffold b σ φ K₀ K₁) {w w' : Fin k → R}
    (h : color σ n q k w = color σ n q k w') (i : Fin k) :
    trace σ (prefixSum n q k w i ^ 2) = trace σ (prefixSum n q k w' i ^ 2) := by
  rw [← color_eq n q k S w i, ← color_eq n q k S w' i, h]

variable {n q k}

/-- Blueprint C02 (colors): under `n ρ² (k+1)² ≤ 1`, for `w ∈ W` the color satisfies
`0 ≤ c(w)ᵢ ≤ D_{i+2} ^ 2`. -/
theorem color_mem_Icc (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    (hρ2 : Fintype.card ι * ρ ^ 2 * (k + 1) ^ 2 ≤ 1) {w : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) (i : Fin k) :
    color σ n q k w i ∈ Finset.Icc 0 ((Params.D n q (i.val + 2) : ℤ) ^ 2) := by
  rw [Finset.mem_Icc]
  have hc := color_eq n q k S w i
  have h0 := trace_sq_nonneg σ (prefixSum n q k w i)
  have hT := trace_sq_le fun ε ↦ abs_prefixSum_le S hq hρ hw i ε
  have hi : (i.val + 1 : ℝ) ≤ k + 1 := by
    have := i.isLt
    exact_mod_cast (by omega : i.val + 1 ≤ k + 1)
  have hsq : (i.val + 1 : ℝ) ^ 2 ≤ (k + 1) ^ 2 := pow_le_pow_left₀ (by positivity) hi 2
  have hbound : trace σ (prefixSum n q k w i ^ 2) ≤ (Params.D n q (i.val + 2) : ℝ) ^ 2 := by
    calc trace σ (prefixSum n q k w i ^ 2)
        ≤ Fintype.card ι * (ρ * (i.val + 1) * Params.D n q (i.val + 2)) ^ 2 := hT
      _ = (Fintype.card ι * ρ ^ 2 * (i.val + 1) ^ 2) * (Params.D n q (i.val + 2) : ℝ) ^ 2 := by
          ring
      _ ≤ 1 * (Params.D n q (i.val + 2) : ℝ) ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          calc (Fintype.card ι : ℝ) * ρ ^ 2 * (i.val + 1) ^ 2
              ≤ Fintype.card ι * ρ ^ 2 * (k + 1) ^ 2 :=
                mul_le_mul_of_nonneg_left hsq (by positivity)
            _ ≤ 1 := hρ2
      _ = (Params.D n q (i.val + 2) : ℝ) ^ 2 := one_mul _
  constructor
  · have : (0 : ℝ) ≤ (color σ n q k w i : ℝ) := hc ▸ h0
    exact_mod_cast this
  · have : ((color σ n q k w i : ℤ) : ℝ) ≤ (((Params.D n q (i.val + 2) : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [hc]
      push_cast
      exact hbound
    exact_mod_cast this

/-- Blueprint C02 (colors): the color of a digit vector lies in `colorBox`. -/
theorem color_mem_colorBox (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    (hρ2 : Fintype.card ι * ρ ^ 2 * (k + 1) ^ 2 ≤ 1) {w : Fin k → R}
    (hw : w ∈ digitSpace S n q k ρ) : color σ n q k w ∈ colorBox n q k := by
  rw [colorBox, Fintype.mem_piFinset]
  exact fun i ↦ color_mem_Icc S hq hρ hρ2 hw i

/-- Blueprint C02: `0 ∈ colorBox`. -/
theorem zero_mem_colorBox : (0 : Fin k → ℤ) ∈ colorBox n q k := by
  rw [colorBox, Fintype.mem_piFinset]
  intro i
  simp only [Pi.zero_apply, Finset.mem_Icc, le_refl, true_and]
  positivity

/-- Blueprint C02: `|colorBox| = ∏ i, (D_{i+2} ^ 2 + 1)`. -/
theorem card_colorBox :
    (colorBox n q k).card = ∏ i : Fin k, (Params.D n q (i.val + 2) ^ 2 + 1) := by
  rw [colorBox, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Int.card_Icc, sub_zero]
  have := Int.toNat_natCast (Params.D n q (i.val + 2) ^ 2 + 1)
  push_cast at this
  exact this

/-- Blueprint C02: `|colorBox| ≤ 2 ^ k * ∏ i, D_{i+2} ^ 2` (as `D ≥ 1`). -/
theorem card_colorBox_le (hq : 1 ≤ q) :
    (colorBox n q k).card ≤ 2 ^ k * ∏ i : Fin k, Params.D n q (i.val + 2) ^ 2 := by
  rw [card_colorBox]
  calc ∏ i : Fin k, (Params.D n q (i.val + 2) ^ 2 + 1)
      ≤ ∏ i : Fin k, 2 * Params.D n q (i.val + 2) ^ 2 := by
        refine Finset.prod_le_prod fun i _ ↦ ?_
        have h1 : 1 ≤ Params.D n q (i.val + 2) ^ 2 := Nat.one_le_pow _ _ (Params.D_pos hq _)
        omega
    _ = 2 ^ k * ∏ i : Fin k, Params.D n q (i.val + 2) ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Blueprint C02 (main statement): the energy fiber. Under `Scaffold`, `q ≥ 1`, `ρ ≥ 0` and
`n ρ² (k+1)² ≤ 1` (with `n = Fintype.card ι` the number of embeddings and `k = h - 1`), there is a
color class `B ⊆ digitSpace` on which `color` is constant, with
`#digitSpace / (2 ^ k * ∏ i, D_{i+2} ^ 2) ≤ #B`. -/
theorem exists_energy_fiber (S : Scaffold b σ φ K₀ K₁) (hq : 1 ≤ q) (hρ : 0 ≤ ρ)
    (hρ2 : Fintype.card ι * ρ ^ 2 * (k + 1) ^ 2 ≤ 1) :
    ∃ B : Finset (Fin k → R), B ⊆ digitSpace S n q k ρ ∧
      (∀ w ∈ B, ∀ w' ∈ B, color σ n q k w = color σ n q k w') ∧
      ((digitSpace S n q k ρ).card : ℝ) /
        (2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2) ≤ B.card := by
  classical
  set W := digitSpace S n q k ρ with hW
  set t := colorBox n q k with ht
  have ht_ne : t.Nonempty := ⟨0, zero_mem_colorBox⟩
  have ht_pos : (0 : ℝ) < t.card := by exact_mod_cast Finset.card_pos.mpr ht_ne
  have hmaps : ∀ w ∈ W, color σ n q k w ∈ t := fun w hw ↦
    color_mem_colorBox S hq hρ hρ2 hw
  obtain ⟨c, -, hc⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (b := (W.card : ℝ) / t.card) hmaps ht_ne
    (by rw [nsmul_eq_mul, mul_div_cancel₀ _ ht_pos.ne'])
  refine ⟨W.filter (fun w ↦ color σ n q k w = c), Finset.filter_subset _ _, ?_, ?_⟩
  · intro w hw w' hw'
    rw [Finset.mem_filter] at hw hw'
    rw [hw.2, hw'.2]
  · refine le_trans ?_ hc
    have hcard : (t.card : ℝ) ≤ 2 ^ k * ∏ i : Fin k, (Params.D n q (i.val + 2) : ℝ) ^ 2 := by
      have := card_colorBox_le (n := n) (k := k) hq
      rw [← ht] at this
      exact_mod_cast this
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) ht_pos hcard

/-- Blueprint C02: the base map `b(w) = ∑ j, Dⱼ wⱼ` is injective on the digit space whenever
`2 ρ √n < 1` (D01 with `θ = 2ρ`). -/
theorem base_injOn (S : Scaffold b σ φ K₀ K₁) (hρ' : 2 * ρ * Real.sqrt (Fintype.card ι) < 1)
    (hq : 1 ≤ q) : Set.InjOn (base n q k) (digitSpace S n q k ρ : Set (Fin k → R)) :=
  S.digitMap_injOn_piFinset hρ' (radix n q k) (radix_pos hq)

/-- Blueprint C02: `|b(B)| = |B|` for every `B ⊆ digitSpace` when `2 ρ √n < 1`. -/
theorem card_image_base_of_subset [DecidableEq R] (S : Scaffold b σ φ K₀ K₁)
    (hρ' : 2 * ρ * Real.sqrt (Fintype.card ι) < 1) (hq : 1 ≤ q) {B : Finset (Fin k → R)}
    (hB : B ⊆ digitSpace S n q k ρ) : (B.image (base n q k)).card = B.card :=
  Finset.card_image_of_injOn ((base_injOn S hρ' hq).mono (Finset.coe_subset.mpr hB))

/-- Blueprint C02: `|b(W)| = |W|` when `2 ρ √n < 1`. -/
theorem card_image_base [DecidableEq R] (S : Scaffold b σ φ K₀ K₁)
    (hρ' : 2 * ρ * Real.sqrt (Fintype.card ι) < 1) (hq : 1 ≤ q) :
    ((digitSpace S n q k ρ).image (base n q k)).card = (digitSpace S n q k ρ).card :=
  card_image_base_of_subset S hρ' hq Finset.Subset.rfl

end DigitSpace

end Scaffold

end Nikodym

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
