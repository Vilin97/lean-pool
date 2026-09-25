/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module
public import Mathlib.Tactic
public import LeanPool.SalemTheorem.PdtSalemCircle
public import LeanPool.SalemTheorem.PdtSalemArith

/-!
# PdtSalemMinus — the minus family

The minus family of Salem's construction, `X^m·P − Q` —
anti-self-inversive pairing, the sine-anchored circle count (`z = 1` is
always a root, so the phase starts on the grid: `m+p−3` interior circle
roots plus `z = 1`), the trichotomy, and the ported arithmetic
certificate.  The assembly (both ladders, the two-sided statement) is
`PdtSalemEndgame`.

The fixed objects (`P`, `Q`, `E`, `V`, `N`, `A`, `psi`) are reused from
`PdtSalemCircle`; the arithmetic helpers from `PdtSalemArith`.  With
`p := roots.card + 1` and `Rm m = X^m·P − Q`, the three sign-flips
against the plus family are:

* the functional equation gains a minus (`Rm_eval_inv`):
  `z^(m+p)·Rm(1/z) = −Rm(z)` — anti-self-inversive, but a zero of a
  negation is a zero, so the pairing survives (`salem_root_inv_minus`);
* the key identity produces SINE instead of cosine (`Rm_eval_E`):
  `Rm(E t) = 2·N t·sin(ψ t)·(i·E((m+p)·t/2))`;
* `z = 1` is ALWAYS a root (`Rm_one_root`: `P(1) = Q(1)` exactly), so
  the phase starts ON the sine grid and the interior count is anchored
  at `m+p−3` (`salem_circle_count_minus`) — no floor function; the
  point `z = 1` is the `(m+p−2)`nd circle root and is inserted
  explicitly in the trichotomy (`salem_root_trichotomy_minus`).

The arithmetic certificate `salem_certificate_minus` is the verbatim
port of `PdtSalemArith.salem_certificate` with the family
`Rz = X^m·Pz − Qz`.
-/

public section

namespace PDT
namespace SalemMinus

noncomputable section
open Polynomial Complex Set
open SalemCircle SalemArith

/-! ### The minus family -/

/-- The minus Salem family `Rm_m = X^m·P − Q`. -/
def Rm (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) : Polynomial ℂ :=
  X ^ m * SalemCircle.P alpha roots - SalemCircle.Q alpha roots

lemma eval_Rm (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (z : ℂ) :
    (Rm alpha roots m).eval z
      = z ^ m * (P alpha roots).eval z - (Q alpha roots).eval z := by
  simp only [Rm, eval_sub, eval_mul, eval_pow, eval_X]

/-! ### The anti-self-inversive pairing and the anchor root -/

/-- **The anti-self-inversive functional equation**:
`z^(m+p)·Rm(1/z) = −Rm(z)` for `z ≠ 0` — the sign flip against the
plus family. -/
lemma Rm_eval_inv (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    z ^ (m + (roots.card + 1)) * (Rm alpha roots m).eval z⁻¹
      = -((Rm alpha roots m).eval z) := by
  have hzm : z ^ m * (z⁻¹) ^ m = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hz, one_pow]
  rw [eval_Rm, eval_Rm, pow_add]
  calc z ^ m * z ^ (roots.card + 1)
        * ((z⁻¹) ^ m * (P alpha roots).eval z⁻¹ - (Q alpha roots).eval z⁻¹)
      = (z ^ m * (z⁻¹) ^ m) * (z ^ (roots.card + 1) * (P alpha roots).eval z⁻¹)
        - z ^ m * (z ^ (roots.card + 1) * (Q alpha roots).eval z⁻¹) := by ring
    _ = -(z ^ m * (P alpha roots).eval z - (Q alpha roots).eval z) := by
        rw [hzm, mirror_P alpha roots hz, mirror_Q alpha roots hz]; ring

/-- **The pairing**: a nonzero root of `Rm_m` pairs with its
inverse — a zero of a negation is a zero. -/
theorem salem_root_inv_minus (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hroot : (Rm alpha roots m).eval z = 0) :
    (Rm alpha roots m).eval z⁻¹ = 0 := by
  have key := Rm_eval_inv alpha roots m hz
  rw [hroot, neg_zero] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero _ hz)
  · exact h

/-- **The anchor**: `z = 1` is ALWAYS a root of the minus family —
`P(1)` and `Q(1)` are literally the same product. -/
theorem Rm_one_root (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) :
    (Rm alpha roots m).eval 1 = 0 := by
  rw [eval_Rm, eval_P, eval_Q]
  simp only [one_pow, one_mul, mul_one]
  ring

/-! ### The sine key identity on the circle -/

/-- `exp(iψ) − exp(−iψ) = 2i·sin ψ`, over the reals — the sine mirror
of `SalemCircle.E_add_E_neg`. -/
lemma E_sub_E_neg (x : ℝ) :
    E x - E (-x) = 2 * Complex.I * ((Real.sin x : ℝ) : ℂ) := by
  simp only [E, Complex.exp_mul_I]
  push_cast
  simp only [Complex.cos_neg, Complex.sin_neg]
  ring

/-- **The key identity**: on the circle,
`Rm_m(E t) = 2·N t·sin(ψ t)·(i·E((m+p)·t/2))` — the sine phase that
replaces the plus family's cosine. -/
lemma Rm_eval_E (alpha : ℝ) (roots : Multiset ℂ)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (t : ℝ) :
    (Rm alpha roots m).eval (E t)
      = ((2 * N alpha roots t * Real.sin (psi alpha roots m t) : ℝ) : ℂ)
        * (Complex.I * E (((m + roots.card + 1 : ℕ) : ℝ) * t / 2)) := by
  have hV := V_polar alpha roots t
  have hQE := eval_Q_E alpha roots hconj t
  have hPE := eval_P_E alpha roots t
  have hpsi : psi alpha roots m t
      = ((m + roots.card + 1 : ℕ) : ℝ) * t / 2 + A alpha roots t := rfl
  set c2 : ℝ := ((m + roots.card + 1 : ℕ) : ℝ) * t / 2 with hc2
  set a : ℝ := A alpha roots t with ha
  set n : ℝ := N alpha roots t with hn
  set ψ : ℝ := psi alpha roots m t with hψ
  have e1 : E ((m : ℝ) * t) * E (((roots.card + 1 : ℕ) : ℝ) * t) * E a
      = E c2 * E ψ := by
    rw [← E_add, ← E_add, ← E_add]
    apply E_congr
    rw [hpsi, hc2]
    push_cast
    ring
  have e2 : E (-a) = E c2 * E (-ψ) := by
    rw [← E_add]
    apply E_congr
    rw [hpsi]
    ring
  have e3 : E ψ - E (-ψ) = 2 * Complex.I * ((Real.sin ψ : ℝ) : ℂ) := E_sub_E_neg ψ
  calc (Rm alpha roots m).eval (E t)
      = E t ^ m * (P alpha roots).eval (E t) - (Q alpha roots).eval (E t) :=
        eval_Rm alpha roots m (E t)
    _ = E ((m : ℝ) * t) * (E (((roots.card + 1 : ℕ) : ℝ) * t) * V alpha roots t)
        - (starRingEnd ℂ) (V alpha roots t) := by rw [E_pow, hPE, hQE]
    _ = (n : ℂ) * (E ((m : ℝ) * t) * E (((roots.card + 1 : ℕ) : ℝ) * t) * E a)
        - (n : ℂ) * E (-a) := by
        rw [hV, map_mul, Complex.conj_ofReal, conj_E]; ring
    _ = (n : ℂ) * (E c2 * E ψ) - (n : ℂ) * (E c2 * E (-ψ)) := by rw [e1, e2]
    _ = (n : ℂ) * E c2 * (E ψ - E (-ψ)) := by ring
    _ = (n : ℂ) * E c2 * (2 * Complex.I * ((Real.sin ψ : ℝ) : ℂ)) := by rw [e3]
    _ = ((2 * n * Real.sin ψ : ℝ) : ℂ) * (Complex.I * E c2) := by push_cast; ring

/-- The zero test on the circle: `Rm_m(E t) = 0 ↔ sin(ψ t) = 0`. -/
lemma Rm_eval_E_eq_zero_iff (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (t : ℝ) :
    (Rm alpha roots m).eval (E t) = 0 ↔ Real.sin (psi alpha roots m t) = 0 := by
  rw [Rm_eval_E alpha roots hconj m t]
  have hN := N_pos alpha roots halpha hroots t
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · have h2 : (2 * N alpha roots t * Real.sin (psi alpha roots m t) : ℝ) = 0 :=
        Complex.ofReal_eq_zero.mp h
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exfalso; linarith
      · exact h3
    · rcases mul_eq_zero.mp h with h4 | h4
      · exact absurd h4 Complex.I_ne_zero
      · exact absurd h4 (E_ne_zero _)
  · intro h
    rw [h]
    simp

/-- **The anchor on the grid**: `Rm(1) = 0` at `t = 0` puts the phase
ON the sine grid — `sin(ψ 0) = 0`. -/
lemma sin_psi_zero_eq_zero (alpha : ℝ) (roots : Multiset ℂ) (halpha : 1 < alpha)
    (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) :
    Real.sin (psi alpha roots m 0) = 0 := by
  have h0 : (Rm alpha roots m).eval (E 0) = 0 := by
    rw [E_zero]; exact Rm_one_root alpha roots m
  exact (Rm_eval_E_eq_zero_iff alpha roots halpha hroots hconj m 0).mp h0

/-! ### The anchored grid count -/

/-- **The anchored grid-count workhorse.**  A continuous phase `f` on
`[0, 2π]` that climbs by exactly `L·π` and starts ON the sine grid
(`sin (f 0) = 0`) attains `L − 1` distinct interior grid values,
planting `L − 1` distinct zeros of `sin ∘ f` in `(0, 2π)` — simpler
than the plus workhorse: the anchor kills the floor function. -/
lemma exists_interior_grid_anchored (f : ℝ → ℝ) (hf : Continuous f) (L : ℕ)
    (hclimb : f (2 * Real.pi) = f 0 + (L : ℝ) * Real.pi)
    (hsin0 : Real.sin (f 0) = 0) :
    ∃ T : Finset ℝ, T.card = L - 1 ∧ ∀ t ∈ T,
      (0 < t ∧ t < 2 * Real.pi) ∧ Real.sin (f t) = 0 := by
  classical
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k0, hk0⟩ := Real.sin_eq_zero_iff.mp hsin0
  have hsing : ∀ j : ℕ, Real.sin (((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi) = 0 := by
    intro j
    rw [Real.sin_eq_zero_iff]
    exact ⟨k0 + 1 + (j : ℤ), by push_cast; ring⟩
  have hlow : ∀ j : ℕ, f 0 < ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j
    have h1 : (0 : ℝ) ≤ (j : ℝ) * Real.pi := mul_nonneg (Nat.cast_nonneg j) hπ.le
    nlinarith [hk0]
  have hhigh : ∀ j : ℕ, j < L - 1 →
      ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi < f (2 * Real.pi) := by
    intro j hj
    rw [hclimb]
    have hjL : (j : ℝ) + 2 ≤ (L : ℝ) := by exact_mod_cast (by omega : j + 2 ≤ L)
    have h2 : ((j : ℝ) + 2) * Real.pi ≤ (L : ℝ) * Real.pi :=
      mul_le_mul_of_nonneg_right hjL hπ.le
    nlinarith [hk0]
  have hIVT := intermediate_value_Icc
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi) hf.continuousOn
  have hex : ∀ j : ℕ, j < L - 1 → ∃ t : ℝ, (0 < t ∧ t < 2 * Real.pi) ∧
      f t = ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j hj
    have hmem : ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi
        ∈ Icc (f 0) (f (2 * Real.pi)) :=
      ⟨le_of_lt (hlow j), le_of_lt (hhigh j hj)⟩
    obtain ⟨t, htmem, hteq⟩ := hIVT hmem
    refine ⟨t, ⟨?_, ?_⟩, hteq⟩
    · rcases eq_or_lt_of_le htmem.1 with h | h
      · exfalso
        rw [← h] at hteq
        exact absurd hteq (ne_of_lt (hlow j))
      · exact h
    · rcases eq_or_lt_of_le htmem.2 with h | h
      · exfalso
        rw [h] at hteq
        exact absurd hteq (ne_of_gt (hhigh j hj))
      · exact h
  set tf : ℕ → ℝ := fun j => if h : j < L - 1 then (hex j h).choose else 0 with htf
  have htf_spec : ∀ j : ℕ, j < L - 1 → (0 < tf j ∧ tf j < 2 * Real.pi) ∧
      f (tf j) = ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi := by
    intro j hj
    simp only [htf, dite_eq_left hj]
    exact (hex j hj).choose_spec
  refine ⟨(Finset.range (L - 1)).image tf, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn, Finset.card_range]
    intro j hj j' hj' heq
    have hj1 := (htf_spec j (Finset.mem_range.mp hj)).2
    have hj2 := (htf_spec j' (Finset.mem_range.mp hj')).2
    rw [heq] at hj1
    have h12 : ((k0 : ℝ) + 1 + (j : ℝ)) * Real.pi
        = ((k0 : ℝ) + 1 + (j' : ℝ)) * Real.pi := hj1.symm.trans hj2
    have h13 := mul_right_cancel₀ (ne_of_gt hπ) h12
    have h14 : (j : ℝ) = (j' : ℝ) := by linarith
    exact_mod_cast h14
  · intro t ht
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    have hspec := htf_spec j (Finset.mem_range.mp hj)
    exact ⟨hspec.1, by rw [hspec.2]; exact hsing j⟩

/-- **The anchored circle count**: with `p = roots.card + 1` and
`3 ≤ m + p`, the minus family `Rm_m` has `m + p − 3` distinct INTERIOR
roots `exp(t·I)`, `t ∈ (0, 2π)`, on the unit circle — `z = 1` (i.e.
`t = 0`) is the `(m+p−2)`nd circle root, always present
(`Rm_one_root`), and it anchors the phase on the grid.
(Stated without the redundant `1 ≤ m`, as in the plus count.) -/
theorem salem_circle_count_minus (alpha : ℝ) (roots : Multiset ℂ)
    (halpha : 1 < alpha) (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ)
    (hmp : 3 ≤ m + (roots.card + 1)) :
    ∃ T : Finset ℝ, T.card = m + (roots.card + 1) - 3 ∧
      ∀ t ∈ T, (0 < t ∧ t < 2 * Real.pi) ∧
        (Rm alpha roots m).eval (Complex.exp (t * Complex.I)) = 0 := by
  have hclimb : psi alpha roots m (2 * Real.pi)
      = psi alpha roots m 0 + ((m + (roots.card + 1) - 2 : ℕ) : ℝ) * Real.pi := by
    rw [psi_two_pi]
    have h2 : 2 ≤ m + roots.card + 1 := by omega
    have heq : m + (roots.card + 1) - 2 = m + roots.card + 1 - 2 := by omega
    rw [heq, Nat.cast_sub h2]
    push_cast
    ring
  obtain ⟨T, hcard, hT⟩ := exists_interior_grid_anchored (psi alpha roots m)
    (continuous_psi alpha roots halpha hroots m) (m + (roots.card + 1) - 2) hclimb
    (sin_psi_zero_eq_zero alpha roots halpha hroots hconj m)
  have hcard3 : T.card = m + (roots.card + 1) - 3 := by
    rw [hcard]
    omega
  refine ⟨T, hcard3, fun t ht => ⟨(hT t ht).1, ?_⟩⟩
  exact (Rm_eval_E_eq_zero_iff alpha roots halpha hroots hconj m t).mpr (hT t ht).2

/-! ### Degree bookkeeping — `Rm_m` is monic of degree `m + p` -/

lemma Rm_eq_add_neg (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) :
    Rm alpha roots m = X ^ m * P alpha roots + -(Q alpha roots) := by
  unfold Rm
  rw [sub_eq_add_neg]

lemma degree_neg_Q_lt (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (-(Q alpha roots)).degree < (X ^ m * P alpha roots).degree := by
  rw [Polynomial.degree_neg]
  exact degree_Q_lt alpha roots m hm

lemma Rm_monic (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (Rm alpha roots m).Monic := by
  rw [Rm_eq_add_neg]
  exact (XmP_monic alpha roots m).add_of_left (degree_neg_Q_lt alpha roots m hm)

lemma Rm_natDegree (alpha : ℝ) (roots : Multiset ℂ) (m : ℕ) (hm : 1 ≤ m) :
    (Rm alpha roots m).natDegree = m + (roots.card + 1) := by
  rw [Rm_eq_add_neg, natDegree_eq_of_degree_eq
    (degree_add_eq_left_of_degree_lt (degree_neg_Q_lt alpha roots m hm))]
  exact XmP_natDegree alpha roots m

/-! ### The circle parametrization avoids `1` on the interior -/

/-- On the open interval `(0, 2π)` the circle parametrization avoids
`1` — so inserting the anchor root `z = 1` genuinely grows the root
set. -/
lemma E_ne_one {t : ℝ} (ht : 0 < t) (ht2 : t < 2 * Real.pi) : E t ≠ 1 := by
  intro heq
  have heq' : E t = E 0 := by rw [E_zero]; exact heq
  simp only [E] at heq'
  rw [Complex.exp_eq_exp_iff_exists_int] at heq'
  obtain ⟨n, hn⟩ := heq'
  have hI : ((t : ℝ) : ℂ) * Complex.I
      = ((0 + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  have hreal : t = 0 + n * (2 * Real.pi) := by
    have h2 := mul_right_cancel₀ Complex.I_ne_zero hI
    exact_mod_cast h2
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases lt_trichotomy n 0 with h | h | h
  · have hn1 : (n : ℝ) ≤ -1 := by exact_mod_cast (by omega : n ≤ -1)
    nlinarith [mul_le_mul_of_nonneg_right hn1
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  · rw [h] at hreal
    norm_num at hreal
    linarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
    nlinarith [mul_le_mul_of_nonneg_right hn1
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

/-! ### The trichotomy -/

/-- **The trichotomy**: if `τ > 1` is a root of `Rm_m` (with
`1 ≤ m` and `3 ≤ m + p`), then EVERY root of `Rm_m` is unimodular or
lies in `{τ, 1/τ}` — the `m + p − 3` interior circle points of the anchored count, the
anchor root `1`, and `τ`, `1/τ` already exhaust the degree `m + p` of
the monic `Rm_m`, by the multiset squeeze `S.val ≤ (Rm_m).roots`. -/
theorem salem_root_trichotomy_minus (alpha : ℝ) (roots : Multiset ℂ)
    (halpha : 1 < alpha) (hroots : ∀ r ∈ roots, ‖r‖ < 1)
    (hconj : roots.map (starRingEnd ℂ) = roots) (m : ℕ) (hm : 1 ≤ m)
    (hmp : 3 ≤ m + (roots.card + 1))
    (tau : ℝ) (htau : 1 < tau) (hroot : (Rm alpha roots m).eval ((tau : ℂ)) = 0) :
    ∀ z : ℂ, (Rm alpha roots m).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
  classical
  obtain ⟨T, hcard, hT⟩ :=
    salem_circle_count_minus alpha roots halpha hroots hconj m hmp
  have hUcard0 : (T.image fun t => E t).card = m + (roots.card + 1) - 3 := by
    rw [← hcard]
    apply Finset.card_image_of_injOn
    intro t ht s hs heq
    exact E_inj (hT t (Finset.mem_coe.mp ht)).1.1 (hT t (Finset.mem_coe.mp ht)).1.2
      (hT s (Finset.mem_coe.mp hs)).1.1 (hT s (Finset.mem_coe.mp hs)).1.2 heq
  have h1notin : (1 : ℂ) ∉ T.image fun t => E t := by
    intro h1
    obtain ⟨t, ht, hEt⟩ := Finset.mem_image.mp h1
    exact E_ne_one (hT t ht).1.1 (hT t ht).1.2 hEt
  have hUcard : (insert (1 : ℂ) (T.image fun t => E t)).card
      = m + (roots.card + 1) - 2 := by
    rw [Finset.card_insert_of_notMem h1notin, hUcard0]
    omega
  have hUnorm : ∀ z ∈ insert (1 : ℂ) (T.image fun t => E t), ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h, norm_one]
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h
      exact norm_E t
  have htaupos : (0 : ℝ) < tau := by linarith
  have htau0 : ((tau : ℂ)) ≠ 0 := by
    intro h
    rw [Complex.ofReal_eq_zero] at h
    linarith
  have htau_norm : ‖((tau : ℂ))‖ = tau := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaupos]
  have htauinv_norm : ‖((tau : ℂ))⁻¹‖ = tau⁻¹ := by
    rw [norm_inv, htau_norm]
  have htinv1 : tau⁻¹ < 1 := inv_lt_one_of_one_lt₀ htau
  have htau_ne : ((tau : ℂ)) ≠ ((tau : ℂ))⁻¹ := by
    intro h
    have h1 : ‖((tau : ℂ))‖ = ‖((tau : ℂ))⁻¹‖ := by rw [← h]
    rw [htau_norm, htauinv_norm] at h1
    linarith
  have hdisj : Disjoint (insert (1 : ℂ) (T.image fun t => E t))
      ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ) := by
    rw [Finset.disjoint_left]
    intro z hzU hzV
    have h1 := hUnorm z hzU
    rcases Finset.mem_insert.mp hzV with h | h
    · rw [h, htau_norm] at h1; linarith
    · rw [Finset.mem_singleton.mp h, htauinv_norm] at h1; linarith
  have hpair : ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr htau_ne
  set S : Finset ℂ :=
    insert (1 : ℂ) (T.image fun t => E t) ∪ {((tau : ℂ)), ((tau : ℂ))⁻¹} with hS
  have hScard : S.card = m + (roots.card + 1) := by
    rw [hS, Finset.card_union_of_disjoint hdisj, hUcard, hpair]
    omega
  have hSroot : ∀ z ∈ S, (Rm alpha roots m).eval z = 0 := by
    intro z hz
    rw [hS, Finset.mem_union] at hz
    rcases hz with h | h
    · rcases Finset.mem_insert.mp h with h1 | h1
      · rw [h1]; exact Rm_one_root alpha roots m
      · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp h1
        exact (hT t ht).2
    · rcases Finset.mem_insert.mp h with h1 | h1
      · rw [h1]; exact hroot
      · rw [Finset.mem_singleton.mp h1]
        exact salem_root_inv_minus alpha roots m htau0 hroot
  have hRne : Rm alpha roots m ≠ 0 := (Rm_monic alpha roots m hm).ne_zero
  have hle : S.val ≤ (Rm alpha roots m).roots := by
    rw [Multiset.le_iff_count]
    intro z
    by_cases hz : z ∈ S
    · rw [Multiset.count_eq_one_of_mem S.nodup (Finset.mem_def.mp hz),
        Polynomial.count_roots]
      have hpos := (Polynomial.rootMultiplicity_pos hRne).mpr (hSroot z hz)
      omega
    · rw [Multiset.count_eq_zero.mpr (fun hv => hz (Finset.mem_def.mpr hv))]
      exact Nat.zero_le _
  have hcards : Multiset.card ((Rm alpha roots m).roots) ≤ Multiset.card S.val := by
    have h1 := Polynomial.card_roots' (Rm alpha roots m)
    rw [Rm_natDegree alpha roots m hm] at h1
    have h2 : Multiset.card S.val = S.card := rfl
    omega
  have heq : S.val = (Rm alpha roots m).roots :=
    Multiset.eq_of_le_of_card_le hle hcards
  intro z hz
  have hzmem : z ∈ (Rm alpha roots m).roots := Polynomial.mem_roots'.mpr ⟨hRne, hz⟩
  rw [← heq] at hzmem
  have hzS : z ∈ S := Finset.mem_def.mpr hzmem
  rw [hS, Finset.mem_union] at hzS
  rcases hzS with h | h
  · exact Or.inl (hUnorm z h)
  · rcases Finset.mem_insert.mp h with h1 | h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Finset.mem_singleton.mp h1))

/-! ### The arithmetic certificate for the minus family -/

/-- The integer minus family `X^m·Pz − Qz` is monic (for `m ≥ 1`). -/
lemma family_monic_minus (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) (hm : 1 ≤ m) : (X ^ m * Pz - Qz).Monic := by
  have hPdeg := Pz_natDegree Pz hmonic alpha inside hfacC
  have hQdeg := Qz_natDegree_le alpha inside Qz hQmap
  have hXm : (X ^ m * Pz).Monic := (monic_X_pow m).mul hmonic
  rw [sub_eq_add_neg]
  refine hXm.add_of_left ?_
  rw [Polynomial.degree_neg]
  apply degree_lt_degree
  rw [(monic_X_pow m).natDegree_mul hmonic, natDegree_X_pow, hPdeg]
  omega

/-- The complex image of the integer minus family is `Rm`. -/
lemma family_map_C_minus (Pz : Polynomial ℤ) (alpha : ℝ) (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) :
    (X ^ m * Pz - Qz).map (Int.castRingHom ℂ) = Rm alpha inside m := by
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, hfacC, hQmap]
  rfl

/-- **The arithmetic Salem-ness certificate for the minus family.**
A real root `tau > 1` of the integer family `X^m·Pz − Qz` — whose
complex image is the minus family `Rm` — is a Salem number, provided
`tau` avoids the two integer degeneracies `tau ∈ ℤ` and
`tau + 1/tau ∈ ℤ`: it is an algebraic integer, its conjugates lie in
the closed unit disk, at least one lies ON the circle, and `1/tau` is
among them.  Verbatim port of `PdtSalemArith.salem_certificate`; all
degenerate exclusions run through the same Gauss step. -/
theorem salem_certificate_minus
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) (hm : 1 ≤ m) (hmp : 3 ≤ m + (inside.card + 1))
    (tau : ℝ) (htau : 1 < tau)
    (hroot : ((X ^ m * Pz - Qz).map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    IsIntegral ℤ tau ∧
    (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 → z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
    (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
    (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
  classical
  set Rz : Polynomial ℤ := X ^ m * Pz - Qz with hRzdef
  -- bridge plumbing
  have hRzMonic : Rz.Monic :=
    family_monic_minus Pz hmonic alpha inside hfacC Qz hQmap m hm
  have hRmap : Rz.map (Int.castRingHom ℂ) = Rm alpha inside m :=
    family_map_C_minus Pz alpha inside hfacC Qz hQmap m
  have haevalR : Polynomial.aeval tau Rz = 0 := by
    rw [aeval_eq_eval_map, algebraMap_int_eq]
    exact hroot
  -- integrality
  have hint : IsIntegral ℤ tau := by
    refine ⟨Rz, hRzMonic, ?_⟩
    rw [← Polynomial.aeval_def]
    exact haevalR
  have hQint : IsIntegral ℚ tau := hint.tower_top
  -- the family root over ℂ, and the trichotomy
  have hRC : (Rm alpha inside m).eval ((tau : ℂ)) = 0 := by
    have h1 : Polynomial.aeval ((tau : ℂ)) Rz = 0 := by
      rw [SalemArith.aeval_ofReal, haevalR, Complex.ofReal_zero]
    rwa [aeval_eq_eval_map, algebraMap_int_eq, hRmap] at h1
  have htri : ∀ z : ℂ, (Rm alpha inside m).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ :=
    salem_root_trichotomy_minus alpha inside halpha hin hconj m hm hmp
      tau htau hRC
  -- the minimal polynomial divides, so conjugates are roots of `Rm`
  have hmpdvd : minpoly ℚ tau ∣ Rz.map (Int.castRingHom ℚ) := by
    apply minpoly.dvd ℚ tau
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
    exact haevalR
  have hdvdC : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ∣ Rm alpha inside m := by
    have h1 : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ∣
        (Rz.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) :=
      Polynomial.map_dvd _ hmpdvd
    rwa [Polynomial.map_map, castQC_triangle, hRmap] at h1
  have hcontain : ∀ z : ℂ, ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 →
      (Rm alpha inside m).eval z = 0 := by
    intro z hz
    obtain ⟨c, hc⟩ := hdvdC
    rw [hc, Polynomial.eval_mul, hz, zero_mul]
  have haevalC : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau)
      = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z := fun z =>
    aeval_eq_eval_map _ z
  have htauCroot : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval ((tau : ℂ)) = 0 := by
    rw [← haevalC, SalemArith.aeval_ofReal, minpoly.aeval, Complex.ofReal_zero]
  -- scalar facts about `tau`
  have htaupos : (0 : ℝ) < tau := by linarith
  have htau_norm : ‖((tau : ℂ))‖ = tau := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaupos]
  have htauinv_norm : ‖((tau : ℂ))⁻¹‖ = tau⁻¹ := by rw [norm_inv, htau_norm]
  have htinv1 : tau⁻¹ < 1 := inv_lt_one_of_one_lt₀ htau
  -- the closed disk
  have hdisk : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 →
      z ≠ ((tau : ℂ)) → ‖z‖ ≤ 1 := by
    intro z hz hzne
    have hz0 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
      rw [← haevalC]; exact hz
    rcases htri z (hcontain z hz0) with h | h | h
    · exact le_of_eq h
    · exact absurd h hzne
    · rw [h, htauinv_norm]; linarith
  -- the Gauss step — every coefficient of the minimal polynomial
  -- over ℚ is the cast of an integer
  have hmz : minpoly ℚ tau = (minpoly ℤ tau).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hcoeff : ∀ i : ℕ,
      (minpoly ℚ tau).coeff i = (((minpoly ℤ tau).coeff i : ℤ) : ℚ) := by
    intro i
    rw [hmz, Polynomial.coeff_map, eq_intCast]
  -- splitting data for the complex minimal polynomial
  have hmpmonic : (minpoly ℚ tau).Monic := minpoly.monic hQint
  have hmpirr : Irreducible (minpoly ℚ tau) := minpoly.irreducible hQint
  have hmpsep : (minpoly ℚ tau).Separable := hmpirr.separable
  have hsepC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Separable := hmpsep.map
  have hnodup : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  have hmonicC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Monic := hmpmonic.map _
  have hCne : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  have hsplits : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hdegC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).natDegree
      = (minpoly ℚ tau).natDegree := hmpmonic.natDegree_map _
  have hcard : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card
      = (minpoly ℚ tau).natDegree := by
    rw [← hdegC]
    exact hsplits.natDegree_eq_card_roots.symm
  have hdegpos : 0 < (minpoly ℚ tau).natDegree := minpoly.natDegree_pos hQint
  have hmem : ∀ z : ℂ, z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots ↔
      ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
    intro z
    rw [Polynomial.mem_roots']
    exact ⟨fun h => h.2, fun h => ⟨hCne, h⟩⟩
  have htauC_mem : ((tau : ℂ)) ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots :=
    (hmem _).mpr htauCroot
  -- a conjugate ON the circle
  have hcircle : ∃ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1 := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    -- containment of all roots in the pair {tau, 1/tau}
    have hpair : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
      intro z hz
      have hz0 := (hmem z).mp hz
      have hz1 : Polynomial.aeval z (minpoly ℚ tau) = 0 := by
        rw [haevalC]; exact hz0
      rcases htri z (hcontain z hz0) with h | h | h
      · exact absurd h (hno z hz1)
      · exact Or.inl h
      · exact Or.inr h
    -- hence the degree is at most 2
    have hsub : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset ⊆
        ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ) := by
      intro z hz
      rcases hpair z (Multiset.mem_toFinset.mp hz) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    have hdeg2 : (minpoly ℚ tau).natDegree ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      have h2 : ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      have h3 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset.card
          = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card :=
        Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
      omega
    rcases (by omega :
        (minpoly ℚ tau).natDegree = 1 ∨ (minpoly ℚ tau).natDegree = 2) with h1 | h2
    · -- degree 1: `tau` would be a rational integer
      have heq : minpoly ℚ tau = X + Polynomial.C ((minpoly ℚ tau).coeff 0) :=
        hmpmonic.eq_X_add_C h1
      have haev := minpoly.aeval ℚ tau
      rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C, hcoeff 0,
        map_intCast] at haev
      exact hτZ (-(minpoly ℤ tau).coeff 0) (by push_cast; linarith)
    · -- degree 2: the root multiset is exactly {tau, 1/tau}, and Vieta on
      -- the X-coefficient makes `tau + 1/tau` a rational integer
      obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
      have hcards := hcard
      rw [hrest, Multiset.card_cons] at hcards
      have hcard_rest : rest.card = 1 := by omega
      obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard_rest
      have hnodup' := hnodup
      rw [hrest, Multiset.nodup_cons] at hnodup'
      have hbmem : b ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots := by
        rw [hrest, hb]
        exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self b)
      have hbval : b = ((tau : ℂ))⁻¹ := by
        rcases hpair b hbmem with h | h
        · exfalso
          apply hnodup'.1
          rw [hb, h]
          exact Multiset.mem_singleton_self _
        · exact h
      have hnext := hsplits.nextCoeff_eq_neg_sum_roots_of_monic hmonicC
      rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hdegC]; omega),
        hdegC, h2, hrest, hb, hbval, Multiset.sum_cons,
        Multiset.sum_singleton] at hnext
      rw [show (2 : ℕ) - 1 = 1 by norm_num] at hnext
      rw [Polynomial.coeff_map, hcoeff 1, map_intCast] at hnext
      have hreal : (((minpoly ℤ tau).coeff 1 : ℤ) : ℝ) = -(tau + tau⁻¹) := by
        exact_mod_cast hnext
      exact hτtr (-(minpoly ℤ tau).coeff 1) (by push_cast; linarith)
  -- `1/tau` is a conjugate
  have hinvroot : Polynomial.aeval (((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
    by_contra hne
    -- every root other than `tau` is unimodular
    have hroots1 : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z ≠ ((tau : ℂ)) → ‖z‖ = 1 := by
      intro z hz hzne
      have hz0 := (hmem z).mp hz
      rcases htri z (hcontain z hz0) with h | h | h
      · exact h
      · exact absurd h hzne
      · exfalso
        apply hne
        rw [← h, haevalC z]
        exact hz0
    obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
    have hnodup' := hnodup
    rw [hrest, Multiset.nodup_cons] at hnodup'
    have hrest1 : ∀ w ∈ rest, ‖w‖ = 1 := by
      intro w hw
      apply hroots1 w (by rw [hrest]; exact Multiset.mem_cons_of_mem hw)
      intro hwz
      exact hnodup'.1 (hwz ▸ hw)
    -- Vieta on the constant term, in absolute value
    have hc0 := hsplits.coeff_zero_eq_prod_roots_of_monic hmonicC
    rw [hrest, Multiset.prod_cons] at hc0
    have hnorm : ‖((minpoly ℚ tau).map (algebraMap ℚ ℂ)).coeff 0‖ = tau := by
      rw [hc0, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, htau_norm, norm_multiset_prod_eq_one rest hrest1, mul_one]
    rw [Polynomial.coeff_map, hcoeff 0, map_intCast,
      show ((((minpoly ℤ tau).coeff 0 : ℤ)) : ℂ)
        = (((((minpoly ℤ tau).coeff 0 : ℤ) : ℝ)) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hnorm
    exact hτZ |(minpoly ℤ tau).coeff 0| hnorm.symm
  exact ⟨hint, hdisk, hcircle, hinvroot⟩

end
end SalemMinus
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
