/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import LeanPool.InflationTermination.TriangleInflation.Graph.Cycles

/-!
# Linear-in-t witnesses (B2)

Statements split from the original `Statements.lean` skeleton (one file per proving task);
see AUDIT-NOTES B2 and the packet source `B6-square-linear-lower-bound.md` §1–2 for the
mathematics.

Proved here: Walsh orthogonality and the Fourier uniqueness of a law on `ι → Bool`
(`funext_of_walsh_moments`); the positivity `W ≥ 3/5` of the corrected `m = 3`, `c = 4`
density for `tq ≤ 1/16` (`triW_ge`), through the division-free form `triW_core` of the
packet's `1 − cos ∑θ_g ≤ 3 ∑ (1 − cos θ_g)`; the complete moment table `triW_moment`; the
normalization `triW_sum` and hence `triDensity_isLaw`; and `triParity_isLaw`.

Not proved here (moved to `InflationGraphOpen/Linear.lean`): `triangle_linear_witness` and `square_linear_witness`, which need the
pushforward of the density along the copied-observation map together with the symmetry, the
diagonal law and the injectable/ancestral prescriptions.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

variable {Γ : PairGraph} {t : ℕ}

/-! ## Walsh characters and Fourier uniqueness

A law on `ι → Bool` is determined by its sign moments. The inversion formula is the
orthogonality of the Walsh characters `χ_S(w) = ∏_{i ∈ S} sgn (w i)`. -/

section Walsh

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Walsh character of a set of coordinates, in the sign convention of `sgn`. -/
def walsh (S : Finset ι) (w : ι → Bool) : ℝ := ∏ i ∈ S, sgn (w i)

-- `sgn_mul_self` is provided by `Cycles.lean`.

theorem sgn_ne_zero (b : Bool) : sgn b ≠ 0 := by cases b <;> norm_num [sgn]

/-- Two bits have sign product `1` when equal and `-1` when different. -/
theorem sgn_mul_sgn (a b : Bool) : sgn a * sgn b = if a = b then 1 else -1 := by
  cases a <;> cases b <;> norm_num [sgn]

/-- The sum of a product over all subsets is the product of `1 + f i`. -/
theorem sum_prod_subsets (f : ι → ℝ) :
    ∑ S : Finset ι, ∏ i ∈ S, f i = ∏ i, (f i + 1) := by
  have h := Finset.prod_add (f := f) (g := fun _ : ι => (1 : ℝ)) (s := (univ : Finset ι))
  simpa [Finset.powerset_univ] using h.symm

/-- Orthogonality of the Walsh characters. -/
theorem walsh_orthogonality (w v : ι → Bool) :
    ∑ S : Finset ι, walsh S w * walsh S v =
      if w = v then (2 : ℝ) ^ (Fintype.card ι) else 0 := by
  have hrw : ∀ S : Finset ι, walsh S w * walsh S v = ∏ i ∈ S, (sgn (w i) * sgn (v i)) := by
    intro S; rw [walsh, walsh, ← Finset.prod_mul_distrib]
  simp only [hrw]
  rw [sum_prod_subsets]
  by_cases h : w = v
  · subst h
    rw [ite_eq_left rfl]
    simp only [sgn_mul_self]
    norm_num [Finset.prod_const, Finset.card_univ]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ v i := by
      by_contra hc
      exact h (funext (fun i => not_not.1 (fun hne => hc ⟨i, hne⟩)))
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [sgn_mul_sgn, ite_eq_right hi]; ring

/-- A weight function on `ι → Bool` is determined by its Walsh moments. -/
theorem funext_of_walsh_moments (P Q : (ι → Bool) → ℝ)
    (h : ∀ S : Finset ι, ∑ w, walsh S w * P w = ∑ w, walsh S w * Q w) : P = Q := by
  funext v
  have hzero : ∀ S : Finset ι, ∑ w, walsh S w * (P w - Q w) = 0 := by
    intro S
    have := h S
    simp only [mul_sub]
    rw [Finset.sum_sub_distrib, this, sub_self]
  have key : (2 : ℝ) ^ (Fintype.card ι) * (P v - Q v)
      = ∑ S : Finset ι, walsh S v * ∑ w, walsh S w * (P w - Q w) := by
    have : ∀ S : Finset ι, walsh S v * ∑ w, walsh S w * (P w - Q w)
        = ∑ w, (walsh S w * walsh S v) * (P w - Q w) := by
      intro S; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (by intros; ring)
    simp only [this]
    rw [Finset.sum_comm]
    have : ∀ w : ι → Bool, ∑ S : Finset ι, walsh S w * walsh S v * (P w - Q w)
        = (if w = v then (2 : ℝ) ^ (Fintype.card ι) else 0) * (P w - Q w) := by
      intro w; rw [← Finset.sum_mul, walsh_orthogonality]
    simp only [this]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [hzero, mul_zero, Finset.sum_const_zero] at key
  have h2 : (0:ℝ) < (2 : ℝ) ^ (Fintype.card ι) := by positivity
  have : P v - Q v = 0 := by
    rcases mul_eq_zero.1 key with h' | h'
    · exact absurd h' (ne_of_gt h2)
    · exact h'
  linarith

/-- The generating identity behind the moment table: pairing the Walsh character `χ_S`
against a product weight replaces the coordinate sum `k v true + k v false` by the
difference `-k v true + k v false` exactly at the coordinates of `S`. -/
theorem sum_walsh_mul_prod (S : Finset ι) (k : ι → Bool → ℂ) :
    ∑ s : ι → Bool, (walsh S s : ℂ) * ∏ v, k v (s v)
      = ∏ v, (if v ∈ S then -k v true + k v false else k v true + k v false) := by
  have hstep : ∀ s : ι → Bool, (walsh S s : ℂ) * ∏ v, k v (s v)
      = ∏ v, ((if v ∈ S then (sgn (s v) : ℂ) else 1) * k v (s v)) := by
    intro s
    rw [Finset.prod_mul_distrib]
    congr 1
    rw [walsh, Complex.ofReal_prod, Finset.prod_ite_mem]
    simp
  simp only [hstep]
  rw [← Fintype.prod_sum (fun (v : ι) (b : Bool) =>
    (if v ∈ S then (sgn b : ℂ) else 1) * k v b)]
  refine Finset.prod_congr rfl ?_
  intro v _
  rw [Fintype.sum_bool]
  by_cases hv : v ∈ S <;> simp [hv, sgn]

end Walsh

/-! ## Positivity of the corrected Fourier density (AUDIT-NOTES B2)

The density is `ρ(s) = 2^{-3t} W(s)` with `W = Re (f_x f_y f_z) + 4 ∑_g (1 − Re f_g)` and
`f_g = ∏_i (1 + i√q s_{g,i})`. Each `f_g` has modulus `R = (1+q)^{t/2}`, and the whole
positivity argument is the following inequality about three complex numbers of equal
modulus, which replaces the packet's argument through `arg` by a division-free telescoping
of `R³ − u₀u₁u₂`. -/

/-- `‖A − u‖² = 2A(A − Re u)` for a complex number of modulus `A`. -/
theorem norm_sub_sq_of_norm_eq (A : ℝ) (u : ℂ) (h : ‖u‖ = A) :
    ‖(A : ℂ) - u‖ ^ 2 = 2 * A * (A - u.re) := by
  have hu : u.re ^ 2 + u.im ^ 2 = A ^ 2 := by
    have h2 := Complex.sq_norm u
    rw [h, Complex.normSq_apply] at h2
    nlinarith [h2]
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im]
  linear_combination hu

/-- The telescoped triangle inequality plus Cauchy–Schwarz: for three complex numbers of
modulus `R`, `R³ − Re(u₀u₁u₂) ≤ 3R² ∑_g (R − Re u_g)`. This is the `m = 3` case of
`1 − cos(∑θ_g) ≤ m ∑_g (1 − cos θ_g)` in AUDIT-NOTES B2, stated without `arg`. -/
theorem re_prod_lower (R : ℝ) (hR0 : 0 < R) (u₀ u₁ u₂ : ℂ)
    (h₀ : ‖u₀‖ = R) (h₁ : ‖u₁‖ = R) (h₂ : ‖u₂‖ = R) :
    R ^ 3 - (u₀ * u₁ * u₂).re ≤
      3 * R ^ 2 * ((R - u₀.re) + (R - u₁.re) + (R - u₂.re)) := by
  set a₀ := ‖(R : ℂ) - u₀‖ with ha₀
  set a₁ := ‖(R : ℂ) - u₁‖ with ha₁
  set a₂ := ‖(R : ℂ) - u₂‖ with ha₂
  have hRC : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  have hprod : ‖u₀ * u₁ * u₂‖ = R ^ 3 := by
    rw [Complex.norm_mul, Complex.norm_mul, h₀, h₁, h₂]; ring
  -- the telescoping identity
  have htel : ((R : ℂ)) ^ 3 - u₀ * u₁ * u₂ =
      ((R : ℂ)) ^ 2 * ((R : ℂ) - u₀) + (R : ℂ) * u₀ * ((R : ℂ) - u₁)
        + u₀ * u₁ * ((R : ℂ) - u₂) := by ring
  have hbig : ‖((R : ℂ)) ^ 3 - u₀ * u₁ * u₂‖ ≤ R ^ 2 * (a₀ + a₁ + a₂) := by
    rw [htel]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    simp only [Complex.norm_mul, Complex.norm_pow, hRC, h₀, h₁]
    apply le_of_eq
    rw [ha₀, ha₁, ha₂]
    ring
  have hcast : ((R : ℂ)) ^ 3 = ((R ^ 3 : ℝ) : ℂ) := by push_cast; ring
  have hsq : 2 * R ^ 3 * (R ^ 3 - (u₀ * u₁ * u₂).re)
      = ‖((R : ℂ)) ^ 3 - u₀ * u₁ * u₂‖ ^ 2 := by
    rw [hcast, norm_sub_sq_of_norm_eq (R ^ 3) _ hprod]
  have h0sq : a₀ ^ 2 = 2 * R * (R - u₀.re) := norm_sub_sq_of_norm_eq R u₀ h₀
  have h1sq : a₁ ^ 2 = 2 * R * (R - u₁.re) := norm_sub_sq_of_norm_eq R u₁ h₁
  have h2sq : a₂ ^ 2 = 2 * R * (R - u₂.re) := norm_sub_sq_of_norm_eq R u₂ h₂
  have hnn : 0 ≤ a₀ + a₁ + a₂ := by positivity
  have hsqle : ‖((R : ℂ)) ^ 3 - u₀ * u₁ * u₂‖ ^ 2 ≤ (R ^ 2 * (a₀ + a₁ + a₂)) ^ 2 := by
    have := Complex.norm_nonneg (((R : ℂ)) ^ 3 - u₀ * u₁ * u₂)
    nlinarith [hbig, this]
  have hcs : (a₀ + a₁ + a₂) ^ 2 ≤ 3 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) := by
    nlinarith [sq_nonneg (a₀ - a₁), sq_nonneg (a₀ - a₂), sq_nonneg (a₁ - a₂)]
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have hchain : 2 * R ^ 3 * (R ^ 3 - (u₀ * u₁ * u₂).re)
      ≤ R ^ 4 * (3 * (2 * R * ((R - u₀.re) + (R - u₁.re) + (R - u₂.re)))) := by
    calc 2 * R ^ 3 * (R ^ 3 - (u₀ * u₁ * u₂).re)
        = ‖((R : ℂ)) ^ 3 - u₀ * u₁ * u₂‖ ^ 2 := hsq
      _ ≤ (R ^ 2 * (a₀ + a₁ + a₂)) ^ 2 := hsqle
      _ = R ^ 4 * (a₀ + a₁ + a₂) ^ 2 := by ring
      _ ≤ R ^ 4 * (3 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2)) := by
          have : (0:ℝ) ≤ R ^ 4 := by positivity
          nlinarith [hcs]
      _ = R ^ 4 * (3 * (2 * R * ((R - u₀.re) + (R - u₁.re) + (R - u₂.re)))) := by
          rw [h0sq, h1sq, h2sq]; ring
  have hR3 : (0 : ℝ) < 2 * R ^ 3 := by positivity
  have := hchain
  nlinarith [hR3, this, hR0]

/-- AUDIT-NOTES B2, `m = 3`, `c = 4`: the density `W = Re(u₀u₁u₂) + 4 ∑_g (1 − Re u_g)` is
at least `3/5` whenever the common modulus `R` satisfies `1 ≤ R` and `R² ≤ 16/15`. -/
theorem triW_core (R : ℝ) (hR1 : 1 ≤ R) (hRsq : R ^ 2 ≤ 16 / 15) (u₀ u₁ u₂ : ℂ)
    (h₀ : ‖u₀‖ = R) (h₁ : ‖u₁‖ = R) (h₂ : ‖u₂‖ = R) :
    3 / 5 ≤ (u₀ * u₁ * u₂).re + 4 * ((1 - u₀.re) + (1 - u₁.re) + (1 - u₂.re)) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hd₀ : 0 ≤ R - u₀.re := by rw [← h₀]; exact sub_nonneg.2 (Complex.re_le_norm u₀)
  have hd₁ : 0 ≤ R - u₁.re := by rw [← h₁]; exact sub_nonneg.2 (Complex.re_le_norm u₁)
  have hd₂ : 0 ≤ R - u₂.re := by rw [← h₂]; exact sub_nonneg.2 (Complex.re_le_norm u₂)
  have hkey := re_prod_lower R hR0 u₀ u₁ u₂ h₀ h₁ h₂
  have hRm1 : R - 1 ≤ 1 / 30 := by nlinarith
  have hcube : 1 ≤ R ^ 3 := one_le_pow₀ hR1
  nlinarith [hkey, hd₀, hd₁, hd₂, hRm1, hcube, hRsq, hR1]

/-! ## The corrected Fourier density of AUDIT-NOTES B2, `m = 3`, `c = 4` -/

/-- The auxiliary signs of the triangle witness: three families (`x`, `z`, `y`) of `t`
copy indices each. -/
abbrev TriSign (t : ℕ) := Fin 3 × Fin t

/-- The complex atom `1 + i√q ε` of the Fourier density, with `ε = sgn b`. -/
noncomputable def triAtom (q : ℝ) (b : Bool) : ℂ :=
  1 + Complex.I * ((Real.sqrt q * sgn b : ℝ) : ℂ)

@[simp] theorem triAtom_re (q : ℝ) (b : Bool) : (triAtom q b).re = 1 := by
  simp [triAtom]

@[simp] theorem triAtom_im (q : ℝ) (b : Bool) :
    (triAtom q b).im = Real.sqrt q * sgn b := by
  simp [triAtom]

/-- `f_g(s) = ∏_i (1 + i√q s_{g,i})`, the factor of the family `g`. -/
noncomputable def triFactor (t : ℕ) (q : ℝ) (s : TriSign t → Bool) (g : Fin 3) : ℂ :=
  ∏ i : Fin t, triAtom q (s (g, i))

/-- `W(s) = Re(f_x f_z f_y) + 4 ∑_g (1 − Re f_g)`, the `m = 3`, `c = 4` density of
AUDIT-NOTES B2 relative to the uniform sign cube. -/
noncomputable def triW (t : ℕ) (q : ℝ) (s : TriSign t → Bool) : ℝ :=
  (triFactor t q s 0 * triFactor t q s 1 * triFactor t q s 2).re
    + 4 * ((1 - (triFactor t q s 0).re) + (1 - (triFactor t q s 1).re)
      + (1 - (triFactor t q s 2).re))

theorem triAtom_norm (q : ℝ) (hq : 0 ≤ q) (b : Bool) :
    ‖triAtom q b‖ = Real.sqrt (1 + q) := by
  rw [Complex.norm_def, Complex.normSq_apply, triAtom_re, triAtom_im]
  congr 1
  cases b <;> simp [sgn] <;> nlinarith [Real.mul_self_sqrt hq]

theorem triFactor_norm (t : ℕ) (q : ℝ) (hq : 0 ≤ q) (s : TriSign t → Bool) (g : Fin 3) :
    ‖triFactor t q s g‖ = Real.sqrt (1 + q) ^ t := by
  rw [triFactor, norm_prod]
  simp [triAtom_norm q hq]

/-- `(1+q)^t ≤ 1/(1 − tq) ≤ 16/15` when `tq ≤ 1/16`: Bernoulli on `(1−q)^t` together with
`(1−q²)^t ≤ 1`. -/
theorem one_add_pow_le (t : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16) :
    (1 + q) ^ t ≤ 16 / 15 := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; norm_num
  have ht1 : (1 : ℝ) ≤ (t : ℕ) := by exact_mod_cast h
  have hq16 : q ≤ 1 / 16 := by nlinarith
  have hbern : 1 + (t : ℝ) * (-q) ≤ (1 + -q) ^ t := one_add_mul_le_pow (by linarith) t
  have hpos : (0 : ℝ) ≤ (1 + q) ^ t := by positivity
  have hprod : (1 + q) ^ t * (1 - q) ^ t ≤ 1 := by
    rw [← mul_pow]
    have hr : (1 + q) * (1 - q) = 1 - q ^ 2 := by ring
    rw [hr]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h1 : (15 : ℝ) / 16 ≤ (1 - q) ^ t := by
    rw [show (1 : ℝ) + (t : ℝ) * -q = 1 - (t : ℝ) * q from by ring,
      show (1 : ℝ) + -q = 1 - q from by ring] at hbern
    linarith
  have h2 : (1 + q) ^ t * ((15 : ℝ) / 16) ≤ (1 + q) ^ t * (1 - q) ^ t :=
    mul_le_mul_of_nonneg_left h1 hpos
  linarith

/-- AUDIT-NOTES B2, the positivity of the corrected density at every sign assignment:
`W ≥ 3/5` whenever `tq ≤ 1/16`. -/
theorem triW_ge (t : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16)
    (s : TriSign t → Bool) : 3 / 5 ≤ triW t q s := by
  have hsq : (0 : ℝ) ≤ 1 + q := by linarith
  set R := Real.sqrt (1 + q) ^ t with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by rw [Real.one_le_sqrt]; linarith)
  have hRsq : R ^ 2 ≤ 16 / 15 := by
    have he : R ^ 2 = (1 + q) ^ t := by
      rw [hR, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hsq]
    rw [he]; exact one_add_pow_le t q hq0 hq
  exact triW_core R hR1 hRsq _ _ _ (triFactor_norm t q hq0 s 0) (triFactor_norm t q hq0 s 1)
    (triFactor_norm t q hq0 s 2)

theorem triW_nonneg (t : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16)
    (s : TriSign t → Bool) : 0 ≤ triW t q s :=
  le_trans (by norm_num) (triW_ge t q hq0 hq s)

/-! ### The moment table (AUDIT-NOTES B2)

`E_ρ ∏_{v ∈ S} s_v` is `1` for `S = ∅`, `0` for odd `|S|`, `−3(−q)^{|S|/2}` for a nonempty
even `S` inside one family, and `(−q)^{|S|/2}` for an even `S` meeting at least two
families. -/

/-- `ζ = i√q`, the per-coordinate Fourier weight. -/
noncomputable def triZeta (q : ℝ) : ℂ := Complex.I * (Real.sqrt q : ℂ)

theorem triZeta_sq (q : ℝ) (hq : 0 ≤ q) : triZeta q ^ 2 = ((-q : ℝ) : ℂ) := by
  rw [triZeta, mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt hq]
  push_cast; ring

/-- The target moment of a character with `n` coordinates: `(−q)^{n/2}` for even `n`
and `0` for odd `n`. -/
def triMom (q : ℝ) (n : ℕ) : ℝ := if n % 2 = 0 then (-q) ^ (n / 2) else 0

theorem triZeta_pow_re (q : ℝ) (hq : 0 ≤ q) (n : ℕ) :
    (triZeta q ^ n).re = triMom q n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp [triMom]
    | 1 => simp [triMom, triZeta]
    | (m + 2) =>
      have h1 : triZeta q ^ (m + 2) = ((-q : ℝ) : ℂ) * triZeta q ^ m := by
        rw [pow_add, triZeta_sq q hq]; ring
      rw [h1, Complex.re_ofReal_mul, ih m (by omega), triMom, triMom,
        show (m + 2) % 2 = m % 2 from by omega, show (m + 2) / 2 = m / 2 + 1 from by omega]
      split_ifs <;> ring

theorem triAtom_add (q : ℝ) : triAtom q true + triAtom q false = 2 := by
  simp [triAtom, sgn]; ring

theorem triAtom_sub (q : ℝ) : -triAtom q true + triAtom q false = 2 * triZeta q := by
  simp [triAtom, sgn, triZeta]; ring

/-- A two-valued product over a finite type. -/
theorem prod_ite_mem_const {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (A B : ℂ) :
    ∏ v : ι, (if v ∈ S then A else B) = A ^ S.card * B ^ (Fintype.card ι - S.card) := by
  rw [← Finset.prod_mul_prod_compl S (fun v => if v ∈ S then A else B)]
  congr 1
  · rw [Finset.prod_congr rfl (fun v hv => ite_eq_left hv), Finset.prod_const]
  · rw [Finset.prod_congr rfl (fun v hv => ite_eq_right (Finset.mem_compl.1 hv)), Finset.prod_const,
      Finset.card_compl]

theorem card_triSign (t : ℕ) : Fintype.card (TriSign t) = 3 * t := by
  simp [TriSign]

/-- The Walsh pairing of the two-valued weight `2ζ` on `S` and `2` off `S`. -/
theorem prod_two_zeta (t : ℕ) (q : ℝ) (S : Finset (TriSign t)) :
    ∏ v : TriSign t, (if v ∈ S then 2 * triZeta q else 2)
      = 2 ^ (3 * t) * triZeta q ^ S.card := by
  rw [prod_ite_mem_const, card_triSign, mul_pow]
  have hle : S.card ≤ 3 * t := by
    simpa [card_triSign] using Finset.card_le_univ S
  rw [mul_assoc, mul_comm (triZeta q ^ S.card), ← mul_assoc, ← pow_add]
  rw [Nat.add_sub_cancel' hle]

/-- The full product `f_x f_z f_y` is the product of the atoms over all auxiliary signs. -/
theorem triFactor_prod (t : ℕ) (q : ℝ) (s : TriSign t → Bool) :
    triFactor t q s 0 * triFactor t q s 1 * triFactor t q s 2
      = ∏ v : TriSign t, triAtom q (s v) := by
  rw [Fintype.prod_prod_type]
  rw [Fin.prod_univ_three (fun g : Fin 3 => ∏ i : Fin t, triAtom q (s (g, i)))]
  rfl

/-- The Walsh moment of the product density. -/
theorem sum_walsh_triProd (t : ℕ) (q : ℝ) (S : Finset (TriSign t)) :
    ∑ s : TriSign t → Bool, (walsh S s : ℂ) *
        (triFactor t q s 0 * triFactor t q s 1 * triFactor t q s 2)
      = 2 ^ (3 * t) * triZeta q ^ S.card := by
  simp only [triFactor_prod]
  rw [sum_walsh_mul_prod S (fun _ b => triAtom q b), ← prod_two_zeta t q S]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ S
  · simp only [ite_eq_left hv, triAtom_sub]
  · simp only [ite_eq_right hv, triAtom_add]

/-- The family factor as a product over all auxiliary signs. -/
theorem triFactor_as_prod (t : ℕ) (q : ℝ) (s : TriSign t → Bool) (g : Fin 3) :
    triFactor t q s g = ∏ v : TriSign t, (if v.1 = g then triAtom q (s v) else 1) := by
  rw [Fintype.prod_prod_type]
  have hstep : ∀ g' : Fin 3,
      (∏ i : Fin t, (if (g', i).1 = g then triAtom q (s (g', i)) else 1))
        = if g' = g then (∏ i : Fin t, triAtom q (s (g', i))) else 1 := by
    intro g'
    by_cases h : g' = g
    · simp [h]
    · simp [h]
  rw [Finset.prod_congr rfl (fun g' (_ : g' ∈ (Finset.univ : Finset (Fin 3))) => hstep g'),
    Finset.prod_ite_eq' (Finset.univ : Finset (Fin 3)) g
      (fun g' => ∏ i : Fin t, triAtom q (s (g', i))), ite_eq_left (Finset.mem_univ g)]
  rfl

/-- The Walsh moment of a single family factor: zero unless `S` lies inside that family. -/
theorem sum_walsh_triFactor (t : ℕ) (q : ℝ) (S : Finset (TriSign t)) (g : Fin 3) :
    ∑ s : TriSign t → Bool, (walsh S s : ℂ) * triFactor t q s g
      = if ∀ v ∈ S, v.1 = g then 2 ^ (3 * t) * triZeta q ^ S.card else 0 := by
  simp only [triFactor_as_prod]
  rw [sum_walsh_mul_prod S (fun v b => if v.1 = g then triAtom q b else 1)]
  by_cases hS : ∀ v ∈ S, v.1 = g
  · rw [ite_eq_left hS, ← prod_two_zeta t q S]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    by_cases hv : v ∈ S
    · simp only [ite_eq_left hv, ite_eq_left (hS v hv), triAtom_sub]
    · simp only [ite_eq_right hv]
      by_cases hg : v.1 = g
      · simp only [ite_eq_left hg, triAtom_add]
      · simp only [ite_eq_right hg]; norm_num
  · rw [ite_eq_right hS]
    obtain ⟨v, hvS, hvg⟩ : ∃ v ∈ S, v.1 ≠ g := by
      by_contra hc
      exact hS (fun v hv => by
        by_contra h
        exact hc ⟨v, hv, h⟩)
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simp only [ite_eq_left hvS, ite_eq_right hvg]
    ring

/-- The Walsh moment of the constant density. -/
theorem sum_walsh_triOne (t : ℕ) (S : Finset (TriSign t)) :
    ∑ s : TriSign t → Bool, (walsh S s : ℂ)
      = if S = ∅ then 2 ^ (3 * t) else 0 := by
  have hb := sum_walsh_mul_prod S (fun (_ : TriSign t) (_ : Bool) => (1 : ℂ))
  simp only [Finset.prod_const_one, mul_one] at hb
  rw [hb]
  by_cases hS : S = ∅
  · subst hS
    rw [ite_eq_left rfl]
    simp only [Finset.prod_const, Finset.card_univ, card_triSign, Finset.notMem_empty,
      ite_false]
    norm_num
  · rw [ite_eq_right hS]
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.2 hS
    refine Finset.prod_eq_zero (Finset.mem_univ v) ?_
    simp [hv]

/-- The Fourier coefficient correction of AUDIT-NOTES B2 with `c = 4`: the characters that
are nonempty and confined to one sign family have their moment multiplied by `1 − 4 = −3`;
every other character keeps the target moment. -/
def triCoeff {t : ℕ} (S : Finset (TriSign t)) : ℝ :=
  if S = ∅ then 1 else if ∃ g : Fin 3, ∀ v ∈ S, v.1 = g then -3 else 1

/-- AUDIT-NOTES B2, the moment table of the corrected density. Against the uniform sign
cube, `∑_s χ_S(s) W(s) = 2^{3t} c_S (−q)^{|S|/2}` with `c_S = 1` for `S = ∅` or `S` meeting
at least two families and `c_S = −3` for a nonempty `S` inside one family; the moment
vanishes for odd `|S|`. -/
theorem triW_moment (t : ℕ) (q : ℝ) (hq : 0 ≤ q) (S : Finset (TriSign t)) :
    ∑ s : TriSign t → Bool, walsh S s * triW t q s
      = 2 ^ (3 * t) * (triCoeff S * triMom q S.card) := by
  have hkey : ∀ s : TriSign t → Bool, walsh S s * triW t q s
      = ((walsh S s : ℂ) * (triFactor t q s 0 * triFactor t q s 1 * triFactor t q s 2)).re
        - 4 * ((walsh S s : ℂ) * triFactor t q s 0).re
        - 4 * ((walsh S s : ℂ) * triFactor t q s 1).re
        - 4 * ((walsh S s : ℂ) * triFactor t q s 2).re
        + 12 * ((walsh S s : ℂ)).re := by
    intro s
    simp only [triW, Complex.re_ofReal_mul, Complex.ofReal_re]
    ring
  rw [Finset.sum_congr rfl (fun s (_ : s ∈ (Finset.univ : Finset (TriSign t → Bool))) => hkey s)]
  rw [show ∀ (f g₀ g₁ g₂ h : (TriSign t → Bool) → ℝ),
      (∑ s, (f s - 4 * g₀ s - 4 * g₁ s - 4 * g₂ s + 12 * h s))
        = (∑ s, f s) - 4 * (∑ s, g₀ s) - 4 * (∑ s, g₁ s) - 4 * (∑ s, g₂ s)
          + 12 * (∑ s, h s) from by
    intro f g₀ g₁ g₂ h
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]]
  simp only [← Complex.re_sum]
  rw [sum_walsh_triProd, sum_walsh_triFactor, sum_walsh_triFactor, sum_walsh_triFactor,
    sum_walsh_triOne]
  have hcoe : ((2 : ℂ)) ^ (3 * t) = (((2 : ℝ) ^ (3 * t) : ℝ) : ℂ) := by push_cast; ring
  have hA : (((2 : ℂ)) ^ (3 * t) * triZeta q ^ S.card).re
      = 2 ^ (3 * t) * triMom q S.card := by
    rw [hcoe, Complex.re_ofReal_mul, triZeta_pow_re q hq]
  have hone : (((2 : ℂ)) ^ (3 * t)).re = 2 ^ (3 * t) := by rw [hcoe, Complex.ofReal_re]
  by_cases hS : S = ∅
  · subst hS
    have htriv : ∀ g : Fin 3, ∀ v ∈ (∅ : Finset (TriSign t)), v.1 = g := by
      intro g v hv; exact absurd hv (Finset.notMem_empty v)
    rw [ite_eq_left (htriv 0), ite_eq_left (htriv 1), ite_eq_left (htriv 2), ite_eq_left rfl, hA, hone,
      triCoeff, ite_eq_left rfl]
    simp only [Finset.card_empty, triMom]
    norm_num
    ring
  · rw [triCoeff, ite_eq_right hS, ite_eq_right hS]
    obtain ⟨v₀, hv₀⟩ := Finset.nonempty_iff_ne_empty.2 hS
    by_cases hone' : ∃ g : Fin 3, ∀ v ∈ S, v.1 = g
    · obtain ⟨g₀, hg₀⟩ := hone'
      have hiff : ∀ g : Fin 3, (∀ v ∈ S, v.1 = g) ↔ g = g₀ := by
        intro g
        constructor
        · intro h; rw [← h v₀ hv₀, hg₀ v₀ hv₀]
        · rintro rfl; exact hg₀
      rw [if_congr (hiff 0) rfl rfl, if_congr (hiff 1) rfl rfl, if_congr (hiff 2) rfl rfl,
        ite_eq_left (⟨g₀, hg₀⟩ : ∃ g : Fin 3, ∀ v ∈ S, v.1 = g)]
      have hsum : ∀ X : ℂ,
          (if (0 : Fin 3) = g₀ then X else 0).re + (if (1 : Fin 3) = g₀ then X else 0).re
            + (if (2 : Fin 3) = g₀ then X else 0).re = X.re := by
        intro X; fin_cases g₀ <;> norm_num [Fin.ext_iff]
      have h3 := hsum (((2 : ℂ)) ^ (3 * t) * triZeta q ^ S.card)
      rw [hA] at h3
      rw [hA]
      simp only [Complex.zero_re, mul_zero, add_zero]
      linear_combination (-4 : ℝ) * h3
    · rw [ite_eq_right hone']
      have hz : ∀ g : Fin 3, ¬ (∀ v ∈ S, v.1 = g) := fun g h => hone' ⟨g, h⟩
      rw [ite_eq_right (hz 0), ite_eq_right (hz 1), ite_eq_right (hz 2), hA]
      simp

/-- The density normalizes: `E W = 1` against the uniform sign cube. -/
theorem triW_sum (t : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    ∑ s : TriSign t → Bool, triW t q s = 2 ^ (3 * t) := by
  have h := triW_moment t q hq (∅ : Finset (TriSign t))
  simp only [walsh, Finset.prod_empty, one_mul, triCoeff, Finset.card_empty, triMom] at h
  rw [h]; norm_num

/-- `ρ(s) = 2^{-3t} W(s)`, the witness density on the auxiliary signs. -/
noncomputable def triDensity (t : ℕ) (q : ℝ) (s : TriSign t → Bool) : ℝ :=
  (1 / 2 ^ (3 * t)) * triW t q s

/-- AUDIT-NOTES B2: the corrected density is a genuine probability law on the `3t`
auxiliary signs whenever `tq ≤ 1/16`. -/
theorem triDensity_isLaw (t : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16) :
    IsLaw (triDensity t q) := by
  constructor
  · intro s
    have := triW_nonneg t q hq0 hq s
    have h2 : (0 : ℝ) < 2 ^ (3 * t) := by positivity
    rw [triDensity]
    positivity
  · rw [show (∑ s : TriSign t → Bool, triDensity t q s)
        = (1 / 2 ^ (3 * t)) * ∑ s : TriSign t → Bool, triW t q s from by
      rw [Finset.mul_sum]; rfl]
    rw [triW_sum t q hq0]
    have h2 : (2 : ℝ) ^ (3 * t) ≠ 0 := by positivity
    field_simp

/-- The parity-perfect triangle target is a law with all one- and two-point moments `−q`. -/
theorem triParity_isLaw (q : ℝ) (hq0 : 0 ≤ q) (hq : q ≤ 1 / 3) :
    IsLaw (triParity q) ∧ triMeanA (triParity q) = -q ∧ triMeanB (triParity q) = -q ∧
      triMeanC (triParity q) = -q := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rintro ⟨a, b, c⟩
    cases a <;> cases b <;> cases c <;> simp [triParity, sgn] <;> linarith
  · simp [Fintype.sum_prod_type, triParity, sgn]
    ring
  · simp [triMeanA, Fintype.sum_prod_type, triParity, sgn]
    ring
  · simp [triMeanB, Fintype.sum_prod_type, triParity, sgn]
    ring
  · simp [triMeanC, Fintype.sum_prod_type, triParity, sgn]
    ring


end TriangleInflation.Graph
