/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Graph.Linear
import LeanPool.InflationTermination.TriangleInflation.Graph.CycleWitness

/-!
# The square witness at q = Θ(1/t)

Theorem `thm:squarelinear` of `papers/inflation-nontermination/paper/sections/15-cycles.tex`.

The corrected Fourier density with `m = 4` families and `c = 5`,
`W = Re ∏_g f_g + 5 ∑_g (1 − Re f_g)`, is pushed forward along the parity read of
`CycleWitness.lean`. Its moments agree with those of the auxiliary density `auxH` on every
set of signs that is empty or meets at least two families, and every character that an
injectable, ancestral-product or diagonal prescription looks at has a latent boundary of
that kind. So each prescribed pushforward of the new witness equals the corresponding
pushforward of `parWit`, and the obligations are inherited from `parWit_diag`,
`parWit_injectable` and `parWit_ai`, which hold for every real `q`.
-/

namespace TriangleInflation.Graph

open Finset TriangleInflation

namespace SqWitnessAux

open CycleWitnessAux

/-! ## Four-factor telescoping -/

/-- The `m = 4` case of `re_prod_lower`: for four complex numbers of modulus `R`,
`R⁴ − Re(u₀u₁u₂u₃) ≤ 4R³ ∑_g (R − Re u_g)`. -/
theorem re_prod_lower4 (R : ℝ) (hR0 : 0 < R) (u₀ u₁ u₂ u₃ : ℂ)
    (h₀ : ‖u₀‖ = R) (h₁ : ‖u₁‖ = R) (h₂ : ‖u₂‖ = R) (h₃ : ‖u₃‖ = R) :
    R ^ 4 - (u₀ * u₁ * u₂ * u₃).re ≤
      4 * R ^ 3 * ((R - u₀.re) + (R - u₁.re) + (R - u₂.re) + (R - u₃.re)) := by
  set a₀ := ‖(R : ℂ) - u₀‖ with ha₀
  set a₁ := ‖(R : ℂ) - u₁‖ with ha₁
  set a₂ := ‖(R : ℂ) - u₂‖ with ha₂
  set a₃ := ‖(R : ℂ) - u₃‖ with ha₃
  have hRC : ‖(R : ℂ)‖ = R := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
  have hprod : ‖u₀ * u₁ * u₂ * u₃‖ = R ^ 4 := by
    rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_mul, h₀, h₁, h₂, h₃]; ring
  have htel : ((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃ =
      ((R : ℂ)) ^ 3 * ((R : ℂ) - u₀) + ((R : ℂ)) ^ 2 * u₀ * ((R : ℂ) - u₁)
        + (R : ℂ) * u₀ * u₁ * ((R : ℂ) - u₂) + u₀ * u₁ * u₂ * ((R : ℂ) - u₃) := by ring
  have hbig : ‖((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃‖ ≤ R ^ 3 * (a₀ + a₁ + a₂ + a₃) := by
    rw [htel]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    simp only [Complex.norm_mul, Complex.norm_pow, hRC, h₀, h₁, h₂]
    apply le_of_eq
    rw [ha₀, ha₁, ha₂, ha₃]
    ring
  have hcast : ((R : ℂ)) ^ 4 = ((R ^ 4 : ℝ) : ℂ) := by push_cast; ring
  have hsq : 2 * R ^ 4 * (R ^ 4 - (u₀ * u₁ * u₂ * u₃).re)
      = ‖((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃‖ ^ 2 := by
    rw [hcast, norm_sub_sq_of_norm_eq (R ^ 4) _ hprod]
  have h0sq : a₀ ^ 2 = 2 * R * (R - u₀.re) := norm_sub_sq_of_norm_eq R u₀ h₀
  have h1sq : a₁ ^ 2 = 2 * R * (R - u₁.re) := norm_sub_sq_of_norm_eq R u₁ h₁
  have h2sq : a₂ ^ 2 = 2 * R * (R - u₂.re) := norm_sub_sq_of_norm_eq R u₂ h₂
  have h3sq : a₃ ^ 2 = 2 * R * (R - u₃.re) := norm_sub_sq_of_norm_eq R u₃ h₃
  have hnn : 0 ≤ a₀ + a₁ + a₂ + a₃ := by positivity
  have hsqle : ‖((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃‖ ^ 2
      ≤ (R ^ 3 * (a₀ + a₁ + a₂ + a₃)) ^ 2 := by
    have := norm_nonneg (((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃)
    nlinarith [hbig, this]
  have hcs : (a₀ + a₁ + a₂ + a₃) ^ 2 ≤ 4 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2) := by
    nlinarith [sq_nonneg (a₀ - a₁), sq_nonneg (a₀ - a₂), sq_nonneg (a₁ - a₂),
      sq_nonneg (a₀ - a₃), sq_nonneg (a₁ - a₃), sq_nonneg (a₂ - a₃)]
  set D := (R - u₀.re) + (R - u₁.re) + (R - u₂.re) + (R - u₃.re) with hD
  have hchain : 2 * R ^ 4 * (R ^ 4 - (u₀ * u₁ * u₂ * u₃).re) ≤ 2 * R ^ 4 * (4 * R ^ 3 * D) := by
    calc 2 * R ^ 4 * (R ^ 4 - (u₀ * u₁ * u₂ * u₃).re)
        = ‖((R : ℂ)) ^ 4 - u₀ * u₁ * u₂ * u₃‖ ^ 2 := hsq
      _ ≤ (R ^ 3 * (a₀ + a₁ + a₂ + a₃)) ^ 2 := hsqle
      _ = R ^ 6 * (a₀ + a₁ + a₂ + a₃) ^ 2 := by ring
      _ ≤ R ^ 6 * (4 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2)) := by
          have : (0:ℝ) ≤ R ^ 6 := by positivity
          exact mul_le_mul_of_nonneg_left hcs this
      _ = 2 * R ^ 4 * (4 * R ^ 3 * D) := by
          rw [h0sq, h1sq, h2sq, h3sq, hD]; ring
  have hR4 : (0 : ℝ) < 2 * R ^ 4 := by positivity
  exact le_of_mul_le_mul_left hchain hR4

/-- The `m = 4`, `c = 5` density `Re(u₀u₁u₂u₃) + 5 ∑_g (1 − Re u_g)` is at least `1/3`
whenever the common modulus `R` satisfies `1 ≤ R` and `R² ≤ 16/15`. -/
theorem sqW_core (R : ℝ) (hR1 : 1 ≤ R) (hRsq : R ^ 2 ≤ 16 / 15) (u₀ u₁ u₂ u₃ : ℂ)
    (h₀ : ‖u₀‖ = R) (h₁ : ‖u₁‖ = R) (h₂ : ‖u₂‖ = R) (h₃ : ‖u₃‖ = R) :
    1 / 3 ≤ (u₀ * u₁ * u₂ * u₃).re
      + 5 * ((1 - u₀.re) + (1 - u₁.re) + (1 - u₂.re) + (1 - u₃.re)) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le one_pos hR1
  have hd₀ : 0 ≤ R - u₀.re := by rw [← h₀]; exact sub_nonneg.2 (Complex.re_le_norm u₀)
  have hd₁ : 0 ≤ R - u₁.re := by rw [← h₁]; exact sub_nonneg.2 (Complex.re_le_norm u₁)
  have hd₂ : 0 ≤ R - u₂.re := by rw [← h₂]; exact sub_nonneg.2 (Complex.re_le_norm u₂)
  have hd₃ : 0 ≤ R - u₃.re := by rw [← h₃]; exact sub_nonneg.2 (Complex.re_le_norm u₃)
  have hkey := re_prod_lower4 R hR0 u₀ u₁ u₂ u₃ h₀ h₁ h₂ h₃
  have hRle : R ≤ 31 / 30 := by nlinarith
  have hR3 : R ^ 3 ≤ 5 / 4 := by
    have := pow_le_pow_left₀ hR0.le hRle 3
    norm_num at this
    linarith
  have hR4 : 1 ≤ R ^ 4 := one_le_pow₀ hR1
  set D := (R - u₀.re) + (R - u₁.re) + (R - u₂.re) + (R - u₃.re) with hD
  have hD0 : 0 ≤ D := by rw [hD]; linarith
  have hmul : 0 ≤ (5 - 4 * R ^ 3) * D := mul_nonneg (by linarith) hD0
  have hsum : (1 - u₀.re) + (1 - u₁.re) + (1 - u₂.re) + (1 - u₃.re) = D - 4 * (R - 1) := by
    rw [hD]; ring
  rw [hsum]
  nlinarith [hkey, hmul, hR4, hRle]

/-! ## The corrected density with a general family type -/

section Density


variable {κ : Type*} [Fintype κ] [DecidableEq κ] {t : ℕ}

/-- `f_g(s) = ∏_i (1 + i√q s_{g,i})`, the factor of the family `g`. -/
noncomputable def fam (t : ℕ) (q : ℝ) (s : κ × Fin t → Bool) (g : κ) : ℂ :=
  ∏ i : Fin t, triAtom q (s (g, i))

/-- `W(s) = Re ∏_g f_g + 5 ∑_g (1 − Re f_g)`. -/
noncomputable def sqW (t : ℕ) (q : ℝ) (s : κ × Fin t → Bool) : ℝ :=
  (∏ g, fam t q s g).re + 5 * ∑ g, (1 - (fam t q s g).re)

omit [Fintype κ] [DecidableEq κ] in
theorem fam_norm (q : ℝ) (hq : 0 ≤ q) (s : κ × Fin t → Bool) (g : κ) :
    ‖fam t q s g‖ = Real.sqrt (1 + q) ^ t := by
  rw [fam, norm_prod]
  simp [triAtom_norm q hq]

omit [DecidableEq κ] in
theorem prod_fam (q : ℝ) (s : κ × Fin t → Bool) :
    ∏ g, fam t q s g = ∏ v : κ × Fin t, triAtom q (s v) := by
  rw [Fintype.prod_prod_type]
  rfl

theorem prod_two_zeta' {ι : Type*} [Fintype ι] [DecidableEq ι] (q : ℝ) (S : Finset ι) :
    ∏ v : ι, (if v ∈ S then 2 * triZeta q else 2)
      = 2 ^ Fintype.card ι * triZeta q ^ S.card := by
  rw [prod_ite_mem_const, mul_pow]
  have hle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
  rw [mul_assoc, mul_comm (triZeta q ^ S.card), ← mul_assoc, ← pow_add,
    Nat.add_sub_cancel' hle]

theorem sum_walsh_prodFam (q : ℝ) (S : Finset (κ × Fin t)) :
    ∑ s : κ × Fin t → Bool, (walsh S s : ℂ) * ∏ g, fam t q s g
      = 2 ^ Fintype.card (κ × Fin t) * triZeta q ^ S.card := by
  simp only [prod_fam]
  rw [sum_walsh_mul_prod S (fun _ b => triAtom q b), ← prod_two_zeta' q S]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  by_cases hv : v ∈ S
  · simp only [ite_eq_left hv, triAtom_sub]
  · simp only [ite_eq_right hv, triAtom_add]

theorem fam_as_prod (q : ℝ) (s : κ × Fin t → Bool) (g : κ) :
    fam t q s g = ∏ v : κ × Fin t, (if v.1 = g then triAtom q (s v) else 1) := by
  rw [Fintype.prod_prod_type]
  have hstep : ∀ g' : κ,
      (∏ i : Fin t, (if (g', i).1 = g then triAtom q (s (g', i)) else 1))
        = if g' = g then (∏ i : Fin t, triAtom q (s (g', i))) else 1 := by
    intro g'
    by_cases h : g' = g
    · simp [h]
    · simp [h]
  rw [Finset.prod_congr rfl (fun g' (_ : g' ∈ (Finset.univ : Finset κ)) => hstep g'),
    Finset.prod_ite_eq' (Finset.univ : Finset κ) g
      (fun g' => ∏ i : Fin t, triAtom q (s (g', i))), ite_eq_left (Finset.mem_univ g)]
  rfl

theorem sum_walsh_fam (q : ℝ) (S : Finset (κ × Fin t)) (g : κ) :
    ∑ s : κ × Fin t → Bool, (walsh S s : ℂ) * fam t q s g
      = if ∀ v ∈ S, v.1 = g then 2 ^ Fintype.card (κ × Fin t) * triZeta q ^ S.card
        else 0 := by
  simp only [fam_as_prod]
  rw [sum_walsh_mul_prod S (fun v b => if v.1 = g then triAtom q b else 1)]
  by_cases hS : ∀ v ∈ S, v.1 = g
  · rw [ite_eq_left hS, ← prod_two_zeta' q S]
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

/-- A set of signs is *spread* when it is empty or meets at least two families. -/
def Spread (S : Finset (κ × Fin t)) : Prop := ∀ l ∈ S, ∃ l' ∈ S, l'.1 ≠ l.1

/-- On a spread set the family corrections cancel: the `g`-term of the moment vanishes. -/
theorem fam_term_zero (q : ℝ) (S : Finset (κ × Fin t)) (hS : Spread S) (g : κ) :
    ∑ s : κ × Fin t → Bool, (walsh S s - ((walsh S s : ℂ) * fam t q s g).re) = 0 := by
  rw [Finset.sum_sub_distrib, ← Complex.re_sum, sum_walsh_fam]
  have hw : (∑ s : κ × Fin t → Bool, walsh S s)
      = if S = ∅ then (2 : ℝ) ^ Fintype.card (κ × Fin t) else 0 := sum_prod_sgn S
  rw [hw]
  by_cases h0 : S = ∅
  · subst h0
    have htriv : ∀ v ∈ (∅ : Finset (κ × Fin t)), v.1 = g := by
      intro v hv; exact absurd hv (Finset.notMem_empty v)
    rw [ite_eq_left rfl, ite_eq_left htriv]
    simp only [Finset.card_empty, pow_zero, mul_one]
    norm_cast
    simp
  · rw [ite_eq_right h0]
    have hn : ¬ ∀ v ∈ S, v.1 = g := by
      intro hall
      obtain ⟨l, hl⟩ := Finset.nonempty_iff_ne_empty.2 h0
      obtain ⟨l', hl', hne⟩ := hS l hl
      exact hne (by rw [hall l hl, hall l' hl'])
    rw [ite_eq_right hn]
    simp

theorem sqW_moment (q : ℝ) (hq : 0 ≤ q) (S : Finset (κ × Fin t)) (hS : Spread S) :
    ∑ s : κ × Fin t → Bool, walsh S s * sqW t q s
      = 2 ^ Fintype.card (κ × Fin t) * triMom q S.card := by
  have h1 : ∀ s : κ × Fin t → Bool, walsh S s * sqW t q s
      = ((walsh S s : ℂ) * ∏ g, fam t q s g).re
        + 5 * ∑ g, (walsh S s - ((walsh S s : ℂ) * fam t q s g).re) := by
    intro s
    simp only [sqW, Complex.re_ofReal_mul, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun g _ => by ring
  rw [Finset.sum_congr rfl (fun s _ => h1 s), Finset.sum_add_distrib, ← Complex.re_sum,
    sum_walsh_prodFam, ← Finset.mul_sum, Finset.sum_comm]
  simp only [fam_term_zero q S hS, Finset.sum_const_zero, mul_zero, add_zero]
  have hcoe : ((2 : ℂ)) ^ Fintype.card (κ × Fin t)
      = (((2 : ℝ) ^ Fintype.card (κ × Fin t) : ℝ) : ℂ) := by push_cast; ring
  rw [hcoe, Complex.re_ofReal_mul, triZeta_pow_re q hq]

/-- `ρ = 2^{−N} W`, the witness density on the auxiliary signs. -/
noncomputable def sqDensity (t : ℕ) (q : ℝ) (s : κ × Fin t → Bool) : ℝ :=
  (1 / 2 ^ Fintype.card (κ × Fin t)) * sqW t q s

theorem sqDensity_moment (q : ℝ) (hq : 0 ≤ q) (S : Finset (κ × Fin t)) (hS : Spread S) :
    (∑ s : κ × Fin t → Bool, sqDensity t q s * ∏ l ∈ S, sgn (s l))
      = if Even S.card then (-q) ^ (S.card / 2) else 0 := by
  have h := sqW_moment q hq S hS
  have e : ∀ s : κ × Fin t → Bool, sqDensity t q s * ∏ l ∈ S, sgn (s l)
      = (1 / 2 ^ Fintype.card (κ × Fin t)) * (walsh S s * sqW t q s) := by
    intro s; simp only [sqDensity, walsh]; ring
  rw [Finset.sum_congr rfl (fun s _ => e s), ← Finset.mul_sum, h, ← mul_assoc]
  have h2 : (2 : ℝ) ^ Fintype.card (κ × Fin t) ≠ 0 := by positivity
  rw [one_div_mul_cancel h2, one_mul, triMom]
  by_cases he : Even S.card
  · rw [ite_eq_left he, ite_eq_left (Nat.even_iff.1 he)]
  · rw [ite_eq_right he, ite_eq_right (fun h => he (Nat.even_iff.2 h))]

theorem sqDensity_sum (q : ℝ) (hq : 0 ≤ q) :
    (∑ s : κ × Fin t → Bool, sqDensity t q s) = 1 := by
  have h := sqDensity_moment (t := t) (κ := κ) q hq ∅ (fun l hl => absurd hl (by simp))
  simpa using h

omit [DecidableEq κ] in
theorem sqW_ge (e : κ ≃ Fin 4) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16)
    (s : κ × Fin t → Bool) : 1 / 3 ≤ sqW t q s := by
  classical
  have hsq : (0 : ℝ) ≤ 1 + q := by linarith
  set R := Real.sqrt (1 + q) ^ t with hR
  have hR1 : 1 ≤ R := one_le_pow₀ (by rw [Real.one_le_sqrt]; linarith)
  have hRsq : R ^ 2 ≤ 16 / 15 := by
    have he : R ^ 2 = (1 + q) ^ t := by
      rw [hR, ← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hsq]
    rw [he]; exact one_add_pow_le t q hq0 hq
  have hprod : ∏ g, fam t q s g = ∏ j : Fin 4, fam t q s (e.symm j) :=
    (Equiv.prod_comp e.symm (fun g => fam t q s g)).symm
  have hsum : ∑ g, (1 - (fam t q s g).re) = ∑ j : Fin 4, (1 - (fam t q s (e.symm j)).re) :=
    (Equiv.sum_comp e.symm (fun g => (1 - (fam t q s g).re))).symm
  rw [sqW, hprod, hsum, Fin.prod_univ_four, Fin.sum_univ_four]
  have hc := sqW_core R hR1 hRsq _ _ _ _ (fam_norm q hq0 s (e.symm 0))
    (fam_norm q hq0 s (e.symm 1)) (fam_norm q hq0 s (e.symm 2)) (fam_norm q hq0 s (e.symm 3))
  linarith

omit [DecidableEq κ] in
theorem sqDensity_nonneg (e : κ ≃ Fin 4) (q : ℝ) (hq0 : 0 ≤ q) (hq : (t : ℝ) * q ≤ 1 / 16)
    (s : κ × Fin t → Bool) : 0 ≤ sqDensity t q s := by
  classical
  have := sqW_ge e q hq0 hq s
  rw [sqDensity]
  have : 0 ≤ sqW t q s := le_trans (by norm_num) this
  positivity

omit [DecidableEq κ] in
theorem sqDensity_perm (q : ℝ) (π : κ → Equiv.Perm (Fin t)) (s : κ × Fin t → Bool) :
    sqDensity t q (fun l => s (l.1, π l.1 l.2)) = sqDensity t q s := by
  have hf : ∀ g, fam t q (fun l => s (l.1, π l.1 l.2)) g = fam t q s g := fun g =>
    Equiv.prod_comp (π g) (fun i => triAtom q (s (g, i)))
  simp only [sqDensity, sqW, hf]

end Density

/-! ## The witness on a cycle -/

section Witness

variable {m t : ℕ}

/-- The square-type witness: the corrected density pushed forward along the parity read. -/
noncomputable def sqWit (hm : 3 ≤ m) (t : ℕ) (q : ℝ) : GAssign (cycle m hm) t → ℝ :=
  pushforward (sqDensity (κ := (cycle m hm).Edge) t q) parityRead

theorem sqWit_moment (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q) (A : Finset (GObs (cycle m hm) t))
    (hA : Spread (latBd A)) :
    (∑ ω, sqWit hm t q ω * ∏ o ∈ A, sgn (ω o))
      = ∑ ω, parWit (cycle m hm) t q ω * ∏ o ∈ A, sgn (ω o) := by
  rw [parWit_moment, sqWit, ← Sound.sum_mul_comp]
  rw [Finset.sum_congr rfl fun s _ => by rw [prod_sgn_parityRead A s]]
  exact sqDensity_moment q hq0 _ hA

/-- A pushforward whose characters all pull back to characters with spread latent boundary is
the same for the new witness and for `parWit`. -/
theorem push_eq (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q) {β : Type} [Finite β] [DecidableEq β]
    {ι : Type} [Finite ι] (f : GAssign (cycle m hm) t → β) (E : β ≃ (ι → Bool))
    (h : ∀ F : Finset ι, ∃ A : Finset (GObs (cycle m hm) t), Spread (latBd A) ∧
      ∀ ω, (∏ v ∈ F, sgn (E (f ω) v)) = ∏ o ∈ A, sgn (ω o)) :
    pushforward (sqWit hm t q) f = pushforward (parWit (cycle m hm) t q) f := by
  classical
  let := Fintype.ofFinite β
  let := Fintype.ofFinite ι
  refine eq_of_moments E _ _ fun F => ?_
  obtain ⟨A, hA, hprod⟩ := h F
  rw [← Sound.sum_mul_comp (G := fun b => ∏ v ∈ F, sgn (E b v)),
    ← Sound.sum_mul_comp (G := fun b => ∏ v ∈ F, sgn (E b v))]
  simp only [hprod]
  exact sqWit_moment hm q hq0 A hA

theorem spread_copy (hm : 3 ≤ m) (ι : (cycle m hm).Edge → Fin t)
    {A : Finset (GObs (cycle m hm) t)} (hA : A ⊆ copySet ι) : Spread (latBd A) := by
  intro l hl
  rw [latBd_copy hm ι hA] at hl ⊢
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hl
  have h2 : 1 < (cycleBoundary m (vertSet hm A)).card := by
    have hpos := Finset.card_pos.2 ⟨j, hj⟩
    obtain ⟨k, hk⟩ := cycleBoundary_card_even (vertSet hm A)
    omega
  obtain ⟨j', hj', hne⟩ := Finset.exists_mem_ne h2 j
  exact ⟨_, Finset.mem_image_of_mem _ hj', fun h => hne (ce_injective hm h)⟩

theorem spread_family (hm : 3 ≤ m) {n : Type*} [Fintype n]
    (A : n → Finset (GObs (cycle m hm) t)) (ιf : n → (cycle m hm).Edge → Fin t)
    (hA : ∀ k, A k ⊆ copySet (ιf k))
    (hd : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k'))) :
    Spread (latBd (Finset.univ.biUnion A)) := by
  classical
  intro l hl
  rw [latBd_biUnion A hd] at hl ⊢
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hl
  obtain ⟨l', hl', hne⟩ := spread_copy hm (ιf k) (hA k) l hk
  exact ⟨l', Finset.mem_biUnion.2 ⟨k, Finset.mem_univ _, hl'⟩, hne⟩

theorem sqWit_isLaw (hm : 3 ≤ m) (e : (cycle m hm).Edge ≃ Fin 4) (q : ℝ) (hq0 : 0 ≤ q)
    (hq : (t : ℝ) * q ≤ 1 / 16) : IsLaw (sqWit hm t q) := by
  refine ⟨fun ω => Finset.sum_nonneg fun s _ => ?_, ?_⟩
  · by_cases h : parityRead s = ω
    · rw [ite_eq_left h]; exact sqDensity_nonneg e q hq0 hq s
    · rw [ite_eq_right h]
  · rw [sqWit, Sound.sum_pushforward]
    exact sqDensity_sum q hq0

theorem sqWit_symmetric (hm : 3 ≤ m) (q : ℝ) : GSymmetric t (sqWit hm t q) := by
  intro π ω
  simp only [sqWit, pushforward]
  refine (Fintype.sum_bijective (fun s l => s (Sound.gLatentPerm π l)) ?_ _ _ fun s => ?_).symm
  · refine ⟨fun s s' h => ?_, fun s => ⟨fun l => s ((Sound.gLatentPerm π).symm l), ?_⟩⟩
    · funext l
      have := congrFun h ((Sound.gLatentPerm π).symm l)
      simpa using this
    · funext l; simp
  · have hd : sqDensity (κ := (cycle m hm).Edge) t q (fun l => s (Sound.gLatentPerm π l))
        = sqDensity t q s := sqDensity_perm q π s
    rw [parityRead_gLatentPerm, hd]
    by_cases h : parityRead s = ω
    · rw [ite_eq_left h, ite_eq_left (congrArg _ h)]
    · rw [ite_eq_right h, ite_eq_right (fun hc => h (gRelabel_injective π hc))]

theorem sqWit_diag_eq (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q) :
    pushforward (sqWit hm t q) readDiag = pushforward (parWit (cycle m hm) t q) readDiag := by
  refine push_eq hm q hq0 readDiag (Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm
    fun F => ?_
  set Ar : Fin t → Finset (GObs (cycle m hm) t) :=
    fun r => (F.filter (fun p => p.1 = r)).image (Sound.diagObs (cycle m hm) t) with hArdef
  have hcopy : ∀ r : Fin t, Ar r ⊆ copySet (fun _ : (cycle m hm).Edge => r) := by
    intro r o ho
    obtain ⟨p, hp, hpo⟩ := Finset.mem_image.1 ho
    have hp1 : p.1 = r := (Finset.mem_filter.1 hp).2
    refine Finset.mem_image.2 ⟨p.2, Finset.mem_univ _, ?_⟩
    rw [← hpo, ← hp1]
    rfl
  have hd : ∀ r r' : Fin t, r ≠ r' →
      Disjoint (gAncestorsOf (Ar r)) (gAncestorsOf (Ar r')) := by
    intro r r' hrr
    rw [Finset.disjoint_left]
    intro l hl hl'
    have h1 : l.2 = r := snd_of_mem_gAncestorsOf (hcopy r) hl
    have h2 : l.2 = r' := snd_of_mem_gAncestorsOf (hcopy r') hl'
    exact hrr (by rw [← h1, h2])
  have hArdisj : ∀ r ∈ (Finset.univ : Finset (Fin t)), ∀ r' ∈ (Finset.univ : Finset (Fin t)),
      r ≠ r' → Disjoint (Ar r) (Ar r') :=
    fun r _ r' _ h => Sound.disjoint_of_gAI (hd r r' h)
  refine ⟨Finset.univ.biUnion Ar, spread_family hm Ar (fun r _ => r) hcopy hd, fun ω => ?_⟩
  have hconv : (∏ p ∈ F, sgn ((Equiv.curry (Fin t) ((cycle m hm).V) Bool).symm (readDiag ω) p))
      = ∏ p ∈ F, sgn (ω (Sound.diagObs (cycle m hm) t p)) := rfl
  rw [hconv, Finset.prod_biUnion hArdisj, ← Finset.prod_fiberwise F (fun p => p.1)
    (fun p => sgn (ω (Sound.diagObs (cycle m hm) t p)))]
  refine Finset.prod_congr rfl fun r _ => ?_
  rw [hArdef, Finset.prod_image]
  intro x _ y _ h
  exact Sound.diagObs_injective (cycle m hm) t h

theorem sqWit_inj_eq (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q) (S : Finset (GObs (cycle m hm) t))
    (hS : GInjectable S) :
    pushforward (sqWit hm t q) (gRestrict S)
      = pushforward (parWit (cycle m hm) t q) (gRestrict S) := by
  obtain ⟨ι, hι⟩ := hS
  refine push_eq hm q hq0 (gRestrict S) (Equiv.refl _) fun B =>
    ⟨B.image (fun p : ↥S => p.1), spread_copy hm ι ((image_val_subset hm B).trans hι),
      fun ω => ?_⟩
  rw [Finset.prod_image (val_inj_on B)]
  rfl

theorem sqWit_ai_eq (hm : 3 ≤ m) (q : ℝ) (hq0 : 0 ≤ q) {n : ℕ}
    (S : Fin n → Finset (GObs (cycle m hm) t)) (hinj : ∀ k, GInjectable (S k))
    (hai : ∀ k k', k ≠ k' → GAncestrallyIndependent (S k) (S k')) :
    pushforward (sqWit hm t q) (fun ω k => gRestrict (S k) ω)
      = pushforward (parWit (cycle m hm) t q) (fun ω k => gRestrict (S k) ω) := by
  obtain ⟨ιf, hιf⟩ : ∃ ιf : Fin n → ((cycle m hm).Edge → Fin t), ∀ k, S k ⊆ copySet (ιf k) :=
    ⟨fun k => (hinj k).choose, fun k => (hinj k).choose_spec⟩
  refine push_eq hm q hq0 _ (Sound.sigCurry S).symm fun B => ?_
  set Bf : ∀ k : Fin n, Finset ↥(S k) :=
    fun k => Finset.univ.filter (fun y : ↥(S k) => (⟨k, y⟩ : Σ k : Fin n, ↥(S k)) ∈ B)
    with hBfdef
  have hBsig : B = Finset.univ.sigma Bf := by
    ext x
    simp [hBfdef, Finset.mem_sigma]
  set A : Fin n → Finset (GObs (cycle m hm) t) :=
    fun k => (Bf k).image (fun y : ↥(S k) => y.1) with hAdef
  have hAsub : ∀ k, A k ⊆ S k := fun k => image_val_subset hm (Bf k)
  have hAcopy : ∀ k, A k ⊆ copySet (ιf k) := fun k => (hAsub k).trans (hιf k)
  have hAai : ∀ k k', k ≠ k' → Disjoint (gAncestorsOf (A k)) (gAncestorsOf (A k')) := by
    intro k k' h
    exact Finset.disjoint_of_subset_left (gAncestorsOf_mono (hAsub k))
      (Finset.disjoint_of_subset_right (gAncestorsOf_mono (hAsub k')) (hai k k' h))
  have hAdisj : ∀ k ∈ (Finset.univ : Finset (Fin n)), ∀ k' ∈ (Finset.univ : Finset (Fin n)),
      k ≠ k' → Disjoint (A k) (A k') :=
    fun k _ k' _ h => Sound.disjoint_of_gAI (hAai k k' h)
  refine ⟨Finset.univ.biUnion A, spread_family hm A ιf hAcopy hAai, fun ω => ?_⟩
  rw [Finset.prod_biUnion hAdisj, hBsig, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hAdef, Finset.prod_image (val_inj_on (Bf k))]
  rfl

end Witness

end SqWitnessAux

open CycleWitnessAux SqWitnessAux

/-! ## B2: the linear-in-`t` witnesses -/

/-- AUDIT-NOTES B2(i). With the corrected Fourier density (`m` families of `t` signs,
`f_g = ∏_i (1 + i√q s_{g,i})`, `W = Re ∏_g f_g + c ∑_g (1 − Re f_g)`, `m = 4`, `c = 5`,
positive for `tq ≤ 1/16`), the square parity target with `q = 1/(16t)` passes every AI
prescription at order `t`. This is the source of the `Ω(1/t)` square lower bound, an order of
magnitude better in `t` than the `q = 1/(4m²t²)` of `cycle_witness`. -/
theorem square_linear_witness (t : ℕ) (ht : 1 ≤ t) (q : ℝ) (hq : q = 1 / (16 * (t : ℝ))) :
    GAIFeasible squareGraph t (squareTarget q) := by
  have h4 : (3 : ℕ) ≤ 4 := by norm_num
  have ht0 : (0 : ℝ) < (t : ℝ) := by
    have : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
    linarith
  have hq0 : 0 ≤ q := by rw [hq]; positivity
  have htq : (t : ℝ) * q ≤ 1 / 16 := by
    rw [hq]; field_simp; norm_num
  have e : (cycle 4 h4).Edge ≃ Fin 4 := Fintype.equivFinOfCardEq (card_cycle_edge h4)
  change GAIFeasible (cycle 4 h4) t (cycleTarget 4 q)
  exact ⟨sqWit h4 t q, sqWit_isLaw h4 e q hq0 htq, sqWit_symmetric h4 q,
    by rw [sqWit_diag_eq h4 q hq0]; exact parWit_diag h4 q,
    fun S hS => by rw [sqWit_inj_eq h4 q hq0 S hS]; exact parWit_injectable h4 q S hS,
    fun n S hinj hai => by
      rw [sqWit_ai_eq h4 q hq0 S hinj hai]; exact parWit_ai h4 q n S hinj hai⟩

end TriangleInflation.Graph
