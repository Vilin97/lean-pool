/-
Copyright (c) 2026 Xuanji Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuanji Li
-/

import LeanPool.Chudnovsky.SingularModuli.QuadraticPoints
import LeanPool.Chudnovsky.Basic

/-!
# Reduction of binary quadratic forms of discriminant `−163` (Phase C, Track 3)

This file provides the `decide`-heavy combinatorial inputs of `PhaseC-PLAN.md` §4.2:

* **`SL₂`-equivalence of forms** (`Equiv`), an equivalence relation, with the two
  generators `T` (shift `b ↦ b + 2an`) and `S` (swap `(a,b,c) ↦ (c,−b,a)`).
* **(C6) enumeration of reduced forms** (`reduced_disc_neg163`): the only positive-definite
  reduced form of discriminant `−163` is `(1, ±1, 41)` — proved by `nlinarith` bounding
  `a ≤ 7` followed by `interval_cases`/`omega`.  Together with the descent
  `exists_reduced_equiv` this gives `h(−163) = 1` at the level of forms.
* **(C5) the three-prime discriminant enumeration** (`three_prime_N` and its `ℤ` wrapper
  `disc_of_three_relations`): the only negative discriminant `D₀` for which
  `t² − 4m = D₀ λ²` is solvable simultaneously for `m ∈ {41, 43, 61}` is `D₀ = −163`.
  This is the arithmetic heart of the rationality argument; the trap noted in §6.6
  (`{41,43,47}` fails, `−43` survives) is what makes the choice of primes load-bearing.

The bridge from these form-level facts to the statement *"every CM point of discriminant
`−163` is `Γ`-equivalent to `τ₁₆₃`"* additionally needs the `SL₂`-action on `ℍ` matched
with `BQF.act`; that analytic bookkeeping is deferred (see the closing `TODO`).
-/

noncomputable section

namespace Chudnovsky.QF

open UpperHalfPlane

/-! ## `SL₂`-equivalence of forms -/

/-- Two forms are `SL₂(ℤ)`-equivalent when one is carried to the other by a determinant-1
`act`. -/
def Equiv (f g : BQF) : Prop :=
  ∃ p q r s : ℤ, p * s - q * r = 1 ∧ act f p q r s = g

@[refl] theorem Equiv.refl (f : BQF) : Equiv f f := ⟨1, 0, 0, 1, by ring, act_one f⟩

theorem Equiv.symm {f g : BQF} (h : Equiv f g) : Equiv g f := by
  obtain ⟨p, q, r, s, hdet, hfg⟩ := h
  exact ⟨s, -q, -r, p, by ring_nf; linarith [hdet], by rw [← hfg]; exact act_act_inv f hdet⟩

theorem Equiv.trans {f g h : BQF} (hfg : Equiv f g) (hgh : Equiv g h) : Equiv f h := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := hfg
  obtain ⟨p', q', r', s', hdet', rfl⟩ := hgh
  refine ⟨p * p' + q * r', p * q' + q * s', r * p' + s * r', r * q' + s * s', ?_,
    (act_act f p q r s p' q' r' s').symm⟩
  nlinarith [hdet, hdet']

/-- The `T`-generator: shift `(a, b, c) ↦ (a, b + 2an, a n² + b n + c)`; preserves the form
class and (obviously) the discriminant. -/
theorem Equiv.T (f : BQF) (n : ℤ) : Equiv f (act f 1 n 0 1) := ⟨1, n, 0, 1, by ring, rfl⟩

lemma act_T_a (f : BQF) (n : ℤ) : (act f 1 n 0 1).a = f.a := by simp
lemma act_T_b (f : BQF) (n : ℤ) : (act f 1 n 0 1).b = f.b + 2 * f.a * n := by
  simp only [act_b]; ring
lemma act_T_c (f : BQF) (n : ℤ) : (act f 1 n 0 1).c = f.a * n ^ 2 + f.b * n + f.c := by
  simp only [act_c]; ring

/-- The `S`-generator: swap `(a, b, c) ↦ (c, −b, a)`. -/
theorem Equiv.S (f : BQF) : Equiv f (act f 0 (-1) 1 0) := ⟨0, -1, 1, 0, by ring, rfl⟩

lemma act_S_a (f : BQF) : (act f 0 (-1) 1 0).a = f.c := by simp
lemma act_S_b (f : BQF) : (act f 0 (-1) 1 0).b = -f.b := by simp only [act_b]; ring
lemma act_S_c (f : BQF) : (act f 0 (-1) 1 0).c = f.a := by simp only [act_c]; ring

/-- Equivalent forms have equal discriminant. -/
theorem Equiv.disc_eq {f g : BQF} (h : Equiv f g) : disc f = disc g := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  rw [disc_act, hdet]; ring

/-- Equivalence preserves primitivity. -/
theorem Equiv.isPrimitive {f g : BQF} (h : Equiv f g) (hf : IsPrimitive f) : IsPrimitive g := by
  obtain ⟨p, q, r, s, hdet, rfl⟩ := h
  exact hf.act hdet

/-! ## Reduced forms of discriminant `−163` -/

/-- A form is *reduced* when `−a ≤ b ≤ a ≤ c` (the loose convention; both `(1,1,41)` and
`(1,−1,41)` count, and they are `T`-equivalent). -/
def IsReduced (f : BQF) : Prop := -f.a ≤ f.b ∧ f.b ≤ f.a ∧ f.a ≤ f.c

/-- **(C6) Enumeration.** The only positive-definite reduced forms of discriminant `−163`
are `(1, −1, 41)` and `(1, 1, 41)`. -/
theorem reduced_disc_neg163 {f : BQF} (ha : 0 < f.a) (hred : IsReduced f)
    (hdisc : disc f = -163) :
    f = ⟨1, -1, 41⟩ ∨ f = ⟨1, 1, 41⟩ := by
  obtain ⟨hab, hba, hac⟩ := hred
  simp only [disc] at hdisc
  obtain ⟨a, b, c⟩ := f
  simp only at ha hab hba hac hdisc ⊢
  have hb2 : b ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hba) (by linarith : (0 : ℤ) ≤ a + b)]
  have hac2 : a ^ 2 ≤ a * c := by nlinarith
  have ha7 : a ≤ 7 := by nlinarith [hb2, hac2, hdisc, sq_nonneg (a - 8)]
  simp only [BQF.mk.injEq]
  interval_cases a <;> interval_cases b <;> omega

/-! ## The reduction descent: every positive-definite form is equivalent to a reduced one -/

/-- Descent step + strong induction on the leading coefficient: `T`-shift `b` into
`(−a, a]`, then `S`-swap whenever `a > c` (which strictly lowers `a`). -/
private theorem exists_reduced_aux : ∀ (n : ℕ) (f : BQF), IsPosDef f → f.a.toNat = n →
    ∃ g, Equiv f g ∧ IsPosDef g ∧ IsReduced g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf hn
    have ha : 0 < f.a := hf.1
    set nsh : ℤ := -((f.b + f.a) / (2 * f.a)) with hnsh
    set f1 : BQF := act f 1 nsh 0 1 with hf1
    have hf1a : f1.a = f.a := by rw [hf1, act_T_a]
    have hEqf1 : Equiv f f1 := Equiv.T f nsh
    have hf1pd : IsPosDef f1 :=
      ⟨by rw [hf1a]; exact ha, by rw [← hEqf1.disc_eq]; exact hf.2⟩
    -- `T`-shift places `f1.b` in `[−a, a)`
    have ha2 : 0 < 2 * f.a := by linarith
    have hmod : f1.b = (f.b + f.a) % (2 * f.a) - f.a := by
      rw [hf1, act_T_b, hnsh]
      have := Int.emod_add_mul_ediv (f.b + f.a) (2 * f.a)
      linarith [this]
    have hmod0 : 0 ≤ (f.b + f.a) % (2 * f.a) := Int.emod_nonneg _ ha2.ne'
    have hmodlt : (f.b + f.a) % (2 * f.a) < 2 * f.a := Int.emod_lt_of_pos _ ha2
    have hblo : -f1.a ≤ f1.b := by rw [hf1a, hmod]; linarith
    have hbhi : f1.b ≤ f1.a := by rw [hf1a, hmod]; linarith
    by_cases hcase : f1.a ≤ f1.c
    · exact ⟨f1, hEqf1, hf1pd, hblo, hbhi, hcase⟩
    · push Not at hcase
      set f2 : BQF := act f1 0 (-1) 1 0 with hf2
      have hf2a : f2.a = f1.c := by rw [hf2, act_S_a]
      have hEqf2 : Equiv f1 f2 := Equiv.S f1
      have hf2pd : IsPosDef f2 :=
        ⟨by rw [hf2a]; exact hf1pd.c_pos, by rw [← hEqf2.disc_eq]; exact hf1pd.2⟩
      have hlt : f2.a.toNat < n := by
        have h1 : f1.c < f1.a := hcase
        have h2 : 0 < f1.c := hf1pd.c_pos
        rw [hf2a]; omega
      obtain ⟨g, hg1, hg2, hg3⟩ := ih f2.a.toNat hlt f2 hf2pd rfl
      exact ⟨g, (hEqf1.trans hEqf2).trans hg1, hg2, hg3⟩

/-- **Existence of a reduced representative.** Every positive-definite form is
`SL₂(ℤ)`-equivalent to a reduced positive-definite form. -/
theorem exists_reduced_equiv (f : BQF) (hf : IsPosDef f) :
    ∃ g, Equiv f g ∧ IsPosDef g ∧ IsReduced g :=
  exists_reduced_aux f.a.toNat f hf rfl

/-- **(C6), form level.** Every positive-definite form of discriminant `−163` is
`SL₂(ℤ)`-equivalent to `(1, −1, 41)` or `(1, 1, 41)` — the two (`T`-related) presentations
of the class of `τ₁₆₃`.  This is `h(−163) = 1` for forms. -/
theorem equiv_of_disc_neg163 {f : BQF} (hpd : IsPosDef f) (hdisc : disc f = -163) :
    Equiv f ⟨1, -1, 41⟩ ∨ Equiv f ⟨1, 1, 41⟩ := by
  obtain ⟨g, hEq, hgpd, hgred⟩ := exists_reduced_equiv f hpd
  have hgd : disc g = -163 := by rw [← hEq.disc_eq]; exact hdisc
  rcases reduced_disc_neg163 hgpd.1 hgred hgd with h | h
  · left; rw [← h]; exact hEq
  · right; rw [← h]; exact hEq

/-! ## (C5) The three-prime discriminant enumeration

For an integer matrix of determinant `m` fixing a CM point of primitive discriminant `D₀`,
the trace `t` and the multiplier `λ` satisfy `t² − 4m = D₀ λ²` (`= disc · λ²`, see
`QuadraticPoints.det_of_fixes`).  The following finite computation shows that
`D₀ = −163` is the *only* negative discriminant solvable for all of `m ∈ {41, 43, 61}`. -/

/-- Whether `D₀ = −(d)` is representable as `t² − 4m = D₀ λ²` within the (generous) search
box `|t| ≤ 15`, `1 ≤ λ ≤ 9` that contains every genuine solution
(`|t|² < 4m ≤ 244` and `|D₀| ≥ 3 ⇒ λ² ≤ 4m/3 < 82`). Phrased over `ℕ` for a fast kernel
`decide`. -/
def reprN (m d : ℕ) : Bool :=
  decide (∃ t ∈ Finset.range 16, ∃ l ∈ Finset.Icc 1 9, 4 * m - t ^ 2 = d * l ^ 2 ∧ t ^ 2 ≤ 4 * m)

/-- **(C5), computational core.** The only `d ∈ [1, 244]` simultaneously representable at
`m = 41, 43, 61` is `d = 163` (i.e. `D₀ = −163`).  The `{41,43,47}` trap of §6.6 is exactly
that `d = 43` would also survive there; here it does not.  Proved in four range chunks so each
`decide` stays within the default recursion depth. -/
theorem three_prime_N : ∀ d ∈ Finset.Icc 1 244,
    reprN 41 d = true → reprN 43 d = true → reprN 61 d = true → d = 163 := by
  have c1 : ∀ d ∈ Finset.Icc 1 61,
      reprN 41 d = true → reprN 43 d = true → reprN 61 d = true → d = 163 := by decide
  have c2 : ∀ d ∈ Finset.Icc 62 122,
      reprN 41 d = true → reprN 43 d = true → reprN 61 d = true → d = 163 := by decide
  have c3 : ∀ d ∈ Finset.Icc 123 183,
      reprN 41 d = true → reprN 43 d = true → reprN 61 d = true → d = 163 := by decide
  have c4 : ∀ d ∈ Finset.Icc 184 244,
      reprN 41 d = true → reprN 43 d = true → reprN 61 d = true → d = 163 := by decide
  intro d hd
  simp only [Finset.mem_Icc] at hd
  by_cases h1 : d ≤ 61
  · exact c1 d (Finset.mem_Icc.mpr ⟨hd.1, h1⟩)
  by_cases h2 : d ≤ 122
  · exact c2 d (Finset.mem_Icc.mpr ⟨by omega, h2⟩)
  by_cases h3 : d ≤ 183
  · exact c3 d (Finset.mem_Icc.mpr ⟨by omega, h3⟩)
  · exact c4 d (Finset.mem_Icc.mpr ⟨by omega, hd.2⟩)

/-- Casting bridge: a genuine integer solution `t² − 4m = D₀ λ²` (with `m ≤ 61`, `D₀ ≤ −3`,
`λ ≠ 0`) witnesses `reprN m (−D₀)`. -/
private lemma reprN_of_relation {m : ℕ} (hm : m ≤ 61) {D0 t l : ℤ} (hD3 : D0 ≤ -3)
    (hl : l ≠ 0) (h : t ^ 2 - 4 * (m : ℤ) = D0 * l ^ 2) : reprN m (-D0).toNat = true := by
  have hl2 : (1 : ℤ) ≤ l ^ 2 := by
    rcases lt_or_gt_of_ne hl with h' | h' <;> nlinarith
  have hmD0 : (0 : ℤ) < -D0 := by linarith
  have hmle : (m : ℤ) ≤ 61 := by exact_mod_cast hm
  have hkey : 4 * (m : ℤ) - t ^ 2 = (-D0) * l ^ 2 := by linarith
  have htle : t ^ 2 ≤ 4 * (m : ℤ) - 3 := by nlinarith [hkey, hmD0, hl2]
  set tN := t.natAbs with htN
  set lN := l.natAbs with hlN
  have htNsq : (tN : ℤ) ^ 2 = t ^ 2 := by rw [htN]; exact Int.natAbs_sq t
  have hlNsq : (lN : ℤ) ^ 2 = l ^ 2 := by rw [hlN]; exact Int.natAbs_sq l
  have hDtoNat : ((-D0).toNat : ℤ) = -D0 := Int.toNat_of_nonneg hmD0.le
  -- `tN < 16` from `t² ≤ 4m − 3 ≤ 241 < 256`
  have htNle : tN < 16 := by
    by_contra hc
    push Not at hc
    have h16 : (16 : ℤ) ≤ (tN : ℤ) := by exact_mod_cast hc
    have : (256 : ℤ) ≤ t ^ 2 := by rw [← htNsq]; nlinarith
    linarith [htle, hmle]
  -- `1 ≤ lN ≤ 9` from `l ≠ 0` and `3·l² ≤ (−D₀)·l² = 4m − t² ≤ 244`
  have hlN1 : 1 ≤ lN := by
    rw [hlN]; exact Int.natAbs_pos.mpr hl
  have hlN9 : lN ≤ 9 := by
    by_contra hc
    push Not at hc
    have h10 : (10 : ℤ) ≤ (lN : ℤ) := by exact_mod_cast hc
    have hl100 : (100 : ℤ) ≤ l ^ 2 := by rw [← hlNsq]; nlinarith
    nlinarith [hkey, hmle, sq_nonneg t]
  -- the ℕ equation
  have htNsq4m : tN ^ 2 ≤ 4 * m := by
    have : (tN : ℤ) ^ 2 ≤ 4 * (m : ℤ) := by rw [htNsq]; linarith
    exact_mod_cast this
  have heq : 4 * m - tN ^ 2 = (-D0).toNat * lN ^ 2 := by
    have hz : ((4 * m - tN ^ 2 : ℕ) : ℤ) = (((-D0).toNat * lN ^ 2 : ℕ) : ℤ) := by
      rw [Nat.cast_sub htNsq4m]
      push_cast
      rw [htNsq, hlNsq, hDtoNat]
      linarith [hkey]
    exact_mod_cast hz
  unfold reprN
  rw [decide_eq_true_eq]
  exact ⟨tN, Finset.mem_range.mpr htNle, lN, Finset.mem_Icc.mpr ⟨hlN1, hlN9⟩, heq, htNsq4m⟩

/-- **(C5), integer form.** The wrapper consumed by the rationality argument: if a common
CM point of primitive discriminant `D₀ ≤ −3` carries integral matrices of determinants
`41, 43, 61` (trace `tᵢ`, non-zero multiplier `λᵢ`, so `tᵢ² − 4mᵢ = D₀ λᵢ²`), then
`D₀ = −163`. -/
theorem disc_of_three_relations {D0 : ℤ} (hD3 : D0 ≤ -3)
    {t1 l1 t2 l2 t3 l3 : ℤ} (hl1 : l1 ≠ 0) (hl2 : l2 ≠ 0) (hl3 : l3 ≠ 0)
    (h1 : t1 ^ 2 - 4 * 41 = D0 * l1 ^ 2) (h2 : t2 ^ 2 - 4 * 43 = D0 * l2 ^ 2)
    (h3 : t3 ^ 2 - 4 * 61 = D0 * l3 ^ 2) : D0 = -163 := by
  have e1 := reprN_of_relation (m := 41) (by norm_num) hD3 hl1 (by exact_mod_cast h1)
  have e2 := reprN_of_relation (m := 43) (by norm_num) hD3 hl2 (by exact_mod_cast h2)
  have e3 := reprN_of_relation (m := 61) (by norm_num) hD3 hl3 (by exact_mod_cast h3)
  have hl1sq : (1 : ℤ) ≤ l1 ^ 2 := by rcases lt_or_gt_of_ne hl1 with h' | h' <;> nlinarith
  have hub : (-D0) ≤ 164 := by nlinarith [h1, hl1sq, sq_nonneg t1]
  have hmem : (-D0).toNat ∈ Finset.Icc 1 244 := by
    rw [Finset.mem_Icc]; omega
  have := three_prime_N (-D0).toNat hmem e1 e2 e3
  omega

/-! ## The bridge to `ℍ`: CM points of discriminant `−163` are `Γ`-equivalent to `τ₁₆₃`

The `SL₂(ℤ)`-action on forms `BQF.act` is matched to the Möbius action on `ℍ`: if
`act f p q r s = g` (determinant 1) and `τ` is a root of `f`, then the point `N • τ` with
`N = ![![s,−q],![−r,p]] ∈ SL₂(ℤ)` (the inverse matrix) is a root of `g`. Combined with the
form-level classification `equiv_of_disc_neg163` and the CM-point uniqueness `root_unique`,
this yields the analytic statement `PhaseC-PLAN.md` (C6) needs. -/

open UpperHalfPlane in
/-- **Root transport.** If `act f p q r s = g` with `p s − q r = 1` and `τ` is a root of `f`,
then `N • τ` is a root of `g` for the inverse matrix `N = ![![s,−q],![−r,p]]`. -/
theorem isRoot_smul {f g : BQF} {p q r s : ℤ} (hdet : p * s - q * r = 1)
    (hg : act f p q r s = g) {τ : ℍ} (hroot : IsRoot f τ) :
    ∃ N : Matrix.SpecialLinearGroup (Fin 2) ℤ, IsRoot g (N • τ) := by
  set N : Matrix.SpecialLinearGroup (Fin 2) ℤ := ⟨!![s, -q; -r, p], by
    simp only [Matrix.det_fin_two_of]; linear_combination hdet⟩ with hNdef
  refine ⟨N, ?_⟩
  set X : ℂ := (s : ℂ) * (τ : ℂ) + (-(q : ℂ)) with hX
  set Y : ℂ := (-(r : ℂ)) * (τ : ℂ) + (p : ℂ) with hY
  have hcoe : (↑(N • τ) : ℂ) = X / Y := by
    rw [UpperHalfPlane.specialLinearGroup_apply, hX, hY]
    simp [hNdef]
  have hYne : Y ≠ 0 := by
    intro h0
    have hlin : ((-r : ℤ) : ℂ) * (τ : ℂ) + ((p : ℤ) : ℂ) = 0 := by rw [← h0, hY]; push_cast; ring
    obtain ⟨hr0, hp0⟩ := int_lin_eq_zero τ hlin
    have hr : r = 0 := by omega
    rw [hr, hp0] at hdet; simp at hdet
  have hform : (g.a : ℂ) * X ^ 2 + (g.b : ℂ) * X * Y + (g.c : ℂ) * Y ^ 2 = 0 := by
    rw [← hg]
    simp only [act_a, act_b, act_c, hX, hY, IsRoot] at hroot ⊢
    push_cast
    linear_combination ((p : ℂ) * s - q * r) ^ 2 * hroot
  simp only [IsRoot, hcoe]
  field_simp
  linear_combination hform

/-- `τ₁₆₃` is the root of the reduced form `(1, −1, 41)` (`41 − τ + τ² = 0`). -/
theorem isRoot_τ₁₆₃ : IsRoot ⟨1, -1, 41⟩ Chudnovsky.τ₁₆₃ := by
  simp only [IsRoot]
  have hre : Chudnovsky.τ₁₆₃.re = 1 / 2 := rfl
  have him : Chudnovsky.τ₁₆₃.im = Real.sqrt 163 / 2 := rfl
  have hτ : (Chudnovsky.τ₁₆₃ : ℂ)
      = ((1 / 2 : ℝ) : ℂ) + ((Real.sqrt 163 / 2 : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre, him]
  have h163 : ((Real.sqrt 163 : ℝ) : ℂ) ^ 2 = 163 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [hτ]; push_cast
  linear_combination (Complex.I ^ 2 / 4) * h163 + (163 / 4) * Complex.I_sq

private lemma posdef_1m141 : IsPosDef ⟨1, -1, 41⟩ := ⟨by norm_num, by norm_num [disc]⟩

/-- **(C6), analytic form.** Every CM point of a positive-definite form of discriminant
`−163` is `SL₂(ℤ)`-equivalent to `τ₁₆₃`. -/
theorem cm_disc_neg163_smul_eq_τ₁₆₃ {f : BQF} (hpd : IsPosDef f) (hdisc : disc f = -163)
    {τ : ℍ} (hroot : IsRoot f τ) :
    ∃ M : Matrix.SpecialLinearGroup (Fin 2) ℤ, M • τ = Chudnovsky.τ₁₆₃ := by
  rcases equiv_of_disc_neg163 hpd hdisc with ⟨p, q, r, s, hdet, hact⟩ | ⟨p, q, r, s, hdet, hact⟩
  · obtain ⟨N, hN⟩ := isRoot_smul hdet hact hroot
    exact ⟨N, root_unique posdef_1m141 hN isRoot_τ₁₆₃⟩
  · obtain ⟨N, hN⟩ := isRoot_smul hdet hact hroot
    have hTact : act (⟨1, 1, 41⟩ : BQF) 1 (-1) 0 1 = ⟨1, -1, 41⟩ := by decide
    obtain ⟨N', hN'⟩ := isRoot_smul (by ring : (1 : ℤ) * 1 - (-1) * 0 = 1) hTact hN
    refine ⟨N' * N, ?_⟩
    rw [mul_smul]
    exact root_unique posdef_1m141 hN' isRoot_τ₁₆₃

end Chudnovsky.QF
