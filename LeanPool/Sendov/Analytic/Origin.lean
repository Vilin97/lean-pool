/-
Copyright (c) 2026 Terence Tao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
module

public import LeanPool.Sendov.Counterexample.Identities
public import LeanPool.Sendov.Analytic.Maclaurin
public import LeanPool.Sendov.Analytic.Defect
public import LeanPool.Sendov.Common.Quadratic
public import LeanPool.Sendov.Analytic.Polar

/-!
# The origin inequality: the pointwise estimate and `(tri)`

The origin argument controls `F(t) = ∏ⱼ (1 - a t qⱼ)` through its derivative,

  `F'(t) = -(n-1) a (x+iy) F(t) - a² t ∑ⱼ qⱼ² ∏_{k≠j} (1 - a t q_k)`,

whose error term is bounded by `a² t (n-1) β(t)^{(n-2)/2}`.  Integrating that against the
fundamental theorem of calculus and `F(0) = 1` gives the triangle inequality `(tri)`.  The
`J`-algebra that turns `(tri)` into `(origin-exact)` follows in a later file.

The error bound has three steps, in increasing order of depth:

* `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, the same expansion that produced the quadratic mean in the
  polar channel — this is where `x` enters;
* Cauchy–Schwarz, `(∑ b)² ≤ N ∑ b²`;
* **Maclaurin's inequality**, `∑ⱼ ∏_{k≠j} bₖ ≤ N (mean b)^{N-1}` — the one ingredient absent
  from Mathlib, proved in `Sendov.Analytic.Maclaurin`.

The blog post applies Maclaurin to `(1/(n-1)) ∑ⱼ ∏_{k≠j} |1 - a t q_k|` and then Cauchy–Schwarz;
the order is immaterial and it is done the same way here.

A note on the bookkeeping.  The quantity `∑ⱼ ∏_{k≠j} f(qⱼ)` is written as a sum over erasures
of `q`, whereas `Multiset.esymm` — which Maclaurin is stated for — is a sum over sub-multisets
of the *image* `q.map f`.  Rather than relate erasure and `map` directly, which needs `f`
injective, the two are matched through the recurrence they share.

## Main statements

* `Sendov.sumEraseProdMap_eq_esymm`: the two forms of `∑ⱼ ∏_{k≠j}` agree;
* `Sendov.sum_norm_sq_one_sub_le`: `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`;
* `Sendov.sumEraseProdMap_norm_le`: the error bound `(n-1) β(t)^{(n-2)/2}`;
* `Sendov.hasDerivAt_Fprod`: `F'(t) = -a ∑ⱼ qⱼ ∏_{k≠j} (1 - a t q_k)`;
* `Sendov.norm_deriv_add_le`: `‖F'(t) + (n-1) a (x+iy) F(t)‖ ≤ a² t (n-1) β(t)^{(n-2)/2}`;
* `Sendov.one_le_tri`: the triangle inequality `(tri)`.

The derivative is assembled from a *weighted* erasure sum `sumEraseProdC q g f = ∑ⱼ g(qⱼ)
∏_{k≠j} f(q_k)`: taking `g = id` gives `F'` itself, and the identity `1 - (1 - a t qⱼ) = a t qⱼ`
splits that into the main term `(∑ⱼ qⱼ) F(t)` plus `a t` times the case `g = (· ^ 2)`, which is
the residual actually being estimated.
-/

public section

namespace Sendov

/-! ### `∑ⱼ ∏_{k≠j}` over erasures, and `esymm` -/

open scoped Classical in
/-- `∑ⱼ ∏_{k≠j} f(sₖ)`, as a sum over erasures of `s`. -/
noncomputable def sumEraseProdMap {α : Type*} (s : Multiset α) (f : α → ℝ) : ℝ :=
  (s.map (fun j => ((s.erase j).map f).prod)).sum

open scoped Classical in
lemma sumEraseProdMap_cons {α : Type*} (v : α) (t : Multiset α) (f : α → ℝ) :
    sumEraseProdMap (v ::ₘ t) f = (t.map f).prod + f v * sumEraseProdMap t f := by
  simp only [sumEraseProdMap, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]

/-- The erasure form and `Multiset.esymm` agree, matched through their common recurrence. -/
theorem sumEraseProdMap_eq_esymm {α : Type*} : ∀ (s : Multiset α) (f : α → ℝ), s ≠ 0 →
    sumEraseProdMap s f = (s.map f).esymm ((s.map f).card - 1) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _ h; exact absurd rfl h
  | cons v t ih =>
    intro f _
    rcases eq_or_ne t 0 with rfl | ht
    · simp [sumEraseProdMap, Multiset.esymm]
    · rw [sumEraseProdMap_cons, ih f ht, Multiset.map_cons, Multiset.card_cons]
      rw [show (t.map f).card + 1 - 1 = (t.map f).card from by omega]
      rw [esymm_card_cons (f v) (t.map f) (by simpa using ht)]

/-! ### The quadratic mean -/

/-- `‖1 + s v‖² = 1 + 2 s Re v + s² ‖v‖²` for real `s`. -/
lemma norm_sq_one_add_real_mul (s : ℝ) (v : ℂ) :
    ‖1 + (s : ℂ) * v‖ ^ 2 = 1 + 2 * s * v.re + s ^ 2 * ‖v‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im]
  ring

lemma sum_norm_sq_one_sub_split (s : ℝ) (q : Multiset ℂ) :
    (q.map (fun v => ‖1 + (s : ℂ) * v‖ ^ 2)).sum
      = (q.card : ℝ) + 2 * s * ((q.map (fun v => v.re)).sum)
        + s ^ 2 * ((q.map (fun v => ‖v‖ ^ 2)).sum) := by
  induction q using Multiset.induction_on with
  | empty => simp
  | cons v t ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
    rw [ih, norm_sq_one_add_real_mul]
    push_cast
    ring

/-- `∑ⱼ ‖1 - a t qⱼ‖² ≤ (n-1) β(t)`, where `β(t) = 1 - 2 a x t + a² t²`. -/
theorem sum_norm_sq_one_sub_le {n : ℕ} {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (hn : 1 ≤ n)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    (q.map (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ ^ 2)).sum
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
  have hNcast : ((q.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hqcard]
    push_cast [Nat.cast_sub hn]
    ring
  have hcast : ∀ v : ℂ, 1 - (a : ℂ) * (t : ℂ) * v = 1 + ((-(a * t) : ℝ) : ℂ) * v := by
    intro v
    push_cast
    ring
  simp only [hcast]
  rw [sum_norm_sq_one_sub_split, hx, hNcast]
  have hsum2 := sum_norm_sq_le_card q hq1
  rw [hNcast] at hsum2
  simp only [QQ]
  nlinarith [hsum2, sq_nonneg (a * t)]

/-! ### Cauchy–Schwarz and the error bound -/

lemma sq_sum_le_card_mul_sum_sq (s : Multiset ℝ) (hs : ∀ b ∈ s, 0 ≤ b) :
    (s.sum) ^ 2 ≤ (s.card : ℝ) * (s.map (fun b => b ^ 2)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons b t ih =>
    have hb := hs b (Multiset.mem_cons_self b t)
    have ht : ∀ u ∈ t, 0 ≤ u := fun u hu => hs u (Multiset.mem_cons_of_mem hu)
    rcases eq_or_ne t 0 with rfl | ht0
    · simp
    · have hIH := ih ht
      have hcard : (0 : ℝ) < (t.card : ℕ) := by
        have := Multiset.card_pos.2 ht0
        exact_mod_cast this
      have hsum : 0 ≤ t.sum := Multiset.sum_nonneg ht
      have hQ : (0 : ℝ) ≤ (t.map (fun b => b ^ 2)).sum :=
        Multiset.sum_nonneg (by
          intro y hy
          obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
          exact sq_nonneg u)
      simp only [Multiset.sum_cons, Multiset.card_cons, Multiset.map_cons]
      push_cast
      nlinarith [hIH, sq_nonneg (t.sum - (t.card : ℝ) * b), hcard, hsum, hb, hQ]

/-- **The error bound.**  `∑ⱼ ∏_{k≠j} ‖1 - a t q_k‖ ≤ (n-1) β(t)^{(n-2)/2}`: Maclaurin's
inequality, then Cauchy–Schwarz, then the quadratic mean.  Nonnegativity of `β(t)` is not
assumed — it follows from the quadratic-mean bound, `β(t)` dominating an average of squares. -/
theorem sumEraseProdMap_norm_le {n : ℕ} (hn : 2 ≤ n) {a x t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x) :
    sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖)
      ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set f : ℂ → ℝ := fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖ with hf
  set bs : Multiset ℝ := q.map f with hbs
  have hbcard : bs.card = n - 1 := by rw [hbs, Multiset.card_map, hqcard]
  have hNcast : ((bs.card : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [hbcard]
    push_cast [Nat.cast_sub (by omega : (1 : ℕ) ≤ n)]
    ring
  have hNpos : (0 : ℝ) < (bs.card : ℕ) := by
    rw [hNcast]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hbs0 : bs ≠ 0 := by
    rw [hbs]
    simpa using hq0
  have hbnn : ∀ b ∈ bs, 0 ≤ b := by
    intro b hb
    rw [hbs] at hb
    obtain ⟨v, _, rfl⟩ := Multiset.mem_map.1 hb
    exact norm_nonneg _
  have hsumnn : 0 ≤ bs.sum := Multiset.sum_nonneg hbnn
  -- the quadratic mean
  have hsq : (bs.map (fun b => b ^ 2)).sum ≤ ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t := by
    rw [hbs, Multiset.map_map]
    exact sum_norm_sq_one_sub_le hqcard hq1 (by omega) hx
  have hβ0 : 0 ≤ QQ (a * x) (a ^ 2) t := by
    have hnn : (0 : ℝ) ≤ (bs.map (fun b => b ^ 2)).sum :=
      Multiset.sum_nonneg (by
        intro y hy
        obtain ⟨u, _, rfl⟩ := Multiset.mem_map.1 hy
        exact sq_nonneg u)
    nlinarith [hsq, hnn, hNcast, hNpos]
  -- Cauchy–Schwarz
  have hcs : (bs.sum) ^ 2 ≤ ((n : ℝ) - 1) ^ 2 * QQ (a * x) (a ^ 2) t := by
    have h := sq_sum_le_card_mul_sum_sq bs hbnn
    rw [hNcast] at h
    nlinarith [h, hsq, hNcast, hNpos]
  have hmean : bs.sum / (bs.card : ℕ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) := by
    rw [div_le_iff₀ hNpos, hNcast]
    have hsqrt : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ 2 = QQ (a * x) (a ^ 2) t :=
      Real.sq_sqrt hβ0
    have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by rw [← hNcast]; exact hNpos
    have hprodnn : (0 : ℝ) ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) * ((n : ℝ) - 1) :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn1)
    nlinarith [hcs, hsqrt, hsumnn, hprodnn, hn1]
  -- Maclaurin
  have hmac := Multiset.esymm_card_pred_le bs hbnn hbs0
  rw [sumEraseProdMap_eq_esymm q f hq0, ← hbs]
  refine hmac.trans ?_
  have hpow : (bs.sum / (bs.card : ℕ)) ^ (bs.card - 1)
      ≤ Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
    refine pow_le_pow_left₀ (by positivity) hmean _
  have hfin : Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1)
      = QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (QQ (a * x) (a ^ 2) t ^ ((1 : ℝ) / 2))
      (bs.card - 1), ← Real.rpow_mul hβ0]
    congr 1
    have hcast2 : ((bs.card - 1 : ℕ) : ℝ) = (n : ℝ) - 2 := by
      rw [hbcard]
      have h2 : n - 1 - 1 = n - 2 := by omega
      rw [h2]
      push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ n)]
      ring
    rw [hcast2]
    ring
  rw [hNcast] at *
  calc ((n : ℝ) - 1) * (bs.sum / ((n : ℝ) - 1)) ^ (bs.card - 1)
      ≤ ((n : ℝ) - 1) * Real.sqrt (QQ (a * x) (a ^ 2) t) ^ (bs.card - 1) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        rw [← hNcast] at hpow ⊢
        exact hpow
    _ = ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by rw [hfin]

/-! ### The derivative of `F(t) = ∏ⱼ (1 - a t qⱼ)` -/

open scoped Classical in
/-- `∑ⱼ g(qⱼ) ∏_{k≠j} f(q_k)`, the weighted erasure sum over `ℂ`.  Taking `g = id` gives the
derivative of a product; taking `g = (· ^ 2)` gives the residual left after the main term is
split off. -/
noncomputable def sumEraseProdC (s : Multiset ℂ) (g f : ℂ → ℂ) : ℂ :=
  (s.map (fun j => g j * ((s.erase j).map f).prod)).sum

open scoped Classical in
@[simp] lemma sumEraseProdC_zero (g f : ℂ → ℂ) : sumEraseProdC 0 g f = 0 := by
  simp [sumEraseProdC]

open scoped Classical in
lemma sumEraseProdC_cons (v : ℂ) (t : Multiset ℂ) (g f : ℂ → ℂ) :
    sumEraseProdC (v ::ₘ t) g f = g v * (t.map f).prod + f v * sumEraseProdC t g f := by
  simp only [sumEraseProdC, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head]
  congr 1
  rw [← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
  intro j hj
  rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
  ring

/-- A weighted erasure sum with unit-size weights is dominated by the unweighted one. -/
lemma norm_sumEraseProdC_le (g f : ℂ → ℂ) : ∀ (s : Multiset ℂ), (∀ v ∈ s, ‖g v‖ ≤ 1) →
    ‖sumEraseProdC s g f‖ ≤ sumEraseProdMap s (fun v => ‖f v‖) := by
  intro s
  induction s using Multiset.induction_on with
  | empty => intro _; simp [sumEraseProdMap]
  | cons v t ih =>
    intro hg
    have hv := hg v (Multiset.mem_cons_self v t)
    have ht : ∀ u ∈ t, ‖g u‖ ≤ 1 := fun u hu => hg u (Multiset.mem_cons_of_mem hu)
    rw [sumEraseProdC_cons, sumEraseProdMap_cons]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_prod_map]
    have h2 : (0 : ℝ) ≤ (t.map (fun v => ‖f v‖)).prod := prod_map_norm_nonneg t f
    nlinarith [ih ht, norm_nonneg (f v), norm_nonneg (sumEraseProdC t g f), h2, hv]

/-- `F(t) = ∏ⱼ (1 - a t qⱼ)`. -/
@[expose]
noncomputable def Fprod (a : ℝ) (q : Multiset ℂ) (t : ℝ) : ℂ :=
  (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod

@[simp] lemma Fprod_zero (a : ℝ) (q : Multiset ℂ) : Fprod a q 0 = 1 := by
  simp [Fprod]

/-- Splitting the derivative sum into its main term and its residual:
`∑ⱼ qⱼ ∏_{k≠j}(1-atq_k) = (∑ⱼ qⱼ) F(t) + a t ∑ⱼ qⱼ² ∏_{k≠j}(1-atq_k)`, since
`1 - (1 - a t qⱼ) = a t qⱼ`. -/
lemma sumEraseProdC_id_eq (a t : ℝ) : ∀ (q : Multiset ℂ),
    sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
      = q.sum * Fprod a q t
        + (a : ℂ) * (t : ℂ) * sumEraseProdC q (fun v => v ^ 2)
            (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simp [Fprod]
  | cons v r ih =>
    rw [sumEraseProdC_cons, sumEraseProdC_cons, ih, Multiset.sum_cons]
    simp only [Fprod, Multiset.map_cons, Multiset.prod_cons, id]
    ring

/-- `F'(t) = -a ∑ⱼ qⱼ ∏_{k≠j}(1 - a t q_k)`. -/
lemma hasDerivAt_Fprod (a t : ℝ) : ∀ (q : Multiset ℂ),
    HasDerivAt (Fprod a q)
      (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)) t := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    have he : Fprod a 0 = fun _ : ℝ => (1 : ℂ) := by funext s; simp [Fprod]
    have hz : -(a : ℂ) * sumEraseProdC 0 id (fun v => 1 - (a : ℂ) * (t : ℂ) * v) = 0 := by simp
    rw [he, hz]
    exact hasDerivAt_const t 1
  | cons v r ih =>
    have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    have h1 : HasDerivAt (fun s : ℝ => 1 - (a : ℂ) * (s : ℂ) * v) (-((a : ℂ) * v)) t := by
      simpa using ((h0.const_mul (a : ℂ)).mul_const v).const_sub 1
    have h2 := h1.mul ih
    have hfun : Fprod a (v ::ₘ r)
        = fun s : ℝ => (1 - (a : ℂ) * (s : ℂ) * v) * Fprod a r s := by
      funext s
      simp only [Fprod, Multiset.map_cons, Multiset.prod_cons]
    have hderiv : -(a : ℂ) * ((v : ℂ) * (r.map (fun w => 1 - (a : ℂ) * (t : ℂ) * w)).prod
          + (1 - (a : ℂ) * (t : ℂ) * v) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w))
        = -((a : ℂ) * v) * Fprod a r t
          + (1 - (a : ℂ) * (t : ℂ) * v)
              * (-(a : ℂ) * sumEraseProdC r id (fun w => 1 - (a : ℂ) * (t : ℂ) * w)) := by
      simp only [Fprod]
      ring
    rw [hfun, sumEraseProdC_cons, id_eq, hderiv]
    exact h2

/-- **The pointwise estimate.**  `‖F'(t) + (n-1) a (x+iy) F(t)‖ ≤ a² t (n-1) β(t)^{(n-2)/2}`. -/
theorem norm_deriv_add_le {n : ℕ} (hn : 2 ≤ n) {a x y t : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1)
    (ha0 : 0 ≤ a) (ht0 : 0 ≤ t)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = (((n : ℝ) - 1) : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    ‖(-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
        + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
      ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set S : ℂ := sumEraseProdC q (fun v => v ^ 2) (fun v => 1 - (a : ℂ) * (t : ℂ) * v) with hS
  have hmain : (-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v))
      + (((n : ℝ) - 1) : ℂ) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t
      = -((a : ℂ) ^ 2 * (t : ℂ)) * S := by
    rw [sumEraseProdC_id_eq, hsum, ← hS]
    ring
  rw [hmain, norm_mul]
  have hnorm : ‖-((a : ℂ) ^ 2 * (t : ℂ))‖ = a ^ 2 * t := by
    simp [abs_of_nonneg ha0, abs_of_nonneg ht0]
  rw [hnorm]
  have hSle : ‖S‖ ≤ sumEraseProdMap q (fun v => ‖1 - (a : ℂ) * (t : ℂ) * v‖) := by
    rw [hS]
    refine norm_sumEraseProdC_le _ _ q ?_
    intro v hv
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg v) (hq1 v hv)
  have hbd := sumEraseProdMap_norm_le (a := a) (x := x) (t := t) hn hqcard hq0 hq1 hx
  have hfac : (0 : ℝ) ≤ a ^ 2 * t := mul_nonneg (pow_nonneg ha0 2) ht0
  calc a ^ 2 * t * ‖S‖
      ≤ a ^ 2 * t * (((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
        mul_le_mul_of_nonneg_left (hSle.trans hbd) hfac
    _ = a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by ring

/-! ### Integrating the pointwise estimate: the triangle inequality `(tri)` -/

lemma continuous_prodC (a : ℝ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => (q.map (fun v => 1 - (a : ℂ) * (t : ℂ) * v)).prod := by
  intro q
  induction q using Multiset.induction_on with
  | empty => simpa using continuous_const
  | cons v r ih =>
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact (by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih

lemma continuous_Fprod (a : ℝ) (q : Multiset ℂ) : Continuous (Fprod a q) :=
  continuous_prodC a q

lemma continuous_sumEraseProdC (a : ℝ) (g : ℂ → ℂ) : ∀ (q : Multiset ℂ),
    Continuous fun t : ℝ => sumEraseProdC q g (fun v => 1 - (a : ℂ) * (t : ℂ) * v) := by
  intro q
  induction q using Multiset.induction_on with
  | empty =>
    simp only [sumEraseProdC_zero]
    exact continuous_const
  | cons v r ih =>
    simp only [sumEraseProdC_cons]
    exact (continuous_const.mul (continuous_prodC a r)).add
      ((by fun_prop : Continuous fun t : ℝ => 1 - (a : ℂ) * (t : ℂ) * v).mul ih)

/-- **The triangle inequality `(tri)`.**  Integrating `norm_deriv_add_le` against the
fundamental theorem of calculus, using `F(0) = 1`. -/
theorem one_le_tri {n : ℕ} (hn : 2 ≤ n) {a x y : ℝ} {q : Multiset ℂ}
    (hqcard : q.card = n - 1) (hq0 : q ≠ 0) (hq1 : ∀ v ∈ q, ‖v‖ ≤ 1) (ha0 : 0 ≤ a)
    (hx : (q.map (fun v => v.re)).sum = ((n : ℝ) - 1) * x)
    (hsum : q.sum = ((n : ℂ) - 1) * ((x : ℂ) + (y : ℂ) * Complex.I)) :
    1 ≤ ‖Fprod a q 1 + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)
            * ∫ t in (0 : ℝ)..1, Fprod a q t‖
        + a ^ 2 * ((n : ℝ) - 1)
            * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
  set c : ℂ := ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) with hc
  set D : ℝ → ℂ := fun t => -(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
    with hDdef
  have hDcont : Continuous D := by
    rw [hDdef]
    exact continuous_const.mul (continuous_sumEraseProdC a id q)
  have hFcont : Continuous (Fprod a q) := continuous_Fprod a q
  have hDint : IntervalIntegrable D MeasureTheory.volume 0 1 := hDcont.intervalIntegrable _ _
  have hFint : IntervalIntegrable (Fprod a q) MeasureTheory.volume 0 1 :=
    hFcont.intervalIntegrable _ _
  have hFTC : ∫ t in (0 : ℝ)..1, D t = Fprod a q 1 - Fprod a q 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_Fprod a t q) hDint
  -- the exact identity behind the triangle inequality
  have hG : ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)
      = (Fprod a q 1 - 1) + c * ∫ t in (0 : ℝ)..1, Fprod a q t := by
    rw [intervalIntegral.integral_add hDint (hFint.const_mul c), hFTC, Fprod_zero,
      intervalIntegral.integral_const_mul]
  have hkey : (1 : ℂ) = (Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t)
      - ∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t) := by
    rw [hG]; ring
  -- the pointwise bound, integrated
  have hexp : (0 : ℝ) ≤ ((n : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hRcont : Continuous fun t : ℝ =>
      a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) :=
    continuous_const.mul (continuous_pow_mul_QQ (a * x) (a ^ 2) 1 hexp)
  have hGnorm : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖D t + c * Fprod a q t‖
      ≤ a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by
    intro t ht
    have h := norm_deriv_add_le hn hqcard hq0 hq1 ha0 ht.1 hx hsum (t := t) (y := y)
    rw [hDdef, hc]
    calc ‖-(a : ℂ) * sumEraseProdC q id (fun v => 1 - (a : ℂ) * (t : ℂ) * v)
            + ((n : ℂ) - 1) * (a : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I) * Fprod a q t‖
        ≤ a ^ 2 * t * ((n : ℝ) - 1) * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := h
      _ = a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)) := by ring
  have hint : ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖
      ≤ a ^ 2 * ((n : ℝ) - 1)
          * ∫ t in (0 : ℝ)..1, t * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by norm_num : (0 : ℝ) ≤ 1)).trans ?_
    have hni : IntervalIntegrable (fun t : ℝ => ‖D t + c * Fprod a q t‖)
        MeasureTheory.volume 0 1 :=
      (hDcont.add (continuous_const.mul hFcont)).norm.intervalIntegrable _ _
    have hri : IntervalIntegrable (fun t : ℝ =>
        a ^ 2 * ((n : ℝ) - 1) * (t ^ 1 * QQ (a * x) (a ^ 2) t ^ (((n : ℝ) - 2) / 2)))
        MeasureTheory.volume 0 1 := hRcont.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1) hni hri hGnorm
    refine hmono.trans ?_
    rw [intervalIntegral.integral_const_mul]
    simp
  -- assemble
  have hnorm1 : ‖(1 : ℂ)‖ ≤ ‖Fprod a q 1 + c * ∫ t in (0 : ℝ)..1, Fprod a q t‖
      + ‖∫ t in (0 : ℝ)..1, (D t + c * Fprod a q t)‖ := by
    conv_lhs => rw [hkey]
    exact norm_sub_le _ _
  rw [norm_one] at hnorm1
  linarith [hnorm1, hint]

end Sendov
