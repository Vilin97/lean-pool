/-
Copyright (c) 2026 William Blair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Blair
-/

import LeanPool.InflationTermination.TriangleInflation.Defs

/-!
# The Finner inequality and the explicit violation

Statements for paper Section 5.2 (`sec:incompat`): Lemma 5.7 (`lem:finner`), Lemma 5.8
(`lem:violation`), and the incompatibility half of Proposition 5.12 (`prop:Rp`). Proofs are
deferred.

This file also collects the basic normalization facts about the weight functions of
`Defs.lean`, which the later files use.
-/

namespace TriangleInflation

open Finset

noncomputable
section

/-! ## Basic normalization facts -/

/-- `Bern(r)` is nonnegative when `r ∈ [0,1]`. -/
private lemma bern_nonneg {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : ∀ b, 0 ≤ bern r b := by
  intro b; cases b <;> simp [bern] <;> linarith

/-- `Bern(r)` is a law when `r ∈ [0,1]`. -/
theorem bern_isLaw {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : IsLaw (bern r) := by
  refine ⟨bern_nonneg h0 h1, ?_⟩
  simp [bern]

/-- A product of per-coordinate laws is a law. -/
theorem prodLaw_isLaw {ι : Type*} [Fintype ι] [DecidableEq ι] {w : ι → Bool → ℝ} (hw : ∀ i, IsLaw (w i)) :
    IsLaw (prodLaw w) := by
  refine ⟨fun x => Finset.prod_nonneg fun i _ => (hw i).1 _, ?_⟩
  have key : (∏ i, ∑ b : Bool, w i b) = ∑ x : ι → Bool, prodLaw w x := by
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  rw [← key]
  have hb : ∀ i, w i true + w i false = 1 := by
    intro i
    have := (hw i).2
    rwa [Fintype.sum_bool] at this
  simp [hb]

/-- A pushforward of a law is a law. -/
theorem pushforward_isLaw {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    {w : α → ℝ} (hw : IsLaw w) (F : α → β) : IsLaw (pushforward w F) := by
  refine ⟨fun b => Finset.sum_nonneg fun a _ => ?_, ?_⟩
  · by_cases hab : F a = b <;> simp [hab, hw.1 a]
  · simp only [pushforward]
    rw [Finset.sum_comm]
    simpa using hw.2

/-- `Q(ε,r)` is a law for `ε, r ∈ [0,1]` (paper equation (eq:Q)). -/
theorem Q_isLaw {ε r : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    IsLaw (Q ε r) := by
  refine ⟨fun w => ?_, ?_⟩
  · have hb := bern_nonneg hr0 hr1
    have hite : (0:ℝ) ≤ (if w = (false, false, false) then (1:ℝ) else 0) := by
      split <;> norm_num
    exact add_nonneg (mul_nonneg hε0 hite)
      (mul_nonneg (by linarith) (mul_nonneg (mul_nonneg (hb _) (hb _)) (hb _)))
  · simp only [Q, bern, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    ring

/-- `R_p` is a law for `p ∈ [0,1]` (paper Proposition 5.12). -/
theorem Rlaw_isLaw {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : IsLaw (Rlaw p) := by
  refine ⟨fun w => ?_, ?_⟩
  · have h1' : (0:ℝ) ≤ 1 - p := by linarith
    refine add_nonneg (mul_nonneg h1' ?_) (mul_nonneg h0 ?_) <;> (split <;> norm_num)
  · simp only [Rlaw, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

/-- The defect-cube law is a law when `ε, s ∈ [0,1]` (paper Section 5.1). -/
theorem defectLaw_isLaw {t : ℕ} {ε s : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : IsLaw (defectLaw t ε s) := by
  refine pushforward_isLaw (prodLaw_isLaw ?_) outputsOf
  intro v
  cases v with
  | inl _ => exact bern_isLaw hε0 hε1
  | inr _ => exact bern_isLaw hs0 hs1

/-! ## The Finner inequality -/

/-- Cauchy–Schwarz for a finite sum with nonnegative weights. -/
private lemma weighted_cauchy_schwarz {ι : Type*} (s : Finset ι) (w u v : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * (u i * v i)) ^ 2
      ≤ (∑ i ∈ s, w i * u i ^ 2) * (∑ i ∈ s, w i * v i ^ 2) := by
  have key := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * u i)
    (fun i => Real.sqrt (w i) * v i)
  have e0 : ∀ i ∈ s, Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i) = w i * (u i * v i) := by
    intro i hi
    have hs : Real.sqrt (w i) * Real.sqrt (w i) = w i := Real.mul_self_sqrt (hw i hi)
    calc Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (u i * v i) := by ring
      _ = w i * (u i * v i) := by rw [hs]
  have e1 : ∀ i ∈ s, (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have e2 : ∀ i ∈ s, (Real.sqrt (w i) * v i) ^ 2 = w i * v i ^ 2 := by
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [Finset.sum_congr rfl e0, Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at key
  exact key

/-- The response mass of the outcome `0`. -/
private lemma respMass_false (q : ℝ) : respMass q false = q := rfl

/-- The response mass of the outcome `1`. -/
private lemma respMass_true (q : ℝ) : respMass q true = 1 - q := rfl

/-- The analytic core of Finner's inequality for the triangle: with source weights
`μX, μY, μZ` and response probabilities `f, g, h` taking values in `[0,1]`, the all-zero atom
is dominated by the geometric mean of the three single-party marginals.

Cauchy–Schwarz in `y`, then Cauchy–Schwarz in the independent pair `(x,z)` (with the constant
function as one factor), then `f ≤ 1`, `g² ≤ g`, `h² ≤ h`. -/
private lemma finner_core {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    (μX : X → ℝ) (μY : Y → ℝ) (μZ : Z → ℝ) (f : X × Z → ℝ) (g : X × Y → ℝ) (h : Z × Y → ℝ)
    (hX0 : ∀ x, 0 ≤ μX x) (hY0 : ∀ y, 0 ≤ μY y) (hZ0 : ∀ z, 0 ≤ μZ z)
    (hf : ∀ p, 0 ≤ f p ∧ f p ≤ 1) (hg : ∀ p, 0 ≤ g p ∧ g p ≤ 1) (hh : ∀ p, 0 ≤ h p ∧ h p ≤ 1) :
    (∑ p : X × Z, μX p.1 * μZ p.2 * f p * ∑ y, μY y * (g (p.1, y) * h (p.2, y))) ^ 2
      ≤ (∑ p : X × Z, μX p.1 * μZ p.2 * f p)
          * (∑ q : X × Y, μX q.1 * μY q.2 * g q)
          * (∑ q : Z × Y, μZ q.1 * μY q.2 * h q) := by
  have hA0 : ∀ p : X × Z, 0 ≤ μX p.1 * μZ p.2 * f p := fun p =>
    mul_nonneg (mul_nonneg (hX0 _) (hZ0 _)) (hf p).1
  -- Cauchy–Schwarz in the independent pair `(x,z)`, against the constant function `1`.
  have cs2 := weighted_cauchy_schwarz (Finset.univ : Finset (X × Z))
    (fun p => μX p.1 * μZ p.2 * f p) (fun _ => 1)
    (fun p => ∑ y, μY y * (g (p.1, y) * h (p.2, y))) (fun p _ => hA0 p)
  simp only [one_mul, one_pow, mul_one] at cs2
  refine le_trans cs2 ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun p _ => hA0 p)
  -- Pointwise: Cauchy–Schwarz in `y`, then `g² ≤ g`, `h² ≤ h` and `f ≤ 1`.
  have key : ∀ p : X × Z,
      μX p.1 * μZ p.2 * f p * (∑ y, μY y * (g (p.1, y) * h (p.2, y))) ^ 2
        ≤ (μX p.1 * ∑ y, μY y * g (p.1, y)) * (μZ p.2 * ∑ y, μY y * h (p.2, y)) := by
    intro p
    have hGh0 : 0 ≤ ∑ y, μY y * g (p.1, y) :=
      Finset.sum_nonneg fun y _ => mul_nonneg (hY0 y) (hg _).1
    have hHh0 : 0 ≤ ∑ y, μY y * h (p.2, y) :=
      Finset.sum_nonneg fun y _ => mul_nonneg (hY0 y) (hh _).1
    have hK2 : (∑ y, μY y * (g (p.1, y) * h (p.2, y))) ^ 2
        ≤ (∑ y, μY y * g (p.1, y)) * (∑ y, μY y * h (p.2, y)) := by
      have cs := weighted_cauchy_schwarz (Finset.univ : Finset Y) μY
        (fun y => g (p.1, y)) (fun y => h (p.2, y)) (fun y _ => hY0 y)
      refine le_trans cs (mul_le_mul ?_ ?_ ?_ hGh0)
      · exact Finset.sum_le_sum fun y _ => by
          nlinarith [mul_nonneg (hY0 y)
            (mul_nonneg (hg (p.1, y)).1 (sub_nonneg.2 (hg (p.1, y)).2))]
      · exact Finset.sum_le_sum fun y _ => by
          nlinarith [mul_nonneg (hY0 y)
            (mul_nonneg (hh (p.2, y)).1 (sub_nonneg.2 (hh (p.2, y)).2))]
      · exact Finset.sum_nonneg fun y _ => mul_nonneg (hY0 y) (sq_nonneg _)
    have hAle : μX p.1 * μZ p.2 * f p ≤ μX p.1 * μZ p.2 := by
      nlinarith [mul_nonneg (hX0 p.1) (hZ0 p.2), (hf p).1, (hf p).2]
    calc μX p.1 * μZ p.2 * f p * (∑ y, μY y * (g (p.1, y) * h (p.2, y))) ^ 2
        ≤ μX p.1 * μZ p.2 * f p
            * ((∑ y, μY y * g (p.1, y)) * (∑ y, μY y * h (p.2, y))) :=
          mul_le_mul_of_nonneg_left hK2 (hA0 p)
      _ ≤ μX p.1 * μZ p.2 * ((∑ y, μY y * g (p.1, y)) * (∑ y, μY y * h (p.2, y))) :=
          mul_le_mul_of_nonneg_right hAle (mul_nonneg hGh0 hHh0)
      _ = (μX p.1 * ∑ y, μY y * g (p.1, y)) * (μZ p.2 * ∑ y, μY y * h (p.2, y)) := by ring
  have eG : ∑ q : X × Y, μX q.1 * μY q.2 * g q = ∑ x, μX x * ∑ y, μY y * g (x, y) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have eH : ∑ q : Z × Y, μZ q.1 * μY q.2 * h q = ∑ z, μZ z * ∑ y, μY y * h (z, y) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  calc ∑ p : X × Z, μX p.1 * μZ p.2 * f p * (∑ y, μY y * (g (p.1, y) * h (p.2, y))) ^ 2
      ≤ ∑ p : X × Z, (μX p.1 * ∑ y, μY y * g (p.1, y)) * (μZ p.2 * ∑ y, μY y * h (p.2, y)) :=
        Finset.sum_le_sum fun p _ => key p
    _ = (∑ q : X × Y, μX q.1 * μY q.2 * g q) * (∑ q : Z × Y, μZ q.1 * μY q.2 * h q) := by
        rw [eG, eH, Fintype.sum_prod_type, Finset.sum_mul_sum]

/-- Multiplying a constant by a normalized weight function. -/
private lemma sum_weight_mul {ι : Type*} [Fintype ι] {μ : ι → ℝ} (hμ : ∑ i, μ i = 1) (c : ℝ) :
    ∑ i, μ i * c = c := by
  rw [← Finset.sum_mul, hμ, one_mul]

/-- Paper Lemma 5.7 (`lem:finner`), the event form of Finner's inequality for the triangle:
every triangle-compatible law satisfies `P(000)² ≤ P_A(0) P_B(0) P_C(0)`.

Formalization boundary: `TriangleCompatible` uses finite latent alphabets (see the header of
`Defs.lean`); the paper's proof uses neither finiteness of the latent alphabets nor
determinism of the responses, so the statement here is the finite-latent instance of it. -/
theorem finner_of_compatible {P : ThreeBit → ℝ} (h : TriangleCompatible P) :
    atom000 P ^ 2 ≤ margA P * margB P * margC P := by
  obtain ⟨M, ⟨hX, hY, hZ, hf, hg, hh⟩, rfl⟩ := h
  -- `P(000)`, with the response masses at `0` read off.
  have hatom : atom000 M.law
      = ∑ p : M.X × M.Z, M.μX p.1 * M.μZ p.2 * M.f p
          * ∑ y, M.μY y * (M.g (p.1, y) * M.h (p.2, y)) := by
    rw [Fintype.sum_prod_type]
    simp only [atom000, TriangleModel.law, respMass_false]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  -- The three single-party marginals, after summing out the two unconstrained bits.
  have hmA : margA M.law = ∑ p : M.X × M.Z, M.μX p.1 * M.μZ p.2 * M.f p := by
    rw [Fintype.sum_prod_type]
    have e : margA M.law = ∑ x, ∑ y, ∑ z, M.μX x * M.μY y * M.μZ z * M.f (x, z) := by
      simp only [margA, TriangleModel.law, Fintype.sum_bool, respMass_false, respMass_true,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => by ring
    rw [e]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    calc ∑ y, M.μX x * M.μY y * M.μZ z * M.f (x, z)
        = ∑ y, M.μY y * (M.μX x * M.μZ z * M.f (x, z)) :=
          Finset.sum_congr rfl fun y _ => by ring
      _ = M.μX x * M.μZ z * M.f (x, z) := sum_weight_mul hY.2 _
  have hmB : margB M.law = ∑ q : M.X × M.Y, M.μX q.1 * M.μY q.2 * M.g q := by
    rw [Fintype.sum_prod_type]
    have e : margB M.law = ∑ x, ∑ y, ∑ z, M.μX x * M.μY y * M.μZ z * M.g (x, y) := by
      simp only [margB, TriangleModel.law, Fintype.sum_bool, respMass_false, respMass_true,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => by ring
    rw [e]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    calc ∑ z, M.μX x * M.μY y * M.μZ z * M.g (x, y)
        = ∑ z, M.μZ z * (M.μX x * M.μY y * M.g (x, y)) :=
          Finset.sum_congr rfl fun z _ => by ring
      _ = M.μX x * M.μY y * M.g (x, y) := sum_weight_mul hZ.2 _
  have hmC : margC M.law = ∑ q : M.Z × M.Y, M.μZ q.1 * M.μY q.2 * M.h q := by
    rw [Fintype.sum_prod_type]
    have e : margC M.law = ∑ x, ∑ y, ∑ z, M.μX x * M.μY y * M.μZ z * M.h (z, y) := by
      simp only [margC, TriangleModel.law, Fintype.sum_bool, respMass_false, respMass_true,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
        Finset.sum_congr rfl fun z _ => by ring
    rw [e]
    calc ∑ x, ∑ y, ∑ z, M.μX x * M.μY y * M.μZ z * M.h (z, y)
        = ∑ x, M.μX x * ∑ y, ∑ z, M.μY y * M.μZ z * M.h (z, y) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ y, ∑ z, M.μY y * M.μZ z * M.h (z, y) := sum_weight_mul hX.2 _
      _ = ∑ z, ∑ y, M.μZ z * M.μY y * M.h (z, y) := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hatom, hmA, hmB, hmC]
  exact finner_core M.μX M.μY M.μZ M.f M.g M.h hX.1 hY.1 hZ.1 hf hg hh

/-! ## The explicit violation -/

/-- `Q(ε,r)(000) = ε + (1-ε)(1-r)³`. -/
private lemma Q_atom (ε r : ℝ) : atom000 (Q ε r) = ε + (1 - ε) * (1 - r) ^ 3 := by
  simp only [atom000, Q, bern]
  norm_num [pow_succ]

/-- `Q(ε,r)_A(0) = ε + (1-ε)(1-r)`. -/
private lemma Q_margA (ε r : ℝ) : margA (Q ε r) = ε + (1 - ε) * (1 - r) := by
  simp only [margA, Q, bern, Fintype.sum_bool]
  norm_num
  ring

/-- `Q(ε,r)_B(0) = ε + (1-ε)(1-r)`. -/
private lemma Q_margB (ε r : ℝ) : margB (Q ε r) = ε + (1 - ε) * (1 - r) := by
  simp only [margB, Q, bern, Fintype.sum_bool]
  norm_num
  ring

/-- `Q(ε,r)_C(0) = ε + (1-ε)(1-r)`. -/
private lemma Q_margC (ε r : ℝ) : margC (Q ε r) = ε + (1 - ε) * (1 - r) := by
  simp only [margC, Q, bern, Fintype.sum_bool]
  norm_num
  ring

/-- The two elementary estimates of paper Lemma 5.8: the atom is at least `ε`, and the common
marginal `1 - (1-ε)^t` lies in `[0, tε]` (Bernoulli's inequality). -/
private lemma witness_key (t : ℕ) (ht : 1 ≤ t) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ε ≤ ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) ^ 3
      ∧ 0 ≤ ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1))
      ∧ ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) ≤ (t : ℝ) * ε := by
  have hb0 : (0:ℝ) ≤ 1 - ε := by linarith
  have hb1 : (1 - ε) ≤ 1 := by linarith
  have hr0 : (0:ℝ) ≤ (1 - ε) ^ (t - 1) := pow_nonneg hb0 _
  have hr1 : (1 - ε) ^ (t - 1) ≤ 1 := pow_le_one₀ hb0 hb1
  -- `(1-ε) · (1-ε)^{t-1} = (1-ε)^t`, using `t ≥ 1`.
  have hts : t - 1 + 1 = t := Nat.succ_pred_eq_of_pos ht
  have hpow : (1 - ε) * (1 - ε) ^ (t - 1) = (1 - ε) ^ t := by
    rw [← pow_succ', hts]
  -- Bernoulli: `1 - tε ≤ (1-ε)^t`.
  have hbern : 1 - (t : ℝ) * ε ≤ (1 - ε) ^ t := by
    have := one_add_mul_le_pow (a := -ε) (by linarith) t
    calc 1 - (t : ℝ) * ε = 1 + (t : ℝ) * (-ε) := by ring
      _ ≤ (1 + -ε) ^ t := this
      _ = (1 - ε) ^ t := by ring_nf
  have hpow1 : (1 - ε) ^ t ≤ 1 := pow_le_one₀ hb0 hb1
  refine ⟨?_, ?_, ?_⟩
  · nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 - (1 - ε) ^ (t - 1)) 3]
  · nlinarith
  · -- `ε + (1-ε)(1 - r) = 1 - (1-ε)^t ≤ tε`
    have expand : ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) = 1 - (1 - ε) ^ t := by
      rw [← hpow]; ring
    rw [expand]; linarith

/-- Paper Lemma 5.8 (`lem:violation`), first part: for `t ≥ 1` and `0 < ε < t⁻³`, the law
`Q(ε, (1-ε)^{t-1})` strictly violates the Finner inequality. -/
theorem witness_violation (t : ℕ) (ht : 1 ≤ t) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / (t : ℝ) ^ 3) :
    margA (Q ε ((1 - ε) ^ (t - 1))) * margB (Q ε ((1 - ε) ^ (t - 1)))
        * margC (Q ε ((1 - ε) ^ (t - 1)))
      < atom000 (Q ε ((1 - ε) ^ (t - 1))) ^ 2 := by
  have ht1 : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht3 : (1:ℝ) ≤ (t : ℝ) ^ 3 := one_le_pow₀ ht1
  have hε1 : ε ≤ 1 := by
    have : 1 / (t : ℝ) ^ 3 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  obtain ⟨ha, hm0, hm⟩ := witness_key t ht h0 hε1
  rw [Q_margA, Q_margB, Q_margC, Q_atom]
  -- `m³ ≤ (tε)³ = t³ε·ε² < ε² ≤ a²`
  set m := ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) with hmdef
  set a := ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) ^ 3 with hadef
  have hcube : m ^ 3 ≤ ((t : ℝ) * ε) ^ 3 := pow_le_pow_left₀ hm0 hm 3
  have hlt : (t : ℝ) ^ 3 * ε < 1 := by
    rw [lt_div_iff₀ (by linarith)] at h1
    linarith [h1]
  have hsq : ((t : ℝ) * ε) ^ 3 < ε ^ 2 := by
    have : ((t : ℝ) * ε) ^ 3 = ((t : ℝ) ^ 3 * ε) * ε ^ 2 := by ring
    rw [this]
    nlinarith [sq_nonneg ε, mul_pos h0 h0]
  nlinarith [hcube, hsq, ha, h0]

/-- Paper Lemma 5.8 (`lem:violation`), conclusion: such a `Q(ε,(1-ε)^{t-1})` is not
triangle compatible. -/
theorem witness_not_compatible (t : ℕ) (ht : 1 ≤ t) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / (t : ℝ) ^ 3) : ¬ TriangleCompatible (Q ε ((1 - ε) ^ (t - 1))) := by
  intro hc
  exact absurd (finner_of_compatible hc) (not_le.2 (witness_violation t ht h0 h1))

/-- Paper Lemma 5.8 (`lem:violation`), quantitative part: at `ε = ε_t = 1/(2t³)` the Finner
margin of `P_t = Q(ε_t, r_t)` is at least `ε_t²/2`. -/
theorem witness_margin (t : ℕ) (ht : 1 ≤ t) :
    epsFam t ^ 2 / 2
      ≤ atom000 (Pfam t) ^ 2 - margA (Pfam t) * margB (Pfam t) * margC (Pfam t) := by
  have ht1 : (1:ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have ht3 : (1:ℝ) ≤ (t : ℝ) ^ 3 := one_le_pow₀ ht1
  have htpos : (0:ℝ) < (t : ℝ) ^ 3 := by linarith
  have heps : epsFam t = 1 / (2 * (t : ℝ) ^ 3) := rfl
  have h0 : 0 < epsFam t := by rw [heps]; positivity
  have hε1 : epsFam t ≤ 1 := by
    rw [heps, div_le_one (by linarith)]
    linarith
  -- `t³ ε_t = 1/2`
  have hhalf : (t : ℝ) ^ 3 * epsFam t = 1 / 2 := by
    rw [heps]; field_simp
  obtain ⟨ha, hm0, hm⟩ := witness_key t ht h0 hε1
  have hP : Pfam t = Q (epsFam t) ((1 - epsFam t) ^ (t - 1)) := rfl
  rw [hP, Q_margA, Q_margB, Q_margC, Q_atom]
  set ε := epsFam t
  set m := ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) with hmdef
  set a := ε + (1 - ε) * (1 - (1 - ε) ^ (t - 1)) ^ 3 with hadef
  have hcube : m ^ 3 ≤ ((t : ℝ) * ε) ^ 3 := pow_le_pow_left₀ hm0 hm 3
  have hval : ((t : ℝ) * ε) ^ 3 = ((t : ℝ) ^ 3 * ε) * ε ^ 2 := by ring
  have hbound : m ^ 3 ≤ ε ^ 2 / 2 := by
    rw [hval, hhalf] at hcube
    linarith
  nlinarith [hcube, hbound, ha, h0]

/-! ## `R_p` -/

private lemma R_atom (p : ℝ) : atom000 (Rlaw p) = p := by
  simp [atom000, Rlaw]

private lemma R_margA (p : ℝ) : margA (Rlaw p) = p := by
  simp [margA, Rlaw]

private lemma R_margB (p : ℝ) : margB (Rlaw p) = p := by
  simp [margB, Rlaw]

private lemma R_margC (p : ℝ) : margC (Rlaw p) = p := by
  simp [margC, Rlaw]

/-- Paper Proposition 5.12 (`prop:Rp`), incompatibility half: `R_p` violates the Finner
inequality, hence is not triangle compatible, for every `0 < p < 1`. -/
theorem Rlaw_not_compatible {p : ℝ} (h0 : 0 < p) (h1 : p < 1) :
    ¬ TriangleCompatible (Rlaw p) := by
  intro hc
  have := finner_of_compatible hc
  rw [R_atom, R_margA, R_margB, R_margC] at this
  nlinarith [this, mul_pos (mul_pos h0 h0) (sub_pos.2 h1)]

end

end TriangleInflation
