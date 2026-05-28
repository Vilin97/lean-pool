/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import LeanPool.Shannon1948Formalization.Entropy.Uniform

/-!
# Shannon.Entropy.Rational

Phase 2 of the characterization: rational probabilities.

This module derives the entropy formula for distributions of the form
`p_i = n_i / N` via grouped equiprobable refinement and the grouping condition.
It also includes a worked decomposition corresponding to Shannon's
`(1/2, 1/3, 1/6)` narrative.
-/
namespace LeanPool.Shannon1948Formalization

noncomputable section
open Filter
open scoped Topology

/-! ## Phase 2: Rational Probabilities via Grouping -/

lemma relabel_compose_rational_eq_uniform
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (n : α → ℕ)
    (hpos : ∀ a, 0 < n a)
    (N : ℕ)
    (hN : 0 < N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ))
    (e : Sigma (fun a : α => Fin (n a)) ≃ Fin N) :
    relabelProb e
      (composeProb p (fun a => uniformPNat ⟨n a, hpos a⟩))
    = uniformPNat ⟨N, hN⟩ := by
  ext x
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hn_ne : (n (e.symm x).1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hpos (e.symm x).1))
  simp [relabelProb, composeProb, uniformPNat, hp]
  field_simp [hN_ne, hn_ne]

lemma grouping_on_rational_counts
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (n : α → ℕ)
    (hpos : ∀ a, 0 < n a)
    (N : ℕ)
    (hN : 0 < N)
    (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    Apos H ⟨N, hN⟩ = H p + ∑ a, p a * Apos H ⟨n a, hpos a⟩ := by
  let q : (a : α) → ProbDist (Fin (n a)) := fun a => uniformPNat ⟨n a, hpos a⟩
  have hgroup := hH.grouping p q
  have hcard : Fintype.card (Sigma (fun a : α => Fin (n a))) = N := by
    calc
      Fintype.card (Sigma (fun a : α => Fin (n a)))
          = ∑ a, Fintype.card (Fin (n a)) := by simp
      _ = ∑ a, n a := by simp
      _ = N := hsum
  let e : Sigma (fun a : α => Fin (n a)) ≃ Fin N := Fintype.equivFinOfCardEq hcard
  have hrelab : H (relabelProb e (composeProb p q)) = H (composeProb p q) :=
    hH.relabelInvariant e (composeProb p q)
  have hident :
      relabelProb e (composeProb p q) = uniformPNat ⟨N, hN⟩ := by
    simpa [q] using relabel_compose_rational_eq_uniform p n hpos N hN hp e
  have hsumA :
      (∑ a, p a * H (q a))
        = ∑ a, p a * Apos H ⟨n a, hpos a⟩ := by
    refine Finset.sum_congr rfl ?_
    intro a _
    rfl
  calc
    Apos H ⟨N, hN⟩ = H (composeProb p q) := by
      simpa [Apos, hident] using hrelab
    _ = H p + ∑ a, p a * H (q a) := hgroup
    _ = H p + ∑ a, p a * Apos H ⟨n a, hpos a⟩ := by rw [hsumA]

lemma entropyNat_of_rational_counts_aux
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (n : α → ℕ)
    (hpos : ∀ a, 0 < n a)
    (N : ℕ)
    (hN : 0 < N)
    (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    H p
      = K H * Real.log (N : ℝ)
        - ∑ a, p a * (K H * Real.log (n a : ℝ)) := by
  have hgroup :
      Apos H ⟨N, hN⟩ = H p + ∑ a, p a * Apos H ⟨n a, hpos a⟩ :=
    grouping_on_rational_counts H hH p n hpos N hN hsum hp
  have hA_N : Apos H ⟨N, hN⟩ = K H * Real.log (N : ℝ) :=
    Apos_eq_K_mul_log H hH ⟨N, hN⟩
  have hA_n :
      (∑ a, p a * Apos H ⟨n a, hpos a⟩)
        = ∑ a, p a * (K H * Real.log (n a : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro a _
    simpa using congrArg (fun t => p a * t) (Apos_eq_K_mul_log H hH ⟨n a, hpos a⟩)
  linarith [hgroup, hA_N, hA_n]

lemma entropyNat_of_rational_counts
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H)
    {α : Type} [Fintype α]
    (p : ProbDist α)
    (n : α → ℕ)
    (hpos : ∀ a, 0 < n a)
    (N : ℕ)
    (hN : 0 < N)
    (hsum : (∑ a, n a) = N)
    (hp : ∀ a, p a = (n a : ℝ) / (N : ℝ)) :
    H p = -K H * ∑ a, p a * Real.log (p a) := by
  have hN_ne : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have h_main :
      H p = K H * Real.log (N : ℝ) - ∑ a, p a * (K H * Real.log (n a : ℝ)) :=
    entropyNat_of_rational_counts_aux H hH p n hpos N hN hsum hp
  have hsum_scale :
      (∑ a, p a * (K H * Real.log (n a : ℝ)))
        = K H * (∑ a, p a * Real.log (n a : ℝ)) := by
    calc
      (∑ a, p a * (K H * Real.log (n a : ℝ)))
          = ∑ a, K H * (p a * Real.log (n a : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              ring
      _ = K H * (∑ a, p a * Real.log (n a : ℝ)) := by
            rw [Finset.mul_sum]
  have hlogp :
      (∑ a, p a * Real.log (p a))
        = (∑ a, p a * Real.log (n a : ℝ)) - Real.log (N : ℝ) := by
    calc
      (∑ a, p a * Real.log (p a))
          = ∑ a, p a * (Real.log (n a : ℝ) - Real.log (N : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro a _
              rw [hp a]
              have hn_ne : (n a : ℝ) ≠ 0 := by
                exact_mod_cast (Nat.ne_of_gt (hpos a))
              rw [Real.log_div hn_ne hN_ne]
      _ = ∑ a, (p a * Real.log (n a : ℝ) - p a * Real.log (N : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro a _
            ring
      _ = (∑ a, p a * Real.log (n a : ℝ)) - ∑ a, p a * Real.log (N : ℝ) := by
            rw [Finset.sum_sub_distrib]
      _ = (∑ a, p a * Real.log (n a : ℝ)) - (∑ a, p a) * Real.log (N : ℝ) := by
            rw [Finset.sum_mul]
      _ = (∑ a, p a * Real.log (n a : ℝ)) - Real.log (N : ℝ) := by
            rw [prob_sum_eq_one p, one_mul]
  calc
    H p = K H * Real.log (N : ℝ) - ∑ a, p a * (K H * Real.log (n a : ℝ)) := h_main
    _ = K H * Real.log (N : ℝ) - K H * (∑ a, p a * Real.log (n a : ℝ)) := by
          rw [hsum_scale]
    _ = -K H * ((∑ a, p a * Real.log (n a : ℝ)) - Real.log (N : ℝ)) := by ring
    _ = -K H * (∑ a, p a * Real.log (p a)) := by rw [hlogp]

/-- First-stage split used in the `(1/2, 1/3, 1/6)` worked decomposition. -/
def workedP : ProbDist Bool := by
  refine ⟨fun _ => (1 : ℝ) / 2, ?_⟩
  constructor
  · intro _
    positivity
  · simp

/-- Second-stage alphabets for the worked decomposition:
`true` has one outcome; `false` has two outcomes. -/
def workedFib : Bool → Type
  | true => Fin 1
  | false => Fin 2

instance : ∀ b : Bool, Fintype (workedFib b)
  | true => by simpa [workedFib] using (inferInstance : Fintype (Fin 1))
  | false => by simpa [workedFib] using (inferInstance : Fintype (Fin 2))

/-- Second-stage conditional probabilities for the worked decomposition. -/
def workedQ : (b : Bool) → ProbDist (workedFib b)
  | true => by
      change ProbDist (Fin 1)
      simpa using (uniformPNat (1 : ℕ+))
  | false => by
      change ProbDist (Fin 2)
      refine ⟨fun i : Fin 2 => if i = 0 then (2 : ℝ) / 3 else (1 : ℝ) / 3, ?_⟩
      constructor
      · intro i
        by_cases hi : i = 0
        · simp only [hi, ↓reduceIte]
          positivity
        · simp only [hi, ↓reduceIte]
          norm_num
      · norm_num [Fin.sum_univ_two]

/-- The composed distribution in the worked `(1/2, 1/3, 1/6)` example. -/
def workedCompose : ProbDist (Sigma workedFib) :=
  composeProb workedP workedQ

/--
Masses in the worked decomposition:
`(true, 0)` has mass `1/2`, `(false, 0)` has mass `1/3`,
and `(false, 1)` has mass `1/6`.
-/
lemma workedCompose_masses :
    workedCompose ⟨true, (0 : Fin 1)⟩ = (1 : ℝ) / 2 ∧
      workedCompose ⟨false, (0 : Fin 2)⟩ = (1 : ℝ) / 3 ∧
      workedCompose ⟨false, (1 : Fin 2)⟩ = (1 : ℝ) / 6 := by
  constructor
  · norm_num [workedCompose, composeProb, workedP, workedQ, workedFib, uniformPNat]
  constructor
  · norm_num [workedCompose, composeProb, workedP, workedQ, workedFib, uniformPNat]
  · norm_num [workedCompose, composeProb, workedP, workedQ, workedFib, uniformPNat]

/--
Worked grouping identity corresponding to Shannon's `(1/2, 1/3, 1/6)` narrative:
first choose `true/false` with probabilities `(1/2, 1/2)`, then if `false`
choose between two outcomes with probabilities `(2/3, 1/3)`.
-/
theorem worked_grouping_identity
    (H : {α : Type} → [Fintype α] → ProbDist α → ℝ)
    (hH : ShannonEntropyAxioms H) :
    H workedCompose = H workedP + (1 / 2 : ℝ) * H (workedQ false) := by
  have hqTrue_zero : H (workedQ true) = 0 := by
    simpa [workedQ, workedFib, Apos] using Apos_one_zero H hH
  have hsum :
      (∑ b : Bool, workedP b * H (workedQ b))
        = (1 / 2 : ℝ) * H (workedQ false) := by
    simp [workedP, hqTrue_zero]
  calc
    H workedCompose = H workedP + ∑ b : Bool, workedP b * H (workedQ b) := by
      simpa [workedCompose] using hH.grouping workedP workedQ
    _ = H workedP + (1 / 2 : ℝ) * H (workedQ false) := by rw [hsum]


end

end LeanPool.Shannon1948Formalization
