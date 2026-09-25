/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/
module


public import LeanPool.ParameterFreeGradient.O3.Stage9Theta
public import LeanPool.ParameterFreeGradient.O3.Stage9Telescoping
public import LeanPool.ParameterFreeGradient.O3.Stage9Certificate

/-!
# Stage 9: quadratic pairing certificate

This module proves the pairing balance required by the finite-data
certificate from the actual auxiliary recurrence.  The balance is a theorem,
not a field of the final statement.
-/

@[expose] public section

open scoped BigOperators

namespace O3

/-- The gradient at index `j` paired with the difference of the two indexed points. -/
noncomputable def stage9PairTerm {d : ℕ} (g v : ℕ → Vec d)
    (i j : ℕ) : ℝ := pairing (g j) (v i - v j)

/-- The two pairing sums combine into one edge sum after discrete summation
by parts and the exact weighted-gradient identity. -/
theorem stage9_pairingAggregate_eq_edgeSum {d : ℕ}
    (n : ℕ) (kappa delta : ℕ → ℝ) (g v : ℕ → Vec d)
    (hdelta : ∀ i, delta i = Stage9Certificate.ogmgDelta kappa i)
    (hweighted : ∀ k, k ≤ n →
      stage9WeightedGradient delta g k = kappa k • stage9P (stage9Theta n) g k) :
    Stage9Certificate.ogmgPairingAggregate n kappa (stage9PairTerm g v) =
      ∑ k ∈ Finset.range n,
        kappa (k + 1) *
          pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (v (k + 1) - v k) := by
  have hparts := stage9_pairing_summation_by_parts delta g v n
  have hsecond :
      (∑ i ∈ Finset.range n,
          Stage9Certificate.ogmgDelta kappa i *
            stage9PairTerm g v n i) =
        ∑ k ∈ Finset.range n,
          pairing (kappa (k + 1) • stage9P (stage9Theta n) g (k + 1))
            (v (k + 1) - v k) := by
    calc
      (∑ i ∈ Finset.range n,
          Stage9Certificate.ogmgDelta kappa i *
            stage9PairTerm g v n i) =
        ∑ i ∈ Finset.range n,
          delta i * pairing (g i) (v n - v i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hdelta]
            rfl
      _ = ∑ k ∈ Finset.range n,
          pairing (stage9WeightedGradient delta g (k + 1))
            (v (k + 1) - v k) := hparts
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hweighted (k + 1) (by simpa using hk)]
  have hsecond' :
      (∑ i ∈ Finset.range n,
          Stage9Certificate.ogmgDelta kappa i *
            pairing (g i) (v n - v i)) =
        ∑ k ∈ Finset.range n,
          pairing (kappa (k + 1) • stage9P (stage9Theta n) g (k + 1))
            (v (k + 1) - v k) := by
    simpa only [stage9PairTerm] using hsecond
  unfold Stage9Certificate.ogmgPairingAggregate stage9PairTerm
  rw [hsecond', ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [Stage2RouteD.pairing_smul_left, pairing_sub_left]
  have hreverse : pairing (g (k + 1)) (v k - v (k + 1)) =
      -pairing (g (k + 1)) (v (k + 1) - v k) := by
    unfold pairing
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.sub_apply]
    ring
  rw [hreverse]
  ring

/-- Native proof of the exact quadratic balance in the source certificate. -/
theorem stage9_pairing_balance {d : ℕ}
    (n : ℕ) (hn : 1 ≤ n) (M : ℝ) (hM : M ≠ 0)
    (g v : ℕ → Vec d)
    (hvelocity : ∀ k, 1 ≤ k → k ≤ n →
      M • (v k - v (k - 1)) =
        (-stage9Theta n k) •
          (stage9P (stage9Theta n) g k + stage9P (stage9Theta n) g (k + 1))) :
    Stage9Certificate.ogmgPairingAggregate n (stage9Kappa n)
        (stage9PairTerm g v) =
      ((stage9Theta n 0) ^ 2 * (lpNorm 2 (g n)) ^ (2 : ℕ) -
          (lpNorm 2 (g 0)) ^ (2 : ℕ)) / (2 * M) := by
  let delta : ℕ → ℝ := stage9Delta n
  have hweighted : ∀ k, k ≤ n →
      stage9WeightedGradient delta g k =
        stage9Kappa n k • stage9P (stage9Theta n) g k := by
    intro k hk
    exact stage9_delta_gradient_sum n (stage9Theta n) (stage9Kappa n)
      delta g (stage9Theta_ne_zero n)
      (fun j hj ↦ stage9Delta_eq_kappa_div_theta hj)
      (fun j hj ↦ stage9Kappa_eq_next_mul_one_sub_inv hj) k hk
  have hedge := stage9_pairingAggregate_eq_edgeSum n (stage9Kappa n)
    delta g v (fun _ ↦ rfl) hweighted
  rw [hedge]
  have hterm : ∀ k ∈ Finset.range n,
      M * (stage9Kappa n (k + 1) *
        pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
          (v (k + 1) - v k)) =
      -stage9Kappa n (k + 1) * (stage9Theta n (k + 1)) ^ 2 *
        ((lpNorm 2 (stage9P (stage9Theta n) g (k + 1))) ^ (2 : ℕ) -
          (lpNorm 2 (stage9P (stage9Theta n) g (k + 2))) ^ (2 : ℕ)) := by
    intro k hk
    have hv := hvelocity (k + 1) (by omega) (by simpa using hk)
    have hpairv : M * pairing
        (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
        (v (k + 1) - v k) =
      -stage9Theta n (k + 1) * pairing
        (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
        (stage9P (stage9Theta n) g (k + 1) +
          stage9P (stage9Theta n) g (k + 2)) := by
      have hp := congrArg (fun x : Vec d ↦ pairing
        (stage9P (stage9Theta n) g (k + 1) - g (k + 1)) x) hv
      simpa only [Stage2RouteD.pairing_smul_right,
        Nat.add_sub_cancel, Nat.add_assoc] using hp
    have hquad := stage9P_quadratic_step
      (theta := stage9Theta n) (g := g)
      (k := k + 1) (stage9Theta_ne_zero n (k + 1))
    have hquad' : stage9Theta n (k + 1) * pairing
        (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
        (stage9P (stage9Theta n) g (k + 1) +
          stage9P (stage9Theta n) g (k + 2)) =
      stage9Theta n (k + 1) ^ 2 *
        ((lpNorm 2 (stage9P (stage9Theta n) g (k + 1))) ^ (2 : ℕ) -
          (lpNorm 2 (stage9P (stage9Theta n) g (k + 2))) ^ (2 : ℕ)) := by
      simpa [Nat.add_assoc] using hquad
    calc
      M * (stage9Kappa n (k + 1) * pairing
          (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
          (v (k + 1) - v k)) =
        stage9Kappa n (k + 1) *
          (M * pairing
            (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (v (k + 1) - v k)) := by ring
      _ = stage9Kappa n (k + 1) *
          (-stage9Theta n (k + 1) * pairing
            (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (stage9P (stage9Theta n) g (k + 1) +
              stage9P (stage9Theta n) g (k + 2))) := by rw [hpairv]
      _ = -stage9Kappa n (k + 1) *
          (stage9Theta n (k + 1) * pairing
            (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (stage9P (stage9Theta n) g (k + 1) +
              stage9P (stage9Theta n) g (k + 2))) := by ring
      _ = _ := by rw [hquad']; ring
  have hsum : M * (∑ k ∈ Finset.range n,
      stage9Kappa n (k + 1) *
        pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
          (v (k + 1) - v k)) =
      ∑ k ∈ Finset.range n,
        (-stage9Kappa n (k + 1) * (stage9Theta n (k + 1)) ^ 2 *
          ((lpNorm 2 (stage9P (stage9Theta n) g (k + 1))) ^ (2 : ℕ) -
            (lpNorm 2 (stage9P (stage9Theta n) g (k + 2))) ^ (2 : ℕ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    exact hterm
  let q : ℕ → ℝ := fun k ↦
    (lpNorm 2 (stage9P (stage9Theta n) g k)) ^ (2 : ℕ)
  have hsumFinal : M * (∑ k ∈ Finset.range n,
      stage9Kappa n (k + 1) *
        pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
          (v (k + 1) - v k)) =
      ((stage9Theta n 0) ^ 2 * (lpNorm 2 (g n)) ^ (2 : ℕ) -
        (lpNorm 2 (g 0)) ^ (2 : ℕ)) / 2 := by
    calc
      M * (∑ k ∈ Finset.range n,
          stage9Kappa n (k + 1) *
            pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
              (v (k + 1) - v k)) =
        ∑ k ∈ Finset.range n,
          (-stage9Kappa n (k + 1) * (stage9Theta n (k + 1)) ^ 2 *
            (q (k + 1) - q (k + 2))) := by simpa only [q] using hsum
      _ = ∑ k ∈ Finset.range n,
          (-(stage9Theta n 0) ^ 2 / 2) * (q (k + 1) - q (k + 2)) := by
            apply Finset.sum_congr rfl
            intro k _
            have hc := stage9Kappa_mul_theta_sq (n := n)
              (by omega : 1 ≤ k + 1)
            calc
              -stage9Kappa n (k + 1) * stage9Theta n (k + 1) ^ 2 *
                  (q (k + 1) - q (k + 2)) =
                -(stage9Kappa n (k + 1) * stage9Theta n (k + 1) ^ 2) *
                  (q (k + 1) - q (k + 2)) := by ring
              _ = _ := by rw [hc]; ring
      _ = (-(stage9Theta n 0) ^ 2 / 2) *
          ∑ k ∈ Finset.range n, (q (k + 1) - q (k + 2)) := by
            rw [Finset.mul_sum]
      _ = (-(stage9Theta n 0) ^ 2 / 2) * (q 1 - q (n + 1)) := by
            rw [Finset.sum_range_sub']
      _ = _ := by
        have hp1 := stage9P_one (theta := stage9Theta n) (g := g)
        have hpend := stage9P_endpoint (theta := stage9Theta n) (g := g)
          (stage9Theta_endpoint hn)
        simp only [q]
        rw [hpend, hp1, Stage2RouteC.lpNorm_smul (by norm_num)]
        have hθ0pos := stage9Theta_pos n 0
        rw [abs_of_pos (div_pos (by norm_num) hθ0pos)]
        field_simp [hθ0pos.ne']
        ring
  apply (eq_div_iff (mul_ne_zero (by norm_num) hM)).2
  calc
    (∑ k ∈ Finset.range n,
        stage9Kappa n (k + 1) *
          pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (v (k + 1) - v k)) * (2 * M) =
      2 * (M * (∑ k ∈ Finset.range n,
        stage9Kappa n (k + 1) *
          pairing (stage9P (stage9Theta n) g (k + 1) - g (k + 1))
            (v (k + 1) - v k))) := by ring
    _ = _ := by rw [hsumFinal]; ring

end O3
