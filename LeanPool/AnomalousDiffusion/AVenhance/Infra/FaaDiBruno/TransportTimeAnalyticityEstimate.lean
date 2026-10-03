/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FaaDiBruno.TransportTimeAnalyticity

/-! # Transport Time Analyticity Estimate

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

open Homogenization MeasureTheory
open scoped ContDiff NNReal Topology

noncomputable section

namespace AVenhance.FaaDiBruno

/-- Unnormalized mixed time-space weight in the transport analyticity estimate. -/
def TransportTimeAnalyticityEstimate.transportTimeRawWeight (m n j k : ℕ)
    (C_f Q_f R A Q ρ : ℝ) : ℝ :=
  C_f * A * (Q_f ^ (m - j) * Q ^ j) *
    ((m - j).factorial * j.factorial) *
    (((n - k).factorial * k.factorial) *
      (((k + j + 1).factorial : ℝ) / k.factorial)) *
    (R ^ (n - k) * ρ ^ (k + 1)) /
      ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2)

theorem TransportTimeAnalyticityEstimate.transportTime_rawWeight_eq_productBound {m n j k : ℕ}
    {C_f Q_f R A Q ρ : ℝ} :
    (C_f * Q_f ^ (m - j) * (m - j).factorial) *
      ((n - k).factorial * R ^ (n - k) / ((n - k + 1 : ℕ) : ℝ) ^ 2) *
      (A * (((k + j + 1).factorial : ℝ) * j.factorial /
        (k + 1).factorial) * Q ^ j) *
      ((k + 1).factorial * ρ ^ (k + 1) / (k + 2 : ℝ) ^ 2) =
    TransportTimeAnalyticityEstimate.transportTimeRawWeight m n j k C_f Q_f R A Q ρ := by
  dsimp [TransportTimeAnalyticityEstimate.transportTimeRawWeight]
  have h₁ : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
  have h₂ : (0 : ℝ) < ((k.factorial : ℝ)) := by positivity
  have h₃ : (0 : ℝ) < ((n - k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - k + 1 by omega)
  have h₄ : (0 : ℝ) < (k + 2 : ℝ) := by positivity
  field_simp [h₁.ne', h₂.ne', h₃.ne', h₄.ne']

theorem TransportTimeAnalyticityEstimate.transportTime_choose_weight_le {m n j k : ℕ}
    (hjm : j ≤ m) (hkn : k ≤ n)
    {C_f Q_f R A Q ρ : ℝ}
    (hCf : 0 ≤ C_f) (hQf : 0 ≤ Q_f) (hQfQ : Q_f ≤ Q)
    (hR : 0 < R) (hRρ : R ≤ ρ) (hρ : 0 < ρ) (hA : 0 ≤ A) :
    (m.choose j : ℝ) * (n.choose k : ℝ) *
        TransportTimeAnalyticityEstimate.transportTimeRawWeight m n j k C_f Q_f R A Q ρ ≤
      C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
        ((((k + j + 1).factorial : ℝ) / k.factorial) /
          (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)) := by
  have hcmNat := Nat.choose_mul_factorial_mul_factorial hjm
  have hcm : (m.choose j : ℝ) * (m - j).factorial * j.factorial =
      m.factorial := by
    calc
      _ = (m.choose j : ℝ) * j.factorial * (m - j).factorial := by ring
      _ = m.factorial := by exact_mod_cast hcmNat
  have hcnNat := Nat.choose_mul_factorial_mul_factorial hkn
  have hcn : (n.choose k : ℝ) * (n - k).factorial * k.factorial =
      n.factorial := by
    calc
      _ = (n.choose k : ℝ) * k.factorial * (n - k).factorial := by ring
      _ = n.factorial := by exact_mod_cast hcnNat
  have hchooseEq :
      (m.choose j : ℝ) * (n.choose k : ℝ) *
          TransportTimeAnalyticityEstimate.transportTimeRawWeight m n j k C_f Q_f R A Q ρ =
        C_f * A * (Q_f ^ (m - j) * Q ^ j) * m.factorial * n.factorial *
          (((k + j + 1).factorial : ℝ) / k.factorial) *
          (R ^ (n - k) * ρ ^ (k + 1)) /
            ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2) := by
    rw [TransportTimeAnalyticityEstimate.transportTimeRawWeight]
    calc
      _ = C_f * A * (Q_f ^ (m - j) * Q ^ j) *
          ((m.choose j : ℝ) * (m - j).factorial * j.factorial) *
          ((n.choose k : ℝ) * (n - k).factorial * k.factorial) *
          (((k + j + 1).factorial : ℝ) / k.factorial) *
          (R ^ (n - k) * ρ ^ (k + 1)) /
            ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2) := by ring
      _ = _ := by rw [hcm, hcn]
  have huj : m - j + j = m := Nat.sub_add_cancel hjm
  have hQ : 0 ≤ Q := le_trans hQf hQfQ
  have hpowF : Q_f ^ (m - j) ≤ Q ^ (m - j) :=
    pow_le_pow_left₀ hQf hQfQ (m - j)
  have hpowQ : Q_f ^ (m - j) * Q ^ j ≤ Q ^ m := by
    calc
      _ ≤ Q ^ (m - j) * Q ^ j :=
        mul_le_mul_of_nonneg_right hpowF (by positivity)
      _ = Q ^ m := by rw [← pow_add, huj]
  have hpowR0 : R ^ (n - k) ≤ ρ ^ (n - k) :=
    pow_le_pow_left₀ hR.le hRρ (n - k)
  have hpowR : R ^ (n - k) * ρ ^ (k + 1) ≤ ρ ^ (n + 1) := by
    calc
      _ ≤ ρ ^ (n - k) * ρ ^ (k + 1) :=
        mul_le_mul_of_nonneg_right hpowR0 (by positivity)
      _ = ρ ^ (n + 1) := by
        rw [← pow_add]
        congr 1
        omega
  have hden : 0 < ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2) := by
    positivity
  have hcoef : 0 ≤ C_f * A * m.factorial * n.factorial *
      (((k + j + 1).factorial : ℝ) / k.factorial) /
        ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2) := by
    positivity
  calc
    _ = (C_f * A * m.factorial * n.factorial *
        (((k + j + 1).factorial : ℝ) / k.factorial) /
          ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2)) *
        ((Q_f ^ (m - j) * Q ^ j) * (R ^ (n - k) * ρ ^ (k + 1))) := by
          rw [hchooseEq]
          ring
    _ ≤ (C_f * A * m.factorial * n.factorial *
        (((k + j + 1).factorial : ℝ) / k.factorial) /
          ((((n - k + 1 : ℕ) : ℝ) ^ 2) * (k + 2 : ℝ) ^ 2)) *
        (Q ^ m * ρ ^ (n + 1)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul hpowQ hpowR (by positivity) (by positivity)
          · exact hcoef
    _ = _ := by ring

/-- Factorial convolution kernel for the mixed transport derivative estimate. -/
def TransportTimeAnalyticityEstimate.transportTimeFactorialKernel (n j k : ℕ) : ℝ :=
  (((k + j + 1).factorial : ℝ) / k.factorial) /
    (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2)

/-- Normalized scalar convolution kernel for the transport time derivative estimate. -/
def TransportTimeAnalyticityEstimate.transportTimeScalarKernel (m n j k : ℕ) : ℝ :=
  ((n + 1 : ℝ) ^ 2 /
    (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2 * (m + 1 : ℝ))) *
      (((k + j + 1).factorial : ℝ) / k.factorial)

theorem TransportTimeAnalyticityEstimate.iteratedJointTimeDerivative_shift (m : ℕ)
    (F : ℝ × Vec 2 → Vec 2) :
    iteratedJointTimeDerivative m (jointTimeDerivative F) =
      iteratedJointTimeDerivative (m + 1) F := by
  induction m with
  | zero => rfl
  | succ m ih =>
      change jointTimeDerivative
        (iteratedJointTimeDerivative m (jointTimeDerivative F)) =
        jointTimeDerivative (iteratedJointTimeDerivative (m + 1) F)
      rw [ih]

theorem TransportTimeAnalyticityEstimate.directionalJet_mixedTime_successor
    (m : ℕ) (L : List (Fin 2)) (F : ℝ × Vec 2 → Vec 2)
    (hF : ContDiff ℝ ∞ F) (p : ℝ × Vec 2) :
    directionalJet (transportTimeDirections m ++
      transportCoordinateDirections L) (jointTimeDerivative F) p =
    directionalJet (transportTimeDirections (m + 1) ++
      transportCoordinateDirections L) F p := by
  calc
    _ = iteratedJointTimeDerivative m
        (directionalJet (transportCoordinateDirections L)
          (jointTimeDerivative F)) p := by
            exact congrFun (directionalJet_mixedCoordinates_eq_iteratedTime_spatial
              m L (jointTimeDerivative F)) p
    _ = iteratedJointTimeDerivative m
        (jointTimeDerivative (directionalJet (transportCoordinateDirections L) F)) p := by
            rw [show directionalJet (transportCoordinateDirections L)
                  (jointTimeDerivative F) =
                jointTimeDerivative (directionalJet (transportCoordinateDirections L) F) by
                  simpa [transportCoordinateDirections] using
                    (directionalJet_jointTime_commute
                      (L.map (coordinateVector 2)) F hF)]
    _ = iteratedJointTimeDerivative (m + 1)
        (directionalJet (transportCoordinateDirections L) F) p := by
            rw [TransportTimeAnalyticityEstimate.iteratedJointTimeDerivative_shift]
    _ = _ := by
          symm
          exact congrFun (directionalJet_mixedCoordinates_eq_iteratedTime_spatial
            (m + 1) L F) p

theorem TransportTimeAnalyticityEstimate.transportTime_mixedJet_pointwise_bound
    {m n N M : ℕ} (L : List (Fin 2)) (hL : L.length = n)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {C_f C_g Q_f Q_g R A Q ρ : ℝ}
    (hmM : m ≤ M) (hnN : n ≤ N) (hmnN : m + n + 1 ≤ N)
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hρ : 0 < ρ) (hRρ : R ≤ ρ)
    (hQf : 0 ≤ Q_f) (hQfQ : Q_f ≤ Q) (hQ : 0 < Q) (hQg : 0 ≤ Q_g)
    (hA : 0 ≤ A)
    (hB : ∀ t u v, u ≤ M → v ≤ N →
      snorm (transportTimeDerivative u (Function.uncurry b) t) v R ≤
        ENNReal.ofReal (C_f * Q_f ^ u * u.factorial))
    (hG : ∀ t, m ≤ M → n ≤ N →
      snorm (transportTimeDerivative m (Function.uncurry g) t) n R ≤
        ENNReal.ofReal (C_g * Q_g ^ m * m.factorial))
    (t : ℝ)
    (hYlower : ∀ j k, j ≤ m → j + (k + 1) ≤ N →
      snorm (transportTimeDerivative j (Function.uncurry Y) t) (k + 1) ρ ≤
        ENNReal.ofReal
          (A * (((k + 1 + j).factorial : ℝ) * j.factorial /
            (k + 1).factorial) * Q ^ j))
    (x : Vec 2) :
    ‖directionalJet (transportTimeDirections (m + 1) ++
        transportCoordinateDirections L) (Function.uncurry Y) (t, x)‖ ≤
      C_g * Q_g ^ m * m.factorial * n.factorial * ρ ^ n /
          (n + 1 : ℝ) ^ 2 +
        2 * C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
  let B : ℝ × Vec 2 → Vec 2 := Function.uncurry b
  let G : ℝ × Vec 2 → Vec 2 := Function.uncurry g
  let U : ℝ × Vec 2 → Vec 2 := Function.uncurry Y
  let I := transportTimeDirections m
  let J := transportCoordinateDirections L
  let raw (j k : ℕ) := TransportTimeAnalyticityEstimate.transportTimeRawWeight m n j k C_f Q_f R A
      Q ρ
  let product (i : Fin 2)
      (p q : List (ℝ × Vec 2) × List (ℝ × Vec 2)) : Vec 2 :=
    directionalJet (p.1 ++ q.1) (fun z => B z i) (t, x) •
      directionalJet (p.2 ++ q.2)
        (fun z => fderiv ℝ U z (0, coordinateVector 2 i)) (t, x)
  have hterm (i : Fin 2) (p : List (ℝ × Vec 2) × List (ℝ × Vec 2))
      (hp : p ∈ directionalSplits I)
      (q : List (ℝ × Vec 2) × List (ℝ × Vec 2))
      (hq : q ∈ directionalSplits J) :
      ‖product i p q‖ ≤ raw p.2.length q.2.length := by
    let j := p.2.length
    let k := q.2.length
    have hpLen := directionalSplits_length_sum I p hp
    have hqLen := directionalSplits_length_sum J q hq
    have hIlen : I.length = m := by simp [I, transportTimeDirections]
    have hJlen : J.length = n := by simp [J, transportCoordinateDirections,
      jointSpatialDirections, hL]
    have hjm : j ≤ m := by dsimp [j]; omega
    have hkn : k ≤ n := by dsimp [k]; omega
    have hpleft : p.1.length = m - j := by dsimp [j]; omega
    have hqleft : q.1.length = n - k := by dsimp [k]; omega
    have hBterm : snorm
        (transportTimeDerivative p.1.length (Function.uncurry b) t)
        q.1.length R ≤ ENNReal.ofReal
          (C_f * Q_f ^ p.1.length * p.1.length.factorial) :=
      hB t p.1.length q.1.length (by omega) (by omega)
    have hYterm : snorm
        (transportTimeDerivative p.2.length (Function.uncurry Y) t)
        (q.2.length + 1) ρ ≤ ENNReal.ofReal
          (A * (((q.2.length + p.2.length + 1).factorial : ℝ) *
            p.2.length.factorial / (q.2.length + 1).factorial) *
              Q ^ p.2.length) := by
      simpa [j, k, mul_assoc, add_assoc, add_left_comm, add_comm] using
        hYlower j k hjm (by omega)
    have hprod := transportTimeLowerProduct_pointwise_bound
      L hL hb hY hR hρ (le_of_lt hCf)
      hQf (le_of_lt hQ) hA hp hq i t x hBterm hYterm
    rw [hpleft, hqleft] at hprod
    rw [show p.2.length = j by rfl, show q.2.length = k by rfl] at hprod
    change ‖product i p q‖ ≤ TransportTimeAnalyticityEstimate.transportTimeRawWeight m n j k C_f
        Q_f R A Q ρ
    rw [← TransportTimeAnalyticityEstimate.transportTime_rawWeight_eq_productBound]
    simpa [product, add_assoc, add_left_comm, add_comm] using hprod
  have hsumBound := directionalSplit_product_sum_bound I J product raw hterm
  have hweights :
      (∑ j ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1),
          (m.choose j : ℝ) * (n.choose k : ℝ) * raw j k) ≤
        C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1),
            (C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1)) *
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k := by
            apply Finset.sum_le_sum
            intro j hj
            apply Finset.sum_le_sum
            intro k hk
            have hjm : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
            have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
            simpa [raw, TransportTimeAnalyticityEstimate.transportTimeFactorialKernel, mul_assoc,
                mul_left_comm,
              mul_comm] using
              TransportTimeAnalyticityEstimate.transportTime_choose_weight_le hjm hkn (le_of_lt
                  hCf) hQf hQfQ hR
                hRρ hρ hA
      _ = _ := by
            calc
              _ = ∑ j ∈ Finset.range (m + 1),
                  (C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1)) *
                    (∑ k ∈ Finset.range (n + 1),
                      TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
                        apply Finset.sum_congr rfl
                        intro j hj
                        rw [← Finset.mul_sum]
              _ = (C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1)) *
                    (∑ j ∈ Finset.range (m + 1),
                      ∑ k ∈ Finset.range (n + 1),
                        TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
                        rw [← Finset.mul_sum]
  have hadv :
      ‖∑ i : Fin 2,
        ((directionalSplits I).map fun p =>
          ((directionalSplits J).map fun q => product i p q).sum).sum‖ ≤
        2 * C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
    have hIl : I.length = m := by simp [I, transportTimeDirections]
    have hJl : J.length = n := by simp [J, transportCoordinateDirections,
      jointSpatialDirections, hL]
    have hsumBound' :
        ‖∑ i : Fin 2,
          ((directionalSplits I).map fun p =>
            ((directionalSplits J).map fun q => product i p q).sum).sum‖ ≤
          2 * (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              (m.choose j : ℝ) * (n.choose k : ℝ) * raw j k) := by
      simpa only [hIl, hJl] using hsumBound
    calc
      _ ≤ 2 * (∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1),
            (m.choose j : ℝ) * (n.choose k : ℝ) * raw j k) := by
              exact hsumBound'
      _ ≤ _ := by
        have := mul_le_mul_of_nonneg_left hweights (by norm_num : (0 : ℝ) ≤ 2)
        calc
          _ ≤ 2 * (C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
              (∑ j ∈ Finset.range (m + 1),
                ∑ k ∈ Finset.range (n + 1),
                  TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k)) := this
          _ = _ := by ring
  have hsource :
      ‖directionalJet (transportTimeDirections m ++ J) G (t, x)‖ ≤
        C_g * Q_g ^ m * m.factorial * n.factorial * ρ ^ n /
          (n + 1 : ℝ) ^ 2 := by
    have hs := hG t (by omega) (by omega)
    have hpoint := coordinateList_timeJet_norm_le_of_snorm
      (Function.uncurry g) hg t L hL hR (by positivity) hs x
    have hpow : R ^ n ≤ ρ ^ n := pow_le_pow_left₀ hR.le hRρ n
    have hcoef : 0 ≤ C_g * Q_g ^ m * m.factorial * n.factorial := by
      positivity
    calc
      _ ≤ C_g * Q_g ^ m * m.factorial * n.factorial * R ^ n /
          (n + 1 : ℝ) ^ 2 := by
            simpa [J, mul_assoc] using hpoint
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hcoef) (by positivity)
  have hregroup (i : Fin 2) :
      ((directionalSplits (I ++ J)).map fun split =>
        directionalJet split.1 (fun z => B z i) (t, x) •
          directionalJet split.2
            (fun z => fderiv ℝ U z (0, coordinateVector 2 i)) (t, x)).sum =
      ((directionalSplits I).map fun p =>
        ((directionalSplits J).map fun q => product i p q).sum).sum := by
    simpa [product] using directionalSplits_append_sum I J
      (fun split => directionalJet split.1 (fun z => B z i) (t, x) •
        directionalJet split.2
          (fun z => fderiv ℝ U z (0, coordinateVector 2 i)) (t, x))
  have hsumEq :
      (∑ i : Fin 2,
        ((directionalSplits (I ++ J)).map fun split =>
          directionalJet split.1 (fun z => B z i) (t, x) •
            directionalJet split.2
              (fun z => fderiv ℝ U z (0, coordinateVector 2 i)) (t, x)).sum) =
      ∑ i : Fin 2,
        ((directionalSplits I).map fun p =>
          ((directionalSplits J).map fun q => product i p q).sum).sum := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hregroup i
  have hEq := congrFun (transportTimeMixedEquation m L hY hb hg) (t, x)
  have hEq' :
      directionalJet (I ++ J) (jointTimeDerivative U) (t, x) =
        directionalJet (I ++ J) G (t, x) -
          ∑ i : Fin 2,
            ((directionalSplits (I ++ J)).map fun split =>
              directionalJet split.1 (fun z => B z i) (t, x) •
                directionalJet split.2
                  (fun z => fderiv ℝ U z (0, coordinateVector 2 i)) (t, x)).sum := by
    simpa [I, J, B, G, U] using hEq
  rw [hsumEq] at hEq'
  have htime := TransportTimeAnalyticityEstimate.directionalJet_mixedTime_successor m L U
      hY.smooth (t, x)
  have hpoint :
      directionalJet (transportTimeDirections (m + 1) ++ J) U (t, x) =
        directionalJet (I ++ J) G (t, x) -
          ∑ i : Fin 2,
            ((directionalSplits I).map fun p =>
              ((directionalSplits J).map fun q => product i p q).sum).sum := by
    rw [← htime]
    exact hEq'
  calc
    _ = ‖directionalJet (I ++ J) G (t, x) -
        ∑ i : Fin 2,
          ((directionalSplits I).map fun p =>
            ((directionalSplits J).map fun q => product i p q).sum).sum‖ :=
          congrArg norm hpoint
    _ ≤ ‖directionalJet (I ++ J) G (t, x)‖ +
        ‖∑ i : Fin 2,
          ((directionalSplits I).map fun p =>
            ((directionalSplits J).map fun q => product i p q).sum).sum‖ :=
          norm_sub_le _ _
    _ ≤ _ := add_le_add hsource hadv

theorem TransportTimeAnalyticityEstimate.transportTime_scalarKernels_sum {m n : ℕ} :
    (∑ j ∈ Finset.range (m + 1),
      ∑ k ∈ Finset.range (n + 1), TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j
          k) =
      (((n + 1 : ℝ) ^ 2 / (m + 1 : ℝ)) *
        (∑ j ∈ Finset.range (m + 1),
          ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k)) := by
  have hterm (j k : ℕ) : TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j k =
      ((n + 1 : ℝ) ^ 2 / (m + 1 : ℝ)) *
        TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k := by
    dsimp [TransportTimeAnalyticityEstimate.transportTimeScalarKernel,
        TransportTimeAnalyticityEstimate.transportTimeFactorialKernel]
    have hn : 0 < (((n - k + 1 : ℕ) : ℝ) ^ 2 * (k + 2 : ℝ) ^ 2) := by
      positivity
    have hm : 0 < (m + 1 : ℝ) := by positivity
    field_simp [hn.ne', hm.ne']
  calc
    _ = ∑ j ∈ Finset.range (m + 1),
        ∑ k ∈ Finset.range (n + 1),
          ((n + 1 : ℝ) ^ 2 / (m + 1 : ℝ)) *
            TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k := by
              apply Finset.sum_congr rfl
              intro j hj
              apply Finset.sum_congr rfl
              intro k hk
              exact hterm j k
    _ = _ := by
          calc
            _ = ∑ j ∈ Finset.range (m + 1),
                (((n + 1 : ℝ) ^ 2 / (m + 1 : ℝ)) *
                  ∑ k ∈ Finset.range (n + 1),
                    TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      rw [Finset.mul_sum]
            _ = ((n + 1 : ℝ) ^ 2 / (m + 1 : ℝ)) *
                  (∑ j ∈ Finset.range (m + 1),
                    ∑ k ∈ Finset.range (n + 1),
                      TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := by
                      rw [Finset.mul_sum]

theorem TransportTimeAnalyticityEstimate.transportTime_mixedJet_sharp_bound
    {m n N M : ℕ} (L : List (Fin 2)) (hL : L.length = n)
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {C_f C_g Q_f Q_g R A Q ρ : ℝ}
    (hmM : m ≤ M) (hnN : n ≤ N) (hmnN : m + n + 1 ≤ N)
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hρR : ρ ≤ 2 * R)
    (hQf : 0 ≤ Q_f) (hQfQ : Q_f ≤ Q) (hQg : 0 ≤ Q_g) (hQgQ : Q_g ≤ Q)
    (hQ1 : C_f * R ≤ Q) (hQ2 : 16 * (2 : ℝ) * C_f * R ≤ Q)
    (hA0 : 0 ≤ A) (hAeq : A = 2 * C_g / (C_f * R))
    (hB : ∀ t u v, u ≤ M → v ≤ N →
      snorm (transportTimeDerivative u (Function.uncurry b) t) v R ≤
        ENNReal.ofReal (C_f * Q_f ^ u * u.factorial))
    (hG : ∀ t, m ≤ M → n ≤ N →
      snorm (transportTimeDerivative m (Function.uncurry g) t) n R ≤
        ENNReal.ofReal (C_g * Q_g ^ m * m.factorial))
    (t : ℝ)
    (hYlower : ∀ j k, j ≤ m → j + (k + 1) ≤ N →
      snorm (transportTimeDerivative j (Function.uncurry Y) t) (k + 1) ρ ≤
        ENNReal.ofReal
          (A * (((k + 1 + j).factorial : ℝ) * j.factorial /
            (k + 1).factorial) * Q ^ j))
    (x : Vec 2) :
    ‖directionalJet (transportTimeDirections (m + 1) ++
        transportCoordinateDirections L) (Function.uncurry Y) (t, x)‖ ≤
      (A * ((((n + m + 1).factorial : ℝ) * (m + 1).factorial) /
        n.factorial) * Q ^ (m + 1)) *
        (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) := by
  let S : ℝ := ((m + 1).factorial : ℝ) * Q ^ (m + 1) *
    (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2)
  let H : ℝ := ((n + m + 1).factorial : ℝ) / n.factorial
  let K : ℝ := A * ((((n + m + 1).factorial : ℝ) * (m + 1).factorial) /
    n.factorial) * Q ^ (m + 1)
  have hQpos : 0 < Q := lt_of_lt_of_le (mul_pos hCf hR) hQ1
  have hS : 0 ≤ S := by
    dsimp [S]
    apply mul_nonneg
    · exact mul_nonneg (by positivity) (pow_nonneg hQpos.le _)
    · exact div_nonneg
        (mul_nonneg (by positivity) (pow_nonneg hρ.le _)) (sq_nonneg _)
  have hfac : ((m + 1).factorial : ℝ) = (m + 1 : ℝ) * m.factorial := by
    exact_mod_cast Nat.factorial_succ m
  have hmp : 0 < (m + 1 : ℝ) := by positivity
  have hnp : 0 < (n + 1 : ℝ) := by positivity
  have hden : (n + 1 : ℝ) ^ 2 ≠ 0 := by positivity
  have hsourceScale :
      C_g * Q_g ^ m * m.factorial * n.factorial * ρ ^ n /
          (n + 1 : ℝ) ^ 2 =
        S * (C_g * Q_g ^ m * m.factorial /
          ((m + 1).factorial * Q ^ (m + 1))) := by
    dsimp [S]
    field_simp [hQpos.ne', Nat.factorial_ne_zero]
  have hkernelSum := TransportTimeAnalyticityEstimate.transportTime_scalarKernels_sum (m := m) (n
      := n)
  have hadvScale :
      2 * C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) =
        S * (2 * C_f * A * ρ / Q *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j k)) := by
    rw [hkernelSum]
    dsimp [S]
    rw [hfac]
    field_simp [hQpos.ne', hmp.ne', hden]
    ring
  have hbudget := transportTimeAnalytic_scalar_budget (m := m) (n := n)
    hCf hCg hR hRρ hρR hQg hQgQ hQ1 hQ2
  have hbudget' :
      C_g * Q_g ^ m * m.factorial /
          ((m + 1).factorial * Q ^ (m + 1)) +
        2 * C_f * A * ρ / Q *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j k) ≤ A * H := by
    simpa [H, TransportTimeAnalyticityEstimate.transportTimeScalarKernel, hAeq] using hbudget
  have htotal :
      C_g * Q_g ^ m * m.factorial * n.factorial * ρ ^ n /
          (n + 1 : ℝ) ^ 2 +
        2 * C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) =
        S * (C_g * Q_g ^ m * m.factorial /
            ((m + 1).factorial * Q ^ (m + 1)) +
          2 * C_f * A * ρ / Q *
            (∑ j ∈ Finset.range (m + 1),
              ∑ k ∈ Finset.range (n + 1),
                TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j k)) := by
    rw [hsourceScale, hadvScale]
    ring
  have htargetEq : S * (A * H) = K *
      (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) := by
    dsimp [S, H, K]
    have hnfac : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp [hnfac]
  have hpoint := TransportTimeAnalyticityEstimate.transportTime_mixedJet_pointwise_bound L hL hY
      hb hg
    hmM hnN hmnN hCf hCg hR hρ hRρ hQf hQfQ hQpos hQg hA0 hB hG t hYlower x
  calc
    _ ≤ C_g * Q_g ^ m * m.factorial * n.factorial * ρ ^ n /
          (n + 1 : ℝ) ^ 2 +
        2 * C_f * A * m.factorial * n.factorial * Q ^ m * ρ ^ (n + 1) *
          (∑ j ∈ Finset.range (m + 1),
            ∑ k ∈ Finset.range (n + 1),
              TransportTimeAnalyticityEstimate.transportTimeFactorialKernel n j k) := hpoint
    _ = S * (C_g * Q_g ^ m * m.factorial /
            ((m + 1).factorial * Q ^ (m + 1)) +
          2 * C_f * A * ρ / Q *
            (∑ j ∈ Finset.range (m + 1),
              ∑ k ∈ Finset.range (n + 1),
                TransportTimeAnalyticityEstimate.transportTimeScalarKernel m n j k)) := htotal
    _ ≤ S * (A * H) := mul_le_mul_of_nonneg_left hbudget' hS
    _ = _ := htargetEq

theorem TransportTimeAnalyticityEstimate.transportTime_snorm_step
    {m n N M : ℕ}
    {b g Y : ℝ → Vec 2 → Vec 2}
    (hY : IsClassicalTransportSolution b g Y)
    (hb : ContDiff ℝ ∞ (Function.uncurry b))
    (hg : ContDiff ℝ ∞ (Function.uncurry g))
    {C_f C_g Q_f Q_g R A Q ρ : ℝ}
    (hmM : m ≤ M) (hnN : n ≤ N) (hmnN : m + n + 1 ≤ N)
    (hCf : 0 < C_f) (hCg : 0 ≤ C_g) (hR : 0 < R)
    (hρ : 0 < ρ) (hRρ : R ≤ ρ) (hρR : ρ ≤ 2 * R)
    (hQf : 0 ≤ Q_f) (hQfQ : Q_f ≤ Q) (hQg : 0 ≤ Q_g) (hQgQ : Q_g ≤ Q)
    (hQ1 : C_f * R ≤ Q) (hQ2 : 16 * (2 : ℝ) * C_f * R ≤ Q)
    (hA0 : 0 ≤ A) (hAeq : A = 2 * C_g / (C_f * R))
    (hB : ∀ t u v, u ≤ M → v ≤ N →
      snorm (transportTimeDerivative u (Function.uncurry b) t) v R ≤
        ENNReal.ofReal (C_f * Q_f ^ u * u.factorial))
    (hG : ∀ t, m ≤ M → n ≤ N →
      snorm (transportTimeDerivative m (Function.uncurry g) t) n R ≤
        ENNReal.ofReal (C_g * Q_g ^ m * m.factorial))
    (t : ℝ)
    (hYlower : ∀ j k, j ≤ m → j + (k + 1) ≤ N →
      snorm (transportTimeDerivative j (Function.uncurry Y) t) (k + 1) ρ ≤
        ENNReal.ofReal
          (A * (((k + 1 + j).factorial : ℝ) * j.factorial /
            (k + 1).factorial) * Q ^ j)) :
    snorm (transportTimeDerivative (m + 1) (Function.uncurry Y) t) n ρ ≤
      ENNReal.ofReal
        (A * ((((n + m + 1).factorial : ℝ) * (m + 1).factorial) /
          n.factorial) * Q ^ (m + 1)) := by
  let K : ℝ := A * ((((n + m + 1).factorial : ℝ) * (m + 1).factorial) /
    n.factorial) * Q ^ (m + 1)
  have hpoint (I : Fin n → Fin 2) (x : Vec 2) :
      ‖orderedPartial n (transportTimeDerivative (m + 1)
          (Function.uncurry Y) t) x I‖ ≤
        K * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2) := by
    let L := List.ofFn I
    have hL : L.length = n := by simp [L]
    have hjet := TransportTimeAnalyticityEstimate.transportTime_mixedJet_sharp_bound L hL hY hb hg
      hmM hnN hmnN hCf hCg hR hρ hRρ hρR hQf hQfQ hQg hQgQ hQ1 hQ2
      hA0 hAeq hB hG t hYlower x
    have hpartial := orderedPartial_timeDerivative_eq_coordinateListJet
      (m + 1) I (Function.uncurry Y) hY.smooth t x
    simpa [K, L, hpartial] using hjet
  have hD : derivativeSup n (transportTimeDerivative (m + 1)
      (Function.uncurry Y) t) ≤
      ENNReal.ofReal (K * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2)) := by
    unfold derivativeSup
    apply iSup_le
    intro I
    unfold partialSup
    exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (hpoint I))
  have hD' : derivativeSup n (transportTimeDerivative (m + 1)
      (Function.uncurry Y) t) ≤
      ENNReal.ofReal (K * ρ ^ n * n.factorial / (n + 1 : ℝ) ^ 2) := by
    calc
      _ ≤ ENNReal.ofReal (K * (n.factorial * ρ ^ n / (n + 1 : ℝ) ^ 2)) := hD
      _ = ENNReal.ofReal (K * ρ ^ n * n.factorial /
          (n + 1 : ℝ) ^ 2) := by
            congr 1
            ring
  exact snorm_le_of_derivativeSup_le _ hρ hD'

end FaaDiBruno

end AVenhance
