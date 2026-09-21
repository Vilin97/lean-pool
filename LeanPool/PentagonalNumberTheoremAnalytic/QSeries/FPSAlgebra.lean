/-
Copyright (c) 2026 Jonathan Conrad, Paula Muermann, Maryna Viazovska. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Conrad, Paula Muermann, Maryna Viazovska
-/
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FPSEuler
import LeanPool.PentagonalNumberTheoremAnalytic.QSeries.FiniteBinomial

/-!
# Algebraic identities for FPS q-series

Purely algebraic proofs of the **Euler second identity** and the **key identity**
`S_k = (qPochhammerInf X)⁻¹` in the formal power series ring `R⟦X⟧` over any
commutative ring with discrete topology. Combined with the product expansion
and Cauchy product, these identities yield the Jacobi triple product.

## Main results

* `QSeries.FormalPowerSeries.euler_second_identity` — FPS Euler second identity.
* `QSeries.FormalPowerSeries.keySum_eq_qPochhammerInfInv` — `S_k = (qPochhammerInf X)⁻¹`
  for all `k`.
* `QSeries.FormalPowerSeries.hasSum_pow_choose_two_nonneg` — Cauchy diagonal coefficient
  for `n ≥ 0`.
* `QSeries.FormalPowerSeries.hasSum_pow_choose_two_neg` — Cauchy diagonal coefficient for `n < 0`.
* `QSeries.FormalPowerSeries.jacobiTripleProduct` — FPS Jacobi Triple Product Identity.
-/

noncomputable section

open scoped MvPowerSeries.WithPiTopology
open PowerSeries Finset

namespace QSeries.FormalPowerSeries

variable {R : Type*} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]


/-- Inverse of `qPochhammer X k` in `R⟦X⟧`, defined via `invOfUnit` since the
constant coefficient is `1`. -/
def qPochhammerInv (k : ℕ) : R⟦X⟧ :=
  MvPowerSeries.invOfUnit (qPochhammer (X : R⟦X⟧) k) 1

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammer X k` times its formal power series inverse equals 1. -/
@[simp]
theorem qPochhammer_X_mul_qPochhammerInv (k : ℕ) :
    qPochhammer (X : R⟦X⟧) k * qPochhammerInv (R := R) k = 1 :=
  PowerSeries.mul_invOfUnit _ 1 (by simpa using constantCoeff_qPochhammer_X (R := R) k)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The formal power series inverse of `qPochhammer X k` times `qPochhammer X k` equals 1. -/
@[simp]
theorem qPochhammerInv_mul_qPochhammer_X (k : ℕ) :
    qPochhammerInv (R := R) k * qPochhammer (X : R⟦X⟧) k = 1 := by
  rw [mul_comm, qPochhammer_X_mul_qPochhammerInv]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- The recursion `(1 - X^{k+1}) * qPochhammerInv(k+1) = qPochhammerInv(k)` for the inverse
q-Pochhammer symbol. -/
theorem one_sub_pow_mul_qPochhammerInv_succ (k : ℕ) :
    (1 - (X : R⟦X⟧) ^ (k + 1)) * qPochhammerInv (R := R) (k + 1) = qPochhammerInv k := by
  have h1 := qPochhammer_X_mul_qPochhammerInv (R := R) (k + 1)
  rw [qPochhammer_succ, ← pow_succ'] at h1
  refine (isUnit_qPochhammer_X (R := R) k).mul_left_cancel ?_
  rw [qPochhammer_X_mul_qPochhammerInv, ← mul_assoc, h1]

/-- `qPochhammerInf X` is a unit. -/
theorem isUnit_qPochhammerInf_X : IsUnit (qPochhammerInf (X : R⟦X⟧)) :=
  isUnit_qPochhammerInf X (by simp)

/-- Inverse of `qPochhammerInf X`. -/
def qPochhammerInfInv : R⟦X⟧ := ↑(isUnit_qPochhammerInf_X (R := R)).unit⁻¹

/-- `qPochhammerInf X` times its formal power series inverse equals 1. -/
@[simp]
theorem qPochhammerInf_X_mul_qPochhammerInfInv :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInfInv (R := R) = 1 :=
  isUnit_qPochhammerInf_X.mul_val_inv

/-- The formal power series inverse of `qPochhammerInf X` times `qPochhammerInf X` equals 1. -/
@[simp]
theorem qPochhammerInfInv_mul_qPochhammerInf_X :
    qPochhammerInfInv (R := R) * qPochhammerInf (X : R⟦X⟧) = 1 :=
  isUnit_qPochhammerInf_X.val_inv_mul

/-- `qPochhammerInf X * qPochhammerInv n = qPochhammerInf (X * X^n)`: multiplying the infinite
product by the `n`-th inverse Pochhammer symbol shifts the argument. -/
theorem qPochhammerInf_X_mul_qPochhammerInv (n : ℕ) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInv (R := R) n = qPochhammerInf (X * X ^ n) := by
  rw [qPochhammerInf_X_eq_qPochhammer_mul n, mul_right_comm, qPochhammer_X_mul_qPochhammerInv,
    one_mul]

section Euler2

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Every finite q-Pochhammer product is `1` plus a multiple of its argument:
`(a; X)_k = 1 + a * g` for some `g`. -/
private theorem exists_qPochhammer_eq_one_add_mul (a : R⟦X⟧) (k : ℕ) :
    ∃ g : R⟦X⟧, qPochhammer a k = 1 + a * g := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨g, hg⟩ := ih
    exact ⟨g - X ^ k - a * g * X ^ k, by rw [qPochhammer_succ, hg]; ring⟩

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j ≤ m` the `j`-th coefficient of `(X·X^m; X)_k` agrees with that of `1`. -/
private theorem coeff_qPochhammer_X_mul_pow (m k : ℕ) {j : ℕ} (hj : j < m + 1) :
    PowerSeries.coeff j (qPochhammer ((X : R⟦X⟧) * X ^ m) k) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := exists_qPochhammer_eq_one_add_mul ((X : R⟦X⟧) * X ^ m) k
  rw [hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul', ite_eq_right hj.not_ge, add_zero]

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Telescoping split `(X; X)_n = (X; X)_{n-k} · (X·X^{n-k}; X)_k` for `k ≤ n`. -/
private theorem qPochhammer_X_eq_qPochhammer_mul {k n : ℕ} (hkn : k ≤ n) :
    qPochhammer (X : R⟦X⟧) n =
      qPochhammer (X : R⟦X⟧) (n - k) * qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
  conv_lhs => rw [show n = n - k + k from (Nat.sub_add_cancel hkn).symm]
  rw [qPochhammer, qPochhammer, qPochhammer, Finset.prod_range_add]
  exact congrArg _ (Finset.prod_congr rfl fun i _ => by ring)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Two power series agreeing in all coefficients below `N` still agree there after
multiplication by a common factor. -/
private theorem coeff_mul_congr {f g b : R⟦X⟧} {N j : ℕ} (hj : j < N)
    (h : ∀ i < N, PowerSeries.coeff i f = PowerSeries.coeff i g) :
    PowerSeries.coeff j (f * b) = PowerSeries.coeff j (g * b) := by
  have hd : (X : R⟦X⟧) ^ N ∣ f - g :=
    PowerSeries.X_pow_dvd_iff.mpr fun i hi => by rw [map_sub, h i hi, sub_self]
  have hj0 := PowerSeries.X_pow_dvd_iff.mp (hd.mul_right b) j hj
  rwa [sub_mul, map_sub, sub_eq_zero] at hj0



omit [TopologicalSpace R] [DiscreteTopology R] in
/-- For `j + k ≤ n`, the `j`-th coefficient of `qBinom n k X` equals that of `qPochhammerInv k`. -/
theorem coeff_qBinom_eq_coeff_qPochhammerInv {k j n : ℕ} (hjk : j + k ≤ n) :
    PowerSeries.coeff j (QSeries.qBinom n k (X : R⟦X⟧)) =
    PowerSeries.coeff j (qPochhammerInv (R := R) k) := by
  have hkn : k ≤ n := by omega
  have h_eq : QSeries.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k *
      qPochhammer (X : R⟦X⟧) (n - k) = qPochhammer (X : R⟦X⟧) n :=
    QSeries.qBinom_mul_qPochhammer_mul_qPochhammer (X : R⟦X⟧) hkn
  have hcancel : QSeries.qBinom n k (X : R⟦X⟧) * qPochhammer (X : R⟦X⟧) k
      = qPochhammer ((X : R⟦X⟧) * X ^ (n - k)) k := by
    refine (isUnit_qPochhammer_X (R := R) (n - k)).mul_right_cancel ?_
    rw [h_eq, qPochhammer_X_eq_qPochhammer_mul hkn]
    exact mul_comm _ _
  have hdvd : (X : R⟦X⟧) ^ (n - k + 1) ∣
      QSeries.qBinom n k (X : R⟦X⟧) - qPochhammerInv (R := R) k := by
    refine (IsUnit.dvd_mul_right (isUnit_qPochhammer_X (R := R) k)).mp ?_
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [sub_mul, hcancel, qPochhammerInv_mul_qPochhammer_X, map_sub,
      coeff_qPochhammer_X_mul_pow _ _ hm, sub_self]
  rw [← sub_eq_zero, ← map_sub]
  exact PowerSeries.X_pow_dvd_iff.mp hdvd j (by omega)

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem qPochhammer_neg_eq_sum (a : R⟦X⟧) (n : ℕ) :
    qPochhammer (-a) n = ∑ k ∈ Finset.range (n + 1),
      X ^ k.choose 2 * QSeries.qBinom n k (X : R⟦X⟧) * a ^ k := by
  rw [qPochhammer, ← QSeries.prod_one_add_mul_pow_eq_sum_qBinom (X : R⟦X⟧) a n]
  exact Finset.prod_congr rfl fun _ _ => by ring

omit [TopologicalSpace R] [DiscreteTopology R] in
private theorem coeff_eq_zero_of_lt_choose_two (a : R⟦X⟧) (d k : ℕ) (hk : d < k.choose 2) :
    PowerSeries.coeff d (X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) = 0 := by
  rw [mul_assoc, PowerSeries.coeff_X_pow_mul', ite_eq_right hk.not_ge]

omit [DiscreteTopology R] in
/-- The Euler-second summands `X^{C(k,2)} · a^k · (X; X)_k⁻¹` form a summable family. -/
private theorem summable_pow_choose_two_mul_pow_mul_qPochhammerInv (a : R⟦X⟧) :
    Summable fun k : ℕ => (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  refine (WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  refine summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun k hk => ?_
  exact coeff_eq_zero_of_lt_choose_two a d k (Nat.lt_choose_two_of_add_two_le (by simpa using hk))

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Termwise agreement, in degree `n`, between the finite q-binomial expansion of
`(-a; X)_{n+1}` and the Euler-second summands. -/
private theorem coeff_pow_choose_two_mul_qBinom_mul_pow (a : R⟦X⟧) (n k : ℕ) :
    PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * QSeries.qBinom (n + 1) k X * a ^ k) =
      PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) := by
  rw [mul_assoc, show (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k
      = X ^ k.choose 2 * (qPochhammerInv (R := R) k * a ^ k) from by ring,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · refine coeff_mul_congr (N := n - k.choose 2 + 1) (by omega) fun i hi => ?_
    exact coeff_qBinom_eq_coeff_qPochhammerInv (by have := Nat.le_choose_two_add_one k; omega)
  · rfl

/-- FPS Euler second identity: `qPochhammerInf(-a) = Σ_{k≥0} X^{C(k,2)} · a^k · (qPochhammer X k)⁻¹`
in `R⟦X⟧`. -/
theorem euler_second_identity (a : R⟦X⟧) :
    qPochhammerInf (-a) = ∑' k : ℕ, X ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k := by
  ext n
  have hcoeff :
      ∑' k : ℕ, PowerSeries.coeff n ((X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k)
        = PowerSeries.coeff n
            (∑' k : ℕ, (X : R⟦X⟧) ^ k.choose 2 * a ^ k * qPochhammerInv (R := R) k) :=
    ((summable_pow_choose_two_mul_pow_mul_qPochhammerInv a).hasSum.map
      (PowerSeries.coeff n).toAddMonoidHom (WithPiTopology.continuous_coeff R n)).tsum_eq
  rw [coeff_qPochhammerInf, qPochhammer_neg_eq_sum, ← hcoeff,
    tsum_eq_sum (s := Finset.range (n + 2)) fun k hk =>
      coeff_eq_zero_of_lt_choose_two a n k (Nat.lt_choose_two_of_add_two_le (by simpa using hk)),
    map_sum]
  exact Finset.sum_congr rfl fun k _ => coeff_pow_choose_two_mul_qBinom_mul_pow a n k

end Euler2


section KeyIdentity

omit [DiscreteTopology R] in
/-- A family `m ↦ X ^ e m * g m` in `R⟦X⟧` is summable as soon as the exponents `e m`
eventually exceed every fixed degree: only finitely many terms contribute to each
coefficient. -/
private theorem summable_X_pow_mul {e : ℕ → ℕ}
    (he : ∀ d : ℕ, ∃ N : ℕ, ∀ m ≥ N, d < e m) (g : ℕ → R⟦X⟧) :
    Summable fun m : ℕ => (X : R⟦X⟧) ^ e m * g m := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff R).mpr fun d => ?_
  obtain ⟨N, hN⟩ := he d
  refine summable_of_ne_finset_zero (s := Finset.range N) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  rw [PowerSeries.coeff_X_pow_mul', ite_eq_right (by have := hN m hm; omega)]

/-- The exponents `m * (m + k)` eventually exceed every fixed degree. -/
private theorem exists_forall_lt_mul (k d : ℕ) : ∃ N : ℕ, ∀ m ≥ N, d < m * (m + k) :=
  ⟨d + 1, fun m hm => lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right m (by omega))⟩

/-- The exponents `C(m, 2)` eventually exceed every fixed degree. -/
private theorem exists_forall_lt_choose_two (d : ℕ) :
    ∃ N : ℕ, ∀ m ≥ N, d < m.choose 2 := by
  refine ⟨d + 2, fun m hm => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_two_succ]
  omega

/-- The key sum `S_k = ∑_m X^{m(m+k)} / ((X;X)_m (X;X)_{m+k})`. -/
def keySum (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)

omit [DiscreteTopology R] in
/-- The defining series for `keySum k` is summable in `R⟦X⟧`. -/
theorem summable_keySummand (k : ℕ) :
    Summable (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k)) := by
  simpa [mul_assoc] using summable_X_pow_mul (R := R)
    (exists_forall_lt_mul k) fun m => qPochhammerInv m * qPochhammerInv (m + k)

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- Key auxiliary: `qPochhammerInv(n-1) + X^n * qPochhammerInv(n) = qPochhammerInv(n)`.
    Equivalently,
    `(1 - X^{n+1}) * qPochhammerInv(n+1) + X^{n+1} * qPochhammerInv(n+1) = qPochhammerInv(n+1)`. -/
private theorem qPochhammerInv_add_pow_mul_qPochhammerInv_succ (n : ℕ) :
    qPochhammerInv (R := R) n + X ^ (n + 1) * qPochhammerInv (R := R) (n + 1) =
    qPochhammerInv (R := R) (n + 1) := by
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) n]; ring

/-- The intermediate sum `T_k = ∑ m, X^{m(m+k)} * qPochhammerInv(m) * qPochhammerInv(m+k+1)`. -/
private def keySumShift (k : ℕ) : R⟦X⟧ :=
  ∑' m : ℕ, X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k + 1)


private theorem keySumShift_eq_keySum_add (k : ℕ) :
    keySumShift (R := R) k = keySum k + X ^ (k + 1) * keySum (k + 1) := by
  unfold keySumShift keySum
  rw [← Summable.tsum_mul_left _ (summable_keySummand (R := R) (k + 1)),
    ← Summable.tsum_add (summable_keySummand (R := R) k)
      (Summable.mul_left _ (summable_keySummand (R := R) (k + 1)))]
  refine tsum_congr fun m => ?_
  simp only [← add_assoc]
  have hpow : (X : R⟦X⟧) ^ (k + 1) * X ^ (m * (m + k + 1)) =
      X ^ (m + k + 1) * X ^ (m * (m + k)) := by
    rw [← pow_add, ← pow_add]; congr 1; ring
  rw [← one_sub_pow_mul_qPochhammerInv_succ (R := R) (m + k), ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)),
    ← mul_assoc ((X : R⟦X⟧) ^ (k + 1)), hpow]
  generalize (X : R⟦X⟧) ^ (m * (m + k)) = A
  ring

/-- The shifted form of `X^{k+1} · S_{k+2}` as a `HasSum` statement. -/
private theorem hasSum_pow_mul_keySum (k : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n * qPochhammerInv (n + k + 2))
      (X ^ (k + 1) * keySum (R := R) (k + 2)) := by
  have hfun : (fun n : ℕ => (X : R⟦X⟧) ^ (k + 1) *
      (X ^ (n * (n + (k + 2))) * qPochhammerInv (R := R) n * qPochhammerInv (n + (k + 2)))) =
      fun n : ℕ => X ^ ((n + 1) * (n + 1 + k)) * qPochhammerInv (R := R) n *
        qPochhammerInv (n + k + 2) := by
    funext n
    rw [show n + (k + 2) = n + k + 2 from by omega,
      show (n + 1) * (n + 1 + k) = k + 1 + n * (n + k + 2) from by ring, pow_add]
    ring
  exact hfun ▸ (summable_keySummand (R := R) (k + 2)).hasSum.mul_left _


private theorem keySumShift_eq_keySum_succ_add (k : ℕ) :
    keySumShift (R := R) k = keySum (k + 1) + X ^ (k + 1) * keySum (k + 2) := by
  have hA := (hasSum_nat_add_iff' (f := fun m : ℕ =>
    X ^ (m * (m + (k + 1))) * qPochhammerInv (R := R) m * qPochhammerInv (m + (k + 1))) 1).mpr
      (summable_keySummand (R := R) (k + 1)).hasSum
  refine HasSum.tsum_eq ((hasSum_nat_add_iff' 1).mp ?_)
  convert hA.add (hasSum_pow_mul_keySum (R := R) k) using 1
  · funext n
    rw [show n + 1 + k + 1 = n + k + 2 from by omega,
      show n + 1 + (k + 1) = n + k + 2 from by omega,
      show (n + 1) * (n + k + 2) = (n + 1) * (n + 1 + k) + (n + 1) from by ring, pow_add]
    conv_lhs => rw [← qPochhammerInv_add_pow_mul_qPochhammerInv_succ (R := R) n]
    ring
  · simp only [keySum, Finset.sum_range_one, Nat.zero_mul, Nat.zero_add, pow_zero, one_mul]
    ring

/-- The recurrence: `S_k − S_{k+1} = X^{k+1} (S_{k+2} − S_{k+1})`. -/
theorem keySum_sub_keySum_succ (k : ℕ) :
    keySum (R := R) k - keySum (k + 1) =
    X ^ (k + 1) * (keySum (R := R) (k + 2) - keySum (k + 1)) := by
  have h := (keySumShift_eq_keySum_add (R := R) k).symm.trans (keySumShift_eq_keySum_succ_add k)
  rw [mul_sub, sub_eq_sub_iff_add_eq_add]
  exact h.trans (add_comm _ _)

/-- `keySum k` is independent of `k`: all values are equal to `keySum 0`. -/
theorem keySum_eq_keySum_zero (k : ℕ) : keySum (R := R) k = keySum 0 := by
  -- `S_j - S_{j+1}` is divisible by `X ^ N` for every `N`, hence zero.
  have key : ∀ N j : ℕ, ∃ g : R⟦X⟧, keySum (R := R) j - keySum (j + 1) = X ^ N * g := by
    intro N
    induction N with
    | zero => exact fun j => ⟨_, (one_mul _).symm⟩
    | succ N ih =>
      intro j
      obtain ⟨g, hg⟩ := ih (j + 1)
      refine ⟨-(X ^ j * g), ?_⟩
      rw [keySum_sub_keySum_succ j, ← neg_sub (keySum (R := R) (j + 1)), hg]
      ring
  have hzero : ∀ j : ℕ, keySum (R := R) j = keySum (j + 1) := by
    intro j
    rw [← sub_eq_zero]
    ext d
    obtain ⟨g, hg⟩ := key (d + 1) j
    rw [hg, PowerSeries.coeff_X_pow_mul', ite_eq_right (by omega), map_zero]
  induction k with
  | zero => rfl
  | succ k ih => rw [← hzero k, ih]

/-- Below degree `k + 1` the series `(X·X^k; X)_∞` is indistinguishable from `1`. -/
private theorem coeff_qPochhammerInf_X_mul_pow {k j : ℕ} (hj : j < k + 1) :
    PowerSeries.coeff j (qPochhammerInf ((X : R⟦X⟧) * X ^ k)) = PowerSeries.coeff j 1 := by
  obtain ⟨g, hg⟩ := exists_qPochhammer_eq_one_add_mul ((X : R⟦X⟧) * X ^ k) (j + 1)
  rw [coeff_qPochhammerInf, hg, map_add, ← pow_succ', PowerSeries.coeff_X_pow_mul',
    ite_eq_right hj.not_ge, add_zero]

/-- For `d < k`, the `d`-th coefficient of `qPochhammerInv k` equals the `d`-th coefficient
of `qPochhammerInfInv`. -/
theorem coeff_qPochhammerInv_eq_coeff_qPochhammerInfInv {k d : ℕ} (hkd : d < k) :
    PowerSeries.coeff d (qPochhammerInv (R := R) k) =
      PowerSeries.coeff d (qPochhammerInfInv (R := R)) := by
  have hQ : ∀ j < k, PowerSeries.coeff j (qPochhammerInf (X : R⟦X⟧) *
      (qPochhammerInv (R := R) k - qPochhammerInfInv (R := R))) = 0 := fun j hj => by
    rw [mul_sub, qPochhammerInf_X_mul_qPochhammerInv, qPochhammerInf_X_mul_qPochhammerInfInv,
      map_sub, sub_eq_zero, coeff_qPochhammerInf_X_mul_pow (by omega)]
  rw [← sub_eq_zero, ← map_sub, show qPochhammerInv (R := R) k - qPochhammerInfInv (R := R) =
    qPochhammerInfInv (R := R) * (qPochhammerInf (X : R⟦X⟧) *
      (qPochhammerInv (R := R) k - qPochhammerInfInv)) from by
        rw [← mul_assoc, qPochhammerInfInv_mul_qPochhammerInf_X, one_mul], PowerSeries.coeff_mul]
  exact Finset.sum_eq_zero fun p hp => by
    rw [hQ p.2 (by have := Finset.mem_antidiagonal.mp hp; omega), mul_zero]

/-- Taking the `d`-th coefficient commutes with a convergent `tsum` in `R⟦X⟧`. -/
private theorem coeff_tsum {f : ℕ → R⟦X⟧} (hf : Summable f) (d : ℕ) :
    PowerSeries.coeff d (∑' m, f m) = ∑' m, PowerSeries.coeff d (f m) :=
  ((hf.hasSum.map (PowerSeries.coeff d).toAddMonoidHom
    (WithPiTopology.continuous_coeff R d)).tsum_eq).symm

omit [TopologicalSpace R] [DiscreteTopology R] in
/-- `qPochhammerInv 0 = 1`. -/
private theorem qPochhammerInv_zero : qPochhammerInv (R := R) 0 = 1 := by
  simpa using qPochhammer_X_mul_qPochhammerInv (R := R) 0

/-- For `d < k`, the `d`-th coefficient of `keySum k` equals the `d`-th coefficient
of `qPochhammerInfInv`. -/
theorem coeff_keySum_eq_coeff_qPochhammerInfInv (k : ℕ) (d : ℕ) (hkd : d < k) :
    PowerSeries.coeff d (keySum (R := R) k) = PowerSeries.coeff d (qPochhammerInfInv (R := R)) := by
  rw [keySum, coeff_tsum (summable_keySummand k), tsum_eq_single 0 fun m hm => by
    rw [mul_assoc, PowerSeries.coeff_X_pow_mul',
      ite_eq_right (by have := Nat.pos_of_ne_zero hm; nlinarith)]]
  simpa [qPochhammerInv_zero] using coeff_qPochhammerInv_eq_coeff_qPochhammerInfInv (R := R) hkd

/-- **Key identity**: `S_k = (qPochhammerInf X)⁻¹` for all `k ≥ 0`. -/
theorem keySum_eq_qPochhammerInfInv (k : ℕ) : keySum (R := R) k = qPochhammerInfInv := by
  ext d
  rw [keySum_eq_keySum_zero k, ← keySum_eq_keySum_zero (R := R) (d + 1)]
  exact coeff_keySum_eq_coeff_qPochhammerInfInv (d + 1) d (Nat.lt_succ_self d)

end KeyIdentity


section Cauchy

/-- `qPochhammerInf X * qPochhammerInf(-a) = Σ_n X^{C(n,2)} a^n qPochhammerInf(X · X^n)`
in `R⟦X⟧`. -/
theorem qPochhammerInf_X_mul_qPochhammerInf_neg (a : R⟦X⟧) :
    qPochhammerInf (X : R⟦X⟧) * qPochhammerInf (-a) =
    ∑' n : ℕ, X ^ n.choose 2 * a ^ n * qPochhammerInf (X * X ^ n) := by
  have hs : Summable fun n : ℕ => X ^ n.choose 2 * a ^ n * qPochhammerInv (R := R) n := by
    simpa [mul_assoc] using summable_X_pow_mul (R := R)
      exists_forall_lt_choose_two fun n => a ^ n * qPochhammerInv n
  rw [euler_second_identity a, ← Summable.tsum_mul_left _ hs]
  exact tsum_congr fun n => by rw [← qPochhammerInf_X_mul_qPochhammerInv n]; ring

/-- The common core of the two Cauchy diagonal computations: after collecting the powers of `X`
the diagonal is `X ^ e` times the key sum `S_k`, and `S_k = qPochhammerInfInv` cancels
`qPochhammerInf X`. -/
private theorem hasSum_pow_mul_qPochhammerInf_mul_qPochhammerInv (k e : ℕ) :
    HasSum (fun m : ℕ => X ^ (e + m * (m + k)) * qPochhammerInf (X : R⟦X⟧) *
      qPochhammerInv (R := R) m * qPochhammerInv (m + k)) (X ^ e : R⟦X⟧) := by
  have h : HasSum (fun m : ℕ =>
      X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k))
      (qPochhammerInfInv (R := R)) := by
    rw [← keySum_eq_qPochhammerInfInv (R := R) k]
    exact (summable_keySummand k).hasSum
  have key := h.mul_left ((X : R⟦X⟧) ^ e * qPochhammerInf X)
  rw [mul_assoc, qPochhammerInf_X_mul_qPochhammerInfInv, mul_one] at key
  have hfun : (fun m : ℕ => (X : R⟦X⟧) ^ e * qPochhammerInf X *
      (X ^ (m * (m + k)) * qPochhammerInv (R := R) m * qPochhammerInv (m + k))) =
      fun m : ℕ => X ^ (e + m * (m + k)) * qPochhammerInf (X : R⟦X⟧) *
        qPochhammerInv (R := R) m * qPochhammerInv (m + k) := by
    funext m; rw [pow_add]; ring
  exact hfun ▸ key

/-- Cauchy diagonal coefficient for non-negative index `k`: the `(m+k, m)` diagonal of the
double series sums to `X^{C(k,2)}` in `R⟦X⟧`. -/
theorem hasSum_pow_choose_two_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      X ^ (m + k).choose 2 * qPochhammerInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochhammerInv (R := R) m))
      (X ^ k.choose 2 : R⟦X⟧) := by
  convert hasSum_pow_mul_qPochhammerInf_mul_qPochhammerInv (R := R) k (k.choose 2) using 1
  funext m
  rw [← qPochhammerInf_X_mul_qPochhammerInv (m + k), ← Nat.choose_two_add_choose_two m k]
  ring

/-- Cauchy diagonal coefficient for negative index `-(l+1)`: the `(n, n+l+1)` diagonal of the
double series sums to `X^{C(l+2,2)}` in `R⟦X⟧`. -/
theorem hasSum_pow_choose_two_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      X ^ n.choose 2 * qPochhammerInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) * qPochhammerInv (R := R) (n + (l + 1))))
      (X ^ (l + 2).choose 2 : R⟦X⟧) := by
  convert hasSum_pow_mul_qPochhammerInf_mul_qPochhammerInv (R := R) (l + 1)
    ((l + 2).choose 2) using 1
  funext n
  rw [← qPochhammerInf_X_mul_qPochhammerInv n, ← Nat.choose_two_add_choose_two' n l]
  ring

end Cauchy


section JTP

private theorem jacobiProd_eq_tsum_mul_tsum :
    @jacobiProd = (∑' n : ℕ, X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
              (∑' m : ℕ, X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m) := by
  convert congr_arg₂ (· * ·) (qPochhammerInf_X_mul_qPochhammerInf_neg laurentZ) _ using 1
  all_goals try rfl
  convert euler_second_identity (X * laurentZInv) using 1
  · exact tprod_congr fun _ => by ring
  · simp +decide [pow_add, mul_pow, mul_assoc, mul_comm, mul_left_comm]

open LaurentPolynomial in
/-- `z * zinv = 1` in `A⟦X⟧`. -/
private theorem laurentZ_mul_laurentZInv : laurentZ * laurentZInv = 1 := by
  rw [← map_mul, ← T_add]
  simp

open LaurentPolynomial in
/-- `z ^ n * zinv ^ n = 1` for all `n`. -/
private theorem laurentZ_pow_mul_laurentZInv_pow (n : ℕ) : laurentZ ^ n * laurentZInv ^ n = 1 := by
  rw [← mul_pow, laurentZ_mul_laurentZInv, one_pow]

open LaurentPolynomial in
/-- `z ^ n = PS (T n)` for natural `n`. -/
private theorem laurentZ_pow (n : ℕ) :
    laurentZ ^ n = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (n : ℤ)) := by
  rw [← map_pow]
  congr 1
  simp

open LaurentPolynomial in
/-- `zinv ^ (m + 1) = PS (T (-(↑m + 1)))`. -/
private theorem laurentZInv_pow (m : ℕ) :
    laurentZInv ^ (m + 1) = (PowerSeries.C : LaurentPolynomial ℂ →+* _) (T (-(↑m + 1))) := by
  rw [← map_pow]
  congr 1
  rw [T_pow]
  push_cast
  ring_nf

open LaurentPolynomial in
/-- Cancelling `zinv ^ m` against the first `m` factors of `z ^ (m + k)`. -/
private theorem laurentZ_pow_add_mul_laurentZInv_pow (m k : ℕ) :
    laurentZ ^ (m + k) * laurentZInv ^ m = laurentZ ^ k := by
  rw [pow_add, mul_right_comm, laurentZ_pow_mul_laurentZInv_pow, one_mul]

open LaurentPolynomial in
/-- Cancelling `z ^ n` against the first `n` factors of `zinv ^ (n + l)`. -/
private theorem laurentZInv_pow_add_mul_laurentZ_pow (n l : ℕ) :
    laurentZInv ^ (n + l) * laurentZ ^ n = laurentZInv ^ l := by
  rw [pow_add, mul_right_comm, mul_comm (laurentZInv ^ n) (laurentZ ^ n),
    laurentZ_pow_mul_laurentZInv_pow, one_mul]

open LaurentPolynomial in
/-- Non-negative diagonal of the Cauchy product: HasSum giving `z^k * X^{C(k,2)}`. -/
private theorem hasSum_diagonal_nonneg (k : ℕ) :
    HasSum (fun m : ℕ =>
      (X ^ (m + k).choose 2 * laurentZ ^ (m + k) * qPochhammerInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m))
      (laurentZ ^ k * X ^ k.choose 2) := by
  have key : ∀ m : ℕ,
      (X ^ (m + k).choose 2 * laurentZ ^ (m + k) * qPochhammerInf (X * X ^ (m + k))) *
      (X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv (R := LaurentPolynomial ℂ) m) =
      laurentZ ^ k * (X ^ (m + k).choose 2 * qPochhammerInf (X * X ^ (m + k)) *
      (X ^ m.choose 2 * X ^ m * qPochhammerInv m)) := fun m => by
    rw [← laurentZ_pow_add_mul_laurentZInv_pow m k]
    ring
  simp_rw [key]
  exact HasSum.mul_left _ (hasSum_pow_choose_two_nonneg k)

open LaurentPolynomial in
/-- Negative diagonal of the Cauchy product: HasSum giving `zinv^{l+1} * X^{C(l+2,2)}`. -/
private theorem hasSum_diagonal_neg (l : ℕ) :
    HasSum (fun n : ℕ =>
      (X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * laurentZInv ^ (n + (l + 1)) *
      qPochhammerInv (n + (l + 1))))
      (laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2) := by
  have key : ∀ n : ℕ, (X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)) *
      (X ^ ((n + (l + 1)).choose 2 + (n + (l + 1))) * laurentZInv ^ (n + (l + 1)) *
      qPochhammerInv (R := LaurentPolynomial ℂ) (n + (l + 1))) =
      laurentZInv ^ (l + 1) * (X ^ n.choose 2 * qPochhammerInf (X * X ^ n) *
      (X ^ (n + (l + 1)).choose 2 * X ^ (n + (l + 1)) *
        qPochhammerInv (n + (l + 1)))) := fun n => by
    rw [← laurentZInv_pow_add_mul_laurentZ_pow n (l + 1)]
    ring
  simp_rw [key]
  exact HasSum.mul_left _ (hasSum_pow_choose_two_neg l)

/-- The equivalence ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) splitting along the diagonal:
  (n, m) ↦ if m ≤ n then inl (n - m, m) else inr (m - n - 1, n). -/
private def diagonalEquiv : ℕ × ℕ ≃ (ℕ × ℕ) ⊕ (ℕ × ℕ) where
  toFun p := if p.2 ≤ p.1 then Sum.inl (p.1 - p.2, p.2) else Sum.inr (p.2 - p.1 - 1, p.1)
  invFun s := match s with
    | Sum.inl (k, m) => (m + k, m)
    | Sum.inr (l, n) => (n, n + l + 1)
  left_inv := by intro ⟨n, m⟩; simp only; split_ifs with h <;> simp <;> omega
  right_inv := by
    intro s
    rcases s with ⟨k, m⟩ | ⟨l, n⟩ <;> simp
    omega

open LaurentPolynomial in
private abbrev leftSummand (n : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ n.choose 2 * laurentZ ^ n * qPochhammerInf (X * X ^ n)

open LaurentPolynomial in
private abbrev rightSummand (m : ℕ) : (LaurentPolynomial ℂ)⟦X⟧ :=
  X ^ (m.choose 2 + m) * laurentZInv ^ m * qPochhammerInv m

open LaurentPolynomial in
/-- `leftSummand n` is divisible by `X ^ C(n, 2)`, so its lower coefficients vanish. -/
private theorem coeff_leftSummand_eq_zero {d n : ℕ} (h : d < n.choose 2) :
    PowerSeries.coeff d (leftSummand n) = 0 := by
  have hrw : leftSummand n = X ^ n.choose 2 * (laurentZ ^ n * qPochhammerInf (X * X ^ n)) := by
    unfold leftSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', ite_eq_right h.not_ge]

open LaurentPolynomial in
/-- `rightSummand m` is divisible by `X ^ (C(m, 2) + m)`, so its lower coefficients vanish. -/
private theorem coeff_rightSummand_eq_zero {d m : ℕ} (h : d < m.choose 2 + m) :
    PowerSeries.coeff d (rightSummand m) = 0 := by
  have hrw : rightSummand m = X ^ (m.choose 2 + m) * (laurentZInv ^ m * qPochhammerInv m) := by
    unfold rightSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', ite_eq_right h.not_ge]

open LaurentPolynomial in
/-- `leftSummand i * rightSummand j` is divisible by `X ^ (C(i, 2) + (C(j, 2) + j))`. -/
private theorem coeff_leftSummand_mul_rightSummand_eq_zero {d i j : ℕ}
    (h : d < i.choose 2 + (j.choose 2 + j)) :
    PowerSeries.coeff d (leftSummand i * rightSummand j) = 0 := by
  have hrw : leftSummand i * rightSummand j = X ^ (i.choose 2 + (j.choose 2 + j)) *
      (laurentZ ^ i * qPochhammerInf (X * X ^ i) * (laurentZInv ^ j * qPochhammerInv j)) := by
    unfold leftSummand rightSummand; ring
  rw [hrw, PowerSeries.coeff_X_pow_mul', ite_eq_right h.not_ge]

open LaurentPolynomial in
/-- The leftSummand sequence is summable. -/
private theorem summable_leftSummand : Summable leftSummand := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 2)) fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  exact coeff_leftSummand_eq_zero (Nat.lt_choose_two_of_add_two_le hn)

open LaurentPolynomial in
/-- The rightSummand sequence is summable. -/
private theorem summable_rightSummand : Summable rightSummand := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero (s := Finset.range (d + 1)) fun m hm => ?_
  rw [Finset.mem_range, not_lt] at hm
  exact coeff_rightSummand_eq_zero (by omega)

open LaurentPolynomial in
/-- The double product sequence is summable. -/
private theorem summable_leftSummand_mul_rightSummand :
    Summable (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h
  · have := Nat.lt_choose_two_of_add_two_le h
    omega
  · omega

open LaurentPolynomial in
/-- HasSum for the double product giving jacobiProd. -/
private theorem hasSum_leftSummand_mul_rightSummand_jacobiProd :
    HasSum (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) jacobiProd := by
  have h : jacobiProd = ∑' p : ℕ × ℕ, leftSummand p.1 * rightSummand p.2 := by
    rw [jacobiProd_eq_tsum_mul_tsum]
    exact summable_leftSummand.hasSum.mul_eq summable_rightSummand.hasSum
      summable_leftSummand_mul_rightSummand.hasSum
  rw [h]
  exact summable_leftSummand_mul_rightSummand.hasSum



open LaurentPolynomial in
/-- Summability of the non-negative diagonal rearrangement. -/
private theorem summable_diagonal_nonneg :
    Summable (fun p : ℕ × ℕ => leftSummand (p.2 + p.1) * rightSummand p.2) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 2) ×ˢ Finset.range (d + 2)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h
  · have := Nat.lt_choose_two_of_add_two_le (show d + 2 ≤ p.2 + p.1 by omega)
    omega
  · omega

open LaurentPolynomial in
/-- Summability of the negative diagonal rearrangement. -/
private theorem summable_diagonal_neg :
    Summable (fun p : ℕ × ℕ => leftSummand p.2 * rightSummand (p.2 + p.1 + 1)) := by
  refine (PowerSeries.WithPiTopology.summable_iff_summable_coeff (LaurentPolynomial ℂ)).mpr
    fun d => summable_of_ne_finset_zero
      (s := Finset.range (d + 1) ×ˢ Finset.range (d + 1)) fun p hp => ?_
  simp only [Finset.mem_product, Finset.mem_range, not_and_or, not_lt] at hp
  refine coeff_leftSummand_mul_rightSummand_eq_zero ?_
  rcases hp with h | h <;> omega

open LaurentPolynomial in
/-- Splitting a `HasSum` over `ℕ × ℕ` into the diagonals `(m + k, m)` and `(n, n + l + 1)`. -/
private theorem hasSum_split_diagonal (f : ℕ × ℕ → (LaurentPolynomial ℂ)⟦X⟧)
    {a b : (LaurentPolynomial ℂ)⟦X⟧}
    (h1 : HasSum (fun p : ℕ × ℕ => f (p.2 + p.1, p.2)) a)
    (h2 : HasSum (fun p : ℕ × ℕ => f (p.2, p.2 + p.1 + 1)) b) :
    HasSum f (a + b) :=
  diagonalEquiv.symm.hasSum_iff.mp (h1.sum h2)

open LaurentPolynomial in
/-- A family indexed by `ℕ × ℕ` sums to the sum of its row sums. -/
private theorem hasSum_of_hasSum_fiberwise {f : ℕ × ℕ → (LaurentPolynomial ℂ)⟦X⟧}
    {g : ℕ → (LaurentPolynomial ℂ)⟦X⟧} (hf : Summable f)
    (hrow : ∀ k : ℕ, HasSum (fun m : ℕ => f (k, m)) (g k)) :
    HasSum f (∑' k : ℕ, g k) := by
  rw [(hf.hasSum.prod_fiberwise hrow).tsum_eq]
  exact hf.hasSum

open LaurentPolynomial in
/-- HasSum for the non-negative diagonal (combined over all k). -/
private theorem hasSum_diagonal_nonneg_part :
    HasSum (fun p : ℕ × ℕ => leftSummand (p.2 + p.1) * rightSummand p.2)
      (∑' k : ℕ, laurentZ ^ k * X ^ k.choose 2) :=
  hasSum_of_hasSum_fiberwise summable_diagonal_nonneg hasSum_diagonal_nonneg

open LaurentPolynomial in
/-- HasSum for the negative diagonal (combined over all l). -/
private theorem hasSum_diagonal_neg_part :
    HasSum (fun p : ℕ × ℕ => leftSummand p.2 * rightSummand (p.2 + p.1 + 1))
      (∑' l : ℕ, laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2) :=
  hasSum_of_hasSum_fiberwise summable_diagonal_neg hasSum_diagonal_neg

open LaurentPolynomial in
/-- HasSum for the double product giving jacobiBilateral. -/
private theorem hasSum_leftSummand_mul_rightSummand_jacobiBilateral :
    HasSum (fun p : ℕ × ℕ => leftSummand p.1 * rightSummand p.2) jacobiBilateral := by
  have h : jacobiBilateral = (∑' k : ℕ, laurentZ ^ k * X ^ k.choose 2) +
      ∑' l : ℕ, laurentZInv ^ (l + 1) * X ^ (l + 2).choose 2 := by
    unfold jacobiBilateral
    congr 1
    · exact tsum_congr fun n => by rw [laurentZ_pow]
    · exact tsum_congr fun m => by rw [laurentZInv_pow]
  rw [h]
  exact hasSum_split_diagonal _ hasSum_diagonal_nonneg_part hasSum_diagonal_neg_part

open LaurentPolynomial in
/-- jacobiProd = jacobiBilateral via HasSum.mul, diagonalEquiv, and diagonal HasSum results. -/
theorem jacobiTripleProduct : @jacobiProd = @jacobiBilateral :=
  hasSum_leftSummand_mul_rightSummand_jacobiProd.unique
    hasSum_leftSummand_mul_rightSummand_jacobiBilateral

end JTP

end QSeries.FormalPowerSeries

end
