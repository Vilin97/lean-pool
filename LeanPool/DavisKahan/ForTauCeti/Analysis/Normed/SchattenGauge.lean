/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.Normed.SymmetricGauge
public import Mathlib.Analysis.MeanInequalities

/-!
# The `ℓᵖ` symmetric gauge

`Φ_p a = (∑ aₙ ^ p) ^ (1 / p)` for `1 ≤ p`, as a `TauCeti.SymmetricGauge` on
finitely supported nonnegative sequences.  Feeding it to
`TauCeti.symmetricGaugeFamily` produces the Schatten-`p` operator ideal family.

* `TauCeti.schattenGaugeFun` — the underlying function;
* `TauCeti.schattenGauge` — the bundled gauge.

## Sums over a larger index set

The gauge is a sum over `a.support`, but its subadditivity compares three
sequences with three different supports.  `schattenGaugeFun_eq_sum_of_subset`
says the sum may be taken over any `Finset` containing the support — the extra
terms are `0 ^ p = 0`, which needs `p ≠ 0` — so all three can be moved to the
union of their supports before Minkowski applies.  That bookkeeping, rather than
the inequality, is the substance of `add_le`.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **new**.  Written against the target signature in
  `TauCetiRoadmap/OperatorTheory/OperatorIdeals/Suggested.lean`.
* Roadmap topic: `OperatorIdeals`.
* Original authors / copyright: Claude Opus 5; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
-/

public section

open scoped NNReal ENNReal

namespace TauCeti

variable {p : ℝ}

/-- The underlying `ℓᵖ` gauge function on finitely supported nonnegative
sequences. -/
@[expose]
noncomputable def schattenGaugeFun (p : ℝ) (a : ℕ →₀ ℝ≥0) : ℝ≥0 :=
  (∑ i ∈ a.support, a i ^ p) ^ (1 / p)

/-- The defining sum may be taken over any finset containing the support: the
extra terms are `0 ^ p = 0`. -/
theorem schattenGaugeFun_eq_sum_of_subset (hp : 0 < p) (a : ℕ →₀ ℝ≥0)
    {s : Finset ℕ} (hs : a.support ⊆ s) :
    schattenGaugeFun p a = (∑ i ∈ s, a i ^ p) ^ (1 / p) := by
  unfold schattenGaugeFun
  rw [Finset.sum_subset hs (fun i _ hi => by
    rw [Finsupp.notMem_support_iff.mp hi, NNReal.zero_rpow hp.ne'])]

/-- Positive homogeneity of the `ℓᵖ` gauge. -/
theorem schattenGaugeFun_smul (hp : 1 ≤ p) (c : ℝ≥0) (a : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (c • a) = c * schattenGaugeFun p a := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hsub : (c • a).support ⊆ a.support := Finsupp.support_smul
  rw [schattenGaugeFun_eq_sum_of_subset hp0 _ hsub, schattenGaugeFun]
  have hterm : ∀ i ∈ a.support, (c • a) i ^ p = c ^ p * a i ^ p := by
    intro i _
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact NNReal.mul_rpow
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, NNReal.mul_rpow]
  congr 1
  rw [← NNReal.rpow_mul, mul_one_div, div_self hp0.ne', NNReal.rpow_one]

/-- **Minkowski.**  Subadditivity of the `ℓᵖ` gauge.

The inequality itself is `NNReal.Lp_add_le`; the work is moving three sums with
three different supports onto their union first. -/
theorem schattenGaugeFun_add_le (hp : 1 ≤ p) (a b : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (a + b) ≤ schattenGaugeFun p a + schattenGaugeFun p b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s : Finset ℕ := a.support ∪ b.support with hs
  have hab : (a + b).support ⊆ s := by
    intro i hi
    simpa [hs] using Finsupp.support_add hi
  have eab : schattenGaugeFun p (a + b) = (∑ i ∈ s, (a i + b i) ^ p) ^ (1 / p) := by
    rw [schattenGaugeFun_eq_sum_of_subset hp0 _ hab]
    rfl
  have ea : schattenGaugeFun p a = (∑ i ∈ s, a i ^ p) ^ (1 / p) :=
    schattenGaugeFun_eq_sum_of_subset hp0 a Finset.subset_union_left
  have eb : schattenGaugeFun p b = (∑ i ∈ s, b i ^ p) ^ (1 / p) :=
    schattenGaugeFun_eq_sum_of_subset hp0 b Finset.subset_union_right
  rw [eab, ea, eb]
  exact NNReal.Lp_add_le s (fun i => a i) (fun i => b i) hp

/-- Permutation invariance of the `ℓᵖ` gauge.

Relabelling the index set is a bijection of the support, so the sum is
unchanged; `Finset.sum_nbij'` states that with the two directions explicit. -/
theorem schattenGaugeFun_symm (_hp : 1 ≤ p) (σ : Equiv.Perm ℕ) (a : ℕ →₀ ℝ≥0) :
    schattenGaugeFun p (Finsupp.equivMapDomain σ a) = schattenGaugeFun p a := by
  unfold schattenGaugeFun
  congr 1
  refine Finset.sum_nbij' (fun i => σ.symm i) (fun i => σ i) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply] at hi ⊢
    exact hi
  · intro i hi
    simp only [Finsupp.mem_support_iff, Finsupp.equivMapDomain_apply] at hi ⊢
    simpa using hi
  · intro i _; simp
  · intro i _; simp
  · intro i _; simp [Finsupp.equivMapDomain_apply]

/-- Monotonicity of the `ℓᵖ` gauge in the termwise order. -/
theorem schattenGaugeFun_mono (hp : 1 ≤ p) {a b : ℕ →₀ ℝ≥0} (hab : a ≤ b) :
    schattenGaugeFun p a ≤ schattenGaugeFun p b := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  set s : Finset ℕ := a.support ∪ b.support with hs
  rw [schattenGaugeFun_eq_sum_of_subset hp0 a Finset.subset_union_left,
    schattenGaugeFun_eq_sum_of_subset hp0 b Finset.subset_union_right]
  refine NNReal.rpow_le_rpow (Finset.sum_le_sum fun i _ => ?_) (by positivity)
  exact NNReal.rpow_le_rpow (hab i) hp0.le

/-- Normalization: a single unit coordinate has gauge one. -/
theorem schattenGaugeFun_normalized (hp : 1 ≤ p) :
    schattenGaugeFun p (Finsupp.single 0 (1 : ℝ≥0)) = 1 := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  unfold schattenGaugeFun
  rw [Finsupp.support_single (0 : ℕ) (one_ne_zero)]
  simp [NNReal.one_rpow]

/-- **The `ℓᵖ` symmetric gauge**, `Φ_p a = (∑ aₙ ^ p) ^ (1 / p)` for `1 ≤ p`.

Feeding this to `TauCeti.symmetricGaugeFamily` produces the Schatten-`p`
operator ideal family, which is what the roadmap's `schattenFamily` names. -/
@[expose]
noncomputable def schattenGauge (p : ℝ) (hp : 1 ≤ p) : SymmetricGauge where
  toFun := schattenGaugeFun p
  add_le := schattenGaugeFun_add_le hp
  smul := schattenGaugeFun_smul hp
  symm := fun σ a => schattenGaugeFun_symm hp σ a
  mono := fun _ _ hab => schattenGaugeFun_mono hp hab
  normalized := schattenGaugeFun_normalized hp

/-- The bundled gauge applies as `schattenGaugeFun`. -/
@[simp]
theorem schattenGauge_apply (hp : 1 ≤ p) (a : ℕ →₀ ℝ≥0) :
    schattenGauge p hp a = schattenGaugeFun p a := rfl

/-- Each coordinate is bounded by the gauge: `cₙ ≤ Φ_p c`. -/
theorem le_schattenGaugeFun (hp : 1 ≤ p) (c : ℕ →₀ ℝ≥0) (i : ℕ) :
    c i ≤ schattenGaugeFun p c := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  by_cases hi : i ∈ c.support
  · have hmem : c i ^ p ≤ ∑ j ∈ c.support, c j ^ p :=
      Finset.single_le_sum (f := fun j => c j ^ p) (fun _ _ => zero_le) hi
    have := NNReal.rpow_le_rpow hmem (by positivity : (0:ℝ) ≤ 1 / p)
    rwa [← NNReal.rpow_mul, mul_one_div, div_self hp0.ne', NNReal.rpow_one] at this
  · rw [Finsupp.notMem_support_iff.mp hi]
    exact zero_le

/-- **The `ℓ` scale nests.**  For `1 ≤ p ≤ q` the `ℓ^q` gauge is below the `ℓ^p`
gauge.

Normalization: each `cₙ` is below `M = Φ_p c`, so `cₙ/M ≤ 1` and raising to the
larger exponent `q` only decreases it; summing gives `∑ cₙ^q ≤ M^q`.  The case
`M = 0` is separate, since there is nothing to divide by — there `c = 0`. -/
theorem schattenGaugeFun_antitone (hp : 1 ≤ p) {q : ℝ} (hq : 1 ≤ q) (hpq : p ≤ q)
    (c : ℕ →₀ ℝ≥0) : schattenGaugeFun q c ≤ schattenGaugeFun p c := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set M := schattenGaugeFun p c with hM
  -- No case split on `M = 0` is needed: `rpow_add_of_nonneg` holds there too,
  -- and when `M = 0` every coordinate is `0`, so the termwise bound is `0 ≤ 0`.
  have hMp : M ^ p = ∑ i ∈ c.support, c i ^ p := by
    rw [hM, schattenGaugeFun, ← NNReal.rpow_mul, one_div,
      inv_mul_cancel₀ hp0.ne', NNReal.rpow_one]
  have hterm : ∀ i ∈ c.support, c i ^ q ≤ c i ^ p * M ^ (q - p) := by
    intro i _
    have hle : c i ≤ M := le_schattenGaugeFun hp c i
    calc c i ^ q = c i ^ (p + (q - p)) := by congr 1; ring
      _ = c i ^ p * c i ^ (q - p) :=
          NNReal.rpow_add_of_nonneg _ (by linarith) (by linarith)
      _ ≤ c i ^ p * M ^ (q - p) := by
          gcongr
  have hsum : ∑ i ∈ c.support, c i ^ q ≤ M ^ q := by
    calc ∑ i ∈ c.support, c i ^ q
        ≤ ∑ i ∈ c.support, c i ^ p * M ^ (q - p) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ c.support, c i ^ p) * M ^ (q - p) := by rw [← Finset.sum_mul]
      _ = M ^ p * M ^ (q - p) := by rw [hMp]
      _ = M ^ q := by
          rw [← NNReal.rpow_add_of_nonneg _ (by linarith : (0:ℝ) ≤ p)
            (by linarith : (0:ℝ) ≤ q - p)]
          congr 1
          ring
  calc schattenGaugeFun q c = (∑ i ∈ c.support, c i ^ q) ^ (1 / q) := rfl
    _ ≤ (M ^ q) ^ (1 / q) := NNReal.rpow_le_rpow hsum (by positivity)
    _ = M := by rw [← NNReal.rpow_mul, mul_one_div, div_self hq0.ne', NNReal.rpow_one]

/-- `rpow` with a positive exponent commutes with suprema on `ℝ≥0∞`.

Mathlib has `ENNReal.iSup_pow` for *natural* powers only; `ENNReal.orderIsoRpow` makes the
real-exponent case immediate, since an order isomorphism preserves suprema.

This is a general `ℝ≥0∞` fact with no Schatten content.  It lives here because that is where
its only consumer is; if a second one appears, move it somewhere shared rather than copying
it. -/
theorem iSup_rpow {ι : Sort*} (f : ι → ℝ≥0∞) {r : ℝ} (hr : 0 < r) :
    (⨆ i, f i) ^ r = ⨆ i, f i ^ r := by
  have h := (ENNReal.orderIsoRpow r hr).map_iSup f
  simpa only [ENNReal.orderIsoRpow_apply] using h

/-- The Schatten gauge of a `Fin k` view is the `ℓᵖ` norm of the first `k` entries. -/
theorem schattenGaugeFun_ofFin {p : ℝ} (hp : 0 < p) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n)
    (k : ℕ) :
    schattenGaugeFun p (SymmetricGauge.ofFin (fun i : Fin k => a i))
      = (∑ n ∈ Finset.range k, (a n).toNNReal ^ p) ^ (1 / p) := by
  classical
  have hsupp : (SymmetricGauge.ofFin (fun i : Fin k => a i)).support ⊆ Finset.range k := by
    intro n hn
    by_contra hk
    rw [Finsupp.mem_support_iff] at hn
    exact hn (SymmetricGauge.ofFin_apply_of_le _ (Finset.mem_range.not.1 hk))
  rw [schattenGaugeFun_eq_sum_of_subset hp _ hsupp]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  have hk : n < k := Finset.mem_range.1 hn
  rw [SymmetricGauge.ofFin_apply _ hk, Real.nnabs_of_nonneg (ha n)]

end TauCeti
