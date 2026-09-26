/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.Trunc
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.AnalyticGerm.CoordinateChange
public import LeanPool.SeveralComplexVariables.SeveralComplexVariables.PolydiscTaylor

/-!
# Total order of analytic germs

The Taylor series of a scalar germ in finite complex coordinates is a Mathlib `MvPowerSeries`.
Its `order` is the least total degree with a nonzero coefficient, with infinity for the zero
series. This is different from order along a chosen axis. The empty coordinate type `Fin 0` is
included.

The basic order characterization and sum rules use Mathlib directly. Taylor uniqueness and the
infinite-order criterion follow from the convergent polydisc expansion. The product rule follows
from multiplicativity of Taylor series. The coordinate chain rule proves that analytic pullback
cannot lower order; applying this to a map and its inverse gives coordinate invariance. Exact
total order along the last axis after a linear change follows [Suwa][Suwa2024], Lemma 1.2: the
leading homogeneous part is a nonzero polynomial, hence nonvanishing at some point. An
invertible shear sends the last basis vector to a suitable such point. These are classical local
analytic facts, as in [Suwa][Suwa2024] §1.4, rather than a development of local algebra.

## Main definitions

* `taylorSeries`: Taylor series of a scalar analytic germ, independent of its representative.
* `order`: Total order of vanishing: the least total degree in the germ's Taylor series.
* `shearToLastAxis`: A linear automorphism sending the last coordinate axis to the line through `c`,
  provided the `i`-th coordinate of `c` is nonzero.

## Main results

* `taylorSeries_injective`: The multivariate Taylor-series map is injective on analytic germs.
* `taylorSeries_mul`: Taylor series preserve multiplication of analytic germs.
* `order_mul`: The order of a product is the sum of the orders, including zero germs.
* `min_order_le_order_add`: Cancellation can only raise the order of a sum.
* `order_eq_zero_iff`: A germ has order zero exactly when it is a unit.
* `order_eq_top_iff`: Infinite order is equivalent to being the zero germ, by uniqueness of the
  convergent multivariate Taylor expansion.
* `order_pullbackEquiv`: An analytic change of coordinates preserves total order.
* `exists_coordinate_change_order`: **[Suwa][Suwa2024], Lemma 1.2.** A linear change makes the order
  on the last axis equal to the total order.

## References

* [T. Suwa, *Complex Analytic Geometry: From the Localization Viewpoint*][Suwa2024]
-/

public noncomputable section

open Filter Metric Set
open scoped Topology

namespace SeveralComplexVariables.AnalyticGerm

variable {n m : ℕ} {x : Fin n → ℂ}

/-- The multivariate Taylor series depends only on the function germ. -/
theorem holomorphicTaylorSeries_congr {f g : (Fin n → ℂ) → ℂ}
    (h : f =ᶠ[𝓝 x] g) : holomorphicTaylorSeries f x = holomorphicTaylorSeries g x := by
  obtain ⟨U, hU, ho, hx⟩ := _root_.eventually_nhds_iff.mp h
  funext k
  dsimp [holomorphicTaylorSeries, multiIndexDeriv]
  rw [iteratedPartialDeriv_congrOn ho hU (multiIndexList k) hx]

/-- Taylor series of a scalar analytic germ, independent of its representative. -/
@[expose] def taylorSeries (f : AnalyticGerm ℂ x) : MvPowerSeries (Fin n) ℂ :=
  f.val.liftOn (fun g => holomorphicTaylorSeries g x)
    (fun _ _ h => holomorphicTaylorSeries_congr h)

/-- Taylor series of a represented germ is the existing Taylor series of the function. -/
@[simp] theorem taylorSeries_ofAnalyticAt (f : (Fin n → ℂ) → ℂ) (hf : AnalyticAt ℂ f x) :
    taylorSeries (ofAnalyticAt f hf) = holomorphicTaylorSeries f x := rfl

/-- Taylor series preserve addition of analytic germs. -/
theorem taylorSeries_add (f g : AnalyticGerm ℂ x) :
    taylorSeries (f + g) = taylorSeries f + taylorSeries g := by
  obtain ⟨f, hf, rfl⟩ := exists_rep f
  obtain ⟨g, hg, rfl⟩ := exists_rep g
  obtain ⟨U, hsub, hU, hx⟩ := _root_.eventually_nhds_iff.mp
    (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hA : ∀ b ∈ (Finset.univ : Finset Bool),
      AnalyticOnNhd ℂ (if b then f else g) U := by
    intro b _ z hz
    cases b
    · exact (hsub z hz).2
    · exact (hsub z hz).1
  change holomorphicTaylorSeries (f + g) x =
    holomorphicTaylorSeries f x + holomorphicTaylorSeries g x
  funext k
  have hD : iteratedPartialDeriv (multiIndexList k) (f + g) x =
      iteratedPartialDeriv (multiIndexList k) f x +
        iteratedPartialDeriv (multiIndexList k) g x := by
    simpa [Fintype.sum_bool, Pi.add_def] using
      (iteratedPartialDeriv_finset_sum Finset.univ hA hU (multiIndexList k) hx)
  change (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) (f + g) x =
    (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) f x +
    (∏ i, (k i).factorial : ℂ)⁻¹ * iteratedPartialDeriv (multiIndexList k) g x
  rw [hD, mul_add]

/-- The zero germ has zero Taylor series, including in dimension zero. -/
@[simp] theorem taylorSeries_zero : taylorSeries (0 : AnalyticGerm ℂ x) = 0 := by
  have hz : ∀ l : List (Fin n), iteratedPartialDeriv l (0 : (Fin n → ℂ) → ℂ) = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
        change partialDeriv i (iteratedPartialDeriv l 0) = 0
        rw [ih]
        funext z
        simp [partialDeriv]
  change holomorphicTaylorSeries (0 : (Fin n → ℂ) → ℂ) x = 0
  funext k
  change holomorphicTaylorSeries (0 : (Fin n → ℂ) → ℂ) x k = 0
  simp [holomorphicTaylorSeries, multiIndexDeriv, hz]

/-- The Taylor series of a coordinate derivative is the formal partial derivative. -/
theorem holomorphicTaylorSeries_partialDeriv {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f x) (i : Fin n) :
    holomorphicTaylorSeries (partialDeriv i f) x =
      MvPowerSeries.pderiv i (holomorphicTaylorSeries f x) := by
  obtain ⟨U, hU, ho, hx⟩ := _root_.eventually_nhds_iff.mp hf.eventually_analyticAt
  ext k
  rw [MvPowerSeries.coeff_pderiv]
  have happ (l : List (Fin n)) :
      iteratedPartialDeriv (l ++ [i]) f = iteratedPartialDeriv l (partialDeriv i f) := by
    induction l with
    | nil => rfl
    | cons j l ih =>
      simpa only [List.cons_append, iteratedPartialDeriv] using congrArg (partialDeriv j) ih
  have hD : multiIndexDeriv k (partialDeriv i f) x =
      multiIndexDeriv (k + Finsupp.single i 1 : Fin n →₀ ℕ) f x := by
    rw [multiIndexDeriv, ← happ]
    apply iteratedPartialDeriv_eq_multiIndexDeriv hU ho hx
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simp [hji, Ne.symm hji]
  have hfac : (∏ j, ((k + Finsupp.single i 1 : Fin n →₀ ℕ) j).factorial : ℂ) =
      (∏ j, (k j).factorial : ℂ) * (k i + 1) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i),
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    have he : (∏ j ∈ Finset.univ.erase i, (((k + Finsupp.single i 1 : Fin n →₀ ℕ) j).factorial :
      ℂ)) =
        ∏ j ∈ Finset.univ.erase i, ((k j).factorial : ℂ) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [Finsupp.single_eq_of_ne (Finset.ne_of_mem_erase hj)]
    rw [he]
    simp [Nat.factorial_succ]
    ring
  change (∏ j, (k j).factorial : ℂ)⁻¹ * multiIndexDeriv k (partialDeriv i f) x =
    (∏ j, ((k + Finsupp.single i 1 : Fin n →₀ ℕ) j).factorial : ℂ)⁻¹ *
      multiIndexDeriv (k + Finsupp.single i 1 : Fin n →₀ ℕ) f x * (k i + 1)
  rw [hD, hfac]
  have hk : (k i : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (k i)
  field_simp

/-- Total order of vanishing: the least total degree in the germ's Taylor series. -/
@[expose] def order (f : AnalyticGerm ℂ x) : ℕ∞ := (taylorSeries f).order

/-- The total order is computed by Mathlib's multivariate power-series order. -/
theorem order_eq_taylorSeries_order (f : AnalyticGerm ℂ x) :
    order f = (taylorSeries f).order := rfl

/-- The constant Taylor coefficient is evaluation at the base point. -/
@[simp] theorem constantCoeff_taylorSeries (f : AnalyticGerm ℂ x) :
    (taylorSeries f).constantCoeff = eval x f := by
  obtain ⟨g, hg, rfl⟩ := exists_rep f
  change holomorphicTaylorSeries g x 0 = g x
  simp [holomorphicTaylorSeries, multiIndexDeriv, multiIndexList, iteratedPartialDeriv]

/-- A germ has order zero exactly when it is a unit. -/
@[simp] theorem order_eq_zero_iff (f : AnalyticGerm ℂ x) : order f = 0 ↔ IsUnit f := by
  rw [isUnit_iff, order]
  have h := MvPowerSeries.order_ne_zero_iff_constCoeff_eq_zero (f := taylorSeries f)
  simpa using not_congr h

/-- The zero germ has infinite total order. -/
@[simp] theorem order_zero : order (0 : AnalyticGerm ℂ x) = ⊤ := by
  simp [order]

/-- Distinct orders prevent cancellation of the leading terms of a sum. -/
theorem order_add_of_ne {f g : AnalyticGerm ℂ x} (h : order f ≠ order g) :
    order (f + g) = min (order f) (order g) := by
  simpa only [order, taylorSeries_add] using MvPowerSeries.order_add_of_order_ne h

/-- A scalar analytic germ is determined to be zero by its Taylor coefficients. The proof uses the
convergent polydisc Taylor expansion, including dimension zero. -/
@[simp] theorem taylorSeries_eq_zero_iff (f : AnalyticGerm ℂ x) :
    taylorSeries f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro hzero
    obtain ⟨g, hg, rfl⟩ := exists_rep f
    change holomorphicTaylorSeries g x = 0 at hzero
    have hb : ∀ᶠ z in 𝓝 x, ‖g z‖ < ‖g x‖ + 1 :=
      hg.continuousAt.norm.eventually_lt_const (by linarith)
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hg.eventually_analyticAt.and hb)
    have hr₂ : 0 < r / 2 := half_pos hr
    have hsub : closedPolydisc x (fun _ => r / 2) ⊆ ball x r := by
      rw [closedPolydisc_eq_closedBall hr₂.le]
      exact closedBall_subset_ball (half_lt_self hr)
    have hA : AnalyticOnNhd ℂ g (closedPolydisc x (fun _ => r / 2)) :=
      fun z hz => (hball (hsub hz)).1
    have hslice : ∀ z ∈ closedPolydisc x (fun _ => r / 2), ∀ i,
        AnalyticAt ℂ (fun w => g (Function.update z i w)) (z i) := by
      intro z hz i
      exact hA.analyticAt_update hz i
    have hcoeff : ∀ m : Fin n → ℕ,
        polydiscCauchyCoeffWithRadii g x (fun _ => r / 2) m = 0 := by
      intro m
      have h := (coeff_holomorphicTaylorSeries (fun _ => hr₂) hA.continuousOn hslice
        (Finsupp.equivFunOnFinite.symm m)).symm
      rw [hzero, Finsupp.coe_equivFunOnFinite_symm] at h
      exact h
    have he : g =ᶠ[𝓝 x] 0 := by
      filter_upwards [ball_mem_nhds x hr₂] with z hz
      have hh : ∀ i, ‖(z - x) i‖ < r / 2 := by
        intro i
        exact lt_of_le_of_lt (norm_le_pi_norm (z - x) i)
          (by simpa only [mem_ball, dist_eq_norm] using hz)
      have hsum := hasSum_polydiscTaylor (fun _ => hr₂) hh hA.continuousOn hslice
        (fun z hz => (hball (hsub hz)).2.le)
      have hxz : x + (z - x) = z := by abel
      have hsum0 : HasSum (fun _ : Fin n → ℕ => (0 : ℂ)) (g z) := by
        simpa only [hcoeff, smul_zero, hxz] using hsum
      exact hsum0.unique hasSum_zero
    exact Subtype.ext (Germ.coe_eq.mpr he)
  · rintro rfl
    exact taylorSeries_zero

/-- The multivariate Taylor-series map is injective on analytic germs. -/
theorem taylorSeries_injective : Function.Injective (taylorSeries (x := x)) := by
  let T : AnalyticGerm ℂ x →+ MvPowerSeries (Fin n) ℂ :=
    { toFun := taylorSeries
      map_zero' := taylorSeries_zero
      map_add' := taylorSeries_add }
  intro f g h
  have hs : taylorSeries (f - g) = 0 := by
    change T (f - g) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr h
  exact sub_eq_zero.mp ((taylorSeries_eq_zero_iff _).mp hs)

/-- Infinite order is equivalent to being the zero germ, by uniqueness of the convergent
multivariate Taylor expansion. -/
@[simp] theorem order_eq_top_iff (f : AnalyticGerm ℂ x) : order f = ⊤ ↔ f = 0 := by
  rw [order, MvPowerSeries.order_eq_top_iff, taylorSeries_eq_zero_iff]

/-- Taylor series preserve multiplication of analytic germs. The proof compares coefficients
inductively, using the analytic and formal coordinate product rules. -/
theorem taylorSeries_mul (f g : AnalyticGerm ℂ x) :
    taylorSeries (f * g) = taylorSeries f * taylorSeries g := by
  let P (k : Fin n →₀ ℕ) : Prop := ∀ f g : AnalyticGerm ℂ x,
    MvPowerSeries.coeff k (taylorSeries (f * g)) =
      MvPowerSeries.coeff k (taylorSeries f * taylorSeries g)
  have hzero : P 0 := by
    intro f g
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      constantCoeff_taylorSeries]
  have hstep (k : Fin n →₀ ℕ) (i : Fin n) (ih : P k) : P (k + Finsupp.single i 1) := by
    intro f g
    obtain ⟨f, hf, rfl⟩ := exists_rep f
    obtain ⟨g, hg, rfl⟩ := exists_rep g
    obtain ⟨U, hU, ho, hx⟩ := _root_.eventually_nhds_iff.mp
      (hf.eventually_analyticAt.and hg.eventually_analyticAt)
    have hAf : AnalyticOnNhd ℂ f U := fun y hy => (hU y hy).1
    have hAg : AnalyticOnNhd ℂ g U := fun y hy => (hU y hy).2
    have hdf := (hAf.partialDeriv ho i) x hx
    have hdg := (hAg.partialDeriv ho i) x hx
    have hdm := ((hAf.mul hAg).partialDeriv ho i) x hx
    have heq : ofAnalyticAt (partialDeriv i (f * g)) hdm =
        ofAnalyticAt (partialDeriv i f) hdf * ofAnalyticAt g hg +
          ofAnalyticAt f hf * ofAnalyticAt (partialDeriv i g) hdg := by
      rw [← ofAnalyticAt_mul, ← ofAnalyticAt_mul, ← ofAnalyticAt_add]
      apply ofAnalyticAt_eq_iff.mpr
      filter_upwards [ho.eventually_mem hx] with y hy
      exact partialDeriv_mul (hAf y hy).differentiableAt (hAg y hy).differentiableAt i
    have hD : MvPowerSeries.coeff k
        (MvPowerSeries.pderiv i (holomorphicTaylorSeries (f * g) x)) =
        MvPowerSeries.coeff k (MvPowerSeries.pderiv i
          (holomorphicTaylorSeries f x * holomorphicTaylorSeries g x)) := by
      rw [← holomorphicTaylorSeries_partialDeriv (hf.mul hg) i]
      change MvPowerSeries.coeff k (taylorSeries (ofAnalyticAt (partialDeriv i (f * g)) hdm)) = _
      rw [heq, taylorSeries_add, map_add, ih, ih]
      simp only [taylorSeries_ofAnalyticAt, holomorphicTaylorSeries_partialDeriv hf i,
        holomorphicTaylorSeries_partialDeriv hg i, Derivation.leibniz, smul_eq_mul, map_add]
      rw [mul_comm (MvPowerSeries.pderiv i (holomorphicTaylorSeries f x))]
      exact add_comm _ _
    simp only [MvPowerSeries.coeff_pderiv] at hD
    exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero (k i)) hD
  have hall (k : Fin n →₀ ℕ) : P k := by
    induction k using Finsupp.induction₂ with
    | zero => exact hzero
    | add_single i b k _ _ ih =>
      have h (b : ℕ) : P (k + Finsupp.single i b) := by
        induction b with
        | zero => simpa using ih
        | succ b hb =>
          simpa only [Finsupp.single_add, add_assoc] using hstep (k + Finsupp.single i b) i hb
      exact h b
  exact MvPowerSeries.ext fun k => hall k f g

/-- The order of a product is the sum of the orders, including zero germs. This follows from
multiplicativity of Taylor series and `MvPowerSeries.order_mul`. -/
theorem order_mul (f g : AnalyticGerm ℂ x) : order (f * g) = order f + order g := by
  simpa only [order, taylorSeries_mul] using MvPowerSeries.order_mul (taylorSeries f)
    (taylorSeries g)

/-- Cancellation can only raise the order of a sum. -/
theorem min_order_le_order_add (f g : AnalyticGerm ℂ x) :
    min (order f) (order g) ≤ order (f + g) := by
  simpa only [order, taylorSeries_add] using
    (MvPowerSeries.min_order_le_add (f := taylorSeries f) (g := taylorSeries g))

/-- Order at least `d + 1` is equivalent to a zero constant term and order at least `d` for every
formal coordinate derivative. -/
private theorem nat_succ_le_series_order_iff (p : MvPowerSeries (Fin n) ℂ) (d : ℕ) :
    (d + 1 : ℕ) ≤ p.order ↔ p.constantCoeff = 0 ∧
      ∀ i, (d : ℕ∞) ≤ (MvPowerSeries.pderiv i p).order := by
  constructor
  · intro h
    constructor
    · exact MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
        (le_trans (by exact_mod_cast Nat.succ_pos d) h)
    · intro i
      apply MvPowerSeries.nat_le_order
      intro k hk
      rw [MvPowerSeries.coeff_pderiv]
      have hdeg : (k + Finsupp.single i 1).degree < d + 1 := by simpa using hk
      rw [MvPowerSeries.coeff_of_lt_order
        (lt_of_lt_of_le (by exact_mod_cast hdeg) h), zero_mul]
  · rintro ⟨hzero, hd⟩
    apply MvPowerSeries.nat_le_order
    intro k hk
    by_cases hk0 : k = 0
    · simpa [hk0] using hzero
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hk0
    have hip : 0 < k i := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hsingle : Finsupp.single i 1 ≤ k := Finsupp.single_le_iff.mpr hip
    let l := k - Finsupp.single i 1
    have hl : l + Finsupp.single i 1 = k := tsub_add_cancel_of_le hsingle
    have hdeg : l.degree < d := by
      have := congrArg Finsupp.degree hl
      simp only [map_add, Finsupp.degree_single] at this
      omega
    have hh := MvPowerSeries.coeff_of_lt_order (f := MvPowerSeries.pderiv i p)
      (lt_of_lt_of_le (by exact_mod_cast hdeg) (hd i))
    rw [MvPowerSeries.coeff_pderiv, hl] at hh
    exact (mul_eq_zero.mp hh).resolve_right (by exact_mod_cast Nat.succ_ne_zero (l i))

/-- A common lower bound on orders is preserved by finite sums of analytic germs. -/
theorem le_order_sum {κ : Type*} (s : Finset κ) (f : κ → AnalyticGerm ℂ x) {d : ℕ∞}
    (h : ∀ i ∈ s, d ≤ order (f i)) : d ≤ order (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact le_trans (le_min (h i (Finset.mem_insert_self _ _))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))) (min_order_le_order_add _ _)

/-- Coordinate differentiation preserves analyticity at a point. -/
private theorem analyticAt_partialDeriv {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f x) (i : Fin n) : AnalyticAt ℂ (partialDeriv i f) x := by
  obtain ⟨r, hr, hfa⟩ := hf.exists_ball_analyticOnNhd
  exact (hfa.partialDeriv isOpen_ball i) x (mem_ball_self hr)

/-- Analytic pullback cannot lower the total order of a scalar germ. This includes maps between
spaces of different dimensions and empty coordinate types. -/
theorem order_le_order_pullback (e : (Fin n → ℂ) → (Fin m → ℂ)) (he : AnalyticAt ℂ e x)
    (f : AnalyticGerm ℂ (e x)) : order f ≤ order (pullback e he f) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro d
  obtain ⟨f, hf, rfl⟩ := exists_rep f
  induction d generalizing f with
  | zero => exact fun _ => bot_le
  | succ d ih =>
    intro hd
    obtain ⟨hzero, hderiv⟩ := (nat_succ_le_series_order_iff
      (holomorphicTaylorSeries f (e x)) d).mp hd
    change ((d + 1 : ℕ) : ℕ∞) ≤ (holomorphicTaylorSeries (f ∘ e) x).order
    apply (nat_succ_le_series_order_iff _ d).mpr
    constructor
    · have h0 : f (e x) = 0 := by
        simpa only [← taylorSeries_ofAnalyticAt f hf, constantCoeff_taylorSeries,
          eval_ofAnalyticAt] using hzero
      simpa only [← taylorSeries_ofAnalyticAt (f ∘ e) (hf.comp he),
        constantCoeff_taylorSeries, eval_ofAnalyticAt, Function.comp_apply] using h0
    · intro i
      let a (j : Fin m) := partialDeriv i (fun z => e z j)
      let b (j : Fin m) := partialDeriv j f ∘ e
      have ha (j : Fin m) : AnalyticAt ℂ (a j) x :=
        analyticAt_partialDeriv (analyticAt_pi_iff.mp he j) i
      have hb (j : Fin m) : AnalyticAt ℂ (b j) x :=
        (analyticAt_partialDeriv hf j).comp he
      have hsum := Finset.univ.analyticAt_sum (fun j _ => (ha j).mul (hb j))
      have heq : ofAnalyticAt (partialDeriv i (f ∘ e))
          (analyticAt_partialDeriv (hf.comp he) i) =
          ∑ j, ofAnalyticAt (a j) (ha j) * ofAnalyticAt (b j) (hb j) := by
        simp_rw [← ofAnalyticAt_mul]
        rw [← ofAnalyticAt_sum Finset.univ (fun j => a j * b j)
          (fun j => (ha j).mul (hb j)) hsum]
        apply ofAnalyticAt_eq_iff.mpr
        filter_upwards [he.eventually_analyticAt,
          he.continuousAt.eventually hf.eventually_analyticAt] with z hez hfz
        simpa [a, b, complexJacobian, smul_eq_mul] using
          partialDeriv_comp hfz.differentiableAt hez.differentiableAt i
      rw [← holomorphicTaylorSeries_partialDeriv (hf.comp he) i]
      change (d : ℕ∞) ≤ order (ofAnalyticAt (partialDeriv i (f ∘ e))
        (analyticAt_partialDeriv (hf.comp he) i))
      rw [heq]
      apply le_order_sum
      intro j _
      rw [order_mul]
      apply le_trans _ (le_add_left (le_refl _))
      apply ih (partialDeriv j f) (analyticAt_partialDeriv hf j)
      simpa only [order, taylorSeries_ofAnalyticAt,
        holomorphicTaylorSeries_partialDeriv hf j] using hderiv j

/-- An analytic change of coordinates preserves total order. Apply order monotonicity to the
coordinate map and its analytic inverse. -/
theorem order_pullbackEquiv (e : (Fin n → ℂ) ≃ₜ (Fin m → ℂ))
    (he : AnalyticAt ℂ e x) (hi : AnalyticAt ℂ e.symm (e x))
    (f : AnalyticGerm ℂ (e x)) : order (pullbackEquiv e x he hi f) = order f := by
  apply le_antisymm
  · obtain ⟨f, hf, rfl⟩ := exists_rep f
    have hc : AnalyticAt ℂ (f ∘ e) (e.symm (e x)) := by simpa using hf.comp he
    have h := order_le_order_pullback e.symm hi (ofAnalyticAt (f ∘ e) hc)
    have heq : ofAnalyticAt ((f ∘ e) ∘ e.symm) (hc.comp hi) = ofAnalyticAt f hf := by
      apply ofAnalyticAt_eq_iff.mpr
      exact .of_forall fun z => by simp
    rw [pullback_ofAnalyticAt, heq] at h
    change (holomorphicTaylorSeries (f ∘ e) (e.symm (e x))).order ≤
      (holomorphicTaylorSeries f (e x)).order at h
    change (holomorphicTaylorSeries (f ∘ e) x).order ≤
      (holomorphicTaylorSeries f (e x)).order
    simpa only [Homeomorph.symm_apply_apply] using h
  · exact order_le_order_pullback e he f

/-- Exact order is characterized by the first nonzero total-degree Taylor coefficient. -/
theorem order_eq_nat_iff (f : AnalyticGerm ℂ x) (d : ℕ) :
    order f = d ↔
      (∃ k, MvPowerSeries.coeff k (taylorSeries f) ≠ 0 ∧ k.degree = d) ∧
      ∀ k, k.degree < d → MvPowerSeries.coeff k (taylorSeries f) = 0 :=
  MvPowerSeries.order_eq_nat

/-- A linear automorphism sending the last coordinate axis to the line through `c`, provided the
`i`-th coordinate of `c` is nonzero. This is the shear used in [Suwa][Suwa2024], Lemma 1.2,
after swapping `i` with the last index. -/
def shearToLastAxis (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (hi : c i ≠ 0) :
    (Fin (n + 1) → ℂ) ≃ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun z j := if j = i then z i * c i else z j + z i * c j
  invFun z j := if j = i then z i / c i else z j - (z i / c i) * c j
  left_inv z := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]; field_simp [hi]; ring
  right_inv z := by
    ext j
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]
  map_add' z w := by
    ext j
    by_cases hj : j = i
    · simp [hj]; ring
    · simp [hj]; ring
  map_smul' a z := by
    ext j
    by_cases hj : j = i
    · simp [hj, smul_eq_mul]; ring
    · simp [hj, smul_eq_mul]; ring

/-- The shear sends the `i`-th axis to the line through `c`. -/
theorem shearToLastAxis_single (c : Fin (n + 1) → ℂ) (i : Fin (n + 1)) (hi : c i ≠ 0)
    (w : ℂ) : shearToLastAxis c i hi (Pi.single i w) = w • c := by
  ext j
  by_cases hj : j = i
  · subst j; simp [shearToLastAxis, Pi.single_eq_same, smul_eq_mul]
  · simp [shearToLastAxis, hj, smul_eq_mul]

/-- Constant functions have constant multivariate Taylor series. -/
theorem holomorphicTaylorSeries_const (a : ℂ) (x : Fin n → ℂ) :
    holomorphicTaylorSeries (fun _ => a) x = MvPowerSeries.C a := by
  ext k
  by_cases hk : k = 0
  · subst k
    change holomorphicTaylorSeries (fun _ => a) x 0 = a
    simp [holomorphicTaylorSeries, multiIndexDeriv, multiIndexList, iteratedPartialDeriv]
  · have hzero (l : List (Fin n)) (hl : l ≠ []) :
        iteratedPartialDeriv l (fun _ : (Fin n → ℂ) => a) = 0 := by
      induction l with
      | nil => exact (hl rfl).elim
      | cons i l ih =>
        by_cases hl0 : l = []
        · subst l
          funext z
          simp [iteratedPartialDeriv, partialDeriv]
        · funext z
          simp [iteratedPartialDeriv, ih hl0, partialDeriv]
    rw [MvPowerSeries.coeff_C_of_ne_zero hk]
    have hlist : multiIndexList k ≠ [] := by
      intro h
      have hcount := congrArg (fun l => l.count) h
      have : k = 0 := by
        ext i
        have := congrFun hcount i
        simpa only [count_multiIndexList, List.count_nil, Finsupp.zero_apply] using this
      exact hk this
    change holomorphicTaylorSeries (fun _ => a) x k = 0
    simp [holomorphicTaylorSeries, multiIndexDeriv, hzero _ hlist]

/-- Coordinate functions have the corresponding formal variable as their Taylor series at zero. -/
theorem holomorphicTaylorSeries_coord (i : Fin n) :
    holomorphicTaylorSeries (fun z : Fin n → ℂ => z i) 0 = MvPowerSeries.X i := by
  have hder (j : Fin n) : partialDeriv j (fun z : Fin n → ℂ => z i) =
      fun _ => if j = i then (1 : ℂ) else 0 := by
    funext z
    by_cases hji : j = i
    · subst j; simp [partialDeriv]
    · simp [partialDeriv, hji, Ne.symm hji]
  have hai : AnalyticAt ℂ (fun z : Fin n → ℂ => z i) 0 :=
    analyticAt_pi_iff.mp analyticAt_id i
  have hd (j : Fin n) : MvPowerSeries.pderiv j
      (holomorphicTaylorSeries (fun z : Fin n → ℂ => z i) 0) =
      MvPowerSeries.pderiv j (MvPowerSeries.X i) := by
    rw [← holomorphicTaylorSeries_partialDeriv hai j, hder,
      holomorphicTaylorSeries_const]
    by_cases hji : j = i <;> simp [MvPowerSeries.pderiv_X, hji]
  ext k
  by_cases hk : k = 0
  · subst k
    simp only [MvPowerSeries.coeff_zero_eq_constantCoeff, MvPowerSeries.constantCoeff_X]
    change holomorphicTaylorSeries (fun z : Fin n → ℂ => z i) 0 0 = 0
    simp [holomorphicTaylorSeries, multiIndexDeriv, multiIndexList, iteratedPartialDeriv]
  · obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hk
    have hjp : 0 < k j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
    let l := k - Finsupp.single j 1
    have hl : l + Finsupp.single j 1 = k :=
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hjp)
    have hh := congrArg (MvPowerSeries.coeff l) (hd j)
    simp only [MvPowerSeries.coeff_pderiv, hl] at hh
    exact mul_right_cancel₀ (by exact_mod_cast Nat.succ_ne_zero (l j)) hh

/-- The Taylor series at zero of polynomial evaluation is the polynomial itself. -/
theorem holomorphicTaylorSeries_eval (p : MvPolynomial (Fin n) ℂ) :
    holomorphicTaylorSeries (fun z => MvPolynomial.eval z p) 0 = p := by
  have ha (q : MvPolynomial (Fin n) ℂ) : AnalyticAt ℂ (fun z => MvPolynomial.eval z q) 0 :=
    AnalyticAt.aeval_mvPolynomial (fun i => analyticAt_pi_iff.mp analyticAt_id i) q
  induction p using MvPolynomial.induction_on with
  | C a => simpa using holomorphicTaylorSeries_const a (0 : Fin n → ℂ)
  | add p q hp hq =>
    change taylorSeries (ofAnalyticAt (fun z => MvPolynomial.eval z (p + q)) (ha _)) = _
    have heq : ofAnalyticAt (fun z => MvPolynomial.eval z (p + q)) (ha _) =
        ofAnalyticAt (fun z => MvPolynomial.eval z p) (ha _) +
          ofAnalyticAt (fun z => MvPolynomial.eval z q) (ha _) := by
      rw [← ofAnalyticAt_add]
      apply ofAnalyticAt_eq_iff.mpr
      exact .of_forall fun z => map_add _ _ _
    rw [heq, taylorSeries_add]
    simp only [taylorSeries_ofAnalyticAt, hp, hq, MvPolynomial.coe_add]
  | mul_X p i hp =>
    change taylorSeries (ofAnalyticAt (fun z => MvPolynomial.eval z (p * MvPolynomial.X i))
      (ha _)) = _
    have heq : ofAnalyticAt (fun z => MvPolynomial.eval z (p * MvPolynomial.X i)) (ha _) =
        ofAnalyticAt (fun z => MvPolynomial.eval z p) (ha _) *
          ofAnalyticAt (fun z : Fin n → ℂ => z i) (analyticAt_pi_iff.mp analyticAt_id i) := by
      rw [← ofAnalyticAt_mul]
      apply ofAnalyticAt_eq_iff.mpr
      exact .of_forall fun z => by simp
    rw [heq, taylorSeries_mul]
    simp only [taylorSeries_ofAnalyticAt, hp, holomorphicTaylorSeries_coord,
      MvPolynomial.coe_mul, MvPolynomial.coe_X]

/-- Total Taylor order in one coordinate agrees with Mathlib's scalar analytic order. -/
theorem order_one_coordinate {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
    order (ofAnalyticAt (fun z : Fin 1 → ℂ => g (z 0))
      (hg.comp_of_eq
        ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt 0) rfl)) =
      analyticOrderAt g 0 := by
  have ha {g : ℂ → ℂ} (hg : AnalyticAt ℂ g 0) :
      AnalyticAt ℂ (fun z : Fin 1 → ℂ => g (z 0)) 0 :=
    hg.comp_of_eq ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt 0) rfl
  apply ENat.eq_of_forall_natCast_le_iff
  intro d
  change (d : ℕ∞) ≤ (holomorphicTaylorSeries (fun z : Fin 1 → ℂ => g (z 0)) 0).order ↔ _
  induction d generalizing g with
  | zero => simp
  | succ d ih =>
    rw [nat_succ_le_series_order_iff]
    have hc : (holomorphicTaylorSeries (fun z : Fin 1 → ℂ => g (z 0)) 0).constantCoeff = g 0 :=
      constantCoeff_taylorSeries (ofAnalyticAt _ (ha hg))
    rw [hc]
    by_cases hz : g 0 = 0
    · rw [and_iff_right hz, Fin.forall_fin_one]
      rw [← holomorphicTaylorSeries_partialDeriv (ha hg) 0]
      have hd : partialDeriv 0 (fun z : Fin 1 → ℂ => g (z 0)) =
          fun z => deriv g (z 0) := by
        funext z
        simp [partialDeriv]
      rw [hd, ih hg.deriv]
      simpa only [Nat.cast_add, Nat.cast_one] using analyticOrderAt_deriv_ge_iff hg hz
    · simp [hz, hg.analyticOrderAt_eq_zero.mpr hz]

/-- Restriction to a complex line cannot lower total order. -/
theorem order_le_analyticOrderAt_line {f : (Fin n → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (v : Fin n → ℂ) :
    order (ofAnalyticAt f hf) ≤ analyticOrderAt (fun w : ℂ => f (w • v)) 0 := by
  let e : (Fin 1 → ℂ) → (Fin n → ℂ) := fun z => z 0 • v
  have he : AnalyticAt ℂ e 0 :=
    ((ContinuousLinearMap.proj (0 : Fin 1) : (Fin 1 → ℂ) →L[ℂ] ℂ).analyticAt 0).smul
      analyticAt_const
  have hf' : AnalyticAt ℂ f (e 0) := by simpa [e] using hf
  have h := order_le_order_pullback e he (ofAnalyticAt f hf')
  rw [pullback_ofAnalyticAt] at h
  have hl : AnalyticAt ℂ (fun w : ℂ => f (w • v)) 0 :=
    hf.comp_of_eq (analyticAt_id.smul analyticAt_const) (zero_smul _ _)
  have hscalar := order_one_coordinate hl
  simp only [order, taylorSeries_ofAnalyticAt] at h hscalar ⊢
  simpa [e, Function.comp_def, hscalar] using h

/-- **[Suwa][Suwa2024], Lemma 1.2.** A linear change makes the order on the last axis equal to the
total order. Positive ambient dimension is explicit; units are permitted and give
order zero. Evaluate the leading homogeneous part at a point with nonzero last
coordinate; the higher-order remainder cannot cancel it along the resulting line. -/
theorem exists_coordinate_change_order {f : (Fin (n + 1) → ℂ) → ℂ}
    (hf : AnalyticAt ℂ f 0) (hne : ofAnalyticAt f hf ≠ 0) :
    ∃ L : (Fin (n + 1) → ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ),
      analyticOrderAt (fun w : ℂ => f (L (Pi.single (Fin.last n) w))) 0 =
        order (ofAnalyticAt f hf) := by
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (show order (ofAnalyticAt f hf) ≠ ⊤ from fun h => hne ((order_eq_top_iff _).mp h))
  let p := taylorSeries (ofAnalyticAt f hf)
  let q := MvPowerSeries.truncTotal (d + 1) p
  have hp : p.order = d := hd.symm
  have hqcoeff (k : Fin (n + 1) →₀ ℕ) : q.coeff k =
      if k.degree < d + 1 then MvPowerSeries.coeff k p else 0 :=
    MvPowerSeries.coeff_truncTotal_eq_ite p
  have hqdeg (k : Fin (n + 1) →₀ ℕ) (hk : k ∈ q.support) : k.degree = d := by
    have hn := MvPolynomial.mem_support_iff.mp hk
    rw [hqcoeff] at hn
    split_ifs at hn with hlt
    · have hge : d ≤ k.degree := by
        by_contra! h
        exact hn (MvPowerSeries.coeff_of_lt_order (by simpa [hp] using h))
      omega
    · exact (hn rfl).elim
  have hqne : q ≠ 0 := by
    obtain ⟨k, hk, hkd⟩ := (order_eq_nat_iff (ofAnalyticAt f hf) d).mp hd.symm |>.1
    intro hq
    have h := congrArg (fun q : MvPolynomial (Fin (n + 1)) ℂ => q.coeff k) hq
    simp only [hqcoeff, hkd, Nat.lt_succ_self, ite_true, AddMonoidAlgebra.coeff_zero] at h
    exact hk h
  obtain ⟨v, hv⟩ : ∃ v : Fin (n + 1) → ℂ,
      MvPolynomial.eval v (q * MvPolynomial.X (Fin.last n)) ≠ 0 := by
    by_contra! h
    exact (mul_ne_zero hqne (MvPolynomial.X_ne_zero _))
      (MvPolynomial.funext fun z => by simpa using h z)
  have hvq : MvPolynomial.eval v q ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hv)).1
  have hvi : v (Fin.last n) ≠ 0 := (mul_ne_zero_iff.mp (by simpa using hv)).2
  have hqline (w : ℂ) : MvPolynomial.eval (w • v) q = w ^ d * MvPolynomial.eval v q := by
    simp only [MvPolynomial.eval_eq', Pi.smul_apply, smul_eq_mul, mul_pow,
      Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hqdeg k hk]
    ring
  let g : (Fin (n + 1) → ℂ) → ℂ := fun z => MvPolynomial.eval z q
  have hg : AnalyticAt ℂ g 0 :=
    AnalyticAt.aeval_mvPolynomial (fun i => analyticAt_pi_iff.mp analyticAt_id i) q
  have ht : taylorSeries (ofAnalyticAt g hg) = q := holomorphicTaylorSeries_eval q
  have hr : (d + 1 : ℕ) ≤ order (ofAnalyticAt (f - g) (hf.sub hg)) := by
    have hs : taylorSeries (ofAnalyticAt (f - g) (hf.sub hg)) = p - q := by
      have heq : ofAnalyticAt (f - g) (hf.sub hg) + ofAnalyticAt g hg =
          ofAnalyticAt f hf := by
        rw [← ofAnalyticAt_add]
        apply ofAnalyticAt_eq_iff.mpr
        exact .of_forall fun z => sub_add_cancel _ _
      have h := congrArg taylorSeries heq
      rw [taylorSeries_add, ht] at h
      exact eq_sub_of_add_eq h
    apply MvPowerSeries.nat_le_order
    intro k hk
    rw [hs, map_sub, MvPolynomial.coeff_coe, hqcoeff, ite_eq_left hk, sub_self]
  have hrem := le_trans hr (order_le_analyticOrderAt_line (hf.sub hg) v)
  have hgo : analyticOrderAt (fun w : ℂ => g (w • v)) 0 = d := by
    apply (AnalyticAt.analyticOrderAt_eq_natCast
      (hg.comp_of_eq (analyticAt_id.smul analyticAt_const) (by simp))).mpr
    refine ⟨fun _ => MvPolynomial.eval v q, analyticAt_const, hvq, ?_⟩
    exact .of_forall fun w => by simpa [g, sub_zero, smul_eq_mul] using hqline w
  have hlt : analyticOrderAt (fun w : ℂ => g (w • v)) 0 <
      analyticOrderAt (fun w : ℂ => (f - g) (w • v)) 0 := by
    rw [hgo]
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d) hrem
  have hsum := analyticOrderAt_add_eq_left_of_lt hlt
  have hfo : analyticOrderAt (fun w : ℂ => f (w • v)) 0 = d := by
    have heq : (fun w : ℂ => g (w • v)) + (fun w : ℂ => (f - g) (w • v)) =
        fun w : ℂ => f (w • v) := by
      funext w
      dsimp
      ring
    rw [heq, hgo] at hsum
    exact hsum
  refine ⟨(shearToLastAxis v (Fin.last n) hvi).toContinuousLinearEquiv, ?_⟩
  simpa only [LinearEquiv.coe_toContinuousLinearEquiv', shearToLastAxis_single, hd] using hfo

end SeveralComplexVariables.AnalyticGerm

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
