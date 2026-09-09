/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.NavierStokes.AxisOperators

/-!
# The natural-axis resolvent from factorial decay of radial shifts

The inverse is constructed by a norm-convergent alternating series. No
small-operator-norm hypothesis is used. The generic Banach-ring lemmas isolate
the analytic implication of the factorial estimate from its radial proof.
-/

@[expose] public section


noncomputable section

namespace NavierStokes.AxisResolvent

open scoped BigOperators Topology
open Filter

/-- Cache the standard `NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε)` instance to
shorten typeclass synthesis. -/
local instance instAxisResolvent1 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedAddCommGroup (AxisCoefficientSpace.AxisSpace I ε) := inferInstance
/-- Cache the standard `NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε)` instance to shorten
typeclass synthesis. -/
local instance instAxisResolvent2 (I : AxisCoefficientSpace.Window) (ε : ℝ) :
    NormedSpace ℝ (AxisCoefficientSpace.AxisSpace I ε) := inferInstance

/-- The majorant produced by `k` applications of the regular radial inverse. -/
def factorialMajorant (K : ℝ) (k : ℕ) : ℝ :=
  K ^ k / ((k.factorial : ℝ) * ((k + 1).factorial : ℝ))

theorem factorialMajorant_nonneg {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    0 ≤ factorialMajorant K k := by
  unfold factorialMajorant
  positivity

theorem factorialMajorant_le_exp_term {K : ℝ} (hK : 0 ≤ K) (k : ℕ) :
    factorialMajorant K k ≤ K ^ k / (k.factorial : ℝ) := by
  have hk : (0 : ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have hk1 : (1 : ℝ) ≤ ((k + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (k + 1)
  apply div_le_div_of_nonneg_left (pow_nonneg hK k) hk
  nlinarith

theorem summable_factorialMajorant {K : ℝ} (hK : 0 ≤ K) :
    Summable (factorialMajorant K) := by
  apply Summable.of_norm_bounded
    (Real.summable_pow_div_factorial K)
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (factorialMajorant_nonneg hK k)]
  exact factorialMajorant_le_exp_term hK k

@[simp] theorem factorialMajorant_zero (K : ℝ) : factorialMajorant K 0 = 1 := by
  norm_num [factorialMajorant]

theorem factorialMajorant_succ (K : ℝ) (k : ℕ) :
    factorialMajorant K (k + 1) =
      (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * factorialMajorant K k := by
  have hf : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h₁ : (k : ℝ) + 1 ≠ 0 := by positivity
  have h₂ : (k : ℝ) + 2 ≠ 0 := by positivity
  simp only [factorialMajorant, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp; ring

section RadialJets

open AxisWeightEstimates

/-- All parameter jets below a prescribed radial degree vanish. -/
def JetVanishesBelow (f : ℕ → ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ n, n < k → ∀ m, f n m = 0

theorem jetProduct_vanishesBelow_right (f g : ℕ → ℕ → ℝ) (k : ℕ)
    (hg : JetVanishesBelow g k) : JetVanishesBelow (jetProduct f g) k := by
  intro n hn m
  unfold jetProduct
  apply Finset.sum_eq_zero
  intro ij hij
  apply Finset.sum_eq_zero
  intro kl _
  have hij' := Finset.mem_antidiagonal.mp hij
  rw [hg ij.2 (by omega) kl.2, mul_zero]

theorem regularInverseJet_vanishesBelow (f : ℕ → ℕ → ℝ) (k : ℕ)
    (hf : JetVanishesBelow f k) :
    JetVanishesBelow (regularInverseJet 2 f) (k + 1) := by
  intro n hn m
  cases n with
  | zero => rfl
  | succ n =>
      change f n m / radialDivisor 2 n = 0
      rw [hf n (by omega) m, zero_div]

theorem radialDivisor_two_mono {k n : ℕ} (hkn : k ≤ n) :
    radialDivisor 2 k ≤ radialDivisor 2 n := by
  have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
  unfold radialDivisor
  norm_num
  gcongr

/-- A radial inverse has a better norm bound on profiles whose first `k`
radial coefficients vanish. This is the source of the two factorials. -/
theorem regularInverseJet_bound_on_order {ε F : ℝ} (hε : 0 < ε) (hF : 0 ≤ F)
    (f : ℕ → ℕ → ℝ) (k : ℕ) (hz : JetVanishesBelow f k)
    (hf : ∀ n m, |f n m| ≤ F * weight ε n m) (n m : ℕ) :
    |regularInverseJet 2 f n m| ≤
      (80 / radialDivisor 2 k) * F * weight ε n m := by
  have hd : 0 < radialDivisor 2 k := radialDivisor_pos (by norm_num) k
  cases n with
  | zero =>
      simp only [regularInverseJet, abs_zero]
      exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hd.le) hF)
        (weight_pos hε 0 m).le
  | succ n =>
      by_cases hn : n < k
      · simp only [regularInverseJet, hz n hn m, zero_div, abs_zero]
        exact mul_nonneg (mul_nonneg (div_nonneg (by norm_num) hd.le) hF)
          (weight_pos hε (n + 1) m).le
      · have hkn : k ≤ n := by omega
        rw [regularInverseJet, abs_div,
          abs_of_pos (radialDivisor_pos (by norm_num : 1 ≤ 2) n)]
        calc
          |f n m| / radialDivisor 2 n ≤ |f n m| / radialDivisor 2 k :=
            div_le_div_of_nonneg_left (abs_nonneg _) hd (radialDivisor_two_mono hkn)
          _ ≤ (F * weight ε n m) / radialDivisor 2 k :=
            div_le_div_of_nonneg_right (hf n m) hd.le
          _ ≤ (F * (80 * weight ε (n + 1) m)) / radialDivisor 2 k :=
            div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_left (weight_radial_shift hε n m) hF) hd.le
          _ = _ := by ring

end RadialJets

section BanachRing

variable {R : Type*} [NormedRing R]

theorem norm_neg_pow_eq (Q : R) (k : ℕ) : ‖(-Q) ^ k‖ = ‖Q ^ k‖ := by
  rcases Nat.even_or_odd k with hk | hk
  · rw [hk.neg_pow]
  · rw [hk.neg_pow, norm_neg]

/-- The alternating series itself, as an element of the ambient Banach ring. -/
def alternatingResolvent (Q : R) : R := ∑' k : ℕ, (-Q) ^ k

/-- A summable geometric family gives an exact left inverse, even when the
norm of its ratio is not less than one. -/
theorem one_sub_mul_tsum_pow {Q : R} (hs : Summable (fun k : ℕ => Q ^ k)) :
    (1 - Q) * (∑' k : ℕ, Q ^ k) = 1 := by
  have h := hs.hasSum.mul_left (1 - Q)
  refine tendsto_nhds_unique h.tendsto_sum_nat ?_
  have hz : Tendsto (fun k : ℕ => 1 - Q ^ k) atTop (𝓝 (1 : R)) := by
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  convert! ← hz using 1
  funext k
  rw [← mul_neg_geom_sum, Finset.mul_sum]

/-- The same convergent series is also a right inverse in a possibly
noncommutative ring. -/
theorem tsum_pow_mul_one_sub {Q : R} (hs : Summable (fun k : ℕ => Q ^ k)) :
    (∑' k : ℕ, Q ^ k) * (1 - Q) = 1 := by
  have h := hs.hasSum.mul_right (1 - Q)
  refine tendsto_nhds_unique h.tendsto_sum_nat ?_
  have hz : Tendsto (fun k : ℕ => 1 - Q ^ k) atTop (𝓝 (1 : R)) := by
    simpa using tendsto_const_nhds.sub hs.tendsto_atTop_zero
  convert! ← hz using 1
  funext k
  rw [← geom_sum_mul_neg, Finset.sum_mul]

theorem summable_norm_neg_pow_of_factorial_bound (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    Summable (fun k : ℕ => ‖(-Q) ^ k‖) := by
  apply Summable.of_norm_bounded (summable_factorialMajorant hK)
  intro k
  simpa only [norm_norm, norm_neg_pow_eq] using hQ k

variable [CompleteSpace R]

theorem summable_neg_pow_of_factorial_bound (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    Summable (fun k : ℕ => (-Q) ^ k) :=
  (summable_norm_neg_pow_of_factorial_bound Q hK hQ).of_norm

theorem hasSum_alternatingResolvent (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    HasSum (fun k : ℕ => (-Q) ^ k) (alternatingResolvent Q) :=
  (summable_neg_pow_of_factorial_bound Q hK hQ).hasSum

theorem one_add_mul_alternatingResolvent (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    (1 + Q) * alternatingResolvent Q = 1 := by
  simpa only [alternatingResolvent, sub_neg_eq_add] using
    one_sub_mul_tsum_pow (summable_neg_pow_of_factorial_bound Q hK hQ)

theorem alternatingResolvent_mul_one_add (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    alternatingResolvent Q * (1 + Q) = 1 := by
  simpa only [alternatingResolvent, sub_neg_eq_add] using
    tsum_pow_mul_one_sub (summable_neg_pow_of_factorial_bound Q hK hQ)

omit [CompleteSpace R] in
theorem norm_alternatingResolvent_le (Q : R) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) :
    ‖alternatingResolvent Q‖ ≤ ∑' k : ℕ, factorialMajorant K k := by
  apply (norm_tsum_le_tsum_norm
    (summable_norm_neg_pow_of_factorial_bound Q hK hQ)).trans
  apply Summable.tsum_le_tsum
    (fun k => by simpa only [norm_neg_pow_eq] using hQ k)
    (summable_norm_neg_pow_of_factorial_bound Q hK hQ)
    (summable_factorialMajorant hK)

end BanachRing

section BanachOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Iteration through the radial-degree filtration gives a factorial bound
for the actual operator powers. No bound less than one is assumed. -/
theorem pow_bound_of_filtration (Q : E →L[ℝ] E) (P : ℕ → E → Prop)
    {K : ℝ} (hK : 0 ≤ K) (hzero : ∀ x, P 0 x)
    (hstep : ∀ k x, P k x → P (k + 1) (Q x))
    (hbound : ∀ k x, P k x →
      ‖Q x‖ ≤ (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * ‖x‖) :
    ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k := by
  have hp : ∀ k x, P k ((Q ^ k) x) ∧
      ‖(Q ^ k) x‖ ≤ factorialMajorant K k * ‖x‖ := by
    intro k
    induction k with
    | zero =>
        intro x
        simpa using And.intro (hzero x) (le_refl ‖x‖)
    | succ k ih =>
        intro x
        rw [pow_succ', _root_.mul_apply_eq_comp]
        refine ⟨hstep k _ (ih x).1, ?_⟩
        calc
          ‖Q ((Q ^ k) x)‖ ≤
              (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) * ‖(Q ^ k) x‖ :=
            hbound k _ (ih x).1
          _ ≤ (K / (((k : ℝ) + 1) * ((k : ℝ) + 2))) *
              (factorialMajorant K k * ‖x‖) :=
            mul_le_mul_of_nonneg_left (ih x).2 (by positivity)
          _ = factorialMajorant K (k + 1) * ‖x‖ := by
            rw [factorialMajorant_succ]
            ring
  intro k
  exact ContinuousLinearMap.opNorm_le_bound _ (factorialMajorant_nonneg hK k)
    (fun x => (hp k x).2)

/-- Pointwise form of the inverse equation used in the nonlinear fixed-point map. -/
theorem one_add_apply_alternatingResolvent (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    (1 + Q) (alternatingResolvent Q x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x)
    (one_add_mul_alternatingResolvent Q hK hQ)
  simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h

theorem alternatingResolvent_apply_one_add (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    alternatingResolvent Q ((1 + Q) x) = x := by
  have h := congrArg (fun T : E →L[ℝ] E => T x)
    (alternatingResolvent_mul_one_add Q hK hQ)
  simpa only [_root_.mul_apply_eq_comp, _root_.one_apply_eq_self] using h

theorem alternatingResolvent_equation (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) (x : E) :
    alternatingResolvent Q x + Q (alternatingResolvent Q x) = x := by
  simpa only [_root_.add_apply, _root_.one_apply_eq_self] using
    one_add_apply_alternatingResolvent Q hK hQ x

/-- The inverse gives the unique solution of the integrated linear equation. -/
theorem alternatingResolvent_unique (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k)
    {x b : E} (hx : x + Q x = b) : x = alternatingResolvent Q b := by
  calc
    x = alternatingResolvent Q ((1 + Q) x) :=
      (alternatingResolvent_apply_one_add Q hK hQ x).symm
    _ = alternatingResolvent Q b := by
      exact congrArg (fun y => alternatingResolvent Q y)
        (by simpa only [_root_.add_apply, _root_.one_apply_eq_self] using hx)

/-- Both continuous directions are constructed explicitly from the series. -/
def oneAddEquiv (Q : E →L[ℝ] E) {K : ℝ} (hK : 0 ≤ K)
    (hQ : ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant K k) : E ≃L[ℝ] E where
  toLinearEquiv :=
    { (1 + Q).toLinearMap with
      invFun := fun x => alternatingResolvent Q x
      left_inv := alternatingResolvent_apply_one_add Q hK hQ
      right_inv := one_add_apply_alternatingResolvent Q hK hQ }
  continuous_toFun := (1 + Q).continuous
  continuous_invFun := (alternatingResolvent Q).continuous

end BanachOperators

section AxisOperators

open AxisCoefficientSpace AxisWeightEstimates

/-- Radial order in the actual compatible coefficient space. -/
def AxisVanishesBelow (I : Window) (ε : ℝ) (A : AxisSpace I ε) (k : ℕ) : Prop :=
  ∀ x : I.interval, JetVanishesBelow (fun n m => jet I (weight ε) A.1 n m x) k

theorem axis_abs_jet_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (n m : ℕ) (x : ℝ) :
    |jet I (weight ε) A.1 n m x| ≤ ‖A‖ * weight ε n m := by
  simpa only [abs_of_pos (weight_pos hε n m), mul_comm] using
    abs_jet_le I (weight ε) A n m x

theorem axis_norm_le_of_jet_bound (I : Window) {ε C : ℝ} (hε : 0 < ε)
    (A : AxisSpace I ε) (hC : 0 ≤ C)
    (hA : ∀ n m (x : I.interval), |jet I (weight ε) A.1 n m x| ≤ C * weight ε n m) :
    ‖A‖ ≤ C := by
  apply (axisSpace_norm_le_iff I hε A C hC).2
  intro n m x
  rw [iteratedDerivWithin_coefficient I (weight ε) A n m x.property]
  exact (div_le_iff₀ (weight_pos hε n m)).2 (hA n m x)

/-- The concrete jet identity for `(1/2) J₂ Mχ`. This records the operation,
not any inverse or spectral property. It allows the estimate to be applied to
any compatible construction of the two bounded operators. -/
def IsAxisLinearOperator (I : Window) (ε : ℝ) (χ : AxisSpace I ε)
    (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε) : Prop :=
  ∀ A n m (x : I.interval),
    jet I (weight ε) (Q A).1 n m x = (1 / 2 : ℝ) *
      regularInverseJet 2
        (jetProduct (fun i j => jet I (weight ε) χ.1 i j x)
          (fun i j => jet I (weight ε) A.1 i j x)) n m

theorem axisLinearOperator_increases_order (I : Window) {ε : ℝ}
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (k : ℕ) (A : AxisSpace I ε)
    (hA : AxisVanishesBelow I ε A k) : AxisVanishesBelow I ε (Q A) (k + 1) := by
  intro x n hn m
  change jet I (weight ε) (Q A).1 n m x = 0
  rw [hQ A n m x]
  have hz := regularInverseJet_vanishesBelow
    (jetProduct (fun i j => jet I (weight ε) χ.1 i j x)
      (fun i j => jet I (weight ε) A.1 i j x)) k
    (jetProduct_vanishesBelow_right
      (fun i j => jet I (weight ε) χ.1 i j x)
      (fun i j => jet I (weight ε) A.1 i j x) k (hA x))
  rw [hz n hn m, mul_zero]

theorem axisLinearOperator_bound_on_order (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (k : ℕ) (A : AxisSpace I ε)
    (hA : AxisVanishesBelow I ε A k) :
    ‖Q A‖ ≤ (2560 * ‖χ‖ / radialDivisor 2 k) * ‖A‖ := by
  have hd : 0 < radialDivisor 2 k := radialDivisor_pos (by norm_num) k
  apply axis_norm_le_of_jet_bound I hε (Q A) (by positivity)
  intro n m x
  let f : ℕ → ℕ → ℝ := fun i j => jet I (weight ε) χ.1 i j x
  let g : ℕ → ℕ → ℝ := fun i j => jet I (weight ε) A.1 i j x
  have hp : ∀ i j, |jetProduct f g i j| ≤
      (64 * ‖χ‖ * ‖A‖) * weight ε i j :=
    jetProduct_bound hε (norm_nonneg χ) (norm_nonneg A) f g
      (fun i j => axis_abs_jet_le I hε χ i j x)
      (fun i j => axis_abs_jet_le I hε A i j x)
  have hz : JetVanishesBelow (jetProduct f g) k :=
    jetProduct_vanishesBelow_right f g k (hA x)
  have hj := regularInverseJet_bound_on_order hε
    (show 0 ≤ 64 * ‖χ‖ * ‖A‖ by positivity) (jetProduct f g) k hz hp n m
  rw [hQ A n m x, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  change (1 / 2 : ℝ) * |regularInverseJet 2 (jetProduct f g) n m| ≤ _
  calc
    (1 / 2 : ℝ) * |regularInverseJet 2 (jetProduct f g) n m| ≤
        (1 / 2 : ℝ) * ((80 / radialDivisor 2 k) *
          (64 * ‖χ‖ * ‖A‖) * weight ε n m) :=
      mul_le_mul_of_nonneg_left hj (by norm_num)
    _ = _ := by ring

/-- The actual weighted radial estimate: any operator with the stated
`(1/2) J₂ Mχ` coefficients has factorial-decaying powers. The multiplier may
even depend on the radial variable; the natural-axis multiplier is a special case. -/
theorem axisLinearOperator_pow_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) :
    ∀ k : ℕ, ‖Q ^ k‖ ≤ factorialMajorant (2560 * ‖χ‖) k := by
  apply pow_bound_of_filtration Q (fun k A => AxisVanishesBelow I ε A k)
    (by positivity)
  · intro A x n hn
    omega
  · exact axisLinearOperator_increases_order I χ Q hQ
  · intro k A hA
    simpa only [radialDivisor, Nat.cast_ofNat] using
      axisLinearOperator_bound_on_order I hε χ Q hQ k A hA

theorem axisLinearOperator_resolvent_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (Q : AxisSpace I ε →L[ℝ] AxisSpace I ε)
    (hQ : IsAxisLinearOperator I ε χ Q) (A : AxisSpace I ε) :
    alternatingResolvent Q A + Q (alternatingResolvent Q A) = A :=
  alternatingResolvent_equation Q (by positivity)
    (axisLinearOperator_pow_bound I hε χ Q hQ) A

/-- The exact bounded operator in the natural angular equation. -/
def naturalOperator (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε :=
  (1 / 2 : ℝ) • ((AxisOperators.regularInverse I hε 2 (by norm_num)).comp
    (AxisOperators.product I hε χ))

theorem naturalOperator_isAxisLinearOperator (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) : IsAxisLinearOperator I ε χ (naturalOperator I hε χ) := by
  intro A n m x
  simp only [naturalOperator, _root_.smul_apply, ContinuousLinearMap.comp_apply,
    Submodule.coe_smul, jet_smul]
  cases n with
  | zero =>
      have hz := AxisOperators.jet_regularInverse_zero I hε 2 (by norm_num)
        (AxisOperators.product I hε χ A) m x.property
      dsimp only [AxisOperators.inputJet] at hz
      rw [hz]
      rfl
  | succ n =>
      have hs := AxisOperators.jet_regularInverse_succ I hε 2 (by norm_num)
        (AxisOperators.product I hε χ A) n m x.property
      have hp := AxisOperators.jet_product I hε χ A n m x.property
      dsimp only [AxisOperators.inputJet] at hs hp
      rw [hs, hp]
      rfl

/-- The operator norm has factorial decay with an explicit constant. -/
theorem naturalOperator_pow_bound (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) (k : ℕ) :
    ‖naturalOperator I hε χ ^ k‖ ≤ factorialMajorant (2560 * ‖χ‖) k :=
  axisLinearOperator_pow_bound I hε χ _ (naturalOperator_isAxisLinearOperator I hε χ) k

/-- The linear resolvent used in the nonlinear natural-axis contraction. -/
def naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε →L[ℝ] AxisSpace I ε := alternatingResolvent (naturalOperator I hε χ)

theorem naturalResolvent_hasSum (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    HasSum (fun k : ℕ => (-naturalOperator I hε χ) ^ k) (naturalResolvent I hε χ) :=
  hasSum_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem naturalResolvent_norm_le (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    ‖naturalResolvent I hε χ‖ ≤ ∑' k : ℕ, factorialMajorant (2560 * ‖χ‖) k :=
  norm_alternatingResolvent_le _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem one_add_mul_naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    (1 + naturalOperator I hε χ) * naturalResolvent I hε χ = 1 :=
  one_add_mul_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem naturalResolvent_mul_one_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) :
    naturalResolvent I hε χ * (1 + naturalOperator I hε χ) = 1 :=
  alternatingResolvent_mul_one_add _ (by positivity) (naturalOperator_pow_bound I hε χ)

theorem one_add_apply_naturalResolvent (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    (1 + naturalOperator I hε χ) (naturalResolvent I hε χ A) = A :=
  one_add_apply_alternatingResolvent _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_apply_one_add (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    naturalResolvent I hε χ ((1 + naturalOperator I hε χ) A) = A :=
  alternatingResolvent_apply_one_add _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_equation (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ A : AxisSpace I ε) :
    naturalResolvent I hε χ A + naturalOperator I hε χ (naturalResolvent I hε χ A) = A :=
  alternatingResolvent_equation _ (by positivity) (naturalOperator_pow_bound I hε χ) A

theorem naturalResolvent_unique (I : Window) {ε : ℝ} (hε : 0 < ε)
    (χ : AxisSpace I ε) {A b : AxisSpace I ε}
    (hA : A + naturalOperator I hε χ A = b) : A = naturalResolvent I hε χ b :=
  alternatingResolvent_unique _ (by positivity) (naturalOperator_pow_bound I hε χ) hA

/-- In particular, the reference angular profile is obtained by applying this
map to the constant coefficient representing `1`. -/
def naturalEquationEquiv (I : Window) {ε : ℝ} (hε : 0 < ε) (χ : AxisSpace I ε) :
    AxisSpace I ε ≃L[ℝ] AxisSpace I ε :=
  oneAddEquiv _ (by positivity) (naturalOperator_pow_bound I hε χ)

end AxisOperators

end NavierStokes.AxisResolvent

end
