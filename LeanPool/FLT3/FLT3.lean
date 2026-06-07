/-
Copyright (c) 2026 Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Sanyam Gupta, Omar Haddad, David Lowry-Duda, Lorenzo Luccioli, Pietro Monticone, Alexis Saurin, Florent Schaffhauser
-/
import Mathlib.NumberTheory.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Three
import Mathlib.NumberTheory.FLT.Three
import LeanPool.FLT3.Cyclo

/-!
# Fermat's Last Theorem for Exponent `n = 3`
The goal of this file is to prove Fermat's Last Theorem for exponent `3`, namely that
for all `a`, `b`, `c` in `ℕ` such that `a ≠ 0` and `b ≠ 0` and `c ≠ 0`,
then `a ^ 3 + b ^ 3 ≠ c ^ 3`.
-/

open NumberField nonZeroDivisors IsCyclotomicExtension.Rat.Three

section case2

section eisenstein

attribute [instance] IsCyclotomicExtension.Rat.three_pid

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]

attribute [-instance] ValuationRing.instIsBezout -- This seems to be a very slow instance

-- This takes Lean some time, so let's do it here once
local instance : IsBezout (𝓞 K) := by infer_instance

noncomputable
instance : NormalizedGCDMonoid (𝓞 K) :=
  have : Nonempty (NormalizedGCDMonoid (𝓞 K)) := inferInstance
  this.some

variable {ζ : K} (hζ : IsPrimitiveRoot ζ (3 : ℕ+))

local notation3 "η" => (IsPrimitiveRoot.isUnit (hζ.toInteger_isPrimitiveRoot) (by decide)).unit
local notation3 "λ" => hζ.toInteger - 1

namespace FermatLastTheoremForThreeGen
section Solution'

variable {hζ} (S : Solution' hζ)

/-- Given `S : Solution'`, then `S.a` and `S.b` are both congruent to `1` modulo `λ ^ 4` or are
both congruent to `-1`.  -/
lemma a_cube_b_cube_same_congr :
    λ ^ 4 ∣ S.a ^ 3 - 1 ∧ λ ^ 4 ∣ S.b ^ 3 + 1 ∨  λ ^ 4 ∣ S.a ^ 3 + 1 ∧ λ ^ 4 ∣ S.b ^ 3 - 1 := by
  obtain ⟨z, hz⟩ := S.hcdvd
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.ha with
    (⟨x, hx⟩ | ⟨x, hx⟩) <;>
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.hb with
    (⟨y, hy⟩ | ⟨y, hy⟩)
  · exfalso
    refine lambda_not_dvd_two hζ ⟨S.u * λ ^ 2 * z ^ 3 - λ ^ 3 * (x + y), ?_⟩
    symm
    calc _ = S.u * (λ * z) ^ 3 - λ ^ 4 * x - λ ^ 4 * y := by ring
    _ = (S.a ^ 3 + S.b ^ 3) - (S.a ^ 3 - 1) - (S.b ^ 3 - 1) := by rw [← hx, ← hy, ← hz, ← S.H]
    _ = 2 := by ring
  · left
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · right
    exact ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  · exfalso
    refine lambda_not_dvd_two hζ ⟨λ ^ 3 * (x + y) - S.u * λ ^ 2 * z ^ 3, ?_⟩
    symm
    calc _ =  λ ^ 4 * x + λ ^ 4 * y - S.u * (λ * z) ^ 3 := by ring
    _ = (S.a ^ 3 + 1) + (S.b ^ 3 + 1) - (S.a ^ 3 + S.b ^ 3) := by rw [← hx, ← hy, ← hz, ← S.H]
    _ = 2 := by ring

/-- Given `S : Solution'`, we have that `λ ^ 4` divides `S.c ^ 3`. -/
lemma lambda_pow_four_dvd_c_cube : λ ^ 4 ∣ S.c ^ 3 := by
  rcases a_cube_b_cube_same_congr S with
    (⟨⟨x, hx⟩, ⟨y, hy⟩⟩ | ⟨⟨x, hx⟩, ⟨y, hy⟩⟩) <;> {
  refine ⟨S.u⁻¹ * (x + y), ?_⟩
  symm
  calc _ = S.u⁻¹ * (λ ^ 4 * x + λ ^ 4 * y) := by ring
  _ = S.u⁻¹ * (S.a ^ 3 + S.b ^ 3) := by rw [← hx, ← hy]; ring
  _ = S.u⁻¹ * (S.u * S.c ^ 3) := by rw [S.H]
  _ = S.c ^ 3 := by simp }

/-- Given `S : Solution'`, we have that `λ ^ 2` divides `S.c`. -/
lemma lambda_pow_two_dvd_c : λ ^ 2 ∣ S.c := by
  classical
  have  hm := S.multiplicity_lambda_c_finite
  suffices 2 ≤ (multiplicity ((hζ.toInteger - 1)) S.c).get hm by
    · obtain ⟨x, hx⟩ := multiplicity.pow_multiplicity_dvd hm
      refine ⟨λ ^ ((multiplicity ((hζ.toInteger - 1)) S.c).get hm - 2) * x, ?_⟩
      rw [← mul_assoc, ← pow_add]
      convert hx using 3
      simp [this]
  have := lambda_pow_four_dvd_c_cube S
  have hm1 :(multiplicity (hζ.toInteger - 1) (S.c ^ 3)).get
    (multiplicity.finite_pow hζ.zeta_sub_one_prime' hm) =
    multiplicity (hζ.toInteger - 1) (S.c ^ 3) := by simp
  rw [multiplicity.pow_dvd_iff_le_multiplicity, ← hm1, multiplicity.pow' hζ.zeta_sub_one_prime' hm,
    Nat.cast_ofNat, Nat.ofNat_le_cast] at this
  linarith

variable [DecidableRel fun (a b : 𝓞 K) ↦ a ∣ b]

/-- Given `S : Solution'`, we have that `2 ≤ S.multiplicity`. -/
lemma Solution'.two_le_multiplicity : 2 ≤ S.multiplicity := by
  simpa [← PartENat.coe_le_coe, Solution'.multiplicity] using
    multiplicity.le_multiplicity_of_pow_dvd (lambda_pow_two_dvd_c S)

/-- Given `S : Solution`, we have that `2 ≤ S.multiplicity`. -/
lemma Solution.two_le_multiplicity (S : Solution hζ) : 2 ≤ S.multiplicity := by
  exact S.toSolution'.two_le_multiplicity

/-- Given `S : Solution'`, the key factorization of `S.a ^ 3 + S.b ^ 3`. -/
lemma cube_add_cube_eq_mul :
    S.a ^ 3 + S.b ^ 3 = (S.a + S.b) * (S.a + η * S.b) * (S.a + η ^ 2 * S.b) := by
  symm
  calc _ = S.a^3+S.a^2*S.b*(η^2+η+1)+S.a*S.b^2*(η^2+η+η^3)+η^3*S.b^3 := by ring
  _ = S.a^3+S.a^2*S.b*(η^2+η+1)+S.a*S.b^2*(η^2+η+1)+S.b^3 := by
    norm_cast
    simp [hζ.toInteger_cube_eq_one]
  _ = S.a ^ 3 + S.b ^ 3 := by rw [hζ.toInteger_eval_cyclo]; ring

open PartENat in
/-- Given `S : Solution'`, we have that `λ ^ 2` divides one amongst `S.a + S.b`,
`S.a + η * S.b` and `S.a + η ^ 2 * S.b`. -/
lemma lambda_sq_dvd_or_dvd_or_dvd :
    λ ^ 2 ∣ S.a + S.b ∨ λ ^ 2 ∣ S.a + η * S.b ∨ λ ^ 2 ∣ S.a + η ^ 2 * S.b := by
  classical
  by_contra! h
  rcases h with ⟨h1, h2, h3⟩
  rw [← multiplicity.multiplicity_lt_iff_not_dvd] at h1 h2 h3
  have h1' : multiplicity.Finite (hζ.toInteger - 1) (S.a + S.b) :=
    multiplicity.ne_top_iff_finite.1 (fun ht ↦ by simp [ht] at h1)
  have h2' : multiplicity.Finite (hζ.toInteger - 1) (S.a + η * S.b) := by
    refine multiplicity.ne_top_iff_finite.1 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h2
  have h3' : multiplicity.Finite (hζ.toInteger - 1) (S.a + η ^ 2 * S.b) := by
    refine multiplicity.ne_top_iff_finite.1 (fun ht ↦ ?_)
    rw [coe_eta] at ht
    simp [ht] at h3
  replace h1' : (multiplicity (hζ.toInteger - 1) (S.a + S.b)).get h1' =
    multiplicity (hζ.toInteger - 1) (S.a + S.b) := by simp
  replace h2' : (multiplicity (hζ.toInteger - 1) (S.a + η * S.b)).get h2' =
    multiplicity (hζ.toInteger - 1) (S.a + η * S.b) := by simp
  replace h3' : (multiplicity (hζ.toInteger - 1) (S.a + η ^ 2 * S.b)).get h3' =
    multiplicity (hζ.toInteger - 1) (S.a + η ^ 2 * S.b) := by simp
  rw [← h1', coe_lt_coe] at h1; rw [← h2', coe_lt_coe] at h2; rw [← h3', coe_lt_coe] at h3
  have := (pow_dvd_pow_of_dvd (lambda_pow_two_dvd_c S) 3).mul_left S.u
  rw [← pow_mul, ← S.H, cube_add_cube_eq_mul, multiplicity.pow_dvd_iff_le_multiplicity,
    multiplicity.mul hζ.zeta_sub_one_prime', multiplicity.mul hζ.zeta_sub_one_prime', ← h1', ← h2',
    ← h3', ← Nat.cast_add, ← Nat.cast_add, coe_le_coe] at this
  omega

open Units in
/-- Given `S : Solution'`, we may assume that `λ ^ 2` divides `S.a + S.b ∨ λ ^ 2` (see also the
result below). -/
lemma ex_dvd_a_add_b : ∃ (a' b' : 𝓞 K), a' ^ 3 + b' ^ 3 = S.u * S.c ^ 3 ∧
    IsCoprime a' b' ∧ ¬ λ ∣ a' ∧ ¬ λ ∣ b' ∧ λ ^ 2 ∣ a' + b' := by
  rcases lambda_sq_dvd_or_dvd_or_dvd S with (h | h | h)
  · exact ⟨S.a, S.b, S.H, S.coprime, S.ha, S.hb, h⟩
  · refine ⟨S.a, η * S.b, ?_, ?_, S.ha, fun ⟨x, hx⟩ ↦ S.hb ⟨η ^ 2 * x, ?_⟩, h⟩
    · rw [mul_pow, ← val_pow_eq_pow_val, hζ.toInteger_cube_eq_one, val_one, one_mul, S.H]
    · refine (isCoprime_mul_unit_left_right (Units.isUnit η) _ _).2 S.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S.b, mul_assoc, ← pow_succ',
        ← val_pow_eq_pow_val, hζ.toInteger_cube_eq_one, val_one, mul_one]
  · refine ⟨S.a, η ^ 2 * S.b, ?_, ?_, S.ha, fun ⟨x, hx⟩ ↦ S.hb ⟨η * x, ?_⟩, h⟩
    · rw [mul_pow, ← pow_mul, mul_comm 2, pow_mul, ← val_pow_eq_pow_val, hζ.toInteger_cube_eq_one,
        val_one, one_pow, one_mul, S.H]
    · exact (isCoprime_mul_unit_left_right ((Units.isUnit η).pow _) _ _).2 S.coprime
    · rw [mul_comm _ x, ← mul_assoc, ← hx, mul_comm _ S.b, mul_assoc, ← pow_succ,
        ← val_pow_eq_pow_val, hζ.toInteger_cube_eq_one, val_one, mul_one]

/-- Given `S : Solution'`, then there is `S₁ : Solution` such that
`S₁.multiplicity = S.multiplicity`. -/
lemma exists_Solution_of_Solution' : ∃ (S₁ : Solution hζ), S₁.multiplicity = S.multiplicity := by
  obtain ⟨a, b, H, coprime, ha, hb, hab⟩ := ex_dvd_a_add_b S
  exact ⟨
  { a := a
    b := b
    c := S.c
    u := S.u
    ha := ha
    hb := hb
    hc := S.hc
    coprime := coprime
    hcdvd := S.hcdvd
    H := H
    hab := hab }, rfl⟩

end Solution'

namespace Solution

variable (S : Solution hζ) {hζ}

lemma a_add_eta_b : S.a + η * S.b = (S.a + S.b) + λ * S.b := by rw [coe_eta]; ring

/-- Given `(S : Solution)`, we have that `λ ∣ (S.a + η * S.b)`. -/
lemma lambda_dvd_a_add_eta_mul_b : λ ∣ (S.a + η * S.b) := by
  rw [a_add_eta_b]
  exact dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨S.b, by rw [mul_comm]⟩

/-- Given `(S : Solution)`, we have that `λ ∣ (S.a + η ^ 2 * S.b)`. -/
lemma lambda_dvd_a_add_eta_sq_mul_b : λ ∣ (S.a + η ^ 2 * S.b) := by
  rw [show S.a + η ^ 2 * S.b = (S.a + S.b) + λ ^ 2 * S.b + 2 * λ * S.b by rw [coe_eta]; ring]
  exact dvd_add (dvd_add (dvd_trans (dvd_pow_self _ (by decide)) S.hab) ⟨λ * S.b, by ring⟩)
    ⟨2 * S.b, by ring⟩

/-- Given `(S : Solution)`, we have that `λ ^ 2` does not divide `S.a + η * S.b`. -/
lemma lambda_sq_not_a_add_eta_mul_b : ¬ λ ^ 2 ∣ (S.a + η * S.b) := by
  simp_rw [a_add_eta_b, dvd_add_right S.hab, pow_two, mul_dvd_mul_iff_left
    hζ.zeta_sub_one_prime'.ne_zero, S.hb, not_false_eq_true]

/-- Given `(S : Solution)`, we have that `λ ^ 2` does not divide `S.a + η ^ 2 * S.b`. -/
lemma lambda_sq_not_dvd_a_add_eta_sq_mul_b : ¬ λ ^ 2 ∣ (S.a + η ^ 2 * S.b) := by
  intro h
  apply S.hb
  rcases h with ⟨k, hk⟩
  rw [show S.a + η ^ 2 * S.b = S.a + S.b - S.b + η ^ 2 * S.b by ring] at hk
  rcases S.hab with ⟨k', hk'⟩
  use (k - k') * (-η)
  rw [hk'] at hk
  rw [show λ ^ 2 * k' - S.b + η ^ 2 * S.b = λ * (S.b * (η +1) + λ * k') by rw [coe_eta]; ring,
    pow_two, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, hζ.zeta_sub_one_prime'.ne_zero, or_false] at hk
  replace hk := congr_arg (fun x => x * (-(η : 𝓞 K))) hk
  simp only at hk
  rw [show (S.b * (η + 1) + λ * k') * -η = (- S.b) * (η ^ 2 + η + 1 - 1) - η * λ * k' by ring] at hk
  rw [hζ.toInteger_eval_cyclo] at hk
  simp only [zero_sub, mul_neg, mul_one, neg_neg] at hk
  rw [sub_eq_iff_eq_add] at hk
  rw [hk]
  ring

lemma eta_add_one_inv : ((η : 𝓞 K) + 1) * (-η) = 1 := by
  calc ((η : 𝓞 K) + 1) * -η = -(η ^ 2 + η + 1) + 1  := by ring
  _ = 1 := by rw [hζ.toInteger_eval_cyclo]; simp

/-- If `p : 𝓞 K` is a prime that divides both `S.a + S.b` and `S.a + η * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpab : p ∣ S.a + S.b) (hpaetab : p ∣ S.a + η * S.b) : Associated p λ := by
  by_cases p_lam : (p ∣ λ)
  · exact hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  have pdivb : p ∣ S.b := by
    have fgh : p ∣ (λ * S.b) := by
      rw [show λ * S.b = (S.a + η * S.b) - (S.a + S.b) by rw [coe_eta]; ring]
      exact dvd_sub hpaetab hpab
    rcases Prime.dvd_or_dvd hp fgh with (h | h)
    · contradiction
    · exact h
  have pdiva : p ∣ S.a := by
    have fgh : p ∣ (λ * S.a) := by
      rw [show λ * S.a = η * (S.a + S.b) - (S.a + η * S.b) by rw [coe_eta]; ring]
      exact dvd_sub (dvd_mul_of_dvd_right hpab _) hpaetab
    rcases Prime.dvd_or_dvd hp fgh with (h | h)
    · tauto
    · exact h
  have punit := IsCoprime.isUnit_of_dvd' S.coprime pdiva pdivb
  exfalso
  exact hp.not_unit punit

/-- If `p : 𝓞 K` is a prime that divides both `S.a + S.b` and `S.a + η ^ 2 * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
  (hpab : p ∣ (S.a + S.b)) (hpaetasqb : p ∣ (S.a + η ^ 2 * S.b)) : Associated p λ := by
  by_cases p_lam : (p ∣ λ)
  · exact hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  have pdivb : p ∣ S.b := by
    have fgh : p ∣ λ * S.b := by
      rw [show λ * S.b = - (1 - η) * S.b by rw [coe_eta]; ring, ← Units.val_one,
        ← hζ.toInteger_cube_eq_one, Units.val_pow_eq_pow_val]
      rw [show - (η ^ 3 - η) * S.b = η * ((S.a + S.b) - (S.a + η ^ 2 * S.b)) by ring]
      rw [(Units.isUnit η).dvd_mul_left]
      exact hpab.sub hpaetasqb
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have pdiva : p ∣ S.a := by
    have fgh : p ∣ λ * S.a := by
      rw [show λ * S.a = - (1 - η) * S.a by rw [coe_eta]; ring, ← Units.val_one,
        ← hζ.toInteger_cube_eq_one, Units.val_pow_eq_pow_val]
      rw [show - (η ^ 3 - η) * S.a = η * ((S.a + η ^ 2 * S.b) - η ^ 2 * (S.a + S.b)) by ring]
      rw [(Units.isUnit η).dvd_mul_left]
      exact hpaetasqb.sub (dvd_mul_of_dvd_right hpab _)
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have punit := S.coprime.isUnit_of_dvd' pdiva pdivb
  exact hp.not_unit punit |>.elim

/-- If `p : 𝓞 K` is a prime that divides both `S.a + η * S.b` and `S.a + η ^ 2 * S.b`, then `p`
is associated with `λ`. -/
lemma associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b {p : 𝓞 K} (hp : Prime p)
    (hpaetab : p ∣ S.a + η * S.b) (hpaetasqb : p ∣ S.a + η ^ 2 * S.b) : Associated p λ := by
  by_cases p_lam : (p ∣ λ)
  · exact hp.associated_of_dvd hζ.zeta_sub_one_prime' p_lam
  have pdivb : p ∣ S.b := by
    have fgh : p ∣ η * (λ * S.b) := by
      rw [show η * (λ * S.b) = (S.a + η ^ 2 * S.b) - (S.a + η * S.b) by rw [coe_eta]; ring]
      exact hpaetasqb.sub hpaetab
    rw [(Units.isUnit η).dvd_mul_left] at fgh
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have pdiva : p ∣ S.a := by
    have fgh : p ∣ λ * S.a := by
      rw [show λ * S.a = η * (S.a + η * S.b) - (S.a + η ^ 2 * S.b) by rw [coe_eta]; ring]
      exact dvd_mul_of_dvd_right hpaetab _ |>.sub hpaetasqb
    exact hp.dvd_or_dvd fgh |>.resolve_left p_lam
  have punit := S.coprime.isUnit_of_dvd' pdiva pdivb
  exact hp.not_unit punit |>.elim

/-- Given `S : Solution`, we let `S.y` be the element such that
`S.a + η * S.b = λ * S.y` -/
noncomputable
def y := (lambda_dvd_a_add_eta_mul_b S).choose

lemma y_spec : S.a + η * S.b = λ * S.y :=
  (lambda_dvd_a_add_eta_mul_b S).choose_spec

/-- Given `S : Solution`, we let `S.z` be the element such that
`S.a + η ^ 2 * S.b = λ * S.z` -/
noncomputable
def z := (lambda_dvd_a_add_eta_sq_mul_b S).choose

lemma z_spec : S.a + η ^ 2 * S.b = λ * S.z :=
  (lambda_dvd_a_add_eta_sq_mul_b S).choose_spec

lemma lambda_not_dvd_y : ¬ λ ∣ S.y := by
  intro h
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← y_spec] at h
  rw [← pow_two] at h
  exact lambda_sq_not_a_add_eta_mul_b _ h

lemma lambda_not_dvd_z : ¬ λ ∣ S.z := by
  intro h
  replace h := mul_dvd_mul_left ((η : 𝓞 K) - 1) h
  rw [coe_eta, ← z_spec] at h
  rw [← pow_two] at h
  exact lambda_sq_not_dvd_a_add_eta_sq_mul_b _ h

variable [DecidableRel fun (a b : 𝓞 K) ↦ a ∣ b]

/-- We have that `λ ^ (3*S.multiplicity-2)` divides `S.a + S.b`. -/
lemma lambda_pow_dvd_a_add_b : λ ^ (3 * S.multiplicity - 2) ∣ S.a + S.b := by
  have h : λ ^ S.multiplicity ∣ S.c  := multiplicity.pow_multiplicity_dvd _
  replace h := pow_dvd_pow_of_dvd h 3
  replace h : (λ ^ multiplicity S) ^ 3 ∣ S.u * S.c ^ 3 := by simp [h]
  rw [← S.H, cube_add_cube_eq_mul, ← pow_mul, mul_comm] at h
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_z
  apply hζ.zeta_sub_one_prime'.pow_dvd_of_dvd_mul_left _ S.lambda_not_dvd_y
  rw [y_spec, z_spec] at h
  have := S.two_le_multiplicity
  have hh : 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S := by
    omega
  rw [← hh, pow_succ, pow_succ] at h
  rw [show (S.a + S.b) * (λ * y S) * (λ * z S) = (S.a + S.b) * y S * z S * λ * λ by ring] at h
  simp only [mul_dvd_mul_iff_right hζ.zeta_sub_one_prime'.ne_zero] at h
  rwa [show (S.a + S.b) * y S * z S = y S * (z S * (S.a + S.b)) by ring] at h

/-- Given `S : Solution`, we let `S.x` be the element such that
`S.a + S.b = λ ^ (3*S.multiplicity-2) * S.x` -/
noncomputable
def x := (lambda_pow_dvd_a_add_b S).choose

lemma x_spec : S.a + S.b = λ ^ (3*S.multiplicity-2) * S.x :=
  (lambda_pow_dvd_a_add_b S).choose_spec


/-- Given `S : Solution`, we let `S.w` be the element such that
`S.c = λ ^ S.multiplicity * S.w` -/
noncomputable
def w :=
  (multiplicity.pow_multiplicity_dvd S.toSolution'.multiplicity_lambda_c_finite).choose

lemma w_spec : S.c = λ ^ S.multiplicity * S.w :=
(multiplicity.pow_multiplicity_dvd S.toSolution'.multiplicity_lambda_c_finite).choose_spec

lemma lambda_not_dvd_w : ¬ λ ∣ S.w := by
  intro h
  replace h := mul_dvd_mul_left (λ ^ S.multiplicity) h
  rw [← w_spec] at h
  have hh : _ := multiplicity.is_greatest' S.toSolution'.multiplicity_lambda_c_finite
    (lt_add_one S.multiplicity)
  rw [pow_succ', mul_comm] at hh
  exact hh h

lemma lambda_not_dvd_x : ¬ λ ∣ S.x := by
  intro h
  replace h := mul_dvd_mul_left (λ ^ (3 * S.multiplicity - 2)) h
  rw [mul_comm, ← x_spec] at h
  replace h := mul_dvd_mul (mul_dvd_mul h S.lambda_dvd_a_add_eta_mul_b) S.lambda_dvd_a_add_eta_sq_mul_b
  rw [← cube_add_cube_eq_mul, S.H, w_spec] at h
  simp only [Units.isUnit, IsUnit.dvd_mul_left] at h
  rw [← pow_succ', mul_comm, ← mul_assoc, ← pow_succ'] at h
  have := S.two_le_multiplicity
  have hh : 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S := by
    omega
  rw [hh, mul_pow, ← pow_mul, mul_comm _ 3, mul_dvd_mul_iff_left _] at h
  replace h := Prime.dvd_of_dvd_pow hζ.zeta_sub_one_prime' h
  exact lambda_not_dvd_w _ h
  simp [hζ.zeta_sub_one_prime'.ne_zero]

lemma coprime_x_y : IsCoprime S.x S.y := by
  apply isCoprime_of_prime_dvd
  · simp only [not_and]
    intro _  hy
    apply lambda_not_dvd_y S
    simp [hy]
  · intro p hp p_dvd_x p_dvd_y
    have aux1 := dvd_mul_of_dvd_right p_dvd_x (λ ^ (3 * S.multiplicity - 2))
    rw [← x_spec] at aux1
    have aux2 := dvd_mul_of_dvd_right p_dvd_y (η -1)
    rw [coe_eta, ← y_spec] at aux2
    have aux3 : Associated p (hζ.toInteger - 1) := by
      apply associated_of_dvd_a_add_b_of_dvd_a_add_eta_mul_b
      exact hp
      exact aux1
      exact aux2
    have aux4 : λ ∣ S.x := by
      rw [← Associated.dvd_iff_dvd_left aux3]
      exact p_dvd_x
    exact lambda_not_dvd_x S aux4

lemma coprime_x_z : IsCoprime S.x S.z := by
  apply isCoprime_of_prime_dvd
  . simp only [not_and]
    intro _ hz
    apply lambda_not_dvd_z S
    simp [hz]
  . intro p hp p_dvd_x p_dvd_z
    have aux1 := dvd_mul_of_dvd_right p_dvd_x (λ ^ (3 * S.multiplicity - 2))
    rw [← x_spec] at aux1
    have aux2 := dvd_mul_of_dvd_right p_dvd_z (η - 1)
    rw [coe_eta, ← z_spec] at aux2
    have aux3 : Associated p (hζ.toInteger - 1) := by
      apply associated_of_dvd_a_add_b_of_dvd_a_add_eta_sq_mul_b
      exact hp
      exact aux1
      exact aux2
    have aux4 : λ ∣ S.x := by
      rw [← Associated.dvd_iff_dvd_left aux3]
      exact p_dvd_x
    exact lambda_not_dvd_x S aux4

lemma coprime_y_z : IsCoprime S.y S.z := by
  apply isCoprime_of_prime_dvd
  . simp only [not_and]
    intro _ hz
    apply lambda_not_dvd_z S
    simp [hz]
  . intro p hp p_dvd_y p_dvd_z
    have aux1 := dvd_mul_of_dvd_right p_dvd_y (η - 1)
    rw [coe_eta, ← y_spec] at aux1
    have aux2 := dvd_mul_of_dvd_right p_dvd_z (η - 1)
    rw [coe_eta, ← z_spec] at aux2
    have aux3 : Associated p (hζ.toInteger - 1) := by
      apply associated_of_dvd_a_add_eta_mul_b_of_dvd_a_add_eta_sq_mul_b
      exact hp
      exact aux1
      exact aux2
    have aux4 : λ ∣ S.y := by
      rw [← Associated.dvd_iff_dvd_left aux3]
      exact p_dvd_y
    exact lambda_not_dvd_y S aux4

lemma mult_minus_two_plus_one_plus_one : 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S := by
  have this : 2 ≤ 3 * multiplicity S := by
    have := two_le_multiplicity S
    omega
  zify [this]
  ring

lemma x_mul_y_mul_z_eq_u_w_pow_three : S.x * S.y * S.z = S.u * S.w ^ 3 := by
  suffices hh : λ ^ (3 * S.multiplicity - 2) * S.x * λ * S.y * λ * S.z =
      S.u * λ ^ (3 * S.multiplicity) * S.w ^ 3 by
    rw [show λ ^ (3 * multiplicity S - 2) * x S * λ * y S * λ * z S =
      λ ^ (3 * multiplicity S - 2) * λ * λ * x S * y S * z S by ring] at hh
    rw [mul_comm _ (λ ^ (3 * multiplicity S))] at hh
    simp only [← pow_succ] at hh
    have := S.two_le_multiplicity
    have hhh : 3 * multiplicity S - 2 + 1 + 1 = 3 * multiplicity S := by
      omega
    rw [hhh] at hh
    rw [mul_assoc, mul_assoc, mul_assoc] at hh
    simp [hζ.zeta_sub_one_prime'.ne_zero] at hh
    convert hh using 1
    ring
  simp only [← x_spec, mul_assoc, ← y_spec, ← z_spec]
  simp only [mul_comm 3, pow_mul, ← mul_pow, ← w_spec]
  rw [← S.H, cube_add_cube_eq_mul]
  ring

lemma x_eq_unit_mul_cube : ∃ (u₁ : (𝓞 K)ˣ) (X : 𝓞 K), S.x = u₁ * X ^ 3 := by
  have h1 : S.x * (S.y * S.z * S.u⁻¹) = S.w ^ 3 := by
    --simp only [x_mul_y_mul_z_eq_u_w_pow_three, ← mul_assoc] --this produces a timeout error
    simp only [← mul_assoc, x_mul_y_mul_z_eq_u_w_pow_three]
    simp only [mul_comm _ (S.w ^ 3), mul_assoc,mul_right_inv, Units.mul_inv, mul_one]
  have h2 : IsCoprime S.x (S.y * S.z * S.u⁻¹) := by
    apply (isCoprime_mul_unit_right_right _ S.x _).mpr
    apply IsCoprime.mul_right S.coprime_x_y S.coprime_x_z
    simp only [Units.isUnit]
  have h3 : _ := exists_associated_pow_of_mul_eq_pow' h2 h1
  rcases h3 with ⟨X, ⟨u₁, hX⟩⟩
  use u₁; use X
  simp [← hX, mul_comm]

lemma y_eq_unit_mul_cube : ∃ (u₂ : (𝓞 K)ˣ) (Y : 𝓞 K), S.y = u₂ * Y ^ 3 := by
  have h1 : S.y * (S.x * S.z * S.u⁻¹) = S.w ^ 3 := by
    rw [← mul_assoc, ← mul_assoc S.y, mul_comm S.y, x_mul_y_mul_z_eq_u_w_pow_three]
    simp only [mul_comm _ (S.w ^ 3), mul_assoc, mul_right_inv, Units.mul_inv, mul_one]
  have h2 : IsCoprime S.y (S.x * S.z * S.u⁻¹) := by
    apply (isCoprime_mul_unit_right_right _ S.y _).mpr
    apply IsCoprime.mul_right S.coprime_x_y.symm S.coprime_y_z
    simp only [Units.isUnit]
  have h3 : _ := exists_associated_pow_of_mul_eq_pow' h2 h1
  rcases h3 with ⟨Y, ⟨u₂, hY⟩⟩
  use u₂; use Y
  simp [← hY, mul_comm]

lemma z_eq_unit_mul_cube : ∃ (u₃ : (𝓞 K)ˣ) (Z : 𝓞 K), S.z = u₃ * Z ^ 3 := by
  have h1 : S.z * (S.x * S.y * S.u⁻¹) = S.w ^ 3 := by
    rw [← mul_assoc, ← mul_assoc S.z, mul_comm S.z, mul_assoc S.x, mul_comm S.z, ← mul_assoc, x_mul_y_mul_z_eq_u_w_pow_three]
    simp only [mul_comm _ (S.w ^ 3), mul_assoc, mul_right_inv, Units.mul_inv, mul_one]
  have h2 : IsCoprime S.z (S.x * S.y * S.u⁻¹) := by
    apply (isCoprime_mul_unit_right_right _ S.z _).mpr
    apply IsCoprime.mul_right S.coprime_x_z.symm S.coprime_y_z.symm
    simp only [Units.isUnit]
  have h3 : _ := exists_associated_pow_of_mul_eq_pow' h2 h1
  rcases h3 with ⟨Z, ⟨u₃, hZ⟩⟩
  use u₃; use Z
  simp [← hZ, mul_comm]

/-- Given `S : Solution`, we let `S.u₁` and `S.X` be the elements such that
`S.x = S.u₁ * S.X ^ 3` -/
noncomputable
def u₁ := (x_eq_unit_mul_cube S).choose

/-- Given `S : Solution`, we let `S.u₁` and `S.X` be the elements such that
`S.x = S.u₁ * S.X ^ 3` -/
noncomputable
def X := (x_eq_unit_mul_cube S).choose_spec.choose

lemma u₁_X_spec : S.x = S.u₁ * S.X ^ 3 := by
  exact (x_eq_unit_mul_cube S).choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₂` and `S.Y` be the elements such that
`S.y = S.u₂ * S.Y ^ 3` -/
noncomputable
def u₂ := (y_eq_unit_mul_cube S).choose

/-- Given `S : Solution`, we let `S.u₂` and `S.Y` be the elements such that
`S.y = S.u₂ * S.Y ^ 3` -/
noncomputable
def Y := (y_eq_unit_mul_cube S).choose_spec.choose

lemma u₂_Y_spec : S.y = S.u₂ * S.Y ^ 3 := by
  exact (y_eq_unit_mul_cube S).choose_spec.choose_spec

/-- Given `S : Solution`, we let `S.u₃` and `S.Z` be the elements such that
`S.z = S.u₃ * S.Z ^ 3` -/
noncomputable
def u₃ := (z_eq_unit_mul_cube S).choose

/-- Given `S : Solution`, we let `S.u₃` and `S.Z` be the elements such that
`S.z = S.u₃ * S.Z ^ 3` -/
noncomputable
def Z := (z_eq_unit_mul_cube S).choose_spec.choose

lemma u₃_Z_spec : S.z = S.u₃ * S.Z ^ 3 := by
  exact (z_eq_unit_mul_cube S).choose_spec.choose_spec

lemma X_ne_zero : S.X ≠ 0 := by
  intro h
  have aux1 : S.x = 0 := by
    rw [u₁_X_spec, h]
    ring
  have aux2 : λ ∣ S.x := by simp [aux1]
  apply lambda_not_dvd_x S
  exact aux2

lemma lambda_not_dvd_X : ¬ λ ∣ S.X := by
  intro h
  have hyp := dvd_mul_of_dvd_right h (S.u₁ * S.X ^ 2)
  rw [show ↑(u₁ S) * X S ^ 2 * X S = ↑S.u₁ * S.X^3 by ring] at hyp
  rw [← u₁_X_spec] at hyp
  apply lambda_not_dvd_x S
  simp [hyp]

lemma lambda_not_dvd_Y : ¬ λ ∣ S.Y := by
  intro h
  have hyp := dvd_mul_of_dvd_right h (S.u₂ * S.Y^2)
  rw [show ↑(u₂ S) * Y S ^ 2 * Y S = ↑S.u₂ * S.Y^3 by ring] at hyp
  rw [← u₂_Y_spec] at hyp
  apply lambda_not_dvd_y S
  simp [hyp]

lemma lambda_not_dvd_Z : ¬ λ ∣ S.Z := by
  intro h
  have hyp := dvd_mul_of_dvd_right h (S.u₃ * S.Z^2)
  rw [show ↑(u₃ S) * Z S ^ 2 * Z S = ↑S.u₃ * S.Z^3 by ring] at hyp
  rw [← u₃_Z_spec] at hyp
  apply lambda_not_dvd_z S
  simp [hyp]

lemma coprime_Y_Z : IsCoprime S.Y S.Z := by
  apply isCoprime_of_prime_dvd
  · simp only [not_and]
    intro _ hy_Z_zero
    apply lambda_not_dvd_Z S
    simp only [hy_Z_zero, dvd_zero]
  · intro p hp p_dvd_Y p_dvd_Z
    have auxY := dvd_mul_of_dvd_right p_dvd_Y (S.u₂ * S.Y^2)
    rw [show S.u₂ * S.Y^2 * S.Y = S.u₂ * S.Y^3 by ring] at auxY
    rw [← u₂_Y_spec] at auxY
    have auxZ := dvd_mul_of_dvd_right p_dvd_Z (S.u₃ * S.Z^2)
    rw [show S.u₃ * S.Z^2 * S.Z = S.u₃ * S.Z^3 by ring] at auxZ
    rw [← u₃_Z_spec] at auxZ
    have gcd_isUnit : IsUnit (gcd S.y S.z) := by
      rw [gcd_isUnit_iff S.y S.z]
      simp only [coprime_y_z]
    apply hp.not_unit
    refine isUnit_of_dvd_unit ?_ gcd_isUnit
    rw [dvd_gcd_iff]
    simp [auxY, auxZ]

lemma formula1 : S.u₁*S.X^3*λ^(3*S.multiplicity-2)+S.u₂*η*S.Y^3*λ+S.u₃*η^2*S.Z^3*λ = 0 := by
  rw [← u₁_X_spec, ← mul_comm (η : 𝓞 K) _, mul_assoc (η : 𝓞 K) _ _, ← u₂_Y_spec,
    ← mul_comm ((η : 𝓞 K) ^ 2) _, mul_assoc ((η : 𝓞 K) ^ 2) _ _, ← u₃_Z_spec]
  rw [mul_comm, mul_assoc, ← x_spec]
  rw [mul_comm, mul_comm _ λ, ← y_spec, mul_comm _ (η : 𝓞 K)]
  rw [mul_assoc, mul_comm _ λ, ← z_spec]
  rw [show S.a + S.b + η * (S.a + η * S.b) + η ^ 2 * (S.a + η ^ 2 * S.b) =
    S.a * (1 + η + η ^ 2) + S.b * (1 + (η ^ 3) * η + η ^ 2) by ring]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζ.toInteger_cube_eq_one,
    Units.val_one, one_mul, ← add_mul, Units.val_pow_eq_pow_val]
  convert mul_zero _
  convert hζ.toInteger_eval_cyclo using 1
  ring

noncomputable
def u₄ := η * S.u₃ * S.u₂⁻¹

noncomputable
def u₅ := -η ^ 2 * S.u₁ * S.u₂⁻¹

lemma formula2 : S.Y ^ 3 + S.u₄ * S.Z ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  unfold u₄
  unfold u₅
  apply mul_left_cancel₀ S.u₂.isUnit.ne_zero
  apply mul_left_cancel₀ (Units.isUnit η).ne_zero
  apply mul_left_cancel₀ hζ.zeta_sub_one_prime'.ne_zero
  push_cast
  rw [show λ * (η * (↑(u₂ S) * (Y S ^ 3 + η * ↑(u₃ S) * ↑(u₂ S)⁻¹ * Z S ^ 3)))
    = λ * η * ↑(u₂ S) * Y S ^ 3 + λ * η^2 * ↑(u₂ S) * ↑(u₂ S)⁻¹ * ↑(u₃ S) * Z S ^ 3 by ring]
  rw [show λ * (η * (↑(u₂ S) * (-η ^ 2 * ↑(u₁ S) * ↑(u₂ S)⁻¹
    * (λ ^ (S.multiplicity - 1) * X S) ^ 3)))
    = λ * (↑(u₂ S) * ↑(u₂ S)⁻¹ * (-η ^ 3 * ↑(u₁ S) * (λ ^ (S.multiplicity - 1) * X S) ^ 3)) by ring]
  rw [← sub_eq_zero]
  simp only [Units.mul_inv_cancel_right, Units.mul_inv, neg_mul, mul_neg, one_mul, sub_neg_eq_add]
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hζ.toInteger_cube_eq_one,
    Units.val_one, one_mul, Units.val_pow_eq_pow_val]
  have tmp : λ * (↑(u₁ S) * (λ ^ (S.multiplicity - 1) * X S) ^ 3)
      = ↑(u₁ S) * X S ^ 3 * λ ^ (3 * S.multiplicity - 2) := by
    rw [mul_comm, mul_assoc, mul_assoc]
    congr 1
    rw [mul_pow, mul_comm, ← mul_assoc, mul_comm _ (S.X ^ _)]
    congr 1
    rw [← pow_mul', ← pow_succ']
    congr 1
    have := two_le_multiplicity S
    omega
  rw [tmp]
  convert formula1 S using 1
  ring

variable (hζ) in
lemma lambda_sq_div_lambda_fourth : λ^2 ∣ λ^4 := by
  use λ^2
  ring

lemma lambda_sq_div_new_X_cubed : λ^2 ∣ ↑(u₅ S) * (λ ^ (multiplicity S - 1) * X S) ^ 3 := by
    have := two_le_multiplicity S
    have tmp : ↑(u₅ S) * λ ^ (3 * S.multiplicity - 5) * λ^2 * S.X^3
              =
              ↑(u₅ S) * (λ ^ (multiplicity S - 1) * X S) ^ 3 := by
      rw [mul_comm, mul_assoc, mul_pow, ← mul_assoc _ _ (S.X ^ 3), mul_comm _ (S.X ^ 3)]
      congr 2
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    rw [← tmp]
    use S.u₅ * (λ ^ (3* S.multiplicity - 5) * X S^ 3)
    ring

variable [DecidableEq (𝓞 K)]

lemma by_kummer : ↑S.u₄ ∈ ({1, -1} : Finset (𝓞 K)) := by
  have h0 := lambda_sq_div_lambda_fourth hζ
  have hX := lambda_sq_div_new_X_cubed S
  suffices hh : S.u₄ = 1 ∨ S.u₄ = -1 by
    rcases hh with (h | h) <;> simp [h]
  apply IsCyclotomicExtension.Rat.Three.eq_one_or_neg_one_of_unit_of_congruent hζ
  rcases hX with ⟨kX, hkX⟩
  rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd hζ S.lambda_not_dvd_Y with
    (HY | HY) <;> rcases lambda_pow_four_dvd_cube_sub_one_or_add_one_of_lambda_not_dvd
      hζ S.lambda_not_dvd_Z with (HZ | HZ) <;> replace HY := h0.trans HY <;> replace HZ :=
      h0.trans HZ <;> rcases HY with ⟨kY, hkY⟩ <;> rcases HZ with ⟨kZ, hkZ⟩
  · use -1
    use kX - kY - S.u₄ * kZ
    rw [show λ ^ 2 * (kX - kY - ↑(u₄ S) * kZ) =
      λ ^ 2 * kX - λ ^ 2 * kY - ↑(u₄ S) * (λ ^ 2 * kZ) by ring]
    rw [← hkX, ← hkY, ← hkZ]
    rw [← S.formula2]
    ring
  · use 1
    use - kX + kY + S.u₄ * kZ
    rw [show λ ^ 2 * (-kX + kY + ↑(u₄ S) * kZ) =
      - (λ ^ 2 * kX - λ ^ 2 * kY - ↑(u₄ S) * (λ ^ 2 * kZ)) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring
  · use 1
    use kX - kY - S.u₄ * kZ
    rw [show λ ^ 2 * (kX - kY - ↑(u₄ S) * kZ) =
      λ ^ 2 * kX - λ ^ 2 * kY - ↑(u₄ S) * (λ ^ 2 * kZ) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring
  · use -1
    use - kX + kY + S.u₄ * kZ
    rw [show λ ^ 2 * (-kX + kY + ↑(u₄ S) * kZ) =
      - (λ ^ 2 * kX - λ ^ 2 * kY - ↑(u₄ S) * (λ ^ 2 * kZ)) by ring]
    rw [← hkX, ← hkY, ← hkZ, ← S.formula2]
    ring

/-- Given `S : Solution`, we have that
`S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3`. -/
lemma final : S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.u₅ * (λ ^ (S.multiplicity - 1) * S.X) ^ 3 := by
  rw [show S.Y ^ 3 + (S.u₄ * S.Z) ^ 3 = S.Y ^ 3 + S.u₄^2 * S.u₄ * S.Z ^ 3 by ring]
  have f2 := formula2 S
  rw [show Y S ^ 3 + ↑(u₄ S) * Z S ^ 3 = Y S ^ 3 + 1 * ↑(u₄ S) * Z S ^ 3 by ring] at f2
  have simple_kummer := by_kummer S
  simp only [Finset.mem_insert, Finset.mem_singleton] at simple_kummer
  have hh : S.u₄ ^ 2 = (1 : 𝓞 K) := by
    rcases simple_kummer with (h | h) <;> simp only [h, one_pow, even_two, Even.neg_pow, one_pow]
  nth_rewrite 1 [← hh] at f2
  exact f2

noncomputable
def _root_.Solution'_final : Solution' hζ where
  a := S.Y
  b := S.u₄ * S.Z
  c := λ ^ (S.multiplicity - 1) * S.X
  u := S.u₅
  ha := S.lambda_not_dvd_Y
  hb := fun h ↦ S.lambda_not_dvd_Z <| Units.dvd_mul_left.1 h
  hc := fun h ↦ S.X_ne_zero <| by simpa [hζ.zeta_sub_one_prime'.ne_zero] using h
  coprime := (isCoprime_mul_unit_left_right S.u₄.isUnit _ _).2 S.coprime_Y_Z
  hcdvd := by
    refine dvd_mul_of_dvd_left (dvd_pow_self _ (fun h ↦ ?_)) _
    rw [Nat.sub_eq_iff_eq_add (le_trans (by norm_num) S.two_le_multiplicity), zero_add] at h
    simpa [h] using S.two_le_multiplicity
  H := final S

lemma _root_.Solution'_final_multiplicity :
    (Solution'_final S).multiplicity = S.multiplicity - 1 := by
  refine (multiplicity.unique' (by simp [Solution'_final]) (fun h ↦ S.lambda_not_dvd_X ?_)).symm
  obtain ⟨k, hk : λ ^ (S.multiplicity - 1) * S.X = λ ^ (S.multiplicity - 1 + 1) * k⟩ := h
  rw [pow_succ, mul_assoc] at hk
  simp only [mul_eq_mul_left_iff, pow_eq_zero_iff', hζ.zeta_sub_one_prime'.ne_zero, ne_eq,
    false_and, or_false] at hk
  simp [hk]

lemma _root_.Solution'_final_multiplicity_lt :
    (Solution'_final S).multiplicity < S.multiplicity := by
  rw [Solution'_final_multiplicity S, Nat.sub_one]
  exact Nat.pred_lt <| by have := S.two_le_multiplicity; omega

theorem exists_Solution_multiplicity_lt :
    ∃ (S' : Solution hζ), S'.multiplicity < S.multiplicity := by
  obtain ⟨S', hS'⟩ := exists_Solution_of_Solution' (Solution'_final S)
  exact ⟨S', hS' ▸ Solution'_final_multiplicity_lt S⟩

end Solution

end FermatLastTheoremForThreeGen

end eisenstein

end case2

theorem fermatLastTheoremThree : FermatLastTheoremFor 3 := by
  classical
  let K := CyclotomicField 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K := IsCyclotomicExtension.numberField {3} ℚ _
  apply FermatLastTheoremForThree_of_FermatLastTheoremThreeGen hζ
  intro a b c u hc ha hb hcdvd coprime H
  let S' : FermatLastTheoremForThreeGen.Solution' hζ :=
  { a := a
    b := b
    c := c
    u := u
    ha := ha
    hb := hb
    hc := hc
    coprime := coprime
    hcdvd := hcdvd
    H := H }
  obtain ⟨S, -⟩ := FermatLastTheoremForThreeGen.exists_Solution_of_Solution' S'
  obtain ⟨Smin, hSmin⟩ := S.exists_minimal
  obtain ⟨Sfin, hSfin⟩ := Smin.exists_Solution_multiplicity_lt
  linarith [hSmin Sfin]
