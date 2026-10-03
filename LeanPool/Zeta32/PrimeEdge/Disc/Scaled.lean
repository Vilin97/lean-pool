/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.PrimeEdge.Disc.LocValue

/-! "Scaled" polynomials and power series (the coefficient of `u^e` has
valuation `≥ e`, i.e. `G(p u)` with `G` integral) and the disc factorization predicate `Good`:
`F(p u - d) = p^E u^E R(u)` with `R` scaled and `R(0)` a `p`-adic unit. -/

public section

open Polynomial
open scoped BigOperators
namespace Zeta32.PrimeEdge

open Zeta32.Arith.Local

variable {p : ℕ}

/-- The coefficient of `u^e` has valuation `≥ e`. -/
def Scaled (p : ℕ) (f : ℚ[X]) : Prop := ∀ e, VG p (f.coeff e) e

/-- Coefficientwise valuation lower bound for a power series scaled by its degree. -/
def ScaledPS (p : ℕ) (f : PowerSeries ℚ) : Prop := ∀ e, VG p (PowerSeries.coeff e f) e

/-- A nonzero rational of valuation `0`. -/
def IsUnitV (p : ℕ) (q : ℚ) : Prop := q ≠ 0 ∧ padicValRat p q = 0

lemma IsUnitV.mul [Fact p.Prime] {q q' : ℚ} (h : IsUnitV p q) (h' : IsUnitV p q') :
    IsUnitV p (q * q') :=
  ⟨mul_ne_zero h.1 h'.1, by rw [padicValRat.mul h.1 h'.1, h.2, h'.2]; rfl⟩

lemma IsUnitV.inv [Fact p.Prime] {q : ℚ} (h : IsUnitV p q) : IsUnitV p q⁻¹ :=
  ⟨inv_ne_zero h.1, by rw [padicValRat.inv, h.2]; rfl⟩

lemma IsUnitV.one : IsUnitV p 1 := ⟨one_ne_zero, by simp⟩

lemma IsUnitV.VG {q : ℚ} (h : IsUnitV p q) : VG p q 0 := Or.inr (by rw [h.2]; rfl)

lemma IsUnitV.pow [Fact p.Prime] {q : ℚ} (h : IsUnitV p q) (n : ℕ) : IsUnitV p (q ^ n) := by
  induction n with
  | zero => simpa using IsUnitV.one
  | succ n ih => rw [pow_succ]; exact ih.mul h

lemma IsUnitV.prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ}
    (h : ∀ i ∈ s, IsUnitV p (f i)) : IsUnitV p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsUnitV.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `j - d` is a unit when `j ≢ d (mod p)`. -/
lemma isUnitV_sub [Fact p.Prime] {j d : ℕ} (h : j % p ≠ d % p) : IsUnitV p ((j : ℚ) - d) := by
  have hcast : ((j : ℚ) - d) = (((j : ℤ) - d : ℤ) : ℚ) := by push_cast; ring
  have hnd : ¬ (p : ℤ) ∣ (j : ℤ) - d := fun hd => h ((Nat.modEq_iff_dvd.mpr hd).symm)
  refine ⟨?_, ?_⟩
  · rw [hcast]
    intro h0
    apply hnd
    have : (j : ℤ) - d = 0 := by exact_mod_cast h0
    rw [this]; exact dvd_zero _
  · rw [hcast]; exact padicValRat_int_eq_zero hnd

/-! ### Scaled polynomials -/

namespace Scaled

lemma mul [Fact p.Prime] {f g : ℚ[X]} (hf : Scaled p f) (hg : Scaled p g) : Scaled p (f * g) :=
  fun e => by
    rw [coeff_mul]
    refine VG.sum _ fun x hx => ?_
    have h := (hf x.1).mul (hg x.2)
    rw [Finset.mem_antidiagonal] at hx
    rw [← hx]; push_cast; exact h

lemma one : Scaled p 1 := fun e => by
  rw [coeff_one]; split_ifs with h
  · subst h; exact VG.one
  · exact VG.zero _

lemma pow [Fact p.Prime] {f : ℚ[X]} (hf : Scaled p f) (n : ℕ) : Scaled p (f ^ n) := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ]; exact ih.mul hf

lemma prod [Fact p.Prime] {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]}
    (h : ∀ i ∈ s, Scaled p (f i)) : Scaled p (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- `α + p u` with `α` integral. -/
lemma lin [hp : Fact p.Prime] {α : ℚ} (hα : VG p α 0) : Scaled p (C α + C (p : ℚ) * X) :=
  fun e => by
    rw [coeff_add, coeff_C, coeff_C_mul, coeff_X]
    rcases e with _ | _ | e
    · simpa using hα
    · have := VG.primePow (p := p) 1
      simpa using this
    · simpa using VG.zero (p := p) _

end Scaled

/-! ### Scaled power series -/

namespace ScaledPS

lemma coe {f : ℚ[X]} (hf : Scaled p f) : ScaledPS p (f : PowerSeries ℚ) := fun e => by
  rw [Polynomial.coeff_coe]; exact hf e

lemma mul [Fact p.Prime] {f g : PowerSeries ℚ} (hf : ScaledPS p f) (hg : ScaledPS p g) :
    ScaledPS p (f * g) := fun e => by
  rw [PowerSeries.coeff_mul]
  refine VG.sum _ fun x hx => ?_
  have h := (hf x.1).mul (hg x.2)
  rw [Finset.mem_antidiagonal] at hx
  rw [← hx]; push_cast; exact h

/-- Inverse of a scaled series with unit constant term. -/
lemma inv [Fact p.Prime] {f : PowerSeries ℚ} (hf : ScaledPS p f)
    (hu : IsUnitV p (PowerSeries.constantCoeff f)) : ScaledPS p f⁻¹ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [PowerSeries.coeff_inv]
    split_ifs with hn
    · subst hn; simpa using hu.inv.VG
    · have hs : VG p (∑ x ∈ Finset.antidiagonal n,
          if x.2 < n then PowerSeries.coeff x.1 f * PowerSeries.coeff x.2 f⁻¹ else 0) n := by
        refine VG.sum _ fun x hx => ?_
        rw [Finset.mem_antidiagonal] at hx
        split_ifs with hlt
        · have h := (hf x.1).mul (ih x.2 hlt)
          rw [← hx]; push_cast; exact h
        · exact VG.zero _
      have h := (hu.inv.VG.neg).mul hs
      simpa using h

end ScaledPS

/-! ### The disc factorization predicate -/

/-- `F(p u - d) = p^E u^E R(u)`, `R` scaled with unit constant term. -/
def Good (p d : ℕ) (F : ℚ[X]) (E : ℕ) : Prop :=
  ∃ R : ℚ[X], F.comp (C (p : ℚ) * X - C (d : ℚ)) = C ((p : ℚ) ^ E) * X ^ E * R ∧
    Scaled p R ∧ IsUnitV p (R.coeff 0)

namespace Good

lemma congr {d : ℕ} {F : ℚ[X]} {E E' : ℕ} (h : Good p d F E) (hE : E = E') : Good p d F E' :=
  hE ▸ h

lemma mul [Fact p.Prime] {d : ℕ} {F G : ℚ[X]} {E E' : ℕ} (hF : Good p d F E)
    (hG : Good p d G E') : Good p d (F * G) (E + E') := by
  obtain ⟨R, hR, hRs, hRu⟩ := hF
  obtain ⟨S, hS, hSs, hSu⟩ := hG
  refine ⟨R * S, ?_, hRs.mul hSs, ?_⟩
  · rw [mul_comp, hR, hS, pow_add, pow_add, C_mul]; ring
  · rw [mul_coeff_zero]; exact hRu.mul hSu

lemma one {d : ℕ} : Good p d 1 0 :=
  ⟨1, by simp, Scaled.one, by simpa using IsUnitV.one⟩

lemma pow [Fact p.Prime] {d : ℕ} {F : ℚ[X]} {E : ℕ} (hF : Good p d F E) (n : ℕ) :
    Good p d (F ^ n) (n * E) := by
  induction n with
  | zero => simpa using one
  | succ n ih => rw [pow_succ]; exact (ih.mul hF).congr (by ring)

lemma prod [Fact p.Prime] {d : ℕ} {ι : Type*} (s : Finset ι) {f : ι → ℚ[X]} {E : ι → ℕ}
    (h : ∀ i ∈ s, Good p d (f i) (E i)) : Good p d (∏ i ∈ s, f i) (∑ i ∈ s, E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A linear factor `t + ℓ` with `0 ≤ ℓ, d < p` on the disc `t = p u - d`. -/
lemma lin [Fact p.Prime] {d ℓ : ℕ} (hd : d < p) (hℓ : ℓ < p) :
    Good p d (X + C (ℓ : ℚ)) (if ℓ = d then 1 else 0) := by
  split_ifs with h
  · subst h
    refine ⟨1, ?_, Scaled.one, by simpa using IsUnitV.one⟩
    simp [add_comp]
  · refine ⟨C ((ℓ : ℚ) - d) + C (p : ℚ) * X, ?_, Scaled.lin ?_, ?_⟩
    · simp only [add_comp, X_comp, C_comp, pow_zero, map_one, one_mul, C_sub]; ring
    · have := isUnitV_sub (p := p) (j := ℓ) (d := d)
        (by rw [Nat.mod_eq_of_lt hℓ, Nat.mod_eq_of_lt hd]; exact h)
      exact this.VG
    · rw [coeff_add, coeff_C_zero, coeff_C_mul, coeff_X_zero, mul_zero, add_zero]
      exact isUnitV_sub (by rw [Nat.mod_eq_of_lt hℓ, Nat.mod_eq_of_lt hd]; exact h)

lemma X_self [Fact p.Prime] {d : ℕ} (hd : d < p) : Good p d X (if 0 = d then 1 else 0) := by
  have h := lin (p := p) (ℓ := 0) hd (by omega)
  simpa using h

end Good

end Zeta32.PrimeEdge

end
