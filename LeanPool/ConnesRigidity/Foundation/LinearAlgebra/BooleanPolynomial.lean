/-
Copyright (c) 2026 Utensil Song, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Utensil Song, OpenAI
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF

/-!
Derived in part from Apache-2.0 `openai/ten-proofs`, `ConnesRigidity.lean` at
94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6, lines 18-23.
Modifications: renamed the elementary `ZMod 2` helper and placed it in the
local Boolean-polynomial namespace. The remaining finite-coordinate support
and weight development is local. See the upstream PORT_MAP.md.
-/

namespace Connes
namespace BooleanPolynomial

/-- Characteristic-two scalar field. Paper: §4. -/
abbrev F := ZMod 2

/-- Nonzero characteristic-two scalars are one. Paper: §2; see the pinned
upstream provenance manifest. -/
theorem eq_one_of_ne_zero (a : F) (ha : a ≠ 0) : a = 1 := by
  fin_cases a
  · exact (ha rfl).elim
  · rfl

/-- Boolean functions on an arbitrary finite coordinate type. Paper: §4. -/
abbrev PolynomialOn (ι : Type*) := (ι → F) → F

/-- Support of a Boolean function on arbitrary finite coordinates. Paper: §4. -/
noncomputable def supportOn {ι : Type*} [Fintype ι] (P : PolynomialOn ι) :
    Finset (ι → F) := by
  classical
  exact Finset.univ.filter (fun x => P x ≠ 0)

/-- Support weight on arbitrary finite coordinates. Paper: §4. -/
noncomputable def weightOn {ι : Type*} [Fintype ι] (P : PolynomialOn ι) : ℕ :=
  (supportOn P).card

/-- Degree-two coefficient data on arbitrary finite Boolean coordinates. Paper: §4. -/
structure QuadraticData (ι : Type*) [Fintype ι] where
  /--
  The `constantTerm` component of `QuadraticData`.
  -/
  constantTerm : F
  /--
  The `linear` component of `QuadraticData`.
  -/
  linear : ι → F
  /--
  The `quadratic` component of `QuadraticData`.
  -/
  quadratic : ι → ι → F

/-- Evaluation of degree-two coefficient data. Paper: §4. -/
def QuadraticData.eval {ι : Type*} [Fintype ι]
    (q : QuadraticData ι) (x : ι → F) : F :=
  q.constantTerm +
    ∑ i, q.linear i * x i +
      ∑ i, ∑ j, q.quadratic i j * x i * x j

/-- Degree restriction on arbitrary finite Boolean coordinates. Paper: §4. -/
def IsQuadratic {ι : Type*} [Fintype ι] (P : PolynomialOn ι) : Prop :=
  ∃ q : QuadraticData ι, ∀ x, q.eval x = P x

/-- Four-point support cover for quadratic functions. Paper: §4. -/
theorem quadratic_support_quarter
    {W : Type*} [AddCommGroup W] [Module F W] [Fintype W]
    (f : W → F) (b : W → W → F)
    (hadd : ∀ x y, f (x + y) = f x + f y + f 0 + b x y)
    (hbadd : ∀ x y z, b (x + y) z = b x z + b y z)
    (hf : ∃ x, f x ≠ 0) :
    Fintype.card W ≤
      4 * ((Finset.univ : Finset W).filter (fun x => f x ≠ 0)).card := by
  classical
  have hchar2 (x : W) : x + x = 0 := by
    rw [← two_smul F x]
    have htwo : (2 : F) = 0 := CharTwo.two_eq_zero
    rw [htwo, zero_smul]
  have hchar2F (a : F) : a + a = 0 := by
    exact CharTwo.add_self_eq_zero a
  let support : Finset W := Finset.univ.filter (fun x => f x ≠ 0)
  let offset (u v : W) (c : Fin 2 × Fin 2) : W :=
    (if c.1 = 0 then 0 else u) + (if c.2 = 0 then 0 else v)
  let cover (u v : W) : (support × (Fin 2 × Fin 2)) → W :=
    fun p => p.1.1 + offset u v p.2
  have hcover_card (u v : W)
      (hsurj : Function.Surjective (cover u v)) :
      Fintype.card W ≤ 4 * support.card := by
    have hcard := Fintype.card_le_of_surjective (cover u v) hsurj
    simpa only [ge_iff_le, Fintype.card_prod, Fintype.card_coe,
      Fintype.card_fin, Nat.reduceMul, Nat.mul_comm] using hcard
  change Fintype.card W ≤ 4 * support.card
  by_cases hb : ∃ u v : W, b u v ≠ 0
  · obtain ⟨u, v, huv⟩ := hb
    have hone : b u v = 1 := eq_one_of_ne_zero _ huv
    have hsquare (x : W) :
        f x + f (x + u) + f (x + v) + f ((x + u) + v) = b u v := by
      simp only [hadd x u, hadd x v, hadd (x + u) v, hbadd x u v]
      have hx : f x + f x = 0 := hchar2F (f x)
      have hu : f u + f u = 0 := hchar2F (f u)
      have hv : f v + f v = 0 := hchar2F (f v)
      have hzero : f 0 + f 0 = 0 := hchar2F (f 0)
      have hxu : b x u + b x u = 0 := hchar2F (b x u)
      have hxv : b x v + b x v = 0 := hchar2F (b x v)
      linear_combination 2 * hx + hu + hv + 2 * hzero + hxu + hxv
    apply hcover_card u v
    intro x
    by_cases hx : f x ≠ 0
    · exact ⟨(⟨x, by simpa only [support, Finset.mem_filter, Finset.mem_univ,
        true_and] using hx⟩, (0, 0)), by simp only [Fin.isValue, ↓reduceIte,
        add_zero, cover, offset]⟩
    by_cases hxu : f (x + u) ≠ 0
    · refine ⟨(⟨x + u, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxu⟩, (1, 0)), ?_⟩
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc,
        cover, offset]
      rw [hchar2]
      simp only [add_zero]
    by_cases hxv : f (x + v) ≠ 0
    · refine ⟨(⟨x + v, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxv⟩, (0, 1)), ?_⟩
      simp only [Fin.isValue, ↓reduceIte, one_ne_zero, zero_add, add_assoc,
        cover, offset]
      rw [hchar2]
      simp only [add_zero]
    have hxuv : f ((x + u) + v) ≠ 0 := by
      intro hz
      have hsq := hsquare x
      rw [not_ne_iff.mp hx, not_ne_iff.mp hxu, not_ne_iff.mp hxv, hz] at hsq
      simp only [add_zero, hone, zero_ne_one] at hsq
    refine ⟨(⟨(x + u) + v, by simpa only [support, Finset.mem_filter,
      Finset.mem_univ, true_and] using hxuv⟩, (1, 1)), ?_⟩
    change ((x + u) + v) + (u + v) = x
    calc
      ((x + u) + v) + (u + v) = x + (u + u) + (v + v) := by abel
      _ = x := by rw [hchar2, hchar2]; simp
  · have hbzero : ∀ u v : W, b u v = 0 := by
      intro u v
      by_contra h
      exact hb ⟨u, v, h⟩
    by_cases hnonconst : ∃ u : W, f u + f 0 ≠ 0
    · obtain ⟨u, hu⟩ := hnonconst
      apply hcover_card u 0
      intro x
      by_cases hx : f x ≠ 0
      · exact ⟨(⟨x, by simpa only [support, Finset.mem_filter,
          Finset.mem_univ, true_and] using hx⟩, (0, 0)), by
          simp only [Fin.isValue, ↓reduceIte, add_zero, cover, offset]⟩
      have hxu : f (x + u) ≠ 0 := by
        rw [hadd x u, not_ne_iff.mp hx, hbzero]
        simpa only [zero_add, add_zero] using hu
      refine ⟨(⟨x + u, by simpa only [support, Finset.mem_filter,
        Finset.mem_univ, true_and] using hxu⟩, (1, 0)), ?_⟩
      simp only [Fin.isValue, one_ne_zero, ↓reduceIte, add_zero, add_assoc,
        cover, offset]
      rw [hchar2]
      simp only [add_zero]
    · have hconst : ∀ x : W, f x = f 0 := by
        intro x
        by_contra h
        apply hnonconst
        refine ⟨x, ?_⟩
        intro hzero
        apply h
        calc
          f x = f x + 0 := by simp
          _ = f x + (f 0 + f 0) := by rw [hchar2F, add_zero]
          _ = (f x + f 0) + f 0 := by abel
          _ = f 0 := by rw [hzero]; simp
      obtain ⟨u, hu⟩ := hf
      have hzero : f 0 ≠ 0 := by simpa [hconst u] using hu
      have hsupport : support = Finset.univ := by
        ext x
        simp only [support, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [hconst x] using hzero
      rw [hsupport, Finset.card_univ]
      omega

/-- Low-degree support estimate on arbitrary finite Boolean coordinates. Paper: §4. -/
theorem quadratic_weight_lower_bound
    {ι : Type*} [Fintype ι] (P : PolynomialOn ι)
    (hdeg : IsQuadratic P) (hP : P ≠ 0) :
    weightOn P ≥ 2 ^ (Fintype.card ι - 2) := by
  classical
  obtain ⟨q, hq⟩ := hdeg
  let b : (ι → F) → (ι → F) → F := fun x y =>
    ∑ i, ∑ j, q.quadratic i j * (x i * y j + y i * x j)
  have hq0 : q.eval 0 = q.constantTerm := by
    simp [QuadraticData.eval]
  have hadd (x y : ι → F) :
      q.eval (x + y) = q.eval x + q.eval y + q.eval 0 + b x y := by
    rw [hq0]
    simp only [QuadraticData.eval, b, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    have hthree : (3 : F) = 1 := by decide
    have hc3 : q.constantTerm * 3 = q.constantTerm := by rw [hthree, mul_one]
    ring_nf
    try rw [hc3]
  have hbadd (x y z : ι → F) : b (x + y) z = b x z + b y z := by
    dsimp [b]
    simp only [add_mul, mul_add]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hf : ∃ x : ι → F, q.eval x ≠ 0 := by
    by_contra h
    apply hP
    funext x
    rw [← hq x]
    exact not_ne_iff.mp (not_exists.mp h x)
  have hcard := quadratic_support_quarter q.eval b hadd hbadd hf
  have hweight :
      ((Finset.univ : Finset (ι → F)).filter (fun x => q.eval x ≠ 0)).card =
        weightOn P := by
    unfold weightOn supportOn
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hq x]
  rw [Fintype.card_fun, ZMod.card] at hcard
  rw [hweight] at hcard
  by_cases hn : 2 ≤ Fintype.card ι
  · have hexp : (Fintype.card ι - 2) + 2 = Fintype.card ι := by omega
    have hpow : 2 ^ Fintype.card ι = 4 * 2 ^ (Fintype.card ι - 2) := by
      rw [← hexp, pow_add]
      norm_num [Nat.mul_comm]
    rw [hpow] at hcard
    exact Nat.le_of_mul_le_mul_left hcard (by norm_num)
  · have hn' : Fintype.card ι = 0 ∨ Fintype.card ι = 1 := by omega
    rcases hn' with hzero | hone
    · have hsupport : 0 < weightOn P := by
        obtain ⟨x, hx⟩ := hf
        have hPx : P x ≠ 0 := by simpa only [← hq x] using hx
        exact Finset.card_pos.mpr ⟨x, by
          simpa [supportOn] using hPx⟩
      have hle : 1 ≤ weightOn P := by omega
      simpa [hzero] using hle
    · have hsupport : 0 < weightOn P := by
        obtain ⟨x, hx⟩ := hf
        have hPx : P x ≠ 0 := by simpa only [← hq x] using hx
        exact Finset.card_pos.mpr ⟨x, by
          simpa [supportOn] using hPx⟩
      have hle : 1 ≤ weightOn P := by omega
      simpa [hone] using hle

end BooleanPolynomial
end Connes
