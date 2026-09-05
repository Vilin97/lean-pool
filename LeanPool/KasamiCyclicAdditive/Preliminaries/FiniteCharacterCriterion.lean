/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/

import LeanPool.KasamiCyclicAdditive.Prelude
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import LeanPool.KasamiCyclicAdditive.Preliminaries.FiniteFieldSums

/-!
# Finite character-sum criteria for bijectivity

Complex-valued characters form a basis of the function space on a finite
abelian group. Consequently, if a self-map preserves the sum of every
character, then it preserves the sum of every complex-valued function. Point
indicators then force surjectivity, hence bijectivity.

For finite fields we also record the multiplicative analogue needed by the
MCM-permutation argument. If a map has zero as its unique zero and preserves
every multiplicative-character sum, restrict it to the unit group and apply the
additive criterion to `Additive Kˣ`.
-/

open Finset
open scoped BigOperators

namespace KasamiCyclicAdditive

noncomputable section

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The difference between a character sum pulled back along `f` and the
plain character sum. -/
private def sumPullbackDiff (f : G → G) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun h := (∑ x : G, h (f x)) - ∑ x : G, h x
  map_add' h g := by
    simp only [Pi.add_apply, Finset.sum_add_distrib]
    ring
  map_smul' c h := by
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [RingHom.id_apply, mul_sub]
    rw [← Finset.mul_sum, ← Finset.mul_sum]

omit [DecidableEq G] in
/-- A self-map of a finite abelian group is bijective if it preserves the sum
of every complex-valued additive character. -/
theorem bijective_of_addChar_sum_eq (f : G → G)
    (hchar : ∀ ψ : AddChar G ℂ, (∑ x : G, ψ (f x)) = ∑ x : G, ψ x) :
    Function.Bijective f := by
  classical
  let L : (G → ℂ) →ₗ[ℂ] ℂ := sumPullbackDiff f
  have hL : L = 0 := by
    apply (AddChar.complexBasis G).ext
    intro ψ
    dsimp [L, sumPullbackDiff]
    rw [AddChar.complexBasis_apply, hchar ψ, sub_self]
  have hall : ∀ h : G → ℂ, (∑ x : G, h (f x)) = ∑ x : G, h x := by
    intro h
    have hz := LinearMap.congr_fun hL h
    change (∑ x : G, h (f x)) - ∑ x : G, h x = 0 at hz
    exact sub_eq_zero.mp hz
  have hsurj : Function.Surjective f := by
    intro y
    by_contra hy
    have hy' : ∀ x : G, f x ≠ y := by
      intro x hx
      exact hy ⟨x, hx⟩
    have h := hall (fun z : G => if z = y then (1 : ℂ) else 0)
    have hleft : (∑ x : G, if f x = y then (1 : ℂ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      simp [hy' x]
    have hright : (∑ x : G, if x = y then (1 : ℂ) else 0) = 1 := by
      simp
    rw [hleft, hright] at h
    exact zero_ne_one h
  exact ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- Every additive character of `Additive Kˣ` is induced by a multiplicative
character of `K`. -/
private lemma exists_mulChar_of_addChar (ψ : AddChar (Additive Kˣ) ℂ) :
    ∃ χ : MulChar K ℂ, ∀ u : Kˣ, χ (u : K) = ψ (Additive.ofMul u) := by
  let h : Kˣ →* ℂ :=
    { toFun := fun u => ψ (Additive.ofMul u)
      map_one' := by
        change ψ (Additive.ofMul (1 : Kˣ)) = 1
        exact ψ.map_zero_eq_one
      map_mul' := by
        intro a b
        change ψ (Additive.ofMul (a * b)) =
          ψ (Additive.ofMul a) * ψ (Additive.ofMul b)
        simpa using AddChar.map_add_eq_mul ψ (Additive.ofMul a) (Additive.ofMul b) }
  exact ⟨MulChar.ofUnitHom h.toHomUnits, fun u => by simp [h]⟩

omit [Fintype K] [DecidableEq K] in
/-- A self-map of `K` whose only zero is `0` is bijective as soon as its
restriction to the units is. -/
private lemma bijective_of_bijective_units {f : K → K} {g : Kˣ → Kˣ}
    (hzero : ∀ x : K, f x = 0 ↔ x = 0)
    (hg : ∀ u : Kˣ, (g u : K) = f (u : K))
    (hgb : Function.Bijective g) :
    Function.Bijective f := by
  have hf0 : f 0 = 0 := (hzero 0).mpr rfl
  constructor
  · intro a b hab
    by_cases ha : a = 0
    · subst ha
      exact ((hzero b).mp (by rw [← hab, hf0])).symm
    · have hb : b ≠ 0 := by
        intro hb0
        subst hb0
        exact ha ((hzero a).mp (by simpa [hf0] using hab))
      have hu : g (Units.mk0 a ha) = g (Units.mk0 b hb) := by
        apply Units.ext
        rw [hg, hg]
        simpa using hab
      simpa using congrArg Units.val (hgb.1 hu)
  · intro y
    by_cases hy : y = 0
    · exact ⟨0, by simpa [hy] using hf0⟩
    · obtain ⟨ux, hux⟩ := hgb.2 (Units.mk0 y hy)
      refine ⟨(ux : K), ?_⟩
      rw [← hg]
      simpa using congrArg Units.val hux

omit [DecidableEq K] in
/-- A finite-field self-map is bijective if zero is its unique zero and it
preserves the sum of every complex-valued multiplicative character. -/
theorem bijective_of_mulChar_sum_eq (f : K → K)
    (hzero : ∀ x : K, f x = 0 ↔ x = 0)
    (hchar : ∀ χ : MulChar K ℂ, (∑ x : K, χ (f x)) = ∑ x : K, χ x) :
    Function.Bijective f := by
  classical
  let fu : Kˣ → Kˣ := fun u =>
    Units.mk0 (f (u : K)) (by
      intro hf
      exact Units.ne_zero u ((hzero (u : K)).mp hf))
  let ga : Additive Kˣ → Additive Kˣ := fun u =>
    Additive.ofMul (fu (Additive.toMul u))
  have hga : Function.Bijective ga := by
    apply bijective_of_addChar_sum_eq ga
    intro ψ
    obtain ⟨χ, hχ⟩ := exists_mulChar_of_addChar (K := K) ψ
    have hf0 : f 0 = 0 := (hzero 0).mpr rfl
    have hunit :
        (∑ u : Kˣ, χ (f (u : K))) = ∑ u : Kˣ, χ (u : K) := by
      calc
        (∑ u : Kˣ, χ (f (u : K))) = ∑ x : K, χ (f x) :=
          KasamiCyclicAdditive.sum_units_eq_sum (fun x : K => χ (f x))
            (by change χ (f 0) = 0; rw [hf0]; exact χ.map_zero)
        _ = ∑ x : K, χ x := hchar χ
        _ = ∑ u : Kˣ, χ (u : K) :=
          (KasamiCyclicAdditive.sum_units_eq_sum (fun x : K => χ x) χ.map_zero).symm
    calc
      (∑ u : Additive Kˣ, ψ (ga u)) =
          ∑ u : Kˣ, ψ (ga (Additive.ofMul u)) := by
        symm
        exact (Additive.ofMul : Kˣ ≃ Additive Kˣ).sum_comp
          (fun u : Additive Kˣ => ψ (ga u))
      _ = ∑ u : Kˣ, χ (f (u : K)) := by
        apply Finset.sum_congr rfl
        intro u hu
        change ψ (Additive.ofMul (fu u)) = χ (f (u : K))
        simpa [fu] using (hχ (fu u)).symm
      _ = ∑ u : Kˣ, χ (u : K) := hunit
      _ = ∑ u : Kˣ, ψ (Additive.ofMul u) := by
        apply Finset.sum_congr rfl
        intro u hu
        exact hχ u
      _ = ∑ u : Additive Kˣ, ψ u :=
        (Additive.ofMul : Kˣ ≃ Additive Kˣ).sum_comp ψ
  have hfu : Function.Bijective fu := by
    constructor
    · intro a b hab
      have hab' : ga (Additive.ofMul a) = ga (Additive.ofMul b) := by
        change Additive.ofMul (fu a) = Additive.ofMul (fu b)
        exact congrArg Additive.ofMul hab
      have h := hga.1 hab'
      exact (Additive.ofMul : Kˣ ≃ Additive Kˣ).injective h
    · intro y
      obtain ⟨x, hx⟩ := hga.2 (Additive.ofMul y)
      refine ⟨Additive.toMul x, ?_⟩
      have hx' : Additive.ofMul (fu (Additive.toMul x)) = Additive.ofMul y := by
        simpa [ga] using hx
      exact (Additive.ofMul : Kˣ ≃ Additive Kˣ).injective hx'
  exact bijective_of_bijective_units hzero (fun _ => rfl) hfu

end

end KasamiCyclicAdditive
