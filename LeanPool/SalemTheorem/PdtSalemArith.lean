/-
Copyright (c) 2026 Stephanie Alexander. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stephanie Alexander
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Tactic
public import LeanPool.SalemTheorem.PdtSalemCircle

/-!
# PdtSalemArith — the arithmetic Salem-ness certificate

The arithmetic certificate for Salem's construction: a real root
`tau > 1` of the integer family, excluded from the two integer
degeneracies, is a Salem number; the exclusions are discharged for the
ladder sequence in the assembly (`PdtSalemEndgame`); Kronecker's theorem
is not needed (the Gauss step covers all degenerate cases).

Setting: `Pz : Polynomial ℤ` monic whose complex image is the `PdtSalemCircle`
product `P alpha inside` (one root `alpha > 1`, the rest strictly inside
the unit circle, conjugation-closed), `Qz : Polynomial ℤ` whose complex
image is the mirrored product `Q alpha inside`, and the family
`Rz = X^m·Pz + Qz`.  If `tau > 1` is a real root of `Rz` with
`tau ∉ ℤ` and `tau + 1/tau ∉ ℤ` (the two degeneracies), then
(`salem_certificate`):

* `tau` is an algebraic integer (`Rz` is monic and kills it);
* every complex root of `minpoly ℚ tau` other than `tau` lies in the
  CLOSED unit disk (the trichotomy of `PdtSalemCircle` through the divisibility
  `minpoly ∣ Rz` over `ℚ`);
* some root lies ON the unit circle — otherwise the minimal polynomial
  has degree ≤ 2 and the Gauss step (`minpoly ℚ = minpoly ℤ` mapped, ℤ
  integrally closed) forces `tau ∈ ℤ` (degree 1) or
  `tau + 1/tau ∈ ℤ` (degree 2, Vieta on the `X`-coefficient);
* `1/tau` is a root of `minpoly ℚ tau` — otherwise all conjugates
  except `tau` are unimodular and the constant term has absolute value
  `tau ∉ ℤ` (Vieta on the constant term, plus the Gauss step again).

Together: `tau` is a Salem number.  `Qz` is data with only its complex
image constrained, so the reverse-polynomial identification is decoupled
(`reverse_bridge` below discharges it for the actual companion
`Qz = Pz.reverse`).
-/

@[expose] public section

namespace PDT
namespace SalemArith

noncomputable section
open Polynomial Complex

/-! ### Small helpers -/

/-- A multiset of unimodular numbers has unimodular product. -/
lemma norm_multiset_prod_eq_one (s : Multiset ℂ) :
    (∀ w ∈ s, ‖w‖ = 1) → ‖s.prod‖ = 1 := by
  induction s using Multiset.induction_on with
  | empty => intro _; simp
  | cons a t ih =>
    intro h
    rw [Multiset.prod_cons, norm_mul, h a (Multiset.mem_cons_self a t), one_mul]
    exact ih fun w hw => h w (Multiset.mem_cons_of_mem hw)

/-- The ℤ-cast triangle through ℚ: ring homs out of ℤ are unique. -/
lemma castQC_triangle :
    (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
  RingHom.ext_int _ _

/-- `aeval` as evaluation of the mapped polynomial. -/
lemma aeval_eq_eval_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] (p : Polynomial R) (x : S) :
    Polynomial.aeval x p = (p.map (algebraMap R S)).eval x := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]

/-- Transport of scalar `aeval` along `ℝ → ℂ`. -/
lemma aeval_ofReal {R : Type*} [CommRing R] [Algebra R ℝ] [Algebra R ℂ]
    [IsScalarTower R ℝ ℂ] (p : Polynomial R) (x : ℝ) :
    Polynomial.aeval ((x : ℂ)) p = ((Polynomial.aeval x p : ℝ) : ℂ) :=
  Polynomial.aeval_algebraMap_apply ℂ x p

/-! ### The family is monic over ℤ, and its complex image is `R` -/

/-- Degree transfer from the complex factorization: `Pz` has degree
`inside.card + 1`. -/
lemma Pz_natDegree (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside) :
    Pz.natDegree = inside.card + 1 := by
  have h1 := hmonic.natDegree_map (Int.castRingHom ℂ)
  rw [hfacC, SalemCircle.P_natDegree] at h1
  exact h1.symm

/-- Degree transfer for the companion: `Qz` has degree at most
`inside.card + 1`. -/
lemma Qz_natDegree_le (alpha : ℝ) (inside : Multiset ℂ) (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside) :
    Qz.natDegree ≤ inside.card + 1 := by
  have hinj : Function.Injective (Int.castRingHom ℂ) := Int.cast_injective
  have h1 := natDegree_map_eq_of_injective hinj Qz
  rw [hQmap] at h1
  rw [← h1]
  exact SalemCircle.Q_natDegree_le alpha inside

/-- The integer family `X^m·Pz + Qz` is monic (for `m ≥ 1`). -/
lemma family_monic (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) (hm : 1 ≤ m) : (X ^ m * Pz + Qz).Monic := by
  have hPdeg := Pz_natDegree Pz hmonic alpha inside hfacC
  have hQdeg := Qz_natDegree_le alpha inside Qz hQmap
  have hXm : (X ^ m * Pz).Monic := (monic_X_pow m).mul hmonic
  refine hXm.add_of_left ?_
  apply degree_lt_degree
  rw [(monic_X_pow m).natDegree_mul hmonic, natDegree_X_pow, hPdeg]
  omega

/-- The complex image of the integer family is the family `R` of `PdtSalemCircle`. -/
lemma family_map_C (Pz : Polynomial ℤ) (alpha : ℝ) (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) :
    (X ^ m * Pz + Qz).map (Int.castRingHom ℂ) = SalemCircle.R alpha inside m := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, hfacC, hQmap]
  rfl

/-! ### The main theorem: the arithmetic Salem-ness certificate -/

/-- **The arithmetic Salem-ness certificate.**  A real root `tau > 1`
of the integer family `X^m·Pz + Qz` — whose complex image is the `PdtSalemCircle`
family — is a Salem number, provided `tau` avoids the two integer
degeneracies `tau ∈ ℤ` and `tau + 1/tau ∈ ℤ`: it is an algebraic
integer, its conjugates lie in the closed unit disk, at least one lies
ON the circle, and `1/tau` is among them.  All degenerate exclusions run
through the Gauss step (`minpoly ℚ tau` is the mapped `minpoly ℤ tau`,
since ℤ is integrally closed). -/
theorem salem_certificate
    (Pz : Polynomial ℤ) (hmonic : Pz.Monic)
    (alpha : ℝ) (halpha : 1 < alpha)
    (inside : Multiset ℂ) (hin : ∀ r ∈ inside, ‖r‖ < 1)
    (hconj : inside.map (starRingEnd ℂ) = inside)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside)
    (Qz : Polynomial ℤ)
    (hQmap : Qz.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside)
    (m : ℕ) (hm : 1 ≤ m) (hmp : 3 ≤ m + (inside.card + 1))
    (tau : ℝ) (htau : 1 < tau)
    (hroot : ((X ^ m * Pz + Qz).map (Int.castRingHom ℝ)).eval tau = 0)
    (hτZ : ∀ n : ℤ, tau ≠ (n : ℝ))
    (hτtr : ∀ n : ℤ, tau + tau⁻¹ ≠ (n : ℝ)) :
    IsIntegral ℤ tau ∧
    (∀ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 → z ≠ (tau : ℂ) → ‖z‖ ≤ 1) ∧
    (∃ z : ℂ, (Polynomial.aeval z) (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1) ∧
    (Polynomial.aeval ((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
  classical
  set Rz : Polynomial ℤ := X ^ m * Pz + Qz with hRzdef
  -- bridge plumbing
  have hRzMonic : Rz.Monic :=
    family_monic Pz hmonic alpha inside hfacC Qz hQmap m hm
  have hRmap : Rz.map (Int.castRingHom ℂ) = SalemCircle.R alpha inside m :=
    family_map_C Pz alpha inside hfacC Qz hQmap m
  have haevalR : Polynomial.aeval tau Rz = 0 := by
    rw [aeval_eq_eval_map, algebraMap_int_eq]
    exact hroot
  -- integrality
  have hint : IsIntegral ℤ tau := by
    refine ⟨Rz, hRzMonic, ?_⟩
    rw [← Polynomial.aeval_def]
    exact haevalR
  have hQint : IsIntegral ℚ tau := hint.tower_top
  -- the family root over ℂ, and the trichotomy
  have hRC : (SalemCircle.R alpha inside m).eval ((tau : ℂ)) = 0 := by
    have h1 : Polynomial.aeval ((tau : ℂ)) Rz = 0 := by
      rw [aeval_ofReal, haevalR, Complex.ofReal_zero]
    rwa [aeval_eq_eval_map, algebraMap_int_eq, hRmap] at h1
  have htri : ∀ z : ℂ, (SalemCircle.R alpha inside m).eval z = 0 →
      ‖z‖ = 1 ∨ z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ :=
    SalemCircle.salem_root_trichotomy alpha inside halpha hin hconj m hm hmp
      tau htau hRC
  -- the minimal polynomial divides, so conjugates are roots of `R`
  have hmpdvd : minpoly ℚ tau ∣ Rz.map (Int.castRingHom ℚ) := by
    apply minpoly.dvd ℚ tau
    rw [← algebraMap_int_eq, Polynomial.aeval_map_algebraMap]
    exact haevalR
  have hdvdC : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ∣ SalemCircle.R alpha inside m := by
    have h1 : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ∣
        (Rz.map (Int.castRingHom ℚ)).map (algebraMap ℚ ℂ) :=
      Polynomial.map_dvd _ hmpdvd
    rwa [Polynomial.map_map, castQC_triangle, hRmap] at h1
  have hcontain : ∀ z : ℂ, ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 →
      (SalemCircle.R alpha inside m).eval z = 0 := by
    intro z hz
    obtain ⟨c, hc⟩ := hdvdC
    rw [hc, Polynomial.eval_mul, hz, zero_mul]
  have haevalC : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau)
      = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z := fun z =>
    aeval_eq_eval_map _ z
  have htauCroot : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval ((tau : ℂ)) = 0 := by
    rw [← haevalC, aeval_ofReal, minpoly.aeval, Complex.ofReal_zero]
  -- scalar facts about `tau`
  have htaupos : (0 : ℝ) < tau := by linarith
  have htau_norm : ‖((tau : ℂ))‖ = tau := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htaupos]
  have htauinv_norm : ‖((tau : ℂ))⁻¹‖ = tau⁻¹ := by rw [norm_inv, htau_norm]
  have htinv1 : tau⁻¹ < 1 := inv_lt_one_of_one_lt₀ htau
  -- the closed disk
  have hdisk : ∀ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 →
      z ≠ ((tau : ℂ)) → ‖z‖ ≤ 1 := by
    intro z hz hzne
    have hz0 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
      rw [← haevalC]; exact hz
    rcases htri z (hcontain z hz0) with h | h | h
    · exact le_of_eq h
    · exact absurd h hzne
    · rw [h, htauinv_norm]; linarith
  -- the Gauss step — every coefficient of the minimal polynomial
  -- over ℚ is the cast of an integer
  have hmz : minpoly ℚ tau = (minpoly ℤ tau).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hint
  have hcoeff : ∀ i : ℕ,
      (minpoly ℚ tau).coeff i = (((minpoly ℤ tau).coeff i : ℤ) : ℚ) := by
    intro i
    rw [hmz, Polynomial.coeff_map, eq_intCast]
  -- splitting data for the complex minimal polynomial
  have hmpmonic : (minpoly ℚ tau).Monic := minpoly.monic hQint
  have hmpirr : Irreducible (minpoly ℚ tau) := minpoly.irreducible hQint
  have hmpsep : (minpoly ℚ tau).Separable := hmpirr.separable
  have hsepC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Separable := hmpsep.map
  have hnodup : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.Nodup :=
    Polynomial.nodup_roots hsepC
  have hmonicC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Monic := hmpmonic.map _
  have hCne : (minpoly ℚ tau).map (algebraMap ℚ ℂ) ≠ 0 := hmonicC.ne_zero
  have hsplits : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).Splits :=
    IsAlgClosed.splits _
  have hdegC : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).natDegree
      = (minpoly ℚ tau).natDegree := hmpmonic.natDegree_map _
  have hcard : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card
      = (minpoly ℚ tau).natDegree := by
    rw [← hdegC]
    exact hsplits.natDegree_eq_card_roots.symm
  have hdegpos : 0 < (minpoly ℚ tau).natDegree := minpoly.natDegree_pos hQint
  have hmem : ∀ z : ℂ, z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots ↔
      ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).eval z = 0 := by
    intro z
    rw [Polynomial.mem_roots']
    exact ⟨fun h => h.2, fun h => ⟨hCne, h⟩⟩
  have htauC_mem : ((tau : ℂ)) ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots :=
    (hmem _).mpr htauCroot
  -- a conjugate ON the circle
  have hcircle : ∃ z : ℂ, Polynomial.aeval z (minpoly ℚ tau) = 0 ∧ ‖z‖ = 1 := by
    by_contra hno
    simp only [not_exists, not_and] at hno
    -- containment of all roots in the pair {tau, 1/tau}
    have hpair : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z = ((tau : ℂ)) ∨ z = ((tau : ℂ))⁻¹ := by
      intro z hz
      have hz0 := (hmem z).mp hz
      have hz1 : Polynomial.aeval z (minpoly ℚ tau) = 0 := by
        rw [haevalC]; exact hz0
      rcases htri z (hcontain z hz0) with h | h | h
      · exact absurd h (hno z hz1)
      · exact Or.inl h
      · exact Or.inr h
    -- hence the degree is at most 2
    have hsub : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset ⊆
        ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ) := by
      intro z hz
      rcases hpair z (Multiset.mem_toFinset.mp hz) with h | h
      · exact Finset.mem_insert.mpr (Or.inl h)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h))
    have hdeg2 : (minpoly ℚ tau).natDegree ≤ 2 := by
      have h1 := Finset.card_le_card hsub
      have h2 : ({((tau : ℂ)), ((tau : ℂ))⁻¹} : Finset ℂ).card ≤ 2 := by
        apply le_trans (Finset.card_insert_le _ _)
        simp
      have h3 : ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.toFinset.card
          = ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots.card :=
        Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
      omega
    rcases (by omega :
        (minpoly ℚ tau).natDegree = 1 ∨ (minpoly ℚ tau).natDegree = 2) with h1 | h2
    · -- degree 1: `tau` would be a rational integer
      have heq : minpoly ℚ tau = X + Polynomial.C ((minpoly ℚ tau).coeff 0) :=
        hmpmonic.eq_X_add_C h1
      have haev := minpoly.aeval ℚ tau
      rw [heq, map_add, Polynomial.aeval_X, Polynomial.aeval_C, hcoeff 0,
        map_intCast] at haev
      exact hτZ (-(minpoly ℤ tau).coeff 0) (by push_cast; linarith)
    · -- degree 2: the root multiset is exactly {tau, 1/tau}, and Vieta on
      -- the X-coefficient makes `tau + 1/tau` a rational integer
      obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
      have hcards := hcard
      rw [hrest, Multiset.card_cons] at hcards
      have hcard_rest : rest.card = 1 := by omega
      obtain ⟨b, hb⟩ := Multiset.card_eq_one.mp hcard_rest
      have hnodup' := hnodup
      rw [hrest, Multiset.nodup_cons] at hnodup'
      have hbmem : b ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots := by
        rw [hrest, hb]
        exact Multiset.mem_cons_of_mem (Multiset.mem_singleton_self b)
      have hbval : b = ((tau : ℂ))⁻¹ := by
        rcases hpair b hbmem with h | h
        · exfalso
          apply hnodup'.1
          rw [hb, h]
          exact Multiset.mem_singleton_self _
        · exact h
      have hnext := hsplits.nextCoeff_eq_neg_sum_roots_of_monic hmonicC
      rw [Polynomial.nextCoeff_of_natDegree_pos (by rw [hdegC]; omega),
        hdegC, h2, hrest, hb, hbval, Multiset.sum_cons,
        Multiset.sum_singleton] at hnext
      rw [show (2 : ℕ) - 1 = 1 by norm_num] at hnext
      rw [Polynomial.coeff_map, hcoeff 1, map_intCast] at hnext
      have hreal : (((minpoly ℤ tau).coeff 1 : ℤ) : ℝ) = -(tau + tau⁻¹) := by
        exact_mod_cast hnext
      exact hτtr (-(minpoly ℤ tau).coeff 1) (by push_cast; linarith)
  -- `1/tau` is a conjugate
  have hinvroot : Polynomial.aeval (((tau : ℂ))⁻¹) (minpoly ℚ tau) = 0 := by
    by_contra hne
    -- every root other than `tau` is unimodular
    have hroots1 : ∀ z ∈ ((minpoly ℚ tau).map (algebraMap ℚ ℂ)).roots,
        z ≠ ((tau : ℂ)) → ‖z‖ = 1 := by
      intro z hz hzne
      have hz0 := (hmem z).mp hz
      rcases htri z (hcontain z hz0) with h | h | h
      · exact h
      · exact absurd h hzne
      · exfalso
        apply hne
        rw [← h, haevalC z]
        exact hz0
    obtain ⟨rest, hrest⟩ := Multiset.exists_cons_of_mem htauC_mem
    have hnodup' := hnodup
    rw [hrest, Multiset.nodup_cons] at hnodup'
    have hrest1 : ∀ w ∈ rest, ‖w‖ = 1 := by
      intro w hw
      apply hroots1 w (by rw [hrest]; exact Multiset.mem_cons_of_mem hw)
      intro hwz
      exact hnodup'.1 (hwz ▸ hw)
    -- Vieta on the constant term, in absolute value
    have hc0 := hsplits.coeff_zero_eq_prod_roots_of_monic hmonicC
    rw [hrest, Multiset.prod_cons] at hc0
    have hnorm : ‖((minpoly ℚ tau).map (algebraMap ℚ ℂ)).coeff 0‖ = tau := by
      rw [hc0, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
        one_mul, htau_norm, norm_multiset_prod_eq_one rest hrest1, mul_one]
    rw [Polynomial.coeff_map, hcoeff 0, map_intCast,
      show ((((minpoly ℤ tau).coeff 0 : ℤ)) : ℂ)
        = (((((minpoly ℤ tau).coeff 0 : ℤ) : ℝ)) : ℂ) by norm_cast,
      Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs] at hnorm
    exact hτZ |(minpoly ℤ tau).coeff 0| hnorm.symm
  exact ⟨hint, hdisk, hcircle, hinvroot⟩

/-! ### The reverse bridge — the companion IS the reverse -/

/-- The reflect of the product `P` at its degree is the mirrored
product `Q`: they agree at every `z ≠ 0` (`mirror_P`), and a cofinite
agreement set forces polynomial equality. -/
lemma reflect_P_eq_Q (alpha : ℝ) (inside : Multiset ℂ) :
    (SalemCircle.P alpha inside).reflect (inside.card + 1)
      = SalemCircle.Q alpha inside := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : ({(0 : ℂ)}ᶜ : Set ℂ) ⊆
      {x : ℂ |
        Polynomial.eval x ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          = Polynomial.eval x (SalemCircle.Q alpha inside)} := by
    intro z hz
    have hz0 : z ≠ 0 := by simpa using hz
    let : Invertible z⁻¹ := invertibleOfNonzero (inv_ne_zero hz0)
    have key := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℂ) z⁻¹
      (inside.card + 1) (SalemCircle.P alpha inside)
      (le_of_eq (SalemCircle.P_natDegree alpha inside))
    rw [Polynomial.eval₂_id, Polynomial.eval₂_id, invOf_eq_inv, inv_inv] at key
    have hzp : (z⁻¹) ^ (inside.card + 1) * z ^ (inside.card + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hz0, one_pow]
    change Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
        = Polynomial.eval z (SalemCircle.Q alpha inside)
    calc Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
        = Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          * ((z⁻¹) ^ (inside.card + 1) * z ^ (inside.card + 1)) := by
          rw [hzp, mul_one]
      _ = (Polynomial.eval z ((SalemCircle.P alpha inside).reflect (inside.card + 1))
          * (z⁻¹) ^ (inside.card + 1)) * z ^ (inside.card + 1) := by ring
      _ = Polynomial.eval z⁻¹ (SalemCircle.P alpha inside)
          * z ^ (inside.card + 1) := by rw [key]
      _ = z ^ (inside.card + 1) * (SalemCircle.P alpha inside).eval z⁻¹ := by ring
      _ = (SalemCircle.Q alpha inside).eval z := SalemCircle.mirror_P alpha inside hz0
  exact Set.Infinite.mono hsub ((Set.finite_singleton 0).infinite_compl)

/-- **The reverse bridge**: the actual Salem companion — the
reverse polynomial of `Pz` — has complex image the mirrored product `Q`,
discharging the hypothesis `hQmap` of `salem_certificate` for
`Qz = Pz.reverse`. -/
theorem reverse_bridge (Pz : Polynomial ℤ) (hmonic : Pz.Monic) (alpha : ℝ)
    (inside : Multiset ℂ)
    (hfacC : Pz.map (Int.castRingHom ℂ) = SalemCircle.P alpha inside) :
    Pz.reverse.map (Int.castRingHom ℂ) = SalemCircle.Q alpha inside := by
  have h1 : Pz.reverse.map (Int.castRingHom ℂ)
      = (Pz.map (Int.castRingHom ℂ)).reflect Pz.natDegree :=
    (Polynomial.reflect_map (Int.castRingHom ℂ) Pz Pz.natDegree).symm
  rw [h1, hfacC, Pz_natDegree Pz hmonic alpha inside hfacC]
  exact reflect_P_eq_Q alpha inside

end
end SalemArith
end PDT

/-
Upstream license notice:
MIT License

Copyright (c) 2026 Stephanie Alexander

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
