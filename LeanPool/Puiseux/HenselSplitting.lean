/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
public import Mathlib.RingTheory.AdicCompletion.Completeness

/-!

# Hensel splitting for polynomials over power series

In this file we derive from the Weierstrass preparation theorem
(`PowerSeries.exists_isWeierstrassFactorization`) a Hensel-style splitting for a monic
polynomial `p` over `K⟦X⟧`: a root of multiplicity `k` of the reduction of `p` modulo the
maximal ideal of `K⟦X⟧` (that is, of the coefficientwise application of
`PowerSeries.constantCoeff` to `p`) lifts to a monic factor of `p` of degree `k`.

## Main results

- `Polynomial.Monic.exists_factorization_rootMultiplicity_zero`: a monic `p` over `K⟦X⟧` of
  degree `m` whose reduction has `0` as a root of multiplicity `k` with `k ≤ m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and the reduction of `g` is `X ^ k`.

- `Polynomial.Monic.exists_factorization_rootMultiplicity`: a monic `p` over `K⟦X⟧` of degree
  `m` whose reduction has a root `a : K` of multiplicity `k` with `k ≤ m` factors as
  `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`.

-/

/- Ported to Lean Pool and its pinned Mathlib toolchain in September 2026. -/

public section

namespace Polynomial

variable {K : Type*} [Field K]

private theorem order_map_residue_of_rootMultiplicity
    {p : (PowerSeries K)[X]} {k : ℕ} (hp : p.Monic)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k) :
    ((p : PowerSeries (PowerSeries K)).map
      (IsLocalRing.residue (PowerSeries K))).order = (k : ℕ∞) := by
  set A := PowerSeries K
  set e := PowerSeries.residueFieldOfPowerSeries (k := K)
  set φ := (p : PowerSeries A).map (IsLocalRing.residue A) with hφ
  -- The residue field of `A` is `K`, so `φ` corresponds to the reduction of `p`.
  have key : φ.map e.toRingHom
      = ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K) := by
    ext n
    simp [hφ, Polynomial.coeff_coe]
    rfl
  -- The order of the coercion of a nonzero polynomial is its root multiplicity at `0`.
  have hordK : ((p.map (PowerSeries.constantCoeff (R := K)) : K[X]) : PowerSeries K).order
      = (k : ℕ∞) := by
    have hnz : (p.map (PowerSeries.constantCoeff (R := K))) ≠ 0 := (hp.map _).ne_zero
    rw [← hk, Polynomial.rootMultiplicity_eq_natTrailingDegree', PowerSeries.order_eq_nat]
    refine ⟨?_, fun i hi ↦ by simpa using Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hi⟩
    simpa [Polynomial.trailingCoeff] using Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hnz
  have hmap : (φ.map e.toRingHom).order = φ.order := by
    have h : (φ.map e.toRingHom).map e.symm.toRingHom = φ := by ext n; simp
    refine le_antisymm ?_ (PowerSeries.le_order_map _)
    simpa only [h] using PowerSeries.le_order_map (φ := φ.map e.toRingHom) e.symm.toRingHom
  rw [← hmap, key, hordK]

/-- **Hensel splitting at zero**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has `0` as a root of multiplicity `k` with
`k ≤ m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`, and `g`
distinguished: its reduction is `X ^ k`. -/
theorem Monic.exists_factorization_rootMultiplicity_zero {p : (PowerSeries K)[X]} {m k : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k)
    (hkm : k ≤ m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k ∧
      g.map (PowerSeries.constantCoeff (R := K)) = X ^ k := by
  have : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries K)) (PowerSeries K) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  set A := PowerSeries K
  set e := PowerSeries.residueFieldOfPowerSeries (k := K)
  set φ := (p : PowerSeries A).map (IsLocalRing.residue A) with hφ
  have horder : φ.order = (k : ℕ∞) := order_map_residue_of_rootMultiplicity hp hk
  have hφnz : φ ≠ 0 := fun h ↦ by simp [h] at horder
  -- Weierstrass preparation for `A⟦X⟧`.
  obtain ⟨f, u, H⟩ := PowerSeries.exists_isWeierstrassFactorization hφnz
  have hfmonic : f.Monic := H.isDistinguishedAt.monic
  have hfdeg : f.natDegree = k := by
    rw [H.natDegree_eq_toNat_order_map, ← hφ, horder, ENat.toNat_natCast]
  have hordf : ((f : PowerSeries A).map
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))).order = (k : ℕ∞) := by
    rw [← H.isDistinguishedAt.coe_natDegree_eq_order_map (f : PowerSeries A) 1 (by simp)
      (by simp), hfdeg]
  -- Divide `p` by the monic `f` in `A[X]`; uniqueness of Weierstrass division forces `u = p /ₘ f`.
  have hdivmod : p = f * (p /ₘ f) + p %ₘ f :=
    ((add_comm _ _).trans (p.modByMonic_add_div f)).symm
  have hrdeg : (p %ₘ f).degree < (k : ℕ) :=
    hfdeg ▸ Polynomial.degree_eq_natDegree hfmonic.ne_zero ▸ p.degree_modByMonic_lt hfmonic
  have huniq := H.isDistinguishedAt.isWeierstrassDivisorAt'.eq_of_mul_add_eq_mul_add (q := u)
    (q' := ↑(p /ₘ f)) (r := 0) (r' := p %ₘ f) (by simp [hordf]) (by rw [hordf]; simpa using hrdeg)
    (by rw [Polynomial.coe_zero, add_zero, ← H.eq_mul]
        exact_mod_cast hdivmod)
  rw [huniq.2.symm, add_zero] at hdivmod
  refine ⟨f, p /ₘ f, hfmonic, hfmonic.of_mul_monic_left (hdivmod ▸ hp), hdivmod, hfdeg, ?_, ?_⟩
  · have := p.natDegree_divByMonic hfmonic
    omega
  · -- `f` is distinguished of degree `k`, so its reduction is `X ^ k`.
    have h1 := congrArg (Polynomial.map e.toRingHom)
      (show f.map (IsLocalRing.residue A) = X ^ k from hfdeg ▸ H.isDistinguishedAt.map_eq_X_pow)
    rwa [Polynomial.map_map, Polynomial.map_pow, Polynomial.map_X] at h1

/-- **Hensel splitting at a root**: a monic `p` over `K⟦X⟧` of degree `m` whose reduction
(coefficientwise `PowerSeries.constantCoeff`) has a root `a : K` of multiplicity `k` with
`k ≤ m` factors as `p = g * h` with `g`, `h` monic of degrees `k` and `m - k`. -/
theorem Monic.exists_factorization_rootMultiplicity {p : (PowerSeries K)[X]} {m k : ℕ} {a : K}
    (hp : p.Monic) (hm : p.natDegree = m)
    (hk : (p.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity a = k)
    (hkm : k ≤ m) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ h.Monic ∧ p = g * h ∧
      g.natDegree = k ∧ h.natDegree = m - k := by
  set c : PowerSeries K := PowerSeries.C a with hc
  -- Shift the root to `0`.
  have hPmonic : (p.comp (X + C c)).Monic := hp.comp_X_add_C c
  have hPdeg : (p.comp (X + C c)).natDegree = m := by simp [Polynomial.natDegree_comp, hm]
  have hred : (p.comp (X + C c)).map (PowerSeries.constantCoeff (R := K))
      = (p.map (PowerSeries.constantCoeff (R := K))).comp (X + C a) := by
    simp [Polynomial.map_comp, hc]
  have hkP : ((p.comp (X + C c)).map
      (PowerSeries.constantCoeff (R := K))).rootMultiplicity 0 = k := by
    rw [hred, ← Polynomial.rootMultiplicity_eq_rootMultiplicity, hk]
  obtain ⟨g₀, h₀, hg₀, hh₀, hpr, hg₀deg, hh₀deg, -⟩ :=
    hPmonic.exists_factorization_rootMultiplicity_zero hPdeg hkP hkm
  -- Shift back.
  have hdegsub : ∀ q : (PowerSeries K)[X], (q.comp (X - C c)).natDegree = q.natDegree := by
    simp [Polynomial.natDegree_comp]
  refine ⟨g₀.comp (X - C c), h₀.comp (X - C c), hg₀.comp_X_sub_C c, hh₀.comp_X_sub_C c, ?_,
    by rw [hdegsub, hg₀deg], by rw [hdegsub, hh₀deg]⟩
  simp [← Polynomial.mul_comp, ← hpr, Polynomial.comp_assoc]

end Polynomial
