/-
Copyright (c) 2026 Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dean Cureton
-/
module

public import LeanPool.Puiseux.HenselSplitting
public import LeanPool.Puiseux.Algebraic

/-!
# Puiseux's theorem

This file proves **Puiseux's theorem**: over an algebraically closed field `K` of characteristic
zero, the field `PuiseuxSeries K = ⋃ n, K((t ^ (1 / n)))` of Puiseux series is algebraically
closed, and is an algebraic closure of the Laurent series field `K((t))`.

The proof is the classical Newton–Puiseux algorithm, organized as a strong induction on the
degree. Given a monic polynomial `p` of degree `m` over `K((t))`:

* a Tschirnhausen substitution `X ↦ X + c` kills the coefficient of degree `m - 1`
  (this is where characteristic zero enters);
* if all lower coefficients vanish the polynomial is `X ^ m`, with root `0`;
* otherwise, rescaling the variable by a monomial `t ^ (a / (nq))` chosen by the minimal Newton
  slope produces a monic polynomial `P` over `K⟦t⟧` whose reduction mod `t` is not a pure power
  (`LaurentSeries.newton_slope_scaling`);
* the reduction of `P` has a root of multiplicity strictly between `0` and `m`, so the Hensel
  splitting `Polynomial.Monic.exists_factorization_rootMultiplicity` produces a proper monic
  factor, and the induction hypothesis applies to it at a finer index
  (`LaurentSeries.newton_puiseux_descent`).

## Main results

* `PuiseuxSeries.exists_root_mem_subfield`: every monic polynomial of positive degree over
  `K((t))`, mapped along any embedding `LaurentSeries.toHahn K n`, has a root in the Puiseux
  subfield of `HahnSeries ℚ K`.
* `PuiseuxSeries.isAlgClosed`: `PuiseuxSeries K` is algebraically closed for `K` algebraically
  closed of characteristic zero.
* `PuiseuxSeries.isAlgClosure`: **Puiseux's theorem** — `PuiseuxSeries K` is an algebraic closure
  of `LaurentSeries K`.

## References

* [D. Eisenbud, *Commutative Algebra with a view toward Algebraic Geometry*][Eisenbud1995],
  Corollary 13.15

## Tags

puiseux series, newton polygon, algebraically closed, algebraic closure
-/

/- Ported to Lean Pool and its pinned Mathlib toolchain in September 2026. -/

@[expose] public section

noncomputable section

open Polynomial

/-! ## Auxiliary polynomial lemmas

Two generic lemmas over a field: the Tschirnhausen substitution killing the subleading
coefficient, and the existence of a root of intermediate multiplicity for a monic polynomial
with vanishing subleading coefficient which is not a pure power of `X`.
-/

namespace Polynomial

/-- **Tschirnhausen substitution**: for `p` monic of degree `m` over a field `F` with
`(m : F) ≠ 0`, substituting `X + C (-p.coeff (m - 1) / m)` for the variable preserves monicity
and degree and kills the coefficient of degree `m - 1`. -/
theorem Monic.tschirnhausen {F : Type*} [Field F] {p : F[X]} {m : ℕ} (hp : p.Monic)
    (hm : p.natDegree = m) (hmF : (m : F) ≠ 0) :
    (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).Monic ∧
      (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).natDegree = m ∧
      (p.comp (X + C (-p.coeff (m - 1) / (m : F)))).coeff (m - 1) = 0 := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmF
  set b : F := -p.coeff (m - 1) / (m : F)
  refine ⟨hp.comp_X_add_C b, by rw [← taylor_apply, natDegree_taylor, hm], ?_⟩
  rw [← taylor_apply, taylor_coeff]
  have hdeg : ((hasseDeriv (m - 1)) p).natDegree < 2 :=
    lt_of_le_of_lt (natDegree_hasseDeriv_le p (m - 1)) (by rw [hm]; omega)
  rw [eval_eq_sum_range' hdeg, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, hasseDeriv_coeff, hasseDeriv_coeff,
    show 1 + (m - 1) = m by omega]
  simp only [Nat.choose_symm (Nat.one_le_iff_ne_zero.mpr hm0), Nat.choose_one_right,
    show p.coeff m = 1 from hm ▸ hp.coeff_natDegree, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul, mul_one, pow_zero, pow_one, b]
  field_simp
  ring

/-- **A monic non-power has a mixed root**: over an algebraically closed field, a monic `r` of
degree `m` with `(m : K) ≠ 0`, vanishing coefficient of degree `m - 1`, and `r ≠ X ^ m` has a
root of multiplicity strictly between `0` and `m`. -/
theorem Monic.exists_rootMultiplicity_pos_lt {K : Type*} [Field K] [IsAlgClosed K]
    {r : K[X]} {m : ℕ} (hr : r.Monic) (hm : r.natDegree = m) (hmK : (m : K) ≠ 0)
    (hsub : r.coeff (m - 1) = 0) (hne : r ≠ X ^ m) :
    ∃ a : K, 0 < r.rootMultiplicity a ∧ r.rootMultiplicity a < m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmK
  have hr0 : r ≠ 0 := hr.ne_zero
  obtain ⟨a, ha⟩ :=
    IsAlgClosed.exists_root r (by rw [degree_eq_natDegree hr0, hm]; exact Nat.cast_ne_zero.mpr hm0)
  refine ⟨a, (rootMultiplicity_pos hr0).2 ha, ?_⟩
  by_contra hlt
  have heq : r = (X - C a) ^ m :=
    eq_of_monic_of_dvd_of_natDegree_le ((monic_X_sub_C a).pow m) hr
      (dvd_trans (pow_dvd_pow _ (Nat.le_of_not_lt hlt)) (pow_rootMultiplicity_dvd r a))
      (by simp [hm])
  have hcoef : ((X - C a) ^ m).coeff (m - 1) = -(m : K) * a := by
    rw [show m - 1 = ((X - C a) ^ m).natDegree - 1 by simp,
      ← nextCoeff_of_natDegree_pos (by simp [Nat.pos_of_ne_zero hm0]),
      (monic_X_sub_C a).nextCoeff_pow, nextCoeff_X_sub_C, nsmul_eq_mul, mul_neg,
      neg_mul]
  rw [heq, hcoef, mul_eq_zero, neg_eq_zero] at hsub
  exact hne (by simpa [hsub.resolve_left hmK] using heq)

end Polynomial

/-! ## The Newton slope rescaling

A Laurent series of nonnegative order is a power series; the per-summand monomial scaling
identity for the embeddings `toHahn`; and the main rescaling lemma producing an integral
polynomial with the right reduction and the root-transfer eval identity.
-/

namespace LaurentSeries

variable {K : Type*} [Field K]

/-- A Laurent series that is zero or has nonnegative order lies in the range of the coercion
from power series. -/
theorem exists_ofPowerSeries_eq_of_order_nonneg {f : LaurentSeries K}
    (hf : f = 0 ∨ 0 ≤ f.order) :
    ∃ F : PowerSeries K, HahnSeries.ofPowerSeries ℤ K F = f := by
  rcases hf with rfl | hf
  · exact ⟨0, PowerSeries.coe_zero⟩
  · exact ⟨PowerSeries.X ^ f.order.toNat * f.powerSeriesPart,
      LaurentSeries.X_order_mul_powerSeriesPart (Int.toNat_of_nonneg hf)⟩

/-- The expansion `expand K q` multiplies `orderTop` by `q`. -/
theorem orderTop_expand (q : ℕ+) (c : LaurentSeries K) :
    (expand K q c).orderTop = c.orderTop.map (fun k => (q : ℤ) * k) := by
  change (HahnSeries.embDomain
      ⟨⟨fun k => (q : ℤ) * k, fun _ _ h => mul_left_cancel₀ (by exact_mod_cast q.ne_zero) h⟩,
        mul_le_mul_iff_right₀ (by exact_mod_cast q.pos)⟩ c).orderTop = _
  rw [HahnSeries.orderTop_embDomain]
  rfl

/-- **Monomial scaling identity** (per-summand computation of the Newton rescaling): for
`τ = single (a / (nq)) 1`,
`τ ^ m * toHahn K (n * q) (expand K q c * single (a * (i - m)) 1) = toHahn K n c * τ ^ i`. -/
theorem toHahn_expand_single_scaling (n q : ℕ+) (a : ℤ) (c : LaurentSeries K) (i m : ℕ) :
    HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) (1 : K) ^ m *
        toHahn K (n * q) (expand K q c * HahnSeries.single (a * ((i : ℤ) - (m : ℤ))) 1)
      = toHahn K n c * HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) (1 : K) ^ i := by
  rw [map_mul, ← RingHom.comp_apply (toHahn K (n * q)) (expand K q),
    toHahn_comp_expand, toHahn_single, HahnSeries.single_pow, HahnSeries.single_pow,
    mul_left_comm, HahnSeries.single_mul_single]
  simp only [one_pow, mul_one, nsmul_eq_mul]
  congr 1
  push_cast
  ring_nf

/-- **Newton slope scaling**: given `p` monic of degree `m` over `K((t))` with vanishing
subleading coefficient and some nonzero lower coefficient, there are `q ≥ 1`, `a : ℤ`, and a
monic `P` of degree `m` over `K⟦X⟧` whose reduction has vanishing subleading coefficient but
some nonzero coefficient below the top, such that roots transfer: evaluating
`p.map (toHahn K n)` at `τ * y` (with `τ = single (a / (nq)) 1`) equals `τ ^ m` times the
evaluation at `y` of the image of `P` under `toHahn K (n * q)` composed with the Laurent
coercion. -/
theorem newton_slope_scaling (n : ℕ+) {p : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p.Monic) (hm : p.natDegree = m) (hsub : p.coeff (m - 1) = 0)
    (hex : ∃ i < m, p.coeff i ≠ 0) :
    ∃ (q : ℕ+) (a : ℤ) (P : Polynomial (PowerSeries K)),
      P.Monic ∧ P.natDegree = m ∧
      (P.map (PowerSeries.constantCoeff (R := K))).coeff (m - 1) = 0 ∧
      (∃ i₀ < m, (P.map (PowerSeries.constantCoeff (R := K))).coeff i₀ ≠ 0) ∧
      ∀ y : HahnSeries ℚ K,
        (p.map (toHahn K n)).eval
            (HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1 * y)
          = HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1 ^ m *
              (P.map ((toHahn K (n * q)).comp (HahnSeries.ofPowerSeries ℤ K))).eval y := by
  classical
  obtain ⟨i₁, hi₁m, hi₁⟩ := hex
  obtain ⟨i₀, hi₀S, hi₀min⟩ :=
    ((Finset.range m).filter (fun i => p.coeff i ≠ 0)).exists_min_image
      (fun i => ((p.coeff i).order : ℚ) / ((m - i : ℕ) : ℚ))
      ⟨i₁, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi₁m, hi₁⟩⟩
  obtain ⟨hi₀m, hc₀⟩ : i₀ < m ∧ p.coeff i₀ ≠ 0 := by
    simpa [Finset.mem_filter, Finset.mem_range] using hi₀S
  obtain ⟨q, hq⟩ : ∃ q : ℕ+, (q : ℕ) = m - i₀ :=
    ⟨⟨m - i₀, Nat.zero_lt_sub_of_lt hi₀m⟩, rfl⟩
  set a : ℤ := (p.coeff i₀).order
  have hqZ : ((q : ℕ) : ℤ) = (m : ℤ) - (i₀ : ℤ) := by rw [hq]; omega
  have key : ∀ i, i < m → p.coeff i ≠ 0 →
      0 ≤ ((q : ℕ) : ℤ) * (p.coeff i).order + a * ((i : ℤ) - (m : ℤ)) := by
    intro i him hci
    have h := hi₀min i (Finset.mem_filter.2 ⟨Finset.mem_range.2 him, hci⟩)
    rw [div_le_div_iff₀ (mod_cast Nat.zero_lt_sub_of_lt hi₀m : (0 : ℚ) < _)
      (mod_cast Nat.zero_lt_sub_of_lt him : (0 : ℚ) < _)] at h
    push_cast [Nat.cast_sub him.le, Nat.cast_sub hi₀m.le] at h
    have hscaled : a * ((m : ℤ) - i) ≤ (p.coeff i).order * ((m : ℤ) - i₀) := by
      exact_mod_cast h
    rw [hqZ]
    nlinarith only [hscaled]
  let d : ℕ → LaurentSeries K := fun i =>
    expand K q (p.coeff i) * HahnSeries.single (a * ((i : ℤ) - (m : ℤ))) 1
  have hdm : d m = 1 := by simp [d, show p.coeff m = 1 from hm ▸ hp.coeff_natDegree]
  have hdz {i} (hi : p.coeff i = 0) : d i = 0 := by simp [d, hi]
  have horder {i} (him : i < m) (hci : p.coeff i ≠ 0) :
      (d i).orderTop = ((((q : ℕ) : ℤ) * (p.coeff i).order + a * ((i : ℤ) - (m : ℤ)) : ℤ) :
        WithTop ℤ) := by
    simp [d, HahnSeries.orderTop_mul, orderTop_expand, HahnSeries.orderTop_single one_ne_zero,
      ← HahnSeries.order_eq_orderTop_of_ne_zero hci]
  have hdnn (i : ℕ) :
      (0 : WithTop ℤ) ≤ (if i ≤ m then d i else 0 : LaurentSeries K).orderTop := by
    split_ifs with him
    · rcases eq_or_lt_of_le him with heq | hlt
      · simp [heq, hdm]
      · by_cases hci : p.coeff i = 0
        · simp [hdz hci]
        · rw [horder hlt hci]; exact_mod_cast key i hlt hci
    · simp
  choose D hD using fun i => exists_ofPowerSeries_eq_of_order_nonneg
    (Or.inr (HahnSeries.zero_le_orderTop_iff.mp (hdnn i)))
  have hDi {i} (hi : i ≤ m) : HahnSeries.ofPowerSeries ℤ K (D i) = d i :=
    (hD i).trans (ite_eq_left hi)
  have hDm : D m = 1 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ) (by simpa [hdm] using hDi le_rfl)
  have hDm1 : D (m - 1) = 0 :=
    HahnSeries.ofPowerSeries_injective (Γ := ℤ)
      (by simpa [hdz hsub] using hDi (Nat.sub_le m 1))
  have hPcoeff (j) :
      (∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)).coeff j =
        if j ≤ m then D j else 0 := by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq']
  set P : Polynomial (PowerSeries K) := ∑ i ∈ Finset.range (m + 1), Polynomial.monomial i (D i)
  have hnd : P.natDegree = m :=
    le_antisymm (Polynomial.natDegree_le_iff_coeff_eq_zero.2 fun N hN => by
        rw [hPcoeff, ite_eq_right (Nat.not_le_of_lt hN)])
      (Polynomial.le_natDegree_of_ne_zero (by
        rw [hPcoeff, ite_eq_left le_rfl, hDm]
        exact one_ne_zero))
  have hmon : P.Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, hnd, hPcoeff, ite_eq_left le_rfl, hDm]
  refine ⟨q, a, P, hmon, hnd, ?_, ?_, ?_⟩
  · rw [Polynomial.coeff_map, hPcoeff, ite_eq_left (Nat.sub_le _ _), hDm1, map_zero]
  · refine ⟨i₀, hi₀m, ?_⟩
    rw [Polynomial.coeff_map, hPcoeff, ite_eq_left hi₀m.le]
    have hz : ((q : ℕ) : ℤ) * (p.coeff i₀).order + a * ((i₀ : ℤ) - (m : ℤ)) = 0 := by
      rw [hqZ]; simp [a]; ring
    have := HahnSeries.coeff_orderTop_ne (by rw [horder hi₀m hc₀, hz])
    rw [← hDi hi₀m.le] at this
    convert this
    simpa using (LaurentSeries.coeff_coe_powerSeries (D i₀) 0).symm
  · intro y
    conv_lhs =>
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans_eq hm))]
    conv_rhs =>
      rw [Polynomial.eval_eq_sum_range'
        (Nat.lt_succ_of_le (Polynomial.natDegree_map_le.trans_eq hnd)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hPcoeff, ite_eq_left him, RingHom.comp_apply,
      hDi him]
    simp only [d]
    rw [mul_pow, ← mul_assoc, ← mul_assoc, toHahn_expand_single_scaling n q a (p.coeff i) i m]

/-! ## The descent step and the main induction -/

/-- **Newton–Puiseux descent**: for `p'` monic of degree `m` over `K((t))` with vanishing
subleading coefficient and some nonzero lower coefficient (`K` algebraically closed,
characteristic zero), there are `q ≥ 1`, an element `τ` in the range of `toHahn K (n * q)`,
and a monic `g` with `1 ≤ deg g < m` such that every root `y` of `g.map (toHahn K (n * q))`
gives the root `τ * y` of `p'.map (toHahn K n)`. -/
theorem newton_puiseux_descent [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p' : Polynomial (LaurentSeries K)} {m : ℕ}
    (hp : p'.Monic) (hm : p'.natDegree = m) (hsub : p'.coeff (m - 1) = 0)
    (hex : ∃ i < m, p'.coeff i ≠ 0) :
    ∃ (q : ℕ+) (τ : HahnSeries ℚ K) (g : Polynomial (LaurentSeries K)),
      τ ∈ (toHahn K (n * q)).fieldRange ∧ g.Monic ∧
      1 ≤ g.natDegree ∧ g.natDegree < m ∧
      ∀ y : HahnSeries ℚ K,
        (g.map (toHahn K (n * q))).eval y = 0 →
        (p'.map (toHahn K n)).eval (τ * y) = 0 := by
  obtain ⟨q, a, P, hPm, hPdeg, hRsub, hRex, hev⟩ := newton_slope_scaling n hp hm hsub hex
  set R := P.map (PowerSeries.constantCoeff (R := K))
  have hRmonic : R.Monic := hPm.map _
  have hRdeg : R.natDegree = m := by rw [hPm.natDegree_map, hPdeg]
  have hRne : R ≠ X ^ m :=
    hRex.elim fun i₀ ⟨hi₀, hne⟩ h => by simp [h, Polynomial.coeff_X_pow, hi₀.ne] at hne
  obtain ⟨a₀, hk0, hkm⟩ := hRmonic.exists_rootMultiplicity_pos_lt hRdeg
    (Nat.cast_ne_zero.mpr (hex.elim fun _ ⟨hi, _⟩ => (Nat.zero_lt_of_lt hi).ne')) hRsub hRne
  obtain ⟨G, h, hG, hh, hPeq, hGdeg, -⟩ :=
    hPm.exists_factorization_rootMultiplicity (a := a₀) hPdeg rfl hk0 hkm
  refine ⟨q, HahnSeries.single ((a : ℚ) / ((n * q : ℕ+) : ℕ)) 1,
    G.map (HahnSeries.ofPowerSeries ℤ K), ⟨HahnSeries.single a 1, by rw [toHahn_single]⟩,
    hG.map _, ?_, ?_, ?_⟩
  · rw [hG.natDegree_map, hGdeg]; exact hk0
  · rw [hG.natDegree_map, hGdeg]; exact hkm
  · intro y hy
    rw [hev y, ← Polynomial.map_map, hPeq, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.eval_mul, hy, zero_mul, mul_zero]

end LaurentSeries

namespace PuiseuxSeries

open LaurentSeries

variable {K : Type*} [Field K]

/-- The Newton–Puiseux induction, in the form suitable for strong induction on the degree:
the statement is quantified over all indices `n`, since the descent step re-enters at a finer
index. -/
private theorem exists_root_mem_subfield_aux [IsAlgClosed K] [CharZero K] :
    ∀ m : ℕ, ∀ (n : ℕ+) (p : Polynomial (LaurentSeries K)), p.Monic → p.natDegree = m →
      1 ≤ m → ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahn K n)).eval x = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n p hp hm hm1
  have hmF : (m : LaurentSeries K) ≠ 0 :=
    mt (fun h => HahnSeries.single_eq_zero_iff.mp
        ((map_natCast (HahnSeries.C : K →+* LaurentSeries K) m).symm.trans h))
      (Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt hm1) : (m : K) ≠ 0)
  obtain ⟨hp'm, hp'deg, hp'sub⟩ := hp.tschirnhausen hm hmF
  set b : LaurentSeries K := -p.coeff (m - 1) / (m : LaurentSeries K)
  set p' : Polynomial (LaurentSeries K) := p.comp (X + C b) with hp'def
  have key : ∃ y ∈ PuiseuxSeries.subfield K, (p'.map (toHahn K n)).eval y = 0 := by
    by_cases hex : ∃ i < m, p'.coeff i ≠ 0
    · obtain ⟨q, τ, g, hτ, hg, hg1, hgm, htrans⟩ :=
        newton_puiseux_descent n hp'm hp'deg hp'sub hex
      obtain ⟨y, hy, hy0⟩ := ih g.natDegree hgm (n * q) g hg rfl hg1
      exact ⟨τ * y, mul_mem ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n * q, hτ⟩) hy,
        htrans y hy0⟩
    · have hall : ∀ i < m, p'.coeff i = 0 := fun i hi => by_contra fun hne => hex ⟨i, hi, hne⟩
      have hXm : p' = X ^ m := Polynomial.ext fun i => by
        rcases lt_trichotomy i m with hi | rfl | hi
        · simp [hall i hi, Polynomial.coeff_X_pow, hi.ne]
        · simpa [Polynomial.leadingCoeff, hp'deg] using hp'm.leadingCoeff
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Polynomial.coeff_X_pow,
            ite_eq_right hi.ne']
      exact ⟨0, zero_mem _, by simp [hXm, Polynomial.map_pow, zero_pow (Nat.ne_zero_of_lt hm1)]⟩
  obtain ⟨y, hy, hy0⟩ := key
  refine ⟨y + toHahn K n b, add_mem hy ((PuiseuxSeries.mem_subfield_iff K).mpr ⟨n, b, rfl⟩), ?_⟩
  simpa [hp'def, Polynomial.map_comp, Polynomial.eval_comp] using hy0

/-- **Puiseux root of a monic polynomial** (the Newton–Puiseux induction): for `K` algebraically
closed of characteristic zero, every monic `p` over `K((t))` of positive degree, mapped along
any embedding `toHahn K n`, has a root in the Puiseux subfield. -/
theorem exists_root_mem_subfield [IsAlgClosed K] [CharZero K] (n : ℕ+)
    {p : Polynomial (LaurentSeries K)} (hp : p.Monic) (hdeg : 1 ≤ p.natDegree) :
    ∃ x ∈ PuiseuxSeries.subfield K, (p.map (toHahn K n)).eval x = 0 :=
  exists_root_mem_subfield_aux p.natDegree n p hp rfl hdeg

/-! ## Main results -/

/-- **Puiseux series are algebraically closed**: for `K` an algebraically closed field of
characteristic zero, the field of Puiseux series over `K` is algebraically closed. This is the
analytic half of **Puiseux's theorem**, proved by the Newton–Puiseux algorithm. -/
instance isAlgClosed (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosed (PuiseuxSeries K) := by
  apply IsAlgClosed.of_exists_root
  intro r hr hirr
  classical
  set ι : PuiseuxSeries K →+* HahnSeries ℚ K := (PuiseuxSeries.subfield K).subtype
  have hιinj : Function.Injective ι := Subtype.val_injective
  obtain ⟨N, hN⟩ :=
    PuiseuxSeries.exists_common_index K
      ((Finset.range (r.natDegree + 1)).image fun i => (r.map ι).coeff i)
      (fun x hx => by
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        rw [Polynomial.coeff_map]
        exact (r.coeff i).2)
  have hrange : ∀ i, (r.map ι).coeff i ∈ Set.range (LaurentSeries.toHahn K N) := by
    intro i
    by_cases hi : i ≤ r.natDegree
    · exact Set.mem_range.mpr
        (hN _ (Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr (Nat.lt_succ_of_le hi), rfl⟩))
    · refine ⟨0, ?_⟩
      rw [map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt
        (by rw [hr.natDegree_map]; exact Nat.lt_of_not_le hi)]
  obtain ⟨p, hpmap, hpdeg, hpm⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic
      ((Polynomial.lifts_iff_coeff_lifts _).mpr hrange) (hr.map ι)
  have hdeg : 1 ≤ p.natDegree := by
    rw [natDegree_eq_of_degree_eq hpdeg, hr.natDegree_map]; exact hirr.natDegree_pos
  obtain ⟨x, hx, hx0⟩ := exists_root_mem_subfield N hpm hdeg
  refine ⟨⟨x, hx⟩, hιinj ?_⟩
  calc
    ι (r.eval ⟨x, hx⟩) = (r.map ι).eval x :=
      (Polynomial.eval₂_hom ι (⟨x, hx⟩ : PuiseuxSeries K)).symm.trans
        (Polynomial.eval_map ι x).symm
    _ = (p.map (toHahn K N)).eval x := congrArg (fun f => f.eval x) hpmap.symm
    _ = 0 := hx0
    _ = ι 0 := (map_zero ι).symm

/-- **Puiseux's theorem**: for `K` an algebraically closed field of characteristic zero, the
Puiseux series field `⋃ n, K((t ^ (1 / n)))` is an algebraic closure of the Laurent series
field `K((t))`. Algebraicity holds over any field (`PuiseuxSeries.isAlgebraic`); algebraic
closedness is the Newton–Puiseux algorithm (`PuiseuxSeries.isAlgClosed`). -/
instance isAlgClosure (K : Type*) [Field K] [IsAlgClosed K] [CharZero K] :
    IsAlgClosure (LaurentSeries K) (PuiseuxSeries K) :=
  ⟨inferInstance, inferInstance⟩

end PuiseuxSeries
