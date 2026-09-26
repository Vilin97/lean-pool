/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerIntertwiner.CompletedSeries
public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.Padic.ChangedUniformizerCoefficient
public import Mathlib.RingTheory.PowerSeries.Expand
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
/-!
# Changed-uniformizer defect correction

This module computes how a degreewise correction changes the semilinear substitution defect and
  constructs the unique coefficient that kills that defect.
-/

@[expose] public section

noncomputable
section

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open SameUniformizer

/-- The defect of a candidate changed-uniformizer intertwiner: the difference
between its Frobenius-twisted multiplicative substitution and its
changed-standard substitution. -/
noncomputable def padicChangedUniformizerDefect
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    PowerSeries (padicCompletedUnramifiedWittRing p) :=
  PowerSeries.subst
      (padicCompletedMultiplicativeSeries p)
      (PowerSeries.map WittVector.frobenius H) -
    PowerSeries.subst H
      (padicCompletedChangedStandardSeries p u)

/-- Reduction modulo `p` commutes with coefficientwise Witt-vector Frobenius
through residue-field Frobenius. -/
theorem padicChangedUniformizerFrobenius_map_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p)) :
    PowerSeries.map WittVector.constantCoeff
        (PowerSeries.map WittVector.frobenius H) =
      PowerSeries.map
        (frobenius (AlgebraicClosure (ZMod p)) p)
        (PowerSeries.map WittVector.constantCoeff H) := by
  apply PowerSeries.ext
  intro n
  simp [PowerSeries.coeff_map, WittVector.constantCoeff_apply,
    WittVector.coeff_frobenius_charP, frobenius_def]

/-- The changed-uniformizer defect vanishes after coefficientwise reduction
modulo `p`. -/
theorem padicChangedUniformizerDefect_map_constantCoeff
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0) :
    PowerSeries.map WittVector.constantCoeff
        (padicChangedUniformizerDefect p u H) = 0 := by
  have hM :
      PowerSeries.HasSubst (padicCompletedMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (padicCompletedMultiplicativeSeries_constantCoeff p)
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hHbar :
      PowerSeries.HasSubst
        (PowerSeries.map WittVector.constantCoeff H) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change WittVector.constantCoeff
          (PowerSeries.constantCoeff H) = 0
      rw [hH, map_zero])
  rw [padicChangedUniformizerDefect, map_sub]
  change
    MvPowerSeries.map WittVector.constantCoeff
          (PowerSeries.subst (padicCompletedMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius H)) -
        MvPowerSeries.map WittVector.constantCoeff
          (PowerSeries.subst H
            (padicCompletedChangedStandardSeries p u)) =
      0
  rw [PowerSeries.map_subst hM,
    PowerSeries.map_subst hHsubst]
  change
    PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff
            (padicCompletedMultiplicativeSeries p))
          (PowerSeries.map WittVector.constantCoeff
            (PowerSeries.map WittVector.frobenius H)) -
        PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff H)
          (PowerSeries.map WittVector.constantCoeff
            (padicCompletedChangedStandardSeries p u)) =
      0
  rw [padicCompletedMultiplicativeSeries_map_constantCoeff,
    padicCompletedChangedStandardSeries_map_constantCoeff,
    padicChangedUniformizerFrobenius_map_constantCoeff]
  rw [← PowerSeries.expand_apply, ← PowerSeries.map_expand]
  change
    MvPowerSeries.map
          (frobenius (AlgebraicClosure (ZMod p)) p)
          (MvPowerSeries.expand p (Fact.out : p.Prime).ne_zero
            (PowerSeries.map WittVector.constantCoeff H)) -
        PowerSeries.subst
          (PowerSeries.map WittVector.constantCoeff H)
          (PowerSeries.X ^ p) =
      0
  rw [MvPowerSeries.map_frobenius_expand p
    (Fact.out : p.Prime).ne_zero]
  rw [PowerSeries.subst_pow hHbar,
    PowerSeries.subst_X hHbar]
  exact sub_self _

/-- Every coefficient of the changed-uniformizer defect is divisible by
`p` in the completed unramified Witt ring. -/
theorem padicChangedUniformizerDefect_coeff_mem_span_p
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    PowerSeries.coeff m (padicChangedUniformizerDefect p u H) ∈
      Ideal.span ({(p : padicCompletedUnramifiedWittRing p)} : Set _) := by
  rw [← WittVector.ker_constantCoeff]
  change
    WittVector.constantCoeff
      (PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H)) = 0
  rw [← PowerSeries.coeff_map,
    padicChangedUniformizerDefect_map_constantCoeff p u H hH,
    map_zero]

private theorem exists_padicChangedUniformizerNormalizedDefect
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    ∃ b : padicCompletedUnramifiedWittRing p,
      (p : padicCompletedUnramifiedWittRing p) * b =
        PowerSeries.coeff m
          (padicChangedUniformizerDefect p u H) := by
  have hmem :=
    padicChangedUniformizerDefect_coeff_mem_span_p p u H hH m
  rw [Ideal.mem_span_singleton] at hmem
  rcases hmem with ⟨b, hb⟩
  exact ⟨b, hb.symm⟩

/-- The degree-`m` changed-uniformizer defect coefficient divided by `p`. -/
noncomputable def padicChangedUniformizerNormalizedDefect
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    padicCompletedUnramifiedWittRing p :=
  Classical.choose
    (show ∃ b : padicCompletedUnramifiedWittRing p,
        (p : padicCompletedUnramifiedWittRing p) * b =
          PowerSeries.coeff m (padicChangedUniformizerDefect p u H) from by
      exact exists_padicChangedUniformizerNormalizedDefect p u H hH m)

private theorem padicChangedUniformizerNormalizedDefect_spec
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) :
    (p : padicCompletedUnramifiedWittRing p) *
        padicChangedUniformizerNormalizedDefect p u H hH m =
      PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H) :=
  Classical.choose_spec
    (exists_padicChangedUniformizerNormalizedDefect p u H hH m)

/-- The completed multiplicative Lubin--Tate series has order one. -/
theorem padicCompletedMultiplicativeSeries_order
    (p : ℕ) [Fact p.Prime] :
    (padicCompletedMultiplicativeSeries p).order = 1 := by
  apply PowerSeries.order_eq_nat.mpr
  constructor
  · rw [padicCompletedMultiplicativeSeries_coeff_one]
    exact
      WittVector.p_nonzero p (AlgebraicClosure (ZMod p))
  · intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa [PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      padicCompletedMultiplicativeSeries_constantCoeff p

/-- The degree-`m` coefficient of the `m`-th power of the completed
multiplicative series is `p ^ m`. -/
theorem padicCompletedMultiplicativeSeries_coeff_pow_self
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    PowerSeries.coeff m
        ((padicCompletedMultiplicativeSeries p) ^ m) =
      (p : padicCompletedUnramifiedWittRing p) ^ m := by
  let M := padicCompletedMultiplicativeSeries p
  have hMorder : M.order = 1 :=
    padicCompletedMultiplicativeSeries_order p
  calc
    PowerSeries.coeff m (M ^ m) =
        PowerSeries.constantCoeff
          (PowerSeries.divXPowOrder (M ^ m)) := by
      rw [PowerSeries.constantCoeff_divXPowOrder,
        PowerSeries.order_pow, hMorder]
      simp
    _ =
        PowerSeries.constantCoeff
          ((PowerSeries.divXPowOrder M) ^ m) := by
      rw [PowerSeries.divXPowOrder_pow]
    _ =
        (PowerSeries.constantCoeff
          (PowerSeries.divXPowOrder M)) ^ m := by
      exact map_pow PowerSeries.constantCoeff _ _
    _ = (PowerSeries.coeff 1 M) ^ m := by
      rw [PowerSeries.constantCoeff_divXPowOrder, hMorder]
      rfl
    _ = (p : padicCompletedUnramifiedWittRing p) ^ m := by
      rw [padicCompletedMultiplicativeSeries_coeff_one]

private theorem padicChangedUniformizer_coeff_pow_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        ((H + PowerSeries.monomial m c) ^ p) =
      PowerSeries.coeff m (H ^ p) := by
  let N := PowerSeries.monomial m c
  let A := H + N
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0)]
  have hAconstant : PowerSeries.constantCoeff A = 0 := by
    simp [A, hH, hNconstant]
  let Q :=
    ∑ i ∈ Finset.range p, A ^ i * H ^ (p - 1 - i)
  have hQ :
      ((p - 1 : ℕ) : ℕ∞) ≤ Q.order := by
    classical
    have hterm : ∀ i ∈ Finset.range p,
        ((p - 1 : ℕ) : ℕ∞) ≤
          (A ^ i * H ^ (p - 1 - i)).order := by
      intro i hi
      have hi' : i < p := Finset.mem_range.mp hi
      calc
        ((p - 1 : ℕ) : ℕ∞) =
            (i : ℕ∞) + ((p - 1 - i : ℕ) : ℕ∞) := by
          norm_cast
          omega
        _ ≤ (A ^ i).order + (H ^ (p - 1 - i)).order :=
          add_le_add
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              i hAconstant)
            (PowerSeries.le_order_pow_of_constantCoeff_eq_zero
              (p - 1 - i) hH)
        _ ≤ (A ^ i * H ^ (p - 1 - i)).order :=
          PowerSeries.le_order_mul _ _
    have hsum (s : Finset ℕ)
        (hs : ∀ i ∈ s,
          ((p - 1 : ℕ) : ℕ∞) ≤
            (A ^ i * H ^ (p - 1 - i)).order) :
        ((p - 1 : ℕ) : ℕ∞) ≤
          (∑ i ∈ s, A ^ i * H ^ (p - 1 - i)).order := by
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
          rw [Finset.sum_insert hi]
          exact
            (le_min
              (hs i (Finset.mem_insert_self i s))
              (ih fun j hj =>
                hs j (Finset.mem_insert_of_mem hj))).trans
            (PowerSeries.min_order_le_order_add _ _)
    simpa only [Q] using hsum (Finset.range p) hterm
  have hNorder : (m : ℕ∞) ≤ N.order := by
    apply PowerSeries.nat_le_order
    intro i hi
    rw [PowerSeries.coeff_monomial, ite_eq_right]
    exact Nat.ne_of_lt hi
  have hfactor :
      (A - H) * Q = A ^ p - H ^ p := by
    exact (Commute.all A H).mul_geom_sum₂ p
  have horder :
      ((m + (p - 1) : ℕ) : ℕ∞) ≤
        (A ^ p - H ^ p).order := by
    calc
      ((m + (p - 1) : ℕ) : ℕ∞) =
          (m : ℕ∞) + ((p - 1 : ℕ) : ℕ∞) := by
        norm_cast
      _ ≤ (A - H).order + Q.order := by
        apply add_le_add
        · simpa [A, N] using hNorder
        · exact hQ
      _ ≤ ((A - H) * Q).order :=
        PowerSeries.le_order_mul _ _
      _ = (A ^ p - H ^ p).order := by
        rw [hfactor]
  have hpTwo : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hltNat : m < m + (p - 1) := by omega
  have hlt :
      (m : ℕ∞) < (A ^ p - H ^ p).order := by
    have hcast :
        (m : ℕ∞) < ((m + (p - 1) : ℕ) : ℕ∞) := by
      exact_mod_cast hltNat
    exact hcast.trans_le horder
  have hcoeff :=
    PowerSeries.coeff_of_lt_order m hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  exact hcoeff

/-- Substituting the completed multiplicative series into a monomial scales
its `m`-th power by the monomial coefficient. -/
theorem padicChangedUniformizer_subst_monomial
    (p : ℕ) [Fact p.Prime]
    (m : ℕ) (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.subst
        (padicCompletedMultiplicativeSeries p)
        (PowerSeries.monomial m c) =
      PowerSeries.C c *
        (padicCompletedMultiplicativeSeries p) ^ m := by
  have hM :
      PowerSeries.HasSubst (padicCompletedMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (padicCompletedMultiplicativeSeries_constantCoeff p)
  rw [PowerSeries.monomial_eq_C_mul_X_pow,
    PowerSeries.subst_mul hM,
    PowerSeries.subst_C,
    PowerSeries.subst_pow hM,
    PowerSeries.subst_X hM]
  rfl

private theorem
    padicChangedUniformizerFrobenius_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (m : ℕ) (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.map WittVector.frobenius
        (H + PowerSeries.monomial m c) =
      PowerSeries.map WittVector.frobenius H +
        PowerSeries.monomial m (WittVector.frobenius c) := by
  apply PowerSeries.ext
  intro i
  by_cases hi : i = m
  · subst i
    simp [PowerSeries.coeff_map]
  · simp [PowerSeries.coeff_map, PowerSeries.coeff_monomial, hi]

private theorem padicChangedUniformizer_coeff_subst_frobenius_add_monomial
    (p : ℕ) [Fact p.Prime]
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (m : ℕ) (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        (PowerSeries.subst
          (padicCompletedMultiplicativeSeries p)
          (PowerSeries.map WittVector.frobenius
            (H + PowerSeries.monomial m c))) =
      PowerSeries.coeff m
          (PowerSeries.subst
            (padicCompletedMultiplicativeSeries p)
            (PowerSeries.map WittVector.frobenius H)) +
        (p : padicCompletedUnramifiedWittRing p) ^ m *
          WittVector.frobenius c := by
  have hM :
      PowerSeries.HasSubst (padicCompletedMultiplicativeSeries p) :=
    PowerSeries.HasSubst.of_constantCoeff_zero'
      (padicCompletedMultiplicativeSeries_constantCoeff p)
  rw [padicChangedUniformizerFrobenius_add_monomial,
    PowerSeries.subst_add hM, map_add,
    padicChangedUniformizer_subst_monomial,
    PowerSeries.coeff_C_mul,
    padicCompletedMultiplicativeSeries_coeff_pow_self]
  ring

private theorem padicChangedUniformizer_coeff_subst_changed_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        (PowerSeries.subst
          (H + PowerSeries.monomial m c)
          (padicCompletedChangedStandardSeries p u)) =
      PowerSeries.coeff m
          (PowerSeries.subst H
            (padicCompletedChangedStandardSeries p u)) +
        ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
            padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) * c := by
  let a : padicCompletedUnramifiedWittRing p :=
    (padicValuationUnitToCompletedUnramifiedWittUnit p u :
      padicCompletedUnramifiedWittRing p) * (p : padicCompletedUnramifiedWittRing p)
  let N := PowerSeries.monomial m c
  let A := H + N
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hm0 : m ≠ 0 := by omega
  have hNconstant : PowerSeries.constantCoeff N = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      PowerSeries.coeff_monomial, ite_eq_right (Ne.symm hm0)]
  have hAsubst : PowerSeries.HasSubst A :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by
      change PowerSeries.constantCoeff H +
          PowerSeries.constantCoeff N = 0
      rw [hH, hNconstant, zero_add])
  rw [padicCompletedChangedStandardSeries_eq,
    PowerSeries.subst_add hAsubst,
    PowerSeries.subst_mul hAsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_pow hAsubst,
    PowerSeries.subst_X hAsubst,
    PowerSeries.subst_add hHsubst,
    PowerSeries.subst_mul hHsubst,
    PowerSeries.subst_C,
    PowerSeries.subst_X hHsubst,
    PowerSeries.subst_pow hHsubst,
    PowerSeries.subst_X hHsubst]
  change
    PowerSeries.coeff m (PowerSeries.C a * A + A ^ p) =
      PowerSeries.coeff m (PowerSeries.C a * H + H ^ p) + a * c
  rw [map_add, map_add, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_C_mul]
  change
    a * PowerSeries.coeff m A + PowerSeries.coeff m (A ^ p) =
      a * PowerSeries.coeff m H + PowerSeries.coeff m (H ^ p) +
        a * c
  rw [show PowerSeries.coeff m A =
      PowerSeries.coeff m H + c by
    simp [A, N],
    padicChangedUniformizer_coeff_pow_add_monomial p H hH m hm c]
  ring

/-- Adding a monomial in degree `m` changes the degree-`m` defect by the
explicit Frobenius-linear correction term. -/
theorem padicChangedUniformizerDefect_coeff_add_monomial
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m)
    (c : padicCompletedUnramifiedWittRing p) :
    PowerSeries.coeff m
        (padicChangedUniformizerDefect p u
          (H + PowerSeries.monomial m c)) =
      PowerSeries.coeff m
          (padicChangedUniformizerDefect p u H) +
        (p : padicCompletedUnramifiedWittRing p) ^ m *
          WittVector.frobenius c -
        ((padicValuationUnitToCompletedUnramifiedWittUnit p u) :
            padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) * c := by
  rw [padicChangedUniformizerDefect, map_sub,
    padicChangedUniformizer_coeff_subst_frobenius_add_monomial,
    padicChangedUniformizer_coeff_subst_changed_add_monomial
      p u H hH m hm c]
  rw [padicChangedUniformizerDefect, map_sub]
  ring

/-- The unique coefficient that corrects the changed-uniformizer defect in
degree `m`. -/
noncomputable def padicChangedUniformizerCorrectionCoefficient
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    padicCompletedUnramifiedWittRing p :=
  Classical.choose
    (existsUnique_padicChangedUniformizerCoefficient p u m hm
      ((↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
          padicCompletedUnramifiedWittRing p) *
        padicChangedUniformizerNormalizedDefect p u H hH m))

/-- The correction coefficient satisfies its defining Frobenius fixed-point
equation. -/
theorem padicChangedUniformizerCorrectionCoefficient_spec
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    padicChangedUniformizerCorrectionCoefficient p u H hH m hm =
      (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
          padicCompletedUnramifiedWittRing p) *
        padicChangedUniformizerNormalizedDefect p u H hH m +
      (↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
          padicCompletedUnramifiedWittRing p) *
        (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
        WittVector.frobenius
          (padicChangedUniformizerCorrectionCoefficient
            p u H hH m hm) :=
  (Classical.choose_spec
    (existsUnique_padicChangedUniformizerCoefficient p u m hm
      ((↑((padicValuationUnitToCompletedUnramifiedWittUnit p u)⁻¹) :
          padicCompletedUnramifiedWittRing p) *
        padicChangedUniformizerNormalizedDefect p u H hH m))).1

/-- Adding the correction coefficient in degree `m` kills the degree-`m`
defect. -/
theorem padicChangedUniformizerCorrectionCoefficient_kills_defect
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    (H : PowerSeries (padicCompletedUnramifiedWittRing p))
    (hH : PowerSeries.constantCoeff H = 0)
    (m : ℕ) (hm : 2 ≤ m) :
    PowerSeries.coeff m
        (padicChangedUniformizerDefect p u
          (H + PowerSeries.monomial m
            (padicChangedUniformizerCorrectionCoefficient
              p u H hH m hm))) = 0 := by
  let V : (padicCompletedUnramifiedWittRing p)ˣ :=
    padicValuationUnitToCompletedUnramifiedWittUnit p u
  let b :=
    padicChangedUniformizerNormalizedDefect p u H hH m
  let c :=
    padicChangedUniformizerCorrectionCoefficient p u H hH m hm
  rw [padicChangedUniformizerDefect_coeff_add_monomial
    p u H hH m hm c,
    ← padicChangedUniformizerNormalizedDefect_spec p u H hH m]
  have hc :=
    padicChangedUniformizerCorrectionCoefficient_spec
      p u H hH m hm
  change c =
      (↑(V⁻¹) : padicCompletedUnramifiedWittRing p) * b +
        (↑(V⁻¹) : padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
          WittVector.frobenius c at hc
  have hc' :
      (V : padicCompletedUnramifiedWittRing p) * c =
        b + (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
          WittVector.frobenius c := by
    calc
      (V : padicCompletedUnramifiedWittRing p) * c =
          (V : padicCompletedUnramifiedWittRing p) *
            ((↑(V⁻¹) : padicCompletedUnramifiedWittRing p) * b +
                (↑(V⁻¹) : padicCompletedUnramifiedWittRing p) *
                (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
                WittVector.frobenius c) :=
        congrArg (fun z : padicCompletedUnramifiedWittRing p =>
          (V : padicCompletedUnramifiedWittRing p) * z) hc
      _ = b + (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
          WittVector.frobenius c := by
        simp [mul_add, mul_assoc]
  have hpow :
      (p : padicCompletedUnramifiedWittRing p) ^ m =
        (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
          (p : padicCompletedUnramifiedWittRing p) := by
    calc
      (p : padicCompletedUnramifiedWittRing p) ^ m =
          (p : padicCompletedUnramifiedWittRing p) ^ ((m - 1) + 1) := by
        congr 1
        omega
      _ = (p : padicCompletedUnramifiedWittRing p) ^ (m - 1) *
          (p : padicCompletedUnramifiedWittRing p) := by
        rw [pow_succ]
  rw [show
      (V : padicCompletedUnramifiedWittRing p) *
          (p : padicCompletedUnramifiedWittRing p) * c =
        (p : padicCompletedUnramifiedWittRing p) *
          ((V : padicCompletedUnramifiedWittRing p) * c) by ring,
    hc', hpow]
  ring

/-- Two one-variable power series have the same total truncation through
degree `m` when their coefficients agree through degree `m`. -/
theorem powerSeries_truncTotal_succ_eq_of_coeff_eq_le
    {R : Type*} [CommRing R]
    {H H' : PowerSeries R} (m : ℕ)
    (hcoeff : ∀ q : ℕ, q ≤ m →
      PowerSeries.coeff q H = PowerSeries.coeff q H') :
    H.truncTotal (m + 1) = H'.truncTotal (m + 1) := by
  ext d
  by_cases hd : d.degree < m + 1
  · rw [MvPowerSeries.coeff_truncTotal H hd,
      MvPowerSeries.coeff_truncTotal H' hd]
    have hdegree : d.degree = d () :=
      Finset.sum_eq_single () (by simp) (by simp)
    simpa only [PowerSeries.coeff_def (R := R) (s := d) rfl] using
      hcoeff (d ()) (by omega)
  · rw [MvPowerSeries.coeff_truncTotal_eq_zero H (not_lt.mp hd),
      MvPowerSeries.coeff_truncTotal_eq_zero H' (not_lt.mp hd)]

/-- The degree-`m` defect depends only on coefficients through degree `m`. -/
theorem padicChangedUniformizerDefect_coeff_eq_of_coeff_eq_le
    (p : ℕ) [Fact p.Prime]
    (u : (padicLocalField p).valuationSubringˣ)
    {H H' : PowerSeries (padicCompletedUnramifiedWittRing p)}
    (hH : PowerSeries.constantCoeff H = 0)
    (hH' : PowerSeries.constantCoeff H' = 0)
    (m : ℕ)
    (hcoeff : ∀ q : ℕ, q ≤ m →
      PowerSeries.coeff q H = PowerSeries.coeff q H') :
    PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H) =
      PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H') := by
  let M := padicCompletedMultiplicativeSeries p
  let E := padicCompletedChangedStandardSeries p u
  let ΦH := PowerSeries.map WittVector.frobenius H
  let ΦH' := PowerSeries.map WittVector.frobenius H'
  let k := m + 1
  have htruncH : H.truncTotal k = H'.truncTotal k :=
    powerSeries_truncTotal_succ_eq_of_coeff_eq_le m hcoeff
  have hcoeffΦ : ∀ q : ℕ, q ≤ m →
      PowerSeries.coeff q ΦH = PowerSeries.coeff q ΦH' := by
    intro q hq
    simp [ΦH, ΦH', PowerSeries.coeff_map, hcoeff q hq]
  have htruncΦ : ΦH.truncTotal k = ΦH'.truncTotal k :=
    powerSeries_truncTotal_succ_eq_of_coeff_eq_le m hcoeffΦ
  have hHsubst : PowerSeries.HasSubst H :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH
  have hH'subst : PowerSeries.HasSubst H' :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hH'
  have hMconstant : PowerSeries.constantCoeff M = 0 :=
    padicCompletedMultiplicativeSeries_constantCoeff p
  have hleft :
      (PowerSeries.subst H E).truncTotal k =
        (PowerSeries.subst H' E).truncTotal k := by
    change
      (MvPowerSeries.subst (fun _ : Unit ↦ H) E).truncTotal k =
        (MvPowerSeries.subst (fun _ : Unit ↦ H') E).truncTotal k
    calc
      (MvPowerSeries.subst (fun _ : Unit ↦ H) E).truncTotal k =
          (MvPowerSeries.subst
            (fun _ : Unit ↦ (H.truncTotal k).toMvPowerSeries)
            E).truncTotal k := by
        exact
          MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
            (f := E) (a := fun _ : Unit ↦ H)
            (x := fun _ : Unit ↦ k) hHsubst.const (fun _ ↦ le_rfl)
      _ = (MvPowerSeries.subst
            (fun _ : Unit ↦ (H'.truncTotal k).toMvPowerSeries)
            E).truncTotal k := by
        rw [htruncH]
      _ = (MvPowerSeries.subst (fun _ : Unit ↦ H') E).truncTotal k := by
        exact
          (MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_truncTotal_of_le
            (f := E) (a := fun _ : Unit ↦ H')
            (x := fun _ : Unit ↦ k) hH'subst.const
            (fun _ ↦ le_rfl)).symm
  have hright :
      (PowerSeries.subst M ΦH).truncTotal k =
        (PowerSeries.subst M ΦH').truncTotal k := by
    change
      (MvPowerSeries.subst (fun _ : Unit ↦ M) ΦH).truncTotal k =
        (MvPowerSeries.subst (fun _ : Unit ↦ M) ΦH').truncTotal k
    calc
      (MvPowerSeries.subst (fun _ : Unit ↦ M) ΦH).truncTotal k =
          (MvPowerSeries.subst (fun _ : Unit ↦ M)
            (ΦH.truncTotal k).toMvPowerSeries).truncTotal k := by
        exact
          MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
            (f := ΦH) (a := fun _ : Unit ↦ M)
            (fun _ ↦ hMconstant)
      _ = (MvPowerSeries.subst (fun _ : Unit ↦ M)
            (ΦH'.truncTotal k).toMvPowerSeries).truncTotal k := by
        rw [htruncΦ]
      _ = (MvPowerSeries.subst (fun _ : Unit ↦ M) ΦH').truncTotal k := by
        exact
          (MvPowerSeries.truncTotal_subst_eq_truncTotal_truncTotal_subst
            (f := ΦH') (a := fun _ : Unit ↦ M)
            (fun _ ↦ hMconstant)).symm
  have hdefect :
      (padicChangedUniformizerDefect p u H).truncTotal k =
        (padicChangedUniformizerDefect p u H').truncTotal k := by
    unfold padicChangedUniformizerDefect
    rw [map_sub, map_sub, hright, hleft]
  have hmDegree :
      (Finsupp.single () m).degree < k := by
    simp [k]
  calc
    PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H) =
        MvPowerSeries.coeff (Finsupp.single () m)
          ((padicChangedUniformizerDefect p u H).truncTotal k) :=
      (MvPowerSeries.coeff_truncTotal
        (padicChangedUniformizerDefect p u H) hmDegree).symm
    _ = MvPowerSeries.coeff (Finsupp.single () m)
          ((padicChangedUniformizerDefect p u H').truncTotal k) := by
      rw [hdefect]
    _ = PowerSeries.coeff m
        (padicChangedUniformizerDefect p u H') :=
      MvPowerSeries.coeff_truncTotal
        (padicChangedUniformizerDefect p u H') hmDegree

end LubinTate

end
