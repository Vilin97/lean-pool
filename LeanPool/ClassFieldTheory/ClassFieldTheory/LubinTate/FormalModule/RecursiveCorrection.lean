/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LubinTate.FormalModule.RecursiveCoefficient
/-!
# Recursive monomial corrections for Lubin--Tate intertwiners

The coefficient selected in `RecursiveCoefficient` is inserted as a single
monomial.  This file proves that the insertion preserves the prescribed linear
term and cancels the defect coefficient in precisely that total degree.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v w

namespace LubinTate
namespace SameUniformizer

open LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}
variable {σ : Type w} [Fintype σ]

/-- The single monomial inserted at one step of the recursive construction. -/
noncomputable def monomialCorrection
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.monomial d
    (correctionCoefficient hπ e ebar hH d hd)

/-- Insert the recursive correction into the current approximation. -/
noncomputable def correctedIntertwiner
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries σ F.valuationSubring :=
  H + monomialCorrection hπ e ebar hH d hd

private theorem degree_le_order_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    (d : τ →₀ ℕ) (c : R) :
    (d.degree : ℕ∞) ≤ (MvPowerSeries.monomial d c).order := by
  classical
  by_cases hc : c = 0
  · simp [hc]
  · rw [MvPowerSeries.order_monomial_of_ne_zero hc]

private theorem natCast_le_order_pow_of_one_le_order
    {R : Type*} [CommRing R] {τ : Type*}
    (f : MvPowerSeries τ R) (n : ℕ)
    (hf : (1 : ℕ∞) ≤ f.order) :
    (n : ℕ∞) ≤ (f ^ n).order := by
  calc
    (n : ℕ∞) = n • (1 : ℕ∞) := by simp
    _ ≤ n • f.order := nsmul_le_nsmul_right hf n
    _ ≤ (f ^ n).order := MvPowerSeries.le_order_pow n

private theorem le_order_finset_sum
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} {f : ι → MvPowerSeries τ R} {m : ℕ∞}
    (h : ∀ i ∈ s, m ≤ (f i).order) :
    m ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact
        (le_min
          (h i (Finset.mem_insert_self i s))
          (ih fun j hj => h j (Finset.mem_insert_of_mem hj))).trans
        MvPowerSeries.min_order_le_add

private theorem natCast_sum_le_order_finset_prod_pow
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι} (f : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤
      (∏ i ∈ s, (f i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      calc
        ((n i + ∑ j ∈ s, n j : ℕ) : ℕ∞) =
            (n i : ℕ∞) + ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
          norm_cast
        _ ≤ ((f i) ^ n i).order +
            (∏ j ∈ s, (f j) ^ n j).order :=
          add_le_add
            (natCast_le_order_pow_of_one_le_order
              (f i) (n i) (hf i (Finset.mem_insert_self i s)))
            (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
        _ ≤ ((f i) ^ n i * ∏ j ∈ s, (f j) ^ n j).order :=
          MvPowerSeries.le_order_mul

private theorem order_sub_add_pred_le_order_pow_sub_pow
    {R : Type*} [CommRing R] {τ : Type*}
    (f g : MvPowerSeries τ R)
    (hf : (1 : ℕ∞) ≤ f.order)
    (hg : (1 : ℕ∞) ≤ g.order)
    (n : ℕ) :
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
      (f ^ n - g ^ n).order := by
  let q :=
    ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hq : ((n - 1 : ℕ) : ℕ∞) ≤ q.order := by
    apply le_order_finset_sum
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    calc
      ((n - 1 : ℕ) : ℕ∞) =
          (i : ℕ∞) + ((n - 1 - i : ℕ) : ℕ∞) := by
        norm_cast
        omega
      _ ≤ (f ^ i).order + (g ^ (n - 1 - i)).order :=
        add_le_add
          (natCast_le_order_pow_of_one_le_order f i hf)
          (natCast_le_order_pow_of_one_le_order
            g (n - 1 - i) hg)
      _ ≤ (f ^ i * g ^ (n - 1 - i)).order :=
        MvPowerSeries.le_order_mul
  have hfactor :
      (f - g) * q = f ^ n - g ^ n := by
    exact (Commute.all f g).mul_geom_sum₂ n
  calc
    (f - g).order + ((n - 1 : ℕ) : ℕ∞) ≤
        (f - g).order + q.order :=
      add_le_add (le_refl _) hq
    _ ≤ ((f - g) * q).order :=
      MvPowerSeries.le_order_mul
    _ = (f ^ n - g ^ n).order :=
      congrArg (fun h : MvPowerSeries τ R => h.order) hfactor

private theorem natCast_sum_add_one_le_order_prod_pow_sub_prod_pow
    {R : Type*} [CommRing R] {τ ι : Type*}
    {s : Finset ι}
    (f g : ι → MvPowerSeries τ R) (n : ι → ℕ)
    (hn : ∀ i ∈ s, n i ≠ 0)
    (hf : ∀ i ∈ s, (1 : ℕ∞) ≤ (f i).order)
    (hg : ∀ i ∈ s, (1 : ℕ∞) ≤ (g i).order)
    (hfg : ∀ i ∈ s, (2 : ℕ∞) ≤ (f i - g i).order) :
    (((∑ i ∈ s, n i) + 1 : ℕ) : ℕ∞) ≤
      ((∏ i ∈ s, (f i) ^ n i) -
        ∏ i ∈ s, (g i) ^ n i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hni : n i ≠ 0 :=
        hn i (Finset.mem_insert_self i s)
      have hpowDifference :
          ((n i + 1 : ℕ) : ℕ∞) ≤
            ((f i) ^ n i - (g i) ^ n i).order := by
        calc
          ((n i + 1 : ℕ) : ℕ∞) =
              (2 : ℕ∞) + ((n i - 1 : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ (f i - g i).order +
              ((n i - 1 : ℕ) : ℕ∞) :=
            add_le_add
              (hfg i (Finset.mem_insert_self i s)) (le_refl _)
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order :=
            order_sub_add_pred_le_order_pow_sub_pow
              (f i) (g i)
              (hf i (Finset.mem_insert_self i s))
              (hg i (Finset.mem_insert_self i s))
              (n i)
      have hprodF :
          ((∑ j ∈ s, n j : ℕ) : ℕ∞) ≤
            (∏ j ∈ s, (f j) ^ n j).order :=
        natCast_sum_le_order_finset_prod_pow f n
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      have hpowG :
          (n i : ℕ∞) ≤ ((g i) ^ n i).order :=
        natCast_le_order_pow_of_one_le_order
          (g i) (n i) (hg i (Finset.mem_insert_self i s))
      have hprodDifference :
          (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((∏ j ∈ s, (f j) ^ n j) -
              ∏ j ∈ s, (g j) ^ n j).order :=
        ih
          (fun j hj => hn j (Finset.mem_insert_of_mem hj))
          (fun j hj => hf j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj))
          (fun j hj => hfg j (Finset.mem_insert_of_mem hj))
      have hleft :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              ((n i + 1 : ℕ) : ℕ∞) +
                ((∑ j ∈ s, n j : ℕ) : ℕ∞) := by
            norm_cast
            omega
          _ ≤ ((f i) ^ n i - (g i) ^ n i).order +
              (∏ j ∈ s, (f j) ^ n j).order :=
            add_le_add hpowDifference hprodF
          _ ≤ (((f i) ^ n i - (g i) ^ n i) *
              ∏ j ∈ s, (f j) ^ n j).order :=
            MvPowerSeries.le_order_mul
      have hright :
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) ≤
            ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order := by
        calc
          (((n i + ∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) =
              (n i : ℕ∞) +
                (((∑ j ∈ s, n j) + 1 : ℕ) : ℕ∞) := by
            norm_cast
          _ ≤ ((g i) ^ n i).order +
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j).order :=
            add_le_add hpowG hprodDifference
          _ ≤ ((g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j)).order :=
            MvPowerSeries.le_order_mul
      rw [Finset.sum_insert hi, Finset.prod_insert hi,
        Finset.prod_insert hi]
      rw [show
        (f i) ^ n i * (∏ j ∈ s, (f j) ^ n j) -
            (g i) ^ n i * (∏ j ∈ s, (g j) ^ n j) =
          ((f i) ^ n i - (g i) ^ n i) *
              (∏ j ∈ s, (f j) ^ n j) +
            (g i) ^ n i *
              ((∏ j ∈ s, (f j) ^ n j) -
                ∏ j ∈ s, (g j) ^ n j) by ring]
      exact
        (le_min hleft hright).trans
          MvPowerSeries.min_order_le_add

/-- The linear part of `e(X_i)` for a same-uniformizer Lubin--Tate series. -/
private noncomputable def linearInVariable
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries σ F.valuationSubring :=
  MvPowerSeries.C π * MvPowerSeries.X i

omit [Fintype σ] in
private theorem linearInVariable_constantCoeff
    (π : F.valuationSubring) (i : σ) :
    MvPowerSeries.constantCoeff (linearInVariable π i) = 0 := by
  rw [linearInVariable, map_mul,
    MvPowerSeries.constantCoeff_C,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_X, mul_zero]

omit [Fintype σ] in
private theorem linearInVariable_hasSubst [Finite σ]
    (π : F.valuationSubring) :
    MvPowerSeries.HasSubst (linearInVariable (σ := σ) π) := by
  classical
  let := Fintype.ofFinite σ
  exact
    MvPowerSeries.hasSubst_of_constantCoeff_zero
        (linearInVariable_constantCoeff π)

omit [Fintype σ] in
private theorem one_le_order_inVariable
    (ebar : LubinTateSeries F π) (i : σ) :
    (1 : ℕ∞) ≤ (inVariable ebar i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (constantCoeff_inVariable ebar i)

omit [Fintype σ] in
private theorem one_le_order_linearInVariable
    (π : F.valuationSubring) (i : σ) :
    (1 : ℕ∞) ≤ (linearInVariable π i).order :=
  MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr
    (linearInVariable_constantCoeff π i)

omit [Fintype σ] in
private theorem two_le_order_inVariable_sub_linearInVariable
    (ebar : LubinTateSeries F π) (i : σ) :
    (2 : ℕ∞) ≤ (inVariable ebar i - linearInVariable π i).order := by
  classical
  apply MvPowerSeries.nat_le_order
  intro d hd
  have hdNat : d.degree < 2 := by
    exact_mod_cast hd
  rw [map_sub]
  by_cases hdi : d = Finsupp.single i (d i)
  · by_cases hzero : d i = 0
    · have hd0 : d = 0 := by
        rw [hdi, hzero]
        simp
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.constantCoeff_eq_zero]
    · have hone : d i = 1 := by
        rw [hdi, Finsupp.degree_single] at hdNat
        omega
      have hd1 : d = Finsupp.single i 1 := by
        rw [hdi, hone]
      subst d
      simp [inVariable, linearInVariable,
        PowerSeries.coeff_subst_single,
        LubinTateSeries.coeff_one_eq_uniformizer]
  · have hsingle : d ≠ Finsupp.single i 1 := by
      intro h
      apply hdi
      rw [h]
      simp
    simp [inVariable, linearInVariable,
      PowerSeries.coeff_subst_single, hdi,
      MvPowerSeries.coeff_X, hsingle]

omit [Fintype σ] in
private theorem degree_add_one_le_order_subst_monomial_sub_linear [Finite σ]
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    ((d.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c) -
        MvPowerSeries.subst (linearInVariable (σ := σ) π)
          (MvPowerSeries.monomial d c)).order := by
  classical
  let := Fintype.ofFinite σ
  have hprod :
      ((d.degree + 1 : ℕ) : ℕ∞) ≤
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n => (linearInVariable π i) ^ n)).order := by
    simpa only [Finsupp.prod, Finsupp.degree_apply] using
      natCast_sum_add_one_le_order_prod_pow_sub_prod_pow
        (s := d.support)
        (fun i : σ => inVariable ebar i)
        (linearInVariable (σ := σ) π)
        (fun i => d i)
        (fun i hi => Finsupp.mem_support_iff.mp hi)
        (fun i _ => one_le_order_inVariable ebar i)
        (fun i _ => one_le_order_linearInVariable π i)
        (fun i _ =>
          two_le_order_inVariable_sub_linearInVariable ebar i)
  rw [
    MvPowerSeries.subst_monomial
      (inVariable_hasSubst ebar) d c,
    MvPowerSeries.subst_monomial
      (linearInVariable_hasSubst (σ := σ) π) d c,
    ← MvPowerSeries.c_eq_algebraMap]
  rw [show
    MvPowerSeries.C c *
          d.prod (fun i n => (inVariable ebar i) ^ n) -
        MvPowerSeries.C c *
          d.prod (fun i n => (linearInVariable π i) ^ n) =
      c •
        (d.prod (fun i n => (inVariable ebar i) ^ n) -
          d.prod (fun i n => (linearInVariable π i) ^ n)) by
    rw [MvPowerSeries.smul_eq_C_mul]
    ring]
  exact hprod.trans MvPowerSeries.le_order_smul

omit [Fintype σ] in
private theorem coeff_subst_linearInVariable_monomial
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (linearInVariable (σ := σ) π)
          (MvPowerSeries.monomial d c)) =
      π ^ d.degree * c := by
  have hlinear :
      (Function.const σ π •
          (MvPowerSeries.X :
            σ → MvPowerSeries σ F.valuationSubring)) =
        linearInVariable (σ := σ) π := by
    funext i
    simp [linearInVariable, MvPowerSeries.smul_eq_C_mul]
  rw [← hlinear, ← MvPowerSeries.rescale_eq_subst,
    MvPowerSeries.coeff_rescale,
    MvPowerSeries.coeff_monomial_same]
  simp only [Finsupp.prod, Function.const_apply,
    Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]

omit [Fintype σ] in
private theorem coeff_subst_inVariables_monomial [Finite σ]
    (ebar : LubinTateSeries F π)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
          (MvPowerSeries.monomial d c)) =
      π ^ d.degree * c := by
  classical
  let := Fintype.ofFinite σ
  have horder :=
    degree_add_one_le_order_subst_monomial_sub_linear ebar d c
  have hlt :
      (d.degree : ℕ∞) <
        (MvPowerSeries.subst (fun i : σ => inVariable ebar i)
            (MvPowerSeries.monomial d c) -
          MvPowerSeries.subst (linearInVariable (σ := σ) π)
            (MvPowerSeries.monomial d c)).order :=
    by
      have hdegree_lt :
          (d.degree : ℕ∞) < ((d.degree + 1 : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.lt_succ_self d.degree
      exact hdegree_lt.trans_le horder
  have hcoeff :=
    MvPowerSeries.coeff_of_lt_order hlt
  rw [map_sub, sub_eq_zero] at hcoeff
  rw [hcoeff, coeff_subst_linearInVariable_monomial]

omit [Fintype σ] in
private theorem coeff_subst_inVariables_add_monomial [Finite σ]
    (ebar : LubinTateSeries F π)
    (H : MvPowerSeries σ F.valuationSubring)
    (d : σ →₀ ℕ) (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i)
          (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff d
          (MvPowerSeries.subst (fun i : σ ↦ inVariable ebar i) H) +
        π ^ d.degree * c := by
  classical
  let := Fintype.ofFinite σ
  rw [
    MvPowerSeries.subst_add (inVariable_hasSubst ebar),
    map_add,
    coeff_subst_inVariables_monomial]

private theorem constantCoeff_monomial_eq_zero
    {R : Type*} [CommRing R] {τ : Type*}
    {d : τ →₀ ℕ} (hd : d ≠ 0) (c : R) :
    MvPowerSeries.constantCoeff (MvPowerSeries.monomial d c) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_monomial_ne]
  exact Ne.symm hd

private theorem coeff_pow_add_monomial_sub_pow
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n - H ^ n) =
      if n = 1 then c else 0 := by
  classical
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  by_cases hn : n = 1
  · subst n
    simp [MvPowerSeries.coeff_monomial_same]
  · rcases n with _ | n
    · simp
    · have hn0 : n ≠ 0 := by
        intro h
        apply hn
        omega
      let M := MvPowerSeries.monomial d c
      let A := H + M
      have hMconstant :
          MvPowerSeries.constantCoeff M = 0 :=
        constantCoeff_monomial_eq_zero hd0 c
      have hAconstant :
          MvPowerSeries.constantCoeff A = 0 := by
        simp [A, hH, hMconstant]
      have hHorder : (1 : ℕ∞) ≤ H.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hH
      have hAorder : (1 : ℕ∞) ≤ A.order :=
        MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hAconstant
      have hpow :
          M.order + (n : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        simpa [A, M, add_sub_cancel_left] using
          order_sub_add_pred_le_order_pow_sub_pow
            A H hAorder hHorder (n + 1)
      have hdegree : (d.degree : ℕ∞) ≤ M.order :=
        degree_le_order_monomial d c
      have hn' : (1 : ℕ∞) ≤ (n : ℕ∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have horder :
          ((d.degree + 1 : ℕ) : ℕ∞) ≤
            (A ^ (n + 1) - H ^ (n + 1)).order := by
        calc
          ((d.degree + 1 : ℕ) : ℕ∞) =
              (d.degree : ℕ∞) + 1 := by norm_cast
          _ ≤ M.order + (n : ℕ∞) :=
            add_le_add hdegree hn'
          _ ≤ (A ^ (n + 1) - H ^ (n + 1)).order :=
            hpow
      have hlt :
          (d.degree : ℕ∞) <
            (A ^ (n + 1) - H ^ (n + 1)).order :=
        by
          have hdegree_lt :
              (d.degree : ℕ∞) < ((d.degree + 1 : ℕ) : ℕ∞) := by
            exact_mod_cast Nat.lt_succ_self d.degree
          exact hdegree_lt.trans_le horder
      have hzero := MvPowerSeries.coeff_of_lt_order hlt
      simpa [A, M, hn0] using hzero

private theorem coeff_pow_add_monomial
    {R : Type*} [CommRing R] {τ : Type*}
    {H : MvPowerSeries τ R}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (d : τ →₀ ℕ) (hd : 2 ≤ d.degree) (c : R) (n : ℕ) :
    MvPowerSeries.coeff d
        ((H + MvPowerSeries.monomial d c) ^ n) =
      MvPowerSeries.coeff d (H ^ n) +
        if n = 1 then c else 0 := by
  have h :=
    coeff_pow_add_monomial_sub_pow hH d hd c n
  rw [map_sub, sub_eq_iff_eq_add] at h
  simpa [add_comm] using h

private theorem coeff_subst_lubinTateSeries_add_monomial
    (e : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (PowerSeries.subst
          (H + MvPowerSeries.monomial d c)
          e.toPowerSeries) =
      MvPowerSeries.coeff d
          (PowerSeries.subst H e.toPowerSeries) +
        π * c := by
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simp at hd
  have hMconstant :
      MvPowerSeries.constantCoeff
          (MvPowerSeries.monomial d c) = 0 :=
    constantCoeff_monomial_eq_zero hd0 c
  have hHconstant :
      MvPowerSeries.constantCoeff H = 0 :=
    hH.constantCoeff_eq_zero
  have hnewSubst :
      PowerSeries.HasSubst
        (H + MvPowerSeries.monomial d c) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (by
      simp [hHconstant, hMconstant])
  let oldTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      MvPowerSeries.coeff d (H ^ n)
  let deltaTerm : ℕ → F.valuationSubring := fun n =>
    PowerSeries.coeff n e.toPowerSeries •
      if n = 1 then c else 0
  have hold : Function.HasFiniteSupport oldTerm := by
    simpa only [oldTerm] using
      PowerSeries.coeff_subst_finite hH.hasSubst e.toPowerSeries d
  have hdelta : Function.HasFiniteSupport deltaTerm := by
    rw [Function.HasFiniteSupport]
    refine (Set.finite_singleton 1).subset ?_
    intro n hn
    simp only [Function.mem_support] at hn
    simp only [Set.mem_singleton_iff]
    by_contra hne
    apply hn
    simp [deltaTerm, hne]
  rw [
    PowerSeries.coeff_subst hnewSubst e.toPowerSeries d,
    PowerSeries.coeff_subst hH.hasSubst e.toPowerSeries d]
  calc
    ∑ᶠ n : ℕ,
        PowerSeries.coeff n e.toPowerSeries •
          MvPowerSeries.coeff d
            ((H + MvPowerSeries.monomial d c) ^ n) =
        ∑ᶠ n : ℕ, (oldTerm n + deltaTerm n) := by
      apply finsum_congr
      intro n
      rw [coeff_pow_add_monomial hHconstant d hd c n,
        smul_add]
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        ∑ᶠ n : ℕ, deltaTerm n :=
      finsum_add_distrib hold hdelta
    _ = (∑ᶠ n : ℕ, oldTerm n) +
        PowerSeries.coeff 1 e.toPowerSeries * c := by
      congr 1
      rw [finsum_eq_single _ 1]
      · simp [deltaTerm, smul_eq_mul]
      · intro n hn
        simp [deltaTerm, hn]
    _ = (∑ᶠ n : ℕ, oldTerm n) + π * c := by
      rw [LubinTateSeries.coeff_one_eq_uniformizer]

private theorem coeff_defect_add_monomial
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) :
    MvPowerSeries.coeff d
        (defect e ebar (H + MvPowerSeries.monomial d c)) =
      MvPowerSeries.coeff d (defect e ebar H) +
        π * ((1 - π ^ (d.degree - 1)) * c) := by
  have hdegree : d.degree = (d.degree - 1) + 1 := by
    omega
  have hpow :
      π ^ d.degree = π * π ^ (d.degree - 1) := by
    calc
      π ^ d.degree = π ^ ((d.degree - 1) + 1) :=
        congrArg (fun n : ℕ => π ^ n) hdegree
      _ = π ^ (d.degree - 1) * π := by
        rw [pow_succ]
      _ = π * π ^ (d.degree - 1) := by
        rw [mul_comm]
  simp only [
    defect,
    map_sub,
    coeff_subst_lubinTateSeries_add_monomial e hH d hd c,
    coeff_subst_inVariables_add_monomial ebar H d c,
    hpow]
  ring

/-- A correction in total degree at least two does not change the prescribed
linear term. -/
theorem correctedIntertwiner_hasLinearTerm
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    HasLinearTerm (correctedIntertwiner hπ e ebar hH d hd) L := by
  rw [correctedIntertwiner, HasLinearTerm]
  have hd' : (2 : ℕ∞) ≤ (d.degree : ℕ∞) := by
    exact_mod_cast hd
  have hcorrection :
      (2 : ℕ∞) ≤ (monomialCorrection hπ e ebar hH d hd).order :=
    hd'.trans
      (degree_le_order_monomial d
        (correctionCoefficient hπ e ebar hH d hd))
  rw [show
    H + monomialCorrection hπ e ebar hH d hd - linearForm L =
      (H - linearForm L) +
        monomialCorrection hπ e ebar hH d hd by ring]
  exact
    (le_min hH hcorrection).trans
      MvPowerSeries.min_order_le_add

/-- The recursively selected degree-`d` monomial cancels the degree-`d`
coefficient of the intertwining defect. -/
theorem coeff_defect_correctedIntertwiner_eq_zero
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (e ebar : LubinTateSeries F π)
    {H : MvPowerSeries σ F.valuationSubring}
    {L : σ → F.valuationSubring} (hH : HasLinearTerm H L)
    (d : σ →₀ ℕ) (hd : 2 ≤ d.degree) :
    MvPowerSeries.coeff d
        (defect e ebar
          (correctedIntertwiner hπ e ebar hH d hd)) = 0 := by
  rw [
    correctedIntertwiner,
    monomialCorrection,
    coeff_defect_add_monomial e ebar hH d hd,
    ← uniformizer_mul_normalizedDefectCoefficient hπ e ebar hH d,
    correctionCoefficient_spec hπ e ebar hH d hd]
  ring

end SameUniformizer
end LubinTate

end
