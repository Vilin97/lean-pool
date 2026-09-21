/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.NormalForm

/-!
# Multiplicativity of support order type and degree

LM24, Fact 3.4.1 imports Berarducci's theorem that support order type is multiplicative on
weakly principal nonpositive real Hahn series. The predicate
`OrderTypeMultiplicativeOnWeaklyPrincipal` records that exact mathematical law. Its proof in
characteristic zero is in `ConwayRefinement.HahnSeries.OrdinalValue.OrderTypeMultiplicativity`.

The repaired `degree_truncLE_mul_lt` formalizes LM24, Lemma 3.4.2. The printed statement omits
`c ≠ 0`: its first support condition holds vacuously for `c = 0`, whereas the asserted strict
inequality then reads `⊥ < ⊥`. The additional hypothesis is necessary and is already implicit in
the printed proof when it chooses an exponent strictly below the support of `c`.

Assuming the Berarducci law, `degree_mul_of_orderTypeMultiplicativeOnWeaklyPrincipal` proves
LM24, Proposition 3.4.3. Its proof uses the principal head decomposition from Proposition 3.3.7
and the repaired truncation lemma. In the branch where a remainder has smaller degree, the proof
uses the strict upper bound with the degree of the original factor; this repairs the repeated
right-hand side in the displayed inequality on published page 30.

Mathlib contains no corresponding Hahn-series multiplicativity theorem.
CombinatorialGames supplies `NatOrdinal.wpow_add`, which is used to show that the natural product
of two powers of `ω` is again a power of `ω`. The order-type law itself remains precisely the
Berarducci prerequisite imported by LM24.
-/

universe v

public noncomputable section

namespace HahnSeries

open Ordinal

variable {R : Type v} [Ring R]

private theorem naturalMul_isAdditivelyPrincipal {a b : Ordinal}
    (ha : a.IsAdditivelyPrincipal) (hb : b.IsAdditivelyPrincipal) :
    (NatOrdinal.of a * NatOrdinal.of b).val.IsAdditivelyPrincipal := by
  obtain ⟨e, rfl⟩ := Ordinal.isAdditivelyPrincipal_iff.mp ha
  obtain ⟨f, rfl⟩ := Ordinal.isAdditivelyPrincipal_iff.mp hb
  apply Ordinal.isAdditivelyPrincipal_iff.mpr
  refine ⟨(NatOrdinal.of e + NatOrdinal.of f).val, ?_⟩
  have he : NatOrdinal.of (Ordinal.omega0 ^ e) =
      (ω^ (NatOrdinal.of e) : NatOrdinal) := by
    apply NatOrdinal.val.injective
    simp only [NatOrdinal.val_of, NatOrdinal.val_wpow]
  have hf : NatOrdinal.of (Ordinal.omega0 ^ f) =
      (ω^ (NatOrdinal.of f) : NatOrdinal) := by
    apply NatOrdinal.val.injective
    simp only [NatOrdinal.val_of, NatOrdinal.val_wpow]
  rw [he, hf, ← NatOrdinal.wpow_add, NatOrdinal.val_wpow]

/-- A Hahn series whose support order type is strictly below a weakly principal support has
strictly smaller degree. -/
theorem degree_lt_of_supportOrderType_lt_of_isWeaklyPrincipal
    {x y : R⟦ℝ⟧} (hx : IsWeaklyPrincipal x)
    (hyx : y.supportOrderType < x.supportOrderType) :
    y.degree < x.degree := by
  obtain ⟨e, he⟩ :=
    Ordinal.isAdditivelyPrincipal_iff.mp (isWeaklyPrincipal_iff.mp hx)
  rw [he] at hyx
  rw [degree_eq_cantorDegree, degree_eq_cantorDegree, he]
  have hpower : Ordinal.cantorDegree (Ordinal.omega0 ^ e) = NatOrdinal.of e := by
    rw [Ordinal.cantorDegree_of_ne_zero
      (Ordinal.opow_ne_zero e Ordinal.omega0_ne_zero),
      Ordinal.log_opow Ordinal.one_lt_omega0]
  by_cases hy : y = 0
  · rw [hy, supportOrderType_zero, Ordinal.cantorDegree_zero, hpower]
    exact WithBot.bot_lt_coe _
  rw [Ordinal.cantorDegree_of_ne_zero (supportOrderType_eq_zero.not.mpr hy), hpower,
    WithBot.coe_lt_coe, NatOrdinal.of_lt_iff]
  exact (Ordinal.lt_opow_iff_log_lt Ordinal.one_lt_omega0
    (supportOrderType_eq_zero.not.mpr hy)).mp hyx

namespace Nonpositive

variable {K : Type v} [Field K]

/-- Support order type is multiplicative, using Hessenberg multiplication, on weakly principal
nonpositive real Hahn series over `K`. This is the exact law imported as LM24, Fact 3.4.1.

The predicate is meaningful over any field. Its proof from Berarducci's result retains the
characteristic-zero hypothesis in LM24's ambient assumptions. -/
def OrderTypeMultiplicativeOnWeaklyPrincipal (K : Type v) [Field K] : Prop :=
  ∀ b c : Nonpositive ℝ K,
    IsWeaklyPrincipal (b : K⟦ℝ⟧) →
      IsWeaklyPrincipal (c : K⟦ℝ⟧) →
        ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).supportOrderType =
          (NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType *
            NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType).val

/-- Characterization of multiplicativity on weakly principal series. -/
theorem orderTypeMultiplicativeOnWeaklyPrincipal_iff :
    OrderTypeMultiplicativeOnWeaklyPrincipal K ↔
      ∀ b c : Nonpositive ℝ K,
        IsWeaklyPrincipal (b : K⟦ℝ⟧) →
          IsWeaklyPrincipal (c : K⟦ℝ⟧) →
            ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).supportOrderType =
              (NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType *
                NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType).val :=
  Iff.rfl

/-- Apply support-order-type multiplicativity to two weakly principal series. -/
theorem OrderTypeMultiplicativeOnWeaklyPrincipal.supportOrderType_mul
    (h : OrderTypeMultiplicativeOnWeaklyPrincipal K)
    {b c : Nonpositive ℝ K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧))
    (hc : IsWeaklyPrincipal (c : K⟦ℝ⟧)) :
    ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).supportOrderType =
      (NatOrdinal.of (b : K⟦ℝ⟧).supportOrderType *
        NatOrdinal.of (c : K⟦ℝ⟧).supportOrderType).val :=
  (orderTypeMultiplicativeOnWeaklyPrincipal_iff.mp h) b c hb hc

/-- Under support-order-type multiplicativity, degree is multiplicative on weakly principal
series. -/
theorem OrderTypeMultiplicativeOnWeaklyPrincipal.degree_mul
    (h : OrderTypeMultiplicativeOnWeaklyPrincipal K)
    {b c : Nonpositive ℝ K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧))
    (hc : IsWeaklyPrincipal (c : K⟦ℝ⟧)) :
    ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  rw [degree_eq_cantorDegree, h.supportOrderType_mul hb hc,
    ← NatOrdinal.cantorDegree_eq_ordinalCantorDegree,
    NatOrdinal.cantorDegree_mul, NatOrdinal.cantorDegree_of,
    NatOrdinal.cantorDegree_of, ← degree_eq_cantorDegree,
    ← degree_eq_cantorDegree]

/-- Under support-order-type multiplicativity, the product of weakly principal series is weakly
principal. -/
theorem OrderTypeMultiplicativeOnWeaklyPrincipal.isWeaklyPrincipal_mul
    (h : OrderTypeMultiplicativeOnWeaklyPrincipal K)
    {b c : Nonpositive ℝ K}
    (hb : IsWeaklyPrincipal (b : K⟦ℝ⟧))
    (hc : IsWeaklyPrincipal (c : K⟦ℝ⟧)) :
    IsWeaklyPrincipal ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧) := by
  rw [isWeaklyPrincipal_iff, h.supportOrderType_mul hb hc]
  exact naturalMul_isAdditivelyPrincipal
    (isWeaklyPrincipal_iff.mp hb) (isWeaklyPrincipal_iff.mp hc)

private theorem truncLE_eq_zero_of_support_subset_Ioi
    {x : K⟦ℝ⟧} {a : ℝ} (h : x.support ⊆ Set.Ioi a) :
    truncLE a x = 0 := by
  rw [← support_eq_empty_iff, support_truncLE]
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hi hia ↦ (not_lt_of_ge hia) (h hi)

private theorem support_mul_subset_Ici_add
    {b c : K⟦ℝ⟧} {x y : ℝ}
    (hb : b.support ⊆ Set.Ici x) (hc : c.support ⊆ Set.Ici y) :
    (b * c).support ⊆ Set.Ici (x + y) := by
  intro z hz
  obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hz
  have hxi : x ≤ i := hb hi
  have hyj : y ≤ j := hc hj
  exact add_le_add hxi hyj

private theorem support_mul_subset_Ioi_add
    {b c : K⟦ℝ⟧} {x y : ℝ}
    (hb : b.support ⊆ Set.Ioi x) (hc : c.support ⊆ Set.Ioi y) :
    (b * c).support ⊆ Set.Ioi (x + y) := by
  intro z hz
  obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset hz
  have hxi : x < i := hb hi
  have hyj : y < j := hc hj
  exact add_lt_add hxi hyj

/-- The strict-support case of the repaired LM24, Lemma 3.4.2. The nonzero hypothesis is necessary
because strict support containment is vacuous for the zero series. -/
theorem degree_truncLE_mul_lt_of_isPrincipal_of_support_subset_Ioi
    {b c : Nonpositive ℝ K} {x : ℝ}
    (hb : IsPrincipal b) (hcne : c ≠ 0)
    (hc : (c : K⟦ℝ⟧).support ⊆ Set.Ioi x) :
    (truncLE x ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)).degree <
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  have hcne' : (c : K⟦ℝ⟧) ≠ 0 := by simpa using hcne
  have horderMem : (c : K⟦ℝ⟧).order ∈ (c : K⟦ℝ⟧).support :=
    (mem_support _ _).mpr (coeff_order_eq_zero.not.mpr hcne')
  have hxorder : x < (c : K⟦ℝ⟧).order := hc horderMem
  let y : ℝ := (x + (c : K⟦ℝ⟧).order) / 2
  have hxy : x < y := by
    dsimp [y]
    linarith
  have hyorder : y < (c : K⟦ℝ⟧).order := by
    dsimp [y]
    linarith
  have hcAboveY : (c : K⟦ℝ⟧).support ⊆ Set.Ioi y := by
    intro i hi
    exact hyorder.trans_le
      (order_le_of_coeff_ne_zero ((mem_support _ _).mp hi))
  let a : ℝ := x - y
  let d : K⟦ℝ⟧ := truncLE a (b : K⟦ℝ⟧)
  let e : K⟦ℝ⟧ := truncGT a (b : K⟦ℝ⟧)
  have ha : a < 0 := by
    dsimp [a]
    linarith
  have hbLUB : IsLUB (b : K⟦ℝ⟧).support 0 :=
    (supportSup_eq_coe_iff.mp hb.supportSup_eq_zero).2
  obtain ⟨g, hg, hag, _⟩ := hbLUB.exists_between ha
  have hdne : d ≠ (b : K⟦ℝ⟧) := by
    intro hdb
    have hcoeff := congrArg (fun z : K⟦ℝ⟧ ↦ z.coeff g) hdb
    have hzero : d.coeff g = 0 :=
      coeff_truncLE_of_lt hag (b : K⟦ℝ⟧)
    exact (mem_support _ _).mp hg (hcoeff.symm.trans hzero)
  have hecAbove : (e * (c : K⟦ℝ⟧)).support ⊆ Set.Ioi x := by
    intro z hz
    obtain ⟨i, hi, j, hj, hij⟩ := support_mul_subset hz
    rw [support_truncGT] at hi
    have hji : y < j := hcAboveY hj
    have hia : a < i := hi.2
    change x < z
    rw [← hij]
    dsimp [a] at hia
    linarith
  have htruncProduct :
      truncLE x ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧) =
        truncLE x (d * (c : K⟦ℝ⟧)) := by
    change truncLE x ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)) = _
    calc
      truncLE x ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)) =
          truncLE x ((d + e) * (c : K⟦ℝ⟧)) := by
            rw [truncLE_add_truncGT a (b : K⟦ℝ⟧)]
      _ = truncLE x (d * (c : K⟦ℝ⟧) + e * (c : K⟦ℝ⟧)) := by
        rw [add_mul]
      _ = truncLE x (d * (c : K⟦ℝ⟧)) +
          truncLE x (e * (c : K⟦ℝ⟧)) := truncLE_add _ _ _
      _ = truncLE x (d * (c : K⟦ℝ⟧)) := by
        rw [truncLE_eq_zero_of_support_subset_Ioi hecAbove, add_zero]
  rw [htruncProduct]
  calc
    (truncLE x (d * (c : K⟦ℝ⟧))).degree ≤
        (d * (c : K⟦ℝ⟧)).degree :=
      degree_truncLE_le _ _
    _ ≤ d.degree + (c : K⟦ℝ⟧).degree := degree_mul_le _ _
    _ < (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
      rw [WithBot.add_lt_add_iff_right (degree_eq_bot.not.mpr hcne')]
      exact degree_lt_of_supportOrderType_lt_of_isWeaklyPrincipal
        hb.isWeaklyPrincipal (supportOrderType_truncLE_lt a hdne)

private theorem degree_truncLE_le_zero_of_support_subset_Ici
    {c : K⟦ℝ⟧} {x : ℝ} (hc : c.support ⊆ Set.Ici x) :
    (truncLE x c).degree ≤ 0 := by
  have hsupport : (truncLE x c).support ⊆ {x} := by
    rw [support_truncLE]
    rintro i ⟨hi, hix⟩
    exact Set.mem_singleton_iff.mpr (le_antisymm hix (hc hi))
  have hfinite : (truncLE x c).support.Finite :=
    Set.finite_singleton x |>.subset hsupport
  by_cases hzero : truncLE x c = 0
  · simp [hzero]
  · rw [(degree_eq_zero.mpr ⟨hzero, hfinite⟩)]

/-- The weak-support, positive-degree case of the repaired LM24, Lemma 3.4.2. -/
theorem degree_truncLE_mul_lt_of_isPrincipal_of_support_subset_Ici_of_degree_pos
    {b c : Nonpositive ℝ K} {x : ℝ}
    (hb : IsPrincipal b) (hc : (c : K⟦ℝ⟧).support ⊆ Set.Ici x)
    (hcDegree : 0 < (c : K⟦ℝ⟧).degree) :
    (truncLE x ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)).degree <
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  let cLower : Nonpositive ℝ K :=
    ⟨truncLE x (c : K⟦ℝ⟧),
      (mem_nonpositiveSubring (x := truncLE x (c : K⟦ℝ⟧))).mpr
        ((support_truncLE_subset x (c : K⟦ℝ⟧)).trans (support_subset c))⟩
  let cUpper : Nonpositive ℝ K :=
    ⟨truncGT x (c : K⟦ℝ⟧),
      (mem_nonpositiveSubring (x := truncGT x (c : K⟦ℝ⟧))).mpr
        ((support_truncGT_subset x (c : K⟦ℝ⟧)).trans (support_subset c))⟩
  have hcLowerDegree : (cLower : K⟦ℝ⟧).degree ≤ 0 :=
    degree_truncLE_le_zero_of_support_subset_Ici hc
  have hcUpperNe : cUpper ≠ 0 := by
    intro hzero
    have hzero' : truncGT x (c : K⟦ℝ⟧) = 0 :=
      congrArg Subtype.val hzero
    have hcEq : (c : K⟦ℝ⟧) = (cLower : K⟦ℝ⟧) := by
      calc
        (c : K⟦ℝ⟧) =
            truncLE x (c : K⟦ℝ⟧) + truncGT x (c : K⟦ℝ⟧) :=
          (truncLE_add_truncGT x (c : K⟦ℝ⟧)).symm
        _ = (cLower : K⟦ℝ⟧) := by rw [hzero', add_zero]
    exact (not_lt_of_ge (hcEq ▸ hcLowerDegree)) hcDegree
  have hcUpperSupport : (cUpper : K⟦ℝ⟧).support ⊆ Set.Ioi x := by
    rw [show (cUpper : K⟦ℝ⟧) = truncGT x (c : K⟦ℝ⟧) from rfl,
      support_truncGT]
    exact fun _ hi ↦ hi.2
  have hcUpperDegree :
      (cUpper : K⟦ℝ⟧).degree ≤ (c : K⟦ℝ⟧).degree :=
    degree_mono_support (support_truncGT_subset x (c : K⟦ℝ⟧))
  have hLower :
      (truncLE x ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧))).degree <
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    calc
      (truncLE x ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧))).degree ≤
          ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧)).degree :=
        degree_truncLE_le _ _
      _ ≤ (b : K⟦ℝ⟧).degree + (cLower : K⟦ℝ⟧).degree :=
        degree_mul_le _ _
      _ < (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
        rw [WithBot.add_lt_add_iff_left
          (degree_eq_bot.not.mpr (by simpa using hb.ne_zero))]
        exact hcLowerDegree.trans_lt hcDegree
  have hUpper :
      (truncLE x ((b : K⟦ℝ⟧) * (cUpper : K⟦ℝ⟧))).degree <
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    exact (degree_truncLE_mul_lt_of_isPrincipal_of_support_subset_Ioi
      hb hcUpperNe hcUpperSupport).trans_le
        (add_le_add_right hcUpperDegree _)
  have hProduct :
      (b : K⟦ℝ⟧) * (c : K⟦ℝ⟧) =
        (b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧) +
          (b : K⟦ℝ⟧) * (cUpper : K⟦ℝ⟧) := by
    rw [show (c : K⟦ℝ⟧) =
      (cLower : K⟦ℝ⟧) + (cUpper : K⟦ℝ⟧) from
        (truncLE_add_truncGT x (c : K⟦ℝ⟧)).symm, mul_add]
  change (truncLE x ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧))).degree < _
  calc
    (truncLE x ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧))).degree =
        (truncLE x ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧) +
          (b : K⟦ℝ⟧) * (cUpper : K⟦ℝ⟧))).degree :=
      congrArg degree (congrArg (truncLE x) hProduct)
    _ = (truncLE x ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧)) +
        truncLE x ((b : K⟦ℝ⟧) * (cUpper : K⟦ℝ⟧))).degree := by
      rw [truncLE_add]
    _ ≤ max
        (truncLE x ((b : K⟦ℝ⟧) * (cLower : K⟦ℝ⟧))).degree
        (truncLE x ((b : K⟦ℝ⟧) * (cUpper : K⟦ℝ⟧))).degree :=
      degree_add_le _ _
    _ < (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree :=
      max_lt hLower hUpper

/-- Repaired LM24, Lemma 3.4.2. If `b` is principal, `c` is nonzero, and the support of `c` is
strictly above `x`, or is weakly above `x` with positive degree, then the degree of the weak lower
truncation of `b * c` is strictly below the natural sum of the factor degrees. -/
theorem degree_truncLE_mul_lt
    {b c : Nonpositive ℝ K} {x : ℝ}
    (hb : IsPrincipal b) (hcne : c ≠ 0)
    (hc : (c : K⟦ℝ⟧).support ⊆ Set.Ioi x ∨
      (c : K⟦ℝ⟧).support ⊆ Set.Ici x ∧
        0 < (c : K⟦ℝ⟧).degree) :
    (truncLE x ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧)).degree <
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  rcases hc with hc | ⟨hc, hcDegree⟩
  · exact degree_truncLE_mul_lt_of_isPrincipal_of_support_subset_Ioi
      hb hcne hc
  · exact
      degree_truncLE_mul_lt_of_isPrincipal_of_support_subset_Ici_of_degree_pos
        hb hc hcDegree

private theorem degree_truncLE_principal_mul_remainder_lt
    {p r c : Nonpositive ℝ K} {x : ℝ}
    (hp : IsPrincipal p) (hcne : c ≠ 0)
    (hrSupport : (r : K⟦ℝ⟧).support ⊆ Set.Ici x)
    (hrDegree : (r : K⟦ℝ⟧).degree ≤ (c : K⟦ℝ⟧).degree)
    (hrStrict : (c : K⟦ℝ⟧).degree = 0 →
      (r : K⟦ℝ⟧).support ⊆ Set.Ioi x) :
    (truncLE x ((p * r : Nonpositive ℝ K) : K⟦ℝ⟧)).degree <
      (p : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  rcases hrDegree.lt_or_eq with hrDegree | hrDegree
  · calc
      (truncLE x ((p * r : Nonpositive ℝ K) : K⟦ℝ⟧)).degree ≤
          ((p : K⟦ℝ⟧) * (r : K⟦ℝ⟧)).degree :=
        degree_truncLE_le _ _
      _ ≤ (p : K⟦ℝ⟧).degree + (r : K⟦ℝ⟧).degree :=
        degree_mul_le _ _
      _ < (p : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
        rw [WithBot.add_lt_add_iff_left
          (degree_eq_bot.not.mpr (by simpa using hp.ne_zero))]
        exact hrDegree
  · have hrne : r ≠ 0 := by
      intro hzero
      have hcDegreeBot : (c : K⟦ℝ⟧).degree = ⊥ := by
        rw [← hrDegree, hzero]
        exact degree_zero
      exact hcne (by
        apply Subtype.ext
        exact degree_eq_bot.mp hcDegreeBot)
    have hcne' : (c : K⟦ℝ⟧) ≠ 0 := by simpa using hcne
    rcases (zero_le_degree_of_ne_zero hcne').eq_or_lt with
      hcDegree | hcDegree
    · have h := degree_truncLE_mul_lt hp hrne
        (Or.inl (hrStrict hcDegree.symm))
      simpa [hrDegree] using h
    · have h := degree_truncLE_mul_lt hp hrne
        (Or.inr ⟨hrSupport, hrDegree ▸ hcDegree⟩)
      simpa [hrDegree] using h

/-- The weak lower truncation at `x + y` of a product of two head decompositions
`translate x b₁ + b'` and `translate y c₁ + c'`. The head term `translate (x + y) (b₁ * c₁)`
survives the truncation unchanged, since `b₁ * c₁` is nonpositive; the two cross terms are
truncated at the shifted cutoffs `y` and `x`; the remainder product is truncated at `x + y`. -/
private theorem truncLE_add_mul_add_of_head_decomposition
    (b₁ b' c₁ c' : Nonpositive ℝ K) (x y : ℝ) :
    truncLE (x + y) ((translate x (b₁ : K⟦ℝ⟧) + (b' : K⟦ℝ⟧)) *
        (translate y (c₁ : K⟦ℝ⟧) + (c' : K⟦ℝ⟧))) =
      translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧) +
        (translate x (truncLE y ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
          (translate y (truncLE x ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
            truncLE (x + y) ((b' * c' : Nonpositive ℝ K) : K⟦ℝ⟧))) := by
  have hHeadProduct :
      translate x (b₁ : K⟦ℝ⟧) * translate y (c₁ : K⟦ℝ⟧) =
        translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧) :=
    translate_mul_translate x y (b₁ : K⟦ℝ⟧) (c₁ : K⟦ℝ⟧)
  have hSecondProduct :
      translate x (b₁ : K⟦ℝ⟧) * (c' : K⟦ℝ⟧) =
        translate x ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧) := by
    simpa using translate_mul_translate
      x 0 (b₁ : K⟦ℝ⟧) (c' : K⟦ℝ⟧)
  have hThirdProduct :
      (b' : K⟦ℝ⟧) * translate y (c₁ : K⟦ℝ⟧) =
        translate y ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧) := by
    rw [mul_comm]
    simpa using translate_mul_translate
      y 0 (c₁ : K⟦ℝ⟧) (b' : K⟦ℝ⟧)
  have hHeadTrunc :
      truncLE (x + y) (translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧)) =
        translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧) := by
    rw [truncLE_translate, _root_.sub_self]
    rw [truncLE_eq_self_of_support_subset_Iic (support_subset (b₁ * c₁))]
  have hSecondTrunc :
      truncLE (x + y) (translate x ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧)) =
        translate x (truncLE y ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧)) := by
    rw [truncLE_translate]
    simp only [add_sub_cancel_left]
  have hThirdTrunc :
      truncLE (x + y) (translate y ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧)) =
        translate y (truncLE x ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧)) := by
    rw [truncLE_translate]
    simp only [add_sub_cancel_right]
  rw [add_mul, mul_add, mul_add, hHeadProduct, hSecondProduct, hThirdProduct,
    truncLE_add, truncLE_add, truncLE_add, hHeadTrunc, hSecondTrunc, hThirdTrunc]
  simp only [add_assoc]
  rfl

/-- The remainder-times-remainder term of the head expansion has degree strictly below the sum of
the factor degrees. When that sum is positive, the truncation of a series supported weakly above
the cutoff has degree at most `0`. When both degrees are `0`, both remainders are supported
strictly above their cutoffs, so the truncated product vanishes and its degree is `⊥`. -/
private theorem degree_truncLE_remainder_mul_remainder_lt
    {b c b' c' : Nonpositive ℝ K} {x y : ℝ} (hbne : b ≠ 0) (hcne : c ≠ 0)
    (hb'Support : (b' : K⟦ℝ⟧).support ⊆ Set.Ici x)
    (hc'Support : (c' : K⟦ℝ⟧).support ⊆ Set.Ici y)
    (hb'Strict : (b : K⟦ℝ⟧).degree = 0 → (b' : K⟦ℝ⟧).support ⊆ Set.Ioi x)
    (hc'Strict : (c : K⟦ℝ⟧).degree = 0 → (c' : K⟦ℝ⟧).support ⊆ Set.Ioi y) :
    (truncLE (x + y) ((b' * c' : Nonpositive ℝ K) : K⟦ℝ⟧)).degree <
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  have hbne' : (b : K⟦ℝ⟧) ≠ 0 := by simpa using hbne
  have hcne' : (c : K⟦ℝ⟧) ≠ 0 := by simpa using hcne
  have hFourthSupport :
      ((b' : K⟦ℝ⟧) * (c' : K⟦ℝ⟧)).support ⊆ Set.Ici (x + y) :=
    support_mul_subset_Ici_add hb'Support hc'Support
  have hFourthDegreeLe :
      (truncLE (x + y) ((b' : K⟦ℝ⟧) * (c' : K⟦ℝ⟧))).degree ≤ 0 :=
    degree_truncLE_le_zero_of_support_subset_Ici hFourthSupport
  have hsumDegreeNonnegative :
      0 ≤ (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree :=
    add_nonneg (zero_le_degree_of_ne_zero hbne') (zero_le_degree_of_ne_zero hcne')
  change (truncLE (x + y) ((b' : K⟦ℝ⟧) * (c' : K⟦ℝ⟧))).degree < _
  rcases hsumDegreeNonnegative.eq_or_lt with hzero | hpos
  · obtain ⟨db, hdb⟩ := WithBot.ne_bot_iff_exists.mp
      (degree_eq_bot.not.mpr hbne')
    obtain ⟨dc, hdc⟩ := WithBot.ne_bot_iff_exists.mp
      (degree_eq_bot.not.mpr hcne')
    have hsum : db + dc = 0 := by
      apply WithBot.coe_injective
      simpa [WithBot.coe_add, hdb, hdc] using hzero.symm
    have hdegrees := NatOrdinal.add_eq_zero_iff.mp hsum
    have hbDegree : (b : K⟦ℝ⟧).degree = 0 :=
      hdb.symm.trans
        (congrArg ((↑·) : NatOrdinal → WithBot NatOrdinal) hdegrees.1)
    have hcDegree : (c : K⟦ℝ⟧).degree = 0 :=
      hdc.symm.trans
        (congrArg ((↑·) : NatOrdinal → WithBot NatOrdinal) hdegrees.2)
    have hstrictSupport :
        ((b' : K⟦ℝ⟧) * (c' : K⟦ℝ⟧)).support ⊆ Set.Ioi (x + y) :=
      support_mul_subset_Ioi_add
        (hb'Strict hbDegree) (hc'Strict hcDegree)
    rw [truncLE_eq_zero_of_support_subset_Ioi hstrictSupport, degree_zero,
      ← hzero]
    exact WithBot.bot_lt_coe 0
  · exact hFourthDegreeLe.trans_lt hpos

/-- In the head expansion of `b * c`, the three terms other than the head have degree strictly
below the sum of the factor degrees: each cross term is a principal head times a remainder,
bounded by the repaired truncation lemma, and the remainder product is handled separately. -/
private theorem degree_head_expansion_remainder_lt
    {b c b₁ b' c₁ c' : Nonpositive ℝ K} {x y : ℝ} (hbne : b ≠ 0) (hcne : c ≠ 0)
    (hb₁Principal : IsPrincipal b₁) (hc₁Principal : IsPrincipal c₁)
    (hb'Support : (b' : K⟦ℝ⟧).support ⊆ Set.Ici x)
    (hc'Support : (c' : K⟦ℝ⟧).support ⊆ Set.Ici y)
    (hb₁Degree : (b₁ : K⟦ℝ⟧).degree = (b : K⟦ℝ⟧).degree)
    (hc₁Degree : (c₁ : K⟦ℝ⟧).degree = (c : K⟦ℝ⟧).degree)
    (hb'Degree : (b' : K⟦ℝ⟧).degree ≤ (b : K⟦ℝ⟧).degree)
    (hc'Degree : (c' : K⟦ℝ⟧).degree ≤ (c : K⟦ℝ⟧).degree)
    (hb'Strict : (b : K⟦ℝ⟧).degree = 0 → (b' : K⟦ℝ⟧).support ⊆ Set.Ioi x)
    (hc'Strict : (c : K⟦ℝ⟧).degree = 0 → (c' : K⟦ℝ⟧).support ⊆ Set.Ioi y) :
    (translate x (truncLE y ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
        (translate y (truncLE x ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
          truncLE (x + y) ((b' * c' : Nonpositive ℝ K) : K⟦ℝ⟧))).degree <
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  have hSecondDegree :
      (translate x (truncLE y ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧))).degree <
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    rw [degree_translate, ← hb₁Degree]
    exact degree_truncLE_principal_mul_remainder_lt
      hb₁Principal hcne hc'Support hc'Degree hc'Strict
  have hThirdDegree :
      (translate y (truncLE x ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧))).degree <
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    rw [degree_translate, ← hc₁Degree, add_comm]
    exact degree_truncLE_principal_mul_remainder_lt
      hc₁Principal hbne hb'Support hb'Degree hb'Strict
  have hFourthDegree :=
    degree_truncLE_remainder_mul_remainder_lt hbne hcne hb'Support hc'Support
      hb'Strict hc'Strict
  exact (degree_add_le _ _).trans_lt
    (max_lt hSecondDegree ((degree_add_le _ _).trans_lt (max_lt hThirdDegree hFourthDegree)))

/-- Assuming the Berarducci weakly-principal order-type law, degree is multiplicative on all
nonpositive real Hahn series. This is LM24, Proposition 3.4.3, with Hessenberg addition on the
degrees and its absorbing bottom convention at zero. -/
theorem degree_mul_of_orderTypeMultiplicativeOnWeaklyPrincipal
    (h : OrderTypeMultiplicativeOnWeaklyPrincipal K)
    (b c : Nonpositive ℝ K) :
    ((b * c : Nonpositive ℝ K) : K⟦ℝ⟧).degree =
      (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
  obtain rfl | hbne := eq_or_ne b 0
  · simp
  obtain rfl | hcne := eq_or_ne c 0
  · simp
  obtain ⟨b₁, x, b', hb₁Principal, hbEq, hb'Support, hb₁Degree,
    hb'Degree, hb'Strict⟩ := exists_principal_head_decomposition hbne
  obtain ⟨c₁, y, c', hc₁Principal, hcEq, hc'Support, hc₁Degree,
    hc'Degree, hc'Strict⟩ := exists_principal_head_decomposition hcne
  have hExpansion :
      truncLE (x + y) ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)) =
        translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧) +
          (translate x (truncLE y ((b₁ * c' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
            (translate y (truncLE x ((c₁ * b' : Nonpositive ℝ K) : K⟦ℝ⟧)) +
              truncLE (x + y) ((b' * c' : Nonpositive ℝ K) : K⟦ℝ⟧))) := by
    rw [hbEq, hcEq]
    exact truncLE_add_mul_add_of_head_decomposition b₁ b' c₁ c' x y
  have hHeadDegree :
      (translate (x + y) ((b₁ * c₁ : Nonpositive ℝ K) : K⟦ℝ⟧)).degree =
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    rw [degree_translate,
      h.degree_mul hb₁Principal.isWeaklyPrincipal hc₁Principal.isWeaklyPrincipal,
      hb₁Degree, hc₁Degree]
  have hRemainderDegree := degree_head_expansion_remainder_lt hbne hcne hb₁Principal
    hc₁Principal hb'Support hc'Support hb₁Degree hc₁Degree hb'Degree hc'Degree
    hb'Strict hc'Strict
  have hTruncDegree :
      (truncLE (x + y) ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧))).degree =
        (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree := by
    rw [hExpansion]
    exact (degree_add_eq_left_of_lt (hHeadDegree.symm ▸ hRemainderDegree)).trans hHeadDegree
  change ((b : K⟦ℝ⟧) * (c : K⟦ℝ⟧)).degree =
    (b : K⟦ℝ⟧).degree + (c : K⟦ℝ⟧).degree
  exact le_antisymm (degree_mul_le _ _) (hTruncDegree ▸ degree_truncLE_le _ _)

end Nonpositive

end HahnSeries
