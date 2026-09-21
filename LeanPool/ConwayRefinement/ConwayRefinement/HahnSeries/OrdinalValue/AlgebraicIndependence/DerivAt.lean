/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.PrincipalComponent
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.TruncationDrop
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus
public import LeanPool.ConwayRefinement.ConwayRefinement.Order.Filter.FunAtZeroMinus.Pointwise
public import LeanPool.ConwayRefinement.ConwayRefinement.SetTheory.Ordinal.FinitePart

import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.OrdinalValueSubmultiplicative

/-!
# The map `∂ : P_{α+1} → Fun_{0⁻}(P_α)`

The paper's `∂ : P_{α+1} → Fun_{0⁻}(P_α)` (eq:derivation). Let `u ∈ J_{ω^(α+2)}`. By the
truncation drop, the translated truncations `u^{|γ}` lie in `J_{ω^(α+1)}` for all `γ < 0`
sufficiently close to `0`, so `γ ↦ u^{|γ} + J_{ω^α}` is a function at `0⁻` with values in `P_α`.
If `u ∈ J_{ω^(α+1)}`, the same lemma with `β = α` makes this function zero. Since translated
truncation is `K`-linear in `u`, this defines the `K`-linear map
`∂(u + J_{ω^(α+1)}) := (γ ↦ u^{|γ} + J_{ω^α})`.

In Lean the component of successor degree is indexed by `α` itself (`0 < α.constantCoeff`) and the
component one degree below it by `α.removeNat 1`, written `α⁻` in these docstrings:
`principalComponentDerivAt K α hα` is
`∂` on `P_{α+1}` in the paper's indexing and `P_α → Fun_{0⁻}(P_{α⁻})` in Lean's. The value
`derivAt α u γ` is `∂(u)(γ)`, set to zero at the `γ` where `u^{|γ} ∉ J_{ω^α}`; the function at
`0⁻` does not depend on those values.
-/

open Filter Topology
open scoped HahnSeries NatOrdinal

universe v

public noncomputable section

namespace Berarducci

open Berarducci HahnSeries

variable {K : Type v} [Field K]

private theorem removeOne_add_one (alpha : NatOrdinal)
    (halpha : 0 < alpha.constantCoeff) :
    alpha.removeNat 1 + 1 = alpha :=
  by simpa using NatOrdinal.removeNat_add_natCast halpha

/-- `∂(u)(γ)`, the class of the translated truncation `u^{|γ}` in `P_α` (paper eq:derivation);
in Lean's indexing it lies in `P_{α⁻}`, the component indexed by the predecessor of the successor
`α`. At the `γ` where
`u^{|γ} ∉ J_{ω^α}` the value is set to zero; the function at `0⁻` is independent of those
values. -/
def derivAt (alpha : NatOrdinal)
    (b : Series K) (gamma : ℝ) :
    PrincipalComponent K (alpha.removeNat 1) :=
  if h : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) <
      ω^ (alpha.removeNat 1 + 1) then
    principalComponentMk (alpha.removeNat 1)
      (translatedTruncation (b : K⟦ℝ⟧) gamma) h
  else
    0

/-- On its domain, `derivAt` is the class of the translated truncation. -/
theorem derivAt_eq (alpha : NatOrdinal)
    (b : Series K) (gamma : ℝ)
    (h : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) <
      ω^ (alpha.removeNat 1 + 1)) :
    derivAt alpha b gamma =
      principalComponentMk (alpha.removeNat 1)
        (translatedTruncation (b : K⟦ℝ⟧) gamma) h := by
  simp only [derivAt, dif_pos h]

/-- A series in `J_{ω^(α+1)}` has translated truncations in `J_{ω^α} = J_{ω^(α⁻+1)}` near zero
(truncation drop with `β = α`). -/
theorem eventually_derivAt_bound (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (b : Series K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    ∀ᶠ gamma in 𝓝[<] (0 : ℝ),
      ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) <
        ω^ (alpha.removeNat 1 + 1) := by
  have h := eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
      alpha b hb
  simpa only [removeOne_add_one alpha halpha] using h

/-- For all `γ < 0` sufficiently close to `0`, `∂(u)(γ)` is the class of the translated
truncation `u^{|γ}` in `P_{α⁻}`, the component indexed by the predecessor of `α`. -/
theorem eventually_derivAt_eq_principalComponentMk
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (b : Series K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    ∀ᶠ gamma in 𝓝[<] (0 : ℝ),
      ∃ hgamma : ordinalValue (translatedTruncation (b : K⟦ℝ⟧) gamma) <
          ω^ (alpha.removeNat 1 + 1),
        derivAt alpha b gamma =
          principalComponentMk (alpha.removeNat 1)
            (translatedTruncation (b : K⟦ℝ⟧) gamma) hgamma := by
  filter_upwards [eventually_derivAt_bound alpha halpha b hb] with
    gamma hgamma
  exact ⟨hgamma, derivAt_eq alpha b gamma hgamma⟩

/-- The quotient projection to `P_α` preserves addition. -/
theorem principalComponentMk_add (alpha : NatOrdinal)
    (b c : Series K)
    (hb : ordinalValue b < ω^ (alpha + 1))
    (hc : ordinalValue c < ω^ (alpha + 1))
    (hbc : ordinalValue (b + c) < ω^ (alpha + 1)) :
    principalComponentMk alpha (b + c) hbc =
      principalComponentMk alpha b hb +
        principalComponentMk alpha c hc := by
  let w := ordinalValueDegreeValuation K
  rw [principalComponentMk_eq_componentMk, principalComponentMk_eq_componentMk,
    principalComponentMk_eq_componentMk]
  change w.componentMk alpha ⟨b + c, _⟩ =
    w.componentMk alpha ⟨b, _⟩ + w.componentMk alpha ⟨c, _⟩
  rw [← map_add]
  apply congrArg (w.componentMk alpha)
  rfl

private theorem eventually_derivAt_add
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (b c : Series K)
    (hb : ordinalValue b < ω^ (alpha + 1))
    (hc : ordinalValue c < ω^ (alpha + 1)) :
    ∀ᶠ gamma in 𝓝[<] (0 : ℝ),
      derivAt alpha (b + c) gamma =
        derivAt alpha b gamma +
          derivAt alpha c gamma := by
  have hbc : ordinalValue (b + c) < ω^ (alpha + 1) :=
    (ordinalValue_add_le_max b c).trans_lt (max_lt hb hc)
  filter_upwards [eventually_derivAt_bound alpha halpha b hb,
    eventually_derivAt_bound alpha halpha c hc,
    eventually_derivAt_bound alpha halpha (b + c) hbc] with
      gamma hbg hcg hbcg
  rw [derivAt_eq alpha b gamma hbg,
    derivAt_eq alpha c gamma hcg,
    derivAt_eq alpha (b + c) gamma hbcg]
  have hseries : translatedTruncation ((b + c : Series K) : K⟦ℝ⟧) gamma =
      translatedTruncation (b : K⟦ℝ⟧) gamma + translatedTruncation (c : K⟦ℝ⟧) gamma :=
    translatedTruncation_add (b : K⟦ℝ⟧) (c : K⟦ℝ⟧) gamma
  have hsum : ordinalValue
      (translatedTruncation (b : K⟦ℝ⟧) gamma + translatedTruncation (c : K⟦ℝ⟧) gamma) <
      ω^ (alpha.removeNat 1 + 1) := by
    rwa [← hseries]
  convert principalComponentMk_add (alpha.removeNat 1)
    (translatedTruncation (b : K⟦ℝ⟧) gamma)
    (translatedTruncation (c : K⟦ℝ⟧) gamma) hbg hcg hsum using 1
  simp only [hseries]

variable (K) in
/-- `u ↦ ∂(u)` as an additive map on the ideal `J_{ω^(α+1)}`, valued in `Fun_{0⁻}(P_{α⁻})`. -/
private def filtrationDerivAt (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    (ordinalValueDegreeValuation K).filtrationLE alpha →+
      FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)) where
  toFun b := (derivAt (K := K) alpha b :
    FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)))
  map_zero' := (FunAtZeroMinus.coe_eq_zero_iff _).mpr <|
    Filter.Eventually.of_forall fun gamma ↦ by
      have hzero : ordinalValue (translatedTruncation (0 : K⟦ℝ⟧) gamma) <
          ω^ (alpha.removeNat 1 + 1) := by
        rw [translatedTruncation_zero_input, ordinalValue_zero]
        exact NatOrdinal.wpow_pos _
      rw [ZeroMemClass.coe_zero, derivAt_eq alpha 0 gamma hzero]
      exact (principalComponentMk_eq_zero_iff _ _ hzero).mpr (by
        rw [translatedTruncation_zero_input, ordinalValue_zero]
        exact NatOrdinal.wpow_pos _)
  map_add' := by
    intro b c
    change (derivAt (K := K) alpha (b + c) :
      FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1))) =
        (derivAt (K := K) alpha b :
          FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1))) +
        (derivAt (K := K) alpha c :
          FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)))
    rw [← Filter.Germ.coe_add, Filter.Germ.coe_eq]
    exact eventually_derivAt_add alpha halpha (b : Series K) (c : Series K)
      ((mem_ordinalValueDegreeValuation_filtrationLE_iff (b : Series K) alpha).mp b.2)
      ((mem_ordinalValueDegreeValuation_filtrationLE_iff (c : Series K) alpha).mp c.2)

variable (K) in
/-- A series `u ∈ J_{ω^α}` has `∂(u) = 0` (truncation drop with `β = α⁻`). -/
private theorem lowerFiltration_le_filtrationDerivAt_ker
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    (ordinalValueDegreeValuation K).lowerFiltration alpha ≤
      (filtrationDerivAt K alpha halpha).ker := by
  let w := ordinalValueDegreeValuation K
  intro b hb
  refine (FunAtZeroMinus.coe_eq_zero_iff (derivAt (K := K) alpha b)).mpr ?_
  have hbValue : ordinalValue (b : Series K) < ω^ (alpha.removeNat 1 + 1) := by
    rw [removeOne_add_one alpha halpha]
    have hvalue := (w.mem_lowerFiltration_iff alpha b).mp hb
    rw [ordinalValueDegreeValuation_apply] at hvalue
    exact (ordinalValueDegree_lt_coe_iff _ alpha).mp hvalue
  have hdrop := eventually_ordinalValue_translatedTruncation_lt_wpow_of_ordinalValue_lt_wpow_add_one
    (alpha.removeNat 1) (b : Series K) hbValue
  filter_upwards [hdrop] with gamma hgamma
  have hupper : ordinalValue (translatedTruncation ((b : Series K) : K⟦ℝ⟧) gamma) <
      ω^ (alpha.removeNat 1 + 1) :=
    hgamma.trans (NatOrdinal.wpow_lt_wpow.mpr (lt_add_one _))
  rw [derivAt_eq alpha (b : Series K) gamma hupper]
  exact (principalComponentMk_eq_zero_iff _ _ hupper).mpr hgamma

variable (K) in
private def principalComponentDerivAtAdd
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    PrincipalComponent K alpha →+ FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)) :=
  QuotientAddGroup.lift
    ((ordinalValueDegreeValuation K).lowerFiltration alpha)
    (filtrationDerivAt K alpha halpha)
    (lowerFiltration_le_filtrationDerivAt_ker K alpha halpha)

private theorem principalComponentDerivAtAdd_principalComponentMk
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (b : Series K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    principalComponentDerivAtAdd K alpha halpha (principalComponentMk alpha b hb) =
      (derivAt (K := K) alpha b :
        FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1))) := by
  let w := ordinalValueDegreeValuation K
  rw [principalComponentMk_eq_componentMk, ← w.coe_component_eq_componentMk]
  rfl

private theorem eventually_derivAt_smul
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (k : K) (b : Series K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    ∀ᶠ gamma in 𝓝[<] (0 : ℝ),
      derivAt alpha
          ((HahnSeries.Nonpositive.C : K →+* Series K) k * b) gamma =
        k • derivAt alpha b gamma := by
  let kb := (HahnSeries.Nonpositive.C : K →+* Series K) k * b
  have hkb : ordinalValue kb < ω^ (alpha + 1) := by
    rcases eq_or_ne k 0 with rfl | hk
    · simp [kb]
    · calc
        ordinalValue kb ≤ ordinalValue ((HahnSeries.Nonpositive.C : K →+* Series K) k) *
            ordinalValue b := ordinalValue_mul_le_naturalMul _ _
        _ = ordinalValue b := by rw [ordinalValue_C_of_ne hk, one_mul]
        _ < ω^ (alpha + 1) := hb
  filter_upwards [eventually_derivAt_bound alpha halpha b hb,
    eventually_derivAt_bound alpha halpha kb hkb] with gamma hbg hkbg
  rw [derivAt_eq alpha b gamma hbg,
    derivAt_eq alpha kb gamma hkbg]
  have hseries : translatedTruncation (kb : K⟦ℝ⟧) gamma =
      (HahnSeries.Nonpositive.C : K →+* Series K) k * translatedTruncation (b : K⟦ℝ⟧) gamma := by
    rw [show (kb : K⟦ℝ⟧) = HahnSeries.C k * (b : K⟦ℝ⟧) by
      change ((((HahnSeries.Nonpositive.C : K →+* Series K) k) * b : Series K) : K⟦ℝ⟧) = _
      rw [Subring.coe_mul, HahnSeries.Nonpositive.coe_C]]
    exact translatedTruncation_C_mul k (b : K⟦ℝ⟧) gamma
  have hproduct : ordinalValue
      ((HahnSeries.Nonpositive.C : K →+* Series K) k * translatedTruncation (b : K⟦ℝ⟧) gamma) <
      ω^ (alpha.removeNat 1 + 1) := by
    rwa [← hseries]
  convert (smul_principalComponentMk (alpha.removeNat 1) k
    (translatedTruncation (b : K⟦ℝ⟧) gamma) hbg).symm using 1
  simp only [hseries]

private theorem principalComponentDerivAtAdd_map_smul
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (k : K) (x : PrincipalComponent K alpha) :
    principalComponentDerivAtAdd K alpha halpha (k • x) =
      k • principalComponentDerivAtAdd K alpha halpha x := by
  obtain ⟨b, hb, rfl⟩ := exists_principalComponentMk alpha x
  rw [smul_principalComponentMk alpha k b hb,
    principalComponentDerivAtAdd_principalComponentMk,
    principalComponentDerivAtAdd_principalComponentMk]
  change (derivAt alpha
      ((HahnSeries.Nonpositive.C : K →+* Series K) k * b) :
      FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1))) =
    k • (derivAt (K := K) alpha b :
      FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)))
  rw [← Filter.Germ.coe_smul, Filter.Germ.coe_eq]
  exact eventually_derivAt_smul alpha halpha k b hb

variable (K) in
/-- `∂` on `P_{α+1}` (paper eq:derivation): in Lean's indexing, the `K`-linear map
`P_α → Fun_{0⁻}(P_{α⁻})` for a successor `α`, where `α⁻ = α.removeNat 1` is the ordinal one below
`α`. -/
def principalComponentDerivAt (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff) :
    PrincipalComponent K alpha →ₗ[K] FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1)) :=
  { principalComponentDerivAtAdd K alpha halpha with
    map_smul' := principalComponentDerivAtAdd_map_smul alpha halpha }

/-- On any representative `u ∈ J_{ω^(α+1)}`, `∂(u + J_{ω^α})` is the function at `0⁻`
`γ ↦ ∂(u)(γ)`, the class of the translated truncation `u^{|γ}` in `P_{α⁻}`. -/
theorem principalComponentDerivAt_principalComponentMk
    (alpha : NatOrdinal) (halpha : 0 < alpha.constantCoeff)
    (b : Series K) (hb : ordinalValue b < ω^ (alpha + 1)) :
    principalComponentDerivAt K alpha halpha (principalComponentMk alpha b hb) =
      (derivAt (K := K) alpha b :
        FunAtZeroMinus (PrincipalComponent K (alpha.removeNat 1))) :=
  principalComponentDerivAtAdd_principalComponentMk alpha halpha b hb

end Berarducci
