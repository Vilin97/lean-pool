/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.DomainEmbedding
public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.SupportSupremum
public import Mathlib.Algebra.Order.Monoid.Submonoid

/-!
# Real support supremum for subgroup-exponent Hahn series

For an additive subgroup `H ⊆ ℝ`, LM24, Section 6.5 uses the supremum in `ℝ` of the
support of a series in `K((H^{≤ 0}))`. We first embed the exponent domain into `ℝ`, and then
apply the existing real Hahn-series support supremum. Thus the value is `⊥` exactly at zero and
otherwise is characterized intrinsically as the least upper bound in `ℝ` of the coerced
support.
-/

open scoped HahnSeries

universe v

public noncomputable section

namespace HahnSeries.Nonpositive

variable (H : AddSubgroup ℝ) {K : Type v} [Field K]

/-- Regard a nonpositive Hahn series over `H ⊆ ℝ` as a real-exponent Hahn series. -/
def mapDomainToReal : Nonpositive H K →+* Nonpositive ℝ K :=
  mapDomain H.subtype Subtype.val_injective fun _ _ ↦ Iff.rfl

/-- The underlying series of `mapDomainToReal` is Mathlib's exponent-domain embedding. -/
@[simp]
theorem coe_mapDomainToReal (b : Nonpositive H K) :
    (mapDomainToReal H b : K⟦ℝ⟧) = HahnSeries.embDomain
      (⟨⟨H.subtype, Subtype.val_injective⟩, by
        intro a b
        exact Subtype.coe_le_coe⟩ : H ↪o ℝ)
        (b : K⟦H⟧) :=
  coe_mapDomain H.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) b

/-- The real-domain embedding maps support by the subgroup inclusion. -/
theorem support_mapDomainToReal (b : Nonpositive H K) :
    (mapDomainToReal H b : K⟦ℝ⟧).support =
      ((fun h : H ↦ (h : ℝ)) '' (b : K⟦H⟧).support) :=
  support_mapDomain H.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) b

/-- The real-domain embedding is injective. -/
theorem mapDomainToReal_injective :
    Function.Injective (mapDomainToReal (K := K) H) :=
  mapDomain_injective H.subtype Subtype.val_injective fun _ _ ↦ Iff.rfl

/-- The real-domain embedding preserves the constant coefficient. -/
theorem constantCoeff_mapDomainToReal (b : Nonpositive H K) :
    constantCoeff (mapDomainToReal H b) = constantCoeff b := by
  have hmap : mapDomainToReal H b =
      mapDomain H.subtype Subtype.val_injective (fun _ _ ↦ Iff.rfl) b := by
    apply Subtype.ext
    rw [coe_mapDomainToReal, coe_mapDomain]
  rw [hmap]
  exact constantCoeff_mapDomain H.subtype Subtype.val_injective
    (fun _ _ ↦ Iff.rfl) b

/-- The supremum in `ℝ` of the support of a nonpositive series with exponents in `H`. -/
def realSupportSup (b : Nonpositive H K) : WithBot ℝ :=
  supportSup (mapDomainToReal H b)

/-- The real support supremum of zero is `⊥`. -/
@[simp]
theorem realSupportSup_zero :
    realSupportSup H (0 : Nonpositive H K) = ⊥ := by
  rw [realSupportSup, map_zero, supportSup_zero]

/-- The real support supremum is `⊥` exactly at zero. -/
@[simp]
theorem realSupportSup_eq_bot {b : Nonpositive H K} :
    realSupportSup H b = ⊥ ↔ b = 0 := by
  rw [realSupportSup, supportSup_eq_bot]
  constructor
  · intro hb
    exact mapDomainToReal_injective H (hb.trans (map_zero _).symm)
  · rintro rfl
    exact map_zero _

/-- A finite real support supremum is precisely a least upper bound of the coerced support. -/
theorem realSupportSup_eq_coe_iff {b : Nonpositive H K} {a : ℝ} :
    realSupportSup H b = (a : WithBot ℝ) ↔
      b ≠ 0 ∧ IsLUB ((fun h : H ↦ (h : ℝ)) '' (b : K⟦H⟧).support) a := by
  rw [realSupportSup, supportSup_eq_coe_iff, support_mapDomainToReal]
  constructor
  · rintro ⟨hb, hlub⟩
    exact ⟨fun hzero ↦ hb (hzero ▸ map_zero _), hlub⟩
  · rintro ⟨hb, hlub⟩
    exact ⟨fun hzero ↦
      hb (mapDomainToReal_injective H (hzero.trans (map_zero _).symm)), hlub⟩

/-- The real support supremum of a nonzero monomial is its real exponent. -/
theorem realSupportSup_single {g : H} {k : K} (hk : k ≠ 0) (hg : g ≤ 0) :
    realSupportSup H (single g k hg) = (g : ℝ) := by
  rw [realSupportSup, mapDomainToReal, mapDomain_single]
  exact supportSup_single hk (by exact_mod_cast hg)

/-- The multiplicative identity has real support supremum zero. -/
@[simp]
theorem realSupportSup_one :
    realSupportSup H (1 : Nonpositive H K) = 0 := by
  rw [realSupportSup, map_one]
  rw [show (1 : Nonpositive ℝ K) = single 0 1 le_rfl by
    apply Subtype.ext
    rw [coe_single]
    rfl]
  exact supportSup_single one_ne_zero le_rfl

end HahnSeries.Nonpositive
