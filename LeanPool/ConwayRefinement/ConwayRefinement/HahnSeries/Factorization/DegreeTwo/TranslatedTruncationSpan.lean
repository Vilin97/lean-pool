/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrdinalValue.Truncation
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Translated-truncation spans modulo `J + K` in Pommersheim--Shahriari

Pommersheim--Shahriari [PS06] study the vector space
`K((ℝ⁽≤0⁾)) / (J + K)`. This differs from Berarducci's germ ring, whose denominator is only `J`:
the extra quotient by constant series is essential to their degree-two irreducibility criterion.

The submodule `nearConstantSubmodule` is proved to have exactly the carrier of Berarducci's
additive subgroup `nearConstantSubgroup`. Thus the two developments use the same `J + K`, while
this module exposes the scalar quotient needed for linear spans and dimensions.

For a series `a`, `translatedTruncationSpan a` is the space denoted `V(a)` in [PS06]: the
span, modulo `J + K`, of its translated truncations at negative exponents.

## References

* J. Pommersheim, S. Shahriari, *Unique factorization in generalized power series rings*,
Proc. Amer. Math. Soc. 134 (2006), 1277–1287, cited as [PS06].
-/

universe v

public noncomputable section

namespace PommersheimShahriari

open HahnSeries

variable {K : Type v} [Field K]

/-- Scalar multiplication on nonpositive Hahn series through the constant-series embedding. -/
instance seriesAlgebra : Algebra K (Berarducci.Series K) :=
  (HahnSeries.Nonpositive.C : K →+* Berarducci.Series K).toAlgebra

/-- The constant-series embedding as a linear map. -/
def constantLinearMap : K →ₗ[K] Berarducci.Series K where
  toFun := HahnSeries.Nonpositive.C
  map_add' x y :=
    (HahnSeries.Nonpositive.C : K →+* Berarducci.Series K).map_add x y
  map_smul' r x := by
    change HahnSeries.Nonpositive.C (r * x) =
      HahnSeries.Nonpositive.C r * HahnSeries.Nonpositive.C x
    exact (HahnSeries.Nonpositive.C : K →+* Berarducci.Series K).map_mul r x

/-- The scalar submodule `J + K` of negative-monomial-ideal elements plus constants. -/
def nearConstantSubmodule (K : Type v) [Field K] :
    Submodule K (Berarducci.Series K) :=
  ((HahnSeries.Nonpositive.negativeMonomialIdeal K :
      Submodule (Berarducci.Series K) (Berarducci.Series K)).restrictScalars K) ⊔
    LinearMap.range (constantLinearMap (K := K))

/-- The scalar submodule `J + K` has exactly the carrier of Berarducci's additive subgroup with
the same name. -/
theorem mem_nearConstantSubmodule_iff {b : Berarducci.Series K} :
    b ∈ nearConstantSubmodule K ↔ b ∈ Berarducci.nearConstantSubgroup K := by
  rw [nearConstantSubmodule, Submodule.mem_sup]
  constructor
  · rintro ⟨j, hj, c, hc, rfl⟩
    rw [LinearMap.mem_range] at hc
    obtain ⟨k, rfl⟩ := hc
    exact Berarducci.mem_nearConstantSubgroup_iff.mpr ⟨j, hj, k, rfl⟩
  · intro hb
    obtain ⟨j, hj, k, rfl⟩ := Berarducci.mem_nearConstantSubgroup_iff.mp hb
    exact ⟨j, hj, HahnSeries.Nonpositive.C k, ⟨k, rfl⟩, rfl⟩

/-- The [PS06] vector space `K((ℝ⁽≤0⁾)) / (J + K)`. -/
abbrev SeriesQuotientByJAddConstants (K : Type v) [Field K] :=
  Berarducci.Series K ⧸ nearConstantSubmodule K

/-- The quotient map from nonpositive Hahn series to the quotient by `J + K`. -/
def toSeriesQuotientByJAddConstants :
    Berarducci.Series K →ₗ[K] SeriesQuotientByJAddConstants K :=
  Submodule.mkQ (nearConstantSubmodule K)

/-- Two series have the same class modulo `J + K` exactly when their difference lies in
Berarducci's subgroup `J + K`. -/
theorem toSeriesQuotientByJAddConstants_eq_iff {b c : Berarducci.Series K} :
    toSeriesQuotientByJAddConstants b = toSeriesQuotientByJAddConstants c ↔
      b - c ∈ Berarducci.nearConstantSubgroup K := by
  rw [toSeriesQuotientByJAddConstants, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, mem_nearConstantSubmodule_iff]

/-- A series has zero image modulo constants exactly when it lies in `J + K`. -/
theorem toSeriesQuotientByJAddConstants_eq_zero_iff {b : Berarducci.Series K} :
    toSeriesQuotientByJAddConstants b = 0 ↔ b ∈ Berarducci.nearConstantSubgroup K := by
  rw [← map_zero toSeriesQuotientByJAddConstants, toSeriesQuotientByJAddConstants_eq_iff, sub_zero]

/-- The class modulo `J + K` of the translated truncation at `x`. -/
def translatedTruncationClass (b : K⟦ℝ⟧) (x : ℝ) : SeriesQuotientByJAddConstants K :=
  toSeriesQuotientByJAddConstants (Berarducci.translatedTruncation b x)

/-- Evaluate a translated-truncation class modulo `J + K`. -/
theorem translatedTruncationClass_apply (b : K⟦ℝ⟧) (x : ℝ) :
    translatedTruncationClass b x =
      toSeriesQuotientByJAddConstants (Berarducci.translatedTruncation b x) := (rfl)

/-- [PS06]'s space `V(a)`, spanned modulo `J + K` by translated truncations at negative
exponents. -/
def translatedTruncationSpan (a : Berarducci.Series K) :
    Submodule K (SeriesQuotientByJAddConstants K) :=
  Submodule.span K (translatedTruncationClass (a : K⟦ℝ⟧) '' Set.Iio 0)

/-- Every translated-truncation class at a negative exponent belongs to `V(a)`. -/
theorem translatedTruncationClass_mem_translatedTruncationSpan (a : Berarducci.Series K)
    {x : ℝ} (hx : x < 0) :
    translatedTruncationClass (a : K⟦ℝ⟧) x ∈ translatedTruncationSpan a :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- A subspace contains `V(a)` exactly when it contains every negative translated-truncation
class used to generate `V(a)`. -/
theorem translatedTruncationSpan_le_iff {a : Berarducci.Series K}
    {p : Submodule K (SeriesQuotientByJAddConstants K)} :
    translatedTruncationSpan a ≤ p ↔
      ∀ x : ℝ, x < 0 → translatedTruncationClass (a : K⟦ℝ⟧) x ∈ p := by
  rw [translatedTruncationSpan, Submodule.span_le]
  constructor
  · intro h x hx
    exact h ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact h x hx

end PommersheimShahriari
