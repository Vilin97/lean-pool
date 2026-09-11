/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
module

public import LeanPool.RiemannRochFunctionFields.CoordinateFree.WeilDifferential
public import LeanPool.RiemannRochFunctionFields.RiemannRochTheorem.Corollaries

/-!
# Coordinate-free Riemann–Roch

This file exposes the Riemann–Roch stack over divisors indexed by intrinsic valuation-subring
places.  The kernel-checked chart proofs are transported across `chartToPlace`.

## Main definitions and results

* `FunctionField.RRspace`, `FunctionField.ell`, and `FunctionField.genus`.
* `FunctionField.AdeleSpace` and `FunctionField.adeleFilt`.
* `FunctionField.IsCanonical` and `FunctionField.duality`.
* `FunctionField.riemann_roch` and coordinate-free corollaries C1–C6.
-/

@[expose] public section

open scoped nonZeroDivisors Polynomial RatFunc WithZero

noncomputable section

namespace FunctionField

open Chart

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- A function belongs to the intrinsic Riemann–Roch space of `D` when its normalized valuation
at every place is bounded by the coefficient of `D` there. -/
def memRRspace (D : Divisor k K) (f : K) : Prop :=
  ∀ v, v.valuation f ≤ WithZero.exp (D v)

namespace memRRspace

variable {k K} {D : Divisor k K}

theorem zero_mem (D : Divisor k K) : memRRspace k K D 0 := fun v => by simp

theorem add_mem {f g : K} (hf : memRRspace k K D f) (hg : memRRspace k K D g) :
    memRRspace k K D (f + g) := fun v =>
  (v.valuation.map_add f g).trans (max_le (hf v) (hg v))

theorem smul_mem (c : k) {f : K} (hf : memRRspace k K D f) :
    memRRspace k K D (c • f) := fun v => by
  by_cases hc : c = 0
  · simp [hc]
  rw [Algebra.smul_def, map_mul, Valuation.IsTrivialOn.eq_one c hc, one_mul]
  exact hf v

end memRRspace

/-- The Riemann–Roch space of an intrinsic divisor. -/
def RRspace (D : Divisor k K) : Submodule k K :=
  { carrier := {f | memRRspace k K D f}
    zero_mem' := memRRspace.zero_mem D
    add_mem' := memRRspace.add_mem
    smul_mem' := memRRspace.smul_mem }

/-- The Riemann–Roch dimension of an intrinsic divisor. -/
noncomputable def ell (D : Divisor k K) : ℕ :=
  Module.finrank k (RRspace k K D)

/-- The defect of an intrinsic divisor. -/
noncomputable def defect (D : Divisor k K) : ℤ :=
  D.deg + 1 - ell k K D

/-- The intrinsic genus is the supremum of the defects of all intrinsic divisors.  The
Riemann–Roch argument below proves that this supremum is attained and agrees with every chart
calculation. -/
noncomputable def genus : ℕ :=
  (sSup {d : ℤ | ∃ D : Divisor k K, defect k K D = d}).toNat

variable [Algebra k[X] K] [Algebra k⟮X⟯ K]
  [IsScalarTower k k[X] K] [IsScalarTower k[X] k⟮X⟯ K] [_root_.FunctionField k K]
  [Algebra.IsSeparable k⟮X⟯ K] [IsFullConstantField k K]

omit [IsFullConstantField k K] in
/-- The intrinsic membership condition agrees with the coordinate construction. -/
theorem memRRspace_equivChart (D : Divisor k K) (f : K) :
    memRRspace k K D f ↔
      Chart.memRRspace k K ((divisorEquivChart k K).symm D) f := by
  constructor
  · intro hf w
    have hv := hf (chartToPlace k K w)
    rw [placeValuation_eq] at hv
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hv
  · intro hf v
    let w := (chartToPlace k K).symm v
    have hw := hf w
    rw [← placeValuation_eq] at hw
    simpa [w, divisorEquivChart, Finsupp.domCongr_apply] using hw

omit [IsFullConstantField k K] in
/-- The intrinsic Riemann–Roch space is the chart space after reindexing divisors. -/
theorem RRspace_eq_chart (D : Divisor k K) :
    RRspace k K D = Chart.RRspace k K ((divisorEquivChart k K).symm D) := by
  ext f
  exact memRRspace_equivChart k K D f

omit [IsFullConstantField k K] in
/-- Riemann–Roch dimension is preserved by the chart equivalence. -/
theorem ell_eq_chart (D : Divisor k K) :
    ell k K D = Chart.ell k K ((divisorEquivChart k K).symm D) := by
  rw [ell, Chart.ell, RRspace_eq_chart k K D]

/-- The index of specialty of an intrinsic divisor. -/
noncomputable def indexOfSpecialty (D : Divisor k K) : ℕ :=
  (ell k K D - (D.deg + 1 - (genus k K : ℤ))).toNat

/-- The dimension of the intrinsic adele quotient by `A(D)` plus the diagonal. -/
noncomputable def finrankAdeleQuotient (D : Divisor k K) : ℕ :=
  Module.finrank k <|
    AdeleSpace k K ⧸ (adeleFilt k K D + diagonalSubmodule k K)

omit [IsFullConstantField k K] in
/-- Pulling an intrinsic divisor back to the chart preserves degree. -/
@[simp]
theorem Divisor.chart_deg (D : Divisor k K) :
    Chart.deg k K ((divisorEquivChart k K).symm D) = D.deg := by
  have h := Divisor.deg_equivChart k K ((divisorEquivChart k K).symm D)
  simpa using h.symm

omit [IsFullConstantField k K] in
/-- Intrinsic defect is preserved by the chart equivalence. -/
theorem defect_eq_chart (D : Divisor k K) :
    defect k K D = Chart.defect k K ((divisorEquivChart k K).symm D) := by
  rw [defect, Chart.defect, ell_eq_chart, Divisor.chart_deg]

/-- The intrinsic supremum definition of genus agrees with the chart construction. -/
theorem genus_eq_genusChart : genus k K = Chart.genus k K := by
  let S : Set ℤ := {d | ∃ D : Divisor k K, defect k K D = d}
  have hS : S.Nonempty := ⟨defect k K 0, ⟨0, rfl⟩⟩
  have hub : ∀ d ∈ S, d ≤ (Chart.genus k K : ℤ) := by
    rintro d ⟨D, rfl⟩
    rw [defect_eq_chart]
    exact Chart.defect_le k K _
  obtain ⟨E, hE⟩ := Chart.exists_defect_eq (k := k) (K := K)
  have happ : ∀ z < (Chart.genus k K : ℤ), ∃ d ∈ S, z < d := by
    intro z hz
    refine ⟨defect k K (divisorEquivChart k K E), ⟨_, rfl⟩, ?_⟩
    rw [defect_eq_chart]
    simpa [hE] using hz
  have hsup : sSup S = (Chart.genus k K : ℤ) :=
    csSup_eq_of_forall_le_of_forall_lt_exists_gt hS hub happ
  rw [genus]
  change (sSup S).toNat = _
  rw [hsup]
  simp

/-- The numerical characterization of a canonical coordinate divisor. -/
theorem chart_isCanonical_iff_degree_ell (E : DivisorA k K) :
    Chart.IsCanonical k K E ↔
      Chart.deg k K E = 2 * (Chart.genus k K : ℤ) - 2 ∧
        Chart.ell k K E = Chart.genus k K := by
  constructor
  · intro hE
    exact ⟨Chart.deg_canonical k K hE, Chart.ell_canonical k K hE⟩
  · rintro ⟨hdegE, hellE⟩
    obtain ⟨C, hC⟩ := Chart.exists_isCanonical k K
    have hRR := Chart.riemann_roch k K hC E
    have hpos : 0 < Chart.ell k K (C - E) := by
      rw [hellE, hdegE] at hRR
      omega
    obtain ⟨x, hxeff⟩ :=
      Chart.exists_effective_add_principal_of_ell_pos k K (C - E) hpos
    let P := principalDivisorA k K (Additive.ofMul x)
    have hdegzero : Chart.deg k K ((C - E) + P) = 0 := by
      rw [Chart.deg_add, Chart.deg_sub,
        deg_principalDivisorA_eq_zero, Chart.deg_canonical k K hC, hdegE]
      omega
    have hzero : (C - E) + P = 0 :=
      eq_zero_of_effective_deg_zero k K hxeff hdegzero
    have hCE : C + P = E := by
      calc
        C + P = E + ((C - E) + P) := by abel
        _ = E := by rw [hzero, add_zero]
    rcases hC with ⟨ω, hω, hdiv⟩
    have hxω : Chart.WeilDifferential.IsNonzero ((x : K) • ω) := by
      intro hx
      have hx0 : (x : K) • ω = 0 := by
        apply Chart.WeilDifferential.ext
        exact hx
      have hω0 := (Chart.WeilDifferential.smulWeil_eq_zero_iff
        (k := k) (K := K) (x : K) (Units.ne_zero x) ω).mp hx0
      apply hω
      rw [hω0]
      rfl
    refine ⟨(x : K) • ω, hxω, ?_⟩
    rw [Chart.WeilDifferential.divOmega_smul (k := k) (K := K) x ω hω hxω, hdiv]
    exact hCE

/-- A divisor is canonical exactly when it has degree `2g - 2` and Riemann–Roch dimension `g`. -/
theorem isCanonical_iff_deg_ell (W : Divisor k K) :
    IsCanonical k K W ↔
      W.deg = 2 * (genus k K : ℤ) - 2 ∧ ell k K W = genus k K := by
  rw [isCanonical_iff_chart, chart_isCanonical_iff_degree_ell]
  simp only [Divisor.chart_deg, ell_eq_chart, genus_eq_genusChart]

/-- The intrinsic specialty index agrees with the coordinate construction. -/
theorem indexOfSpecialty_eq_chart (D : Divisor k K) :
    indexOfSpecialty k K D =
      Chart.indexOfSpecialty k K ((divisorEquivChart k K).symm D) := by
  rw [indexOfSpecialty, Chart.indexOfSpecialty, ell_eq_chart, Divisor.chart_deg,
    genus_eq_genusChart]

/-- The intrinsic adele quotient is linearly equivalent to its chart presentation. -/
noncomputable def adeleQuotientEquivChart (D : Divisor k K) :
    (AdeleSpace k K ⧸ (adeleFilt k K D + diagonalSubmodule k K)) ≃ₗ[k]
      (Chart.AdeleSpace k K ⧸
        (Chart.adeleFilt k K ((divisorEquivChart k K).symm D) +
          Chart.diagonalSubmodule k K)) :=
  Submodule.Quotient.equiv _ _ (adeleEquivChart k K)
    (map_adeleFilt_add_diagonal_equivChart k K D)

omit [IsFullConstantField k K] in
/-- The intrinsic and chart adele quotients have the same dimension. -/
theorem finrankAdeleQuotient_eq_chart (D : Divisor k K) :
    finrankAdeleQuotient k K D =
      Chart.finrankAdeleQuotient k K ((divisorEquivChart k K).symm D) :=
  (adeleQuotientEquivChart k K D).finrank_eq

/-- The intrinsic adele quotient dimension is the index of specialty. -/
theorem finrank_adele_quotient (D : Divisor k K) :
    finrankAdeleQuotient k K D = indexOfSpecialty k K D := by
  rw [finrankAdeleQuotient_eq_chart, Chart.finrank_adele_quotient,
    indexOfSpecialty_eq_chart]

/-- The rank change in the intrinsic filtration-and-diagonal sandwich. -/
noncomputable def sandwichRank (D E : Divisor k K) : ℤ :=
  Chart.sandwichRank k K ((divisorEquivChart k K).symm D) ((divisorEquivChart k K).symm E)

omit [IsFullConstantField k K] in
/-- The intrinsic sandwich rank is the change in `deg D - ell(D)`. -/
theorem sandwich {D E : Divisor k K} (h : D ≤ E) :
    sandwichRank k K D E = E.deg - ell k K E - (D.deg - ell k K D) := by
  have hchart : (divisorEquivChart k K).symm D ≤
      (divisorEquivChart k K).symm E := by
    intro w
    have hw := h (chartToPlace k K w)
    simpa [divisorEquivChart, Finsupp.domCongr_apply] using hw
  simp only [sandwichRank]
  rw [Chart.sandwich k K hchart]
  simp only [Divisor.chart_deg, ell_eq_chart]

/-- The dimension of intrinsic `Omega(D)` is the index of specialty of `D`. -/
theorem WeilDifferential.finrank_differentialSpace (D : Divisor k K) :
    Module.finrank k (WeilDifferential.differentialSpace (k := k) (K := K) D) =
      indexOfSpecialty k K D := by
  rw [WeilDifferential.finrank_differentialSpace_eq_chart,
    Chart.WeilDifferential.finrank_differentialSpace, indexOfSpecialty_eq_chart]

/-- Every function field admits an intrinsic canonical divisor. -/
theorem exists_isCanonical : ∃ W : Divisor k K, IsCanonical k K W := by
  obtain ⟨W, hW⟩ := Chart.exists_isCanonical k K
  refine ⟨divisorEquivChart k K W, ?_⟩
  apply (isCanonical_iff_chart k K _).mpr
  simpa using hW

/-- Coordinate-free duality. -/
theorem duality {W : Divisor k K} (hW : IsCanonical k K W) (D : Divisor k K) :
    ell k K (W - D) = indexOfSpecialty k K D := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  rw [ell_eq_chart, indexOfSpecialty_eq_chart]
  simpa using Chart.duality k K hW' ((divisorEquivChart k K).symm D)

/-- Riemann's inequality for intrinsic divisors. -/
theorem riemann_ineq (D : Divisor k K) :
    (ell k K D : ℤ) ≥ D.deg + 1 - (genus k K : ℤ) := by
  rw [ell_eq_chart]
  simpa [genus_eq_genusChart] using
    Chart.riemann_ineq k K ((divisorEquivChart k K).symm D)

/-- The coordinate-free Riemann–Roch theorem. -/
theorem riemann_roch {W : Divisor k K} (hW : IsCanonical k K W) (D : Divisor k K) :
    (ell k K D : ℤ) = D.deg + 1 - (genus k K : ℤ) + ell k K (W - D) := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  rw [ell_eq_chart, ell_eq_chart]
  simpa [genus_eq_genusChart] using
    Chart.riemann_roch k K hW' ((divisorEquivChart k K).symm D)

section Canonical

variable {W : Divisor k K} (hW : IsCanonical k K W)

include hW

/-- **C1**: a canonical divisor has Riemann–Roch dimension equal to the genus. -/
theorem ell_canonical : ell k K W = genus k K := by
  exact (isCanonical_iff_deg_ell k K W).mp hW |>.2

/-- **C2**: a canonical divisor has degree `2g - 2`. -/
theorem deg_canonical : W.deg = 2 * (genus k K : ℤ) - 2 := by
  exact (isCanonical_iff_deg_ell k K W).mp hW |>.1

/-- **C3**: divisors of degree at least `2g - 1` are nonspecial. -/
theorem ell_eq_of_deg_ge (D : Divisor k K)
    (hdeg : D.deg ≥ 2 * (genus k K : ℤ) - 1) :
    (ell k K D : ℤ) = D.deg + 1 - (genus k K : ℤ) := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  have hdeg' : Chart.deg k K ((divisorEquivChart k K).symm D) ≥
      2 * (Chart.genus k K : ℤ) - 1 := by simpa [genus_eq_genusChart] using hdeg
  rw [ell_eq_chart]
  simpa [genus_eq_genusChart] using
    Chart.ell_eq_of_deg_ge k K hW' ((divisorEquivChart k K).symm D) hdeg'

/-- **C4**: the specialty index is `ℓ(W-D)`. -/
theorem indexOfSpecialty_eq_ell (D : Divisor k K) :
    (indexOfSpecialty k K D : ℤ) = ell k K (W - D) := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  rw [indexOfSpecialty_eq_chart, ell_eq_chart]
  simpa using Chart.indexOfSpecialty_eq_ell k K hW'
    ((divisorEquivChart k K).symm D)

end Canonical

/-- The core Clifford inequality for intrinsic divisors: whenever `ℓ(D)` and `ℓ(W − D)` are
both positive for a canonical `W`, `2(ℓ(D) − 1) ≤ deg D`.  No degree bounds are needed. -/
theorem clifford_of_ell_pos {W : Divisor k K} (hW : IsCanonical k K W) (D : Divisor k K)
    (hℓD : 0 < ell k K D) (hℓW : 0 < ell k K (W - D)) :
    2 * ((ell k K D : ℤ) - 1) ≤ D.deg := by
  have hW' := (isCanonical_iff_chart k K W).mp hW
  rw [ell_eq_chart k K D] at hℓD ⊢
  rw [ell_eq_chart k K (W - D)] at hℓW
  simpa using Chart.clifford_of_ell_pos k K hW' ((divisorEquivChart k K).symm D) hℓD hℓW

/-- **C5**: Clifford's inequality for intrinsic divisors in its textbook form.  The degree
bounds `0 ≤ deg D ≤ 2g − 2` are kept for fidelity to the standard statement but are not needed;
see `clifford_of_ell_pos`. -/
theorem clifford {W : Divisor k K} (hW : IsCanonical k K W) (D : Divisor k K)
    (_hdeg₀ : 0 ≤ D.deg) (_hdeg₁ : D.deg ≤ 2 * (genus k K : ℤ) - 2)
    (hℓD : 0 < ell k K D) (hℓW : 0 < ell k K (W - D)) :
    2 * ((ell k K D : ℤ) - 1) ≤ D.deg :=
  clifford_of_ell_pos k K hW D hℓD hℓW

/-- **C6**: there exists an intrinsic nonspecial divisor. -/
theorem exists_nonspecial_divisor :
    ∃ D : Divisor k K, indexOfSpecialty k K D = 0 := by
  obtain ⟨D, hD⟩ := Chart.exists_nonspecial_divisor k K
  refine ⟨divisorEquivChart k K D, ?_⟩
  rw [indexOfSpecialty_eq_chart]
  simpa using hD

end FunctionField
