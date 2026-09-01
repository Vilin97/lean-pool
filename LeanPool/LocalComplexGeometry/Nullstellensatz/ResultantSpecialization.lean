/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/

import LeanPool.LocalComplexGeometry.Geometry.FiniteProjection
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Specializing fixed-degree resultants

This file packages the algebraic specialization argument for resultants of
polynomial families with analytic coefficients.  The fixed Sylvester sizes
are part of every definition, so specialization remains valid even when a
fiber drops degree.
-/

open Filter
open scoped BigOperators Topology


namespace LocalComplexGeometry

noncomputable section

/-! ## Fixed-degree polynomial families -/

/-- Assemble coefficients indexed by `Fin (d + 1)` into a polynomial of
degree at most `d`. -/
def fixedDegreePolynomial {R : Type*} [Semiring R] {d : ℕ}
    (c : Fin (d + 1) → R) : Polynomial R :=
  ∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)

/-- Specialize a fixed-degree polynomial family at a parameter. -/
def fixedDegreePolynomialAt {R X : Type*} [Semiring R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X) : Polynomial R :=
  fixedDegreePolynomial (fun i ↦ c i x)

@[simp]
theorem fixedDegreePolynomial_map
    {R S : Type*} [Semiring R] [Semiring S] {d : ℕ}
    (φ : R →+* S) (c : Fin (d + 1) → R) :
    (fixedDegreePolynomial c).map φ =
      fixedDegreePolynomial (fun i ↦ φ (c i)) := by
  unfold fixedDegreePolynomial
  rw [Polynomial.map_sum]
  simp

@[simp]
theorem fixedDegreePolynomialAt_eval
    {R X : Type*} [CommSemiring R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X) (w : R) :
    (fixedDegreePolynomialAt c x).eval w =
      ∑ i : Fin (d + 1), c i x * w ^ (i : ℕ) := by
  change (Polynomial.evalRingHom w) (fixedDegreePolynomialAt c x) = _
  unfold fixedDegreePolynomialAt fixedDegreePolynomial
  rw [map_sum]
  simp

/-- The displayed polynomial has degree at most its fixed degree bound. -/
theorem fixedDegreePolynomial_natDegree_le
    {R : Type*} [Semiring R] {d : ℕ} (c : Fin (d + 1) → R) :
    (fixedDegreePolynomial c).natDegree ≤ d := by
  unfold fixedDegreePolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (c i) (i : ℕ)).trans
    (Nat.lt_succ_iff.mp i.isLt)

/-- Every coefficient of the assembled polynomial is the corresponding
displayed coefficient inside the fixed range and is zero outside it. -/
@[simp]
theorem fixedDegreePolynomial_coeff
    {R : Type*} [Semiring R] {d k : ℕ} (c : Fin (d + 1) → R) :
    (fixedDegreePolynomial c).coeff k =
      if h : k < d + 1 then c ⟨k, h⟩ else 0 := by
  classical
  unfold fixedDegreePolynomial
  change Polynomial.lcoeff R k
      (∑ i : Fin (d + 1), Polynomial.C (c i) * Polynomial.X ^ (i : ℕ)) = _
  rw [map_sum]
  simp only [Polynomial.lcoeff_apply, Polynomial.coeff_C_mul_X_pow]
  by_cases hk : k < d + 1
  · rw [dite_eq_left hk, Finset.sum_eq_single ⟨k, hk⟩]
    · simp
    · intro i hi hne
      have hki : k ≠ (i : ℕ) := fun h ↦ hne (Fin.ext h.symm)
      simp [hki]
    · simp
  · rw [dite_eq_right hk]
    apply Finset.sum_eq_zero
    intro i hi
    have hki : k ≠ (i : ℕ) := by
      intro h
      apply hk
      simpa [h] using i.isLt
    simp [hki]

/-- The coefficient at the fixed top degree is the displayed top
coefficient. -/
theorem fixedDegreePolynomial_coeff_top
    {R : Type*} [Semiring R] {d : ℕ} (c : Fin (d + 1) → R) :
    (fixedDegreePolynomial c).coeff d = c ⟨d, Nat.lt_succ_self d⟩ := by
  simp

/-- Reassembling all coefficients up to a valid fixed bound recovers the
polynomial. -/
theorem fixedDegreePolynomial_coefficients_eq
    {R : Type*} [Semiring R] {d : ℕ} (p : Polynomial R)
    (hp : p.natDegree ≤ d) :
    fixedDegreePolynomial (fun i : Fin (d + 1) ↦ p.coeff i) = p := by
  unfold fixedDegreePolynomial
  calc
    (∑ i : Fin (d + 1), Polynomial.C (p.coeff (i : ℕ)) *
        Polynomial.X ^ (i : ℕ)) =
        ∑ i ∈ Finset.range (d + 1),
          Polynomial.C (p.coeff i) * Polynomial.X ^ i :=
      Fin.sum_univ_eq_sum_range
        (fun i : ℕ ↦ Polynomial.C (p.coeff i) * Polynomial.X ^ i) (d + 1)
    _ = p := (p.as_sum_range_C_mul_X_pow'
      (Nat.lt_succ_of_le hp)).symm

/-- A nonzero displayed top coefficient forces the exact fixed degree. -/
theorem fixedDegreePolynomial_natDegree_eq
    {R : Type*} [Semiring R] {d : ℕ}
    (c : Fin (d + 1) → R)
    (htop : c ⟨d, Nat.lt_succ_self d⟩ ≠ 0) :
    (fixedDegreePolynomial c).natDegree = d := by
  apply le_antisymm (fixedDegreePolynomial_natDegree_le c)
  exact Polynomial.le_natDegree_of_ne_zero
    (by simpa using htop)

/-- A fixed-degree polynomial whose displayed top coefficient is one is
monic. -/
theorem fixedDegreePolynomial_monic
    {R : Type*} [Semiring R] [Nontrivial R] {d : ℕ}
    (c : Fin (d + 1) → R)
    (htop : c ⟨d, Nat.lt_succ_self d⟩ = 1) :
    (fixedDegreePolynomial c).Monic := by
  rw [Polynomial.Monic.def]
  rw [Polynomial.leadingCoeff, fixedDegreePolynomial_natDegree_eq c]
  · exact fixedDegreePolynomial_coeff_top c |>.trans htop
  · simp [htop]

theorem fixedDegreePolynomialAt_natDegree_le
    {R X : Type*} [Semiring R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X) :
    (fixedDegreePolynomialAt c x).natDegree ≤ d :=
  fixedDegreePolynomial_natDegree_le (fun i ↦ c i x)

theorem fixedDegreePolynomialAt_natDegree_eq
    {R X : Type*} [Semiring R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X)
    (htop : c ⟨d, Nat.lt_succ_self d⟩ x ≠ 0) :
    (fixedDegreePolynomialAt c x).natDegree = d :=
  fixedDegreePolynomial_natDegree_eq (fun i ↦ c i x) htop

theorem fixedDegreePolynomialAt_monic
    {R X : Type*} [Semiring R] [Nontrivial R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X)
    (htop : c ⟨d, Nat.lt_succ_self d⟩ x = 1) :
    (fixedDegreePolynomialAt c x).Monic :=
  fixedDegreePolynomial_monic (fun i ↦ c i x) htop

/-- Specializing the coefficient-function polynomial agrees with assembling
the specialized coefficients. -/
theorem fixedDegreePolynomial_map_eval
    {R X : Type*} [CommSemiring R] {d : ℕ}
    (c : Fin (d + 1) → X → R) (x : X) :
    (fixedDegreePolynomial c).map
        (Pi.evalRingHom (fun _ : X ↦ R) x) =
      fixedDegreePolynomialAt c x := by
  simp [fixedDegreePolynomialAt]

/-! ## Algebraic specialization of resultants -/

/-- The pointwise fixed-size resultant of two coefficient families. -/
def fixedDegreeResultantAt
    {R X : Type*} [CommRing R] {d e : ℕ}
    (a : Fin (d + 1) → X → R) (b : Fin (e + 1) → X → R)
    (x : X) : R :=
  Polynomial.resultant
    (fixedDegreePolynomialAt a x) (fixedDegreePolynomialAt b x) d e

/-- A fixed-size resultant over a function ring specializes pointwise. -/
theorem fixedDegreeResultant_function_apply
    {R X : Type*} [CommRing R] {d e : ℕ}
    (a : Fin (d + 1) → X → R) (b : Fin (e + 1) → X → R)
    (x : X) :
    Polynomial.resultant (fixedDegreePolynomial a)
        (fixedDegreePolynomial b) d e x =
      fixedDegreeResultantAt a b x := by
  change (Pi.evalRingHom (fun _ : X ↦ R) x)
      (Polynomial.resultant (fixedDegreePolynomial a)
        (fixedDegreePolynomial b) d e) = _
  unfold fixedDegreeResultantAt
  rw [← fixedDegreePolynomial_map_eval a x,
    ← fixedDegreePolynomial_map_eval b x]
  exact (Polynomial.resultant_map_map
    (fixedDegreePolynomial a) (fixedDegreePolynomial b) d e
    (Pi.evalRingHom (fun _ : X ↦ R) x)).symm

/-- Two finite analytic coefficient families have an analytic representative
of their fixed-size resultant.  Its equality with the pointwise complex
resultant is a germ equality, hence holds on a neighborhood of the origin. -/
theorem exists_analytic_fixedDegreeResultantAt_origin
    {n d e : ℕ}
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (b : Fin (e + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0)
    (hb : ∀ i, AnalyticAt ℂ (b i) 0) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ 0 ∧
      ∀ᶠ z in 𝓝 0, Δ z = fixedDegreeResultantAt a b z := by
  let A : Fin (d + 1) → HolomorphicGerm n :=
    fun i ↦ HolomorphicGerm.ofFunction (a i) (ha i)
  let B : Fin (e + 1) → HolomorphicGerm n :=
    fun i ↦ HolomorphicGerm.ofFunction (b i) (hb i)
  let ρ : HolomorphicGerm n →+* FunctionGerm n :=
    (holomorphicGermSubring n).subtype
  let γ : (ComplexEuclidean n → ℂ) →+* FunctionGerm n :=
    Filter.Germ.coeRingHom (𝓝 (0 : ComplexEuclidean n))
  let resGerm : HolomorphicGerm n :=
    Polynomial.resultant (fixedDegreePolynomial A)
      (fixedDegreePolynomial B) d e
  obtain ⟨Δ, hΔ, hΔrep⟩ := HolomorphicGerm.exists_rep resGerm
  refine ⟨Δ, hΔ, ?_⟩
  have hAmap : (fixedDegreePolynomial A).map ρ =
      (fixedDegreePolynomial a).map γ := by
    simp [A, ρ, γ]
  have hBmap : (fixedDegreePolynomial B).map ρ =
      (fixedDegreePolynomial b).map γ := by
    simp [B, ρ, γ]
  have hresGerm : (resGerm : FunctionGerm n) =
      γ (Polynomial.resultant (fixedDegreePolynomial a)
        (fixedDegreePolynomial b) d e) := by
    have hHol := Polynomial.resultant_map_map
      (fixedDegreePolynomial A) (fixedDegreePolynomial B) d e ρ
    have hFun := Polynomial.resultant_map_map
      (fixedDegreePolynomial a) (fixedDegreePolynomial b) d e γ
    rw [hAmap, hBmap] at hHol
    exact hHol.symm.trans hFun
  have hpointwise :
      (fixedDegreeResultantAt a b : ComplexEuclidean n → ℂ) =
        Polynomial.resultant (fixedDegreePolynomial a)
          (fixedDegreePolynomial b) d e := by
    funext z
    exact (fixedDegreeResultant_function_apply a b z).symm
  apply Filter.Germ.coe_eq.mp
  have hpointwiseGerm := congrArg
    (fun f : ComplexEuclidean n → ℂ ↦ (f : FunctionGerm n)) hpointwise
  exact hΔrep.trans (hresGerm.trans hpointwiseGerm.symm)

/-- Arbitrary-base-point form of analytic resultant specialization. -/
theorem exists_analytic_fixedDegreeResultantAt
    {n d e : ℕ} {z₀ : ComplexEuclidean n}
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (b : Fin (e + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (hb : ∀ i, AnalyticAt ℂ (b i) z₀) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ z₀ ∧
      ∀ᶠ z in 𝓝 z₀, Δ z = fixedDegreeResultantAt a b z := by
  let a₀ : Fin (d + 1) → ComplexEuclidean n → ℂ :=
    fun i z ↦ a i (z + z₀)
  let b₀ : Fin (e + 1) → ComplexEuclidean n → ℂ :=
    fun i z ↦ b i (z + z₀)
  have ha₀ : ∀ i, AnalyticAt ℂ (a₀ i) 0 := by
    intro i
    exact (ha i).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
  have hb₀ : ∀ i, AnalyticAt ℂ (b₀ i) 0 := by
    intro i
    exact (hb i).comp_of_eq (analyticAt_id.add analyticAt_const) (by simp)
  obtain ⟨δ, hδ, hδeq⟩ :=
    exists_analytic_fixedDegreeResultantAt_origin a₀ b₀ ha₀ hb₀
  let Δ : ComplexEuclidean n → ℂ := fun z ↦ δ (z - z₀)
  have hsub : AnalyticAt ℂ (fun z : ComplexEuclidean n ↦ z - z₀) z₀ :=
    analyticAt_id.sub analyticAt_const
  have hΔ : AnalyticAt ℂ Δ z₀ := by
    exact hδ.comp_of_eq hsub (by simp)
  refine ⟨Δ, hΔ, ?_⟩
  have hsubTendsto : Tendsto (fun z : ComplexEuclidean n ↦ z - z₀)
      (𝓝 z₀) (𝓝 0) := by
    have h := hsub.continuousAt
    change Tendsto (fun z : ComplexEuclidean n ↦ z - z₀) (𝓝 z₀)
      (𝓝 (z₀ - z₀)) at h
    simpa only [sub_self] using h
  have hδeq' := hsubTendsto hδeq
  filter_upwards [hδeq'] with z hz
  change δ (z - z₀) = fixedDegreeResultantAt a b z
  change δ (z - z₀) = fixedDegreeResultantAt a₀ b₀ (z - z₀) at hz
  have haeq : fixedDegreePolynomialAt a₀ (z - z₀) =
      fixedDegreePolynomialAt a z := by
    ext k
    simp only [fixedDegreePolynomialAt, fixedDegreePolynomial_coeff]
    split_ifs <;> simp [a₀]
  have hbeq : fixedDegreePolynomialAt b₀ (z - z₀) =
      fixedDegreePolynomialAt b z := by
    ext k
    simp only [fixedDegreePolynomialAt, fixedDegreePolynomial_coeff]
    split_ifs <;> simp [b₀]
  change δ (z - z₀) = Polynomial.resultant
      (fixedDegreePolynomialAt a₀ (z - z₀))
      (fixedDegreePolynomialAt b₀ (z - z₀)) d e at hz
  rw [haeq, hbeq] at hz
  exact hz

/-! ## Nonvanishing derivative resultants and simple fibers -/

/-- A complex polynomial of known positive degree is separable when its
fixed-size resultant with its derivative is nonzero.  No monicity assumption
is needed. -/
theorem separable_of_resultant_derivative_ne_zero
    {d : ℕ} (_hd : 0 < d) {p : Polynomial ℂ}
    (hdegree : p.natDegree = d)
    (hres : Polynomial.resultant p p.derivative d (d - 1) ≠ 0) :
    p.Separable := by
  have hp : p ≠ 0 := by
    intro hpzero
    rw [hpzero, Polynomial.natDegree_zero] at hdegree
    omega
  have hres' : Polynomial.resultant p p.derivative ≠ 0 := by
    simpa only [hdegree, Polynomial.natDegree_derivative] using hres
  rw [Polynomial.separable_def]
  by_contra hcoprime
  apply hres'
  exact Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl hp, hcoprime⟩

/-- Nonmonic coefficient-family criterion.  A nonzero displayed top
coefficient prevents degree drop, so the fixed-size resultant detects
separability of the specialized fiber. -/
theorem fixedDegreePolynomialAt_separable_of_top_ne_zero_of_resultant_derivative_ne_zero
    {X : Type*} {d : ℕ} (hd : 0 < d)
    (a : Fin (d + 1) → X → ℂ) (x : X)
    (htop : a ⟨d, Nat.lt_succ_self d⟩ x ≠ 0)
    (hres : Polynomial.resultant
      (fixedDegreePolynomialAt a x)
      (fixedDegreePolynomialAt a x).derivative d (d - 1) ≠ 0) :
    (fixedDegreePolynomialAt a x).Separable := by
  apply separable_of_resultant_derivative_ne_zero hd
  · exact fixedDegreePolynomial_natDegree_eq _ htop
  · exact hres

/-- For a positive-degree monic complex polynomial, nonvanishing of the
fixed-size resultant with its derivative implies separability. -/
theorem monic_separable_of_resultant_derivative_ne_zero
    {d : ℕ} (_hd : 0 < d) {p : Polynomial ℂ}
    (hmonic : p.Monic) (hdegree : p.natDegree = d)
    (hres : Polynomial.resultant p p.derivative d (d - 1) ≠ 0) :
    p.Separable := by
  have hres' : Polynomial.resultant p p.derivative ≠ 0 := by
    simpa only [hdegree, Polynomial.natDegree_derivative] using hres
  exact (Polynomial.isUnit_resultant_iff_isCoprime hmonic).mp
    (isUnit_iff_ne_zero.mpr hres')

/-- Coefficient-family form of the preceding separability criterion. -/
theorem fixedDegreePolynomialAt_separable_of_resultant_derivative_ne_zero
    {X : Type*} {d : ℕ} (hd : 0 < d)
    (a : Fin (d + 1) → X → ℂ) (x : X)
    (htop : a ⟨d, Nat.lt_succ_self d⟩ x = 1)
    (hres : Polynomial.resultant
      (fixedDegreePolynomialAt a x)
      (fixedDegreePolynomialAt a x).derivative d (d - 1) ≠ 0) :
    (fixedDegreePolynomialAt a x).Separable := by
  apply monic_separable_of_resultant_derivative_ne_zero hd
  · exact fixedDegreePolynomial_monic _ htop
  · apply fixedDegreePolynomial_natDegree_eq
    simp [htop]
  · exact hres

/-- Eventual simple-fiber package: wherever an eventual representative of
the derivative resultant is nonzero, the specialized fixed-degree fiber is
separable.  This is the form consumed by polynomial-fiber rigidity. -/
theorem eventually_separable_of_resultant_derivative_rep
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (Δ : ComplexEuclidean n → ℂ)
    (htop : ∀ᶠ z in 𝓝 z₀,
      a ⟨d, Nat.lt_succ_self d⟩ z = 1)
    (hΔ : ∀ᶠ z in 𝓝 z₀,
      Δ z = Polynomial.resultant
        (fixedDegreePolynomialAt a z)
        (fixedDegreePolynomialAt a z).derivative d (d - 1)) :
    ∀ᶠ z in 𝓝 z₀, Δ z ≠ 0 →
      (fixedDegreePolynomialAt a z).Separable := by
  filter_upwards [htop, hΔ] with z htopz hΔz
  intro hne
  apply fixedDegreePolynomialAt_separable_of_resultant_derivative_ne_zero
    hd a z htopz
  rwa [← hΔz]

/-- Eventual nonmonic simple-fiber criterion, retaining the useful
pointwise implication from nonvanishing of the resultant representative. -/
theorem eventually_separable_of_top_ne_zero_of_resultant_derivative_rep
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (Δ : ComplexEuclidean n → ℂ)
    (htop : ∀ᶠ z in 𝓝 z₀,
      a ⟨d, Nat.lt_succ_self d⟩ z ≠ 0)
    (hΔ : ∀ᶠ z in 𝓝 z₀,
      Δ z = Polynomial.resultant
        (fixedDegreePolynomialAt a z)
        (fixedDegreePolynomialAt a z).derivative d (d - 1)) :
    ∀ᶠ z in 𝓝 z₀, Δ z ≠ 0 →
      (fixedDegreePolynomialAt a z).Separable := by
  filter_upwards [htop, hΔ] with z htopz hΔz
  intro hne
  apply
    fixedDegreePolynomialAt_separable_of_top_ne_zero_of_resultant_derivative_ne_zero
      hd a z htopz
  rwa [← hΔz]

/-- If both the displayed top coefficient and the derivative-resultant
representative are eventually nonzero, all nearby specialized fibers are
eventually separable. -/
theorem eventually_separable_of_top_ne_zero_of_resultant_derivative_ne_zero
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (Δ : ComplexEuclidean n → ℂ)
    (htop : ∀ᶠ z in 𝓝 z₀,
      a ⟨d, Nat.lt_succ_self d⟩ z ≠ 0)
    (hΔ : ∀ᶠ z in 𝓝 z₀,
      Δ z = Polynomial.resultant
        (fixedDegreePolynomialAt a z)
        (fixedDegreePolynomialAt a z).derivative d (d - 1))
    (hΔne : ∀ᶠ z in 𝓝 z₀, Δ z ≠ 0) :
    ∀ᶠ z in 𝓝 z₀, (fixedDegreePolynomialAt a z).Separable := by
  filter_upwards
    [eventually_separable_of_top_ne_zero_of_resultant_derivative_rep
      hd a Δ htop hΔ, hΔne] with z hz hne
  exact hz hne

/-! ## Analytic derivative-resultant representatives -/

/-- The coefficient family (with fixed degree bound `d - 1`) of the
derivative of a degree-`d` polynomial family. -/
def fixedDegreeDerivativeFamily
    {X : Type*} {d : ℕ}
    (a : Fin (d + 1) → X → ℂ) :
    Fin ((d - 1) + 1) → X → ℂ :=
  fun i x ↦ (fixedDegreePolynomialAt a x).derivative.coeff (i : ℕ)

/-- Derivative coefficients of an analytic positive-degree family are
analytic. -/
theorem analyticAt_fixedDegreeDerivativeFamily
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (i : Fin ((d - 1) + 1)) :
    AnalyticAt ℂ (fixedDegreeDerivativeFamily a i) z₀ := by
  have hi : (i : ℕ) < d := by omega
  let j : Fin (d + 1) := ⟨(i : ℕ) + 1, by omega⟩
  have heq : fixedDegreeDerivativeFamily a i =
      fun z ↦ a j z * ((i : ℕ) + 1 : ℂ) := by
    funext z
    simp [fixedDegreeDerivativeFamily, fixedDegreePolynomialAt,
      Polynomial.coeff_derivative, j, hi]
  rw [heq]
  exact (ha j).mul analyticAt_const

/-- Assembling the displayed derivative coefficients recovers the actual
polynomial derivative. -/
theorem fixedDegreePolynomialAt_derivativeFamily
    {X : Type*} {d : ℕ} (_hd : 0 < d)
    (a : Fin (d + 1) → X → ℂ) (x : X) :
    fixedDegreePolynomialAt (fixedDegreeDerivativeFamily a) x =
      (fixedDegreePolynomialAt a x).derivative := by
  let p := fixedDegreePolynomialAt a x
  have hp : p.derivative.natDegree ≤ d - 1 :=
    (Polynomial.natDegree_derivative_le p).trans <|
      Nat.sub_le_sub_right
        (fixedDegreePolynomial_natDegree_le (fun i ↦ a i x)) 1
  simpa only [fixedDegreeDerivativeFamily, fixedDegreePolynomialAt, p] using
    fixedDegreePolynomial_coefficients_eq p.derivative hp

/-- A positive-degree analytic coefficient family admits an analytic
representative of its fixed-size resultant with its derivative. -/
theorem exists_analytic_resultant_derivative
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ z₀ ∧
      ∀ᶠ z in 𝓝 z₀,
        Δ z = Polynomial.resultant
          (fixedDegreePolynomialAt a z)
          (fixedDegreePolynomialAt a z).derivative d (d - 1) := by
  let b := fixedDegreeDerivativeFamily a
  have hb : ∀ i, AnalyticAt ℂ (b i) z₀ :=
    fun i ↦ analyticAt_fixedDegreeDerivativeFamily hd a ha i
  obtain ⟨Δ, hΔ, hΔeq⟩ :=
    exists_analytic_fixedDegreeResultantAt a b ha hb
  refine ⟨Δ, hΔ, ?_⟩
  filter_upwards [hΔeq] with z hz
  change Δ z = Polynomial.resultant
      (fixedDegreePolynomialAt a z)
      (fixedDegreePolynomialAt b z) d (d - 1) at hz
  rw [fixedDegreePolynomialAt_derivativeFamily hd a z] at hz
  exact hz

/-- End-to-end analytic resultant package for a locally nonmonic family whose
displayed leading coefficient does not vanish. -/
theorem exists_analytic_resultant_derivative_and_eventually_separable_of_top_ne_zero
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (htop : ∀ᶠ z in 𝓝 z₀,
      a ⟨d, Nat.lt_succ_self d⟩ z ≠ 0) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ z₀ ∧
      (∀ᶠ z in 𝓝 z₀,
        Δ z = Polynomial.resultant
          (fixedDegreePolynomialAt a z)
          (fixedDegreePolynomialAt a z).derivative d (d - 1)) ∧
      (∀ᶠ z in 𝓝 z₀, Δ z ≠ 0 →
        (fixedDegreePolynomialAt a z).Separable) := by
  obtain ⟨Δ, hΔ, hΔeq⟩ := exists_analytic_resultant_derivative hd a ha
  exact ⟨Δ, hΔ, hΔeq,
    eventually_separable_of_top_ne_zero_of_resultant_derivative_rep
      hd a Δ htop hΔeq⟩

/-- End-to-end local simple-fiber package for a monic analytic family. -/
theorem exists_analytic_resultant_derivative_and_eventually_separable
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin (d + 1) → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀)
    (htop : ∀ᶠ z in 𝓝 z₀,
      a ⟨d, Nat.lt_succ_self d⟩ z = 1) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ z₀ ∧
      (∀ᶠ z in 𝓝 z₀,
        Δ z = Polynomial.resultant
          (fixedDegreePolynomialAt a z)
          (fixedDegreePolynomialAt a z).derivative d (d - 1)) ∧
      (∀ᶠ z in 𝓝 z₀, Δ z ≠ 0 →
        (fixedDegreePolynomialAt a z).Separable) := by
  obtain ⟨Δ, hΔ, hΔeq⟩ := exists_analytic_resultant_derivative hd a ha
  exact ⟨Δ, hΔ, hΔeq,
    eventually_separable_of_resultant_derivative_rep hd a Δ htop hΔeq⟩

/-! ## Prepared-polynomial specialization -/

/-- Complete the `d` lower coefficients of a prepared polynomial by its
constant leading coefficient one. -/
def monicCoefficientCompletion
    {R X : Type*} [Semiring R] {d : ℕ}
    (a : Fin d → X → R) : Fin (d + 1) → X → R :=
  fun i x ↦ if h : (i : ℕ) < d then a ⟨i, h⟩ x else 1

@[simp]
theorem monicCoefficientCompletion_castSucc
    {R X : Type*} [Semiring R] {d : ℕ}
    (a : Fin d → X → R) (i : Fin d) (x : X) :
    monicCoefficientCompletion a i.castSucc x = a i x := by
  simp [monicCoefficientCompletion, i.isLt]

@[simp]
theorem monicCoefficientCompletion_last
    {R X : Type*} [Semiring R] {d : ℕ}
    (a : Fin d → X → R) (x : X) :
    monicCoefficientCompletion a (Fin.last d) x = 1 := by
  simp [monicCoefficientCompletion]

/-- Completing analytic lower coefficients by one preserves analyticity. -/
theorem analyticAt_monicCoefficientCompletion
    {n d : ℕ} {z₀ : ComplexEuclidean n}
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) (i : Fin (d + 1)) :
    AnalyticAt ℂ (monicCoefficientCompletion a i) z₀ := by
  by_cases hi : (i : ℕ) < d
  · have heq : monicCoefficientCompletion a i = a ⟨i, hi⟩ := by
      funext z
      simp [monicCoefficientCompletion, hi]
    rw [heq]
    exact ha ⟨i, hi⟩
  · have heq : monicCoefficientCompletion a i =
        (fun _ : ComplexEuclidean n ↦ (1 : ℂ)) := by
      funext z
      simp [monicCoefficientCompletion, hi]
    rw [heq]
    exact analyticAt_const

/-- The completed fixed-degree polynomial is the prepared monic polynomial
used by the finite-fiber API. -/
theorem fixedDegreePolynomialAt_monicCoefficientCompletion
    {n d : ℕ} (a : Fin d → ComplexEuclidean n → ℂ)
    (z : ComplexEuclidean n) :
    fixedDegreePolynomialAt (monicCoefficientCompletion a) z =
      preparedPolynomialAt a z := by
  unfold fixedDegreePolynomialAt fixedDegreePolynomial preparedPolynomialAt
  rw [Fin.sum_univ_castSucc]
  simp [add_comm]

/-- Direct resultant/simple-root package for prepared polynomial fibers. -/
theorem exists_analytic_prepared_resultant_and_eventually_separable
    {n d : ℕ} {z₀ : ComplexEuclidean n} (hd : 0 < d)
    (a : Fin d → ComplexEuclidean n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) z₀) :
    ∃ Δ : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ Δ z₀ ∧
      (∀ᶠ z in 𝓝 z₀,
        Δ z = Polynomial.resultant
          (preparedPolynomialAt a z)
          (preparedPolynomialAt a z).derivative d (d - 1)) ∧
      (∀ᶠ z in 𝓝 z₀, Δ z ≠ 0 →
        (preparedPolynomialAt a z).Separable) := by
  let A := monicCoefficientCompletion a
  have hA : ∀ i, AnalyticAt ℂ (A i) z₀ :=
    fun i ↦ analyticAt_monicCoefficientCompletion a ha i
  have htop : ∀ᶠ z in 𝓝 z₀,
      A ⟨d, Nat.lt_succ_self d⟩ z = 1 := by
    apply Filter.Eventually.of_forall
    intro z
    simp [A, monicCoefficientCompletion]
  obtain ⟨Δ, hΔ, hΔeq, hsep⟩ :=
    exists_analytic_resultant_derivative_and_eventually_separable
      hd A hA htop
  refine ⟨Δ, hΔ, ?_, ?_⟩
  · filter_upwards [hΔeq] with z hz
    have hAz : fixedDegreePolynomialAt A z = preparedPolynomialAt a z := by
      simpa only [A] using
        fixedDegreePolynomialAt_monicCoefficientCompletion a z
    rw [hAz] at hz
    exact hz
  · filter_upwards [hsep] with z hz
    intro hne
    have hAz : fixedDegreePolynomialAt A z = preparedPolynomialAt a z := by
      simpa only [A] using
        fixedDegreePolynomialAt_monicCoefficientCompletion a z
    rw [hAz] at hz
    exact hz hne

end

end LocalComplexGeometry
