/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
import LeanPool.SpectralTheory.Spectral.Spectral.Uniqueness

/-!
# Intrinsic statement of the unbounded spectral theorem

This file packages the spectral representation without exposing the library's
particular construction of the unbounded spectral integral. The scalar
measure of a vector is fixed by the PVM's diagonal matrix coefficients, the
operator domain is exactly the finite-second-moment space, and the operator's
diagonal matrix coefficient is the first moment.
-/

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A PVM intrinsically represents a partial linear operator when its scalar
spectral measures give the exact domain and first-moment quadratic form. -/
def PVM.Represents (E_pvm : PVM E) (A : E →ₗ.[ℂ] E) : Prop :=
  ∃ scalarMeasure : E → Measure ℝ,
    (∀ (x : E) (S : Set ℝ), MeasurableSet S →
      scalarMeasure x S =
        ENNReal.ofReal ((@inner ℂ E _ (E_pvm.proj S x) x).re)) ∧
    (∀ x : E, x ∈ A.domain ↔
      ∫⁻ t, ‖(t : ℂ)‖₊ ^ 2 ∂(scalarMeasure x) < ⊤) ∧
    (∀ x : A.domain,
      @inner ℂ E _ (x : E) (A x) =
        ∫ t, (t : ℂ) ∂(scalarMeasure (x : E)))

/-- Equality with the coordinate spectral integral supplies an intrinsic
representation. -/
theorem PVM.represents_of_unboundedIntegral_eq (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E)
    (h : E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A) :
    E_pvm.Represents A := by
  subst A
  refine ⟨E_pvm.scalarMeasure, ?_, ?_, ?_⟩
  · intro x S hS
    exact E_pvm.scalarMeasure_apply x S hS
  · intro x
    exact E_pvm.mem_domain_unboundedIntegral
      ((↑) : ℝ → ℂ) Complex.continuous_ofReal.measurable x
  · intro x
    exact E_pvm.inner_coordinate_unboundedIntegral_self x

/-- Every self-adjoint partial linear operator has an intrinsic spectral
representation by a real projection-valued measure. -/
theorem spectral_theorem_intrinsic_existence
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E, E_pvm.Represents A := by
  rcases spectral_theorem_existence A hA with ⟨E_pvm, hrep⟩
  exact ⟨E_pvm, E_pvm.represents_of_unboundedIntegral_eq A hrep⟩

/-- The intrinsic representation is equivalent to the library's spectral
integral representation. In particular, its diagonal moment formulation does
not weaken the operator equality: complex polarization recovers every mixed
matrix coefficient. -/
theorem PVM.Represents.unboundedIntegral_eq
    {E_pvm : PVM E} {A : E →ₗ.[ℂ] E} (hrep : E_pvm.Represents A)
    (hA : IsSelfAdjoint A) :
    E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
      Complex.continuous_ofReal.measurable = A := by
  let coord : ℝ → ℂ := (↑)
  let hcoord : Measurable coord := Complex.continuous_ofReal.measurable
  let B := E_pvm.unboundedIntegral coord hcoord
  rcases hrep with ⟨mu, hmu, hdomain, hmoment⟩
  have hmeasure (x : E) : mu x = E_pvm.scalarMeasure x := by
    apply Measure.ext
    intro S hS
    rw [hmu x S hS, E_pvm.scalarMeasure_apply x S hS]
    rfl
  have hdomains : B.domain = A.domain := by
    ext x
    rw [show x ∈ B.domain ↔
        ∫⁻ t, ‖coord t‖₊ ^ 2 ∂(E_pvm.scalarMeasure x) < ⊤ from
      E_pvm.mem_domain_unboundedIntegral coord hcoord x]
    rw [hdomain x, hmeasure x]
  have hquad (z : E) (hzB : z ∈ B.domain) (hzA : z ∈ A.domain) :
      @inner ℂ E _ (B ⟨z, hzB⟩) z =
        @inner ℂ E _ (A ⟨z, hzA⟩) z := by
    have hdiag : @inner ℂ E _ z (B ⟨z, hzB⟩) =
        @inner ℂ E _ z (A ⟨z, hzA⟩) := by
      calc
        @inner ℂ E _ z (B ⟨z, hzB⟩) =
            ∫ t, coord t ∂(E_pvm.scalarMeasure z) := by
          exact E_pvm.inner_coordinate_unboundedIntegral_self ⟨z, hzB⟩
        _ = ∫ t, coord t ∂(mu z) := by rw [hmeasure z]
        _ = @inner ℂ E _ z (A ⟨z, hzA⟩) := (hmoment ⟨z, hzA⟩).symm
    calc
      @inner ℂ E _ (B ⟨z, hzB⟩) z =
          (starRingEnd ℂ) (@inner ℂ E _ z (B ⟨z, hzB⟩)) :=
        (inner_conj_symm (B ⟨z, hzB⟩) z).symm
      _ = (starRingEnd ℂ) (@inner ℂ E _ z (A ⟨z, hzA⟩)) :=
        congrArg (starRingEnd ℂ) hdiag
      _ = @inner ℂ E _ (A ⟨z, hzA⟩) z :=
        inner_conj_symm (A ⟨z, hzA⟩) z
  have hquad_sub (zB : B.domain) (zA : A.domain)
      (hz : (zB : E) = (zA : E)) :
      @inner ℂ E _ (B zB) (zB : E) =
        @inner ℂ E _ (A zA) (zA : E) := by
    rcases zB with ⟨zB, hzB⟩
    rcases zA with ⟨zA, hzA⟩
    simp only at hz ⊢
    subst zA
    exact hquad zB hzB hzA
  have hpolarization (T : E →ₗ.[ℂ] E) (a b : T.domain) :
      @inner ℂ E _ (T b) (a : E) =
        (@inner ℂ E _ (T (a + b)) ((a + b : T.domain) : E) -
            @inner ℂ E _ (T (a - b)) ((a - b : T.domain) : E) +
              Complex.I * @inner ℂ E _ (T (a + Complex.I • b))
                ((a + Complex.I • b : T.domain) : E) -
            Complex.I * @inner ℂ E _ (T (a - Complex.I • b))
              ((a - Complex.I • b : T.domain) : E)) / 4 := by
    simp only [LinearPMap.map_add, LinearPMap.map_sub, inner_add_left,
      inner_add_right, LinearPMap.map_smul, inner_smul_left, inner_smul_right,
      Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
      mul_add, ← mul_assoc, mul_neg, neg_neg, one_mul, neg_one_mul, mul_sub,
      sub_sub, Submodule.coe_add, Submodule.coe_sub, Submodule.coe_smul]
    ring
  apply LinearPMap.ext hdomains
  intro y hyB hyA
  apply hA.dense_domain.eq_of_inner_left ℂ
  intro v hvA
  have hvB : v ∈ B.domain := by rw [hdomains]; exact hvA
  let aB : B.domain := ⟨v, hvB⟩
  let bB : B.domain := ⟨y, hyB⟩
  let aA : A.domain := ⟨v, hvA⟩
  let bA : A.domain := ⟨y, hyA⟩
  rw [hpolarization B aB bB, hpolarization A aA bA]
  rw [hquad_sub (aB + bB) (aA + bA) rfl,
    hquad_sub (aB - bB) (aA - bA) rfl,
    hquad_sub (aB + Complex.I • bB) (aA + Complex.I • bA) rfl,
    hquad_sub (aB - Complex.I • bB) (aA - Complex.I • bA) rfl]

/-- For self-adjoint operators, the intrinsic and constructed spectral
integral formulations are logically equivalent. -/
theorem PVM.represents_iff_unboundedIntegral_eq (E_pvm : PVM E)
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    E_pvm.Represents A ↔
      E_pvm.unboundedIntegral ((↑) : ℝ → ℂ)
        Complex.continuous_ofReal.measurable = A :=
  ⟨fun h ↦ h.unboundedIntegral_eq hA,
    E_pvm.represents_of_unboundedIntegral_eq A⟩

/-- Intrinsic representations of a self-adjoint operator have the same
spectral projections on every measurable set. -/
theorem PVM.Represents.proj_eq_on_measurable
    {A : E →ₗ.[ℂ] E} (hA : IsSelfAdjoint A)
    {E₁ E₂ : PVM E} (h₁ : E₁.Represents A) (h₂ : E₂.Represents A)
    (S : Set ℝ) (hS : MeasurableSet S) :
    E₁.proj S = E₂.proj S :=
  spectral_theorem_uniqueness A hA E₁ E₂
    (h₁.unboundedIntegral_eq hA) (h₂.unboundedIntegral_eq hA) S hS

/-- The unbounded spectral theorem in intrinsic PVM form: every self-adjoint
partial operator has a spectral representation, unique on Borel sets. -/
theorem spectral_theorem_intrinsic
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by
  rcases spectral_theorem_intrinsic_existence A hA with ⟨E_pvm, hrep⟩
  refine ⟨E_pvm, hrep, ?_⟩
  intro F_pvm hF S hS
  exact hrep.proj_eq_on_measurable hA hF S hS
