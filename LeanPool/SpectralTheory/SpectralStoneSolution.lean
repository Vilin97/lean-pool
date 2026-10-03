/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/
/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanPool.SpectralTheory.Spectral.Spectral.Intrinsic
public import LeanPool.SpectralTheory.Spectral.Stone.Intrinsic


/-!
# Spectral theorem for unbounded self-adjoint operators (Solution)

Redeclare-bridge: `PVM` and `StrongContUnitary` are restated verbatim in the
`PalomarSpectralStone` namespace (matching `SpectralStoneChallenge.lean`), with
conversion functions to and from the proof library's independently-elaborated
copies. `spectral_theorem_intrinsic` and `stone_theorem_intrinsic` are
restated and closed by transporting the library's theorems across that
conversion.
-/

public section

open Function MeasureTheory

namespace PalomarSpectralStone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A projection-valued measure on `ℝ`, countably additive in the strong
operator topology. Its laws are imposed on Borel-measurable sets. -/
structure PVM (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] where
  /-- The orthogonal projection assigned to a measurable subset of the real line. -/
  proj : Set ℝ → (E →L[ℂ] E)
  isOrthogonalProjection : ∀ S, MeasurableSet S →
    IsSelfAdjoint (proj S) ∧ IsIdempotentElem (proj S)
  empty : proj ∅ = 0
  univ : proj Set.univ = 1
  inter : ∀ S T, MeasurableSet S → MeasurableSet T →
    proj (S ∩ T) = proj S * proj T
  countably_additive : ∀ (S : ℕ → Set ℝ),
    (∀ i, MeasurableSet (S i)) →
    Pairwise (Disjoint on S) →
    ∀ x, Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, proj (S i) x)
      Filter.atTop (nhds (proj (⋃ i, S i) x))

/-- `E_pvm` represents `A` when its scalar measures are the diagonal matrix
coefficients of the spectral projections, `A` has precisely their finite
second-moment domain, and the diagonal matrix coefficient of `A` is their
first moment. Complex polarization recovers all mixed matrix coefficients. -/
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

/-- Repackage a library `PVM` as a `PalomarSpectralStone.PVM` with the same fields. -/
def PVM.ofRoot (p : _root_.PVM E) : PVM E :=
  ⟨p.proj, p.isOrthogonalProjection, p.empty, p.univ, p.inter, p.countably_additive⟩

/-- Repackage a `PalomarSpectralStone.PVM` as a library `PVM` with the same fields. -/
def PVM.toRoot (p : PVM E) : _root_.PVM E :=
  ⟨p.proj, p.isOrthogonalProjection, p.empty, p.univ, p.inter, p.countably_additive⟩

theorem PVM.represents_ofRoot {p : _root_.PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.ofRoot p).Represents A ↔ p.Represents A := Iff.rfl

theorem PVM.represents_toRoot {p : PVM E} {A : E →ₗ.[ℂ] E} :
    (PVM.toRoot p).Represents A ↔ p.Represents A := Iff.rfl

/-- Every unbounded self-adjoint operator has a real PVM spectral
representation, unique on Borel-measurable sets. -/
theorem spectral_theorem_intrinsic
    (A : E →ₗ.[ℂ] E) (hA : IsSelfAdjoint A) :
    ∃ E_pvm : PVM E,
      E_pvm.Represents A ∧
      ∀ F_pvm : PVM E, F_pvm.Represents A →
        ∀ S : Set ℝ, MeasurableSet S → E_pvm.proj S = F_pvm.proj S := by
  obtain ⟨E_pvm, hRep, hUniq⟩ := _root_.spectral_theorem_intrinsic A hA
  refine ⟨PVM.ofRoot E_pvm, PVM.represents_ofRoot.mpr hRep, ?_⟩
  intro F_pvm hF S hS
  exact hUniq (PVM.toRoot F_pvm) (PVM.represents_toRoot.mpr hF) S hS

/-- A strongly continuous one-parameter unitary group. -/
structure StrongContUnitary (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] where
  /-- The unitary operator at each real time. -/
  toFun : ℝ → (E →L[ℂ] E)
  isUnitary : ∀ t, toFun t ∈ unitary (E →L[ℂ] E)
  zero : toFun 0 = 1
  add : ∀ s t, toFun (s + t) = toFun s * toFun t
  stronglyContinuous : ∀ x, Continuous (fun t => toFun t x)

/-- `U` has infinitesimal generator `A`: its domain is exactly the vectors
whose Stone difference quotient converges, and the limit is `A`. -/
def StrongContUnitary.Generates (U : StrongContUnitary E)
    (A : E →ₗ.[ℂ] E) : Prop :=
  (∀ x : E, x ∈ A.domain ↔
    ∃ y, Filter.Tendsto
      (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t x - x))
      (nhdsWithin 0 {0}ᶜ) (nhds y)) ∧
  ∀ x : A.domain, Filter.Tendsto
    (fun t : ℝ ↦ (Complex.I * (t : ℂ))⁻¹ • (U.toFun t (x : E) - x))
    (nhdsWithin 0 {0}ᶜ) (nhds (A x))

/-- Repackage a library `StrongContUnitary` with the same fields. -/
def StrongContUnitary.ofRoot (u : _root_.StrongContUnitary E) : StrongContUnitary E :=
  ⟨u.toFun, u.isUnitary, u.zero, u.add, u.stronglyContinuous⟩

/-- Repackage a `PalomarSpectralStone.StrongContUnitary` as a library one. -/
def StrongContUnitary.toRoot (u : StrongContUnitary E) : _root_.StrongContUnitary E :=
  ⟨u.toFun, u.isUnitary, u.zero, u.add, u.stronglyContinuous⟩

theorem StrongContUnitary.generates_ofRoot
    {u : _root_.StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.ofRoot u).Generates A ↔ u.Generates A := Iff.rfl

theorem StrongContUnitary.generates_toRoot
    {u : StrongContUnitary E} {A : E →ₗ.[ℂ] E} :
    (StrongContUnitary.toRoot u).Generates A ↔ u.Generates A := Iff.rfl

/-- Stone's theorem: every strongly continuous unitary group has a
self-adjoint generator, and every self-adjoint operator generates such
a group. -/
theorem stone_theorem_intrinsic :
    (∀ U : StrongContUnitary E, ∃ A : E →ₗ.[ℂ] E,
      IsSelfAdjoint A ∧ U.Generates A) ∧
    (∀ A : E →ₗ.[ℂ] E, IsSelfAdjoint A →
      ∃ U : StrongContUnitary E, U.Generates A) := by
  refine ⟨fun U ↦ ?_, fun A hA ↦ ?_⟩
  · obtain ⟨A, hA, hGen⟩ := _root_.stone_theorem_intrinsic.1 (StrongContUnitary.toRoot U)
    exact ⟨A, hA, StrongContUnitary.generates_toRoot.mp hGen⟩
  · obtain ⟨U, hGen⟩ := _root_.stone_theorem_intrinsic.2 A hA
    exact ⟨StrongContUnitary.ofRoot U, StrongContUnitary.generates_ofRoot.mpr hGen⟩

end PalomarSpectralStone
