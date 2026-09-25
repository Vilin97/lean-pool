/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.BonnetMyers.Curvature
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite-dimensional Ricci contraction

The index-form argument uses an orthonormal family perpendicular to the unit
tangent of a geodesic.  This file records the finite-dimensional algebra
behind that step.  It does not use a diameter or geodesic theorem.
-/

@[expose] public section

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology RealInnerProductSpace BigOperators

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- An orthonormal basis can be chosen with a prescribed unit vector at its
first index.  The nonzero-dimension hypothesis is stated as an inequality so
the lemma remains independent of any particular tangent-bundle instance. -/
lemma exists_orthonormalBasis_first {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] {a : V}
    (ha : ‖a‖ = 1) (hn : 1 ≤ Module.finrank ℝ V) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V,
      b ⟨0, by omega⟩ = a := by
  let i0 : Fin (Module.finrank ℝ V) := ⟨0, by omega⟩
  let s : Set (Fin (Module.finrank ℝ V)) := {i0}
  let v : Fin (Module.finrank ℝ V) → V := fun i => if i = i0 then a else 0
  have hv : Orthonormal ℝ (s.domRestrict v) := by
    rw [Orthonormal]
    constructor
    · intro i
      have hi : i = ⟨i0, by simp [s]⟩ := Subsingleton.elim _ _
      rw [hi]
      simp [s, v, ha]
    · intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
  obtain ⟨b, hb⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := V) (ι := Fin (Module.finrank ℝ V)) (s := s)
      (v := v) (by simp) hv
  refine ⟨b, ?_⟩
  simpa [i0, v] using hb i0 (show i0 ∈ s by simp [s])

/-- The trace of an endomorphism which kills a prescribed unit vector is the
sum over the remaining vectors of an orthonormal basis beginning with that
vector. -/
lemma trace_eq_sum_erase_zero_of_apply_eq_zero {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    {a : V} (ha : ‖a‖ = 1) (hn : 1 ≤ Module.finrank ℝ V)
    (T : V →ₗ[ℝ] V) (hTa : T a = 0) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ V)) ℝ V,
      b ⟨0, by omega⟩ = a ∧
        LinearMap.trace ℝ V T =
          Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin (Module.finrank ℝ V)))
            (fun i ↦ inner ℝ (b i) (T (b i))) := by
  obtain ⟨b, hb0⟩ := exists_orthonormalBasis_first ha hn
  have h0 : inner ℝ (b ⟨0, by omega⟩) (T (b ⟨0, by omega⟩)) = 0 := by
    rw [hb0, hTa, inner_zero_right]
  refine ⟨b, hb0, ?_⟩
  calc
    LinearMap.trace ℝ V T = ∑ i, inner ℝ (b i) (T (b i)) :=
      LinearMap.trace_eq_sum_inner T b
    _ = Finset.sum (Finset.univ.erase (⟨0, by omega⟩ : Fin (Module.finrank ℝ V)))
        (fun i ↦ inner ℝ (b i) (T (b i))) := by
      symm
      exact Finset.sum_erase _ h0

/-- The trace can be evaluated in any specified orthonormal basis after its
distinguished member is killed.  Unlike the preceding existence lemma, this
preserves a supplied moving frame, which is essential when the basis has been
obtained by parallel transport along a geodesic. -/
lemma trace_eq_sum_erase_of_orthonormalBasis
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : OrthonormalBasis ι ℝ V) (i₀ : ι) (T : V →ₗ[ℝ] V)
    (hT : T (b i₀) = 0) :
    LinearMap.trace ℝ V T =
      Finset.sum (Finset.univ.erase i₀)
        (fun i ↦ inner ℝ (b i) (T (b i))) := by
  classical
  have hzero : inner ℝ (b i₀) (T (b i₀)) = 0 := by
    rw [hT, inner_zero_right]
  calc
    LinearMap.trace ℝ V T = ∑ i, inner ℝ (b i) (T (b i)) :=
      LinearMap.trace_eq_sum_inner T b
    _ = Finset.sum (Finset.univ.erase i₀)
        (fun i ↦ inner ℝ (b i) (T (b i))) := by
      symm
      exact Finset.sum_erase _ hzero

/-- The curvature endomorphism obtained by fixing the last two slots of a
nested continuous-linear-map curvature tensor. -/
def curvatureEndomorphism
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (x : M) (a : TM x) : TM x →ₗ[ℝ] TM x where
  toFun z := R x z a a
  map_add' z z' := by simp
  map_smul' c z := by simp

@[simp] lemma curvatureEndomorphism_apply
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (x : M) (a z : TM x) :
    curvatureEndomorphism (R := R) x a z = R x z a a := rfl

lemma trace_eq_sum_erase_zero_curvature
    [RiemannianBundle TM]
    (R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x)
    (x : M) (a : TM x) (ha : ‖a‖ = 1)
    (hn : 1 ≤ Module.finrank ℝ (TM x))
    (hself : R x a a a = 0) :
    ∃ b : OrthonormalBasis (Fin (Module.finrank ℝ (TM x))) ℝ (TM x),
      b ⟨0, by omega⟩ = a ∧
        LinearMap.trace ℝ (TM x) (curvatureEndomorphism (R := R) x a) =
          Finset.sum
            (Finset.univ.erase (⟨0, by omega⟩ : Fin (Module.finrank ℝ (TM x))))
            (fun i ↦ inner ℝ (b i) (R x (b i) a a)) := by
  letI : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I : M → Type _) x
  have hTa : curvatureEndomorphism (R := R) x a a = 0 := by
    exact hself
  obtain ⟨b, hb0, htrace⟩ := trace_eq_sum_erase_zero_of_apply_eq_zero
    (V := TM x) ha hn (curvatureEndomorphism (R := R) x a) hTa
  refine ⟨b, hb0, ?_⟩
  simpa only [curvatureEndomorphism_apply] using htrace

end BonnetMyersEntry
