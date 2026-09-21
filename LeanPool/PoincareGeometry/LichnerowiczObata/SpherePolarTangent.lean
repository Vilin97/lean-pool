/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import LeanPool.PoincareGeometry.LichnerowiczObata.PolarMetricNondegeneracy
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Manifold angular tangents in the polar derivative -/

@[expose] public noncomputable section
open scoped Manifold
namespace LichnerowiczObata
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]

/-- The differential of sphere inclusion supplies intrinsic angular
tangent vectors; the radial component is left unchanged. -/
def spherePolarTangentInclusion (u : Metric.sphere (0 : P) 1) :
    TangentSpace (𝓡 n) u × ℝ →L[ℝ] P × ℝ :=
  (mvfderiv (𝓡 n) (Subtype.val : Metric.sphere (0 : P) 1 → P) u).prodMap
    (ContinuousLinearMap.id ℝ ℝ)

theorem spherePolarTangentInclusion_orthogonal (u : Metric.sphere (0 : P) 1)
    (v : TangentSpace (𝓡 n) u × ℝ) :
    inner ℝ (u : P) (spherePolarTangentInclusion u v).1 = 0 := by
  apply Submodule.mem_orthogonal_singleton_iff_inner_right.mp
  rw [← range_mvfderiv_subtypeVal (n := n) u]
  exact ⟨v.1, rfl⟩

theorem spherePolarTangentInclusion_injective (u : Metric.sphere (0 : P) 1) :
    Function.Injective (spherePolarTangentInclusion (n := n) u) := by
  intro x y hxy
  have hf := congrArg Prod.fst hxy
  have hs := congrArg Prod.snd hxy
  apply Prod.ext
  · exact injective_mvfderiv_subtypeVal_sphere u hf
  · exact hs

/-- Polar injectivity on the orthogonal angular hyperplane becomes genuine
injectivity on the sphere manifold tangent and radial parameter space. -/
theorem polar_derivative_sphere_tangent_injective
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (u : Metric.sphere (0 : P) 1) (D : P × ℝ →L[ℝ] V)
    (hD : Set.InjOn D {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    Function.Injective (D.comp (spherePolarTangentInclusion (n := n) u)) := by
  intro x y hxy
  apply spherePolarTangentInclusion_injective u
  exact hD (spherePolarTangentInclusion_orthogonal u x)
    (spherePolarTangentInclusion_orthogonal u y) hxy

/-- The constructed tangent inclusion is the actual derivative of the
sphere-and-radius inclusion map. -/
theorem mvfderiv_sphere_polar_inclusion (u : Metric.sphere (0 : P) 1) (r : ℝ) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (fun q : Metric.sphere (0 : P) 1 × ℝ => ((q.1 : P), q.2)) (u, r) =
      spherePolarTangentInclusion (n := n) u := by
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P)
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P)
      (fun q : Metric.sphere (0 : P) 1 × ℝ => (q.1 : P)) (u, r) :=
    hc.comp (f := Prod.fst) (g := Subtype.val) (u, r) mdifferentiableAt_fst
  have hs : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : Metric.sphere (0 : P) 1 × ℝ → ℝ) (u, r) := mdifferentiableAt_snd
  have hp := mfderiv_prodMk hf hs
  have hfst : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (Prod.fst : Metric.sphere (0 : P) 1 × ℝ → Metric.sphere (0 : P) 1) (u, r) :=
    mdifferentiableAt_fst
  have he := mfderiv_comp (f := Prod.fst) (g := (Subtype.val : Metric.sphere (0 : P) 1 → P))
    (u, r) hc hfst
  rw [mfderiv_fst] at he
  simp only [Function.comp_def] at he
  rw [he, mfderiv_snd] at hp
  convert hp using 1 <;> first | rfl | skip
  simp only [mvfderiv, mfderiv, hf.prodMk_space hs, hf.prodMk hs, if_true]
  rfl

section Restriction
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- Joint ambient differentiability restricts to the actual angular sphere
and radial manifold, with its standard sphere charts. -/
theorem mdifferentiableAt_sphere_polar_restriction {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r)) :
    MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) := by
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, P)
      (Subtype.val : Metric.sphere (0 : P) 1 → P) u :=
    (contMDiff_coe_sphere u).mdifferentiableAt one_ne_zero
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P)
      (fun q : Metric.sphere (0 : P) 1 × ℝ => (q.1 : P)) (u, r) :=
    hc.comp (f := Prod.fst) (g := Subtype.val) (u, r) mdifferentiableAt_fst
  have hi : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P × ℝ)
      (fun q : Metric.sphere (0 : P) 1 × ℝ => ((q.1 : P), q.2)) (u, r) :=
    hf.prodMk_space mdifferentiableAt_snd
  exact hΦ.comp (u, r) hi

/-- The actual derivative of the restricted polar map is its ambient
derivative composed with the sphere tangent inclusion. -/
theorem mfderiv_sphere_polar_restriction {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r)) :
    mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) =
      (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r)).comp
        (spherePolarTangentInclusion (n := n) u) := by
  let j := fun q : Metric.sphere (0 : P) 1 × ℝ => ((q.1 : P), q.2)
  have hj : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P × ℝ) j (u, r) :=
    mdifferentiableAt_sphere_polar_restriction u r (Φ := id) mdifferentiableAt_id
  have hd : mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, P × ℝ) j (u, r) =
      spherePolarTangentInclusion (n := n) u := by
    ext v
    exact congrArg (fun D => D v) (mvfderiv_sphere_polar_inclusion (n := n) u r)
  have hc := mfderiv_comp (f := j) (g := Φ) (u, r) hΦ hj
  rw [hd] at hc
  exact hc

/-- Orthogonal polar injectivity is injectivity of the actual manifold
derivative of the sphere-restricted parameter map. -/
theorem mfderiv_sphere_polar_restriction_injective {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
    (hD : Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
      {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    Function.Injective (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
      (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r)) := by
  rw [mfderiv_sphere_polar_restriction u r hΦ]
  exact polar_derivative_sphere_tangent_injective u _ hD

end Restriction

section Equivalence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- With matching dimensions, the actual sphere-restricted polar derivative
is a continuous linear equivalence, not merely an injective map. -/
theorem exists_sphere_polar_derivative_equiv {Φ : P × ℝ → M}
    (u : Metric.sphere (0 : P) 1) (r : ℝ)
    (hDim : Module.finrank ℝ E = n + 1)
    (hΦ : MDifferentiableAt 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
    (hD : Set.InjOn (mfderiv 𝓘(ℝ, P × ℝ) I Φ ((u : P), r))
      {q : P × ℝ | inner ℝ (u : P) q.1 = 0}) :
    ∃ e : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) (u, r) ≃L[ℝ]
        TangentSpace I (Φ ((u : P), r)),
      (e : _ →L[ℝ] _) = mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
        (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) ∧
      HasMFDerivAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
        (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r) (e : _ →L[ℝ] _) := by
  let : FiniteDimensional ℝ (TangentSpace I (Φ ((u : P), r))) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  let : T2Space (TangentSpace I (Φ ((u : P), r))) := inferInstanceAs (T2Space E)
  let : FiniteDimensional ℝ (TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) (u, r)) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n) × ℝ))
  let : T2Space (TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) (u, r)) :=
    inferInstanceAs (T2Space (EuclideanSpace ℝ (Fin n) × ℝ))
  let D := mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) I
    (fun q : Metric.sphere (0 : P) 1 × ℝ => Φ (q.1, q.2)) (u, r)
  have hi : Function.Injective D := mfderiv_sphere_polar_restriction_injective u r hΦ hD
  have hd : Module.finrank ℝ (TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) (u, r)) =
      Module.finrank ℝ (TangentSpace I (Φ ((u : P), r))) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) = Module.finrank ℝ E
    simp [Module.finrank_prod, hDim]
  let e := (D.toLinearMap.linearEquivOfInjective hi hd).toContinuousLinearEquiv
  have he : (e : _ →L[ℝ] _) = D := by ext v; rfl
  refine ⟨e, he, ?_⟩
  rw [he]
  exact (mdifferentiableAt_sphere_polar_restriction u r hΦ).hasMFDerivAt

end Equivalence
end LichnerowiczObata
