/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.LichnerowiczObata.ObataMatchedPolarModels
public import LeanPool.PoincareGeometry.LichnerowiczObata.SphereRadialExtension
public import LeanPool.PoincareGeometry.LichnerowiczObata.EuclideanPolarInverse

/-! # Differentials of radial extensions of angular metric isometries -/

@[expose] public noncomputable section
open Set Metric
open scoped Manifold Topology
namespace LichnerowiczObata
variable {P V : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [Fact (Module.finrank ℝ P = n + 1)]
  [Fact (Module.finrank ℝ V = n + 1)]

def sphereAngularRadialMap (A : sphere (0 : P) 1 → sphere (0 : V) 1)
    (q : sphere (0 : P) 1 × ℝ) : V := q.2 • (A q.1 : V)

theorem mdifferentiable_sphereAngularRadialMap
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A) :
    MDifferentiable ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) (sphereAngularRadialMap A) := by
  intro q
  have ha := (hA q.1).comp q (mdifferentiableAt_fst (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)))
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, V)
      (Subtype.val : sphere (0 : V) 1 → V) (A q.1) :=
    (contMDiff_coe_sphere (A q.1)).mdifferentiableAt one_ne_zero
  exact mdifferentiableAt_snd.smul (hc.comp q ha)

theorem mvfderiv_sphereAngularRadialMap_apply
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (u : sphere (0 : P) 1) (r : ℝ) (v : TangentSpace (𝓡 n) u) (s : ℝ) :
    mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (sphereAngularRadialMap A) (u, r) (v, s) =
      r • (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u v)) + s • (A u : V) := by
  let g := fun q : sphere (0 : P) 1 × ℝ => (A q.1 : V)
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ, V)
      (Subtype.val : sphere (0 : V) 1 → V) (A u) :=
    (contMDiff_coe_sphere (A u)).mdifferentiableAt one_ne_zero
  have hf : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 n)
      (Prod.fst : sphere (0 : P) 1 × ℝ → sphere (0 : P) 1) (u, r) :=
    mdifferentiableAt_fst
  have hg : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, V) g (u, r) :=
    (hc.comp u (hA u)).comp (f := Prod.fst)
      (g := fun a : sphere (0 : P) 1 => (A a : V)) (u, r) hf
  have hs : MDifferentiableAt ((𝓡 n).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ)
      (Prod.snd : sphere (0 : P) 1 × ℝ → ℝ) (u, r) := mdifferentiableAt_snd
  have hgd : mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) g (u, r) (v, s) =
      mvfderiv (𝓡 n) (Subtype.val : sphere (0 : V) 1 → V) (A u)
        (mfderiv (𝓡 n) (𝓡 n) A u v) := by
    have hh := mfderiv_comp (f := Prod.fst)
      (g := fun a : sphere (0 : P) 1 => (A a : V)) (u, r) (hc.comp u (hA u)) hf
    have ha := mfderiv_comp (f := A)
      (g := (Subtype.val : sphere (0 : V) 1 → V)) u hc (hA u)
    simp only [Function.comp_def] at ha
    rw [mfderiv_fst, ha] at hh
    convert congrArg (fun D => D (v, s)) hh using 1 <;> rfl
  have hsd : mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ))
      (Prod.snd : sphere (0 : P) 1 × ℝ → ℝ) (u, r) (v, s) = s := by
    simp only [mvfderiv, mfderiv_snd]
    rfl
  have hh := congrArg (fun D => D (v, s)) (mvfderiv_smul hs hg)
  change mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (sphereAngularRadialMap A) (u, r) (v, s) =
    r • mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) g (u, r) (v, s) +
      mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) Prod.snd (u, r) (v, s) • (A u : V) at hh
  rwa [hgd, hsd] at hh

theorem sphereAngularRadialMap_metric
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (hm : PreservesSphereTangentMetric (n := n) A)
    (u : sphere (0 : P) 1) (r : ℝ) (v w : TangentSpace (𝓡 n) u) (s t : ℝ) :
    inner ℝ
      (mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (sphereAngularRadialMap A) (u, r) (v, s))
      (mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (sphereAngularRadialMap A) (u, r) (w, t)) =
      r ^ 2 * inner ℝ
        (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : P) 1 → P) u v)
        (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : P) 1 → P) u w) + s * t := by
  have hv := spherePolarTangentInclusion_orthogonal (n := n) (A u)
    (mfderiv (𝓡 n) (𝓡 n) A u v, 0)
  have hw := spherePolarTangentInclusion_orthogonal (n := n) (A u)
    (mfderiv (𝓡 n) (𝓡 n) A u w, 0)
  have hh := euclideanPolar_metric (A u) _ _ hv hw r s t
  simp only [fderiv_euclideanPolar_apply] at hh
  simp [spherePolarTangentInclusion] at hh
  rw [mvfderiv_sphereAngularRadialMap_apply hA, mvfderiv_sphereAngularRadialMap_apply hA]
  exact hh.trans (congrArg (fun a : ℝ => r ^ 2 * a + s * t) (hm u v w))

/-- The radial extension is differentiable away from zero, using the
constructed differentiable inverse of Euclidean polar coordinates. -/
theorem differentiableAt_sphereRadialExtension
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A) {x : P} (hx : x ≠ 0) :
    DifferentiableAt ℝ (sphereRadialExtension A) x := by
  let q := homeomorphUnitSphereProd P ⟨x, by simpa using hx⟩
  obtain ⟨e, hes, het, he, hi, hd⟩ := exists_euclidean_polar_inverse (n := n) q.1
  have hh := (mdifferentiable_sphereAngularRadialMap hA (e.symm x)).comp x (hd x hx)
  apply mdifferentiableAt_iff_differentiableAt.mp
  apply hh.congr_of_eventuallyEq
  filter_upwards [(isOpen_compl_singleton : IsOpen ({0}ᶜ : Set P)).mem_nhds
    (show x ∈ ({0}ᶜ : Set P) by simpa using hx)] with y hy
  have hy0 : y ≠ 0 := by simpa using hy
  rw [Function.comp_apply, hi ⟨y, hy⟩]
  simp [sphereRadialExtension, sphereAngularRadialMap, hy0]

/-- The ordinary Euclidean derivative of the radial extension preserves
inner products at every positive radial parameter. -/
theorem fderiv_sphereRadialExtension_inner_polar
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (hm : PreservesSphereTangentMetric (n := n) A)
    (u : sphere (0 : P) 1) {r : ℝ} (hr : 0 < r) (v w : P) :
    inner ℝ (fderiv ℝ (sphereRadialExtension A) (r • (u : P)) v)
      (fderiv ℝ (sphereRadialExtension A) (r • (u : P)) w) = inner ℝ v w := by
  let : FiniteDimensional ℝ P := .of_fact_finrank_eq_succ n
  let σ := fun q : P × ℝ => q.2 • q.1
  let σs := fun q : sphere (0 : P) 1 × ℝ => q.2 • (q.1 : P)
  have hσ : MDifferentiableAt 𝓘(ℝ, P × ℝ) 𝓘(ℝ, P) σ ((u : P), r) := by
    apply mdifferentiableAt_iff_differentiableAt.mpr
    dsimp [σ]
    fun_prop
  have hF : MDifferentiableAt 𝓘(ℝ, P) 𝓘(ℝ, V)
      (sphereRadialExtension A) (r • (u : P)) :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (differentiableAt_sphereRadialExtension hA
        (smul_ne_zero hr.ne' (ne_zero_of_mem_unit_sphere u)))
  obtain ⟨D', hD, hDeriv⟩ := exists_sphere_polar_derivative_equiv
    (I := 𝓘(ℝ, P)) (n := n) u r Fact.out hσ (euclideanPolar_derivative_injOn u hr)
  let D := D'.trans (NormedSpace.fromTangentSpace (σ ((u : P), r)))
  obtain ⟨v₀, rfl⟩ := D.surjective v
  obtain ⟨w₀, rfl⟩ := D.surjective w
  have hlocal : (sphereRadialExtension A ∘ σs)
      =ᶠ[𝓝 (u, r)] sphereAngularRadialMap A := by
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hr] with q hq
    exact sphereRadialExtension_smul A q.1 hq
  have hchain : (fderiv ℝ (sphereRadialExtension A) (r • (u : P))).comp
      (D : _ →L[ℝ] P) =
      mvfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (sphereAngularRadialMap A) (u, r) := by
    have hh := mfderiv_comp (f := σs) (g := sphereRadialExtension A) (u, r) hF
      (mdifferentiableAt_sphere_polar_restriction (n := n) u r hσ)
    rw [← hD, mfderiv_eq_fderiv] at hh
    convert hh.symm.trans hlocal.mfderiv_eq using 1 <;> rfl
  have hmetricD : inner ℝ (D v₀) (D w₀) = r ^ 2 *
      inner ℝ (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : P) 1 → P) u v₀.1)
        (mvfderiv (𝓡 n) (Subtype.val : sphere (0 : P) 1 → P) u w₀.1) + v₀.2 * w₀.2 := by
    have hv := congrArg (fun T => T v₀) hD
    have hw := congrArg (fun T => T w₀) hD
    rw [mfderiv_sphere_polar_restriction u r hσ, mfderiv_eq_fderiv] at hv hw
    change D v₀ = _ at hv
    change D w₀ = _ at hw
    rw [hv, hw]
    have hh := euclideanPolar_metric u _ _
      (spherePolarTangentInclusion_orthogonal u v₀)
      (spherePolarTangentInclusion_orthogonal u w₀) r v₀.2 w₀.2
    convert hh using 1 <;> rfl
  change inner ℝ
    (((fderiv ℝ (sphereRadialExtension A) (r • (u : P))).comp (D : _ →L[ℝ] P)) v₀)
    (((fderiv ℝ (sphereRadialExtension A) (r • (u : P))).comp (D : _ →L[ℝ] P)) w₀) = _
  rw [hchain, hmetricD]
  exact sphereAngularRadialMap_metric hA hm u r v₀.1 w₀.1 v₀.2 w₀.2

/-- The radial extension has an inner-product-preserving derivative at
every nonzero point. -/
theorem fderiv_sphereRadialExtension_inner
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (hm : PreservesSphereTangentMetric (n := n) A)
    {x : P} (hx : x ≠ 0) (v w : P) :
    inner ℝ (fderiv ℝ (sphereRadialExtension A) x v)
      (fderiv ℝ (sphereRadialExtension A) x w) = inner ℝ v w := by
  let q := homeomorphUnitSphereProd P ⟨x, by simpa using hx⟩
  have hq : (q.2 : ℝ) • (q.1 : P) = x :=
    congrArg Subtype.val ((homeomorphUnitSphereProd P).symm_apply_apply
      ⟨x, by simpa using hx⟩)
  have hh := fderiv_sphereRadialExtension_inner_polar hA hm q.1 q.2.property v w
  rwa [hq] at hh

theorem norm_fderiv_sphereRadialExtension_le
    {A : sphere (0 : P) 1 → sphere (0 : V) 1}
    (hA : MDifferentiable (𝓡 n) (𝓡 n) A)
    (hm : PreservesSphereTangentMetric (n := n) A)
    {x : P} (hx : x ≠ 0) : ‖fderiv ℝ (sphereRadialExtension A) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [one_mul]
  have hh := fderiv_sphereRadialExtension_inner hA hm hx v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg v, norm_nonneg (fderiv ℝ (sphereRadialExtension A) x v)]

end LichnerowiczObata
