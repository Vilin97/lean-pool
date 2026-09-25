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

/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smoothness of a *parametrized* fibrewise bilinear form on a vector bundle

Mathlib's `ContMDiffWithinAt.inner_bundle` proves that, on a Riemannian vector bundle, the scalar
product `⟪v m, w m⟫` of two smooth sections is smooth.  Its smoothness of the metric is supplied by
the typeclass `[IsContMDiffRiemannianBundle IB n F E]`, which fixes *one* metric on the bundle.

For a genuinely **time-dependent** metric `g_t` on the tangent bundle — the setting of Ricci flow —
that single-metric typeclass is not enough: as the time parameter varies, the fibrewise bilinear form
`g_t.inner x : E x →L[ℝ] E x →L[ℝ] ℝ` traces a family that must be controlled *jointly* in `(t, x)`.

This module records the parametrized version of `inner_bundle`, in which the fibrewise bilinear form
`g : Π y, E y →L[ℝ] E y →L[ℝ] ℝ` is supplied as an **explicit jointly-smooth section** (over a base
map `b : M → B`), rather than through the `IsContMDiffRiemannianBundle` instance.  The conclusion is
that evaluating it on two jointly-smooth sections is jointly smooth.  Instantiating the parameter
manifold `M := ℝ × M` and `b := Prod.snd` yields the joint `(t, x)` smoothness of a time-dependent
metric evaluated on fixed frame vectors — the missing input for the space-time Gram matrix used by
the Ricci–DeTurck gauge field.

The proof is exactly the internal argument of `inner_bundle` (`ContMDiffWithinAt.clm_bundle_apply₂`
into the trivial `ℝ`-bundle, then read off the fibre component), with the metric section made an
explicit hypothesis instead of extracted from the typeclass.
-/

@[expose] public section

open Manifold Bundle
open scoped Manifold Topology

namespace PoincareCurvature.ParametrizedInner

section

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}
  {g : ∀ y : B, E y →L[ℝ] E y →L[ℝ] ℝ}

/-- **Parametrized `inner_bundle`, within a set at a point.**  If a fibrewise bilinear form section
`g` (over a base map `b : M → B`) and two sections `v w` are all `C^n` jointly in the parameter `m`,
then the scalar `m ↦ g (b m) (v m) (w m)` is `C^n`.  This is the version of
`ContMDiffWithinAt.inner_bundle` in which the metric section is an explicit hypothesis rather than an
`IsContMDiffRiemannianBundle` instance, so it applies to a time-dependent metric. -/
lemma contMDiffWithinAt_metricSection_apply₂
    (hg : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) s x := by
  have hres : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (g (b m) (v m) (w m))) s x :=
    hg.clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [contMDiffWithinAt_totalSpace] at hres
  exact hres.2

/-- **Parametrized `inner_bundle`, at a point.** -/
lemma contMDiffAt_metricSection_apply₂
    (hg : ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) x := by
  rw [← contMDiffWithinAt_univ] at hg hv hw ⊢
  exact contMDiffWithinAt_metricSection_apply₂ hg hv hw

/-- **Parametrized `inner_bundle`, on a set.** -/
lemma contMDiffOn_metricSection_apply₂
    (hg : ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) s :=
  fun m hm ↦ contMDiffWithinAt_metricSection_apply₂ (hg m hm) (hv m hm) (hw m hm)

/-- **Parametrized `inner_bundle`, everywhere.** -/
lemma contMDiff_metricSection_apply₂
    (hg : ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (g (b m))))
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ g (b m) (v m) (w m)) :=
  fun m ↦ contMDiffAt_metricSection_apply₂ (hg m) (hv m) (hw m)

end

section ParamBilin

/-!
### The genuinely parameter-dependent bilinear form

For a *time-dependent* metric the fibrewise bilinear form depends on the full parameter `m` (which
carries the time coordinate), not merely on the base point `b m`.  We therefore also record the
version whose bilinear-form section `ψ : ∀ m, E (b m) →L[ℝ] E (b m) →L[ℝ] ℝ` is an arbitrary function
of the parameter (its fibre still living over `b m`).  Instantiating `M := ℝ × M`, `b := Prod.snd`,
and `ψ (t, x) := (g t).inner x` gives the joint `(t, x)` smoothness of a time-dependent metric
evaluated on two jointly-smooth sections — exactly the input the space-time Gram matrix needs.
-/

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ x, E (b x)} {s : Set M} {x : M}
  {ψ : ∀ m : M, E (b m) →L[ℝ] E (b m) →L[ℝ] ℝ}

/-- **Parameter-dependent bilinear form, within a set at a point.**  Here the bilinear-form section
`ψ m : E (b m) →L[ℝ] E (b m) →L[ℝ] ℝ` may depend on the full parameter `m` (its fibre over `b m`).
If it and two sections `v w` are `C^n` jointly in `m`, so is the scalar `m ↦ ψ m (v m) (w m)`. -/
lemma contMDiffWithinAt_paramBilin_apply₂
    (hψ : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (ψ m)) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ ψ m (v m) (w m)) s x := by
  have hres : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (ψ m (v m) (w m))) s x :=
    hψ.clm_bundle_apply₂ (F₁ := F) (F₂ := F) hv hw
  simp only [contMDiffWithinAt_totalSpace] at hres
  exact hres.2

/-- **Parameter-dependent bilinear form, at a point.** -/
lemma contMDiffAt_paramBilin_apply₂
    (hψ : ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (ψ m)) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ ψ m (v m) (w m)) x := by
  rw [← contMDiffWithinAt_univ] at hψ hv hw ⊢
  exact contMDiffWithinAt_paramBilin_apply₂ hψ hv hw

/-- **Parameter-dependent bilinear form, on a set.** -/
lemma contMDiffOn_paramBilin_apply₂
    (hψ : ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (ψ m)) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ ψ m (v m) (w m)) s :=
  fun m hm ↦ contMDiffWithinAt_paramBilin_apply₂ (hψ m hm) (hv m hm) (hw m hm)

/-- **Parameter-dependent bilinear form, everywhere.** -/
lemma contMDiff_paramBilin_apply₂
    (hψ : ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] E y →L[ℝ] ℝ)) (b m) (ψ m)))
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (w m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ ψ m (v m) (w m)) :=
  fun m ↦ contMDiffAt_paramBilin_apply₂ (hψ m) (hv m) (hw m)

end ParamBilin

section ParamLinear

/-!
### A parameter-dependent linear form

For the DeTurck one-form pairing `b(t, x)ⱼ = ω_t(x)(frameⱼ)` we need the *linear* analogue: a section
`φ : ∀ m, E (b m) →L[ℝ] ℝ` of the dual bundle, depending on the full parameter `m`, applied to a
jointly-smooth section.  This is `clm_bundle_apply` into the trivial `ℝ`-bundle followed by reading
off the fibre component.
-/

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℝ (E x)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v : ∀ x, E (b x)} {s : Set M} {x : M}
  {φ : ∀ m : M, E (b m) →L[ℝ] ℝ}

/-- **Parameter-dependent linear form, within a set at a point.**  A jointly-smooth dual-bundle
section `φ m : E (b m) →L[ℝ] ℝ` applied to a jointly-smooth section `v m` gives a jointly-smooth
scalar `m ↦ φ m (v m)`. -/
lemma contMDiffWithinAt_paramLinear_apply
    (hφ : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] ℝ)) (b m) (φ m)) s x)
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s x) :
    ContMDiffWithinAt IM 𝓘(ℝ) n (fun m ↦ φ m (v m)) s x := by
  have hres : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ)) n
      (fun m ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial B ℝ) (b m) (φ m (v m))) s x :=
    hφ.clm_bundle_apply (F₁ := F) hv
  simp only [contMDiffWithinAt_totalSpace] at hres
  exact hres.2

/-- **Parameter-dependent linear form, at a point.** -/
lemma contMDiffAt_paramLinear_apply
    (hφ : ContMDiffAt IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] ℝ)) (b m) (φ m)) x)
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) x) :
    ContMDiffAt IM 𝓘(ℝ) n (fun m ↦ φ m (v m)) x := by
  rw [← contMDiffWithinAt_univ] at hφ hv ⊢
  exact contMDiffWithinAt_paramLinear_apply hφ hv

/-- **Parameter-dependent linear form, on a set.** -/
lemma contMDiffOn_paramLinear_apply
    (hφ : ContMDiffOn IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] ℝ)) (b m) (φ m)) s)
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E)) s) :
    ContMDiffOn IM 𝓘(ℝ) n (fun m ↦ φ m (v m)) s :=
  fun m hm ↦ contMDiffWithinAt_paramLinear_apply (hφ m hm) (hv m hm)

/-- **Parameter-dependent linear form, everywhere.** -/
lemma contMDiff_paramLinear_apply
    (hφ : ContMDiff IM (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun m ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (E y →L[ℝ] ℝ)) (b m) (φ m)))
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, F)) n (fun m ↦ (v m : TotalSpace F E))) :
    ContMDiff IM 𝓘(ℝ) n (fun m ↦ φ m (v m)) :=
  fun m ↦ contMDiffAt_paramLinear_apply (hφ m) (hv m)

end ParamLinear

end PoincareCurvature.ParametrizedInner
