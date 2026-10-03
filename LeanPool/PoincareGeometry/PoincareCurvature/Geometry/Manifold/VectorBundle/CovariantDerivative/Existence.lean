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

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Topology.VectorBundle.Constructions

/-!
# Existence of covariant derivatives

This file constructs local flat covariant derivatives from trivializations, then globalizes them via
a smooth partition of unity. The resulting theorem only gives existence of some affine connection; it
does not yet solve the Levi-Civita correction problem.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V]

lemma extDerivFun_inCoordinates_eq_inTangentCoordinates [IsManifold I 1 M]
    {g : M → ℝ} {x₀ x : M} (hx : x ∈ (chartAt H x₀).source) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x
      (_root_.mvfderiv (I := I) g x) =
        inTangentCoordinates I 𝓘(ℝ) id g (mfderiv% g) x₀ x := by
  dsimp [inTangentCoordinates]
  rw [ContinuousLinearMap.inCoordinates_eq hx (by simpa [chartAt_self_eq])]
  rw [ContinuousLinearMap.inCoordinates_eq hx (by simpa [chartAt_self_eq])]
  simp [_root_.mvfderiv, Trivialization.coe_continuousLinearEquivAt_eq']
  ext v
  rw [Trivialization.coe_continuousLinearEquivAt_eq'
    (e := trivializationAt ℝ (TangentSpace 𝓘(ℝ, ℝ)) (g x₀)) (R := ℝ) (b := g x)
    (by
      rw [TangentBundle.trivializationAt_baseSet]
      simp [chartAt_self_eq])]
  rw [TangentBundle.continuousLinearMapAt_model_space]
  rfl

/-- A `C^n` scalar function has a `C^m` exterior derivative section whenever `m + 1 ≤ n`. -/
theorem ContMDiffAt.extDerivSection [IsManifold I 1 M]
    {m n : WithTop ℕ∞} {g : M → ℝ} {x₀ : M}
    (hg : ContMDiffAt I 𝓘(ℝ) n g x₀) (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (_root_.mvfderiv (I := I) g x)) x₀ := by
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let F : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E (TangentSpace I) ℝ (fun _ : M ↦ ℝ) x₀ x x₀ x
      (_root_.mvfderiv (I := I) g x)
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) m F x₀
  have hchart : ∀ᶠ x in 𝓝 x₀, x ∈ (chartAt H x₀).source := by
    exact (chartAt H x₀).open_source.mem_nhds (mem_chart_source H x₀)
  have hF :
      F =ᶠ[𝓝 x₀] inTangentCoordinates I 𝓘(ℝ) id g (mfderiv% g) x₀ := by
    filter_upwards [hchart] with x hx
    exact extDerivFun_inCoordinates_eq_inTangentCoordinates (I := I) (g := g) hx
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hF
  exact ContMDiffAt.mfderiv_const (I := I) (I' := 𝓘(ℝ)) (f := g) (m := m) hg hmn

theorem ContMDiff.extDerivSection [IsManifold I 1 M]
    {m n : WithTop ℕ∞} {g : M → ℝ}
    (hg : ContMDiff I 𝓘(ℝ) n g) (hmn : m + 1 ≤ n) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) m
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) x (_root_.mvfderiv (I := I) g x)) := by
  intro x
  exact (hg x).extDerivSection (I := I) (E := E) hmn

local notation "TStar" => (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] V x)

namespace ContinuousLinearMap

lemma inCoordinates_smulRight_eq [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    {x₀ x : M} {φ : TangentSpace I x →L[ℝ] ℝ} {v : V x}
    (hxT : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hxV : x ∈ (trivializationAt F V x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
        (φ.smulRight v) =
      (ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hxV) v) := by
  ext u
  have hleft :
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
          (φ.smulRight v) u =
        ((trivializationAt F V x₀)
          (TotalSpace.mk' F x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := by
    calc
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
          (φ.smulRight v) u =
          φ ((Trivialization.continuousLinearEquivAt ℝ
            (trivializationAt E (TangentSpace I : M → Type _) x₀) x hxT).symm u) •
            ((trivializationAt F V x₀) (TotalSpace.mk' F x v)).2 := by
        simpa [ContinuousLinearMap.smulRight_apply] using congrArg (fun L : E →L[ℝ] F => L u)
          (ContinuousLinearMap.inCoordinates_eq (F := E) (E := (TangentSpace I : M → Type _))
            (F' := F) (E' := V) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
            (ϕ := φ.smulRight v) hxT hxV)
      _ = ((trivializationAt F V x₀)
          (TotalSpace.mk' F x <|
            φ ((Trivialization.continuousLinearEquivAt ℝ
              (trivializationAt E (TangentSpace I : M → Type _) x₀) x hxT).symm u) • v)).2 := by
        symm
        simpa using
          (((trivializationAt F V x₀).linear (R := ℝ) hxV).map_smul
            (φ ((Trivialization.continuousLinearEquivAt ℝ
              (trivializationAt E (TangentSpace I : M → Type _) x₀) x hxT).symm u)) v)
  have hphi :
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ u =
        φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
          hxT).symm u) := by
    simpa using congrArg (fun L : E →L[ℝ] ℝ => L u)
      (ContinuousLinearMap.inCoordinates_eq (F := E) (E := (TangentSpace I : M → Type _))
        (F' := ℝ) (E' := fun _ : M ↦ ℝ) (x₀ := x₀) (x := x) (y₀ := x₀) (y := x)
        (ϕ := φ) hxT (by simp))
  have hsymm :
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxT).symm u =
        (trivializationAt E (TangentSpace I : M → Type _) x₀).symm x u := by
    simpa using
      (Trivialization.symm_continuousLinearEquivAt_eq
        (e := trivializationAt E (TangentSpace I : M → Type _) x₀) (R := ℝ) (b := x) hxT u)
  let a : ℝ := φ ((trivializationAt E (TangentSpace I : M → Type _) x₀).symm x u)
  have hsmulV :
      ((trivializationAt F V x₀) (TotalSpace.mk' F x (a • v))).2 =
        a • ((trivializationAt F V x₀) (TotalSpace.mk' F x v)).2 := by
    simpa using ((trivializationAt F V x₀).linear (R := ℝ) hxV).map_smul a v
  calc
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
        (φ.smulRight v) u
      = ((trivializationAt F V x₀)
          (TotalSpace.mk' F x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := hleft
    _ = a • ((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hsymm]
          simpa [a] using hsmulV
    _ = ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ u •
        ((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hphi, hsymm]
    _ = ((ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt F V x₀).continuousLinearEquivAt ℝ x hxV) v)) u := by
          simp [ContinuousLinearMap.smulRight_apply]

end ContinuousLinearMap

theorem ContMDiffAt.smulRightSection [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, V x} {x₀ : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) x₀)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, F)) 1
      (fun x ↦ TotalSpace.mk' F x (v x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x))) x₀ := by
  rw [contMDiffAt_hom_bundle (IB := I) (IM := I) (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
    (F₂ := F) (E₂ := V)
    (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x)))]
  refine ⟨contMDiffAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) 1
    (fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
      ((φ x).smulRight (v x))) x₀
  let Φ : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
      x₀ x x₀ x (φ x)
  let Vc : M → F := fun x ↦ ((trivializationAt F V x₀) (TotalSpace.mk' F x (v x))).2
  have hΦ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) 1 Φ x₀ := by
    simpa [Φ] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
        (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x))).mp hφ).2)
  have hxV : x₀ ∈ (trivializationAt F V x₀).baseSet := mem_baseSet_trivializationAt F V x₀
  have hVc : ContMDiffAt I 𝓘(ℝ, F) 1 Vc x₀ := by
    simpa [Vc] using ((trivializationAt F V x₀).contMDiffAt_section_iff (n := 1) hxV).mp hv
  have hcoord :
      (fun x ↦
        (ContinuousLinearMap.smulRightL ℝ E F) (Φ x) (Vc x)) =ᶠ[𝓝 x₀]
      (fun x ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
          ((φ x).smulRight (v x))) := by
    have hT :
        ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      exact (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀)
    have hV : ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt F V x₀).baseSet := by
      exact (trivializationAt F V x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V x₀)
    filter_upwards [hT, hV] with x hxT hxV
    rw [ContinuousLinearMap.inCoordinates_smulRight_eq (I := I) (V := V) hxT hxV]
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hcoord.symm
  exact (contMDiffAt_const.clm_apply hΦ).clm_apply hVc

theorem ContMDiffOn.smulRightSection [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, V x} {s : Set M}
    (hs : IsOpen s)
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) s)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 1
      (fun x ↦ TotalSpace.mk' F x (v x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x))) s := by
  intro x hx
  exact (ContMDiffAt.smulRightSection
    ((hφ x hx).contMDiffAt (hs.mem_nhds hx))
    ((hv x hx).contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

/-- **Level-generic version of `ContMDiffAt.smulRightSection`.** For any smoothness level `n`, the
scalar-right multiplication `φ ↦ φ.smulRight v` of a `C^n` cotangent-valued section `φ` with a `C^n`
bundle section `v` is a `C^n` hom-bundle section. This is the `smulRight`-product regularity input
that lowers the regularity of a covariant derivative by exactly one order (used to run the frame
covariant-derivative regularity at levels below the hard-coded `2 → 1`). -/
theorem ContMDiffAt.smulRightSection_of_level {n : WithTop ℕ∞}
    [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, V x} {x₀ : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) x₀)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (v x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x))) x₀ := by
  rw [contMDiffAt_hom_bundle (IB := I) (IM := I) (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
    (F₂ := F) (E₂ := V)
    (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x)))]
  refine ⟨contMDiffAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] F) n
    (fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
      ((φ x).smulRight (v x))) x₀
  let Φ : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
      x₀ x x₀ x (φ x)
  let Vc : M → F := fun x ↦ ((trivializationAt F V x₀) (TotalSpace.mk' F x (v x))).2
  have hΦ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) n Φ x₀ := by
    simpa [Φ] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
        (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x))).mp hφ).2)
  have hxV : x₀ ∈ (trivializationAt F V x₀).baseSet := mem_baseSet_trivializationAt F V x₀
  have hVc : ContMDiffAt I 𝓘(ℝ, F) n Vc x₀ := by
    simpa [Vc] using ((trivializationAt F V x₀).contMDiffAt_section_iff (n := n) hxV).mp hv
  have hcoord :
      (fun x ↦
        (ContinuousLinearMap.smulRightL ℝ E F) (Φ x) (Vc x)) =ᶠ[𝓝 x₀]
      (fun x ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) F V x₀ x x₀ x
          ((φ x).smulRight (v x))) := by
    have hT :
        ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      exact (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀)
    have hV : ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt F V x₀).baseSet := by
      exact (trivializationAt F V x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F V x₀)
    filter_upwards [hT, hV] with x hxT hxV
    rw [ContinuousLinearMap.inCoordinates_smulRight_eq (I := I) (V := V) hxT hxV]
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hcoord.symm
  exact (contMDiffAt_const.clm_apply hΦ).clm_apply hVc

/-- **Level-generic version of `ContMDiffOn.smulRightSection`.** The `ContMDiffOn` form of
`ContMDiffAt.smulRightSection_of_level`. -/
theorem ContMDiffOn.smulRightSection_of_level {n : WithTop ℕ∞}
    [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, V x} {s : Set M}
    (hs : IsOpen s)
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) s)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
      (fun x ↦ TotalSpace.mk' F x (v x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x ((φ x).smulRight (v x))) s := by
  intro x hx
  exact (ContMDiffAt.smulRightSection_of_level
    ((hφ x hx).contMDiffAt (hs.mem_nhds hx))
    ((hv x hx).contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

namespace Bundle.Trivialization

section Local

variable [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I 1 M]
  [ContMDiffVectorBundle 1 F V I]
  {ι : Type*} [Fintype ι]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Module.Basis ι ℝ F)

/-- The flat covariant derivative attached to a local frame coming from a trivialization. -/
def frameCovariantDerivative (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [MemTrivializationAtlas e] (b : Module.Basis ι ℝ F) :
    (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
  fun σ x ↦
    ∑ i : ι, (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
      (e.localFrame b i x)

theorem isCovariantDerivativeOn_frameCovariantDerivative
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) :
    IsCovariantDerivativeOn F (frameCovariantDerivative (I := I) e b) e.baseSet := by
  classical
  refine
    { add := ?_
      leibniz := ?_ }
  · intro σ τ x hσ hτ hx
    have hcoeffσ :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hcoeffτ :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrameCoeff I e b i)) τ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := τ) hx hτ i
    calc
      frameCovariantDerivative (I := I) e b (σ + τ) x
          = ∑ i : ι,
              (mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) (σ + τ)) x).smulRight
                (e.localFrame b i x) := rfl
      _ = ∑ i : ι,
            ((mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x).smulRight
                (e.localFrame b i x) +
              (mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) τ) x).smulRight
                (e.localFrame b i x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcoord :
                  mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y + τ y)) x =
                    mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y)) x +
                      mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (τ y)) x := by
                have hfun :
                    (fun y ↦ (localFrameCoeff I e b i y) (σ y + τ y)) =
                      (fun y ↦ (localFrameCoeff I e b i y) (σ y)) +
                        (fun y ↦ (localFrameCoeff I e b i y) (τ y)) := by
                  funext y
                  simp [map_add]
                rw [hfun]
                exact mvfderiv_add (I := I)
                  (g := fun y ↦ (localFrameCoeff I e b i y) (σ y))
                  (g' := fun y ↦ (localFrameCoeff I e b i y) (τ y)) (hcoeffσ i) (hcoeffτ i)
              calc
                (mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y + τ y)) x).smulRight
                    (e.localFrame b i x)
                    = (mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y)) x +
                        mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (τ y)) x).smulRight
                        (e.localFrame b i x) := by
                          simpa using congrArg (fun A ↦ A.smulRight (e.localFrame b i x)) hcoord
                _ = (mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y)) x).smulRight
                      (e.localFrame b i x) +
                    (mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (τ y)) x).smulRight
                      (e.localFrame b i x) := by
                        ext w
                        simp [ContinuousLinearMap.smulRight_apply, add_smul]
      _ = frameCovariantDerivative (I := I) e b σ x +
            frameCovariantDerivative (I := I) e b τ x := by
              simp [frameCovariantDerivative, Finset.sum_add_distrib]
  · intro σ g x hσ hg hx
    ext v
    have hcoeff :
        ∀ i, MDiffAt ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hprod :
        ∀ i,
          mvfderiv (I := I)
              ((LinearMap.piApply (localFrameCoeff I e b i)) (g • σ)) x v
            = g x * mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v
                + ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x
                    * mvfderiv (I := I) g x v := by
      intro i
      have hs :
          ((LinearMap.piApply (localFrameCoeff I e b i)) (g • σ)) =
            fun y ↦ g y * ((LinearMap.piApply (localFrameCoeff I e b i)) σ) y := by
        funext y
        simp [LinearMap.piApply_apply, Pi.smul_apply, map_smul]
      have hi :
          mvfderiv (I := I) (fun y ↦ g y * (localFrameCoeff I e b i y) (σ y)) x =
            g x • mvfderiv (I := I) (fun y ↦ (localFrameCoeff I e b i y) (σ y)) x +
              (localFrameCoeff I e b i x) (σ x) • mvfderiv (I := I) g x := by
        have hfun :
            (fun y ↦ g y * (localFrameCoeff I e b i y) (σ y)) =
              g * (fun y ↦ (localFrameCoeff I e b i y) (σ y)) := by
          funext y
          rfl
        rw [hfun]
        exact mvfderiv_mul (I := I) (x := x) (f := g)
          (g := fun y ↦ (localFrameCoeff I e b i y) (σ y)) hg (hcoeff i)
      simpa [hs, ContinuousLinearMap.smulRight_apply, mul_comm, mul_left_comm,
        mul_assoc] using congr(($hi v))
    have hframe :
        ∑ i : ι, ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x • e.localFrame b i x = σ x := by
      simpa [LinearMap.piApply_apply] using (e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
        (s := σ) (x' := x) hx).symm
    have hframeCov :
        ∑ i : ι, mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v •
            e.localFrame b i x =
          frameCovariantDerivative (I := I) e b σ x v := by
      simp [frameCovariantDerivative, ContinuousLinearMap.smulRight_apply]
    calc
      frameCovariantDerivative (I := I) e b (g • σ) x v
          = ∑ i,
              (g x * mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v
                + ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x * mvfderiv (I := I) g x v) •
                e.localFrame b i x := by
              simp [frameCovariantDerivative]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [ContinuousLinearMap.smulRight_apply] using
                congrArg (fun a ↦ a • e.localFrame b i x) (hprod i)
      _ = ∑ i : ι,
            (g x * mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v) •
              e.localFrame b i x
          + ∑ i : ι,
              (((LinearMap.piApply (localFrameCoeff I e b i)) σ) x * mvfderiv (I := I) g x v) •
                e.localFrame b i x := by
              simp_rw [add_smul]
              rw [Finset.sum_add_distrib]
      _ = g x • ∑ i : ι,
            mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v •
              e.localFrame b i x
          + mvfderiv (I := I) g x v • ∑ i : ι,
              ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x • e.localFrame b i x := by
              congr 1
              · calc
                  ∑ i : ι,
                      (g x * mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          g x •
                            (mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g x • ∑ i : ι,
                        mvfderiv (I := I) ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x v •
                          e.localFrame b i x := by
                            rw [Finset.smul_sum]
              · calc
                  ∑ i : ι,
                      (((LinearMap.piApply (localFrameCoeff I e b i)) σ) x * mvfderiv (I := I) g x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          mvfderiv (I := I) g x v •
                            (((LinearMap.piApply (localFrameCoeff I e b i)) σ) x •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [mul_comm, smul_smul]
                  _ = mvfderiv (I := I) g x v • ∑ i : ι,
                        ((LinearMap.piApply (localFrameCoeff I e b i)) σ) x • e.localFrame b i x := by
                            rw [Finset.smul_sum]
        _ = g x • frameCovariantDerivative (I := I) e b σ x v + mvfderiv (I := I) g x v • σ x := by
             rw [hframeCov, hframe]

theorem covariantDerivative_eq_frameCovariantDerivative_add_difference
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) (cov : CovariantDerivative I F V)
    {σ : Π x : M, V x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    cov σ x =
      frameCovariantDerivative (I := I) e b σ x +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
          (s := e.baseSet) x) (σ x) := by
  have hdiff :=
    IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
      (s := e.baseSet) (x := x) (hx := hx) (σ := σ) (hσ := hσ)
  calc
    cov σ x = (cov σ x - frameCovariantDerivative (I := I) e b σ x) +
        frameCovariantDerivative (I := I) e b σ x := (sub_add_cancel _ _).symm
    _ = frameCovariantDerivative (I := I) e b σ x +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
          (s := e.baseSet) x) (σ x) := by
            rw [← hdiff]
            abel

theorem covariantDerivative_apply_eq_frameCovariantDerivative_apply_add_difference
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) (cov : CovariantDerivative I F V)
    {σ : Π x : M, V x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      frameCovariantDerivative (I := I) e b σ x v +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
          (s := e.baseSet) x) (σ x) v := by
  simpa using congrArg (fun A ↦ A v) <|
    e.covariantDerivative_eq_frameCovariantDerivative_add_difference
      (I := I) b cov hx hσ

theorem covariantDerivative_apply_eq_sum_localFrame_add_difference
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) (cov : CovariantDerivative I F V)
    {σ : Π x : M, V x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      (∑ i : ι,
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
          e.localFrame b i x) +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
          (s := e.baseSet) x) (σ x) v := by
  simpa [frameCovariantDerivative, ContinuousLinearMap.smulRight_apply] using
    e.covariantDerivative_apply_eq_frameCovariantDerivative_apply_add_difference
      (I := I) b cov hx hσ v

theorem frameCovariantDerivative_localFrame_eq_zero
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) {j : ι} {x : M} (hx : x ∈ e.baseSet) :
    frameCovariantDerivative (I := I) e b (e.localFrame b j) x = 0 := by
  classical
  ext v
  simp [frameCovariantDerivative, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  have hcoeff :
      (fun y ↦ (e.localFrameCoeff I b i y) (e.localFrame b j y)) =ᶠ[𝓝 x]
        (fun _ : M ↦ if i = j then 1 else 0) := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with y hy
    have hrepr :
        (e.basisAt b hy).repr (e.localFrame b j y) i = if i = j then 1 else 0 := by
      rw [e.localFrame_apply_of_mem_baseSet (b := b) hy]
      simp [Module.Basis.repr_self, Finsupp.single_apply, eq_comm]
    exact
      (e.localFrameCoeff_apply_of_mem_baseSet (I := I) (b := b) hy (s := e.localFrame b j) i).trans
        hrepr
  let c : ℝ := if i = j then 1 else 0
  have hconst : HasMFDerivAt I 𝓘(ℝ) (fun _ : M ↦ c) x 0 := by
    simpa [c] using (hasMFDerivAt_const (I := I) (I' := 𝓘(ℝ)) (x := x) (c := c))
  have hcoeff' :
      HasMFDerivAt I 𝓘(ℝ) (fun y ↦ (e.localFrameCoeff I b i y) (e.localFrame b j y)) x 0 :=
    hconst.congr_of_eventuallyEq hcoeff
  have hv0 :
      ((mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (e.localFrame b j y)) x) v) = 0 := by
    simp [mvfderiv, hcoeff'.mfderiv]
  rw [hv0]
  simp

theorem difference_localFrame_eq_covariantDerivative
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) (cov : CovariantDerivative I F V)
    {j : ι} {x : M} (hx : x ∈ e.baseSet) :
    (IsCovariantDerivativeOn.difference
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
      (s := e.baseSet) x) (e.localFrame b j x) =
        cov (e.localFrame b j) x := by
  have hdiff :=
    IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
      (s := e.baseSet) (x := x) (hx := hx) (σ := e.localFrame b j)
      (hσ := (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := (1 : WithTop ℕ∞)) j hx).mdifferentiableAt one_ne_zero)
  simpa [e.frameCovariantDerivative_localFrame_eq_zero (I := I) b hx] using hdiff

theorem covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
    (b : Module.Basis ι ℝ F) (cov : CovariantDerivative I F V)
    {σ : Π x : M, V x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      ∑ i : ι,
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
      ∑ i : ι,
        ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • cov (e.localFrame b i) x v := by
  let A :=
    IsCovariantDerivativeOn.difference
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := e.isCovariantDerivativeOn_frameCovariantDerivative (I := I) b)
      (s := e.baseSet)
  have hframe :
      ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • e.localFrame b i x = σ x := by
    simpa [LinearMap.piApply_apply] using
      (e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := σ) (x' := x) hx).symm
  have hdiff :
      A x (σ x) v =
        ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • cov (e.localFrame b i) x v := by
    have hlin :
        A x (σ x) = ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • A x (e.localFrame b i x) := by
      rw [← hframe]
      simp [A, map_sum]
    calc
      A x (σ x) v
          = (∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
              A x (e.localFrame b i x)) v := by rw [hlin]
      _ = ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
            (A x (e.localFrame b i x) v) := by
            simp [Pi.smul_apply]
      _ = ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
            cov (e.localFrame b i) x v := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [e.difference_localFrame_eq_covariantDerivative (I := I) b cov hx]
  calc
    cov σ x v
        = ∑ i : ι,
            mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
          A x (σ x) v := by
            simpa using
              e.covariantDerivative_apply_eq_sum_localFrame_add_difference (I := I) b cov hx hσ v
    _ = ∑ i : ι,
          mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
        ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
          cov (e.localFrame b i) x v := by rw [hdiff]

end Local

section Regularity

variable [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I 2 M]
  [ContMDiffVectorBundle 2 F V I]
  {ι : Type*} [Fintype ι]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Module.Basis ι ℝ F)

theorem contMDiffOn_frameCovariantDerivative {σ : Π x : M, V x}
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (fun x ↦ TotalSpace.mk' F x (σ x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x
        (frameCovariantDerivative (I := I) e b σ x)) u := by
  classical
  simpa [frameCovariantDerivative] using
    (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦ by
      have hcoeff : ContMDiffOn I 𝓘(ℝ) 2 ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) u :=
        contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) hu hu' hσ i
      have hext : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 1
          (fun x ↦
            TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
              (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x)) u := by
        intro x hx
        exact (((hcoeff x hx).contMDiffAt (hu.mem_nhds hx)).extDerivSection
          (I := I) (E := E) (m := 1) (n := 2)
          (show (1 : WithTop ℕ∞) + 1 ≤ (2 : WithTop ℕ∞) by norm_num)).contMDiffWithinAt
      have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 1
          (fun x ↦ TotalSpace.mk' F x (e.localFrame b i x)) u := by
        exact
          (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
            (n := (1 : WithTop ℕ∞)) (b := b) i).mono hu'
      exact ContMDiffOn.smulRightSection (I := I) (V := V) hu hext hframe)

theorem contMDiffOn_frameCovariantDerivative_baseSet {σ : Π x : M, V x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (fun x ↦ TotalSpace.mk' F x (σ x)) e.baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x
        (frameCovariantDerivative (I := I) e b σ x)) e.baseSet := by
  exact e.contMDiffOn_frameCovariantDerivative (I := I) b e.open_baseSet (subset_refl _) hσ

theorem contMDiffCovariantDerivativeOn_frameCovariantDerivative :
    ContMDiffCovariantDerivativeOn F 1 (frameCovariantDerivative (I := I) e b) e.baseSet where
  contMDiff hσ := e.contMDiffOn_frameCovariantDerivative_baseSet (I := I) b hσ

end Regularity

section RegularityLevel

variable [FiniteDimensional ℝ F] [CompleteSpace F] [IsManifold I 1 M]
  {ι : Type*} [Fintype ι]
  (e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)) [MemTrivializationAtlas e]
  (b : Module.Basis ι ℝ F)

/-- **Level-generic frame covariant-derivative regularity.** Generalizes
`contMDiffOn_frameCovariantDerivative` (hard-coded `2 → 1`) to an arbitrary smoothness level `n`: a
`C^{n+1}` section has a `C^n` frame covariant derivative, since `frameCovariantDerivative` differs
`σ` by exactly one order (the `mvfderiv` step) and multiplies against the frame. The `n = 0`
instance (a `C¹` section has a `C⁰`, i.e. continuous, frame covariant derivative) is the regularity
drop needed to see the covariant derivative of a merely-`C¹` vector field as a continuous section. -/
theorem contMDiffOn_frameCovariantDerivative_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle (n + 1) F V I]
    {σ : Π x : M, V x}
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (n + 1) (fun x ↦ TotalSpace.mk' F x (σ x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x
        (frameCovariantDerivative (I := I) e b σ x)) u := by
  classical
  simpa [frameCovariantDerivative] using
    (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦ by
      have hcoeff : ContMDiffOn I 𝓘(ℝ) (n + 1)
          ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) u :=
        contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) hu hu' hσ i
      have hext : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
          (fun x ↦
            TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x
              (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x)) u := by
        intro x hx
        exact (((hcoeff x hx).contMDiffAt (hu.mem_nhds hx)).extDerivSection
          (I := I) (E := E) (m := n) (n := n + 1)
          (le_refl _)).contMDiffWithinAt
      have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, F)) n
          (fun x ↦ TotalSpace.mk' F x (e.localFrame b i x)) u := by
        exact
          (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
            (n := n) (b := b) i).mono hu'
      exact ContMDiffOn.smulRightSection_of_level (I := I) (V := V) hu hext hframe)

/-- `e.baseSet` version of `contMDiffOn_frameCovariantDerivative_of_level`. -/
theorem contMDiffOn_frameCovariantDerivative_baseSet_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle (n + 1) F V I]
    {σ : Π x : M, V x}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (n + 1)
      (fun x ↦ TotalSpace.mk' F x (σ x)) e.baseSet) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) x
        (frameCovariantDerivative (I := I) e b σ x)) e.baseSet := by
  exact e.contMDiffOn_frameCovariantDerivative_of_level (I := I) b e.open_baseSet
    (subset_refl _) hσ

/-- **Level-generic frame covariant-derivative class instance.** The frame covariant derivative is a
`C^n` covariant derivative on `e.baseSet` for every smoothness level `n` (given a `C^{n+1}`-regular
bundle). Specializing to `n = 0` gives the frame connection as a `C⁰` (continuous) covariant
derivative, which is the level-downgrade template for `ContMDiffCovariantDerivativeOn`. -/
theorem contMDiffCovariantDerivativeOn_frameCovariantDerivative_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle (n + 1) F V I] :
    ContMDiffCovariantDerivativeOn F n (frameCovariantDerivative (I := I) e b) e.baseSet where
  contMDiff hσ := e.contMDiffOn_frameCovariantDerivative_baseSet_of_level (I := I) b hσ

end RegularityLevel

end Bundle.Trivialization

namespace CovariantDerivative

section Global

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [IsManifold I ∞ M] [ContMDiffVectorBundle 1 F V I]
  [T2Space M] [SigmaCompactSpace M]

/-- Every finite-dimensional smooth real vector bundle over a Hausdorff σ-compact manifold admits a
global covariant derivative. -/
theorem nonempty : Nonempty (CovariantDerivative I F V) := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ F) ℝ F :=
    Module.Basis.ofVectorSpace ℝ F
  obtain ⟨ρ, hρ⟩ :
      ∃ ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M),
        ρ.IsSubordinate (fun x ↦ (trivializationAt F V x).baseSet) :=
    SmoothPartitionOfUnity.exists_isSubordinate (ι := M) (I := I) (M := M)
      (s := (Set.univ : Set M)) isClosed_univ
      (fun x ↦ (trivializationAt F V x).baseSet)
      (fun x ↦ (trivializationAt F V x).open_baseSet)
      (by
        intro x _
        exact Set.mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F V x⟩)
  let cov :
      (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
    fun σ x ↦
      ∑ i ∈ ρ.fintsupport x, ρ i x •
        Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ x
  let s : M → Set M := fun x ↦
    { y | ρ.fintsupport y ⊆ ρ.fintsupport x } ∩
      ⋂ i ∈ ρ.fintsupport x, (trivializationAt F V i).baseSet
  have hscover : ⋃ x, s x = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      refine Set.mem_iUnion.2 ⟨y, ?_⟩
      refine ⟨show ρ.fintsupport y ⊆ ρ.fintsupport y from subset_rfl, ?_⟩
      refine Set.mem_iInter.2 ?_
      intro i
      refine Set.mem_iInter.2 ?_
      intro hi
      exact hρ i ((ρ.mem_fintsupport_iff (x₀ := y) i).1 hi)
  have hcov : ∀ x, IsCovariantDerivativeOn F cov (s x) := by
    intro x
    refine
      { add := ?_
        leibniz := ?_ }
    · intro σ τ y hσ hτ hy
      have hySub : ρ.fintsupport y ⊆ ρ.fintsupport x := hy.1
      have hyBase :
          ∀ i ∈ ρ.fintsupport x, y ∈ (trivializationAt F V i).baseSet := by
        intro i hi
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 i) hi
      have hsum :
          cov (σ + τ) y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                (σ + τ) y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumσ :
          cov σ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumτ :
          cov τ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b τ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      rw [hsum, hsumσ, hsumτ]
      calc
        ∑ i ∈ ρ.fintsupport x, (ρ i) y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (σ + τ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  σ y +
                (ρ i) y •
                  Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                    τ y) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).add hσ hτ (hyBase i hi), smul_add]
        _ = ∑ i ∈ ρ.fintsupport x, (ρ i) y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + ∑ i ∈ ρ.fintsupport x, (ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  τ y := by
                rw [Finset.sum_add_distrib]
    · intro σ g y hσ hg hy
      have hySub : ρ.fintsupport y ⊆ ρ.fintsupport x := hy.1
      have hyBase :
          ∀ i ∈ ρ.fintsupport x, y ∈ (trivializationAt F V i).baseSet := by
        intro i hi
        exact Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 i) hi
      have hsum :
          ∑ i ∈ ρ.fintsupport x, ρ i y = 1 := by
        apply ρ.sum_finsupport'
        trivial
        exact (ρ.finsupport_subset_fintsupport (x₀ := y)).trans hySub
      have hsumσ :
          cov σ y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      have hsumgσ :
          cov (g • σ) y =
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                (g • σ) y := by
        unfold cov
        exact Finset.sum_subset hySub fun i hi hiy ↦ by
          have hρiy : ρ i y = 0 := by
            by_contra hne
            exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
              subset_closure (by simpa [Function.support] using hne))
          simp [hρiy]
      rw [hsumgσ, hsumσ]
      calc
        ∑ i ∈ ρ.fintsupport x, ρ i y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (g • σ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((g y * ρ i y) •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y +
                ρ i y • (mvfderiv (I := I) g y).smulRight (σ y)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).leibniz hσ hg (hyBase i hi), smul_add, smul_smul]
                rw [mul_comm]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + (∑ i ∈ ρ.fintsupport x, ρ i y) • (mvfderiv (I := I) g y).smulRight (σ y) := by
              rw [Finset.sum_add_distrib]
              congr 1
              · calc
                  ∑ i ∈ ρ.fintsupport x,
                      (g y * ρ i y) •
                        Bundle.Trivialization.frameCovariantDerivative (I := I)
                          (trivializationAt F V i) b σ y
                    = ∑ i ∈ ρ.fintsupport x,
                        g y •
                          ((ρ i y) •
                            Bundle.Trivialization.frameCovariantDerivative (I := I)
                              (trivializationAt F V i) b σ y) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g y • ∑ i ∈ ρ.fintsupport x,
                        (ρ i y) •
                          Bundle.Trivialization.frameCovariantDerivative (I := I)
                            (trivializationAt F V i) b σ y := by
                              rw [Finset.smul_sum]
              · rw [Finset.sum_smul]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              (trivializationAt F V i).frameCovariantDerivative (I := I) b σ y
            + (mvfderiv (I := I) g y).smulRight (σ y) := by
              rw [hsum]
              simp
  exact ⟨CovariantDerivative.ofIsCovariantDerivativeOnOfOpenCover
    (s := s) (cov := cov) hcov hscover⟩

end Global

section GlobalRegularity

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]

/-- Every finite-dimensional `C^{n+1}` real vector bundle over a Hausdorff σ-compact smooth
manifold admits a global `C^n` covariant derivative. -/
theorem contMDiff_nonempty_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle n F V I]
    [ContMDiffVectorBundle (n + 1) F V I] (hn : n ≤ ∞) :
    Nonempty { cov : CovariantDerivative I F V // ContMDiffCovariantDerivative cov n } := by
  classical
  let b : Module.Basis (Module.Basis.ofVectorSpaceIndex ℝ F) ℝ F :=
    Module.Basis.ofVectorSpace ℝ F
  obtain ⟨ρ, hρ⟩ :
      ∃ ρ : SmoothPartitionOfUnity M I M (Set.univ : Set M),
        ρ.IsSubordinate (fun x ↦ (trivializationAt F V x).baseSet) :=
    SmoothPartitionOfUnity.exists_isSubordinate (ι := M) (I := I) (M := M)
      (s := (Set.univ : Set M)) isClosed_univ
      (fun x ↦ (trivializationAt F V x).baseSet)
      (fun x ↦ (trivializationAt F V x).open_baseSet)
      (by
        intro x _
        exact Set.mem_iUnion.2 ⟨x, mem_baseSet_trivializationAt F V x⟩)
  let cov :
      (Π x : M, V x) → (Π x : M, TangentSpace I x →L[ℝ] V x) :=
    fun σ x ↦
      ∑ i ∈ ρ.fintsupport x, ρ i x •
        Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ x
  have hu :
      ∀ x : M,
        ∃ u : Set M, IsOpen u ∧ x ∈ u ∧
          u ⊆ { y | ρ.fintsupport y ⊆ ρ.fintsupport x } := by
    intro x
    rcases mem_nhds_iff.mp (ρ.eventually_fintsupport_subset x) with ⟨u, hsub, hu, hxu⟩
    exact ⟨u, hu, hxu, hsub⟩
  choose u huOpen hxu huSubset using hu
  let t : M → Set M := fun x ↦
    u x ∩ ⋂ i ∈ ρ.fintsupport x, (trivializationAt F V i).baseSet
  have htOpen : ∀ x, IsOpen (t x) := by
    intro x
    refine (huOpen x).inter ?_
    exact isOpen_biInter_finset fun i hi ↦ (trivializationAt F V i).open_baseSet
  have hxt : ∀ x, x ∈ t x := by
    intro x
    refine ⟨hxu x, ?_⟩
    refine Set.mem_iInter.2 ?_
    intro i
    refine Set.mem_iInter.2 ?_
    intro hi
    exact hρ i ((ρ.mem_fintsupport_iff (x₀ := x) i).1 hi)
  have htcover : ⋃ x, t x = Set.univ := by
    ext y
    constructor
    · intro _
      trivial
    · intro _
      exact Set.mem_iUnion.2 ⟨y, hxt y⟩
  have htSubset :
      ∀ {x y : M}, y ∈ t x → ρ.fintsupport y ⊆ ρ.fintsupport x := by
    intro x y hy
    exact huSubset x hy.1
  have htBase :
      ∀ {x y : M} {i : M}, y ∈ t x → i ∈ ρ.fintsupport x →
        y ∈ (trivializationAt F V i).baseSet := by
    intro x y i hy hi
    exact Set.mem_iInter.1 (Set.mem_iInter.1 hy.2 i) hi
  have htBaseSubset :
      ∀ {x i : M}, i ∈ ρ.fintsupport x → t x ⊆ (trivializationAt F V i).baseSet := by
    intro x i hi y hy
    exact htBase hy hi
  have hsum_eq :
      ∀ {σ : Π x : M, V x} {x y : M}, y ∈ t x →
        cov σ y =
          ∑ i ∈ ρ.fintsupport x, ρ i y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y := by
    intro σ x y hy
    unfold cov
    exact Finset.sum_subset (htSubset hy) fun i hi hiy ↦ by
      have hρiy : ρ i y = 0 := by
        by_contra hne
        exact hiy ((ρ.mem_fintsupport_iff (x₀ := y) i).2 <|
          subset_closure (by simpa [Function.support] using hne))
      simp [hρiy]
  have hcov : ∀ x, IsCovariantDerivativeOn F cov (t x) := by
    intro x
    refine
      { add := ?_
        leibniz := ?_ }
    · intro σ τ y hσ hτ hy
      rw [hsum_eq (σ := σ + τ) hy, hsum_eq (σ := σ) hy, hsum_eq (σ := τ) hy]
      calc
        ∑ i ∈ ρ.fintsupport x, (ρ i) y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (σ + τ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  σ y +
                (ρ i) y •
                  Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                    τ y) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).add hσ hτ (htBase hy hi), smul_add]
        _ = ∑ i ∈ ρ.fintsupport x, (ρ i) y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + ∑ i ∈ ρ.fintsupport x, (ρ i) y •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
                  τ y := by
                rw [Finset.sum_add_distrib]
    · intro σ g y hσ hg hy
      have hsum :
          ∑ i ∈ ρ.fintsupport x, ρ i y = 1 := by
        apply ρ.sum_finsupport'
        trivial
        exact (ρ.finsupport_subset_fintsupport (x₀ := y)).trans (htSubset hy)
      rw [hsum_eq (σ := g • σ) hy, hsum_eq (σ := σ) hy]
      calc
        ∑ i ∈ ρ.fintsupport x, ρ i y •
            Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b
              (g • σ) y
          = ∑ i ∈ ρ.fintsupport x,
              ((g y * ρ i y) •
                Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y +
                ρ i y • (mvfderiv (I := I) g y).smulRight (σ y)) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [(Bundle.Trivialization.isCovariantDerivativeOn_frameCovariantDerivative (I := I)
                  (e := trivializationAt F V i) b).leibniz hσ hg (htBase hy hi), smul_add, smul_smul]
                rw [mul_comm]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y
            + (∑ i ∈ ρ.fintsupport x, ρ i y) • (mvfderiv (I := I) g y).smulRight (σ y) := by
              rw [Finset.sum_add_distrib]
              congr 1
              · calc
                  ∑ i ∈ ρ.fintsupport x,
                      (g y * ρ i y) •
                        Bundle.Trivialization.frameCovariantDerivative (I := I)
                          (trivializationAt F V i) b σ y
                    = ∑ i ∈ ρ.fintsupport x,
                        g y •
                          ((ρ i y) •
                            Bundle.Trivialization.frameCovariantDerivative (I := I)
                              (trivializationAt F V i) b σ y) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g y • ∑ i ∈ ρ.fintsupport x,
                        (ρ i y) •
                          Bundle.Trivialization.frameCovariantDerivative (I := I)
                            (trivializationAt F V i) b σ y := by
                              rw [Finset.smul_sum]
              · rw [Finset.sum_smul]
        _ = g y • ∑ i ∈ ρ.fintsupport x, ρ i y •
              (trivializationAt F V i).frameCovariantDerivative (I := I) b σ y
            + (mvfderiv (I := I) g y).smulRight (σ y) := by
              rw [hsum]
              simp
  have hreg : ∀ x, ContMDiffCovariantDerivativeOn F n cov (t x) := by
    intro x
    have hlocal :
        ContMDiffCovariantDerivativeOn F n
          (fun σ y ↦
            ∑ i ∈ ρ.fintsupport x, ρ i y •
              Bundle.Trivialization.frameCovariantDerivative (I := I) (trivializationAt F V i) b σ y)
          (t x) := by
      refine ContMDiffCovariantDerivativeOn.finite_affine_combination ?_ ?_
      · intro i hi
        refine { contMDiff := ?_ }
        intro σ hσ
        simpa using
          (trivializationAt F V i).contMDiffOn_frameCovariantDerivative_of_level
            (I := I) (n := n) b
            (htOpen x) (htBaseSubset (x := x) hi) (hσ.mono (by intro y hy; trivial))
      · intro i hi
        simpa using
          (((ρ i).contMDiff.of_le hn).contMDiffOn :
            ContMDiffOn I 𝓘(ℝ) n (ρ i) (t x))
    refine { contMDiff := ?_ }
    intro σ hσ
    refine (hlocal.contMDiff (hσ.mono (by intro y hy; trivial))).congr ?_
    intro y hy
    congr 1
    exact hsum_eq hy
  let cov' : CovariantDerivative I F V :=
    CovariantDerivative.ofIsCovariantDerivativeOnOfOpenCover (F := F) (s := t) (cov := cov)
      hcov htcover
  refine ⟨cov', ?_⟩
  refine { contMDiff := ?_ }
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  refine ⟨t x, htOpen x, hxt x, ?_⟩
  simpa only [Set.univ_inter, cov',
    CovariantDerivative.ofIsCovariantDerivativeOnOfOpenCover] using
    (hreg x).contMDiff (hσ.mono (by intro y hy; trivial))

/-- Every finite-dimensional `C^2` real vector bundle over a Hausdorff σ-compact smooth manifold
admits a global `C^1` covariant derivative. -/
theorem contMDiff_nonempty [ContMDiffVectorBundle 2 F V I] :
    Nonempty { cov : CovariantDerivative I F V // ContMDiffCovariantDerivative cov 1 } := by
  haveI : ContMDiffVectorBundle (1 + 1) F V I := by
    exact ContMDiffVectorBundle.of_le (n := 2) (by norm_num)
  exact contMDiff_nonempty_of_level (I := I) (F := F) (V := V) (n := 1)
    (WithTop.coe_le_coe.mpr le_top)

/-- Every finite-dimensional `C^3` real vector bundle over a Hausdorff σ-compact smooth manifold
admits a global `C^2` covariant derivative. -/
theorem contMDiff_nonempty_two [ContMDiffVectorBundle 3 F V I] :
    Nonempty { cov : CovariantDerivative I F V // ContMDiffCovariantDerivative cov 2 } := by
  letI : ContMDiffVectorBundle 2 F V I :=
    ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  haveI : ContMDiffVectorBundle (2 + 1) F V I := by
    exact ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  exact contMDiff_nonempty_of_level (I := I) (F := F) (V := V) (n := 2)
    (WithTop.coe_le_coe.mpr le_top)

end GlobalRegularity

section LevelDowngrade

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [CompleteSpace F]
  [T2Space M] [IsManifold I ∞ M] [ContMDiffVectorBundle 2 F V I]

/-- **General-bundle class-to-set restriction of a `C²` covariant derivative.**
A globally `C²` covariant derivative restricts to a `C²` covariant
derivative on every open set.  The proof localizes a `C³` section with a
smooth bump, applies the global regularity class, and uses locality of the
covariant derivative on the region where the bump is one. -/
theorem contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
    [ContMDiffVectorBundle 3 F V I]
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov 2]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn F 2 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 3 ψ :=
    ψ.contMDiff.of_le (show (3 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, V y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 3 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := F) (V := V) (u := u)
        (n := (3 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 3 (T% τ) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 2).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (T% σ) y :=
      (((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero
    have hτy : MDiffAt (T% τ) y :=
      (hτ.contMDiffAt.of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy
      (hwopen.mem_nhds hy) (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := THom) (E →L[ℝ] F) y A)
      (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

/-- **General-bundle class-to-set restriction of a `C¹` covariant derivative.**  A globally `C¹`
covariant derivative (`ContMDiffCovariantDerivative cov 1`) restricts to a `C¹` covariant derivative
on every open set.  Proved by a smooth-bump localization: multiplying a `C²` section by a bump equal
to `1` near a point produces a globally `C²` section, whose covariant derivative is `C¹` by the class,
and which agrees with the original covariant derivative where the bump is `1`.  Bundle-generic version
of the tangent-bundle lemma in `LeviCivita.lean`; kept in the `RiemannianBundle`-free `Existence`
context so the frame decomposition can be applied without an instance diamond. -/
theorem contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn F 1 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 2 ψ := ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, V y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, F)) 2 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := F) (V := V) (u := u)
        (n := (2 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% τ) Set.univ := by
      simpa [contMDiffOn_univ] using hτ
    simpa [contMDiffOn_univ] using
      ((inferInstance : ContMDiffCovariantDerivative cov 1).contMDiff.contMDiff hτOn)
  have hψeq1 : {y : M | ψ y = 1} ∈ nhds x := by
    filter_upwards [ψ.eventuallyEq_one] with y hy
    simpa using hy
  rcases mem_nhds_iff.mp hψeq1 with ⟨w, hwsub, hwopen, hxw⟩
  have hwu : w ⊆ u := by
    intro y hy
    have hy1 : ψ y = 1 := hwsub hy
    have hysupp : y ∈ Function.support ψ := by
      simpa [Function.support] using show ψ y ≠ 0 by rw [hy1]; norm_num
    exact hψsupp hysupp
  have hEq : ∀ y ∈ w, cov σ y = cov τ y := by
    intro y hy
    have hyu : y ∈ u := hwu hy
    have hσy : MDiffAt (T% σ) y :=
      (((hσ y hyu).contMDiffAt (hu.mem_nhds hyu)).of_le
        (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    have hτy : MDiffAt (T% τ) y :=
      (hτ.contMDiffAt.of_le (by simp : (1 : WithTop ℕ∞) ≤ 2)).mdifferentiableAt one_ne_zero
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy (hwopen.mem_nhds hy)
      (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] F)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] F) (E := THom) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := THom) (E →L[ℝ] F) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

/-- **General-bundle covariant-derivative level downgrade `2 → 1`.** A globally `C²`
covariant derivative is a `C¹` covariant derivative on every open set.  The proof uses the
actual local-frame decomposition: the frame derivative of a `C²` section is `C¹`, while the
connection applied to each `C³` frame is `C²`; their coefficient-weighted sum is therefore
`C¹`. -/
theorem contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_two
    [ContMDiffVectorBundle 3 F V I]
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov 2]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn F 1 cov.toFun u := by
  classical
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let e := trivializationAt F V x
  let b := Module.finBasis ℝ F
  have hxbase : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  refine ⟨e.baseSet, e.open_baseSet, hxbase, ?_⟩
  haveI : ContMDiffVectorBundle 1 F V I :=
    ContMDiffVectorBundle.of_le (n := 3) (show (1 : WithTop ℕ∞) ≤ 3 by norm_num)
  haveI : ContMDiffVectorBundle (1 + 1) F V I := by
    exact ContMDiffVectorBundle.of_le (n := 3) (by norm_num)
  have hopen : IsOpen (u ∩ e.baseSet) := hu.inter e.open_baseSet
  have hsub : u ∩ e.baseSet ⊆ e.baseSet := Set.inter_subset_right
  have hσ2 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 2 (T% σ) (u ∩ e.baseSet) := by
    convert (show ContMDiffOn I (I.prod 𝓘(ℝ, F)) (1 + 1) (T% σ) u from hσ).mono
      Set.inter_subset_left using 1 <;> norm_num
  have hcov2 : ContMDiffCovariantDerivativeOn F 2 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
      (u := e.baseSet) e.open_baseSet
  have hσ12 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (1 + 1) (T% σ)
      (u ∩ e.baseSet) := by
    convert hσ2 using 1 <;> norm_num
  have hframe1 := Bundle.Trivialization.contMDiffOn_frameCovariantDerivative_of_level
    (I := I) (V := V) (n := 1) e b hopen hsub hσ12
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 2
      ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) (u ∩ e.baseSet) := fun i =>
    contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) hopen hsub hσ2 i
  have hframe3 : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, F)) (2 + 1)
      (T% (e.localFrame b i)) e.baseSet := fun i => by
    convert Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (3 : WithTop ℕ∞)) (b := b) i using 1 <;> norm_num
  have hcovframe := fun i => hcov2.contMDiff (hframe3 i)
  have hdiff1 := ContMDiffOn.sum_section (s := (Finset.univ : Finset _))
    (fun i (_ : i ∈ Finset.univ) =>
      ContMDiffOn.smul_section (n := (1 : WithTop ℕ∞))
        ((hcoeff i).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num))
        (((hcovframe i).mono hsub).of_le (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)))
  have htotal := ContMDiffOn.add_section hframe1 hdiff1
  refine htotal.congr fun y hy => ?_
  have hMDiff : MDiffAt (T% σ) y :=
    ((hσ2 y hy).contMDiffAt (hopen.mem_nhds hy)).mdifferentiableAt (by norm_num)
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  have hdec := e.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I) b cov hy.2 hMDiff v
  simpa [Bundle.Trivialization.frameCovariantDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply] using hdec

/-- A globally `C²` covariant derivative is also globally `C¹`. -/
theorem contMDiffCovariantDerivative_one_of_contMDiffCovariantDerivative_two
    [ContMDiffVectorBundle 3 F V I]
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov 2] :
    ContMDiffCovariantDerivative cov 1 :=
  ⟨contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_two
    (I := I) (F := F) (V := V) (u := Set.univ) isOpen_univ⟩

/-- **General-bundle covariant-derivative level downgrade `1 → 0`.**  A globally `C¹` covariant
derivative (`ContMDiffCovariantDerivative cov 1`) is a `C⁰` covariant derivative on every open set:
the covariant derivative of a merely-`C¹` section is a *continuous* `T*M ⊗ V`-section.  This is the
"any `C^{k+1}` covariant derivative is `C^k`" monotonicity for `k = 0` (an explicit Mathlib "later
file" TODO), proved from the local frame decomposition
`∇σ = ∇^{frame}σ + ∑ᵢ (coeffᵢ σ) · ∇(frameᵢ)`: the frame term is `C⁰` by
`contMDiffOn_frameCovariantDerivative_of_level`, and each `∇(frameᵢ)` is `C¹` because a `C²`-regular
bundle has `C²` local frames that probe the `C¹` class (via the class-to-set restriction).  Applying
to the tangent bundle: the covariant derivative of a `C¹` vector field is a continuous section — the
DeTurck-correction regularity input. -/
theorem contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
    {cov : CovariantDerivative I F V} [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn F 0 cov.toFun u := by
  classical
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let e := trivializationAt F V x
  let b := Module.finBasis ℝ F
  have hxbase : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  refine ⟨e.baseSet, e.open_baseSet, hxbase, ?_⟩
  haveI : ContMDiffVectorBundle 0 F V I :=
    ContMDiffVectorBundle.of_le (n := 2) (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  haveI : ContMDiffVectorBundle (0 + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 F V I)
  have hopen : IsOpen (u ∩ e.baseSet) := hu.inter e.open_baseSet
  have hsub : u ∩ e.baseSet ⊆ e.baseSet := Set.inter_subset_right
  have hσ1 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) 1 (T% σ) (u ∩ e.baseSet) := by
    simpa using (show ContMDiffOn I (I.prod 𝓘(ℝ, F)) (0 + 1) (T% σ) u from hσ).mono
      Set.inter_subset_left
  have hcov1 : ContMDiffCovariantDerivativeOn F 1 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (u := e.baseSet) e.open_baseSet
  have hσ01 : ContMDiffOn I (I.prod 𝓘(ℝ, F)) (0 + 1) (T% σ) (u ∩ e.baseSet) := by
    simpa using hσ1
  have hframe0 := Bundle.Trivialization.contMDiffOn_frameCovariantDerivative_of_level
    (I := I) (V := V) (n := 0) e b hopen hsub hσ01
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 1
      ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) (u ∩ e.baseSet) := fun i =>
    contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) hopen hsub hσ1 i
  have hframe2 : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, F)) (1 + 1)
      (T% (e.localFrame b i)) e.baseSet := fun i => by
    convert Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (2 : WithTop ℕ∞)) (b := b) i using 1 <;> norm_num
  have hcovframe := fun i => hcov1.contMDiff (hframe2 i)
  have hdiff0 := ContMDiffOn.sum_section (s := (Finset.univ : Finset _))
    (fun i (_ : i ∈ Finset.univ) =>
      ContMDiffOn.smul_section (n := (0 : WithTop ℕ∞))
        ((hcoeff i).of_le (show (0 : WithTop ℕ∞) ≤ 1 by norm_num))
        (((hcovframe i).mono hsub).of_le (show (0 : WithTop ℕ∞) ≤ 1 by norm_num)))
  have htotal := ContMDiffOn.add_section hframe0 hdiff0
  refine htotal.congr fun y hy => ?_
  have hMDiff : MDiffAt (T% σ) y :=
    ((hσ1 y hy).contMDiffAt (hopen.mem_nhds hy)).mdifferentiableAt one_ne_zero
  congr 1
  refine ContinuousLinearMap.ext fun v => ?_
  have hdec := e.covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I) b cov hy.2 hMDiff v
  simpa [Bundle.Trivialization.frameCovariantDerivative, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply] using hdec

end LevelDowngrade

end CovariantDerivative
