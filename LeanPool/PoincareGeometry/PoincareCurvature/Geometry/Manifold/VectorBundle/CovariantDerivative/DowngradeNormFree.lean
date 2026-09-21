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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Existence

/-!
# Fiber-norm-free tangent-bundle frame covariant-derivative regularity

The frame–covariant-derivative regularity chain in `Existence.lean` (culminating in the level
downgrade `CovariantDerivative.contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one`)
is stated in that file's variable context, which carries the auto-included — but genuinely *unused*
(the compiler reports them) — fiber-norm hypotheses `[∀ x, NormedAddCommGroup (V x)]` /
`[∀ x, NormedSpace ℝ (V x)]`.

To apply that chain to the geometric Ricci–DeTurck operator we need it at the **tangent bundle**
`V = TangentSpace I`.  There the *pointwise* `NormedAddCommGroup (TangentSpace I x)` is resolvable by
the bundle machinery through the synonym `TangentSpace I x = E`, but the *Π-instance*
`∀ x, NormedAddCommGroup (TangentSpace I x)` (which the `Existence` versions require, because their
building block `Bundle.Trivialization.frameCovariantDerivative` carries it in its signature) is **not**
synthesizable from the synonym.  Supplying it by hand (`RiemannianBundle`/`letI`) then yields a
defeq-but-not-syntactic diamond against the synonym norm used by the hom-bundle machinery.

This module re-establishes the frame covariant-derivative regularity **directly at the tangent
bundle**, with *no* Π fiber-norm hypothesis: it introduces a fiber-norm-free tangent-bundle copy
`frameCovariantDerivativeTangent` of `Bundle.Trivialization.frameCovariantDerivative`, and transcribes
the `smulRight`-product and frame regularity lemmas (specialized to `F = E`, `V = TangentSpace I`).
Every fiber-norm the proofs need is *pointwise* and resolves through the synonym uniformly, so no
diamond arises.  These are the fiber-norm-free building blocks the geometric-operator regularity (the
covariant derivative of a `C¹` vector field is a continuous `Hom(TM, TM)`-section) is assembled from.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TStar" => (fun x : M ↦ TangentSpace I x →L[ℝ] ℝ)
local notation "THom" => (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)

namespace CovariantDerivative
namespace TangentFrame

/-- Tangent-bundle copy of `ContinuousLinearMap.inCoordinates_smulRight_eq`. -/
lemma inCoordinates_smulRight_eq
    {x₀ x : M} {φ : TangentSpace I x →L[ℝ] ℝ} {v : TangentSpace I x}
    (hxT : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet)
    (hxV : x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) =
      (ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v) := by
  ext u
  have hleft :
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
          (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) u =
        ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (TotalSpace.mk' E x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := by
    calc
      ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
          (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) u
          = φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) •
              ((trivializationAt E (TangentSpace I : M → Type _) x₀)
                (TotalSpace.mk' E x v)).2 := by
            simpa [ContinuousLinearMap.smulRight_apply] using congrArg
              (fun L : E →L[ℝ] E => L u)
              (ContinuousLinearMap.inCoordinates_eq (F := E)
                (E := (TangentSpace I : M → Type _)) (F' := E)
                (E' := (TangentSpace I : M → Type _)) (x₀ := x₀) (x := x)
                (y₀ := x₀) (y := x) (ϕ := φ.smulRight v) hxT hxV)
      _ = ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (TotalSpace.mk' E x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := by
            symm
            simpa using ((trivializationAt E (TangentSpace I : M → Type _) x₀).linear
              (R := ℝ) hxV).map_smul
              (φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
                hxT).symm u)) v
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
      ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x (a • v))).2 =
        a • ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x v)).2 := by
    simpa using ((trivializationAt E (TangentSpace I : M → Type _) x₀).linear (R := ℝ) hxV).map_smul a v
  calc
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
        (TangentSpace I : M → Type _) x₀ x x₀ x (φ.smulRight v) u
      = ((trivializationAt E (TangentSpace I : M → Type _) x₀)
          (TotalSpace.mk' E x <|
            φ (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x
              hxT).symm u) • v)).2 := hleft
    _ = a • ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hsymm]
          simpa [a] using hsmulV
    _ = ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ u •
        ((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v := by
          rw [hphi, hsymm]
    _ = ((ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
          x₀ x x₀ x φ).smulRight
        (((trivializationAt E (TangentSpace I : M → Type _) x₀).continuousLinearEquivAt ℝ x hxV) v)) u := by
          simp [ContinuousLinearMap.smulRight_apply]

/-- Tangent-bundle copy of `ContMDiffAt.smulRightSection_of_level`. -/
theorem contMDiffAt_smulRightSection_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, TangentSpace I x} {x₀ : M}
    (hφ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) x₀)
    (hv : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (v x)) x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x))) x₀ := by
  rw [contMDiffAt_hom_bundle (IB := I) (IM := I) (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
    (F₂ := E) (E₂ := (TangentSpace I : M → Type _))
    (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x)))]
  refine ⟨contMDiffAt_id, ?_⟩
  change ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) n
    (fun x ↦ ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
      (TangentSpace I : M → Type _) x₀ x x₀ x ((φ x).smulRight (v x))) x₀
  let Φ : M → E →L[ℝ] ℝ := fun x ↦
    ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) ℝ (fun _ : M ↦ ℝ)
      x₀ x x₀ x (φ x)
  let Vc : M → E := fun x ↦
    ((trivializationAt E (TangentSpace I : M → Type _) x₀) (TotalSpace.mk' E x (v x))).2
  have hΦ : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) n Φ x₀ := by
    simpa [Φ] using
      (((contMDiffAt_hom_bundle
        (IB := I) (IM := I)
        (F₁ := E) (E₁ := (TangentSpace I : M → Type _))
        (F₂ := ℝ) (E₂ := fun _ : M ↦ ℝ)
        (f := fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x))).mp hφ).2)
  have hxV : x₀ ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet :=
    mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀
  have hVc : ContMDiffAt I 𝓘(ℝ, E) n Vc x₀ := by
    simpa [Vc] using
      ((trivializationAt E (TangentSpace I : M → Type _) x₀).contMDiffAt_section_iff (n := n) hxV).mp hv
  have hcoord :
      (fun x ↦
        (ContinuousLinearMap.smulRightL ℝ E E) (Φ x) (Vc x)) =ᶠ[𝓝 x₀]
      (fun x ↦
        ContinuousLinearMap.inCoordinates E (TangentSpace I : M → Type _) E
          (TangentSpace I : M → Type _) x₀ x x₀ x ((φ x).smulRight (v x))) := by
    have hT :
        ∀ᶠ x in 𝓝 x₀, x ∈ (trivializationAt E (TangentSpace I : M → Type _) x₀).baseSet := by
      exact (trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀)
    filter_upwards [hT] with x hxT
    rw [inCoordinates_smulRight_eq (I := I) hxT hxT]
    rfl
  refine ContMDiffAt.congr_of_eventuallyEq ?_ hcoord.symm
  exact (contMDiffAt_const.clm_apply hΦ).clm_apply hVc

/-- Tangent-bundle copy of `ContMDiffOn.smulRightSection_of_level`. -/
theorem contMDiffOn_smulRightSection_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    {φ : ∀ x, TangentSpace I x →L[ℝ] ℝ} {v : ∀ x, TangentSpace I x} {s : Set M}
    (hs : IsOpen s)
    (hφ : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := TStar) x (φ x)) s)
    (hv : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
      (fun x ↦ TotalSpace.mk' E x (v x)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x ((φ x).smulRight (v x))) s := by
  intro x hx
  exact (contMDiffAt_smulRightSection_of_level
    ((hφ x hx).contMDiffAt (hs.mem_nhds hx))
    ((hv x hx).contMDiffAt (hs.mem_nhds hx))).contMDiffWithinAt

/-- Fiber-norm-free tangent-bundle copy of `Bundle.Trivialization.frameCovariantDerivative`: the
local frame–connection expression `∑ᵢ d(coeffᵢ σ) ⊗ frameᵢ`, stated directly for the tangent bundle
so that no Π fiber-norm hypothesis is needed. -/
def frameCovariantDerivativeTangent
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E) :
    (Π x : M, TangentSpace I x) → (Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x) :=
  fun σ x ↦
    ∑ i : ι, (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
      (e.localFrame b i x)

/-- Tangent-bundle, fiber-norm-free copy of
`Bundle.Trivialization.contMDiffOn_frameCovariantDerivative_of_level`: on a trivialization patch the
frame covariant derivative of a `C^{n+1}` vector field is a `C^n` `Hom(TM, TM)`-section. -/
theorem contMDiffOn_frameCovariantDerivativeTangent_of_level {n : WithTop ℕ∞}
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle n E (TangentSpace I : M → Type _) I]
    [ContMDiffVectorBundle (n + 1) E (TangentSpace I : M → Type _) I]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M))
    [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {σ : Π x : M, TangentSpace I x}
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (n + 1) (fun x ↦ TotalSpace.mk' E x (σ x)) u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) x
        (frameCovariantDerivativeTangent (I := I) e b σ x)) u := by
  classical
  simpa [frameCovariantDerivativeTangent] using
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
      have hframe : ContMDiffOn I (I.prod 𝓘(ℝ, E)) n
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u := by
        exact
          (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
            (n := n) (b := b) i).mono hu'
      exact contMDiffOn_smulRightSection_of_level (I := I) hu hext hframe)

/-- Tangent-bundle copy of
`CovariantDerivative.contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two`: a
globally `C²` covariant derivative on the tangent bundle restricts to a `C²` covariant derivative on
every open set (needs no Π fiber-norm). -/
theorem contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
    [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 2]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 2 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 3 ψ :=
    ψ.contMDiff.of_le (show (3 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TangentSpace I y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u)
        (n := (3 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (T% τ) Set.univ := by
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
      (hτ.contMDiffAt.of_le (by simp : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero
    exact (cov.isCovariantDerivativeOn (s := w)).congr_of_eqOn hσy hτy (hwopen.mem_nhds hy)
      (fun z hz ↦ by
        have hz1 : ψ z = 1 := hwsub hz
        calc
          σ z = 1 • σ z := by simpa using (one_smul ℝ (σ z)).symm
          _ = ψ z • σ z := by simpa [hz1])
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := THom) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw

/-- Tangent-bundle copy of
`CovariantDerivative.contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one`: a
globally `C¹` covariant derivative on the tangent bundle restricts to a `C¹` covariant derivative on
every open set (needs no Π fiber-norm). -/
theorem contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 1 cov.toFun u := by
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  have hux : u ∈ nhds x := hu.mem_nhds hx
  obtain ⟨ψ, hψtsupp, hψsupp⟩ :=
    (SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hux).mem_iff.mp hux
  have hψ : ContMDiff I 𝓘(ℝ) 2 ψ := ψ.contMDiff.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide)
  let τ : Π y : M, TangentSpace I y := fun y ↦ ψ y • σ y
  have hτ : ContMDiff I (I.prod 𝓘(ℝ, E)) 2 (T% τ) := by
    simpa [τ] using
      (ContMDiffOn.smul_section_of_tsupport (I := I) (F := E)
        (V := (TangentSpace I : M → Type _)) (u := u)
        (n := (2 : WithTop ℕ∞)) (ψ := ψ) hψ.contMDiffOn hu hψtsupp hσ)
  have hcovτ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov τ y)) := by
    have hτOn : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% τ) Set.univ := by
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
  have hcovσw : ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E) (E := THom) y (cov σ y)) w := by
    refine ContMDiffOn.congr hcovτ.contMDiffOn ?_
    intro y hy
    exact congrArg (fun A ↦ TotalSpace.mk' (E := THom) (E →L[ℝ] E) y A) (hEq y hy)
  refine ⟨w, hwopen, hxw, ?_⟩
  simpa [Set.inter_eq_right.mpr hwu] using hcovσw


/-! ## Frame-decomposition cascade (fiber-norm-free) and the level 1-to-0 downgrade -/

theorem isCovariantDerivativeOn_frameCovariantDerivativeTangent
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) :
    IsCovariantDerivativeOn E (frameCovariantDerivativeTangent (I := I) e b) e.baseSet := by
  classical
  refine
    { add := ?_
      leibniz := ?_ }
  · intro σ τ x hσ hτ hx
    have hcoeffσ :
        ∀ i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hcoeffτ :
        ∀ i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) τ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := τ) hx hτ i
    calc
      frameCovariantDerivativeTangent (I := I) e b (σ + τ) x
          = ∑ i : ι,
              (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) (σ + τ)) x).smulRight
                (e.localFrame b i x) := rfl
      _ = ∑ i : ι,
            ((mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x).smulRight
                (e.localFrame b i x) +
              (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) τ) x).smulRight
                (e.localFrame b i x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hcoord :
                  mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y + τ y)) x =
                    mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y)) x +
                      mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (τ y)) x := by
                have hadd :
                    (fun y ↦ (e.localFrameCoeff I b i y) (σ y + τ y)) =
                      (fun y ↦ (e.localFrameCoeff I b i y) (σ y)) +
                        (fun y ↦ (e.localFrameCoeff I b i y) (τ y)) := by
                  funext y
                  simp [LinearMap.map_add]
                rw [hadd]
                exact mvfderiv_add (I := I)
                  (g := fun y ↦ (e.localFrameCoeff I b i y) (σ y))
                  (g' := fun y ↦ (e.localFrameCoeff I b i y) (τ y)) (hcoeffσ i) (hcoeffτ i)
              calc
                (mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y + τ y)) x).smulRight
                    (e.localFrame b i x)
                    = (mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y)) x +
                        mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (τ y)) x).smulRight
                        (e.localFrame b i x) := by
                          simpa using congrArg (fun A ↦ A.smulRight (e.localFrame b i x)) hcoord
                _ = (mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y)) x).smulRight
                      (e.localFrame b i x) +
                    (mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (τ y)) x).smulRight
                      (e.localFrame b i x) := by
                        ext w
                        simp [ContinuousLinearMap.smulRight_apply, add_smul]
      _ = frameCovariantDerivativeTangent (I := I) e b σ x +
            frameCovariantDerivativeTangent (I := I) e b τ x := by
              simp [frameCovariantDerivativeTangent, Finset.sum_add_distrib]
  · intro σ g x hσ hg hx
    ext v
    have hcoeff :
        ∀ i, MDiffAt ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x := by
      intro i
      exact mdifferentiableAt_localFrameCoeff (I := I) (e := e) (b := b) (s := σ) hx hσ i
    have hprod :
        ∀ i,
          mvfderiv (I := I)
              ((LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ)) x v
            = g x * mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v
                + ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x
                    * mvfderiv (I := I) g x v := by
      intro i
      have hs :
          ((LinearMap.piApply (e.localFrameCoeff I b i)) (g • σ)) =
            fun y ↦ g y * ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) y := by
        funext y
        simp [map_smul]
      have hi :
          mvfderiv (I := I) (fun y ↦ g y * (e.localFrameCoeff I b i y) (σ y)) x =
            g x • mvfderiv (I := I) (fun y ↦ (e.localFrameCoeff I b i y) (σ y)) x +
              (e.localFrameCoeff I b i x) (σ x) • mvfderiv (I := I) g x := by
        exact mvfderiv_mul (I := I) (f := g)
          (g := fun y ↦ (e.localFrameCoeff I b i y) (σ y)) hg (hcoeff i)
      simpa [hs, ContinuousLinearMap.smulRight_apply, mul_comm, mul_left_comm,
        mul_assoc] using congr(($hi v))
    have hframe :
        ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • e.localFrame b i x = σ x := by
      simpa [LinearMap.piApply_apply] using (e.eq_sum_localFrameCoeff_smul (I := I) (b := b)
        (s := σ) (x' := x) hx).symm
    have hframeCov :
        ∑ i : ι, mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
            e.localFrame b i x =
          frameCovariantDerivativeTangent (I := I) e b σ x v := by
      simp [frameCovariantDerivativeTangent, ContinuousLinearMap.smulRight_apply]
    calc
      frameCovariantDerivativeTangent (I := I) e b (g • σ) x v
          = ∑ i,
              (g x * mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v
                + ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x * mvfderiv (I := I) g x v) •
                e.localFrame b i x := by
              simp [frameCovariantDerivativeTangent]
              refine Finset.sum_congr rfl ?_
              intro i hi
              simpa [ContinuousLinearMap.smulRight_apply] using
                congrArg (fun a ↦ a • e.localFrame b i x) (hprod i)
      _ = ∑ i : ι,
            (g x * mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v) •
              e.localFrame b i x
          + ∑ i : ι,
              (((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x * mvfderiv (I := I) g x v) •
                e.localFrame b i x := by
              simp_rw [add_smul]
              rw [Finset.sum_add_distrib]
      _ = g x • ∑ i : ι,
            mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
              e.localFrame b i x
          + mvfderiv (I := I) g x v • ∑ i : ι,
              ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • e.localFrame b i x := by
              congr 1
              · calc
                  ∑ i : ι,
                      (g x * mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          g x •
                            (mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [smul_smul]
                  _ = g x • ∑ i : ι,
                        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
                          e.localFrame b i x := by
                            rw [Finset.smul_sum]
              · calc
                  ∑ i : ι,
                      (((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x * mvfderiv (I := I) g x v) •
                        e.localFrame b i x
                      = ∑ i : ι,
                          mvfderiv (I := I) g x v •
                            (((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
                              e.localFrame b i x) := by
                                refine Finset.sum_congr rfl ?_
                                intro i hi
                                rw [mul_comm, smul_smul]
                  _ = mvfderiv (I := I) g x v • ∑ i : ι,
                        ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • e.localFrame b i x := by
                            rw [Finset.smul_sum]
        _ = g x • frameCovariantDerivativeTangent (I := I) e b σ x v + mvfderiv (I := I) g x v • σ x := by
             rw [hframeCov, hframe]

theorem covariantDerivative_eq_frameCovariantDerivativeTangent_add_difference
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : Π x : M, TangentSpace I x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x) :
    cov σ x =
      frameCovariantDerivativeTangent (I := I) e b σ x +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
          (s := e.baseSet) x) (σ x) := by
  have hdiff :=
    IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
      (s := e.baseSet) (x := x) (hx := hx) (σ := σ) (hσ := hσ)
  calc
    cov σ x = (cov σ x - frameCovariantDerivativeTangent (I := I) e b σ x) +
        frameCovariantDerivativeTangent (I := I) e b σ x := (sub_add_cancel _ _).symm
    _ = frameCovariantDerivativeTangent (I := I) e b σ x +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
          (s := e.baseSet) x) (σ x) := by
            rw [← hdiff]
            abel

theorem covariantDerivative_apply_eq_frameCovariantDerivativeTangent_apply_add_difference
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : Π x : M, TangentSpace I x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      frameCovariantDerivativeTangent (I := I) e b σ x v +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
          (s := e.baseSet) x) (σ x) v := by
  simpa using congrArg (fun A ↦ A v) <|
    covariantDerivative_eq_frameCovariantDerivativeTangent_add_difference
      (I := I) e b cov hx hσ

theorem covariantDerivative_apply_eq_sum_localFrame_add_difference
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : Π x : M, TangentSpace I x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      (∑ i : ι,
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v •
          e.localFrame b i x) +
        (IsCovariantDerivativeOn.difference
          (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
          (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
          (s := e.baseSet) x) (σ x) v := by
  simpa [frameCovariantDerivativeTangent, ContinuousLinearMap.smulRight_apply] using
    covariantDerivative_apply_eq_frameCovariantDerivativeTangent_apply_add_difference
      (I := I) e b cov hx hσ v

theorem frameCovariantDerivativeTangent_localFrame_eq_zero
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) {j : ι} {x : M} (hx : x ∈ e.baseSet) :
    frameCovariantDerivativeTangent (I := I) e b (e.localFrame b j) x = 0 := by
  classical
  ext v
  simp [frameCovariantDerivativeTangent, ContinuousLinearMap.smulRight_apply]
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
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {j : ι} {x : M} (hx : x ∈ e.baseSet) :
    (IsCovariantDerivativeOn.difference
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
      (s := e.baseSet) x) (e.localFrame b j x) =
        cov (e.localFrame b j) x := by
  have hdiff :=
    IsCovariantDerivativeOn.difference_apply
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
      (s := e.baseSet) (x := x) (hx := hx) (σ := e.localFrame b j)
      (hσ := (contMDiffAt_localFrame_of_mem (I := I) (e := e) (b := b)
        (n := (1 : WithTop ℕ∞)) j hx).mdifferentiableAt one_ne_zero)
  simpa [frameCovariantDerivativeTangent_localFrame_eq_zero (I := I) e b hx] using hdiff

theorem covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (e : Trivialization E (TotalSpace.proj : TotalSpace E (TangentSpace I : M → Type _) → M)) [MemTrivializationAtlas e] {ι : Type*} [Fintype ι] [DecidableEq ι]
    [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
    (b : Module.Basis ι ℝ E) (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {σ : Π x : M, TangentSpace I x} {x : M} (hx : x ∈ e.baseSet) (hσ : MDiffAt (T% σ) x)
    (v : TangentSpace I x) :
    cov σ x v =
      ∑ i : ι,
        mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
      ∑ i : ι,
        ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x • cov (e.localFrame b i) x v := by
  let A :=
    IsCovariantDerivativeOn.difference
      (hcov := cov.isCovariantDerivativeOnUniv.mono (Set.subset_univ e.baseSet))
      (hcov' := isCovariantDerivativeOn_frameCovariantDerivativeTangent (I := I) e b)
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
            rw [difference_localFrame_eq_covariantDerivative (I := I) e b cov hx]
  calc
    cov σ x v
        = ∑ i : ι,
            mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
          A x (σ x) v := by
            simpa using
              covariantDerivative_apply_eq_sum_localFrame_add_difference (I := I) e b cov hx hσ v
    _ = ∑ i : ι,
          mvfderiv (I := I) ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x v • e.localFrame b i x +
        ∑ i : ι, ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) x •
          cov (e.localFrame b i) x v := by rw [hdiff]

/-- **Tangent-bundle covariant-derivative level downgrade `1 → 0`, fiber-norm-free.**  A globally
`C¹` covariant derivative on the tangent bundle (`ContMDiffCovariantDerivative cov 1`) is a `C⁰`
covariant derivative on every open set: the covariant derivative of a merely-`C¹` vector field is a
*continuous* `Hom(TM, TM)`-section.  Proved from the fiber-norm-free frame decomposition
`∇σ = ∇^{frame}σ + ∑ᵢ (coeffᵢ σ) · ∇(frameᵢ)` (transcribed above against
`frameCovariantDerivativeTangent`), avoiding the Π fiber-norm diamond at `V = TangentSpace I`. -/
theorem contMDiffCovariantDerivativeOn_zero_of_contMDiffCovariantDerivative_one
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [ContMDiffCovariantDerivative cov 1]
    {u : Set M} (hu : IsOpen u) :
    ContMDiffCovariantDerivativeOn E 0 cov.toFun u := by
  classical
  refine { contMDiff := ?_ }
  intro σ hσ
  apply contMDiffOn_of_locally_contMDiffOn
  intro x hx
  let e := trivializationAt E (TangentSpace I : M → Type _) x
  let b := Module.finBasis ℝ E
  have hxbase : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x
  refine ⟨e.baseSet, e.open_baseSet, hxbase, ?_⟩
  haveI : ContMDiffVectorBundle 0 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (show (0 : WithTop ℕ∞) ≤ 2 by norm_num)
  haveI : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I :=
    ContMDiffVectorBundle.of_le (n := 2) (show (1 : WithTop ℕ∞) ≤ 2 by norm_num)
  haveI : ContMDiffVectorBundle (0 + 1) E (TangentSpace I : M → Type _) I := by
    simpa using (inferInstance : ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I)
  have hopen : IsOpen (u ∩ e.baseSet) := hu.inter e.open_baseSet
  have hsub : u ∩ e.baseSet ⊆ e.baseSet := Set.inter_subset_right
  have hσ1 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 1 (T% σ) (u ∩ e.baseSet) := by
    simpa using (show ContMDiffOn I (I.prod 𝓘(ℝ, E)) (0 + 1) (T% σ) u from hσ).mono
      Set.inter_subset_left
  have hcov1 : ContMDiffCovariantDerivativeOn E 1 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_one_of_contMDiffCovariantDerivative_one
      (u := e.baseSet) e.open_baseSet
  have hσ01 : ContMDiffOn I (I.prod 𝓘(ℝ, E)) (0 + 1) (T% σ) (u ∩ e.baseSet) := by
    simpa using hσ1
  have hframe0 := contMDiffOn_frameCovariantDerivativeTangent_of_level
    (I := I) (n := 0) e b hopen hsub hσ01
  have hcoeff : ∀ i, ContMDiffOn I 𝓘(ℝ) 1
      ((LinearMap.piApply (e.localFrameCoeff I b i)) σ) (u ∩ e.baseSet) := fun i =>
    contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) hopen hsub hσ1 i
  have hframe2 : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E)) (1 + 1)
      (T% (e.localFrame b i)) e.baseSet := fun i => by
    convert (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
      (n := (2 : WithTop ℕ∞)) (b := b) i) using 1 <;> norm_num
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
  have hdec := covariantDerivative_apply_eq_sum_localFrame_add_sum_covariantDerivative_localFrame
    (I := I) e b cov hy.2 hMDiff v
  simpa [frameCovariantDerivativeTangent, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply] using hdec

end TangentFrame

end CovariantDerivative
