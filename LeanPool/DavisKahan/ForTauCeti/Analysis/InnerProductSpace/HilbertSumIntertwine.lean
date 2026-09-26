/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.OperatorUnitaryEquiv
public import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Two Hilbert sums of the same family carry the same operator

If a family of Hilbert spaces `G i` carries operators `T i`, and two Hilbert sums `(E, V)` and
`(F, W)` of that family carry operators `A` and `B` restricting to `T i` on each summand, then
`A` and `B` are **unitarily equivalent** -- by the canonical unitary `E ≃ₗᵢ lp G 2 ≃ₗᵢ F`.

This is the bridge from "the operator acts summand-wise" to "the operator is what the model
says", and it is used twice: once to move a normal operator onto its cyclic multiplication
model, and once to move that model onto the assembled single-`L²` model.

The proof is a density argument, not a computation.  The two continuous maps `x ↦ e (A x)` and
`x ↦ B (e x)` agree on every summand, so they agree on the closed submodule where they agree,
which contains the span of the summands, whose closure is everything.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Extraction class: **authored in place** for the Tau Ceti staging layer.
* Spectra influence: **none** -- this module imports only Mathlib and `ForTauCeti`.
-/

@[expose] public section

namespace TauCeti

variable {ι : Type*} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace ℂ (G i)]
variable [∀ i, CompleteSpace (G i)]

/-- The span of the summands of a Hilbert sum is dense. -/
theorem topologicalClosure_iSup_range_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E}
    (hV : IsHilbertSum ℂ G V) :
    (⊤ : Submodule ℂ E) ≤ (⨆ i, LinearMap.range (V i).toLinearMap).topologicalClosure := by
  have htop : LinearMap.range hV.OrthogonalFamily.linearIsometry.toLinearMap = ⊤ :=
    LinearMap.range_eq_top.mpr hV.surjective_isometry
  rw [hV.OrthogonalFamily.range_linearIsometry] at htop
  exact htop.ge

omit [∀ i, CompleteSpace (G i)] in
/-- The canonical unitary between two Hilbert sums of the same family matches the summand
embeddings. -/
theorem linearIsometryEquiv_trans_symm_apply_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E}
    {W : ∀ i, G i →ₗᵢ[ℂ] F} (hV : IsHilbertSum ℂ G V) (hW : IsHilbertSum ℂ G W) (i : ι)
    (y : G i) :
    (hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm) (V i y) = W i y := by
  classical
  have hVsingle : hV.linearIsometryEquiv.symm (lp.single 2 i y) = V i y :=
    hV.linearIsometryEquiv_symm_apply_single y
  have hfwd : hV.linearIsometryEquiv (V i y) = lp.single 2 i y := by
    rw [← hVsingle, LinearIsometryEquiv.apply_symm_apply]
  simp only [LinearIsometryEquiv.trans_apply, hfwd]
  exact hW.linearIsometryEquiv_symm_apply_single y

/-- **The canonical unitary between two Hilbert sums is equivariant for any summand-wise
additive continuous structure map** -- in particular for pointwise complex conjugation.

The statement asks nothing of `cE`, `cF` beyond *additivity* and *continuity*: no
conjugate-linearity, no involutivity, no compatibility with the inner product.  That is exactly
what the density argument consumes, and it is why a real-scalar `IsHilbertSum` -- which Mathlib
does not have -- is not needed: the supremum of the summand ranges is generated **under addition
alone** from those ranges (`Submodule.iSup_induction`), and each range is already carried into
the equalizer by the per-summand hypothesis.  The `ℂ`-scalar structure of the supremum is never
re-examined. -/
theorem star_linearIsometryEquiv_trans_symm_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E}
    {W : ∀ i, G i →ₗᵢ[ℂ] F} (hV : IsHilbertSum ℂ G V) (hW : IsHilbertSum ℂ G W) {cE : E → E}
    {cF : F → F} {c : ∀ i, G i → G i} (hcE : Continuous cE)
    (hcEadd : ∀ x y, cE (x + y) = cE x + cE y) (hcF : Continuous cF)
    (hcFadd : ∀ x y, cF (x + y) = cF x + cF y) (hVc : ∀ i y, V i (c i y) = cE (V i y))
    (hWc : ∀ i y, W i (c i y) = cF (W i y)) (x : E) :
    (hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm) (cE x)
      = cF ((hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm) x) := by
  classical
  set e : E ≃ₗᵢ[ℂ] F := hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm with he
  have heV : ∀ (i : ι) (y : G i), e (V i y) = W i y :=
    linearIsometryEquiv_trans_symm_apply_of_isHilbertSum hV hW
  have hcE0 : cE 0 = 0 := by
    have h := hcEadd 0 0
    simpa using h.symm
  have hcF0 : cF 0 = 0 := by
    have h := hcFadd 0 0
    simpa using h.symm
  have hclosed : IsClosed {z : E | e (cE z) = cF (e z)} :=
    isClosed_eq (e.continuous.comp hcE) (hcF.comp e.continuous)
  have hmem : ∀ z ∈ (⨆ i, LinearMap.range (V i).toLinearMap), e (cE z) = cF (e z) := by
    intro z hz
    refine Submodule.iSup_induction (motive := fun w : E => e (cE w) = cF (e w)) _ hz
      (fun i w hw => ?_) ?_ (fun z₁ z₂ h₁ h₂ => ?_)
    · obtain ⟨y, rfl⟩ := hw
      have hcast : cE (V i y) = V i (c i y) := (hVc i y).symm
      simp only [LinearIsometry.coe_toLinearMap] at hcast ⊢
      rw [hcast, heV i (c i y), hWc i y, heV i y]
    · rw [hcE0, map_zero, hcF0]
    · rw [hcEadd, map_add, h₁, h₂, ← hcFadd, ← map_add]
  have hx : x ∈ closure ((⨆ i, LinearMap.range (V i).toLinearMap : Submodule ℂ E) : Set E) := by
    have := (topologicalClosure_iSup_range_of_isHilbertSum hV) (Submodule.mem_top (x := x))
    rwa [← Submodule.topologicalClosure_coe]
  exact closure_minimal hmem hclosed hx

/-- **The canonical unitary between two Hilbert sums intertwines two summand-wise operators.**

This is the content of `operatorUnitaryEquiv_of_isHilbertSum`, stated for the *named* unitary
rather than existentially, so that it can be paired with
`star_linearIsometryEquiv_trans_symm_of_isHilbertSum` -- which speaks about the same unitary --
into a single `TauCeti.StarOperatorUnitaryEquiv`.  The existential form cannot be so paired,
because two invocations of it need not choose the same witness. -/
theorem intertwines_linearIsometryEquiv_trans_symm_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E}
    {W : ∀ i, G i →ₗᵢ[ℂ] F} (hV : IsHilbertSum ℂ G V) (hW : IsHilbertSum ℂ G W)
    {T : ∀ i, G i →L[ℂ] G i} {A : E →L[ℂ] E} {B : F →L[ℂ] F}
    (hA : ∀ i y, A (V i y) = V i (T i y)) (hB : ∀ i y, B (W i y) = W i (T i y)) (x : E) :
    (hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm) (A x)
      = B ((hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm) x) := by
  classical
  set e : E ≃ₗᵢ[ℂ] F := hV.linearIsometryEquiv.trans hW.linearIsometryEquiv.symm with he
  have heV : ∀ (i : ι) (y : G i), e (V i y) = W i y :=
    linearIsometryEquiv_trans_symm_apply_of_isHilbertSum hV hW
  set f₁ : E →L[ℂ] F := (e.toLinearIsometry.toContinuousLinearMap).comp A with hf₁
  set f₂ : E →L[ℂ] F := B.comp (e.toLinearIsometry.toContinuousLinearMap) with hf₂
  have hsub : (⨆ i, LinearMap.range (V i).toLinearMap)
      ≤ LinearMap.eqLocus f₁.toLinearMap f₂.toLinearMap := by
    refine iSup_le fun i => ?_
    rintro _ ⟨y, rfl⟩
    have h₁ : f₁ (V i y) = W i (T i y) := by
      simp only [hf₁, ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      rw [hA i y, heV i (T i y)]
    have h₂ : f₂ (V i y) = W i (T i y) := by
      simp only [hf₂, ContinuousLinearMap.coe_comp, Function.comp_apply,
        LinearIsometry.coe_toContinuousLinearMap, LinearIsometryEquiv.coe_toLinearIsometry]
      rw [heV i y, hB i y]
    exact h₁.trans h₂.symm
  have hclosed : IsClosed
      ((LinearMap.eqLocus f₁.toLinearMap f₂.toLinearMap : Submodule ℂ E) : Set E) :=
    isClosed_eq f₁.continuous f₂.continuous
  have htop := (topologicalClosure_iSup_range_of_isHilbertSum hV).trans
    (Submodule.topologicalClosure_minimal _ hsub hclosed)
  exact htop Submodule.mem_top

/-- **Two Hilbert sums of the same family carry unitarily equivalent operators**, provided each
carries the same summand-wise operator. -/
theorem operatorUnitaryEquiv_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E} {W : ∀ i, G i →ₗᵢ[ℂ] F}
    (hV : IsHilbertSum ℂ G V) (hW : IsHilbertSum ℂ G W) {T : ∀ i, G i →L[ℂ] G i}
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} (hA : ∀ i y, A (V i y) = V i (T i y))
    (hB : ∀ i y, B (W i y) = W i (T i y)) : OperatorUnitaryEquiv A B :=
  operatorUnitaryEquiv_of_intertwines _
    (intertwines_linearIsometryEquiv_trans_symm_of_isHilbertSum hV hW hA hB)

/-- **Two Hilbert sums of the same family carry `star`-equivariantly unitarily equivalent
operators**, provided each carries the same summand-wise operator *and* the same summand-wise
structure map.

This is `operatorUnitaryEquiv_of_isHilbertSum` with the conjugation carried along, and it is the
step the mission's probe was about: the two components are proved for the **same** named
unitary, so no field-change of `IsHilbertSum` -- which Mathlib does not have -- is involved. -/
theorem starOperatorUnitaryEquiv_of_isHilbertSum {V : ∀ i, G i →ₗᵢ[ℂ] E} {W : ∀ i, G i →ₗᵢ[ℂ] F}
    (hV : IsHilbertSum ℂ G V) (hW : IsHilbertSum ℂ G W) {T : ∀ i, G i →L[ℂ] G i}
    {A : E →L[ℂ] E} {B : F →L[ℂ] F} {cE : E → E} {cF : F → F} {c : ∀ i, G i → G i}
    (hA : ∀ i y, A (V i y) = V i (T i y)) (hB : ∀ i y, B (W i y) = W i (T i y))
    (hcE : Continuous cE) (hcEadd : ∀ x y, cE (x + y) = cE x + cE y) (hcF : Continuous cF)
    (hcFadd : ∀ x y, cF (x + y) = cF x + cF y) (hVc : ∀ i y, V i (c i y) = cE (V i y))
    (hWc : ∀ i y, W i (c i y) = cF (W i y)) : StarOperatorUnitaryEquiv cE cF A B :=
  starOperatorUnitaryEquiv_of_intertwines _
    (intertwines_linearIsometryEquiv_trans_symm_of_isHilbertSum hV hW hA hB)
    (star_linearIsometryEquiv_trans_symm_of_isHilbertSum hV hW hcE hcEadd hcF hcFadd hVc hWc)

end TauCeti
