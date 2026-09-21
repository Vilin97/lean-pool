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

/-
Copyright (c) 2026 Poincaré formalization project. All rights reserved.
-/
import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.ParametrizedInner
import LeanPool.PoincareGeometry.PoincareCurvature.Analysis.MatrixSmoothness
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# Joint `(t, x)` smoothness of the local-frame Gram matrix of a time-dependent metric

The joint space-time smoothness of the Ricci–DeTurck gauge field reduces, via the raised-covector
coefficient formula, to inverting the local-frame Gram matrix of the *time-dependent* metric jointly
in `(t, x)`.  The field-independent matrix calculus that inverts and contracts such a jointly-smooth
matrix already exists (`PoincareCurvature.MatrixSmoothness`).  The missing input is the joint
`(t, x)` smoothness of the Gram *readout* itself,
`G(t, x)ᵢⱼ = (g t).inner x (frameᵢ x) (frameⱼ x)`.

Given a time-dependent metric `g : ℝ → ContMDiffRiemannianMetric` whose fibrewise bilinear form is
**jointly** `(t, x)`-smooth (the honest "time-dependent Riemannian raising" datum), this file proves
that readout is `ContMDiffOn` over `ℝ × B`, valued in `ι → ι → ℝ` — exactly the matrix family the
`contMDiffOn_matrixInv_mulVec` / `contMDiffOn_bilinForm` core consumes.

The proof feeds the joint metric section and the (time-independent) local frame vectors into the
parameter-dependent bilinear-form apply lemma `contMDiffOn_paramBilin_apply₂` from
`PoincareCurvature.Analysis.ParametrizedInner`, with parameter manifold `ℝ × B` and base map
`Prod.snd`.
-/

open Manifold Bundle
open scoped Manifold Topology

namespace PoincareCurvature.ParametrizedInner

section Gram

variable
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} {n : WithTop ℕ∞}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, NormedAddCommGroup (V x)]
  [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle n F V IB]

/-- **Joint `(t, x)` smoothness of a time-independent local frame section, over the space-time base.**
Composing the spatial `contMDiffOn_localFrame_baseSet` with `Prod.snd : ℝ × B → B`.  This is the
common `v`/`w` input to both the Gram readout and the one-form pairing readout. -/
theorem contMDiffOn_frameSection_prodSnd
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet) (k : ι) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ (TotalSpace.mk' F p.2 (e.localFrame bas k p.2))) (Set.univ ×ˢ u) := by
  have hspatial : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
      (fun x : B ↦ TotalSpace.mk' F x (e.localFrame bas k x)) u :=
    (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := IB) (e := e)
      (n := n) (b := bas) k).mono hu'
  exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp ↦ hp.2)

omit [ContMDiffVectorBundle n F V IB] in
/-- **Positive-definiteness of the local-frame Gram form of a Riemannian metric.**  For `c ≠ 0`,
`∑ᵢⱼ cᵢ cⱼ · g.inner x (frameᵢ) (frameⱼ) > 0`, since it equals `g.inner x w w` for the nonzero
combination `w = ∑ᵢ cᵢ • frameᵢ` and the metric is positive-definite. -/
theorem timeDependentGram_pos
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) {c : ι → ℝ} (hc : c ≠ 0) :
    0 < ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := by
  classical
  let w : V x := ∑ i, c i • e.localFrame bas i x
  have hw : w ≠ 0 := by
    intro hw0
    apply hc
    calc
      c = (e.basisAt bas hx).repr w := by
        simpa [w, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := bas) hx]
          using ((e.basisAt bas hx).repr_sum_self c).symm
      _ = 0 := by simp [hw0]
  have hsum :
      g.inner x w w =
        ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := by
    show (g.inner x) (∑ i, c i • e.localFrame bas i x) (∑ j, c j • e.localFrame bas j x) = _
    rw [_root_.map_sum (g.inner x), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply,
      _root_.map_sum (g.inner x (e.localFrame bas i x)), Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, smul_eq_mul]
    ring
  calc
    0 < g.inner x w w := g.pos x w hw
    _ = ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) := hsum

omit [ContMDiffVectorBundle n F V IB] in
/-- **The local-frame Gram matrix of a Riemannian metric is nonsingular.**  Its determinant is
nonzero at every base point of the trivialization, since positive-definiteness rules out a nontrivial
kernel vector.  This discharges the nonsingularity hypothesis of
`PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec` for the time-dependent Gram
readout. -/
theorem timeDependentGram_det_ne_zero
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) :
    (show Matrix ι ι ℝ from
        (fun i j ↦ g.inner x (e.localFrame bas i x) (e.localFrame bas j x))).det ≠ 0 := by
  classical
  let A : Matrix ι ι ℝ := fun i j ↦ g.inner x (e.localFrame bas i x) (e.localFrame bas j x)
  intro hA
  obtain ⟨c, hc, hAc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  have hAcA : A.mulVec c = 0 := by simpa [A] using hAc
  have hAc' : ∀ i, ∑ j, A i j * c j = 0 := by
    intro i
    have hi := congrFun hAcA i
    simpa [Matrix.mulVec, dotProduct] using hi
  have hsum :
      ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x) = 0 := by
    calc
      ∑ i, ∑ j, c i * c j * g.inner x (e.localFrame bas i x) (e.localFrame bas j x)
          = ∑ i, c i * (∑ j, A i j * c j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [A]
            ring
      _ = ∑ i, c i * 0 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [hAc' i]
      _ = 0 := by simp
  have hpos := timeDependentGram_pos g e bas hx hc
  rw [hsum] at hpos
  exact lt_irrefl 0 hpos

/-- **Joint `(t, x)` smoothness of a fixed pair of frame vectors paired by a time-dependent metric.**
If the fibrewise bilinear form `(g t).inner` of a time-dependent metric is jointly `(t, x)`-smooth
over `ℝ ×ˢ u`, and `i j` index a local frame of a trivialization `e` with `u ⊆ e.baseSet`, then the
scalar `(t, x) ↦ (g t).inner x (frameᵢ x) (frameⱼ x)` is `ContMDiffOn` over `Set.univ ×ˢ u`. -/
theorem contMDiffOn_timeDependentInner_localFrame
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (i j : ι) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ) n
      (fun p : ℝ × B ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2))
      (Set.univ ×ˢ u) := by
  have hframe : ∀ k : ι, ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ (TotalSpace.mk' F p.2 (e.localFrame bas k p.2))) (Set.univ ×ˢ u) := by
    intro k
    have hspatial : ContMDiffOn IB (IB.prod 𝓘(ℝ, F)) n
        (fun x : B ↦ TotalSpace.mk' F x (e.localFrame bas k x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := IB) (e := e)
        (n := n) (b := bas) k).mono hu'
    exact hspatial.comp (contMDiff_snd.contMDiffOn) (fun p hp ↦ hp.2)
  exact contMDiffOn_paramBilin_apply₂ (b := Prod.snd) (v := fun p ↦ e.localFrame bas i p.2)
    (w := fun p ↦ e.localFrame bas j p.2) (ψ := fun p ↦ (g p.1).inner p.2) hg (hframe i) (hframe j)

/-- **Joint `(t, x)` smoothness of the time-dependent local-frame Gram readout.**  Packaging the
previous lemma over all index pairs, the matrix-valued readout
`(t, x) ↦ fun i j ↦ (g t).inner x (frameᵢ x) (frameⱼ x)` is `ContMDiffOn` over `Set.univ ×ˢ u`,
valued in `ι → ι → ℝ`.  This is exactly the shape of the matrix family fed to
`PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec` and `contMDiffOn_bilinForm`. -/
theorem contMDiffOn_timeDependentGramReadout
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ι → ℝ) n
      (fun p : ℝ × B ↦
        (fun i j ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2) : ι → ι → ℝ))
      (Set.univ ×ˢ u) := by
  rw [contMDiffOn_pi_space]
  intro i
  rw [contMDiffOn_pi_space]
  intro j
  exact contMDiffOn_timeDependentInner_localFrame g e bas hu' hg i j

/-- **Joint `(t, x)` smoothness of a time-dependent one-form pairing readout.**  Given a
time-dependent field of covectors `ω t : Π y, V y →L[ℝ] ℝ` whose section `(t, x) ↦ ω t x` is jointly
`(t, x)`-smooth over `ℝ ×ˢ u`, the pairing readout `(t, x) ↦ fun j ↦ ω t x (frameⱼ x)` is
`ContMDiffOn` over `Set.univ ×ˢ u`, valued in `ι → ℝ`.  This is the vector family `b(t, x)ⱼ` fed
(alongside the inverse Gram matrix) to `PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec`
to obtain the joint `(t, x)` raised-covector coefficients. -/
theorem contMDiffOn_timeDependentOneFormPairing
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hω : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n
      (fun p : ℝ × B ↦ (fun j ↦ ω p.1 p.2 (e.localFrame bas j p.2) : ι → ℝ)) (Set.univ ×ˢ u) := by
  rw [contMDiffOn_pi_space]
  intro j
  exact contMDiffOn_paramLinear_apply (b := Prod.snd) (v := fun p ↦ e.localFrame bas j p.2)
    (φ := fun p ↦ ω p.1 p.2) hω (contMDiffOn_frameSection_prodSnd e bas hu' j)

/-- **Joint `(t, x)` smoothness of the raised-covector coefficients.**  Combining the joint Gram
readout, the joint one-form pairing, and Gram nonsingularity through the Cramer-solve smoothness
`contMDiffOn_matrixInv_mulVec`, the raised-covector coefficient family
`cᵢ(t, x) = (G(t, x)⁻¹ *ᵥ b(t, x))ᵢ` — where `Gᵢⱼ = (g t).inner x (frameᵢ) (frameⱼ)` and
`bⱼ = ω t x (frameⱼ)` — is `ContMDiffOn` over `Set.univ ×ˢ u`, valued in `ι → ℝ`.  This is the joint
`(t, x)` version of the raised-coefficient formula `cᵢ = ∑ⱼ (Gram⁻¹)ᵢⱼ · ω(frameⱼ)`, the coefficients
of the space-time raised section. -/
theorem contMDiffOn_timeDependentRaisedCoeff
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (hω : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n
      (fun p : ℝ × B ↦ (show ι → ℝ from
        ((show Matrix ι ι ℝ from
            (fun i j ↦ (g p.1).inner p.2 (e.localFrame bas i p.2) (e.localFrame bas j p.2)))⁻¹
          : Matrix ι ι ℝ).mulVec (fun j ↦ ω p.1 p.2 (e.localFrame bas j p.2)))) (Set.univ ×ˢ u) :=
  PoincareCurvature.MatrixSmoothness.contMDiffOn_matrixInv_mulVec
    (contMDiffOn_timeDependentGramReadout g e bas hu' hg)
    (contMDiffOn_timeDependentOneFormPairing ω e bas hu' hω)
    (fun p hp ↦ timeDependentGram_det_ne_zero (g p.1) e bas (hu' hp.2))

/-- **Joint `(t, x)` smoothness of a raised section assembled from smooth coefficients.**  Given a
jointly `(t, x)`-smooth family of coefficients `c(t, x) : ι → ℝ`, the raised section
`(t, x) ↦ ∑ᵢ c(t, x)ᵢ • frameᵢ(x)` — a section of the bundle `V` along `Prod.snd : ℝ × B → B` — is
`ContMDiffOn` over `Set.univ ×ˢ u`.  Combined with `contMDiffOn_timeDependentRaisedCoeff` (whose output
is exactly such a `c`), this produces the joint `(t, x)` smoothness of the raised gauge field on a
single chart patch — the per-patch `hXfield`.  The proof composes the smooth inverse trivialization
`e.symm` with the smooth coordinate map `(t, x) ↦ (x, ∑ᵢ c(t, x)ᵢ • basᵢ)`. -/
theorem contMDiffOn_raisedSection_of_coeff
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    {c : ℝ × B → ι → ℝ}
    (hc : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, ι → ℝ) n c (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' F p.2 (∑ i, c p i • e.localFrame bas i p.2))
      (Set.univ ×ˢ u) := by
  have hcoord : ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n
      (fun p : ℝ × B ↦ ∑ i, c p i • bas i) (Set.univ ×ˢ u) := by
    classical
    have hs : ∀ t : Finset ι, ContMDiffOn (𝓘(ℝ).prod IB) 𝓘(ℝ, F) n
        (fun p : ℝ × B ↦ ∑ i ∈ t, c p i • bas i) (Set.univ ×ˢ u) := by
      intro t
      induction t using Finset.induction_on with
      | empty => simpa using (contMDiffOn_const (c := (0 : F)))
      | insert i t hi ih =>
        simp only [Finset.sum_insert hi]
        exact (((contMDiffOn_pi_space.mp hc) i).smul contMDiffOn_const).add ih
    exact hs Finset.univ
  have hh : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ ((p.2, ∑ i, c p i • bas i) : B × F)) (Set.univ ×ˢ u) :=
    (contMDiff_snd.contMDiffOn).prodMk hcoord
  have hmaps : Set.MapsTo (fun p : ℝ × B ↦ ((p.2, ∑ i, c p i • bas i) : B × F))
      (Set.univ ×ˢ u) e.target := fun p hp ↦ e.mem_target.mpr (hu' hp.2)
  have hcomp := (Bundle.Trivialization.contMDiffOn_symm e (n := n)).comp hh hmaps
  refine hcomp.congr fun p hp ↦ ?_
  have hp2 : p.2 ∈ e.baseSet := hu' hp.2
  have hframe : ∀ i : ι, e.localFrame bas i p.2 = e.symm p.2 (bas i) := by
    intro i
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet e bas hp2]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
  have hlin : e.symm p.2 (∑ i, c p i • bas i) = ∑ i, c p i • e.symm p.2 (bas i) := by
    have h := map_sum (e.symmL ℝ p.2) (fun i => c p i • bas i) Finset.univ
    simp only [map_smul] at h
    simpa only [Bundle.Trivialization.symmL_apply e hp2] using h
  show TotalSpace.mk' F p.2 (∑ i, c p i • e.localFrame bas i p.2)
      = e.toOpenPartialHomeomorph.symm ((p.2, ∑ i, c p i • bas i))
  rw [← Bundle.Trivialization.mk_symm e hp2, hlin]
  refine congrArg (TotalSpace.mk' F p.2) ?_
  exact (Finset.sum_congr rfl fun i _ => by rw [hframe i]).symm

/-- **Joint `(t, x)` smoothness of the raised gauge field section on a chart patch.**  Chaining the
raised-covector coefficients with the section assembly: given a time-dependent metric `g` and a
time-dependent one-form `ω`, both jointly `(t, x)`-smooth (as fibrewise sections over `ℝ ×ˢ u`), the
raised section `(t, x) ↦ ∑ᵢ (G(t, x)⁻¹ *ᵥ b(t, x))ᵢ • frameᵢ(x)` — the metric-raised vector field of
`ω_t` — is `ContMDiffOn` over `Set.univ ×ˢ u`.  This is the per-chart-patch joint field jet produced by
the entire field-independent joint space-time raising chain; for the tangent bundle it is exactly the
tangent-section input to `contMDiff_spaceTimeField_of_contMDiff_tangentSection`. -/
theorem contMDiffOn_timeDependentRaisedSection
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet)
    (hg : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)) (Set.univ ×ˢ u))
    (hω : ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)) (Set.univ ×ˢ u)) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' F p.2
        (∑ i, (show ι → ℝ from
            ((show Matrix ι ι ℝ from
                (fun a b ↦ (g p.1).inner p.2 (e.localFrame bas a p.2) (e.localFrame bas b p.2)))⁻¹
              : Matrix ι ι ℝ).mulVec (fun j ↦ ω p.1 p.2 (e.localFrame bas j p.2))) i
          • e.localFrame bas i p.2)) (Set.univ ×ˢ u) :=
  contMDiffOn_raisedSection_of_coeff e bas hu'
    (contMDiffOn_timeDependentRaisedCoeff g ω e bas hu' hg hω)

omit [ContMDiffVectorBundle n F V IB] in
/-- **Joint `(t, x)` smoothness of a time-INDEPENDENT metric section, over the space-time base.**
Composing the spatial metric smoothness `g₀.contMDiff` with `Prod.snd : ℝ × B → B` gives the
constant-family instance of the capstone's `hg` input: a background/reference metric that does not
evolve in time is (trivially) jointly `(t, x)`-smooth as a fibrewise bilinear-form section.  This is
the `hg` hypothesis of `contMDiffOn_timeDependentRaisedSection` for the constant family
`g := fun _ ↦ g₀` (via `.contMDiffOn`). -/
theorem contMDiff_constMetricSection_prodSnd
    (g₀ : Bundle.ContMDiffRiemannianMetric IB n F V) :
    ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 (g₀.inner p.2)) :=
  g₀.contMDiff.comp contMDiff_snd

omit [ContMDiffVectorBundle n F V IB] in
/-- **Joint `(t, x)` smoothness of a time-INDEPENDENT one-form section, over the space-time base.**
Composing a spatially-smooth covector section with `Prod.snd : ℝ × B → B` gives the constant-family
instance of the capstone's `hω` input: a time-independent one-form (e.g. the traced DeTurck one-form
of a static metric) is jointly `(t, x)`-smooth.  This is the `hω` hypothesis of
`contMDiffOn_timeDependentRaisedSection` for the constant family `ω := fun _ ↦ ω₀` (via
`.contMDiffOn`). -/
theorem contMDiff_constOneFormSection_prodSnd
    (ω₀ : ∀ y : B, V y →L[ℝ] ℝ)
    (hω₀ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y : B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) y (ω₀ y))) :
    ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω₀ p.2)) :=
  hω₀.comp contMDiff_snd

/-- **Per-patch raised gauge field for time-INDEPENDENT metric + one-form.**  The autonomous-data
instance of `contMDiffOn_timeDependentRaisedSection`: for a static metric `g₀` and static one-form
`ω₀` (spatially smooth as a covector section), the metric-raised vector field
`x ↦ ∑ᵢ (G₀⁻¹ *ᵥ b₀)ᵢ • frameᵢ(x)` of `ω₀` — read as a time-independent section over `ℝ ×ˢ u` — is
`ContMDiffOn`.  This discharges both geometric inputs of the field-independent raising capstone from
the two constant-family smoothness lemmas above, giving the per-patch gauge-field jet for a static
gauge. -/
theorem contMDiffOn_timeIndependentRaisedSection
    (g₀ : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω₀ : ∀ y : B, V y →L[ℝ] ℝ)
    (hω₀ : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun y : B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) y (ω₀ y)))
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {u : Set B} (hu' : u ⊆ e.baseSet) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' F p.2
        (∑ i, (show ι → ℝ from
            ((show Matrix ι ι ℝ from
                (fun a b ↦ g₀.inner p.2 (e.localFrame bas a p.2) (e.localFrame bas b p.2)))⁻¹
              : Matrix ι ι ℝ).mulVec (fun j ↦ ω₀ p.2 (e.localFrame bas j p.2))) i
          • e.localFrame bas i p.2)) (Set.univ ×ˢ u) :=
  contMDiffOn_timeDependentRaisedSection (fun _ ↦ g₀) (fun _ ↦ ω₀) e bas hu'
    (contMDiff_constMetricSection_prodSnd g₀).contMDiffOn
    (contMDiff_constOneFormSection_prodSnd ω₀ hω₀).contMDiffOn

omit [ContMDiffVectorBundle n F V IB] in
/-- **The raised gauge vector solves the raising equation on frame vectors.**  Writing `G` for the
local-frame Gram matrix `Gᵢⱼ = g.inner x (frameᵢ) (frameⱼ)` and `bⱼ = ω x (frameⱼ)`, the raised
vector `v = ∑ᵢ (G⁻¹ *ᵥ b)ᵢ • frameᵢ(x)` produced by the raising capstone satisfies
`g.inner x v (frameₖ x) = ω x (frameₖ x)` for every frame index `k`.  This is Cramer's identity
`G (G⁻¹ b) = b` combined with the symmetry `Gᵢⱼ = Gⱼᵢ` of the metric: it certifies that the
coordinate raised vector is the honest metric dual of `ω` tested against the frame, which (extended to
all of `V x`) makes the raised section *coordinate-free* and hence globally well defined across
overlapping trivializations. -/
theorem raisedVector_inner_localFrame_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) (k : ι) :
    g.inner x
        (∑ i, ((show Matrix ι ι ℝ from
              (fun a b ↦ g.inner x (e.localFrame bas a x) (e.localFrame bas b x)))⁻¹
            : Matrix ι ι ℝ).mulVec (fun j ↦ ω x (e.localFrame bas j x)) i
          • e.localFrame bas i x)
        (e.localFrame bas k x)
      = ω x (e.localFrame bas k x) := by
  classical
  set G : Matrix ι ι ℝ := fun a b ↦ g.inner x (e.localFrame bas a x) (e.localFrame bas b x)
    with hGdef
  set bvec : ι → ℝ := fun j ↦ ω x (e.localFrame bas j x) with hbdef
  have hdet : G.det ≠ 0 := timeDependentGram_det_ne_zero g e bas hx
  have hGc : G.mulVec (G⁻¹.mulVec bvec) = bvec := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hLHS :
      g.inner x (∑ i, G⁻¹.mulVec bvec i • e.localFrame bas i x) (e.localFrame bas k x)
        = ∑ i, G⁻¹.mulVec bvec i * g.inner x (e.localFrame bas i x) (e.localFrame bas k x) := by
    rw [_root_.map_sum (g.inner x), ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsym : ∀ i, g.inner x (e.localFrame bas i x) (e.localFrame bas k x) = G k i :=
    fun i => g.symm x (e.localFrame bas i x) (e.localFrame bas k x)
  calc
    g.inner x
        (∑ i, G⁻¹.mulVec bvec i • e.localFrame bas i x) (e.localFrame bas k x)
        = ∑ i, G⁻¹.mulVec bvec i * g.inner x (e.localFrame bas i x) (e.localFrame bas k x) := hLHS
    _ = ∑ i, G k i * G⁻¹.mulVec bvec i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsym i, mul_comm]
    _ = G.mulVec (G⁻¹.mulVec bvec) k := rfl
    _ = bvec k := by rw [hGc]
    _ = ω x (e.localFrame bas k x) := rfl

omit [ContMDiffVectorBundle n F V IB] in
/-- **The raised gauge vector is the coordinate-free metric dual of the one-form.**  Extending
`raisedVector_inner_localFrame_eq` from frame vectors to an arbitrary `w : V x`: the raised vector
`v = ∑ᵢ (G⁻¹ *ᵥ b)ᵢ • frameᵢ(x)` satisfies `g.inner x v w = ω x w` for *every* tangent vector `w`.
Since `v` is thereby characterised by the trivialization-independent equation `g.inner x v = ω x`,
the raised section is independent of the chosen trivialization and local frame — precisely the
coordinate-freeness needed to glue the per-chart raised sections into a single global gauge field. -/
theorem raisedVector_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {x : B} (hx : x ∈ e.baseSet) (w : V x) :
    g.inner x
        (∑ i, ((show Matrix ι ι ℝ from
              (fun a b ↦ g.inner x (e.localFrame bas a x) (e.localFrame bas b x)))⁻¹
            : Matrix ι ι ℝ).mulVec (fun j ↦ ω x (e.localFrame bas j x)) i
          • e.localFrame bas i x)
        w
      = ω x w := by
  classical
  set v : V x := ∑ i, ((show Matrix ι ι ℝ from
        (fun a b ↦ g.inner x (e.localFrame bas a x) (e.localFrame bas b x)))⁻¹
      : Matrix ι ι ℝ).mulVec (fun j ↦ ω x (e.localFrame bas j x)) i
    • e.localFrame bas i x with hvdef
  have hframe : ∀ k, e.localFrame bas k x = (e.basisAt bas hx) k := fun k =>
    Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := bas) hx
  set d : ι → ℝ := fun i => (e.basisAt bas hx).repr w i with hd
  have hw : w = ∑ k, d k • e.localFrame bas k x := by
    simp_rw [hframe]
    rw [hd]
    exact ((e.basisAt bas hx).sum_repr w).symm
  rw [hw, _root_.map_sum (g.inner x v), _root_.map_sum (ω x)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]
  congr 1
  exact raisedVector_inner_localFrame_eq g ω e bas hx k

omit [ContMDiffVectorBundle n F V IB] in
/-- **Nondegeneracy of a Riemannian metric on the left.**  If two vectors pair identically with every
vector under `g.inner x`, they are equal.  (Positive-definiteness rules out a nonzero difference:
`g.inner x (u - u') (u - u') = 0` forces `u = u'`.)  This is the uniqueness half of the metric-dual
correspondence. -/
theorem eq_of_forall_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    {x : B} {u u' : V x} (h : ∀ w, g.inner x u w = g.inner x u' w) : u = u' := by
  by_contra hne
  have e1 : g.inner x (u - u') = g.inner x u - g.inner x u' := map_sub (g.inner x) u u'
  have hz : g.inner x (u - u') (u - u') = 0 := by
    rw [e1, ContinuousLinearMap.sub_apply, h (u - u'), sub_self]
  have hpos := g.pos x (u - u') (sub_ne_zero.mpr hne)
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

omit [ContMDiffVectorBundle n F V IB] in
/-- **Trivialization independence of the raised gauge vector.**  The metric-raised vector field of a
one-form `ω`, computed via the local-frame Gram inverse of *any* trivialization `e` and model basis
`bas`, is independent of that choice: two trivializations `e, e'` (with bases `bas, bas'`, possibly
over different index types) covering `x` produce the *same* raised vector.  Both are the unique
metric dual of `ω` at `x` (`raisedVector_inner_eq`), so nondegeneracy (`eq_of_forall_inner_eq`)
identifies them.  This is exactly the compatibility that lets the per-chart raised sections be glued
into a single globally-defined gauge field on the manifold. -/
theorem raisedVector_trivialization_independent
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    (e' : Trivialization F (π F V)) [MemTrivializationAtlas e']
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (bas' : Module.Basis ι' ℝ F)
    {x : B} (hx : x ∈ e.baseSet) (hx' : x ∈ e'.baseSet) :
    (∑ i, ((show Matrix ι ι ℝ from
          (fun a b ↦ g.inner x (e.localFrame bas a x) (e.localFrame bas b x)))⁻¹
        : Matrix ι ι ℝ).mulVec (fun j ↦ ω x (e.localFrame bas j x)) i
      • e.localFrame bas i x)
      = ∑ i, ((show Matrix ι' ι' ℝ from
          (fun a b ↦ g.inner x (e'.localFrame bas' a x) (e'.localFrame bas' b x)))⁻¹
        : Matrix ι' ι' ℝ).mulVec (fun j ↦ ω x (e'.localFrame bas' j x)) i
      • e'.localFrame bas' i x := by
  refine eq_of_forall_inner_eq g fun w => ?_
  rw [raisedVector_inner_eq g ω e bas hx w, raisedVector_inner_eq g ω e' bas' hx' w]

/-- **The globally-defined metric-raised gauge field.**  For a smooth Riemannian metric `g` and a
one-form `ω` (a covector section), the metric-raised vector at `y` is the honest metric dual of
`ω y`, computed here concretely via the *canonical* trivialization `trivializationAt F V y` and a
fixed model basis `bas` of `F`.  Because every point lies in the base set of its canonical
trivialization (`FiberBundle.mem_baseSet_trivializationAt'`), this is a genuine global section of `V`;
and by `raisedVector_trivialization_independent` its value does not depend on the trivialization used,
so on *every* trivialization patch it agrees with the local-frame raised expression
(`raisedGaugeField_eq_localFrame`) and it is the unique metric dual of `ω`
(`raisedGaugeField_inner_eq`).  This is the coordinate-free gauge field whose per-patch smoothness
(via the raising capstone) glues to the global `hXfield` of the compact-`M` gauge-flow assembly. -/
noncomputable def raisedGaugeField
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) : V y :=
  ∑ i, ((show Matrix ι ι ℝ from
        (fun a b ↦ g.inner y ((trivializationAt F V y).localFrame bas a y)
          ((trivializationAt F V y).localFrame bas b y)))⁻¹
      : Matrix ι ι ℝ).mulVec
        (fun j ↦ ω y ((trivializationAt F V y).localFrame bas j y)) i
    • (trivializationAt F V y).localFrame bas i y

omit [ContMDiffVectorBundle n F V IB] in
/-- **On every trivialization patch the global raised field is the local-frame raised expression.**
For any trivialization `e` (with model basis `bas`) whose base set contains `y`, the global gauge
field `raisedGaugeField g ω bas y` equals the concrete local-frame raised vector
`∑ᵢ (G⁻¹ *ᵥ b)ᵢ • frameᵢ(y)` of `e`.  Both are the unique metric dual of `ω y`, identified by
`raisedVector_trivialization_independent` (comparing `e` with the canonical trivialization used in the
definition).  This is what transfers the per-patch joint `(t, x)`-smoothness of the raising capstone
to the globally-defined field. -/
theorem raisedGaugeField_eq_localFrame
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    (e : Trivialization F (π F V)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {y : B} (hy : y ∈ e.baseSet) :
    raisedGaugeField g ω bas y
      = ∑ i, ((show Matrix ι ι ℝ from
            (fun a b ↦ g.inner y (e.localFrame bas a y) (e.localFrame bas b y)))⁻¹
          : Matrix ι ι ℝ).mulVec (fun j ↦ ω y (e.localFrame bas j y)) i
        • e.localFrame bas i y := by
  have hy0 : y ∈ (trivializationAt F V y).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y
  exact raisedVector_trivialization_independent g ω (trivializationAt F V y) e bas bas hy0 hy

omit [ContMDiffVectorBundle n F V IB] in
/-- **The global raised gauge field is the honest metric dual of the one-form.**  `raisedGaugeField`
satisfies `g.inner y (raisedGaugeField g ω bas y) = ω y` as continuous linear functionals: it is the
metric-`♯` of `ω`.  Follows pointwise from `raisedVector_inner_eq` at the canonical trivialization. -/
theorem raisedGaugeField_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    g.inner y (raisedGaugeField g ω bas y) = ω y := by
  have hy0 : y ∈ (trivializationAt F V y).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt' y
  ext w
  exact raisedVector_inner_eq g ω (trivializationAt F V y) bas hy0 w

omit [ContMDiffVectorBundle n F V IB] in
/-- **`raisedGaugeField` is the unique metric dual of the one-form.**  Any vector `v : V y` whose
metric pairing `g.inner y v` (as a continuous linear functional) equals `ω y` coincides with the
globally-defined raised gauge field `raisedGaugeField g ω bas y`.  This is nondegeneracy
(`eq_of_forall_inner_eq`) applied to `raisedGaugeField_inner_eq`: since both `v` and the raised field
represent `ω y` under `g`, they are equal.  This is the bridge that lets *any* concretely-constructed
metric dual — e.g. a Riesz-map raise `♯ω` — be identified with the coordinate-free `raisedGaugeField`
consumed by the compact-manifold gauge-flow assembly. -/
theorem raisedGaugeField_eq_of_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {y : B} {v : V y} (hv : g.inner y v = ω y) :
    v = raisedGaugeField g ω bas y := by
  refine eq_of_forall_inner_eq g fun w => ?_
  rw [hv, raisedGaugeField_inner_eq g ω bas y]

omit [ContMDiffVectorBundle n F V IB] in
/-- **Pointwise-pairing form of `raisedGaugeField_eq_of_inner_eq`.**  If `v : V y` pairs with every
`w` as `g.inner y v w = ω y w`, then `v = raisedGaugeField g ω bas y`.  This is the form most directly
usable when a candidate dual is only known to represent `ω` slotwise. -/
theorem raisedGaugeField_eq_of_forall_inner_eq
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    {y : B} {v : V y} (hv : ∀ w, g.inner y v w = ω y w) :
    v = raisedGaugeField g ω bas y :=
  raisedGaugeField_eq_of_inner_eq g ω bas (by ext w; exact hv w)

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric dual of the zero one-form is the zero vector.**  `raisedGaugeField g 0 bas y = 0`,
since the zero vector's metric pairing is the zero functional (`raisedGaugeField_eq_of_forall_inner_eq`
with `v = 0`). -/
theorem raisedGaugeField_zero
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g (0 : ∀ z : B, V z →L[ℝ] ℝ) bas y = 0 :=
  (raisedGaugeField_eq_of_forall_inner_eq g 0 bas (fun w => by simp)).symm

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric dual is additive in the one-form.**  `raisedGaugeField g (ω₁ + ω₂) bas y =
raisedGaugeField g ω₁ bas y + raisedGaugeField g ω₂ bas y`: the sum of the two duals pairs to
`ω₁ + ω₂` under `g` (bilinearity of `g.inner` and `raisedGaugeField_inner_eq`), so uniqueness of the
metric dual identifies it with the dual of the sum. -/
theorem raisedGaugeField_add
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω₁ ω₂ : ∀ z : B, V z →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g (ω₁ + ω₂) bas y
      = raisedGaugeField g ω₁ bas y + raisedGaugeField g ω₂ bas y :=
  (raisedGaugeField_eq_of_forall_inner_eq g (ω₁ + ω₂) bas (fun w => by
    simp only [map_add, ContinuousLinearMap.add_apply, Pi.add_apply,
      raisedGaugeField_inner_eq])).symm

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric dual is homogeneous in the one-form.**  `raisedGaugeField g (c • ω) bas y =
c • raisedGaugeField g ω bas y`. -/
theorem raisedGaugeField_smul
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (c : ℝ) (ω : ∀ z : B, V z →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g (c • ω) bas y = c • raisedGaugeField g ω bas y :=
  (raisedGaugeField_eq_of_forall_inner_eq g (c • ω) bas (fun w => by
    simp only [map_smul, ContinuousLinearMap.smul_apply, Pi.smul_apply,
      raisedGaugeField_inner_eq])).symm

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric dual negates with the one-form.**  `raisedGaugeField g (-ω) bas y =
-raisedGaugeField g ω bas y`.  In particular a metric-raised *gauge field* built from the negation of
a one-form (as with the reverse DeTurck gauge field `-♯ω`) is the negation of the raised field of the
one-form itself. -/
theorem raisedGaugeField_neg
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ∀ z : B, V z →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g (-ω) bas y = -raisedGaugeField g ω bas y :=
  (raisedGaugeField_eq_of_forall_inner_eq g (-ω) bas (fun w => by
    simp only [map_neg, ContinuousLinearMap.neg_apply, Pi.neg_apply,
      raisedGaugeField_inner_eq])).symm

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric dual subtracts with the one-form.**  `raisedGaugeField g (ω₁ - ω₂) bas y =
raisedGaugeField g ω₁ bas y - raisedGaugeField g ω₂ bas y`.  Relevant to the intrinsic DeTurck
one-form, which is a *difference* of connection (Christoffel) one-forms. -/
theorem raisedGaugeField_sub
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω₁ ω₂ : ∀ z : B, V z →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g (ω₁ - ω₂) bas y
      = raisedGaugeField g ω₁ bas y - raisedGaugeField g ω₂ bas y :=
  (raisedGaugeField_eq_of_forall_inner_eq g (ω₁ - ω₂) bas (fun w => by
    simp only [map_sub, ContinuousLinearMap.sub_apply, Pi.sub_apply,
      raisedGaugeField_inner_eq])).symm

omit [ContMDiffVectorBundle n F V IB] in
/-- **The metric-raised gauge field depends only on the metric's inner product, not its smoothness
class.**  If two smooth Riemannian metrics `g` (class `n`) and `g'` (class `m`) induce the same fibre
inner product at every base point (`g.inner y v w = g'.inner y v w`), then their metric-raised gauge
fields of the same one-form coincide: `raisedGaugeField g ω bas y = raisedGaugeField g' ω bas y`.
Both are the unique metric dual `♯ω` under a common inner product, so the uniqueness characterisation
`raisedGaugeField_eq_of_forall_inner_eq` identifies them.  This is the regularity bridge that lets a
`C^∞` metric's raised field (consumed by the compact-manifold gauge-flow raising capstone, which
requires a `ℝ → ContMDiffRiemannianMetric I ∞`) be identified with the `C²` metric-family raised field
appearing in the intrinsic DeTurck one-form identities — closing the `n = 2` ↔ `n = ∞` step of the
smoothness-ladder reconciliation.  Diamond-free: the fibre `V y` (and hence the raised value's type)
does not depend on the metric, so no transported-instance reconciliation is required. -/
theorem raisedGaugeField_congr_inner
    {m : WithTop ℕ∞} [ContMDiffVectorBundle m F V IB]
    (g : Bundle.ContMDiffRiemannianMetric IB n F V)
    (g' : Bundle.ContMDiffRiemannianMetric IB m F V)
    (hinner : ∀ (y : B) (v w : V y), g.inner y v w = g'.inner y v w)
    (ω : ∀ z : B, V z →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (y : B) :
    raisedGaugeField g ω bas y = raisedGaugeField g' ω bas y := by
  refine raisedGaugeField_eq_of_forall_inner_eq g' ω bas (fun w => ?_)
  rw [← hinner y (raisedGaugeField g ω bas y) w]
  exact DFunLike.congr_fun (raisedGaugeField_inner_eq g ω bas y) w

/-- **Per-patch joint `(t, x)` smoothness of the global raised gauge field, as a tangent-style
section.**  Over the canonical trivialization patch around any base point `x`, the globally-defined
raised gauge field `raisedGaugeField (g ·) (ω ·) bas`, read as the section
`(t, y) ↦ TotalSpace.mk' F y (raisedGaugeField (g t) (ω t) bas y)`, is `ContMDiffOn` on
`ℝ ×ˢ (trivializationAt F V x).baseSet`, given the joint smoothness `hg` of the (time-dependent)
metric and `hω` of the one-form.  This packages the raising capstone
`contMDiffOn_timeDependentRaisedSection` composed with the patch identity
`raisedGaugeField_eq_localFrame`, entirely inside the abstract vector-bundle section so that no
tangent-bundle instance is instantiated here; the compact-manifold gauge-flow assembly then applies it
per chart to obtain the global gauge-field jet. -/
theorem contMDiffOn_raisedGaugeField_tangentSection
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (hg : ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)))
    (hω : ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)))
    (x : B) :
    ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' F p.2 (raisedGaugeField (g p.1) (ω p.1) bas p.2))
      (Set.univ ×ˢ (trivializationAt F V x).baseSet) := by
  have hcap := contMDiffOn_timeDependentRaisedSection g ω (trivializationAt F V x) bas
    (subset_rfl) hg.contMDiffOn hω.contMDiffOn
  refine hcap.congr ?_
  intro p hp
  exact congrArg (TotalSpace.mk' F p.2)
    (raisedGaugeField_eq_localFrame (g p.1) (ω p.1) (trivializationAt F V x) bas hp.2)

/-- **Local gauge-field jet of the global raised field, packaged for the flow assembly.**  Around any
base point `x` there is an open set (the base set of the canonical trivialization) containing `x` on
whose time-full slab the raised gauge-field section
`(t, y) ↦ TotalSpace.mk' F y (raisedGaugeField (g t) (ω t) bas y)` is `ContMDiffOn`.  This is exactly
the spatially-local joint-smoothness hypothesis consumed by the compact-manifold gauge-flow assembly
`exists_flow_Ioo_forall_contMDiff_of_locally_contMDiffOn_tangentSection_compact`.  All references to the
trivialization live inside this abstract vector-bundle statement, so the flow assembly need only apply
it (with the tangent bundle) without instantiating any trivialization by hand. -/
theorem exists_isOpen_contMDiffOn_raisedGaugeField_tangentSection
    (g : ℝ → Bundle.ContMDiffRiemannianMetric IB n F V)
    (ω : ℝ → ∀ y : B, V y →L[ℝ] ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (bas : Module.Basis ι ℝ F)
    (hg : ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] V y →L[ℝ] ℝ)) p.2 ((g p.1).inner p.2)))
    (hω : ContMDiff (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F →L[ℝ] ℝ)) n
      (fun p : ℝ × B ↦ TotalSpace.mk' (F →L[ℝ] ℝ)
        (E := fun (y : B) ↦ (V y →L[ℝ] ℝ)) p.2 (ω p.1 p.2)))
    (x : B) :
    ∃ s : Set B, IsOpen s ∧ x ∈ s ∧
      ContMDiffOn (𝓘(ℝ).prod IB) (IB.prod 𝓘(ℝ, F)) n
        (fun p : ℝ × B ↦ TotalSpace.mk' F p.2 (raisedGaugeField (g p.1) (ω p.1) bas p.2))
        (Set.univ ×ˢ s) :=
  ⟨(trivializationAt F V x).baseSet, (trivializationAt F V x).open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt' x,
    contMDiffOn_raisedGaugeField_tangentSection g ω bas hg hω x⟩

end Gram

end PoincareCurvature.ParametrizedInner
