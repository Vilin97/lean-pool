/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame
public import Mathlib.Topology.VectorBundle.Hom
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Module.TransferInstance
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Continuity criteria for vector-bundle sections

This file adds repo-local `C^0` analogues of mathlib's local-frame smoothness
criteria for sections of finite-rank vector bundles.

The main point is that on an open trivializing set, continuity of a section is
equivalent to continuity of its local-frame coefficient functions. This is the
first bridge from continuous bundle sections to compact-space `ContinuousMap`
techniques, which are needed for later function-space work toward point 4.
-/

@[expose] public noncomputable section

open Bundle Module
open scoped Bundle Manifold ContDiff Topology

namespace PoincareCurvature

namespace Bundle.Trivialization

section

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {e : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e]
  {ι : Type*} (b : Basis ι 𝕜 F) {s : Π x : M, V x} {t : Set M}

/-- Each section in the local frame induced by a compatible trivialization is continuous on the
trivialization domain. -/
lemma continuousOn_localFrame_baseSet [ContMDiffVectorBundle 1 F V I] (i : ι) :
    ContinuousOn (T% (e.localFrame b i)) e.baseSet := by
  simpa using
    (show ContinuousOn (T% (e.localFrame b i)) e.baseSet from
      (e.contMDiffOn_localFrame_baseSet (I := I) (n := (1 : WithTop ℕ∞)) b i).continuousOn)

/-- If a section is continuous on an open subset of a trivialization domain, then each local-frame
coefficient function is continuous there. -/
lemma continuousOn_localFrameCoeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) (hs : ContinuousOn (T% s) t) (i : ι) :
    ContinuousOn ((LinearMap.piApply (e.localFrameCoeff I b i)) s) t := by
  have hs' : CMDiff[t] (0 : WithTop ℕ∞) (T% s) := by
    rwa [contMDiffOn_zero_iff]
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_localFrameCoeff (I := I) (e := e) (b := b) (t := t)
      (k := (0 : WithTop ℕ∞)) ht ht' hs' i)

/-- On an open subset of a trivialization domain, a section is continuous iff each local-frame
coefficient function is continuous. -/
lemma continuousOn_iff_localFrameCoeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (ht : IsOpen t) (ht' : t ⊆ e.baseSet) :
    ContinuousOn (T% s) t ↔
      ∀ i, ContinuousOn ((LinearMap.piApply (e.localFrameCoeff I b i)) s) t := by
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_iff_localFrameCoeff (I := I) (e := e) (b := b) (t := t)
      (k := (0 : WithTop ℕ∞)) ht ht')

/-- On a trivialization domain, a section is continuous iff each local-frame coefficient function is
continuous. -/
lemma continuousOn_baseSet_iff_localFrameCoeff
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] :
    ContinuousOn (T% s) e.baseSet ↔
      ∀ i, ContinuousOn ((LinearMap.piApply (e.localFrameCoeff I b i)) s) e.baseSet := by
  simpa [contMDiffOn_zero_iff] using
    (contMDiffOn_baseSet_iff_localFrameCoeff (I := I) (e := e) (b := b)
      (s := s) (k := (0 : WithTop ℕ∞)))

/-- Package a continuous section, read in a compatible trivialization, as an `F`-valued continuous
map on a compact subset of the trivialization domain. -/
def coordContinuousMap (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) : C(K, F) where
  toFun x := (e ((T% s) x.1)).2
  continuous_toFun := by
    have htriv : ContinuousOn (fun y ↦ e ((T% s) y)) e.baseSet := by
      refine e.continuousOn.comp hs ?_
      intro y hy
      simpa [e.mem_source] using hy
    have hcoord : ContinuousOn (fun y ↦ (e ((T% s) y)).2) e.baseSet :=
      continuous_snd.comp_continuousOn htriv
    exact continuousOn_iff_continuous_domRestrict.mp (hcoord.mono hK)

@[simp]
lemma coordContinuousMap_apply (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (x : K) :
    coordContinuousMap (e := e) K hK hs x = (e ((T% s) x.1)).2 := rfl

/-- Package the coordinate change on a compact overlap piece as an `F`-valued endomorphism of
continuous coordinate maps. -/
def coordChangeContinuousMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u : C(K, F)) : C(K, F) where
  toFun x := e.coordChangeL 𝕜 e' x.1 (u x)
  continuous_toFun := by
    have hchg : ContinuousOn (fun b ↦ Trivialization.coordChangeL 𝕜 e e' b : M → F →L[𝕜] F) (e.baseSet ∩ e'.baseSet) :=
      continuousOn_coordChange (R := 𝕜) (e := e) (e' := e')
    have hchg' : Continuous fun x : K ↦ (Trivialization.coordChangeL 𝕜 e e' x.1 : F →L[𝕜] F) := by
      exact continuousOn_iff_continuous_domRestrict.mp (hchg.mono hK)
    exact hchg'.clm_apply u.continuous

@[simp]
lemma coordChangeContinuousMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u : C(K, F)) (x : K) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u x =
      e.coordChangeL 𝕜 e' x.1 (u x) := rfl

/-- Bundle the overlap coordinate change itself as an operator-valued continuous map. -/
def coordChangeLContinuousMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    C(K, F →L[𝕜] F) where
  toFun x := e.coordChangeL 𝕜 e' x.1
  continuous_toFun := by
    have hchg : ContinuousOn (fun b ↦ Trivialization.coordChangeL 𝕜 e e' b : M → F →L[𝕜] F)
        (e.baseSet ∩ e'.baseSet) :=
      continuousOn_coordChange (R := 𝕜) (e := e) (e' := e')
    exact continuousOn_iff_continuous_domRestrict.mp (hchg.mono hK)

@[simp]
lemma coordChangeLContinuousMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) (x : K) :
    coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x = e.coordChangeL 𝕜 e' x.1 :=
  rfl

/-- The compact overlap coordinate change, packaged as a continuous linear operator on `C(K, F)`. -/
def coordChangeContinuousLinearMap
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    C(K, F) →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK
      map_add' := by
        intro u v
        ext x
        simp [coordChangeContinuousMap, map_add]
      map_smul' := by
        intro c u
        ext x
        simp [coordChangeContinuousMap, map_smul] }
    ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖
    (fun u ↦ by
      refine (ContinuousMap.norm_le (f := coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u)
        (by positivity : 0 ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖ * ‖u‖)).mpr ?_
      intro x
      calc
        ‖coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u x‖ =
            ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x (u x)‖ := by
              rfl
        _ ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK x‖ * ‖u x‖ := by
              exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK‖ * ‖u‖ := by
              gcongr
              · exact (coordChangeLContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK).norm_coe_le_norm x
              · exact u.norm_coe_le_norm x)

@[simp]
lemma coordChangeContinuousLinearMap_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) (u : C(K, F)) :
    coordChangeContinuousLinearMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u :=
  by
    change coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u
    rfl

/-- On compact overlap pieces, the packaged coordinate maps from two trivializations are related
pointwise by the bundle coordinate change. -/
lemma coordContinuousMap_coordChangeL_apply
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s) e'.baseSet) (x : K) :
    e.coordChangeL 𝕜 e' x.1 (coordContinuousMap (e := e) K (fun _ hy ↦ (hK hy).1) hs x) =
      coordContinuousMap (e := e') K (fun _ hy ↦ (hK hy).2) hs' x := by
  have hsymm : e.symm x.1 ((e ((T% s) x.1)).2) = s x.1 := by
    simpa using e.symm_apply_apply_mk (hK x.2).1 (s x.1)
  rw [e.coordChangeL_apply (R := 𝕜) e' (hK x.2)]
  simp [coordContinuousMap, hsymm]

/-- On compact overlap pieces, the packaged coordinate maps from two trivializations are related by
the coordinate-change operator as an equality of continuous maps. -/
lemma coordContinuousMap_coordChangeL
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s) e'.baseSet) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK
        (coordContinuousMap (e := e) K (fun _ hy ↦ (hK hy).1) hs) =
      coordContinuousMap (e := e') K (fun _ hy ↦ (hK hy).2) hs' := by
  ext x
  exact coordContinuousMap_coordChangeL_apply (𝕜 := 𝕜) (e := e) (e' := e')
    K hK hs hs' x

@[simp]
lemma coordChangeContinuousMap_zero
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (0 : C(K, F)) = 0 := by
  ext x
  simp [coordChangeContinuousMap]

@[simp]
lemma coordChangeContinuousMap_add
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (u v : C(K, F)) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (u + v) =
      coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u +
        coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK v := by
  ext x
  simp [coordChangeContinuousMap, map_add]

@[simp]
lemma coordChangeContinuousMap_smul
    {e' : Trivialization F (TotalSpace.proj : TotalSpace F V → M)} [MemTrivializationAtlas e']
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet ∩ e'.baseSet)
    (c : 𝕜) (u : C(K, F)) :
    coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK (c • u) =
      c • coordChangeContinuousMap (𝕜 := 𝕜) (e := e) (e' := e') K hK u := by
  ext x
  simp [coordChangeContinuousMap, map_smul]

/-- The inclusion of one compact subset into a larger one, bundled as a continuous map. -/
def compactSubsetInclusion {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) : C(K, L) where
  toFun x := ⟨x.1, hKL x.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
lemma compactSubsetInclusion_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (x : K) :
    compactSubsetInclusion hKL x = ⟨x.1, hKL x.2⟩ := rfl

/-- Restrict a continuous map on a compact set to a smaller compact subset. -/
def restrictToCompact {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) : C(K, F) :=
  u.comp (compactSubsetInclusion hKL)

@[simp]
lemma restrictToCompact_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) (x : K) :
    restrictToCompact hKL u x = u ⟨x.1, hKL x.2⟩ := rfl

@[simp]
lemma restrictToCompact_coordContinuousMap {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (hL : (L : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) :
    restrictToCompact hKL (coordContinuousMap (e := e) L hL hs) =
      coordContinuousMap (e := e) K (fun _ hx ↦ hL (hKL hx)) hs := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_zero {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) :
    restrictToCompact hKL (0 : C(L, F)) = 0 := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_add {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u v : C(L, F)) :
    restrictToCompact hKL (u + v) = restrictToCompact hKL u + restrictToCompact hKL v := by
  ext x
  rfl

@[simp]
lemma restrictToCompact_smul {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (c : 𝕜) (u : C(L, F)) :
    restrictToCompact hKL (c • u) = c • restrictToCompact hKL u := by
  ext x
  rfl

/-- Restriction to a smaller compact set, packaged as a continuous linear map. -/
def restrictToCompactContinuousLinearMap {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) : C(L, F) →L[𝕜] C(K, F) :=
  LinearMap.mkContinuous
    { toFun := restrictToCompact hKL
      map_add' := by
        intro u v
        ext x
        rfl
      map_smul' := by
        intro c u
        ext x
        rfl }
    1
    (fun u ↦ by
      refine (ContinuousMap.norm_le (f := restrictToCompact hKL u)
        (by positivity : 0 ≤ (1 : ℝ) * ‖u‖)).mpr ?_
      intro x
      simpa [one_mul, restrictToCompact_apply] using u.norm_coe_le_norm ⟨x.1, hKL x.2⟩)

@[simp]
lemma restrictToCompactContinuousLinearMap_apply {K L : TopologicalSpace.Compacts M}
    (hKL : (K : Set M) ⊆ (L : Set M)) (u : C(L, F)) :
    restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) hKL u = restrictToCompact hKL u := by
  change restrictToCompact hKL u = restrictToCompact hKL u
  rfl

/-- Package the `i`-th local-frame coefficient of a continuous section as a continuous map on a
compact subset of a trivialization domain. -/
def localFrameCoeffContinuousMap
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (i : ι) : C(K, 𝕜) where
  toFun x := e.localFrameCoeff I b i x.1 (s x.1)
  continuous_toFun := by
    have hcoeff : ContinuousOn ((LinearMap.piApply (e.localFrameCoeff I b i)) s) e.baseSet :=
      (continuousOn_baseSet_iff_localFrameCoeff (I := I) (e := e) (b := b) (s := s)).mp hs i
    exact continuousOn_iff_continuous_domRestrict.mp (hcoeff.mono hK)

@[simp]
lemma localFrameCoeffContinuousMap_apply
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (i : ι) (x : K) :
    localFrameCoeffContinuousMap (I := I) (e := e) b K hK hs i x =
      e.localFrameCoeff I b i x.1 (s x.1) := rfl

/-- The pointwise local-frame reconstruction formula can be read directly from the packaged
coefficient maps on a compact subset of the trivialization domain. -/
lemma eq_sum_localFrameCoeffContinuousMap_smul
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] [Fintype ι]
    (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (x : K) :
    s x.1 = ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) b K hK hs i x • e.localFrame b i x.1 := by
  simpa [localFrameCoeffContinuousMap] using
    (e.eq_sum_localFrameCoeff_smul (I := I) (b := b) (s := s) (x' := x.1) (hK x.2))

/-- On a compact subset of a trivialization domain, a continuous section is completely determined by
its packaged local-frame coefficient maps. -/
lemma eqOn_compact_iff_localFrameCoeffContinuousMap_eq
    [FiniteDimensional 𝕜 F] [CompleteSpace 𝕜] [ContMDiffVectorBundle 1 F V I] [Fintype ι]
    {s' : Π x : M, V x} (K : TopologicalSpace.Compacts M) (hK : (K : Set M) ⊆ e.baseSet)
    (hs : ContinuousOn (T% s) e.baseSet) (hs' : ContinuousOn (T% s') e.baseSet) :
    (∀ x ∈ (K : Set M), s x = s' x) ↔
      ∀ i,
        localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i =
          localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i := by
  constructor
  · intro h i
    ext x
    simpa [localFrameCoeffContinuousMap] using
      (e.localFrameCoeff_congr (I := I) (b := b) (s := s) (s' := s') (x := x.1) (i := i)
        (h x.1 x.2))
  · intro h x hx
    let xK : K := ⟨x, hx⟩
    calc
      s x =
          ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i xK •
            e.localFrame b i x := by
            simpa [xK] using
              (eq_sum_localFrameCoeffContinuousMap_smul (I := I) (e := e) (b := b) (s := s)
                K hK hs xK)
      _ =
          ∑ i, localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i xK •
            e.localFrame b i x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hix :
                localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s) K hK hs i xK =
                  localFrameCoeffContinuousMap (I := I) (e := e) (b := b) (s := s') K hK hs' i xK := by
              simpa using congrArg (fun f => f xK) (h i)
            rw [hix]
      _ = s' x := by
            symm
            simpa [xK] using
              (eq_sum_localFrameCoeffContinuousMap_smul (I := I) (e := e) (b := b) (s := s')
                K hK hs' xK)

section CoverCompatibility

/-- A family of compact coordinate maps, one on each compact trivializing piece. -/
abbrev CoordFamily {κ : Type*} (Kc : κ → TopologicalSpace.Compacts M) := ∀ i, C(Kc i, F)

instance coordFamilyCompleteSpace {κ : Type*} [Fintype κ]
    (Kc : κ → TopologicalSpace.Compacts M) [CompleteSpace F] :
    CompleteSpace (CoordFamily (F := F) Kc) := by
  dsimp [CoordFamily]
  infer_instance

/-- Compatibility of a compact coordinate family on pairwise overlap pieces. -/
def CoordFamilyCompatible
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) : Prop :=
  ∀ i j,
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
      (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
    restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)

/-- The subtype of compact coordinate families satisfying the overlap compatibility relations. -/
def CompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :=
  {u : CoordFamily (F := F) Kc //
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)}

/-- Package a continuous section as a family of compact coordinate maps along a trivializing family. -/
def coordFamilyOfSection
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (hs : Continuous (T% s)) : CoordFamily (F := F) Kc :=
  fun i ↦ coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn

/-- The compact coordinate family associated to a continuous section satisfies the overlap
compatibility relations. -/
lemma coordFamilyOfSection_compatible
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1)
          (coordFamilyOfSection (s := s) et Kc hKc hs i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2)
        (coordFamilyOfSection (s := s) et Kc hKc hs j) := by
  intro i j
  have hleft :
      restrictToCompact (fun _ hx ↦ (hKo i j hx).1)
          (coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn) =
        coordContinuousMap (e := et i) (Ko i j)
          (fun _ hx ↦ hKc i ((hKo i j hx).1)) hs.continuousOn := by
    exact restrictToCompact_coordContinuousMap
      (e := et i) (s := s) (K := Ko i j) (L := Kc i)
      (fun _ hx ↦ (hKo i j hx).1) (hKc i) hs.continuousOn
  have hright :
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2)
          (coordContinuousMap (e := et j) (Kc j) (hKc j) hs.continuousOn) =
        coordContinuousMap (e := et j) (Ko i j)
          (fun _ hx ↦ hKc j ((hKo i j hx).2)) hs.continuousOn := by
    exact restrictToCompact_coordContinuousMap
      (e := et j) (s := s) (K := Ko i j) (L := Kc j)
      (fun _ hx ↦ (hKo i j hx).2) (hKc j) hs.continuousOn
  change
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1)
          (coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2)
        (coordContinuousMap (e := et j) (Kc j) (hKc j) hs.continuousOn)
  rw [hleft, hright]
  exact coordContinuousMap_coordChangeL
    (𝕜 := 𝕜) (e := et i) (e' := et j) (K := Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
      hs.continuousOn hs.continuousOn

/-- The compatible compact coordinate family associated to a continuous section. -/
def compatibleCoordFamilyOfSection
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    {u : CoordFamily (F := F) Kc //
      ∀ i j,
        coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
          (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
          (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
        restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)} :=
  ⟨coordFamilyOfSection (s := s) et Kc hKc hs,
    coordFamilyOfSection_compatible (s := s) et Kc hKc Ko hKo hs⟩

/-- A family of compact overlap defects, one for each ordered pair of compact pieces. -/
abbrev OverlapFamily {κ : Type*} (Ko : κ → κ → TopologicalSpace.Compacts M) :=
  ∀ i j, C(Ko i j, F)

instance overlapFamilyCompleteSpace {κ : Type*} [Fintype κ]
    (Ko : κ → κ → TopologicalSpace.Compacts M) [CompleteSpace F] :
    CompleteSpace (OverlapFamily (F := F) Ko) := by
  dsimp [OverlapFamily]
  infer_instance

/-- The overlap defect of a compact coordinate family: it vanishes exactly when the family is
compatible. -/
def coordFamilyCompatibilityError
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) : OverlapFamily (F := F) Ko :=
  fun i j ↦
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
      (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) -
    restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)

/-- Compatibility is equivalent to vanishing of the overlap defect family. -/
lemma coordFamilyCompatible_iff_coordFamilyCompatibilityError_eq_zero
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc} :
    CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u ↔
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u = 0 := by
  constructor
  · intro hu
    funext i j
    exact sub_eq_zero.mpr (hu i j)
  · intro hu i j
    exact sub_eq_zero.mp (congrArg (fun f => f i j) hu)

/-- The overlap defect is linear in the compact coordinate family. -/
def coordFamilyCompatibilityLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CoordFamily (F := F) Kc →ₗ[𝕜] OverlapFamily (F := F) Ko where
  toFun := coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  map_add' u v := by
    funext i j
    apply ContinuousMap.ext
    intro x
    change
      (et i).coordChangeL 𝕜 (et j) x
          ((u i) ⟨x, (hKo i j x.2).1⟩ + (v i) ⟨x, (hKo i j x.2).1⟩) -
        ((u j) ⟨x, (hKo i j x.2).2⟩ + (v j) ⟨x, (hKo i j x.2).2⟩) =
      ((et i).coordChangeL 𝕜 (et j) x ((u i) ⟨x, (hKo i j x.2).1⟩) -
          (u j) ⟨x, (hKo i j x.2).2⟩) +
        ((et i).coordChangeL 𝕜 (et j) x ((v i) ⟨x, (hKo i j x.2).1⟩) -
          (v j) ⟨x, (hKo i j x.2).2⟩)
    rw [map_add]
    abel
  map_smul' c u := by
    funext i j
    apply ContinuousMap.ext
    intro x
    change
      (et i).coordChangeL 𝕜 (et j) x
          (c • (u i) ⟨x, (hKo i j x.2).1⟩) - c • (u j) ⟨x, (hKo i j x.2).2⟩ =
        c • ((et i).coordChangeL 𝕜 (et j) x ((u i) ⟨x, (hKo i j x.2).1⟩) -
          (u j) ⟨x, (hKo i j x.2).2⟩)
    rw [map_smul, smul_sub]

/-- The compact coordinate families satisfying the overlap equations form the kernel of the overlap
defect map. -/
def compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    Submodule 𝕜 (CoordFamily (F := F) Kc) :=
  (coordFamilyCompatibilityLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).ker

/-- Membership in the compatibility submodule is exactly the overlap compatibility condition. -/
lemma mem_compatibleCoordFamilySubmodule_iff
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc} :
    u ∈ compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo ↔
      CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u := by
  change coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u = 0 ↔
    CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u
  exact
    (coordFamilyCompatible_iff_coordFamilyCompatibilityError_eq_zero
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo (u := u)).symm

/-- The compact coordinate family of a continuous section lies in the compatibility kernel. -/
lemma coordFamilyOfSection_mem_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hs : Continuous (T% s)) :
    coordFamilyOfSection (s := s) et Kc hKc hs ∈
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo := by
  rw [mem_compatibleCoordFamilySubmodule_iff]
  exact coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs

/-- The `(i,j)` overlap defect component, packaged as a continuous linear map on compact coordinate
families. -/
def coordFamilyCompatibilityComponentContinuousLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (i j : κ) : CoordFamily (F := F) Kc →L[𝕜] C(Ko i j, F) :=
  (coordChangeContinuousLinearMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
      (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)).comp
    ((restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) (fun _ hx ↦ (hKo i j hx).1)).comp
      (ContinuousLinearMap.proj i))
    -
  (restrictToCompactContinuousLinearMap (𝕜 := 𝕜) (F := F) (fun _ hx ↦ (hKo i j hx).2)).comp
    (ContinuousLinearMap.proj j)

@[simp]
lemma coordFamilyCompatibilityComponentContinuousLinearMap_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (i j : κ) (u : CoordFamily (F := F) Kc) :
    coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
      i j u =
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j := by
  ext x
  change
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) x -
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j) x =
    coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) x -
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j) x
  rfl

/-- The full overlap defect map, packaged as a continuous linear map into the family of compact
overlap defects. -/
def coordFamilyCompatibilityContinuousLinearMap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CoordFamily (F := F) Kc →L[𝕜] OverlapFamily (F := F) Ko where
  toLinearMap := coordFamilyCompatibilityLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  cont := by
    refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
    have hcomp : Continuous fun u ↦
      coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        i j u :=
      (coordFamilyCompatibilityComponentContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        i j).continuous
    simpa [coordFamilyCompatibilityLinearMap, coordFamilyCompatibilityError] using hcomp

@[simp]
lemma coordFamilyCompatibilityContinuousLinearMap_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc) (i j : κ) :
    coordFamilyCompatibilityContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j =
      coordFamilyCompatibilityError (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u i j := rfl

/-- The compatibility kernel is closed because it is the kernel of a continuous linear map. -/
lemma isClosed_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    IsClosed
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) := by
  change IsClosed
    ((coordFamilyCompatibilityContinuousLinearMap (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).ker :
      Set (CoordFamily (F := F) Kc))
  exact ContinuousLinearMap.isClosed_ker _

/-- The compatibility kernel is complete as soon as the ambient coordinate-family space is. -/
lemma isComplete_compatibleCoordFamilySubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [CompleteSpace (CoordFamily (F := F) Kc)] :
    IsComplete
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) := by
  exact (isClosed_compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).isComplete

instance compatibleCoordFamilySubmodule.completeSpace
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    [CompleteSpace (CoordFamily (F := F) Kc)] :
    CompleteSpace (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) := by
  letI : IsClosed
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :
        Set (CoordFamily (F := F) Kc)) :=
    isClosed_compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
  infer_instance

/-- A total-space valued map whose first coordinate is always the base point determines a genuine
section. -/
noncomputable def sectionOfTotalSpaceMap (f : M → TotalSpace F V)
    (hf : ∀ x, (f x).1 = x) : Π x : M, V x :=
  fun x ↦ cast (congrArg V (hf x)) (f x).2

/-- The total-space map attached to `sectionOfTotalSpaceMap` is the original map. -/
lemma totalSpace_sectionOfTotalSpaceMap (f : M → TotalSpace F V) (hf : ∀ x, (f x).1 = x) :
    T% (sectionOfTotalSpaceMap (V := V) f hf) = f := by
  funext x
  refine Bundle.TotalSpace.ext (hf x).symm ?_
  change cast (congrArg V (hf x)) (f x).2 ≍ (f x).2
  exact (cast_heq_iff_heq (congrArg V (hf x)) (f x).2 (f x).2).2 HEq.rfl

/-- Read a compact coordinate family back as a total-space valued map on a single compact piece. -/
def totalSpaceMapOnCompactOfCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (u : CoordFamily (F := F) Kc) (i : κ) : C(Kc i, TotalSpace F V) where
  toFun x := ⟨x.1, (et i).symm x.1 (u i x)⟩
  continuous_toFun := by
    have hpair : Continuous fun x : Kc i ↦ (x.1, u i x) := continuous_subtype_val.prodMk (u i).continuous
    exact (et i).continuousOn_symm.comp_continuous hpair fun x ↦
      Set.mk_mem_prod (hKc i x.2) (Set.mem_univ _)

@[simp]
lemma totalSpaceMapOnCompactOfCoordFamily_apply
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (u : CoordFamily (F := F) Kc) (i : κ) (x : Kc i) :
    totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x =
      ⟨x.1, (et i).symm x.1 (u i x)⟩ :=
  rfl

/-- On full compact overlaps, the local total-space maps reconstructed from a compatible coordinate
family agree. -/
lemma totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    {u : CoordFamily (F := F) Kc}
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    {i j : κ} {x : M} (hxi : x ∈ (Kc i : Set M)) (hxj : x ∈ (Kc j : Set M)) :
    totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i ⟨x, hxi⟩ =
      totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u j ⟨x, hxj⟩ := by
  have hxKo : x ∈ (Ko i j : Set M) := by
    rw [hKoEq i j]
    exact ⟨hxi, hxj⟩
  let xKo : Ko i j := ⟨x, hxKo⟩
  have hcoord :
      (et i).coordChangeL 𝕜 (et j) x (u i ⟨x, hxi⟩) = u j ⟨x, hxj⟩ := by
    have h := congrArg (fun f ↦ f xKo) (hu i j)
    change
      (et i).coordChangeL 𝕜 (et j) x
          (u i ⟨x, (hKo i j hxKo).1⟩) =
        u j ⟨x, (hKo i j hxKo).2⟩ at h
    have hxi' : (⟨x, (hKo i j hxKo).1⟩ : Kc i) = ⟨x, hxi⟩ := by
      apply Subtype.ext
      rfl
    have hxj' : (⟨x, (hKo i j hxKo).2⟩ : Kc j) = ⟨x, hxj⟩ := by
      apply Subtype.ext
      rfl
    simpa [hxi', hxj'] using h
  have hb : x ∈ (et i).baseSet ∩ (et j).baseSet := ⟨hKc i hxi, hKc j hxj⟩
  change (⟨x, (et i).symm x (u i ⟨x, hxi⟩)⟩ : TotalSpace F V) =
    ⟨x, (et j).symm x (u j ⟨x, hxj⟩)⟩
  apply congrArg (fun v ↦ (⟨x, v⟩ : TotalSpace F V))
  calc
      (et i).symm x (u i ⟨x, hxi⟩) =
          (et j).symm x ((et i).coordChangeL 𝕜 (et j) x (u i ⟨x, hxi⟩)) := by
            rw [(et i).coordChangeL_apply (R := 𝕜) (e' := et j) hb]
            simpa using ((et j).symm_apply_apply_mk hb.2 ((et i).symm x (u i ⟨x, hxi⟩))).symm
      _ = (et j).symm x (u j ⟨x, hxj⟩) := by rw [hcoord]

/-- Glue a compatible compact coordinate family into a total-space valued map on the base. -/
noncomputable def totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    M → TotalSpace F V :=
  Set.liftCover (fun i => (Kc i : Set M))
    (fun i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i)
    (fun _ _ _ hxi hxj =>
      totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hu hxi hxj)
    hcover

@[simp]
lemma totalSpaceMapOfCompatibleCoordFamily_of_mem
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {i : κ} {x : M} (hx : x ∈ (Kc i : Set M)) :
    totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover x =
      totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i ⟨x, hx⟩ := by
  simpa [totalSpaceMapOfCompatibleCoordFamily] using
    (Set.liftCover_of_mem
      (S := fun i => (Kc i : Set M))
      (f := fun i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i)
      (hf := fun i j x hxi hxj =>
        totalSpaceMapOnCompactOfCoordFamily_eq_on_overlap
          (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hu hxi hxj)
      (hS := hcover) (i := i) (x := x) hx)

@[simp]
lemma proj_totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) (x : M) :
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover x).1 =
      x := by
  have hx : x ∈ (⋃ i, (Kc i : Set M)) := by simp [hcover]
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  simpa [totalSpaceMapOnCompactOfCoordFamily] using
    congrArg Bundle.TotalSpace.proj
      (totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x) hxi)

/-- On a finite compact cover of a Hausdorff base, the glued total-space map is continuous. -/
lemma continuous_totalSpaceMapOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Continuous (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) := by
  let S : κ → Set M := fun i => (Kc i : Set M)
  let g : M → TotalSpace F V :=
    totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover
  let hlf : LocallyFinite S := locallyFinite_of_finite S
  refine hlf.continuous hcover ?_ ?_
  · intro i
    exact (Kc i).isCompact.isClosed
  · intro i
    rw [continuousOn_iff_continuous_domRestrict]
    have hrestrict :
        (S i).domRestrict g =
          fun x : S i => totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x := by
      funext x
      exact totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x.1) x.2
    rw [hrestrict]
    simpa [S, totalSpaceMapOnCompactOfCoordFamily] using
      (totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i).continuous

/-- Reconstruct a section from a compatible compact coordinate family on a covering compact
trivializing family. -/
noncomputable def sectionOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Π x : M, V x :=
  sectionOfTotalSpaceMap (V := V)
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
    (proj_totalSpaceMapOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)

@[simp]
lemma totalSpace_sectionOfCompatibleCoordFamily
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) =
      totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover :=
  totalSpace_sectionOfTotalSpaceMap (V := V)
    (totalSpaceMapOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
    (proj_totalSpaceMapOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)

/-- The reconstructed section has continuous total-space map on a finite compact cover of a Hausdorff
base. -/
lemma continuous_sectionOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Continuous (T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)) := by
  rw [totalSpace_sectionOfCompatibleCoordFamily]
  exact continuous_totalSpaceMapOfCompatibleCoordFamily
    (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover

/-- Reconstructing a section from a compatible compact coordinate family recovers that family. -/
lemma coordFamilyOfSection_sectionOfCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (u : CoordFamily (F := F) Kc)
    (hu : CoordFamilyCompatible (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u)
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    coordFamilyOfSection
        (s := sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover)
        et Kc hKc
        (continuous_sectionOfCompatibleCoordFamily
          (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) =
      u := by
  funext i
  ext x
  have htx :
      T% (sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover) x.1 =
        totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x := by
    rw [totalSpace_sectionOfCompatibleCoordFamily]
    simpa using
      (totalSpaceMapOfCompatibleCoordFamily_of_mem
        (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u hu hKoEq hcover (i := i) (x := x.1) x.2)
  have hcoord :
      (et i (totalSpaceMapOnCompactOfCoordFamily (F := F) et Kc hKc u i x)).2 = u i x := by
    simpa [totalSpaceMapOnCompactOfCoordFamily] using
      congrArg Prod.snd ((et i).apply_mk_symm (hKc i x.2) (u i x))
  simpa [coordFamilyOfSection, coordContinuousMap, htx] using hcoord

/-- The zero coordinate family is compatible on overlaps. -/
lemma coordFamilyCompatible_zero
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (0 : C(Kc i, F))) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (0 : C(Kc j, F)) := by
  intro i j
  ext x
  change (et i).coordChangeL 𝕜 (et j) x 0 = 0
  exact map_zero _

/-- Compatibility on overlaps is preserved by addition of coordinate families. -/
lemma coordFamilyCompatible_add
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {u v : CoordFamily (F := F) Kc}
    (hu : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j))
    (hv : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (v i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (v j)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) ((u + v) i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) ((u + v) j) := by
  intro i j
  ext x
  have hux := congrArg (fun f => f x) (hu i j)
  have hvx := congrArg (fun f => f x) (hv i j)
  change
    (et i).coordChangeL 𝕜 (et j) x
        ((u i) ⟨x, (hKo i j x.2).1⟩ + (v i) ⟨x, (hKo i j x.2).1⟩) =
      (u j) ⟨x, (hKo i j x.2).2⟩ + (v j) ⟨x, (hKo i j x.2).2⟩
  change
    (et i).coordChangeL 𝕜 (et j) x ((u i) ⟨x, (hKo i j x.2).1⟩) =
      (u j) ⟨x, (hKo i j x.2).2⟩ at hux
  change
    (et i).coordChangeL 𝕜 (et j) x ((v i) ⟨x, (hKo i j x.2).1⟩) =
      (v j) ⟨x, (hKo i j x.2).2⟩ at hvx
  rw [map_add, hux, hvx]

/-- Compatibility on overlaps is preserved by scalar multiplication. -/
lemma coordFamilyCompatible_smul
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {u : CoordFamily (F := F) Kc} (c : 𝕜)
    (hu : ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) (u i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) (u j)) :
    ∀ i j,
      coordChangeContinuousMap (𝕜 := 𝕜) (e := et i) (e' := et j) (Ko i j)
        (fun _ hx ↦ ⟨hKc i ((hKo i j hx).1), hKc j ((hKo i j hx).2)⟩)
        (restrictToCompact (fun _ hx ↦ (hKo i j hx).1) ((c • u) i)) =
      restrictToCompact (fun _ hx ↦ (hKo i j hx).2) ((c • u) j) := by
  intro i j
  ext x
  have hux := congrArg (fun f => f x) (hu i j)
  change
    (et i).coordChangeL 𝕜 (et j) x (c • (u i) ⟨x, (hKo i j x.2).1⟩) =
      c • (u j) ⟨x, (hKo i j x.2).2⟩
  change
    (et i).coordChangeL 𝕜 (et j) x ((u i) ⟨x, (hKo i j x.2).1⟩) =
      (u j) ⟨x, (hKo i j x.2).2⟩ at hux
  rw [map_smul, hux]

/-- If two continuous sections have the same compact coordinate family, then they agree on the
union of the compact pieces. -/
lemma eqOn_iUnion_of_coordFamilyOfSection_eq
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    {s' : Π x : M, V x} (hs : Continuous (T% s)) (hs' : Continuous (T% s'))
    (hcoord : ∀ i,
      coordFamilyOfSection (s := s) et Kc hKc hs i =
        coordFamilyOfSection (s := s') et Kc hKc hs' i) :
    ∀ x ∈ (⋃ i, (Kc i : Set M)), s x = s' x := by
  intro x hx
  rcases Set.mem_iUnion.mp hx with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  have hix :
      coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn xK =
        coordContinuousMap (e := et i) (Kc i) (hKc i) hs'.continuousOn xK := by
    simpa [coordFamilyOfSection, xK] using congrArg (fun f => f xK) (hcoord i)
  have hsymm :
      (et i).symm x (coordContinuousMap (e := et i) (Kc i) (hKc i) hs.continuousOn xK) = s x := by
    simpa [coordContinuousMap, xK] using (et i).symm_apply_apply_mk (hKc i hxi) (s x)
  have hsymm' :
      (et i).symm x (coordContinuousMap (e := et i) (Kc i) (hKc i) hs'.continuousOn xK) = s' x := by
    simpa [coordContinuousMap, xK] using (et i).symm_apply_apply_mk (hKc i hxi) (s' x)
  rw [← hsymm, hix, hsymm']

/-- If the compact pieces cover the base, the compact coordinate family construction is injective. -/
lemma coordFamilyOfSection_injective
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    {s' : Π x : M, V x} (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (hs : Continuous (T% s)) (hs' : Continuous (T% s'))
    (hcoord : ∀ i,
      coordFamilyOfSection (s := s) et Kc hKc hs i =
        coordFamilyOfSection (s := s') et Kc hKc hs' i) :
    s = s' := by
  funext x
  exact eqOn_iUnion_of_coordFamilyOfSection_eq (et := et) (Kc := Kc) (hKc := hKc)
    (s := s) (s' := s') hs hs' hcoord x (by simp [hcover])

/-- Applying the reconstruction map to the compact coordinate family of a continuous section returns
the original section. -/
lemma sectionOfCompatibleCoordFamily_coordFamilyOfSection
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {s : Π x : M, V x} (hs : Continuous (T% s)) :
    sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        (coordFamilyOfSection (s := s) et Kc hKc hs)
        (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
        hKoEq hcover =
      s := by
  exact coordFamilyOfSection_injective
      (et := et) (Kc := Kc) (hKc := hKc)
      (s := sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
        (coordFamilyOfSection (s := s) et Kc hKc hs)
        (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
        hKoEq hcover)
      (s' := s) (hcover := hcover)
      (continuous_sectionOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
      (coordFamilyOfSection (s := s) et Kc hKc hs)
      (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
      hKoEq hcover)
      hs
      (by
        intro i
        simpa using
          congrArg (fun f => f i)
            (coordFamilyOfSection_sectionOfCompatibleCoordFamily
              (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo
              (coordFamilyOfSection (s := s) et Kc hKc hs)
              (coordFamilyOfSection_compatible (𝕜 := 𝕜) (s := s) et Kc hKc Ko hKo hs)
              hKoEq hcover))

/-- On a finite compact trivializing cover of a Hausdorff base, continuous sections are equivalent
to compatible compact coordinate families. -/
noncomputable def continuousSectionEquivCompatibleCoordFamily
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    {s : Π x : M, V x // Continuous (T% s)} ≃ CompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo where
  toFun s := compatibleCoordFamilyOfSection (𝕜 := 𝕜) (s := s.1) et Kc hKc Ko hKo s.2
  invFun u :=
    ⟨sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover,
      continuous_sectionOfCompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover⟩
  left_inv s := by
    apply Subtype.ext
    exact sectionOfCompatibleCoordFamily_coordFamilyOfSection
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover s.2
  right_inv u := by
    apply Subtype.ext
    exact coordFamilyOfSection_sectionOfCompatibleCoordFamily
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo u.1 u.2 hKoEq hcover

/-- The predicate-style compatible coordinate family type is equivalent to the corresponding kernel
submodule. -/
noncomputable def compatibleCoordFamilyEquivSubmodule
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)) :
    CompatibleCoordFamily (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo where
  toFun u :=
    ⟨u.1, (mem_compatibleCoordFamilySubmodule_iff
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).2 u.2⟩
  invFun u :=
    ⟨u.1, (mem_compatibleCoordFamilySubmodule_iff
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).1 u.2⟩
  left_inv u := by
    apply Subtype.ext
    rfl
  right_inv u := by
    apply Subtype.ext
    rfl

/-- Combining the finite-cover reconstruction equivalence with the kernel packaging identifies
continuous sections with the closed compatibility kernel itself. -/
noncomputable def continuousSectionEquivCompatibleCoordFamilySubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    {s : Π x : M, V x // Continuous (T% s)} ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :=
  (continuousSectionEquivCompatibleCoordFamily
    (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover).trans
    (compatibleCoordFamilyEquivSubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)

/-- Bundled continuous sections, viewed relative to a fixed finite compact trivializing cover. The
cover data appears in the type so that later transported normed-space instances depend on the chosen
section-space model rather than on the raw subtype of continuous sections. -/
structure ContinuousSectionSpace
    (𝕜 : Type*)
    [NontriviallyNormedField 𝕜]
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) where
  toFun : Π x : M, V x
  continuous_toFun : Continuous (T% toFun)

namespace ContinuousSectionSpace

instance
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ} :
    CoeFun (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
      (fun _ => Π x : M, V x) :=
  ⟨ContinuousSectionSpace.toFun⟩

@[ext]
theorem ext
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    (h : ∀ x : M, s x = t x) :
    s = t := by
  cases s with
  | mk sf sc =>
    cases t with
    | mk tf tc =>
      have hfun : sf = tf := funext h
      cases hfun
      rfl

@[simp]
lemma continuous
    {κ : Type*}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :
    Continuous (T% (s : Π x : M, V x)) := by
  simpa using s.continuous_toFun

/-- Forget the wrapper and recover the raw subtype of continuous sections. -/
def toSubtype
    {κ : Type*}
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover ≃
      {s : Π x : M, V x // Continuous (T% s)} where
  toFun s := ⟨s, s.continuous_toFun⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv s := by cases s; rfl
  right_inv s := by cases s; rfl

/-- The transported section space is equivalent to the closed compatibility-kernel submodule. -/
noncomputable def equivCompatibleCoordFamilySubmodule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover ≃
      compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo :=
  (toSubtype (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover).trans
    (continuousSectionEquivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover)

instance instAddCommGroup
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    AddCommGroup (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.addCommGroup

instance instModule
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    Module 𝕜 (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : AddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.module 𝕜

instance instNormedAddCommGroup
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedAddCommGroup (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  exact e.normedAddCommGroup

instance instNormedSpace
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    NormedSpace 𝕜 (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedSpace 𝕜
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedSpace
      (𝕜 := 𝕜) (R := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  exact e.normedSpace 𝕜

instance instCompleteSpace
    {κ : Type*} [Finite κ] [T2Space M] [CompleteSpace F]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    CompleteSpace (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  have hIso : Isometry e := by
    intro x y
    rfl
  exact (completeSpace_congr (e := e) hIso.isUniformEmbedding).2 inferInstance

/-- The coordinate-family representation of a continuous section as a continuous linear map. -/
noncomputable def toCompatibleCoordFamilySubmoduleContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      →L[𝕜] compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo := by
  let e := equivCompatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : NormedSpace 𝕜
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedSpace
      (𝕜 := 𝕜) (R := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  letI : AddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : Module 𝕜
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instModule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : NormedAddCommGroup
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedAddCommGroup (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  letI : NormedSpace 𝕜
      (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :=
    instNormedSpace (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo hKoEq hcover
  refine
    { toLinearMap :=
        { toFun := e
          map_add' := by
            intro s t
            change e (e.symm (e s + e t)) = e s + e t
            simp
          map_smul' := by
            intro c s
            change e (e.symm (c • e s)) = c • e s
            simp }
      cont := ?_ }
  have hIso : Isometry e := by
    intro s t
    rfl
  exact hIso.continuous

@[simp]
lemma toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    toCompatibleCoordFamilySubmoduleContinuousLinearMap
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s =
      equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s := rfl

/-- Read one compact coordinate component of a continuous section as a continuous linear map. -/
noncomputable def coordReadoutContinuousLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      →L[𝕜] F :=
  (ContinuousMap.evalCLM (R := 𝕜) (M := F) x).comp
    ((ContinuousLinearMap.proj i).comp
      (((compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo).subtypeL).comp
        (toCompatibleCoordFamilySubmoduleContinuousLinearMap
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)))

@[simp]
lemma coordReadoutContinuousLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (i : κ) (x : Kc i)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    coordReadoutContinuousLinearMap
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover i x s =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x := rfl

/-- Uniform control of every compact coordinate readout controls the transported finite-cover
section norm.  This is the basic bridge from fiberwise/local approximation estimates to the Banach
norm on `ContinuousSectionSpace`. -/
theorem dist_le_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) ≤ C) :
    dist s t ≤ C := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := by
    intro x y
    rfl
  rw [← he.dist_eq s t]
  change dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1) ≤ C
  rw [dist_pi_le_iff hC]
  intro i
  exact (ContinuousMap.dist_le hC).2 (hcoord i)

/-- Coordinatewise finite-cover Lipschitz estimates imply a `LipschitzOnWith` estimate for a
section-space map in the transported finite-cover norm.  This is the norm-level handoff needed when
local chart estimates control every compact coordinate readout of a vector field. -/
theorem lipschitzOnWith_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (hcoord : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
          ≤ (L : ℝ) * dist s t) :
    LipschitzOnWith L A stateSet := by
  refine LipschitzOnWith.of_dist_le_mul ?_
  intro s hs t ht
  exact dist_le_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := A s) (t := A t)
    (mul_nonneg (NNReal.coe_nonneg L) dist_nonneg)
    (fun i x => hcoord hs ht i x)

/-- A finite coordinate-family Lipschitz estimate gives the pointwise compact-coordinate
distance estimates expected by local chart handoffs. -/
theorem forall_coord_dist_le_of_coordFamily_lipschitzOnWith
    {κ : Type*} [Fintype κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (h : LipschitzOnWith L
      (fun s =>
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 :
            CoordFamily (F := F) Kc))
      stateSet) :
    ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet → ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
        ≤ (L : ℝ) * dist s t := by
  intro s hs t ht i x
  have hC : 0 ≤ (L : ℝ) * dist s t :=
    mul_nonneg (NNReal.coe_nonneg L) dist_nonneg
  have hdist := h.dist_le_mul s hs t ht
  have hi :
      dist
          (((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 :
              CoordFamily (F := F) Kc) i)
          (((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 :
              CoordFamily (F := F) Kc) i)
        ≤ (L : ℝ) * dist s t :=
    (dist_pi_le_iff hC).1 hdist i
  exact (ContinuousMap.dist_le hC).1 hi x

/-- Time-parameterized version of
`ContinuousSectionSpace.lipschitzOnWith_of_forall_coord_dist_le`: coordinatewise finite-cover
estimates on each time slice produce the corresponding family of section-space Lipschitz
estimates. -/
theorem lipschitzOnWith_family_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (hcoord : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ (L : ℝ) * dist s t) :
    ∀ τ ∈ timeSet, LipschitzOnWith L (A τ) stateSet := by
  intro τ hτ
  exact lipschitzOnWith_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ) (L := L)
    (fun s hs t ht i x => hcoord τ hτ hs ht i x)

/-- Time-parameterized version of
`ContinuousSectionSpace.forall_coord_dist_le_of_coordFamily_lipschitzOnWith`: finite coordinate
readout Lipschitz estimates on each time slice give the pointwise coordinate estimates consumed by
preferred-cover chart builders. -/
theorem forall_coord_dist_le_family_of_coordFamily_lipschitzOnWith
    {κ : Type*} [Fintype κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (h : ∀ τ, τ ∈ timeSet →
      LipschitzOnWith L
        (fun s =>
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 :
              CoordFamily (F := F) Kc))
        stateSet) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ (L : ℝ) * dist s t := by
  intro τ hτ
  exact forall_coord_dist_le_of_coordFamily_lipschitzOnWith
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ) (L := L) (h τ hτ)

/-- Strict coordinatewise control yields strict control in the transported finite-cover section
norm. -/
theorem dist_lt_of_forall_coord_dist_lt
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 < C)
    (hcoord : ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) < C) :
    dist s t < C := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := by
    intro x y
    rfl
  rw [← he.dist_eq s t]
  change dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1) < C
  rw [dist_pi_lt_iff hC]
  intro i
  exact (ContinuousMap.dist_lt_iff hC).2 (hcoord i)

/-- Fiberwise approximation estimates imply finite-cover section-space approximation when the
coordinate readouts are uniformly Lipschitz with respect to the chosen fiber distances.  This is the
bookkeeping form needed after bounding a finite trivializing family on compact sets. -/
theorem dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    {κ : Type*} [Finite κ] [T2Space M]
    [∀ x, PseudoMetricSpace (V x)]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {L η C : ℝ} (hL : 0 < L) (hC : 0 < C) (hLC : L * η < C)
    (hfiber : ∀ x : M, dist (s x) (t x) < η)
    (hcoordLip : ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ L * dist (s x.1) (t x.1)) :
    dist s t < C := by
  refine dist_lt_of_forall_coord_dist_lt
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := s) (t := t) hC ?_
  intro i x
  exact lt_of_le_of_lt (hcoordLip i x)
    ((mul_lt_mul_of_pos_left (hfiber x.1) hL).trans hLC)

/-- A fiberwise approximation theorem upgrades to approximation in the transported finite-cover
section norm once the finite coordinate readouts satisfy a uniform Lipschitz estimate. -/
theorem exists_dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    {κ : Type*} [Finite κ] [T2Space M]
    [∀ x, PseudoMetricSpace (V x)]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {P : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover → Prop}
    {L : ℝ} (hL : 0 < L)
    (happrox : ∀ η > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover,
        P u ∧ ∀ x : M, dist (s x) (u x) < η)
    (hcoordLip : ∀ u,
      P u →
      ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover u).1 i x)
          ≤ L * dist (s x.1) (u x.1)) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover,
        P u ∧ dist s u < ε := by
  intro ε hε
  let η : ℝ := ε / L / 2
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hLη : L * η < ε := by
    have hLne : L ≠ 0 := ne_of_gt hL
    have hcalc : L * η = ε / 2 := by
      dsimp [η]
      field_simp [hLne]
    rw [hcalc]
    linarith
  rcases happrox η hηpos with ⟨u, huP, hufiber⟩
  refine ⟨u, huP, ?_⟩
  exact dist_lt_of_forall_fiber_dist_lt_of_coord_lipschitz
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (s := s) (t := u) hL hε hLη hufiber (hcoordLip u huP)

/-- Two finite-cover section-space points are equal when all compact coordinate readouts agree. -/
theorem eq_of_coordReadout_eq
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    (hcoord : ∀ i (x : Kc i),
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x =
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x) :
    s = t := by
  apply (equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover).injective
  apply Subtype.ext
  funext i
  ext x
  exact hcoord i x

end ContinuousSectionSpace

end CoverCompatibility

end

namespace ContinuousSectionSpace

section TrivializationOpNorm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, SeminormedAddCommGroup (V x)] [∀ x, NormedSpace 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The compact coordinate readouts of two sections are Lipschitz with the op-norm of the
corresponding fiber trivialization. This turns a uniform bound on a finite family of
trivialization maps into the `hcoordLip` hypothesis used by the fiberwise approximation bridge. -/
theorem coord_dist_le_of_trivialization_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {L : ℝ}
    (hL : ∀ i (x : Kc i), ‖(et i).continuousLinearMapAt 𝕜 x.1‖ ≤ L)
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ L * dist (s x.1) (t x.1) := by
  intro i x
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have hx : x.1 ∈ (et i).baseSet := hKc i x.2
  have hscoord :
      ((e s).1 i x) = (et i).continuousLinearMapAt 𝕜 x.1 (s x.1) := by
    change (et i ((T% s) x.1)).2 =
      (et i).continuousLinearMapAt 𝕜 x.1 (s x.1)
    exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      (R := 𝕜) (e := et i) hx (s x.1)).symm
  have htcoord :
      ((e t).1 i x) = (et i).continuousLinearMapAt 𝕜 x.1 (t x.1) := by
    change (et i ((T% t) x.1)).2 =
      (et i).continuousLinearMapAt 𝕜 x.1 (t x.1)
    exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
      (R := 𝕜) (e := et i) hx (t x.1)).symm
  calc
    dist ((e s).1 i x) ((e t).1 i x)
        = dist ((et i).continuousLinearMapAt 𝕜 x.1 (s x.1))
            ((et i).continuousLinearMapAt 𝕜 x.1 (t x.1)) := by rw [hscoord, htcoord]
    _ ≤ ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * dist (s x.1) (t x.1) :=
      ContinuousLinearMap.dist_le_opNorm ((et i).continuousLinearMapAt 𝕜 x.1) (s x.1) (t x.1)
    _ ≤ L * dist (s x.1) (t x.1) := by
      exact mul_le_mul_of_nonneg_right (hL i x) dist_nonneg

/-- The compact coordinate readout of a section at a point of its trivializing piece is the
trivialization's fiberwise linear map applied to the pointwise value.  This is the named form of the
`hscoord`/`htcoord` computation used throughout the finite-cover norm bridge. -/
theorem coord_apply
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x =
      (et i).continuousLinearMapAt 𝕜 x.1 (s x.1) := by
  have hx : x.1 ∈ (et i).baseSet := hKc i x.2
  change (et i ((T% s) x.1)).2 =
    (et i).continuousLinearMapAt 𝕜 x.1 (s x.1)
  exact (Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
    (R := 𝕜) (e := et i) hx (s x.1)).symm

/-- Inversion of `coord_apply`: on a trivializing piece the pointwise value of a section is
recovered from its compact coordinate readout by the trivialization's backwards fiber map. -/
theorem apply_eq_symmL_coord
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    {i : κ} {x : M} (hi : x ∈ (Kc i : Set M)) :
    s x =
      (et i).symmL 𝕜 x
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i ⟨x, hi⟩) := by
  have hx : x ∈ (et i).baseSet := hKc i hi
  rw [coord_apply s i ⟨x, hi⟩]
  exact ((et i).symmL_continuousLinearMapAt hx (s x)).symm

/-- The algebraic zero section evaluates pointwise to zero. -/
theorem zero_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (x : M) :
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) x = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) hi]
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  rw [he0]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply, map_zero]

/-- The pointwise value of a sum of sections is the sum of the pointwise values. -/
theorem add_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (s + t) x = s x + t x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord s hi, apply_eq_symmL_coord t hi,
    apply_eq_symmL_coord (s + t) hi, ← map_add]
  congr 1
  have he : (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) (s + t)
      = equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s
        + equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := s),
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := t),
        map_add]
  rw [he]
  rfl

/-- The pointwise value of a difference of sections is the difference of the pointwise values. -/
theorem sub_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (s - t) x = s x - t x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord s hi, apply_eq_symmL_coord t hi,
    apply_eq_symmL_coord (s - t) hi, ← map_sub]
  congr 1
  have he : (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) (s - t)
      = equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s
        - equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := s),
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := t),
        map_sub]
  rw [he]
  rfl

/-- The pointwise value of a negated section is the negation of the pointwise value. -/
theorem neg_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (-s) x = -(s x) := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord s hi, apply_eq_symmL_coord (-s) hi, ← map_neg]
  congr 1
  have he : (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) (-s)
      = -(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s) := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := s),
        map_neg]
  rw [he]
  rfl

/-- The pointwise value of a scalar multiple of a section is the scalar multiple of the pointwise
value. -/
theorem smul_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    (c : 𝕜)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (c • s) x = c • s x := by
  obtain ⟨i, hi⟩ : ∃ i, x ∈ (Kc i : Set M) :=
    Set.mem_iUnion.mp (by rw [hcover]; exact Set.mem_univ x)
  rw [apply_eq_symmL_coord s hi, apply_eq_symmL_coord (c • s) hi, ← map_smul]
  congr 1
  have he : (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) (c • s)
      = c • equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
        ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s := s),
        map_smul]
  rw [he]
  rfl

/-- Uniform control of every compact coordinate readout by a constant `C` controls the
transported finite-cover section norm.  This is the boundedness companion of
`dist_le_of_forall_coord_dist_le` (the case `t = 0`): the norm-level handoff turning local
trivialization/coordinate sup-bounds into the global boundedness hypothesis
`∀ s, ‖A s‖ ≤ C` demanded by the Banach-space Picard–Lindelöf foundation for a section-space
vector field. -/
theorem norm_le_of_forall_coord_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ i (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ ≤ C) :
    ‖s‖ ≤ C := by
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  have hdist : dist s
      (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover) ≤ C := by
    refine dist_le_of_forall_coord_dist_le (𝕜 := 𝕜) (F := F) (V := V)
      (et := et) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq)
      (hcover := hcover) (s := s)
      (t := (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover)) hC ?_
    intro i x
    rw [he0]
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply, dist_zero_right]
    exact hcoord i x
  rwa [dist_zero_right] at hdist

/-- Global (`LipschitzWith`) version of `lipschitzOnWith_of_forall_coord_dist_le`: coordinatewise
finite-cover Lipschitz estimates on *all* sections imply a global Lipschitz estimate for a
section-space map.  This is the form consumed as the `hlip` hypothesis of the Banach-space
Picard–Lindelöf foundation `isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`. -/
theorem lipschitzWith_of_forall_coord_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L : NNReal}
    (hcoord : ∀ s t, ∀ i (x : Kc i),
      dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
        ≤ (L : ℝ) * dist s t) :
    LipschitzWith L A := by
  rw [← lipschitzOnWith_univ]
  exact lipschitzOnWith_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) (A := A) (L := L)
    (stateSet := Set.univ)
    (fun s _ t _ i x => hcoord s t i x)

/-- Coordinatewise time-continuity of every compact readout transports to continuity of a
section-valued map in the finite-cover Banach norm.  With finitely many trivializing pieces the
transported section norm is the sup of the compact coordinate `C(Kc i, F)` norms (the transport
`equivCompatibleCoordFamilySubmodule` is a definitional isometry into `∀ i, C(Kc i, F)`), so
continuity of each readout `x ↦ (f x)ᵢ` into `C(Kc i, F)` yields continuity of `x ↦ f x` into
`ContinuousSectionSpace`.  This is the time-continuity handoff
`∀ s, ContinuousOn (fun t => A t s) (Icc t₀ T)` demanded by the Banach-space Picard–Lindelöf
foundation `isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc`. -/
theorem continuousOn_of_forall_coord_continuousOn
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {s : Set X}
    (hcoord : ∀ i, ContinuousOn
      (fun x => (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f x)).1 i) s) :
    ContinuousOn f s := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := fun _ _ => rfl
  have hval : Isometry
      (fun a : compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo =>
        (a : CoordFamily (F := F) Kc)) :=
    Isometry.of_nndist_eq fun _ _ => rfl
  have hInd : Topology.IsInducing
      (fun z : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover =>
        ((e z).1 : CoordFamily (F := F) Kc)) :=
    (hval.comp he).isUniformEmbedding.toIsUniformInducing.isInducing
  rw [hInd.continuousOn_iff, continuousOn_pi]
  exact hcoord

/-- **A continuous section has a uniformly bounded compact coordinate readout.**  For a section `s`
along a finite trivializing cover, the finite family of compact coordinate maps
`(equivCompatibleCoordFamilySubmodule … s).1 i : C(Kc i, F)` — each a continuous function on the
compact base piece `Kc i` — is uniformly bounded: there is a single constant `C ≥ 0` with
`‖(coord s).1 i x‖ ≤ C` for every trivialization index `i` and base point `x ∈ Kc i`.  Each
coordinate map is bounded by its sup-norm `‖(coord s).1 i‖` (finite because `Kc i` is compact) and
the finite index family of these sup-norms is bounded above.  This is the existence form supplying
the constant that `norm_le_of_forall_coord_norm_le` consumes as input, and is exactly the
centre-readout size datum feeding the section-space Picard–Lindelöf `hcenter` hypothesis for a
genuine (continuous) section such as the initial metric. -/
theorem exists_forall_coord_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ ≤ C := by
  classical
  obtain ⟨C, hC⟩ :=
    (Set.finite_range (fun i => ‖(equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i‖)).bddAbove
  refine ⟨max C 0, le_max_right _ _, fun i x => ?_⟩
  calc
    ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖
        ≤ ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i‖ :=
      ContinuousMap.norm_coe_le_norm _ x
    _ ≤ C := hC (Set.mem_range_self i)
    _ ≤ max C 0 := le_max_left _ _

/-- **Uniform centre-readout bound from time-continuity of the coordinate readout.**  If a
time-parametrised section `f : ℝ → ContinuousSectionSpace` has, on each trivializing piece `i`, a
compact coordinate readout `t ↦ (equivCompatibleCoordFamilySubmodule … (f t)).1 i` that is
`ContinuousOn (Icc t₀ T)` (the `hcont` datum of the section-space Picard–Lindelöf constructor,
specialised at the centre section `f t = A t x0`), then the pointwise coordinate values are
uniformly bounded over the whole compact time window and finite trivializing cover: there is a
constant `C ≥ 0` with `‖(coord (f t)).1 i x‖ ≤ C` for all `t ∈ Icc t₀ T`, indices `i`, and base
points `x ∈ Kc i`.  Each `t ↦ ‖(coord (f t)).1 i‖` (sup-norm of the coordinate map) is continuous on
the compact `Icc t₀ T`, hence bounded, and the finite family of these interval bounds is bounded
above.  This produces precisely the `hcenter` hypothesis
`∀ t ∈ Icc t₀ T, ∀ i x, ‖(coord (A t x0)).1 i x‖ ≤ Mc` (take `Mc := C.toNNReal`) of
`isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` from the (provable)
time-continuity of the operator's coordinate readout at the initial metric. -/
theorem exists_forall_mem_Icc_coord_norm_le_of_continuousOn
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {f : ℝ → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ}
    (hcont : ∀ i, ContinuousOn
      (fun t => (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i)
      (Set.Icc t₀ T)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc t₀ T, ∀ i (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i x‖ ≤ C := by
  classical
  choose C hC using fun i => isCompact_Icc.exists_bound_of_continuousOn (hcont i)
  obtain ⟨D, hD⟩ := (Set.finite_range C).bddAbove
  refine ⟨max D 0, le_max_right _ _, fun t ht i x => ?_⟩
  calc
    ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i x‖
        ≤ ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i‖ :=
      ContinuousMap.norm_coe_le_norm _ x
    _ ≤ C i := hC i t ht
    _ ≤ D := hD (Set.mem_range_self i)
    _ ≤ max D 0 := le_max_left _ _

/-- **The compact coordinate readout is `1`-Lipschitz in the section distance (`C(Kc i, F)`
level).**  The transport `equivCompatibleCoordFamilySubmodule` is a definitional isometry from
`ContinuousSectionSpace` onto the compatible-coordinate-family submodule of `∀ i, C(Kc i, F)`,
carrying the finite-cover Banach norm to the `sup`-over-`i` (Pi) norm of the compact coordinate
maps.  Hence each single coordinate map `s ↦ (coord s).1 i : C(Kc i, F)` contracts distances:
`dist ((coord s).1 i) ((coord t).1 i) ≤ dist s t`.  This is the elementary contraction that turns
section-space (Banach-norm) control of an operator into control of each of its compact coordinate
readouts — the converse direction to `continuousOn_of_forall_coord_continuousOn`. -/
theorem coordContinuousMap_dist_le_dist
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) :
    dist
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i)
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i)
      ≤ dist s t := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := fun _ _ => rfl
  have hval : Isometry
      (fun a : compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo =>
        (a : CoordFamily (F := F) Kc)) :=
    Isometry.of_nndist_eq fun _ _ => rfl
  have hcomp : Isometry
      (fun z : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover =>
        ((e z).1 : CoordFamily (F := F) Kc)) :=
    hval.comp he
  calc
    dist ((e s).1 i) ((e t).1 i)
        ≤ dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1 : CoordFamily (F := F) Kc) :=
          dist_le_pi_dist _ _ i
    _ = dist s t := hcomp.dist_eq s t

/-- **The pointwise coordinate readout is `1`-Lipschitz in the section distance (fibre `F` level).**
Evaluating the `1`-Lipschitz `C(Kc i, F)`-level readout at a base point `x ∈ Kc i` (evaluation of a
continuous map on a compact space is itself `1`-Lipschitz for the sup metric) gives
`dist ((coord s).1 i x) ((coord t).1 i x) ≤ dist s t`.  This is the pointwise contraction consumed
by the coordinatewise `hlip` hypothesis of the section-space Picard–Lindelöf constructor. -/
theorem coord_dist_le_dist
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    dist
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
      ≤ dist s t :=
  le_trans (ContinuousMap.dist_apply_le_dist x)
    (coordContinuousMap_dist_le_dist s t i)

/-- The compact coordinate readout of the zero section vanishes pointwise:
`(coord 0).1 i x = 0`.  The transport `equivCompatibleCoordFamilySubmodule` is additive (it is the
underlying equivalence of the section-space module structure), so it sends `0` to `0`, and the
coordinate/point projections of the zero coordinate family vanish.  This is the coordinate-readout
companion of `zero_apply`, used to turn section-distance contractions into section-norm bounds. -/
theorem coord_zero_apply
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover)).1 i x = 0 := by
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  rw [he0]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply]

/-- **The compact coordinate readout is additive:**
`(coord (s + t)).1 i x = (coord s).1 i x + (coord t).1 i x`.  The transport
`equivCompatibleCoordFamilySubmodule` is the underlying (continuous) linear equivalence of the
section-space module structure, so it sends `s + t` to `equiv s + equiv t`, and the
coordinate/point projections of a sum coordinate family are pointwise sums.  This is the
coordinate-readout companion of `coord_zero_apply`, used to reduce the coordinate estimates of an
*affine* section-space operator `A t s = L s + b` (a linear generator plus a fixed source) to those
of its linear part: the source `b` contributes the same coordinate summand to `A t s` and `A t s'`,
which cancels in the coordinate distance. -/
theorem coord_add_apply
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s + t)).1 i x
      = (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x
        + (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x := by
  have he :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s + t))
      = (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s)
        + (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t) := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_add _ s t
  rw [he]
  simp only [AddMemClass.coe_add, Pi.add_apply, ContinuousMap.add_apply]

/-- **The pointwise coordinate readout is norm-nonexpansive:** `‖(coord s).1 i x‖ ≤ ‖s‖`.  The
norm-level companion of `coord_dist_le_dist` (take `t = 0` and use `coord_zero_apply`).  Composed
with a section-space *boundedness* estimate `‖A t x0‖ ≤ Mc` this yields the coordinate centre-bound
`‖(coord (A t x0)).1 i x‖ ≤ Mc` — the `hcenter` datum of
`isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` — turning the "bounded"
half of a bounded + Lipschitz section-space operator into the constructor's centre-size input. -/
theorem coord_norm_le_norm
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    ‖(equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ ≤ ‖s‖ := by
  have h := coord_dist_le_dist s
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) i x
  rw [coord_zero_apply, dist_zero_right, dist_zero_right] at h
  exact h

/-- **Section-space continuity transfers to each compact coordinate readout.**  From continuity of a
section-valued map `f : X → ContinuousSectionSpace` (in the finite-cover Banach norm) on a set `s`,
each compact coordinate readout `x ↦ (coord (f x)).1 i` is continuous on `s`.  Immediate from the
`1`-Lipschitz (hence continuous) single readout `z ↦ (coord z).1 i` composed with `f`.  This is the
converse of `continuousOn_of_forall_coord_continuousOn`, reducing the coordinatewise time-continuity
hypothesis `hcont` of the section-space Picard–Lindelöf constructor to *section-space* continuity of
the operator. -/
theorem continuousOn_coord_of_continuousOn
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {s : Set X}
    (hf : ContinuousOn f s) (i : κ) :
    ContinuousOn
      (fun x => (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f x)).1 i) s := by
  have hLip : LipschitzWith 1
      (fun z : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover =>
        (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover z).1 i) :=
    LipschitzWith.of_dist_le_mul fun z w => by
      simpa only [NNReal.coe_one, one_mul] using
        coordContinuousMap_dist_le_dist z w i
  exact hLip.continuous.comp_continuousOn hf

/-- **Fiberwise Lipschitz control of a section-space operator upgrades to a `LipschitzOnWith`
estimate in the transported finite-cover Banach norm.**  If every fiber trivialization map of the
finite cover is bounded in operator norm by `L`, and the operator `A` is fiber-pointwise
`C`-Lipschitz in the state — i.e. `dist ((A s) x) ((A t) x) ≤ C * dist s t` at every base point `x`,
uniformly over the state set — then `A` is `L * C`-Lipschitz on the state set.  This is the
interface a (regularised) geometric section-space operator naturally verifies: its value's fiber at
each base point is Lipschitz in the state, and the finite cover's trivialization maps are uniformly
bounded; the conclusion is precisely the `hlip` hypothesis of the section-space Picard–Lindelöf
capstone `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_lipschitzOnWith_continuousOn`. -/
theorem lipschitzOnWith_of_forall_fiber_dist_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover}
    {L C : NNReal}
    (hL : ∀ i (x : Kc i), ‖(et i).continuousLinearMapAt 𝕜 x.1‖ ≤ (L : ℝ))
    (hfiber : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A s) x) ((A t) x) ≤ (C : ℝ) * dist s t) :
    LipschitzOnWith (L * C) A stateSet := by
  refine lipschitzOnWith_of_forall_coord_dist_le
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover)
    (A := A) (L := L * C) (stateSet := stateSet) ?_
  intro s hs t ht i x
  calc
    dist
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
        ((equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
        ≤ (L : ℝ) * dist ((A s) x.1) ((A t) x.1) :=
      coord_dist_le_of_trivialization_opNorm_le (L := (L : ℝ)) hL (A s) (A t) i x
    _ ≤ (L : ℝ) * ((C : ℝ) * dist s t) :=
      mul_le_mul_of_nonneg_left (hfiber hs ht x.1) (NNReal.coe_nonneg L)
    _ = ((L * C : NNReal) : ℝ) * dist s t := by
      rw [NNReal.coe_mul]; ring

/-- **Coordinatewise joint (time–base) continuity of a section-valued family upgrades to continuity
in the transported finite-cover Banach norm.**  If, for every trivialization index `i`, the
coordinate readout `(t, x) ↦ (et i).continuousLinearMapAt 𝕜 x ((f t) x)` of the section `f t` in the
`i`-th trivialization is jointly continuous on `timeSet ×ˢ Kc i`, then `t ↦ f t` is continuous on
`timeSet` in the finite-cover Banach norm.  The compact base pieces `Kc i` supply the uniform-in-`x`
control (via `ContinuousMap.continuousOn_of_continuousOn_uncurry`) that passes from pointwise joint
continuity to `C(Kc i, F)`-valued continuity, which `continuousOn_of_forall_coord_continuousOn` then
assembles.  This is the fiber-level route to the `hcont` hypothesis
`∀ s, ContinuousOn (fun t => A t s) (Icc t₀ T)` of the section-space Picard–Lindelöf capstone. -/
theorem continuousOn_of_forall_coord_uncurry_continuousOn
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {timeSet : Set X}
    (hcoord : ∀ i, ContinuousOn
      (fun p : X × M => (et i).continuousLinearMapAt 𝕜 p.2 ((f p.1) p.2))
      (timeSet ×ˢ (Kc i : Set M))) :
    ContinuousOn f timeSet := by
  refine continuousOn_of_forall_coord_continuousOn
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) ?_
  intro i
  refine ContinuousMap.continuousOn_of_continuousOn_uncurry _ ?_
  have hnice : ContinuousOn
      (fun p : X × (Kc i) =>
        (et i).continuousLinearMapAt 𝕜 p.2.1 ((f p.1) p.2.1))
      (timeSet ×ˢ Set.univ) := by
    refine (hcoord i).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn ?_
    intro p hp
    exact ⟨hp.1, p.2.2⟩
  refine hnice.congr ?_
  intro p _
  exact coord_apply (f p.1) i p.2

/-- **Joint total-space continuity of a parametrised section family upgrades to continuity in the
transported finite-cover Banach norm.**  If the family `f : X → ContinuousSectionSpace`, read jointly
in the parameter and base point as a map into the total space
`(p, x) ↦ TotalSpace.mk' F x ((f p) x)`, is continuous, then `t ↦ f t` is continuous on any set
`timeSet` in the finite-cover Banach norm.  This is the clean, coordinate-free route to the
`hcont`/`hLc`/`hb` time-continuity hypotheses of the section-space Picard–Lindelöf capstones: rather
than joint continuity of each trivialization coordinate readout, it suffices that the family be
jointly continuous *into the total space*, the trivialization readout continuity then being supplied
internally from `Trivialization.continuousOn` and `coe_linearMapAt_of_mem`.  Reduces to
`continuousOn_of_forall_coord_uncurry_continuousOn`. -/
theorem continuousOn_of_continuous_totalSpace_uncurry
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {timeSet : Set X}
    (hjoint : Continuous (fun p : X × M => TotalSpace.mk' F p.2 ((f p.1) p.2))) :
    ContinuousOn f timeSet := by
  refine continuousOn_of_forall_coord_uncurry_continuousOn
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) ?_
  intro i
  have hmaps : Set.MapsTo (fun p : X × M => TotalSpace.mk' F p.2 ((f p.1) p.2))
      (timeSet ×ˢ (Kc i : Set M)) (et i).source := by
    intro p hp
    exact (et i).mem_source.mpr (hKc i hp.2)
  have hsnd : ContinuousOn
      (fun p : X × M => ((et i) (TotalSpace.mk' F p.2 ((f p.1) p.2))).2)
      (timeSet ×ˢ (Kc i : Set M)) :=
    continuous_snd.comp_continuousOn ((et i).continuousOn.comp hjoint.continuousOn hmaps)
  refine hsnd.congr ?_
  intro p hp
  exact congrFun ((et i).coe_linearMapAt_of_mem (hKc i hp.2)) ((f p.1) p.2)

/-- **Bounded linear section-space operator from a coordinatewise operator-norm bound.**  Given a
`𝕜`-linear map `T` on the transported finite-cover section space together with a uniform bound
`‖(coord (T s)).1 i x‖ ≤ C · ‖s‖` on every compact coordinate readout of the image, `T` is bounded and
packages into a `ContinuousSectionSpace →L[𝕜] ContinuousSectionSpace`.  The coordinate bound is pushed
to the section-norm bound `‖T s‖ ≤ C · ‖s‖` by `norm_le_of_forall_coord_norm_le`, then
`LinearMap.mkContinuous` supplies the packaged operator (whose operator-norm control is
`mkContinuousOfForallCoordNormLe_norm_le`).  This is the missing constructor that turns a generator's
fiber/coordinate operator estimate into the `CSS →L[𝕜] CSS` object consumed as the bounded linear
generator `L t` of the section-space Picard–Lindelöf `picard` field. -/
noncomputable def mkContinuousOfForallCoordNormLe
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →ₗ[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (T s)).1 i x‖ ≤ C * ‖s‖) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover :=
  T.mkContinuous C fun s =>
    norm_le_of_forall_coord_norm_le (mul_nonneg hC (norm_nonneg s)) (hbound s)

@[simp]
theorem mkContinuousOfForallCoordNormLe_apply
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →ₗ[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (T s)).1 i x‖ ≤ C * ‖s‖)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover) :
    mkContinuousOfForallCoordNormLe T C hC hbound s = T s :=
  rfl

/-- Operator-norm control for `mkContinuousOfForallCoordNormLe`: the packaged section-space operator
has operator norm at most the coordinatewise bound `C`. -/
theorem mkContinuousOfForallCoordNormLe_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (T : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →ₗ[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (T s)).1 i x‖ ≤ C * ‖s‖) :
    ‖mkContinuousOfForallCoordNormLe T C hC hbound‖ ≤ C := by
  refine LinearMap.mkContinuous_norm_le T hC fun s => ?_
  exact norm_le_of_forall_coord_norm_le (mul_nonneg hC (norm_nonneg s)) (hbound s)

/-- **Scalar-function multiplication preserves continuity of a bundle section.**  If `φ : M → 𝕜` is
continuous and the section `s` is continuous (as a map into the total space), then so is the pointwise
scalar multiple `x ↦ φ x • s x`.  Checked fibrewise via `FiberBundle.continuousAt_totalSpace`: in the
canonical trivialization at each base point the readout is `φ x • (e (T% s x)).2`, continuous by
continuity of `φ` and of the section's trivialization readout.  This is the continuity input for
building zeroth-order (multiplication) section-space generators. -/
lemma continuous_smul_section
    {φ : M → 𝕜} (hφ : Continuous φ)
    {s : Π x : M, V x} (hs : Continuous (T% s)) :
    Continuous (T% (fun x => φ x • s x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hs_at : ContinuousAt (T% s) x₀ := hs.continuousAt
  rw [FiberBundle.continuousAt_totalSpace F] at hs_at
  rw [FiberBundle.continuousAt_totalSpace F]
  refine ⟨continuousAt_id, ?_⟩
  have hfib_s : ContinuousAt
      (fun x => (trivializationAt F V x₀ ((T% s) x)).2) x₀ := hs_at.2
  show ContinuousAt
    (fun x => (trivializationAt F V x₀ ((T% fun y => φ y • s y) x)).2) x₀
  have hx₀base : x₀ ∈ (trivializationAt F V x₀).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt F V x₀
  have hev :
      (fun x => (trivializationAt F V x₀ ((T% fun y => φ y • s y) x)).2)
        =ᶠ[nhds x₀] (fun x => φ x • (trivializationAt F V x₀ ((T% s) x)).2) := by
    filter_upwards [(trivializationAt F V x₀).open_baseSet.mem_nhds hx₀base] with x hx
    have key : ∀ v : V x,
        (trivializationAt F V x₀ (TotalSpace.mk' F x v)).2
          = (trivializationAt F V x₀).linearMapAt 𝕜 x v := by
      intro v
      rw [Bundle.Trivialization.coe_linearMapAt_of_mem (R := 𝕜)
        (trivializationAt F V x₀) hx]
    show (trivializationAt F V x₀ (TotalSpace.mk' F x (φ x • s x))).2
      = φ x • (trivializationAt F V x₀ (TotalSpace.mk' F x (s x))).2
    rw [key (φ x • s x), key (s x), map_smul]
  exact (hφ.continuousAt.smul hfib_s).congr hev.symm

/-- The scalar-field multiplication operator on the section space, as a `𝕜`-linear map: for a
continuous scalar field `φ : M → 𝕜` it sends a section `s` to `x ↦ φ x • s x` (continuous by
`continuous_smul_section`). -/
def smulFieldLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {φ : M → 𝕜} (hφ : Continuous φ) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →ₗ[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover where
  toFun s := ⟨fun x => φ x • s x, continuous_smul_section hφ s.continuous_toFun⟩
  map_add' s t := by
    refine ContinuousSectionSpace.ext (fun x => ?_)
    rw [add_apply]
    show φ x • (s + t) x = φ x • s x + φ x • t x
    rw [add_apply, smul_add]
  map_smul' c s := by
    refine ContinuousSectionSpace.ext (fun x => ?_)
    rw [smul_apply]
    show φ x • (c • s) x = c • (φ x • s x)
    rw [smul_apply, smul_comm]

@[simp]
theorem smulFieldLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {φ : M → 𝕜} (hφ : Continuous φ)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (smulFieldLinearMap (V := V) et Kc hKc Ko hKo hKoEq hcover hφ s) x = φ x • s x :=
  rfl

/-- **The scalar-field multiplication operator packaged as a bounded section-space operator.**  For a
continuous scalar field `φ : M → 𝕜` bounded by `C` on the finite cover, `s ↦ (x ↦ φ x • s x)` is a
`ContinuousSectionSpace →L[𝕜] ContinuousSectionSpace` of operator norm at most `C`.  This is a genuine
zeroth-order (multiplication) generator on the transported section space, built through
`mkContinuousOfForallCoordNormLe`: the coordinate readout of the image is `φ x • (coord s) i x`, so the
coordinate operator bound `‖(coord (φ • s)) i x‖ ≤ C · ‖s‖` follows from `‖φ x‖ ≤ C` and the
norm-nonexpansiveness `coord_norm_le_norm`. -/
noncomputable def smulField
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {φ : M → 𝕜} (hφ : Continuous φ) (C : ℝ) (hC : 0 ≤ C)
    (hφbound : ∀ (i : κ) (x : Kc i), ‖φ x.1‖ ≤ C) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover :=
  mkContinuousOfForallCoordNormLe
    (smulFieldLinearMap (V := V) et Kc hKc Ko hKo hKoEq hcover hφ) C hC
    (fun s i x => by
      rw [coord_apply]
      show ‖(et i).continuousLinearMapAt 𝕜 x.1 (φ x.1 • s x.1)‖ ≤ C * ‖s‖
      rw [map_smul, norm_smul, ← coord_apply s i x]
      calc ‖φ x.1‖ * ‖(equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖
          ≤ C * ‖(equivCompatibleCoordFamilySubmodule
              (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ :=
            mul_le_mul_of_nonneg_right (hφbound i x) (norm_nonneg _)
        _ ≤ C * ‖s‖ := mul_le_mul_of_nonneg_left (coord_norm_le_norm s i x) hC)

@[simp]
theorem smulField_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {φ : M → 𝕜} (hφ : Continuous φ) (C : ℝ) (hC : 0 ≤ C)
    (hφbound : ∀ (i : κ) (x : Kc i), ‖φ x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (smulField (V := V) et Kc hKc Ko hKo hKoEq hcover hφ C hC hφbound s) x = φ x • s x :=
  rfl

/-- The scalar-field multiplication operator has operator norm at most the field bound `C`. -/
theorem smulField_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {φ : M → 𝕜} (hφ : Continuous φ) (C : ℝ) (hC : 0 ≤ C)
    (hφbound : ∀ (i : κ) (x : Kc i), ‖φ x.1‖ ≤ C) :
    ‖smulField (V := V) et Kc hKc Ko hKo hKoEq hcover hφ C hC hφbound‖ ≤ C :=
  mkContinuousOfForallCoordNormLe_norm_le _ C hC _

/-- **Coordinate readout of a continuous endomorphism-bundle section.**  Continuity of a section `Φ`
of the endomorphism (hom) bundle `V →L[𝕜] V`, phrased as continuity of
`x ↦ TotalSpace.mk' (F →L[𝕜] F) x (Φ x)` into the hom-bundle total space, is equivalent (via
`continuousAt_hom_bundle`) to base-continuity together with continuity of the fiber readout
`x ↦ inCoordinates F V F V x₀ x x₀ x (Φ x) = (trivₓ₀).clmAt x ∘ Φ x ∘ (trivₓ₀).symmL x`.  This is the
extractor half: from hom-section continuity it produces `ContinuousAt` of the coordinate readout at
each base point.  It is the shared engine behind the closure lemmas
`continuous_add_endo_section`, `continuous_smul_endo_section`, `continuous_comp_endo_section` below,
which combine coordinate readouts and transport the result back through `continuousAt_hom_bundle`. -/
theorem continuousAt_inCoordinates_of_continuous_homSection
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (x₀ : M) :
    ContinuousAt (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x)) x₀ := by
  have h := hΦ.continuousAt (x := x₀)
  rw [continuousAt_hom_bundle] at h
  exact h.2

/-- **The coordinate readout of a continuous endomorphism-bundle section is continuous on the whole
trivializing set.**  Unlike `continuousAt_inCoordinates_of_continuous_homSection` (which yields
continuity only *at* the trivialization centre `x₀`), this gives `ContinuousOn` on the entire hom-bundle
base set: for a continuous hom-section `Φ`, the fixed-centre readout
`x ↦ inCoordinates F V F V x₀ x x₀ x (Φ x)` equals `(trivₓ₀ ⟨x, Φ x⟩).2` (`hom_trivializationAt_apply`),
and the hom trivialization is continuous on its source (which the section maps the base set into).
This is the ingredient that turns a *per-point* section-space Picard coordinate bound
`‖inCoord (P x)‖ ≤ Kp` into a *uniform* bound over a compact cover (via
`IsCompact.exists_bound_of_continuousOn` on each compact piece and a finite index sup), supplying the
uniform Lipschitz constant `K = 2·Kp` the section-space Picard bridge consumes. -/
theorem continuousOn_inCoordinates_of_continuous_homSection
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (x₀ : M) :
    ContinuousOn (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x))
      (trivializationAt (F →L[𝕜] F) (fun x => V x →L[𝕜] V x) x₀).baseSet := by
  set et := trivializationAt (F →L[𝕜] F) (fun x => V x →L[𝕜] V x) x₀ with het
  have hEq : (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x))
      = fun x => (et (TotalSpace.mk' (F →L[𝕜] F) x (Φ x))).2 := by
    funext x
    rw [het, hom_trivializationAt_apply]
  rw [hEq]
  have hsrc : Set.MapsTo (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x))
      et.baseSet et.source := by
    intro x hx
    rw [Trivialization.mem_source]
    exact hx
  exact continuous_snd.comp_continuousOn (et.continuousOn.comp hΦ.continuousOn hsrc)

/-- **Continuity of an endomorphism-bundle section from continuity of its coordinate readout.**  The
constructor dual of `continuousAt_inCoordinates_of_continuous_homSection`: if, at every base point
`x₀`, the fiber readout `x ↦ inCoordinates F V F V x₀ x x₀ x (Φ x) = (trivₓ₀).clmAt x ∘ Φ x ∘
(trivₓ₀).symmL x` is continuous at `x₀`, then the section `x ↦ TotalSpace.mk' (F →L[𝕜] F) x (Φ x)` is
continuous into the hom-bundle total space.  This is the entry point for proving continuity of any
concretely-defined endomorphism section (e.g. a fiber-linear geometric reaction endomorphism): reduce
to computing its trivialization readout and checking that readout is continuous, then discharge with
this lemma.  It is `continuousAt_hom_bundle.mpr` paired with continuity of the (identity) base map. -/
theorem continuous_homSection_of_continuousAt_inCoordinates
    {Φ : Π x : M, V x →L[𝕜] V x}
    (h : ∀ x₀ : M,
      ContinuousAt (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x)) x₀) :
    Continuous (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  exact ⟨continuousAt_id, h x₀⟩

/-- **The identity endomorphism-bundle section is continuous.**  The natural section
`x ↦ TotalSpace.mk' (F →L[𝕜] F) x (ContinuousLinearMap.id 𝕜 (V x))` of the hom bundle `V →L[𝕜] V` is
continuous into the total space.  This is the first supplier of the `hΦ` hypothesis that
`continuous_endo_section`/`endoField` consume (nothing previously *constructed* such a witness — the
existing zeroth-order generators either assumed it or specialised to the scalar `smulField`).  Proof:
via `continuousAt_hom_bundle`, the fiber readout `inCoordinates F V F V x₀ x x₀ x id` equals
`(trivₓ₀).clmAt x ∘ (trivₓ₀).symmL x`, which is `id_F` for `x` in the trivializing base set
(`continuousLinearMapAt_symmL`); so the readout is eventually constant and hence continuous. -/
theorem continuous_id_endo_section :
    Continuous (fun x : M => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x
      (ContinuousLinearMap.id 𝕜 (V x))) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hev : (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x
        (ContinuousLinearMap.id 𝕜 (V x)))
      =ᶠ[nhds x₀] (fun _ => ContinuousLinearMap.id 𝕜 F) := by
    filter_upwards [(trivializationAt F V x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x₀)] with x hx
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
      Function.comp_apply, ContinuousLinearMap.id_apply]
    exact (trivializationAt F V x₀).continuousLinearMapAt_symmL (R := 𝕜) hx y
  exact continuousAt_const.congr hev.symm

/-- **Pointwise sum of continuous endomorphism-bundle sections is continuous.**  If `Φ` and `Ψ` are
continuous sections of the hom bundle `V →L[𝕜] V`, so is `x ↦ Φ x + Ψ x`.  Proof: the fiber readout
`inCoordinates` is linear in the endomorphism argument (it is a two-sided composition with the
trivialization maps), so the readout of `Φ + Ψ` is the sum of the readouts, continuous by
`continuousAt_inCoordinates_of_continuous_homSection`; transport back via `continuousAt_hom_bundle`. -/
theorem continuous_add_endo_section {Φ Ψ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (hΨ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Ψ x))) :
    Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x + Ψ x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hΦr := continuousAt_inCoordinates_of_continuous_homSection hΦ x₀
  have hΨr := continuousAt_inCoordinates_of_continuous_homSection hΨ x₀
  have heq : (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x + Ψ x))
      = (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x)
          + ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Ψ x)) := by
    funext x
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.add_comp]
  rw [heq]
  exact hΦr.add hΨr

/-- **Continuous scalar-field multiple of a continuous endomorphism-bundle section is continuous.**
If `c : M → 𝕜` is continuous and `Φ` is a continuous section of the hom bundle `V →L[𝕜] V`, then
`x ↦ c x • Φ x` is a continuous section.  Proof: the fiber readout `inCoordinates` is homogeneous in
the endomorphism argument, so the readout of `c • Φ` is `c` times the readout of `Φ`; combine
continuity of `c` with `continuousAt_inCoordinates_of_continuous_homSection` and transport back. -/
theorem continuous_smul_endo_section {c : M → 𝕜} (hc : Continuous c)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x))) :
    Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (c x • Φ x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hΦr := continuousAt_inCoordinates_of_continuous_homSection hΦ x₀
  have heq : (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (c x • Φ x))
      = (fun x => c x • ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x)) := by
    funext x
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.smul_comp]
  rw [heq]
  exact hc.continuousAt.smul hΦr

/-- **Pointwise composition of continuous endomorphism-bundle sections is continuous.**  If `Φ` and
`Ψ` are continuous sections of the hom bundle `V →L[𝕜] V`, so is `x ↦ Φ x ∘L Ψ x`.  Proof: on the
trivializing base set the readout of `Φ ∘ Ψ` equals the composition of the readouts — the identity
`symmL x ∘ clmAt x = id` (`symmL_continuousLinearMapAt`) inserted between the two factors collapses
the middle transport — so the readout is eventually the composition of two continuous
`ContinuousLinearMap`-valued functions (`ContinuousAt.clm_comp`); transport back via
`continuousAt_hom_bundle`.  Together with `continuous_id_endo_section`, `continuous_add_endo_section`
and `continuous_smul_endo_section` this closes the class of continuous endomorphism-bundle sections
under the pointwise algebra operations, the structural closure a fiber-linear reaction endomorphism is
assembled from. -/
theorem continuous_comp_endo_section {Φ Ψ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (hΨ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Ψ x))) :
    Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x ∘L Ψ x)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  rw [continuousAt_hom_bundle]
  refine ⟨continuousAt_id, ?_⟩
  have hΦr := continuousAt_inCoordinates_of_continuous_homSection hΦ x₀
  have hΨr := continuousAt_inCoordinates_of_continuous_homSection hΨ x₀
  have hev : (fun x => ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x ∘L Ψ x))
      =ᶠ[nhds x₀] (fun x => (ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Φ x)).comp
          (ContinuousLinearMap.inCoordinates F V F V x₀ x x₀ x (Ψ x))) := by
    filter_upwards [(trivializationAt F V x₀).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt F V x₀)] with x hx
    apply ContinuousLinearMap.ext
    intro y
    simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [(trivializationAt F V x₀).symmL_continuousLinearMapAt (R := 𝕜) hx]
  rw [continuousAt_congr hev]
  exact hΦr.clm_comp hΨr

/-- **Fiberwise continuous-linear-endomorphism application preserves continuity of a bundle
section.**  If `Φ` is a continuous section of the endomorphism bundle `V →L[𝕜] V` (continuity phrased
as continuity of `x ↦ TotalSpace.mk' (F →L[𝕜] F) x (Φ x)` into the hom-bundle total space) and the
section `s` is continuous, then so is the pointwise application `x ↦ Φ x (s x)`.  This is the
continuity input for building zeroth-order fiber-linear (bundle-endomorphism) section-space
generators, generalising `continuous_smul_section` (whose special case is `Φ x = φ x • id`).  Proof:
Mathlib's `Continuous.clm_bundle_apply` for the endomorphism (hom) bundle over the identity base
map. -/
lemma continuous_endo_section
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    {s : Π x : M, V x} (hs : Continuous (T% s)) :
    Continuous (T% (fun x => Φ x (s x))) :=
  hΦ.clm_bundle_apply (b := fun x => x) hs

/-- The fiberwise continuous-linear-endomorphism operator on the section space, as a `𝕜`-linear map:
for a continuous section `Φ` of the endomorphism bundle `V →L[𝕜] V` it sends a section `s` to
`x ↦ Φ x (s x)` (continuous by `continuous_endo_section`).  This generalises `smulFieldLinearMap`
(the special case `Φ x = φ x • id`) to a genuine fiber-linear coupling — the structural shape of the
zeroth-order (curvature) term of a linearised geometric operator. -/
def endoFieldLinearMap
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x))) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →ₗ[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover where
  toFun s := ⟨fun x => Φ x (s x), continuous_endo_section hΦ s.continuous_toFun⟩
  map_add' s t := by
    refine ContinuousSectionSpace.ext (fun x => ?_)
    rw [add_apply]
    show Φ x ((s + t) x) = Φ x (s x) + Φ x (t x)
    rw [add_apply, map_add]
  map_smul' c s := by
    refine ContinuousSectionSpace.ext (fun x => ?_)
    rw [smul_apply]
    show Φ x ((c • s) x) = c • Φ x (s x)
    rw [smul_apply, map_smul]

@[simp]
theorem endoFieldLinearMap_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (endoFieldLinearMap (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ s) x = Φ x (s x) :=
  rfl

/-- **The fiberwise endomorphism operator packaged as a bounded section-space operator.**  For a
continuous section `Φ` of the endomorphism bundle `V →L[𝕜] V` whose section-space operator size is
controlled on the finite cover by the trivialization-distorted fiber bound
`‖(et i).continuousLinearMapAt 𝕜 x‖ · ‖Φ x‖ · ‖(et i).symmL 𝕜 x‖ ≤ C`, the operator
`s ↦ (x ↦ Φ x (s x))` is a `ContinuousSectionSpace →L[𝕜] ContinuousSectionSpace` of operator norm at
most `C`.  This is a genuine zeroth-order fiber-linear (bundle-endomorphism) generator on the
transported section space — the `L t : CSS →L[𝕜] CSS` shape the section-space Picard `picard` field
consumes — built through `mkContinuousOfForallCoordNormLe`: the coordinate readout of the image is
`(et i).continuousLinearMapAt 𝕜 x (Φ x (s x))`, and writing `s x` back through
`(et i).symmL 𝕜 x` gives the coordinate operator bound via the composed operator norms.  Generalises
`smulField`, whose scalar coupling pulls through the trivialization with no distortion factor. -/
noncomputable def endoField
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * ‖Φ x.1‖ * ‖(et i).symmL 𝕜 x.1‖ ≤ C) :
    ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover →L[𝕜]
      ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover :=
  mkContinuousOfForallCoordNormLe
    (endoFieldLinearMap (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ) C hC
    (fun s i x => by
      rw [coord_apply]
      show ‖(et i).continuousLinearMapAt 𝕜 x.1 (Φ x.1 (s x.1))‖ ≤ C * ‖s‖
      have hsx : ‖s x.1‖ ≤ ‖(et i).symmL 𝕜 x.1‖ * ‖s‖ := by
        rw [apply_eq_symmL_coord s x.2]
        refine le_trans (((et i).symmL 𝕜 x.1).le_opNorm _) ?_
        exact mul_le_mul_of_nonneg_left (coord_norm_le_norm s i _) (norm_nonneg _)
      calc ‖(et i).continuousLinearMapAt 𝕜 x.1 (Φ x.1 (s x.1))‖
          ≤ ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * ‖Φ x.1 (s x.1)‖ :=
            ((et i).continuousLinearMapAt 𝕜 x.1).le_opNorm _
        _ ≤ ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * (‖Φ x.1‖ * ‖s x.1‖) :=
            mul_le_mul_of_nonneg_left ((Φ x.1).le_opNorm _) (norm_nonneg _)
        _ ≤ ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * (‖Φ x.1‖ * (‖(et i).symmL 𝕜 x.1‖ * ‖s‖)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hsx (norm_nonneg _)) (norm_nonneg _)
        _ = ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * ‖Φ x.1‖ * ‖(et i).symmL 𝕜 x.1‖ * ‖s‖ := by
            ring
        _ ≤ C * ‖s‖ := mul_le_mul_of_nonneg_right (hbound i x) (norm_nonneg s))

@[simp]
theorem endoField_apply
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * ‖Φ x.1‖ * ‖(et i).symmL 𝕜 x.1‖ ≤ C)
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (x : M) :
    (endoField (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ C hC hbound s) x = Φ x (s x) :=
  rfl

/-- The fiberwise endomorphism operator has operator norm at most the trivialization-distorted fiber
bound `C`. -/
theorem endoField_norm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {Φ : Π x : M, V x →L[𝕜] V x}
    (hΦ : Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ x)))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ (i : κ) (x : Kc i),
      ‖(et i).continuousLinearMapAt 𝕜 x.1‖ * ‖Φ x.1‖ * ‖(et i).symmL 𝕜 x.1‖ ≤ C) :
    ‖endoField (V := V) et Kc hKc Ko hKo hKoEq hcover hΦ C hC hbound‖ ≤ C :=
  mkContinuousOfForallCoordNormLe_norm_le _ C hC _

/-- **Strong time-continuity of the fiberwise endomorphism generator.**  For a parametrised
endomorphism family `Φ : X → Π x, V x →L[𝕜] V x` that is jointly continuous into the endomorphism
(hom) bundle `(p, x) ↦ TotalSpace.mk' (F →L[𝕜] F) x (Φ p x)`, and any fixed section `s`, the section
`p ↦ (x ↦ Φ p x (s x))` is continuous on any set `timeSet` in the finite-cover Banach norm.  This is
exactly the strong time-continuity `hLc : ∀ s, ContinuousOn (fun t => (L t) s) [t₀, T]` that the
affine section-space Picard–Lindelöf capstone consumes for a time-dependent endomorphism generator
`L t = endoField (Φ t)` (whose value `(endoField (Φ t) …) s = (endoFieldLinearMap (Φ t) …) s`
coincides with the map below).  Proof: `Continuous.clm_bundle_apply` (over the base projection
`Prod.snd`) makes `(p, x) ↦ Φ p x (s x)` jointly continuous into the total space, which
`continuousOn_of_continuous_totalSpace_uncurry` lifts to Banach-norm time-continuity. -/
theorem endoFieldLinearMap_continuousOn
    {κ : Type*} [Finite κ] [T2Space M]
    (et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M))
    [∀ i, MemTrivializationAtlas (et i)]
    (Kc : κ → TopologicalSpace.Compacts M)
    (hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet)
    (Ko : κ → κ → TopologicalSpace.Compacts M)
    (hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M))
    (hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M))
    (hcover : (⋃ i, (Kc i : Set M)) = Set.univ)
    {X : Type*} [TopologicalSpace X]
    {Φ : X → Π x : M, V x →L[𝕜] V x}
    (hΦ : ∀ p, Continuous
      (fun x => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) x (Φ p x)))
    (hΦjoint : Continuous
      (fun p : X × M => TotalSpace.mk' (F →L[𝕜] F) (E := fun x => V x →L[𝕜] V x) p.2 (Φ p.1 p.2)))
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover)
    (timeSet : Set X) :
    ContinuousOn
      (fun p => endoFieldLinearMap (V := V) et Kc hKc Ko hKo hKoEq hcover (hΦ p) s)
      timeSet := by
  refine continuousOn_of_continuous_totalSpace_uncurry
    (𝕜 := 𝕜) (F := F) (V := V) (et := et) (Kc := Kc) (hKc := hKc)
    (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq) (hcover := hcover) ?_
  have hv : Continuous (fun p : X × M => TotalSpace.mk' F p.2 (s p.2)) :=
    (ContinuousSectionSpace.continuous s).comp continuous_snd
  exact hΦjoint.clm_bundle_apply (b := Prod.snd) hv

end TrivializationOpNorm

/-!
### Topological-fibre coordinate control (Path-B compatible)

The `TrivializationOpNorm` section above states `norm_le_of_forall_coord_norm_le` and
`continuousOn_of_forall_coord_continuousOn` with a fibre `[∀ x, SeminormedAddCommGroup (V x)]`,
whose induced fibre topology (Path A) is then baked into the `ContinuousSectionSpace` type of those
lemmas.  Neither lemma actually uses the fibre norm — the seminormed structure is present only to
*supply the fibre topology* the section space needs.  For a fibre that carries a *different-spelled*
(yet defeq) topology — e.g. the `ContinuousLinearMap.topologicalSpace` (Path B) on a
`BilinearFormBundle` fibre `V x = W x →L[𝕜] W x →L[𝕜] ℝ`, which is what `FiberBundle`/`VectorBundle`
and the concrete coordinate readout lemmas use — the Path-A-baked statements do not unify at
application time (the section-space Picard bridge then cannot consume Path-B coordinate bounds).

The two lemmas below are the identical facts stated with the fibre topology taken as an *explicit*
`[∀ x, TopologicalSpace (V x)]` instance binder (plus the bare `AddCommGroup`/`Module` structure the
vector-bundle already provides), so the section-space topology is synthesised in the caller's context
rather than derived from a seminormed structure.  This lets the section-space Picard bridge apply to
the concrete `BilinearFormBundle` continuous section space (Path B) verbatim.  The proofs are copied
from the seminormed originals unchanged — every step is Banach-`F`-norm level and never touches a
fibre norm.
-/

section TopologicalFibreCoordControl

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {M : Type*} [TopologicalSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- **Topological-fibre version of `norm_le_of_forall_coord_norm_le`.**  Identical statement and
proof, but with the fibre topology taken as an explicit `[∀ x, TopologicalSpace (V x)]` binder
(instead of being derived from a `SeminormedAddCommGroup (V x)`).  Every step is at the Banach
`F`-norm / coordinate level, so the fibre norm is never needed.  This is the boundedness handoff the
section-space Picard–Lindelöf bridge consumes for a section space whose fibre carries a
non-seminormed-derived (e.g. `ContinuousLinearMap`) topology. -/
theorem norm_le_of_forall_coord_norm_le_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {C : ℝ} (hC : 0 ≤ C)
    (hcoord : ∀ i (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ ≤ C) :
    ‖s‖ ≤ C := by
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  have hdist : dist s
      (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover) ≤ C := by
    refine dist_le_of_forall_coord_dist_le (𝕜 := 𝕜) (F := F) (V := V)
      (et := et) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo) (hKoEq := hKoEq)
      (hcover := hcover) (s := s)
      (t := (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover)) hC ?_
    intro i x
    rw [he0]
    simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply, dist_zero_right]
    exact hcoord i x
  rwa [dist_zero_right] at hdist

/-- **Topological-fibre version of `continuousOn_of_forall_coord_continuousOn`.**  Identical
statement and proof, but with the fibre topology taken as an explicit `[∀ x, TopologicalSpace (V x)]`
binder.  The transport `equivCompatibleCoordFamilySubmodule` is a definitional isometry into
`∀ i, C(Kc i, F)`, so coordinatewise time-continuity into `C(Kc i, F)` yields continuity into the
section space — a fact at the Banach `F`-norm level that never touches a fibre norm.  This is the
time-continuity handoff the section-space Picard–Lindelöf bridge consumes for a section space whose
fibre carries a non-seminormed-derived topology. -/
theorem continuousOn_of_forall_coord_continuousOn_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {X : Type*} [TopologicalSpace X]
    {f : X → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {s : Set X}
    (hcoord : ∀ i, ContinuousOn
      (fun x => (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f x)).1 i) s) :
    ContinuousOn f s := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := fun _ _ => rfl
  have hval : Isometry
      (fun a : compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo =>
        (a : CoordFamily (F := F) Kc)) :=
    Isometry.of_nndist_eq fun _ _ => rfl
  have hInd : Topology.IsInducing
      (fun z : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover =>
        ((e z).1 : CoordFamily (F := F) Kc)) :=
    (hval.comp he).isUniformEmbedding.toIsUniformInducing.isInducing
  rw [hInd.continuousOn_iff, continuousOn_pi]
  exact hcoord

/-- **Topological-fibre version of `exists_forall_mem_Icc_coord_norm_le_of_continuousOn`.**
Identical statement and proof, with the fibre topology taken as an explicit
`[∀ x, TopologicalSpace (V x)]` binder.  Each compact coordinate readout is bounded on the compact
time interval by its sup-norm and the finite index family of these bounds is bounded above — a fact
at the Banach `F`-norm level that never touches a fibre norm.  This supplies the centre-readout size
constant the forward-time section-space Picard endpoint chooser consumes. -/
theorem exists_forall_mem_Icc_coord_norm_le_of_continuousOn_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {f : ℝ → ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover}
    {t₀ T : ℝ}
    (hcont : ∀ i, ContinuousOn
      (fun t => (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i)
      (Set.Icc t₀ T)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Icc t₀ T, ∀ i (x : Kc i),
      ‖(equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i x‖ ≤ C := by
  classical
  choose C hC using fun i => isCompact_Icc.exists_bound_of_continuousOn (hcont i)
  obtain ⟨D, hD⟩ := (Set.finite_range C).bddAbove
  refine ⟨max D 0, le_max_right _ _, fun t ht i x => ?_⟩
  calc
    ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i x‖
        ≤ ‖(equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (f t)).1 i‖ :=
      ContinuousMap.norm_coe_le_norm _ x
    _ ≤ C i := hC i t ht
    _ ≤ D := hD (Set.mem_range_self i)
    _ ≤ max D 0 := le_max_left _ _

/-- **Topological-fibre version of `coordContinuousMap_dist_le_dist`.**  Identical statement and
proof, with the fibre topology taken as an explicit `[∀ x, TopologicalSpace (V x)]` binder instead of
derived from a `SeminormedAddCommGroup (V x)`.  Every step is at the section-space
`NormedAddCommGroup` / coordinate-family Banach `F`-norm level (`equivCompatibleCoordFamilySubmodule`
is a definitional isometry onto the compatible-coordinate-family submodule of `∀ i, C(Kc i, F)`) and
never touches a fibre norm, so the seminormed-fibre proof ports verbatim.  This lets the contraction
apply to a section space whose fibre carries a non-seminormed-derived (e.g. `ContinuousLinearMap`)
topology, such as the `BilinearFormBundle` hom fibre at `TangentSpace I`. -/
theorem coordContinuousMap_dist_le_dist_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) :
    dist
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i)
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i)
      ≤ dist s t := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  letI : NormedAddCommGroup
      (compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo) :=
    Submodule.normedAddCommGroup
      (𝕜 := 𝕜) (E := CoordFamily (F := F) Kc)
      (s := compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo)
  let e := equivCompatibleCoordFamilySubmodule
    (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
  have he : Isometry e := fun _ _ => rfl
  have hval : Isometry
      (fun a : compatibleCoordFamilySubmodule (𝕜 := 𝕜) (F := F) et Kc hKc Ko hKo =>
        (a : CoordFamily (F := F) Kc)) :=
    Isometry.of_nndist_eq fun _ _ => rfl
  have hcomp : Isometry
      (fun z : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover =>
        ((e z).1 : CoordFamily (F := F) Kc)) :=
    hval.comp he
  calc
    dist ((e s).1 i) ((e t).1 i)
        ≤ dist ((e s).1 : CoordFamily (F := F) Kc) ((e t).1 : CoordFamily (F := F) Kc) :=
          dist_le_pi_dist _ _ i
    _ = dist s t := hcomp.dist_eq s t

/-- **Topological-fibre version of `coord_dist_le_dist`.**  The pointwise compact coordinate readout
is `1`-Lipschitz in the section distance, stated with the fibre topology as an explicit
`[∀ x, TopologicalSpace (V x)]` binder.  This is the pointwise `hlip` handoff the section-space
Picard–Lindelöf bridge consumes for a section space whose fibre carries a non-seminormed-derived
(e.g. `ContinuousLinearMap`) topology: the geometric Ricci–DeTurck reaction operator produces
`BilinearFormBundle` sections whose hom fibre topology defeats the seminormed-fibre
`coord_dist_le_dist`; this variant applies directly. -/
theorem coord_dist_le_dist_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    dist
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x)
      ((equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x)
      ≤ dist s t :=
  le_trans (ContinuousMap.dist_apply_le_dist x)
    (coordContinuousMap_dist_le_dist_topFibre s t i)

/-- **Topological-fibre version of `coord_zero_apply`.**  The compact coordinate readout of the zero
section vanishes pointwise, stated with the fibre topology as an explicit
`[∀ x, TopologicalSpace (V x)]` binder.  The transport
`toCompatibleCoordFamilySubmoduleContinuousLinearMap` is a continuous *linear* map (built at the
section-space Banach level, never touching a fibre norm), so it sends `0` to `0`. -/
theorem coord_zero_apply_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
      (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
        et Kc hKc Ko hKo hKoEq hcover)).1 i x = 0 := by
  have he0 :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover
        (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
          et Kc hKc Ko hKo hKoEq hcover)) = 0 := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_zero _
  rw [he0]
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply, ContinuousMap.zero_apply]

/-- **Topological-fibre version of `coord_norm_le_norm`:** `‖(coord s).1 i x‖ ≤ ‖s‖`, stated with the
fibre topology as an explicit `[∀ x, TopologicalSpace (V x)]` binder.  The `t = 0` specialisation of
`coord_dist_le_dist_topFibre` combined with `coord_zero_apply_topFibre`.  This is the `hcenter`
handoff the section-space Picard–Lindelöf bridge consumes for a section space whose fibre carries a
non-seminormed-derived (e.g. `ContinuousLinearMap`) topology — turning a section-space centre size
`‖A t σ₀‖ ≤ Mc` into the coordinate centre bound `‖(coord (A t σ₀)).1 i x‖ ≤ Mc`. -/
theorem coord_norm_le_norm_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    ‖(equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x‖ ≤ ‖s‖ := by
  have h := coord_dist_le_dist_topFibre s
    (0 : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) i x
  rw [coord_zero_apply_topFibre, dist_zero_right, dist_zero_right] at h
  exact h

/-- **Topological-fibre version of `coord_add_apply`.**  The compact coordinate readout is additive:
`(coord (s + t)).1 i x = (coord s).1 i x + (coord t).1 i x`, stated with the fibre topology as an
explicit `[∀ x, TopologicalSpace (V x)]` binder (instead of derived from a
`SeminormedAddCommGroup (V x)`).  The transport `toCompatibleCoordFamilySubmoduleContinuousLinearMap`
is a continuous *linear* map (built at the section-space Banach level, never touching a fibre norm),
so it sends `s + t` to `equiv s + equiv t`, and the coordinate/point projections of a sum coordinate
family are pointwise sums.  This is the additivity handoff used to reduce the coordinate estimates of
an *affine* section-space operator `A t s = L s + b` (a linear/reaction generator plus a fixed source)
to those of its non-affine part: the fixed source `b` contributes the same coordinate summand to
`A t s` and `A t s'`, which cancels in the coordinate distance (`dist_add_right`).  This is the
fibre-topology-native companion the geometric Ricci–DeTurck chart operator consumes, since its
`BilinearFormBundle` hom fibre topology defeats the seminormed-fibre `coord_add_apply`. -/
theorem coord_add_apply_topFibre
    {κ : Type*} [Finite κ] [T2Space M]
    {et : κ → Trivialization F (TotalSpace.proj : TotalSpace F V → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s t : ContinuousSectionSpace (𝕜 := 𝕜) (F := F) (V := V)
      et Kc hKc Ko hKo hKoEq hcover) (i : κ) (x : Kc i) :
    (equivCompatibleCoordFamilySubmodule
      (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s + t)).1 i x
      = (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s).1 i x
        + (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t).1 i x := by
  have he :
      (equivCompatibleCoordFamilySubmodule
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover (s + t))
      = (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover s)
        + (equivCompatibleCoordFamilySubmodule
          (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover t) := by
    rw [← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover,
      ← toCompatibleCoordFamilySubmoduleContinuousLinearMap_apply
        (𝕜 := 𝕜) (F := F) (V := V) et Kc hKc Ko hKo hKoEq hcover]
    exact map_add _ s t
  rw [he]
  simp only [AddMemClass.coe_add, Pi.add_apply, ContinuousMap.add_apply]

end TopologicalFibreCoordControl

end ContinuousSectionSpace

end Bundle.Trivialization

end PoincareCurvature
