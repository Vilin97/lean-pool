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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Along

/-!
# Higher regularity of affine torsion

This file records the regularity needed to turn a `C²` affine tangent
connection into a `C²` torsion-free one.  The correction is one half of the
torsion tensor itself and is algebraically metric-free; the bundled
regularity theorems are stated in the smooth Riemannian tangent-bundle context
used by the tensor-heat layer.
-/

@[expose] public noncomputable section
open Bundle FiberBundle Set
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TEnd" =>
  (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
local notation "TCorr" =>
  (fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)

namespace CovariantDerivative

/-- Evaluation of the torsion of a `C²` affine connection on two `C³`
tangent fields is `C²`. -/
theorem contMDiffOn_torsion_section_two
    [ContMDiffVectorBundle 3 E TM I]
    {s : Set M} (hs : IsOpen s)
    {cov : CovariantDerivative I E TM}
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun s)
    {σ τ : Π y : M, TangentSpace I y}
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (σ y)) s)
    (hτ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3 (fun y ↦ TotalSpace.mk' E y (τ y)) s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
      (fun x ↦ TotalSpace.mk' E x (cov.torsion x (σ x) (τ x))) s := by
  have hσ₂ := hσ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hτ₂ := hτ.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hcovσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun x ↦ TM x →L[ℝ] TM x)
          x (cov σ x)) s :=
    hcov.contMDiff hσ
  have hcovτ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := fun x ↦ TM x →L[ℝ] TM x)
          x (cov τ x)) s :=
    hcov.contMDiff hτ
  have hAlongστ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (cov.along σ τ y)) s := by
    simpa [CovariantDerivative.along] using hcovτ.clm_bundle_apply hσ₂
  have hAlongτσ :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (cov.along τ σ y)) s := by
    simpa [CovariantDerivative.along] using hcovσ.clm_bundle_apply hτ₂
  letI : IsManifold I (minSmoothness ℝ 3) M := by
    apply IsManifold.of_le (n := 4)
    norm_num
  letI : IsManifold I ((3 : ℕ∞) + 1) M := by
    apply IsManifold.of_le (n := 4)
    norm_num
  have hBracketWithin :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracketWithin I σ τ s y)) s := by
    simpa using
      (hσ.mlieBracketWithin_vectorField (I := I) (m := (2 : ℕ∞)) hτ hs.uniqueMDiffOn
        (by norm_num))
  have hBracket :
      ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun y ↦ TotalSpace.mk' E y (VectorField.mlieBracket I σ τ y)) s := by
    refine ContMDiffOn.congr hBracketWithin ?_
    intro x hx
    have hσx : MDiffAt (T% σ) x := by
      exact ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
          (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero)
    have hτx : MDiffAt (T% τ) x := by
      exact ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
          (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero)
    congr 1
    simpa using
      (VectorField.mlieBracketWithin_eq_mlieBracket (I := I) (s := s) (x := x)
        (hs.uniqueMDiffWithinAt hx) hσx hτx).symm
  have hEq :
      Set.EqOn
        (fun x ↦ TotalSpace.mk' E x (cov.torsion x (σ x) (τ x)))
        (fun x ↦ TotalSpace.mk' E x
          (cov.along σ τ x - cov.along τ σ x - VectorField.mlieBracket I σ τ x))
        s := by
    intro x hx
    congr 1
    simpa [CovariantDerivative.along] using
      (cov.torsion_apply
        ((((hσ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
            (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero)
        ((((hτ x hx).contMDiffAt (hs.mem_nhds hx)).of_le
            (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).mdifferentiableAt one_ne_zero))
  refine ContMDiffOn.congr ((hAlongστ.sub_section hAlongτσ).sub_section hBracket) ?_
  intro x hx
  simpa using (hEq hx)

/-- The torsion tensor of a `C²` affine connection is a `C²` section of the
bundle of tangent-valued bilinear maps. -/
theorem contMDiffOn_torsion_tensor_two
    [ContMDiffVectorBundle 3 E TM I]
    {cov : CovariantDerivative I E TM}
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M)) [MemTrivializationAtlas e]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℝ E)
    {u : Set M} (hu : IsOpen u) (hu' : u ⊆ e.baseSet)
    (hcov : ContMDiffCovariantDerivativeOn E 2 cov.toFun u) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (cov.torsion x)) u := by
  classical
  letI tangentTwo : ContMDiffVectorBundle 2 E TM I :=
    ContMDiffVectorBundle.of_le (F := E) (E := TM) (IB := I)
      (m := 2) (n := 3) (by norm_num)
  letI tangentOne : ContMDiffVectorBundle 1 E TM I :=
    ContMDiffVectorBundle.of_le (F := E) (E := TM) (IB := I)
      (m := 1) (n := 2) (by norm_num)
  letI endTwo : ContMDiffVectorBundle 2 (E →L[ℝ] E) TEnd I :=
    ContMDiffVectorBundle.continuousLinearMap
  letI endOne : ContMDiffVectorBundle 1 (E →L[ℝ] E) TEnd I :=
    ContMDiffVectorBundle.of_le (F := E →L[ℝ] E) (E := TEnd) (IB := I)
      (m := 1) (n := 2) (by norm_num)
  let eLine : Trivialization ℝ (TotalSpace.proj : TotalSpace ℝ (fun _ : M ↦ ℝ) → M) :=
    Bundle.Trivial.trivialization M ℝ
  letI : MemTrivializationAtlas eLine := by
    constructor
    change Bundle.Trivial.trivialization M ℝ ∈ ({Bundle.Trivial.trivialization M ℝ} : Set _)
    simp [eLine]
  let eStar :
      Trivialization (E →L[ℝ] ℝ)
        (TotalSpace.proj : TotalSpace (E →L[ℝ] ℝ)
          (fun x : M ↦ TM x →L[ℝ] ℝ) → M) :=
    e.continuousLinearMap (σ := RingHom.id ℝ) eLine
  have huStar : u ⊆ eStar.baseSet := by
    intro x hx
    simp [eStar, eLine, hu' hx]
  have hdual :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] ℝ) (E := fun x ↦ TM x →L[ℝ] ℝ) x
          (eStar.localFrame (continuousDualBasis b) i x)) u := by
    intro i
    exact
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := eStar)
        (n := (2 : WithTop ℕ∞)) (b := continuousDualBasis b) i).mono huStar
  have hvalue :
      ∀ i j, ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2
        (fun x ↦ TotalSpace.mk' E x
          (cov.torsion x (e.localFrame b i x) (e.localFrame b j x))) u := by
    intro i j
    have hframeI :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b i x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (3 : WithTop ℕ∞)) (b := b) i).mono hu'
    have hframeJ :
        ContMDiffOn I (I.prod 𝓘(ℝ, E)) 3
          (fun x ↦ TotalSpace.mk' E x (e.localFrame b j x)) u :=
      (Bundle.Trivialization.contMDiffOn_localFrame_baseSet (I := I) (e := e)
        (n := (3 : WithTop ℕ∞)) (b := b) j).mono hu'
    exact contMDiffOn_torsion_section_two (I := I) (E := E) hu hcov hframeI hframeJ
  have hinner :
      ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E) (E := TEnd) x
          (∑ j,
            (eStar.localFrame (continuousDualBasis b) j x).smulRight
              (cov.torsion x (e.localFrame b i x) (e.localFrame b j x)))) u := by
    intro i
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun j hj ↦
        ContMDiffOn.smulRightSection_of_level (n := (2 : WithTop ℕ∞))
          (I := I) (F := E) (V := TM) hu (hdual j) (hvalue i j))
  have hsum :
      ContMDiffOn I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
          (∑ i,
            (eStar.localFrame (continuousDualBasis b) i x).smulRight
              (∑ j,
                (eStar.localFrame (continuousDualBasis b) j x).smulRight
                  (cov.torsion x (e.localFrame b i x) (e.localFrame b j x))))) u := by
    simpa using
      (ContMDiffOn.sum_section (s := (Finset.univ : Finset ι)) fun i hi ↦
        ContMDiffOn.smulRightSection_of_level (n := (2 : WithTop ℕ∞))
          (I := I) (F := E →L[ℝ] E) (V := TEnd) hu (hdual i) (hinner i))
  refine ContMDiffOn.congr hsum ?_
  intro x hx
  have hxE : x ∈ e.baseSet := hu' hx
  have hxStar : x ∈ eStar.baseSet := huStar hx
  apply congrArg (fun A ↦ TotalSpace.mk'
    (E := TCorr) (E →L[ℝ] E →L[ℝ] E) x A)
  ext v w
  let basis := e.basisAt b hxE
  let sV : Π y : M, TM y := fun y ↦ ∑ j, basis.repr v j • e.localFrame b j y
  let sW : Π y : M, TM y := fun y ↦ ∑ j, basis.repr w j • e.localFrame b j y
  have hsVx : sV x = v := by
    simpa [sV, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr v
  have hsWx : sW x = w := by
    simpa [sW, basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      using basis.sum_repr w
  have hcoeffV : ∀ i, e.localFrameCoeff I b i x v = basis.repr v i := by
    intro i
    calc
      e.localFrameCoeff I b i x v = e.localFrameCoeff I b i x (sV x) := by rw [hsVx]
      _ = basis.repr (sV x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := sV) (i := i))
      _ = basis.repr v i := by rw [hsVx]
  have hcoeffW : ∀ i, e.localFrameCoeff I b i x w = basis.repr w i := by
    intro i
    calc
      e.localFrameCoeff I b i x w = e.localFrameCoeff I b i x (sW x) := by rw [hsWx]
      _ = basis.repr (sW x) i := by
            simpa [basis] using
              (Bundle.Trivialization.localFrameCoeff_apply_of_mem_baseSet
                (I := I) (e := e) (b := b) (hx := hxE) (s := sW) (i := i))
      _ = basis.repr w i := by rw [hsWx]
  have hdual_basis :
      ∀ i j,
        eStar.localFrame (continuousDualBasis b) i x (e.localFrame b j x) = if i = j then 1 else 0 := by
    intro i j
    rw [Bundle.Trivialization.localFrame_apply_of_mem_baseSet
      (e := eStar) (b := continuousDualBasis b) hxStar,
      Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
    simp only [Bundle.Trivialization.basisAt, Module.Basis.map_apply]
    rw [Bundle.Trivialization.linearEquivAt_symm_apply,
      Bundle.Trivialization.linearEquivAt_symm_apply]
    rw [← Bundle.Trivialization.symmL_apply (R := ℝ) e hxE]
    have hsymm :
        eStar.symm x ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x)) := by
      change
        (Bundle.Pretrivialization.continuousLinearMap (RingHom.id ℝ) e eLine).symm x
            ((continuousDualBasis b) i) =
          (eLine.symmL ℝ x).comp
            (((continuousDualBasis b) i).comp (e.continuousLinearMapAt ℝ x))
      simpa [eLine] using
        (Bundle.Pretrivialization.continuousLinearMap_symm_apply'
          (σ := RingHom.id ℝ) (e₁ := e) (e₂ := eLine) (b := x)
          (hb := ⟨hxE, by simp [eLine]⟩) ((continuousDualBasis b) i))
    rw [hsymm]
    simp only [ContinuousLinearMap.comp_apply]
    rw [Bundle.Trivialization.continuousLinearMapAt_symmL (e := e) (R := ℝ) (hb := hxE)]
    simpa [eLine, continuousDualBasis, Finsupp.single_apply, eq_comm]
  have hdual_applyV :
      ∀ i, eStar.localFrame (continuousDualBasis b) i x v = e.localFrameCoeff I b i x v := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x v
          = eStar.localFrame (continuousDualBasis b) i x (∑ j, basis.repr v j • basis j) := by
              rw [basis.sum_repr v]
      _ = ∑ j, basis.repr v j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr v j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr v j * r) (hdual_basis i j)
      _ = basis.repr v i := by simp
      _ = e.localFrameCoeff I b i x v := by rw [hcoeffV i]
  have hdual_applyW :
      ∀ i, eStar.localFrame (continuousDualBasis b) i x w = e.localFrameCoeff I b i x w := by
    intro i
    calc
      eStar.localFrame (continuousDualBasis b) i x w
          = eStar.localFrame (continuousDualBasis b) i x (∑ j, basis.repr w j • basis j) := by
              rw [basis.sum_repr w]
      _ = ∑ j, basis.repr w j * eStar.localFrame (continuousDualBasis b) i x (basis j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro j hj
            rw [map_smul]
            simp [smul_eq_mul]
      _ = ∑ j, basis.repr w j * (if i = j then 1 else 0) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simpa [basis, Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
              using congrArg (fun r : ℝ ↦ basis.repr w j * r) (hdual_basis i j)
      _ = basis.repr w i := by simp
      _ = e.localFrameCoeff I b i x w := by rw [hcoeffW i]
  have hdecompV :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x = v := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x
          = ∑ i, e.localFrameCoeff I b i x v • e.localFrame b i x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hdual_applyV i]
      _ = ∑ i, basis.repr v i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeffV i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = v := by simpa using basis.sum_repr v
  have hdecompW :
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) w • e.localFrame b i x = w := by
    calc
      ∑ i, (eStar.localFrame (continuousDualBasis b) i x) w • e.localFrame b i x
          = ∑ i, e.localFrameCoeff I b i x w • e.localFrame b i x := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [hdual_applyW i]
      _ = ∑ i, basis.repr w i • basis i := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [basis, hcoeffW i,
              Bundle.Trivialization.localFrame_apply_of_mem_baseSet (e := e) (b := b) hxE]
      _ = w := by simpa using basis.sum_repr w
  calc
    cov.torsion x v w =
        cov.torsion x
          (∑ i, (eStar.localFrame (continuousDualBasis b) i x) v • e.localFrame b i x)
          (∑ j, (eStar.localFrame (continuousDualBasis b) j x) w • e.localFrame b j x) := by
            rw [hdecompV, hdecompW]
    _ = ∑ i, ∑ j,
          (eStar.localFrame (continuousDualBasis b) i x) v •
            (eStar.localFrame (continuousDualBasis b) j x) w •
              cov.torsion x (e.localFrame b i x) (e.localFrame b j x) := by
            simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply,
              ContinuousLinearMap.smul_apply, Finset.smul_sum]
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            module
    _ = ((∑ i,
          (eStar.localFrame (continuousDualBasis b) i x).smulRight
            (∑ j,
              (eStar.localFrame (continuousDualBasis b) j x).smulRight
                (cov.torsion x (e.localFrame b i x) (e.localFrame b j x)))) v) w := by
          simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.smul_sum]
          simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.smulRight_apply]

/-- A globally `C²` affine connection has a globally `C²` torsion tensor. -/
theorem contMDiff_torsion_tensor_two
    [ContMDiffVectorBundle 3 E TM I]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 2] :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (cov.torsion x)) := by
  apply contMDiff_of_locally_contMDiffOn
  intro x
  let e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M) :=
    trivializationAt E TM x
  let b := Module.finBasis ℝ E
  refine ⟨e.baseSet, e.open_baseSet,
    FiberBundle.mem_baseSet_trivializationAt E TM x, ?_⟩
  have hcovOn : ContMDiffCovariantDerivativeOn E 2 cov.toFun e.baseSet :=
    contMDiffCovariantDerivativeOn_two_of_contMDiffCovariantDerivative_two
      (I := I) (F := E) (V := TM) e.open_baseSet
  simpa [e, b] using
    (contMDiffOn_torsion_tensor_two (I := I) (E := E) (cov := cov) e b
      e.open_baseSet (subset_refl _) hcovOn)

/-- The metric-free torsion correction which makes an affine connection
torsion-free.  Its first argument is the differentiated vector, as for
`CovariantDerivative.addOneForm`. -/
noncomputable def torsionFreeCorrection (cov : CovariantDerivative I E TM) (x : M) :
    TCorr x :=
  (1 / 2 : ℝ) • cov.torsion x

/-- The half-torsion correction is `C²` when the original connection is `C²`. -/
theorem contMDiff_torsionFreeCorrection_two
    [ContMDiffVectorBundle 3 E TM I]
    {cov : CovariantDerivative I E TM} [ContMDiffCovariantDerivative cov 2] :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
        (torsionFreeCorrection cov x)) := by
  simpa [torsionFreeCorrection] using
    (ContMDiff.const_smul_section (a := (1 / 2 : ℝ))
      (contMDiff_torsion_tensor_two (I := I) (E := E) (cov := cov)))

/-- Adding `torsionFreeCorrection` removes torsion. -/
theorem torsionFreeCorrection_isTorsionFree (cov : CovariantDerivative I E TM) :
    (CovariantDerivative.addOneForm cov (torsionFreeCorrection cov)).IsTorsionFree := by
  unfold IsTorsionFree
  ext x u v
  rw [torsion_addOneForm_apply]
  change cov.torsion x u v + ((1 / 2 : ℝ) • cov.torsion x) v u -
    ((1 / 2 : ℝ) • cov.torsion x) u v = 0
  simp only [ContinuousLinearMap.smul_apply]
  have hanti : cov.torsion x v u = -cov.torsion x u v :=
    cov.torsion_antisymm v u
  rw [hanti]
  module

/-- A global `C²` torsion-free affine connection exists on every σ-compact
smooth tangent bundle admitting a `C³` vector-bundle structure. -/
theorem exists_contMDiffTorsionFreeAffineConnection_two
    [SigmaCompactSpace M]
    [ContMDiffVectorBundle 3 E TM I] :
    ∃ cov : CovariantDerivative I E TM,
      cov.IsTorsionFree ∧ ContMDiffCovariantDerivative cov 2 := by
  obtain ⟨cov, hcov⟩ := exists_contMDiffAffineConnection_two (I := I) (E := E) (M := M)
  letI : ContMDiffCovariantDerivative cov 2 := hcov
  let corrected := CovariantDerivative.addOneForm cov (torsionFreeCorrection cov)
  have hcorrection :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] E)) 2
        (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] E) (E := TCorr) x
          (torsionFreeCorrection cov x)) :=
    contMDiff_torsionFreeCorrection_two (I := I) (E := E) (cov := cov)
  have hcorrected : ContMDiffCovariantDerivative corrected 2 := by
    simpa [corrected] using
      (ContMDiffCovariantDerivative.addOneForm (I := I) (E := E) (F := E) (V := TM)
        (n := 2) (cov := cov) hcorrection)
  refine ⟨corrected, ?_, hcorrected⟩
  simpa [corrected] using torsionFreeCorrection_isTorsionFree (I := I) (E := E) cov

end CovariantDerivative
