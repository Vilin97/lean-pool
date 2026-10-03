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

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureDerivativeComparison
public import LeanPool.PoincareGeometry.AlmostSchur.ScalarCurvatureTraceDerivative

/-! # Actual contracted Bianchi for the constructed Levi-Civita connection

The curvature core and smooth-extension locality lemmas used below are the
attributed extraction in CurvatureVendor (see its PROVENANCE.json). No prior
Schur proof is imported.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators
namespace AlmostSchur
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 1 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 3 E (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)
local instance actualBianchiFiniteDimensional (x : M) : FiniteDimensional ℝ (TM x) :=
  VectorBundle.finiteDimensional ℝ E TM x

/-- Raising an index commutes with covariant differentiation: the metric
Leibniz rule cancels the differentiated test slot. -/
theorem inner_covariant_ricciRaised_eq
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X Y Z : Π y, TM y) (x : M)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
    inner ℝ (cov (fun y ↦ ricciRaisedEndomorphism cov y (Y y)) x (X x) -
      ricciRaisedEndomorphism cov x (cov Y x (X x))) (Z x) =
      ricciDirectionalDerivative cov X Y Z x := by
  have hAY := (contMDiffAt_ricciRaisedEndomorphism_one cov hm ht x).clm_bundle_apply
    (hY.of_le (by norm_num : (1 : ℕ∞ω) ≤ 3))
  have hd := CovariantDerivative.IsMetricCompatible.mvfderiv_inner_eq hm X
    (hAY.mdifferentiableAt (by norm_num)) (hZ.mdifferentiableAt (by norm_num))
  simp only [inner_ricciRaisedEndomorphism] at hd
  simp only [inner_sub_left, inner_ricciRaisedEndomorphism, ricciDirectionalDerivative]
  linarith

/-- Transport any tangent orthonormal basis to the model fibre of a compatible
trivialization. Its local frame agrees with that orthonormal basis at the point. -/
theorem localFrame_map_orthonormalBasis
    {ι : Type} [Fintype ι] (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (hx : x ∈ e.baseSet)
    (o : OrthonormalBasis ι ℝ (TM x)) (i : ι) :
    e.localFrame (o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)) i x = o i := by
  rw [e.localFrame_apply_of_mem_baseSet _ hx]
  change (e.linearEquivAt (R := ℝ) x hx).symm
    ((e.linearEquivAt (R := ℝ) x hx) (o i)) = o i
  exact LinearEquiv.symm_apply_apply _ _

/-- The matching frame coefficient is the actual fibre inner product. -/
theorem localFrameCoeff_map_orthonormalBasis
    {ι : Type} [Fintype ι] (x : M)
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (hx : x ∈ e.baseSet)
    (o : OrthonormalBasis ι ℝ (TM x)) (i : ι) (v : TM x) :
    e.localFrameCoeff I (o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)) i x v =
      inner ℝ v (o i) := by
  have hh := e.localFrameCoeff_apply_of_mem_baseSet
    (I := I) (o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)) hx
    (FiberBundle.extend E v) i
  have hb : e.basisAt (o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)) hx =
      o.toBasis := by
    ext j
    change (e.linearEquivAt (R := ℝ) x hx).symm
      ((e.linearEquivAt (R := ℝ) x hx) (o j)) = o j
    exact LinearEquiv.symm_apply_apply _ _
  rw [hb] at hh
  simpa only [FiberBundle.extend_apply_self, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, real_inner_comm] using hh

/-- Germ locality of the corrected curvature derivative, including its outer
covariant differentiation. The C³ hypotheses discharge all derivative premises. -/
theorem secondBianchiAux_eq_of_germs
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    {X U Y Z X' U' Y' Z' : Π y, TM y} {x : M}
    (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
    (hU : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% U) x)
    (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
    (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x)
    (hX' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X') x)
    (hU' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% U') x)
    (hY' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y') x)
    (hZ' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z') x)
    (eX : X =ᶠ[𝓝 x] X') (eU : U =ᶠ[𝓝 x] U')
    (eY : Y =ᶠ[𝓝 x] Y') (eZ : Z =ᶠ[𝓝 x] Z') :
    cov.secondBianchiAuxAlmostSchur X U Y Z x = cov.secondBianchiAuxAlmostSchur X' U' Y' Z' x := by
  rw [← curvatureDirectionalDerivative_eq_secondBianchiAux cov hm ht hX hU hY hZ,
    ← curvatureDirectionalDerivative_eq_secondBianchiAux cov hm ht hX' hU' hY' hZ']
  have hc {V V' : Π y, TM y}
      (hV : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% V) x)
      (hV' : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% V') x)
      (he : V =ᶠ[𝓝 x] V') : cov V x = cov V' x :=
    cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
      (hV.mdifferentiableAt (by norm_num)) (hV'.mdifferentiableAt (by norm_num)) (by simp) he
  have hR : (fun y ↦ cov.curvatureTensorAlmostSchur y (U y) (Y y) (Z y)) =ᶠ[𝓝 x]
      (fun y ↦ cov.curvatureTensorAlmostSchur y (U' y) (Y' y) (Z' y)) := by
    filter_upwards [eU, eY, eZ] with y hu hy hz
    rw [hu, hy, hz]
  have hcR := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    ((contMDiffAt_curvatureTensor_apply_one cov hm ht hU hY hZ).mdifferentiableAt
      (by norm_num))
    ((contMDiffAt_curvatureTensor_apply_one cov hm ht hU' hY' hZ').mdifferentiableAt
      (by norm_num)) (by simp) hR
  simp only [curvatureDirectionalDerivative, hcR, hc hU hU' eU, hc hY hY' eY,
    hc hZ hZ' eZ, eX.eq_of_nhds, eU.eq_of_nhds, eY.eq_of_nhds, eZ.eq_of_nhds]

/-- Scalar differentiation is the trace of corrected Ricci differentiation in
an arbitrary trivialization made orthonormal at the single evaluation point. -/
theorem mvfderiv_scalarCurvature_eq_sum_ricciDirectionalDerivative
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (hm : tangentMetricCompatible cov) (ht : cov.torsion = 0)
    (X : Π y, TM y) (x : M)
    {ι : Type} [Fintype ι]
    (e : Trivialization E (TotalSpace.proj : TotalSpace E TM → M))
    [MemTrivializationAtlas e] (hx : x ∈ e.baseSet)
    (o : OrthonormalBasis ι ℝ (TM x)) :
    let b := o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)
    mvfderiv I cov.scalarCurvatureAlmostSchur x (X x) =
      ∑ i, ricciDirectionalDerivative cov X (e.localFrame b i) (e.localFrame b i) x := by
  dsimp only
  rw [mvfderiv_scalarCurvature_eq_contraction cov hm ht X x e
    (o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)) hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [localFrameCoeff_map_orthonormalBasis]
  rw [← localFrame_map_orthonormalBasis x e hx o i]
  exact inner_covariant_ricciRaised_eq cov hm ht X _ _ x
    (contMDiffAt_localFrame_of_mem 3 e _ i hx)
    (contMDiffAt_localFrame_of_mem 3 e _ i hx)

local instance actualBianchiManifoldMinTwo : IsManifold I (minSmoothness ℝ 2) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance actualBianchiManifoldMinThree : IsManifold I (minSmoothness ℝ 3) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance actualBianchiManifoldMinFour : IsManifold I (minSmoothness ℝ 4) M :=
  IsManifold.of_le (n := ∞) (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.mpr le_top)
local instance actualBianchiManifoldTwoAddOne : IsManifold I ((2 : ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (2 + 1 : ℕ∞) ≤ ⊤))
local instance actualBianchiManifoldThreeAddOne : IsManifold I ((3 : ℕ∞) + 1) M :=
  IsManifold.of_le (n := ∞) (by exact_mod_cast (le_top : (3 + 1 : ℕ∞) ≤ ⊤))

/-- Double contraction on the local frame of the canonical trivialization.
The attributed smooth-extension germ lemma permits applying the global
section version of the curvature core without asserting global frame smoothness. -/
theorem leviCivita_secondBianchiAux_doubleContraction_localFrame
    (x : M) {ι : Type} [Fintype ι] (b : Module.Basis ι ℝ E)
    (w : Π y, TM y) (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    let cov := leviCivitaConnection (I := I) (M := M)
    let f := (trivializationAt E TM x).localFrame b
    (∑ i, ∑ k, inner ℝ (cov.secondBianchiAuxAlmostSchur w (f k) (f i) (f i) x) (f k x)) =
      2 * ∑ i, ∑ k, inner ℝ
        (cov.secondBianchiAuxAlmostSchur (f i) (f k) (f i) w x) (f k x) := by
  let cov := leviCivitaConnection (I := I) (M := M)
  let f := (trivializationAt E TM x).localFrame b
  let s := fun i ↦ CovariantDerivative.smoothExtendAlmostSchur I E TM x (f i x)
  have hs i : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% (s i)) :=
    CovariantDerivative.smoothExtend_contMDiff_threeAlmostSchur x (f i x)
  have hf i : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% (f i)) x :=
    contMDiffAt_localFrame_of_mem 3 _ b i (mem_baseSet_trivializationAt E TM x)
  have he i : f i =ᶠ[𝓝 x] s i :=
    Filter.EventuallyEq.symm (CovariantDerivative.smoothExtend_trivializationAt_localFrame_eventuallyEqAlmostSchur
      (I := I) (F := E) (V := TM) b x i)
  have h1 i k : cov.secondBianchiAuxAlmostSchur w (f k) (f i) (f i) x =
      cov.secondBianchiAuxAlmostSchur w (s k) (s i) (s i) x :=
    secondBianchiAux_eq_of_germs cov leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion (hw x) (hf k) (hf i) (hf i)
      (hw x) (hs k x) (hs i x) (hs i x) .rfl (he k) (he i) (he i)
  have h2 i k : cov.secondBianchiAuxAlmostSchur (f i) (f k) (f i) w x =
      cov.secondBianchiAuxAlmostSchur (s i) (s k) (s i) w x :=
    secondBianchiAux_eq_of_germs cov leviCivitaConnection_metricCompatible
      leviCivitaConnection_torsion (hf i) (hf k) (hf i) (hw x)
      (hs i x) (hs k x) (hs i x) (hw x) (he i) (he k) (he i) .rfl
  have core := CovariantDerivative.curvatureCovariantDerivativeInner_doubleContraction_sectionsAlmostSchur
    cov x leviCivitaConnection_torsion
    (tangentMetricCompatible_to_curvatureVendor cov leviCivitaConnection_metricCompatible)
    s w hs hw
  change (∑ i, ∑ k, inner ℝ (cov.secondBianchiAuxAlmostSchur w (f k) (f i) (f i) x) (f k x)) =
    2 * ∑ i, ∑ k, inner ℝ (cov.secondBianchiAuxAlmostSchur (f i) (f k) (f i) w x) (f k x)
  simp only [h1, h2]
  simpa only [s, CovariantDerivative.smoothExtend_applyAlmostSchur] using core

/-- Actual contracted Bianchi: the scalar differential is twice the tangent
orthonormal contraction of the corrected Ricci differential. The local frame
is orthonormal only at x, and both Ricci-slot corrections remain explicit in
ricciDirectionalDerivative. No curvature or connection identity is assumed. -/
theorem leviCivita_contractedBianchi_actual
    (x : M) {ι : Type} [Fintype ι] (o : OrthonormalBasis ι ℝ (TM x))
    (w : Π y, TM y) (hw : ContMDiff I (I.prod 𝓘(ℝ, E)) 3 (T% w)) :
    let cov := leviCivitaConnection (I := I) (M := M)
    let e := trivializationAt E TM x
    let b := o.toBasis.map (e.linearEquivAt (R := ℝ) x (mem_baseSet_trivializationAt E TM x))
    let f := e.localFrame b
    mvfderiv I cov.scalarCurvatureAlmostSchur x (w x) =
      2 * ∑ i, ricciDirectionalDerivative cov (f i) (f i) w x := by
  let cov := leviCivitaConnection (I := I) (M := M)
  let e := trivializationAt E TM x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E TM x
  let b := o.toBasis.map (e.linearEquivAt (R := ℝ) x hx)
  let f := e.localFrame b
  have hf i : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% (f i)) x :=
    contMDiffAt_localFrame_of_mem 3 e b i hx
  have hc (X Y Z : Π y, TM y)
      (hX : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% X) x)
      (hY : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Y) x)
      (hZ : ContMDiffAt I (I.prod 𝓘(ℝ, E)) 3 (T% Z) x) :
      ricciDirectionalDerivative cov X Y Z x =
        ∑ k, inner ℝ (cov.secondBianchiAuxAlmostSchur X (f k) Y Z x) (f k x) := by
    rw [ricciDirectionalDerivative_eq_secondBianchiAux_contraction cov
      leviCivitaConnection_metricCompatible leviCivitaConnection_torsion
      X Y Z x hX hY hZ e b hx]
    apply Finset.sum_congr rfl
    intro k _
    rw [localFrameCoeff_map_orthonormalBasis]
    change inner ℝ _ (o k) = inner ℝ _ (e.localFrame b k x)
    rw [localFrame_map_orthonormalBasis]
  change mvfderiv I cov.scalarCurvatureAlmostSchur x (w x) =
    2 * ∑ i, ricciDirectionalDerivative cov (f i) (f i) w x
  rw [mvfderiv_scalarCurvature_eq_sum_ricciDirectionalDerivative cov
    leviCivitaConnection_metricCompatible leviCivitaConnection_torsion w x e hx o]
  change (∑ i, ricciDirectionalDerivative cov w (f i) (f i) x) =
    2 * ∑ i, ricciDirectionalDerivative cov (f i) (f i) w x
  simp only [hc w _ _ (hw x) (hf _) (hf _), hc _ _ w (hf _) (hf _) (hw x)]
  exact leviCivita_secondBianchiAux_doubleContraction_localFrame x b w hw

/-- Tangent-fibre form of actual contracted Bianchi, with no regularity
premise on a chosen vector or vector field. The standard orthonormal basis
is transported into the model fibre; the test vector uses the attributed
canonical smooth extension. Both correction terms are displayed explicitly. -/
theorem leviCivita_contractedBianchi_tangent (x : M) (v : TM x) :
    let cov := leviCivitaConnection (I := I) (M := M)
    let o := stdOrthonormalBasis ℝ (TM x)
    let e := trivializationAt E TM x
    let b := o.toBasis.map (e.linearEquivAt (R := ℝ) x (mem_baseSet_trivializationAt E TM x))
    let f := e.localFrame b
    let W := CovariantDerivative.smoothExtendAlmostSchur I E TM x v
    mvfderiv I cov.scalarCurvatureAlmostSchur x v = 2 * ∑ i,
      (mvfderiv I (fun y ↦ cov.ricciCurvatureAlmostSchur y (f i y) (W y)) x (f i x) -
        cov.ricciCurvatureAlmostSchur x (cov (f i) x (f i x)) v -
        cov.ricciCurvatureAlmostSchur x (f i x) (cov W x (f i x))) := by
  have h := leviCivita_contractedBianchi_actual x (stdOrthonormalBasis ℝ (TM x))
    (CovariantDerivative.smoothExtendAlmostSchur I E TM x v)
    (CovariantDerivative.smoothExtend_contMDiff_threeAlmostSchur x v)
  simpa only [ricciDirectionalDerivative, CovariantDerivative.smoothExtend_applyAlmostSchur] using h

end AlmostSchur
