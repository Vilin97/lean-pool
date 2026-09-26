/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
public import LeanPool.CoarseGraining.Homogenization.Ambient.HilbertFinite
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # L2Ambient -/

@[expose] public section

namespace Homogenization

/-!
This file introduces the actual `L²` ambient types used later to package the
potential and solenoidal spaces as subspaces of a Hilbert space.

The current Sobolev layer still uses predicate-level `MemLp` witnesses in many
places. This file provides the first typed `Lp` layer on bounded domains so the
closed-subspace and minimization arguments can be formulated cleanly.
-/

/-- The restricted Lebesgue measure on a domain `U ⊆ \R^d`. -/
noncomputable abbrev volumeMeasureOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U

/-- Scalar-valued `L²(U)` with respect to restricted Lebesgue measure. -/
noncomputable abbrev ScalarL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp ℝ 2 (volumeMeasureOn U)

/-- Vector-valued `L²(U; \R^d)`. -/
noncomputable abbrev VectorL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (Vec d) 2 (volumeMeasureOn U)

/-- Block-valued `L²(U; \R^{2d})`. -/
noncomputable abbrev BlockL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (BlockVec d) 2 (volumeMeasureOn U)

/-- Hilbert-valued `L²(U; \R^d)` built from the custom Euclidean carrier
`HilbertVec d`. This is the intended ambient space for Hilbert-space arguments. -/
noncomputable abbrev HilbertVectorL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (HilbertVec d) 2 (volumeMeasureOn U)

/-- Hilbert-valued `L²(U; \R^{2d})` built from the custom Euclidean carrier
`HilbertBlockVec d`. This is the intended ambient space for the doubled
`\mu`-problem. -/
noncomputable abbrev HilbertBlockL2 {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.Lp (HilbertBlockVec d) 2 (volumeMeasureOn U)

noncomputable instance instMeasurableSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    MeasurableSpace (HilbertVectorL2 U) :=
  borel _

noncomputable instance instBorelSpaceHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} :
    BorelSpace (HilbertVectorL2 U) :=
  ⟨rfl⟩

/-- Predicate-level scalar `L²` membership on `U`. -/
noncomputable abbrev MemScalarL2 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MeasureTheory.MemLp u 2 (volumeMeasureOn U)

/-- Predicate-level vector `L²` membership on `U`. -/
noncomputable abbrev MemVectorL2 {d : ℕ} (U : Set (Vec d)) (f : Vec d → Vec d) : Prop :=
  MeasureTheory.MemLp f 2 (volumeMeasureOn U)

/-- Predicate-level block `L²` membership on `U`. -/
noncomputable abbrev MemBlockL2 {d : ℕ} (U : Set (Vec d)) (F : Vec d → BlockVec d) : Prop :=
  MeasureTheory.MemLp F 2 (volumeMeasureOn U)

/-- Predicate-level Hilbert-vector `L²` membership on `U`. -/
noncomputable abbrev MemHilbertVectorL2 {d : ℕ} (U : Set (Vec d))
    (f : Vec d → HilbertVec d) : Prop :=
  MeasureTheory.MemLp f 2 (volumeMeasureOn U)

/-- Predicate-level Hilbert-block `L²` membership on `U`. -/
noncomputable abbrev MemHilbertBlockL2 {d : ℕ} (U : Set (Vec d))
    (F : Vec d → HilbertBlockVec d) : Prop :=
  MeasureTheory.MemLp F 2 (volumeMeasureOn U)

/-- Reinterpret a plain vector field as a field valued in the Euclidean Hilbert
carrier. -/
def hilbertifyVecField {d : ℕ} (f : Vec d → Vec d) : Vec d → HilbertVec d :=
  fun x => HilbertVec.ofVec (f x)

/-- Reinterpret a plain doubled field as a field valued in the Euclidean
Hilbert carrier. -/
def hilbertifyBlockField {d : ℕ} (F : Vec d → BlockVec d) : Vec d → HilbertBlockVec d :=
  fun x => HilbertBlockVec.ofBlockVec (F x)

/-- Promote a scalar `MemLp` witness to the ambient `ScalarL2` type. -/
noncomputable def toScalarL2 {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MemScalarL2 U u) : ScalarL2 U :=
  hu.toLp u

/-- Promote a vector `MemLp` witness to the ambient `VectorL2` type. -/
noncomputable def toVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : VectorL2 U :=
  hf.toLp f

/-- Promote a block `MemLp` witness to the ambient `BlockL2` type. -/
noncomputable def toBlockL2 {d : ℕ} {U : Set (Vec d)} {F : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) : BlockL2 U :=
  hF.toLp F

/-- Extract `L²` control of the first block component from block `L²` control. -/
theorem memVectorL2_fst_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) :
    MemVectorL2 U (fun x => (F x).1) :=
  (ContinuousLinearMap.fst ℝ (Vec d) (Vec d)).comp_memLp' hF

/-- Extract `L²` control of the second block component from block `L²` control. -/
theorem memVectorL2_snd_of_memBlockL2 {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) :
    MemVectorL2 U (fun x => (F x).2) :=
  (ContinuousLinearMap.snd ℝ (Vec d) (Vec d)).comp_memLp' hF

/-- Reinterpret a plain block `L²` witness as a Hilbert-block `L²` witness. -/
theorem memHilbertBlockL2_hilbertifyBlockField {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) :
    MemHilbertBlockL2 U (hilbertifyBlockField F) :=
  let T : BlockVec d →L[ℝ] HilbertBlockVec d :=
    ((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap
  T.comp_memLp' hF

/-- Reinterpret a plain vector `L²` witness as a Hilbert-vector `L²` witness. -/
theorem memHilbertVectorL2_hilbertifyVecField {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MemHilbertVectorL2 U (hilbertifyVecField f) :=
  let T : Vec d →L[ℝ] HilbertVec d :=
    ((HilbertVec.continuousLinearEquivVec d).symm).toContinuousLinearMap
  T.comp_memLp' hf

/-- Promote a Hilbert-vector `MemLp` witness to the ambient `HilbertVectorL2`
type. -/
noncomputable def toHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → HilbertVec d}
    (hf : MemHilbertVectorL2 U f) : HilbertVectorL2 U :=
  hf.toLp f

/-- Promote a plain vector `MemLp` witness directly to the Hilbert-vector
ambient type. -/
noncomputable def toHilbertVectorL2OfVecField {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) : HilbertVectorL2 U :=
  toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hf)

/-- Promote a Hilbert-block `MemLp` witness to the ambient `HilbertBlockL2`
type. -/
noncomputable def toHilbertBlockL2 {d : ℕ} {U : Set (Vec d)} {F : Vec d → HilbertBlockVec d}
    (hF : MemHilbertBlockL2 U F) : HilbertBlockL2 U :=
  hF.toLp F

/-- Promote a plain block `MemLp` witness directly to the Hilbert-block ambient
type. -/
noncomputable def toHilbertBlockL2OfBlockField {d : ℕ} {U : Set (Vec d)}
    {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) : HilbertBlockL2 U :=
  toHilbertBlockL2 (memHilbertBlockL2_hilbertifyBlockField hF)

theorem coeFn_toScalarL2 {d : ℕ} {U : Set (Vec d)} {u : Vec d → ℝ}
    (hu : MemScalarL2 U u) :
    toScalarL2 hu =ᵐ[volumeMeasureOn U] u := by
  exact MeasureTheory.MemLp.coeFn_toLp hu

theorem coeFn_toVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    toVectorL2 hf =ᵐ[volumeMeasureOn U] f := by
  exact MeasureTheory.MemLp.coeFn_toLp hf

theorem coeFn_toBlockL2 {d : ℕ} {U : Set (Vec d)} {F : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) :
    toBlockL2 hF =ᵐ[volumeMeasureOn U] F := by
  exact MeasureTheory.MemLp.coeFn_toLp hF

theorem coeFn_toHilbertVectorL2 {d : ℕ} {U : Set (Vec d)} {f : Vec d → HilbertVec d}
    (hf : MemHilbertVectorL2 U f) :
    toHilbertVectorL2 hf =ᵐ[volumeMeasureOn U] f := by
  exact MeasureTheory.MemLp.coeFn_toLp hf

theorem coeFn_toHilbertVectorL2OfVecField {d : ℕ} {U : Set (Vec d)} {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    toHilbertVectorL2OfVecField hf =ᵐ[volumeMeasureOn U] hilbertifyVecField f := by
  exact coeFn_toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hf)

theorem coeFn_toHilbertBlockL2 {d : ℕ} {U : Set (Vec d)} {F : Vec d → HilbertBlockVec d}
    (hF : MemHilbertBlockL2 U F) :
    toHilbertBlockL2 hF =ᵐ[volumeMeasureOn U] F := by
  exact MeasureTheory.MemLp.coeFn_toLp hF

theorem coeFn_toHilbertBlockL2OfBlockField {d : ℕ} {U : Set (Vec d)} {F : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) :
    toHilbertBlockL2OfBlockField hF =ᵐ[volumeMeasureOn U] hilbertifyBlockField F := by
  exact coeFn_toHilbertBlockL2 (memHilbertBlockL2_hilbertifyBlockField hF)

theorem toScalarL2_eq_toScalarL2_iff {d : ℕ} {U : Set (Vec d)} {u v : Vec d → ℝ}
    (hu : MemScalarL2 U u) (hv : MemScalarL2 U v) :
    toScalarL2 hu = toScalarL2 hv ↔ u =ᵐ[volumeMeasureOn U] v := by
  exact MeasureTheory.MemLp.toLp_eq_toLp_iff hu hv

theorem toVectorL2_eq_toVectorL2_iff {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toVectorL2 hf = toVectorL2 hg ↔ f =ᵐ[volumeMeasureOn U] g := by
  exact MeasureTheory.MemLp.toLp_eq_toLp_iff hf hg

theorem toBlockL2_eq_toBlockL2_iff {d : ℕ} {U : Set (Vec d)} {F G : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) (hG : MemBlockL2 U G) :
    toBlockL2 hF = toBlockL2 hG ↔ F =ᵐ[volumeMeasureOn U] G := by
  exact MeasureTheory.MemLp.toLp_eq_toLp_iff hF hG

theorem toHilbertVectorL2_eq_toHilbertVectorL2_iff {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → HilbertVec d} (hf : MemHilbertVectorL2 U f) (hg : MemHilbertVectorL2 U g) :
    toHilbertVectorL2 hf = toHilbertVectorL2 hg ↔ f =ᵐ[volumeMeasureOn U] g := by
  exact MeasureTheory.MemLp.toLp_eq_toLp_iff hf hg

theorem toHilbertBlockL2_eq_toHilbertBlockL2_iff {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → HilbertBlockVec d} (hF : MemHilbertBlockL2 U F)
    (hG : MemHilbertBlockL2 U G) :
    toHilbertBlockL2 hF = toHilbertBlockL2 hG ↔ F =ᵐ[volumeMeasureOn U] G := by
  exact MeasureTheory.MemLp.toLp_eq_toLp_iff hF hG

section CarrierTransport

variable {d : ℕ} {U : Set (Vec d)}

/-- Continuous linear integration over a measurable subset, acting on scalar
`L²(U)` classes. -/
noncomputable def scalarL2SetIntegralCLM [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) : ScalarL2 U →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (ScalarL2 U)
    (MeasureTheory.indicatorConstLp (μ := volumeMeasureOn U) (p := (2 : ENNReal))
      hS (MeasureTheory.measure_ne_top (volumeMeasureOn U) S) (1 : ℝ))

/-- Continuous linear coordinate integration over a measurable subset, acting
on Hilbert-vector `L²(U)` classes. -/
noncomputable def hilbertVectorL2CoordSetIntegralCLM
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (i : Fin d) :
    HilbertVectorL2 U →L[ℝ] ℝ :=
  (scalarL2SetIntegralCLM (U := U) S hS).comp
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2
      (volumeMeasureOn U))

@[simp] theorem scalarL2SetIntegralCLM_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (f : ScalarL2 U) :
    scalarL2SetIntegralCLM (U := U) S hS f =
      ∫ x in S, f x ∂volumeMeasureOn U := by
  rw [scalarL2SetIntegralCLM, InnerProductSpace.toDual_apply_apply]
  exact MeasureTheory.L2.inner_indicatorConstLp_one
    (𝕜 := ℝ) hS (MeasureTheory.measure_ne_top (volumeMeasureOn U) S) f

@[simp] theorem hilbertVectorL2CoordSetIntegralCLM_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (S : Set (Vec d)) (hS : MeasurableSet S) (i : Fin d)
    (f : HilbertVectorL2 U) :
    hilbertVectorL2CoordSetIntegralCLM (U := U) S hS i f =
      ∫ x in S, f x i ∂volumeMeasureOn U := by
  rw [hilbertVectorL2CoordSetIntegralCLM]
  have hproj :
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2
        (volumeMeasureOn U) f)
        =ᵐ[volumeMeasureOn U] fun x => f x i :=
    ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i)
      (f := f)
  calc
    scalarL2SetIntegralCLM (U := U) S hS
        (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2
          (volumeMeasureOn U)) f)
      = ∫ x in S,
          ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL 2
            (volumeMeasureOn U) f) x ∂volumeMeasureOn U := by
          rw [scalarL2SetIntegralCLM_apply]
    _ = ∫ x in S, f x i ∂volumeMeasureOn U := by
          refine MeasureTheory.integral_congr_ae ?_
          exact hproj.filter_mono
            (MeasureTheory.ae_mono (MeasureTheory.Measure.restrict_le_self))

/-- Transport plain vector `L²` fields into the Hilbert-vector carrier by
applying `Vec -> HilbertVec` pointwise. -/
noncomputable def vectorL2ToHilbertVectorL2 : VectorL2 U →L[ℝ] HilbertVectorL2 U :=
  (HilbertVec.ofVecL d).compLpL 2 (volumeMeasureOn U)

/-- Transport Hilbert-vector `L²` fields back to the plain vector carrier by
applying `HilbertVec -> Vec` pointwise. -/
noncomputable def hilbertVectorL2ToVectorL2 : HilbertVectorL2 U →L[ℝ] VectorL2 U :=
  ((HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap).compLpL 2
    (volumeMeasureOn U)

theorem coeFn_vectorL2ToHilbertVectorL2 (f : VectorL2 U) :
    vectorL2ToHilbertVectorL2 (U := U) f =ᵐ[volumeMeasureOn U]
      fun x => HilbertVec.ofVec (f x) := by
  simpa [vectorL2ToHilbertVectorL2] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := HilbertVec.ofVecL d)
      (f := f))

theorem coeFn_hilbertVectorL2ToVectorL2 (f : HilbertVectorL2 U) :
    hilbertVectorL2ToVectorL2 (U := U) f =ᵐ[volumeMeasureOn U]
      fun x => (f x).toVec := by
  simpa [hilbertVectorL2ToVectorL2] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap)
      (f := f))

theorem vectorL2ToHilbertVectorL2_toVectorL2 {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    vectorL2ToHilbertVectorL2 (U := U) (toVectorL2 hf) = toHilbertVectorL2OfVecField hf := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_vectorL2ToHilbertVectorL2 (U := U) (f := toVectorL2 hf),
       coeFn_toVectorL2 hf,
       coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf]
    with x htransport hvec hhilbert
  rw [htransport, hvec, hhilbert]
  simp [hilbertifyVecField]

theorem hilbertVectorL2ToVectorL2_toHilbertVectorL2 {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    hilbertVectorL2ToVectorL2 (U := U) (toHilbertVectorL2OfVecField hf) = toVectorL2 hf := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := toHilbertVectorL2OfVecField hf),
       coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf,
       coeFn_toVectorL2 hf]
    with x htransport hhilbert hvec
  rw [htransport, hhilbert, hvec]
  simp [hilbertifyVecField]

theorem toHilbertVectorL2OfVecField_sub {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toHilbertVectorL2OfVecField (hf.sub hg) =
      toHilbertVectorL2OfVecField hf - toHilbertVectorL2OfVecField hg := by
  let hfH : MemHilbertVectorL2 U (hilbertifyVecField f) :=
    memHilbertVectorL2_hilbertifyVecField hf
  let hgH : MemHilbertVectorL2 U (hilbertifyVecField g) :=
    memHilbertVectorL2_hilbertifyVecField hg
  exact MeasureTheory.MemLp.toLp_sub hfH hgH

theorem toHilbertVectorL2OfVecField_add {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toHilbertVectorL2OfVecField (hf.add hg) =
      toHilbertVectorL2OfVecField hf + toHilbertVectorL2OfVecField hg := by
  let hfH : MemHilbertVectorL2 U (hilbertifyVecField f) :=
    memHilbertVectorL2_hilbertifyVecField hf
  let hgH : MemHilbertVectorL2 U (hilbertifyVecField g) :=
    memHilbertVectorL2_hilbertifyVecField hg
  exact MeasureTheory.MemLp.toLp_add hfH hgH

theorem hilbertVectorL2ToVectorL2_vectorL2ToHilbertVectorL2 (f : VectorL2 U) :
    hilbertVectorL2ToVectorL2 (U := U) (vectorL2ToHilbertVectorL2 (U := U) f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_hilbertVectorL2ToVectorL2 (U := U)
        (f := vectorL2ToHilbertVectorL2 (U := U) f),
       coeFn_vectorL2ToHilbertVectorL2 (U := U) (f := f)]
    with x hback hforward
  rw [hback, hforward]

theorem vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (f : HilbertVectorL2 U) :
    vectorL2ToHilbertVectorL2 (U := U) (hilbertVectorL2ToVectorL2 (U := U) f) = f := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_vectorL2ToHilbertVectorL2 (U := U)
        (f := hilbertVectorL2ToVectorL2 (U := U) f),
       coeFn_hilbertVectorL2ToVectorL2 (U := U) (f := f)]
    with x hforward hback
  rw [hforward, hback]

/-- Continuous linear identification between the plain vector carrier
`VectorL2 U` and the Hilbert-vector carrier `HilbertVectorL2 U`. -/
noncomputable def continuousLinearEquivVectorL2 : VectorL2 U ≃L[ℝ] HilbertVectorL2 U where
  toLinearEquiv :=
    { toFun := vectorL2ToHilbertVectorL2 (U := U)
      invFun := hilbertVectorL2ToVectorL2 (U := U)
      left_inv := hilbertVectorL2ToVectorL2_vectorL2ToHilbertVectorL2 (U := U)
      right_inv := vectorL2ToHilbertVectorL2_hilbertVectorL2ToVectorL2 (U := U)
      map_add' := (vectorL2ToHilbertVectorL2 (U := U)).map_add
      map_smul' := (vectorL2ToHilbertVectorL2 (U := U)).map_smul }
  continuous_toFun := (vectorL2ToHilbertVectorL2 (U := U)).continuous
  continuous_invFun := (hilbertVectorL2ToVectorL2 (U := U)).continuous

@[simp] theorem continuousLinearEquivVectorL2_apply (f : VectorL2 U) :
    continuousLinearEquivVectorL2 (U := U) f = vectorL2ToHilbertVectorL2 (U := U) f :=
  rfl

@[simp] theorem continuousLinearEquivVectorL2_symm_apply (f : HilbertVectorL2 U) :
    (continuousLinearEquivVectorL2 (U := U)).symm f = hilbertVectorL2ToVectorL2 (U := U) f :=
  rfl

theorem norm_hilbertVectorL2ToVectorL2_le :
    ‖hilbertVectorL2ToVectorL2 (d := d) (U := U)‖ ≤ 1 := by
  calc
    ‖hilbertVectorL2ToVectorL2 (d := d) (U := U)‖
        ≤ ‖(HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap‖ := by
          simpa [hilbertVectorL2ToVectorL2] using
            (ContinuousLinearMap.norm_compLpL_le
              (p := 2)
              (μ := volumeMeasureOn U)
              (L := (HilbertVec.continuousLinearEquivVec d).toContinuousLinearMap))
    _ ≤ 1 := HilbertVec.norm_continuousLinearEquivVec_le d

theorem norm_toVectorL2_le_toHilbertVectorL2 {f : Vec d → HilbertVec d}
    (hf : MemHilbertVectorL2 U f) :
    ‖hilbertVectorL2ToVectorL2 (U := U) (toHilbertVectorL2 hf)‖ ≤ ‖toHilbertVectorL2 hf‖ := by
  calc
    ‖hilbertVectorL2ToVectorL2 (U := U) (toHilbertVectorL2 hf)‖
        ≤ ‖hilbertVectorL2ToVectorL2 (d := d) (U := U)‖ * ‖toHilbertVectorL2 hf‖ := by
          exact (hilbertVectorL2ToVectorL2 (d := d) (U := U)).le_opNorm (toHilbertVectorL2 hf)
    _ ≤ 1 * ‖toHilbertVectorL2 hf‖ := by
          gcongr
          exact norm_hilbertVectorL2ToVectorL2_le (d := d) (U := U)
    _ = ‖toHilbertVectorL2 hf‖ := by ring

theorem norm_toVectorL2_le_toHilbertVectorL2OfVecField {f : Vec d → Vec d}
    (hf : MemVectorL2 U f) :
    ‖toVectorL2 hf‖ ≤ ‖toHilbertVectorL2OfVecField hf‖ := by
  calc
    ‖toVectorL2 hf‖
        = ‖hilbertVectorL2ToVectorL2 (U := U) (toHilbertVectorL2OfVecField hf)‖ := by
            rw [hilbertVectorL2ToVectorL2_toHilbertVectorL2 (U := U) (f := f) hf]
    _ ≤ ‖toHilbertVectorL2OfVecField hf‖ := by
          exact norm_toVectorL2_le_toHilbertVectorL2 (d := d) (U := U)
            (memHilbertVectorL2_hilbertifyVecField hf)

theorem norm_vectorL2ToHilbertVectorL2_le :
    ‖vectorL2ToHilbertVectorL2 (d := d) (U := U)‖ ≤ (d : ℝ) := by
  calc
    ‖vectorL2ToHilbertVectorL2 (d := d) (U := U)‖ ≤ ‖HilbertVec.ofVecL d‖ := by
      simpa [vectorL2ToHilbertVectorL2] using
        (ContinuousLinearMap.norm_compLpL_le
          (p := 2)
          (μ := volumeMeasureOn U)
          (L := HilbertVec.ofVecL d))
    _ ≤ (d : ℝ) := HilbertVec.norm_ofVecL_le d

theorem norm_toHilbertVectorL2OfVecField_le {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    ‖toHilbertVectorL2OfVecField hf‖ ≤ (d : ℝ) * ‖toVectorL2 hf‖ := by
  calc
    ‖toHilbertVectorL2OfVecField hf‖
        = ‖vectorL2ToHilbertVectorL2 (U := U) (toVectorL2 hf)‖ := by
            rw [vectorL2ToHilbertVectorL2_toVectorL2 (U := U) (f := f) hf]
    _ ≤ ‖vectorL2ToHilbertVectorL2 (d := d) (U := U)‖ * ‖toVectorL2 hf‖ := by
          exact (vectorL2ToHilbertVectorL2 (d := d) (U := U)).le_opNorm (toVectorL2 hf)
    _ ≤ (d : ℝ) * ‖toVectorL2 hf‖ := by
          gcongr
          exact norm_vectorL2ToHilbertVectorL2_le (d := d) (U := U)

theorem inner_toHilbertVectorL2OfVecField_eq_integral {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    inner ℝ (toHilbertVectorL2OfVecField hf) (toHilbertVectorL2OfVecField hg) =
      ∫ x in U, vecDot (f x) (g x) ∂MeasureTheory.volume := by
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards
      [coeFn_toHilbertVectorL2OfVecField (U := U) (f := f) hf,
       coeFn_toHilbertVectorL2OfVecField (U := U) (f := g) hg]
    with x hf' hg'
  rw [hf', hg']
  simp [hilbertifyVecField, HilbertVec.inner_def]

/-- Transport plain block `L²` fields into the Hilbert-block carrier by applying
`BlockVec -> HilbertBlockVec` pointwise. -/
noncomputable def blockL2ToHilbertBlockL2 : BlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap).compLpL 2
    (volumeMeasureOn U)

/-- Transport Hilbert-block `L²` fields back to the plain block carrier by
applying `HilbertBlockVec -> BlockVec` pointwise. -/
noncomputable def hilbertBlockL2ToBlockL2 : HilbertBlockL2 U →L[ℝ] BlockL2 U :=
  ((HilbertBlockVec.continuousLinearEquivBlockVec d).toContinuousLinearMap).compLpL 2
    (volumeMeasureOn U)

theorem coeFn_blockL2ToHilbertBlockL2 (F : BlockL2 U) :
    blockL2ToHilbertBlockL2 (U := U) F =ᵐ[volumeMeasureOn U]
      fun x => HilbertBlockVec.ofBlockVec (F x) := by
  simpa [blockL2ToHilbertBlockL2] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := ((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap)
      (f := F))

theorem coeFn_hilbertBlockL2ToBlockL2 (F : HilbertBlockL2 U) :
    hilbertBlockL2ToBlockL2 (U := U) F =ᵐ[volumeMeasureOn U]
      fun x => (F x).toBlockVec := by
  simpa [hilbertBlockL2ToBlockL2] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := (HilbertBlockVec.continuousLinearEquivBlockVec d).toContinuousLinearMap)
      (f := F))

theorem blockL2ToHilbertBlockL2_toBlockL2 {F : Vec d → BlockVec d} (hF : MemBlockL2 U F) :
    blockL2ToHilbertBlockL2 (U := U) (toBlockL2 hF) = toHilbertBlockL2OfBlockField hF := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_blockL2ToHilbertBlockL2 (U := U) (F := toBlockL2 hF),
       coeFn_toBlockL2 hF,
       coeFn_toHilbertBlockL2OfBlockField (U := U) (F := F) hF]
    with x htransport hblock hhilbert
  rw [htransport, hblock, hhilbert]
  simp [hilbertifyBlockField]

theorem hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField {F : Vec d → BlockVec d}
    (hF : MemBlockL2 U F) :
    hilbertBlockL2ToBlockL2 (U := U) (toHilbertBlockL2OfBlockField hF) = toBlockL2 hF := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_hilbertBlockL2ToBlockL2 (U := U) (F := toHilbertBlockL2OfBlockField hF),
       coeFn_toHilbertBlockL2OfBlockField (U := U) (F := F) hF,
       coeFn_toBlockL2 hF]
    with x htransport hhilbert hblock
  rw [htransport, hhilbert, hblock]
  simp [hilbertifyBlockField]

theorem hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2 (F : BlockL2 U) :
    hilbertBlockL2ToBlockL2 (U := U) (blockL2ToHilbertBlockL2 (U := U) F) = F := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_hilbertBlockL2ToBlockL2 (U := U)
        (F := blockL2ToHilbertBlockL2 (U := U) F),
       coeFn_blockL2ToHilbertBlockL2 (U := U) (F := F)]
    with x hback hforward
  rw [hback, hforward]
  simp

theorem blockL2ToHilbertBlockL2_hilbertBlockL2ToBlockL2 (F : HilbertBlockL2 U) :
    blockL2ToHilbertBlockL2 (U := U) (hilbertBlockL2ToBlockL2 (U := U) F) = F := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_blockL2ToHilbertBlockL2 (U := U)
        (F := hilbertBlockL2ToBlockL2 (U := U) F),
       coeFn_hilbertBlockL2ToBlockL2 (U := U) (F := F)]
    with x hforward hback
  rw [hforward, hback]
  simp

/-- Continuous linear identification between the plain block carrier `BlockL2 U`
and the Hilbert-block carrier `HilbertBlockL2 U`. -/
noncomputable def continuousLinearEquivBlockL2 : BlockL2 U ≃L[ℝ] HilbertBlockL2 U where
  toLinearEquiv :=
    { toFun := blockL2ToHilbertBlockL2 (U := U)
      invFun := hilbertBlockL2ToBlockL2 (U := U)
      left_inv := hilbertBlockL2ToBlockL2_blockL2ToHilbertBlockL2 (U := U)
      right_inv := blockL2ToHilbertBlockL2_hilbertBlockL2ToBlockL2 (U := U)
      map_add' := (blockL2ToHilbertBlockL2 (U := U)).map_add
      map_smul' := (blockL2ToHilbertBlockL2 (U := U)).map_smul }
  continuous_toFun := (blockL2ToHilbertBlockL2 (U := U)).continuous
  continuous_invFun := (hilbertBlockL2ToBlockL2 (U := U)).continuous

@[simp] theorem continuousLinearEquivBlockL2_apply (F : BlockL2 U) :
    continuousLinearEquivBlockL2 (U := U) F = blockL2ToHilbertBlockL2 (U := U) F :=
  rfl

@[simp] theorem continuousLinearEquivBlockL2_symm_apply (F : HilbertBlockL2 U) :
    (continuousLinearEquivBlockL2 (U := U)).symm F = hilbertBlockL2ToBlockL2 (U := U) F :=
  rfl

/-- Continuous linear projection from a Hilbert block `L²` field to its
potential component. -/
noncomputable def hilbertBlockVecPotentialCLM {d : ℕ} :
    HilbertBlockVec d →L[ℝ] HilbertVec d where
  toLinearMap :=
    PiLp.projₗ (2 : ENNReal) (𝕜 := ℝ) (β := fun _ : Fin 2 => HilbertVec d) 0
  cont :=
    PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => HilbertVec d) (0 : Fin 2)

/-- Continuous linear projection from a Hilbert block vector to its flux
component. -/
noncomputable def hilbertBlockVecFluxCLM {d : ℕ} :
    HilbertBlockVec d →L[ℝ] HilbertVec d where
  toLinearMap :=
    PiLp.projₗ (2 : ENNReal) (𝕜 := ℝ) (β := fun _ : Fin 2 => HilbertVec d) 1
  cont :=
    PiLp.continuous_apply (p := (2 : ENNReal))
      (β := fun _ : Fin 2 => HilbertVec d) (1 : Fin 2)

@[simp] theorem hilbertBlockVecPotentialCLM_apply {d : ℕ} (X : HilbertBlockVec d) :
    hilbertBlockVecPotentialCLM X = X.potential :=
  rfl

@[simp] theorem hilbertBlockVecFluxCLM_apply {d : ℕ} (X : HilbertBlockVec d) :
    hilbertBlockVecFluxCLM X = X.flux :=
  rfl

/-- Continuous linear projection from a Hilbert block `L²` field to its
potential component. -/
noncomputable def hilbertBlockL2PotentialCLM : HilbertBlockL2 U →L[ℝ] HilbertVectorL2 U :=
  (hilbertBlockVecPotentialCLM (d := d)).compLpL 2 (volumeMeasureOn U)

/-- Continuous linear projection from a Hilbert block `L²` field to its flux
component. -/
noncomputable def hilbertBlockL2FluxCLM : HilbertBlockL2 U →L[ℝ] HilbertVectorL2 U :=
  (hilbertBlockVecFluxCLM (d := d)).compLpL 2 (volumeMeasureOn U)

theorem coeFn_hilbertBlockL2PotentialCLM (F : HilbertBlockL2 U) :
    hilbertBlockL2PotentialCLM (U := U) F =ᵐ[volumeMeasureOn U]
      fun x => (F x).potential := by
  simpa [hilbertBlockL2PotentialCLM, HilbertBlockVec.potential] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := hilbertBlockVecPotentialCLM (d := d))
      (f := F))

theorem coeFn_hilbertBlockL2FluxCLM (F : HilbertBlockL2 U) :
    hilbertBlockL2FluxCLM (U := U) F =ᵐ[volumeMeasureOn U]
      fun x => (F x).flux := by
  simpa [hilbertBlockL2FluxCLM, HilbertBlockVec.flux] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := hilbertBlockVecFluxCLM (d := d))
      (f := F))

end CarrierTransport

section ConstantFields

variable {d : ℕ} {U : Set (Vec d)}
variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

/-- Constant Hilbert block fields as elements of the ambient space
`L²(U; \R^{2d})`. -/
noncomputable def hilbertBlockL2Const : HilbertBlockVec d →L[ℝ] HilbertBlockL2 U :=
  MeasureTheory.Lp.constL 2 (volumeMeasureOn U) ℝ

theorem coeFn_hilbertBlockL2Const (X : HilbertBlockVec d) :
    hilbertBlockL2Const (U := U) X =ᵐ[volumeMeasureOn U] Function.const _ X := by
  simpa [hilbertBlockL2Const] using
    (MeasureTheory.Lp.coeFn_const (p := 2) (μ := volumeMeasureOn U) (c := X))

/-- Constant algebraic block vectors embedded into the Hilbert-valued ambient
space `L²(U; \R^{2d})`. -/
noncomputable def blockVecToHilbertBlockL2Const : BlockVec d →L[ℝ] HilbertBlockL2 U :=
  (hilbertBlockL2Const (U := U)).comp
    (((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap)

theorem coeFn_blockVecToHilbertBlockL2Const (P : BlockVec d) :
    blockVecToHilbertBlockL2Const (U := U) P =ᵐ[volumeMeasureOn U]
      Function.const _ (HilbertBlockVec.ofBlockVec P) := by
  simpa [blockVecToHilbertBlockL2Const] using
    (coeFn_hilbertBlockL2Const (U := U) (X := HilbertBlockVec.ofBlockVec P))

end ConstantFields

section Operators

variable {d : ℕ} {U : Set (Vec d)}

/-- A fixed block matrix acts continuously on the ambient Hilbert space
`L²(U; \R^{2d})` by pointwise application. -/
noncomputable def hilbertBlockL2OperatorOfBlockMat (U : Set (Vec d)) (A : BlockMat d) :
    HilbertBlockL2 U →L[ℝ] HilbertBlockL2 U :=
  (HilbertBlockVec.applyBlockMat A).compLpL 2 (volumeMeasureOn U)

theorem coeFn_hilbertBlockL2OperatorOfBlockMat (A : BlockMat d) (F : HilbertBlockL2 U) :
    hilbertBlockL2OperatorOfBlockMat U A F =ᵐ[volumeMeasureOn U]
      fun x => HilbertBlockVec.applyBlockMat A (F x) := by
  simpa [hilbertBlockL2OperatorOfBlockMat] using
    (ContinuousLinearMap.coeFn_compLpL
      (p := 2)
      (μ := volumeMeasureOn U)
      (L := HilbertBlockVec.applyBlockMat A)
      (f := F))

variable [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]

theorem hilbertBlockL2OperatorOfBlockMat_apply_const (A : BlockMat d) (P : BlockVec d) :
    hilbertBlockL2OperatorOfBlockMat U A (blockVecToHilbertBlockL2Const (U := U) P) =
      blockVecToHilbertBlockL2Const (U := U) (blockMatVecMul A P) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_hilbertBlockL2OperatorOfBlockMat (U := U) (A := A)
        (F := blockVecToHilbertBlockL2Const (U := U) P),
       coeFn_blockVecToHilbertBlockL2Const (U := U) (P := P),
       coeFn_blockVecToHilbertBlockL2Const (U := U) (P := blockMatVecMul A P)]
    with x hOp hConst hTarget
  simp [hOp, hConst, hTarget, HilbertBlockVec.applyBlockMat_apply]

end Operators

end Homogenization
