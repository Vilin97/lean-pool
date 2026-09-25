/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.L2Ambient
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.MeanZero
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.ZeroTraceAverages
public import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidal
public import LeanPool.CoarseGraining.Homogenization.Geometry.ConvexDomain
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! # Potential Solenoidal L2 -/

@[expose] public section

namespace Homogenization

/-!
This file packages the note's spaces `\Lpot(U)`, `\Lpoto(U)`, `\Lsol(U)`,
`\Lsolo(U)` and their doubled block versions as actual closed subspaces of the
ambient `L²` spaces.

The structures remain abstract so downstream arguments can still be phrased in
terms of packaged closed subspaces. This file also provides canonical
constructors obtained by taking closures of the predicate-generated Sobolev
submodules that already exist in the current development.
-/

/-- Combine two vector fields into one block-valued field. -/
def blockField {d : ℕ} (f g : Vec d → Vec d) : Vec d → BlockVec d :=
  fun x => (f x, g x)

@[simp] theorem blockField_fst {d : ℕ} (f g : Vec d → Vec d) (x : Vec d) :
    (blockField f g x).1 = f x :=
  rfl

@[simp] theorem blockField_snd {d : ℕ} (f g : Vec d → Vec d) (x : Vec d) :
    (blockField f g x).2 = g x :=
  rfl

theorem memBlockL2_blockField {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    MemBlockL2 U (blockField f g) := by
  have hf' :
      MemBlockL2 U
        (fun x => (ContinuousLinearMap.inl ℝ (Vec d) (Vec d)) (f x)) := by
    simpa using!
      (ContinuousLinearMap.inl ℝ (Vec d) (Vec d)).comp_memLp' hf
  have hg' :
      MemBlockL2 U
        (fun x => (ContinuousLinearMap.inr ℝ (Vec d) (Vec d)) (g x)) := by
    simpa using!
      (ContinuousLinearMap.inr ℝ (Vec d) (Vec d)).comp_memLp' hg
  convert hf'.add hg' using 1
  funext x
  apply Prod.ext
  · ext i
    simp [blockField]
  · ext i
    simp [blockField]

/-- Promote a pair of vector `L²` witnesses to the block-valued ambient type. -/
noncomputable def toBlockL2OfComponents {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    BlockL2 U :=
  toBlockL2 (memBlockL2_blockField hf hg)

theorem coeFn_toBlockL2OfComponents {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toBlockL2OfComponents hf hg =ᵐ[volumeMeasureOn U] blockField f g :=
  coeFn_toBlockL2 (memBlockL2_blockField hf hg)

/-- Combine two vector fields into one Hilbert block-valued field. -/
def hilbertBlockField {d : ℕ} (f g : Vec d → Vec d) : Vec d → HilbertBlockVec d :=
  hilbertifyBlockField (blockField f g)

theorem memHilbertBlockL2_blockField {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    MemHilbertBlockL2 U (hilbertBlockField f g) := by
  let T : BlockVec d →L[ℝ] HilbertBlockVec d :=
    ((HilbertBlockVec.continuousLinearEquivBlockVec d).symm).toContinuousLinearMap
  simpa [hilbertBlockField, hilbertifyBlockField] using!
    T.comp_memLp' (memBlockL2_blockField hf hg)

/-- Promote a pair of vector `L²` witnesses to the Hilbert block-valued ambient
type. -/
noncomputable def toHilbertBlockL2OfComponents {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    HilbertBlockL2 U :=
  toHilbertBlockL2 (memHilbertBlockL2_blockField hf hg)

theorem coeFn_toHilbertBlockL2OfComponents {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toHilbertBlockL2OfComponents hf hg =ᵐ[volumeMeasureOn U] hilbertBlockField f g :=
  coeFn_toHilbertBlockL2 (memHilbertBlockL2_blockField hf hg)

theorem memScalarL2_coord_of_memVectorL2 {d : ℕ} {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (i : Fin d) :
    MemScalarL2 U (fun x => f x i) := by
  let pi : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [MemScalarL2, MemVectorL2, volumeMeasureOn] using! pi.comp_memLp' hf

theorem integrableOn_vecDot_of_memVectorL2 {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    MeasureTheory.IntegrableOn (fun x => vecDot (f x) (g x)) U := by
  have hsum :
      MeasureTheory.IntegrableOn (fun x => ∑ i, f x i * g x i) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integrable_finsetSum
        (μ := volumeMeasureOn U)
        Finset.univ
        (fun i _ =>
          (memScalarL2_coord_of_memVectorL2 hf i).integrable_mul
            (memScalarL2_coord_of_memVectorL2 hg i)))
  simpa [vecDot] using hsum

theorem IsSolenoidalZeroNormalTraceOn.isSolenoidalOn {d : ℕ} {U : Set (Vec d)}
    {g : Vec d → Vec d} (hg : IsSolenoidalZeroNormalTraceOn U g) :
    IsSolenoidalOn U g := by
  intro φ
  exact hg φ.toH1Function

theorem isSolenoidalOn_add_of_memVectorL2 {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf_mem : MemVectorL2 U f) (hg_mem : MemVectorL2 U g)
    (hf : IsSolenoidalOn U f) (hg : IsSolenoidalOn U g) :
    IsSolenoidalOn U (f + g) := by
  refine isSolenoidalOn_add hf hg ?_ ?_
  · intro φ
    exact integrableOn_vecDot_of_memVectorL2 hf_mem φ.toH1Function.grad_memVectorL2
  · intro φ
    exact integrableOn_vecDot_of_memVectorL2 hg_mem φ.toH1Function.grad_memVectorL2

theorem isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 {d : ℕ} {U : Set (Vec d)}
    {f g : Vec d → Vec d} (hf_mem : MemVectorL2 U f) (hg_mem : MemVectorL2 U g)
    (hf : IsSolenoidalZeroNormalTraceOn U f)
    (hg : IsSolenoidalZeroNormalTraceOn U g) :
    IsSolenoidalZeroNormalTraceOn U (f + g) := by
  refine isSolenoidalZeroNormalTraceOn_add hf hg ?_ ?_
  · intro φ
    exact integrableOn_vecDot_of_memVectorL2 hf_mem φ.grad_memVectorL2
  · intro φ
    exact integrableOn_vecDot_of_memVectorL2 hg_mem φ.grad_memVectorL2

namespace IsSolenoidalOn

/-- Constant vector fields are solenoidal against `H¹₀` tests on
Sobolev-regular domains. -/
theorem const_isSolenoidalOn_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (hU : IsSobolevRegularDomain U) (hvol : (MeasureTheory.volume U).toReal ≠ 0)
    (q : Vec d) :
    IsSolenoidalOn U (fun _ : Vec d => q) := by
  intro φ
  have havg :
      φ.toH1Function.averageGradient = 0 :=
    H10Function.averageGradient_eq_zero_of_isSobolevRegularDomain hU φ
  have hzero :
      (fun i => ∫ x in U, φ.toH1Function.grad x i ∂MeasureTheory.volume) = 0 :=
    H1Function.integral_eq_zero_of_averageGradient_eq_zero
      (u := φ.toH1Function) hvol havg
  calc
    ∫ x in U, vecDot q (φ.toH1Function.grad x) ∂MeasureTheory.volume =
        ∫ x in U, ∑ i, q i * φ.toH1Function.grad x i ∂MeasureTheory.volume := by
          simp [vecDot]
    _ = ∑ i, ∫ x in U, q i * φ.toH1Function.grad x i ∂MeasureTheory.volume := by
          rw [MeasureTheory.integral_finsetSum]
          intro i hi
          have hbase :
              MeasureTheory.Integrable
                (fun x => φ.toH1Function.grad x i) (MeasureTheory.volume.restrict U) :=
            (φ.toH1Function.grad_memL2 i).integrable (by norm_num : (1 : ENNReal) ≤ 2)
          simpa using hbase.const_mul (q i)
    _ = 0 := by
          refine Finset.sum_eq_zero ?_
          intro i hi
          have hzeroi : ∫ x in U, φ.toH1Function.grad x i ∂MeasureTheory.volume = 0 := by
            simpa using congrFun hzero i
          rw [MeasureTheory.integral_const_mul, hzeroi]
          simp

end IsSolenoidalOn

theorem toBlockL2OfComponents_add {d : ℕ} {U : Set (Vec d)}
    {f1 f2 g1 g2 : Vec d → Vec d}
    (hf1 : MemVectorL2 U f1) (hg1 : MemVectorL2 U g1)
    (hf2 : MemVectorL2 U f2) (hg2 : MemVectorL2 U g2) :
    toBlockL2OfComponents (hf1.add hf2) (hg1.add hg2) =
      toBlockL2OfComponents hf1 hg1 + toBlockL2OfComponents hf2 hg2 := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toBlockL2OfComponents hf1 hg1,
       coeFn_toBlockL2OfComponents hf2 hg2,
       coeFn_toBlockL2OfComponents (hf1.add hf2) (hg1.add hg2),
       MeasureTheory.Lp.coeFn_add (toBlockL2OfComponents hf1 hg1)
         (toBlockL2OfComponents hf2 hg2)]
    with x h1 h2 hsum hadd
  rw [hsum, hadd]
  simp [Pi.add_apply, h1, h2, blockField]

theorem toBlockL2OfComponents_smul {d : ℕ} {U : Set (Vec d)}
    (c : ℝ) {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    toBlockL2OfComponents (hf.const_smul c) (hg.const_smul c) =
      c • toBlockL2OfComponents hf hg := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toBlockL2OfComponents hf hg,
       coeFn_toBlockL2OfComponents (hf.const_smul c) (hg.const_smul c),
       MeasureTheory.Lp.coeFn_smul c (toBlockL2OfComponents hf hg)]
    with x h hsmul hLpSmul
  rw [hsmul, hLpSmul]
  simp [Pi.smul_apply, h, blockField]

/--
Packaged `L²` data for the note's potential and solenoidal spaces.

The four vector-valued closed subspaces model
`Lpot(U)`, `Lpoto(U)`, `Lsol(U)`, `Lsolo(U)`, while the two block-valued closed
subspaces model `Lpot(U) × Lsol(U)` and `Lpoto(U) × Lsolo(U)`.
-/
structure PotentialSolenoidalL2Data {d : ℕ} (U : Set (Vec d)) where
  /-- The closed `L²` subspace modeling `\Lpot(U)`. -/
  potential : ClosedSubmodule ℝ (VectorL2 U)
  /-- The closed `L²` subspace modeling `\Lpoto(U)`. -/
  potentialZeroTrace : ClosedSubmodule ℝ (VectorL2 U)
  /-- The closed `L²` subspace modeling `\Lsol(U)`. -/
  solenoidal : ClosedSubmodule ℝ (VectorL2 U)
  /-- The closed `L²` subspace modeling `\Lsolo(U)`. -/
  solenoidalZeroNormalTrace : ClosedSubmodule ℝ (VectorL2 U)
  /-- The closed block subspace modeling `\Lpot(U) × \Lsol(U)`. -/
  blockPotentialSolenoidal : ClosedSubmodule ℝ (BlockL2 U)
  /-- The closed block subspace modeling `\Lpoto(U) × \Lsolo(U)`. -/
  blockPotentialZeroTraceSolenoidalZeroNormalTrace : ClosedSubmodule ℝ (BlockL2 U)
  /-- Predicate-level potentials land in the packaged `L²` subspace. -/
  mem_potential :
    ∀ {f : Vec d → Vec d} (hf : MemVectorL2 U f),
      IsPotentialOn U f → toVectorL2 hf ∈ potential
  /-- Predicate-level zero-trace potentials land in the packaged `L²` subspace. -/
  mem_potentialZeroTrace :
    ∀ {f : Vec d → Vec d} (hf : MemVectorL2 U f),
      IsPotentialZeroTraceOn U f → toVectorL2 hf ∈ potentialZeroTrace
  /-- Predicate-level solenoidal fields land in the packaged `L²` subspace. -/
  mem_solenoidal :
    ∀ {g : Vec d → Vec d} (hg : MemVectorL2 U g),
      IsSolenoidalOn U g → toVectorL2 hg ∈ solenoidal
  /-- Predicate-level zero-normal-trace solenoidal fields land in the packaged
  `L²` subspace. -/
  mem_solenoidalZeroNormalTrace :
    ∀ {g : Vec d → Vec d} (hg : MemVectorL2 U g),
      IsSolenoidalZeroNormalTraceOn U g → toVectorL2 hg ∈ solenoidalZeroNormalTrace
  /-- Predicate-level block fields in `\Lpot(U) × \Lsol(U)` land in the
  packaged block `L²` subspace. -/
  mem_blockPotentialSolenoidal :
    ∀ {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g),
      IsPotentialOn U f →
      IsSolenoidalOn U g →
      toBlockL2OfComponents hf hg ∈ blockPotentialSolenoidal
  /-- Predicate-level block fields in `\Lpoto(U) × \Lsolo(U)` land in the
  packaged block `L²` subspace. -/
  mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace :
    ∀ {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g),
      IsPotentialZeroTraceOn U f →
      IsSolenoidalZeroNormalTraceOn U g →
      toBlockL2OfComponents hf hg ∈ blockPotentialZeroTraceSolenoidalZeroNormalTrace
  /-- The note's inclusion `\Lpoto(U) ⊆ \Lpot(U)`. -/
  potentialZeroTrace_le_potential : potentialZeroTrace ≤ potential
  /-- The note's inclusion `\Lsolo(U) ⊆ \Lsol(U)`. -/
  solenoidalZeroNormalTrace_le_solenoidal :
    solenoidalZeroNormalTrace ≤ solenoidal
  /-- The block-level inclusion
  `\Lpoto(U) × \Lsolo(U) ⊆ \Lpot(U) × \Lsol(U)`. -/
  blockPotentialZeroTraceSolenoidalZeroNormalTrace_le_blockPotentialSolenoidal :
    blockPotentialZeroTraceSolenoidalZeroNormalTrace ≤ blockPotentialSolenoidal

/--
Black-box Hilbert-valued `L²` packaging of the correction space
`\mathcal H(U) = \Lpoto(U) × \Lsolo(U)` used in the doubled `\mu` problem.

This is the exact closed subspace that later sits inside the ambient Hilbert
space `L²(U; \R^{2d})`.
-/
structure MuCorrectionSpaceData {d : ℕ} (U : Set (Vec d)) where
  /-- The closed Hilbert subspace modeling `\Lpoto(U) × \Lsolo(U)`. -/
  correctionSpace : ClosedSubmodule ℝ (HilbertBlockL2 U)
  /-- Predicate-level correction pairs land in the packaged Hilbert subspace. -/
  mem_correctionSpace :
    ∀ {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g),
      IsPotentialZeroTraceOn U f →
      IsSolenoidalZeroNormalTraceOn U g →
      toHilbertBlockL2OfComponents hf hg ∈ correctionSpace

namespace PotentialSolenoidalL2Data

variable {d : ℕ} {U : Set (Vec d)}

/-- Predicate-generated `L²` submodule for `\Lpot(U)`. -/
def potentialSubmodule (U : Set (Vec d)) : Submodule ℝ (VectorL2 U) where
  carrier := {F | ∃ f, ∃ hf : MemVectorL2 U f, toVectorL2 hf = F ∧ IsPotentialOn U f}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    exact ⟨0, h0, by simp [toVectorL2], isPotentialOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f, hf, rfl, hpot⟩
    rcases hY with ⟨g, hg, rfl, hpot'⟩
    exact
      ⟨f + g, hf.add hg,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_add hf hg,
        isPotentialOn_add hpot hpot'⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨f, hf, rfl, hpot⟩
    exact
      ⟨c • f, hf.const_smul c,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_const_smul c hf,
        isPotentialOn_smul hpot c⟩

/-- Predicate-generated `L²` submodule for `\Lpoto(U)`. -/
def potentialZeroTraceSubmodule (U : Set (Vec d)) : Submodule ℝ (VectorL2 U) where
  carrier := {F | ∃ f, ∃ hf : MemVectorL2 U f, toVectorL2 hf = F ∧ IsPotentialZeroTraceOn U f}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    exact
      ⟨0, h0, by simp [toVectorL2],
        isPotentialZeroTraceOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f, hf, rfl, hpot⟩
    rcases hY with ⟨g, hg, rfl, hpot'⟩
    exact
      ⟨f + g, hf.add hg,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_add hf hg,
        isPotentialZeroTraceOn_add hpot hpot'⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨f, hf, rfl, hpot⟩
    exact
      ⟨c • f, hf.const_smul c,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_const_smul c hf,
        isPotentialZeroTraceOn_smul hpot c⟩

/-- Predicate-generated `L²` submodule for `\Lsol(U)`. -/
def solenoidalSubmodule (U : Set (Vec d)) : Submodule ℝ (VectorL2 U) where
  carrier := {F | ∃ g, ∃ hg : MemVectorL2 U g, toVectorL2 hg = F ∧ IsSolenoidalOn U g}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    exact ⟨0, h0, by simp [toVectorL2], isSolenoidalOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f, hf, rfl, hsol⟩
    rcases hY with ⟨g, hg, rfl, hsol'⟩
    exact
      ⟨f + g, hf.add hg,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_add hf hg,
        isSolenoidalOn_add_of_memVectorL2 hf hg hsol hsol'⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨g, hg, rfl, hsol⟩
    exact
      ⟨c • g, hg.const_smul c,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_const_smul c hg,
        isSolenoidalOn_smul hsol c⟩

/-- Predicate-generated `L²` submodule for `\Lsolo(U)`. -/
def solenoidalZeroNormalTraceSubmodule (U : Set (Vec d)) : Submodule ℝ (VectorL2 U) where
  carrier := {F | ∃ g, ∃ hg : MemVectorL2 U g,
    toVectorL2 hg = F ∧ IsSolenoidalZeroNormalTraceOn U g}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    exact
      ⟨0, h0, by simp [toVectorL2],
        isSolenoidalZeroNormalTraceOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f, hf, rfl, hsol⟩
    rcases hY with ⟨g, hg, rfl, hsol'⟩
    exact
      ⟨f + g, hf.add hg,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_add hf hg,
        isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 hf hg hsol hsol'⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨g, hg, rfl, hsol⟩
    exact
      ⟨c • g, hg.const_smul c,
        by simpa [toVectorL2] using MeasureTheory.MemLp.toLp_const_smul c hg,
        isSolenoidalZeroNormalTraceOn_smul hsol c⟩

private noncomputable def gradientPairingVectorL2CLM {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : VectorL2 U →L[ℝ] ℝ :=
  ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U))
      (toHilbertVectorL2OfVecField u.grad_memVectorL2)).comp
    (continuousLinearEquivVectorL2 (U := U)).toContinuousLinearMap

private theorem gradientPairingVectorL2CLM_apply_toVectorL2
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2 U g) (u : H1Function U) :
    gradientPairingVectorL2CLM u (toVectorL2 hg) =
      ∫ x in U, vecDot (g x) (u.grad x) ∂MeasureTheory.volume := by
  calc
    gradientPairingVectorL2CLM u (toVectorL2 hg)
        = inner ℝ
            (toHilbertVectorL2OfVecField u.grad_memVectorL2)
            ((continuousLinearEquivVectorL2 (U := U)) (toVectorL2 hg)) := by
              simp [gradientPairingVectorL2CLM]
    _ = inner ℝ (toHilbertVectorL2OfVecField u.grad_memVectorL2)
          (toHilbertVectorL2OfVecField hg) := by
          rw [continuousLinearEquivVectorL2_apply, vectorL2ToHilbertVectorL2_toVectorL2]
    _ = ∫ x in U, vecDot (g x) (u.grad x) ∂MeasureTheory.volume := by
          rw [real_inner_comm]
          exact inner_toHilbertVectorL2OfVecField_eq_integral
            (U := U) hg u.grad_memVectorL2

theorem isSolenoidalOn_of_mem_closure_solenoidalSubmodule
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2 U g)
    (hmem : toVectorL2 hg ∈ (solenoidalSubmodule U).closure) :
    IsSolenoidalOn U g := by
  intro φ
  let ℓ : VectorL2 U →L[ℝ] ℝ := gradientPairingVectorL2CLM φ.toH1Function
  let K : ClosedSubmodule ℝ (VectorL2 U) := {
    toSubmodule := LinearMap.ker (ℓ : VectorL2 U →ₗ[ℝ] ℝ)
    isClosed' := ContinuousLinearMap.isClosed_ker ℓ
  }
  have hsub : solenoidalSubmodule U ≤ K := by
    intro X hX
    rcases hX with ⟨f, hf, rfl, hsol⟩
    change ℓ (toVectorL2 hf) = 0
    rw [gradientPairingVectorL2CLM_apply_toVectorL2 hf φ.toH1Function]
    exact hsol φ
  have hclosure :
      (solenoidalSubmodule U).closure ≤ K := by
    exact Submodule.closure_le.mpr hsub
  have hzero : ℓ (toVectorL2 hg) = 0 := by
    change toVectorL2 hg ∈ K
    exact hclosure hmem
  rw [gradientPairingVectorL2CLM_apply_toVectorL2 hg φ.toH1Function] at hzero
  exact hzero

theorem isSolenoidalZeroNormalTraceOn_of_mem_closure_solenoidalZeroNormalTraceSubmodule
    {d : ℕ} {U : Set (Vec d)} {g : Vec d → Vec d}
    (hg : MemVectorL2 U g)
    (hmem : toVectorL2 hg ∈ (solenoidalZeroNormalTraceSubmodule U).closure) :
    IsSolenoidalZeroNormalTraceOn U g := by
  intro u
  let ℓ : VectorL2 U →L[ℝ] ℝ := gradientPairingVectorL2CLM u
  let K : ClosedSubmodule ℝ (VectorL2 U) := {
    toSubmodule := LinearMap.ker (ℓ : VectorL2 U →ₗ[ℝ] ℝ)
    isClosed' := ContinuousLinearMap.isClosed_ker ℓ
  }
  have hsub : solenoidalZeroNormalTraceSubmodule U ≤ K := by
    intro X hX
    rcases hX with ⟨f, hf, rfl, hsol⟩
    change ℓ (toVectorL2 hf) = 0
    rw [gradientPairingVectorL2CLM_apply_toVectorL2 hf u]
    exact hsol u
  have hclosure :
      (solenoidalZeroNormalTraceSubmodule U).closure ≤ K := by
    exact Submodule.closure_le.mpr hsub
  have hzero : ℓ (toVectorL2 hg) = 0 := by
    change toVectorL2 hg ∈ K
    exact hclosure hmem
  rw [gradientPairingVectorL2CLM_apply_toVectorL2 hg u] at hzero
  exact hzero

/-- Predicate-generated block `L²` submodule for `\Lpot(U) × \Lsol(U)`. -/
def blockPotentialSolenoidalSubmodule (U : Set (Vec d)) : Submodule ℝ (BlockL2 U) where
  carrier := {F | ∃ f g, ∃ hf : MemVectorL2 U f, ∃ hg : MemVectorL2 U g,
    toBlockL2OfComponents hf hg = F ∧ IsPotentialOn U f ∧ IsSolenoidalOn U g}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    have hblock0 : toBlockL2OfComponents h0 h0 = (0 : BlockL2 U) := by
      apply MeasureTheory.Lp.ext
      filter_upwards
          [coeFn_toBlockL2OfComponents h0 h0,
           MeasureTheory.Lp.coeFn_zero (E := BlockVec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)]
        with x h hzero
      rw [h, hzero]
      simp [blockField]
    exact
      ⟨0, 0, h0, h0, hblock0, isPotentialOn_zero, isSolenoidalOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f1, g1, hf1, hg1, rfl, hpot1, hsol1⟩
    rcases hY with ⟨f2, g2, hf2, hg2, rfl, hpot2, hsol2⟩
    exact
      ⟨f1 + f2, g1 + g2, hf1.add hf2, hg1.add hg2,
        toBlockL2OfComponents_add hf1 hg1 hf2 hg2,
        isPotentialOn_add hpot1 hpot2,
        isSolenoidalOn_add_of_memVectorL2 hg1 hg2 hsol1 hsol2⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨f, g, hf, hg, rfl, hpot, hsol⟩
    exact
      ⟨c • f, c • g, hf.const_smul c, hg.const_smul c,
        toBlockL2OfComponents_smul c hf hg,
        isPotentialOn_smul hpot c,
        isSolenoidalOn_smul hsol c⟩

/-- Predicate-generated block `L²` submodule for `\Lpoto(U) × \Lsolo(U)`. -/
def blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule
    (U : Set (Vec d)) : Submodule ℝ (BlockL2 U) where
  carrier := {F | ∃ f g, ∃ hf : MemVectorL2 U f, ∃ hg : MemVectorL2 U g,
    toBlockL2OfComponents hf hg = F ∧
      IsPotentialZeroTraceOn U f ∧ IsSolenoidalZeroNormalTraceOn U g}
  zero_mem' := by
    let h0 : MemVectorL2 U (0 : Vec d → Vec d) := MeasureTheory.MemLp.zero
    have hblock0 : toBlockL2OfComponents h0 h0 = (0 : BlockL2 U) := by
      apply MeasureTheory.Lp.ext
      filter_upwards
          [coeFn_toBlockL2OfComponents h0 h0,
           MeasureTheory.Lp.coeFn_zero (E := BlockVec d) (p := (2 : ENNReal)) (μ := volumeMeasureOn U)]
        with x h hzero
      rw [h, hzero]
      simp [blockField]
    exact
      ⟨0, 0, h0, h0, hblock0, isPotentialZeroTraceOn_zero, isSolenoidalZeroNormalTraceOn_zero⟩
  add_mem' := by
    intro X Y hX hY
    rcases hX with ⟨f1, g1, hf1, hg1, rfl, hpot1, hsol1⟩
    rcases hY with ⟨f2, g2, hf2, hg2, rfl, hpot2, hsol2⟩
    exact
      ⟨f1 + f2, g1 + g2, hf1.add hf2, hg1.add hg2,
        toBlockL2OfComponents_add hf1 hg1 hf2 hg2,
        isPotentialZeroTraceOn_add hpot1 hpot2,
        isSolenoidalZeroNormalTraceOn_add_of_memVectorL2 hg1 hg2 hsol1 hsol2⟩
  smul_mem' := by
    intro c X hX
    rcases hX with ⟨f, g, hf, hg, rfl, hpot, hsol⟩
    exact
      ⟨c • f, c • g, hf.const_smul c, hg.const_smul c,
        toBlockL2OfComponents_smul c hf hg,
        isPotentialZeroTraceOn_smul hpot c,
        isSolenoidalZeroNormalTraceOn_smul hsol c⟩

theorem potentialZeroTraceSubmodule_le_potentialSubmodule :
    potentialZeroTraceSubmodule U ≤ potentialSubmodule U := by
  intro X hX
  rcases hX with ⟨f, hf, hEq, hpot⟩
  exact ⟨f, hf, hEq, hpot.isPotentialOn⟩

theorem solenoidalZeroNormalTraceSubmodule_le_solenoidalSubmodule :
    solenoidalZeroNormalTraceSubmodule U ≤ solenoidalSubmodule U := by
  intro X hX
  rcases hX with ⟨g, hg, hEq, hsol⟩
  exact ⟨g, hg, hEq, hsol.isSolenoidalOn⟩

theorem
    blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule_le_blockPotentialSolenoidalSubmodule :
    blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U ≤
      blockPotentialSolenoidalSubmodule U := by
  intro X hX
  rcases hX with ⟨f, g, hf, hg, hEq, hpot, hsol⟩
  exact ⟨f, g, hf, hg, hEq, hpot.isPotentialOn, hsol.isSolenoidalOn⟩

/-- Canonical packaged `L²` data obtained by closing the predicate-generated
Sobolev submodules. -/
noncomputable def ofSubmoduleClosures (U : Set (Vec d)) : PotentialSolenoidalL2Data U where
  potential := (potentialSubmodule U).closure
  potentialZeroTrace := (potentialZeroTraceSubmodule U).closure
  solenoidal := (solenoidalSubmodule U).closure
  solenoidalZeroNormalTrace := (solenoidalZeroNormalTraceSubmodule U).closure
  blockPotentialSolenoidal := (blockPotentialSolenoidalSubmodule U).closure
  blockPotentialZeroTraceSolenoidalZeroNormalTrace :=
    (blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U).closure
  mem_potential := by
    intro f hf hpot
    show toVectorL2 hf ∈ closure ((potentialSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
    exact subset_closure ⟨f, hf, rfl, hpot⟩
  mem_potentialZeroTrace := by
    intro f hf hpot
    show toVectorL2 hf ∈
      closure ((potentialZeroTraceSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
    exact subset_closure ⟨f, hf, rfl, hpot⟩
  mem_solenoidal := by
    intro g hg hsol
    show toVectorL2 hg ∈ closure ((solenoidalSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
    exact subset_closure ⟨g, hg, rfl, hsol⟩
  mem_solenoidalZeroNormalTrace := by
    intro g hg hsol
    show toVectorL2 hg ∈
      closure ((solenoidalZeroNormalTraceSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
    exact subset_closure ⟨g, hg, rfl, hsol⟩
  mem_blockPotentialSolenoidal := by
    intro f g hf hg hpot hsol
    show toBlockL2OfComponents hf hg ∈
      closure ((blockPotentialSolenoidalSubmodule U : Submodule ℝ (BlockL2 U)) : Set (BlockL2 U))
    exact subset_closure ⟨f, g, hf, hg, rfl, hpot, hsol⟩
  mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace := by
    intro f g hf hg hpot hsol
    show toBlockL2OfComponents hf hg ∈
      closure
        ((blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U :
          Submodule ℝ (BlockL2 U)) : Set (BlockL2 U))
    exact subset_closure ⟨f, g, hf, hg, rfl, hpot, hsol⟩
  potentialZeroTrace_le_potential := by
    exact Submodule.closure_le.mpr <| by
      intro X hX
      show X ∈ closure ((potentialSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
      exact subset_closure (potentialZeroTraceSubmodule_le_potentialSubmodule hX)
  solenoidalZeroNormalTrace_le_solenoidal := by
    exact Submodule.closure_le.mpr <| by
      intro X hX
      show X ∈ closure ((solenoidalSubmodule U : Submodule ℝ (VectorL2 U)) : Set (VectorL2 U))
      exact subset_closure (solenoidalZeroNormalTraceSubmodule_le_solenoidalSubmodule hX)
  blockPotentialZeroTraceSolenoidalZeroNormalTrace_le_blockPotentialSolenoidal := by
    exact Submodule.closure_le.mpr <| by
      intro X hX
      show X ∈ closure ((blockPotentialSolenoidalSubmodule U : Submodule ℝ (BlockL2 U)) : Set (BlockL2 U))
      exact subset_closure
        (blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule_le_blockPotentialSolenoidalSubmodule hX)

/--
Canonical packaged `L²` data attached to a Sobolev-regular domain.

The current implementation is obtained by closing the predicate-generated
Sobolev submodules; the domain regularity hypothesis gives downstream files a
stable constructor surface to consume.
-/
noncomputable def ofIsSobolevRegularDomain
    (_hU : IsSobolevRegularDomain U) : PotentialSolenoidalL2Data U :=
  ofSubmoduleClosures U

/-- Canonical packaged `L²` data attached to a bounded open convex domain. -/
noncomputable def ofIsOpenBoundedConvexDomain
    (hU : IsOpenBoundedConvexDomain U) : PotentialSolenoidalL2Data U :=
  ofIsSobolevRegularDomain hU.isSobolevRegularDomain

/-- Honest closed-range/realization hypothesis for the canonical zero-trace
potential space. This says that the closure used in `ofSubmoduleClosures` has
no extra abstract elements: every closed `L²` zero-trace potential class is
represented by the gradient of an actual `H¹₀` function. -/
def HasPotentialZeroTraceClosureRealization (U : Set (Vec d)) : Prop :=
  ∀ F : VectorL2 U,
    F ∈ (ofSubmoduleClosures U).potentialZeroTrace →
      IsPotentialZeroTraceOn U F

/-- Apply the closed-range/realization hypothesis for the canonical zero-trace
potential subspace. -/
theorem isPotentialZeroTraceOn_of_mem_potentialZeroTrace_ofSubmoduleClosures
    (hRealize : HasPotentialZeroTraceClosureRealization U)
    (F : VectorL2 U) (hF : F ∈ (ofSubmoduleClosures U).potentialZeroTrace) :
    IsPotentialZeroTraceOn U F :=
  hRealize F hF

/-- Membership in the canonical closed solenoidal subspace recovers the weak
solenoidal predicate on the represented vector field. -/
theorem isSolenoidalOn_of_mem_solenoidal_ofSubmoduleClosures
    (G : VectorL2 U) (hG : G ∈ (ofSubmoduleClosures U).solenoidal) :
    IsSolenoidalOn U G := by
  have hEq : toVectorL2 (MeasureTheory.Lp.memLp G) = G := by
    exact MeasureTheory.Lp.toLp_coeFn G (MeasureTheory.Lp.memLp G)
  have hG' : toVectorL2 (MeasureTheory.Lp.memLp G) ∈ (solenoidalSubmodule U).closure := by
    simpa [ofSubmoduleClosures, hEq] using hG
  simpa using
    isSolenoidalOn_of_mem_closure_solenoidalSubmodule (MeasureTheory.Lp.memLp G) hG'

/-- Membership in the canonical closed zero-normal-trace solenoidal subspace
recovers the corresponding weak predicate on the represented vector field. -/
theorem isSolenoidalZeroNormalTraceOn_of_mem_solenoidalZeroNormalTrace_ofSubmoduleClosures
    (G : VectorL2 U) (hG : G ∈ (ofSubmoduleClosures U).solenoidalZeroNormalTrace) :
    IsSolenoidalZeroNormalTraceOn U G := by
  have hEq : toVectorL2 (MeasureTheory.Lp.memLp G) = G := by
    exact MeasureTheory.Lp.toLp_coeFn G (MeasureTheory.Lp.memLp G)
  have hG' :
      toVectorL2 (MeasureTheory.Lp.memLp G) ∈ (solenoidalZeroNormalTraceSubmodule U).closure := by
    simpa [ofSubmoduleClosures, hEq] using hG
  simpa using
    isSolenoidalZeroNormalTraceOn_of_mem_closure_solenoidalZeroNormalTraceSubmodule
      (MeasureTheory.Lp.memLp G) hG'

private noncomputable def vectorPairingCLM
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) :
    VectorL2 U →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ (HilbertVectorL2 U) (toHilbertVectorL2OfVecField hg)).comp
    ((continuousLinearEquivVectorL2 (U := U)).toContinuousLinearMap)

private theorem vectorPairingCLM_apply_eq_integral
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (F : VectorL2 U) :
    vectorPairingCLM (U := U) hg F =
      ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume := by
  have hF :
      (continuousLinearEquivVectorL2 (U := U)) F =
        toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F) := by
    calc
      (continuousLinearEquivVectorL2 (U := U)) F = vectorL2ToHilbertVectorL2 (U := U) F := by
        rfl
      _ =
          vectorL2ToHilbertVectorL2 (U := U)
            (toVectorL2 (MeasureTheory.Lp.memLp F)) := by
              congr 1
              exact (MeasureTheory.Lp.toLp_coeFn F (MeasureTheory.Lp.memLp F)).symm
      _ = toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F) := by
        rfl
  calc
    vectorPairingCLM (U := U) hg F
        = inner ℝ
            (toHilbertVectorL2OfVecField hg)
            ((continuousLinearEquivVectorL2 (U := U)) F) := by
              simp [vectorPairingCLM]
    _ =
        inner ℝ
          (toHilbertVectorL2OfVecField hg)
          (toHilbertVectorL2OfVecField (MeasureTheory.Lp.memLp F)) := by
            rw [hF]
    _ = ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume := by
          exact inner_toHilbertVectorL2OfVecField_eq_integral
            (U := U) hg (MeasureTheory.Lp.memLp F)

private theorem scalarInner_eq_integral_local
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (f g : ScalarL2 U) :
    inner ℝ f g = ∫ x in U, f x * g x ∂MeasureTheory.volume := by
  rw [MeasureTheory.L2.inner_def]
  simp [mul_comm]

private noncomputable def oneScalarL2Local
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] : ScalarL2 U :=
  Homogenization.toScalarL2
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := (1 : ℝ)))

private theorem coeFn_oneScalarL2Local
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] :
    oneScalarL2Local (U := U) =ᵐ[volumeMeasureOn U] fun _ : Vec d => (1 : ℝ) :=
  Homogenization.coeFn_toScalarL2
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (p := (2 : ENNReal)) (c := (1 : ℝ)))

private noncomputable def scalarIntegralCLMLocal
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] : ScalarL2 U →L[ℝ] ℝ :=
  InnerProductSpace.toDual ℝ (ScalarL2 U) (oneScalarL2Local (U := U))

private theorem scalarIntegralCLMLocal_apply
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (s : ScalarL2 U) :
    scalarIntegralCLMLocal (U := U) s = ∫ x in U, s x ∂MeasureTheory.volume := by
  rw [scalarIntegralCLMLocal, InnerProductSpace.toDual_apply_apply, real_inner_comm,
    scalarInner_eq_integral_local]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [coeFn_oneScalarL2Local (U := U)] with x h1
  rw [h1]
  ring

/-- Members of the canonical closed zero-trace potential subspace are
orthogonal to every zero-normal-trace solenoidal test field. -/
theorem integral_vecDot_eq_zero_of_mem_potentialZeroTrace_ofSubmoduleClosures
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (F : VectorL2 U) (hF : F ∈ (ofSubmoduleClosures U).potentialZeroTrace)
    {g : Vec d → Vec d} (hg : MemVectorL2 U g)
    (hsol : IsSolenoidalZeroNormalTraceOn U g) :
    ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume = 0 := by
  let ℓ : VectorL2 U →L[ℝ] ℝ := vectorPairingCLM (U := U) hg
  have hKClosed : IsClosed ((LinearMap.ker ℓ.toLinearMap : Submodule ℝ (VectorL2 U)) :
      Set (VectorL2 U)) := by
    simpa [LinearMap.mem_ker] using!
      isClosed_singleton.preimage (ContinuousLinearMap.continuous ℓ)
  let K : ClosedSubmodule ℝ (VectorL2 U) := ⟨LinearMap.ker ℓ.toLinearMap, hKClosed⟩
  have hsub : potentialZeroTraceSubmodule U ≤ LinearMap.ker ℓ.toLinearMap := by
    intro X hX
    rcases hX with ⟨f, hf, rfl, hpot⟩
    change ℓ (toVectorL2 hf) = 0
    rcases hpot with ⟨u, hu⟩
    have hpair :
        ∫ x in U, vecDot (g x) ((toVectorL2 hf) x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_toVectorL2 hf] with x hx
      rw [hx]
    calc
      ℓ (toVectorL2 hf) = ∫ x in U, vecDot (g x) ((toVectorL2 hf) x) ∂MeasureTheory.volume :=
        vectorPairingCLM_apply_eq_integral (U := U) hg (toVectorL2 hf)
      _ = ∫ x in U, vecDot (g x) (f x) ∂MeasureTheory.volume := hpair
      _ = 0 := by
        simpa [hu] using hsol u.toH1Function
  have hclosure : (ofSubmoduleClosures U).potentialZeroTrace ≤ LinearMap.ker ℓ.toLinearMap := by
    exact (Submodule.closure_le (s := potentialZeroTraceSubmodule U) (t := K)).2 hsub
  have hkerF : F ∈ LinearMap.ker ℓ.toLinearMap := hclosure hF
  have hzero : ℓ F = 0 := by
    exact hkerF
  calc
    ∫ x in U, vecDot (g x) (F x) ∂MeasureTheory.volume = ℓ F := by
      symm
      exact vectorPairingCLM_apply_eq_integral (U := U) hg F
    _ = 0 := hzero

private noncomputable def coordIntegralCLM
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (i : Fin d) :
    VectorL2 U →L[ℝ] ℝ :=
  (scalarIntegralCLMLocal (U := U)).comp
    ((ContinuousLinearMap.proj i).compLpL 2 (volumeMeasureOn U))

private theorem coordIntegralCLM_apply_eq_integral
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (i : Fin d) (F : VectorL2 U) :
    coordIntegralCLM (U := U) i F =
      ∫ x in U, F x i ∂MeasureTheory.volume := by
  let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  calc
    coordIntegralCLM (U := U) i F
        = scalarIntegralCLMLocal (U := U) ((π.compLpL 2 (volumeMeasureOn U)) F) := by
            rfl
    _ = ∫ x in U, ((π.compLpL 2 (volumeMeasureOn U)) F) x ∂MeasureTheory.volume := by
          exact scalarIntegralCLMLocal_apply (U := U) ((π.compLpL 2 (volumeMeasureOn U)) F)
    _ = ∫ x in U, F x i ∂MeasureTheory.volume := by
          refine MeasureTheory.integral_congr_ae ?_
          simpa using!
            (ContinuousLinearMap.coeFn_compLpL
              (p := 2)
              (μ := volumeMeasureOn U)
              (L := π)
              (f := F))

/-- Members of the canonical closed zero-trace potential subspace have
componentwise zero averages. -/
theorem integral_coord_eq_zero_of_mem_potentialZeroTrace_ofSubmoduleClosures
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (F : VectorL2 U) (hF : F ∈ (ofSubmoduleClosures U).potentialZeroTrace)
    (i : Fin d) :
    ∫ x in U, F x i ∂MeasureTheory.volume = 0 := by
  let ℓ : VectorL2 U →L[ℝ] ℝ := coordIntegralCLM (U := U) i
  have hKClosed : IsClosed ((LinearMap.ker ℓ.toLinearMap : Submodule ℝ (VectorL2 U)) :
      Set (VectorL2 U)) := by
    simpa [LinearMap.mem_ker] using!
      isClosed_singleton.preimage (ContinuousLinearMap.continuous ℓ)
  let K : ClosedSubmodule ℝ (VectorL2 U) := ⟨LinearMap.ker ℓ.toLinearMap, hKClosed⟩
  have hsub : potentialZeroTraceSubmodule U ≤ LinearMap.ker ℓ.toLinearMap := by
    intro X hX
    rcases hX with ⟨f, hf, rfl, hpot⟩
    change ℓ (toVectorL2 hf) = 0
    have hzero := IsPotentialZeroTraceOn.integral_eq_zero hpot
    have hpair :
        ∫ x in U, ((toVectorL2 hf) x) i ∂MeasureTheory.volume =
          ∫ x in U, f x i ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [coeFn_toVectorL2 hf] with x hx
      rw [hx]
    calc
      ℓ (toVectorL2 hf) = ∫ x in U, ((toVectorL2 hf) x) i ∂MeasureTheory.volume :=
        coordIntegralCLM_apply_eq_integral (U := U) i (toVectorL2 hf)
      _ = ∫ x in U, f x i ∂MeasureTheory.volume := hpair
      _ = 0 := by
        simpa using congrFun hzero i
  have hclosure : (ofSubmoduleClosures U).potentialZeroTrace ≤ LinearMap.ker ℓ.toLinearMap := by
    exact (Submodule.closure_le (s := potentialZeroTraceSubmodule U) (t := K)).2 hsub
  have hkerF : F ∈ LinearMap.ker ℓ.toLinearMap := hclosure hF
  have hzero : ℓ F = 0 := by
    exact hkerF
  calc
    ∫ x in U, F x i ∂MeasureTheory.volume = ℓ F := by
      symm
      exact coordIntegralCLM_apply_eq_integral (U := U) i F
    _ = 0 := hzero

/-- Specialization of the ambient carrier transport to block fields built from
two vector components. -/
theorem hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents
    {f g : Vec d → Vec d} (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    hilbertBlockL2ToBlockL2 (U := U) (toHilbertBlockL2OfComponents hf hg) =
      toBlockL2OfComponents hf hg := by
  simpa [toBlockL2OfComponents, toHilbertBlockL2OfComponents] using!
    (Homogenization.hilbertBlockL2ToBlockL2_toHilbertBlockL2OfBlockField
      (U := U)
      (F := blockField f g)
      (memBlockL2_blockField hf hg))

/-- Transport the packaged block correction space
`\Lpoto(U) × \Lsolo(U) ⊆ BlockL²(U)` into the Hilbert-block ambient space used
by the doubled `μ` problem. -/
noncomputable def toMuCorrectionSpaceData (M : PotentialSolenoidalL2Data U) :
    MuCorrectionSpaceData U where
  correctionSpace :=
    M.blockPotentialZeroTraceSolenoidalZeroNormalTrace.comap
      (hilbertBlockL2ToBlockL2 (U := U))
  mem_correctionSpace := by
    intro f g hf hg hpot hsol
    show
      hilbertBlockL2ToBlockL2 (U := U) (toHilbertBlockL2OfComponents hf hg) ∈
        M.blockPotentialZeroTraceSolenoidalZeroNormalTrace
    rw [hilbertBlockL2ToBlockL2_toHilbertBlockL2OfComponents (U := U) hf hg]
    exact
      M.mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace hf hg hpot hsol

@[simp] theorem mem_toMuCorrectionSpaceData_iff (M : PotentialSolenoidalL2Data U)
    (X : HilbertBlockL2 U) :
    X ∈ M.toMuCorrectionSpaceData.correctionSpace ↔
      hilbertBlockL2ToBlockL2 (U := U) X ∈
        M.blockPotentialZeroTraceSolenoidalZeroNormalTrace :=
  Iff.rfl

end PotentialSolenoidalL2Data

namespace MuCorrectionSpaceData

variable {d : ℕ}

/-- Canonical Hilbert correction-space packaging obtained from the closed
predicate-generated Sobolev block submodule. -/
noncomputable def ofSubmoduleClosures (U : Set (Vec d)) : MuCorrectionSpaceData U :=
  (PotentialSolenoidalL2Data.ofSubmoduleClosures U).toMuCorrectionSpaceData

/--
Canonical Hilbert correction-space packaging attached to a Sobolev-regular
domain.
-/
noncomputable def ofIsSobolevRegularDomain {U : Set (Vec d)}
    (hU : IsSobolevRegularDomain U) : MuCorrectionSpaceData U :=
  (PotentialSolenoidalL2Data.ofIsSobolevRegularDomain (U := U) hU).toMuCorrectionSpaceData

/-- Canonical Hilbert correction-space packaging attached to a bounded open
convex domain. -/
noncomputable def ofIsOpenBoundedConvexDomain {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) : MuCorrectionSpaceData U :=
  (PotentialSolenoidalL2Data.ofIsOpenBoundedConvexDomain (U := U) hU).toMuCorrectionSpaceData

end MuCorrectionSpaceData

/-- Canonical packaged `L²` potential/solenoidal data on a Sobolev-regular
domain. -/
noncomputable def potentialSolenoidalL2Data_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    PotentialSolenoidalL2Data U :=
  PotentialSolenoidalL2Data.ofIsSobolevRegularDomain hU

/-- Canonical packaged Hilbert correction space on a Sobolev-regular domain. -/
noncomputable def muCorrectionSpaceData_of_isSobolevRegularDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MuCorrectionSpaceData U :=
  MuCorrectionSpaceData.ofIsSobolevRegularDomain hU

/-- Canonical packaged `L²` potential/solenoidal data on a bounded open convex
domain. -/
noncomputable def potentialSolenoidalL2Data_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    PotentialSolenoidalL2Data U :=
  PotentialSolenoidalL2Data.ofIsOpenBoundedConvexDomain hU

/-- Canonical packaged Hilbert correction space on a bounded open convex
domain. -/
noncomputable def muCorrectionSpaceData_of_isOpenBoundedConvexDomain
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U) :
    MuCorrectionSpaceData U :=
  MuCorrectionSpaceData.ofIsOpenBoundedConvexDomain hU

end Homogenization
