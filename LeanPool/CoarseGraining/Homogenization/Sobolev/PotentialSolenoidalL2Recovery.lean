/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.Hodge
import LeanPool.CoarseGraining.Homogenization.Sobolev.PotentialSolenoidalL2
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.Topology.Basic

/-! # Potential Solenoidal L2Recovery -/

namespace Homogenization

noncomputable section

/-!
This file adds a representative-level recovery interface for the abstract
Hilbert correction space `\Lpoto(U) × \Lsolo(U)`.

`MuCorrectionSpaceData` packages the correction space as a closed Hilbert
subspace of `L²(U; \R^{2d})`, which is the right level for minimization. The
results downstream that recover the note-faithful pointwise minimizers need a
converse interface: a way to choose actual potential/solenoidal vector fields
representing abstract elements of that closed subspace.
-/

section Representatives

variable {d : ℕ} {U : Set (Vec d)}

/-- A pointwise representative of an element of
`\Lpoto(U) × \Lsolo(U)`. -/
structure CorrectionFieldData (U : Set (Vec d)) where
  /-- The potential component. -/
  potential : Vec d → Vec d
  /-- The solenoidal component. -/
  flux : Vec d → Vec d
  /-- `L²` control of the potential component. -/
  potential_memL2 : MemVectorL2 U potential
  /-- `L²` control of the solenoidal component. -/
  flux_memL2 : MemVectorL2 U flux
  /-- Zero-trace potential witness. -/
  isPotentialZeroTrace : IsPotentialZeroTraceOn U potential
  /-- Zero-normal-trace solenoidal witness. -/
  isSolenoidalZeroNormalTrace : IsSolenoidalZeroNormalTraceOn U flux

namespace CorrectionFieldData

variable {d : ℕ} {U : Set (Vec d)}

theorem memScalarL2_coord_of_memVectorL2
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (i : Fin d) :
    MemScalarL2 U (fun x => f x i) := by
  let π : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  simpa [MemScalarL2, MemVectorL2, volumeMeasureOn] using! π.comp_memLp' hf

theorem integrableOn_coord_of_memVectorL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) (i : Fin d) :
    MeasureTheory.IntegrableOn (fun x => f x i) U := by
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    (memScalarL2_coord_of_memVectorL2 hf i).integrable (by norm_num : (1 : ENNReal) ≤ 2)

theorem integrableOn_vecDot_const_left_of_memVectorL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (p : Vec d) {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    MeasureTheory.IntegrableOn (fun x => vecDot p (f x)) U := by
  have hsum :
      MeasureTheory.IntegrableOn (fun x => ∑ i, p i * f x i) U := by
    simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
      (MeasureTheory.integrable_finsetSum
        (μ := volumeMeasureOn U)
        Finset.univ
        (fun i _ => (integrableOn_coord_of_memVectorL2 hf i).integrable.const_mul (p i)))
  simpa [vecDot] using hsum

theorem integrableOn_vecDot_of_memVectorL2
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
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

theorem integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (p : Vec d) {f : Vec d → Vec d}
    (hf : MemVectorL2 U f)
    (hzero : (fun i => ∫ x in U, f x i ∂MeasureTheory.volume) = 0) :
    ∫ x in U, vecDot p (f x) ∂MeasureTheory.volume = 0 := by
  rw [show (fun x => vecDot p (f x)) = fun x => ∑ i, p i * f x i by
    funext x
    simp [vecDot]]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_eq_zero ?_
    intro i hi
    rw [MeasureTheory.integral_const_mul]
    rw [congrFun hzero i]
    simp
  · intro i hi
    exact (integrableOn_coord_of_memVectorL2 hf i).integrable.const_mul (p i)

/-- The block-valued field represented by the two components. -/
def toBlockField (X : CorrectionFieldData U) : Vec d → BlockVec d :=
  blockField X.potential X.flux

@[simp] theorem toBlockField_fst (X : CorrectionFieldData U) (x : Vec d) :
    (X.toBlockField x).1 = X.potential x :=
  rfl

@[simp] theorem toBlockField_snd (X : CorrectionFieldData U) (x : Vec d) :
    (X.toBlockField x).2 = X.flux x :=
  rfl

/-- The represented block field is in `L²(U; \R^{2d})`. -/
theorem memBlockL2_toBlockField (X : CorrectionFieldData U) :
    MemBlockL2 U X.toBlockField :=
  memBlockL2_blockField X.potential_memL2 X.flux_memL2

/-- The represented correction field as an element of the plain block ambient
space. -/
noncomputable def toBlockL2 (X : CorrectionFieldData U) : BlockL2 U :=
  Homogenization.toBlockL2 X.memBlockL2_toBlockField

/-- The plain block `L²` representative agrees almost everywhere with the
pointwise block field. -/
theorem coeFn_toBlockL2 (X : CorrectionFieldData U) :
    X.toBlockL2 =ᵐ[volumeMeasureOn U] X.toBlockField :=
  Homogenization.coeFn_toBlockL2 X.memBlockL2_toBlockField

/-- The represented correction field as an element of the Hilbert ambient
space. -/
noncomputable def toHilbertBlockL2 (X : CorrectionFieldData U) : HilbertBlockL2 U :=
  toHilbertBlockL2OfComponents X.potential_memL2 X.flux_memL2

theorem coeFn_toHilbertBlockL2 (X : CorrectionFieldData U) :
    X.toHilbertBlockL2 =ᵐ[volumeMeasureOn U] hilbertBlockField X.potential X.flux :=
  coeFn_toHilbertBlockL2OfComponents X.potential_memL2 X.flux_memL2

theorem blockL2ToHilbertBlockL2_toBlockL2 (X : CorrectionFieldData U) :
    blockL2ToHilbertBlockL2 (U := U) X.toBlockL2 = X.toHilbertBlockL2 := by
  calc
    blockL2ToHilbertBlockL2 (U := U) X.toBlockL2
      = toHilbertBlockL2OfBlockField X.memBlockL2_toBlockField := by
          simpa [CorrectionFieldData.toBlockL2] using
            (Homogenization.blockL2ToHilbertBlockL2_toBlockL2
              (U := U)
              (F := X.toBlockField)
              X.memBlockL2_toBlockField)
    _ = X.toHilbertBlockL2 := by
          apply MeasureTheory.Lp.ext
          filter_upwards
              [coeFn_toHilbertBlockL2OfBlockField (U := U)
                (F := X.toBlockField)
                X.memBlockL2_toBlockField,
               X.coeFn_toHilbertBlockL2]
            with x hblock hhilbert
          rw [hblock, hhilbert]
          simp [CorrectionFieldData.toBlockField, hilbertifyBlockField, hilbertBlockField, blockField]

theorem integrableOn_pairing_affine
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (X : CorrectionFieldData U) (p q : Vec d) :
    MeasureTheory.IntegrableOn
      (fun x => vecDot (p + X.potential x) (q + X.flux x)) U := by
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hsum :
      MeasureTheory.IntegrableOn
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum123.integrable.add hpairInt.integrable
  have hEq :
      (fun x => vecDot (p + X.potential x) (q + X.flux x)) =
        (fun x =>
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x)) := by
    funext x
    simp [vecDot_add_left, vecDot_add_right, add_assoc]
    ring
  rw [hEq]
  exact hsum

theorem integral_pairing_affine_eq_volume_mul_vecDot_of_integral_eq_zero
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    (X : CorrectionFieldData U) (p q : Vec d)
    (hpotZero :
      (fun i => ∫ x in U, X.potential x i ∂MeasureTheory.volume) = 0)
    (hfluxZero :
      (fun i => ∫ x in U, X.flux x i ∂MeasureTheory.volume) = 0) :
    ∫ x in U, vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
      (MeasureTheory.volume U).toReal * vecDot p q := by
  rcases X.isPotentialZeroTrace with ⟨u, hu⟩
  have hpairZero :
      ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume = 0 := by
    simpa [hu, vecDot_comm] using X.isSolenoidalZeroNormalTrace u.toH1Function
  have hconstInt :
      MeasureTheory.IntegrableOn (fun _ : Vec d => vecDot p q) U := by
    simp [MeasureTheory.IntegrableOn]
  have hfluxInt :
      MeasureTheory.IntegrableOn (fun x => vecDot p (X.flux x)) U :=
    integrableOn_vecDot_const_left_of_memVectorL2 (U := U) p X.flux_memL2
  have hpotInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) q) U := by
    simpa [vecDot_comm] using
      (integrableOn_vecDot_const_left_of_memVectorL2 (U := U) q X.potential_memL2)
  have hpairInt :
      MeasureTheory.IntegrableOn (fun x => vecDot (X.potential x) (X.flux x)) U :=
    integrableOn_vecDot_of_memVectorL2 (U := U) X.potential_memL2 X.flux_memL2
  have hsum12 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x)) U := by
    simpa [MeasureTheory.IntegrableOn] using hconstInt.integrable.add hfluxInt.integrable
  have hsum123 :
      MeasureTheory.IntegrableOn
        (fun x => (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) U := by
    simpa [MeasureTheory.IntegrableOn] using! hsum12.integrable.add hpotInt.integrable
  have hfluxTerm :
      ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume = 0 :=
    integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) p X.flux_memL2 hfluxZero
  have hpotTerm :
      ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume = 0 := by
    rw [show (fun x => vecDot (X.potential x) q) = fun x => vecDot q (X.potential x) by
      funext x
      exact vecDot_comm _ _]
    exact integral_vecDot_const_left_eq_zero_of_integral_eq_zero_coords
      (U := U) q X.potential_memL2 hpotZero
  calc
    ∫ x in U, vecDot (p + X.potential x) (q + X.flux x) ∂MeasureTheory.volume =
        ∫ x in U,
          ((vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q) +
            vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
          congr 1
          funext x
          simp [vecDot_add_left, vecDot_add_right, add_assoc]
          ring
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum123 hpairInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) + vecDot (X.potential x) q
          ∂MeasureTheory.volume := by
            rw [hpairZero, add_zero]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume +
          ∫ x in U, vecDot (X.potential x) q ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hsum12 hpotInt]
    _ =
        ∫ x in U, (vecDot p q) + vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [hpotTerm, add_zero]
    _ =
        ∫ x in U, (vecDot p q) ∂MeasureTheory.volume +
          ∫ x in U, vecDot p (X.flux x) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_add hconstInt hfluxInt]
    _ = (MeasureTheory.volume U).toReal * vecDot p q := by
      rw [hfluxTerm, add_zero]
      rw [MeasureTheory.integral_const, smul_eq_mul]
      have hμ₁ :
          (MeasureTheory.volume.restrict U).real Set.univ = MeasureTheory.volume.real U := by
        exact MeasureTheory.measureReal_restrict_apply_univ (μ := MeasureTheory.volume) U
      have hμ₂ : MeasureTheory.volume.real U = (MeasureTheory.volume U).toReal := rfl
      rw [hμ₁, hμ₂]

end CorrectionFieldData

private noncomputable def blockFstCLM {d : ℕ} {U : Set (Vec d)} :
    BlockL2 U →L[ℝ] VectorL2 U :=
  (ContinuousLinearMap.fst ℝ (Vec d) (Vec d)).compLpL 2 (volumeMeasureOn U)

private noncomputable def blockSndCLM {d : ℕ} {U : Set (Vec d)} :
    BlockL2 U →L[ℝ] VectorL2 U :=
  (ContinuousLinearMap.snd ℝ (Vec d) (Vec d)).compLpL 2 (volumeMeasureOn U)

private theorem blockFstCLM_apply_toBlockL2OfComponents
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    blockFstCLM (U := U) (toBlockL2OfComponents hf hg) = toVectorL2 hf := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL
        (p := 2)
        (μ := volumeMeasureOn U)
        (L := ContinuousLinearMap.fst ℝ (Vec d) (Vec d))
        (f := toBlockL2OfComponents hf hg),
       coeFn_toBlockL2OfComponents hf hg,
       coeFn_toVectorL2 hf]
    with x hfst hblock hvec
  calc
    (blockFstCLM (U := U) (toBlockL2OfComponents hf hg)) x
        = (ContinuousLinearMap.fst ℝ (Vec d) (Vec d))
            ((toBlockL2OfComponents hf hg) x) := by
              simpa [blockFstCLM] using hfst
    _ = f x := by
          simp [hblock, blockField]
    _ = (toVectorL2 hf) x := by
          symm
          exact hvec

private theorem blockSndCLM_apply_toBlockL2OfComponents
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → Vec d}
    (hf : MemVectorL2 U f) (hg : MemVectorL2 U g) :
    blockSndCLM (U := U) (toBlockL2OfComponents hf hg) = toVectorL2 hg := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [ContinuousLinearMap.coeFn_compLpL
        (p := 2)
        (μ := volumeMeasureOn U)
        (L := ContinuousLinearMap.snd ℝ (Vec d) (Vec d))
        (f := toBlockL2OfComponents hf hg),
       coeFn_toBlockL2OfComponents hf hg,
       coeFn_toVectorL2 hg]
    with x hsnd hblock hvec
  calc
    (blockSndCLM (U := U) (toBlockL2OfComponents hf hg)) x
        = (ContinuousLinearMap.snd ℝ (Vec d) (Vec d))
            ((toBlockL2OfComponents hf hg) x) := by
              simpa [blockSndCLM] using hsnd
    _ = g x := by
          simp [hblock, blockField]
    _ = (toVectorL2 hg) x := by
          symm
          exact hvec

private theorem toBlockL2OfComponents_blockFstCLM_blockSndCLM
    {d : ℕ} {U : Set (Vec d)} (X : BlockL2 U) :
    toBlockL2OfComponents
        (MeasureTheory.Lp.memLp (blockFstCLM (U := U) X))
        (MeasureTheory.Lp.memLp (blockSndCLM (U := U) X)) =
      X := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toBlockL2OfComponents
        (MeasureTheory.Lp.memLp (blockFstCLM (U := U) X))
        (MeasureTheory.Lp.memLp (blockSndCLM (U := U) X)),
       ContinuousLinearMap.coeFn_compLpL
        (p := 2)
        (μ := volumeMeasureOn U)
        (L := ContinuousLinearMap.fst ℝ (Vec d) (Vec d))
        (f := X),
       ContinuousLinearMap.coeFn_compLpL
        (p := 2)
        (μ := volumeMeasureOn U)
        (L := ContinuousLinearMap.snd ℝ (Vec d) (Vec d))
        (f := X)]
    with x hblock hfst hsnd
  rw [hblock]
  ext i
  · simpa [blockField, blockFstCLM] using congrFun hfst i
  · simpa [blockField, blockSndCLM] using congrFun hsnd i

theorem PotentialSolenoidalL2Data.mem_potentialZeroTrace_of_mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_ofSubmoduleClosures
    {d : ℕ} {U : Set (Vec d)} (X : BlockL2 U)
    (hX :
      X ∈ (PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace) :
    blockFstCLM (U := U) X ∈ (PotentialSolenoidalL2Data.ofSubmoduleClosures U).potentialZeroTrace := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let K : ClosedSubmodule ℝ (BlockL2 U) := M.potentialZeroTrace.comap (blockFstCLM (U := U))
  have hsub :
      blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U ≤ K.toSubmodule := by
    intro Y hY
    rcases hY with ⟨f, g, hf, hg, rfl, hpot, _hsol⟩
    show blockFstCLM (U := U) (toBlockL2OfComponents hf hg) ∈ M.potentialZeroTrace
    rw [blockFstCLM_apply_toBlockL2OfComponents hf hg]
    simpa [M] using M.mem_potentialZeroTrace hf hpot
  have hclosure :
      (blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U).closure ≤ K.toSubmodule := by
    exact
      (Submodule.closure_le (s := blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U)
        (t := K)).2 hsub
  have hclosure' : M.blockPotentialZeroTraceSolenoidalZeroNormalTrace ≤ K := by
    intro Y hY
    exact hclosure (by simpa [M] using! hY)
  exact hclosure' hX

theorem PotentialSolenoidalL2Data.mem_solenoidalZeroNormalTrace_of_mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_ofSubmoduleClosures
    {d : ℕ} {U : Set (Vec d)} (X : BlockL2 U)
    (hX :
      X ∈ (PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace) :
    blockSndCLM (U := U) X ∈
      (PotentialSolenoidalL2Data.ofSubmoduleClosures U).solenoidalZeroNormalTrace := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let K : ClosedSubmodule ℝ (BlockL2 U) :=
    M.solenoidalZeroNormalTrace.comap (blockSndCLM (U := U))
  have hsub :
      blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U ≤ K.toSubmodule := by
    intro Y hY
    rcases hY with ⟨f, g, hf, hg, rfl, _hpot, hsol⟩
    show blockSndCLM (U := U) (toBlockL2OfComponents hf hg) ∈ M.solenoidalZeroNormalTrace
    rw [blockSndCLM_apply_toBlockL2OfComponents hf hg]
    simpa [M] using M.mem_solenoidalZeroNormalTrace hg hsol
  have hclosure :
      (blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U).closure ≤ K.toSubmodule := by
    exact
      (Submodule.closure_le (s := blockPotentialZeroTraceSolenoidalZeroNormalTraceSubmodule U)
        (t := K)).2 hsub
  have hclosure' : M.blockPotentialZeroTraceSolenoidalZeroNormalTrace ≤ K := by
    intro Y hY
    exact hclosure (by simpa [M] using! hY)
  exact hclosure' hX

/-- The pointwise block correction fields with exact zero-trace / zero-normal-trace
admissibility. This is the ambient vector space used to choose linear
representatives of the closed `L²` correction space. -/
def correctionFieldSubmodule {d : ℕ} (U : Set (Vec d)) :
    Submodule ℝ (Vec d → BlockVec d) where
  carrier := {F |
    MemBlockL2 U F ∧
      IsPotentialZeroTraceOn U (fun x => (F x).1) ∧
      IsSolenoidalZeroNormalTraceOn U (fun x => (F x).2)}
  zero_mem' := by
    refine ⟨MeasureTheory.MemLp.zero, ?_, ?_⟩
    · simpa using! (isPotentialZeroTraceOn_zero (U := U))
    · simpa using! (isSolenoidalZeroNormalTraceOn_zero (U := U))
  add_mem' := by
    intro F G hF hG
    rcases hF with ⟨hFmem, hFpot, hFsol⟩
    rcases hG with ⟨hGmem, hGpot, hGsol⟩
    refine ⟨hFmem.add hGmem, ?_, ?_⟩
    · simpa using! isPotentialZeroTraceOn_add hFpot hGpot
    · exact
        isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
          (memVectorL2_snd_of_memBlockL2 (U := U) hFmem)
          (memVectorL2_snd_of_memBlockL2 (U := U) hGmem)
          (by simpa using hFsol)
          (by simpa using hGsol)
  smul_mem' := by
    intro c F hF
    rcases hF with ⟨hFmem, hFpot, hFsol⟩
    refine ⟨hFmem.const_smul c, ?_, ?_⟩
    · simpa using! isPotentialZeroTraceOn_smul hFpot c
    · simpa using! isSolenoidalZeroNormalTraceOn_smul hFsol c

namespace correctionFieldSubmodule

theorem mem_potential_memVectorL2
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → BlockVec d}
    (hF : F ∈ correctionFieldSubmodule U) :
    MemVectorL2 U (fun x => (F x).1) :=
  memVectorL2_fst_of_memBlockL2 (U := U) hF.1

theorem mem_flux_memVectorL2
    {d : ℕ} {U : Set (Vec d)} {F : Vec d → BlockVec d}
    (hF : F ∈ correctionFieldSubmodule U) :
    MemVectorL2 U (fun x => (F x).2) :=
  memVectorL2_snd_of_memBlockL2 (U := U) hF.1

/-- Convert an exact pointwise block correction field into bundled
`CorrectionFieldData`. -/
noncomputable def toCorrectionFieldData
    {d : ℕ} {U : Set (Vec d)}
    (F : correctionFieldSubmodule U) : CorrectionFieldData U where
  potential := fun x => (F.1 x).1
  flux := fun x => (F.1 x).2
  potential_memL2 := mem_potential_memVectorL2 F.2
  flux_memL2 := mem_flux_memVectorL2 F.2
  isPotentialZeroTrace := F.2.2.1
  isSolenoidalZeroNormalTrace := F.2.2.2

@[simp] theorem toCorrectionFieldData_toBlockField
    {d : ℕ} {U : Set (Vec d)}
    (F : correctionFieldSubmodule U) :
    (toCorrectionFieldData F).toBlockField = F := by
  funext x
  ext i <;> rfl

end correctionFieldSubmodule

namespace PotentialSolenoidalL2RecoveryData

/-- The natural quotient map from exact pointwise correction fields to the
canonical closed block correction space. -/
noncomputable def correctionFieldSubmoduleToBlockSubmodule
    {d : ℕ} {U : Set (Vec d)} :
    correctionFieldSubmodule U →ₗ[ℝ]
      ((PotentialSolenoidalL2Data.ofSubmoduleClosures U).blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule) where
  toFun := fun F =>
    ⟨toBlockL2 F.2.1,
      by
        let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
        exact M.mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace
          (memVectorL2_fst_of_memBlockL2 (U := U) F.2.1)
          (memVectorL2_snd_of_memBlockL2 (U := U) F.2.1)
          F.2.2.1 F.2.2.2⟩
  map_add' := by
    intro F G
    apply Subtype.ext
    exact toBlockL2OfComponents_add
      (memVectorL2_fst_of_memBlockL2 (U := U) F.2.1)
      (memVectorL2_snd_of_memBlockL2 (U := U) F.2.1)
      (memVectorL2_fst_of_memBlockL2 (U := U) G.2.1)
      (memVectorL2_snd_of_memBlockL2 (U := U) G.2.1)
  map_smul' := by
    intro c F
    apply Subtype.ext
    exact toBlockL2OfComponents_smul c
      (memVectorL2_fst_of_memBlockL2 (U := U) F.2.1)
      (memVectorL2_snd_of_memBlockL2 (U := U) F.2.1)

theorem correctionFieldSubmoduleToBlockSubmodule_surjective_of_potentialZeroTraceClosureRealization
    {d : ℕ} {U : Set (Vec d)}
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U) :
    Function.Surjective (correctionFieldSubmoduleToBlockSubmodule (U := U)) := by
  intro X
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  have hpotMem : blockFstCLM (U := U) X ∈ M.potentialZeroTrace := by
    exact
      PotentialSolenoidalL2Data.mem_potentialZeroTrace_of_mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_ofSubmoduleClosures
        (U := U) X X.2
  have hsolMem : blockSndCLM (U := U) X ∈ M.solenoidalZeroNormalTrace := by
    exact
      PotentialSolenoidalL2Data.mem_solenoidalZeroNormalTrace_of_mem_blockPotentialZeroTraceSolenoidalZeroNormalTrace_ofSubmoduleClosures
        (U := U) X X.2
  let F : correctionFieldSubmodule U :=
    ⟨blockField (blockFstCLM (U := U) X) (blockSndCLM (U := U) X),
      memBlockL2_blockField
        (MeasureTheory.Lp.memLp (blockFstCLM (U := U) X))
        (MeasureTheory.Lp.memLp (blockSndCLM (U := U) X)),
      PotentialSolenoidalL2Data.isPotentialZeroTraceOn_of_mem_potentialZeroTrace_ofSubmoduleClosures
        (U := U) hRealize (blockFstCLM (U := U) X) hpotMem,
      PotentialSolenoidalL2Data.isSolenoidalZeroNormalTraceOn_of_mem_solenoidalZeroNormalTrace_ofSubmoduleClosures
        (U := U) (blockSndCLM (U := U) X) hsolMem⟩
  refine ⟨F, ?_⟩
  apply Subtype.ext
  simpa [F, correctionFieldSubmoduleToBlockSubmodule] using!
    toBlockL2OfComponents_blockFstCLM_blockSndCLM (U := U) X

end PotentialSolenoidalL2RecoveryData

theorem memVectorL2_const {d : ℕ} {U : Set (Vec d)}
    [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)] (p : Vec d) :
    MemVectorL2 U (fun _ : Vec d => p) := by
  simpa using
    (MeasureTheory.memLp_const (μ := volumeMeasureOn U) (c := p))

theorem IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2
    {d : ℕ} {U : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn U)]
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (hU : IsOpen U)
    (htest : ∀ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ U →
        ∫ x in U, vecDot (g x) (fun i => (fderiv ℝ ψ x) (basisVec i))
          ∂MeasureTheory.volume = 0) :
    IsSolenoidalOn U g := by
  intro φ
  let μ := volumeMeasureOn U
  let D : ℕ → Vec d → Vec d := fun n x i => (fderiv ℝ (φ.approx n) x) (basisVec i)
  have hD_coord : ∀ n i, MemScalarL2 U (fun x => D n x i) := by
    intro n i
    let ψ : H10Function U :=
      H10Function.ofContDiff hU (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
        (φ.approx_support_subset n)
    simpa [D, ψ, H10Function.ofContDiff, H1Function.ofContDiff] using ψ.toH1Function.gradMemL2 i
  have htest_approx :
      ∀ n,
        ∫ x in U, vecDot (g x) (D n x) ∂MeasureTheory.volume = 0 := by
    intro n
    exact htest (φ.approx n) (φ.approx_smooth n) (φ.approx_hasCompactSupport n)
      (φ.approx_support_subset n)
  have hcoord_tendsto :
      ∀ i : Fin d,
        Filter.Tendsto
          (fun n => ∫ x in U, g x i * D n x i ∂MeasureTheory.volume)
          Filter.atTop
          (nhds (∫ x in U, g x i * φ.toH1Function.grad x i ∂MeasureTheory.volume)) := by
    intro i
    let gi : Vec d → ℝ := fun x => g x i
    let diff : ℕ → Vec d → ℝ := fun n x => D n x i - φ.toH1Function.grad x i
    let Fn : ℕ → Vec d → ℝ := fun n x => gi x * D n x i
    let f : Vec d → ℝ := fun x => gi x * φ.toH1Function.grad x i
    have hgi_mem : MemScalarL2 U gi :=
      CorrectionFieldData.memScalarL2_coord_of_memVectorL2 hg i
    have hdiff_mem : ∀ n, MemScalarL2 U (diff n) := by
      intro n
      exact (hD_coord n i).sub (φ.toH1Function.gradMemL2 i)
    have hFn_int :
        ∀ᶠ n in Filter.atTop, MeasureTheory.Integrable (Fn n) μ := by
      refine Filter.Eventually.of_forall ?_
      intro n
      simpa [Fn, gi, D, μ, MeasureTheory.IntegrableOn] using!
        (hgi_mem.integrable_mul (hD_coord n i))
    have hf_int : MeasureTheory.Integrable f μ := by
      simpa [f, gi, μ, MeasureTheory.IntegrableOn] using!
        (hgi_mem.integrable_mul (φ.toH1Function.gradMemL2 i))
    have hL1_bound :
        ∀ n,
          MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ ≤
            MeasureTheory.eLpNorm gi 2 μ *
              MeasureTheory.eLpNorm (diff n) 2 μ := by
      intro n
      have hgi_meas : MeasureTheory.AEStronglyMeasurable gi μ := hgi_mem.aestronglyMeasurable
      have hdiff_meas :
          MeasureTheory.AEStronglyMeasurable (diff n) μ := (hdiff_mem n).aestronglyMeasurable
      simpa [gi, diff] using
        (MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
          (μ := μ) (p := (2 : ENNReal)) (q := (2 : ENNReal)) (r := (1 : ENNReal))
          hgi_meas hdiff_meas (fun a b : ℝ => a * b) 1
          (Filter.Eventually.of_forall fun x => by simp))
    have hconst_ne_top : MeasureTheory.eLpNorm gi 2 μ ≠ ⊤ := hgi_mem.eLpNorm_lt_top.ne
    have hL1 :
        Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hscaled :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm gi 2 μ * MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop
            (nhds (MeasureTheory.eLpNorm gi 2 μ * 0)) := by
        exact ENNReal.Tendsto.const_mul (φ.tendsto_approx_grad i) (Or.inr hconst_ne_top)
      have hscaled0 :
          Filter.Tendsto
            (fun n =>
              MeasureTheory.eLpNorm gi 2 μ * MeasureTheory.eLpNorm (diff n) 2 μ)
            Filter.atTop (nhds 0) := by
        simpa [mul_zero] using hscaled
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds hscaled0 (fun _ => zero_le) hL1_bound
    have hL1_diff :
        Filter.Tendsto
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - f x) 1 μ)
          Filter.atTop (nhds 0) := by
      have hEq :
          (fun n => MeasureTheory.eLpNorm (fun x => Fn n x - f x) 1 μ) =
            fun n => MeasureTheory.eLpNorm (fun x => gi x * diff n x) 1 μ := by
        funext n
        congr 1
        funext x
        simp [Fn, f, gi, diff]
        ring
      rw [hEq]
      exact hL1
    exact MeasureTheory.tendsto_integral_of_L1' (μ := μ) (f := f)
      hf_int.aestronglyMeasurable hFn_int hL1_diff
  have hIntegral_tendsto :
      Filter.Tendsto (fun n => ∫ x in U, vecDot (g x) (D n x) ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)) := by
    have hEq :
        (fun n => ∫ x in U, vecDot (g x) (D n x) ∂MeasureTheory.volume) =
          fun n => ∑ i, ∫ x in U, g x i * D n x i ∂MeasureTheory.volume := by
      funext n
      rw [show (fun x => vecDot (g x) (D n x)) = fun x => ∑ i, g x i * D n x i by
            funext x
            simp [vecDot, D]]
      rw [MeasureTheory.integral_finsetSum]
      intro i hi
      exact ((CorrectionFieldData.memScalarL2_coord_of_memVectorL2 hg i).integrable_mul
        (hD_coord n i))
    have hEq_limit :
        ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume =
          ∑ i, ∫ x in U, g x i * φ.toH1Function.grad x i ∂MeasureTheory.volume := by
      rw [show (fun x => vecDot (g x) (φ.toH1Function.grad x)) =
            fun x => ∑ i, g x i * φ.toH1Function.grad x i by
            funext x
            simp [vecDot]]
      rw [MeasureTheory.integral_finsetSum]
      intro i hi
      exact ((CorrectionFieldData.memScalarL2_coord_of_memVectorL2 hg i).integrable_mul
        (φ.toH1Function.gradMemL2 i))
    rw [hEq]
    have hsum :
        Filter.Tendsto
          (fun n => ∑ i, ∫ x in U, g x i * D n x i ∂MeasureTheory.volume)
          Filter.atTop
          (nhds (∑ i, ∫ x in U, g x i * φ.toH1Function.grad x i ∂MeasureTheory.volume)) := by
      simpa using
        tendsto_finsetSum Finset.univ (fun i _ => hcoord_tendsto i)
    rw [hEq_limit]
    exact hsum
  have hzero_tendsto :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂MeasureTheory.volume)) := by
    have hEq :
        (fun n => ∫ x in U, vecDot (g x) (D n x) ∂MeasureTheory.volume) = fun _ => (0 : ℝ) := by
      funext n
      exact htest_approx n
    simpa [hEq] using hIntegral_tendsto
  exact tendsto_nhds_unique hzero_tendsto tendsto_const_nhds

namespace IsSolenoidalOn

theorem restrict_of_isOpen_of_memVectorL2
    {d : ℕ} {U V : Set (Vec d)} [MeasureTheory.IsFiniteMeasure (volumeMeasureOn V)]
    {g : Vec d → Vec d} (hg : IsSolenoidalOn U g) (hU : IsOpen U) (hV : IsOpen V)
    (hVU : V ⊆ U) (hgV : MemVectorL2 V g) :
    IsSolenoidalOn V g := by
  apply IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hgV hV
  intro ψ hψ_smooth hψ_compact hψ_sub
  have hzeroV :
      ∀ x : Vec d, x ∉ V →
        vecDot (g x) (fun i => (fderiv ℝ ψ x) (basisVec i)) = 0 := by
    intro x hx
    have hx_notin : x ∉ tsupport ψ := fun hx' => hx (hψ_sub hx')
    have hψ_eq : ψ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := ψ)).isOpen_compl.eventually_mem hx_notin |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    rw [Filter.EventuallyEq.fderiv_eq hψ_eq]
    simp [vecDot]
  have hzeroU :
      ∀ x : Vec d, x ∉ U →
        vecDot (g x) (fun i => (fderiv ℝ ψ x) (basisVec i)) = 0 := by
    intro x hx
    exact hzeroV x (fun hxV => hx (hVU hxV))
  have hset :
      ∫ x in V, vecDot (g x) (fun i => (fderiv ℝ ψ x) (basisVec i)) ∂MeasureTheory.volume =
        ∫ x in U, vecDot (g x) (fun i => (fderiv ℝ ψ x) (basisVec i)) ∂MeasureTheory.volume := by
    rw [MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroV,
      MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzeroU]
  rw [hset]
  exact hg.test_of_contDiff hU hψ_smooth hψ_compact (hψ_sub.trans hVU)

end IsSolenoidalOn

/--
Recovery data for the abstract Hilbert correction space
`\Lpoto(U) × \Lsolo(U)`.

This extends `MuCorrectionSpaceData` by choosing pointwise representatives of
all abstract correction fields, together with the linearity and realization
statements needed later for minimizer recovery.
-/
structure MuCorrectionSpaceRecoveryData (U : Set (Vec d)) extends MuCorrectionSpaceData U where
  /-- A pointwise representative of each abstract correction field. -/
  repr : correctionSpace.toSubmodule → CorrectionFieldData U
  /-- Additivity of the chosen representatives at the level of block fields. -/
  repr_add :
    ∀ X Y : correctionSpace.toSubmodule,
      (repr (X + Y)).toBlockField = (repr X).toBlockField + (repr Y).toBlockField
  /-- Homogeneity of the chosen representatives at the level of block fields. -/
  repr_smul :
    ∀ (c : ℝ) (X : correctionSpace.toSubmodule),
      (repr (c • X)).toBlockField = c • (repr X).toBlockField
  /-- The chosen representative realizes the abstract correction field in the
  Hilbert ambient space. -/
  repr_eq :
    ∀ X : correctionSpace.toSubmodule, (repr X).toHilbertBlockL2 = X

/--
Representative-level recovery data on the plain block ambient space
`BlockL²(U)`, anchored to the packaged block correction space
`\Lpoto(U) × \Lsolo(U)`.
-/
structure PotentialSolenoidalL2RecoveryData (U : Set (Vec d))
    extends PotentialSolenoidalL2Data U where
  /-- A pointwise representative of each block correction field. -/
  repr :
    blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule →
      CorrectionFieldData U
  /-- Additivity of the chosen representatives at the level of block fields. -/
  repr_add :
    ∀ X Y : blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule,
      (repr (X + Y)).toBlockField = (repr X).toBlockField + (repr Y).toBlockField
  /-- Homogeneity of the chosen representatives at the level of block fields. -/
  repr_smul :
    ∀ (c : ℝ) (X : blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule),
      (repr (c • X)).toBlockField = c • (repr X).toBlockField
  /-- The chosen representative realizes the abstract block correction field in
  `BlockL²(U)`. -/
  repr_eq :
    ∀ X : blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule,
      (repr X).toBlockL2 = X

namespace PotentialSolenoidalL2RecoveryData

variable {d : ℕ} {U : Set (Vec d)}

/-- View a Hilbert-block correction field in the transported correction space as
the corresponding element of the original block correction subspace. -/
noncomputable def toBlockCorrectionSubmodule (M : PotentialSolenoidalL2RecoveryData U) :
    M.toMuCorrectionSpaceData.correctionSpace.toSubmodule →
      M.blockPotentialZeroTraceSolenoidalZeroNormalTrace.toSubmodule :=
  fun X => ⟨hilbertBlockL2ToBlockL2 (U := U) X, X.2⟩

theorem toBlockCorrectionSubmodule_add (M : PotentialSolenoidalL2RecoveryData U)
    (X Y : M.toMuCorrectionSpaceData.correctionSpace.toSubmodule) :
    M.toBlockCorrectionSubmodule (X + Y) =
      M.toBlockCorrectionSubmodule X + M.toBlockCorrectionSubmodule Y := by
  apply Subtype.ext
  change
    hilbertBlockL2ToBlockL2 (U := U) (X + Y) =
      hilbertBlockL2ToBlockL2 (U := U) X + hilbertBlockL2ToBlockL2 (U := U) Y
  exact (hilbertBlockL2ToBlockL2 (U := U)).map_add X Y

theorem toBlockCorrectionSubmodule_smul (M : PotentialSolenoidalL2RecoveryData U)
    (c : ℝ) (X : M.toMuCorrectionSpaceData.correctionSpace.toSubmodule) :
    M.toBlockCorrectionSubmodule (c • X) = c • M.toBlockCorrectionSubmodule X := by
  apply Subtype.ext
  change
    hilbertBlockL2ToBlockL2 (U := U) (c • X) =
      c • hilbertBlockL2ToBlockL2 (U := U) X
  exact (hilbertBlockL2ToBlockL2 (U := U)).map_smul c X

/-- Lift block-side recovery data to the Hilbert correction space used by the
doubled `μ` minimization problem. -/
noncomputable def toMuCorrectionSpaceRecoveryData (M : PotentialSolenoidalL2RecoveryData U) :
    MuCorrectionSpaceRecoveryData U where
  toMuCorrectionSpaceData := M.toPotentialSolenoidalL2Data.toMuCorrectionSpaceData
  repr := fun X => M.repr (M.toBlockCorrectionSubmodule X)
  repr_add := by
    intro X Y
    simpa [PotentialSolenoidalL2RecoveryData.toBlockCorrectionSubmodule_add] using
      M.repr_add (M.toBlockCorrectionSubmodule X) (M.toBlockCorrectionSubmodule Y)
  repr_smul := by
    intro c X
    simpa [PotentialSolenoidalL2RecoveryData.toBlockCorrectionSubmodule_smul] using
      M.repr_smul c (M.toBlockCorrectionSubmodule X)
  repr_eq := by
    intro X
    calc
      (M.repr (M.toBlockCorrectionSubmodule X)).toHilbertBlockL2
        = blockL2ToHilbertBlockL2 (U := U)
            ((M.repr (M.toBlockCorrectionSubmodule X)).toBlockL2) := by
              symm
              exact CorrectionFieldData.blockL2ToHilbertBlockL2_toBlockL2
                (M.repr (M.toBlockCorrectionSubmodule X))
      _ = blockL2ToHilbertBlockL2 (U := U) (M.toBlockCorrectionSubmodule X) := by
            rw [M.repr_eq (M.toBlockCorrectionSubmodule X)]
      _ = X := by
            change
              blockL2ToHilbertBlockL2 (U := U)
                (hilbertBlockL2ToBlockL2 (U := U) (X : HilbertBlockL2 U)) =
                  (X : HilbertBlockL2 U)
            exact
              (Homogenization.blockL2ToHilbertBlockL2_hilbertBlockL2ToBlockL2
                (U := U)
                (X : HilbertBlockL2 U))

end PotentialSolenoidalL2RecoveryData

/-- Canonical representative-level recovery data obtained from the closed
predicate-generated block correction space, assuming the zero-trace potential
closure has honest `H¹₀` representatives. -/
noncomputable def
    potentialSolenoidalL2RecoveryData_ofSubmoduleClosures_of_potentialZeroTraceClosureRealization
    {d : ℕ} {U : Set (Vec d)}
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U) :
    PotentialSolenoidalL2RecoveryData U := by
  let M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U
  let L := PotentialSolenoidalL2RecoveryData.correctionFieldSubmoduleToBlockSubmodule (U := U)
  classical
  let hgExists :=
    L.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.2
        (PotentialSolenoidalL2RecoveryData.correctionFieldSubmoduleToBlockSubmodule_surjective_of_potentialZeroTraceClosureRealization
          (U := U) hRealize))
  let g := Classical.choose hgExists
  let hg := Classical.choose_spec hgExists
  refine
    { toPotentialSolenoidalL2Data := M
      repr := fun X => correctionFieldSubmodule.toCorrectionFieldData (g X)
      repr_add := ?_
      repr_smul := ?_
      repr_eq := ?_ }
  · intro X Y
    calc
      (correctionFieldSubmodule.toCorrectionFieldData (g (X + Y))).toBlockField
          = g (X + Y) :=
            correctionFieldSubmodule.toCorrectionFieldData_toBlockField (g (X + Y))
      _ = g X + g Y := congrArg Subtype.val (map_add g X Y)
      _ = (correctionFieldSubmodule.toCorrectionFieldData (g X)).toBlockField +
            (correctionFieldSubmodule.toCorrectionFieldData (g Y)).toBlockField := by
            rw [correctionFieldSubmodule.toCorrectionFieldData_toBlockField,
              correctionFieldSubmodule.toCorrectionFieldData_toBlockField]
  · intro c X
    calc
      (correctionFieldSubmodule.toCorrectionFieldData (g (c • X))).toBlockField
          = g (c • X) :=
            correctionFieldSubmodule.toCorrectionFieldData_toBlockField (g (c • X))
      _ = c • g X := congrArg Subtype.val (map_smul g c X)
      _ = c • (correctionFieldSubmodule.toCorrectionFieldData (g X)).toBlockField := by
            rw [correctionFieldSubmodule.toCorrectionFieldData_toBlockField]
  · intro X
    have hX : L (g X) = X := by
      simpa using congrArg (fun T => T X) hg
    apply Subtype.ext
    simpa [L,
      PotentialSolenoidalL2RecoveryData.correctionFieldSubmoduleToBlockSubmodule,
      correctionFieldSubmodule.toCorrectionFieldData_toBlockField]
      using! congrArg Subtype.val hX

end Representatives

end

end Homogenization
