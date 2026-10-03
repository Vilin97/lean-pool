/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.ReflectionParentPotential

/-! # Reflection Parent Orthogonality -/

@[expose] public section

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

variable {d : ℕ} {m : ℤ}

/-- Fold a parent-cube vector field back to the original cube by summing the
signed pullbacks from all reflection cells. This is the test field whose
solenoidal zero-normal property is the concrete Hodge-orthogonality task left
by the reflection argument. -/
def cubeFaceReflectionFoldedParentVectorField {d : ℕ}
    (Q : TriadicCube d) (g : Vec d → Vec d) : Vec d → Vec d :=
  fun y =>
    ∑ choice : Fin d → Fin 3,
      cubeFaceReflectionCellFoldLinear choice
        (g (cubeFaceReflectionCellFoldMap Q choice y))

private theorem preimage_cubeFaceReflectionCellFoldMap_cellCube {d : ℕ}
    (Q : TriadicCube d) (choice : Fin d → Fin 3) :
    cubeFaceReflectionCellFoldMap Q choice ⁻¹'
        openCubeSet (cubeFaceReflectionCellCube Q choice) =
      openCubeSet Q := by
  ext x
  constructor
  · intro hx
    have hx' :
        cubeFaceReflectionCellFoldMap Q choice x ∈
          cubeFaceReflectionCellFoldMap Q choice ⁻¹' openCubeSet Q := by
      simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using hx
    simpa [cubeFaceReflectionCellFoldMap_involutive Q choice x] using hx'
  · intro hx
    have hx' :
        cubeFaceReflectionCellFoldMap Q choice x ∈
          cubeFaceReflectionCellFoldMap Q choice ⁻¹' openCubeSet Q := by
      simpa [cubeFaceReflectionCellFoldMap_involutive Q choice x] using hx
    simpa [preimage_cubeFaceReflectionCellFoldMap_openCubeSet Q choice] using hx'

private theorem memVectorL2_openCubeSet_cellCube_comp_cellFoldMap
    {d : ℕ} {Q : TriadicCube d} {choice : Fin d → Fin 3}
    {g : Vec d → Vec d}
    (hg :
      MemVectorL2 (openCubeSet (cubeFaceReflectionCellCube Q choice)) g) :
    MemVectorL2 (openCubeSet Q)
      (fun y => g (cubeFaceReflectionCellFoldMap Q choice y)) := by
  have hmp :=
    (measurePreserving_cubeFaceReflectionCellFoldMap Q choice).restrict_preimage_emb
      (measurableEmbedding_cubeFaceReflectionCellFoldMap Q choice)
      (openCubeSet (cubeFaceReflectionCellCube Q choice))
  have hcomp := hg.comp_measurePreserving hmp
  simpa [MemVectorL2, volumeMeasureOn,
    preimage_cubeFaceReflectionCellFoldMap_cellCube Q choice,
    Function.comp_def] using hcomp

private theorem memVectorL2_openCubeSet_cellFoldLinear_comp_cellFoldMap
    {d : ℕ} {Q : TriadicCube d} {choice : Fin d → Fin 3}
    {g : Vec d → Vec d}
    (hg :
      MemVectorL2 (openCubeSet (cubeFaceReflectionCellCube Q choice)) g) :
    MemVectorL2 (openCubeSet Q)
      (fun y =>
        cubeFaceReflectionCellFoldLinear choice
          (g (cubeFaceReflectionCellFoldMap Q choice y))) := by
  have hcomp :=
    memVectorL2_openCubeSet_cellCube_comp_cellFoldMap
      (Q := Q) (choice := choice) hg
  simpa [Function.comp_def] using
    (cubeFaceReflectionCellFoldLinear choice).comp_memLp' hcomp

private theorem integrable_openCubeSet_vecDot_cellFoldLinear_comp_cellFoldMap
    {d : ℕ} {Q : TriadicCube d} {choice : Fin d → Fin 3}
    {g G : Vec d → Vec d}
    (hg :
      MemVectorL2 (openCubeSet (cubeFaceReflectionCellCube Q choice)) g)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    MeasureTheory.Integrable
      (fun y =>
        vecDot
          (cubeFaceReflectionCellFoldLinear choice
            (g (cubeFaceReflectionCellFoldMap Q choice y)))
          (G y))
      (MeasureTheory.volume.restrict (openCubeSet Q)) := by
  have hgFold :=
    memVectorL2_openCubeSet_cellFoldLinear_comp_cellFoldMap
      (Q := Q) (choice := choice) hg
  simpa [MeasureTheory.IntegrableOn, volumeMeasureOn] using
    integrableOn_vecDot_of_memVectorL2
      (U := openCubeSet Q) hgFold hG

private theorem vecDot_fintype_sum_left {d : ℕ} {ι : Type*}
    [Fintype ι] (a : ι → Vec d) (b : Vec d) :
    vecDot (∑ i, a i) b = ∑ i, vecDot (a i) b := by
  classical
  rw [vecDot]
  simp only [Finset.sum_apply, Finset.sum_mul]
  change
    (∑ x : Fin d, ∑ y : ι, a y x * b x) =
      ∑ y : ι, vecDot (a y) b
  rw [Finset.sum_comm]
  simp [vecDot]

private theorem openCubeSet_cellCube_subset_originCube_succ
    {d : ℕ} (m : ℤ) (choice : Fin d → Fin 3) :
    openCubeSet (cubeFaceReflectionCellCube (originCube d m) choice) ⊆
      openCubeSet (originCube d (m + 1)) := by
  intro x hx
  have hcellBlock :
      openCubeSet (cubeFaceReflectionCellCube (originCube d m) choice) ⊆
        cubeFaceReflectionBlockSet (originCube d m) := by
    simpa [openCubeSet_cubeFaceReflectionCellCube] using
      cubeFaceReflectionCellSet_subset_cubeFaceReflectionBlockSet
        (originCube d m) choice
  exact cubeFaceReflectionBlockSet_originCube_subset_openCubeSet_succ d m
    (hcellBlock hx)

private theorem memVectorL2_openCubeSet_cellCube_of_memVectorL2_originCube_succ
    {d : ℕ} {m : ℤ} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m + 1))) g)
    (choice : Fin d → Fin 3) :
    MemVectorL2
      (openCubeSet (cubeFaceReflectionCellCube (originCube d m) choice)) g := by
  have hsub := openCubeSet_cellCube_subset_originCube_succ (d := d) m choice
  have hmono :=
    MeasureTheory.Measure.restrict_mono_set MeasureTheory.volume hsub
  simpa [MemVectorL2, volumeMeasureOn] using hg.mono_measure hmono

/-- The finite folded parent vector field is `L²` on the original cube. -/
theorem memVectorL2_openCubeSet_cubeFaceReflectionFoldedParentVectorField
    {d : ℕ} {m : ℤ} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m + 1))) g) :
    MemVectorL2 (openCubeSet (originCube d m))
      (cubeFaceReflectionFoldedParentVectorField (originCube d m) g) := by
  classical
  simpa [cubeFaceReflectionFoldedParentVectorField] using!
    MeasureTheory.memLp_finsetSum
      (s := (Finset.univ : Finset (Fin d → Fin 3)))
      (f := fun choice : Fin d → Fin 3 => fun y : Vec d =>
        cubeFaceReflectionCellFoldLinear choice
          (g (cubeFaceReflectionCellFoldMap (originCube d m) choice y)))
      (p := (2 : ℝ≥0∞))
      (μ := MeasureTheory.volume.restrict (openCubeSet (originCube d m)))
      (fun choice _hchoice =>
        memVectorL2_openCubeSet_cellFoldLinear_comp_cellFoldMap
          (Q := originCube d m) (choice := choice)
          (memVectorL2_openCubeSet_cellCube_of_memVectorL2_originCube_succ
            (m := m) hg choice))

/-- Change variables on one reflection cell in the pairing between an
arbitrary parent vector field and a reflected original-cube vector field. -/
theorem setIntegral_cubeFaceReflectionCellCube_vecDot_field_reflectedVectorField_eq
    {d : ℕ} {Q : TriadicCube d} {g G : Vec d → Vec d}
    (choice : Fin d → Fin 3) :
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        vecDot
          (cubeFaceReflectionCellFoldLinear choice
            (g (cubeFaceReflectionCellFoldMap Q choice y)))
          (G y) ∂MeasureTheory.volume := by
  let T : Vec d → Vec d := cubeFaceReflectionCellFoldMap Q choice
  let L : Vec d →L[ℝ] Vec d := cubeFaceReflectionCellFoldLinear choice
  calc
    ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
        (fun y => vecDot (L (g (T y))) (G y)) (T x)
        ∂MeasureTheory.volume := by
          refine MeasureTheory.setIntegral_congr_fun
            (measurableSet_openCubeSet (cubeFaceReflectionCellCube Q choice)) ?_
          intro x hx
          have hvec :=
            cubeCoordinateFoldReflectedVectorField_eq_cellFoldLinear_of_mem_cellCube
              Q choice G hx
          calc
            vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
                = vecDot (g x) (L (G (T x))) := by
                    simpa [T, L] using congrArg (fun v => vecDot (g x) v) hvec
            _ = vecDot (L (g x)) (G (T x)) := by
                    exact
                      (vecDot_cubeFaceReflectionCellFoldLinear_left
                        choice (g x) (G (T x))).symm
            _ = vecDot (L (g (T (T x)))) (G (T x)) := by
                    simp [T, cubeFaceReflectionCellFoldMap_involutive Q choice x]
    _ = ∫ y in openCubeSet Q,
        vecDot (L (g (T y))) (G y) ∂MeasureTheory.volume := by
          simpa [T, L] using
            setIntegral_cubeFaceReflectionCellCube_comp_cellFoldMap
              Q choice
              (fun y => vecDot (L (g (T y))) (G y))

/-- The block pairing with a reflected vector field is the original-cube
pairing against the finite folded parent vector field. -/
theorem setIntegral_cubeFaceReflectionBlockSet_vecDot_field_reflectedVectorField_eq_folded
    {d : ℕ} {Q : TriadicCube d} {g G : Vec d → Vec d}
    (hgCell :
      ∀ choice : Fin d → Fin 3,
        MemVectorL2 (openCubeSet (cubeFaceReflectionCellCube Q choice)) g)
    (hG : MemVectorL2 (openCubeSet Q) G) :
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      ∫ y in openCubeSet Q,
        vecDot (cubeFaceReflectionFoldedParentVectorField Q g y) (G y)
        ∂MeasureTheory.volume := by
  classical
  let f : Vec d → ℝ :=
    fun x => vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
  have hRBlock :
      MemVectorL2 (cubeFaceReflectionBlockSet Q)
        (cubeCoordinateFoldReflectedVectorField Q G) :=
    memVectorL2_cubeFaceReflectionBlockSet_cubeCoordinateFoldReflectedVectorField
      Q hG
  have hcell_subset :
      ∀ choice : Fin d → Fin 3,
        openCubeSet (cubeFaceReflectionCellCube Q choice) ⊆
          cubeFaceReflectionBlockSet Q := by
    intro choice
    simpa [openCubeSet_cubeFaceReflectionCellCube] using
      cubeFaceReflectionCellSet_subset_cubeFaceReflectionBlockSet Q choice
  have hfCell :
      ∀ choice : Fin d → Fin 3,
        MeasureTheory.Integrable f
          (MeasureTheory.volume.restrict
            (openCubeSet (cubeFaceReflectionCellCube Q choice))) := by
    intro choice
    have hRCell :
        MemVectorL2 (openCubeSet (cubeFaceReflectionCellCube Q choice))
          (cubeCoordinateFoldReflectedVectorField Q G) := by
      have hmono :=
        MeasureTheory.Measure.restrict_mono_set
          MeasureTheory.volume (hcell_subset choice)
      simpa [MemVectorL2, volumeMeasureOn] using hRBlock.mono_measure hmono
    simpa [f, MeasureTheory.IntegrableOn, volumeMeasureOn] using
      integrableOn_vecDot_of_memVectorL2
        (U := openCubeSet (cubeFaceReflectionCellCube Q choice))
        (hgCell choice) hRCell
  have hsplit :
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume =
        ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume :=
    setIntegral_cubeFaceReflectionBlockSet_cellCube Q f hfCell
  have hsum :
      (∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            vecDot
              (cubeFaceReflectionCellFoldLinear choice
                (g (cubeFaceReflectionCellFoldMap Q choice y)))
              (G y) ∂MeasureTheory.volume) =
        ∫ y in openCubeSet Q,
          vecDot (cubeFaceReflectionFoldedParentVectorField Q g y) (G y)
          ∂MeasureTheory.volume := by
    calc
      (∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            vecDot
              (cubeFaceReflectionCellFoldLinear choice
                (g (cubeFaceReflectionCellFoldMap Q choice y)))
              (G y) ∂MeasureTheory.volume) =
        ∫ y in openCubeSet Q,
          ∑ choice : Fin d → Fin 3,
            vecDot
              (cubeFaceReflectionCellFoldLinear choice
                (g (cubeFaceReflectionCellFoldMap Q choice y)))
              (G y) ∂MeasureTheory.volume := by
            rw [MeasureTheory.integral_finsetSum]
            intro choice _hchoice
            exact
              integrable_openCubeSet_vecDot_cellFoldLinear_comp_cellFoldMap
                (Q := Q) (choice := choice) (g := g) (G := G)
                (hgCell choice) hG
      _ = ∫ y in openCubeSet Q,
          vecDot (cubeFaceReflectionFoldedParentVectorField Q g y) (G y)
          ∂MeasureTheory.volume := by
            refine MeasureTheory.setIntegral_congr_fun
              (measurableSet_openCubeSet Q) ?_
            intro y _hy
            exact
              (vecDot_fintype_sum_left
                (fun choice : Fin d → Fin 3 =>
                  cubeFaceReflectionCellFoldLinear choice
                    (g (cubeFaceReflectionCellFoldMap Q choice y)))
                (G y)).symm
  calc
    ∫ x in cubeFaceReflectionBlockSet Q,
        vecDot (g x) (cubeCoordinateFoldReflectedVectorField Q G x)
        ∂MeasureTheory.volume =
      ∫ x in cubeFaceReflectionBlockSet Q, f x ∂MeasureTheory.volume := rfl
    _ = ∑ choice : Fin d → Fin 3,
          ∫ x in openCubeSet (cubeFaceReflectionCellCube Q choice),
            f x ∂MeasureTheory.volume := hsplit
    _ = ∑ choice : Fin d → Fin 3,
          ∫ y in openCubeSet Q,
            vecDot
              (cubeFaceReflectionCellFoldLinear choice
                (g (cubeFaceReflectionCellFoldMap Q choice y)))
              (G y) ∂MeasureTheory.volume := by
          apply Finset.sum_congr rfl
          intro choice _hchoice
          simpa [f] using
            setIntegral_cubeFaceReflectionCellCube_vecDot_field_reflectedVectorField_eq
              (Q := Q) (g := g) (G := G) choice
    _ = ∫ y in openCubeSet Q,
        vecDot (cubeFaceReflectionFoldedParentVectorField Q g y) (G y)
        ∂MeasureTheory.volume := hsum

/-- Centered parent-cube form of the folded-field reduction. To prove the
Hodge orthogonality demanded by the parent reflection potential theorem, it is
enough to show that this folded field is solenoidal zero-normal on the original
cube. -/
theorem setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
    {d : ℕ} {m : ℤ} {g G : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m + 1))) g)
    (hG : MemVectorL2 (openCubeSet (originCube d m)) G) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot (g x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m) G x)
        ∂MeasureTheory.volume =
      ∫ y in openCubeSet (originCube d m),
        vecDot
          (cubeFaceReflectionFoldedParentVectorField (originCube d m) g y)
          (G y) ∂MeasureTheory.volume := by
  rw [setIntegral_openCubeSet_succ_originCube_eq_cubeFaceReflectionBlockSet
    (m := m)
    (f := fun x =>
      vecDot (g x)
        (cubeCoordinateFoldReflectedVectorField (originCube d m) G x))]
  exact
    setIntegral_cubeFaceReflectionBlockSet_vecDot_field_reflectedVectorField_eq_folded
      (Q := originCube d m) (g := g) (G := G)
      (fun choice =>
        memVectorL2_openCubeSet_cellCube_of_memVectorL2_originCube_succ
          (m := m) hg choice)
      hG

/-- If every original-cube `H¹` test admits the expected all-face reflected
`H¹` realization on the centered parent cube, then folding a parent
solenoidal zero-normal field back to the original cube preserves the
solenoidal zero-normal test identity. This is the remaining Sobolev gluing
lemma in its most concrete form. -/
theorem cubeFaceReflectionFoldedParentVectorField_isSolenoidalZeroNormalTraceOn_of_parent_reflected_h1_tests
    {d : ℕ} {m : ℤ} {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m + 1))) g)
    (hsol :
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (m + 1))) g)
    (hreflect :
      ∀ φ : H1Function (openCubeSet (originCube d m)),
        ∃ ψ : H1Function (openCubeSet (originCube d (m + 1))),
          ψ.grad =
            cubeCoordinateFoldReflectedVectorField (originCube d m)
              (fun y => φ.grad y)) :
    IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d m))
      (cubeFaceReflectionFoldedParentVectorField (originCube d m) g) := by
  intro φ
  rcases hreflect φ with ⟨ψ, hψ_grad⟩
  have hpair :=
    setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
      (m := m) (g := g) (G := fun y => φ.grad y)
      hg φ.grad_memVectorL2
  have hparent :
      ∫ x in openCubeSet (originCube d (m + 1)),
          vecDot (g x)
            (cubeCoordinateFoldReflectedVectorField (originCube d m)
              (fun y => φ.grad y) x) ∂MeasureTheory.volume = 0 := by
    simpa [hψ_grad] using hsol ψ
  rw [hpair] at hparent
  exact hparent

namespace MeanZeroNeumannPoissonSolution

variable {F : Vec d → ℝ}

/-- Conditional discharge of the parent Hodge orthogonality: after folding a
parent solenoidal test field back to the original cube, the remaining analytic
claim is exactly that the folded field is solenoidal zero-normal there. -/
theorem cubeFaceReflectionParent_orthogonal_of_folded_solenoidal
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d (m + 1))) g)
    (hfoldSol :
      IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d m))
        (cubeFaceReflectionFoldedParentVectorField (originCube d m) g)) :
    ∫ x in openCubeSet (originCube d (m + 1)),
        vecDot (g x)
          (cubeCoordinateFoldReflectedVectorField (originCube d m)
            (fun y => W.w.toH1Function.grad y) x)
        ∂MeasureTheory.volume = 0 := by
  have hG : MemVectorL2 (openCubeSet (originCube d m))
      (fun y => W.w.toH1Function.grad y) := by
    simpa [MemVectorL2, volumeMeasureOn] using
      W.w.toH1Function.grad_memVectorL2
  rw [setIntegral_originCube_succ_vecDot_field_reflectedVectorField_eq_folded
    (m := m) (g := g) (G := fun y => W.w.toH1Function.grad y) hg hG]
  exact hfoldSol W.w.toH1Function

/-- Hodge-potential handoff with the remaining trace/gluing task isolated to a
single preservation property for folded parent solenoidal tests. -/
theorem cubeFaceReflectionParent_reflectedGradient_isPotentialOn_originCube_of_folded_solenoidal
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hfoldSol :
      ∀ {g : Vec d → Vec d},
        MemVectorL2 (openCubeSet (originCube d (m + 1))) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (m + 1))) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d m))
          (cubeFaceReflectionFoldedParentVectorField (originCube d m) g)) :
    IsPotentialOn (openCubeSet (originCube d (m + 1)))
      (cubeCoordinateFoldReflectedVectorField (originCube d m)
        (fun y => W.w.toH1Function.grad y)) := by
  exact
    W.cubeFaceReflectionParent_reflectedGradient_isPotentialOn_originCube_of_orthogonal
      (by
        intro g hg hsol
        exact W.cubeFaceReflectionParent_orthogonal_of_folded_solenoidal
          hg (hfoldSol hg hsol))

/-- Full weak-equation handoff from the folded-solenoidal preservation lemma.
This is the exact interface needed before applying the interior `H²` estimate
on the centered parent cube. -/
theorem exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_folded_solenoidal
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hfoldSol :
      ∀ {g : Vec d → Vec d},
        MemVectorL2 (openCubeSet (originCube d (m + 1))) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d (m + 1))) g →
        IsSolenoidalZeroNormalTraceOn (openCubeSet (originCube d m))
          (cubeFaceReflectionFoldedParentVectorField (originCube d m) g))
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y) ∧
      WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
        (cubeCoordinateFoldReflectedScalar (originCube d m) F) := by
  exact
    W.exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_isPotentialOn
      (W.cubeFaceReflectionParent_reflectedGradient_isPotentialOn_originCube_of_folded_solenoidal
        hfoldSol)
      hmean hF

/-- End-to-end conditional form of the reflection route: it remains to
construct the reflected parent `H¹` test for every original-cube `H¹` test. -/
theorem exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_parent_reflected_h1_tests
    (W : MeanZeroNeumannPoissonSolution (originCube d m) F)
    (hreflect :
      ∀ φ : H1Function (openCubeSet (originCube d m)),
        ∃ ψ : H1Function (openCubeSet (originCube d (m + 1))),
          ψ.grad =
            cubeCoordinateFoldReflectedVectorField (originCube d m)
              (fun y => φ.grad y))
    (hmean : cubeAverage (originCube d m) F = 0)
    (hF :
      MeasureTheory.MemLp F (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d m))) :
    ∃ uP : H1Function (openCubeSet (originCube d (m + 1))),
      uP.grad =
        cubeCoordinateFoldReflectedVectorField (originCube d m)
          (fun y => W.w.toH1Function.grad y) ∧
      WeakPoissonEquationOn (openCubeSet (originCube d (m + 1))) uP
        (cubeCoordinateFoldReflectedScalar (originCube d m) F) := by
  exact
    W.exists_cubeFaceReflectionParent_weakPoissonEquationOn_originCube_of_folded_solenoidal
      (by
        intro g hg hsol
        exact
          cubeFaceReflectionFoldedParentVectorField_isSolenoidalZeroNormalTraceOn_of_parent_reflected_h1_tests
            hg hsol hreflect)
      hmean hF

end MeanZeroNeumannPoissonSolution

end

end Homogenization
