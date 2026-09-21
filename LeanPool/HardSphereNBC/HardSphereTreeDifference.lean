/-
Copyright (c) 2026 ukiyois, OpenCode agent sessions. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ukiyois, OpenCode agent sessions
-/
import LeanPool.HardSphereNBC.HardSphereTree
import LeanPool.HardSphereNBC.HardSphereGeometry
import Mathlib.LinearAlgebra.Matrix.Block

/-! ### Triangular difference maps -/

namespace HsVirial

open Set
open Metric
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section



/-- Subtract each coordinate's parent coordinate, retaining root coordinates unchanged. -/
def hardSphereParentDifferenceLinearMap {ι : Type*}
    (parent : ι → Option ι) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  { toFun := fun x i => match parent i with
      | none => x i
      | some p => x i - x p
    map_add' := by
      intro x y
      funext i
      cases h : parent i with
      | none => simp [h]
      | some p => simp [h]; ring
    map_smul' := by
      intro c x
      funext i
      cases h : parent i with
      | none => simp [h]
      | some p => simp [h]; ring }

lemma hardSphereParentDifferenceLinearMap_apply
    {ι : Type*} (parent : ι → Option ι) (x : ι → ℝ) (i : ι) :
    hardSphereParentDifferenceLinearMap parent x i = match parent i with
      | none => x i
      | some p => x i - x p := by
  rfl

lemma hardSphereParentDifferenceLinearMap_toMatrix_lower
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent : ι → Option ι) (ord : LinearOrder ι)
    (hlt : ∀ i p, parent i = some p → @LT.lt ι ord.toLT p i) :
    (LinearMap.toMatrix'
      (hardSphereParentDifferenceLinearMap parent)).BlockTriangular
        (⇑OrderDual.toDual) := by
  let := ord
  intro i j hij
  change i < j at hij
  rw [LinearMap.toMatrix'_apply]
  cases hpi : parent i with
  | none =>
      simp [hardSphereParentDifferenceLinearMap, hpi, ne_of_gt hij]
  | some p =>
      have hp : p < i := hlt i p hpi
      simp [hardSphereParentDifferenceLinearMap, hpi,
        ne_of_gt hij, ne_of_lt (hp.trans hij)]

lemma hardSphereParentDifferenceLinearMap_toMatrix_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (parent : ι → Option ι) (ord : LinearOrder ι)
    (hlt : ∀ i p, parent i = some p → @LT.lt ι ord.toLT p i) (i : ι) :
    LinearMap.toMatrix'
      (hardSphereParentDifferenceLinearMap parent) i i = 1 := by
  let := ord
  rw [LinearMap.toMatrix'_apply]
  cases hpi : parent i with
  | none => simp [hardSphereParentDifferenceLinearMap, hpi]
  | some p =>
      have hp : p < i := hlt i p hpi
      simp [hardSphereParentDifferenceLinearMap, hpi, ne_of_lt hp]

lemma hardSphereParentDifferenceLinearMap_det
    {ι : Type*} [Finite ι] (parent : ι → Option ι) (ord : LinearOrder ι)
    (hlt : ∀ i p, parent i = some p → @LT.lt ι ord.toLT p i) :
    LinearMap.det (hardSphereParentDifferenceLinearMap parent) = 1 := by
  classical
  let := Fintype.ofFinite ι
  let := ord
  rw [← LinearMap.det_toMatrix']
  rw [Matrix.det_of_isLowerTriangular _
    (hardSphereParentDifferenceLinearMap_toMatrix_lower parent ord hlt)]
  simp_rw [hardSphereParentDifferenceLinearMap_toMatrix_diag parent ord hlt]
  simp

lemma measurePreserving_hardSphereParentDifferenceLinearMap
    {ι : Type*} [Fintype ι] (parent : ι → Option ι) (ord : LinearOrder ι)
    (hlt : ∀ i p, parent i = some p → @LT.lt ι ord.toLT p i) :
    MeasurePreserving (hardSphereParentDifferenceLinearMap parent)
      (volume : Measure (ι → ℝ)) (volume : Measure (ι → ℝ)) := by
  classical
  have hdet : LinearMap.det (hardSphereParentDifferenceLinearMap parent) ≠ 0 := by
    rw [hardSphereParentDifferenceLinearMap_det parent ord hlt]
    norm_num
  have hmatrix := Real.map_linearMap_volume_pi_eq_smul_volume_pi hdet
  refine ⟨?_, ?_⟩
  · exact (hardSphereParentDifferenceLinearMap parent).continuous_of_finiteDimensional.measurable
  · rw [hmatrix, hardSphereParentDifferenceLinearMap_det parent ord hlt]
    norm_num

/-! ### Rooted tree coordinates -/

/-- The parent's free index, or no index when the parent is the anchored particle. -/
def hardSphereTreeParentFreeIndex {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (i : Fin (k - 1)) : Option (Fin (k - 1)) :=
  if hp : hardSphereTreeParent hT i = 0 then
    none
  else
    some (hardSphereFreeIndex (hardSphereTreeParent hT i) hp)

/-- Lift the particle-parent relation to each scalar spatial coordinate. -/
def hardSphereTreeFlatParent {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (q : Fin (k - 1) × Fin 3) : Option (Fin (k - 1) × Fin 3) :=
  (hardSphereTreeParentFreeIndex hT q.1).map (fun p => (p, q.2))

/-- Order flattened spatial coordinates compatibly with the rooted-tree order. -/
@[instance_reducible]
noncomputable def hardSphereTreeFlatIndexOrder {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    LinearOrder (Fin (k - 1) × Fin 3) := by
  let treeOrd : LinearOrder (Fin (k - 1)) :=
    hardSphereTreeIndexOrder (k := k) T hT
  let : LinearOrder (Fin (k - 1)) := treeOrd
  let : LT (Fin (k - 1)) := treeOrd.toLT
  let : LE (Fin (k - 1)) := treeOrd.toLE
  let lexOrd : LinearOrder ((Fin (k - 1)) ×ₗ (Fin 3)) :=
    @Prod.Lex.instLinearOrder (Fin (k - 1)) (Fin 3) treeOrd inferInstance
  exact @LinearOrder.lift' (Fin (k - 1) × Fin 3)
    ((Fin (k - 1)) ×ₗ (Fin 3)) lexOrd
    (fun q => toLex (q.1, q.2)) (by
      intro q r h
      change toLex (q.1, q.2) = toLex (r.1, r.2) at h
      have h' : (q.1, q.2) = (r.1, r.2) := by
        apply Prod.ext
        · simpa using congrArg (fun p : (Fin (k - 1)) ×ₗ (Fin 3) =>
            (ofLex p).1) h
        · simpa using congrArg (fun p : (Fin (k - 1)) ×ₗ (Fin 3) =>
            (ofLex p).2) h
      exact h')

/-- The linear transformation from scalar positions to scalar tree differences. -/
def hardSphereTreeFlatDifferenceLinearMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    ((Fin (k - 1) × Fin 3) → ℝ) →ₗ[ℝ] ((Fin (k - 1) × Fin 3) → ℝ) :=
  hardSphereParentDifferenceLinearMap (hardSphereTreeFlatParent hT)

lemma hardSphereTreeFlatParent_lt {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    ∀ q p, hardSphereTreeFlatParent hT q = some p →
      @LT.lt _ (hardSphereTreeFlatIndexOrder hT).toLT p q := by
  let treeOrd : LinearOrder (Fin (k - 1)) :=
    hardSphereTreeIndexOrder (k := k) T hT
  let : LinearOrder (Fin (k - 1)) := treeOrd
  let : LT (Fin (k - 1)) := treeOrd.toLT
  let : LE (Fin (k - 1)) := treeOrd.toLE
  let lexOrd : LinearOrder ((Fin (k - 1)) ×ₗ (Fin 3)) :=
    @Prod.Lex.instLinearOrder (Fin (k - 1)) (Fin 3) treeOrd inferInstance
  intro q p hqp
  unfold hardSphereTreeFlatParent at hqp
  cases hparent : hardSphereTreeParentFreeIndex hT q.1 with
  | none => simp [hparent] at hqp
  | some parent =>
    simp only [hparent, Option.map_some, Option.some.injEq] at hqp
    obtain rfl := hqp
    have hroot : hardSphereTreeParent hT q.1 ≠ 0 := by
      intro hzero
      simp [hardSphereTreeParentFreeIndex, hzero] at hparent
    have hparent_eq :
        hardSphereFreeIndex (hardSphereTreeParent hT q.1) hroot = parent := by
      simpa [hardSphereTreeParentFreeIndex, hroot] using hparent
    have hlt := hardSphereTreeParent_index_lt hT q.1 hroot
    change @LT.lt ((Fin (k - 1)) ×ₗ (Fin 3)) lexOrd.toLT
      (toLex (parent, q.2)) (toLex (q.1, q.2))
    rw [@Prod.Lex.toLex_lt_toLex (Fin (k - 1)) (Fin 3)
      treeOrd.toLT (inferInstance : LT (Fin 3))]
    exact Or.inl (by simpa [hparent_eq] using hlt)

lemma measurePreserving_hardSphereTreeFlatDifferenceLinearMap
    {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    MeasurePreserving (hardSphereTreeFlatDifferenceLinearMap hT)
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ))
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ)) := by
  let treeOrd : LinearOrder (Fin (k - 1)) :=
    hardSphereTreeIndexOrder (k := k) T hT
  let : LinearOrder (Fin (k - 1)) := treeOrd
  let : LT (Fin (k - 1)) := treeOrd.toLT
  let : LE (Fin (k - 1)) := treeOrd.toLE
  let : LinearOrder (Fin (k - 1) × Fin 3) := hardSphereTreeFlatIndexOrder hT
  exact measurePreserving_hardSphereParentDifferenceLinearMap _
    (hardSphereTreeFlatIndexOrder hT) (hardSphereTreeFlatParent_lt hT)

/-! ### Product-coordinate volume -/

/-- Flatten an anchored three-dimensional configuration into scalar coordinates. -/
def hardSphereCoordinateEquiv (k : Nat) :
    HardSphereConfiguration k 3 ≃ᵐ (Fin (k - 1) × Fin 3 → ℝ) :=
  let e₁ := MeasurableEquiv.piCongrRight
    (fun _ : Fin (k - 1) =>
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm)
  let e₂ := (MeasurableEquiv.curry (Fin (k - 1)) (Fin 3) ℝ).symm
  e₁.trans e₂

lemma measurePreserving_hardSphereCoordinateEquiv (k : Nat) :
    MeasurePreserving (hardSphereCoordinateEquiv k)
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ)) := by
  let e₁ := MeasurableEquiv.piCongrRight
    (fun _ : Fin (k - 1) =>
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm)
  let e₂ := (MeasurableEquiv.curry (Fin (k - 1)) (Fin 3) ℝ).symm
  have h₁ : MeasurePreserving e₁
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure (Fin (k - 1) → Fin 3 → ℝ)) := by
    exact volume_preserving_pi
      (fun _ : Fin (k - 1) =>
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have h₂ : MeasurePreserving e₂
      (volume : Measure (Fin (k - 1) → Fin 3 → ℝ))
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ)) := by
    exact measurePreserving_curry_pi (μ := (volume : Measure ℝ))
  change MeasurePreserving (e₁.trans e₂) volume volume
  exact h₁.trans h₂

/-- Flattened position arrays with every three-dimensional block in the unit ball. -/
def hardSphereFlatProductBallRegion (n : Nat) :
    Set (Fin n × Fin 3 → ℝ) :=
  {x | ∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (fun a => x (i, a)) ∈
    Metric.ball (0 : HSPosition 3) 1}

lemma measurableSet_hardSphereFlatProductBallRegion (n : Nat) :
    MeasurableSet (hardSphereFlatProductBallRegion n) := by
  rw [show hardSphereFlatProductBallRegion n =
      ⋂ i : Fin n, {x : Fin n × Fin 3 → ℝ |
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (fun a => x (i, a)) ∈
          Metric.ball (0 : HSPosition 3) 1} by
    ext x
    simp [hardSphereFlatProductBallRegion]]
  exact MeasurableSet.iInter (fun i => by
    change MeasurableSet ((fun x : Fin n × Fin 3 → ℝ =>
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (fun a => x (i, a))) ⁻¹'
        Metric.ball (0 : HSPosition 3) 1)
    apply MeasurableSet.preimage measurableSet_ball
    fun_prop)

/-- Arrays of three-coordinate blocks lying in the unit ball. -/
def hardSphereBlockBallRegion (n : Nat) :
    Set (Fin n → Fin 3 → ℝ) :=
  {x | ∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (x i) ∈
    Metric.ball (0 : HSPosition 3) 1}

/-- Identify three-coordinate blocks with Euclidean positions, measurably. -/
def hardSphereBlockToPositionEquiv (n : Nat) :
    (Fin n → Fin 3 → ℝ) ≃ᵐ (Fin n → HSPosition 3) :=
  MeasurableEquiv.piCongrRight
    (fun _ : Fin n => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

lemma hardSphereBlockBallRegion_eq_preimage (n : Nat) :
    hardSphereBlockBallRegion n =
      hardSphereBlockToPositionEquiv n ⁻¹'
        hardSphereProductBallRegion n := by
  ext x
  change (∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (x i) ∈
      Metric.ball (0 : HSPosition 3) 1) ↔
    ∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (x i) ∈
      Metric.ball (0 : HSPosition 3) 1
  rfl

lemma measurableSet_hardSphereBlockBallRegion (n : Nat) :
    MeasurableSet (hardSphereBlockBallRegion n) := by
  rw [hardSphereBlockBallRegion_eq_preimage]
  exact MeasurableSet.preimage (measurableSet_hardSphereProductBallRegion n)
    (hardSphereBlockToPositionEquiv n).measurable

lemma measurePreserving_hardSphereBlockToPositionEquiv (n : Nat) :
    MeasurePreserving (hardSphereBlockToPositionEquiv n)
      (volume : Measure (Fin n → Fin 3 → ℝ))
      (volume : Measure (Fin n → HSPosition 3)) := by
  let e := MeasurableEquiv.piCongrRight
    (fun _ : Fin n => MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
  have h : MeasurePreserving e.symm
      (volume : Measure (Fin n → HSPosition 3))
      (volume : Measure (Fin n → Fin 3 → ℝ)) := by
    change MeasurePreserving
      (MeasurableEquiv.piCongrRight
        (fun _ : Fin n => (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm))
      volume volume
    exact volume_preserving_pi
      (fun _ : Fin n =>
        EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))
  have h' := MeasurePreserving.symm e.symm h
  change MeasurePreserving e volume volume
  exact h'

lemma hardSphereFlatProductBallRegion_volume (n : Nat) :
    (volume : Measure (Fin n × Fin 3 → ℝ)).real
        (hardSphereFlatProductBallRegion n) = hardSphereKappa ^ n := by
  let curryEquiv := MeasurableEquiv.curry (Fin n) (Fin 3) ℝ
  let hCurry : MeasurePreserving curryEquiv
      (volume : Measure (Fin n × Fin 3 → ℝ))
      (volume : Measure (Fin n → Fin 3 → ℝ)) := by
    exact (measurePreserving_curry_pi (μ := (volume : Measure ℝ))).symm
  let hBlock := measurePreserving_hardSphereBlockToPositionEquiv n
  have hblock_measure :
      (volume : Measure (Fin n → Fin 3 → ℝ))
          (hardSphereBlockBallRegion n) =
        (volume : Measure (Fin n → HSPosition 3))
          (hardSphereProductBallRegion n) := by
    rw [hardSphereBlockBallRegion_eq_preimage]
    calc
      (volume : Measure (Fin n → Fin 3 → ℝ))
          ((hardSphereBlockToPositionEquiv n) ⁻¹'
            hardSphereProductBallRegion n) =
          (Measure.map (hardSphereBlockToPositionEquiv n)
            (volume : Measure (Fin n → Fin 3 → ℝ)))
            (hardSphereProductBallRegion n) := by
        rw [Measure.map_apply (hardSphereBlockToPositionEquiv n).measurable
          (measurableSet_hardSphereProductBallRegion n)]
      _ = (volume : Measure (Fin n → HSPosition 3))
          (hardSphereProductBallRegion n) := by
        rw [hBlock.map_eq]
  have hflat_set : hardSphereFlatProductBallRegion n =
      curryEquiv ⁻¹' hardSphereBlockBallRegion n := by
    ext x
    change (∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => x (i, a)) ∈ Metric.ball (0 : HSPosition 3) 1) ↔
      ∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        ((curryEquiv x) i) ∈ Metric.ball (0 : HSPosition 3) 1
    rfl
  have hflat_measure :
      (volume : Measure (Fin n × Fin 3 → ℝ))
          (hardSphereFlatProductBallRegion n) =
        (volume : Measure (Fin n → Fin 3 → ℝ))
          (hardSphereBlockBallRegion n) := by
    rw [hflat_set]
    calc
      (volume : Measure (Fin n × Fin 3 → ℝ))
          (curryEquiv ⁻¹' hardSphereBlockBallRegion n) =
          (Measure.map curryEquiv
            (volume : Measure (Fin n × Fin 3 → ℝ)))
            (hardSphereBlockBallRegion n) := by
        rw [Measure.map_apply curryEquiv.measurable
          (measurableSet_hardSphereBlockBallRegion n)]
      _ = (volume : Measure (Fin n → Fin 3 → ℝ))
          (hardSphereBlockBallRegion n) := by
        rw [hCurry.map_eq]
  calc
    (volume : Measure (Fin n × Fin 3 → ℝ)).real
        (hardSphereFlatProductBallRegion n) =
      (volume : Measure (Fin n → Fin 3 → ℝ)).real
        (hardSphereBlockBallRegion n) := by
      exact congrArg ENNReal.toReal hflat_measure
    _ = (volume : Measure (Fin n → HSPosition 3)).real
        (hardSphereProductBallRegion n) := by
      exact congrArg ENNReal.toReal hblock_measure
    _ = hardSphereKappa ^ n := hardSphereProductBallRegion_volume n

/-! ### The separated two-member block -/

/-- Pairs of unit-ball positions separated by distance at least one. -/
def hardSphereSeparatedPairRegion : Set (HSPosition 3 × HSPosition 3) :=
  {p | p.1 ∈ ball (0 : HSPosition 3) 1 ∧
    p.2 ∈ ball (0 : HSPosition 3) 1 ∧
    1 ≤ ‖p.1 - p.2‖}

lemma measurableSet_hardSphereSeparatedPairRegion :
    MeasurableSet hardSphereSeparatedPairRegion := by
  unfold hardSphereSeparatedPairRegion
  rw [show {p : HSPosition 3 × HSPosition 3 |
      p.1 ∈ ball (0 : HSPosition 3) 1 ∧
        p.2 ∈ ball (0 : HSPosition 3) 1 ∧
        1 ≤ ‖p.1 - p.2‖} =
      (Prod.fst ⁻¹' ball (0 : HSPosition 3) 1) ∩
      (Prod.snd ⁻¹' ball (0 : HSPosition 3) 1) ∩
        ((fun p : HSPosition 3 × HSPosition 3 => ‖p.1 - p.2‖) ⁻¹' Ici 1) by
    ext p
    simp [Set.mem_ofPred_eq, and_assoc]
  ]
  have hfst : MeasurableSet
      (Prod.fst ⁻¹' ball (0 : HSPosition 3) 1) :=
    MeasurableSet.preimage
      (measurableSet_ball : MeasurableSet (ball (0 : HSPosition 3) 1))
      (measurable_fst : Measurable (fun p : HSPosition 3 × HSPosition 3 => p.1))
  have hsnd : MeasurableSet
      (Prod.snd ⁻¹' ball (0 : HSPosition 3) 1) :=
    MeasurableSet.preimage
      (measurableSet_ball : MeasurableSet (ball (0 : HSPosition 3) 1))
      (measurable_snd : Measurable (fun p : HSPosition 3 × HSPosition 3 => p.2))
  have hnorm : MeasurableSet
      ((fun p : HSPosition 3 × HSPosition 3 => ‖p.1 - p.2‖) ⁻¹' Ici 1) :=
    MeasurableSet.preimage measurableSet_Ici
      (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable
  exact (hfst.inter hsnd).inter hnorm

/-! ### Relative coordinates for a separated pair -/

/-- Flatten a pair of three-dimensional Euclidean positions. -/
def hardSpherePairCoordinateEquiv :
    (HSPosition 3 × HSPosition 3) ≃ᵐ (Fin 2 × Fin 3 → ℝ) :=
  (MeasurableEquiv.finTwoArrow (α := HSPosition 3)).symm.trans
    (hardSphereCoordinateEquiv 3)

lemma measurePreserving_hardSpherePairCoordinateEquiv :
    MeasurePreserving hardSpherePairCoordinateEquiv := by
  change MeasurePreserving
    ((MeasurableEquiv.finTwoArrow (α := HSPosition 3)).symm.trans
      (hardSphereCoordinateEquiv 3)) volume volume
  exact (MeasurePreserving.symm
      (MeasurableEquiv.finTwoArrow (α := HSPosition 3))
      (volume_preserving_finTwoArrow (HSPosition 3))).trans
    (measurePreserving_hardSphereCoordinateEquiv 3)

lemma hardSpherePairCoordinateEquiv_apply_zero
    (p : HSPosition 3 × HSPosition 3) (a : Fin 3) :
    hardSpherePairCoordinateEquiv p (0, a) = p.1.ofLp a := by
  rcases p with ⟨p, q⟩
  rfl

lemma hardSpherePairCoordinateEquiv_apply_one
    (p : HSPosition 3 × HSPosition 3) (a : Fin 3) :
    hardSpherePairCoordinateEquiv p (1, a) = p.2.ofLp a := by
  rcases p with ⟨p, q⟩
  rfl

lemma hardSpherePairCoordinate_block_zero (p : HSPosition 3 × HSPosition 3) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSpherePairCoordinateEquiv p (0, a)) = p.1 := by
  change (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => hardSpherePairCoordinateEquiv p (0, a)) =
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (fun a => p.1.ofLp a)
  congr 1

lemma hardSpherePairCoordinate_block_one (p : HSPosition 3 × HSPosition 3) :
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSpherePairCoordinateEquiv p (1, a)) = p.2 := by
  change (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => hardSpherePairCoordinateEquiv p (1, a)) =
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)) (fun a => p.2.ofLp a)
  congr 1

lemma hardSpherePairCoordinateEquiv_preimage_flatProductBallRegion :
    hardSpherePairCoordinateEquiv ⁻¹'
        hardSphereFlatProductBallRegion 2 =
      ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1 := by
  ext p
  change (∀ i, (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => hardSpherePairCoordinateEquiv p (i, a)) ∈
        ball (0 : HSPosition 3) 1) ↔
    p.1 ∈ ball (0 : HSPosition 3) 1 ∧ p.2 ∈ ball (0 : HSPosition 3) 1
  constructor
  · intro hp
    have h0 := hp (0 : Fin 2)
    have h1 := hp (1 : Fin 2)
    rw [hardSpherePairCoordinate_block_zero] at h0
    rw [hardSpherePairCoordinate_block_one] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · change (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSpherePairCoordinateEquiv p (0, a)) ∈
          ball (0 : HSPosition 3) 1
      rw [hardSpherePairCoordinate_block_zero]
      exact h0
    · change (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => hardSpherePairCoordinateEquiv p (1, a)) ∈
          ball (0 : HSPosition 3) 1
      rw [hardSpherePairCoordinate_block_one]
      exact h1

/-- The separated-pair region in flattened scalar coordinates. -/
def hardSphereSeparatedPairFlatRegion : Set (Fin 2 × Fin 3 → ℝ) :=
  hardSphereFlatProductBallRegion 2 ∩
    {x | 1 ≤ ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
          (fun a => x (0, a)) -
        (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
          (fun a => x (1, a))‖}

lemma hardSpherePairCoordinateEquiv_image_separatedPairRegion :
    hardSpherePairCoordinateEquiv '' hardSphereSeparatedPairRegion =
      hardSphereSeparatedPairFlatRegion := by
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    rw [hardSphereSeparatedPairFlatRegion]
    refine ⟨?_, ?_⟩
    · have hprod : p ∈ ball (0 : HSPosition 3) 1 ×ˢ
          ball (0 : HSPosition 3) 1 := ⟨hp.1, hp.2.1⟩
      change p ∈ hardSpherePairCoordinateEquiv ⁻¹'
        hardSphereFlatProductBallRegion 2
      rw [hardSpherePairCoordinateEquiv_preimage_flatProductBallRegion]
      exact hprod
    · exact hp.2.2
  · intro x hx
    let p := hardSpherePairCoordinateEquiv.symm x
    have hpx : hardSpherePairCoordinateEquiv p = x := by
      simp [p]
    have hprod : p ∈ ball (0 : HSPosition 3) 1 ×ˢ
        ball (0 : HSPosition 3) 1 := by
      rw [← hardSpherePairCoordinateEquiv_preimage_flatProductBallRegion]
      change hardSpherePairCoordinateEquiv p ∈ hardSphereFlatProductBallRegion 2
      rw [hpx]
      exact hx.1
    have hsep : 1 ≤ ‖p.1 - p.2‖ := by
      have hxsep := hx.2
      change 1 ≤ ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
            (fun a => x (0, a)) -
          (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
            (fun a => x (1, a))‖ at hxsep
      rw [← hpx, hardSpherePairCoordinate_block_zero,
        hardSpherePairCoordinate_block_one] at hxsep
      exact hxsep
    refine ⟨p, ⟨hprod.1, hprod.2, hsep⟩, hpx⟩

lemma hardSphereSeparatedPairRegion_flatten_volume :
    (volume : Measure (Fin 2 × Fin 3 → ℝ)).real
        (hardSpherePairCoordinateEquiv '' hardSphereSeparatedPairRegion) =
      (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion := by
  exact congrArg ENNReal.toReal
    (measure_image_eq_of_measurePreserving hardSpherePairCoordinateEquiv
      measurePreserving_hardSpherePairCoordinateEquiv
      measurableSet_hardSphereSeparatedPairRegion)

lemma hardSphereSeparatedPairRegion_flatten_volume_eq_flat :
    (volume : Measure (Fin 2 × Fin 3 → ℝ)).real
        (hardSpherePairCoordinateEquiv '' hardSphereSeparatedPairRegion) =
      (volume : Measure (Fin 2 × Fin 3 → ℝ)).real
        hardSphereSeparatedPairFlatRegion := by
  rw [hardSpherePairCoordinateEquiv_image_separatedPairRegion]

/-- Pairs of unit-ball positions separated by distance less than one. -/
def hardSphereClosePairRegion : Set (HSPosition 3 × HSPosition 3) :=
  {p | p.1 ∈ ball (0 : HSPosition 3) 1 ∧
    p.2 ∈ ball (0 : HSPosition 3) 1 ∧
    ‖p.1 - p.2‖ < 1}

lemma measurableSet_hardSphereClosePairRegion :
    MeasurableSet hardSphereClosePairRegion := by
  unfold hardSphereClosePairRegion
  rw [show {p : HSPosition 3 × HSPosition 3 |
      p.1 ∈ ball (0 : HSPosition 3) 1 ∧
        p.2 ∈ ball (0 : HSPosition 3) 1 ∧
        ‖p.1 - p.2‖ < (1 : ℝ)} =
      (Prod.fst ⁻¹' ball (0 : HSPosition 3) 1) ∩
      (Prod.snd ⁻¹' ball (0 : HSPosition 3) 1) ∩
        ((fun p : HSPosition 3 × HSPosition 3 => ‖p.1 - p.2‖) ⁻¹' Iio 1) by
    ext p
    simp [Set.mem_ofPred_eq, and_assoc]]
  have hfst : MeasurableSet
      (Prod.fst ⁻¹' ball (0 : HSPosition 3) 1) :=
    MeasurableSet.preimage
      (measurableSet_ball : MeasurableSet (ball (0 : HSPosition 3) 1))
      (measurable_fst : Measurable (fun p : HSPosition 3 × HSPosition 3 => p.1))
  have hsnd : MeasurableSet
      (Prod.snd ⁻¹' ball (0 : HSPosition 3) 1) :=
    MeasurableSet.preimage
      (measurableSet_ball : MeasurableSet (ball (0 : HSPosition 3) 1))
      (measurable_snd : Measurable (fun p : HSPosition 3 × HSPosition 3 => p.2))
  have hnorm : MeasurableSet
      ((fun p : HSPosition 3 × HSPosition 3 => ‖p.1 - p.2‖) ⁻¹' Iio 1) :=
    MeasurableSet.preimage measurableSet_Iio
      (continuous_norm.comp (continuous_fst.sub continuous_snd)).measurable
  exact (hfst.inter hsnd).inter hnorm

lemma hardSphereSeparatedPairRegion_eq_product_sdiff_close :
    hardSphereSeparatedPairRegion =
      (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1) \
        hardSphereClosePairRegion := by
  ext p
  simp only [hardSphereSeparatedPairRegion, hardSphereClosePairRegion,
    mem_sdiff, mem_prod, mem_ball, dist_zero_right, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp1, hp2, hsep⟩
    refine ⟨⟨hp1, hp2⟩, ?_⟩
    intro hclose
    exact (not_lt_of_ge hsep) hclose.2.2
  · rintro ⟨⟨hp1, hp2⟩, hnotclose⟩
    refine ⟨hp1, hp2, le_of_not_gt ?_⟩
    intro hclose
    exact hnotclose ⟨hp1, hp2, hclose⟩

lemma hardSphereClosePairRegion_subset_product :
    hardSphereClosePairRegion ⊆
      ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1 := by
  intro p hp
  exact ⟨hp.1, hp.2.1⟩

lemma hardSphereSeparatedPairRegion_add_close_volume :
    (volume : Measure (HSPosition 3 × HSPosition 3))
        hardSphereSeparatedPairRegion +
      volume hardSphereClosePairRegion =
      volume (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1) := by
  rw [hardSphereSeparatedPairRegion_eq_product_sdiff_close]
  have h := measure_sdiff_add_inter
    (μ := (volume : Measure (HSPosition 3 × HSPosition 3)))
    (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1)
    measurableSet_hardSphereClosePairRegion
  rw [inter_eq_right.mpr hardSphereClosePairRegion_subset_product] at h
  exact h

lemma hardSphereSeparatedPairRegion_real_add_close_volume :
    (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion +
      (volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereClosePairRegion = hardSphereKappa ^ 2 := by
  have hball :
      volume (ball (0 : HSPosition 3) 1) < ∞ := measure_ball_lt_top
  have hprod :
      volume (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1) < ∞ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hball hball
  have hsep :
      volume (hardSphereSeparatedPairRegion) ≠ ∞ :=
    (lt_of_le_of_lt
      (measure_mono (by
        rw [hardSphereSeparatedPairRegion_eq_product_sdiff_close]
        exact sdiff_subset)) hprod).ne
  have hclose : volume hardSphereClosePairRegion ≠ ∞ :=
    (lt_of_le_of_lt
      (measure_mono hardSphereClosePairRegion_subset_product) hprod).ne
  have h := congrArg ENNReal.toReal hardSphereSeparatedPairRegion_add_close_volume
  rw [ENNReal.toReal_add hsep hclose] at h
  have htotal :
      (volume : Measure (HSPosition 3 × HSPosition 3)).real
          (ball (0 : HSPosition 3) 1 ×ˢ ball (0 : HSPosition 3) 1) =
        hardSphereKappa ^ 2 := by
    change (volume (ball (0 : HSPosition 3) 1 ×ˢ
        ball (0 : HSPosition 3) 1)).toReal = _
    rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]
    rw [pow_two]
    rfl
  exact h.trans htotal

/-- The parent relation implementing the difference of the second position from the first. -/
def hardSpherePairParent (q : Fin 2 × Fin 3) : Option (Fin 2 × Fin 3) :=
  if q.1 = 0 then none else some (0, q.2)

/-- The lexicographic order on particle and spatial indices for a pair. -/
@[instance_reducible]
noncomputable def hardSpherePairIndexOrder : LinearOrder (Fin 2 × Fin 3) := by
  let lexOrd : LinearOrder ((Fin 2) ×ₗ (Fin 3)) :=
    @Prod.Lex.instLinearOrder (Fin 2) (Fin 3) inferInstance inferInstance
  exact @LinearOrder.lift' (Fin 2 × Fin 3) ((Fin 2) ×ₗ (Fin 3)) lexOrd
    (fun q => toLex (q.1, q.2)) (by
      intro q r h
      change toLex (q.1, q.2) = toLex (r.1, r.2) at h
      have h' : (q.1, q.2) = (r.1, r.2) := by
        apply Prod.ext
        · simpa using congrArg (fun p : (Fin 2) ×ₗ (Fin 3) => (ofLex p).1) h
        · simpa using congrArg (fun p : (Fin 2) ×ₗ (Fin 3) => (ofLex p).2) h
      exact h')

lemma hardSpherePairParent_lt : ∀ q p, hardSpherePairParent q = some p →
    @LT.lt _ hardSpherePairIndexOrder.toLT p q := by
  let lexOrd : LinearOrder ((Fin 2) ×ₗ (Fin 3)) :=
    @Prod.Lex.instLinearOrder (Fin 2) (Fin 3) inferInstance inferInstance
  intro q p h
  by_cases hq : q.1 = 0
  · simp [hardSpherePairParent, hq] at h
  · have hp : p = (0, q.2) := by
      simpa [hardSpherePairParent, hq] using h.symm
    subst p
    have hqpos : 0 < q.1 := Fin.pos_iff_ne_zero.mpr hq
    change @LT.lt ((Fin 2) ×ₗ (Fin 3)) lexOrd.toLT
      (toLex (0, q.2)) (toLex (q.1, q.2))
    rw [Prod.Lex.toLex_lt_toLex]
    left
    exact hqpos

/-- The linear parent-difference map on a flattened pair of positions. -/
def hardSpherePairDifferenceLinearMap :
    ((Fin 2 × Fin 3) → ℝ) →ₗ[ℝ] ((Fin 2 × Fin 3) → ℝ) :=
  hardSphereParentDifferenceLinearMap hardSpherePairParent

lemma measurePreserving_hardSpherePairDifferenceLinearMap :
    MeasurePreserving hardSpherePairDifferenceLinearMap := by
  exact measurePreserving_hardSphereParentDifferenceLinearMap hardSpherePairParent
    hardSpherePairIndexOrder hardSpherePairParent_lt

/-- The two leaf positions relative to the common center of a fork. -/
def hardSphereForkRelativePair {k : Nat} [NeZero k]
    (r : HardSphereConfiguration k 3) (a b c : Fin k) :
    HSPosition 3 × HSPosition 3 :=
  (hardSpherePosition r b - hardSpherePosition r a,
    hardSpherePosition r c - hardSpherePosition r a)

lemma hardSphere_nbc_region_mem_separatedPair
    {k : Nat} [NeZero k] {r : HardSphereConfiguration k 3}
    {T : Finset (Sym2 (Fin k))} {a b c : Fin k}
    (hr : r ∈ nbcRegion (V := Fin k)
      (hardSphereActiveExact (k := k) (d := 3)) T)
    (hf : hardSphereFork T a b c) :
    hardSphereForkRelativePair r a b c ∈ hardSphereSeparatedPairRegion := by
  have htree := hardSphere_nbc_region_subset_tree_region hr
  have habactive := htree (s(a, b)) hf.2.2.1
  have hacactive := htree (s(a, c)) hf.2.2.2
  rw [hardSphereActiveExact_mk] at habactive hacactive
  have habnorm : ‖hardSpherePosition r b - hardSpherePosition r a‖ < (1 : ℝ) := by
    rw [norm_sub_rev]
    exact of_decide_eq_true habactive
  have hacnorm : ‖hardSpherePosition r c - hardSpherePosition r a‖ < (1 : ℝ) := by
    rw [norm_sub_rev]
    exact of_decide_eq_true hacactive
  have hbcnot : ¬ ‖hardSpherePosition r b - hardSpherePosition r c‖ < (1 : ℝ) := by
    intro hbc
    exact hardSphere_nbc_region_excludes_fork_chord r hr hf hbc
  rw [hardSphereForkRelativePair, hardSphereSeparatedPairRegion]
  simp only [Set.mem_ofPred_eq]
  rw [show (hardSpherePosition r b - hardSpherePosition r a) -
      (hardSpherePosition r c - hardSpherePosition r a) =
      hardSpherePosition r b - hardSpherePosition r c by abel]
  refine ⟨?_, ?_, le_of_not_gt hbcnot⟩
  · rw [mem_ball_iff_norm]
    simpa [sub_zero] using habnorm
  · rw [mem_ball_iff_norm]
    simpa [sub_zero] using hacnorm

/-- Families of separated pairs, each lying in the unit ball. -/
def hardSphereSeparatedPairProductRegion (m : Nat) :
    Set (Fin m → (HSPosition 3 × HSPosition 3)) :=
  {x | ∀ i, x i ∈ hardSphereSeparatedPairRegion}

lemma measurableSet_hardSphereSeparatedPairProductRegion (m : Nat) :
    MeasurableSet (hardSphereSeparatedPairProductRegion m) := by
  rw [show hardSphereSeparatedPairProductRegion m =
      Set.univ.pi (fun _ : Fin m => hardSphereSeparatedPairRegion) by
    ext x
    simp [hardSphereSeparatedPairProductRegion]]
  exact MeasurableSet.pi Set.countable_univ
    (fun _ _ => measurableSet_hardSphereSeparatedPairRegion)

lemma hardSphereSeparatedPairProductRegion_volume (m : Nat) :
    (volume : Measure (Fin m → (HSPosition 3 × HSPosition 3))).real
        (hardSphereSeparatedPairProductRegion m) =
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion) ^ m := by
  have hset : hardSphereSeparatedPairProductRegion m =
      Set.univ.pi (fun _ : Fin m => hardSphereSeparatedPairRegion) := by
    ext x
    simp [hardSphereSeparatedPairProductRegion]
  change (volume (hardSphereSeparatedPairProductRegion m)).toReal = _
  rw [hset, volume_pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Measure.real]

/-- A product of separated-pair regions and unconstrained unit-ball positions. -/
def hardSphereSeparatedBlockProductRegion (m q : Nat) :
    Set ((Fin m → (HSPosition 3 × HSPosition 3)) ×
      (Fin q → HSPosition 3)) :=
  hardSphereSeparatedPairProductRegion m ×ˢ hardSphereProductBallRegion q

lemma measurableSet_hardSphereSeparatedBlockProductRegion (m q : Nat) :
    MeasurableSet (hardSphereSeparatedBlockProductRegion m q) := by
  exact (measurableSet_hardSphereSeparatedPairProductRegion m).prod
    (measurableSet_hardSphereProductBallRegion q)

lemma hardSphereSeparatedBlockProductRegion_volume (m q : Nat) :
    (volume : Measure ((Fin m → (HSPosition 3 × HSPosition 3)) ×
      (Fin q → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) =
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
        hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q := by
  change (volume (hardSphereSeparatedBlockProductRegion m q)).toReal = _
  rw [hardSphereSeparatedBlockProductRegion, Measure.volume_eq_prod,
    Measure.prod_prod, ENNReal.toReal_mul]
  change (volume : Measure (Fin m → (HSPosition 3 × HSPosition 3))).real
      (hardSphereSeparatedPairProductRegion m) *
      (volume : Measure (Fin q → HSPosition 3)).real
        (hardSphereProductBallRegion q) = _
  rw [hardSphereSeparatedPairProductRegion_volume,
    hardSphereProductBallRegion_volume]

/-! ### Canonical separated-block coordinates -/

/-- Split a position array into paired blocks and remaining single positions. -/
def hardSphereBlockCoordinateEquiv (m q : Nat) :
    (Fin (m * 2 + q) → HSPosition 3) ≃ᵐ
      ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3)) := by
  let eSplit : (Fin (m * 2 + q) → HSPosition 3) ≃ᵐ
      ((Fin (m * 2) → HSPosition 3) × (Fin q → HSPosition 3)) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (m * 2 + q) => HSPosition 3)
      (@finSumFinEquiv (m * 2) q)).symm.trans
      (MeasurableEquiv.sumPiEquivProdPi
        (fun _ : Fin (m * 2) ⊕ Fin q => HSPosition 3))
  let eGroup : (Fin (m * 2) → HSPosition 3) ≃ᵐ
      (Fin m × Fin 2 → HSPosition 3) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (m * 2) => HSPosition 3)
      (@finProdFinEquiv m 2)).symm
  let ePair : (Fin m × Fin 2 → HSPosition 3) ≃ᵐ
      (Fin m → (HSPosition 3 × HSPosition 3)) :=
    (MeasurableEquiv.curry (Fin m) (Fin 2) (HSPosition 3)).trans
      (MeasurableEquiv.piCongrRight
        (fun _ : Fin m => MeasurableEquiv.finTwoArrow))
  exact eSplit.trans (MeasurableEquiv.prodCongr
    (eGroup.trans ePair)
    (MeasurableEquiv.refl (Fin q → HSPosition 3)))

lemma measurePreserving_hardSphereBlockCoordinateEquiv (m q : Nat) :
    MeasurePreserving (hardSphereBlockCoordinateEquiv m q)
      (volume : Measure (Fin (m * 2 + q) → HSPosition 3))
      (volume : Measure ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3))) := by
  let eReindex : (Fin (m * 2 + q) → HSPosition 3) ≃ᵐ
      ((Fin (m * 2) ⊕ Fin q) → HSPosition 3) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (m * 2 + q) => HSPosition 3)
      (@finSumFinEquiv (m * 2) q)).symm
  let eSplit : ((Fin (m * 2) ⊕ Fin q) → HSPosition 3) ≃ᵐ
      ((Fin (m * 2) → HSPosition 3) × (Fin q → HSPosition 3)) :=
    MeasurableEquiv.sumPiEquivProdPi
      (fun _ : Fin (m * 2) ⊕ Fin q => HSPosition 3)
  let eGroup : (Fin (m * 2) → HSPosition 3) ≃ᵐ
      (Fin m × Fin 2 → HSPosition 3) :=
    (MeasurableEquiv.piCongrLeft
      (fun _ : Fin (m * 2) => HSPosition 3)
      (@finProdFinEquiv m 2)).symm
  let ePair : (Fin m × Fin 2 → HSPosition 3) ≃ᵐ
      (Fin m → (HSPosition 3 × HSPosition 3)) :=
    (MeasurableEquiv.curry (Fin m) (Fin 2) (HSPosition 3)).trans
      (MeasurableEquiv.piCongrRight
        (fun _ : Fin m => MeasurableEquiv.finTwoArrow))
  have hReindex : MeasurePreserving eReindex := by
    exact MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (m * 2 + q) => HSPosition 3)
        (@finSumFinEquiv (m * 2) q))
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin (m * 2 + q) => HSPosition 3)
        (@finSumFinEquiv (m * 2) q))
  have hSplit : MeasurePreserving eSplit :=
    volume_measurePreserving_sumPiEquivProdPi _
  have hGroup : MeasurePreserving eGroup := by
    exact MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin (m * 2) => HSPosition 3)
        (@finProdFinEquiv m 2))
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin (m * 2) => HSPosition 3)
        (@finProdFinEquiv m 2))
  have hPair : MeasurePreserving ePair := by
    have hCurry : MeasurePreserving
        (MeasurableEquiv.curry (Fin m) (Fin 2) (HSPosition 3)) volume volume := by
      exact MeasurePreserving.symm
        (MeasurableEquiv.curry (Fin m) (Fin 2) (HSPosition 3)).symm
        (measurePreserving_curry_pi (μ := (volume : Measure (HSPosition 3))))
    have hPi : MeasurePreserving
        (MeasurableEquiv.piCongrRight
          (fun _ : Fin m =>
            MeasurableEquiv.finTwoArrow (α := HSPosition 3))) volume volume := by
      change MeasurePreserving
        (fun (x : Fin m → (Fin 2 → HSPosition 3)) (i : Fin m) =>
          MeasurableEquiv.finTwoArrow (x i)) volume volume
      exact volume_preserving_pi (fun _ =>
        volume_preserving_finTwoArrow (HSPosition 3))
    exact hCurry.trans hPi
  have hProd : MeasurePreserving
      (MeasurableEquiv.prodCongr (eGroup.trans ePair)
        (MeasurableEquiv.refl (Fin q → HSPosition 3))) := by
    exact (hGroup.trans hPair).prod (MeasurePreserving.id volume)
  change MeasurePreserving
    (eReindex.trans (eSplit.trans
      (MeasurableEquiv.prodCongr (eGroup.trans ePair)
        (MeasurableEquiv.refl (Fin q → HSPosition 3))))) volume volume
  exact hReindex.trans (hSplit.trans hProd)

lemma hardSphereBlockCoordinateEquiv_preimage_separatedBlockProductRegion_volume
    (m q : Nat) :
    (volume : Measure (Fin (m * 2 + q) → HSPosition 3)).real
        ((hardSphereBlockCoordinateEquiv m q) ⁻¹'
          hardSphereSeparatedBlockProductRegion m q) =
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q := by
  let hmap := measurePreserving_hardSphereBlockCoordinateEquiv m q
  calc
    (volume : Measure (Fin (m * 2 + q) → HSPosition 3)).real
        ((hardSphereBlockCoordinateEquiv m q) ⁻¹'
          hardSphereSeparatedBlockProductRegion m q) =
      (Measure.map (hardSphereBlockCoordinateEquiv m q)
        (volume : Measure (Fin (m * 2 + q) → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) := by
      exact congrArg ENNReal.toReal
        (Measure.map_apply hmap.measurable
          (measurableSet_hardSphereSeparatedBlockProductRegion m q)).symm
    _ = (volume : Measure
          ((Fin m → (HSPosition 3 × HSPosition 3)) ×
            (Fin q → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) := by
      rw [hmap.map_eq]
    _ = ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q :=
      hardSphereSeparatedBlockProductRegion_volume m q

/-- Reindex a position array before separating paired and single blocks. -/
def hardSphereReindexedBlockCoordinateEquiv
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n) :
    (Fin n → HSPosition 3) ≃ᵐ
      ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3)) :=
  (MeasurableEquiv.piCongrLeft
      (fun _ : Fin n => HSPosition 3) e).symm.trans
    (hardSphereBlockCoordinateEquiv m q)

lemma measurePreserving_hardSphereReindexedBlockCoordinateEquiv
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n) :
    MeasurePreserving (hardSphereReindexedBlockCoordinateEquiv e)
      (volume : Measure (Fin n → HSPosition 3))
      (volume : Measure ((Fin m → (HSPosition 3 × HSPosition 3)) ×
        (Fin q → HSPosition 3))) := by
  have hReindex : MeasurePreserving
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin n => HSPosition 3) e).symm := by
    exact MeasurePreserving.symm
      (MeasurableEquiv.piCongrLeft
        (fun _ : Fin n => HSPosition 3) e)
      (volume_measurePreserving_piCongrLeft
        (fun _ : Fin n => HSPosition 3) e)
  change MeasurePreserving
    ((MeasurableEquiv.piCongrLeft
      (fun _ : Fin n => HSPosition 3) e).symm.trans
      (hardSphereBlockCoordinateEquiv m q)) volume volume
  exact hReindex.trans (measurePreserving_hardSphereBlockCoordinateEquiv m q)

lemma hardSphereReindexedBlockCoordinateEquiv_preimage_separatedBlockProductRegion_volume
    {n m q : Nat} (e : Fin (m * 2 + q) ≃ Fin n) :
    (volume : Measure (Fin n → HSPosition 3)).real
        ((hardSphereReindexedBlockCoordinateEquiv e) ⁻¹'
          hardSphereSeparatedBlockProductRegion m q) =
      ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q := by
  let hmap := measurePreserving_hardSphereReindexedBlockCoordinateEquiv e
  calc
    (volume : Measure (Fin n → HSPosition 3)).real
        ((hardSphereReindexedBlockCoordinateEquiv e) ⁻¹'
          hardSphereSeparatedBlockProductRegion m q) =
      (Measure.map (hardSphereReindexedBlockCoordinateEquiv e)
        (volume : Measure (Fin n → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) := by
      exact congrArg ENNReal.toReal
        (Measure.map_apply hmap.measurable
          (measurableSet_hardSphereSeparatedBlockProductRegion m q)).symm
    _ = (volume : Measure
          ((Fin m → (HSPosition 3 × HSPosition 3)) ×
            (Fin q → HSPosition 3))).real
        (hardSphereSeparatedBlockProductRegion m q) := by
      rw [hmap.map_eq]
    _ = ((volume : Measure (HSPosition 3 × HSPosition 3)).real
          hardSphereSeparatedPairRegion) ^ m * hardSphereKappa ^ q :=
      hardSphereSeparatedBlockProductRegion_volume m q

/-! ### The tree region in difference coordinates -/

lemma hardSphereCoordinateEquiv_apply {k : Nat}
     (r : HardSphereConfiguration k 3)
    (i : Fin (k - 1)) (a : Fin 3) :
    hardSphereCoordinateEquiv k r (i, a) = r i a := by
  rfl

lemma hardSphereTreeDifferenceFlatBlock_eq {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (r : HardSphereConfiguration k 3) (i : Fin (k - 1)) :
    (fun a => hardSphereTreeFlatDifferenceLinearMap hT
      (hardSphereCoordinateEquiv k r) (i, a)) =
      (fun a => hardSphereTreeDifference hT r i a) := by
  by_cases hp : hardSphereTreeParent hT i = 0
  · funext a
    simp [hardSphereTreeFlatDifferenceLinearMap,
      hardSphereParentDifferenceLinearMap_apply,
      hardSphereTreeFlatParent, hardSphereTreeParentFreeIndex, hp,
      hardSphereCoordinateEquiv_apply, hardSphereTreeDifference,
      hardSpherePosition_zero]
  · let p := hardSphereFreeIndex (hardSphereTreeParent hT i) hp
    have hpdef : hardSphereTreeParentFreeIndex hT i = some p := by
      simp [hardSphereTreeParentFreeIndex, hp, p]
    have hpos : hardSpherePosition r (hardSphereTreeParent hT i) = r p := by
      rw [show hardSphereTreeParent hT i = hardSphereFreeParticleIndex p by
        symm
        exact hardSphereFreeParticleIndex_freeIndex
          (hardSphereTreeParent hT i) hp]
      simp
    funext a
    simp [hardSphereTreeFlatDifferenceLinearMap,
      hardSphereParentDifferenceLinearMap_apply,
      hardSphereTreeFlatParent, hpdef, hardSphereCoordinateEquiv_apply,
      hardSphereTreeDifference, hpos, p]

lemma hardSphereTreeRegion_subset_flatDifferencePreimage {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    hardSphereTreeRegion T ⊆
      (fun r => hardSphereTreeFlatDifferenceLinearMap hT
        (hardSphereCoordinateEquiv k r)) ⁻¹'
        hardSphereFlatProductBallRegion (k - 1) := by
  intro r hr i
  rw [mem_ball_iff_norm]
  have hblock := hardSphereTreeDifferenceFlatBlock_eq hT r i
  rw [hblock]
  simpa [sub_zero] using hardSphereTreeDifference_norm_lt_one hT hr i

/-- Send an anchored configuration to its flattened tree-difference coordinates. -/
def hardSphereTreeFlatDifferenceMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    HardSphereConfiguration k 3 → (Fin (k - 1) × Fin 3 → ℝ) :=
  fun r => hardSphereTreeFlatDifferenceLinearMap hT
    (hardSphereCoordinateEquiv k r)

lemma measurePreserving_hardSphereTreeFlatDifferenceMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    MeasurePreserving (hardSphereTreeFlatDifferenceMap hT)
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ)) := by
  let hcoord := measurePreserving_hardSphereCoordinateEquiv k
  let hdiff := measurePreserving_hardSphereTreeFlatDifferenceLinearMap hT
  refine ⟨hdiff.measurable.comp hcoord.measurable, ?_⟩
  change Measure.map
      ((hardSphereTreeFlatDifferenceLinearMap hT) ∘
        (hardSphereCoordinateEquiv k)) volume = volume
  rw [← Measure.map_map hdiff.measurable hcoord.measurable,
    hcoord.map_eq, hdiff.map_eq]

/-- Send an anchored configuration to the Euclidean differences along tree edges. -/
def hardSphereTreeDifferencePositionMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    HardSphereConfiguration k 3 → (Fin (k - 1) → HSPosition 3) :=
  fun r => hardSphereBlockToPositionEquiv (k - 1)
    ((MeasurableEquiv.curry (Fin (k - 1)) (Fin 3) ℝ)
      (hardSphereTreeFlatDifferenceMap hT r))

lemma hardSphereTreeDifferencePositionMap_apply {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k))
    (r : HardSphereConfiguration k 3) (i : Fin (k - 1)) :
    hardSphereTreeDifferencePositionMap hT r i =
      hardSphereTreeDifference hT r i := by
  unfold hardSphereTreeDifferencePositionMap hardSphereBlockToPositionEquiv
    hardSphereTreeFlatDifferenceMap
  change (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => hardSphereTreeFlatDifferenceLinearMap hT
        (hardSphereCoordinateEquiv k r) (i, a)) = _
  rw [hardSphereTreeDifferenceFlatBlock_eq hT r i]
  simp

lemma measurePreserving_hardSphereTreeDifferencePositionMap {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    MeasurePreserving (hardSphereTreeDifferencePositionMap hT)
      (volume : Measure (HardSphereConfiguration k 3))
      (volume : Measure (Fin (k - 1) → HSPosition 3)) := by
  let eCurry := MeasurableEquiv.curry (Fin (k - 1)) (Fin 3) ℝ
  have hCurry : MeasurePreserving eCurry
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ))
      (volume : Measure (Fin (k - 1) → Fin 3 → ℝ)) := by
    exact MeasurePreserving.symm eCurry.symm
      (measurePreserving_curry_pi (μ := (volume : Measure ℝ)))
  let hflat := measurePreserving_hardSphereTreeFlatDifferenceMap hT
  let hblock := measurePreserving_hardSphereBlockToPositionEquiv (k - 1)
  refine ⟨hblock.measurable.comp (hCurry.measurable.comp hflat.measurable), ?_⟩
  change Measure.map
      ((hardSphereBlockToPositionEquiv (k - 1)) ∘
        (eCurry ∘ hardSphereTreeFlatDifferenceMap hT)) volume = volume
  rw [← Measure.map_map hblock.measurable
      (hCurry.measurable.comp hflat.measurable),
    ← Measure.map_map hCurry.measurable hflat.measurable,
    hflat.map_eq, hCurry.map_eq, hblock.map_eq]

lemma hardSphereTreeRegion_volume_le_flatProductBallRegion {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (volume : Measure (HardSphereConfiguration k 3))
        (hardSphereTreeRegion T) ≤
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ))
        (hardSphereFlatProductBallRegion (k - 1)) := by
  let hmap := measurePreserving_hardSphereTreeFlatDifferenceMap hT
  have hsubset := hardSphereTreeRegion_subset_flatDifferencePreimage hT
  calc
    (volume : Measure (HardSphereConfiguration k 3))
        (hardSphereTreeRegion T) ≤
      (volume : Measure (HardSphereConfiguration k 3))
        ((hardSphereTreeFlatDifferenceMap hT) ⁻¹'
          hardSphereFlatProductBallRegion (k - 1)) :=
      measure_mono hsubset
    _ = (Measure.map (hardSphereTreeFlatDifferenceMap hT)
          (volume : Measure (HardSphereConfiguration k 3)))
        (hardSphereFlatProductBallRegion (k - 1)) := by
      rw [Measure.map_apply hmap.measurable
        (measurableSet_hardSphereFlatProductBallRegion (k - 1))]
    _ = (volume : Measure (Fin (k - 1) × Fin 3 → ℝ))
        (hardSphereFlatProductBallRegion (k - 1)) := by
      rw [hmap.map_eq]

lemma hardSphereFlatProductBallRegion_subset_closedBall (n : Nat) :
    hardSphereFlatProductBallRegion n ⊆
      closedBall (0 : Fin n × Fin 3 → ℝ) 1 := by
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ 1)).2
  intro q
  have hblock : (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => x (q.1, a)) ∈ Metric.ball (0 : HSPosition 3) 1 := hx q.1
  have hnorm : ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => x (q.1, a))‖ < (1 : ℝ) := by
    simpa [mem_ball_iff_norm] using hblock
  have hcoord : ‖x q‖ ≤ ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
      (fun a => x (q.1, a))‖ := by
    change ‖(fun a => x (q.1, a)) q.2‖ ≤
      ‖(MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => x (q.1, a))‖
    exact PiLp.norm_apply_le
      ((MeasurableEquiv.toLp 2 (Fin 3 → ℝ))
        (fun a => x (q.1, a))) q.2
  exact hcoord.trans hnorm.le

lemma hardSphereFlatProductBallRegion_measure_ne_top (n : Nat) :
    (volume : Measure (Fin n × Fin 3 → ℝ))
        (hardSphereFlatProductBallRegion n) ≠ ∞ := by
  have hball : (volume : Measure (Fin n × Fin 3 → ℝ))
        (closedBall (0 : Fin n × Fin 3 → ℝ) 1) < ∞ :=
    (isCompact_closedBall (0 : Fin n × Fin 3 → ℝ) 1).measure_lt_top
  exact (lt_of_le_of_lt
    (measure_mono (hardSphereFlatProductBallRegion_subset_closedBall n)) hball).ne

theorem hardSphereTreeRegion_real_volume_le_kappa {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (hardSphereTreeRegion T) ≤ hardSphereKappa ^ (k - 1) := by
  calc
    (volume : Measure (HardSphereConfiguration k 3)).real
        (hardSphereTreeRegion T) ≤
      (volume : Measure (Fin (k - 1) × Fin 3 → ℝ)).real
        (hardSphereFlatProductBallRegion (k - 1)) :=
      ENNReal.toReal_mono
        (hardSphereFlatProductBallRegion_measure_ne_top (k - 1))
        (hardSphereTreeRegion_volume_le_flatProductBallRegion hT)
    _ = hardSphereKappa ^ (k - 1) :=
      hardSphereFlatProductBallRegion_volume (k - 1)

theorem hardSphereNBCRegion_real_volume_le_kappa {k : Nat} [NeZero k]
    {T : Finset (Sym2 (Fin k))}
    (hT : T ∈ treeUniverse (V := Fin k)) :
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      hardSphereKappa ^ (k - 1) := by
  have htree_le := hardSphereTreeRegion_volume_le_flatProductBallRegion hT
  have htree_ne_top :
      (volume : Measure (HardSphereConfiguration k 3))
          (hardSphereTreeRegion T) ≠ ∞ := by
    exact (lt_of_le_of_lt htree_le
      (lt_top_iff_ne_top.mpr
        (hardSphereFlatProductBallRegion_measure_ne_top (k - 1)))).ne
  calc
    (volume : Measure (HardSphereConfiguration k 3)).real
        (nbcRegion (V := Fin k)
          (hardSphereActiveExact (k := k) (d := 3)) T) ≤
      (volume : Measure (HardSphereConfiguration k 3)).real
        (hardSphereTreeRegion T) := by
      apply ENNReal.toReal_mono htree_ne_top
      apply measure_mono
      intro r hr
      exact hardSphere_nbc_region_subset_tree_region hr
    _ ≤ hardSphereKappa ^ (k - 1) :=
      hardSphereTreeRegion_real_volume_le_kappa hT

end

end HsVirial
