/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2

/-!
# Hopf problem: cusp fibre · cusp central homology 2

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private def CuspCentralHomology.suspensionSetoid (X : Type*) : Setoid (unitInterval × X)
    where
  r p q := p.1 = q.1 ∧ (p.1 = 0 ∨ p.1 = 1 ∨ p.2 = q.2)
  iseqv :=
    { refl := fun _ => ⟨rfl, Or.inr (Or.inr rfl)⟩
      symm := by
        rintro p q ⟨ht, h | h | h⟩
        · exact ⟨ht.symm, Or.inl (ht.symm.trans h)⟩
        · exact ⟨ht.symm, Or.inr (Or.inl (ht.symm.trans h))⟩
        · exact ⟨ht.symm, Or.inr (Or.inr h.symm)⟩
      trans := by
        rintro p q r ⟨hpq, hp | hp | hp⟩ ⟨hqr, hq⟩
        · exact ⟨hpq.trans hqr, Or.inl hp⟩
        · exact ⟨hpq.trans hqr, Or.inr (Or.inl hp)⟩
        · rcases hq with hq | hq | hq
          · exact ⟨hpq.trans hqr, Or.inl (hpq.trans hq)⟩
          · exact ⟨hpq.trans hqr, Or.inr (Or.inl (hpq.trans hq))⟩
          · exact ⟨hpq.trans hqr, Or.inr (Or.inr (hp.trans hq))⟩ }

private def CuspCentralHomology.Suspension (X : Type*) :=
  Quotient (suspensionSetoid X)

private instance CuspCentralHomology.instLocal1 {X : Type*} [TopologicalSpace X] :
    TopologicalSpace (Suspension X) :=
  inferInstanceAs (TopologicalSpace (Quotient (suspensionSetoid X)))

private def CuspCentralHomology.Suspension.mk {X : Type*} (t : unitInterval) (x : X) :
    CuspCentralHomology.Suspension X :=
  Quotient.mk (CuspCentralHomology.suspensionSetoid X) (t, x)

private theorem
    CuspCentralHomology.Suspension.mk_eq_mk_iff {X : Type*} (t s : unitInterval) (x y : X) :
    CuspCentralHomology.Suspension.mk t x = CuspCentralHomology.Suspension.mk s y ↔
      t = s ∧ (t = 0 ∨ t = 1 ∨ x = y) :=
  Quotient.eq

private theorem CuspCentralHomology.Suspension.mk_surjective {X : Type*} :
    Function.Surjective (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) :=
  Quotient.mk_surjective

private theorem CuspCentralHomology.Suspension.isQuotientMap_mk {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap
      (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) :=
  isQuotientMap_quotient_mk'

@[continuity, fun_prop]
private theorem CuspCentralHomology.Suspension.continuous_mk {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) :=
  isQuotientMap_mk.continuous

private def CuspCentralHomology.Suspension.height {X : Type*} :
    CuspCentralHomology.Suspension X → unitInterval :=
  Quotient.lift Prod.fst (fun _ _ h => h.1)

@[continuity, fun_prop]
private theorem CuspCentralHomology.Suspension.continuous_height {X : Type*} [TopologicalSpace X] :
    Continuous (height : CuspCentralHomology.Suspension X → _) :=
  isQuotientMap_mk.continuous_iff.mpr continuous_fst

@[continuity, fun_prop]
private theorem
    CuspCentralHomology.Suspension.continuous_realHeight {X : Type*} [TopologicalSpace X] :
    Continuous (fun p : CuspCentralHomology.Suspension X => (height p : ℝ)) :=
  continuous_subtype_val.comp continuous_height

private theorem CuspCentralHomology.Suspension.mk_zero_eq {X : Type*} (x y : X) :
    CuspCentralHomology.Suspension.mk 0 x = CuspCentralHomology.Suspension.mk 0 y :=
  Quotient.sound ⟨rfl, Or.inl rfl⟩

private theorem CuspCentralHomology.Suspension.mk_one_eq {X : Type*} (x y : X) :
    CuspCentralHomology.Suspension.mk 1 x = CuspCentralHomology.Suspension.mk 1 y :=
  Quotient.sound ⟨rfl, Or.inr (Or.inl rfl)⟩

private def CuspCentralHomology.Suspension.northOpen {X : Type*} :
    Set (CuspCentralHomology.Suspension X) :=
  {p | (height p : ℝ) < 3 / 4}

private def CuspCentralHomology.Suspension.southOpen {X : Type*} :
    Set (CuspCentralHomology.Suspension X) :=
  {p | 1 / 4 < (height p : ℝ)}

@[simp]
private theorem CuspCentralHomology.Suspension.mem_northOpen {X : Type*}
    (p : CuspCentralHomology.Suspension X) : p ∈ northOpen ↔ (height p : ℝ) < 3 / 4 :=
  Iff.rfl

@[simp]
private theorem CuspCentralHomology.Suspension.mem_southOpen {X : Type*}
    (p : CuspCentralHomology.Suspension X) : p ∈ southOpen ↔ 1 / 4 < (height p : ℝ) :=
  Iff.rfl

private theorem CuspCentralHomology.Suspension.northOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (northOpen : Set (CuspCentralHomology.Suspension X)) :=
  isOpen_lt continuous_realHeight continuous_const

private theorem CuspCentralHomology.Suspension.southOpen_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (southOpen : Set (CuspCentralHomology.Suspension X)) :=
  isOpen_lt continuous_const continuous_realHeight

private theorem CuspCentralHomology.Suspension.open_cover {X : Type*} :
    (northOpen ∪ southOpen : Set (CuspCentralHomology.Suspension X)) = Set.univ := by
  ext p
  simp only [Set.mem_union, mem_northOpen, mem_southOpen, Set.mem_univ, iff_true]
  by_cases h : (height p : ℝ) < 3 / 4
  · exact Or.inl h
  · exact Or.inr (by linarith)

private def CuspCentralHomology.Suspension.north {X : Type*} [Nonempty X] :
    CuspCentralHomology.Suspension X :=
  CuspCentralHomology.Suspension.mk 0 (Classical.choice ‹Nonempty X›)

private def CuspCentralHomology.Suspension.south {X : Type*} [Nonempty X] :
    CuspCentralHomology.Suspension X :=
  CuspCentralHomology.Suspension.mk 1 (Classical.choice ‹Nonempty X›)

@[simp]
private theorem CuspCentralHomology.Suspension.mk_zero {X : Type*} [Nonempty X] (x : X) :
    CuspCentralHomology.Suspension.mk 0 x = north :=
  mk_zero_eq _ _

@[simp]
private theorem CuspCentralHomology.Suspension.mk_one {X : Type*} [Nonempty X] (x : X) :
    CuspCentralHomology.Suspension.mk 1 x = south :=
  mk_one_eq _ _

private theorem CuspCentralHomology.Suspension.north_mem_northOpen {X : Type*} [Nonempty X] :
    (north : CuspCentralHomology.Suspension X) ∈ northOpen := by
  change (0 : ℝ) < 3 / 4
  norm_num

private theorem CuspCentralHomology.Suspension.south_mem_southOpen {X : Type*} [Nonempty X] :
    (south : CuspCentralHomology.Suspension X) ∈ southOpen := by
  change (1 / 4 : ℝ) < 1
  norm_num

private instance CuspCentralHomology.Suspension.instLocal1 {X : Type*} [Nonempty X] :
    Nonempty (CuspCentralHomology.Suspension X) :=
  ⟨north⟩

private abbrev CuspCentralHomology.Suspension.middleBand (X : Type*) :=
  (northOpen ∩ southOpen : Set (CuspCentralHomology.Suspension X))

private abbrev CuspCentralHomology.Suspension.middleCylinder (X : Type*) :=
  (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) ⁻¹' middleBand X

private theorem CuspCentralHomology.Suspension.middleBand_isOpen {X : Type*} [TopologicalSpace X] :
    IsOpen (middleBand X) :=
  northOpen_isOpen.inter southOpen_isOpen

private theorem CuspCentralHomology.Suspension.middleCylinder_height_mo1973_4378 {X : Type*}
    (p : middleCylinder X) : (1 / 4 : ℝ) < (p.1.1 : ℝ) ∧ (p.1.1 : ℝ) < 3 / 4 :=
  ⟨p.2.2, p.2.1⟩

private theorem CuspCentralHomology.Suspension.middleBand_restrict_injective {X : Type*} :
    Function.Injective
      ((middleBand X).restrictPreimage
        (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2)) := by
  intro p q h
  have hmk :
    CuspCentralHomology.Suspension.mk p.1.1 p.1.2 =
      CuspCentralHomology.Suspension.mk q.1.1 q.1.2 :=
    congrArg Subtype.val h
  obtain ⟨ht, hx⟩ := (mk_eq_mk_iff _ _ _ _).mp hmk
  have hp := middleCylinder_height_mo1973_4378 p
  have hx' : p.1.2 = q.1.2 := by
    rcases hx with h0 | h1 | hx
    · have hz : (p.1.1 : ℝ) = 0 := congrArg Subtype.val h0
      linarith [hp.1]
    · have hz : (p.1.1 : ℝ) = 1 := congrArg Subtype.val h1
      linarith [hp.2]
    · exact hx
  exact Subtype.ext (Prod.ext ht hx')

private def
    CuspCentralHomology.Suspension.middleBandQuotientHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ middleBand X :=
  ((isHomeomorph_iff_isQuotientMap_injective).mpr
        ⟨isQuotientMap_mk.restrictPreimage_isOpen middleBand_isOpen,
          middleBand_restrict_injective⟩).homeomorph
    _

private def
    CuspCentralHomology.Suspension.middleCylinderHomeomorph {X : Type*} [TopologicalSpace X] :
    middleCylinder X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X)
    where
  toFun p := (⟨p.1.1, middleCylinder_height_mo1973_4378 p⟩, p.1.2)
  invFun p := ⟨(⟨p.1, by constructor <;> linarith [p.1.2.1, p.1.2.2]⟩, p.2), p.1.2.2, p.1.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    · exact continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact continuous_subtype_val.comp continuous_fst
    · exact continuous_snd

private def CuspCentralHomology.Suspension.middleBandHomeomorph {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₜ (Set.Ioo (1 / 4 : ℝ) (3 / 4) × X) :=
  middleBandQuotientHomeomorph.symm.trans middleCylinderHomeomorph

private instance CuspCentralHomology.Suspension.middleInterval_contractibleSpace :
    ContractibleSpace (Set.Ioo (1 / 4 : ℝ) (3 / 4)) :=
  (convex_Ioo (1 / 4 : ℝ) (3 / 4)).contractibleSpace ⟨1 / 2, by norm_num⟩

private def
    CuspCentralHomology.Suspension.middleBandHomotopyEquiv {X : Type*} [TopologicalSpace X] :
    middleBand X ≃ₕ X :=
  middleBandHomeomorph.toHomotopyEquiv.trans
    (((Classical.choice (ContractibleSpace.hequiv_unit (Set.Ioo (1 / 4 : ℝ) (3 / 4)))).prodCongr
          (ContinuousMap.HomotopyEquiv.refl X)).trans
      (Homeomorph.uniqueProd Unit X).toHomotopyEquiv)

private theorem
    CuspCentralHomology.Suspension.joined_north {X : Type*} [TopologicalSpace X] [Nonempty X]
    (p : CuspCentralHomology.Suspension X) :
    Joined (north : CuspCentralHomology.Suspension X) p := by
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective p
  refine
    ⟨{  toFun := fun s : unitInterval => CuspCentralHomology.Suspension.mk (s * t) x
        continuous_toFun := by
          apply continuous_mk.comp (f := fun s : unitInterval => (s * t, x))
          apply Continuous.prodMk
          · apply Continuous.subtype_mk
            exact continuous_subtype_val.mul continuous_const
          · exact continuous_const
        source' := by simp
        target' := by simp }⟩

private instance CuspCentralHomology.Suspension.suspension_pathConnectedSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] : PathConnectedSpace (CuspCentralHomology.Suspension X)
    where
  nonempty := inferInstance
  joined p q := (joined_north p).symm.trans (joined_north q)

/-- A choice-based lift of a function along a surjection in its second coordinate. -/
public
def CuspCentralHomology.Suspension.liftFromSurjection {A B S Z : Type*}
    (q : A → B) (hq : Function.Surjective q) (F : S × A → Z) (p : S × B) : Z :=
  F (p.1, Function.surjInv hq p.2)

private theorem CuspCentralHomology.Suspension.liftFromSurjection_comp_mo1973_4392
    {A B S Z : Type*} (q : A → B) (hq : Function.Surjective q) (F : S × A → Z)
    (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (s : S) (a : A) :
    liftFromSurjection q hq F (s, q a) = F (s, a) :=
  hF s _ _ (Function.surjInv_eq hq (q a))

public
theorem CuspCentralHomology.Suspension.liftFromSurjection_continuous_mo1973_4393
    {A B S Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace S]
    [TopologicalSpace Z] [LocallyCompactSpace S] (q : A → B) (hq : Topology.IsQuotientMap q)
    (F : S × A → Z) (hF : ∀ s a b, q a = q b → F (s, a) = F (s, b)) (hcont : Continuous F) :
    Continuous (liftFromSurjection q hq.surjective F) := by
  apply hq.continuous_lift_prod_right
  convert hcont using 1
  funext p
  exact liftFromSurjection_comp_mo1973_4392 q hq.surjective F hF p.1 p.2

private abbrev CuspCentralHomology.Suspension.NorthCylinder_mo1973_4394 (X : Type*)
     :=
  (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) ⁻¹' northOpen

private def CuspCentralHomology.Suspension.northProjection_mo1973_4395 {X : Type*}
     :
    NorthCylinder_mo1973_4394 X → (northOpen : Set (CuspCentralHomology.Suspension X)) :=
  northOpen.restrictPreimage
    (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2)

private theorem CuspCentralHomology.Suspension.northProjection_isQuotientMap_mo1973_4396
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (northProjection_mo1973_4395 (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen northOpen_isOpen

private def CuspCentralHomology.Suspension.northCylinderContraction_mo1973_4397 {X : Type*}
     (p : unitInterval × NorthCylinder_mo1973_4394 X) :
    (northOpen : Set (CuspCentralHomology.Suspension X)) :=
  ⟨CuspCentralHomology.Suspension.mk (unitInterval.symm p.1 * p.2.1.1) p.2.1.2,
    by
    change ((unitInterval.symm p.1 * p.2.1.1 : unitInterval) : ℝ) < 3 / 4
    exact lt_of_le_of_lt unitInterval.mul_le_right p.2.2⟩

private theorem CuspCentralHomology.Suspension.northCylinderContraction_respects_mo1973_4398
    {X : Type*} (s : unitInterval) (a b : NorthCylinder_mo1973_4394 X)
    (h : northProjection_mo1973_4395 a = northProjection_mo1973_4395 b) :
    northCylinderContraction_mo1973_4397 (s, a) = northCylinderContraction_mo1973_4397 (s, b) := by
  apply Subtype.ext
  have hab :
    CuspCentralHomology.Suspension.mk a.1.1 a.1.2 =
      CuspCentralHomology.Suspension.mk b.1.1 b.1.2 :=
    congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    exact
      ⟨congrArg (fun t => unitInterval.symm s * t) ht,
        Or.inl (by rw [hzero, MulZeroClass.mul_zero])⟩
  · have ha : (a.1.1 : ℝ) < 3 / 4 := a.2
    rw [hone] at ha
    norm_num at ha
  · change
      CuspCentralHomology.Suspension.mk (unitInterval.symm s * a.1.1) a.1.2 =
        CuspCentralHomology.Suspension.mk (unitInterval.symm s * b.1.1) b.1.2
    rw [ht, hx]

private theorem CuspCentralHomology.Suspension.northCylinderContraction_continuous_mo1973_4399
    {X : Type*} [TopologicalSpace X] :
    Continuous (northCylinderContraction_mo1973_4397 (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × NorthCylinder_mo1973_4394 X =>
      (unitInterval.symm p.1 * p.2.1.1, p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        (continuous_subtype_val.comp
          (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

private def CuspCentralHomology.Suspension.northContract_mo1973_4400 {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (northOpen : Set (CuspCentralHomology.Suspension X)) →
      (northOpen : Set (CuspCentralHomology.Suspension X)) :=
  liftFromSurjection northProjection_mo1973_4395
    northProjection_isQuotientMap_mo1973_4396.surjective northCylinderContraction_mo1973_4397

private theorem CuspCentralHomology.Suspension.northContract_projection_mo1973_4401 {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : NorthCylinder_mo1973_4394 X) :
    northContract_mo1973_4400 (s, northProjection_mo1973_4395 a) =
      northCylinderContraction_mo1973_4397 (s, a) :=
  liftFromSurjection_comp_mo1973_4392 _ _ _ northCylinderContraction_respects_mo1973_4398 s a

private theorem CuspCentralHomology.Suspension.northContract_continuous_mo1973_4402 {X : Type*}
    [TopologicalSpace X] : Continuous (northContract_mo1973_4400 (X := X)) :=
  liftFromSurjection_continuous_mo1973_4393 _ northProjection_isQuotientMap_mo1973_4396 _
    northCylinderContraction_respects_mo1973_4398 northCylinderContraction_continuous_mo1973_4399

private def CuspCentralHomology.Suspension.northContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (northOpen : Set (CuspCentralHomology.Suspension X)))
      (ContinuousMap.const _ ⟨north, north_mem_northOpen⟩)
    where
  toFun := northContract_mo1973_4400
  continuous_toFun := northContract_continuous_mo1973_4402
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap_mo1973_4396.surjective q
    rw [northContract_projection_mo1973_4401]
    apply Subtype.ext
    change
      CuspCentralHomology.Suspension.mk (unitInterval.symm 0 * a.1.1) a.1.2 =
        CuspCentralHomology.Suspension.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := northProjection_isQuotientMap_mo1973_4396.surjective q
    rw [northContract_projection_mo1973_4401]
    apply Subtype.ext
    change CuspCentralHomology.Suspension.mk (unitInterval.symm 1 * a.1.1) a.1.2 = north
    simp

private instance CuspCentralHomology.Suspension.northOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (northOpen : Set (CuspCentralHomology.Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨north, north_mem_northOpen⟩, ⟨northContraction⟩⟩

private abbrev CuspCentralHomology.Suspension.SouthCylinder_mo1973_4406 (X : Type*)
     :=
  (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2) ⁻¹' southOpen

private def CuspCentralHomology.Suspension.southProjection_mo1973_4407 {X : Type*}
     :
    SouthCylinder_mo1973_4406 X → (southOpen : Set (CuspCentralHomology.Suspension X)) :=
  southOpen.restrictPreimage
    (fun p : unitInterval × X => CuspCentralHomology.Suspension.mk p.1 p.2)

private theorem CuspCentralHomology.Suspension.southProjection_isQuotientMap_mo1973_4408
    {X : Type*} [TopologicalSpace X] :
    Topology.IsQuotientMap (southProjection_mo1973_4407 (X := X)) :=
  isQuotientMap_mk.restrictPreimage_isOpen southOpen_isOpen

private def CuspCentralHomology.Suspension.southCylinderContraction_mo1973_4409 {X : Type*}
     (p : unitInterval × SouthCylinder_mo1973_4406 X) :
    (southOpen : Set (CuspCentralHomology.Suspension X)) :=
  ⟨CuspCentralHomology.Suspension.mk
      (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1)) p.2.1.2,
    by
    change
      1 / 4 <
        ((unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) : unitInterval) :
          ℝ)
    have hle : unitInterval.symm p.1 * unitInterval.symm p.2.1.1 ≤ unitInterval.symm p.2.1.1 :=
      unitInterval.mul_le_right
    have hbound :
      p.2.1.1 ≤ unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1) :=
      unitInterval.le_symm_comm.mpr hle
    exact lt_of_lt_of_le p.2.2 hbound⟩

private theorem CuspCentralHomology.Suspension.southCylinderContraction_respects_mo1973_4410
    {X : Type*} (s : unitInterval) (a b : SouthCylinder_mo1973_4406 X)
    (h : southProjection_mo1973_4407 a = southProjection_mo1973_4407 b) :
    southCylinderContraction_mo1973_4409 (s, a) = southCylinderContraction_mo1973_4409 (s, b) := by
  apply Subtype.ext
  have hab :
    CuspCentralHomology.Suspension.mk a.1.1 a.1.2 =
      CuspCentralHomology.Suspension.mk b.1.1 b.1.2 :=
    congrArg Subtype.val h
  rcases (mk_eq_mk_iff _ _ _ _).mp hab with ⟨ht, hzero | hone | hx⟩
  · have ha : 1 / 4 < (a.1.1 : ℝ) := a.2
    rw [hzero] at ha
    norm_num at ha
  · apply (mk_eq_mk_iff _ _ _ _).mpr
    refine
      ⟨congrArg (fun t => unitInterval.symm (unitInterval.symm s * unitInterval.symm t)) ht,
        Or.inr (Or.inl ?_)⟩
    simp [hone]
  · change
      CuspCentralHomology.Suspension.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm a.1.1)) a.1.2 =
        CuspCentralHomology.Suspension.mk
          (unitInterval.symm (unitInterval.symm s * unitInterval.symm b.1.1)) b.1.2
    rw [ht, hx]

private theorem CuspCentralHomology.Suspension.southCylinderContraction_continuous_mo1973_4411
    {X : Type*} [TopologicalSpace X] :
    Continuous (southCylinderContraction_mo1973_4409 (X := X)) := by
  apply Continuous.subtype_mk
  apply
    continuous_mk.comp (f := fun p : unitInterval × SouthCylinder_mo1973_4406 X =>
      (unitInterval.symm (unitInterval.symm p.1 * unitInterval.symm p.2.1.1), p.2.1.2))
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact
      continuous_const.sub
        ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
          (continuous_const.sub
            (continuous_subtype_val.comp
              (continuous_fst.comp (continuous_subtype_val.comp continuous_snd)))))
  · exact continuous_snd.comp (continuous_subtype_val.comp continuous_snd)

private def CuspCentralHomology.Suspension.southContract_mo1973_4412 {X : Type*}
    [TopologicalSpace X] :
    unitInterval × (southOpen : Set (CuspCentralHomology.Suspension X)) →
      (southOpen : Set (CuspCentralHomology.Suspension X)) :=
  liftFromSurjection southProjection_mo1973_4407
    southProjection_isQuotientMap_mo1973_4408.surjective southCylinderContraction_mo1973_4409

private theorem CuspCentralHomology.Suspension.southContract_projection_mo1973_4413 {X : Type*}
    [TopologicalSpace X] (s : unitInterval) (a : SouthCylinder_mo1973_4406 X) :
    southContract_mo1973_4412 (s, southProjection_mo1973_4407 a) =
      southCylinderContraction_mo1973_4409 (s, a) :=
  liftFromSurjection_comp_mo1973_4392 _ _ _ southCylinderContraction_respects_mo1973_4410 s a

private theorem CuspCentralHomology.Suspension.southContract_continuous_mo1973_4414 {X : Type*}
    [TopologicalSpace X] : Continuous (southContract_mo1973_4412 (X := X)) :=
  liftFromSurjection_continuous_mo1973_4393 _ southProjection_isQuotientMap_mo1973_4408 _
    southCylinderContraction_respects_mo1973_4410 southCylinderContraction_continuous_mo1973_4411

private def CuspCentralHomology.Suspension.southContraction {X : Type*} [TopologicalSpace X]
    [Nonempty X] :
    ContinuousMap.Homotopy (ContinuousMap.id (southOpen : Set (CuspCentralHomology.Suspension X)))
      (ContinuousMap.const _ ⟨south, south_mem_southOpen⟩)
    where
  toFun := southContract_mo1973_4412
  continuous_toFun := southContract_continuous_mo1973_4414
  map_zero_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap_mo1973_4408.surjective q
    rw [southContract_projection_mo1973_4413]
    apply Subtype.ext
    change
      CuspCentralHomology.Suspension.mk
          (unitInterval.symm (unitInterval.symm 0 * unitInterval.symm a.1.1)) a.1.2 =
        CuspCentralHomology.Suspension.mk a.1.1 a.1.2
    simp
  map_one_left
    q := by
    obtain ⟨a, rfl⟩ := southProjection_isQuotientMap_mo1973_4408.surjective q
    rw [southContract_projection_mo1973_4413]
    apply Subtype.ext
    change
      CuspCentralHomology.Suspension.mk
          (unitInterval.symm (unitInterval.symm 1 * unitInterval.symm a.1.1)) a.1.2 =
        south
    simp

private instance CuspCentralHomology.Suspension.southOpen_contractibleSpace {X : Type*}
    [TopologicalSpace X] [Nonempty X] :
    ContractibleSpace (southOpen : Set (CuspCentralHomology.Suspension X)) :=
  (contractible_iff_id_nullhomotopic _).mpr ⟨⟨south, south_mem_southOpen⟩, ⟨southContraction⟩⟩

@[simp]
private theorem CuspCentralHomology.Suspension.middleBandHomotopyEquiv_apply {X : Type*}
    [TopologicalSpace X] (p : middleBand X) :
    middleBandHomotopyEquiv p = (middleBandHomeomorph p).2 :=
  rfl

private instance
    CuspCentralHomology.Suspension.suspension_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X] : CompactSpace (CuspCentralHomology.Suspension X) :=
  mk_surjective.compactSpace continuous_mk

private theorem
    CuspCentralHomology.contractibleCoverConnecting_injective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    Function.Injective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover n) := by
  let :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  apply LinearMap.ker_eq_bot.mp
  rw [← SingularMayerVietoris.exact_at_ambient U V hU hV hcover n]
  apply LinearMap.range_eq_bot.mpr
  apply LinearMap.ext
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  rw [ha, map_zero, LinearMap.zero_apply]

private theorem
    CuspCentralHomology.contractibleCoverConnecting_surjective {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    Function.Surjective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover (n + 1)) :=
  by
  let :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton U (n + 1) (Nat.succ_ne_zero _)
  let :=
    PeriodTorusHigherHomology.contractible_homology_subsingleton V (n + 1) (Nat.succ_ne_zero _)
  intro a
  have ha : a ∈ LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V (n + 1)) := by
    exact Subsingleton.elim _ _
  rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover (n + 1)] at ha
  exact ha

private def CuspCentralHomology.contractibleCoverHomologyHigherEquiv {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] (n : ℕ) :
    SingularMayerVietoris.SingularHomology X (n + 2) ≃ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (U ∩ V : Set X) (n + 1) :=
  LinearEquiv.ofBijective (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover (n + 1))
    ⟨contractibleCoverConnecting_injective U V hU hV hcover (n + 1),
      contractibleCoverConnecting_surjective U V hU hV hcover n⟩

private def CuspCentralHomology.contractibleCoverConnectingToKernel {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    SingularMayerVietoris.SingularHomology X 1 →ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) :=
  PeriodTorusHigherHomology.intLinearMapOfAddHom
    ((SingularMayerVietoris.connectingHomomorphism U V hU hV hcover 0).codRestrict
        (LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0))
        (by
          intro a
          rw [← SingularMayerVietoris.exact_at_intersection U V hU hV hcover 0]
          exact ⟨a, rfl⟩)).toAddMonoidHom

private theorem CuspCentralHomology.contractibleCoverConnectingToKernel_bijective {X : Type}
    [TopologicalSpace X] (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] :
    Function.Bijective (contractibleCoverConnectingToKernel U V hU hV hcover) := by
  constructor
  · intro a b hab
    apply contractibleCoverConnecting_injective U V hU hV hcover 0
    exact congrArg Subtype.val hab
  · intro a
    have ha :
      (a : SingularMayerVietoris.SingularHomology (U ∩ V : Set X) 0) ∈
        LinearMap.range (SingularMayerVietoris.connectingHomomorphism U V hU hV hcover 0) :=
      (SingularMayerVietoris.exact_at_intersection U V hU hV hcover 0).symm.le a.property
    obtain ⟨b, hb⟩ := ha
    exact ⟨b, Subtype.ext hb⟩

private def
    CuspCentralHomology.contractibleCoverHomologyOneEquivKernel {X : Type} [TopologicalSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ)
    [ContractibleSpace U] [ContractibleSpace V] :
    SingularMayerVietoris.SingularHomology X 1 ≃ₗ[ℤ]
      LinearMap.ker (SingularMayerVietoris.leftHomologyMap U V 0) :=
  LinearEquiv.ofBijective (contractibleCoverConnectingToKernel U V hU hV hcover)
    (contractibleCoverConnectingToKernel_bijective U V hU hV hcover)

end Mathoverflow1973

end
