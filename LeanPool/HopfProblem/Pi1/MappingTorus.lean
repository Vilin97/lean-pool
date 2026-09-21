/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Threefold.SpecialPeriods2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods2

/-!
# Hopf problem: pi 1 · mapping torus

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

private abbrev MappingTorus.Circle :=
  AddCircle (1 : ℝ)

private def
    MappingTorus.deck {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) : ℝ × X :=
  (p.1 + (n : ℝ), (f ^ (-n)) p.2)

@[simp]
private theorem MappingTorus.deck_zero {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) :
    deck f 0 p = p := by simp [deck]

private theorem MappingTorus.deck_add {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (m n : ℤ)
    (p : ℝ × X) : deck f (m + n) p = deck f m (deck f n p) := by
  apply Prod.ext
  · simp only [deck, Int.cast_add]
    abel
  · simp only [deck, neg_add, zpow_add, Homeomorph.mul_apply]

private theorem MappingTorus.deck_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) :
    Continuous (deck f n) :=
  (continuous_fst.add continuous_const).prodMk ((f ^ (-n)).continuous.comp continuous_snd)

private def MappingTorus.deckHomeomorph {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) :
    (ℝ × X) ≃ₜ (ℝ × X) where
  toFun := deck f n
  invFun := deck f (-n)
  left_inv p := by rw [← deck_add, neg_add_cancel, deck_zero]
  right_inv p := by rw [← deck_add, add_neg_cancel, deck_zero]
  continuous_toFun := deck_continuous f n
  continuous_invFun := deck_continuous f (-n)

private def MappingTorus.orbitSetoid {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) : Setoid (ℝ × X)
    where
  r p q := ∃ n : ℤ, deck f n p = q
  iseqv :=
    { refl := fun p ↦ ⟨0, deck_zero f p⟩
      symm := by
        rintro p q ⟨n, rfl⟩
        exact ⟨-n, by rw [← deck_add, neg_add_cancel, deck_zero]⟩
      trans := by
        rintro p q r ⟨m, rfl⟩ ⟨n, rfl⟩
        exact ⟨n + m, deck_add f n m p⟩ }

private def MappingTorus.Torus {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :=
  Quotient (orbitSetoid f)

private instance MappingTorus.instLocal1 {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    TopologicalSpace (Torus f) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid f)))

private def MappingTorus.mk {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) : Torus f :=
  Quotient.mk (orbitSetoid f) p

private theorem MappingTorus.mk_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    Continuous (MappingTorus.mk f) :=
  continuous_quotient_mk'

private theorem MappingTorus.mk_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    Function.Surjective (MappingTorus.mk f) :=
  Quotient.mk_surjective

private theorem
    MappingTorus.mk_eq_mk_iff {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p q : ℝ × X) :
    MappingTorus.mk f p = MappingTorus.mk f q ↔
      ∃ n : ℤ, q.1 = p.1 + (n : ℝ) ∧ q.2 = (f ^ (-n)) p.2 := by
  change (Quotient.mk (orbitSetoid f) p = Quotient.mk (orbitSetoid f) q) ↔ _
  rw [Quotient.eq]
  change (∃ n : ℤ, deck f n p = q) ↔ _
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, (congrArg Prod.fst hn).symm, (congrArg Prod.snd hn).symm⟩
  · rintro ⟨n, ht, hx⟩
    exact ⟨n, Prod.ext ht.symm hx.symm⟩

@[simp]
private theorem
    MappingTorus.mk_deck {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (n : ℤ) (p : ℝ × X) :
    MappingTorus.mk f (deck f n p) = MappingTorus.mk f p :=
  (Quotient.sound (s := orbitSetoid f) ⟨n, rfl⟩).symm

@[simp]
private theorem
    MappingTorus.mk_sub_one {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (t : ℝ) (x : X) :
    MappingTorus.mk f (t - 1, f x) = MappingTorus.mk f (t, x) := by
  simpa [deck, sub_eq_add_neg] using mk_deck f (-1) (t, x)

private theorem
    MappingTorus.mk_add_one {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (t : ℝ) (x : X) :
    MappingTorus.mk f (t + 1, x) = MappingTorus.mk f (t, f x) := by
  simpa using (mk_sub_one f (t + 1) x).symm

private theorem MappingTorus.mk_preimage_image {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (s : Set (ℝ × X)) : MappingTorus.mk f ⁻¹' (MappingTorus.mk f '' s) = ⋃ n : ℤ, deck f n '' s :=
  by
  ext p
  constructor
  · rintro ⟨q, hq, he⟩
    obtain ⟨n, hn⟩ := Quotient.exact he
    exact Set.mem_iUnion.mpr ⟨n, q, hq, hn⟩
  · intro hp
    obtain ⟨n, q, hq, rfl⟩ := Set.mem_iUnion.mp hp
    exact ⟨q, hq, (mk_deck f n q).symm⟩

private theorem MappingTorus.mk_open {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpenMap (MappingTorus.mk f) := by
  intro s hs
  apply (isQuotientMap_quotient_mk' (s := orbitSetoid f)).isOpen_preimage.mp
  change IsOpen (MappingTorus.mk f ⁻¹' (MappingTorus.mk f '' s))
  rw [mk_preimage_image]
  exact isOpen_iUnion fun n ↦ (deckHomeomorph f n).isOpenMap s hs

@[simp]
private theorem MappingTorus.circle_intCast (n : ℤ) : ((n : ℝ) : MappingTorus.Circle) = 0 := by
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  exact ⟨n, by simp⟩

private theorem MappingTorus.circle_coe_eq_iff (t s : ℝ) :
    (t : MappingTorus.Circle) = (s : MappingTorus.Circle) ↔ ∃ n : ℤ, s = t + (n : ℝ) := by
  constructor
  · intro h
    have hs : ((s - t : ℝ) : MappingTorus.Circle) = 0 := by rw [AddCircle.coe_sub, h, sub_self]
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hs
    refine ⟨n, ?_⟩
    simp only [zsmul_eq_mul, mul_one] at hn
    linarith
  · rintro ⟨n, rfl⟩
    simp

private def MappingTorus.base {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(Torus f, MappingTorus.Circle)
    where
  toFun :=
    Quotient.lift (fun p : ℝ × X ↦ (p.1 : MappingTorus.Circle))
      (by
        rintro p q ⟨n, rfl⟩
        simp [deck])
  continuous_toFun := (AddCircle.continuous_mk' (1 : ℝ)).comp continuous_fst |>.quotient_lift _

@[simp]
private theorem MappingTorus.base_mk {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (p : ℝ × X) :
    base f (MappingTorus.mk f p) = (p.1 : MappingTorus.Circle) :=
  rfl

/-- The torus monodromy used for the cusp boundary mapping torus. -/
public
abbrev ThreefoldOverlapMappingTorus.Cusp.monodromy : RealTorus₄ ≃ₜ RealTorus₄ :=
  SpecialPeriods.CuspFamily.cuspTorusHomeomorph 1

private abbrev ThreefoldOverlapMappingTorus.Cusp.Boundary :=
  MappingTorus.Torus monodromy

private def ThreefoldOverlapMappingTorus.Cusp.monodromyHom_mo1973_10002 :
    Multiplicative ℤ →* (RealTorus₄ ≃ₜ RealTorus₄)
    where
  toFun k := SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd
  map_one' := SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_eq
  map_mul' k
    l := by
    apply Homeomorph.ext
    exact SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply k.toAdd l.toAdd

private theorem ThreefoldOverlapMappingTorus.Cusp.monodromy_zpow (k : ℤ) :
    monodromy ^ k = SpecialPeriods.CuspFamily.cuspTorusHomeomorph k := by
  have h := map_zpow monodromyHom_mo1973_10002 (Multiplicative.ofAdd (1 : ℤ)) k
  change
    SpecialPeriods.CuspFamily.cuspTorusHomeomorph (((Multiplicative.ofAdd (1 : ℤ)) ^ k).toAdd) =
      monodromy ^ k at h
  simpa using h.symm

private def ThreefoldOverlapMappingTorus.Cusp.heightThreshold (r : ℝ) : ℝ :=
  -Real.log r / (2 * Real.pi)

private abbrev ThreefoldOverlapMappingTorus.Cusp.Height (r : ℝ) :=
  Set.Ioi (heightThreshold r)

private theorem
    ThreefoldOverlapMappingTorus.Cusp.mem_logBase_iff_height (r : ℝ) (hr : 0 < r) (s : ℂ) :
    s ∈ SpecialPeriods.CuspFamily.logBase r ↔ heightThreshold r < s.im := by
  simpa only [SpecialPeriods.CuspFamily.mem_logBase, CuspUniformization.mem_logDomain,
    heightThreshold] using (CuspUniformization.mem_logDomain_iff_im r hr (s, (0 : ComplexPlane₂)))

private def ThreefoldOverlapMappingTorus.Cusp.logPoint (r : ℝ) (hr : 0 < r) (t : ℝ) (h : Height r) :
    SpecialPeriods.CuspFamily.LogBase r :=
  ⟨(t : ℂ) + (h : ℝ) * Complex.I,
    (mem_logBase_iff_height r hr _).mpr
      (by
        simpa only [Height, Set.mem_Ioi, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, MulZeroClass.mul_zero, zero_add,
          add_zero] using h.property)⟩

@[simp]
private theorem ThreefoldOverlapMappingTorus.Cusp.logPoint_re (r : ℝ) (hr : 0 < r) (t : ℝ)
    (h : Height r) : (logPoint r hr t h : ℂ).re = t := by simp [logPoint]

@[simp]
private theorem ThreefoldOverlapMappingTorus.Cusp.logPoint_im (r : ℝ) (hr : 0 < r) (t : ℝ)
    (h : Height r) : (logPoint r hr t h : ℂ).im = (h : ℝ) := by simp [logPoint]

private def ThreefoldOverlapMappingTorus.Cusp.logBaseHeightHomeomorph (r : ℝ) (hr : 0 < r) :
    SpecialPeriods.CuspFamily.LogBase r ≃ₜ Height r × ℝ
    where
  toFun s := (⟨(s : ℂ).im, (mem_logBase_iff_height r hr s).mp s.property⟩, (s : ℂ).re)
  invFun p := logPoint r hr p.2 p.1
  left_inv
    s := by
    apply Subtype.ext
    apply Complex.ext <;> simp [logPoint]
  right_inv
    p := by
    apply Prod.ext
    · apply Subtype.ext
      exact logPoint_im r hr p.2 p.1
    · exact logPoint_re r hr p.2 p.1
  continuous_toFun :=
    ((Complex.continuous_im.comp continuous_subtype_val).subtype_mk _).prodMk
      (Complex.continuous_re.comp continuous_subtype_val)
  continuous_invFun :=
    ((Complex.continuous_ofReal.comp continuous_snd).add
          ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_fst)).mul
            continuous_const)).subtype_mk
      _

private theorem
    ThreefoldOverlapMappingTorus.Cusp.logPoint_translate (r : ℝ) (hr : 0 < r) (k : ℤ) (t : ℝ)
    (h : Height r) :
    SpecialPeriods.CuspFamily.logBaseTranslate r k (logPoint r hr t h) =
      logPoint r hr (t - (k : ℝ)) h := by
  apply Subtype.ext
  change (t : ℂ) + (h : ℝ) * Complex.I - (k : ℂ) = ((t - (k : ℝ) : ℝ) : ℂ) + (h : ℝ) * Complex.I
  push_cast
  ring

private def ThreefoldOverlapMappingTorus.Cusp.familyCylinderHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) : D.TotalSpace ≃ₜ Height D.radius × (ℝ × RealTorus₄) :=
  ((logBaseHeightHomeomorph D.radius D.radius_pos).prodCongr (Homeomorph.refl RealTorus₄)).trans
    (Homeomorph.prodAssoc (Height D.radius) ℝ RealTorus₄)

private theorem ThreefoldOverlapMappingTorus.Cusp.familyCylinderHomeomorph_smul
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    familyCylinderHomeomorph D (k • x) =
      ((familyCylinderHomeomorph D x).1,
        MappingTorus.deck monodromy (-k.toAdd) (familyCylinderHomeomorph D x).2) := by
  let := D.totalAction
  apply Prod.ext
  · apply Subtype.ext
    change ((x.1 : ℂ) - (k.toAdd : ℂ)).im = (x.1 : ℂ).im
    simp
  · apply Prod.ext
    · change ((x.1 : ℂ) - (k.toAdd : ℂ)).re = (x.1 : ℂ).re + ((-k.toAdd : ℤ) : ℝ)
      simp [sub_eq_add_neg]
    · change
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph k.toAdd x.2 =
          (monodromy ^ (-(-k.toAdd))) x.2
      rw [neg_neg, monodromy_zpow]

private def ThreefoldOverlapMappingTorus.Cusp.commonQuotientHomeomorph_mo1973_10028
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] (f : A → X)
    (g : A → Y) (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) : X ≃ₜ Y := by
  let e : X ≃ Y :=
    Equiv.ofBijective (CuspHoneycombHexagon.CommonFibres.descend f g hf.surjective)
      ⟨CuspHoneycombHexagon.CommonFibres.descend_injective f g hf.surjective
          (fun a b => (he a b).mpr),
        CuspHoneycombHexagon.CommonFibres.descend_surjective f g hf.surjective
          (fun a b => (he a b).mp) hg.surjective⟩
  refine
    { toEquiv := e
      continuous_toFun :=
        CuspHoneycombHexagon.CommonFibres.descend_continuous f g hf.surjective hf hg.continuous
          (fun a b => (he a b).mp)
      continuous_invFun := ?_ }
  apply hg.continuous_iff.mpr
  change Continuous (e.symm ∘ g)
  have hcomp : e.symm ∘ g = f := by
    funext a
    apply e.injective
    change e (e.symm (g a)) = e (f a)
    rw [e.apply_symm_apply]
    exact
      (CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (he a b).mp)
          a).symm
  rw [hcomp]
  exact hf.continuous

private theorem ThreefoldOverlapMappingTorus.Cusp.commonQuotientHomeomorph_apply_mo1973_10029
    {A X Y : Type*} [TopologicalSpace A] [TopologicalSpace X] [TopologicalSpace Y] (f : A → X)
    (g : A → Y) (hf : Topology.IsQuotientMap f) (hg : Topology.IsQuotientMap g)
    (he : ∀ a b, f a = f b ↔ g a = g b) (a : A) :
    commonQuotientHomeomorph_mo1973_10028 f g hf hg he (f a) = g a :=
  CuspHoneycombHexagon.CommonFibres.descend_apply f g hf.surjective (fun a b => (he a b).mp) a

private def ThreefoldOverlapMappingTorus.Cusp.cylinderProjection (r : ℝ) :
    C(Height r × (ℝ × RealTorus₄), Height r × Boundary) :=
  ⟨Prod.map id (MappingTorus.mk monodromy),
    continuous_id.prodMap (MappingTorus.mk_continuous monodromy)⟩

private theorem ThreefoldOverlapMappingTorus.Cusp.cylinderProjection_isOpenQuotientMap (r : ℝ) :
    IsOpenQuotientMap (cylinderProjection r) :=
  IsOpenQuotientMap.id.prodMap
    ⟨MappingTorus.mk_surjective monodromy, MappingTorus.mk_continuous monodromy,
      MappingTorus.mk_open monodromy⟩

private def
    ThreefoldOverlapMappingTorus.Cusp.familyProductMap (D : SpecialPeriods.CuspFamily.Data) :
    C(D.TotalSpace, Height D.radius × Boundary) :=
  (cylinderProjection D.radius).comp
    ⟨familyCylinderHomeomorph D, (familyCylinderHomeomorph D).continuous⟩

private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_isOpenQuotientMap
    (D : SpecialPeriods.CuspFamily.Data) : IsOpenQuotientMap (familyProductMap D) :=
  (cylinderProjection_isOpenQuotientMap D.radius).comp
    (familyCylinderHomeomorph D).isOpenQuotientMap

private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_smul
    (D : SpecialPeriods.CuspFamily.Data) (k : Multiplicative ℤ) (x : D.TotalSpace) :
    letI := D.totalAction
    familyProductMap D (k • x) = familyProductMap D x := by
  let := D.totalAction
  change Prod.map id (MappingTorus.mk monodromy) (familyCylinderHomeomorph D (k • x)) = _
  rw [familyCylinderHomeomorph_smul]
  exact Prod.ext rfl (MappingTorus.mk_deck monodromy (-k.toAdd) _)

private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_eq_iff
    (D : SpecialPeriods.CuspFamily.Data) (x y : D.TotalSpace) :
    familyProductMap D x = familyProductMap D y ↔ D.quotient x = D.quotient y := by
  let := D.totalAction
  constructor
  · intro h
    have hheight : (x.1 : ℂ).im = (y.1 : ℂ).im :=
      congrArg (fun p : Height D.radius × Boundary => (p.1 : ℝ)) h
    have htime := congrArg Prod.snd h
    change
      MappingTorus.mk monodromy ((x.1 : ℂ).re, x.2) =
        MappingTorus.mk monodromy ((y.1 : ℂ).re, y.2) at htime
    obtain ⟨n, ht, hx⟩ := (MappingTorus.mk_eq_mk_iff monodromy _ _).mp htime
    apply (D.quotient_eq_iff x y).mpr
    refine ⟨Multiplicative.ofAdd n, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Complex.ext
      · change ((y.1 : ℂ) - (n : ℂ)).re = (x.1 : ℂ).re
        change (y.1 : ℂ).re = (x.1 : ℂ).re + (n : ℝ) at ht
        simp only [Complex.sub_re, Complex.intCast_re]
        linarith
      · change ((y.1 : ℂ) - (n : ℂ)).im = (x.1 : ℂ).im
        simpa only [Complex.sub_im, Complex.intCast_im, sub_zero] using hheight.symm
    · change SpecialPeriods.CuspFamily.cuspTorusHomeomorph n y.2 = x.2
      change y.2 = (monodromy ^ (-n)) x.2 at hx
      rw [monodromy_zpow] at hx
      rw [hx, ← SpecialPeriods.CuspFamily.cuspTorusHomeomorph_add_apply, add_neg_cancel,
        SpecialPeriods.CuspFamily.cuspTorusHomeomorph_zero_apply]
  · intro h
    obtain ⟨k, hk⟩ := (D.quotient_eq_iff x y).mp h
    rw [← hk, familyProductMap_smul]

private theorem ThreefoldOverlapMappingTorus.Cusp.familyQuotient_isQuotientMap
    (D : SpecialPeriods.CuspFamily.Data) : Topology.IsQuotientMap D.quotient := by
  let := D.totalAction
  exact D.quotientCoveringMap.toIsQuotientMap

private def ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) : D.Space ≃ₜ Height D.radius × Boundary :=
  commonQuotientHomeomorph_mo1973_10028 D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D) (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm)

@[simp]
private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_quotient
    (D : SpecialPeriods.CuspFamily.Data) (x : D.TotalSpace) :
    familyProductHomeomorph D (D.quotient x) = familyProductMap D x :=
  commonQuotientHomeomorph_apply_mo1973_10029 D.quotient (familyProductMap D)
    (familyQuotient_isQuotientMap D) (familyProductMap_isOpenQuotientMap D).isQuotientMap
    (fun x y => (familyProductMap_eq_iff D x y).symm) x

private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductMap_logPoint
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    familyProductMap D (logPoint D.radius D.radius_pos t h, x) =
      (h, MappingTorus.mk monodromy (t, x)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact logPoint_im D.radius D.radius_pos t h
  · change MappingTorus.mk monodromy ((logPoint D.radius D.radius_pos t h : ℂ).re, x) = _
    rw [logPoint_re]

private theorem ThreefoldOverlapMappingTorus.Cusp.familyProductHomeomorph_symm_mk
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    (familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x)) =
      D.quotient (logPoint D.radius D.radius_pos t h, x) := by
  simpa only [familyProductHomeomorph_quotient, familyProductMap_logPoint] using
    (familyProductHomeomorph D).symm_apply_apply
      (D.quotient (logPoint D.radius D.radius_pos t h, x))

private theorem
    MappingTorus.base_mk_ne_of_mem_Ioo {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ)
    (t : Set.Ioo a (a + 1)) (x : X) :
    base f (MappingTorus.mk f ((t : ℝ), x)) ≠ (a : MappingTorus.Circle) :=
  (AddCircle.openPartialHomeomorphCoe (1 : ℝ) a).map_source t.property

private def MappingTorus.intervalParam {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ)
    (p : Set.Ioo a (a + 1) × X) : { q : Torus f // base f q ≠ (a : MappingTorus.Circle) } :=
  ⟨MappingTorus.mk f ((p.1 : ℝ), p.2), base_mk_ne_of_mem_Ioo f a p.1 p.2⟩

private theorem MappingTorus.intervalParam_continuous {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Continuous (intervalParam f a) :=
  ((mk_continuous f).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk
    _

private theorem
    MappingTorus.intervalParam_open {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ) :
    IsOpenMap (intervalParam f a) :=
  ((mk_open f).comp (isOpen_Ioo.isOpenMap_subtype_val.prodMap IsOpenMap.id)).subtype_mk _

private theorem MappingTorus.intervalParam_injective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Function.Injective (intervalParam f a) := by
  intro p q hpq
  have he : MappingTorus.mk f ((p.1 : ℝ), p.2) = MappingTorus.mk f ((q.1 : ℝ), q.2) :=
    congrArg Subtype.val hpq
  have hc : ((p.1 : ℝ) : MappingTorus.Circle) = ((q.1 : ℝ) : MappingTorus.Circle) :=
    congrArg (base f) he
  have ht : (p.1 : ℝ) = (q.1 : ℝ) :=
    (AddCircle.coe_eq_coe_iff_of_mem_Ico (Set.Ioo_subset_Ico_self p.1.property)
          (Set.Ioo_subset_Ico_self q.1.property)).mp
      hc
  obtain ⟨n, hn, hx⟩ := (mk_eq_mk_iff f _ _).mp he
  have hnR : (n : ℝ) = 0 := by
    dsimp at hn
    linarith
  have hn0 : n = 0 := Int.cast_eq_zero.mp hnR
  apply Prod.ext (Subtype.ext ht)
  simpa [hn0] using hx.symm

private theorem MappingTorus.intervalParam_surjective {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) : Function.Surjective (intervalParam f a) := by
  intro q
  obtain ⟨⟨s, x⟩, hp⟩ := mk_surjective f q.val
  let e := AddCircle.openPartialHomeomorphCoe (1 : ℝ) a
  let t : Set.Ioo a (a + 1) := ⟨e.symm (base f q.val), e.map_target q.property⟩
  have ht : ((t : ℝ) : MappingTorus.Circle) = base f q.val := e.right_inv q.property
  have hst : (s : MappingTorus.Circle) = ((t : ℝ) : MappingTorus.Circle) :=
    (congrArg (base f) hp).trans ht.symm
  obtain ⟨n, hn⟩ := (circle_coe_eq_iff s (t : ℝ)).mp hst
  refine ⟨(t, (f ^ (-n)) x), Subtype.ext ?_⟩
  change MappingTorus.mk f ((t : ℝ), (f ^ (-n)) x) = q.val
  rw [hn]
  exact (mk_deck f n (s, x)).trans hp

private def MappingTorus.intervalHomeomorph {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X) (a : ℝ) :
    { q : Torus f // base f q ≠ (a : MappingTorus.Circle) } ≃ₜ (Set.Ioo a (a + 1) × X) :=
  ((Equiv.ofBijective (intervalParam f a)
          ⟨intervalParam_injective f a,
            intervalParam_surjective f a⟩).toHomeomorphOfContinuousOpen
      (intervalParam_continuous f a) (intervalParam_open f a)).symm

@[simp]
private theorem
    MappingTorus.intervalHomeomorph_symm_coe {X : Type*} [TopologicalSpace X] (f : X ≃ₜ X)
    (a : ℝ) (p : Set.Ioo a (a + 1) × X) :
    ((intervalHomeomorph f a).symm p : Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  rfl

private theorem MappingTorus.HomologyCover.negativeHalf_coe :
    ((-(1 / 2 : ℝ)) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
      PeriodTorusHigherHomology.CircleTopology.halfPoint := by
  have h := AddCircle.coe_add_period (p := (1 : ℝ)) (-(1 / 2 : ℝ))
  norm_num [PeriodTorusHigherHomology.CircleTopology.halfPoint] at h ⊢
  exact h.symm

private theorem MappingTorus.HomologyCover.negativeHalf_coe_ne_zero :
    ((-(1 / 2 : ℝ)) : (PeriodTorusHigherHomology.CircleTopology.Circle)) ≠ 0 := by
  rw [negativeHalf_coe]
  exact PeriodTorusHigherHomology.CircleTopology.halfPoint_ne_zero

private theorem
    MappingTorus.HomologyCover.unitInterval_coe_eq_negativeHalf_iff (t : Set.Ioo (0 : ℝ) 1) :
    ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) =
        ((-(1 / 2 : ℝ)) : (PeriodTorusHigherHomology.CircleTopology.Circle)) ↔
      (t : ℝ) = 1 / 2 := by
  rw [negativeHalf_coe]
  exact
    AddCircle.coe_eq_coe_iff_of_mem_Ico (p := (1 : ℝ)) (a := 0)
      ⟨le_of_lt t.property.1, by simpa only [zero_add] using t.property.2⟩ (by norm_num)

private theorem
    MappingTorus.HomologyCover.unitInterval_coe_ne_negativeHalf_iff (t : Set.Ioo (0 : ℝ) 1) :
    ((t : ℝ) : (PeriodTorusHigherHomology.CircleTopology.Circle)) ≠
        ((-(1 / 2 : ℝ)) : (PeriodTorusHigherHomology.CircleTopology.Circle)) ↔
      (t : ℝ) ≠ 1 / 2 :=
  not_congr (unitInterval_coe_eq_negativeHalf_iff t)

private def MappingTorus.HomologyCover.firstPredicateHomeomorph (A X : Type*) [TopologicalSpace A]
    [TopologicalSpace X] (p : A → Prop) : { z : A × X // p z.1 } ≃ₜ ({ a : A // p a } × X)
    where
  toFun z := (⟨z.val.1, z.property⟩, z.val.2)
  invFun z := ⟨(z.1.val, z.2), z.1.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.fst.subtype_mk _).prodMk continuous_subtype_val.snd
  continuous_invFun :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).subtype_mk _

private def
    MappingTorus.HomologyCover.intervalIntersectionHomeomorph (X : Type*) [TopologicalSpace X] :
    { p : Set.Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2 } ≃ₜ
      ((Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X)) :=
  ((firstPredicateHomeomorph (Set.Ioo (0 : ℝ) 1) X (fun t => (t : ℝ) ≠ 1 / 2)).trans
        (PeriodTorusHigherHomology.CircleTopology.puncturedIntervalHomeomorph.prodCongr
          (Homeomorph.refl X))).trans
    Homeomorph.sumProdDistrib

private def MappingTorus.HomologyCover.U {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    Set (MappingTorus.Torus f) :=
  {q | MappingTorus.base f q ≠ ((0 : ℝ) : MappingTorus.Circle)}

private def MappingTorus.HomologyCover.V {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    Set (MappingTorus.Torus f) :=
  {q | MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)}

private theorem MappingTorus.HomologyCover.U_open {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpen (U f) :=
  isOpen_compl_singleton.preimage (MappingTorus.base f).continuous

private theorem MappingTorus.HomologyCover.V_open {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    IsOpen (V f) :=
  isOpen_compl_singleton.preimage (MappingTorus.base f).continuous

private theorem MappingTorus.HomologyCover.cover {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ∪ V f = Set.univ := by
  ext q
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases hq : MappingTorus.base f q = 0
  · right
    change MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle)
    rw [hq]
    exact Ne.symm negativeHalf_coe_ne_zero
  · exact Or.inl hq

private def MappingTorus.HomologyCover.chartU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ≃ₜ Set.Ioo (0 : ℝ) 1 × X :=
  (MappingTorus.intervalHomeomorph f 0).trans
    ((Homeomorph.setCongr (by simp : Ioo (0 : ℝ) (0 + 1) = Ioo 0 1)).prodCongr
      (Homeomorph.refl X))

private def MappingTorus.HomologyCover.chartV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    V f ≃ₜ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X :=
  (MappingTorus.intervalHomeomorph f (-(1 / 2 : ℝ))).trans
    ((Homeomorph.setCongr
          (by norm_num : Ioo (-(1 / 2 : ℝ)) (-(1 / 2) + 1) = Ioo (-(1 / 2)) (1 / 2))).prodCongr
      (Homeomorph.refl X))

@[simp]
private theorem
    MappingTorus.HomologyCover.chartU_symm_coe {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (p : Set.Ioo (0 : ℝ) 1 × X) :
    ((chartU f).symm p : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  MappingTorus.intervalHomeomorph_symm_coe f 0 _

@[simp]
private theorem
    MappingTorus.HomologyCover.chartV_symm_coe {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (p : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X) :
    ((chartV f).symm p : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  MappingTorus.intervalHomeomorph_symm_coe f (-(1 / 2 : ℝ)) _

private theorem MappingTorus.HomologyCover.chartU_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) (p : Set.Ioo (0 : ℝ) 1 × X)
    (hq : (q : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2)) : chartU f q = p := by
  apply (chartU f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartU_symm_coe f p).symm)

private theorem MappingTorus.HomologyCover.chartV_mk {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : V f) (p : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) × X)
    (hq : (q : MappingTorus.Torus f) = MappingTorus.mk f ((p.1 : ℝ), p.2)) : chartV f q = p := by
  apply (chartV f).symm.injective
  rw [Homeomorph.symm_apply_apply]
  exact Subtype.ext (hq.trans (chartV_symm_coe f p).symm)

private theorem MappingTorus.HomologyCover.chartU_representation {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (q : U f) :
    MappingTorus.mk f (((chartU f q).1 : ℝ), (chartU f q).2) = (q : MappingTorus.Torus f) := by
  rw [← chartU_symm_coe, Homeomorph.symm_apply_apply]

private theorem MappingTorus.HomologyCover.chartV_representation {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (q : V f) :
    MappingTorus.mk f (((chartV f q).1 : ℝ), (chartV f q).2) = (q : MappingTorus.Torus f) := by
  rw [← chartV_symm_coe, Homeomorph.symm_apply_apply]

private theorem MappingTorus.HomologyCover.chartU_base {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) : (((chartU f q).1 : ℝ) : MappingTorus.Circle) = MappingTorus.base f q := by
  have h := congrArg (MappingTorus.base f) (chartU_representation f q)
  simpa only [MappingTorus.base_mk] using h

private theorem
    MappingTorus.HomologyCover.chartU_mem_V_iff {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    (q : U f) : (q : MappingTorus.Torus f) ∈ V f ↔ ((chartU f q).1 : ℝ) ≠ 1 / 2 := by
  change MappingTorus.base f q ≠ ((-(1 / 2 : ℝ)) : MappingTorus.Circle) ↔ _
  rw [← chartU_base]
  exact unitInterval_coe_ne_negativeHalf_iff _

private def
    MappingTorus.HomologyCover.intersectionChart {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    ↥(U f ∩ V f) ≃ₜ { p : Set.Ioo (0 : ℝ) 1 × X // (p.1 : ℝ) ≠ 1 / 2 } :=
  (PeriodTorusHigherHomology.CircleTopology.intersectionSubtypeHomeomorph (U f) (V f)).trans
    ((chartU f).subtype (chartU_mem_V_iff f))

private def MappingTorus.HomologyCover.intersectionHomeomorph {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    ↥(U f ∩ V f) ≃ₜ ((Set.Ioo (0 : ℝ) (1 / 2) × X) ⊕ (Set.Ioo (1 / 2 : ℝ) 1 × X)) :=
  (intersectionChart f).trans (intervalIntersectionHomeomorph X)

@[simp]
private theorem MappingTorus.HomologyCover.intersectionHomeomorph_symm_inl_coe {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    ((intersectionHomeomorph f).symm (Sum.inl p) : MappingTorus.Torus f) =
      MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

@[simp]
private theorem MappingTorus.HomologyCover.intersectionHomeomorph_symm_inr_coe {X : Type}
    [TopologicalSpace X] (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    ((intersectionHomeomorph f).symm (Sum.inr p) : MappingTorus.Torus f) =
      MappingTorus.mk f ((p.1 : ℝ), p.2) :=
  chartU_symm_coe f _

private def MappingTorus.HomologyCover.inclusionU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(U f, MappingTorus.Torus f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def MappingTorus.HomologyCover.inclusionV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(V f, MappingTorus.Torus f) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private def
    MappingTorus.HomologyCover.intersectionToU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(↥(U f ∩ V f), U f) :=
  ContinuousMap.inclusion Set.inter_subset_left

private def
    MappingTorus.HomologyCover.intersectionToV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(↥(U f ∩ V f), V f) :=
  ContinuousMap.inclusion Set.inter_subset_right

private theorem MappingTorus.HomologyCover.chartU_intersection_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 = p.2 := by
  exact
    congrArg Prod.snd
      (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inl p)))
        ((PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInl p.1).val, p.2)
        (intersectionHomeomorph_symm_inl_coe f p))

private theorem MappingTorus.HomologyCover.chartU_intersection_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    (chartU f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 = p.2 := by
  exact
    congrArg Prod.snd
      (chartU_mk f (intersectionToU f ((intersectionHomeomorph f).symm (Sum.inr p)))
        ((PeriodTorusHigherHomology.CircleTopology.puncturedIntervalInr p.1).val, p.2)
        (intersectionHomeomorph_symm_inr_coe f p))

private theorem MappingTorus.HomologyCover.chartV_intersection_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inl p)))).2 = p.2 := by
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨p.1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  rw [chartV_mk f _ (t, p.2) (intersectionHomeomorph_symm_inl_coe f p)]

private theorem MappingTorus.HomologyCover.chartV_intersection_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    (chartV f (intersectionToV f ((intersectionHomeomorph f).symm (Sum.inr p)))).2 = f p.2 := by
  let t : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) :=
    ⟨(p.1 : ℝ) - 1, by constructor <;> linarith [p.1.property.1, p.1.property.2]⟩
  apply congrArg Prod.snd (chartV_mk f _ (t, f p.2) ?_)
  exact (intersectionHomeomorph_symm_inr_coe f p).trans (MappingTorus.mk_sub_one f _ _).symm

private def MappingTorus.HomologyCover.fibreInclusion {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(X, MappingTorus.Torus f) :=
  ⟨fun x => MappingTorus.mk f (0, x),
    (MappingTorus.mk_continuous f).comp (continuous_const.prodMk continuous_id)⟩

private def MappingTorus.HomologyCover.liftContraction {X : Type} [TopologicalSpace X] (f : X ≃ₜ X)
    {S : Type} [TopologicalSpace S] (q : C(S, MappingTorus.Torus f)) (l : C(S, ℝ × X))
    (hl : ∀ s, MappingTorus.mk f (l s) = q s) :
    q.Homotopy ((fibreInclusion f).comp (ContinuousMap.snd.comp l))
    where
  toFun p := MappingTorus.mk f ((1 - (p.1 : ℝ)) * (l p.2).1, (l p.2).2)
  continuous_toFun :=
    (MappingTorus.mk_continuous f).comp
      (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
            (l.continuous.fst.comp continuous_snd)).prodMk
        (l.continuous.snd.comp continuous_snd))
  map_zero_left s := by simpa using hl s
  map_one_left s := by simp [fibreInclusion]

private def MappingTorus.HomologyCover.liftU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(U f, ℝ × X) :=
  ⟨fun q => (((chartU f q).1 : ℝ), (chartU f q).2),
    (continuous_subtype_val.comp (chartU f).continuous.fst).prodMk (chartU f).continuous.snd⟩

private def MappingTorus.HomologyCover.liftV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    C(V f, ℝ × X) :=
  ⟨fun q => (((chartV f q).1 : ℝ), (chartV f q).2),
    (continuous_subtype_val.comp (chartV f).continuous.fst).prodMk (chartV f).continuous.snd⟩

private def MappingTorus.HomologyCover.homotopyEquivU {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    U f ≃ₕ X := by
  letI : ContractibleSpace (Set.Ioo (0 : ℝ) 1) :=
    PeriodTorusHigherHomology.CircleTopology.intervalContractible 0 1 zero_lt_one
  exact
    (chartU f).toHomotopyEquiv.trans
      (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv (Set.Ioo (0 : ℝ) 1)
        X)

private def MappingTorus.HomologyCover.homotopyEquivV {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    V f ≃ₕ X := by
  letI : ContractibleSpace (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    PeriodTorusHigherHomology.CircleTopology.intervalContractible _ _ (by norm_num)
  exact
    (chartV f).toHomotopyEquiv.trans
      (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) X)

private def
    MappingTorus.HomologyCover.inclusionUHomotopy {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    (inclusionU f).Homotopy ((fibreInclusion f).comp (homotopyEquivU f).toFun) :=
  liftContraction f (inclusionU f) (liftU f) (chartU_representation f)

private def
    MappingTorus.HomologyCover.inclusionVHomotopy {X : Type} [TopologicalSpace X] (f : X ≃ₜ X) :
    (inclusionV f).Homotopy ((fibreInclusion f).comp (homotopyEquivV f).toFun) :=
  liftContraction f (inclusionV f) (liftV f) (chartV_representation f)

private def MappingTorus.HomologyCover.intersectionHomotopyEquiv {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) : ↥(U f ∩ V f) ≃ₕ X ⊕ X :=
  (intersectionHomeomorph f).toHomotopyEquiv.trans
    (PeriodTorusHigherHomology.CircleTopology.sumHomotopyEquiv
      (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (0 : ℝ) (1 / 2)) X)
      (PeriodTorusHigherHomology.CircleTopology.contractibleProdHomotopyEquiv
        (Set.Ioo (1 / 2 : ℝ) 1) X))

@[simp]
private theorem
    MappingTorus.HomologyCover.intersectionHomotopyEquiv_inl {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (0 : ℝ) (1 / 2) × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inl p)) = Sum.inl p.2 := by
  change
    Sum.map (fun p : Set.Ioo (0 : ℝ) (1 / 2) × X => p.2)
        (fun p : Set.Ioo (1 / 2 : ℝ) 1 × X => p.2)
        (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inl p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

@[simp]
private theorem
    MappingTorus.HomologyCover.intersectionHomotopyEquiv_inr {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) (p : Set.Ioo (1 / 2 : ℝ) 1 × X) :
    intersectionHomotopyEquiv f ((intersectionHomeomorph f).symm (Sum.inr p)) = Sum.inr p.2 := by
  change
    Sum.map (fun p : Set.Ioo (0 : ℝ) (1 / 2) × X => p.2)
        (fun p : Set.Ioo (1 / 2 : ℝ) 1 × X => p.2)
        (intersectionHomeomorph f ((intersectionHomeomorph f).symm (Sum.inr p))) =
      _
  rw [Homeomorph.apply_symm_apply]
  rfl

private theorem MappingTorus.HomologyCover.intersectionToU_fold {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    (homotopyEquivU f).toFun.comp (intersectionToU f) =
      (PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl
    p =>
    change
      (chartU f (intersectionToU f _)).2 =
        PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartU_intersection_inl]
    rfl
  | inr
    p =>
    change
      (chartU f (intersectionToU f _)).2 =
        PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (ContinuousMap.id X)
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartU_intersection_inr]
    rfl

private theorem
    MappingTorus.HomologyCover.intersectionToV_twistedFold {X : Type} [TopologicalSpace X]
    (f : X ≃ₜ X) :
    (homotopyEquivV f).toFun.comp (intersectionToV f) =
      (PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))).comp
        (intersectionHomotopyEquiv f).toFun := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨p, rfl⟩ := (intersectionHomeomorph f).symm.surjective q
  cases p with
  | inl
    p =>
    change
      (chartV f (intersectionToV f _)).2 =
        PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inl, chartV_intersection_inl]
    rfl
  | inr
    p =>
    change
      (chartV f (intersectionToV f _)).2 =
        PeriodTorusHigherHomology.sumElimMap (ContinuousMap.id X) (f : C(X, X))
          (intersectionHomotopyEquiv f _)
    rw [intersectionHomotopyEquiv_inr, chartV_intersection_inr]
    rfl

private def ThreefoldOverlapMappingTorus.Cusp.heightContraction (r : ℝ) (h : Height r) :
    (ContinuousMap.const (Height r) h).Homotopy (ContinuousMap.id (Height r))
    where
  toFun
    p :=
    ⟨(1 - (p.1 : ℝ)) * (h : ℝ) + (p.1 : ℝ) * (p.2 : ℝ),
      (convex_Ioi (heightThreshold r)) h.property p.2.property (sub_nonneg.mpr p.1.property.2)
        p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩
  continuous_toFun :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
              continuous_const).add
          ((continuous_subtype_val.comp continuous_fst).mul
            (continuous_subtype_val.comp continuous_snd))).subtype_mk
      _
  map_zero_left
    x := by
    apply Subtype.ext
    change (1 - (0 : ℝ)) * (h : ℝ) + 0 * (x : ℝ) = (h : ℝ)
    simp only [sub_zero, one_mul, MulZeroClass.zero_mul, add_zero]
  map_one_left
    x := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) * (h : ℝ) + 1 * (x : ℝ) = (x : ℝ)
    simp only [sub_self, MulZeroClass.zero_mul, one_mul, zero_add]

private def ThreefoldOverlapMappingTorus.Cusp.heightProductHomotopyEquiv (r : ℝ) (h : Height r) :
    (Height r × Boundary) ≃ₕ Boundary
    where
  toFun := ContinuousMap.snd
  invFun := (ContinuousMap.const Boundary h).prodMk (ContinuousMap.id Boundary)
  left_inv :=
    (show (ContinuousMap.const (Height r) h).Homotopic (ContinuousMap.id (Height r)) from
          ⟨heightContraction r h⟩).prodMap
      (.refl (ContinuousMap.id Boundary))
  right_inv := .refl (ContinuousMap.id Boundary)

private def ThreefoldOverlapMappingTorus.Cusp.familyMappingTorusHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) : D.Space ≃ₕ Boundary :=
  (familyProductHomeomorph D).toHomotopyEquiv.trans (heightProductHomotopyEquiv D.radius h)

private def ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    D.Space ≃ₜ CuspUniformization.PuncturedQuotient D.correction D.radius := by
  letI := D.chartedSpace
  letI :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph.toHomeomorph

@[simp]
private theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_iteratedCover
    (D : SpecialPeriods.CuspFamily.Data) (p : CuspUniformization.LogCover D.radius) :
    puncturedFamilyHomeomorph D (D.iteratedCover p) =
      CuspUniformization.puncturedCuspCover D.correction D.radius p := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph_iteratedCover p

private theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_base
    (D : SpecialPeriods.CuspFamily.Data) (q : D.Space) :
    CuspQuotient.projection D.correction D.radius (puncturedFamilyHomeomorph D q) =
      (D.projection q : ℂ) := by
  let := D.chartedSpace
  let :=
    CuspQuotient.chartedSpace D.correction D.radius D.radius_pos D.radius_lt_one D.holomorphic
      D.smallDrift
  exact D.puncturedFamilyBiholomorph_preserves_base q

private theorem ThreefoldOverlapMappingTorus.Cusp.puncturedFamilyHomeomorph_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (s : SpecialPeriods.CuspFamily.LogBase D.radius)
    (x : RealPlane₄) :
    puncturedFamilyHomeomorph D (D.quotient (s, standardLattice.mkQ x)) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ := by
  have he :
    D.iteratedCover ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩ =
      D.quotient (s, standardLattice.mkQ x) := by
    change
      D.quotient
          (s, standardLattice.mkQ ((D.periods.periodEquiv s).symm (D.periods.periodEquiv s x))) =
        _
    rw [LinearEquiv.symm_apply_apply]
  rw [← he, puncturedFamilyHomeomorph_iteratedCover]

private def ThreefoldOverlapMappingTorus.Cusp.puncturedProductHomeomorph
    (D : SpecialPeriods.CuspFamily.Data) :
    CuspUniformization.PuncturedQuotient D.correction D.radius ≃ₜ Height D.radius × Boundary :=
  (puncturedFamilyHomeomorph D).symm.trans (familyProductHomeomorph D)

private def ThreefoldOverlapMappingTorus.Cusp.puncturedMappingTorusHomotopyEquiv
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) :
    CuspUniformization.PuncturedQuotient D.correction D.radius ≃ₕ Boundary :=
  (puncturedFamilyHomeomorph D).symm.toHomotopyEquiv.trans (familyMappingTorusHomotopyEquiv D h)

private def ThreefoldOverlapMappingTorus.Cusp.boundaryInclusion (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(Boundary, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (puncturedMappingTorusHomotopyEquiv D h).invFun

private def ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(ℝ × RealTorus₄, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp ⟨MappingTorus.mk monodromy, MappingTorus.mk_continuous monodromy⟩

private theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_apply
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    boundaryCylinder D h (t, x) =
      puncturedFamilyHomeomorph D (D.quotient (logPoint D.radius D.radius_pos t h, x)) := by
  change
    puncturedFamilyHomeomorph D
        ((familyProductHomeomorph D).symm (h, MappingTorus.mk monodromy (t, x))) =
      _
  rw [familyProductHomeomorph_symm_mk]

private theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealPlane₄) :
    boundaryCylinder D h (t, standardLattice.mkQ x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos t h : ℂ),
            D.periods.periodEquiv (logPoint D.radius D.radius_pos t h) x),
          (logPoint D.radius D.radius_pos t h).property⟩ := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_realCoordinates]

private theorem ThreefoldOverlapMappingTorus.Cusp.boundaryCylinder_base
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (t : ℝ) (x : RealTorus₄) :
    CuspQuotient.projection D.correction D.radius (boundaryCylinder D h (t, x)) =
      CuspUniformization.exponential ((t : ℂ) + (h : ℝ) * Complex.I) := by
  rw [boundaryCylinder_apply, puncturedFamilyHomeomorph_base, D.projection_quotient]
  rfl

private def ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured (D : SpecialPeriods.CuspFamily.Data)
    (h : Height D.radius) :
    C(RealTorus₄, CuspUniformization.PuncturedQuotient D.correction D.radius) :=
  (boundaryInclusion D h).comp (MappingTorus.HomologyCover.fibreInclusion monodromy)

private theorem ThreefoldOverlapMappingTorus.Cusp.fibreToPunctured_realCoordinates
    (D : SpecialPeriods.CuspFamily.Data) (h : Height D.radius) (x : RealPlane₄) :
    fibreToPunctured D h (standardLattice.mkQ x) =
      CuspUniformization.puncturedCuspCover D.correction D.radius
        ⟨((logPoint D.radius D.radius_pos 0 h : ℂ),
            D.periods.periodEquiv (logPoint D.radius D.radius_pos 0 h) x),
          (logPoint D.radius D.radius_pos 0 h).property⟩ :=
  boundaryCylinder_realCoordinates D h 0 x

end Mathoverflow1973

end
