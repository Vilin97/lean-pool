/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.Core
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.FiniteNormExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaAbsoluteValue
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaIntegralClosure
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.RamificationInvariants
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueValuationSubring
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
/-!
# Localization and decomposition comparison through density

For an infinite algebraic extension, the canonical `L_w` is the algebraic
localization `L K_v`, not the whole metric completion.  This file records the
density consequences needed to transport inertia and ramification conditions
between `L` and `L_w`.  None of the results below assumes finite degree.
-/

@[expose] public section

open _root_.ValuationTheory.DiscreteValuationField.ResidueField renaming
  residue_eq_residue_iff_sub_mem_maximalIdeal →
    residue_eq_residue_iff_sub_mem_maximalIdeal


noncomputable section

universe u v

namespace HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

open AlgebraicNumberTheory.Valuations

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

section AbsoluteValuePrincipalUnits

variable {F : Type*} [Field F]

/-- For the valuation subring attached to a nonarchimedean absolute value,
the ambient-field nonunits are exactly the open unit ball. -/
theorem algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one
    (a : AbsoluteValue F ℝ) (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : F) :
    x ∈ (absoluteValueValuationSubring a ha).nonunits ↔
      a x < 1 := by
  let A := absoluteValueValuationSubring a ha
  change x ∈ A.nonunits ↔ a x < 1
  rw [A.mem_nonunits_iff_exists_mem_maximalIdeal]
  constructor
  · rintro ⟨hxA, hx⟩
    exact
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        a ha ⟨x, hxA⟩).mp hx
  · intro hx
    have hxA : x ∈ A :=
      (mem_absoluteValueValuationSubring_iff
        a ha x).mpr hx.le
    refine ⟨hxA, ?_⟩
    exact
      (absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one
        a ha ⟨x, hxA⟩).mpr hx

/-- Principal-unit membership in an absolute-value valuation subring is the
strict-unit inequality `|u - 1| < 1`. -/
theorem algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one
    (a : AbsoluteValue F ℝ) (ha : LubinTate.Valuations.NonarchimedeanAbsoluteValue a)
    (x : Fˣ) :
    x ∈ (absoluteValueValuationSubring a ha).principalUnitGroup ↔
      a ((x : F) - 1) < 1 := by
  let A := absoluteValueValuationSubring a ha
  change A.valuation ((x : F) - 1) < 1 ↔ a ((x : F) - 1) < 1
  rw [← A.mem_nonunits_iff,
    algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one a ha]

end AbsoluteValuePrincipalUnits

namespace ValuationSubring

/-- Inertia membership as the congruence `sigma x = x` modulo the maximal
ideal for every integral element. -/
theorem mem_inertiaGroup_iff_sub_mem_nonunits
    {F : Type*} {E : Type*} [Field F] [Field E] [Algebra F E]
    (A : _root_.ValuationSubring E) (sigma : decompositionGroup F A) :
    sigma ∈ inertiaGroup F A ↔
      ∀ x : A,
        ((sigma : E ≃ₐ[F] E) (x : E) - (x : E)) ∈ A.nonunits := by
  change residueAction F A sigma = 1 ↔ _
  constructor
  · intro hsigma x
    have happ := congrArg
      (fun e : IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A ↦
        e (IsLocalRing.residue A x)) hsigma
    change sigma • (IsLocalRing.residue A x) =
      IsLocalRing.residue A x at happ
    rw [← IsLocalRing.ResidueField.residue_smul,
      residue_eq_residue_iff_sub_mem_maximalIdeal]
      at happ
    exact A.coe_mem_nonunits_iff.mpr happ
  · intro hsigma
    apply RingEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    change sigma • (IsLocalRing.residue A x) =
      IsLocalRing.residue A x
    rw [← IsLocalRing.ResidueField.residue_smul,
      residue_eq_residue_iff_sub_mem_maximalIdeal]
    exact A.coe_mem_nonunits_iff.mp (hsigma x)

end ValuationSubring

section Localization

variable (vK : AbsoluteValue K ℝ)
variable (w : AbsoluteValueExtension vK L)

/-- The completion at the extended absolute value is a `K`-algebra through the original
extension. -/
local instance completionBaseAlgebra : Algebra K w.1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra (K := K) w.1

/-- The action of `K` on the extended completion is induced by its completion algebra. -/
local instance completionBaseSMul : SMul K w.1.Completion :=
  (AbsoluteValue.extensionCompletionAlgebra (K := K) w.1).toSMul

/-- The completion at the extended absolute value is an algebra over the completed base field. -/
local instance completionAlgebra : Algebra vK.Completion w.1.Completion :=
  AbsoluteValue.completionAlgebra vK w.1 w.2

private abbrev localization : IntermediateField vK.Completion w.1.Completion :=
  AbsoluteValue.algebraicLocalization vK w.1 w.2

private abbrev toLocalization : L →+* localization vK w :=
  AbsoluteValue.toAlgebraicLocalization vK w.1 w.2

private abbrev localizationAbsoluteValue :
    AbsoluteValue (localization vK w) ℝ :=
  AbsoluteValue.algebraicLocalizationAbsoluteValue vK w.1 w.2

/-- The dense copy of `L` approximates every element of the algebraic
localization.  This is the common source for residue and principal-unit
transport in the localization and decomposition comparison. -/
theorem algebraicLocalizationDensity_localization_exists_close
    (z : localization vK w) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ x : L,
      localizationAbsoluteValue vK w (z - toLocalization vK w x) < epsilon := by
  obtain ⟨x, hx⟩ :=
    (AbsoluteValue.denseRange_toCompletion w.1).exists_dist_lt
      (z : w.1.Completion) hepsilon
  refine ⟨x, ?_⟩
  change ‖(z : w.1.Completion) -
      AbsoluteValue.toCompletion w.1 x‖ < epsilon
  simpa only [dist_eq_norm] using hx

/-- Nonarchimedeanness passes from `w` to the absolute value on `L K_v`.
The bounded-natural-number definition makes this a direct consequence of
the restriction formula on the dense copy of `L`. -/
theorem algebraicLocalizationDensity_localization_nonarchimedean
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1) :
    LubinTate.Valuations.NonarchimedeanAbsoluteValue (localizationAbsoluteValue vK w) := by
  rcases hw with ⟨C, hC⟩
  refine ⟨C, fun n ↦ ?_⟩
  have hrestrict :=
    AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 (n : L)
  simpa using hrestrict.trans_le (hC n)

private abbrev extensionValuationSubring
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1) :
    _root_.ValuationSubring L :=
  absoluteValueValuationSubring w.1 hw

private abbrev localizationValuationSubring
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1) :
    _root_.ValuationSubring (localization vK w) :=
  absoluteValueValuationSubring
    (localizationAbsoluteValue vK w)
    (algebraicLocalizationDensity_localization_nonarchimedean vK w hw)

/-- The valuation subring on `L K_v` pulls back to the valuation subring on
`L`.  This is the concrete valuation-ring square used by the conjugation and base-change law in
the localization specialization. -/
theorem algebraicLocalizationDensity_localizationValuationSubring_comap
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1) :
    (localizationValuationSubring vK w hw).comap (toLocalization vK w) =
      extensionValuationSubring vK w hw := by
  ext x
  rw [_root_.ValuationSubring.mem_comap]
  rw [mem_absoluteValueValuationSubring_iff,
    mem_absoluteValueValuationSubring_iff,
    AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization]

/-- Every automorphism of the algebraic localization over `K_v` preserves
its unique extended absolute value.  This is the isometry source used when
transporting strict congruences from the dense copy of `L`. -/
theorem algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv
    [Algebra.IsAlgebraic K L]
    (hvK : vK.IsNontrivial)
    (tau : localization vK w ≃ₐ[vK.Completion] localization vK w)
    (z : localization vK w) :
    localizationAbsoluteValue vK w (tau z) =
      localizationAbsoluteValue vK w z := by
  let aK := AbsoluteValue.completionAbsoluteValue vK
  let aE := localizationAbsoluteValue vK w
  let : Algebra.IsAlgebraic vK.Completion (localization vK w) :=
    AbsoluteValue.algebraicLocalization_isAlgebraic vK w.1 w.2
  let R := AbsoluteValue.uniqueAlgebraicExtension
    (K := vK.Completion) (L := localization vK w)
    aK
    (AbsoluteValue.completionAbsoluteValue_complete vK)
    (AbsoluteValue.completionAbsoluteValue_isNontrivial vK hvK)
  have haE : aE = R.extension := by
    apply R.unique
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2
  have htau :
      aE.comp (f := tau.toRingEquiv.toRingHom) tau.injective = R.extension := by
    apply R.unique
    intro x
    change aE (tau (algebraMap vK.Completion (localization vK w) x)) = aK x
    rw [tau.commutes]
    exact AbsoluteValue.algebraicLocalizationAbsoluteValue_extends vK w.1 w.2 x
  calc
    aE (tau z) =
        (aE.comp (f := tau.toRingEquiv.toRingHom) tau.injective) z := rfl
    _ = R.extension z := DFunLike.congr_fun htau z
    _ = aE z := (DFunLike.congr_fun haE z).symm

/-- Every integral element of `L K_v` has the same residue as an integral
element from `L`.  The displayed strict inequality is the source form of
surjectivity on residue fields and avoids choosing a quotient model. -/
theorem algebraicLocalizationDensity_localization_exists_residueRepresentative
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (z : localizationValuationSubring vK w hw) :
    ∃ x : extensionValuationSubring vK w hw,
      localizationAbsoluteValue vK w
          ((z : localization vK w) -
            toLocalization vK w (x : L)) < 1 := by
  obtain ⟨x, hx⟩ :=
    algebraicLocalizationDensity_localization_exists_close vK w
      (z : localization vK w) (show (0 : ℝ) < 1 by norm_num)
  let aE := localizationAbsoluteValue vK w
  let hE := algebraicLocalizationDensity_localization_nonarchimedean vK w hw
  have hstrong : LubinTate.Valuations.StrongTriangle aE :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean aE hE
  have hz : aE (z : localization vK w) ≤ 1 :=
    (mem_absoluteValueValuationSubring_iff
      aE hE (z : localization vK w)).mp z.property
  have hxLocal : aE (toLocalization vK w x) ≤ 1 := by
    calc
      aE (toLocalization vK w x) =
          aE ((z : localization vK w) +
            -((z : localization vK w) - toLocalization vK w x)) := by
        congr 1
        ring
      _ ≤ max (aE (z : localization vK w))
          (aE (-((z : localization vK w) - toLocalization vK w x))) :=
        hstrong _ _
      _ = max (aE (z : localization vK w))
          (aE ((z : localization vK w) - toLocalization vK w x)) := by
        rw [AbsoluteValue.map_neg]
      _ ≤ 1 := max_le hz hx.le
  have hxGlobal : w.1 x ≤ 1 := by
    rw [← AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 x]
    exact hxLocal
  let xA : extensionValuationSubring vK w hw :=
    ⟨x,
      (mem_absoluteValueValuationSubring_iff
        w.1 hw x).mpr hxGlobal⟩
  exact ⟨xA, hx⟩

/-- The difficult direction of inertia transport in the localization and decomposition comparison.
An automorphism of `L K_v` whose restriction is inertial on `L` is inertial
on the whole localization.  Density supplies an integral representative of
each residue class. -/
theorem algebraicLocalizationDensity_localization_mem_inertia_of_commutes
    [Algebra.IsAlgebraic K L]
    (hvK : vK.IsNontrivial)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (tau : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup vK.Completion
      (localizationValuationSubring vK w hw))
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
      (extensionValuationSubring vK w hw))
    (hcomm : ∀ x : L,
      ((tau : localization vK w ≃ₐ[vK.Completion] localization vK w)
          (toLocalization vK w x)) =
        toLocalization vK w
          ((sigma : L ≃ₐ[K] L) x))
    (hsigma : sigma ∈ RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
      (extensionValuationSubring vK w hw)) :
    tau ∈ RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
      (localizationValuationSubring vK w hw) := by
  rw [ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits]
  intro z
  rw [algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one]
  obtain ⟨x, hx⟩ :=
    algebraicLocalizationDensity_localization_exists_residueRepresentative vK w hw z
  let aE := localizationAbsoluteValue vK w
  let hE := algebraicLocalizationDensity_localization_nonarchimedean vK w hw
  let tauE : localization vK w ≃ₐ[vK.Completion] localization vK w := tau
  let sigmaL : L ≃ₐ[K] L := sigma
  let e : localization vK w :=
    (z : localization vK w) - toLocalization vK w (x : L)
  have hstrong : LubinTate.Valuations.StrongTriangle aE :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean aE hE
  have htau (y : localization vK w) : aE (tauE y) = aE y :=
    algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv vK w hvK tauE y
  have herror : aE (tauE e - e) < 1 := by
    calc
      aE (tauE e - e) = aE (tauE e + -e) := by rw [sub_eq_add_neg]
      _ ≤ max (aE (tauE e)) (aE (-e)) := hstrong _ _
      _ = aE e := by rw [htau e, AbsoluteValue.map_neg, max_self]
      _ < 1 := hx
  have hglobalNonunit :
      (sigmaL (x : L) - (x : L)) ∈
        (extensionValuationSubring vK w hw).nonunits :=
    (ValuationSubring.mem_inertiaGroup_iff_sub_mem_nonunits
      (extensionValuationSubring vK w hw) sigma).mp hsigma x
  have hglobal : w.1 (sigmaL (x : L) - (x : L)) < 1 :=
    (algebraicLocalizationDensity_mem_nonunits_iff_abs_lt_one w.1 hw _).mp hglobalNonunit
  have hmain :
      aE (tauE (toLocalization vK w (x : L)) -
        toLocalization vK w (x : L)) < 1 := by
    calc
      aE (tauE (toLocalization vK w (x : L)) -
          toLocalization vK w (x : L)) =
          aE (toLocalization vK w (sigmaL (x : L)) -
            toLocalization vK w (x : L)) := by rw [hcomm]
      _ = aE (toLocalization vK w
          (sigmaL (x : L) - (x : L))) := by
        congr 1
        exact (map_sub (toLocalization vK w) (sigmaL (x : L)) (x : L)).symm
      _ = w.1 (sigmaL (x : L) - (x : L)) :=
        AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _
      _ < 1 := hglobal
  have hdecomp :
      tauE (z : localization vK w) - (z : localization vK w) =
        (tauE e - e) +
          (tauE (toLocalization vK w (x : L)) -
            toLocalization vK w (x : L)) := by
    dsimp [e]
    rw [map_sub]
    ring
  rw [hdecomp]
  exact (hstrong _ _).trans_lt (max_lt herror hmain)

/-- Every nonzero element of `L K_v` is congruent modulo principal units to
an element from `Lˣ`.  The equality of absolute values is included because
it is the value-group transport used in the ramification argument. -/
theorem algebraicLocalizationDensity_localization_exists_principalUnitRepresentative_abs
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (z : (localization vK w)ˣ) :
    ∃ x : Lˣ,
      localizationAbsoluteValue vK w
          (toLocalization vK w (x : L)) =
        localizationAbsoluteValue vK w (z : localization vK w) ∧
      localizationAbsoluteValue vK w
          ((z : localization vK w) /
            toLocalization vK w (x : L) - 1) < 1 := by
  let aE := localizationAbsoluteValue vK w
  let hE := algebraicLocalizationDensity_localization_nonarchimedean vK w hw
  have hstrong : LubinTate.Valuations.StrongTriangle aE :=
    LubinTate.Valuations.strong_triangle_of_nonarchimedean aE hE
  have hz0 : (z : localization vK w) ≠ 0 := Units.ne_zero z
  have hzpos : 0 < aE (z : localization vK w) := aE.pos hz0
  obtain ⟨y, hyClose⟩ :=
    algebraicLocalizationDensity_localization_exists_close vK w
      (z : localization vK w) hzpos
  change aE ((z : localization vK w) - toLocalization vK w y) <
    aE (z : localization vK w) at hyClose
  have hy0 : y ≠ 0 := by
    intro hy
    subst y
    rw [map_zero, sub_zero] at hyClose
    exact (lt_irrefl _ hyClose)
  have hyValue : aE (toLocalization vK w y) =
      aE (z : localization vK w) := by
    have hne : aE (z : localization vK w) ≠
        aE (-((z : localization vK w) - toLocalization vK w y)) := by
      rw [AbsoluteValue.map_neg]
      exact ne_of_gt hyClose
    have hsum := LubinTate.Valuations.strong_triangle_eq_max_of_ne hstrong hne
    calc
      aE (toLocalization vK w y) =
          aE ((z : localization vK w) +
            -((z : localization vK w) - toLocalization vK w y)) := by
        congr 1
        ring
      _ = max (aE (z : localization vK w))
          (aE (-((z : localization vK w) - toLocalization vK w y))) := hsum
      _ = max (aE (z : localization vK w))
          (aE ((z : localization vK w) - toLocalization vK w y)) := by
        rw [AbsoluteValue.map_neg]
      _ = aE (z : localization vK w) := max_eq_left hyClose.le
  let x : Lˣ := Units.mk0 y hy0
  refine ⟨x, hyValue, ?_⟩
  change aE ((z : localization vK w) / toLocalization vK w y - 1) < 1
  rw [div_sub_one ((map_ne_zero (toLocalization vK w)).mpr hy0),
    map_div₀, hyValue]
  exact (div_lt_one hzpos).mpr hyClose

/-- Quotient formulation of the preceding approximation: the natural map
`Lˣ / U_L¹ → (L K_v)ˣ / U_{L K_v}¹` is surjective on
representatives. -/
theorem algebraicLocalizationDensity_localization_exists_principalUnitRepresentative
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (z : (localization vK w)ˣ) :
    ∃ x : Lˣ,
      z / Units.map (toLocalization vK w) x ∈
        (localizationValuationSubring vK w hw).principalUnitGroup := by
  obtain ⟨x, _, hx⟩ :=
    algebraicLocalizationDensity_localization_exists_principalUnitRepresentative_abs
      vK w hw z
  refine ⟨x, ?_⟩
  rw [algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one]
  simpa using hx

/-- The dense embedding `L → L K_v` sends global principal units to
local principal units. -/
theorem algebraicLocalizationDensity_localization_principalUnit_map
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (x : Lˣ)
    (hx : x ∈ (extensionValuationSubring vK w hw).principalUnitGroup) :
    Units.map (toLocalization vK w) x ∈
      (localizationValuationSubring vK w hw).principalUnitGroup := by
  have hxAbs : w.1 ((x : L) - 1) < 1 :=
    (algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one w.1 hw x).mp hx
  rw [algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one]
  calc
    localizationAbsoluteValue vK w
        (((Units.map (toLocalization vK w) x :
          (localization vK w)ˣ) : localization vK w) - 1) =
      localizationAbsoluteValue vK w
        (toLocalization vK w ((x : L) - 1)) := by
          congr 1
          simp
    _ = w.1 ((x : L) - 1) :=
      AbsoluteValue.algebraicLocalizationAbsoluteValue_toAlgebraicLocalization vK w.1 w.2 _
    _ < 1 := hxAbs

/-- The difficult direction of ramification transport in the localization and decomposition
comparison.
Once the restrictions commute, an automorphism ramified-trivially on every
global multiplicative class is ramified-trivially on every local class.
Surjectivity modulo principal units is the essential density input. -/
theorem algebraicLocalizationDensity_localization_mem_ramification_of_commutes
    [Algebra.IsAlgebraic K L]
    (hvK : vK.IsNontrivial)
    (hw : LubinTate.Valuations.NonarchimedeanAbsoluteValue w.1)
    (tau : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup vK.Completion
      (localizationValuationSubring vK w hw))
    (sigma : RamificationTheory.HilbertRamification.ValuationSubring.inertiaGroup K
      (extensionValuationSubring vK w hw))
    (hcomm : ∀ x : L,
      (((tau : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
        vK.Completion
          (localizationValuationSubring vK w hw)) :
            localization vK w ≃ₐ[vK.Completion] localization vK w)
          (toLocalization vK w x)) =
        toLocalization vK w
          ((((sigma : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K
            (extensionValuationSubring vK w hw)) : L ≃ₐ[K] L) x)))
    (hsigma : sigma ∈ RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup K
      (extensionValuationSubring vK w hw)) :
    tau ∈ RamificationTheory.HilbertRamification.ValuationSubring.ramificationGroup vK.Completion
      (localizationValuationSubring vK w hw) := by
  rw [RamificationTheory.HilbertRamification.ValuationSubring.mem_ramificationGroup_iff]
  intro z
  let AE := localizationValuationSubring vK w hw
  let AL := extensionValuationSubring vK w hw
  let j := toLocalization vK w
  let tauD : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup
    vK.Completion AE := tau
  let sigmaD : RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroup K AL
    := sigma
  let tauE : localization vK w ≃ₐ[vK.Completion] localization vK w := tauD
  let sigmaL : L ≃ₐ[K] L := sigmaD
  obtain ⟨x, hu⟩ :=
    algebraicLocalizationDensity_localization_exists_principalUnitRepresentative vK w hw z
  let xE : (localization vK w)ˣ := Units.map j x
  let u : (localization vK w)ˣ := z / xE
  have hu' : u ∈ AE.principalUnitGroup := hu
  have htauU : Units.mapEquiv tauE.toMulEquiv u ∈
      AE.principalUnitGroup := by
    have huAbs : localizationAbsoluteValue vK w
        ((u : localization vK w) - 1) < 1 :=
      (algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one
        (localizationAbsoluteValue vK w)
        (algebraicLocalizationDensity_localization_nonarchimedean vK w hw) u).mp hu'
    rw [algebraicLocalizationDensity_mem_principalUnitGroup_iff_abs_lt_one]
    calc
      localizationAbsoluteValue vK w
          (((Units.mapEquiv tauE.toMulEquiv u :
            (localization vK w)ˣ) : localization vK w) - 1) =
        localizationAbsoluteValue vK w
          (tauE ((u : localization vK w) - 1)) := by
            congr 1
            simp
      _ = localizationAbsoluteValue vK w
          ((u : localization vK w) - 1) :=
        algebraicLocalizationDensity_localizationAbsoluteValue_algEquiv vK w hvK tauE _
      _ < 1 := huAbs
  have hquotU :
      RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
        vK.Completion AE tauD u ∈
        AE.principalUnitGroup := by
    change Units.mapEquiv tauE.toMulEquiv u / u ∈ AE.principalUnitGroup
    exact AE.principalUnitGroup.div_mem htauU hu'
  have hxGlobal :
      RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K AL
        sigmaD x ∈
        AL.principalUnitGroup :=
    (RamificationTheory.HilbertRamification.ValuationSubring.mem_ramificationGroup_iff K AL
      sigma).mp hsigma x
  have hxMapped : Units.map j
      (RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K AL
        sigmaD x) ∈
        AE.principalUnitGroup :=
    algebraicLocalizationDensity_localization_principalUnit_map vK w hw _ hxGlobal
  have hquotX :
      RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
        vK.Completion AE tauD xE ∈
        AE.principalUnitGroup := by
    have heq :
        RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
          vK.Completion AE tauD xE =
          Units.map j
            (RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient K
              AL sigmaD x) := by
      ext
      simp [RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient, xE,
        tauD, sigmaD, j, hcomm]
    rw [heq]
    exact hxMapped
  have hzFactor : u * xE = z := by
    exact div_mul_cancel z xE
  rw [← hzFactor]
  have hquotMul :
      RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
        vK.Completion AE tauD (u * xE) =
        RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
          vK.Completion AE tauD u *
          RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient
            vK.Completion AE tauD xE := by
    ext
    simp [RamificationTheory.HilbertRamification.ValuationSubring.automorphismUnitQuotient,
      div_eq_mul_inv]
    ac_rfl
  rw [hquotMul]
  exact AE.principalUnitGroup.mul_mem hquotU hquotX

end Localization

end HilbertRamification

end
