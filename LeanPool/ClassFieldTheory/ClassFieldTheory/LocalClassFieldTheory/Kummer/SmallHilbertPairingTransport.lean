/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ShrinkTransport
/-!
# Transport of Hilbert pairings across field equivalences

The Type 0 local construction can be applied to a small representative of a
local field.  This file transports its public power-class and Kummer-norm
statements back across the field equivalence.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

universe u v

/-- A field equivalence identifies the groups of `n`-th power classes. -/
noncomputable def powerClassGroupEquivOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+) :
    PowerClassGroup F n ≃* PowerClassGroup G n := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toMulEquiv
  let NF : Subgroup Fˣ := (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range
  let NG : Subgroup Gˣ := (powMonoidHom (n : ℕ) : Gˣ →* Gˣ).range
  have hfg : NF ≤ NG.comap eu.toMonoidHom := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    change eu (y ^ (n : ℕ)) ∈ NG
    exact ⟨eu y, by simp⟩
  have hgf : NG ≤ NF.comap eu.symm.toMonoidHom := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    change eu.symm (y ^ (n : ℕ)) ∈ NF
    exact ⟨eu.symm y, by simp⟩
  let fwd : Fˣ ⧸ NF →* Gˣ ⧸ NG :=
    QuotientGroup.map NF NG eu.toMonoidHom hfg
  let bwd : Gˣ ⧸ NG →* Fˣ ⧸ NF :=
    QuotientGroup.map NG NF eu.symm.toMonoidHom hgf
  change (Fˣ ⧸ NF) ≃* (Gˣ ⧸ NG)
  refine MonoidHom.toMulEquiv fwd bwd ?_ ?_
  · ext x
    simp [fwd, bwd]
  · ext x
    simp [fwd, bwd]

/-- A field equivalence identifies the `n`-th roots of unity. -/
noncomputable def rootsOfUnityEquivOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) G := by
  letI : NeZero (n : ℕ) := ⟨n.pos.ne'⟩
  exact rootsOfUnityEquivOfPrimitiveRoots e.injective hmu

/-- The image of a representative under the induced power-class equivalence. -/
theorem powerClassGroupEquivOfRingEquiv_powerClass
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+) (a : Fˣ) :
    powerClassGroupEquivOfRingEquiv e n (powerClass F n a) =
      powerClass G n (Units.mapEquiv e.toMulEquiv a) := by
  rfl

/-- A representative pulled back from the target power-class group. -/
theorem powerClassGroupEquivOfRingEquiv_symm_powerClass
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+) (a : Gˣ) :
    (powerClassGroupEquivOfRingEquiv e n).symm (powerClass G n a) =
      powerClass F n ((Units.mapEquiv e.toMulEquiv).symm a) := by
  apply (powerClassGroupEquivOfRingEquiv e n).injective
  rw [MulEquiv.apply_symm_apply, powerClassGroupEquivOfRingEquiv_powerClass]
  simp only [MulEquiv.apply_symm_apply]

/-- Kummer-algebra norm membership is invariant under a field equivalence,
even when the Kummer polynomial is reducible. -/
theorem isKummerNorm_iff_of_ringEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+) (a b : Fˣ) :
    IsKummerNorm F n a b ↔
      IsKummerNorm G n
        (Units.mapEquiv e.toMulEquiv a)
        (Units.mapEquiv e.toMulEquiv b) := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toMulEquiv
  let pF : Polynomial F := Polynomial.X ^ (n : ℕ) - Polynomial.C (a : F)
  let pG : Polynomial G := Polynomial.X ^ (n : ℕ) - Polynomial.C (eu a : G)
  have hpmap : pF.map e.toRingHom = pG := by
    simp [pF, pG, eu, Polynomial.map_sub, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C, Units.coe_mapEquiv]
  let eqv : AdjoinRoot pF ≃+* AdjoinRoot pG :=
    AdjoinRoot.mapRingEquiv e pF pG (Associated.of_eq hpmap)
  have hcomp : RingHom.comp (algebraMap G (AdjoinRoot pG)) e.toRingHom =
      RingHom.comp eqv.toRingHom (algebraMap F (AdjoinRoot pF)) := by
    ext x
    simp [eqv, AdjoinRoot.algebraMap_eq]
  have hnorm (y : AdjoinRoot pF) :
      e (Algebra.norm F y) = Algebra.norm G (eqv y) := by
    have h := Algebra.norm_eq_of_equiv_equiv e eqv hcomp y
    exact (congrArg e h).trans (e.apply_symm_apply _)
  change (∃ y : (AdjoinRoot pF)ˣ, Algebra.norm F (y : AdjoinRoot pF) = (b : F)) ↔
    ∃ z : (AdjoinRoot pG)ˣ, Algebra.norm G (z : AdjoinRoot pG) = (eu b : G)
  constructor
  · rintro ⟨y, hy⟩
    let z : (AdjoinRoot pG)ˣ := Units.mapEquiv eqv.toMulEquiv y
    refine ⟨z, ?_⟩
    change Algebra.norm G (eqv (y : AdjoinRoot pF)) = (eu b : G)
    calc
      Algebra.norm G (eqv (y : AdjoinRoot pF)) =
          e (Algebra.norm F (y : AdjoinRoot pF)) := (hnorm _).symm
      _ = e (b : F) := congrArg e hy
      _ = (eu b : G) := by simp [eu]
  · rintro ⟨z, hz⟩
    let y : (AdjoinRoot pF)ˣ := (Units.mapEquiv eqv.toMulEquiv).symm z
    refine ⟨y, ?_⟩
    apply e.injective
    calc
      e (Algebra.norm F (y : AdjoinRoot pF)) =
          Algebra.norm G (eqv (y : AdjoinRoot pF)) := hnorm _
      _ = Algebra.norm G (z : AdjoinRoot pG) := by
            congr 1
            simp [y]
      _ = (eu b : G) := hz
      _ = e (b : F) := by simp [eu]

/-- Pull a pairing on power classes across an equivalence of base fields. -/
noncomputable def hilbertPairingOfRingEquiv
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n) : HilbertPairing G n :=
  let pF := PowerClassGroup F n
  let pG := PowerClassGroup G n
  let rF := rootsOfUnity (n : ℕ) F
  let rG := rootsOfUnity (n : ℕ) G
  let ep := powerClassGroupEquivOfRingEquiv e n
  let er := rootsOfUnityEquivOfRingEquiv e n hmu
  ((MonoidHom.compHom (M := pG) (N := rF) (P := rG)) er.toMonoidHom).comp
    (((MonoidHom.compHom' (M := pG) (N := pF) (P := rF))
      ep.symm.toMonoidHom).comp (B.comp ep.symm.toMonoidHom))

/-- Evaluation of a transported Hilbert pairing. -/
theorem hilbertPairingOfRingEquiv_apply
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n)
    (x y : PowerClassGroup G n) :
    hilbertPairingOfRingEquiv e n hmu B x y =
      rootsOfUnityEquivOfRingEquiv e n hmu
        (B ((powerClassGroupEquivOfRingEquiv e n).symm x)
          ((powerClassGroupEquivOfRingEquiv e n).symm y)) := by
  rfl

/-- The Steinberg relation is preserved by base-field equivalence. -/
theorem hilbertPairingOfRingEquiv_isSteinberg
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n) (hB : B.IsSteinberg) :
    (hilbertPairingOfRingEquiv e n hmu B).IsSteinberg := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toMulEquiv
  let er := rootsOfUnityEquivOfRingEquiv e n hmu
  intro a ha
  let a0 : Fˣ := eu.symm a
  have ha0 : 1 - (a0 : F) ≠ 0 := by
    intro hz
    apply ha
    have hzG := congrArg e hz
    simpa [a0, eu] using hzG
  let c0 : Fˣ := Units.mk0 (1 - (a0 : F)) ha0
  have hc0 : eu.symm (Units.mk0 (1 - (a : G)) ha) = c0 := by
    apply Units.ext
    change e.symm (1 - (a : G)) = 1 - (a0 : F)
    simp [a0, eu]
  change hilbertPairingOfRingEquiv e n hmu B (powerClass G n a)
    (powerClass G n (Units.mk0 (1 - (a : G)) ha)) = 1
  rw [hilbertPairingOfRingEquiv_apply,
    powerClassGroupEquivOfRingEquiv_symm_powerClass,
    powerClassGroupEquivOfRingEquiv_symm_powerClass, hc0]
  change er (B.symbol a0 c0) = 1
  rw [hB a0 ha0, map_one]

/-- Skew-symmetry is preserved by base-field equivalence. -/
theorem hilbertPairingOfRingEquiv_isSkewSymmetric
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n) (hB : B.IsSkewSymmetric) :
    (hilbertPairingOfRingEquiv e n hmu B).IsSkewSymmetric := by
  intro x y
  rw [hilbertPairingOfRingEquiv_apply, hilbertPairingOfRingEquiv_apply]
  rw [hB ((powerClassGroupEquivOfRingEquiv e n).symm x)
      ((powerClassGroupEquivOfRingEquiv e n).symm y), map_inv]

/-- Nondegeneracy in both variables is preserved by field equivalence. -/
theorem hilbertPairingOfRingEquiv_isNondegenerate
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n) (hB : B.IsNondegenerate) :
    (hilbertPairingOfRingEquiv e n hmu B).IsNondegenerate := by
  let ep := powerClassGroupEquivOfRingEquiv e n
  let er := rootsOfUnityEquivOfRingEquiv e n hmu
  constructor
  · intro x hx
    have hx0 : ep.symm x = 1 := by
      apply hB.1
      intro y
      have hxy := hx (ep y)
      rw [hilbertPairingOfRingEquiv_apply, ep.symm_apply_apply] at hxy
      apply er.injective
      simpa only [map_one] using hxy
    calc
      x = ep (ep.symm x) := (ep.apply_symm_apply x).symm
      _ = ep 1 := congrArg ep hx0
      _ = 1 := map_one ep
  · intro y hy
    have hy0 : ep.symm y = 1 := by
      apply hB.2
      intro x
      have hxy := hy (ep x)
      rw [hilbertPairingOfRingEquiv_apply, ep.symm_apply_apply] at hxy
      apply er.injective
      simpa only [map_one] using hxy
    calc
      y = ep (ep.symm y) := (ep.apply_symm_apply y).symm
      _ = ep 1 := congrArg ep hy0
      _ = 1 := map_one ep

/-- The canonical Kummer norm-residue law is preserved by field equivalence. -/
theorem hilbertPairingOfRingEquiv_satisfiesNormResidueCriterion
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n) (hB : B.SatisfiesNormResidueCriterion) :
    (hilbertPairingOfRingEquiv e n hmu B).SatisfiesNormResidueCriterion := by
  let eu : Fˣ ≃* Gˣ := Units.mapEquiv e.toMulEquiv
  let er := rootsOfUnityEquivOfRingEquiv e n hmu
  intro a b
  let a0 : Fˣ := eu.symm a
  let b0 : Fˣ := eu.symm b
  have htr : (hilbertPairingOfRingEquiv e n hmu B).symbol a b = 1 ↔
      B.symbol a0 b0 = 1 := by
    change hilbertPairingOfRingEquiv e n hmu B
      (powerClass G n a) (powerClass G n b) = 1 ↔ _
    rw [hilbertPairingOfRingEquiv_apply,
      powerClassGroupEquivOfRingEquiv_symm_powerClass,
      powerClassGroupEquivOfRingEquiv_symm_powerClass]
    change er (B.symbol a0 b0) = 1 ↔ B.symbol a0 b0 = 1
    rw [← map_one er, er.injective.eq_iff]
  calc
    (hilbertPairingOfRingEquiv e n hmu B).symbol a b = 1 ↔
        B.symbol a0 b0 = 1 := htr
    _ ↔ IsKummerNorm F n a0 b0 := hB a0 b0
    _ ↔ IsKummerNorm G n a b := by
      have ha : Units.mapEquiv e.toMulEquiv a0 = a :=
        eu.apply_symm_apply a
      have hb : Units.mapEquiv e.toMulEquiv b0 = b :=
        eu.apply_symm_apply b
      simpa only [ha, hb] using
        (isKummerNorm_iff_of_ringEquiv e n a0 b0)

/-- All public local-pairing properties are invariant under a field
equivalence. -/
theorem hilbertPairingOfRingEquiv_isLocalHilbertPairing
    {F : Type u} {G : Type v} [Field F] [Field G]
    (e : F ≃+* G) (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
    (B : HilbertPairing F n)
    (hB : HilbertPairing.IsLocalHilbertPairing B) :
    HilbertPairing.IsLocalHilbertPairing
      (hilbertPairingOfRingEquiv e n hmu B) := by
  exact ⟨hilbertPairingOfRingEquiv_isSteinberg e n hmu B hB.1,
    hilbertPairingOfRingEquiv_isSkewSymmetric e n hmu B hB.2.1,
    hilbertPairingOfRingEquiv_isNondegenerate e n hmu B hB.2.2.1,
    hilbertPairingOfRingEquiv_satisfiesNormResidueCriterion e n hmu B hB.2.2.2⟩

end ClassFieldTheory
