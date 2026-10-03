/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.Finsupp.Fintype
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.RingTheory.LocalRing.Module
/-!
# Prime-power kernel coordinates

Linear-algebraic coordinates for kernels of surjections between finite free modules over `ZMod
  (p ^ v)`.
-/

@[expose] public section

open scoped IsMulCommutative

noncomputable
section

namespace KummerTheory

open scoped Classical in
/-- A prime-power residue ring is local.  This instance is the algebraic
input needed to turn the projective kernel in the finite S-unit preparation argument into a free
`ZMod (p ^ v)`-module. -/
theorem zmodPrimePower_isLocalRing
    (p v : ℕ) (hp : p.Prime) (hv : 0 < v) :
    IsLocalRing (ZMod (p ^ v)) := by
  let : Fact (1 < p ^ v) := ⟨by
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)⟩
  have hmodulus : p ∣ p ^ v := by
    exact dvd_pow_self p hv.ne'
  apply IsLocalRing.of_nonunits_add
  intro a b ha hb
  have hunit (x : ZMod (p ^ v)) :
      IsUnit x ↔ ¬ p ∣ x.val := by
    constructor
    · intro hx
      apply (ZMod.isUnit_natCast_iff_not_dvd_pow hp hv).1
      simpa only [ZMod.natCast_zmod_val] using hx
    · intro hx
      have hcast :=
        (ZMod.isUnit_natCast_iff_not_dvd_pow hp hv).2 hx
      simpa only [ZMod.natCast_zmod_val] using hcast
  have ha' : p ∣ a.val := by
    change ¬ IsUnit a at ha
    exact Classical.not_not.mp
      (mt (hunit a).2 ha)
  have hb' : p ∣ b.val := by
    change ¬ IsUnit b at hb
    exact Classical.not_not.mp
      (mt (hunit b).2 hb)
  have hsum : p ∣ a.val + b.val :=
    dvd_add ha' hb'
  have hmultiple :
      p ∣ p ^ v * ((a.val + b.val) / p ^ v) :=
    dvd_mul_of_dvd_left hmodulus _
  have hrem :
      p ∣ (a.val + b.val) % p ^ v := by
    apply (Nat.dvd_add_iff_left hmultiple).mpr
    simpa only [Nat.mod_add_div] using hsum
  change ¬ IsUnit (a + b)
  intro hab
  apply (hunit (a + b)).1 hab
  rw [ZMod.val_add]
  exact hrem

open scoped Classical in
/-- Over a local ring, the kernel of a surjection between finite free
modules is free.  The proof constructs the splitting explicitly and then
uses finite projective modules over local rings. -/
theorem free_ker_of_surjective_linearMap_of_isLocalRing
    {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N]
    [Module.Free R M] [Module.Free R N]
    [Finite M]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) :
    Module.Free R (LinearMap.ker f) := by
  obtain ⟨sec, hsec⟩ :=
    Module.projective_lifting_property
      f LinearMap.id hf
  let q : M →ₗ[R] M :=
    LinearMap.id - sec.comp f
  have hq (x : M) : q x ∈ LinearMap.ker f := by
    rw [LinearMap.mem_ker]
    change f (x - sec (f x)) = 0
    rw [map_sub]
    have hsec_apply :
        f (sec (f x)) = f x := by
      have :=
        DFunLike.congr_fun hsec (f x)
      simpa using this
    rw [hsec_apply, sub_self]
  let projection : M →ₗ[R] LinearMap.ker f :=
    LinearMap.codRestrict (LinearMap.ker f) q hq
  have hprojection :
      projection.comp (LinearMap.ker f).subtype =
        LinearMap.id := by
    ext x
    change x.1 - sec (f x.1) = x.1
    rw [show f x.1 = 0 from x.2]
    simp
  let : Module.Projective R (LinearMap.ker f) :=
    Module.Projective.of_split
      (LinearMap.ker f).subtype projection hprojection
  let : Module.Finite R (LinearMap.ker f) :=
    Module.Finite.of_finite
  exact Module.free_of_flat_of_isLocalRing

open scoped Classical in
/-- The cardinality of a finite free module is the cardinality of the
coefficient ring raised to the size of a chosen basis. -/
theorem card_eq_card_pow_card_chooseBasisIndex
    {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M]
    [Module.Free R M] [Finite R] [Finite M] :
    Nat.card M =
      Nat.card R ^
        Fintype.card (Module.Free.ChooseBasisIndex R M) := by
  let : Fintype R :=
    Fintype.ofFinite R
  let : Fintype M :=
    Fintype.ofFinite M
  let : Module.Finite R M :=
    Module.Finite.of_finite
  rw [Nat.card_congr
    (Module.Free.chooseBasis R M).repr.toEquiv]
  simp only [Nat.card_eq_fintype_card,
    Fintype.card_finsupp]

open scoped Classical in
/-- Multiplicative product coordinates, interpreted as a `ZMod n`-linear
equivalence on the additive presentations. -/
noncomputable def additiveCoordinatesLinearEquiv
    {G A B : Type*} [CommGroup G] [AddCommGroup A]
    [AddCommGroup B] (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) A] [Module (ZMod n) B]
    (e : G ≃* Multiplicative A × Multiplicative B) :
    Additive G ≃ₗ[ZMod n] A × B := by
  let eAdd : Additive G ≃+ A × B :=
    MulEquiv.toAdditiveLeft e
  exact
  { eAdd with
    map_smul' := by
      simpa using ZMod.map_smul eAdd }

open scoped Classical in
/-- The canonical `ZMod n`-module on the additive presentation of a
commutative group of exponent dividing `n`. -/
@[reducible]
noncomputable def additiveZModModuleOfPowEqOne
    {G : Type*} [CommGroup G] (n : ℕ)
    (h : ∀ g : G, g ^ n = 1) :
    Module (ZMod n) (Additive G) :=
  AddCommGroup.zmodModule <| by
    intro x
    apply Additive.toMul.injective
    simpa using h (Additive.toMul x)

open scoped Classical in
/-- Multiplicative function coordinates, interpreted as a `ZMod n`-linear
equivalence on the additive presentations. -/
noncomputable def additivePiLinearEquiv
    {G A : Type*} [CommGroup G] [AddCommGroup A]
    {ι : Type*} (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) A]
    (e : G ≃* (ι → Multiplicative A)) :
    Additive G ≃ₗ[ZMod n] (ι → A) := by
  let eAdd : Additive G ≃+ (ι → A) :=
    MulEquiv.toAdditiveLeft e
  exact
  { eAdd with
    map_smul' := by
      simpa using ZMod.map_smul eAdd }

open scoped Classical in
/-- The multiplicative kernel of a homomorphism is the multiplicative
presentation of the kernel of its induced `ZMod n`-linear map. -/
noncomputable def monoidKerEquivMultiplicativeLinearKer
    {G H : Type*} [CommGroup G] [CommGroup H]
    (n : ℕ)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) (Additive H)]
    (f : G →* H) :
    f.ker ≃*
      Multiplicative
        (LinearMap.ker
          (f.toAdditive.toZModLinearMap n)) where
  toFun x :=
    Multiplicative.ofAdd
      ⟨Additive.ofMul x.1, by
        rw [LinearMap.mem_ker]
        apply Additive.toMul.injective
        exact x.2⟩
  invFun x :=
    ⟨Additive.toMul (Multiplicative.toAdd x).1, by
      change f (Additive.toMul (Multiplicative.toAdd x).1) = 1
      have hx := (Multiplicative.toAdd x).2
      rw [LinearMap.mem_ker] at hx
      exact congrArg Additive.toMul hx⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    rfl

open scoped Classical in
/-- A surjection between finite free `ZMod (p ^ v)`-modules has a
kernel with genuine coordinates.  Its number of coordinates is read off
from the cardinality of the kernel. -/
theorem exists_kernelMulEquiv_pi_zmod_of_primePower
    {G H : Type*} [CommGroup G] [CommGroup H]
    (n p v q : ℕ)
    (hp : p.Prime) (hv : 0 < v)
    (hn : n = p ^ v)
    [Module (ZMod n) (Additive G)]
    [Module (ZMod n) (Additive H)]
    (freeG : Module.Free (ZMod n) (Additive G))
    (freeH : Module.Free (ZMod n) (Additive H))
    [Finite G]
    (f : G →* H) (hf : Function.Surjective f)
    (hcard : Nat.card f.ker = n ^ q) :
    Nonempty
      (f.ker ≃*
        (Fin q → Multiplicative (ZMod n))) := by
  have hn_one : 1 < n := by
    rw [hn]
    calc
      1 < p := hp.one_lt
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ v :=
        Nat.pow_le_pow_right hp.pos
          (Nat.succ_le_iff.mpr hv)
  let : Module.Free (ZMod n) (Additive G) :=
    freeG
  let : Module.Free (ZMod n) (Additive H) :=
    freeH
  let : NeZero n := ⟨by omega⟩
  let : IsLocalRing (ZMod n) := by
    rw [hn]
    exact zmodPrimePower_isLocalRing p v hp hv
  let fLinear :
      Additive G →ₗ[ZMod n] Additive H :=
    f.toAdditive.toZModLinearMap n
  have hfLinear :
      Function.Surjective fLinear := by
    intro y
    obtain ⟨x, hx⟩ := hf (Additive.toMul y)
    refine ⟨Additive.ofMul x, ?_⟩
    apply Additive.toMul.injective
    exact hx
  let : Module.Free (ZMod n)
      (LinearMap.ker fLinear) :=
    free_ker_of_surjective_linearMap_of_isLocalRing
      fLinear hfLinear
  let : Module.Finite (ZMod n)
      (LinearMap.ker fLinear) :=
    Module.Finite.of_finite
  let I :=
    Module.Free.ChooseBasisIndex
      (ZMod n) (LinearMap.ker fLinear)
  let b₀ :=
    Module.Free.chooseBasis
      (ZMod n) (LinearMap.ker fLinear)
  have hlinearCard :
      Nat.card (LinearMap.ker fLinear) = n ^ q := by
    calc
      Nat.card (LinearMap.ker fLinear) =
          Nat.card (Multiplicative
            (LinearMap.ker fLinear)) := rfl
      _ = Nat.card f.ker :=
        Nat.card_congr
          (monoidKerEquivMultiplicativeLinearKer
            n f).symm.toEquiv
      _ = n ^ q := hcard
  have hbasisCard :
      Nat.card (LinearMap.ker fLinear) =
        n ^ Fintype.card I := by
    simpa only [Nat.card_zmod] using
      (card_eq_card_pow_card_chooseBasisIndex
        (R := ZMod n)
        (M := LinearMap.ker fLinear))
  have hI : Fintype.card I = q := by
    apply Nat.pow_right_injective hn_one
    exact hbasisCard.symm.trans hlinearCard
  let eI : I ≃ Fin q :=
    (Fintype.equivFin I).trans (finCongr hI)
  let b := b₀.reindex eI
  exact ⟨
    (monoidKerEquivMultiplicativeLinearKer n f).trans <|
      b.repr.toAddEquiv.toMultiplicative |>.trans <|
        (Finsupp.addEquivFunOnFinite).toMultiplicative |>.trans
          (MulEquiv.refl _)⟩

open scoped Classical in
/-- The exponent-`n` statement read directly from coordinates
`Gal(E/K) ≃ (Z/nZ)^r`. -/
theorem galois_pow_eq_one_of_equiv_pi_zmod
    {K Omega : Type*} [Field K] [Field Omega] [Algebra K Omega]
    (E : IntermediateField K Omega)
    (n : ℕ+) (r : ℕ)
    (eG :
      (E ≃ₐ[K] E) ≃*
        (Fin r → Multiplicative (ZMod (n : ℕ))))
    (sigma : E ≃ₐ[K] E) :
    sigma ^ (n : ℕ) = 1 := by
  apply eG.injective
  rw [map_pow, map_one]
  ext i
  apply Multiplicative.toAdd.injective
  change
    (n : ℕ) • Multiplicative.toAdd (eG sigma i) = 0
  simp

end KummerTheory
