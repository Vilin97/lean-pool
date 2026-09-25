/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
/-!
# Prime cyclotomic base change

This file constructs the roots-of-unity base change for a prime-degree
extension.  If `L / K` has prime degree `p`, the
cyclotomic extension `K(μ_p) / K` has degree strictly smaller than `p`.
The two degrees are therefore coprime, and

`K(μ_p) ⊗[K] L`

is an actual field, Galois of degree `p` over `K(μ_p)`.
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace KummerTheory

universe u

variable
    (K L : Type u)
    [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L]

/-- Over a characteristic-zero field, the concrete cyclotomic field
of order `m` has degree at most `φ(m)`. -/
theorem cyclotomicField_finrank_le_totient
    (F : Type*) [Field F] [CharZero F]
    (m : ℕ) (hm : 0 < m) :
    Module.finrank F (CyclotomicField m F) ≤
      Nat.totient m := by
  let : NeZero m := ⟨hm.ne'⟩
  let C := CyclotomicField m F
  let : IsCyclotomicExtension {m} F C :=
    CyclotomicField.isCyclotomicExtension m F
  let : FiniteDimensional F C :=
    IsCyclotomicExtension.finiteDimensional {m} F C
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension m F).exists_isPrimitiveRoot
      (Set.mem_singleton m) hm.ne'
  have hgen : Algebra.adjoin F ({ζ} : Set C) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ
  have htop :
      IntermediateField.adjoin F ({ζ} : Set C) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_algebra
      F ({ζ} : Set C) hgen
  have hroot :
      Polynomial.aeval ζ
          (Polynomial.cyclotomic m F) = 0 := by
    rw [Polynomial.aeval_def,
      Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic,
      ← Polynomial.IsRoot.def]
    exact hζ.isRoot_cyclotomic hm
  have hdegree :
      (minpoly F ζ).natDegree ≤
        (Polynomial.cyclotomic m F).natDegree :=
    Polynomial.natDegree_le_natDegree
      (minpoly.min F ζ
        (Polynomial.cyclotomic.monic m F) hroot)
  calc
    Module.finrank F (CyclotomicField m F) =
        Module.finrank F C := rfl
    _ = Module.finrank F
          (IntermediateField.adjoin F ({ζ} : Set C)) := by
      rw [htop]
      simp
    _ = (minpoly F ζ).natDegree :=
      IntermediateField.adjoin.finrank
        (IsIntegral.of_finite F ζ)
    _ ≤ (Polynomial.cyclotomic m F).natDegree :=
      hdegree
    _ = Nat.totient m :=
      Polynomial.natDegree_cyclotomic m F

/-- The prime cyclotomic base field used for prime-degree base change. -/
abbrev PrimeCyclotomicBase (p : ℕ) :=
  CyclotomicField p K

/-- The tensor-product compositum of `L` and the prime cyclotomic
base field.  Its field structure is constructed below from coprime
degrees. -/
abbrev PrimeCyclotomicPushout (p : ℕ) :=
  PrimeCyclotomicBase K p ⊗[K] L

noncomputable instance primeCyclotomicBaseFiniteDimensional
    (p : ℕ) :
    FiniteDimensional K (PrimeCyclotomicBase K p) :=
  IsCyclotomicExtension.finiteDimensional
    {p} K (PrimeCyclotomicBase K p)

noncomputable instance primeCyclotomicBaseIsGalois
    (p : ℕ) :
    IsGalois K (PrimeCyclotomicBase K p) :=
  IsCyclotomicExtension.isGalois
    {p} K (PrimeCyclotomicBase K p)

noncomputable instance primeCyclotomicBaseNumberField
    (p : ℕ) [NeZero p] :
    NumberField (PrimeCyclotomicBase K p) :=
  NumberField.of_module_finite K
    (PrimeCyclotomicBase K p)

/-- Over a characteristic-zero field, the degree of `K(μ_p)` is
strictly smaller than the prime `p`. -/
theorem primeCyclotomicBase_finrank_lt
    (p : ℕ) (hp : p.Prime) :
    Module.finrank K (PrimeCyclotomicBase K p) < p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  have hle :
      Module.finrank K (PrimeCyclotomicBase K p) ≤
        Nat.totient p :=
    cyclotomicField_finrank_le_totient
      K p hp.pos
  rw [Nat.totient_prime hp] at hle
  exact hle.trans_lt (Nat.sub_one_lt hp.ne_zero)

omit [NumberField L] [IsGalois K L] in
/-- The cyclotomic degree is coprime to a prime-degree extension. -/
theorem primeCyclotomicBase_finrank_coprime
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    (Module.finrank K (PrimeCyclotomicBase K p)).Coprime
      (Module.finrank K L) := by
  rw [hdegree]
  exact
    (Nat.coprime_of_lt_prime
      (ne_of_gt Module.finrank_pos)
      (primeCyclotomicBase_finrank_lt
        (K := K) p hp)
      hp).symm

/-- The field structure on the prime cyclotomic pushout, obtained
from coprime degrees. -/
@[reducible]
noncomputable def primeCyclotomicPushoutField
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    Field (PrimeCyclotomicPushout K L p) :=
  (tensorProduct_isField_of_finrank_coprime
    K (PrimeCyclotomicBase K p) L
    (primeCyclotomicBase_finrank_coprime
      (K := K) (L := L) p hp hdegree)).toField

/-- The canonical left-factor algebra structure, restated after
installing the field structure on the tensor product. -/
@[reducible]
noncomputable def primeCyclotomicPushoutAlgebra
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) := by
  letI : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  exact Algebra.TensorProduct.leftAlgebra

omit [IsGalois K L] in
/-- The pushout has the expected degree over the cyclotomic base. -/
theorem primeCyclotomicPushout_finrank
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    Module.finrank
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) =
      p := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  rw [Module.finrank_baseChange, hdegree]

/-- The prime cyclotomic pushout is Galois over `K(μ_p)`. -/
theorem primeCyclotomicPushout_isGalois
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  exact
    tensorProduct_isGalois_of_finrank_coprime
      K (PrimeCyclotomicBase K p) L
      (primeCyclotomicBase_finrank_coprime
        (K := K) (L := L) p hp hdegree)

omit [IsGalois K L] in
/-- The prime cyclotomic pushout is again a number field. -/
theorem primeCyclotomicPushout_numberField
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    NumberField (PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  exact
    NumberField.of_module_finite
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p)

/-- The cyclotomic base contains a primitive `p`-th root of unity. -/
theorem primeCyclotomicBase_primitiveRoots_nonempty
    (p : ℕ) (hp : p.Prime) :
    (primitiveRoots p (PrimeCyclotomicBase K p)).Nonempty := by
  let : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ :=
    (CyclotomicField.isCyclotomicExtension p K).exists_isPrimitiveRoot
      (Set.mem_singleton p) hp.ne_zero
  exact ⟨ζ, (mem_primitiveRoots hp.pos).2 hζ⟩

/-- The Galois group after cyclotomic base change is cyclic of prime
order. -/
theorem primeCyclotomicPushout_isCyclic
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    letI : IsGalois
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushout_isGalois
        K L p hp hdegree
    IsCyclic
      (PrimeCyclotomicPushout K L p ≃ₐ[PrimeCyclotomicBase K p]
        PrimeCyclotomicPushout K L p) := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  let : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  let : IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let : Fact p.Prime := ⟨hp⟩
  exact
    isCyclic_of_prime_card (p := p) (by
      rw [IsGalois.card_aut_eq_finrank,
        primeCyclotomicPushout_finrank
          K L p hp hdegree])

/-- Prime-degree Kummer coordinates for the base-changed Galois group,
in the exact one-coordinate form used by the prime-degree Kummer coordinate construction. -/
noncomputable def primeCyclotomicPushoutGalEquivPiZMod
    (p : ℕ) (hp : p.Prime)
    (hdegree : Module.finrank K L = p) :
    letI : NeZero p := ⟨hp.ne_zero⟩
    letI : Field (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutField K L p hp hdegree
    letI : Algebra
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushoutAlgebra K L p hp hdegree
    letI : IsGalois
        (PrimeCyclotomicBase K p)
        (PrimeCyclotomicPushout K L p) :=
      primeCyclotomicPushout_isGalois
        K L p hp hdegree
    (PrimeCyclotomicPushout K L p ≃ₐ[PrimeCyclotomicBase K p]
        PrimeCyclotomicPushout K L p) ≃*
      (Fin 1 → Multiplicative (ZMod p)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  letI : Field (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutField K L p hp hdegree
  letI : Algebra
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushoutAlgebra K L p hp hdegree
  letI : IsGalois
      (PrimeCyclotomicBase K p)
      (PrimeCyclotomicPushout K L p) :=
    primeCyclotomicPushout_isGalois
      K L p hp hdegree
  let G :=
    PrimeCyclotomicPushout K L p ≃ₐ[PrimeCyclotomicBase K p]
      PrimeCyclotomicPushout K L p
  letI : IsCyclic G :=
    primeCyclotomicPushout_isCyclic
      K L p hp hdegree
  have hcardG : Nat.card G = p := by
    dsimp only [G]
    rw [IsGalois.card_aut_eq_finrank,
      primeCyclotomicPushout_finrank
        K L p hp hdegree]
  exact
    (hcardG ▸ (zmodCyclicMulEquiv
      (inferInstance : IsCyclic G)).symm).trans
      (MulEquiv.piUnique
        (fun _ : Fin 1 => Multiplicative (ZMod p))).symm

end KummerTheory
