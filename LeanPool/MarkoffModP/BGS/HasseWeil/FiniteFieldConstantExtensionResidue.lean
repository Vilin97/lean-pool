/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantTensorResidue
import LeanPool.MarkoffModP.BGS.HasseWeil.FiniteFieldConstantExtensionNormalization

/-!
# Residue degrees after finite constant extension

This file transports the abstract residue-tensor calculation across the
normalization equivalence.  If `q` is a maximal ideal of the normalization
after extending finite constants from `C` to `S`, and `p` is its contraction
to the old normalization, then

`[κ(q) : C] = lcm([S : C], [κ(p) : C])`

and hence

`[κ(q) : S] = [κ(p) : C] / gcd([S : C], [κ(p) : C])`.

In particular, `q` is rational over `S` whenever the downstairs residue
degree divides `[S : C]`.
-/

open scoped Polynomial TensorProduct

namespace BGS.HasseWeil

noncomputable section

variable (C S N : Type*) [Field C] [Field S] [Algebra C S]
  [Fintype C] [Finite S]
  [CommRing N] [Algebra C[X] N]

local instance constantExtensionResidueBaseConstantAlgebra : Algebra C N :=
  RingHom.toAlgebra ((algebraMap C[X] N).comp (algebraMap C C[X]))

local instance constantExtensionResidueBaseConstantPolynomialTower :
    IsScalarTower C C[X] N :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance constantExtensionResidueCoefficientPolynomialAlgebra :
    Algebra C[X] S[X] :=
  Polynomial.algebra C S

local instance constantExtensionResidueOldNormalizationConstantAlgebra :
    Algebra C (integralClosure C[X] N) :=
  RingHom.toAlgebra
    ((algebraMap C[X] (integralClosure C[X] N)).comp
      (algebraMap C C[X]))

local instance constantExtensionResidueTargetPolynomialAlgebra :
    Algebra S[X] (S ⊗[C] N) :=
  polynomialTensorCancelTargetPolynomialExtensionAlgebra C S N

local instance constantExtensionResidueTargetConstantAlgebra :
    Algebra S (S ⊗[C] N) :=
  Algebra.TensorProduct.leftAlgebra

local instance constantExtensionResidueTargetConstantPolynomialTower :
    IsScalarTower S S[X] (S ⊗[C] N) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro s
    change s ⊗ₜ[C] (1 : N) =
      Polynomial.aeval
        (polynomialTensorCancelEvaluationPoint C S N) (Polynomial.C s)
    simp)

local instance constantExtensionResidueTargetNormalizationConstantAlgebra :
    Algebra S (integralClosure S[X] (S ⊗[C] N)) :=
  RingHom.toAlgebra
    ((algebraMap S[X] (integralClosure S[X] (S ⊗[C] N))).comp
      (algebraMap S S[X]))

local instance constantExtensionResidueTargetNormalizationBaseAlgebra :
    Algebra C (integralClosure S[X] (S ⊗[C] N)) :=
  RingHom.toAlgebra
    ((algebraMap S (integralClosure S[X] (S ⊗[C] N))).comp
      (algebraMap C S))

local instance constantExtensionResidueTargetNormalizationConstantTower :
    IsScalarTower C S (integralClosure S[X] (S ⊗[C] N)) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Pull a maximal ideal of the base-changed normalization back to the tensor
model of that normalization. -/
def finiteFieldConstantExtensionTensorIdeal
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) :
    Ideal (S ⊗[C] integralClosure C[X] N) :=
  q.comap
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).toRingHom

/-- The inclusion of the old normalization into the normalization after
constant extension. -/
def finiteFieldConstantExtensionIntegralClosureAlgHom :
    integralClosure C[X] N →ₐ[C]
      integralClosure S[X] (S ⊗[C] N) :=
  ((finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).restrictScalars
      C).toAlgHom.comp
    (Algebra.TensorProduct.includeRight
      (R := C) (A := S) (B := integralClosure C[X] N))

/-- Ring-homomorphism form of the old-normalization inclusion. -/
def finiteFieldConstantExtensionIntegralClosureRingHom :
    integralClosure C[X] N →+*
      integralClosure S[X] (S ⊗[C] N) :=
  (finiteFieldConstantExtensionIntegralClosureAlgHom C S N).toRingHom

/-- Contract an upstairs maximal ideal to the old normalization. -/
def finiteFieldConstantExtensionDownstairsIdeal
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) :
    Ideal (integralClosure C[X] N) :=
  q.comap (finiteFieldConstantExtensionIntegralClosureRingHom C S N)

@[simp]
theorem finiteFieldConstantExtensionDownstairsIdeal_eq
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) :
    finiteFieldConstantExtensionDownstairsIdeal C S N q =
      (finiteFieldConstantExtensionTensorIdeal C S N q).comap
        (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom :=
  rfl

@[simp]
theorem finiteFieldConstantExtensionIntegralClosureRingHom_coe
    (a : integralClosure C[X] N) :
    (((finiteFieldConstantExtensionIntegralClosureRingHom C S N a :
        integralClosure S[X] (S ⊗[C] N)) : S ⊗[C] N)) =
      (1 : S) ⊗ₜ[C] (a : N) := by
  exact finiteFieldConstantExtensionIntegralClosureAlgEquiv_tmul
    C S N 1 a

local instance finiteFieldConstantExtensionTensorIdeal_isMaximal
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal] :
    (finiteFieldConstantExtensionTensorIdeal C S N q).IsMaximal := by
  unfold finiteFieldConstantExtensionTensorIdeal
  exact Ideal.comap_isMaximal_of_surjective
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).toRingHom
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N).surjective

local instance finiteFieldConstantExtensionDownstairsIdeal_isPrime
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal] :
    (finiteFieldConstantExtensionDownstairsIdeal C S N q).IsPrime := by
  unfold finiteFieldConstantExtensionDownstairsIdeal
  exact Ideal.comap_isPrime
    (f := finiteFieldConstantExtensionIntegralClosureRingHom C S N)
    (K := q)

/-- The normalization equivalence induces an `S`-algebra equivalence of the
corresponding residue fields. -/
def finiteFieldConstantExtensionResidueFieldAlgEquiv
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal] :
    (finiteFieldConstantExtensionTensorIdeal C S N q).ResidueField ≃ₐ[S]
      q.ResidueField :=
  Ideal.residueFieldAlgEquiv
    (finiteFieldConstantExtensionTensorIdeal C S N q) q
    (finiteFieldConstantExtensionIntegralClosureAlgEquiv C S N) rfl

local instance finiteFieldConstantExtensionTensorResidueFinite
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField] :
    Finite (finiteFieldConstantExtensionTensorIdeal C S N q).ResidueField :=
  let eS := finiteFieldConstantExtensionResidueFieldAlgEquiv C S N q
  Finite.of_injective eS eS.injective

local instance finiteFieldConstantExtensionDownstairsResidueFinite
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField] :
    Finite
      (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField := by
  let q₀ := finiteFieldConstantExtensionTensorIdeal C S N q
  let p := finiteFieldConstantExtensionDownstairsIdeal C S N q
  let fp : p.ResidueField →ₐ[C] q₀.ResidueField :=
    Ideal.ResidueField.mapₐ p q₀
      (Algebra.TensorProduct.includeRight
        (R := C) (A := S) (B := integralClosure C[X] N)) rfl
  exact Finite.of_injective fp fp.injective

/-- The contraction of an upstairs maximal ideal is maximal.  The proof uses
the already established embedding of its residue field into the finite
upstairs residue field: the downstairs quotient is therefore a finite domain,
and hence a field. -/
theorem finiteFieldConstantExtensionDownstairsIdeal_isMaximal
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField] :
    (finiteFieldConstantExtensionDownstairsIdeal C S N q).IsMaximal := by
  let p := finiteFieldConstantExtensionDownstairsIdeal C S N q
  let : Finite p.ResidueField := by
    change Finite
      (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField
    infer_instance
  let : Finite (integralClosure C[X] N ⧸ p) :=
    Finite.of_injective
      (algebraMap (integralClosure C[X] N ⧸ p) p.ResidueField)
      p.injective_algebraMap_quotient_residueField
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mpr
    (Finite.isField_of_domain (integralClosure C[X] N ⧸ p))

/-- Absolute residue-degree form of the constant-extension compositum
formula. -/
theorem finiteFieldConstantExtensionResidue_finrank_eq_lcm
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField] :
    Module.finrank C q.ResidueField =
      Nat.lcm (Module.finrank C S)
        (Module.finrank C
          (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField) := by
  let q₀ := finiteFieldConstantExtensionTensorIdeal C S N q
  let : q₀.IsMaximal :=
    finiteFieldConstantExtensionTensorIdeal_isMaximal C S N q
  let eS := finiteFieldConstantExtensionResidueFieldAlgEquiv C S N q
  let p := q₀.comap (Algebra.TensorProduct.includeRight
    (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom
  let : Finite p.ResidueField := by
    change Finite
      (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField
    infer_instance
  have h := constantTensorResidue_finrank_eq_lcm
    C (integralClosure C[X] N) S q₀
  change Module.finrank C q.ResidueField =
    Nat.lcm (Module.finrank C S)
      (Module.finrank C
        (q₀.comap (Algebra.TensorProduct.includeRight
          (R := C) (A := S) (B := integralClosure C[X] N)).toRingHom).ResidueField)
  calc
    Module.finrank C q.ResidueField = Module.finrank C q₀.ResidueField :=
      (eS.restrictScalars C).toLinearEquiv.finrank_eq.symm
    _ = _ := h

/-- Relative residue-degree form of the constant-extension compositum
formula. -/
theorem finiteFieldConstantExtensionResidue_finrank_over_constants_eq_div_gcd
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField] :
    Module.finrank S q.ResidueField =
      Module.finrank C
          (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField /
        Nat.gcd (Module.finrank C S)
          (Module.finrank C
            (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField) := by
  let m := Module.finrank C S
  let n := Module.finrank C
    (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField
  let d := Nat.gcd m n
  let l := Nat.lcm m n
  let r := Module.finrank S q.ResidueField
  have htotal : Module.finrank C q.ResidueField = l :=
    finiteFieldConstantExtensionResidue_finrank_eq_lcm C S N q
  have hmr : m * r = l := by
    exact (Module.finrank_mul_finrank C S q.ResidueField).trans htotal
  have hdr : d * r = n := by
    apply Nat.mul_left_cancel
      (Module.finrank_pos (R := C) (M := S))
    calc
      m * (d * r) = d * (m * r) := by ac_rfl
      _ = d * l := by rw [hmr]
      _ = m * n := Nat.gcd_mul_lcm m n
  have hdpos : 0 < d := Nat.gcd_pos_of_pos_left n
    (Module.finrank_pos (R := C) (M := S))
  change r = n / d
  symm
  apply Nat.div_eq_of_eq_mul_left hdpos
  simpa [mul_comm] using hdr.symm

/-- If the downstairs residue degree divides the constant-extension degree,
then the upstairs maximal ideal has residue degree one over the enlarged
constants. -/
theorem finiteFieldConstantExtensionResidue_finrank_eq_one_of_dvd
    (q : Ideal (integralClosure S[X] (S ⊗[C] N))) [q.IsMaximal]
    [Finite q.ResidueField]
    (hdiv : Module.finrank C
        (finiteFieldConstantExtensionDownstairsIdeal C S N q).ResidueField ∣
      Module.finrank C S) :
    Module.finrank S q.ResidueField = 1 := by
  rw [finiteFieldConstantExtensionResidue_finrank_over_constants_eq_div_gcd
    C S N q]
  rw [Nat.gcd_eq_right_iff_dvd.mpr hdiv]
  exact Nat.div_self
    (Module.finrank_pos (R := C)
      (M := (finiteFieldConstantExtensionDownstairsIdeal
        C S N q).ResidueField))

end


end BGS.HasseWeil
