/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.Galois.Abelian
/-!
# Abelian Galois extensions under equivalent field presentations

Compatible equivalences of the base and extension fields identify their
Galois automorphisms and preserve the abelian Galois property. These results
use only Mathlib's algebra and Galois APIs; they do not depend on local class
field theory or ramification.
-/

@[expose] public section

noncomputable
section

namespace ClassFieldTheory

/-- Abelian Galois extensions remain abelian Galois after compatible ring
equivalences on both the base and extension fields. -/
theorem isAbelianGalois_of_equiv_equiv
    {K L M N : Type*}
    [Field K] [Field L] [Algebra K L] [IsAbelianGalois K L]
    [Field M] [Field N] [Algebra M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L)) :
    IsAbelianGalois M N := by
  let : IsGalois M N := IsGalois.of_equiv_equiv (f := f) (g := g) hcomp
  have hbase (x : K) :
      g (algebraMap K L x) = algebraMap M N (f x) := by
    exact congrArg (fun h : K →+* N => h x) hcomp.symm
  let transport (σ : Gal(N/M)) : Gal(L/K) :=
    AlgEquiv.ofRingEquiv
      (f := (g.trans σ.toRingEquiv).trans g.symm) (by
        intro x
        apply g.injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
        rw [hbase]
        change σ (algebraMap M N (f x)) = algebraMap M N (f x)
        exact σ.commutes (f x))
  have htransport_mul (σ τ : Gal(N/M)) :
      transport (σ * τ) = transport σ * transport τ := by
    ext x
    simp only [transport, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
      AlgEquiv.mul_apply, RingEquiv.apply_symm_apply]
    congr 1
  have htransport_injective : Function.Injective transport := by
    intro σ τ h
    ext x
    have hx := congrArg (fun e : Gal(L/K) => e (g.symm x)) h
    have hx' := congrArg g hx
    change σ.toRingEquiv x = τ.toRingEquiv x
    simpa only [transport,
      AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
      RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply] using hx'
  let : IsMulCommutative Gal(N/M) :=
    .of_comm fun σ τ => htransport_injective (by
      calc
        transport (σ * τ) = transport σ * transport τ := htransport_mul σ τ
        _ = transport τ * transport σ := mul_comm' _ _
        _ = transport (τ * σ) := (htransport_mul τ σ).symm)
  exact { }

/-- Compatible equivalences of field extensions identify their Galois
automorphisms by conjugation. -/
noncomputable def galEquivOfEquivEquiv
    {K L M N : Type*}
    [Field K] [Field L] [Algebra K L]
    [Field M] [Field N] [Algebra M N]
    (f : K ≃+* M) (g : L ≃+* N)
    (hcomp : (algebraMap M N).comp f.toRingHom =
      g.toRingHom.comp (algebraMap K L)) :
    Gal(N/M) ≃ Gal(L/K) := by
  have hbase (x : K) :
      g (algebraMap K L x) = algebraMap M N (f x) :=
    congrArg (fun h : K →+* N => h x) hcomp.symm
  have hbase' (x : M) :
      g.symm (algebraMap M N x) = algebraMap K L (f.symm x) := by
    apply g.injective
    rw [g.apply_symm_apply, hbase, f.apply_symm_apply]
  let forward (σ : Gal(N/M)) : Gal(L/K) :=
    AlgEquiv.ofRingEquiv
      (f := (g.trans σ.toRingEquiv).trans g.symm) (by
        intro x
        apply g.injective
        simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
        rw [hbase]
        change σ (algebraMap M N (f x)) = algebraMap M N (f x)
        exact σ.commutes (f x))
  let backward (τ : Gal(L/K)) : Gal(N/M) :=
    AlgEquiv.ofRingEquiv
      (f := (g.symm.trans τ.toRingEquiv).trans g) (by
        intro x
        apply g.symm.injective
        simp only [RingEquiv.trans_apply, RingEquiv.symm_apply_apply]
        rw [hbase']
        change τ (algebraMap K L (f.symm x)) = algebraMap K L (f.symm x)
        exact τ.commutes (f.symm x))
  refine {
    toFun := forward
    invFun := backward
    left_inv := ?_
    right_inv := ?_ }
  · intro σ
    ext x
    simp [forward, backward, AlgEquiv.ofRingEquiv_apply]
  · intro τ
    ext x
    simp [forward, backward, AlgEquiv.ofRingEquiv_apply]

end ClassFieldTheory
