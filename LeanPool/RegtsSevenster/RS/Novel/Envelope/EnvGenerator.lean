/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Envelope.EnvInstances
public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.TensorPow

/-!
# The strand generator of the envelope

The embedded strand objects of the envelope and their tensor
calculus: the `n`-strand envelope object is the `n`-th tensor
power of the single strand, up to canonical isomorphism.  This is
the spine of the Deligne generator and moderate-growth fields.
-/

@[expose] public section

namespace RS

open CategoryTheory CategoryTheory.Category CategoryTheory.Idempotents
open CategoryTheory.Limits MonoidalCategory

universe v u

variable {R : ℕ} (f : EdgeRankParameter R)

/-! ### Object-level equalities in Karoubi envelopes -/

/-- Karoubi objects with equal idempotents are equal. -/
theorem karoubi_obj_ext {D : Type u} [Category.{v} D] {X : D}
    {p q : X ⟶ X} (h : p = q) {hp : p ≫ p = p} {hq : q ≫ q = q} :
    (⟨X, p, hp⟩ : Karoubi D) = ⟨X, q, hq⟩ := by
  subst h; rfl

/-! ### The embedded strands -/

/-- The embedded `n`-strand object of the corner category. -/
noncomputable def strandK (n : ℕ) : Karoubi (SkeinObj f) :=
  (toKaroubi (SkeinObj f)).obj (SkeinObj.mk n)

/-- The embedded `n`-strand object of the envelope. -/
noncomputable def envStrand (n : ℕ) : Env f :=
  (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).obj
    ((Mat_.embedding (Karoubi (SkeinObj f))).obj (strandK f n))

/-- Strand corner objects multiply arities. -/
theorem strandK_tensor (a b : ℕ) :
    strandK f a ⊗ strandK f b = strandK f (a + b) :=
  karoubi_obj_ext (skein_tensor_id f (SkeinObj.mk a) (SkeinObj.mk b))

/-! ### The matrix embedding is tensor-compatible -/

section MatEmb

variable {D : Type u}

/-- The diagonal comparison from the tensor of embeddings to the
embedding of the tensor. -/
noncomputable def matEmbTensorHom
    [Category.{v} D] [Preadditive D] [MonoidalCategory D]
    (x y : D) :
    (Mat_.embedding D).obj x ⊗ (Mat_.embedding D).obj y ⟶
      (Mat_.embedding D).obj (x ⊗ y) :=
  fun _ _ => 𝟙 (x ⊗ y)

/-- The diagonal comparison from the embedding of the tensor to
the tensor of embeddings. -/
noncomputable def matEmbTensorInv
    [Category.{v} D] [Preadditive D] [MonoidalCategory D]
    (x y : D) :
    (Mat_.embedding D).obj (x ⊗ y) ⟶
      (Mat_.embedding D).obj x ⊗ (Mat_.embedding D).obj y :=
  fun _ _ => 𝟙 (x ⊗ y)

/-- The diagonal isomorphism between the tensor of embeddings and
the embedding of the tensor. -/
noncomputable def matEmbTensorIso
    [Category.{v} D] [Preadditive D] [MonoidalCategory D]
    (x y : D) :
    (Mat_.embedding D).obj x ⊗ (Mat_.embedding D).obj y ≅
      (Mat_.embedding D).obj (x ⊗ y) where
  hom := matEmbTensorHom x y
  inv := matEmbTensorInv x y
  hom_inv_id := by
    apply Mat_.hom_ext
    intro i j
    have : Subsingleton (((Mat_.embedding D).obj x ⊗
        (Mat_.embedding D).obj y).ι) :=
      inferInstanceAs (Subsingleton (PUnit × PUnit))
    obtain rfl : i = j := Subsingleton.elim i j
    rw [Mat_.comp_apply, Mat_.id_apply_self]
    change ∑ _j : PUnit, 𝟙 (x ⊗ y) ≫ 𝟙 (x ⊗ y) = 𝟙 (x ⊗ y)
    simp
  inv_hom_id := by
    apply Mat_.hom_ext
    intro i j
    have : Subsingleton
        (((Mat_.embedding D).obj (x ⊗ y)).ι) :=
      inferInstanceAs (Subsingleton PUnit)
    obtain rfl : i = j := Subsingleton.elim i j
    rw [Mat_.comp_apply, Mat_.id_apply_self]
    change ∑ _j : PUnit × PUnit, 𝟙 (x ⊗ y) ≫ 𝟙 (x ⊗ y) =
      𝟙 (x ⊗ y)
    simp

end MatEmb

/-! ### The Karoubi embedding is tensor-compatible -/

/-- The embedding into the Karoubi envelope carries tensor to
tensor, on the nose. -/
theorem toKaroubi_tensor {D : Type u} [Category.{v} D]
    [MonoidalCategory D] (A B : D) :
    (toKaroubi D).obj A ⊗ (toKaroubi D).obj B =
      (toKaroubi D).obj (A ⊗ B) :=
  karoubi_obj_ext (by simp)

/-! ### The strand tensor calculus in the envelope -/

/-- The strand objects of the envelope multiply arities. -/
noncomputable def envStrandTensorIso (a b : ℕ) :
    envStrand f a ⊗ envStrand f b ≅ envStrand f (a + b) :=
  eqToIso (toKaroubi_tensor _ _) ≪≫
    (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).mapIso
      (matEmbTensorIso (strandK f a) (strandK f b) ≪≫
        eqToIso (congrArg (Mat_.embedding
          (Karoubi (SkeinObj f))).obj (strandK_tensor f a b)))

/-- The zero strand of the envelope is the unit. -/
theorem envStrand_zero : envStrand f 0 = 𝟙_ (Env f) := rfl

/-- **The strand power isomorphism**: the `n`-th tensor power of
the single strand is the `n`-strand object. -/
noncomputable def envStrandPowIso :
    (n : ℕ) → tensorPow (Env f) (envStrand f 1) n ≅ envStrand f n
  | 0 => eqToIso (envStrand_zero f).symm
  | n + 1 =>
    tensorIso (envStrandPowIso n) (Iso.refl (envStrand f 1)) ≪≫
      envStrandTensorIso f n 1

/-! ### Retracts through the layers -/

/-- The ambient section: an envelope object into the full matrix
object it corners. -/
noncomputable def envAmbientSec (E : Env f) :
    E ⟶ (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).obj E.X :=
  ⟨E.p, by
    change E.p ≫ E.p ≫ 𝟙 E.X = E.p
    rw [comp_id]; exact E.idem⟩

/-- The ambient retraction. -/
noncomputable def envAmbientRet (E : Env f) :
    (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).obj E.X ⟶ E :=
  ⟨E.p, by
    change 𝟙 E.X ≫ E.p ≫ E.p = E.p
    rw [id_comp]; exact E.idem⟩

/-- The envelope object is a retract of its ambient object. -/
theorem envAmbientSec_ret (E : Env f) :
    envAmbientSec f E ≫ envAmbientRet f E = 𝟙 E := by
  apply Karoubi.hom_ext
  change E.p ≫ E.p = E.p
  exact E.idem

/-- The corner section: a skein corner into its full strand. -/
noncomputable def cornerSecK (x : Karoubi (SkeinObj f)) :
    x ⟶ strandK f x.X.arity :=
  ⟨x.p, by
    change x.p ≫ x.p ≫ 𝟙 (SkeinObj.mk x.X.arity) = x.p
    rw [comp_id]; exact x.idem⟩

/-- The corner retraction. -/
noncomputable def cornerRetK (x : Karoubi (SkeinObj f)) :
    strandK f x.X.arity ⟶ x :=
  ⟨x.p, by
    change 𝟙 (SkeinObj.mk x.X.arity) ≫ x.p ≫ x.p = x.p
    rw [id_comp]; exact x.idem⟩

/-- A Karoubi object is a retract of its corner in the
envelope. -/
theorem cornerSecK_ret (x : Karoubi (SkeinObj f)) :
    cornerSecK f x ≫ cornerRetK f x = 𝟙 x := by
  apply Karoubi.hom_ext
  change x.p ≫ x.p = x.p
  exact x.idem

/-- The embedded corner object of the envelope. -/
noncomputable def envEmb (x : Karoubi (SkeinObj f)) : Env f :=
  (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).obj
    ((Mat_.embedding (Karoubi (SkeinObj f))).obj x)

/-- The embedded corner section into its strand object. -/
noncomputable def envEmbSec (x : Karoubi (SkeinObj f)) :
    envEmb f x ⟶ envStrand f x.X.arity :=
  (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).map
    ((Mat_.embedding (Karoubi (SkeinObj f))).map (cornerSecK f x))

/-- The embedded corner retraction. -/
noncomputable def envEmbRet (x : Karoubi (SkeinObj f)) :
    envStrand f x.X.arity ⟶ envEmb f x :=
  (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).map
    ((Mat_.embedding (Karoubi (SkeinObj f))).map (cornerRetK f x))

/-- And the embedding of a Karoubi object is a retract of it —
the three sections that make the strand generator work. -/
theorem envEmbSec_ret (x : Karoubi (SkeinObj f)) :
    envEmbSec f x ≫ envEmbRet f x = 𝟙 (envEmb f x) := by
  have h := congrArg (fun t =>
    (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).map
      ((Mat_.embedding (Karoubi (SkeinObj f))).map t))
    (cornerSecK_ret f x)
  simp only [Functor.map_comp] at h
  refine h.trans ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  rfl

/-! ### The biproduct decomposition of a matrix object -/

/-- A matrix object of the envelope is the biproduct of its
embedded entries. -/
noncomputable def envMatDecomp (A : Mat_ (Karoubi (SkeinObj f))) :
    (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).obj A ≅
      ⨁ fun i : A.ι => envEmb f (A.X i) :=
  (toKaroubi (Mat_ (Karoubi (SkeinObj f)))).mapIso
      A.isoBiproductEmbedding ≪≫
    Functor.mapBiproduct _ _

/-! ### The generator field -/

-- Raised budget: the retract is built from a finite biproduct
-- indexed by the object's own index type, so the biproduct
-- structure is unfolded.
/-- **The strand generates the envelope**: every object is a
retract of a finite biproduct of tensor powers of the single
strand. -/
theorem env_strandRetract :
    RetractGeneratedBy (Env f) (envStrand f 1) := by
  classical
  intro E
  set A := E.X with hA
  let q : Fin (Fintype.card A.ι) ≃ A.ι :=
    (Fintype.equivFin A.ι).symm
  let ns : Fin (Fintype.card A.ι) → ℕ :=
    fun i => ((A.X (q i)).X).arity
  let L : (⨁ fun i : A.ι => envEmb f (A.X i)) ⟶
      ⨁ fun i => tensorPow (Env f) (envStrand f 1) (ns i) :=
    biproduct.lift fun i =>
      biproduct.π (fun i : A.ι => envEmb f (A.X i)) (q i) ≫
      envEmbSec f (A.X (q i)) ≫ (envStrandPowIso f (ns i)).inv
  let D : (⨁ fun i => tensorPow (Env f) (envStrand f 1) (ns i)) ⟶
      ⨁ fun i : A.ι => envEmb f (A.X i) :=
    biproduct.desc fun i => (envStrandPowIso f (ns i)).hom ≫
      envEmbRet f (A.X (q i)) ≫
      biproduct.ι (fun i : A.ι => envEmb f (A.X i)) (q i)
  have hLD : L ≫ D = 𝟙 _ := by
    rw [biproduct.lift_desc]
    rw [Finset.sum_congr rfl fun i _ => show
      (biproduct.π (fun i : A.ι => envEmb f (A.X i)) (q i) ≫
        envEmbSec f (A.X (q i)) ≫
        (envStrandPowIso f (ns i)).inv) ≫
      ((envStrandPowIso f (ns i)).hom ≫
        envEmbRet f (A.X (q i)) ≫
        biproduct.ι (fun i : A.ι => envEmb f (A.X i)) (q i)) =
      biproduct.π (fun i : A.ι => envEmb f (A.X i)) (q i) ≫
        biproduct.ι (fun i : A.ι => envEmb f (A.X i)) (q i) from by
      simp only [assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% (envEmbSec_ret f (A.X (q i)))]]
    rw [Equiv.sum_comp q (fun j =>
      biproduct.π (fun i : A.ι => envEmb f (A.X i)) j ≫
        biproduct.ι (fun i : A.ι => envEmb f (A.X i)) j)]
    exact biproduct.total
  refine ⟨Fintype.card A.ι, ns,
    envAmbientSec f E ≫ (envMatDecomp f A).hom ≫ L,
    D ≫ (envMatDecomp f A).inv ≫ envAmbientRet f E, ?_⟩
  simp only [assoc]
  rw [reassoc_of% hLD, Iso.hom_inv_id_assoc]
  exact envAmbientSec_ret f E

end RS
