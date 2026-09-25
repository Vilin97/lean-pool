/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndKill

/-!
# The Kronecker kill: diagonal products die with their multiplicity

In the group algebra of the product group `S_n × S_n`, the external
product of two recast Shape idempotents times the diagonal image of
a third is an idempotent whose coefficient at the identity is a
positive multiple of the Kronecker multiplicity `[λ : μ ⊗ ν]`.  An
idempotent of a finite group algebra over ℂ vanishes exactly when
its identity coefficient does, so the product is zero as soon as
the multiplicity is.  This mirrors the induction kill of
`RS.Classical.Deligne.IndKill`, with the block embedding replaced
by the two external embeddings and the diagonal.
-/

@[expose] public section

namespace RS

open Finset

private theorem ma_add_apply {G : Type*} (f g : MonoidAlgebra ℂ G)
    (x : G) : (f + g).coeff x = f.coeff x + g.coeff x := rfl

private theorem ma_smul_apply {G : Type*} (r : ℂ)
    (f : MonoidAlgebra ℂ G) (x : G) : (r • f).coeff x = r * f.coeff x := rfl

universe u

/-- The first-factor embedding of `S_n` into `S_n × S_n`. -/
noncomputable def extFstHom (n : ℕ) :
    Equiv.Perm (Fin n) →*
      Equiv.Perm (Fin n) × Equiv.Perm (Fin n) where
  toFun σ := (σ, 1)
  map_one' := rfl
  map_mul' σ σ' := by rw [Prod.mk_mul_mk, one_mul]

/-- The second-factor embedding of `S_n` into `S_n × S_n`. -/
noncomputable def extSndHom (n : ℕ) :
    Equiv.Perm (Fin n) →*
      Equiv.Perm (Fin n) × Equiv.Perm (Fin n) where
  toFun τ := (1, τ)
  map_one' := rfl
  map_mul' τ τ' := by rw [Prod.mk_mul_mk, one_mul]

/-- The diagonal embedding of `S_n` into `S_n × S_n`. -/
noncomputable def diagHom (n : ℕ) :
    Equiv.Perm (Fin n) →*
      Equiv.Perm (Fin n) × Equiv.Perm (Fin n) where
  toFun σ := (σ, σ)
  map_one' := rfl
  map_mul' σ σ' := by rw [Prod.mk_mul_mk]

/-- **The external product**: the product of the two one-sided
images of a pair of group-algebra elements in the group algebra of
`S_n × S_n`. -/
noncomputable def extProd {n : ℕ} (x y : SymGroupAlgebra n) :
    MonoidAlgebra ℂ (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x *
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y

/-- **The diagonal embedding of group algebras**: extension of the
diagonal along `mapDomain`, an algebra homomorphism. -/
noncomputable def diagEmbed {n : ℕ} :
    SymGroupAlgebra n →ₐ[ℂ]
      MonoidAlgebra ℂ (Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ (diagHom n)

/-- On basis permutations the external product is the single at the
pair. -/
theorem extProd_single {n : ℕ} (σ τ : Equiv.Perm (Fin n))
    (c d : ℂ) :
    extProd (MonoidAlgebra.single σ c) (MonoidAlgebra.single τ d) =
      MonoidAlgebra.single (σ, τ) (c * d) := by
  have hL : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n)
      (MonoidAlgebra.single σ c) =
      MonoidAlgebra.single
        ((σ, 1) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) c := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single σ c) = _
    exact MonoidAlgebra.mapDomain_single
  have hR : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n)
      (MonoidAlgebra.single τ d) =
      MonoidAlgebra.single
        ((1, τ) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) d := by
    change MonoidAlgebra.mapDomain _ (MonoidAlgebra.single τ d) = _
    exact MonoidAlgebra.mapDomain_single
  unfold extProd
  rw [hL, hR, MonoidAlgebra.single_mul_single]
  congr 1

/-- The two external images commute elementwise. -/
theorem extImages_comm {n : ℕ} (x y : SymGroupAlgebra n) :
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ =>
      have hL : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n)
          (MonoidAlgebra.single σ 1) =
          MonoidAlgebra.single
            ((σ, 1) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))
            (1 : ℂ) := by
        change MonoidAlgebra.mapDomain _
          (MonoidAlgebra.single σ 1) = _
        exact MonoidAlgebra.mapDomain_single
      have hR : MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n)
          (MonoidAlgebra.single τ 1) =
          MonoidAlgebra.single
            ((1, τ) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))
            (1 : ℂ) := by
        change MonoidAlgebra.mapDomain _
          (MonoidAlgebra.single τ 1) = _
        exact MonoidAlgebra.mapDomain_single
      simp only [MonoidAlgebra.of_apply]
      rw [hL, hR, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      congr 1
    | add y y' hy hy' =>
      rw [map_add, mul_add, add_mul, hy, hy']
    | smul r y hy =>
      rw [map_smul, mul_smul_comm, smul_mul_assoc, hy]
  | add x x' hx hx' =>
    rw [map_add, add_mul, mul_add, hx, hx']
  | smul r x hx =>
    rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

/-- The external product is multiplicative in the two slots
jointly. -/
theorem extProd_mul_extProd {n : ℕ}
    (x x' y y' : SymGroupAlgebra n) :
    extProd x y * extProd x' y' = extProd (x * x') (y * y') := by
  unfold extProd
  rw [map_mul, map_mul]
  calc MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x *
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y *
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x' *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y')
      = MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y *
          MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x') *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y' := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extFstHom n) x' *
          MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y) *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (extSndHom n) y' := by
        rw [extImages_comm]
    _ = _ := by
        rw [mul_assoc, mul_assoc, mul_assoc]

/-- The external product of Shape idempotents is idempotent. -/
theorem extProd_shape_e_idem (P : SchurPackage.{u}) {n : ℕ}
    (μ ν : Shape n) :
    extProd (Shape.e P μ) (Shape.e P ν) *
        extProd (Shape.e P μ) (Shape.e P ν) =
      extProd (Shape.e P μ) (Shape.e P ν) := by
  rw [extProd_mul_extProd, Shape.e_mul_self, Shape.e_mul_self]

/-- The external product is additive in the first argument. -/
theorem extProd_add_fst {n : ℕ} (x x' y : SymGroupAlgebra n) :
    extProd (x + x') y = extProd x y + extProd x' y := by
  unfold extProd
  rw [map_add, add_mul]

/-- The external product is homogeneous in the first argument. -/
theorem extProd_smul_fst {n : ℕ} (r : ℂ)
    (x y : SymGroupAlgebra n) :
    extProd (r • x) y = r • extProd x y := by
  unfold extProd
  rw [map_smul, smul_mul_assoc]

/-- The external product is additive in the second argument. -/
theorem extProd_add_snd {n : ℕ} (x y y' : SymGroupAlgebra n) :
    extProd x (y + y') = extProd x y + extProd x y' := by
  unfold extProd
  rw [map_add, mul_add]

/-- The external product is homogeneous in the second argument. -/
theorem extProd_smul_snd {n : ℕ} (r : ℂ)
    (x y : SymGroupAlgebra n) :
    extProd x (r • y) = r • extProd x y := by
  unfold extProd
  rw [map_smul, mul_smul_comm]

/-- The external product's coefficient at a pair is the product of
the coefficients. -/
theorem extProd_apply_pair {n : ℕ} (x y : SymGroupAlgebra n)
    (σ τ : Equiv.Perm (Fin n)) :
    (extProd x y).coeff (σ, τ) = x.coeff σ * y.coeff τ := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of σ₀ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ₀ =>
      simp only [MonoidAlgebra.of_apply]
      rw [extProd_single]
      by_cases hcase : σ₀ = σ ∧ τ₀ = τ
      · obtain ⟨rfl, rfl⟩ := hcase
        simp
      · have hne : ((σ₀, τ₀) :
            Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) ≠ (σ, τ) := by
          intro he
          exact hcase ⟨congrArg Prod.fst he, congrArg Prod.snd he⟩
        rcases not_and_or.mp hcase with hσ | hτ
        · simp [Finsupp.single_apply, hne, hσ]
        · simp [Finsupp.single_apply, hne, hτ]
    | add y y' hy hy' =>
      rw [extProd_add_snd, ma_add_apply, hy, hy', ma_add_apply,
        mul_add]
    | smul r y hy =>
      rw [extProd_smul_snd, ma_smul_apply, hy, ma_smul_apply]
      ring
  | add x x' hx hx' =>
    rw [extProd_add_fst, ma_add_apply, hx, hx', ma_add_apply,
      add_mul]
  | smul r x hx =>
    rw [extProd_smul_fst, ma_smul_apply, hx, ma_smul_apply]
    ring

/-- The external product of Shape idempotents has conjugation
invariant coefficients. -/
theorem extProd_shape_e_coeff_conj (P : SchurPackage.{u}) {n : ℕ}
    (μ ν : Shape n)
    (g k : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) :
    (extProd (Shape.e P μ) (Shape.e P ν)).coeff (g⁻¹ * k * g) =
      (extProd (Shape.e P μ) (Shape.e P ν)).coeff k := by
  change (extProd (Shape.e P μ) (Shape.e P ν)).coeff
      (g.1⁻¹ * k.1 * g.1, g.2⁻¹ * k.2 * g.2) =
    (extProd (Shape.e P μ) (Shape.e P ν)).coeff (k.1, k.2)
  rw [extProd_apply_pair, extProd_apply_pair, shape_e_coeff_conj,
    shape_e_coeff_conj]

/-- The external products of Shape idempotents are central. -/
theorem extProd_shape_e_central (P : SchurPackage.{u}) {n : ℕ}
    (μ ν : Shape n)
    (z : MonoidAlgebra ℂ
      (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))) :
    extProd (Shape.e P μ) (Shape.e P ν) * z =
      z * extProd (Shape.e P μ) (Shape.e P ν) := by
  classical
  -- Reduce to singles by linearity.
  suffices hsingle : ∀
      (g : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)) (c : ℂ),
      extProd (Shape.e P μ) (Shape.e P ν) *
          MonoidAlgebra.single g c =
        MonoidAlgebra.single g c *
          extProd (Shape.e P μ) (Shape.e P ν) by
    induction z using MonoidAlgebra.induction_on with
    | of g => exact hsingle g 1
    | add y z hy hz => rw [mul_add, add_mul, hy, hz]
    | smul r y hy => rw [mul_smul_comm, smul_mul_assoc, hy]
  intro g c
  ext k
  rw [MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply]
  have hconj := extProd_shape_e_coeff_conj P μ ν g (k * g⁻¹)
  have harg : g⁻¹ * (k * g⁻¹) * g = g⁻¹ * k := by
    group
  rw [harg] at hconj
  rw [← hconj]
  ring

/-- The diagonal embedding is injective on group elements. -/
theorem diagHom_injective (n : ℕ) :
    Function.Injective (diagHom n) := fun _ _ h =>
  congrArg Prod.fst h

/-- The diagonal image's coefficient on the diagonal. -/
theorem diagEmbed_apply_diag {n : ℕ} (x : SymGroupAlgebra n)
    (σ : Equiv.Perm (Fin n)) : (diagEmbed x).coeff (σ, σ) = x.coeff σ := by
  change Finsupp.mapDomain (diagHom n) x.coeff (σ, σ) = x.coeff σ
  exact Finsupp.mapDomain_apply_of_injective (diagHom_injective n) x.coeff σ

/-- The diagonal image vanishes off the diagonal. -/
theorem diagEmbed_apply_off_diag {n : ℕ} (x : SymGroupAlgebra n)
    {p : Equiv.Perm (Fin n) × Equiv.Perm (Fin n)}
    (h : p.1 ≠ p.2) : (diagEmbed x).coeff p = 0 := by
  change Finsupp.mapDomain (diagHom n) x.coeff p = 0
  refine Finsupp.mapDomain_of_notMem_range x.coeff p ?_
  rintro ⟨σ, hσ⟩
  rw [← hσ] at h
  exact h rfl

/-- The identity coefficient of the diagonal product is a positive
multiple of the Kronecker multiplicity. -/
theorem extProd_mul_diagEmbed_apply_one (P : SchurPackage.{u})
    {n : ℕ} (lam μ ν : Shape n) :
    (extProd (Shape.e P μ) (Shape.e P ν) *
        diagEmbed (Shape.e P lam)).coeff (1, 1) =
      (P.dim μ.val : ℂ) * (P.dim ν.val : ℂ) *
        (P.dim lam.val : ℂ) /
        ((n.factorial : ℂ) * (n.factorial : ℂ)) *
        kronMult lam μ ν := by
  classical
  change (extProd (Shape.e P μ) (Shape.e P ν) *
      diagEmbed (Shape.e P lam)).coeff 1 = _
  rw [mul_apply_one]
  have hoff : ∀ p ∈ (Finset.univ :
        Finset (Equiv.Perm (Fin n) × Equiv.Perm (Fin n))),
      p ∉ (Finset.univ : Finset (Equiv.Perm (Fin n))).image
        (fun σ =>
          ((σ, σ) : Equiv.Perm (Fin n) × Equiv.Perm (Fin n))) →
      (extProd (Shape.e P μ) (Shape.e P ν)).coeff p *
        (diagEmbed (Shape.e P lam)).coeff p⁻¹ = 0 := by
    intro p _ hp
    have hne : p.1 ≠ p.2 := by
      intro he
      exact hp (Finset.mem_image.mpr
        ⟨p.1, Finset.mem_univ _, Prod.ext rfl he⟩)
    have hne' : (p⁻¹).1 ≠ (p⁻¹).2 := by
      rw [Prod.fst_inv, Prod.snd_inv]
      exact fun he => hne (inv_injective he)
    rw [diagEmbed_apply_off_diag _ hne', mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hoff]
  rw [Finset.sum_image (fun _ _ _ _ h => congrArg Prod.fst h)]
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      (extProd (Shape.e P μ) (Shape.e P ν)).coeff (σ, σ) *
        (diagEmbed (Shape.e P lam)).coeff ((σ, σ)⁻¹) =
      ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim ν.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim lam.val : ℂ) / (n.factorial : ℂ)) *
        (jtChar lam.val (permCast lam.prop.symm σ) *
          jtChar μ.val (permCast μ.prop.symm σ) *
          jtChar ν.val (permCast ν.prop.symm σ)) := by
    intro σ
    have h2 : (diagEmbed (Shape.e P lam)).coeff ((σ, σ)⁻¹) =
        (Shape.e P lam).coeff σ⁻¹ :=
      diagEmbed_apply_diag (Shape.e P lam) σ⁻¹
    have hc := shape_e_coeff P lam σ⁻¹
    rw [permCast_inv, jtChar_inv] at hc
    rw [extProd_apply_pair, h2,
      show (Shape.e P lam).coeff σ⁻¹ =
        ((P.dim lam.val : ℂ) / (n.factorial : ℂ)) *
          jtChar lam.val (permCast lam.prop.symm σ) from hc,
      show (Shape.e P μ).coeff σ =
        ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) *
          jtChar μ.val (permCast μ.prop.symm σ) from
        shape_e_coeff P μ σ,
      show (Shape.e P ν).coeff σ =
        ((P.dim ν.val : ℂ) / (n.factorial : ℂ)) *
          jtChar ν.val (permCast ν.prop.symm σ) from
        shape_e_coeff P ν σ]
    ring
  rw [Finset.sum_congr rfl fun σ _ => hterm σ]
  rw [show (∑ σ : Equiv.Perm (Fin n),
      ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim ν.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim lam.val : ℂ) / (n.factorial : ℂ)) *
        (jtChar lam.val (permCast lam.prop.symm σ) *
          jtChar μ.val (permCast μ.prop.symm σ) *
          jtChar ν.val (permCast ν.prop.symm σ))) =
      ((P.dim μ.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim ν.val : ℂ) / (n.factorial : ℂ)) *
        ((P.dim lam.val : ℂ) / (n.factorial : ℂ)) *
        ∑ σ : Equiv.Perm (Fin n),
          jtChar lam.val (permCast lam.prop.symm σ) *
            jtChar μ.val (permCast μ.prop.symm σ) *
            jtChar ν.val (permCast ν.prop.symm σ) from by
    simp only [Finset.mul_sum]]
  rw [kronMult]
  have hn : ((n.factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr n.factorial_ne_zero
  field_simp

/-- **The Kronecker kill**: a vanishing Kronecker multiplicity
kills the diagonal product in the product group algebra. -/
theorem extProd_mul_diagEmbed_eq_zero (P : SchurPackage.{u})
    {n : ℕ} (lam μ ν : Shape n) (h : kronMult lam μ ν = 0) :
    extProd (Shape.e P μ) (Shape.e P ν) *
        diagEmbed (Shape.e P lam) = 0 := by
  classical
  apply eq_zero_of_idem_of_coeff_one
  · set A := extProd (Shape.e P μ) (Shape.e P ν) with hA
    set B := diagEmbed (Shape.e P lam) with hB
    have hc : B * A = A * B :=
      (extProd_shape_e_central P μ ν B).symm
    have hd : B * B = B := by
      rw [hB, ← map_mul, Shape.e_mul_self]
    have ha : A * A = A := extProd_shape_e_idem P μ ν
    calc A * B * (A * B)
        = A * (B * (A * B)) := mul_assoc _ _ _
      _ = A * (B * A * B) :=
          congrArg (fun z => A * z) (mul_assoc _ _ _).symm
      _ = A * (A * B * B) :=
          congrArg (fun z => A * (z * B)) hc
      _ = A * (A * (B * B)) :=
          congrArg (fun z => A * z) (mul_assoc _ _ _)
      _ = A * (A * B) :=
          congrArg (fun z => A * (A * z)) hd
      _ = A * A * B := (mul_assoc _ _ _).symm
      _ = A * B := congrArg (fun z => z * B) ha
  · have h4 := extProd_mul_diagEmbed_apply_one P lam μ ν
    rw [h, mul_zero] at h4
    exact h4

end RS
