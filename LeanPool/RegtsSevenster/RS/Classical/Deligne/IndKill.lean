/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.IndSplit
import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.RegularTrace

/-!
# The induction kill: block products die with their multiplicity

The product of the central idempotent of `λ` with the embedded
block idempotent of `(μ, ν)` is an idempotent of the group algebra
whose coefficient at the identity is a positive multiple of the
induction multiplicity `[λ : μ, ν]`.  An idempotent of a group
algebra over ℂ vanishes exactly when its identity coefficient
does — the trace of its left-regular action — so the product is
zero as soon as the multiplicity is.  This is the bridge from the
character combinatorics to the categorical direct-sum transfer of
Schur vanishing.
-/

namespace RS

open Finset

private theorem ma_add_apply {G : Type*} (f g : MonoidAlgebra ℂ G)
    (x : G) : (f + g).coeff x = f.coeff x + g.coeff x := rfl

private theorem ma_smul_apply {G : Type*} (r : ℂ)
    (f : MonoidAlgebra ℂ G) (x : G) : (r • f).coeff x = r * f.coeff x := rfl

/-- The trace of left multiplication on a group algebra is the
group order times the identity coefficient. -/
theorem trace_mulLeft_monoidAlgebra {G : Type*} [Group G]
    [Fintype G] (x : MonoidAlgebra ℂ G) :
    LinearMap.trace ℂ (MonoidAlgebra ℂ G)
      (LinearMap.mulLeft ℂ x) =
      (Fintype.card G : ℂ) * x.coeff 1 := by
  classical
  exact
    trace_mulLeft x

/-- An idempotent of a finite group algebra over ℂ with vanishing
identity coefficient is zero. -/
theorem eq_zero_of_idem_of_coeff_one {G : Type*} [Group G]
    [Finite G] {x : MonoidAlgebra ℂ G}
    (hidem : x * x = x) (h1 : x.coeff 1 = 0) : x = 0 := by
  classical
  let := Fintype.ofFinite G
  set L := LinearMap.mulLeft ℂ x with hLdef
  have hLL : L ∘ₗ L = L := by
    rw [hLdef, ← LinearMap.mulLeft_mul, hidem]
  have hproj : LinearMap.IsProj (LinearMap.range L) L := by
    refine ⟨fun y => LinearMap.mem_range_self L y, ?_⟩
    rintro y ⟨z, rfl⟩
    exact congrArg (fun f => f z) hLL
  have htr := hproj.trace
  rw [show LinearMap.trace ℂ (MonoidAlgebra ℂ G) L =
    (Fintype.card G : ℂ) * x.coeff 1 from
      trace_mulLeft_monoidAlgebra x, h1, mul_zero] at htr
  have hrank : Module.finrank ℂ (LinearMap.range L) = 0 := by
    exact_mod_cast htr.symm
  have hbot : LinearMap.range L = ⊥ :=
    Submodule.finrank_eq_zero.mp hrank
  have hL0 : L = 0 := LinearMap.range_eq_bot.mp hbot
  have hx := congrArg (fun f : _ →ₗ[ℂ] _ =>
    f (1 : MonoidAlgebra ℂ G)) hL0
  simpa [hLdef, LinearMap.mulLeft_apply] using hx

universe u

/-- The Shape idempotent's coefficients are conjugation
invariant. -/
theorem shape_e_coeff_conj (P : SchurPackage.{u}) {n : ℕ}
    (lam : Shape n) (g k : Equiv.Perm (Fin n)) :
    (Shape.e P lam).coeff (g⁻¹ * k * g) = (Shape.e P lam).coeff k := by
  have h1 := shape_e_coeff P lam (g⁻¹ * k * g)
  have h2 := shape_e_coeff P lam k
  have hcast : permCast lam.prop.symm (g⁻¹ * k * g) =
      (permCast lam.prop.symm g)⁻¹ *
        permCast lam.prop.symm k * permCast lam.prop.symm g := by
    rw [permCast_mul, permCast_mul, permCast_inv]
  have hchar : jtChar lam.val (permCast lam.prop.symm
      (g⁻¹ * k * g)) =
      jtChar lam.val (permCast lam.prop.symm k) := by
    rw [hcast]
    have := jtChar_conj lam.val
      ((permCast lam.prop.symm g)⁻¹ : _)
      (permCast lam.prop.symm k)
    simpa [inv_inv] using this
  change (Shape.e P lam).coeff (g⁻¹ * k * g) =
    (Shape.e P lam).coeff k
  rw [h1, h2, hchar]

/-- The Shape idempotents are central. -/
theorem shape_e_central (P : SchurPackage.{u}) {n : ℕ}
    (lam : Shape n) (y : SymGroupAlgebra n) :
    Shape.e P lam * y = y * Shape.e P lam := by
  classical
  -- Reduce to singles by linearity.
  suffices hsingle : ∀ (g : Equiv.Perm (Fin n)) (c : ℂ),
      Shape.e P lam * MonoidAlgebra.single g c =
        MonoidAlgebra.single g c * Shape.e P lam by
    induction y using MonoidAlgebra.induction_on with
    | of g => exact hsingle g 1
    | add y z hy hz => rw [mul_add, add_mul, hy, hz]
    | smul r y hy => rw [mul_smul_comm, smul_mul_assoc, hy]
  intro g c
  ext k
  rw [MonoidAlgebra.coeff_mul_single_apply,
    MonoidAlgebra.coeff_single_mul_apply]
  have hconj := shape_e_coeff_conj P lam g (k * g⁻¹)
  have harg : g⁻¹ * (k * g⁻¹) * g = g⁻¹ * k := by
    group
  rw [harg] at hconj
  rw [← hconj]
  ring

/-- The two block images commute elementwise. -/
theorem blockImages_comm {a b : ℕ} (x : SymGroupAlgebra a)
    (y : SymGroupAlgebra b) :
    MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y =
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b)
          x := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of σ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ =>
      have hL : MonoidAlgebra.mapDomainAlgHom ℂ ℂ
          (blockEmbedFstHom a b) (MonoidAlgebra.single σ 1) =
          MonoidAlgebra.single (blockEmbed σ 1) (1 : ℂ) := by
        change MonoidAlgebra.mapDomain _
          (MonoidAlgebra.single σ 1) = _
        exact MonoidAlgebra.mapDomain_single
      have hR : MonoidAlgebra.mapDomainAlgHom ℂ ℂ
          (blockEmbedSndHom a b) (MonoidAlgebra.single τ 1) =
          MonoidAlgebra.single (blockEmbed 1 τ) (1 : ℂ) := by
        change MonoidAlgebra.mapDomain _
          (MonoidAlgebra.single τ 1) = _
        exact MonoidAlgebra.mapDomain_single
      simp only [MonoidAlgebra.of_apply]
      rw [hL, hR, MonoidAlgebra.single_mul_single,
        MonoidAlgebra.single_mul_single]
      congr 1
      rw [← blockEmbed_mul, ← blockEmbed_mul]
      simp
    | add y y' hy hy' =>
      rw [map_add, mul_add, add_mul, hy, hy']
    | smul r y hy =>
      rw [map_smul, mul_smul_comm, smul_mul_assoc, hy]
  | add x x' hx hx' =>
    rw [map_add, add_mul, mul_add, hx, hx']
  | smul r x hx =>
    rw [map_smul, smul_mul_assoc, mul_smul_comm, hx]

/-- The block embedding is multiplicative in the two slots
jointly. -/
theorem blockAlgEmbed_mul_blockAlgEmbed {a b : ℕ}
    (x x' : SymGroupAlgebra a) (y y' : SymGroupAlgebra b) :
    blockAlgEmbed x y * blockAlgEmbed x' y' =
      blockAlgEmbed (x * x') (y * y') := by
  unfold blockAlgEmbed
  rw [map_mul, map_mul]
  calc MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x *
      MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y *
      (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x' *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y')
      = MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b) y *
          MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b)
            x') *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b)
          y' := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b) x *
        (MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedFstHom a b)
            x' *
          MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b)
            y) *
        MonoidAlgebra.mapDomainAlgHom ℂ ℂ (blockEmbedSndHom a b)
          y' := by
        rw [blockImages_comm]
    _ = _ := by
        rw [mul_assoc, mul_assoc, mul_assoc]

/-- The embedded block idempotent is idempotent. -/
theorem blockAlgEmbed_shape_e_idem (P : SchurPackage.{u})
    {a b : ℕ} (μ : Shape a) (ν : Shape b) :
    blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
        blockAlgEmbed (Shape.e P μ) (Shape.e P ν) =
      blockAlgEmbed (Shape.e P μ) (Shape.e P ν) := by
  rw [blockAlgEmbed_mul_blockAlgEmbed, Shape.e_mul_self,
    Shape.e_mul_self]

/-- Joint injectivity of the block embedding. -/
theorem blockEmbed_inj {a b : ℕ} {σ σ' : Equiv.Perm (Fin a)}
    {τ τ' : Equiv.Perm (Fin b)}
    (h : blockEmbed σ τ = blockEmbed σ' τ') : σ = σ' ∧ τ = τ' := by
  constructor
  · ext i
    have h1 := DFunLike.congr_fun h (Fin.castAdd b i)
    rw [blockEmbed_castAdd, blockEmbed_castAdd] at h1
    have := congrArg Fin.val h1
    simp only [Fin.val_castAdd] at this
    omega
  · ext j
    have h1 := DFunLike.congr_fun h (Fin.natAdd a j)
    rw [blockEmbed_natAdd, blockEmbed_natAdd] at h1
    have := congrArg Fin.val h1
    simp only [Fin.val_natAdd] at this
    omega

/-- The block image's coefficient on the block. -/
theorem blockAlgEmbed_apply_blockEmbed {a b : ℕ}
    (x : SymGroupAlgebra a) (y : SymGroupAlgebra b)
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    (blockAlgEmbed x y).coeff (blockEmbed σ τ) = x.coeff σ * y.coeff τ := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of σ₀ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ₀ =>
      simp only [MonoidAlgebra.of_apply]
      rw [blockAlgEmbed_single]
      by_cases hcase : σ₀ = σ ∧ τ₀ = τ
      · obtain ⟨rfl, rfl⟩ := hcase
        simp
      · have hne : blockEmbed σ₀ τ₀ ≠ blockEmbed σ τ := by
          intro he
          exact hcase (blockEmbed_inj he)
        rcases not_and_or.mp hcase with hσ | hτ
        · simp [Finsupp.single_apply, hne, hσ]
        · simp [Finsupp.single_apply, hne, hτ]
    | add y y' hy hy' =>
      rw [blockAlgEmbed_add_snd, ma_add_apply, hy, hy',
        ma_add_apply, mul_add]
    | smul r y hy =>
      rw [blockAlgEmbed_smul_snd, ma_smul_apply, hy,
        ma_smul_apply]
      ring
  | add x x' hx hx' =>
    rw [blockAlgEmbed_add_fst, ma_add_apply, hx, hx',
      ma_add_apply, add_mul]
  | smul r x hx =>
    rw [blockAlgEmbed_smul_fst, ma_smul_apply, hx,
      ma_smul_apply]
    ring

/-- The block image vanishes off the block. -/
theorem blockAlgEmbed_apply_eq_zero {a b : ℕ}
    (x : SymGroupAlgebra a) (y : SymGroupAlgebra b)
    {g : Equiv.Perm (Fin (a + b))}
    (h : ∀ (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)),
      g ≠ blockEmbed σ τ) :
    (blockAlgEmbed x y).coeff g = 0 := by
  classical
  induction x using MonoidAlgebra.induction_on with
  | of σ₀ =>
    induction y using MonoidAlgebra.induction_on with
    | of τ₀ =>
      simp only [MonoidAlgebra.of_apply]
      rw [blockAlgEmbed_single]
      have hne : blockEmbed σ₀ τ₀ ≠ g := fun he => h σ₀ τ₀ he.symm
      simp [hne]
    | add y y' hy hy' =>
      rw [blockAlgEmbed_add_snd, ma_add_apply, hy, hy', add_zero]
    | smul r y hy =>
      rw [blockAlgEmbed_smul_snd, ma_smul_apply, hy, mul_zero]
  | add x x' hx hx' =>
    rw [blockAlgEmbed_add_fst, ma_add_apply, hx, hx', add_zero]
  | smul r x hx =>
    rw [blockAlgEmbed_smul_fst, ma_smul_apply, hx, mul_zero]

/-- Convolution at the identity. -/
theorem mul_apply_one {G : Type*} [Group G] [Fintype G]
    (x y : MonoidAlgebra ℂ G) :
    (x * y).coeff 1 = ∑ g : G, x.coeff g * y.coeff g⁻¹ := by
  classical
  rw [MonoidAlgebra.coeff_mul_apply_left]
  simp only [mul_one, Finsupp.sum]
  exact Finset.sum_subset (Finset.subset_univ _) fun g _ hg => by
    rw [Finsupp.notMem_support_iff.mp hg, zero_mul]

/-- The identity coefficient of the block product is a positive
multiple of the induction multiplicity. -/
theorem shape_e_mul_block_apply_one (P : SchurPackage.{u})
    {a b : ℕ} (lam : Shape (a + b)) (μ : Shape a) (ν : Shape b) :
    (Shape.e P lam *
        blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff 1 =
      (P.dim lam.val : ℂ) * (P.dim μ.val : ℂ) *
        (P.dim ν.val : ℂ) / (((a + b).factorial : ℂ)) *
        indMult lam μ ν := by
  classical
  rw [mul_apply_one]
  have hswap : (∑ g : Equiv.Perm (Fin (a + b)),
      (Shape.e P lam).coeff g *
        (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff g⁻¹) =
      ∑ g : Equiv.Perm (Fin (a + b)),
        (Shape.e P lam).coeff g⁻¹ *
          (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff g :=
    Fintype.sum_equiv (Equiv.inv _) _ _ fun g => by
      change (Shape.e P lam).coeff g *
          (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff g⁻¹ =
        (Shape.e P lam).coeff g⁻¹⁻¹ *
          (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff g⁻¹
      rw [inv_inv]
  rw [hswap]
  have hoff : ∀ g ∈ (Finset.univ :
        Finset (Equiv.Perm (Fin (a + b)))),
      g ∉ (Finset.univ ×ˢ Finset.univ).image
        (fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) =>
          blockEmbed p.1 p.2) →
      (Shape.e P lam).coeff g⁻¹ *
        (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff g = 0 := by
    intro g _ hg
    rw [blockAlgEmbed_apply_eq_zero _ _ fun σ τ he =>
      hg (Finset.mem_image.mpr ⟨(σ, τ),
        Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Finset.mem_univ _⟩, he.symm⟩),
      mul_zero]
  rw [← Finset.sum_subset (Finset.subset_univ _) hoff]
  rw [Finset.sum_image (by
    intro p _ q _ hpq
    obtain ⟨h1, h2⟩ := blockEmbed_inj hpq
    exact Prod.ext h1 h2)]
  rw [Finset.sum_product]
  have hterm : ∀ (σ : Equiv.Perm (Fin a))
      (τ : Equiv.Perm (Fin b)),
      (Shape.e P lam).coeff (blockEmbed σ τ)⁻¹ *
        (blockAlgEmbed (Shape.e P μ) (Shape.e P ν)).coeff
          (blockEmbed σ τ) =
      ((P.dim lam.val : ℂ) / (((a + b).factorial : ℂ))) *
        ((P.dim μ.val : ℂ) / ((a.factorial : ℂ))) *
        ((P.dim ν.val : ℂ) / ((b.factorial : ℂ))) *
        (jtChar lam.val
          (permCast lam.prop.symm (blockEmbed σ τ)) *
          jtChar μ.val (permCast μ.prop.symm σ) *
          jtChar ν.val (permCast ν.prop.symm τ)) := by
    intro σ τ
    rw [blockAlgEmbed_apply_blockEmbed]
    have h1 : (Shape.e P lam).coeff ((blockEmbed σ τ)⁻¹) =
        ((P.dim lam.val : ℂ) / (((a + b).factorial : ℂ))) *
          jtChar lam.val
            (permCast lam.prop.symm (blockEmbed σ τ)) := by
      have hc := shape_e_coeff P lam ((blockEmbed σ τ)⁻¹)
      rw [permCast_inv, jtChar_inv] at hc
      exact hc
    have h2 := shape_e_coeff P μ σ
    have h3 := shape_e_coeff P ν τ
    rw [h1, show (Shape.e P μ).coeff σ =
        ((P.dim μ.val : ℂ) / ((a.factorial : ℂ))) *
          jtChar μ.val (permCast μ.prop.symm σ) from h2,
      show (Shape.e P ν).coeff τ =
        ((P.dim ν.val : ℂ) / ((b.factorial : ℂ))) *
          jtChar ν.val (permCast ν.prop.symm τ) from h3]
    ring
  rw [Finset.sum_congr rfl fun σ _ =>
    Finset.sum_congr rfl fun τ _ => hterm σ τ]
  rw [show (∑ σ : Equiv.Perm (Fin a), ∑ τ : Equiv.Perm (Fin b),
      ((P.dim lam.val : ℂ) / (((a + b).factorial : ℂ))) *
        ((P.dim μ.val : ℂ) / ((a.factorial : ℂ))) *
        ((P.dim ν.val : ℂ) / ((b.factorial : ℂ))) *
        (jtChar lam.val
          (permCast lam.prop.symm (blockEmbed σ τ)) *
          jtChar μ.val (permCast μ.prop.symm σ) *
          jtChar ν.val (permCast ν.prop.symm τ))) =
      ((P.dim lam.val : ℂ) / (((a + b).factorial : ℂ))) *
        ((P.dim μ.val : ℂ) / ((a.factorial : ℂ))) *
        ((P.dim ν.val : ℂ) / ((b.factorial : ℂ))) *
        ∑ σ : Equiv.Perm (Fin a), ∑ τ : Equiv.Perm (Fin b),
          jtChar lam.val
            (permCast lam.prop.symm (blockEmbed σ τ)) *
            jtChar μ.val (permCast μ.prop.symm σ) *
            jtChar ν.val (permCast ν.prop.symm τ) from by
    simp only [Finset.mul_sum]]
  rw [indMult]
  have ha : ((a.factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr a.factorial_ne_zero
  have hb : ((b.factorial : ℂ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr b.factorial_ne_zero
  field_simp

/-- **The induction kill**: a vanishing induction multiplicity
kills the block product in the group algebra. -/
theorem shape_e_mul_blockAlgEmbed_eq_zero (P : SchurPackage.{u})
    {a b : ℕ} (lam : Shape (a + b)) (μ : Shape a) (ν : Shape b)
    (h : indMult lam μ ν = 0) :
    Shape.e P lam * blockAlgEmbed (Shape.e P μ) (Shape.e P ν) =
      0 := by
  classical
  apply eq_zero_of_idem_of_coeff_one
  · have hc : blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
        Shape.e P lam =
        Shape.e P lam *
          blockAlgEmbed (Shape.e P μ) (Shape.e P ν) :=
      (shape_e_central P lam _).symm
    calc Shape.e P lam *
        blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
        (Shape.e P lam *
          blockAlgEmbed (Shape.e P μ) (Shape.e P ν))
        = Shape.e P lam *
          (blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
            (Shape.e P lam *
              blockAlgEmbed (Shape.e P μ) (Shape.e P ν))) :=
          mul_assoc _ _ _
      _ = Shape.e P lam *
          (blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
              Shape.e P lam *
            blockAlgEmbed (Shape.e P μ) (Shape.e P ν)) :=
          congrArg (fun z => Shape.e P lam * z)
            (mul_assoc _ _ _).symm
      _ = Shape.e P lam *
          (Shape.e P lam *
              blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
            blockAlgEmbed (Shape.e P μ) (Shape.e P ν)) :=
          congrArg (fun z => Shape.e P lam *
            (z * blockAlgEmbed (Shape.e P μ) (Shape.e P ν))) hc
      _ = Shape.e P lam *
          (Shape.e P lam *
            (blockAlgEmbed (Shape.e P μ) (Shape.e P ν) *
              blockAlgEmbed (Shape.e P μ) (Shape.e P ν))) :=
          congrArg (fun z => Shape.e P lam * z) (mul_assoc _ _ _)
      _ = Shape.e P lam *
          (Shape.e P lam *
            blockAlgEmbed (Shape.e P μ) (Shape.e P ν)) :=
          congrArg (fun z => Shape.e P lam * (Shape.e P lam * z))
            (blockAlgEmbed_shape_e_idem P μ ν)
      _ = Shape.e P lam * Shape.e P lam *
          blockAlgEmbed (Shape.e P μ) (Shape.e P ν) :=
          (mul_assoc _ _ _).symm
      _ = Shape.e P lam *
          blockAlgEmbed (Shape.e P μ) (Shape.e P ν) :=
          congrArg (fun z => z *
            blockAlgEmbed (Shape.e P μ) (Shape.e P ν))
            (Shape.e_mul_self P lam)
  · rw [shape_e_mul_block_apply_one, h, mul_zero]

end RS
