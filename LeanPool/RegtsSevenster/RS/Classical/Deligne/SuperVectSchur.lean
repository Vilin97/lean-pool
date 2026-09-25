/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PieriPos
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SchurVanishing
public import LeanPool.RegtsSevenster.RS.Classical.Super.TotalSpace

/-!
# Schur nonvanishing on the standard super vector space

The nonvanishing half of Deligne 1.9 in `SuperVect`: on the standard
super object of dimension `(p, q)` the central idempotent of every
diagram avoiding the cell `(p, q)` acts nonzero on the tensor power.

The route is a trace computation.  The *super trace functional*
`sTr` — the plain trace of the even and odd components — is linear,
cyclic, and multiplicative for the graded tensor product, so
`σ ↦ sTr (permMor X n σ)` is a class function multiplicative over
block embeddings.  A partial-trace identity for the Koszul braiding
(`sTr_swap_conj`) evaluates it on the standard cycles, giving the
character formula `sTr (permMor X n σ) = cycleFun (superPS p q) σ`.
Evaluating `sTr ∘ permAlg` on a package idempotent through the
Frobenius formula then yields `dim λ · s_λ(superPS p q)`, positive by
hook positivity — so the idempotent's action cannot vanish.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open scoped TensorProduct

noncomputable section

/-! ## The standard super vector space -/

/-- **The standard super vector space of dimension `(p, q)`**:
`ℂ^p` in even degree and `ℂ^q` in odd degree. -/
def stdSuper (p q : ℕ) : SuperVect where
  even := Fin p → ℂ
  odd := Fin q → ℂ

/-- The even component of the standard super object. -/
@[simp]
theorem stdSuper_even (p q : ℕ) : (stdSuper p q).even = (Fin p → ℂ) :=
  rfl

/-- The odd component of the standard super object. -/
@[simp]
theorem stdSuper_odd (p q : ℕ) : (stdSuper p q).odd = (Fin q → ℂ) :=
  rfl

/-! ## The super trace functional

The plain trace of a grading-preserving endomorphism: the sum of the
traces of its two components.  (This is the trace of the underlying
linear endomorphism, not the supertrace; the Koszul signs of the
braiding enter through the action itself.) -/

/-- The trace of an endomorphism in `SuperVect`: the sum of the
traces of its even and odd components. -/
def sTr {V : SuperVect} (f : V ⟶ V) : ℂ :=
  LinearMap.trace ℂ V.even (SuperVect.Hom.evenMap f) +
    LinearMap.trace ℂ V.odd (SuperVect.Hom.oddMap f)

/-- The super trace as a linear functional on endomorphisms. -/
def sTrL (V : SuperVect) : (V ⟶ V) →ₗ[ℂ] ℂ where
  toFun := sTr
  map_add' f g := by
    simp [sTr, SuperVect.add_evenMap, SuperVect.add_oddMap]
    ring
  map_smul' c f := by
    simp [sTr, SuperVect.smul_evenMap, SuperVect.smul_oddMap]
    ring

/-- `sTrL` evaluates to `sTr`. -/
@[simp]
theorem sTrL_apply (V : SuperVect) (f : V ⟶ V) : sTrL V f = sTr f :=
  rfl

/-- The super trace of the identity is the total dimension. -/
theorem sTr_id (V : SuperVect) :
    sTr (𝟙 V) = (Module.finrank ℂ V.even : ℂ) +
      (Module.finrank ℂ V.odd : ℂ) := by
  simp [sTr, SuperVect.cat_id_evenMap, SuperVect.cat_id_oddMap,
    LinearMap.trace_id]

/-- **Cyclicity of the super trace.** -/
theorem sTr_comp_comm {V W : SuperVect} (f : V ⟶ W) (g : W ⟶ V) :
    sTr (f ≫ g) = sTr (g ≫ f) := by
  simp only [sTr, SuperVect.cat_comp_evenMap, SuperVect.cat_comp_oddMap]
  rw [LinearMap.trace_comp_comm', LinearMap.trace_comp_comm'
    (SuperVect.Hom.oddMap f) (SuperVect.Hom.oddMap g)]

/-- The super trace is invariant under conjugation by an
isomorphism. -/
theorem sTr_conj {V W : SuperVect} (e : V ≅ W) (f : V ⟶ V) :
    sTr (e.inv ≫ f ≫ e.hom) = sTr f := by
  rw [sTr_comp_comm, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **Multiplicativity of the super trace** for the graded tensor
product of endomorphisms. -/
theorem sTr_tensorHom {V W : SuperVect} (f : V ⟶ V) (g : W ⟶ W) :
    sTr (f ⊗ₘ g) = sTr f * sTr g := by
  change sTr (SuperVect.tensorHom f g) = sTr f * sTr g
  rw [sTr, SuperVect.tensorHom_evenMap, SuperVect.tensorHom_oddMap]
  rw [show LinearMap.trace ℂ (SuperVect.tensorObj V W).even
        (LinearMap.prodMap (TensorProduct.map f.evenMap g.evenMap)
          (TensorProduct.map f.oddMap g.oddMap)) =
      LinearMap.trace ℂ V.even f.evenMap *
          LinearMap.trace ℂ W.even g.evenMap +
        LinearMap.trace ℂ V.odd f.oddMap *
          LinearMap.trace ℂ W.odd g.oddMap from by
    change LinearMap.trace ℂ
      ((V.even ⊗[ℂ] W.even) × (V.odd ⊗[ℂ] W.odd)) _ = _
    rw [LinearMap.trace_prodMap', LinearMap.trace_tensorProduct',
      LinearMap.trace_tensorProduct']]
  rw [show LinearMap.trace ℂ (SuperVect.tensorObj V W).odd
        (LinearMap.prodMap (TensorProduct.map f.evenMap g.oddMap)
          (TensorProduct.map f.oddMap g.evenMap)) =
      LinearMap.trace ℂ V.even f.evenMap *
          LinearMap.trace ℂ W.odd g.oddMap +
        LinearMap.trace ℂ V.odd f.oddMap *
          LinearMap.trace ℂ W.even g.evenMap from by
    change LinearMap.trace ℂ
      ((V.even ⊗[ℂ] W.odd) × (V.odd ⊗[ℂ] W.even)) _ = _
    rw [LinearMap.trace_prodMap', LinearMap.trace_tensorProduct',
      LinearMap.trace_tensorProduct']]
  rw [sTr, sTr]
  ring

/-! ## The parity involution -/

/-- The parity involution of a super vector space: the identity on
the even component and minus the identity on the odd component. -/
def parHom (V : SuperVect) : V ⟶ V where
  evenMap := LinearMap.id
  oddMap := -LinearMap.id

/-- The even component of the parity involution. -/
@[simp]
theorem parHom_evenMap (V : SuperVect) :
    (parHom V).evenMap = LinearMap.id := rfl

/-- The odd component of the parity involution. -/
@[simp]
theorem parHom_oddMap (V : SuperVect) :
    (parHom V).oddMap = -LinearMap.id := rfl

/-- The parity involution commutes with every morphism. -/
theorem parHom_comm {V W : SuperVect} (f : V ⟶ W) :
    f ≫ parHom W = parHom V ≫ f := by
  apply SuperVect.hom_ext
  · simp [SuperVect.cat_comp_evenMap]
  · simp [SuperVect.cat_comp_oddMap, LinearMap.comp_neg,
      LinearMap.neg_comp]

/-- The iterated parity involution. -/
def parPow (V : SuperVect) : ℕ → (V ⟶ V)
  | 0 => 𝟙 V
  | n + 1 => parPow V n ≫ parHom V

/-- The even component of the iterated parity involution. -/
theorem parPow_evenMap (V : SuperVect) (n : ℕ) :
    (parPow V n).evenMap = LinearMap.id := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change ((parPow V n) ≫ parHom V).evenMap = _
      rw [SuperVect.cat_comp_evenMap, parHom_evenMap, ih]
      rfl

/-- The odd component of the iterated parity involution. -/
theorem parPow_oddMap (V : SuperVect) (n : ℕ) :
    (parPow V n).oddMap = ((-1 : ℂ) ^ n) • LinearMap.id := by
  induction n with
  | zero => simp [parPow, SuperVect.cat_id_oddMap]
  | succ n ih =>
      change ((parPow V n) ≫ parHom V).oddMap = _
      rw [SuperVect.cat_comp_oddMap, parHom_oddMap, ih, pow_succ]
      ext v
      simp

/-- The super trace of an iterated parity involution. -/
theorem sTr_parPow (V : SuperVect) (n : ℕ) :
    sTr (parPow V n) = (Module.finrank ℂ V.even : ℂ) +
      (-1 : ℂ) ^ n * (Module.finrank ℂ V.odd : ℂ) := by
  rw [sTr, parPow_evenMap, parPow_oddMap, map_smul,
    LinearMap.trace_id, LinearMap.trace_id]
  simp

/-! ## The total space and the total tensor identification

The underlying vector space of a super vector space is the product
of its components; the graded tensor product's total space is the
tensor product of the total spaces, by the four-block shuffle
`totTensor`.  All structure maps of `SuperVect` are conjugates of
plain linear maps under this identification, which is what the
braiding trace identity is proved through. -/

/-- The super trace is the plain trace of the total map. -/
theorem sTr_eq_trace_tot {V : SuperVect} (f : V ⟶ V) :
    sTr f = LinearMap.trace ℂ (Tot V) (tot f) := by
  rw [sTr, tot, LinearMap.trace_prodMap']

/-- The middle shuffle of four product components:
`((A × B) × (C × D)) ≃ₗ ((A × D) × (B × C))`. -/
def prodShuffle (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D] :
    ((A × B) × (C × D)) ≃ₗ[ℂ] ((A × D) × (B × C)) where
  toFun x := ((x.1.1, x.2.2), (x.1.2, x.2.1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := ((x.1.1, x.2.1), (x.2.2, x.1.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The shuffle, applied. -/
@[simp]
theorem prodShuffle_apply (A B C D : Type*)
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] [AddCommGroup D] [Module ℂ D]
    (x : (A × B) × (C × D)) :
    prodShuffle A B C D x = ((x.1.1, x.2.2), (x.1.2, x.2.1)) := rfl

/-- **The total tensor identification**: the total space of a graded
tensor product is the tensor product of the total spaces, by the
four-block shuffle. -/
def totTensor (V W : SuperVect) :
    (Tot V ⊗[ℂ] Tot W) ≃ₗ[ℂ] Tot (SuperVect.tensorObj V W) :=
  (TensorProduct.prodLeft ℂ ℂ V.even V.odd (Tot W)).trans
    ((LinearEquiv.prodCongr
      (TensorProduct.prodRight ℂ ℂ V.even W.even W.odd)
      (TensorProduct.prodRight ℂ ℂ V.odd W.even W.odd)).trans
    (prodShuffle (V.even ⊗[ℂ] W.even) (V.even ⊗[ℂ] W.odd)
      (V.odd ⊗[ℂ] W.even) (V.odd ⊗[ℂ] W.odd)))

/-- The total tensor identification on a pure tensor. -/
@[simp]
theorem totTensor_tmul (V W : SuperVect) (x : Tot V) (y : Tot W) :
    totTensor V W (x ⊗ₜ y) =
      ((x.1 ⊗ₜ y.1, x.2 ⊗ₜ y.2), (x.1 ⊗ₜ y.2, x.2 ⊗ₜ y.1)) := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [totTensor, LinearEquiv.trans_apply,
    TensorProduct.prodLeft_tmul]
  rfl

/-- **Naturality of the total tensor identification**: the total map
of a graded tensor of morphisms is the plain tensor of the total
maps, conjugated by `totTensor`. -/
theorem tot_tensorHom {V₁ V₂ W₁ W₂ : SuperVect}
    (f : V₁ ⟶ V₂) (g : W₁ ⟶ W₂) :
    (tot (f ⊗ₘ g)).comp (totTensor V₁ W₁).toLinearMap =
      (totTensor V₂ W₂).toLinearMap.comp
        (TensorProduct.map (tot f) (tot g)) := by
  apply TensorProduct.ext'
  intro x y
  change tot (f ⊗ₘ g) (totTensor V₁ W₁ (x ⊗ₜ y)) =
    totTensor V₂ W₂ (TensorProduct.map (tot f) (tot g) (x ⊗ₜ y))
  rw [TensorProduct.map_tmul, totTensor_tmul, totTensor_tmul]
  change tot (SuperVect.tensorHom f g) _ = _
  simp only [tot, SuperVect.tensorHom_evenMap, SuperVect.tensorHom_oddMap,
    LinearMap.prodMap_apply]
  rfl

/-! ## The associator under the total identification -/

/-- The inverse of `prodRight` reassembles a pair of tensors with a
common first factor. -/
theorem prodRight_symm_tmul {A B C : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    [AddCommGroup C] [Module ℂ C] (a : A) (b : B) (c : C) :
    (TensorProduct.prodRight ℂ ℂ A B C).symm (a ⊗ₜ b, a ⊗ₜ c) =
      a ⊗ₜ (b, c) := by
  apply (TensorProduct.prodRight ℂ ℂ A B C).injective
  rw [LinearEquiv.apply_symm_apply, TensorProduct.prodRight_tmul]

/-- The module-level associator block of `SuperVect`, applied to the
pure elements produced by the total identification. -/
theorem assocAux_pure {A₁ A₂ B₁ B₂ C₁ C₂ : Type*}
    [AddCommGroup A₁] [Module ℂ A₁] [AddCommGroup A₂] [Module ℂ A₂]
    [AddCommGroup B₁] [Module ℂ B₁] [AddCommGroup B₂] [Module ℂ B₂]
    [AddCommGroup C₁] [Module ℂ C₁] [AddCommGroup C₂] [Module ℂ C₂]
    (a₁ : A₁) (a₂ : A₂) (b₁ : B₁) (b₂ : B₂) (c₁ : C₁) (c₂ : C₂) :
    SuperVect.assocAux A₁ A₂ B₁ B₂ C₁ C₂
        ((a₁ ⊗ₜ b₁, a₂ ⊗ₜ b₂) ⊗ₜ c₁, (a₁ ⊗ₜ b₂, a₂ ⊗ₜ b₁) ⊗ₜ c₂) =
      (a₁ ⊗ₜ (b₁ ⊗ₜ c₁, b₂ ⊗ₜ c₂), a₂ ⊗ₜ (b₁ ⊗ₜ c₂, b₂ ⊗ₜ c₁)) := by
  have h4 : ∀ (x : ((A₁ ⊗[ℂ] B₁) ⊗[ℂ] C₁) × ((A₂ ⊗[ℂ] B₂) ⊗[ℂ] C₁))
      (y : ((A₁ ⊗[ℂ] B₂) ⊗[ℂ] C₂) × ((A₂ ⊗[ℂ] B₁) ⊗[ℂ] C₂)),
      SuperVect.prod4Perm ((A₁ ⊗[ℂ] B₁) ⊗[ℂ] C₁)
        ((A₂ ⊗[ℂ] B₂) ⊗[ℂ] C₁) ((A₁ ⊗[ℂ] B₂) ⊗[ℂ] C₂)
        ((A₂ ⊗[ℂ] B₁) ⊗[ℂ] C₂) (x, y) =
        ((x.1, y.1), (y.2, x.2)) := fun _ _ => rfl
  simp only [SuperVect.assocAux, LinearEquiv.trans_apply,
    LinearEquiv.prodCongr_apply,
    TensorProduct.prodLeft_tmul, h4, TensorProduct.assoc_tmul,
    prodRight_symm_tmul]

/-- **The associator under the total identification** is the plain
associator of the total spaces. -/
theorem tot_associator (V W Z : SuperVect) :
    (tot (α_ V W Z).hom).comp
        ((totTensor (SuperVect.tensorObj V W) Z).toLinearMap.comp
          (TensorProduct.map (totTensor V W).toLinearMap
            LinearMap.id)) =
      ((totTensor V (SuperVect.tensorObj W Z)).toLinearMap.comp
          (TensorProduct.map LinearMap.id
            (totTensor W Z).toLinearMap)).comp
        (TensorProduct.assoc ℂ (Tot V) (Tot W) (Tot Z)).toLinearMap
    := by
  apply TensorProduct.ext'
  intro u z
  induction u using TensorProduct.inductionOn with
  | add a b ha hb => simp only [TensorProduct.add_tmul, map_add, ha, hb]
  | tmul x y =>
      change tot (α_ V W Z).hom
          (totTensor (SuperVect.tensorObj V W) Z
            (TensorProduct.map (totTensor V W).toLinearMap
              LinearMap.id ((x ⊗ₜ y) ⊗ₜ z))) =
        totTensor V (SuperVect.tensorObj W Z)
          (TensorProduct.map LinearMap.id (totTensor W Z).toLinearMap
            (TensorProduct.assoc ℂ (Tot V) (Tot W) (Tot Z)
              ((x ⊗ₜ y) ⊗ₜ z)))
      rw [TensorProduct.map_tmul, TensorProduct.assoc_tmul,
        TensorProduct.map_tmul, LinearMap.id_apply,
        LinearMap.id_apply, LinearEquiv.coe_coe,
        LinearEquiv.coe_coe, totTensor_tmul, totTensor_tmul,
        totTensor_tmul, totTensor_tmul]
      change (LinearMap.prodMap
          ((SuperVect.associator V W Z).hom.evenMap)
          ((SuperVect.associator V W Z).hom.oddMap)) _ = _
      rw [SuperVect.associator_hom_evenMap,
        SuperVect.associator_hom_oddMap]
      change ((SuperVect.assocEvenEquiv V W Z) _,
        (SuperVect.assocOddEquiv V W Z) _) = _
      rw [show SuperVect.assocEvenEquiv V W Z =
        SuperVect.assocAux V.even V.odd W.even W.odd Z.even Z.odd
        from rfl]
      rw [show SuperVect.assocOddEquiv V W Z =
        SuperVect.assocAux V.even V.odd W.even W.odd Z.odd Z.even
        from rfl]
      dsimp only
      exact congrArg₂ Prod.mk
        (assocAux_pure x.1 x.2 y.1 y.2 z.1 z.2)
        (assocAux_pure x.1 x.2 y.1 y.2 z.2 z.1)

/-! ## The Koszul braiding under the total identification -/

/-- Projection onto the even summand of a total space. -/
def totEvenProj (V : SuperVect) : Tot V →ₗ[ℂ] Tot V :=
  (LinearMap.inl ℂ V.even V.odd).comp (LinearMap.fst ℂ V.even V.odd)

/-- Projection onto the odd summand of a total space. -/
def totOddProj (V : SuperVect) : Tot V →ₗ[ℂ] Tot V :=
  (LinearMap.inr ℂ V.even V.odd).comp (LinearMap.snd ℂ V.even V.odd)

/-- **The signed flip of total spaces**: the plain flip on the even
part of the first factor, and the parity-twisted flip on its odd
part — the Koszul rule `(−1)^{|x||y|}` in operator form. -/
def signedFlip (V W : SuperVect) :
    (Tot V ⊗[ℂ] Tot W) →ₗ[ℂ] (Tot W ⊗[ℂ] Tot V) :=
  (TensorProduct.comm ℂ (Tot V) (Tot W)).toLinearMap.comp
    (TensorProduct.map (totEvenProj V) LinearMap.id +
      TensorProduct.map (totOddProj V) (tot (parHom W)))

/-- The signed flip on a pure tensor. -/
theorem signedFlip_tmul (V W : SuperVect) (x : Tot V) (y : Tot W) :
    signedFlip V W (x ⊗ₜ y) =
      y ⊗ₜ ((x.1, 0) : Tot V) +
        ((y.1, -y.2) : Tot W) ⊗ₜ ((0, x.2) : Tot V) := by
  simp only [signedFlip, LinearMap.comp_apply, LinearMap.add_apply,
    TensorProduct.map_tmul, map_add]
  rfl

/-- The even Koszul block on a pair. -/
theorem koszulBraidingEven_pair (V W : SuperVect)
    (a : V.even ⊗[ℂ] W.even) (b : V.odd ⊗[ℂ] W.odd) :
    SuperVect.koszulBraidingEven V W (a, b) =
      (TensorProduct.comm ℂ V.even W.even a,
        -(TensorProduct.comm ℂ V.odd W.odd b)) := rfl

/-- **The Koszul braiding under the total identification** is the
signed flip. -/
theorem tot_koszulBraiding (V W : SuperVect) :
    (tot (β_ V W).hom).comp (totTensor V W).toLinearMap =
      (totTensor W V).toLinearMap.comp (signedFlip V W) := by
  apply TensorProduct.ext'
  intro x y
  obtain ⟨x1, x2⟩ := x
  have hx : ((x1, x2) : Tot V) = (x1, 0) + (0, x2) := by
    rw [Prod.mk_add_mk, add_zero, zero_add]
  change tot (β_ V W).hom (totTensor V W ((x1, x2) ⊗ₜ y)) =
    totTensor W V (signedFlip V W ((x1, x2) ⊗ₜ y))
  rw [hx, TensorProduct.add_tmul, map_add, map_add, map_add, map_add]
  refine congrArg₂ (· + ·) ?_ ?_
  · rw [totTensor_tmul, signedFlip_tmul]
    dsimp only
    rw [show ((0, 0) : Tot V) = 0 from rfl, TensorProduct.tmul_zero,
      add_zero, TensorProduct.zero_tmul,
      TensorProduct.zero_tmul, totTensor_tmul]
    change (SuperVect.koszulBraidingEven V W (x1 ⊗ₜ y.1, 0),
        SuperVect.koszulBraidingOdd V W (x1 ⊗ₜ y.2, 0)) = _
    rw [koszulBraidingEven_pair, SuperVect.koszulBraidingOdd_pair]
    simp [TensorProduct.comm_tmul, TensorProduct.tmul_zero]
  · rw [totTensor_tmul, signedFlip_tmul]
    dsimp only
    rw [show ((0, 0) : Tot V) = 0 from rfl, TensorProduct.tmul_zero,
      zero_add, TensorProduct.zero_tmul,
      TensorProduct.zero_tmul, totTensor_tmul]
    change (SuperVect.koszulBraidingEven V W (0, x2 ⊗ₜ y.2),
        SuperVect.koszulBraidingOdd V W (0, x2 ⊗ₜ y.1)) = _
    rw [koszulBraidingEven_pair, SuperVect.koszulBraidingOdd_pair]
    simp [TensorProduct.comm_tmul, TensorProduct.tmul_zero,
      TensorProduct.neg_tmul]

/-! ## Plain trace identities

The linear-algebra core of the braiding trace computation: tracing
a tensor of maps against the flip contracts to the trace of the
composite, and the same identity holds with a spectator factor and a
twist on the last slot. -/

section PlainTrace

variable {U V : Type*}

/-- **The contraction identity**: the trace of `f ⊗ g` against the
flip is the trace of `f ∘ g`. -/
theorem trace_map_comp_comm
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f g : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ (V ⊗[ℂ] V)
        ((TensorProduct.map f g).comp
          (TensorProduct.comm ℂ V V).toLinearMap) =
      LinearMap.trace ℂ V (f.comp g) := by
  classical
  set b := Module.Free.chooseBasis ℂ V with hb
  rw [LinearMap.trace_eq_matrix_trace ℂ (b.tensorProduct b),
    LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace, Matrix.trace,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdiag : ∀ j,
      (LinearMap.toMatrix (b.tensorProduct b) (b.tensorProduct b)
        ((TensorProduct.map f g).comp
          (TensorProduct.comm ℂ V V).toLinearMap)).diag (i, j) =
      b.repr (g (b i)) j * b.repr (f (b j)) i := by
    intro j
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply,
      Module.Basis.tensorProduct_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, TensorProduct.comm_tmul,
      TensorProduct.map_tmul,
      Module.Basis.tensorProduct_repr_tmul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl fun j _ => hdiag j, Matrix.diag_apply,
    LinearMap.toMatrix_apply, LinearMap.comp_apply]
  conv_rhs => rw [show g (b i) = ∑ j, b.repr (g (b i)) j • b j from
    (b.sum_repr _).symm]
  simp only [map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, smul_eq_mul]

/-- **The spectator contraction identity**: with a spectator factor
`U`, a twist `H` on the outer slot and modifications `s`, `t` inside
the flip, the trace contracts to a trace over `U ⊗ V`. -/
theorem trace_flip_twist
    [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (G : U ⊗[ℂ] V →ₗ[ℂ] U ⊗[ℂ] V)
    (H s t : V →ₗ[ℂ] V) :
    LinearMap.trace ℂ ((U ⊗[ℂ] V) ⊗[ℂ] V)
        ((TensorProduct.map LinearMap.id H).comp
          ((TensorProduct.map G LinearMap.id).comp
            (((TensorProduct.assoc ℂ U V V).symm.toLinearMap).comp
              ((TensorProduct.map LinearMap.id
                ((TensorProduct.comm ℂ V V).toLinearMap.comp
                  (TensorProduct.map s t))).comp
                (TensorProduct.assoc ℂ U V V).toLinearMap)))) =
      LinearMap.trace ℂ (U ⊗[ℂ] V)
        (G.comp (TensorProduct.map LinearMap.id
          ((t.comp H).comp s))) := by
  classical
  -- reduce to pure tensors of endomorphisms via the hom-tensor-hom
  -- equivalence
  obtain ⟨T, rfl⟩ := (homTensorHomEquiv ℂ U V U V).surjective G
  rw [homTensorHomEquiv_apply]
  induction T using TensorProduct.inductionOn with
  | add a c ha hc =>
      rw [map_add, TensorProduct.map_add_left, LinearMap.add_comp,
        LinearMap.comp_add, map_add, ha, hc, LinearMap.add_comp,
        map_add]
  | tmul f₀ g₀ =>
      rw [TensorProduct.homTensorHomMap_apply]
      -- identify the composite with an associator conjugate
      have hcomp :
          (TensorProduct.map LinearMap.id H).comp
            ((TensorProduct.map (TensorProduct.map f₀ g₀)
              LinearMap.id).comp
              (((TensorProduct.assoc ℂ U V V).symm.toLinearMap).comp
                ((TensorProduct.map LinearMap.id
                  ((TensorProduct.comm ℂ V V).toLinearMap.comp
                    (TensorProduct.map s t))).comp
                  (TensorProduct.assoc ℂ U V V).toLinearMap))) =
          (((TensorProduct.assoc ℂ U V V).symm.toLinearMap).comp
            ((TensorProduct.map f₀
              ((TensorProduct.map (g₀.comp t) (H.comp s)).comp
                (TensorProduct.comm ℂ V V).toLinearMap)).comp
              (TensorProduct.assoc ℂ U V V).toLinearMap)) := by
        apply TensorProduct.ext'
        intro w z
        induction w using TensorProduct.inductionOn with
        | add w₁ w₂ h₁ h₂ =>
            rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂]
        | tmul u v =>
            simp [TensorProduct.assoc_tmul, TensorProduct.comm_tmul,
              TensorProduct.map_tmul, TensorProduct.assoc_symm_tmul]
      rw [hcomp]
      -- conjugation by the associator preserves the trace
      rw [show (((TensorProduct.assoc ℂ U V V).symm.toLinearMap).comp
            ((TensorProduct.map f₀
              ((TensorProduct.map (g₀.comp t) (H.comp s)).comp
                (TensorProduct.comm ℂ V V).toLinearMap)).comp
              (TensorProduct.assoc ℂ U V V).toLinearMap)) =
          (TensorProduct.assoc ℂ U V V).symm.conj
            (TensorProduct.map f₀
              ((TensorProduct.map (g₀.comp t) (H.comp s)).comp
                (TensorProduct.comm ℂ V V).toLinearMap)) from by
        rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm]
        rfl]
      rw [LinearMap.trace_conj', LinearMap.trace_tensorProduct',
        trace_map_comp_comm]
      rw [show (TensorProduct.map f₀ g₀).comp
            (TensorProduct.map LinearMap.id ((t.comp H).comp s)) =
          TensorProduct.map f₀ (g₀.comp ((t.comp H).comp s)) from by
        rw [← TensorProduct.map_comp, LinearMap.comp_id]]
      rw [LinearMap.trace_tensorProduct']
      congr 2

end PlainTrace

/-! ## The braiding partial-trace identity -/

/-- A monoid-instance form of the trace commutation, so that the
statement's instances match those of concretely built product and
tensor types without deep unfolding. -/
private theorem trace_comp_comm_monoid {M N : Type*}
    [AddCommMonoid M] [Module ℂ M] [Module.Free ℂ M]
    [Module.Finite ℂ M] [AddCommMonoid N] [Module ℂ N]
    [Module.Free ℂ N] [Module.Finite ℂ N]
    (f : M →ₗ[ℂ] N) (g : N →ₗ[ℂ] M) :
    LinearMap.trace ℂ M (g ∘ₗ f) = LinearMap.trace ℂ N (f ∘ₗ g) := by
  let : AddCommGroup M := Module.addCommMonoidToAddCommGroup ℂ
  let : AddCommGroup N := Module.addCommMonoidToAddCommGroup ℂ
  exact LinearMap.trace_comp_comm' f g

-- Raised budget: the supertrace is conjugated through the
-- braiding on each of the four parity blocks.
private theorem sTr_comp_whiskerLeft_total (P X : SuperVect)
    (g : SuperVect.tensorObj P X ⟶ SuperVect.tensorObj P X) (k : X ⟶ X) :
    sTr (g ≫ (P ◁ k)) =
      LinearMap.trace ℂ _
        ((((totTensor P X).symm.toLinearMap.comp (tot g)).comp
          (totTensor P X).toLinearMap).comp
          (TensorProduct.map LinearMap.id (tot k))) := by
  classical
  set TP := totTensor P X
  set g' : (Tot P ⊗[ℂ] Tot X) →ₗ[ℂ] Tot P ⊗[ℂ] Tot X :=
    (TP.symm.toLinearMap.comp (tot g)).comp TP.toLinearMap with hg'
  have hwhiskk : ∀ y, tot (P ◁ k) (TP y) =
      TP (TensorProduct.map LinearMap.id (tot k) y) := by
    intro y
    have h1 := LinearMap.congr_fun (tot_tensorHom (𝟙 P) k) y
    rwa [tot_id] at h1
  have hRHS : sTr (g ≫ (P ◁ k)) =
      LinearMap.trace ℂ _
        (g'.comp (TensorProduct.map LinearMap.id (tot k))) := by
    rw [sTr_eq_trace_tot, tot_comp]
    have hcomp2 : tot (P ◁ k) =
        (TP.toLinearMap.comp
          (TensorProduct.map LinearMap.id (tot k))).comp
          TP.symm.toLinearMap := by
      refine LinearMap.ext fun z => ?_
      have h1 := hwhiskk (TP.symm z)
      rw [LinearEquiv.apply_symm_apply] at h1
      simpa using h1
    rw [hcomp2]
    rw [show ((TP.toLinearMap.comp
        (TensorProduct.map LinearMap.id (tot k))).comp
        TP.symm.toLinearMap).comp (tot g) =
      TP.toLinearMap.comp
        (((TensorProduct.map LinearMap.id (tot k)).comp
          TP.symm.toLinearMap).comp (tot g)) from by
      simp only [LinearMap.comp_assoc]]
    rw [LinearMap.trace_comp_comm']
    rw [show (((TensorProduct.map LinearMap.id (tot k)).comp
        TP.symm.toLinearMap).comp (tot g)).comp TP.toLinearMap =
      (TensorProduct.map LinearMap.id (tot k)).comp g' from by
      rw [hg']
      simp only [LinearMap.comp_assoc]]
    rw [LinearMap.trace_comp_comm']
  exact hRHS

/-- **The braiding partial-trace identity**: composing the braiding
of the top two slots with a whiskered endomorphism and a twist of
the top slot traces to the endomorphism alone, with the twist
parity-corrected and moved down one slot.  This is the engine of the
cycle evaluation. -/
theorem sTr_swap_conj (P X : SuperVect)
    (g : SuperVect.tensorObj P X ⟶ SuperVect.tensorObj P X)
    (h : X ⟶ X) :
    sTr ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv ≫
        (g ▷ X) ≫ (SuperVect.tensorObj P X ◁ h)) =
      sTr (g ≫ (P ◁ (h ≫ parHom X))) := by
  classical
  set TP := totTensor P X with hTP
  set TXX := totTensor X X with hTXX
  set TA := totTensor (SuperVect.tensorObj P X) X with hTA
  set TB := totTensor P (SuperVect.tensorObj X X) with hTB
  set A := TensorProduct.assoc ℂ (Tot P) (Tot X) (Tot X) with hAdef
  set Jlin : ((Tot P ⊗[ℂ] Tot X) ⊗[ℂ] Tot X) →ₗ[ℂ]
      Tot (SuperVect.tensorObj (SuperVect.tensorObj P X) X) :=
    TA.toLinearMap.comp
      (TensorProduct.map TP.toLinearMap LinearMap.id) with hJlin
  set J'lin : (Tot P ⊗[ℂ] (Tot X ⊗[ℂ] Tot X)) →ₗ[ℂ]
      Tot (SuperVect.tensorObj P (SuperVect.tensorObj X X)) :=
    TB.toLinearMap.comp
      (TensorProduct.map LinearMap.id TXX.toLinearMap) with hJ'lin
  set g' : (Tot P ⊗[ℂ] Tot X) →ₗ[ℂ] Tot P ⊗[ℂ] Tot X :=
    (TP.symm.toLinearMap.comp (tot g)).comp TP.toLinearMap with hg'
  set k : X ⟶ X := h ≫ parHom X with hk
  -- the five conjugation steps, pointwise
  have halpha : ∀ x, tot (α_ P X X).hom (Jlin x) = J'lin (A x) :=
    fun x => LinearMap.congr_fun (tot_associator P X X) x
  have hwhiskβ : ∀ y, tot (P ◁ (β_ X X).hom) (TB y) =
      TB (TensorProduct.map LinearMap.id (tot (β_ X X).hom) y) := by
    intro y
    have h1 := LinearMap.congr_fun
      (tot_tensorHom (𝟙 P) (β_ X X).hom) y
    rwa [tot_id] at h1
  have hbeta : ∀ x, tot (P ◁ (β_ X X).hom) (J'lin x) =
      J'lin (TensorProduct.map LinearMap.id (signedFlip X X) x) := by
    intro x
    change tot (P ◁ (β_ X X).hom)
        (TB (TensorProduct.map LinearMap.id TXX.toLinearMap x)) =
      TB (TensorProduct.map LinearMap.id TXX.toLinearMap
        (TensorProduct.map LinearMap.id (signedFlip X X) x))
    rw [hwhiskβ, TensorProduct.map_map, TensorProduct.map_map,
      tot_koszulBraiding]
  have hcancelα : ∀ y, tot (α_ P X X).inv (tot (α_ P X X).hom y) = y
      := by
    intro y
    rw [← LinearMap.comp_apply, ← tot_comp, Iso.hom_inv_id, tot_id,
      LinearMap.id_apply]
  have halphainv : ∀ x, tot (α_ P X X).inv (J'lin x) =
      Jlin (A.symm x) := by
    intro x
    have h1 := halpha (A.symm x)
    rw [LinearEquiv.apply_symm_apply] at h1
    rw [← h1, hcancelα]
  have hgconj : (tot g).comp TP.toLinearMap = TP.toLinearMap.comp g'
      := by
    refine LinearMap.ext fun y => ?_
    change tot g (TP y) = TP (g' y)
    rw [hg']
    simp
  have hwhiskg : ∀ y, tot (g ▷ X) (TA y) =
      TA (TensorProduct.map (tot g) LinearMap.id y) := by
    intro y
    have h1 := LinearMap.congr_fun (tot_tensorHom g (𝟙 X)) y
    rwa [tot_id] at h1
  have hgstep : ∀ x, tot (g ▷ X) (Jlin x) =
      Jlin (TensorProduct.map g' LinearMap.id x) := by
    intro x
    change tot (g ▷ X)
        (TA (TensorProduct.map TP.toLinearMap LinearMap.id x)) =
      TA (TensorProduct.map TP.toLinearMap LinearMap.id
        (TensorProduct.map g' LinearMap.id x))
    rw [hwhiskg, TensorProduct.map_map, TensorProduct.map_map,
      hgconj]
  have hwhiskh : ∀ y,
      tot (SuperVect.tensorObj P X ◁ h) (TA y) =
      TA (TensorProduct.map LinearMap.id (tot h) y) := by
    intro y
    have h1 := LinearMap.congr_fun
      (tot_tensorHom (𝟙 (SuperVect.tensorObj P X)) h) y
    rwa [tot_id] at h1
  have hhstep : ∀ x, tot (SuperVect.tensorObj P X ◁ h) (Jlin x) =
      Jlin (TensorProduct.map LinearMap.id (tot h) x) := by
    intro x
    change tot (SuperVect.tensorObj P X ◁ h)
        (TA (TensorProduct.map TP.toLinearMap LinearMap.id x)) =
      TA (TensorProduct.map TP.toLinearMap LinearMap.id
        (TensorProduct.map LinearMap.id (tot h) x))
    rw [hwhiskh, TensorProduct.map_map, TensorProduct.map_map]
    simp only [LinearMap.id_comp, LinearMap.comp_id]
  -- the conjugated composite
  set C' : ((Tot P ⊗[ℂ] Tot X) ⊗[ℂ] Tot X) →ₗ[ℂ]
      ((Tot P ⊗[ℂ] Tot X) ⊗[ℂ] Tot X) :=
    (TensorProduct.map LinearMap.id (tot h)).comp
      ((TensorProduct.map g' LinearMap.id).comp
        (A.symm.toLinearMap.comp
          ((TensorProduct.map LinearMap.id (signedFlip X X)).comp
            A.toLinearMap))) with hC'
  have htotpt : ∀ {V₁ V₂ V₃ : SuperVect} (a : V₁ ⟶ V₂)
      (b : V₂ ⟶ V₃) (y : Tot V₁),
      tot (a ≫ b) y = tot b (tot a y) := by
    intro V₁ V₂ V₃ a b y
    rw [tot_comp]
    rfl
  have hchain : ∀ x,
      tot ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv ≫
        (g ▷ X) ≫ (SuperVect.tensorObj P X ◁ h)) (Jlin x) =
      Jlin (C' x) := by
    intro x
    rw [htotpt, htotpt, htotpt, htotpt, halpha, hbeta, halphainv,
      hgstep, hhstep]
    rfl
  -- the total identification as an equivalence, and the trace
  set JE : ((Tot P ⊗[ℂ] Tot X) ⊗[ℂ] Tot X) ≃ₗ[ℂ]
      Tot (SuperVect.tensorObj (SuperVect.tensorObj P X) X) :=
    (TensorProduct.congr TP (LinearEquiv.refl ℂ (Tot X))).trans TA
    with hJE
  have hJapp : ∀ x, JE x = Jlin x := fun _ => rfl
  have hfact :
      tot ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv ≫
        (g ▷ X) ≫ (SuperVect.tensorObj P X ◁ h)) =
      (JE.toLinearMap.comp C').comp JE.symm.toLinearMap := by
    refine LinearMap.ext fun z => ?_
    change tot _ z = JE (C' (JE.symm z))
    conv_lhs => rw [show z = JE (JE.symm z) from
      (JE.apply_symm_apply z).symm]
    rw [show (JE (JE.symm z) :
        Tot (SuperVect.tensorObj (SuperVect.tensorObj P X) X)) =
      Jlin (JE.symm z) from hJapp _]
    rw [hchain]
    exact (hJapp _).symm
  have htrace1 :
      sTr ((α_ P X X).hom ≫ (P ◁ (β_ X X).hom) ≫ (α_ P X X).inv ≫
        (g ▷ X) ≫ (SuperVect.tensorObj P X ◁ h)) =
      LinearMap.trace ℂ _ C' := by
    have e1 : LinearMap.trace ℂ
        (Tot (SuperVect.tensorObj (SuperVect.tensorObj P X) X))
        ((JE.toLinearMap.comp C').comp JE.symm.toLinearMap) =
      LinearMap.trace ℂ ((Tot P ⊗[ℂ] Tot X) ⊗[ℂ] Tot X)
        (JE.symm.toLinearMap.comp (JE.toLinearMap.comp C')) :=
      trace_comp_comm_monoid JE.symm.toLinearMap
        (JE.toLinearMap.comp C')
    have e2 : JE.symm.toLinearMap.comp (JE.toLinearMap.comp C') = C'
        := LinearMap.ext fun z => JE.symm_apply_apply (C' z)
    rw [e2] at e1
    rw [sTr_eq_trace_tot, hfact]
    exact e1
  -- split the signed flip and contract each summand
  have hsplit : C' =
      (TensorProduct.map LinearMap.id (tot h)).comp
        ((TensorProduct.map g' LinearMap.id).comp
          (A.symm.toLinearMap.comp
            ((TensorProduct.map LinearMap.id
              ((TensorProduct.comm ℂ (Tot X) (Tot X)).toLinearMap.comp
                (TensorProduct.map (totEvenProj X)
                  LinearMap.id))).comp A.toLinearMap))) +
      (TensorProduct.map LinearMap.id (tot h)).comp
        ((TensorProduct.map g' LinearMap.id).comp
          (A.symm.toLinearMap.comp
            ((TensorProduct.map LinearMap.id
              ((TensorProduct.comm ℂ (Tot X) (Tot X)).toLinearMap.comp
                (TensorProduct.map (totOddProj X)
                  (tot (parHom X))))).comp A.toLinearMap))) := by
    rw [hC', signedFlip, LinearMap.comp_add,
      TensorProduct.map_add_right, LinearMap.add_comp,
      LinearMap.comp_add, LinearMap.comp_add, LinearMap.comp_add]
  have htrace2 : LinearMap.trace ℂ _ C' =
      LinearMap.trace ℂ _ (g'.comp (TensorProduct.map LinearMap.id
        ((LinearMap.id.comp (tot h)).comp (totEvenProj X)))) +
      LinearMap.trace ℂ _ (g'.comp (TensorProduct.map LinearMap.id
        (((tot (parHom X)).comp (tot h)).comp (totOddProj X)))) := by
    rw [hsplit, map_add]
    exact congrArg₂ (· + ·)
      (trace_flip_twist g' (tot h) (totEvenProj X) LinearMap.id)
      (trace_flip_twist g' (tot h) (totOddProj X) (tot (parHom X)))
  have hkey : (LinearMap.id.comp (tot h)).comp (totEvenProj X) +
      ((tot (parHom X)).comp (tot h)).comp (totOddProj X) = tot k
      := by
    refine LinearMap.ext fun x => ?_
    change (tot h ((x.1, 0) : Tot X)) +
      tot (parHom X) (tot h ((0, x.2) : Tot X)) = tot k x
    rw [hk]
    change ((SuperVect.Hom.evenMap h x.1, SuperVect.Hom.oddMap h 0)
        : Tot X) +
      ((SuperVect.Hom.evenMap h 0,
        -SuperVect.Hom.oddMap h x.2) : Tot X) =
      ((SuperVect.Hom.evenMap h x.1, -SuperVect.Hom.oddMap h x.2)
        : Tot X)
    rw [map_zero, map_zero, Prod.mk_add_mk, add_zero, zero_add]
  have htrace3 : LinearMap.trace ℂ _ C' =
      LinearMap.trace ℂ _
        (g'.comp (TensorProduct.map LinearMap.id (tot k))) := by
    rw [htrace2]
    have hsum : g'.comp (TensorProduct.map LinearMap.id
          ((LinearMap.id.comp (tot h)).comp (totEvenProj X))) +
        g'.comp (TensorProduct.map LinearMap.id
          (((tot (parHom X)).comp (tot h)).comp (totOddProj X))) =
        g'.comp (TensorProduct.map LinearMap.id (tot k)) := by
      rw [← LinearMap.comp_add, ← TensorProduct.map_add_right, hkey]
    rw [← map_add, hsum]
  -- identify the right-hand side
  have hRHS := sTr_comp_whiskerLeft_total P X g k
  rw [htrace1, htrace3, hRHS]

/-! ## The trace of the standard cycles

Unrolling the bubbling `insertTop X n n` through the braiding
partial-trace identity leaves an iterated parity twist: each
braiding step converts one slot's twist into a parity correction. -/

/-- **The bubbling trace, with a twist**: the full insertion
composed with a twist of the top slot traces to the `n`-fold parity
correction of the twist. -/
theorem sTr_insertTop_full (X : SuperVect) :
    ∀ (n : ℕ) (h : X ⟶ X),
      sTr (insertTop X n n ≫ (tensorPow SuperVect X n ◁ h)) =
        sTr (parPow X n ≫ h) := by
  intro n
  induction n with
  | zero =>
      intro h
      erw [show insertTop X 0 0 = 𝟙 _ from insertTop_zero X 0,
        Category.id_comp]
      change sTr (𝟙 (tensorPow SuperVect X 0) ⊗ₘ h) = _
      rw [sTr_tensorHom, sTr_id, parPow, Category.id_comp]
      rw [show Module.finrank ℂ (tensorPow SuperVect X 0).even
        = 1 from Module.finrank_self ℂ]
      have : Subsingleton (tensorPow SuperVect X 0).odd :=
        inferInstanceAs (Subsingleton PUnit)
      rw [show Module.finrank ℂ (tensorPow SuperVect X 0).odd
        = 0 from Module.finrank_eq_zero_of_subsingleton _ _]
      norm_num
  | succ n ih =>
      intro h
      have h1 : sTr (insertTop X (n + 1) (n + 1) ≫
            (tensorPow SuperVect X (n + 1) ◁ h)) =
          sTr (insertTop X n n ≫
            (tensorPow SuperVect X n ◁ (h ≫ parHom X))) :=
        sTr_swap_conj (tensorPow SuperVect X n) X (insertTop X n n)
          h
      rw [h1, ih (h ≫ parHom X)]
      rw [show parPow X n ≫ h ≫ parHom X =
        parPow X (n + 1) ≫ h from by
        rw [parHom_comm h, ← Category.assoc]
        rfl]

/-- **The trace of the standard cycle** on the tensor power is the
alternating parity trace. -/
theorem sTr_permMor_topCycle_zero (X : SuperVect) (n : ℕ) :
    sTr (permMor X (n + 1) (topCycle (0 : Fin (n + 1)))) =
      sTr (parPow X n) := by
  have h2 : insertTop X n n ≫
      (tensorPow SuperVect X n ◁ (𝟙 X)) = insertTop X n n := by
    rw [MonoidalCategory.whiskerLeft_id]
    change insertTop X n n ≫ 𝟙 (tensorPow SuperVect X (n + 1)) = _
    rw [Category.comp_id]
  rw [permMor_topCycle,
    show ((0 : Fin (n + 1)) : ℕ) = 0 from rfl, Nat.sub_zero]
  calc sTr (insertTop X n n)
      = sTr (insertTop X n n ≫
          (tensorPow SuperVect X n ◁ (𝟙 X))) :=
        (congrArg sTr h2).symm
    _ = sTr (parPow X n ≫ 𝟙 X) := sTr_insertTop_full X n (𝟙 X)
    _ = sTr (parPow X n) := congrArg sTr (Category.comp_id _)

/-! ## The super character of the permutation action -/

/-- **The super character**: the trace of a permutation's action on
the tensor power of the standard super object. -/
def superChar (p q n : ℕ) (σ : Equiv.Perm (Fin n)) : ℂ :=
  sTr (permMor (stdSuper p q) n σ)

/-- The super character is a class function. -/
theorem superChar_conj (p q : ℕ) {n : ℕ}
    (τ σ : Equiv.Perm (Fin n)) :
    superChar p q n (τ * σ * τ⁻¹) = superChar p q n σ := by
  unfold superChar
  rw [show τ * σ * τ⁻¹ = τ * (σ * τ⁻¹) from mul_assoc τ σ τ⁻¹,
    permMor_mul, permMor_mul]
  rw [Category.assoc, sTr_comp_comm]
  rw [Category.assoc, ← permMor_mul, inv_mul_cancel, permMor_one,
    Category.comp_id]

/-- The super character is multiplicative over block embeddings. -/
theorem superChar_blockEmbed (p q : ℕ) {a b : ℕ}
    (σ : Equiv.Perm (Fin a)) (τ : Equiv.Perm (Fin b)) :
    superChar p q (a + b) (blockEmbed σ τ) =
      superChar p q a σ * superChar p q b τ := by
  set X := stdSuper p q with hX
  have h1 : permMor X (a + b) (blockEmbed σ τ) =
      (tensorPowConcat X a b).inv ≫
        ((permMor X a σ ⊗ₘ permMor X b τ) ≫
          (tensorPowConcat X a b).hom) := by
    rw [← tensorPowConcat_permMor, Iso.inv_hom_id_assoc]
  unfold superChar
  rw [h1, sTr_conj, sTr_tensorHom]

/-- The standard cycle of each length: the full rotation. -/
def nfCycle : (c : ℕ) → Equiv.Perm (Fin c)
  | 0 => 1
  | _ + 1 => topCycle 0

/-- The super character of a standard cycle is the super power
sum. -/
theorem superChar_nfCycle (p q : ℕ) {c : ℕ} (hc : 1 ≤ c) :
    superChar p q c (nfCycle c) = superPS p q c := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  unfold superChar
  rw [show nfCycle (m + 1) = topCycle 0 from rfl,
    sTr_permMor_topCycle_zero, sTr_parPow]
  rw [show Module.finrank ℂ (stdSuper p q).even = p from
    Module.finrank_fin_fun ℂ]
  rw [show Module.finrank ℂ (stdSuper p q).odd = q from
    Module.finrank_fin_fun ℂ]
  rw [superPS, show (-1 : ℂ) ^ (m + 1 + 1) = (-1 : ℂ) ^ m from by
    rw [pow_succ, pow_succ]
    ring]

/-! ## Normal forms and cycle types -/

/-- Relabelling along an embedding preserves the cycle type. -/
theorem cycleType_viaEmbedding {α β : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : Equiv.Perm α) (ι : α ↪ β) :
    (e.viaEmbedding ι).cycleType = e.cycleType := by
  rw [Equiv.Perm.viaEmbedding]
  let : DecidablePred (· ∈ Set.range ι.toFun) :=
    fun a => Classical.propDecidable _
  exact Equiv.Perm.cycleType_extendDomain _

/-- A one-sided block embedding is a relabelling along the
first-block embedding. -/
theorem blockEmbed_fst_viaEmbedding {a b : ℕ}
    (σ : Equiv.Perm (Fin a)) :
    blockEmbed σ (1 : Equiv.Perm (Fin b)) =
      σ.viaEmbedding (Fin.castAddEmb b) := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i =>
      rw [blockEmbed_castAdd,
        show Fin.castAdd b i = Fin.castAddEmb b i from rfl,
        Equiv.Perm.viaEmbedding_apply]
      rfl
  | right j =>
      rw [blockEmbed_natAdd, Equiv.Perm.one_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem]
      rintro ⟨i, hi⟩
      have := congrArg Fin.val hi
      simp only [Fin.castAddEmb_apply, Fin.val_castAdd,
        Fin.val_natAdd] at this
      omega

/-- A one-sided block embedding is a relabelling along the
last-block embedding. -/
theorem blockEmbed_snd_viaEmbedding {a b : ℕ}
    (τ : Equiv.Perm (Fin b)) :
    blockEmbed (1 : Equiv.Perm (Fin a)) τ =
      τ.viaEmbedding (Fin.natAddEmb a) := by
  refine Equiv.ext fun x => ?_
  induction x using Fin.addCases with
  | left i =>
      rw [blockEmbed_castAdd, Equiv.Perm.one_apply,
        Equiv.Perm.viaEmbedding_apply_of_notMem]
      rintro ⟨j, hj⟩
      have := congrArg Fin.val hj
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd,
        Fin.val_castAdd] at this
      omega
  | right j =>
      rw [blockEmbed_natAdd,
        show Fin.natAdd a j = Fin.natAddEmb a j from rfl,
        Equiv.Perm.viaEmbedding_apply]
      rfl

/-- The two one-sided block embeddings are disjoint. -/
theorem blockEmbed_disjoint {a b : ℕ} (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    Equiv.Perm.Disjoint (blockEmbed σ (1 : Equiv.Perm (Fin b)))
      (blockEmbed (1 : Equiv.Perm (Fin a)) τ) := by
  intro x
  induction x using Fin.addCases with
  | left i =>
      right
      rw [blockEmbed_castAdd, Equiv.Perm.one_apply]
  | right j =>
      left
      rw [blockEmbed_natAdd, Equiv.Perm.one_apply]

/-- The cycle type of a block embedding is the sum of the cycle
types. -/
theorem cycleType_blockEmbed {a b : ℕ} (σ : Equiv.Perm (Fin a))
    (τ : Equiv.Perm (Fin b)) :
    (blockEmbed σ τ).cycleType = σ.cycleType + τ.cycleType := by
  rw [blockEmbed_decompose,
    (blockEmbed_disjoint σ τ).cycleType_mul,
    blockEmbed_fst_viaEmbedding, blockEmbed_snd_viaEmbedding,
    cycleType_viaEmbedding, cycleType_viaEmbedding]

/-- The cycle type of a standard cycle of length at least two. -/
theorem cycleType_nfCycle_of_two_le {c : ℕ} (hc : 2 ≤ c) :
    (nfCycle c).cycleType = {c} := by
  obtain ⟨m, rfl⟩ : ∃ m, c = m + 1 := ⟨c - 1, by omega⟩
  rw [show nfCycle (m + 1) = topCycle 0 from rfl, topCycle_zero]
  exact cycleType_finRotate_of_le hc

/-- The cycle type of a short standard cycle is empty. -/
theorem cycleType_nfCycle_of_le_one {c : ℕ} (hc : c ≤ 1) :
    (nfCycle c).cycleType = 0 := by
  match c, hc with
  | 0, _ => exact Equiv.Perm.cycleType_one
  | 1, _ =>
      rw [show nfCycle 1 = 1 from Subsingleton.elim _ _]
      exact Equiv.Perm.cycleType_one

/-- **The normal form of a cycle-length list**: the block product
of standard cycles. -/
def nfPerm : (cs : List ℕ) → Equiv.Perm (Fin cs.sum)
  | [] => 1
  | c :: cs => blockEmbed (nfCycle c) (nfPerm cs)

/-- The cycle type of a normal form: the cycle lengths of at least
two. -/
theorem cycleType_nfPerm : ∀ cs : List ℕ,
    (nfPerm cs).cycleType =
      ((cs.filter (fun c => decide (2 ≤ c))) : Multiset ℕ) := by
  intro cs
  induction cs with
  | nil => exact Equiv.Perm.cycleType_one
  | cons c cs ih =>
      refine Eq.trans
        (cycleType_blockEmbed (nfCycle c) (nfPerm cs)) ?_
      rw [ih]
      by_cases hc : 2 ≤ c
      · rw [cycleType_nfCycle_of_two_le hc,
          List.filter_cons_of_pos (by simpa using hc),
          Multiset.singleton_add]
        rfl
      · rw [cycleType_nfCycle_of_le_one (by omega),
          List.filter_cons_of_neg (by simpa using hc), zero_add]

/-- The super character of a normal form is the product of the
super power sums of its cycle lengths. -/
theorem superChar_nfPerm (p q : ℕ) : ∀ cs : List ℕ,
    (∀ c ∈ cs, 1 ≤ c) →
    superChar p q cs.sum (nfPerm cs) =
      (cs.map (fun c => superPS p q c)).prod := by
  intro cs
  induction cs with
  | nil =>
      intro _
      change superChar p q 0 1 = (List.map (fun c => superPS p q c)
        []).prod
      unfold superChar
      rw [permMor_one, sTr_id]
      rw [show Module.finrank ℂ
        (tensorPow SuperVect (stdSuper p q) 0).even = 1 from
        Module.finrank_self ℂ]
      have : Subsingleton
          (tensorPow SuperVect (stdSuper p q) 0).odd :=
        inferInstanceAs (Subsingleton PUnit)
      rw [show Module.finrank ℂ
        (tensorPow SuperVect (stdSuper p q) 0).odd = 0 from
        Module.finrank_eq_zero_of_subsingleton _ _]
      rw [List.map_nil, List.prod_nil]
      norm_num
  | cons c cs ih =>
      intro hpos
      refine Eq.trans
        (superChar_blockEmbed p q (nfCycle c) (nfPerm cs)) ?_
      rw [superChar_nfCycle p q (hpos c List.mem_cons_self),
        ih (fun d hd => hpos d (List.mem_cons_of_mem c hd)),
        List.map_cons, List.prod_cons]

/-- Relabelling along an equality of sizes preserves the super
character. -/
theorem superChar_permCast (p q : ℕ) {m n : ℕ} (h : m = n)
    (σ : Equiv.Perm (Fin m)) :
    superChar p q n (permCast h σ) = superChar p q m σ := by
  subst h
  rw [permCast_rfl]
  rfl

/-! ## The character formula -/

/-- **The super character formula** (super Schur–Weyl, character
side): the trace of a permutation's action on the tensor power of
the standard super object of dimension `(p, q)` is the completed
cycle product of the super power sums. -/
theorem sTr_permMor (p q : ℕ) {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    sTr (permMor (stdSuper p q) n σ) = cycleFun (superPS p q) σ := by
  classical
  set cs : List ℕ := σ.cycleType.toList ++
    List.replicate (n - σ.cycleType.sum) 1 with hcs
  have hpos : ∀ c ∈ cs, 1 ≤ c := by
    intro c hc
    rcases List.mem_append.mp hc with h1 | h1
    · have := Equiv.Perm.two_le_of_mem_cycleType
        (Multiset.mem_toList.mp h1)
      omega
    · rw [List.eq_of_mem_replicate h1]
  have hsumle : σ.cycleType.sum ≤ n := by
    have h1 := Equiv.Perm.sum_cycleType_le σ
    rwa [Fintype.card_fin] at h1
  have hsum : cs.sum = n := by
    rw [hcs, List.sum_append, List.sum_replicate, smul_eq_mul,
      mul_one, Multiset.sum_toList]
    omega
  have hfilter : cs.filter (fun c => decide (2 ≤ c)) =
      σ.cycleType.toList := by
    rw [hcs, List.filter_append]
    have h1 : σ.cycleType.toList.filter (fun c => decide (2 ≤ c)) =
        σ.cycleType.toList :=
      List.filter_eq_self.mpr fun c hc => by
        simpa using Equiv.Perm.two_le_of_mem_cycleType
          (Multiset.mem_toList.mp hc)
    have h2 : (List.replicate (n - σ.cycleType.sum) 1).filter
        (fun c => decide (2 ≤ c)) = [] := by
      refine List.filter_eq_nil_iff.mpr fun a ha => ?_
      rw [List.eq_of_mem_replicate ha]
      decide
    rw [h1, h2, List.append_nil]
  have hct : (permCast hsum (nfPerm cs)).cycleType = σ.cycleType
      := by
    rw [cycleType_permCast, cycleType_nfPerm, hfilter,
      Multiset.coe_toList]
  have hconj : IsConj σ (permCast hsum (nfPerm cs)) :=
    Equiv.Perm.isConj_iff_cycleType_eq.mpr hct.symm
  obtain ⟨u, hu⟩ := isConj_iff.mp hconj
  have hchar : sTr (permMor (stdSuper p q) n σ) =
      (cs.map (fun c => superPS p q c)).prod := by
    calc sTr (permMor (stdSuper p q) n σ)
        = superChar p q n (u * σ * u⁻¹) :=
          (superChar_conj p q u σ).symm
      _ = superChar p q n (permCast hsum (nfPerm cs)) := by rw [hu]
      _ = superChar p q cs.sum (nfPerm cs) :=
          superChar_permCast p q hsum _
      _ = (cs.map (fun c => superPS p q c)).prod :=
          superChar_nfPerm p q cs hpos
  rw [hchar, hcs, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate, cycleFun]
  rw [show ((σ.cycleType.toList.map fun c => superPS p q c).prod) =
      (σ.cycleType.map (superPS p q)).prod from by
    conv_rhs => rw [← Multiset.coe_toList σ.cycleType]
    rfl]

/-! ## Nonvanishing of the idempotent action -/

/-- **The idempotent trace formula**: the super trace of a package
idempotent's action on the tensor power of the standard super
object is the dimension times the Schur specialisation at the super
power sums. -/
theorem sTr_permAlg_e (P : SchurPackage.{0}) (p q : ℕ)
    (lam : YoungDiagram) :
    sTr (permAlg (stdSuper p q) lam.card (P.e lam)) =
      (P.dim lam : ℂ) * diagramSchur lam (superPS p q) := by
  classical
  set L : SymGroupAlgebra lam.card →ₗ[ℂ] ℂ :=
    (sTrL (tensorPow SuperVect (stdSuper p q) lam.card)).comp
      (permAlg (stdSuper p q) lam.card).toLinearMap with hL
  have hLof : ∀ π : Equiv.Perm (Fin lam.card),
      L (MonoidAlgebra.of ℂ (Equiv.Perm (Fin lam.card)) π) =
        cycleFun (superPS p q) π := by
    intro π
    change sTrL _ (permAlg (stdSuper p q) lam.card
      (MonoidAlgebra.of ℂ (Equiv.Perm (Fin lam.card)) π)) = _
    rw [show MonoidAlgebra.of ℂ (Equiv.Perm (Fin lam.card)) π =
      MonoidAlgebra.single π (1 : ℂ) from rfl, permAlg_single,
      sTrL_apply, sTr_permMor]
  have hgoal : sTr (permAlg (stdSuper p q) lam.card (P.e lam)) =
      L (P.e lam) := rfl
  rw [hgoal, SchurPackage.e_def, charIdempotent, map_smul, map_sum]
  rw [Finset.sum_congr rfl fun π _ => show
      L (P.char lam π • MonoidAlgebra.of ℂ
        (Equiv.Perm (Fin lam.card)) π) =
      P.char lam π * cycleFun (superPS p q) π from by
    rw [map_smul, hLof π, smul_eq_mul]]
  rw [smul_eq_mul, show ((P.dim lam : ℂ) /
      (lam.card.factorial : ℂ)) *
      (∑ π : Equiv.Perm (Fin lam.card),
        P.char lam π * cycleFun (superPS p q) π) =
    (P.dim lam : ℂ) * (((lam.card.factorial : ℂ))⁻¹ *
      ∑ π : Equiv.Perm (Fin lam.card),
        P.char lam π * cycleFun (superPS p q) π) from by ring]
  congr 1
  exact P.frobenius lam (superPS p q)

/-- **Schur nonvanishing on the standard super vector space**
(Deligne 1.9, nonvanishing direction): a diagram avoiding the cell
`(p, q)` does not kill the standard super object of dimension
`(p, q)` — the central idempotent of its block acts nonzero on the
tensor power. -/
theorem not_schurKilled_stdSuper (P : SchurPackage.{0}) {p q : ℕ}
    {lam : YoungDiagram} (h : (p, q) ∉ lam) :
    ¬ SchurKilled P (stdSuper p q) lam := by
  intro h0
  have hval := sTr_permAlg_e P p q lam
  have h0' : permAlg (stdSuper p q) lam.card (P.e lam) = 0 := h0
  rw [h0'] at hval
  obtain ⟨m, hm, hs⟩ := diagramSchur_superPS_pos lam h
  rw [hs] at hval
  have hzero : sTr (0 : tensorPow SuperVect (stdSuper p q) lam.card
      ⟶ tensorPow SuperVect (stdSuper p q) lam.card) = 0 := by
    rw [sTr, SuperVect.zero_evenMap, SuperVect.zero_oddMap,
      map_zero, map_zero, add_zero]
  have hd := P.dim_pos lam
  have hne : ((P.dim lam : ℂ)) * (m : ℂ) ≠ 0 := by
    refine mul_ne_zero ?_ ?_
    · exact Nat.cast_ne_zero.mpr (by omega)
    · exact Nat.cast_ne_zero.mpr (by omega)
  exact hne (hzero.symm.trans hval).symm

/-! ## The graded signed permutation representation

The same action, packaged as a genuine representation of the
symmetric group on the total space of the tensor power — the free
module on colourings carrying the Koszul signs, in its categorical
presentation. -/

/-- **The graded signed permutation representation**: the symmetric
group acting on the total space of the tensor power of the standard
super object, by the categorical action with its Koszul signs. -/
def gradedSignRep (p q n : ℕ) :
    Representation ℂ (Equiv.Perm (Fin n))
      (Tot (tensorPow SuperVect (stdSuper p q) n)) where
  toFun σ := tot (permMor (stdSuper p q) n σ)
  map_one' := by rw [permMor_one, tot_id]; rfl
  map_mul' σ τ := by
    change tot (permMor (stdSuper p q) n (σ * τ)) = _
    rw [permMor_mul, tot_comp]
    rfl

/-- The representation of a permutation is the total map of its
categorical action. -/
theorem gradedSignRep_apply (p q n : ℕ) (σ : Equiv.Perm (Fin n)) :
    gradedSignRep p q n σ = tot (permMor (stdSuper p q) n σ) := rfl

/-- The algebra action of the representation is the total map of
the categorical algebra action. -/
theorem gradedSignRep_asAlgebraHom (p q n : ℕ)
    (z : SymGroupAlgebra n) :
    (gradedSignRep p q n).asAlgebraHom z =
      tot (permAlg (stdSuper p q) n z) := by
  induction z using MonoidAlgebra.induction_on with
  | of σ =>
      change (gradedSignRep p q n).asAlgebraHom
          (MonoidAlgebra.single σ (1 : ℂ)) =
        tot (permAlg (stdSuper p q) n
          (MonoidAlgebra.single σ (1 : ℂ)))
      rw [Representation.asAlgebraHom_single, one_smul,
        gradedSignRep_apply]
      exact congrArg tot (permAlg_single _ _ σ).symm
  | add a b ha hb =>
      rw [map_add, map_add, ha, hb]
      exact (tot_add (permAlg (stdSuper p q) n a)
        (permAlg (stdSuper p q) n b)).symm
  | smul r a ha =>
      rw [map_smul, map_smul, ha]
      exact (tot_smul r (permAlg (stdSuper p q) n a)).symm

end

end RS
