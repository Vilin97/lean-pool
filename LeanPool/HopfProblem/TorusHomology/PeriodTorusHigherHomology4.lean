/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.HomologyTheory.SphereHomology2
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.HomologyTheory.SphereHomology2

/-!
# Hopf problem: torus homology · period torus higher homology 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/


open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

@[instance_reducible]
private def PeriodTorusHigherHomology.integerLinearMapModule {A B : Type*} [AddCommGroup A]
    [AddCommGroup B] [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A →ₗ[ℤ] B) :=
  @LinearMap.module ℤ ℤ ℤ A B _ _ _ _ modA modB (RingHom.id ℤ) _ modB
    (@smulCommClass_self ℤ B _ modB.toMulAction)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule in
@[instance_reducible]
private def
    PeriodTorusHigherHomology.integerTensorModule {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [modA : Module ℤ A] [modB : Module ℤ B] : Module ℤ (A ⊗[ℤ] B) :=
  @TensorProduct.instModule ℤ _ A B _ _ modA modB

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.integerBilinearRightApply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) : A →ₗ[ℤ] C
    where
  toFun a := F a b
  map_add' a a' := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_add a a')
  map_smul' r a := congrArg (fun l : B →ₗ[ℤ] C => l b) (F.map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.integerBilinearRightApply_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearRightApply F b a = F a b :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.integerBilinearFlip {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) : B →ₗ[ℤ] A →ₗ[ℤ] C
    where
  toFun := integerBilinearRightApply F
  map_add' b
    b' := by
    apply LinearMap.ext
    intro a
    exact (F a).map_add b b'
  map_smul' r
    b := by
    apply LinearMap.ext
    intro a
    exact (F a).map_smul r b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.integerBilinearFlip_apply {A B C : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (b : B) (a : A) : integerBilinearFlip F b a = F a b :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.chainBilinearLift (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : FirstHurewicz.SingularSimplex X p → FirstHurewicz.SingularSimplex Y q → M) :
    FirstHurewicz.Chains X p →ₗ[ℤ] FirstHurewicz.Chains Y q →ₗ[ℤ] M :=
  FirstHurewicz.chainLift X p fun σ => FirstHurewicz.chainLift Y q (f σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.chainBilinearLift_simplex_left (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : FirstHurewicz.SingularSimplex X p → FirstHurewicz.SingularSimplex Y q → M)
    (σ : FirstHurewicz.SingularSimplex X p) :
    chainBilinearLift X Y p q f (FirstHurewicz.simplexChain X p σ) =
      FirstHurewicz.chainLift Y q (f σ) :=
  FirstHurewicz.chainLift_simplex X p _ σ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.chainBilinearLift_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    (f : FirstHurewicz.SingularSimplex X p → FirstHurewicz.SingularSimplex Y q → M)
    (σ : FirstHurewicz.SingularSimplex X p) (τ : FirstHurewicz.SingularSimplex Y q) :
    chainBilinearLift X Y p q f (FirstHurewicz.simplexChain X p σ)
        (FirstHurewicz.simplexChain Y q τ) =
      f σ τ := by rw [chainBilinearLift_simplex_left, FirstHurewicz.chainLift_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.chainBilinearMap_ext (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (p q : ℕ) {M : Type} [AddCommGroup M] [modM : Module ℤ M]
    {F G : FirstHurewicz.Chains X p →ₗ[ℤ] FirstHurewicz.Chains Y q →ₗ[ℤ] M}
    (h :
      ∀ σ τ,
        F (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ) =
          G (FirstHurewicz.simplexChain X p σ) (FirstHurewicz.simplexChain Y q τ)) :
    F = G := by
  apply FirstHurewicz.chainMap_ext X p
  intro σ
  apply FirstHurewicz.chainMap_ext Y q
  intro τ
  exact h σ τ

private def PeriodTorusHigherHomology.zeroSimplexValue {X : Type} [TopologicalSpace X]
    (σ : FirstHurewicz.SingularSimplex X 0) : X :=
  σ (stdSimplex.vertex (S := ℝ) (0 : Fin 1))

@[simp]
private theorem PeriodTorusHigherHomology.zeroSimplexValue_comp {X X' : Type} [TopologicalSpace X]
    [TopologicalSpace X'] (f : C(X, X')) (σ : FirstHurewicz.SingularSimplex X 0) :
    zeroSimplexValue (f.comp σ) = f (zeroSimplexValue σ) :=
  rfl

private def PeriodTorusHigherHomology.crossInsertLeft {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (x : X) : C(Y, X × Y) :=
  ⟨fun y => (x, y), continuous_const.prodMk continuous_id⟩

private def PeriodTorusHigherHomology.crossInsertRight {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (y : Y) : C(X, X × Y) :=
  ⟨fun x => (x, y), continuous_id.prodMk continuous_const⟩

private theorem
    PeriodTorusHigherHomology.crossInsertLeft_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (x : X) : (f.prodMap g).comp (crossInsertLeft x) = (crossInsertLeft (f x)).comp g :=
  rfl

private theorem PeriodTorusHigherHomology.inducedChain_crossInsertLeft {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (x : X) (n : ℕ) (c : FirstHurewicz.Chains Y n) :
    FirstHurewicz.inducedChain (f.prodMap g) n
        (FirstHurewicz.inducedChain (crossInsertLeft x) n c) =
      FirstHurewicz.inducedChain (crossInsertLeft (f x)) n (FirstHurewicz.inducedChain g n c) := by
  have h :=
    congrArg (fun h : C(Y, X' × Y') => FirstHurewicz.inducedChain h n c)
      (crossInsertLeft_natural f g x)
  simpa only [FirstHurewicz.inducedChain_comp, LinearMap.comp_apply] using h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductZeroLeft (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.Chains X 0 →ₗ[ℤ]
      FirstHurewicz.Chains Y n →ₗ[ℤ] FirstHurewicz.Chains (X × Y) n :=
  chainBilinearLift X Y 0 n fun σ τ =>
    FirstHurewicz.simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductZeroRight (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.Chains X n →ₗ[ℤ]
      FirstHurewicz.Chains Y 0 →ₗ[ℤ] FirstHurewicz.Chains (X × Y) n :=
  chainBilinearLift X Y n 0 fun σ τ =>
    FirstHurewicz.simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductZeroLeft_simplex_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X 0) :
    crossProductZeroLeft X Y n (FirstHurewicz.simplexChain X 0 σ) =
      FirstHurewicz.inducedChain (crossInsertLeft (Y := Y) (zeroSimplexValue σ)) n := by
  apply FirstHurewicz.chainMap_ext Y n
  intro τ
  rw [crossProductZeroLeft, chainBilinearLift_simplex, FirstHurewicz.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductZeroLeft_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X 0)
    (τ : FirstHurewicz.SingularSimplex Y n) :
    crossProductZeroLeft X Y n (FirstHurewicz.simplexChain X 0 σ)
        (FirstHurewicz.simplexChain Y n τ) =
      FirstHurewicz.simplexChain (X × Y) n ((crossInsertLeft (zeroSimplexValue σ)).comp τ) := by
  rw [crossProductZeroLeft_simplex_left, FirstHurewicz.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductZeroRight_simplex_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (c : FirstHurewicz.Chains X n)
    (τ : FirstHurewicz.SingularSimplex Y 0) :
    crossProductZeroRight X Y n c (FirstHurewicz.simplexChain Y 0 τ) =
      FirstHurewicz.inducedChain (crossInsertRight (zeroSimplexValue τ)) n c := by
  have h :
    integerBilinearRightApply (crossProductZeroRight X Y n) (FirstHurewicz.simplexChain Y 0 τ) =
      FirstHurewicz.inducedChain (crossInsertRight (zeroSimplexValue τ)) n := by
    apply FirstHurewicz.chainMap_ext X n
    intro σ
    simp only [integerBilinearRightApply_apply, crossProductZeroRight, chainBilinearLift_simplex,
      FirstHurewicz.inducedChain_simplex]
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductZeroRight_simplex {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X n)
    (τ : FirstHurewicz.SingularSimplex Y 0) :
    crossProductZeroRight X Y n (FirstHurewicz.simplexChain X n σ)
        (FirstHurewicz.simplexChain Y 0 τ) =
      FirstHurewicz.simplexChain (X × Y) n ((crossInsertRight (zeroSimplexValue τ)).comp σ) := by
  rw [crossProductZeroRight_simplex_right, FirstHurewicz.inducedChain_simplex]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductZeroLeft_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : FirstHurewicz.Chains X 0)
    (b : FirstHurewicz.Chains Y n) :
    FirstHurewicz.inducedChain (f.prodMap g) n (crossProductZeroLeft X Y n a b) =
      crossProductZeroLeft X' Y' n (FirstHurewicz.inducedChain f 0 a)
        (FirstHurewicz.inducedChain g n b) := by
  have h :
    (FirstHurewicz.inducedChain (f.prodMap g) n).comp
        (integerBilinearRightApply (crossProductZeroLeft X Y n) b) =
      (integerBilinearRightApply (crossProductZeroLeft X' Y' n)
            (FirstHurewicz.inducedChain g n b)).comp
        (FirstHurewicz.inducedChain f 0) := by
    apply FirstHurewicz.chainMap_ext X 0
    intro σ
    simp only [LinearMap.comp_apply, integerBilinearRightApply_apply,
      FirstHurewicz.inducedChain_simplex, crossProductZeroLeft_simplex_left,
      zeroSimplexValue_comp]
    exact inducedChain_crossInsertLeft f g (zeroSimplexValue σ) n b
  exact LinearMap.congr_fun h a

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.integerBilinearPostcompose {A B C D : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B] [Module ℤ C]
    [Module ℤ D] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) : A →ₗ[ℤ] B →ₗ[ℤ] D
    where
  toFun a := g.comp (F a)
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_add a a')).trans
        (g.map_add (F a b) (F a' b))
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    exact (congrArg (fun l : B →ₗ[ℤ] C => g (l b)) (F.map_smul r a)).trans (g.map_smul r (F a b))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.integerBilinearPostcompose_apply {A B C D : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup D] [Module ℤ A] [Module ℤ B]
    [Module ℤ C] [Module ℤ D] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (g : C →ₗ[ℤ] D) (a : A) (b : B) :
    integerBilinearPostcompose F g a b = g (F a b) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def
    PeriodTorusHigherHomology.integerBilinearPrecompose {A B C A' B' : Type*} [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B'] [Module ℤ A]
    [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C) (f : A' →ₗ[ℤ] A)
    (g : B' →ₗ[ℤ] B) : A' →ₗ[ℤ] B' →ₗ[ℤ] C
    where
  toFun a := (F (f a)).comp g
  map_add' a
    a' := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun x => F x (g b)) (f.map_add a a')).trans
        (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_add (f a) (f a')))
  map_smul' r
    a := by
    apply LinearMap.ext
    intro b
    exact
      (congrArg (fun x => F x (g b)) (f.map_smul r a)).trans
        (congrArg (fun l : B →ₗ[ℤ] C => l (g b)) (F.map_smul r (f a)))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.integerBilinearPrecompose_apply {A B C A' B' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [AddCommGroup A'] [AddCommGroup B']
    [Module ℤ A] [Module ℤ B] [Module ℤ C] [Module ℤ A'] [Module ℤ B'] (F : A →ₗ[ℤ] B →ₗ[ℤ] C)
    (f : A' →ₗ[ℤ] A) (g : B' →ₗ[ℤ] B) (a : A') (b : B') :
    integerBilinearPrecompose F f g a b = F (f a) (g b) :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.integerFormalBilinearMap_ext (V W : Type*) (p q : ℕ) {M : Type*}
    [AddCommGroup M] [Module ℤ M]
    {F G :
      SingularMayerVietoris.FormalChains V p →ₗ[ℤ] SingularMayerVietoris.FormalChains W q →ₗ[ℤ] M}
    (h :
      ∀ v w,
        F (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w) =
          G (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)) :
    F = G := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply SingularMayerVietoris.formalChains_ext
  intro w
  exact h v w

private theorem PeriodTorusHigherHomology.formalChains_bilinear_ext {V W M : Type*} {n m : ℕ}
    [AddCommGroup M] [Module ℤ M]
    {f g :
      SingularMayerVietoris.FormalChains V n →ₗ[ℤ] SingularMayerVietoris.FormalChains W m →ₗ[ℤ] M}
    (h :
      ∀ v w,
        f (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w) =
          g (SingularMayerVietoris.formalSimplex v) (SingularMayerVietoris.formalSimplex w)) :
    f = g := by
  apply SingularMayerVietoris.formalChains_ext
  intro v
  apply SingularMayerVietoris.formalChains_ext
  exact h v

private def PeriodTorusHigherHomology.formalBilinearLift {V W M : Type*} {n m : ℕ} [AddCommGroup M]
    [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) :
    SingularMayerVietoris.FormalChains V n →ₗ[ℤ] SingularMayerVietoris.FormalChains W m →ₗ[ℤ] M :=
  SingularMayerVietoris.formalLift fun v => SingularMayerVietoris.formalLift (f v)

@[simp]
private theorem PeriodTorusHigherHomology.formalBilinearLift_simplex {V W M : Type*} {n m : ℕ}
    [AddCommGroup M] [Module ℤ M] (f : (Fin n → V) → (Fin m → W) → M) (v : Fin n → V)
    (w : Fin m → W) :
    formalBilinearLift f (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      f v w := by simp [formalBilinearLift]

private def PeriodTorusHigherHomology.formalPointCrossProduct {V W : Type*} (q : ℕ) :
    SingularMayerVietoris.FormalChains V 1 →ₗ[ℤ]
      SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
        SingularMayerVietoris.FormalChains (V × W) (q + 1) :=
  SingularMayerVietoris.formalLift fun v =>
    SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1)

@[simp]
private theorem PeriodTorusHigherHomology.formalPointCrossProduct_simplex_left {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v) d =
      SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) d

private theorem PeriodTorusHigherHomology.formalPointCrossProduct_simplex {V W : Type*} (q : ℕ)
    (v : Fin 1 → V) (w : Fin (q + 1) → W) :
    formalPointCrossProduct q (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalSimplex (fun i => (v 0, w i)) := by
  rw [formalPointCrossProduct_simplex_left, SingularMayerVietoris.formalMap_simplex]
  rfl

@[simp]
private theorem PeriodTorusHigherHomology.formalPointCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 1) (w : Fin 1 → W) :
    formalPointCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 c := by
  have h :
    (formalPointCrossProduct (V := V) 0).flip (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 1 := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    simp only [LinearMap.flip_apply, formalPointCrossProduct_simplex,
      SingularMayerVietoris.formalMap_simplex]
    congr 1
    funext i
    rw [Fin.eq_zero i]
    rfl
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.formalBoundary_pointCrossProduct {V W : Type*} (q : ℕ)
    (c : SingularMayerVietoris.FormalChains V 1)
    (d : SingularMayerVietoris.FormalChains W (q + 2)) :
    SingularMayerVietoris.formalBoundary (q + 1) (formalPointCrossProduct (q + 1) c d) =
      formalPointCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) (q + 1)).compr₂
        (SingularMayerVietoris.formalBoundary (q + 1)) =
      (formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalBoundary (q + 1)) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply,
      formalPointCrossProduct_simplex_left]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (v 0, z)) (q + 1)
          (SingularMayerVietoris.formalSimplex w)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem
    PeriodTorusHigherHomology.formalMap_pointCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') (q : ℕ) (c : SingularMayerVietoris.FormalChains V 1)
    (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    SingularMayerVietoris.formalMap (Prod.map f g) (q + 1) (formalPointCrossProduct q c d) =
      formalPointCrossProduct q (SingularMayerVietoris.formalMap f 1 c)
        (SingularMayerVietoris.formalMap g (q + 1) d) := by
  have h :
    (formalPointCrossProduct (V := V) (W := W) q).compr₂
        (SingularMayerVietoris.formalMap (Prod.map f g) (q + 1)) =
      ((formalPointCrossProduct q).compl₂ (SingularMayerVietoris.formalMap g (q + 1))).comp
        (SingularMayerVietoris.formalMap f 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
      formalPointCrossProduct_simplex, SingularMayerVietoris.formalMap_simplex]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

/-- The formal chain-level cross product with an oriented edge. -/
public
def PeriodTorusHigherHomology.formalEdgeCrossProduct {V W : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 2 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × W) (q + 2)
  | 0 =>
    (SingularMayerVietoris.formalLift fun w : Fin 1 → W =>
        SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2).flip
  | q + 1 =>
    formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

@[simp]
private theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (w : Fin 1 → W) :
    formalEdgeCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 2 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

@[simp]
private theorem PeriodTorusHigherHomology.formalEdgeCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (w : Fin (q + 2) → W) :
    formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 2)
        (formalPointCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) -
          formalEdgeCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

private theorem PeriodTorusHigherHomology.formalBoundary_edgeCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 2) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 1 (formalEdgeCrossProduct 0 c d) =
      formalPointCrossProduct 0 (SingularMayerVietoris.formalBoundary 1 c) d := by
  have h :
    (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂ (SingularMayerVietoris.formalBoundary 1) =
      (formalPointCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 1) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalEdgeCrossProduct_zero_simplex_right, formalPointCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 1
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem PeriodTorusHigherHomology.formalBoundary_edgeCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 2) (formalEdgeCrossProduct (q + 1) c d) =
        formalPointCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 1 c) d -
          formalEdgeCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 2) =
        (formalPointCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 1) -
          (formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 2
            (formalEdgeCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 1
            (formalPointCrossProduct 1
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              formalEdgeCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, formalBoundary_pointCrossProduct, formalBoundary_edgeCrossProduct_zero,
          sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 3)) =
        (formalPointCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 1) -
          (formalEdgeCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalEdgeCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 2)
            (formalPointCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) -
              formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_sub, formalBoundary_pointCrossProduct, ih,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, sub_zero, sub_self]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem
    PeriodTorusHigherHomology.formalMap_edgeCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 2)
      (d : SingularMayerVietoris.FormalChains W (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 2) (formalEdgeCrossProduct q c d) =
        formalEdgeCrossProduct q (SingularMayerVietoris.formalMap f 2 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 2) =
        ((formalEdgeCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        formalEdgeCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalEdgeCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 3)) =
        ((formalEdgeCrossProduct (q + 1)).compl₂ (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 2) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, formalEdgeCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_sub, formalMap_pointCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

@[simp]
private theorem
    PeriodTorusHigherHomology.affineSimplex_constant {n p : ℕ} (a : FirstHurewicz.Simplex p) :
    SingularMayerVietoris.affineSimplex (fun _ : Fin (n + 1) => a) =
      ContinuousMap.const (FirstHurewicz.Simplex n) a := by
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  change (∑ i, t i • (a : Fin (p + 1) → ℝ)) = (a : Fin (p + 1) → ℝ)
  rw [← Finset.sum_smul, stdSimplex.sum_eq_one t, one_smul]

private def PeriodTorusHigherHomology.productAffineSimplex {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :=
  (SingularMayerVietoris.affineSimplex (fun i => (v i).1)).prodMk
    (SingularMayerVietoris.affineSimplex (fun i => (v i).2))

@[simp]
private theorem PeriodTorusHigherHomology.productAffineSimplex_vertex {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) (i : Fin (n + 1)) :
    productAffineSimplex v (SingularMayerVietoris.stdVertices n i) = v i := by
  apply Prod.ext <;> simp [productAffineSimplex, SingularMayerVietoris.stdVertices]

private theorem PeriodTorusHigherHomology.productAffineSimplex_face {n p q : ℕ}
    (v : Fin (n + 2) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) (i : Fin (n + 2)) :
    (productAffineSimplex v).comp (FirstHurewicz.simplexFace n i) =
      productAffineSimplex (fun j => v (i.succAbove j)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex p) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).1) i)
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex n, FirstHurewicz.Simplex q) => f t)
        (SingularMayerVietoris.affineSimplex_face (fun j => (v j).2) i)

private theorem PeriodTorusHigherHomology.prodMap_productAffineSimplex {m p q r s : ℕ}
    (v : Fin (p + 1) → FirstHurewicz.Simplex r) (w : Fin (q + 1) → FirstHurewicz.Simplex s)
    (z : Fin (m + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w)).comp
        (productAffineSimplex z) =
      productAffineSimplex
        (fun j =>
          (SingularMayerVietoris.affineSimplex v (z j).1,
            SingularMayerVietoris.affineSimplex w (z j).2)) := by
  apply ContinuousMap.ext
  intro t
  apply Prod.ext
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex r) => f t)
        (SingularMayerVietoris.affineSimplex_comp v (fun j => (z j).1))
  · exact
      congrArg (fun f : C(FirstHurewicz.Simplex m, FirstHurewicz.Simplex s) => f t)
        (SingularMayerVietoris.affineSimplex_comp w (fun j => (z j).2))

private def PeriodTorusHigherHomology.productAffineChainMap (p q n : ℕ) :
    SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
        (n + 1) →ₗ[ℤ]
      FirstHurewicz.Chains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) n :=
  SingularMayerVietoris.formalLift fun v =>
    FirstHurewicz.simplexChain (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) n
      (productAffineSimplex v)

@[simp]
private theorem PeriodTorusHigherHomology.productAffineChainMap_simplex (p q n : ℕ)
    (v : Fin (n + 1) → FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) :
    productAffineChainMap p q n (SingularMayerVietoris.formalSimplex v) =
      FirstHurewicz.simplexChain (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q) n
        (productAffineSimplex v) :=
  SingularMayerVietoris.formalLift_simplex _ _

private theorem PeriodTorusHigherHomology.productAffineChainMap_boundary (p q n : ℕ)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
        (n + 2)) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d (n + 1)
            n).hom
        (productAffineChainMap p q (n + 1) c) =
      productAffineChainMap p q n (SingularMayerVietoris.formalBoundary (n + 1) c) := by
  have h :
    (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d
              (n + 1) n).hom).comp
        (productAffineChainMap p q (n + 1)) =
      (productAffineChainMap p q n).comp (SingularMayerVietoris.formalBoundary (n + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro v
    change
      ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d
              (n + 1) n).hom
          (productAffineChainMap p q (n + 1) (SingularMayerVietoris.formalSimplex v)) =
        _
    rw [productAffineChainMap_simplex, FirstHurewicz.boundary_simplex]
    change
      _ =
        productAffineChainMap p q n
          (SingularMayerVietoris.formalBoundary (n + 1) (SingularMayerVietoris.formalSimplex v))
    rw [SingularMayerVietoris.formalBoundary_simplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_zsmul, productAffineChainMap_simplex, productAffineSimplex_face]
    rfl
  exact LinearMap.congr_fun h c

private theorem PeriodTorusHigherHomology.inducedChain_productAffineChainMap {m p q r s : ℕ}
    (v : Fin (p + 1) → FirstHurewicz.Simplex r) (w : Fin (q + 1) → FirstHurewicz.Simplex s)
    (c :
      SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)
        (m + 1)) :
    FirstHurewicz.inducedChain
        ((SingularMayerVietoris.affineSimplex v).prodMap (SingularMayerVietoris.affineSimplex w))
        m (productAffineChainMap p q m c) =
      productAffineChainMap r s m
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1) c) := by
  have h :
    (FirstHurewicz.inducedChain
            ((SingularMayerVietoris.affineSimplex v).prodMap
              (SingularMayerVietoris.affineSimplex w))
            m).comp
        (productAffineChainMap p q m) =
      (productAffineChainMap r s m).comp
        (SingularMayerVietoris.formalMap
          ((SingularMayerVietoris.affineSimplex v).prodMap
            (SingularMayerVietoris.affineSimplex w))
          (m + 1)) := by
    apply SingularMayerVietoris.formalChains_ext
    intro z
    simp only [LinearMap.comp_apply, productAffineChainMap_simplex,
      FirstHurewicz.inducedChain_simplex, SingularMayerVietoris.formalMap_simplex,
      prodMap_productAffineSimplex]
    rfl
  exact LinearMap.congr_fun h c

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductEdge (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.Chains X 1 →ₗ[ℤ]
      FirstHurewicz.Chains Y n →ₗ[ℤ] FirstHurewicz.Chains (X × Y) (n + 1) :=
  chainBilinearLift X Y 1 n fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) (n + 1)
      (productAffineChainMap 1 n (n + 1)
        (formalEdgeCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductEdge_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X 1)
    (τ : FirstHurewicz.SingularSimplex Y n) :
    crossProductEdge X Y n (FirstHurewicz.simplexChain X 1 σ) (FirstHurewicz.simplexChain Y n τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) (n + 1)
        (productAffineChainMap 1 n (n + 1)
          (formalEdgeCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainBilinearLift_simplex X Y 1 n _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductEdge_natural {X Y X' Y' : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y'] (f : C(X, X')) (g : C(Y, Y'))
    (n : ℕ) (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y n) :
    FirstHurewicz.inducedChain (f.prodMap g) (n + 1) (crossProductEdge X Y n a b) =
      crossProductEdge X' Y' n (FirstHurewicz.inducedChain f 1 a)
        (FirstHurewicz.inducedChain g n b) := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y n)
        (FirstHurewicz.inducedChain (f.prodMap g) (n + 1)) =
      integerBilinearPrecompose (crossProductEdge X' Y' n) (FirstHurewicz.inducedChain f 1)
        (FirstHurewicz.inducedChain g n) := by
    apply chainBilinearMap_ext X Y 1 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductEdge_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.affineSimplex_stdVertices_image {n p : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p) :
    SingularMayerVietoris.affineSimplex v ∘ SingularMayerVietoris.stdVertices n = v := by
  funext i
  exact SingularMayerVietoris.affineSimplex_vertex v i

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.productAffineSimplex_point_left {n p q : ℕ}
    (a : FirstHurewicz.Simplex p) (v : Fin (n + 1) → FirstHurewicz.Simplex q) :
    productAffineSimplex (fun i => (a, v i)) =
      (crossInsertLeft a).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.productAffineSimplex_point_right {n p q : ℕ}
    (v : Fin (n + 1) → FirstHurewicz.Simplex p) (b : FirstHurewicz.Simplex q) :
    productAffineSimplex (fun i => (v i, b)) =
      (crossInsertRight b).comp (SingularMayerVietoris.affineSimplex v) := by
  rw [productAffineSimplex, affineSimplex_constant]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductZeroLeft_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 1)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) (n + 1)) :
    crossProductZeroLeft (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 0 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q n (formalPointCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductZeroLeft (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 0) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalPointCrossProduct n) (productAffineChainMap p q n) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductZeroLeft_simplex]
    have hv : zeroSimplexValue (SingularMayerVietoris.affineSimplex v) = v 0 :=
      SingularMayerVietoris.affineSimplex_vertex v 0
    rw [hv]
    calc
      _ =
          productAffineChainMap p q n
            (SingularMayerVietoris.formalSimplex (fun i => (v 0, w i))) := by
        rw [productAffineChainMap_simplex, productAffineSimplex_point_left]
      _ = _ := congrArg (productAffineChainMap p q n) (formalPointCrossProduct_simplex n v w).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) (n + 1)) :
    crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 1 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q (n + 1) (formalEdgeCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 1) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalEdgeCrossProduct n) (productAffineChainMap p q (n + 1)) :=
    by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductEdge_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q (n + 1)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 2)
            (formalEdgeCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_edgeCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

private def PeriodTorusHigherHomology.formalTriangleCrossProduct {V W : Type*} :
    (q : ℕ) →
      SingularMayerVietoris.FormalChains V 3 →ₗ[ℤ]
        SingularMayerVietoris.FormalChains W (q + 1) →ₗ[ℤ]
          SingularMayerVietoris.FormalChains (V × W) (q + 3)
  | 0 =>
    (SingularMayerVietoris.formalLift fun w : Fin 1 → W =>
        SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3).flip
  | q + 1 =>
    formalBilinearLift fun v w =>
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w)))

@[simp]
private theorem
    PeriodTorusHigherHomology.formalTriangleCrossProduct_zero_simplex_right {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (w : Fin 1 → W) :
    formalTriangleCrossProduct 0 c (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalMap (fun v => (v, w 0)) 3 c := by
  exact LinearMap.congr_fun (SingularMayerVietoris.formalLift_simplex _ _) c

@[simp]
private theorem
    PeriodTorusHigherHomology.formalTriangleCrossProduct_simplex_succ {V W : Type*} (q : ℕ)
    (v : Fin 3 → V) (w : Fin (q + 2) → W) :
    formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
        (SingularMayerVietoris.formalSimplex w) =
      SingularMayerVietoris.formalCone (v 0, w 0) (q + 3)
        (formalEdgeCrossProduct (q + 1)
            (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
            (SingularMayerVietoris.formalSimplex w) +
          formalTriangleCrossProduct q (SingularMayerVietoris.formalSimplex v)
            (SingularMayerVietoris.formalBoundary (q + 1)
              (SingularMayerVietoris.formalSimplex w))) :=
  formalBilinearLift_simplex _ _ _

private theorem PeriodTorusHigherHomology.formalBoundary_triangleCrossProduct_zero {V W : Type*}
    (c : SingularMayerVietoris.FormalChains V 3) (d : SingularMayerVietoris.FormalChains W 1) :
    SingularMayerVietoris.formalBoundary 2 (formalTriangleCrossProduct 0 c d) =
      formalEdgeCrossProduct 0 (SingularMayerVietoris.formalBoundary 2 c) d := by
  have h :
    (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
        (SingularMayerVietoris.formalBoundary 2) =
      (formalEdgeCrossProduct 0).comp (SingularMayerVietoris.formalBoundary 2) := by
    apply formalChains_bilinear_ext
    intro v w
    simp only [LinearMap.compr₂_apply, LinearMap.comp_apply,
      formalTriangleCrossProduct_zero_simplex_right, formalEdgeCrossProduct_zero_simplex_right]
    exact
      (SingularMayerVietoris.formalMap_boundary (fun z => (z, w 0)) 2
          (SingularMayerVietoris.formalSimplex v)).symm
  exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem PeriodTorusHigherHomology.formalBoundary_triangleCrossProduct {V W : Type*} :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 3)
      (d : SingularMayerVietoris.FormalChains W (q + 2)),
      SingularMayerVietoris.formalBoundary (q + 3) (formalTriangleCrossProduct (q + 1) c d) =
        formalEdgeCrossProduct (q + 1) (SingularMayerVietoris.formalBoundary 2 c) d +
          formalTriangleCrossProduct q c (SingularMayerVietoris.formalBoundary (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) 1).compr₂
          (SingularMayerVietoris.formalBoundary 3) =
        (formalEdgeCrossProduct 1).comp (SingularMayerVietoris.formalBoundary 2) +
          (formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalBoundary 1) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary 3
            (formalTriangleCrossProduct 1 (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary 2
            (formalEdgeCrossProduct 1
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              formalTriangleCrossProduct 0 (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary 1
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, formalBoundary_edgeCrossProduct,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
          formalBoundary_triangleCrossProduct_zero, neg_add_cancel]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) (q + 2)).compr₂
          (SingularMayerVietoris.formalBoundary (q + 4)) =
        (formalEdgeCrossProduct (q + 2)).comp (SingularMayerVietoris.formalBoundary 2) +
          (formalTriangleCrossProduct (q + 1)).compl₂
            (SingularMayerVietoris.formalBoundary (q + 2)) := by
      apply formalChains_bilinear_ext
      intro v w
      change
        SingularMayerVietoris.formalBoundary (q + 4)
            (formalTriangleCrossProduct (q + 2) (SingularMayerVietoris.formalSimplex v)
              (SingularMayerVietoris.formalSimplex w)) =
          _
      rw [formalTriangleCrossProduct_simplex_succ, SingularMayerVietoris.formalBoundary_cone]
      have hz :
        SingularMayerVietoris.formalBoundary (q + 3)
            (formalEdgeCrossProduct (q + 2)
                (SingularMayerVietoris.formalBoundary 2 (SingularMayerVietoris.formalSimplex v))
                (SingularMayerVietoris.formalSimplex w) +
              formalTriangleCrossProduct (q + 1) (SingularMayerVietoris.formalSimplex v)
                (SingularMayerVietoris.formalBoundary (q + 2)
                  (SingularMayerVietoris.formalSimplex w))) =
          0 := by
        rw [map_add, formalBoundary_edgeCrossProduct,
          SingularMayerVietoris.formalBoundary_boundary, map_zero, LinearMap.zero_apply, zero_sub,
          ih, SingularMayerVietoris.formalBoundary_boundary, map_zero, add_zero, neg_add_cancel]
      rw [hz, map_zero, sub_zero]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

private theorem
    PeriodTorusHigherHomology.formalMap_triangleCrossProduct {V W V' W' : Type*} (f : V → V')
    (g : W → W') :
    ∀ (q : ℕ) (c : SingularMayerVietoris.FormalChains V 3)
      (d : SingularMayerVietoris.FormalChains W (q + 1)),
      SingularMayerVietoris.formalMap (Prod.map f g) (q + 3) (formalTriangleCrossProduct q c d) =
        formalTriangleCrossProduct q (SingularMayerVietoris.formalMap f 3 c)
          (SingularMayerVietoris.formalMap g (q + 1) d) := by
  intro q
  induction q with
  | zero =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) 0).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) 3) =
        ((formalTriangleCrossProduct 0).compl₂ (SingularMayerVietoris.formalMap g 1)).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        formalTriangleCrossProduct_zero_simplex_right, SingularMayerVietoris.formalMap_simplex]
      rfl
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d
  | succ q ih =>
    intro c d
    have h :
      (formalTriangleCrossProduct (V := V) (W := W) (q + 1)).compr₂
          (SingularMayerVietoris.formalMap (Prod.map f g) (q + 4)) =
        ((formalTriangleCrossProduct (q + 1)).compl₂
              (SingularMayerVietoris.formalMap g (q + 2))).comp
          (SingularMayerVietoris.formalMap f 3) := by
      apply formalChains_bilinear_ext
      intro v w
      simp only [LinearMap.compr₂_apply, LinearMap.compl₂_apply, LinearMap.comp_apply,
        SingularMayerVietoris.formalMap_simplex, formalTriangleCrossProduct_simplex_succ]
      rw [SingularMayerVietoris.formalMap_cone]
      congr 1
      rw [map_add, formalMap_edgeCrossProduct, ih, SingularMayerVietoris.formalMap_boundary,
        SingularMayerVietoris.formalMap_boundary, SingularMayerVietoris.formalMap_simplex,
        SingularMayerVietoris.formalMap_simplex]
    exact LinearMap.congr_fun (LinearMap.congr_fun h c) d

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductTriangle (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    FirstHurewicz.Chains X 2 →ₗ[ℤ]
      FirstHurewicz.Chains Y n →ₗ[ℤ] FirstHurewicz.Chains (X × Y) (n + 2) :=
  chainBilinearLift X Y 2 n fun σ τ =>
    FirstHurewicz.inducedChain (σ.prodMap τ) (n + 2)
      (productAffineChainMap 2 n (n + 2)
        (formalTriangleCrossProduct n
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
          (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n))))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.crossProductTriangle_simplex (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (σ : FirstHurewicz.SingularSimplex X 2)
    (τ : FirstHurewicz.SingularSimplex Y n) :
    crossProductTriangle X Y n (FirstHurewicz.simplexChain X 2 σ)
        (FirstHurewicz.simplexChain Y n τ) =
      FirstHurewicz.inducedChain (σ.prodMap τ) (n + 2)
        (productAffineChainMap 2 n (n + 2)
          (formalTriangleCrossProduct n
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
            (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) :=
  chainBilinearLift_simplex X Y 2 n _ σ τ

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_natural {X Y X' Y' : Type}
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace X'] [TopologicalSpace Y']
    (f : C(X, X')) (g : C(Y, Y')) (n : ℕ) (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y n) :
    FirstHurewicz.inducedChain (f.prodMap g) (n + 2) (crossProductTriangle X Y n a b) =
      crossProductTriangle X' Y' n (FirstHurewicz.inducedChain f 2 a)
        (FirstHurewicz.inducedChain g n b) := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y n)
        (FirstHurewicz.inducedChain (f.prodMap g) (n + 2)) =
      integerBilinearPrecompose (crossProductTriangle X' Y' n) (FirstHurewicz.inducedChain f 2)
        (FirstHurewicz.inducedChain g n) := by
    apply chainBilinearMap_ext X Y 2 n
    intro σ τ
    simp only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      FirstHurewicz.inducedChain_simplex, crossProductTriangle_simplex]
    have hc : (f.comp σ).prodMap (g.comp τ) = (f.prodMap g).comp (σ.prodMap τ) := rfl
    rw [hc, FirstHurewicz.inducedChain_comp]
    rfl
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_affineChainMap (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) (n + 1)) :
    crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n
        (SingularMayerVietoris.affineChainMap p 2 a)
        (SingularMayerVietoris.affineChainMap q n b) =
      productAffineChainMap p q (n + 2) (formalTriangleCrossProduct n a b) := by
  have h :
    integerBilinearPrecompose
        (crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n)
        (SingularMayerVietoris.affineChainMap p 2) (SingularMayerVietoris.affineChainMap q n) =
      integerBilinearPostcompose (formalTriangleCrossProduct n)
        (productAffineChainMap p q (n + 2)) := by
    apply integerFormalBilinearMap_ext
    intro v w
    simp only [integerBilinearPrecompose_apply, integerBilinearPostcompose_apply,
      SingularMayerVietoris.affineChainMap_simplex, crossProductTriangle_simplex]
    rw [inducedChain_productAffineChainMap]
    change
      productAffineChainMap p q (n + 2)
          (SingularMayerVietoris.formalMap
            (Prod.map (SingularMayerVietoris.affineSimplex v)
              (SingularMayerVietoris.affineSimplex w))
            (n + 3)
            (formalTriangleCrossProduct n
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
              (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices n)))) =
        _
    rw [formalMap_triangleCrossProduct, SingularMayerVietoris.formalMap_simplex,
      SingularMayerVietoris.formalMap_simplex, affineSimplex_stdVertices_image,
      affineSimplex_stdVertices_image]
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_zero_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 1) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 2
            1).hom
        (crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 0
        (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 2 1).hom
          (SingularMayerVietoris.affineChainMap p 2 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    crossProductEdge_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 3)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) (n + 2)) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d (n + 3)
            (n + 2)).hom
        (crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 2 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) (n + 1)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 2 1).hom
            (SingularMayerVietoris.affineChainMap p 2 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) +
        crossProductTriangle (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 2 a)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [crossProductTriangle_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_triangleCrossProduct, map_add, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductEdge_affineChainMap,
    crossProductTriangle_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_zero {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y 0) :
    ((FirstHurewicz.singularComplex (X × Y)).d 2 1).hom (crossProductTriangle X Y 0 a b) =
      crossProductEdge X Y 0 (((FirstHurewicz.singularComplex X).d 2 1).hom a) b := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y 0)
        ((FirstHurewicz.singularComplex (X × Y)).d 2 1).hom =
      integerBilinearPrecompose (crossProductEdge X Y 0)
        ((FirstHurewicz.singularComplex X).d 2 1).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 2 0
    intro σ τ
    have hstd :=
      crossProductTriangle_boundary_zero_affine 2 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 1) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, FirstHurewicz.inducedChain_boundary, crossProductTriangle_natural,
      crossProductEdge_natural, SingularMayerVietoris.affineChainMap_stdVertices,
      FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductTriangle_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y (n + 1)) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 3) (n + 2)).hom
        (crossProductTriangle X Y (n + 1) a b) =
      crossProductEdge X Y (n + 1) (((FirstHurewicz.singularComplex X).d 2 1).hom a) b +
        crossProductTriangle X Y n a (((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    integerBilinearPostcompose (crossProductTriangle X Y (n + 1))
        ((FirstHurewicz.singularComplex (X × Y)).d (n + 3) (n + 2)).hom =
      integerBilinearPrecompose (crossProductEdge X Y (n + 1))
          ((FirstHurewicz.singularComplex X).d 2 1).hom LinearMap.id +
        integerBilinearPrecompose (crossProductTriangle X Y n) LinearMap.id
          ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 2 (n + 1)
    intro σ τ
    have hstd :=
      crossProductTriangle_boundary_affine 2 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 2))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) (n + 2)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.add_apply, LinearMap.id_apply, map_add, FirstHurewicz.inducedChain_boundary,
      crossProductTriangle_natural, crossProductEdge_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductTriangle_boundary_of_right_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 2)
    (b : FirstHurewicz.Chains Y n)
    (hb : ((FirstHurewicz.singularComplex Y).d n (n - 1)).hom b = 0) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductTriangle X Y n a b) =
      crossProductEdge X Y n (((FirstHurewicz.singularComplex X).d 2 1).hom a) b := by
  cases n with
  | zero => exact crossProductTriangle_boundary_zero a b
  | succ
    n =>
    have hb' : ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [crossProductTriangle_boundary, hb', map_zero, add_zero]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_boundary_zero_affine (p q : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) 1) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d 1
            0).hom
        (crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 0
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q 0 b)) =
      crossProductZeroLeft (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) 0
        (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 1 0).hom
          (SingularMayerVietoris.affineChainMap p 1 a))
        (SingularMayerVietoris.affineChainMap q 0 b) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct_zero, SingularMayerVietoris.affineChainMap_boundary,
    crossProductZeroLeft_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_boundary_affine (p q n : ℕ)
    (a : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex p) 2)
    (b : SingularMayerVietoris.FormalChains (FirstHurewicz.Simplex q) (n + 2)) :
    ((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p × FirstHurewicz.Simplex q)).d (n + 2)
            (n + 1)).hom
        (crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) (n + 1)
          (SingularMayerVietoris.affineChainMap p 1 a)
          (SingularMayerVietoris.affineChainMap q (n + 1) b)) =
      crossProductZeroLeft (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) (n + 1)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex p)).d 1 0).hom
            (SingularMayerVietoris.affineChainMap p 1 a))
          (SingularMayerVietoris.affineChainMap q (n + 1) b) -
        crossProductEdge (FirstHurewicz.Simplex p) (FirstHurewicz.Simplex q) n
          (SingularMayerVietoris.affineChainMap p 1 a)
          (((FirstHurewicz.singularComplex (FirstHurewicz.Simplex q)).d (n + 1) n).hom
            (SingularMayerVietoris.affineChainMap q (n + 1) b)) := by
  rw [crossProductEdge_affineChainMap, productAffineChainMap_boundary,
    formalBoundary_edgeCrossProduct, map_sub, SingularMayerVietoris.affineChainMap_boundary,
    SingularMayerVietoris.affineChainMap_boundary, crossProductZeroLeft_affineChainMap,
    crossProductEdge_affineChainMap]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductEdge_boundary_zero {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y 0) :
    ((FirstHurewicz.singularComplex (X × Y)).d 1 0).hom (crossProductEdge X Y 0 a b) =
      crossProductZeroLeft X Y 0 (((FirstHurewicz.singularComplex X).d 1 0).hom a) b := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y 0)
        ((FirstHurewicz.singularComplex (X × Y)).d 1 0).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y 0)
        ((FirstHurewicz.singularComplex X).d 1 0).hom LinearMap.id := by
    apply chainBilinearMap_ext X Y 1 0
    intro σ τ
    have hstd :=
      crossProductEdge_boundary_zero_affine 1 0
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 0))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) 0) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.id_apply, FirstHurewicz.inducedChain_boundary, crossProductEdge_natural,
      crossProductZeroLeft_natural, SingularMayerVietoris.affineChainMap_stdVertices,
      FirstHurewicz.inducedChain_simplex, ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem
    PeriodTorusHigherHomology.crossProductEdge_boundary {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (b : FirstHurewicz.Chains Y (n + 1)) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      crossProductZeroLeft X Y (n + 1) (((FirstHurewicz.singularComplex X).d 1 0).hom a) b -
        crossProductEdge X Y n a (((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b) := by
  have h :
    integerBilinearPostcompose (crossProductEdge X Y (n + 1))
        ((FirstHurewicz.singularComplex (X × Y)).d (n + 2) (n + 1)).hom =
      integerBilinearPrecompose (crossProductZeroLeft X Y (n + 1))
          ((FirstHurewicz.singularComplex X).d 1 0).hom LinearMap.id -
        integerBilinearPrecompose (crossProductEdge X Y n) LinearMap.id
          ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom := by
    apply chainBilinearMap_ext X Y 1 (n + 1)
    intro σ τ
    have hstd :=
      crossProductEdge_boundary_affine 1 (n + 1) n
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices 1))
        (SingularMayerVietoris.formalSimplex (SingularMayerVietoris.stdVertices (n + 1)))
    have hστ := congrArg (FirstHurewicz.inducedChain (σ.prodMap τ) (n + 1)) hstd
    simpa only [integerBilinearPostcompose_apply, integerBilinearPrecompose_apply,
      LinearMap.sub_apply, LinearMap.id_apply, map_sub, FirstHurewicz.inducedChain_boundary,
      crossProductEdge_natural, crossProductZeroLeft_natural,
      SingularMayerVietoris.affineChainMap_stdVertices, FirstHurewicz.inducedChain_simplex,
      ContinuousMap.comp_id] using hστ
  exact LinearMap.congr_fun (LinearMap.congr_fun h a) b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_cycle {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 1) (b : FirstHurewicz.Chains Y n)
    (ha : ((FirstHurewicz.singularComplex X).d 1 0).hom a = 0)
    (hb : ((FirstHurewicz.singularComplex Y).d n (n - 1)).hom b = 0) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 1) n).hom (crossProductEdge X Y n a b) = 0 := by
  cases n with
  | zero =>
    have h := crossProductEdge_boundary_zero a b
    rw [ha, map_zero, LinearMap.zero_apply] at h
    exact h
  | succ
    n =>
    have hb' : ((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b = 0 := by
      simpa only [Nat.succ_sub_one] using hb
    simp only [crossProductEdge_boundary, ha, hb', map_zero, LinearMap.zero_apply, sub_self]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_boundary_of_left_cycle {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 1)
    (ha : ((FirstHurewicz.singularComplex X).d 1 0).hom a = 0)
    (b : FirstHurewicz.Chains Y (n + 1)) :
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (crossProductEdge X Y (n + 1) a b) =
      -crossProductEdge X Y n a (((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b) := by
  simp only [crossProductEdge_boundary, ha, map_zero, LinearMap.zero_apply, zero_sub]

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
private abbrev PeriodTorusHigherHomology.homologyBoundaries (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) : Submodule ℤ (SingularMayerVietoris.ModuleHomology.Cycle K n) :=
  FirstHurewicz.ChainHomology.ShortBoundaries (K.sc n)

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
private theorem
    PeriodTorusHigherHomology.homologyLinearMap_ext (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M] {f g : K.homology n →ₗ[ℤ] M}
    (h :
      ∀ c : SingularMayerVietoris.ModuleHomology.Cycle K n,
        f (SingularMayerVietoris.ModuleHomology.cycleClass K n c) =
          g (SingularMayerVietoris.ModuleHomology.cycleClass K n c)) :
    f = g := by
  apply LinearMap.ext
  intro x
  obtain ⟨c, rfl⟩ := SingularMayerVietoris.ModuleHomology.cycleClass_surjective K n x
  exact h c

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
private theorem
    PeriodTorusHigherHomology.homologyBoundaries_le_ker (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    homologyBoundaries K n ≤ LinearMap.ker f := by
  rintro c ⟨b, hb⟩
  have hc : SingularMayerVietoris.ModuleHomology.cycleClass K n c = 0 :=
    (FirstHurewicz.ChainHomology.shortCycleClass_eq_zero_iff (K.sc n) c).mpr
      ⟨b, congrArg Subtype.val hb⟩
  obtain ⟨b', hb'⟩ := (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff K n c).mp hc
  have he : SingularMayerVietoris.ModuleHomology.boundaryCycle K n b' = c := Subtype.ext hb'
  exact (congrArg f he).symm.trans (hf b')

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
private def PeriodTorusHigherHomology.homologyDesc (K : ChainComplex (ModuleCat.{0} ℤ) ℕ) (n : ℕ)
    {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0) :
    K.homology n →ₗ[ℤ] M :=
  ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)).comp
    (K.sc n).moduleCatHomologyIso.hom.hom

attribute [local instance] FirstHurewicz.ChainHomology.shortCycleModule in
@[simp]
private theorem
    PeriodTorusHigherHomology.homologyDesc_cycleClass (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (n : ℕ) {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : SingularMayerVietoris.ModuleHomology.Cycle K n →ₗ[ℤ] M)
    (hf : ∀ b : K.X (n + 1), f (SingularMayerVietoris.ModuleHomology.boundaryCycle K n b) = 0)
    (c : SingularMayerVietoris.ModuleHomology.Cycle K n) :
    homologyDesc K n f hf (SingularMayerVietoris.ModuleHomology.cycleClass K n c) = f c := by
  have h :=
    congrArg (fun q => q.hom (Submodule.Quotient.mk c)) (K.sc n).moduleCatHomologyIso.inv_hom_id
  exact congrArg ((homologyBoundaries K n).liftQ f (homologyBoundaries_le_ker K n f hf)) h

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n →ₗ[ℤ]
        SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex (X × Y)) (n + 1)
    where
  toFun
    a :=
    { toFun
        b :=
        SingularMayerVietoris.ModuleHomology.mkCycle (FirstHurewicz.singularComplex (X × Y))
          (n + 1) (crossProductEdge X Y n a.1 b.1)
          (by
            rw [Nat.add_sub_cancel]
            exact
              crossProductEdge_cycle n a.1 b.1
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex X) 1 a)
                (SingularMayerVietoris.ModuleHomology.cycle_condition
                  (FirstHurewicz.singularComplex Y) n b))
      map_add' b
        c := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_add b.1 c.1
      map_smul' r
        b := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_smul r b.1 }
  map_add' a
    b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : FirstHurewicz.Chains Y n →ₗ[ℤ] FirstHurewicz.Chains (X × Y) (n + 1) => f c.1)
        ((crossProductEdge X Y n).map_add a.1 b.1)
  map_smul' r
    a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact
      congrArg
        (fun f : FirstHurewicz.Chains Y n →ₗ[ℤ] FirstHurewicz.Chains (X × Y) (n + 1) => f c.1)
        ((crossProductEdge X Y n).map_smul r a.1)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductCycles_val (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    (crossProductCycles X Y n a b).1 = crossProductEdge X Y n a.1 b.1 :=
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductCycleClasses (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1 →ₗ[ℤ]
      SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n →ₗ[ℤ]
        (FirstHurewicz.singularComplex (X × Y)).homology (n + 1) :=
  integerBilinearPostcompose (crossProductCycles X Y n)
    (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y))
      (n + 1))

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCycleClasses_boundary_right {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : FirstHurewicz.Chains Y (n + 1)) :
    crossProductCycleClasses X Y n a
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (FirstHurewicz.singularComplex Y) n
          b) =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (FirstHurewicz.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨-crossProductEdge X Y (n + 1) a.1 b, ?_⟩
  change
    ((FirstHurewicz.singularComplex (X × Y)).d (n + 2) (n + 1)).hom
        (-crossProductEdge X Y (n + 1) a.1 b) =
      crossProductEdge X Y n a.1 (((FirstHurewicz.singularComplex Y).d (n + 1) n).hom b)
  rw [map_neg,
    crossProductEdge_boundary_of_left_cycle n a.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex X) 1
        a),
    neg_neg]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductHomologyFixed {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1) :
    (FirstHurewicz.singularComplex Y).homology n →ₗ[ℤ]
      (FirstHurewicz.singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (FirstHurewicz.singularComplex Y) n (crossProductCycleClasses X Y n a)
    (crossProductCycleClasses_boundary_right n a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductHomologyFixed_cycleClass {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    crossProductHomologyFixed n a
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y))
        (n + 1) (crossProductCycles X Y n a b) :=
  homologyDesc_cycleClass _ _ _ _ b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductHomologyCycles (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1 →ₗ[ℤ]
      ((FirstHurewicz.singularComplex Y).homology n →ₗ[ℤ]
        (FirstHurewicz.singularComplex (X × Y)).homology (n + 1))
    where
  toFun a := crossProductHomologyFixed n a
  map_add' a
    b := by
    apply homologyLinearMap_ext (FirstHurewicz.singularComplex Y) n
    intro c
    change
      crossProductHomologyFixed n (a + b)
          (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n
            c) =
        crossProductHomologyFixed n a
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n
              c) +
          crossProductHomologyFixed n b
            (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n
              c)
    simp only [crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n →ₗ[ℤ]
              (FirstHurewicz.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((crossProductCycleClasses X Y n).map_add a b)
  map_smul' r
    a := by
    apply homologyLinearMap_ext (FirstHurewicz.singularComplex Y) n
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, crossProductHomologyFixed_cycleClass]
    exact
      congrArg
        (fun f :
            SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n →ₗ[ℤ]
              (FirstHurewicz.singularComplex (X × Y)).homology (n + 1) =>
          f c)
        ((crossProductCycleClasses X Y n).map_smul r a)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductCycleClasses_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 2)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    crossProductCycleClasses X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (FirstHurewicz.singularComplex X) 1 a)
        b =
      0 := by
  apply
    (SingularMayerVietoris.ModuleHomology.cycleClass_eq_zero_iff
        (FirstHurewicz.singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨crossProductTriangle X Y n a b.1, ?_⟩
  exact
    crossProductTriangle_boundary_of_right_cycle n a b.1
      (SingularMayerVietoris.ModuleHomology.cycle_condition (FirstHurewicz.singularComplex Y) n b)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductHomologyCycles_boundary_left {X Y : Type}
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) (a : FirstHurewicz.Chains X 2) :
    crossProductHomologyCycles X Y n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (FirstHurewicz.singularComplex X) 1
          a) =
      0 := by
  apply homologyLinearMap_ext (FirstHurewicz.singularComplex Y) n
  intro b
  change
    crossProductHomologyFixed n
        (SingularMayerVietoris.ModuleHomology.boundaryCycle (FirstHurewicz.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n b) =
      0
  rw [crossProductHomologyFixed_cycleClass]
  exact crossProductCycleClasses_boundary_left n a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private def PeriodTorusHigherHomology.crossProductHomology (X Y : Type) [TopologicalSpace X]
    [TopologicalSpace Y] (n : ℕ) :
    (FirstHurewicz.singularComplex X).homology 1 →ₗ[ℤ]
      (FirstHurewicz.singularComplex Y).homology n →ₗ[ℤ]
        (FirstHurewicz.singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (FirstHurewicz.singularComplex X) 1 (crossProductHomologyCycles X Y n)
    (crossProductHomologyCycles_boundary_left n)

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductHomology_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1)
    (b : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex Y) n) :
    crossProductHomology X Y n
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 1 a)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) n b) =
      SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex (X × Y))
        (n + 1) (crossProductCycles X Y n a b) := by
  rw [crossProductHomology, homologyDesc_cycleClass]
  exact crossProductHomologyFixed_cycleClass n a b

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_zero_eq_zeroRight (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] :
    crossProductEdge X Y 0 = crossProductZeroRight X Y 1 := by
  apply chainBilinearMap_ext X Y 1 0
  intro σ τ
  rw [crossProductEdge_simplex, formalEdgeCrossProduct_zero_simplex_right,
    SingularMayerVietoris.formalMap_simplex, productAffineChainMap_simplex,
    FirstHurewicz.inducedChain_simplex, crossProductZeroRight_simplex]
  apply congrArg (FirstHurewicz.simplexChain (X × Y) 1)
  change
    (σ.prodMap τ).comp
        (productAffineSimplex
          (fun i =>
            (SingularMayerVietoris.stdVertices 1 i, SingularMayerVietoris.stdVertices 0 0))) =
      (crossInsertRight (zeroSimplexValue τ)).comp σ
  rw [productAffineSimplex_point_right, SingularMayerVietoris.affineSimplex_stdVertices,
    ContinuousMap.comp_id]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_zero_simplex_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1)
    (τ : FirstHurewicz.SingularSimplex Y 0) :
    crossProductEdge X Y 0 a (FirstHurewicz.simplexChain Y 0 τ) =
      FirstHurewicz.inducedChain (crossInsertRight (zeroSimplexValue τ)) 1 a := by
  rw [crossProductEdge_zero_eq_zeroRight, crossProductZeroRight_simplex_right]

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
private theorem PeriodTorusHigherHomology.crossProductEdge_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : FirstHurewicz.Chains X 1) (y : Y) :
    crossProductEdge X Y 0 a (pointCycle y).1 =
      FirstHurewicz.inducedChain (crossInsertRight y) 1 a := by
  rw [pointCycle_val, crossProductEdge_zero_simplex_right]
  rfl

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductCycles_pointCycle_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularMayerVietoris.ModuleHomology.Cycle (FirstHurewicz.singularComplex X) 1) (y : Y) :
    crossProductCycles X Y 0 a (pointCycle y) =
      SingularMayerVietoris.ModuleHomology.mapCycles
        (FirstHurewicz.singularChainMap (crossInsertRight y)) 1 a := by
  apply Subtype.ext
  rw [crossProductCycles_val, SingularMayerVietoris.ModuleHomology.mapCycles_val]
  exact crossProductEdge_pointCycle_right X Y a.1 y

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
    PeriodTorusHigherHomology.integerTensorModule in
@[simp]
private theorem PeriodTorusHigherHomology.crossProductHomology_pointClass_right (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (a : SingularMayerVietoris.SingularHomology X 1)
    (y : Y) :
    crossProductHomology X Y 0 a (pointClass y) =
      SingularMayerVietoris.singularHomologyMap (crossInsertRight y) 1 a := by
  obtain ⟨c, rfl⟩ :=
    SingularMayerVietoris.ModuleHomology.cycleClass_surjective (FirstHurewicz.singularComplex X) 1
      a
  change
    crossProductHomology X Y 0
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex X) 1 c)
        (SingularMayerVietoris.ModuleHomology.cycleClass (FirstHurewicz.singularComplex Y) 0
          (pointCycle y)) =
      _
  rw [crossProductHomology_cycleClass, crossProductCycles_pointCycle_right]
  exact
    (SingularMayerVietoris.ModuleHomology.homologyMap_cycleClass
        (FirstHurewicz.singularChainMap (crossInsertRight y)) 1 c).symm

private theorem PeriodTorusHigherHomology.formalBoundary_edge_simplex {V : Type*} (v : Fin 2 → V) :
    SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v) =
      SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 1) -
        SingularMayerVietoris.formalSimplex (fun _ : Fin 1 => v 0) := by
  rw [SingularMayerVietoris.formalBoundary_simplex]
  change
    (∑ i : Fin 2, (-1 : ℤ) ^ i.val • SingularMayerVietoris.formalSimplex (v ∘ i.succAbove)) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul,
    neg_one_smul, ← sub_eq_add_neg]
  congr 1 <;> congr 1 <;> funext i <;> rw [Fin.eq_zero i] <;> rfl

private theorem
    PeriodTorusHigherHomology.formalPointCrossProduct_edge_boundary {V W : Type*} (q : ℕ)
    (v : Fin 2 → V) (d : SingularMayerVietoris.FormalChains W (q + 1)) :
    formalPointCrossProduct q
        (SingularMayerVietoris.formalBoundary 1 (SingularMayerVietoris.formalSimplex v)) d =
      SingularMayerVietoris.formalMap (fun w => (v 1, w)) (q + 1) d -
        SingularMayerVietoris.formalMap (fun w => (v 0, w)) (q + 1) d := by
  rw [formalBoundary_edge_simplex, map_sub, LinearMap.sub_apply,
    formalPointCrossProduct_simplex_left, formalPointCrossProduct_simplex_left]

end Mathoverflow1973

end
