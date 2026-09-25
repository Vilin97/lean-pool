/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModBiprod

/-!
# Super modules form an abelian category

A module over a super-commutative ℂ-algebra `S` is a pair of
ℂ-modules carrying four bilinear action blocks, and a morphism is a
pair of ℂ-linear maps intertwining those blocks.  Every construction
needed for abelianness is therefore performed degreewise in
`Module ℂ`:

* the kernel is the pair of kernels of the two components, and the
  four blocks restrict to it;
* the cokernel is the pair of quotients by the two ranges, and the
  four blocks descend to them;
* a morphism is a monomorphism exactly when both of its components
  are injective, and an epimorphism exactly when both are
  surjective — the forward directions are read off the kernel and
  the cokernel respectively;
* a monomorphism is the kernel of its cokernel and an epimorphism is
  the cokernel of its kernel, because a degreewise factorisation
  through an injective (respectively surjective) component again
  intertwines the four blocks.

The route taken to `CategoryTheory.Abelian` is therefore the
normality route: the two normality instances, together with the
finite products of `RS.Classical.Deligne.SuperModBiprod` and the
kernels and cokernels built here.

Two small pieces of linear algebra carry all of the graded
bookkeeping.  `RS.SuperCommAlgebra.Mod.actRestrict` restricts a
bilinear action block to a pair of submodules stable under it, and
`RS.SuperCommAlgebra.Mod.actQuot` descends one to a pair of
quotients; the ten axioms of a super module are pointwise
identities, so each survives verbatim in a submodule and in a
quotient.
-/

namespace RS

open CategoryTheory Limits

universe u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}

/-! ## Restricting and descending an action block -/

section Blocks

variable {A E F : Type*}

/-- **The restriction of an action block** to a pair of submodules
carried into one another by it. -/
def actRestrict [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (φ : A →ₗ[ℂ] E →ₗ[ℂ] F) {p : Submodule ℂ E}
    {q : Submodule ℂ F} (h : ∀ a : A, ∀ e ∈ p, φ a e ∈ q) :
    A →ₗ[ℂ] p →ₗ[ℂ] q where
  toFun a :=
    LinearMap.codRestrict q ((φ a).comp p.subtype)
      fun e => h a e e.2
  map_add' a b := by
    refine LinearMap.ext fun e => Subtype.ext ?_
    simp
    rfl
  map_smul' c a := by
    refine LinearMap.ext fun e => Subtype.ext ?_
    simp
    rfl

@[simp]
theorem actRestrict_coe
    [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (φ : A →ₗ[ℂ] E →ₗ[ℂ] F)
    {p : Submodule ℂ E} {q : Submodule ℂ F}
    (h : ∀ a : A, ∀ e ∈ p, φ a e ∈ q) (a : A) (e : p) :
    (actRestrict φ h a e : F) = φ a e := rfl

/-- **The descent of an action block** to a pair of quotients, the
first by a submodule carried by the block into the second. -/
def actQuot [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (φ : A →ₗ[ℂ] E →ₗ[ℂ] F) {p : Submodule ℂ E}
    {q : Submodule ℂ F} (h : ∀ a : A, ∀ e ∈ p, φ a e ∈ q) :
    A →ₗ[ℂ] (E ⧸ p) →ₗ[ℂ] (F ⧸ q) :=
  (p.liftQ (LinearMap.compr₂ φ q.mkQ).flip
    (by
      intro e he
      refine LinearMap.mem_ker.2 (LinearMap.ext fun a => ?_)
      exact (Submodule.Quotient.mk_eq_zero q).2 (h a e he))).flip

@[simp]
theorem actQuot_mk [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (φ : A →ₗ[ℂ] E →ₗ[ℂ] F) {p : Submodule ℂ E}
    {q : Submodule ℂ F} (h : ∀ a : A, ∀ e ∈ p, φ a e ∈ q) (a : A)
    (e : E) :
    actQuot φ h a (Submodule.Quotient.mk e)
      = (Submodule.Quotient.mk (φ a e) : F ⧸ q) := rfl

/-- Congruence for the class map of a quotient module. -/
theorem quotMk_congr [AddCommGroup F] [Module ℂ F]
    {q : Submodule ℂ F} {a b : F} (h : a = b) :
    (Submodule.Quotient.mk a : F ⧸ q) = Submodule.Quotient.mk b :=
  congrArg _ h

end Blocks

/-! ## Degreewise factorisation -/

section Factor

variable {E F G : Type*}

/-- **The factorisation of a linear map through an injective one**
whose range contains its values. -/
noncomputable def preimageMap
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (g : E →ₗ[ℂ] G) (φ : F →ₗ[ℂ] G)
    (hφ : Function.Injective φ)
    (h : ∀ e, g e ∈ LinearMap.range φ) : E →ₗ[ℂ] F :=
  (LinearEquiv.ofInjective φ hφ).symm.toLinearMap.comp
    (LinearMap.codRestrict (LinearMap.range φ) g h)

@[simp]
theorem preimageMap_spec
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (g : E →ₗ[ℂ] G) (φ : F →ₗ[ℂ] G)
    (hφ : Function.Injective φ)
    (h : ∀ e, g e ∈ LinearMap.range φ) (e : E) :
    φ (preimageMap g φ hφ h e) = g e :=
  LinearEquiv.ofInjective_symm_apply (h := hφ) φ _

/-- A linear map annihilating the kernel of another has a larger
kernel. -/
theorem ker_le_ker [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (g : E →ₗ[ℂ] G) (φ : E →ₗ[ℂ] F)
    (h : ∀ e, φ e = 0 → g e = 0) :
    LinearMap.ker φ ≤ LinearMap.ker g := by
  intro e he
  exact LinearMap.mem_ker.2 (h e (LinearMap.mem_ker.1 he))

/-- **The factorisation of a linear map through a surjective one**
whose kernel it annihilates. -/
noncomputable def quotientMap
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (g : E →ₗ[ℂ] G) (φ : E →ₗ[ℂ] F)
    (hφ : Function.Surjective φ)
    (h : ∀ e, φ e = 0 → g e = 0) : F →ₗ[ℂ] G :=
  (Submodule.liftQ (LinearMap.ker φ) g (ker_le_ker g φ h)).comp
    (LinearMap.quotKerEquivOfSurjective φ hφ).symm.toLinearMap

@[simp]
theorem quotientMap_spec
    [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    [AddCommGroup G] [Module ℂ G]
    (g : E →ₗ[ℂ] G) (φ : E →ₗ[ℂ] F)
    (hφ : Function.Surjective φ)
    (h : ∀ e, φ e = 0 → g e = 0) (e : E) :
    quotientMap g φ hφ h (φ e) = g e := by
  have hs : (LinearMap.quotKerEquivOfSurjective φ hφ).symm (φ e)
      = Submodule.Quotient.mk e :=
    LinearMap.quotKerEquivOfSurjective_symm_apply φ hφ e
  change Submodule.liftQ (LinearMap.ker φ) g (ker_le_ker g φ h)
      ((LinearMap.quotKerEquivOfSurjective φ hφ).symm (φ e)) = g e
  rw [hs]
  rfl

end Factor

/-! ## Degreewise criteria for monomorphisms and epimorphisms -/

section Criteria

variable {M N : S.Mod.{u, u, u, u}}

/-- A degreewise injective morphism of super modules is a
monomorphism. -/
theorem mono_of_injective (f : M ⟶ N)
    (he : Function.Injective f.evenMap)
    (ho : Function.Injective f.oddMap) : Mono f where
  right_cancellation {W} g h heq := by
    refine Hom.ext (LinearMap.ext fun w => he ?_)
      (LinearMap.ext fun w => ho ?_)
    · exact congrArg (fun t : W ⟶ N => t.evenMap w) heq
    · exact congrArg (fun t : W ⟶ N => t.oddMap w) heq

/-- A degreewise surjective morphism of super modules is an
epimorphism. -/
theorem epi_of_surjective (f : M ⟶ N)
    (he : Function.Surjective f.evenMap)
    (ho : Function.Surjective f.oddMap) : Epi f where
  left_cancellation {W} g h heq := by
    refine Hom.ext (LinearMap.ext fun n => ?_)
      (LinearMap.ext fun n => ?_)
    · obtain ⟨m, rfl⟩ := he n
      exact congrArg (fun t : M ⟶ W => t.evenMap m) heq
    · obtain ⟨m, rfl⟩ := ho n
      exact congrArg (fun t : M ⟶ W => t.oddMap m) heq

end Criteria

/-! ## Kernels -/

section Kernels

variable {M N : S.Mod.{u, u, u, u}} (f : M ⟶ N)

theorem actEE_mem_ker (x : S.even) (m : M.even)
    (hm : m ∈ LinearMap.ker f.evenMap) :
    M.actEE x m ∈ LinearMap.ker f.evenMap := by
  refine LinearMap.mem_ker.2 ?_
  rw [f.map_actEE, LinearMap.mem_ker.1 hm, map_zero]

theorem actEO_mem_ker (x : S.even) (m : M.odd)
    (hm : m ∈ LinearMap.ker f.oddMap) :
    M.actEO x m ∈ LinearMap.ker f.oddMap := by
  refine LinearMap.mem_ker.2 ?_
  rw [f.map_actEO, LinearMap.mem_ker.1 hm, map_zero]

theorem actOE_mem_ker (v : S.odd) (m : M.even)
    (hm : m ∈ LinearMap.ker f.evenMap) :
    M.actOE v m ∈ LinearMap.ker f.oddMap := by
  refine LinearMap.mem_ker.2 ?_
  rw [f.map_actOE, LinearMap.mem_ker.1 hm, map_zero]

theorem actOO_mem_ker (v : S.odd) (m : M.odd)
    (hm : m ∈ LinearMap.ker f.oddMap) :
    M.actOO v m ∈ LinearMap.ker f.evenMap := by
  refine LinearMap.mem_ker.2 ?_
  rw [f.map_actOO, LinearMap.mem_ker.1 hm, map_zero]

/-- **The kernel of a morphism of super modules**: the kernels of
the two components, with the four action blocks restricted. -/
def kerMod : S.Mod.{u, u, u, u} where
  even := LinearMap.ker f.evenMap
  odd := LinearMap.ker f.oddMap
  actEE := actRestrict M.actEE (actEE_mem_ker f)
  actEO := actRestrict M.actEO (actEO_mem_ker f)
  actOE := actRestrict M.actOE (actOE_mem_ker f)
  actOO := actRestrict M.actOO (actOO_mem_ker f)
  one_act_e m := Subtype.ext (M.one_act_e m.1)
  one_act_o m := Subtype.ext (M.one_act_o m.1)
  assoc_eee x y m := Subtype.ext (M.assoc_eee x y m.1)
  assoc_eeo x y m := Subtype.ext (M.assoc_eeo x y m.1)
  assoc_eoe x v m := Subtype.ext (M.assoc_eoe x v m.1)
  assoc_eoo x v m := Subtype.ext (M.assoc_eoo x v m.1)
  assoc_oee v x m := Subtype.ext (M.assoc_oee v x m.1)
  assoc_oeo v x m := Subtype.ext (M.assoc_oeo v x m.1)
  assoc_ooe v w m := Subtype.ext (M.assoc_ooe v w m.1)
  assoc_ooo v w m := Subtype.ext (M.assoc_ooo v w m.1)

/-- The inclusion of the kernel of a morphism of super modules. -/
def kerIncl : kerMod f ⟶ M where
  evenMap := (LinearMap.ker f.evenMap).subtype
  oddMap := (LinearMap.ker f.oddMap).subtype
  map_actEE _ _ := rfl
  map_actEO _ _ := rfl
  map_actOE _ _ := rfl
  map_actOO _ _ := rfl

theorem kerIncl_comp : kerIncl f ≫ f = 0 := by
  refine Hom.ext (LinearMap.ext fun z => ?_)
    (LinearMap.ext fun z => ?_)
  · exact LinearMap.mem_ker.1 z.2
  · exact LinearMap.mem_ker.1 z.2

/-- The inclusion of the kernel is a monomorphism. -/
theorem mono_kerIncl : Mono (kerIncl f) :=
  mono_of_injective _ Subtype.coe_injective Subtype.coe_injective

/-- The lift of a morphism annihilated by `f` through the
inclusion of the kernel. -/
def kerLift {W : S.Mod.{u, u, u, u}} (k : W ⟶ M)
    (hk : k ≫ f = 0) : W ⟶ kerMod f where
  evenMap :=
    LinearMap.codRestrict _ k.evenMap fun w =>
      LinearMap.mem_ker.2
        (congrArg (fun t : W ⟶ N => t.evenMap w) hk)
  oddMap :=
    LinearMap.codRestrict _ k.oddMap fun w =>
      LinearMap.mem_ker.2
        (congrArg (fun t : W ⟶ N => t.oddMap w) hk)
  map_actEE x m := Subtype.ext (k.map_actEE x m)
  map_actEO x m := Subtype.ext (k.map_actEO x m)
  map_actOE v m := Subtype.ext (k.map_actOE v m)
  map_actOO v m := Subtype.ext (k.map_actOO v m)

theorem kerLift_comp {W : S.Mod.{u, u, u, u}} (k : W ⟶ M)
    (hk : k ≫ f = 0) : kerLift f k hk ≫ kerIncl f = k :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

/-- The kernel fork of a morphism of super modules. -/
def kernelFork : KernelFork f :=
  KernelFork.ofι (kerIncl f) (kerIncl_comp f)

/-- **The kernel fork is limiting.** -/
def kernelForkIsLimit : IsLimit (kernelFork f) :=
  have : Mono (kerIncl f) := mono_kerIncl f
  KernelFork.IsLimit.ofι' (kerIncl f) (kerIncl_comp f)
    fun k hk => ⟨kerLift f k hk, kerLift_comp f k hk⟩

/-- **Super modules have kernels**, computed degreewise. -/
instance instHasKernels : HasKernels S.Mod.{u, u, u, u} where
  has_limit f := HasLimit.mk
    { cone := kernelFork f
      isLimit := kernelForkIsLimit f }

end Kernels

/-! ## Cokernels -/

section Cokernels

variable {M N : S.Mod.{u, u, u, u}} (f : M ⟶ N)

theorem actEE_mem_range (x : S.even) (n : N.even)
    (hn : n ∈ LinearMap.range f.evenMap) :
    N.actEE x n ∈ LinearMap.range f.evenMap := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨M.actEE x m, f.map_actEE x m⟩

theorem actEO_mem_range (x : S.even) (n : N.odd)
    (hn : n ∈ LinearMap.range f.oddMap) :
    N.actEO x n ∈ LinearMap.range f.oddMap := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨M.actEO x m, f.map_actEO x m⟩

theorem actOE_mem_range (v : S.odd) (n : N.even)
    (hn : n ∈ LinearMap.range f.evenMap) :
    N.actOE v n ∈ LinearMap.range f.oddMap := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨M.actOE v m, f.map_actOE v m⟩

theorem actOO_mem_range (v : S.odd) (n : N.odd)
    (hn : n ∈ LinearMap.range f.oddMap) :
    N.actOO v n ∈ LinearMap.range f.evenMap := by
  obtain ⟨m, rfl⟩ := hn
  exact ⟨M.actOO v m, f.map_actOO v m⟩

/-- **The cokernel of a morphism of super modules**: the quotients
of the two components by the two ranges, with the four action
blocks descended. -/
def cokerMod : S.Mod.{u, u, u, u} where
  even := N.even ⧸ LinearMap.range f.evenMap
  odd := N.odd ⧸ LinearMap.range f.oddMap
  actEE := actQuot N.actEE (actEE_mem_range f)
  actEO := actQuot N.actEO (actEO_mem_range f)
  actOE := actQuot N.actOE (actOE_mem_range f)
  actOO := actQuot N.actOO (actOO_mem_range f)
  one_act_e z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.one_act_e n)
  one_act_o z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.one_act_o n)
  assoc_eee x y z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_eee x y n)
  assoc_eeo x y z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_eeo x y n)
  assoc_eoe x v z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_eoe x v n)
  assoc_eoo x v z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_eoo x v n)
  assoc_oee v x z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_oee v x n)
  assoc_oeo v x z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_oeo v x n)
  assoc_ooe v w z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_ooe v w n)
  assoc_ooo v w z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact quotMk_congr (N.assoc_ooo v w n)

/-- The projection onto the cokernel of a morphism of super
modules. -/
def cokerProj : N ⟶ cokerMod f where
  evenMap := (LinearMap.range f.evenMap).mkQ
  oddMap := (LinearMap.range f.oddMap).mkQ
  map_actEE _ _ := rfl
  map_actEO _ _ := rfl
  map_actOE _ _ := rfl
  map_actOO _ _ := rfl

theorem comp_cokerProj : f ≫ cokerProj f = 0 := by
  refine Hom.ext (LinearMap.ext fun m => ?_)
    (LinearMap.ext fun m => ?_)
  · exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩
  · exact (Submodule.Quotient.mk_eq_zero _).2 ⟨m, rfl⟩

/-- The projection onto the cokernel is an epimorphism. -/
theorem epi_cokerProj : Epi (cokerProj f) :=
  epi_of_surjective _ (Submodule.mkQ_surjective _)
    (Submodule.mkQ_surjective _)

/-- The descent of a morphism annihilating `f` through the
projection onto the cokernel. -/
def cokerDesc {W : S.Mod.{u, u, u, u}} (k : N ⟶ W)
    (hk : f ≫ k = 0) : cokerMod f ⟶ W where
  evenMap :=
    Submodule.liftQ _ k.evenMap
      (by
        refine LinearMap.range_le_ker_iff.2 ?_
        have h : k.evenMap.comp f.evenMap
            = (0 : M.even →ₗ[ℂ] W.even) :=
          congrArg (fun t : M ⟶ W => t.evenMap) hk
        exact h)
  oddMap :=
    Submodule.liftQ _ k.oddMap
      (by
        refine LinearMap.range_le_ker_iff.2 ?_
        have h : k.oddMap.comp f.oddMap
            = (0 : M.odd →ₗ[ℂ] W.odd) :=
          congrArg (fun t : M ⟶ W => t.oddMap) hk
        exact h)
  map_actEE x z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact k.map_actEE x n
  map_actEO x z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact k.map_actEO x n
  map_actOE v z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact k.map_actOE v n
  map_actOO v z := by
    obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact k.map_actOO v n

theorem cokerProj_desc {W : S.Mod.{u, u, u, u}} (k : N ⟶ W)
    (hk : f ≫ k = 0) : cokerProj f ≫ cokerDesc f k hk = k :=
  Hom.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

/-- The cokernel cofork of a morphism of super modules. -/
def cokernelCofork : CokernelCofork f :=
  CokernelCofork.ofπ (cokerProj f) (comp_cokerProj f)

/-- **The cokernel cofork is colimiting.** -/
def cokernelCoforkIsColimit : IsColimit (cokernelCofork f) :=
  have : Epi (cokerProj f) := epi_cokerProj f
  CokernelCofork.IsColimit.ofπ' (cokerProj f) (comp_cokerProj f)
    fun k hk => ⟨cokerDesc f k hk, cokerProj_desc f k hk⟩

/-- **Super modules have cokernels**, computed degreewise. -/
instance instHasCokernels : HasCokernels S.Mod.{u, u, u, u} where
  has_colimit f := HasColimit.mk
    { cocone := cokernelCofork f
      isColimit := cokernelCoforkIsColimit f }

end Cokernels

/-! ## The degreewise bridges -/

section Bridges

variable {M N : S.Mod.{u, u, u, u}}

/-- **A morphism of super modules is a monomorphism exactly when
both of its components are injective.** -/
theorem mono_iff (f : M ⟶ N) : Mono f ↔
    Function.Injective f.evenMap ∧ Function.Injective f.oddMap := by
  refine ⟨fun hf => ?_, fun h => mono_of_injective f h.1 h.2⟩
  have h0 : kerIncl f = 0 := by
    refine (cancel_mono f).1 ?_
    rw [kerIncl_comp, Limits.zero_comp]
  constructor
  · refine LinearMap.ker_eq_bot.1 (Submodule.eq_bot_iff _ |>.2 ?_)
    intro m hm
    exact congrArg
      (fun t : kerMod f ⟶ M => t.evenMap ⟨m, hm⟩) h0
  · refine LinearMap.ker_eq_bot.1 (Submodule.eq_bot_iff _ |>.2 ?_)
    intro m hm
    exact congrArg
      (fun t : kerMod f ⟶ M => t.oddMap ⟨m, hm⟩) h0

/-- **A morphism of super modules is an epimorphism exactly when
both of its components are surjective.** -/
theorem epi_iff (f : M ⟶ N) : Epi f ↔
    Function.Surjective f.evenMap ∧ Function.Surjective f.oddMap := by
  refine ⟨fun hf => ?_, fun h => epi_of_surjective f h.1 h.2⟩
  have h0 : cokerProj f = 0 := by
    refine (cancel_epi f).1 ?_
    rw [comp_cokerProj, Limits.comp_zero]
  constructor
  · refine LinearMap.range_eq_top.1 (Submodule.eq_top_iff'.2 ?_)
    intro n
    have h : (Submodule.Quotient.mk n :
        N.even ⧸ LinearMap.range f.evenMap) = 0 :=
      congrArg (fun t : N ⟶ cokerMod f => t.evenMap n) h0
    exact (Submodule.Quotient.mk_eq_zero _).1 h
  · refine LinearMap.range_eq_top.1 (Submodule.eq_top_iff'.2 ?_)
    intro n
    have h : (Submodule.Quotient.mk n :
        N.odd ⧸ LinearMap.range f.oddMap) = 0 :=
      congrArg (fun t : N ⟶ cokerMod f => t.oddMap n) h0
    exact (Submodule.Quotient.mk_eq_zero _).1 h

end Bridges

/-! ## Normality -/

section Normal

variable {M N : S.Mod.{u, u, u, u}} (f : M ⟶ N)

/-- The degreewise factorisation of a morphism annihilated by the
projection onto the cokernel of a degreewise injective `f`. -/
noncomputable def monoLift {W : S.Mod.{u, u, u, u}}
    (he : Function.Injective f.evenMap)
    (ho : Function.Injective f.oddMap) (k : W ⟶ N)
    (hme : ∀ w, k.evenMap w ∈ LinearMap.range f.evenMap)
    (hmo : ∀ w, k.oddMap w ∈ LinearMap.range f.oddMap) :
    W ⟶ M where
  evenMap := preimageMap k.evenMap f.evenMap he hme
  oddMap := preimageMap k.oddMap f.oddMap ho hmo
  map_actEE x m := by
    refine he ?_
    rw [preimageMap_spec, f.map_actEE, preimageMap_spec,
      k.map_actEE]
  map_actEO x m := by
    refine ho ?_
    rw [preimageMap_spec, f.map_actEO, preimageMap_spec,
      k.map_actEO]
  map_actOE v m := by
    refine ho ?_
    rw [preimageMap_spec, f.map_actOE, preimageMap_spec,
      k.map_actOE]
  map_actOO v m := by
    refine he ?_
    rw [preimageMap_spec, f.map_actOO, preimageMap_spec,
      k.map_actOO]

theorem monoLift_comp {W : S.Mod.{u, u, u, u}}
    (he : Function.Injective f.evenMap)
    (ho : Function.Injective f.oddMap) (k : W ⟶ N)
    (hme : ∀ w, k.evenMap w ∈ LinearMap.range f.evenMap)
    (hmo : ∀ w, k.oddMap w ∈ LinearMap.range f.oddMap) :
    monoLift f he ho k hme hmo ≫ f = k :=
  Hom.ext
    (LinearMap.ext fun w =>
      preimageMap_spec k.evenMap f.evenMap he hme w)
    (LinearMap.ext fun w =>
      preimageMap_spec k.oddMap f.oddMap ho hmo w)

theorem evenMap_mem_range {W : S.Mod.{u, u, u, u}} (k : W ⟶ N)
    (hk : k ≫ cokerProj f = 0) (w : W.even) :
    k.evenMap w ∈ LinearMap.range f.evenMap := by
  have h : (Submodule.Quotient.mk (k.evenMap w) :
      N.even ⧸ LinearMap.range f.evenMap) = 0 :=
    congrArg (fun t : W ⟶ cokerMod f => t.evenMap w) hk
  exact (Submodule.Quotient.mk_eq_zero _).1 h

theorem oddMap_mem_range {W : S.Mod.{u, u, u, u}} (k : W ⟶ N)
    (hk : k ≫ cokerProj f = 0) (w : W.odd) :
    k.oddMap w ∈ LinearMap.range f.oddMap := by
  have h : (Submodule.Quotient.mk (k.oddMap w) :
      N.odd ⧸ LinearMap.range f.oddMap) = 0 :=
    congrArg (fun t : W ⟶ cokerMod f => t.oddMap w) hk
  exact (Submodule.Quotient.mk_eq_zero _).1 h

/-- **A degreewise injective morphism of super modules is the
kernel of its cokernel.** -/
@[implicit_reducible]
noncomputable def normalMonoOfInjective (he : Function.Injective f.evenMap)
    (ho : Function.Injective f.oddMap) : NormalMono f where
  Z := cokerMod f
  g := cokerProj f
  w := comp_cokerProj f
  isLimit :=
    have : Mono f := mono_of_injective f he ho
    KernelFork.IsLimit.ofι' f (comp_cokerProj f)
      fun k hk =>
        ⟨monoLift f he ho k (evenMap_mem_range f k hk)
            (oddMap_mem_range f k hk),
          monoLift_comp f he ho k _ _⟩

/-- The degreewise factorisation of a morphism annihilating the
inclusion of the kernel of a degreewise surjective `f`. -/
noncomputable def epiDesc {W : S.Mod.{u, u, u, u}}
    (he : Function.Surjective f.evenMap)
    (ho : Function.Surjective f.oddMap) (k : M ⟶ W)
    (hke : ∀ m, f.evenMap m = 0 → k.evenMap m = 0)
    (hko : ∀ m, f.oddMap m = 0 → k.oddMap m = 0) :
    N ⟶ W where
  evenMap := quotientMap k.evenMap f.evenMap he hke
  oddMap := quotientMap k.oddMap f.oddMap ho hko
  map_actEE x n := by
    obtain ⟨m, rfl⟩ := he n
    rw [← f.map_actEE, quotientMap_spec, quotientMap_spec,
      k.map_actEE]
  map_actEO x n := by
    obtain ⟨m, rfl⟩ := ho n
    rw [← f.map_actEO, quotientMap_spec, quotientMap_spec,
      k.map_actEO]
  map_actOE v n := by
    obtain ⟨m, rfl⟩ := he n
    rw [← f.map_actOE, quotientMap_spec, quotientMap_spec,
      k.map_actOE]
  map_actOO v n := by
    obtain ⟨m, rfl⟩ := ho n
    rw [← f.map_actOO, quotientMap_spec, quotientMap_spec,
      k.map_actOO]

theorem comp_epiDesc {W : S.Mod.{u, u, u, u}}
    (he : Function.Surjective f.evenMap)
    (ho : Function.Surjective f.oddMap) (k : M ⟶ W)
    (hke : ∀ m, f.evenMap m = 0 → k.evenMap m = 0)
    (hko : ∀ m, f.oddMap m = 0 → k.oddMap m = 0) :
    f ≫ epiDesc f he ho k hke hko = k :=
  Hom.ext
    (LinearMap.ext fun m =>
      quotientMap_spec k.evenMap f.evenMap he hke m)
    (LinearMap.ext fun m =>
      quotientMap_spec k.oddMap f.oddMap ho hko m)

theorem evenMap_eq_zero_of_comp {W : S.Mod.{u, u, u, u}}
    (k : M ⟶ W) (hk : kerIncl f ≫ k = 0) (m : M.even)
    (hm : f.evenMap m = 0) : k.evenMap m = 0 :=
  congrArg
    (fun t : kerMod f ⟶ W =>
      t.evenMap ⟨m, LinearMap.mem_ker.2 hm⟩) hk

theorem oddMap_eq_zero_of_comp {W : S.Mod.{u, u, u, u}}
    (k : M ⟶ W) (hk : kerIncl f ≫ k = 0) (m : M.odd)
    (hm : f.oddMap m = 0) : k.oddMap m = 0 :=
  congrArg
    (fun t : kerMod f ⟶ W =>
      t.oddMap ⟨m, LinearMap.mem_ker.2 hm⟩) hk

/-- **A degreewise surjective morphism of super modules is the
cokernel of its kernel.** -/
@[implicit_reducible]
noncomputable def normalEpiOfSurjective (he : Function.Surjective f.evenMap)
    (ho : Function.Surjective f.oddMap) : NormalEpi f where
  W := kerMod f
  g := kerIncl f
  w := kerIncl_comp f
  isColimit :=
    have : Epi f := epi_of_surjective f he ho
    CokernelCofork.IsColimit.ofπ' f (kerIncl_comp f)
      fun k hk =>
        ⟨epiDesc f he ho k (evenMap_eq_zero_of_comp f k hk)
            (oddMap_eq_zero_of_comp f k hk),
          comp_epiDesc f he ho k _ _⟩

end Normal

/-! ## Abelianness -/

/-- **Every monomorphism of super modules is a kernel.** -/
instance instIsNormalMonoCategory :
    IsNormalMonoCategory S.Mod.{u, u, u, u} where
  normalMonoOfMono f hf :=
    ⟨normalMonoOfInjective f ((mono_iff f).1 hf).1
      ((mono_iff f).1 hf).2⟩

/-- **Every epimorphism of super modules is a cokernel.** -/
instance instIsNormalEpiCategory :
    IsNormalEpiCategory S.Mod.{u, u, u, u} where
  normalEpiOfEpi f hf :=
    ⟨normalEpiOfSurjective f ((epi_iff f).1 hf).1
      ((epi_iff f).1 hf).2⟩

/-- Super modules have finite products: they have a zero object and
binary biproducts. -/
instance instHasFiniteProducts :
    HasFiniteProducts S.Mod.{u, u, u, u} :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- **Modules over a super-commutative ℂ-algebra form an abelian
category**, with kernels, cokernels and biproducts all computed
degreewise. -/
noncomputable instance instAbelian : Abelian S.Mod.{u, u, u, u} where
  normalMonoOfMono f hf :=
    ⟨normalMonoOfInjective f ((mono_iff f).1 hf).1
      ((mono_iff f).1 hf).2⟩
  normalEpiOfEpi f hf :=
    ⟨normalEpiOfSurjective f ((epi_iff f).1 hf).1
      ((epi_iff f).1 hf).2⟩

end SuperCommAlgebra.Mod

end RS
