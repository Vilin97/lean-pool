/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.Cech

/-!
# Multiplication on Čech `H¹` by global meromorphic functions (cechcount unit)

Unit: cechcount (`Jacobian/CechCount/`), the final gate: Forster §17.8-17.9 at the Čech level.

Multiplication by a fixed global meromorphic function `f : ℳ X` acts on `O_D`-valued Čech
cochains, sending the `D`-pole-bound to an `E`-pole-bound whenever the pointwise order bound
`MulBound f D E` (`∀ x, D x - E x ≤ ord_x f`, in `WithTop ℤ`) holds.  This file builds the
action level by level, mirroring `Colimit.lean`'s `H1Incl` construction verbatim:

* `MulBound f D E` and its kit (`mulBound_zero`, `MulBound.add/smul/mul`, `mulBound_one`,
  `le_of_mulBound_one`, `mulBound_of_mem_linSys`).
* `mulOn f hf U : LinSysOn D U →ₗ LinSysOn E U` (germ level, via `LinearMap.mulLeft` and
  `MeroGermOn.restrict`), commuting with the presheaf restrictions (`restrictL_mulOn`).
* `mulC0`/`mulC1` (cochain level), commuting with `d0`/`d1`/`resC1`, hence `mulZ1`,
  `mulH1Cover` (`Submodule.mapQ`), commuting with `resH1`.
* **`mulH1 f hf : H1 D →ₗ[ℂ] H1 E`** (`Module.DirectLimit.map`), with `mulH1_toH1` and the
  algebra laws `mulH1_add`, `mulH1_smul`, `mulH1_mulH1` (composition = product),
  `mulH1_one` (= `H1Incl`), `mulH1_H1Incl`, `mulH1_congr`.

`Surjective.lean` (next file) combines these with `H1Incl_surjective` into the Forster 17.8
epimorphism statement `mulH1_surjective`.
-/

open scoped ContDiff Manifold
open Set TopologicalSpace RS.Cech Module


namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pointwise multiplication bound -/

/-- The pointwise order bound making multiplication by `f` carry `O_D`-cochains to
`O_E`-cochains: `D x - E x ≤ ord_x f` for every `x` (in `WithTop ℤ`; for `f = 0` the order is
`⊤` everywhere, so `MulBound 0 D E` always holds — multiplication by `0` is the zero map). -/
def MulBound (f : ℳ X) (D E : RS.Divisor X) : Prop :=
  ∀ x : X, ((D x - E x : ℤ) : WithTop ℤ) ≤ f.ord x

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulBound_zero (D E : RS.Divisor X) : MulBound (0 : ℳ X) D E := by
  intro x
  rw [RS.MeroGermOn.ord_zero, if_pos ⟨isOpen_univ, mem_univ x⟩]
  exact le_top

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem MulBound.add {f g : ℳ X} {D E : RS.Divisor X} (hf : MulBound f D E)
    (hg : MulBound g D E) : MulBound (f + g) D E := fun x =>
  le_trans (le_min (hf x) (hg x)) (RS.MeroGermOn.ord_add isOpen_univ (mem_univ x) f g)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem MulBound.smul {f : ℳ X} {D E : RS.Divisor X} (c : ℂ) (hf : MulBound f D E) :
    MulBound (c • f) D E := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    exact mulBound_zero D E
  · intro x
    rw [RS.MeroGermOn.ord_smul isOpen_univ (mem_univ x) hc]
    exact hf x

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem MulBound.mul {f g : ℳ X} {D D' E : RS.Divisor X} (hf : MulBound f D' E)
    (hg : MulBound g D D') : MulBound (f * g) D E := by
  intro x
  rw [RS.MeroGermOn.ord_mul isOpen_univ (mem_univ x)]
  have hsplit : (D x - E x : ℤ) = (D' x - E x) + (D x - D' x) := by ring
  calc ((D x - E x : ℤ) : WithTop ℤ)
      = ((D' x - E x : ℤ) : WithTop ℤ) + ((D x - D' x : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add, ← hsplit]
    _ ≤ f.ord x + g.ord x := add_le_add (hf x) (hg x)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulBound_one {D E : RS.Divisor X} (h : D ≤ E) : MulBound (1 : ℳ X) D E := by
  intro x
  rw [RS.MeroGermOn.ord_one isOpen_univ (mem_univ x)]
  have hx : D x ≤ E x := Function.locallyFinsuppWithin.le_def.1 h x
  exact_mod_cast sub_nonpos.mpr hx

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem le_of_mulBound_one {D E : RS.Divisor X} (h : MulBound (1 : ℳ X) D E) : D ≤ E := by
  rw [Function.locallyFinsuppWithin.le_def]
  intro x
  have hx := h x
  rw [RS.MeroGermOn.ord_one isOpen_univ (mem_univ x)] at hx
  have hle : (D x - E x : ℤ) ≤ 0 := by exact_mod_cast hx
  exact sub_nonpos.mp hle

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulBound_of_mem_linSys {f : ℳ X} {B D E : RS.Divisor X} (hf : f ∈ RS.LinSys B)
    (h : ∀ x, D x - E x ≤ -(B x)) : MulBound f D E := fun x =>
  le_trans (WithTop.coe_le_coe.mpr (h x)) (hf x)

/-! ### Germ level: `mulOn` -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mul_restrict_mem_linSysOn {f : ℳ X} {D E : RS.Divisor X} (hf : MulBound f D E)
    (U : Opens X) {φ : RS.MeroGermOn X (U : Set X)} (hφ : φ ∈ RS.LinSysOn D (U : Set X)) :
    RS.MeroGermOn.restrict (Set.subset_univ (U : Set X)) f * φ ∈ RS.LinSysOn E (U : Set X) := by
  rw [RS.mem_linSysOn_iff_of_isOpen U.isOpen] at hφ ⊢
  intro x hx
  rw [RS.MeroGermOn.ord_mul U.isOpen hx,
    RS.MeroGermOn.ord_restrict (Set.subset_univ (U : Set X)) U.isOpen isOpen_univ hx]
  have hsplit : (-(E x) : ℤ) = (D x - E x) + (-(D x)) := by ring
  calc ((-(E x) : ℤ) : WithTop ℤ)
      = ((D x - E x : ℤ) : WithTop ℤ) + ((-(D x) : ℤ) : WithTop ℤ) := by
        rw [← WithTop.coe_add, ← hsplit]
    _ ≤ f.ord x + φ.ord x := add_le_add (hf x) (hφ x hx)

/-- Multiplication by (the restriction of) a global meromorphic function on relative linear
systems over an open `U`, under the pointwise bound `MulBound f D E`. -/
noncomputable def mulOn (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (U : Opens X) :
    RS.LinSysOn D (U : Set X) →ₗ[ℂ] RS.LinSysOn E (U : Set X) :=
  LinearMap.restrict
    (LinearMap.mulLeft ℂ (RS.MeroGermOn.restrict (Set.subset_univ (U : Set X)) f))
    (fun _φ hφ => by
      simpa only [LinearMap.mulLeft_apply] using mul_restrict_mem_linSysOn hf U hφ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulOn_apply_coe (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (U : Opens X)
    (φ : RS.LinSysOn D (U : Set X)) :
    (mulOn f hf U φ : RS.MeroGermOn X (U : Set X)) =
      RS.MeroGermOn.restrict (Set.subset_univ (U : Set X)) f *
        (φ : RS.MeroGermOn X (U : Set X)) := by
  rw [mulOn, LinearMap.coe_restrict_apply, LinearMap.mulLeft_apply]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `mulOn` commutes with the presheaf restriction maps. -/
theorem restrictL_mulOn {V U : Opens X} (hVU : V ≤ U) (f : ℳ X) {D E : RS.Divisor X}
    (hf : MulBound f D E) (φ : RS.LinSysOn D (U : Set X)) :
    LinSysOn.restrictL E hVU (mulOn f hf U φ) = mulOn f hf V (LinSysOn.restrictL D hVU φ) := by
  apply Subtype.ext
  rw [restrictL_apply_coe, mulOn_apply_coe, mulOn_apply_coe, restrictL_apply_coe, map_mul]
  congr 1
  exact RS.MeroGermOn.restrict_restrict _ _ f

/-! ### Cochain level: `mulC0`, `mulC1` -/

variable {Ω : Opens X}

/-- Multiplication by `f` on `0`-cochains (componentwise `mulOn`). -/
noncomputable def mulC0 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (𝒰 : FinCover Ω) :
    C0 D 𝒰 →ₗ[ℂ] C0 E 𝒰 :=
  LinearMap.pi fun i => (mulOn f hf (𝒰.U i)).comp (LinearMap.proj i)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulC0_apply (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    (g : C0 D 𝒰) (i : Fin 𝒰.n) : mulC0 f hf 𝒰 g i = mulOn f hf (𝒰.U i) (g i) := rfl

/-- Multiplication by `f` on `1`-cochains (componentwise `mulOn`). -/
noncomputable def mulC1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (𝒰 : FinCover Ω) :
    C1 D 𝒰 →ₗ[ℂ] C1 E 𝒰 :=
  LinearMap.pi fun p : Fin 𝒰.n × Fin 𝒰.n =>
    (mulOn f hf (𝒰.U p.1 ⊓ 𝒰.U p.2)).comp (LinearMap.proj p)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulC1_apply (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    (c : C1 D 𝒰) (p : Fin 𝒰.n × Fin 𝒰.n) :
    mulC1 f hf 𝒰 c p = mulOn f hf (𝒰.U p.1 ⊓ 𝒰.U p.2) (c p) := rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication commutes with the coboundary `d0`. -/
theorem mulC1_d0 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (𝒰 : FinCover Ω)
    (g : C0 D 𝒰) : mulC1 f hf 𝒰 (d0 D 𝒰 g) = d0 E 𝒰 (mulC0 f hf 𝒰 g) := by
  funext p
  rw [mulC1_apply, d0_apply, d0_apply, mulC0_apply, mulC0_apply, map_sub,
    ← restrictL_mulOn inf_le_right f hf (g p.2), ← restrictL_mulOn inf_le_left f hf (g p.1)]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication preserves cocycles. -/
theorem mulC1_mem_Z1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    {c : C1 D 𝒰} (hc : c ∈ Z1 D 𝒰) : mulC1 f hf 𝒰 c ∈ Z1 E 𝒰 := by
  rw [mem_Z1_iff]
  rintro ⟨i, j, k⟩
  rw [d1_apply, mulC1_apply, mulC1_apply, mulC1_apply,
    restrictL_mulOn (le_inf (inf_le_left.trans inf_le_right) inf_le_right) f hf (c (j, k)),
    restrictL_mulOn (le_inf (inf_le_left.trans inf_le_left) inf_le_right) f hf (c (i, k)),
    restrictL_mulOn inf_le_left f hf (c (i, j)),
    ← map_sub, ← map_add, ← d1_apply, (mem_Z1_iff D 𝒰 c).1 hc (i, j, k), map_zero]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication preserves coboundaries. -/
theorem mulC1_mem_B1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    {c : C1 D 𝒰} (hc : c ∈ B1 D 𝒰) : mulC1 f hf 𝒰 c ∈ B1 E 𝒰 := by
  obtain ⟨g, rfl⟩ := hc
  exact ⟨mulC0 f hf 𝒰 g, (mulC1_d0 f hf 𝒰 g).symm⟩

/-! ### Cocycle and cover-level `H¹` -/

/-- Multiplication on `1`-cocycles. -/
noncomputable def mulZ1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) (𝒰 : FinCover Ω) :
    Z1 D 𝒰 →ₗ[ℂ] Z1 E 𝒰 :=
  LinearMap.restrict (mulC1 f hf 𝒰) (fun _c hc => mulC1_mem_Z1 f hf hc)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulZ1_apply_coe (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    (c : Z1 D 𝒰) : (mulZ1 f hf 𝒰 c : C1 E 𝒰) = mulC1 f hf 𝒰 (c : C1 D 𝒰) := rfl

/-- Multiplication on cover-level `H¹`. -/
noncomputable def mulH1Cover (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E)
    (𝒰 : FinCover Ω) : H1Cover D 𝒰 →ₗ[ℂ] H1Cover E 𝒰 :=
  Submodule.mapQ _ _ (mulZ1 f hf 𝒰) (fun z hz => by
    simp only [Submodule.mem_comap] at hz ⊢
    exact mulC1_mem_B1 f hf hz)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulH1Cover_mk (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 : FinCover Ω}
    (c : Z1 D 𝒰) :
    mulH1Cover f hf 𝒰 (H1Cover.mk D 𝒰 c) = H1Cover.mk E 𝒰 (mulZ1 f hf 𝒰 c) :=
  Submodule.mapQ_apply _ _ _ c

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication commutes with refinement of `1`-cochains. -/
theorem mulC1_resC1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) {𝒰 𝒱 : FinCover Ω}
    (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (c : C1 D 𝒰) :
    mulC1 f hf 𝒱 (resC1 D τ hτ c) = resC1 E τ hτ (mulC1 f hf 𝒰 c) := by
  funext p
  rw [mulC1_apply, resC1_apply, resC1_apply, mulC1_apply,
    restrictL_mulOn (inf_le_inf (hτ p.1) (hτ p.2)) f hf (c (τ p.1, τ p.2))]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication commutes with refinement of cover-level `H¹`. -/
theorem mulH1Cover_resH1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E)
    {𝒰 𝒱 : FinCover Ω} (τ : Fin 𝒱.n → Fin 𝒰.n) (hτ : IsRefIdx 𝒰 𝒱 τ) (ξ : H1Cover D 𝒰) :
    mulH1Cover f hf 𝒱 (resH1 D τ hτ ξ) = resH1 E τ hτ (mulH1Cover f hf 𝒰 ξ) := by
  obtain ⟨c, rfl⟩ := H1Cover.mk_surjective D 𝒰 ξ
  simp only [resH1_mk, mulH1Cover_mk]
  congr 1
  exact Subtype.ext (mulC1_resC1 f hf τ hτ (c : C1 D 𝒰))

/-! ### The colimit map `mulH1` -/

/-- **Multiplication on Čech `H¹`** by a global meromorphic function `f` under the pointwise
bound `MulBound f D E` (Forster §17.8's sheaf morphism `O_D → O_E`, `g ↦ f·g`, at the colimit
level). Built via `Module.DirectLimit.map`, mirroring `H1Incl`. -/
noncomputable def mulH1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E) :
    H1 D →ₗ[ℂ] H1 E :=
  Module.DirectLimit.map (fun 𝒰 : FinCover (⊤ : Opens X) => mulH1Cover f hf 𝒰)
    (fun 𝒰 𝒱 h𝒰𝒱 => by
      apply LinearMap.ext
      intro ξ
      change mulH1Cover f hf 𝒱 (resH1' D h𝒰𝒱 ξ) = resH1' E h𝒰𝒱 (mulH1Cover f hf 𝒰 ξ)
      rw [resH1'_eq_resH1 D h𝒰𝒱 (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱),
        resH1'_eq_resH1 E h𝒰𝒱 (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱)]
      exact mulH1Cover_resH1 f hf (chosenRefIdx h𝒰𝒱) (chosenRefIdx_spec h𝒰𝒱) ξ)

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
@[simp] theorem mulH1_toH1 (f : ℳ X) {D E : RS.Divisor X} (hf : MulBound f D E)
    (𝒰 : FinCover (⊤ : Opens X)) (c : H1Cover D 𝒰) :
    mulH1 f hf (toH1 D 𝒰 c) = toH1 E 𝒰 (mulH1Cover f hf 𝒰 c) :=
  Module.DirectLimit.map_apply_of _ _ c

/-! ### Algebra laws for `mulH1` -/

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- `mulH1` only depends on the function, not on the bound proof (and transports along equality
of functions). -/
theorem mulH1_congr {f g : ℳ X} (hfg : f = g) {D E : RS.Divisor X} (hf : MulBound f D E)
    (hg : MulBound g D E) (ξ : H1 D) : mulH1 f hf ξ = mulH1 g hg ξ := by
  subst hfg
  rfl

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulH1_add {f g : ℳ X} {D E : RS.Divisor X} (hf : MulBound f D E) (hg : MulBound g D E)
    (hfg : MulBound (f + g) D E) (ξ : H1 D) :
    mulH1 (f + g) hfg ξ = mulH1 f hf ξ + mulH1 g hg ξ := by
  induction ξ using H1.induction_on with
  | ih 𝒰 c =>
    simp only [mulH1_toH1]
    rw [← map_add]
    congr 1
    obtain ⟨z, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    simp only [mulH1Cover_mk]
    rw [← map_add]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_add, mulZ1_apply_coe, mulZ1_apply_coe, mulZ1_apply_coe]
    funext p
    rw [Pi.add_apply, mulC1_apply, mulC1_apply, mulC1_apply]
    apply Subtype.ext
    rw [Submodule.coe_add, mulOn_apply_coe, mulOn_apply_coe, mulOn_apply_coe, map_add, add_mul]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
theorem mulH1_smul {f : ℳ X} {D E : RS.Divisor X} (a : ℂ) (hf : MulBound f D E)
    (haf : MulBound (a • f) D E) (ξ : H1 D) :
    mulH1 (a • f) haf ξ = a • mulH1 f hf ξ := by
  induction ξ using H1.induction_on with
  | ih 𝒰 c =>
    simp only [mulH1_toH1]
    rw [← map_smul]
    congr 1
    obtain ⟨z, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    simp only [mulH1Cover_mk]
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    rw [Submodule.coe_smul, mulZ1_apply_coe, mulZ1_apply_coe]
    funext p
    rw [Pi.smul_apply, mulC1_apply, mulC1_apply]
    apply Subtype.ext
    rw [Submodule.coe_smul, mulOn_apply_coe, mulOn_apply_coe, map_smul, smul_mul_assoc]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Composition of multiplications is multiplication by the product. -/
theorem mulH1_mulH1 {f g : ℳ X} {D D' E : RS.Divisor X} (hf : MulBound f D' E)
    (hg : MulBound g D D') (hfg : MulBound (f * g) D E) (ξ : H1 D) :
    mulH1 f hf (mulH1 g hg ξ) = mulH1 (f * g) hfg ξ := by
  induction ξ using H1.induction_on with
  | ih 𝒰 c =>
    simp only [mulH1_toH1]
    congr 1
    obtain ⟨z, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    simp only [mulH1Cover_mk]
    congr 1
    apply Subtype.ext
    simp only [mulZ1_apply_coe]
    funext p
    simp only [mulC1_apply]
    apply Subtype.ext
    simp only [mulOn_apply_coe]
    rw [map_mul, mul_assoc]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication by `1` is the divisor inclusion. -/
theorem mulH1_one {D E : RS.Divisor X} (h1 : MulBound (1 : ℳ X) D E) (hDE : D ≤ E) (ξ : H1 D) :
    mulH1 (1 : ℳ X) h1 ξ = H1Incl D hDE ξ := by
  induction ξ using H1.induction_on with
  | ih 𝒰 c =>
    rw [mulH1_toH1, H1Incl_toH1]
    congr 1
    obtain ⟨z, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    rw [mulH1Cover_mk, h1CoverIncl_mk]
    congr 1
    apply Subtype.ext
    rw [mulZ1_apply_coe, LinearMap.coe_restrict_apply]
    funext p
    rw [mulC1_apply, inclC1_apply]
    apply Subtype.ext
    rw [mulOn_apply_coe, map_one, one_mul, Submodule.coe_inclusion]

omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- Multiplication absorbs a preceding divisor inclusion. -/
theorem mulH1_H1Incl {f : ℳ X} {D D' E : RS.Divisor X} (h : D ≤ D') (hf' : MulBound f D' E)
    (hf : MulBound f D E) (ξ : H1 D) :
    mulH1 f hf' (H1Incl D h ξ) = mulH1 f hf ξ := by
  induction ξ using H1.induction_on with
  | ih 𝒰 c =>
    rw [H1Incl_toH1]
    simp only [mulH1_toH1]
    congr 1
    obtain ⟨z, rfl⟩ := H1Cover.mk_surjective D 𝒰 c
    rw [h1CoverIncl_mk]
    simp only [mulH1Cover_mk]
    congr 1

end RS.Cech
