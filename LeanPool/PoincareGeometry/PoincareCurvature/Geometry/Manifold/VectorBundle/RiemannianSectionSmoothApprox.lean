/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.RiemannianSection
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.SmoothApprox

/-!
# Smooth approximation for bilinear-form section carriers

This file keeps the analytic-density bridge out of the large Ricci-flow modules.  It combines the
fiberwise smooth-approximant interface with the preferred bilinear-form finite-cover norm control
from `RiemannianSection`.
-/

@[expose] public noncomputable section

open scoped Bundle Manifold ContDiff Topology

namespace PoincareCurvature
namespace Bundle.Trivialization
namespace ContinuousSectionSpace

section PreferredBilinearSmoothApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance smoothApproxBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))
local instance smoothApproxBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
local instance smoothApproxBilWNormedAddCommGroup (x : M) : NormedAddCommGroup (BilW x) :=
  inferInstance
local instance smoothApproxBilWNormedSpace (x : M) : NormedSpace ℝ (BilW x) :=
  inferInstance
local instance smoothApproxBilWTopologicalSpace :
    TopologicalSpace (_root_.Bundle.TotalSpace BilF BilW) :=
  _root_.Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance smoothApproxBilWFiberBundle : FiberBundle BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance smoothApproxBilWVectorBundle : VectorBundle ℝ BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
/-- The inverse preferred bilinear-form trivialization pulls both arguments forward through the
underlying vector-bundle trivialization. -/
lemma trivializationAt_bilinearFormBundle_symm_apply_eq
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    (B : BilF) (u v : W x) :
    ((trivializationAt BilF BilW x0).symm x B) u v =
      B ((trivializationAt F W x0).continuousLinearMapAt ℝ x u)
        ((trivializationAt F W x0).continuousLinearMapAt ℝ x v) := by
  let e := (trivializationAt F W x0).continuousLinearEquivAt ℝ x hx
  let tb := trivializationAt BilF BilW x0
  have hxBil : x ∈ tb.baseSet := by
    simpa [tb] using hx
  have happly : (tb ⟨x, tb.symm x B⟩).2 = B := by
    exact congrArg Prod.snd (tb.apply_mk_symm hxBil B)
  have hleft :
      (tb ⟨x, tb.symm x B⟩).2 (e u) (e v) = tb.symm x B u v := by
    rw [_root_.Bundle.trivializationAt_bilinearFormBundle_apply_eq
      (F := F) (W := W) x0 x hx (tb.symm x B) (e u) (e v)]
    simpa [e] using
      congrArg₂ (fun a b : W x => tb.symm x B a b)
        (e.symm_apply_apply u) (e.symm_apply_apply v)
  have hright := congrArg (fun C : BilF => C (e u) (e v)) happly
  simpa [tb, e, Bundle.Trivialization.linearMapAt_apply, hx] using hleft.symm.trans hright

/-- The inverse preferred bilinear-form trivialization is bounded by the square of the underlying
vector-bundle trivialization bound. -/
theorem preferredBilinear_symmL_opNorm_le_of_linearMapAt_opNorm_le
    (x0 x : M) (hx : x ∈ (trivializationAt F W x0).baseSet)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ‖(trivializationAt F W x0).continuousLinearMapAt ℝ x‖ ≤ C) :
    ‖(trivializationAt BilF BilW x0).symmL ℝ x‖ ≤ C * C := by
  let S : W x →L[ℝ] F := (trivializationAt F W x0).continuousLinearMapAt ℝ x
  let A : BilF →L[ℝ] BilW x := (trivializationAt BilF BilW x0).symmL ℝ x
  have hA : ‖A‖ ≤ C * C := by
    refine ContinuousLinearMap.opNorm_le_bound A (mul_nonneg hC0 hC0) ?_
    intro B
    have hCB : 0 ≤ (C * C) * ‖B‖ := mul_nonneg (mul_nonneg hC0 hC0) (norm_nonneg B)
    refine ContinuousLinearMap.opNorm_le_bound (A B) hCB ?_
    intro u
    have hCBu : 0 ≤ ((C * C) * ‖B‖) * ‖u‖ := mul_nonneg hCB (norm_nonneg u)
    refine ContinuousLinearMap.opNorm_le_bound ((A B) u) hCBu ?_
    intro v
    have hSu : ‖S u‖ ≤ C * ‖u‖ := by
      exact (ContinuousLinearMap.le_opNorm S u).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg u))
    have hSv : ‖S v‖ ≤ C * ‖v‖ := by
      exact (ContinuousLinearMap.le_opNorm S v).trans
        (mul_le_mul_of_nonneg_right hC (norm_nonneg v))
    have hAuv : (A B) u v = B (S u) (S v) := by
      dsimp [A, S]
      rw [Bundle.Trivialization.symmL_apply (R := ℝ)
        (trivializationAt BilF BilW x0) (by simpa using hx) B]
      exact trivializationAt_bilinearFormBundle_symm_apply_eq
        (F := F) (W := W) x0 x hx B u v
    calc
      ‖(A B) u v‖ = ‖B (S u) (S v)‖ := by rw [hAuv]
      _ ≤ ‖B‖ * ‖S u‖ * ‖S v‖ :=
        ContinuousLinearMap.le_opNorm₂ B (S u) (S v)
      _ ≤ ‖B‖ * (C * ‖u‖) * (C * ‖v‖) := by
        gcongr
      _ = (((C * C) * ‖B‖) * ‖u‖) * ‖v‖ := by ring
  simpa [A] using hA

/-- Coordinate control on a preferred finite cover gives pointwise fibrewise control for
bilinear-form sections.  This is the reverse direction of the finite-cover norm bridge: it turns
local bilinear-coordinate estimates, such as local-frame RHS matrix estimates after coordinate
identification, into the fibrewise distance estimate consumed by geometric Banach-chart builders. -/
theorem preferredBilinear_fiber_dist_le_of_coord_dist_le_of_linearMapAt_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {s t : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {C K : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ C)
    (hcoord : ∀ i (x : Kc i),
      dist
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover s).1 i x)
          ((equivCompatibleCoordFamilySubmodule
            (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i))
            Kc hKc Ko hKo hKoEq hcover t).1 i x)
        ≤ K) :
    ∀ x : M, dist (s x) (t x) ≤ (C * C) * K := by
  classical
  intro x
  letI : Fintype κ := Fintype.ofFinite κ
  have hxcover : x ∈ ⋃ i, (Kc i : Set M) := by
    simp [hcover]
  rcases Set.mem_iUnion.mp hxcover with ⟨i, hxi⟩
  let xK : Kc i := ⟨x, hxi⟩
  let eCoord :=
    equivCompatibleCoordFamilySubmodule
      (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i))
      Kc hKc Ko hKo hKoEq hcover
  let tb := trivializationAt BilF BilW (x0 i)
  let A : BilF →L[ℝ] BilW x := (trivializationAt BilF BilW (x0 i)).symmL ℝ x
  have hxBil : x ∈ tb.baseSet := hKc i hxi
  have hxW : x ∈ (trivializationAt F W (x0 i)).baseSet := by
    simpa [tb] using hxBil
  have hscoord :
      (eCoord s).1 i xK =
        (trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x (s x) := by
    simpa [eCoord] using coord_apply s i xK
  have htcoord :
      (eCoord t).1 i xK =
        (trivializationAt BilF BilW (x0 i)).continuousLinearMapAt ℝ x (t x) := by
    simpa [eCoord] using coord_apply t i xK
  have hsrec : A ((eCoord s).1 i xK) = s x := by
    dsimp [A]
    rw [hscoord]
    exact (trivializationAt BilF BilW (x0 i)).symmL_continuousLinearMapAt
      (R := ℝ) hxBil (s x)
  have htrec : A ((eCoord t).1 i xK) = t x := by
    dsimp [A]
    rw [htcoord]
    exact (trivializationAt BilF BilW (x0 i)).symmL_continuousLinearMapAt
      (R := ℝ) hxBil (t x)
  have hA : ‖A‖ ≤ C * C := by
    simpa [A] using
      preferredBilinear_symmL_opNorm_le_of_linearMapAt_opNorm_le
        (F := F) (W := W) (x0 := x0 i) (x := x) hxW hC0 (hC i xK)
  calc
    dist (s x) (t x) =
        dist (A ((eCoord s).1 i xK)) (A ((eCoord t).1 i xK)) := by
          rw [hsrec, htrec]
    _ ≤ ‖A‖ * dist ((eCoord s).1 i xK) ((eCoord t).1 i xK) :=
        ContinuousLinearMap.dist_le_opNorm A ((eCoord s).1 i xK) ((eCoord t).1 i xK)
    _ ≤ (C * C) * dist ((eCoord s).1 i xK) ((eCoord t).1 i xK) :=
        mul_le_mul_of_nonneg_right hA dist_nonneg
    _ ≤ (C * C) * K :=
        mul_le_mul_of_nonneg_left (hcoord i xK) (mul_nonneg hC0 hC0)

/-- A coordinatewise Lipschitz estimate for a preferred-cover bilinear vector field gives the
fibrewise Lipschitz estimate needed before applying the finite-cover section-space norm bridge. -/
theorem preferredBilinear_forall_fiber_dist_le_of_forall_coord_dist_le_of_linearMapAt_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)}
    {A : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {C Kcoord : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ C)
    (hcoord : ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover (A s)).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover (A t)).1 i x)
          ≤ Kcoord * dist s t) :
  ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet → ∀ x : M,
      dist ((A s) x) ((A t) x) ≤ ((C * C) * Kcoord) * dist s t := by
  intro s hs t ht x
  have hfiber :=
    preferredBilinear_fiber_dist_le_of_coord_dist_le_of_linearMapAt_opNorm_le
      (M := M) (F := F) (W := W) (x0 := x0)
      (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover)
      (s := A s) (t := A t)
      (C := C) (K := Kcoord * dist s t) hC0 hC
      (fun i x => hcoord hs ht i x) x
  calc
    dist ((A s) x) ((A t) x) ≤ (C * C) * (Kcoord * dist s t) := hfiber
    _ = ((C * C) * Kcoord) * dist s t := by ring

/-- Time-parameterized version of
`preferredBilinear_forall_fiber_dist_le_of_forall_coord_dist_le_of_linearMapAt_opNorm_le`. -/
theorem preferredBilinear_forall_fiber_dist_le_family_of_forall_coord_dist_le_of_linearMapAt_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover}
    {C Kcoord : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ C)
    (hcoord : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet →
      ∀ ⦃t⦄, t ∈ stateSet → ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              (fun i => trivializationAt BilF BilW (x0 i))
              Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ Kcoord * dist s t) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A τ s) x) ((A τ t) x) ≤
        ((C * C) * Kcoord) * dist s t := by
  intro τ hτ
  exact preferredBilinear_forall_fiber_dist_le_of_forall_coord_dist_le_of_linearMapAt_opNorm_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A τ)
    (C := C) (Kcoord := Kcoord) hC0 hC
    (fun s hs t ht i x => hcoord τ hτ hs ht i x)

/-- Preferred-cover equality version of
`preferredBilinear_forall_fiber_dist_le_family_of_forall_coord_dist_le_of_linearMapAt_opNorm_le`.
This is the shape used by Ricci-DeTurck Banach-chart records, where the cover is carried as an
abstract `et` together with `het : et i = trivializationAt ...`. -/
theorem preferredBilinear_forall_fiber_dist_le_family_of_forall_coord_dist_le_of_eq_trivializationAt
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    (x0 : κ → M)
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {C Kcoord : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).continuousLinearMapAt ℝ x.1‖ ≤ C)
    (hcoord : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet →
      ∀ ⦃t⦄, t ∈ stateSet → ∀ i (x : Kc i),
        dist
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ s)).1 i x)
            ((equivCompatibleCoordFamilySubmodule
              (𝕜 := ℝ) (F := BilF) (V := BilW)
              et Kc hKc Ko hKo hKoEq hcover (A τ t)).1 i x)
          ≤ Kcoord * dist s t) :
    ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A τ s) x) ((A τ t) x) ≤
        ((C * C) * Kcoord) * dist s t := by
  have het_fun : et = fun i => trivializationAt BilF BilW (x0 i) := funext het
  subst et
  exact
    preferredBilinear_forall_fiber_dist_le_family_of_forall_coord_dist_le_of_linearMapAt_opNorm_le
      (M := M) (F := F) (W := W) (x0 := x0)
      (timeSet := timeSet) (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
      (hKoEq := hKoEq) (hcover := hcover)
      (stateSet := stateSet) (A := A)
      (C := C) (Kcoord := Kcoord) hC0 hC hcoord

/-- A local bound for the underlying vector-bundle trivialization gives the local inverse-bound
needed to smooth bilinear-form sections. -/
theorem eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
    (hbound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C) :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C := by
  intro x
  obtain ⟨C, hCpos, hCevent⟩ := hbound x
  refine ⟨C * C + 1, by nlinarith [hCpos], ?_⟩
  have hxbase : x ∈ (trivializationAt F W x).baseSet := mem_baseSet_trivializationAt F W x
  filter_upwards [hCevent, (trivializationAt F W x).open_baseSet.mem_nhds hxbase] with y hy hybase
  have hle :
      ‖(trivializationAt BilF BilW x).symmL ℝ y‖ ≤ C * C :=
    preferredBilinear_symmL_opNorm_le_of_linearMapAt_opNorm_le
      (F := F) (W := W) x y hybase hCpos.le hy.le
  exact lt_of_le_of_lt hle (by nlinarith [hCpos])

/-- Continuous preferred bilinear-form sections have smooth fiberwise approximants once the
underlying vector-bundle trivializations are locally bounded. -/
theorem exists_smooth_fiberwise_approx_preferredBilinear_of_eventually_norm_trivializationAt_lt
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    (hbound : ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C)
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η := by
  intro η hη
  have hBilBound :
      ∀ x : M, ∃ C > 0,
        ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C :=
    eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
      (F := F) (W := W) hbound
  obtain ⟨g, hg⟩ :=
    Continuous.exists_contMDiffSection_approx_of_eventually_norm_symmL_lt
      (I := I) (F := BilF) (V := BilW) (n := (2 : ℕ∞))
      hBilBound (s := (s : ∀ x : M, BilW x)) s.continuous continuous_const (fun _ => hη)
  exact ⟨g, fun x => by simpa [dist_comm] using hg x⟩

/-- Smooth fiberwise approximation of bilinear-form bundle sections upgrades to approximation in the
transported finite-cover Banach norm for preferred bilinear-form trivializations, provided the
underlying inverse vector-bundle trivializations are uniformly bounded on the cover.

This is the concrete density bridge needed downstream: it replaces an abstract Banach-norm
approximation hypothesis by a fiberwise smooth-approximant theorem plus a finite-cover coordinate
Lipschitz estimate. -/
theorem exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hsmoothApprox : ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε := by
  refine exists_dist_lt_of_forall_fiber_dist_lt_preferredBilinear_of_symmL_opNorm_le
    (M := M) (F := F) (W := W) (x0 := x0)
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover) (s := s)
    (P := fun u ↦ ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)))
    hCpos hC ?_
  intro η hη
  obtain ⟨g, hg⟩ := hsmoothApprox η hη
  let u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
    ⟨fun x ↦ g x, g.contMDiff.continuous⟩
  refine ⟨u, ?_, ?_⟩
  · simpa [u] using g.contMDiff
  · intro x
    have hdist_comm : dist (s x) (g x) = dist (g x) (s x) := dist_comm _ _
    simpa [u, hdist_comm] using hg x

/-- Symmetric targets have symmetric smooth approximants in the transported finite-cover Banach
norm whenever arbitrary smooth fiberwise approximants are available and the underlying inverse
vector-bundle trivializations are uniformly bounded on the cover. -/
theorem exists_symmetric_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
    {κ : Type*} [Finite κ] [T2Space M]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C)
    (hsmoothApprox : ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        u ∈ symmetricLocus (M := M) (F := F) (W := W)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε := by
  intro ε hε
  obtain ⟨u, hu_smooth, hudist⟩ :=
    exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
      (M := M) (F := F) (W := W) x0 s hCpos hC hsmoothApprox ε hε
  have hu_symm_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
        (_root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x)) :=
    _root_.Bundle.contMDiff_symmetrizeBilinearSection
      (W := W) (s := fun y ↦ u y) hu_smooth
  let v : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
    ⟨fun x ↦ _root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x,
      by
        change Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          (_root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x))
        exact hu_symm_smooth.continuous⟩
  have hv_symm : v ∈ symmetricLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover := by
    intro x p q
    exact _root_.Bundle.symmetrizeBilinearSection_forall_symmetric
      (W := W) (fun y ↦ u y) x p q
  have hv_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (v x)) := by
    simpa [v] using hu_symm_smooth
  have hdist_le : dist s v ≤ dist s u :=
    dist_symmetrizeBilinearSection_le_of_symmetric
      (M := M) (F := F) (W := W)
      x0 (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
      Kc hKc Ko hKo hKoEq hcover s u v hs (by
        intro x p q
        change (_root_.Bundle.symmetrizeBilinearSection
            (W := W) (fun y ↦ u y) x) p q =
          ((u x) p q + (u x) q p) / 2
        exact _root_.Bundle.symmetrizeBilinearSection_apply_apply
          (W := W) (fun y ↦ u y) x p q)
  exact ⟨v, hv_symm, hv_smooth, lt_of_le_of_lt hdist_le hudist⟩

end PreferredBilinearSmoothApprox

section PreferredBilinearRiemannianSmoothApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {W : M → Type*} [TopologicalSpace (_root_.Bundle.TotalSpace F W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, InnerProductSpace ℝ (W x)]
  [FiberBundle F W] [VectorBundle ℝ F W]

local notation "BilF" => (F →L[ℝ] F →L[ℝ] ℝ)
local notation "BilW" => _root_.Bundle.BilinearFormBundle (V := W)

local instance riemannianSmoothApproxBilFNormedAddCommGroup : NormedAddCommGroup BilF :=
  (inferInstance : NormedAddCommGroup (F →L[ℝ] F →L[ℝ] ℝ))
local instance riemannianSmoothApproxBilFNormedSpace : NormedSpace ℝ BilF :=
  (inferInstance : NormedSpace ℝ (F →L[ℝ] F →L[ℝ] ℝ))
local instance riemannianSmoothApproxBilWNormedAddCommGroup (x : M) :
    NormedAddCommGroup (BilW x) :=
  inferInstance
local instance riemannianSmoothApproxBilWNormedSpace (x : M) : NormedSpace ℝ (BilW x) :=
  inferInstance
local instance riemannianSmoothApproxBilWTopologicalSpace :
    TopologicalSpace (_root_.Bundle.TotalSpace BilF BilW) :=
  _root_.Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance riemannianSmoothApproxBilWFiberBundle : FiberBundle BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.fiberBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
local instance riemannianSmoothApproxBilWVectorBundle : VectorBundle ℝ BilF BilW :=
  _root_.Bundle.ContinuousLinearMap.vectorBundle
    (RingHom.id ℝ) F W (F →L[ℝ] ℝ) (fun x ↦ W x →L[ℝ] ℝ)
/-- A continuous Riemannian vector-bundle structure gives the local coordinate-map bounds used by
the preferred bilinear-form smooth-approximation theorem. -/
theorem eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W] :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x).continuousLinearMapAt ℝ y‖ < C := by
  intro x
  exact eventually_norm_trivializationAt_lt (F := F) (E := W) x

/-- A continuous Riemannian vector-bundle structure supplies the local inverse bounds for the
bilinear-form bundle induced by preferred trivializations. -/
theorem eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_isContinuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W] :
    ∀ x : M, ∃ C > 0,
      ∀ᶠ y in 𝓝 x, ‖(trivializationAt BilF BilW x).symmL ℝ y‖ < C :=
  eventually_norm_symmL_bilinearFormBundle_trivializationAt_lt_of_eventually_norm_trivializationAt_lt
    (F := F) (W := W)
    (eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle (F := F) (W := W))

/-- Near any point in a fixed trivialization domain, the inverse map of that fixed
trivialization is locally bounded.  The proof factors the fixed-center inverse through the
centered inverse trivialization and a continuous coordinate change. -/
theorem eventually_norm_fixed_trivializationAt_symmL_lt_of_mem_baseSet
    [IsContinuousRiemannianBundle (B := M) F W]
    {x0 x : M} (hx : x ∈ (trivializationAt F W x0).baseSet) :
    ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖(trivializationAt F W x0).symmL ℝ y‖ < C := by
  let e0 : _root_.Bundle.Trivialization F (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace F W → M) :=
    trivializationAt F W x0
  let ex : _root_.Bundle.Trivialization F (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace F W → M) :=
    trivializationAt F W x
  have hxex : x ∈ ex.baseSet := mem_baseSet_trivializationAt F W x
  obtain ⟨C₁, hC₁pos, hC₁event⟩ := eventually_norm_symmL_trivializationAt_lt (F := F) (E := W) x
  let D : ℝ := ‖(e0.coordChangeL ℝ ex x : F →L[ℝ] F)‖ + 1
  have hDpos : 0 < D := by
    dsimp [D]
    positivity
  refine ⟨C₁ * D, mul_pos hC₁pos hDpos, ?_⟩
  have hinter_mem : e0.baseSet ∩ ex.baseSet ∈ 𝓝 x :=
    Filter.inter_mem (e0.open_baseSet.mem_nhds hx) (ex.open_baseSet.mem_nhds hxex)
  have hcoord :
      ContinuousAt (fun y ↦ (e0.coordChangeL ℝ ex y : F →L[ℝ] F)) x := by
    exact ((continuousOn_coordChange (R := ℝ) (F := F) (E := W) e0 ex).continuousAt hinter_mem)
  have hcoord_event :
      ∀ᶠ y in 𝓝 x, ‖(e0.coordChangeL ℝ ex y : F →L[ℝ] F)‖ < D := by
    exact ((continuous_norm.continuousAt.comp hcoord).eventually_lt_const (lt_add_one _))
  filter_upwards [hinter_mem, hC₁event, hcoord_event] with y hy hsymm hcoordBound
  have hfactor :
      e0.symmL ℝ y = ex.symmL ℝ y ∘L (e0.coordChangeL ℝ ex y : F →L[ℝ] F) := by
    ext v
    have hcoord_eq :=
      _root_.Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change
        (R := ℝ) (e := e0) (e' := ex) (b := y) (hb := hy)
    have hcoord_apply :
        (e0.coordChangeL ℝ ex y : F →L[ℝ] F) v =
          ex.continuousLinearEquivAt ℝ y hy.2 (e0.symmL ℝ y v) := by
      rw [e0.symmL_apply hy.1]
      rw [← hcoord_eq]
      simp
    rw [ContinuousLinearMap.comp_apply, hcoord_apply]
    have h := _root_.Bundle.Trivialization.symmL_continuousLinearMapAt
      (e := ex) (R := ℝ) hy.2 (e0.symmL ℝ y v)
    simpa [_root_.Bundle.Trivialization.coe_continuousLinearEquivAt_eq (e := ex) hy.2] using h.symm
  calc
    ‖e0.symmL ℝ y‖ = ‖ex.symmL ℝ y ∘L (e0.coordChangeL ℝ ex y : F →L[ℝ] F)‖ := by
      rw [hfactor]
    _ ≤ ‖ex.symmL ℝ y‖ * ‖(e0.coordChangeL ℝ ex y : F →L[ℝ] F)‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ < C₁ * D := mul_lt_mul'' hsymm hcoordBound (norm_nonneg _) (norm_nonneg _)

/-- On a compact subset of a fixed trivialization domain in a continuous Riemannian vector bundle,
the inverse fixed trivialization has a uniform operator-norm bound. -/
theorem exists_uniform_norm_fixed_trivializationAt_symmL_le_of_compact
    [IsContinuousRiemannianBundle (B := M) F W]
    {x0 : M} (K : TopologicalSpace.Compacts M)
    (hK : (K : Set M) ⊆ (trivializationAt F W x0).baseSet) :
    ∃ C > 0, ∀ x : K, ‖(trivializationAt F W x0).symmL ℝ x.1‖ ≤ C := by
  classical
  let e0 : _root_.Bundle.Trivialization F (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace F W → M) :=
    trivializationAt F W x0
  have hlocal : ∀ x ∈ (K : Set M), ∃ C > 0, ∀ᶠ y in 𝓝 x, ‖e0.symmL ℝ y‖ < C := by
    intro x hxK
    simpa [e0] using
      eventually_norm_fixed_trivializationAt_symmL_lt_of_mem_baseSet
        (F := F) (W := W) (x0 := x0) (x := x) (hK hxK)
  have hlocalK : ∀ x : K, ∃ C > 0, ∀ᶠ y in 𝓝 (x : M), ‖e0.symmL ℝ y‖ < C := by
    intro x
    exact hlocal x.1 x.2
  choose C hCpos hCevent using hlocalK
  let U : ∀ x ∈ (K : Set M), Set M := fun x hx ↦ {y | ‖e0.symmL ℝ y‖ < C ⟨x, hx⟩}
  have hU : ∀ x (hx : x ∈ (K : Set M)), U x hx ∈ 𝓝 x := by
    intro x hxK
    change ∀ᶠ y in 𝓝 x, ‖e0.symmL ℝ y‖ < C ⟨x, hxK⟩
    exact hCevent ⟨x, hxK⟩
  rcases K.isCompact.elim_nhds_subcover' U hU with ⟨t, htcover⟩
  refine ⟨(∑ x ∈ t, C x) + 1, ?_, ?_⟩
  · have hsum_nonneg : 0 ≤ ∑ x ∈ t, C x :=
      Finset.sum_nonneg fun x _hxmem ↦ le_of_lt (hCpos x)
    linarith
  · intro x
    rcases Set.mem_iUnion₂.mp (htcover x.2) with ⟨y, hymem, hyU⟩
    have hyle : C y ≤ ∑ z ∈ t, C z :=
      Finset.single_le_sum
        (fun z _hzmem ↦ le_of_lt (hCpos z)) hymem
    have hxlt : ‖e0.symmL ℝ x.1‖ < C y := by
      simpa [U] using hyU
    exact le_trans (le_of_lt hxlt) (by linarith)

/-- A finite family of compact subsets of preferred trivialization domains admits one uniform
operator-norm bound for all inverse preferred trivializations.  This is the finite-cover
compactness input used by both smooth-density and finite-cover Lipschitz handoffs. -/
theorem exists_uniform_norm_preferred_trivializationAt_symmL_le_of_finite_compact_cover
    [IsContinuousRiemannianBundle (B := M) F W]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    (hKc : ∀ i, (Kc i : Set M) ⊆ (trivializationAt F W (x0 i)).baseSet) :
    ∃ C > 0, ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C := by
  classical
  letI : Fintype κ := Fintype.ofFinite κ
  choose C hCpos hC using fun i ↦
    exists_uniform_norm_fixed_trivializationAt_symmL_le_of_compact
      (F := F) (W := W) (x0 := x0 i) (Kc i) (hKc i)
  let Csum : ℝ := (∑ i : κ, C i) + 1
  have hCsum_pos : 0 < Csum := by
    have hsum_nonneg : 0 ≤ ∑ i : κ, C i :=
      Finset.sum_nonneg fun i _hi ↦ le_of_lt (hCpos i)
    dsimp [Csum]
    linarith
  have hCsum_bound : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ Csum := by
    intro i x
    have hi_le : C i ≤ ∑ j : κ, C j :=
      Finset.single_le_sum (fun j _hj ↦ le_of_lt (hCpos j)) (Finset.mem_univ i)
    exact (hC i x).trans (by dsimp [Csum]; linarith)
  exact ⟨Csum, hCsum_pos, hCsum_bound⟩

/-- In a continuous Riemannian vector bundle, a time-family of preferred bilinear-form section
fields with a fibrewise Lipschitz estimate has some finite-cover section-space Lipschitz constant.
This combines the compact finite-cover inverse-trivialization bound with the preferred-bilinear
Lipschitz handoff in the `et`/`het` cover shape used by chart records. -/
theorem exists_preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le
    [IsContinuousRiemannianBundle (B := M) F W]
    {κ : Type*} [Finite κ] [T2Space M]
    {τ : Type*} {timeSet : Set τ}
    (x0 : κ → M)
    {et : κ → _root_.Bundle.Trivialization BilF
      (_root_.Bundle.TotalSpace.proj : _root_.Bundle.TotalSpace BilF BilW → M)}
    [∀ i, MemTrivializationAtlas (et i)]
    (het : ∀ i, et i = trivializationAt BilF BilW (x0 i))
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆ (et i).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    {stateSet : Set (ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      et Kc hKc Ko hKo hKoEq hcover)}
    {A : τ →
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover →
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          et Kc hKc Ko hKo hKoEq hcover}
    {K : NNReal}
    (hfiber : ∀ τ, τ ∈ timeSet → ∀ ⦃s⦄, s ∈ stateSet → ∀ ⦃t⦄, t ∈ stateSet →
      ∀ x : M, dist ((A τ s) x) ((A τ t) x) ≤ (K : ℝ) * dist s t) :
    ∃ Ksection : NNReal, ∀ τ ∈ timeSet, LipschitzOnWith Ksection (A τ) stateSet := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_uniform_norm_preferred_trivializationAt_symmL_le_of_finite_compact_cover
      (F := F) (W := W) (x0 := x0)
      (Kc := Kc) (fun i x hx => by simpa [het i] using hKc i hx)
  let Ksection : NNReal :=
    ⟨(C * C) * (K : ℝ), mul_nonneg (mul_nonneg hCpos.le hCpos.le) (NNReal.coe_nonneg K)⟩
  refine ⟨Ksection, ?_⟩
  change ∀ τ ∈ timeSet, LipschitzOnWith Ksection (A τ) stateSet
  exact preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le_of_eq_trivializationAt
    (M := M) (F := F) (W := W) (x0 := x0) (timeSet := timeSet)
    (et := et) het
    (Kc := Kc) (hKc := hKc) (Ko := Ko) (hKo := hKo)
    (hKoEq := hKoEq) (hcover := hcover)
    (stateSet := stateSet) (A := A)
    (C := C) hCpos.le hC (K := K) hfiber

/-- Continuous preferred bilinear-form sections have smooth fiberwise approximants in a continuous
Riemannian vector bundle.  This discharges the local trivialization-boundedness hypothesis from the
Riemannian vector-bundle estimate. -/
theorem exists_smooth_fiberwise_approx_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ η > 0,
      ∃ g : Cₛ^(2 : ℕ∞)⟮I; BilF, BilW⟯,
        ∀ x : M, dist (s x) (g x) < η :=
  exists_smooth_fiberwise_approx_preferredBilinear_of_eventually_norm_trivializationAt_lt
    (F := F) (W := W)
    (eventually_norm_trivializationAt_lt_of_isContinuousRiemannianBundle (F := F) (W := W))
    x0 s

/-- Smooth approximation in the transported finite-cover Banach norm for preferred bilinear-form
trivializations in a continuous Riemannian vector bundle.  The local coordinate-map boundedness
hypothesis is discharged internally by the Riemannian vector-bundle estimate; only the finite-cover
inverse bound remains as explicit input. -/
theorem exists_dist_lt_preferredBilinear_of_continuousRiemannianBundle_and_symmL_opNorm_le
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {C : ℝ} (hCpos : 0 < C)
    (hC : ∀ i (x : Kc i),
      ‖(trivializationAt F W (x0 i)).symmL ℝ x.1‖ ≤ C) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε :=
  exists_dist_lt_of_smooth_fiberwise_approx_preferredBilinear_of_symmL_opNorm_le
    (F := F) (W := W) x0 s hCpos hC
    (exists_smooth_fiberwise_approx_preferredBilinear_of_continuousRiemannianBundle
      (F := F) (W := W) x0 s)

/-- Smooth approximation in the transported finite-cover Banach norm for preferred bilinear-form
trivializations in a continuous Riemannian vector bundle.  Both analytic boundedness inputs used by
the older preferred-cover theorem are discharged here: local coordinate-map boundedness follows from
the Riemannian bundle estimate, and the finite-cover inverse bound follows from compactness of the
cover pieces inside their fixed trivialization domains. -/
theorem exists_dist_lt_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε := by
  obtain ⟨Csum, hCsum_pos, hCsum_bound⟩ :=
    exists_uniform_norm_preferred_trivializationAt_symmL_le_of_finite_compact_cover
      (F := F) (W := W) (x0 := x0)
      (Kc := Kc) (fun i x hx => by simpa using hKc i hx)
  exact exists_dist_lt_preferredBilinear_of_continuousRiemannianBundle_and_symmL_opNorm_le
    (F := F) (W := W) x0 s hCsum_pos hCsum_bound

/-- Symmetric continuous preferred bilinear-form sections have symmetric smooth approximants in the
transported finite-cover Banach norm for continuous Riemannian vector bundles.

The proof first uses the Riemannian-bundle smooth-density theorem to find an arbitrary smooth
bilinear-form approximant, then fiberwise symmetrizes it. The finite-cover symmetrization estimate
shows that this does not increase distance to the symmetric target. -/
theorem exists_symmetric_dist_lt_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    ∀ ε > 0,
      ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
        u ∈ symmetricLocus (M := M) (F := F) (W := W)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
        ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
          (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
        dist s u < ε := by
  intro ε hε
  obtain ⟨u, hu_smooth, hudist⟩ :=
    exists_dist_lt_preferredBilinear_of_continuousRiemannianBundle
      (E := E) (H := H) (I := I) (M := M) (F := F) (W := W) x0 s ε hε
  have hu_symm_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
        (_root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x)) :=
    _root_.Bundle.contMDiff_symmetrizeBilinearSection
      (W := W) (s := fun y ↦ u y) hu_smooth
  let v : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover :=
    ⟨fun x ↦ _root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x,
      by
        change Continuous (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x
          (_root_.Bundle.symmetrizeBilinearSection (W := W) (fun y ↦ u y) x))
        exact hu_symm_smooth.continuous⟩
  have hv_symm : v ∈ symmetricLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover := by
    intro x p q
    exact _root_.Bundle.symmetrizeBilinearSection_forall_symmetric
      (W := W) (fun y ↦ u y) x p q
  have hv_smooth : ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
      (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (v x)) := by
    simpa [v] using hu_symm_smooth
  have hdist_le : dist s v ≤ dist s u :=
    dist_symmetrizeBilinearSection_le_of_symmetric
      (M := M) (F := F) (W := W)
      x0 (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
      Kc hKc Ko hKo hKoEq hcover s u v hs (by
        intro x p q
        change (_root_.Bundle.symmetrizeBilinearSection
            (W := W) (fun y ↦ u y) x) p q =
          ((u x) p q + (u x) q p) / 2
        exact _root_.Bundle.symmetrizeBilinearSection_apply_apply
          (W := W) (fun y ↦ u y) x p q)
  exact ⟨v, hv_symm, hv_smooth, lt_of_le_of_lt hdist_le hudist⟩

/-- Quantitative smooth-SPD density at continuous symmetric positive-definite sections in continuous
Riemannian vector bundles.

Symmetric smooth approximants are produced by the previous theorem, while positivity is kept by
approximating inside the open positive-definite locus. -/
theorem exists_smooth_spd_dist_lt_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
      u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
      dist s u < ε := by
  obtain ⟨δ, hδpos, hδsubset⟩ :=
    exists_dist_lt_subset_positiveDefiniteLocus
      (M := M) (F := F) (W := W)
      x0 (fun i ↦ trivializationAt BilF BilW (x0 i)) (fun _ ↦ rfl)
      Kc hKc Ko hKo hKoEq hcover hs.2
  let η : ℝ := min ε δ
  have hηpos : 0 < η := lt_min hε hδpos
  obtain ⟨u, hu_symm, hu_smooth, hudist⟩ :=
    exists_symmetric_dist_lt_preferredBilinear_of_continuousRiemannianBundle
      (E := E) (H := H) (I := I) (M := M) (F := F) (W := W)
      x0 s hs.1 η hηpos
  have hudistε : dist s u < ε := lt_of_lt_of_le hudist (min_le_left ε δ)
  have hudistδ : dist u s < δ := by
    rw [dist_comm]
    exact lt_of_lt_of_le hudist (min_le_right ε δ)
  exact ⟨u, ⟨hu_symm, hδsubset u hudistδ⟩, hu_smooth, hudistε⟩

/-- Continuous Riemannian vector bundles have smooth symmetric positive-definite sections dense at
every continuous symmetric positive-definite section in the preferred finite-cover norm.

This is the generic vector-bundle closure theorem behind the Ricci-DeTurck metric-cone density
route. -/
theorem mem_closure_smooth_spd_preferredBilinear_of_continuousRiemannianBundle
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (hs : s ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) :
    s ∈ closure
      ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover |
          u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
          ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
            (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) := by
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  obtain ⟨u, hu_spd, hu_smooth, hudist⟩ :=
    exists_smooth_spd_dist_lt_preferredBilinear_of_continuousRiemannianBundle
      (E := E) (H := H) (I := I) (M := M) (F := F) (W := W) x0 s hs hε
  exact ⟨u, ⟨hu_spd, hu_smooth⟩, hudist⟩

/-- A continuous Riemannian metric, viewed as a preferred finite-cover bilinear-form section, lies in
the closure of smooth symmetric positive-definite sections. -/
theorem _root_.Bundle.ContinuousRiemannianMetric.mem_closure_smooth_spd_preferredBilinear
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) ∈
      closure
        ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover |
            u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
              (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
            ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
              (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) :=
  mem_closure_smooth_spd_preferredBilinear_of_continuousRiemannianBundle
    (E := E) (H := H) (I := I) (M := M) (F := F) (W := W) x0
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
    (mem_symmetricPositiveDefiniteLocus_of_continuousRiemannianMetric
      (M := M) (F := F) (W := W)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover g)

/-- Quantitative form of metric-level smooth-SPD density: for every radius in the preferred
finite-cover Banach norm, a bundled continuous Riemannian metric has a smooth symmetric
positive-definite bilinear-form section inside that radius. -/
theorem _root_.Bundle.ContinuousRiemannianMetric.exists_smooth_spd_dist_lt_preferredBilinear
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover,
      u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
      ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
        (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x)) ∧
      dist
        (⟨g.toSection, g.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
        u < ε := by
  have hclosure :
      (⟨g.toSection, g.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) ∈
        closure
          ({u : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover |
              u ∈ symmetricPositiveDefiniteLocus (M := M) (F := F) (W := W)
                (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover ∧
              ContMDiff I (I.prod 𝓘(ℝ, BilF)) 2
                (fun x ↦ _root_.Bundle.TotalSpace.mk' BilF x (u x))}) :=
    g.mem_closure_smooth_spd_preferredBilinear
      (E := E) (H := H) (I := I) (M := M) (W := W) x0
  rw [Metric.mem_closure_iff] at hclosure
  obtain ⟨u, hu, hudist⟩ := hclosure ε hε
  exact ⟨u, hu.1, hu.2, hudist⟩

/-- Bundled metric-density form: every continuous Riemannian metric admits a bundled `C²`
Riemannian metric approximation in any positive preferred finite-cover radius. -/
theorem _root_.Bundle.ContinuousRiemannianMetric.exists_contMDiffRiemannianMetric_dist_lt_preferredBilinear
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g' : _root_.Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞) F W,
      dist
        (⟨g.toSection, g.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover)
        (⟨g'.toSection, g'.continuous_toSection⟩ :
          ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
            (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) < ε := by
  obtain ⟨u, hu_spd, hu_smooth, hudist⟩ :=
    g.exists_smooth_spd_dist_lt_preferredBilinear
      (E := E) (H := H) (I := I) (M := M) (W := W) x0 hε
  let g' : _root_.Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞) F W :=
    _root_.Bundle.ContMDiffRiemannianMetric.ofContinuousSectionSpace
      (M := M) (F := F) (W := W) (I₀ := I)
      (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover
      u hu_spd hu_smooth
  refine ⟨g', ?_⟩
  have hsection :
      (⟨g'.toSection, g'.continuous_toSection⟩ :
        ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) = u := by
    ext x
    rfl
  simpa [hsection] using hudist

/-- Smooth Riemannian metrics are dense, in the preferred finite-cover section norm, at every
continuous Riemannian metric.  This is the bundled metric-locus closure form of the smooth-SPD
density theorem. -/
theorem _root_.Bundle.ContinuousRiemannianMetric.mem_closure_contMDiffRiemannianMetric_preferredBilinear
    [IsContinuousRiemannianBundle (B := M) F W]
    [FiniteDimensional ℝ E] [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
    [SecondCountableTopology H] [ContMDiffVectorBundle (2 : ℕ∞) BilF BilW I]
    [FiniteDimensional ℝ F] [Nontrivial F]
    {κ : Type*} [Finite κ]
    (x0 : κ → M)
    {Kc : κ → TopologicalSpace.Compacts M}
    {hKc : ∀ i, (Kc i : Set M) ⊆
      (trivializationAt BilF BilW (x0 i)).baseSet}
    {Ko : κ → κ → TopologicalSpace.Compacts M}
    {hKo : ∀ i j, (Ko i j : Set M) ⊆ (Kc i : Set M) ∩ (Kc j : Set M)}
    {hKoEq : ∀ i j, (Ko i j : Set M) = (Kc i : Set M) ∩ (Kc j : Set M)}
    {hcover : (⋃ i, (Kc i : Set M)) = Set.univ}
    (g : _root_.Bundle.ContinuousRiemannianMetric F W) :
    (⟨g.toSection, g.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover) ∈
      closure
        ({s : ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
          (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover |
            ∃ g' : _root_.Bundle.ContMDiffRiemannianMetric I (2 : ℕ∞) F W,
              s =
                (⟨g'.toSection, g'.continuous_toSection⟩ :
                  ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
                    (fun i => trivializationAt BilF BilW (x0 i))
                    Kc hKc Ko hKo hKoEq hcover)}) := by
  refine Metric.mem_closure_iff.2 ?_
  intro ε hε
  obtain ⟨g', hgdist⟩ :=
    g.exists_contMDiffRiemannianMetric_dist_lt_preferredBilinear
      (E := E) (H := H) (I := I) (M := M) (W := W) x0 hε
  refine ⟨(⟨g'.toSection, g'.continuous_toSection⟩ :
      ContinuousSectionSpace (𝕜 := ℝ) (F := BilF) (V := BilW)
        (fun i => trivializationAt BilF BilW (x0 i)) Kc hKc Ko hKo hKoEq hcover), ?_, hgdist⟩
  exact ⟨g', rfl⟩

end PreferredBilinearRiemannianSmoothApprox

end ContinuousSectionSpace
end Bundle.Trivialization
end PoincareCurvature
