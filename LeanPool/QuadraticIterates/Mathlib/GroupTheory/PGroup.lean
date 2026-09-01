/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.Perm.DomMulAct

/-!
# Fixed points of 2-groups on 𝔽₂-modules

A 2-group acting on a nontrivial finite `𝔽₂`-module has a nonzero fixed vector; under a
transitive action on the coordinates, an invariant nonzero submodule of `𝔽₂^ι` contains the
all-ones vector.

Auxiliary material for the formalization of M. Stoll, *Galois groups over ℚ of some iterated
polynomials*, Arch. Math. 59 (1992), 239-244; upstreaming candidates for Mathlib.

## Implementation notes

The eventual Mathlib home of `fixed_points_nontrivial` and `invariant_submodule_all_ones` is
not obvious (they sit between `GroupTheory.PGroup`, `RepresentationTheory`, and the linear-algebra
`Module` files); they are grouped here for now and will be placed during upstreaming.
-/

/-- A `2`-group acting `ZMod 2`-linearly on a nontrivial finite `𝔽₂`-module fixes some nonzero
vector. -/
theorem fixed_points_nontrivial {G : Type*} [Group G] (hG : IsPGroup 2 G)
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] [Nontrivial M]
    [DistribMulAction G M] :
    ∃ m : M, m ≠ 0 ∧ m ∈ MulAction.fixedPoints G M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card M = 2 ^ Module.finrank (ZMod 2) M := by
    simpa using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M)
  have hdvd : 2 ∣ Nat.card M := hcard ▸ dvd_pow_self 2 Module.finrank_pos.ne'
  have hcong := IsPGroup.card_modEq_card_fixedPoints hG M (p := 2)
  have hdvdfix : 2 ∣ Nat.card ↑(MulAction.fixedPoints G M) :=
    Nat.modEq_zero_iff_dvd.mp (((Nat.modEq_zero_iff_dvd.mpr hdvd).symm.trans hcong).symm)
  have : Finite ↑(MulAction.fixedPoints G M) := Set.Finite.to_subtype (Set.toFinite _)
  have hcardpos : 0 < Nat.card ↑(MulAction.fixedPoints G M) :=
    Nat.card_pos_iff.mpr ⟨⟨0, smul_zero⟩, inferInstance⟩
  have hnt : Nontrivial ↑(MulAction.fixedPoints G M) :=
    Finite.one_lt_card_iff_nontrivial.mp (by lia)
  obtain ⟨x, y, hxy⟩ := hnt
  by_cases hx : (x : M) = 0
  · exact ⟨(y : M), fun hy0 ↦ hxy (by ext; rw [hx, hy0]), y.2⟩
  · exact ⟨(x : M), hx, x.2⟩

/-- A `ZMod 2`-valued function on a pretransitive `G`-set that is `G`-invariant is constant,
hence `0` or `1`. -/
private theorem transitive_invariant {G : Type*} [Group G] {ι : Type*} [MulAction G ι]
    [MulAction.IsPretransitive G ι] [Nonempty ι] (v : ι → ZMod 2)
    (hv : ∀ (g : G) (i : ι), v (g • i) = v i) :
    v = 0 ∨ v = 1 := by
  obtain ⟨i₀⟩ := (inferInstance : Nonempty ι)
  have hconst : ∀ i, v i = v i₀ := fun i ↦
    (MulAction.exists_smul_eq G i₀ i).elim fun g hg ↦ hg ▸ hv g i₀
  refine (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (v i₀) |>.imp ?_ ?_ <;>
    exact fun h ↦ funext fun i ↦ by simp [hconst i, h]

/-- Under a finite `2`-group `G` acting on `ι`, a nonzero `G`-invariant `𝔽₂`-subspace `V` of
`ι → 𝔽₂` contains a nonzero vector that is constant along `G`-orbits. This applies
`fixed_points_nontrivial` to `V` under the `Gᵈᵐᵃ`-action `g • v := v ∘ (g⁻¹ • ·)`. -/
private theorem exists_ne_zero_orbit_const_mem {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {ι : Type*} [Finite ι] [MulAction G ι] (V : Submodule (ZMod 2) (ι → ZMod 2))
    (hV : ∀ (g : G) (v : ι → ZMod 2), v ∈ V → (fun i ↦ v (g⁻¹ • i)) ∈ V) (hVne : V ≠ ⊥) :
    ∃ w : ι → ZMod 2, w ∈ V ∧ w ≠ 0 ∧ ∀ (g : G) (i : ι), w (g • i) = w i := by
  have hVinv : ∀ (g : Gᵈᵐᵃ) (v : ι → ZMod 2), v ∈ V → g • v ∈ V := by
    intro g v hv
    have hkey : (g • v) = (fun i ↦ v ((DomMulAct.mk.symm g)⁻¹⁻¹ • i)) := by
      funext i; rw [DomMulAct.smul_apply]; simp
    exact hkey ▸ hV (DomMulAct.mk.symm g)⁻¹ v hv
  let smulV : SMul Gᵈᵐᵃ ↥V := ⟨fun g v ↦ ⟨g • (v : ι → ZMod 2), hVinv g v v.2⟩⟩
  have hsmulV_coe (g : Gᵈᵐᵃ) (v : ↥V) : ((g • v : ↥V) : ι → ZMod 2) = g • (v : ι → ZMod 2) := rfl
  let mulActV : MulAction Gᵈᵐᵃ ↥V :=
    { smulV with
      one_smul := fun v ↦ by ext i; simp [hsmulV_coe]
      mul_smul := fun g h v ↦ by ext i; simp [hsmulV_coe, mul_smul] }
  let distribV : DistribMulAction Gᵈᵐᵃ ↥V :=
    { mulActV with
      smul_zero := fun g ↦ by ext i; simp [hsmulV_coe]
      smul_add := fun g x y ↦ by ext i; simp [hsmulV_coe, Submodule.coe_add, smul_add] }
  have hcomm : SMulCommClass Gᵈᵐᵃ (ZMod 2) ↥V :=
    ⟨fun g r v ↦ by ext i; simp [hsmulV_coe, smul_comm]⟩
  have hntV : Nontrivial ↥V := Submodule.nontrivial_iff_ne_bot.mpr hVne
  have hGdma : IsPGroup 2 Gᵈᵐᵃ := by
    obtain ⟨k, hk⟩ := hG.exists_card_dvd_pow
    exact .of_card_dvd_pow (by rwa [Nat.card_congr DomMulAct.mk.symm])
  obtain ⟨w, hwne, hwfix⟩ := fixed_points_nontrivial (G := Gᵈᵐᵃ) hGdma (M := ↥V)
  exact ⟨(w : ι → ZMod 2), w.2, fun h0 ↦ hwne (Subtype.ext h0),
    fun g i ↦ congrFun (congrArg (fun x : ↥V ↦ (x : ι → ZMod 2)) (hwfix (DomMulAct.mk g))) i⟩

/-- A nonzero `G`-invariant `𝔽₂`-subspace of `ι → 𝔽₂`, where the finite `2`-group `G` acts
pretransitively on `ι`, contains the all-ones vector. -/
theorem invariant_submodule_all_ones {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {ι : Type*} [Finite ι] [Nonempty ι] [MulAction G ι] [MulAction.IsPretransitive G ι]
    (V : Submodule (ZMod 2) (ι → ZMod 2))
    (hV : ∀ (g : G) (v : ι → ZMod 2), v ∈ V → (fun i ↦ v (g⁻¹ • i)) ∈ V) (hVne : V ≠ ⊥) :
    (fun _ ↦ 1) ∈ V := by
  obtain ⟨w, hwV, hwne, hwinv⟩ := exists_ne_zero_orbit_const_mem hG V hV hVne
  rcases transitive_invariant (G := G) w hwinv with h0 | h1
  · exact absurd h0 hwne
  · exact (show w = (fun _ ↦ 1) by ext i; rw [h1]; rfl) ▸ hwV
