/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.Core5
public import LeanPool.HopfProblem.Uniformization.SpecialPeriods9
import all LeanPool.HopfProblem.Lattice.Core1
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.Toric.ToricSpace1
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Uniformization.CuspUniformization1
import all LeanPool.HopfProblem.Foundations.Core3
import all LeanPool.HopfProblem.Lattice.Core2
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods1
import all LeanPool.HopfProblem.Threefold.SpecialPeriods2
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods4
import all LeanPool.HopfProblem.PeriodFamily.Core1
import all LeanPool.HopfProblem.PeriodFamily.Core2
import all LeanPool.HopfProblem.Threefold.SpecialPeriods6
import all LeanPool.HopfProblem.HomologyOfX.ThreefoldGluing1
import all LeanPool.HopfProblem.Uniformization.TriangleUniformizationGluing
import all LeanPool.HopfProblem.Threefold.SpecialPeriods7
import all LeanPool.HopfProblem.Threefold.SpecialPeriods8
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Foundations.Core5
import all LeanPool.HopfProblem.Uniformization.SpecialPeriods9

/-!
# Hopf problem: pi 1 · twist group

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

private def LatticeCuspNormalClosure.uHat : Lattice :=
  ![0, 1, 0, 0]

private def LatticeCuspNormalClosure.wHat : Lattice :=
  ![0, 0, 1, 0]

private theorem LatticeCuspNormalClosure.first_matrix_wHat : A₁ *ᵥ wHat = uHat - wHat := by decide

private theorem LatticeCuspNormalClosure.image_wHat_eq_one {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G)
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) :
    φ (Multiplicative.ofAdd wHat) = 1 :=
  hc wHat rfl rfl

private theorem LatticeCuspNormalClosure.image_uHat_eq_one {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) :
    φ (Multiplicative.ofAdd uHat) = 1 := by
  have h := hx wHat
  rw [first_matrix_wHat, ofAdd_sub, map_div, image_wHat_eq_one φ hc] at h
  simpa only [mul_one, mul_inv_cancel, div_one] using h.symm

private theorem LatticeCuspNormalClosure.image_eq_one_of_gamma_eq_zero {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) (v : Lattice)
    (hv : γ v = 0) : φ (Multiplicative.ofAdd v) = 1 := by
  have hv₀ : v 0 = 0 := hv
  have hrest := hc (v - v 1 • uHat) (by simp [uHat, hv₀]) (by simp [uHat])
  have hu : φ (Multiplicative.ofAdd (v 1 • uHat)) = 1 := by
    rw [ofAdd_zsmul, map_zpow, image_uHat_eq_one φ x hx hc, one_zpow]
  simpa only [ofAdd_sub, map_div, hu, div_one] using hrest

private theorem LatticeCuspNormalClosure.image_eq_zpow_gamma {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) (v : Lattice) :
    φ (Multiplicative.ofAdd v) = φ (Multiplicative.ofAdd ε) ^ γ v := by
  have hk : γ (v - γ v • ε) = 0 := by simp [γ, ε]
  have h := image_eq_one_of_gamma_eq_zero φ x hx hc (v - γ v • ε) hk
  rw [ofAdd_sub, map_div, ofAdd_zsmul, map_zpow] at h
  exact div_eq_one.mp h

private theorem LatticeCuspNormalClosure.image_epsilon_prime_eq {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) :
    φ (Multiplicative.ofAdd ε') = φ (Multiplicative.ofAdd ε) := by
  simpa only [γ_ε', zpow_one] using image_eq_zpow_gamma φ x hx hc ε'

private theorem LatticeCuspNormalClosure.image_epsilon_commute_first {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v))) :
    Commute (φ (Multiplicative.ofAdd ε)) x := by
  have h := hx ε
  rw [A₁_fixes_ε] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

private theorem LatticeCuspNormalClosure.image_epsilon_commute_second {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x y : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hy :
      ∀ v : Lattice, y * φ (Multiplicative.ofAdd v) * y⁻¹ = φ (Multiplicative.ofAdd (A₂ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1) :
    Commute (φ (Multiplicative.ofAdd ε)) y := by
  have h := hy ε'
  rw [A₂_fixes_ε', image_epsilon_prime_eq φ x hx hc] at h
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

private theorem LatticeCuspNormalClosure.image_epsilon_commute_lattice {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (v : Multiplicative Lattice) :
    Commute (φ (Multiplicative.ofAdd ε)) (φ v) := by
  change φ (Multiplicative.ofAdd ε) * φ v = φ v * φ (Multiplicative.ofAdd ε)
  rw [← map_mul, ← map_mul, mul_comm]

private theorem LatticeCuspNormalClosure.image_epsilon_mem_center_of_hom_ext {G : Type*} [Group G]
    (φ : Multiplicative Lattice →* G) (x y : G)
    (hx :
      ∀ v : Lattice, x * φ (Multiplicative.ofAdd v) * x⁻¹ = φ (Multiplicative.ofAdd (A₁ *ᵥ v)))
    (hy :
      ∀ v : Lattice, y * φ (Multiplicative.ofAdd v) * y⁻¹ = φ (Multiplicative.ofAdd (A₂ *ᵥ v)))
    (hc : ∀ v : Lattice, v 0 = 0 → v 1 = 0 → φ (Multiplicative.ofAdd v) = 1)
    (hext :
      ∀ f g : G →* G,
        (∀ v : Multiplicative Lattice, f (φ v) = g (φ v)) → f x = g x → f y = g y → f = g) :
    φ (Multiplicative.ofAdd ε) ∈ Subgroup.center G := by
  let a := φ (Multiplicative.ofAdd ε)
  have hconj : (MulAut.conj a).toMonoidHom = MonoidHom.id G := by
    apply hext
    · intro v
      change a * φ v * a⁻¹ = φ v
      rw [(image_epsilon_commute_lattice φ v).eq, mul_inv_cancel_right]
    · change a * x * a⁻¹ = x
      rw [(image_epsilon_commute_first φ x hx).eq, mul_inv_cancel_right]
    · change a * y * a⁻¹ = y
      rw [(image_epsilon_commute_second φ x y hx hy hc).eq, mul_inv_cancel_right]
  apply Subgroup.mem_center_iff.mpr
  intro g
  have h : a * g * a⁻¹ = g := DFunLike.congr_fun hconj g
  exact ((mul_inv_eq_iff_eq_mul).mp h).symm

private abbrev TwistGroup (a b d : ℤ) :=
  PresentedGroup (Set.range (twistRelators a b d))

private def TwistGroup.c (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 0

private def TwistGroup.x (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 1

private def TwistGroup.y (a b d : ℤ) : TwistGroup a b d :=
  PresentedGroup.of 2

private theorem TwistGroup.c_commute_x (a b d : ℤ) : Commute (c a b d) (x a b d) := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨0, rfl⟩)

private theorem TwistGroup.x_mul_y (a b d : ℤ) : x a b d * y a b d = c a b d ^ a := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨2, rfl⟩)

private theorem TwistGroup.x_cube (a b d : ℤ) : x a b d ^ 3 = c a b d ^ b := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨3, rfl⟩)

private theorem TwistGroup.y_fourth (a b d : ℤ) : y a b d ^ 4 = c a b d ^ d := by
  exact PresentedGroup.mk_eq_mk_of_mul_inv_mem (Set.mem_range.mpr ⟨4, rfl⟩)

private theorem TwistGroup.x_commute_y (a b d : ℤ) : Commute (x a b d) (y a b d) := by
  change x a b d * y a b d = y a b d * x a b d
  apply mul_left_cancel (a := x a b d)
  calc
    x a b d * (x a b d * y a b d) = x a b d * c a b d ^ a := by rw [x_mul_y]
    _ = c a b d ^ a * x a b d := ((c_commute_x a b d).symm.zpow_right a).eq
    _ = x a b d * (y a b d * x a b d) := by rw [← x_mul_y, mul_assoc]

private theorem TwistGroup.x_fourth (a b d : ℤ) : x a b d ^ 4 = c a b d ^ (4 * a - d) := by
  calc
    x a b d ^ 4 = (x a b d * y a b d) ^ 4 * (y a b d ^ 4)⁻¹ := by
      rw [(x_commute_y a b d).mul_pow]; group
    _ = (c a b d ^ a) ^ 4 * (c a b d ^ d)⁻¹ := by rw [x_mul_y, y_fourth]
    _ = c a b d ^ (4 * a - d) := by
      rw [← zpow_natCast _ 4, ← zpow_mul, ← zpow_sub]
      congr 1
      ring

private theorem TwistGroup.x_eq_c_power (a b d : ℤ) : x a b d = c a b d ^ (4 * a - b - d) := by
  calc
    x a b d = x a b d ^ 4 * (x a b d ^ 3)⁻¹ := by group
    _ = c a b d ^ (4 * a - d) * (c a b d ^ b)⁻¹ := by rw [x_fourth, x_cube]
    _ = c a b d ^ (4 * a - b - d) := by
      rw [← zpow_sub]
      congr 1
      ring

private theorem TwistGroup.y_eq_c_power (a b d : ℤ) : y a b d = c a b d ^ (-3 * a + b + d) := by
  calc
    y a b d = (x a b d)⁻¹ * (x a b d * y a b d) := by group
    _ = (c a b d ^ (4 * a - b - d))⁻¹ * c a b d ^ a := by rw [x_mul_y, x_eq_c_power]
    _ = c a b d ^ (-3 * a + b + d) := by
      rw [← zpow_neg, ← zpow_add]
      congr 1
      ring

private theorem TwistGroup.c_twistOrder (a b d : ℤ) : c a b d ^ twistOrder a b d = 1 := by
  have h := x_cube a b d
  rw [x_eq_c_power, ← zpow_natCast _ 3, ← zpow_mul] at h
  have h' := congrArg (fun z => z * (c a b d ^ b)⁻¹) h
  rw [mul_inv_cancel, ← zpow_sub] at h'
  norm_num only [Nat.cast_ofNat] at h'
  have he : (4 * a - b - d) * 3 - b = twistOrder a b d := by unfold twistOrder; ring
  rwa [he] at h'

private theorem TwistGroup.generated_by_c (a b d : ℤ) (z : TwistGroup a b d) :
    z ∈ Subgroup.zpowers (c a b d) := by
  apply PresentedGroup.generated_by
  intro j
  fin_cases j
  · exact Subgroup.mem_zpowers _
  · change x a b d ∈ _
    rw [x_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _
  · change y a b d ∈ _
    rw [y_eq_c_power]
    exact Subgroup.zpow_mem_zpowers _ _

private theorem TwistGroup.main_group_trivial (z : TwistGroup 0 1 (-1)) : z = 1 := by
  have hc : c 0 1 (-1) = 1 := by
    simpa only [main_twist_value, zpow_neg_one, inv_eq_one] using c_twistOrder 0 1 (-1)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (generated_by_c 0 1 (-1) z)
  simp [hc]

private def TwistGroup.realizationImages {G : Type*} (c₀ x₀ y₀ : G) : Fin 3 → G :=
  ![c₀, x₀, y₀]

private theorem
    TwistGroup.realizationImages_relators {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) :
    ∀ r ∈ Set.range (twistRelators a b d), FreeGroup.lift (realizationImages c₀ x₀ y₀) r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i <;> simp [twistRelators, realizationImages, hcx.eq, hcy.eq, hxy, hx, hy]

private def TwistGroup.realizationHom {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : TwistGroup a b d →* G :=
  PresentedGroup.toGroup (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
private theorem TwistGroup.realizationHom_c {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (c a b d) = c₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
private theorem TwistGroup.realizationHom_x {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (x a b d) = x₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

@[simp]
private theorem TwistGroup.realizationHom_y {G : Type*} [Group G] (a b d : ℤ) (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = c₀ ^ a) (hx : x₀ ^ 3 = c₀ ^ b)
    (hy : y₀ ^ 4 = c₀ ^ d) : realizationHom a b d c₀ x₀ y₀ hcx hcy hxy hx hy (y a b d) = y₀ :=
  PresentedGroup.toGroup.of (realizationImages_relators a b d c₀ x₀ y₀ hcx hcy hxy hx hy)

public
theorem TwistGroup.main_realization_generators_eq_one {G : Type*} [Group G] (c₀ x₀ y₀ : G)
    (hcx : Commute c₀ x₀) (hcy : Commute c₀ y₀) (hxy : x₀ * y₀ = 1) (hx : x₀ ^ 3 = c₀)
    (hy : y₀ ^ 4 = c₀⁻¹) : c₀ = 1 ∧ x₀ = 1 ∧ y₀ = 1 := by
  let f :=
    realizationHom 0 1 (-1) c₀ x₀ y₀ hcx hcy (by simpa only [zpow_zero] using hxy)
      (by simpa only [zpow_one] using hx) (by simpa only [zpow_neg_one] using hy)
  have hc₀ : f (c 0 1 (-1)) = c₀ := realizationHom_c ..
  have hx₀ : f (x 0 1 (-1)) = x₀ := realizationHom_x ..
  have hy₀ : f (y 0 1 (-1)) = y₀ := realizationHom_y ..
  refine ⟨hc₀.symm.trans ?_, hx₀.symm.trans ?_, hy₀.symm.trans ?_⟩
  · exact (congrArg f (main_group_trivial _)).trans f.map_one
  · exact (congrArg f (main_group_trivial _)).trans f.map_one
  · exact (congrArg f (main_group_trivial _)).trans f.map_one

private def ThreefoldOverlapMappingTorus.Cusp.boundaryRegularData :
    PeriodFamily.Data ℂ SpecialPeriods.TriangleRegularPoint :=
  PeriodFamily.regularData SpecialPeriods.specialPeriodMap
    SpecialPeriods.specialPeriodMap_generator₁ SpecialPeriods.specialPeriodMap_generator₂

private theorem ThreefoldOverlapMappingTorus.Cusp.specialRadius_cap :
    specialData.radius ≤ SpecialPeriods.Triangle.cuspRadius SpecialPeriods.Triangle.width :=
  SpecialPeriods.Threefold.specialBaseCover_cusp_radius_bounds.2.2.le

private theorem ThreefoldOverlapMappingTorus.Cusp.specialPeriod_agreement
    (s : SpecialPeriods.CuspFamily.LogBase specialData.radius) :
    boundaryRegularData.periods.point
        (SpecialPeriods.CuspFamily.logBaseToRegular specialData.radius specialRadius_cap s) =
      specialData.periods.point s :=
  SpecialPeriods.CuspGlobalOverlap.spherePeriod_agreement
    SpecialPeriods.Triangle.triangleSphereUniformization
    SpecialPeriods.Triangle.triangleSphereUniformization_cusp
    SpecialPeriods.Triangle.triangleSphereUniformization_centerOne
    SpecialPeriods.Triangle.triangleSphereUniformization_centerTwo
    (SpecialPeriods.Threefold.specialBaseCover.radius Option.none)
    (SpecialPeriods.Threefold.specialBaseCover.radius_pos Option.none)
    SpecialPeriods.Threefold.specialCuspRadius_le specialRadius_cap s

private theorem ThreefoldOverlapMappingTorus.Cusp.puncturedPieceToRegular_cusp
    (x : ThreefoldOverlapMappingTorus.PuncturedPiece Option.none) :
    ThreefoldOverlapMappingTorus.puncturedPieceToRegular Option.none x =
      SpecialPeriods.Threefold.specialCuspOverlap x.val := by
  apply (SpecialPeriods.Threefold.inclusion_openEmbedding Option.none).injective
  have hx : x.val ∈ SpecialPeriods.Threefold.specialCuspOverlap.source := by
    rw [SpecialPeriods.Threefold.specialCuspOverlap_source]
    exact x.property
  refine (ThreefoldOverlapMappingTorus.puncturedPieceToRegular_inclusion Option.none x).trans ?_
  change
    SpecialPeriods.Threefold.gluingData.inclusion (Option.some Option.none) x.val =
      SpecialPeriods.Threefold.gluingData.inclusion Option.none
        (SpecialPeriods.Threefold.specialCuspOverlap x.val)
  exact
    (SpecialPeriods.Threefold.gluingData.inclusion_eq_iff (Option.some Option.none) Option.none _
          _).mpr
      ⟨hx, rfl⟩

private theorem
    ThreefoldOverlapMappingTorus.Cusp.specialCuspOverlap_family (y : specialData.Space) :
    SpecialPeriods.Threefold.specialCuspOverlap (puncturedFamilyHomeomorph specialData y).val =
      SpecialPeriods.CuspGlobalOverlap.familyMap specialData boundaryRegularData specialRadius_cap
        y := by
  let := specialData.chartedSpace
  let :=
    CuspQuotient.chartedSpace specialData.correction specialData.radius specialData.radius_pos
      specialData.radius_lt_one specialData.holomorphic specialData.smallDrift
  let :=
    boundaryRegularData.chartedSpace
      (SpecialPeriods.CuspGlobalOverlap.familyCovering boundaryRegularData)
  change
    SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial specialData boundaryRegularData
        specialRadius_cap specialPeriod_agreement (puncturedFamilyHomeomorph specialData y).val =
      _
  rw [SpecialPeriods.CuspGlobalOverlap.cuspToRegularPartial_apply specialData boundaryRegularData
      specialRadius_cap specialPeriod_agreement _
      (puncturedFamilyHomeomorph specialData y).property]
  change
    SpecialPeriods.CuspGlobalOverlap.familyMap specialData boundaryRegularData specialRadius_cap
        (specialData.puncturedFamilyBiholomorph.symm (specialData.puncturedFamilyBiholomorph y)) =
      _
  rw [Diffeomorph.symm_apply_apply]

private theorem ThreefoldOverlapMappingTorus.Cusp.boundaryToRegularFamily_cusp_mk (t : ℝ)
    (x : RealTorus₄) :
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
        (MappingTorus.mk monodromy (t, x)) =
      boundaryRegularData.quotient
        (SpecialPeriods.CuspFamily.logBaseToRegular specialData.radius specialRadius_cap
            (logPoint specialData.radius specialData.radius_pos t specialHeight),
          x) := by
  let p : ThreefoldOverlapMappingTorus.PuncturedPiece Option.none :=
    specialBoundaryInclusion (MappingTorus.mk monodromy (t, x))
  have hp :
    ThreefoldOverlapMappingTorus.boundaryToRegularFamily Option.none
        (MappingTorus.mk monodromy (t, x)) =
      SpecialPeriods.Threefold.specialCuspOverlap p.val :=
    puncturedPieceToRegular_cusp p
  refine hp.trans ?_
  change
    SpecialPeriods.Threefold.specialCuspOverlap
        (boundaryCylinder specialData specialHeight (t, x)).val =
      _
  rw [boundaryCylinder_apply, specialCuspOverlap_family,
    SpecialPeriods.CuspGlobalOverlap.familyMap_quotient]

end Mathoverflow1973

end
