/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

import LeanPool.JacobianDiffgeo.DolbeaultComparison.Leray
import LeanPool.JacobianDiffgeo.DolbeaultComparison.GlueForm01
import LeanPool.JacobianDiffgeo.DolbeaultComparison.Splitting
import LeanPool.JacobianDiffgeo.DolbeaultComparison.Comparison

/-!
# dolbeault-comparison: Leray's theorem and the Dolbeault comparison (namespaces `RS`, `RS.Cech`,
`RS.Dolb`)

API summary (see `docs/design/dolbeault-comparison.md`). Zero sorries throughout.

* **`Leray.lean`** (namespace `RS.Cech`; no `Form01`/PoU/dbar-solving — pure cech/mero machinery
  plus dbar's disk-acyclicity black box): `FinCover.induced`, `exists_goodCover`; `exists_trade`
  (Forster 14.6(a), the qualitative Schwartz-surjectivity input consumed by finiteness-and-chi);
  `resH1_surjective_of_isGood`; `toH1_surjective_of_isGood` (**Leray**, Forster 12.8's
  surjectivity half — discharges the interface recorded in cech's `Colimit.lean`); `h1CoverEquiv`
  (`H1Cover D 𝒰 ≃ₗ[ℂ] H1 D` for good `𝒰`).
* **`GlueForm01.lean`** (namespace `RS`; the Mittag-Leffler-style gluing atom, D4):
  `Form01.ext_center`; `DbarGlueData` (local smooth dbar-data on a chart-subordinate cover) with
  `DbarGlueData.form`/`isDbarOn_form`/`form_unique` — every well-definedness question of the
  comparison reduces to `form_unique`.
* **`Splitting.lean`** (namespace `RS.Dolb`; Forster 12.6's PoU splitting of a `D = 0` cocycle):
  `Z1.repr` + its pointwise algebraic identities (`repr_cocycle`/`repr_add`/`repr_smul`);
  `SmoothSplitting`, `exists_smoothSplitting`; `SmoothSplitting.glueData`, `dolbForm`; the
  independence lemmas (`sub_mem_range_dbar_of_splittings`, `dolbForm_add_sub_mem`,
  `dolbForm_smul_sub_mem`, `dolbForm_mem_range_of_mem_B1`, `dolbForm_res_sub_mem`), all reducing
  to `DbarGlueData.form_unique`.
* **`Comparison.lean`** (namespace `RS`; Forster 15.14(a), PDE-free, `D = 0`): `H01 X := Form01 X
  ⧸ range dbar`; `toDolb`/`cechToH01` (the Čech → Dolbeault map, built via `H1.lift`); its
  injectivity (`cechToH01_injective`, the CR-bridge argument) and surjectivity
  (`cechToH01_surjective`, chart-disk dbar-solvability + PoU gluing); the assembled
  `dolbeaultEquiv : H1 (0 : Divisor X) ≃ₗ[ℂ] H01 X`; `finiteDimensional_H01` (gated on
  `[FiniteDimensional ℂ (H1 (0 : Divisor X))]` — `Jacobian/Finiteness/H1Finite.lean` had not
  landed at the time of this build, see the build log); `exists_dbar_eq_iff`.

No Weyl lemma, no elliptic regularity, no harmonic theory anywhere: the only PDE fact ever
consumed is dbar-solvability's `exists_dbar_solution_chart_ball`/disk acyclicity.
-/
