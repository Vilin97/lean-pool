/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch031`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCells4f78f3c271

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `00002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00002201)))

/-- Subcell `000022100220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100220 : AngleCell :=
  childLL (childHL (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100221 : AngleCell :=
  childLH (childHL (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100222 : AngleCell :=
  childHL (childHL (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100223 : AngleCell :=
  childHH (childHL (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100230 : AngleCell :=
  childLL (childHH (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100231 : AngleCell :=
  childLH (childHH (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100232 : AngleCell :=
  childHL (childHH (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100233 : AngleCell :=
  childHH (childHH (childHL (childLL thetaAboveCell00002210)))

/-- Subcell `000022100320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100320 : AngleCell :=
  childLL (childHL (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100321 : AngleCell :=
  childLH (childHL (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100322 : AngleCell :=
  childHL (childHL (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100323 : AngleCell :=
  childHH (childHL (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100330 : AngleCell :=
  childLL (childHH (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100331 : AngleCell :=
  childLH (childHH (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100332 : AngleCell :=
  childHL (childHH (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022100333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022100333 : AngleCell :=
  childHH (childHH (childHH (childLL thetaAboveCell00002210)))

/-- Subcell `000022101220` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101220 : AngleCell :=
  childLL (childHL (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101221` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101221 : AngleCell :=
  childLH (childHL (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101222` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101222 : AngleCell :=
  childHL (childHL (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101223` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101223 : AngleCell :=
  childHH (childHL (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101230` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101230 : AngleCell :=
  childLL (childHH (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101231` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101231 : AngleCell :=
  childLH (childHH (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101232` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101232 : AngleCell :=
  childHL (childHH (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101233` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101233 : AngleCell :=
  childHH (childHH (childHL (childLH thetaAboveCell00002210)))

/-- Subcell `000022101320` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101320 : AngleCell :=
  childLL (childHL (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101321` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101321 : AngleCell :=
  childLH (childHL (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101322` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101322 : AngleCell :=
  childHL (childHL (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101323` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101323 : AngleCell :=
  childHH (childHL (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101330` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101330 : AngleCell :=
  childLL (childHH (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101331` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101331 : AngleCell :=
  childLH (childHH (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101332` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101332 : AngleCell :=
  childHL (childHH (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022101333` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022101333 : AngleCell :=
  childHH (childHH (childHH (childLH thetaAboveCell00002210)))

/-- Subcell `000022102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00002210)))

/-- Subcell `000022102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00002210)))

/-- Subcell `000022103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `000022103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00002210)))

/-- Subcell `0000220131002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013100)))

/-- Subcell `0000220131003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022013100)))

/-- Subcell `0000220131012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell000022013101)))

/-- Subcell `0000220131013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell000022013101)))

/-- Subcell `0000220131102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell000022013110)))

/-- Subcell `0000220131103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell000022013110)))

/-- Subcell `0000220131103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220131103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell000022013110)))

end GerverSofa.PartE.CertificateCells4f78f3c271

namespace GerverSofa.PartE.CertificateCellsea4abf6409

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0000)))

/-- Subcell `000022002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000022002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00002200)))

/-- Subcell `0000220021003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell000022002100)))

/-- Subcell `0000220021003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000220021003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell000022002100)))

end GerverSofa.PartE.CertificateCellsea4abf6409

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatchF910cf651a2033b4`.
* `KernelOnly.PartE.E24KC6R4Subtree001eda2c378d570b`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4f78f3c271

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCells4f78f3c271

open CertificateCells4f78f3c271
theorem cover_subtree_be10dc5c5840 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013100))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002020 h)
        (by
          have h : (thetaAboveCell0000220131002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002021 h)
        (by
          have h : (thetaAboveCell0000220131002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002022 h)
        (by
          have h : (thetaAboveCell0000220131002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002030 h)
        (by
          have h : (thetaAboveCell0000220131002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002031 h)
        (by
          have h : (thetaAboveCell0000220131002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002032 h)
        (by
          have h : (thetaAboveCell0000220131002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002033 h))

theorem cover_subtree_e2664fa77be7 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013100))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002120 h)
        (by
          have h : (thetaAboveCell0000220131002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002121 h)
        (by
          have h : (thetaAboveCell0000220131002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002122 h)
        (by
          have h : (thetaAboveCell0000220131002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002130 h)
        (by
          have h : (thetaAboveCell0000220131002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002131 h)
        (by
          have h : (thetaAboveCell0000220131002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002132 h)
        (by
          have h : (thetaAboveCell0000220131002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002133 h))

theorem cover_subtree_aabbbf73f733 :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002200 h)
        (by
          have h : (thetaAboveCell0000220131002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002201 h)
        (by
          have h : (thetaAboveCell0000220131002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002202 h)
        (by
          have h : (thetaAboveCell0000220131002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002210 h)
        (by
          have h : (thetaAboveCell0000220131002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002211 h)
        (by
          have h : (thetaAboveCell0000220131002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002212 h)
        (by
          have h : (thetaAboveCell0000220131002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022013100))) h)

theorem cover_subtree_9241fb51793c :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002300 h)
        (by
          have h : (thetaAboveCell0000220131002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002301 h)
        (by
          have h : (thetaAboveCell0000220131002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002302 h)
        (by
          have h : (thetaAboveCell0000220131002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002310 h)
        (by
          have h : (thetaAboveCell0000220131002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002311 h)
        (by
          have h : (thetaAboveCell0000220131002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002312 h)
        (by
          have h : (thetaAboveCell0000220131002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022013100))) h)

theorem cover_subtree_2c937348b9e5 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013100)
    cover_subtree_be10dc5c5840
    cover_subtree_e2664fa77be7
    cover_subtree_aabbbf73f733
    cover_subtree_9241fb51793c

theorem cover_subtree_ebd2440c450c :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013100))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003020 h)
        (by
          have h : (thetaAboveCell0000220131003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003021 h)
        (by
          have h : (thetaAboveCell0000220131003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003022 h)
        (by
          have h : (thetaAboveCell0000220131003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003030 h)
        (by
          have h : (thetaAboveCell0000220131003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003031 h)
        (by
          have h : (thetaAboveCell0000220131003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003032 h)
        (by
          have h : (thetaAboveCell0000220131003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003033 h))

theorem cover_subtree_7da0e2645020 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013100))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013100))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003120 h)
        (by
          have h : (thetaAboveCell0000220131003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003121 h)
        (by
          have h : (thetaAboveCell0000220131003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003122 h)
        (by
          have h : (thetaAboveCell0000220131003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003130 h)
        (by
          have h : (thetaAboveCell0000220131003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003131 h)
        (by
          have h : (thetaAboveCell0000220131003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003132 h)
        (by
          have h : (thetaAboveCell0000220131003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003133 h))

theorem cover_subtree_f0b1927352c1 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003200 h)
        (by
          have h : (thetaAboveCell0000220131003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003201 h)
        (by
          have h : (thetaAboveCell0000220131003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003202 h)
        (by
          have h : (thetaAboveCell0000220131003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003210 h)
        (by
          have h : (thetaAboveCell0000220131003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003211 h)
        (by
          have h : (thetaAboveCell0000220131003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003212 h)
        (by
          have h : (thetaAboveCell0000220131003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022013100))) h)

theorem cover_subtree_183a71e75e23 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022013100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003300 h)
        (by
          have h : (thetaAboveCell0000220131003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003301 h)
        (by
          have h : (thetaAboveCell0000220131003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003302 h)
        (by
          have h : (thetaAboveCell0000220131003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022013100)))
        (by
          have h : (thetaAboveCell0000220131003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003310 h)
        (by
          have h : (thetaAboveCell0000220131003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003311 h)
        (by
          have h : (thetaAboveCell0000220131003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003312 h)
        (by
          have h : (thetaAboveCell0000220131003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022013100))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022013100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022013100))) h)

theorem cover_subtree_fed838534b7a :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013100)
    cover_subtree_ebd2440c450c
    cover_subtree_7da0e2645020
    cover_subtree_f0b1927352c1
    cover_subtree_183a71e75e23

theorem cover_subtree_90b4414de137 :
    adaptiveCoverCheck 7 thetaAboveCell000022013100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013100
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013100)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013100)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013100)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013100)) h))
    cover_subtree_2c937348b9e5
    cover_subtree_fed838534b7a

theorem cover_subtree_68d45fba5878 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013101))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012020 h)
        (by
          have h : (thetaAboveCell0000220131012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012021 h)
        (by
          have h : (thetaAboveCell0000220131012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012022 h)
        (by
          have h : (thetaAboveCell0000220131012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012030 h)
        (by
          have h : (thetaAboveCell0000220131012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012031 h)
        (by
          have h : (thetaAboveCell0000220131012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012032 h)
        (by
          have h : (thetaAboveCell0000220131012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012033 h))

theorem cover_subtree_1378cfbe9d41 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013101))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012120 h)
        (by
          have h : (thetaAboveCell0000220131012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012121 h)
        (by
          have h : (thetaAboveCell0000220131012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012122 h)
        (by
          have h : (thetaAboveCell0000220131012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012130 h)
        (by
          have h : (thetaAboveCell0000220131012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012131 h)
        (by
          have h : (thetaAboveCell0000220131012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012132 h)
        (by
          have h : (thetaAboveCell0000220131012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012133 h))

theorem cover_subtree_d4c18a11dbdf :
    adaptiveCoverCheck 5 (childHL (childHL thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012200 h)
        (by
          have h : (thetaAboveCell0000220131012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012201 h)
        (by
          have h : (thetaAboveCell0000220131012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012202 h)
        (by
          have h : (thetaAboveCell0000220131012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012210 h)
        (by
          have h : (thetaAboveCell0000220131012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012211 h)
        (by
          have h : (thetaAboveCell0000220131012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012212 h)
        (by
          have h : (thetaAboveCell0000220131012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
        thetaAboveCell000022013101))) h)

theorem cover_subtree_5c02510827fa :
    adaptiveCoverCheck 5 (childHH (childHL thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012300 h)
        (by
          have h : (thetaAboveCell0000220131012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012301 h)
        (by
          have h : (thetaAboveCell0000220131012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012302 h)
        (by
          have h : (thetaAboveCell0000220131012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHL
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012310 h)
        (by
          have h : (thetaAboveCell0000220131012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012311 h)
        (by
          have h : (thetaAboveCell0000220131012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012312 h)
        (by
          have h : (thetaAboveCell0000220131012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
        thetaAboveCell000022013101))) h)

theorem cover_subtree_a9496679df68 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013101)
    cover_subtree_68d45fba5878
    cover_subtree_1378cfbe9d41
    cover_subtree_d4c18a11dbdf
    cover_subtree_5c02510827fa

theorem cover_subtree_489a9c102105 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013101))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013020 h)
        (by
          have h : (thetaAboveCell0000220131013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013021 h)
        (by
          have h : (thetaAboveCell0000220131013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013022 h)
        (by
          have h : (thetaAboveCell0000220131013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013030 h)
        (by
          have h : (thetaAboveCell0000220131013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013031 h)
        (by
          have h : (thetaAboveCell0000220131013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013032 h)
        (by
          have h : (thetaAboveCell0000220131013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013033 h))

theorem cover_subtree_83fbbe580c99 :
    adaptiveCoverCheck 5 (childLH (childHH thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013101))
    (by
      have h : ((childLL (childLH (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childLH (childLH (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
        thetaAboveCell000022013101))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013120 h)
        (by
          have h : (thetaAboveCell0000220131013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013121 h)
        (by
          have h : (thetaAboveCell0000220131013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013122 h)
        (by
          have h : (thetaAboveCell0000220131013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013130 h)
        (by
          have h : (thetaAboveCell0000220131013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013131 h)
        (by
          have h : (thetaAboveCell0000220131013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013132 h)
        (by
          have h : (thetaAboveCell0000220131013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013133 h))

theorem cover_subtree_41d6d032c729 :
    adaptiveCoverCheck 5 (childHL (childHH thetaAboveCell000022013101)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013101))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHL (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013200 h)
        (by
          have h : (thetaAboveCell0000220131013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013201 h)
        (by
          have h : (thetaAboveCell0000220131013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013202 h)
        (by
          have h : (thetaAboveCell0000220131013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHL (childHH
        thetaAboveCell000022013101)))
        (by
          have h : (thetaAboveCell0000220131013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013210 h)
        (by
          have h : (thetaAboveCell0000220131013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013211 h)
        (by
          have h : (thetaAboveCell0000220131013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013212 h)
        (by
          have h : (thetaAboveCell0000220131013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
        thetaAboveCell000022013101))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell000022013101)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
        thetaAboveCell000022013101))) h)

theorem cover_subtree_51fa07c59358 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013101)
    cover_subtree_489a9c102105
    cover_subtree_83fbbe580c99
    cover_subtree_41d6d032c729
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022013101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022013101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022013101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022013101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022013101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022013101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022013101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022013101))) h))

theorem cover_subtree_e719563f2a9a :
    adaptiveCoverCheck 7 thetaAboveCell000022013101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013101
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013101)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013101)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013101)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013101)) h))
    cover_subtree_a9496679df68
    cover_subtree_51fa07c59358

theorem cover_subtree_5da232081c3f :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013102)) h)

theorem cover_subtree_5c0d2361729f :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013102)) h)

theorem cover_subtree_7dff7749156d :
    adaptiveCoverCheck 7 thetaAboveCell000022013102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013102
    cover_subtree_5da232081c3f
    cover_subtree_5c0d2361729f
    (by
      have h : ((childHL thetaAboveCell000022013102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013102) h)
    (by
      have h : ((childHH thetaAboveCell000022013102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013102) h)

theorem cover_subtree_c4dcfe2e3e24 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013103))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013103)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013103)) h)

theorem cover_subtree_264dbac80856 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013103))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013103)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013103)) h)

theorem cover_subtree_e684324b85dc :
    adaptiveCoverCheck 7 thetaAboveCell000022013103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013103
    cover_subtree_c4dcfe2e3e24
    cover_subtree_264dbac80856
    (by
      have h : ((childHL thetaAboveCell000022013103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013103) h)
    (by
      have h : ((childHH thetaAboveCell000022013103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013103) h)

theorem cover_subtree_ce7ce9f6c591 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00002201)))
    cover_subtree_90b4414de137
    cover_subtree_e719563f2a9a
    cover_subtree_7dff7749156d
    cover_subtree_e684324b85dc

theorem cover_subtree_a70ca499a0b4 :
    adaptiveCoverCheck 5 (childLL (childHL thetaAboveCell000022013110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013110))
    (by
      have h : ((childLL (childLL (childHL thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
        thetaAboveCell000022013110))) h)
    (by
      have h : ((childLH (childLL (childHL thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
        thetaAboveCell000022013110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHL
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102020 h)
        (by
          have h : (thetaAboveCell0000220131102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102021 h)
        (by
          have h : (thetaAboveCell0000220131102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102022 h)
        (by
          have h : (thetaAboveCell0000220131102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHL
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102030 h)
        (by
          have h : (thetaAboveCell0000220131102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102031 h)
        (by
          have h : (thetaAboveCell0000220131102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102032 h)
        (by
          have h : (thetaAboveCell0000220131102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102033 h))

theorem cover_subtree_6d4fa0be4462 :
    adaptiveCoverCheck 5 (childLH (childHL thetaAboveCell000022013110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013110))
    (by
      have h : ((childLL (childLH (childHL thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
        thetaAboveCell000022013110))) h)
    (by
      have h : ((childLH (childLH (childHL thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
        thetaAboveCell000022013110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLH (childHL
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102120 h)
        (by
          have h : (thetaAboveCell0000220131102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102121 h)
        (by
          have h : (thetaAboveCell0000220131102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102122 h)
        (by
          have h : (thetaAboveCell0000220131102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLH (childHL
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102130 h)
        (by
          have h : (thetaAboveCell0000220131102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102131 h)
        (by
          have h : (thetaAboveCell0000220131102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102132 h)
        (by
          have h : (thetaAboveCell0000220131102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131102133 h))

theorem cover_subtree_a8973ec340e4 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013110)
    cover_subtree_a70ca499a0b4
    cover_subtree_6d4fa0be4462
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022013110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022013110))) h))

theorem cover_subtree_3831ad0b2d96 :
    adaptiveCoverCheck 5 (childLL (childHH thetaAboveCell000022013110)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013110))
    (by
      have h : ((childLL (childLL (childHH thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
        thetaAboveCell000022013110))) h)
    (by
      have h : ((childLH (childLL (childHH thetaAboveCell000022013110)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
        thetaAboveCell000022013110))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHL (childLL (childHH
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103020 h)
        (by
          have h : (thetaAboveCell0000220131103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103021 h)
        (by
          have h : (thetaAboveCell0000220131103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103022 h)
        (by
          have h : (thetaAboveCell0000220131103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childHH (childLL (childHH
        thetaAboveCell000022013110)))
        (by
          have h : (thetaAboveCell0000220131103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103030 h)
        (by
          have h : (thetaAboveCell0000220131103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103031 h)
        (by
          have h : (thetaAboveCell0000220131103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103032 h)
        (by
          have h : (thetaAboveCell0000220131103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220131103033 h))

theorem cover_subtree_209916dfc771 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013110)
    cover_subtree_3831ad0b2d96
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013110))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022013110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022013110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022013110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022013110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022013110))) h))

theorem cover_subtree_9102dd71dbed :
    adaptiveCoverCheck 7 thetaAboveCell000022013110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013110
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013110)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013110)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013110)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013110)) h))
    cover_subtree_a8973ec340e4
    cover_subtree_209916dfc771

theorem cover_subtree_62849ad9787b :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022013111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022013111)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022013111))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022013111))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022013111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022013111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022013111))) h))

theorem cover_subtree_bfb0ae9bf369 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022013111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022013111)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022013111))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022013111))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022013111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022013111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022013111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022013111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022013111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022013111))) h))

theorem cover_subtree_eaa4ec2c0c14 :
    adaptiveCoverCheck 7 thetaAboveCell000022013111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013111
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013111)
        (by
          have h : ((childLL (childLL thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022013111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013111)
        (by
          have h : ((childLL (childLH thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022013111)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022013111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022013111)) h))
    cover_subtree_62849ad9787b
    cover_subtree_bfb0ae9bf369

theorem cover_subtree_e17df11d5039 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013112))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013112)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013112)) h)

theorem cover_subtree_c71b0926b90d :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013112))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013112)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013112)) h)

theorem cover_subtree_9a7254ea80d1 :
    adaptiveCoverCheck 7 thetaAboveCell000022013112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013112
    cover_subtree_e17df11d5039
    cover_subtree_c71b0926b90d
    (by
      have h : ((childHL thetaAboveCell000022013112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013112) h)
    (by
      have h : ((childHH thetaAboveCell000022013112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013112) h)

theorem cover_subtree_6a20205ec3a1 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022013113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022013113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022013113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022013113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022013113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022013113))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022013113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022013113)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022013113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022013113)) h)

theorem cover_subtree_1b35fa72d695 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022013113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022013113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022013113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022013113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022013113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022013113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022013113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022013113))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022013113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022013113)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022013113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022013113)) h)

theorem cover_subtree_19dbc3a1cabf :
    adaptiveCoverCheck 7 thetaAboveCell000022013113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022013113
    cover_subtree_6a20205ec3a1
    cover_subtree_1b35fa72d695
    (by
      have h : ((childHL thetaAboveCell000022013113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022013113) h)
    (by
      have h : ((childHH thetaAboveCell000022013113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022013113) h)

theorem cover_subtree_306835c71900 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00002201))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00002201)))
    cover_subtree_9102dd71dbed
    cover_subtree_eaa4ec2c0c14
    cover_subtree_9a7254ea80d1
    cover_subtree_19dbc3a1cabf

theorem e24KC2ThetaAboveLeaf0000220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00002201))
    cover_subtree_ce7ce9f6c591
    cover_subtree_306835c71900
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013120 h)
        (by
          have h : (thetaAboveCell000022013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013121 h)
        (by
          have h : (thetaAboveCell000022013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013122 h)
        (by
          have h : (thetaAboveCell000022013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00002201)))
        (by
          have h : (thetaAboveCell000022013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013130 h)
        (by
          have h : (thetaAboveCell000022013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013131 h)
        (by
          have h : (thetaAboveCell000022013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013132 h)
        (by
          have h : (thetaAboveCell000022013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022013133 h))
theorem e24KC2ThetaAboveLeaf0000220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00002201))
    (by
      have h : ((childLL (childHL (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHL (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00002201))) h)
theorem e24KC2ThetaAboveLeaf0000220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00002201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00002201))
    (by
      have h : ((childLL (childHH (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childLH (childHH (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00002201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00002201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00002201))) h)
theorem e24KC2ThetaAboveLeaf0000221002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00002210))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00002210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022100220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100220 h)
        (by
          have h : (thetaAboveCell000022100221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100221 h)
        (by
          have h : (thetaAboveCell000022100222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100222 h)
        (by
          have h : (thetaAboveCell000022100223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022100230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100230 h)
        (by
          have h : (thetaAboveCell000022100231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100231 h)
        (by
          have h : (thetaAboveCell000022100232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100232 h)
        (by
          have h : (thetaAboveCell000022100233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100233 h))
theorem e24KC2ThetaAboveLeaf0000221003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00002210))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00002210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022100320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100320 h)
        (by
          have h : (thetaAboveCell000022100321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100321 h)
        (by
          have h : (thetaAboveCell000022100322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100322 h)
        (by
          have h : (thetaAboveCell000022100323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022100330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100330 h)
        (by
          have h : (thetaAboveCell000022100331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100331 h)
        (by
          have h : (thetaAboveCell000022100332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100332 h)
        (by
          have h : (thetaAboveCell000022100333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022100333 h))
theorem e24KC2ThetaAboveLeaf0000221012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00002210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHL (childLH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022101220).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101220 h)
        (by
          have h : (thetaAboveCell000022101221).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101221 h)
        (by
          have h : (thetaAboveCell000022101222).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101222 h)
        (by
          have h : (thetaAboveCell000022101223).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101223 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHL (childLH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022101230).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101230 h)
        (by
          have h : (thetaAboveCell000022101231).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101231 h)
        (by
          have h : (thetaAboveCell000022101232).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101232 h)
        (by
          have h : (thetaAboveCell000022101233).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101233 h))
theorem e24KC2ThetaAboveLeaf0000221013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00002210))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00002210))) h)
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childHH (childLH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022101320).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101320 h)
        (by
          have h : (thetaAboveCell000022101321).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101321 h)
        (by
          have h : (thetaAboveCell000022101322).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101322 h)
        (by
          have h : (thetaAboveCell000022101323).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101323 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childHH (childLH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022101330).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101330 h)
        (by
          have h : (thetaAboveCell000022101331).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101331 h)
        (by
          have h : (thetaAboveCell000022101332).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101332 h)
        (by
          have h : (thetaAboveCell000022101333).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022101333 h))
theorem cover_subtree_c6b00b0efe5e :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102000)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102000))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102000))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102000))) h))

theorem cover_subtree_da57798dbd9f :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102000)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102000))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102000))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102000))) h))

theorem cover_subtree_bf93e03bf258 :
    adaptiveCoverCheck 7 thetaAboveCell000022102000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102000
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102000)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102000)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102000)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102000)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102000))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102000)) h))
    cover_subtree_c6b00b0efe5e
    cover_subtree_da57798dbd9f

theorem cover_subtree_77f8696b5d47 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102001)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102001))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102001))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102001))) h))

theorem cover_subtree_d9ace3f5364c :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102001)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102001))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102001))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102001))) h))

theorem cover_subtree_31e6b90084eb :
    adaptiveCoverCheck 7 thetaAboveCell000022102001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102001
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102001)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102001)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102001)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102001)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102001))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102001)) h))
    cover_subtree_77f8696b5d47
    cover_subtree_d9ace3f5364c

theorem cover_subtree_bf46f98b974d :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102002))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102002)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102002)) h)

theorem cover_subtree_1ce6ea29c41d :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102002))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102002)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102002)) h)

theorem cover_subtree_5f2916b0629e :
    adaptiveCoverCheck 7 thetaAboveCell000022102002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102002
    cover_subtree_bf46f98b974d
    cover_subtree_1ce6ea29c41d
    (by
      have h : ((childHL thetaAboveCell000022102002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102002) h)
    (by
      have h : ((childHH thetaAboveCell000022102002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102002) h)

theorem cover_subtree_bf2a6b948a6e :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102003))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102003)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102003)) h)

theorem cover_subtree_80d3b8565aa4 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102003)) h)

theorem cover_subtree_256b0c79e2b4 :
    adaptiveCoverCheck 7 thetaAboveCell000022102003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102003
    cover_subtree_bf2a6b948a6e
    cover_subtree_80d3b8565aa4
    (by
      have h : ((childHL thetaAboveCell000022102003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102003) h)
    (by
      have h : ((childHH thetaAboveCell000022102003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102003) h)

theorem cover_subtree_2cb6fcc01da2 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00002210)))
    cover_subtree_bf93e03bf258
    cover_subtree_31e6b90084eb
    cover_subtree_5f2916b0629e
    cover_subtree_256b0c79e2b4

theorem cover_subtree_9079844093a9 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102010)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102010))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102010))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102010))) h))

theorem cover_subtree_dfea94ec6240 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102010)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102010))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102010))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102010))) h))

theorem cover_subtree_b660fcad9ea4 :
    adaptiveCoverCheck 7 thetaAboveCell000022102010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102010
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102010)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102010)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102010)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102010)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102010))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102010)) h))
    cover_subtree_9079844093a9
    cover_subtree_dfea94ec6240

theorem cover_subtree_5c3913aa5f15 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102011)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102011))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102011))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102011))) h))

theorem cover_subtree_fbab0316abef :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102011)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102011))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102011))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102011))) h))

theorem cover_subtree_c4d768804304 :
    adaptiveCoverCheck 7 thetaAboveCell000022102011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102011
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102011)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102011)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102011)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102011)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102011))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102011)) h))
    cover_subtree_5c3913aa5f15
    cover_subtree_fbab0316abef

theorem cover_subtree_241920b95407 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102012)) h)

theorem cover_subtree_7da00eb7f7ae :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102012)) h)

theorem cover_subtree_f82bf90640b6 :
    adaptiveCoverCheck 7 thetaAboveCell000022102012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102012
    cover_subtree_241920b95407
    cover_subtree_7da00eb7f7ae
    (by
      have h : ((childHL thetaAboveCell000022102012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102012) h)
    (by
      have h : ((childHH thetaAboveCell000022102012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102012) h)

theorem cover_subtree_afdbba9126b4 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102013)) h)

theorem cover_subtree_66c22a722e78 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102013)) h)

theorem cover_subtree_21534bc80804 :
    adaptiveCoverCheck 7 thetaAboveCell000022102013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102013
    cover_subtree_afdbba9126b4
    cover_subtree_66c22a722e78
    (by
      have h : ((childHL thetaAboveCell000022102013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102013) h)
    (by
      have h : ((childHH thetaAboveCell000022102013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102013) h)

theorem cover_subtree_e39770fd6802 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00002210)))
    cover_subtree_b660fcad9ea4
    cover_subtree_c4d768804304
    cover_subtree_f82bf90640b6
    cover_subtree_21534bc80804

theorem e24KC2ThetaAboveLeaf0000221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00002210))
    cover_subtree_2cb6fcc01da2
    cover_subtree_e39770fd6802
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102020 h)
        (by
          have h : (thetaAboveCell000022102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102021 h)
        (by
          have h : (thetaAboveCell000022102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102022 h)
        (by
          have h : (thetaAboveCell000022102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102030 h)
        (by
          have h : (thetaAboveCell000022102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102031 h)
        (by
          have h : (thetaAboveCell000022102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102032 h)
        (by
          have h : (thetaAboveCell000022102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102033 h))
theorem cover_subtree_5ec7a41b8f5f :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102100)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102100))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102100))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102100))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102100))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102100))) h))

theorem cover_subtree_cd20ac2a69b7 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102100) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102100)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102100))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102100))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102100))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102100))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102100))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102100))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102100)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102100))) h))

theorem cover_subtree_15babda5d60b :
    adaptiveCoverCheck 7 thetaAboveCell000022102100 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102100
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102100)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102100)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102100)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102100)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102100))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102100)) h))
    cover_subtree_5ec7a41b8f5f
    cover_subtree_cd20ac2a69b7

theorem cover_subtree_b76fce14d656 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102101)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102101))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102101))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102101))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102101))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102101))) h))

theorem cover_subtree_b7fed3746307 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102101) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102101)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102101))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102101))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102101))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102101))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102101))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102101))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102101)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102101))) h))

theorem cover_subtree_a92382a463a3 :
    adaptiveCoverCheck 7 thetaAboveCell000022102101 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102101
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102101)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102101)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102101)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102101)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102101))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102101)) h))
    cover_subtree_b76fce14d656
    cover_subtree_b7fed3746307

theorem cover_subtree_1f53d26ec077 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102102))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102102))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102102))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102102)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102102)) h)

theorem cover_subtree_d3e2670ab1ea :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102102) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102102)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102102))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102102))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102102))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102102))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102102)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102102))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102102)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102102))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102102)) h)

theorem cover_subtree_98de717668b3 :
    adaptiveCoverCheck 7 thetaAboveCell000022102102 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102102
    cover_subtree_1f53d26ec077
    cover_subtree_d3e2670ab1ea
    (by
      have h : ((childHL thetaAboveCell000022102102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102102) h)
    (by
      have h : ((childHH thetaAboveCell000022102102)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102102) h)

theorem cover_subtree_db5013993ba5 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102103))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102103))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102103))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102103)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102103)) h)

theorem cover_subtree_9589615e51ad :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102103) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102103)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102103))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102103))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102103))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102103))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102103)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102103))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102103)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102103))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102103)) h)

theorem cover_subtree_fdef224c05a8 :
    adaptiveCoverCheck 7 thetaAboveCell000022102103 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102103
    cover_subtree_db5013993ba5
    cover_subtree_9589615e51ad
    (by
      have h : ((childHL thetaAboveCell000022102103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102103) h)
    (by
      have h : ((childHH thetaAboveCell000022102103)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102103) h)

theorem cover_subtree_6fb265308e16 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00002210)))
    cover_subtree_15babda5d60b
    cover_subtree_a92382a463a3
    cover_subtree_98de717668b3
    cover_subtree_fdef224c05a8

theorem cover_subtree_460dcf0085c5 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102110)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102110))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102110))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102110))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102110))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102110))) h))

theorem cover_subtree_51ce5942d936 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102110) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102110)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102110))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102110))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102110))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102110))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102110))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102110))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102110)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102110))) h))

theorem cover_subtree_2be474cb7a0f :
    adaptiveCoverCheck 7 thetaAboveCell000022102110 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102110
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102110)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102110)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102110)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102110)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102110))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102110)) h))
    cover_subtree_460dcf0085c5
    cover_subtree_51ce5942d936

theorem cover_subtree_4bc40a8305e2 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022102111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022102111)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022102111))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022102111))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022102111))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022102111))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022102111))) h))

theorem cover_subtree_bc2667f250d6 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022102111) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022102111)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022102111))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022102111))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022102111))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022102111))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022102111))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022102111))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022102111)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022102111))) h))

theorem cover_subtree_100b7236ad12 :
    adaptiveCoverCheck 7 thetaAboveCell000022102111 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102111
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102111)
        (by
          have h : ((childLL (childLL thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLL
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childLH (childLL thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLL
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childHL (childLL thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childHH (childLL thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL
            thetaAboveCell000022102111)) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102111)
        (by
          have h : ((childLL (childLH thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLL (childLH
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childLH (childLH thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childLH (childLH
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childHL (childLH thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH
            thetaAboveCell000022102111)) h)
        (by
          have h : ((childHH (childLH thetaAboveCell000022102111))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH
            thetaAboveCell000022102111)) h))
    cover_subtree_4bc40a8305e2
    cover_subtree_bc2667f250d6

theorem cover_subtree_968e16bde444 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102112))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102112))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102112))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102112)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102112)) h)

theorem cover_subtree_069815638772 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102112) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102112)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102112))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102112))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102112))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102112))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102112)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102112))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102112)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102112))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102112)) h)

theorem cover_subtree_da19516a51b8 :
    adaptiveCoverCheck 7 thetaAboveCell000022102112 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102112
    cover_subtree_968e16bde444
    cover_subtree_069815638772
    (by
      have h : ((childHL thetaAboveCell000022102112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102112) h)
    (by
      have h : ((childHH thetaAboveCell000022102112)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102112) h)

theorem cover_subtree_7602df0c45bd :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022102113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022102113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022102113))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022102113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022102113))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022102113))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022102113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022102113)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022102113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022102113)) h)

theorem cover_subtree_4f04fe0498c3 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022102113) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022102113)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022102113))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022102113))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022102113))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022102113))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022102113)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022102113))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022102113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022102113)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022102113))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022102113)) h)

theorem cover_subtree_69b60a777b1c :
    adaptiveCoverCheck 7 thetaAboveCell000022102113 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022102113
    cover_subtree_7602df0c45bd
    cover_subtree_4f04fe0498c3
    (by
      have h : ((childHL thetaAboveCell000022102113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022102113) h)
    (by
      have h : ((childHH thetaAboveCell000022102113)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022102113) h)

theorem cover_subtree_13f3502e8052 :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00002210)))
    cover_subtree_2be474cb7a0f
    cover_subtree_100b7236ad12
    cover_subtree_da19516a51b8
    cover_subtree_69b60a777b1c

theorem e24KC2ThetaAboveLeaf0000221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00002210))
    cover_subtree_6fb265308e16
    cover_subtree_13f3502e8052
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102120 h)
        (by
          have h : (thetaAboveCell000022102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102121 h)
        (by
          have h : (thetaAboveCell000022102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102122 h)
        (by
          have h : (thetaAboveCell000022102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102130 h)
        (by
          have h : (thetaAboveCell000022102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102131 h)
        (by
          have h : (thetaAboveCell000022102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102132 h)
        (by
          have h : (thetaAboveCell000022102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022102133 h))
theorem e24KC2ThetaAboveLeaf0000221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00002210))
    (by
      have h : ((childLL (childHL (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHL (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00002210))) h)
theorem e24KC2ThetaAboveLeaf0000221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00002210))
    (by
      have h : ((childLL (childHH (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childLH (childHH (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00002210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00002210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00002210))) h)
theorem cover_subtree_4e4a856a348d :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103000)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103000))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022103000))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103000))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103000))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103000))) h))

theorem cover_subtree_a9ec07ce774e :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103000) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103000)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022103000))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022103000))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103000))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103000))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103000))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103000))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103000)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103000))) h))

theorem cover_subtree_4f8bdd1a7038 :
    adaptiveCoverCheck 7 thetaAboveCell000022103000 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103000
    (by
      have h : ((childLL thetaAboveCell000022103000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103000) h)
    (by
      have h : ((childLH thetaAboveCell000022103000)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103000) h)
    cover_subtree_4e4a856a348d
    cover_subtree_a9ec07ce774e

theorem cover_subtree_45d6d513875c :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103001)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103001))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022103001))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103001))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103001))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103001))) h))

theorem cover_subtree_e48f2ce51ae0 :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103001) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103001)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022103001))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022103001))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103001))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103001))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103001))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103001))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103001)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103001))) h))

theorem cover_subtree_3fbacc491dec :
    adaptiveCoverCheck 7 thetaAboveCell000022103001 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103001
    (by
      have h : ((childLL thetaAboveCell000022103001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103001) h)
    (by
      have h : ((childLH thetaAboveCell000022103001)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103001) h)
    cover_subtree_45d6d513875c
    cover_subtree_e48f2ce51ae0

theorem cover_subtree_c5ade50b08f1 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103002))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103002))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103002))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103002)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103002)) h)

theorem cover_subtree_65c0c0fb0c61 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103002) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103002)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103002))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103002))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103002))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103002))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103002)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103002))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103002)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103002))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103002)) h)

theorem cover_subtree_81fc74c0ffd0 :
    adaptiveCoverCheck 7 thetaAboveCell000022103002 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103002
    cover_subtree_c5ade50b08f1
    cover_subtree_65c0c0fb0c61
    (by
      have h : ((childHL thetaAboveCell000022103002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103002) h)
    (by
      have h : ((childHH thetaAboveCell000022103002)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103002) h)

theorem cover_subtree_7eb489ebb172 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103003))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103003))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103003))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103003)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103003)) h)

theorem cover_subtree_f21141f5d5d1 :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103003) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103003)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103003))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103003))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103003))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103003))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103003)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103003))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103003)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103003))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103003)) h)

theorem cover_subtree_ac4f9a09671e :
    adaptiveCoverCheck 7 thetaAboveCell000022103003 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103003
    cover_subtree_7eb489ebb172
    cover_subtree_f21141f5d5d1
    (by
      have h : ((childHL thetaAboveCell000022103003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103003) h)
    (by
      have h : ((childHH thetaAboveCell000022103003)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103003) h)

theorem cover_subtree_dc732abf341f :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00002210)))
    cover_subtree_4f8bdd1a7038
    cover_subtree_3fbacc491dec
    cover_subtree_81fc74c0ffd0
    cover_subtree_ac4f9a09671e

theorem cover_subtree_4c23e9a4e125 :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103010)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103010))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022103010))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103010))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103010))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103010))) h))

theorem cover_subtree_100c345ae68a :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103010) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103010)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022103010))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022103010))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103010))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103010))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103010))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103010))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103010)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103010))) h))

theorem cover_subtree_712a58fdc8d3 :
    adaptiveCoverCheck 7 thetaAboveCell000022103010 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103010
    (by
      have h : ((childLL thetaAboveCell000022103010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103010) h)
    (by
      have h : ((childLH thetaAboveCell000022103010)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103010) h)
    cover_subtree_4c23e9a4e125
    cover_subtree_100c345ae68a

theorem cover_subtree_38c5b4ed074a :
    adaptiveCoverCheck 6 (childHL thetaAboveCell000022103011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHL thetaAboveCell000022103011)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHL thetaAboveCell000022103011))
        (by
          have h : ((childLL (childLL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childLL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childLL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childLL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHL
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHL thetaAboveCell000022103011))
        (by
          have h : ((childLL (childLH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childLH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childLH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childLH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHL
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHL thetaAboveCell000022103011))
        (by
          have h : ((childLL (childHL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childHL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childHL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childHL (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHL
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHL thetaAboveCell000022103011))
        (by
          have h : ((childLL (childHH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childHH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childHH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHL
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childHH (childHL thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHL
            thetaAboveCell000022103011))) h))

theorem cover_subtree_0e2d12c802dd :
    adaptiveCoverCheck 6 (childHH thetaAboveCell000022103011) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childHH thetaAboveCell000022103011)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childHH thetaAboveCell000022103011))
        (by
          have h : ((childLL (childLL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childLL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childLL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childLL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childHH
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childHH thetaAboveCell000022103011))
        (by
          have h : ((childLL (childLH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childLH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childLH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childLH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childHH
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHL (childHH thetaAboveCell000022103011))
        (by
          have h : ((childLL (childHL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childHL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childHL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHL (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childHL (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHL (childHH
            thetaAboveCell000022103011))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022103011))
        (by
          have h : ((childLL (childHH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childHH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childLH (childHH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childHH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHL (childHH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
            thetaAboveCell000022103011))) h)
        (by
          have h : ((childHH (childHH (childHH thetaAboveCell000022103011)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
            thetaAboveCell000022103011))) h))

theorem cover_subtree_cb9f911d2fd7 :
    adaptiveCoverCheck 7 thetaAboveCell000022103011 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103011
    (by
      have h : ((childLL thetaAboveCell000022103011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000022103011) h)
    (by
      have h : ((childLH thetaAboveCell000022103011)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000022103011) h)
    cover_subtree_38c5b4ed074a
    cover_subtree_0e2d12c802dd

theorem cover_subtree_f068368a2274 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103012))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103012))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103012))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103012)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103012)) h)

theorem cover_subtree_2a95bb96602e :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103012) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103012)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103012))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103012))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103012))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103012))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103012)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103012))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103012)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103012))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103012)) h)

theorem cover_subtree_75584557442b :
    adaptiveCoverCheck 7 thetaAboveCell000022103012 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103012
    cover_subtree_f068368a2274
    cover_subtree_2a95bb96602e
    (by
      have h : ((childHL thetaAboveCell000022103012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103012) h)
    (by
      have h : ((childHH thetaAboveCell000022103012)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103012) h)

theorem cover_subtree_5dbf852f82f6 :
    adaptiveCoverCheck 6 (childLL thetaAboveCell000022103013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLL thetaAboveCell000022103013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLL thetaAboveCell000022103013))
        (by
          have h : ((childLL (childLL (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childLH (childLL (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHL (childLL (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHH (childLL (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLL
            thetaAboveCell000022103013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLL thetaAboveCell000022103013))
        (by
          have h : ((childLL (childLH (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childLH (childLH (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHL (childLH (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLL
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHH (childLH (childLL thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLL
            thetaAboveCell000022103013))) h))
    (by
      have h : ((childHL (childLL thetaAboveCell000022103013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLL thetaAboveCell000022103013)) h)
    (by
      have h : ((childHH (childLL thetaAboveCell000022103013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLL thetaAboveCell000022103013)) h)

theorem cover_subtree_4ebc7849af7a :
    adaptiveCoverCheck 6 (childLH thetaAboveCell000022103013) = true := by
  exact adaptiveCoverCheck_succ_of_children 5 (childLH thetaAboveCell000022103013)
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLL (childLH thetaAboveCell000022103013))
        (by
          have h : ((childLL (childLL (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLL (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childLH (childLL (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLL (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHL (childLL (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLL (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHH (childLL (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLL (childLH
            thetaAboveCell000022103013))) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 4 (childLH (childLH thetaAboveCell000022103013))
        (by
          have h : ((childLL (childLH (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLL (childLH (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childLH (childLH (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childLH (childLH (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHL (childLH (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childLH (childLH
            thetaAboveCell000022103013))) h)
        (by
          have h : ((childHH (childLH (childLH thetaAboveCell000022103013)))).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childLH (childLH
            thetaAboveCell000022103013))) h))
    (by
      have h : ((childHL (childLH thetaAboveCell000022103013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHL (childLH thetaAboveCell000022103013)) h)
    (by
      have h : ((childHH (childLH thetaAboveCell000022103013))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 5 (childHH (childLH thetaAboveCell000022103013)) h)

theorem cover_subtree_e5feda84d791 :
    adaptiveCoverCheck 7 thetaAboveCell000022103013 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000022103013
    cover_subtree_5dbf852f82f6
    cover_subtree_4ebc7849af7a
    (by
      have h : ((childHL thetaAboveCell000022103013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000022103013) h)
    (by
      have h : ((childHH thetaAboveCell000022103013)).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000022103013) h)

theorem cover_subtree_7644ff41fef4 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00002210))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00002210)))
    cover_subtree_712a58fdc8d3
    cover_subtree_cb9f911d2fd7
    cover_subtree_75584557442b
    cover_subtree_e5feda84d791

theorem e24KC2ThetaAboveLeaf0000221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00002210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00002210))
    cover_subtree_dc732abf341f
    cover_subtree_7644ff41fef4
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103020 h)
        (by
          have h : (thetaAboveCell000022103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103021 h)
        (by
          have h : (thetaAboveCell000022103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103022 h)
        (by
          have h : (thetaAboveCell000022103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00002210)))
        (by
          have h : (thetaAboveCell000022103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103030 h)
        (by
          have h : (thetaAboveCell000022103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103031 h)
        (by
          have h : (thetaAboveCell000022103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103032 h)
        (by
          have h : (thetaAboveCell000022103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000022103033 h))

end PartE
end GerverSofa

end

end

end

section

/-! KC6R4 explicit terminal-certificate subtree. No adaptive search. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea4abf6409

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsea4abf6409

open CertificateCellsea4abf6409
theorem e24KC2ThetaAboveLeaf0000220021_c0_c0_c3_c3 :
    adaptiveCoverCheck 5 (childHH (childHH thetaAboveCell000022002100)) = true := by
  exact adaptiveCoverCheck_succ_of_children 4 (childHH (childHH thetaAboveCell000022002100))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLL (childHH (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003300 h)
        (by
          have h : (thetaAboveCell0000220021003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003301 h)
        (by
          have h : (thetaAboveCell0000220021003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003302 h)
        (by
          have h : (thetaAboveCell0000220021003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 3 (childLH (childHH (childHH
        thetaAboveCell000022002100)))
        (by
          have h : (thetaAboveCell0000220021003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003310 h)
        (by
          have h : (thetaAboveCell0000220021003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003311 h)
        (by
          have h : (thetaAboveCell0000220021003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003312 h)
        (by
          have h : (thetaAboveCell0000220021003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 3 thetaAboveCell0000220021003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHL (childHH (childHH
        thetaAboveCell000022002100))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell000022002100)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 4 (childHH (childHH (childHH
        thetaAboveCell000022002100))) h)

end PartE
end GerverSofa

end

end

end

end

end

end
