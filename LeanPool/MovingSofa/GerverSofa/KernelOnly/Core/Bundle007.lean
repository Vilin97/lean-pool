/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Semantics.Batch002`.
-/

public section

noncomputable section

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24PhiBelowKernelLH`.
* `KernelOnly.PartE.E24PhiBelowKernelLL`.
-/

public section

noncomputable section

section

/-! E24 kernel child certificate: PhiBelow/LH, remaining depth 13. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE
namespace CoverCertificatee18e89e753

private abbrev cellRoot : AngleCell :=
  (childLH e24PhiBelowRoot)

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell000 : AngleCell :=
  childLL cell00

private abbrev cell001 : AngleCell :=
  childLH cell00

private abbrev cell002 : AngleCell :=
  childHL cell00

private abbrev cell003 : AngleCell :=
  childHH cell00

private abbrev cell010 : AngleCell :=
  childLL cell01

private abbrev cell011 : AngleCell :=
  childLH cell01

private abbrev cell012 : AngleCell :=
  childHL cell01

private abbrev cell013 : AngleCell :=
  childHH cell01

private abbrev cell020 : AngleCell :=
  childLL cell02

private abbrev cell021 : AngleCell :=
  childLH cell02

private abbrev cell022 : AngleCell :=
  childHL cell02

private abbrev cell023 : AngleCell :=
  childHH cell02

private abbrev cell030 : AngleCell :=
  childLL cell03

private abbrev cell031 : AngleCell :=
  childLH cell03

private abbrev cell032 : AngleCell :=
  childHL cell03

private abbrev cell033 : AngleCell :=
  childHH cell03

private abbrev cell100 : AngleCell :=
  childLL cell10

private abbrev cell101 : AngleCell :=
  childLH cell10

private abbrev cell102 : AngleCell :=
  childHL cell10

private abbrev cell103 : AngleCell :=
  childHH cell10

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

private abbrev cell200 : AngleCell :=
  childLL cell20

private abbrev cell201 : AngleCell :=
  childLH cell20

private abbrev cell202 : AngleCell :=
  childHL cell20

private abbrev cell203 : AngleCell :=
  childHH cell20

private abbrev cell210 : AngleCell :=
  childLL cell21

private abbrev cell211 : AngleCell :=
  childLH cell21

private abbrev cell212 : AngleCell :=
  childHL cell21

private abbrev cell213 : AngleCell :=
  childHH cell21

private abbrev cell220 : AngleCell :=
  childLL cell22

private abbrev cell221 : AngleCell :=
  childLH cell22

private abbrev cell222 : AngleCell :=
  childHL cell22

private abbrev cell223 : AngleCell :=
  childHH cell22

private abbrev cell230 : AngleCell :=
  childLL cell23

private abbrev cell231 : AngleCell :=
  childLH cell23

private abbrev cell232 : AngleCell :=
  childHL cell23

private abbrev cell233 : AngleCell :=
  childHH cell23

private abbrev cell300 : AngleCell :=
  childLL cell30

private abbrev cell301 : AngleCell :=
  childLH cell30

private abbrev cell302 : AngleCell :=
  childHL cell30

private abbrev cell303 : AngleCell :=
  childHH cell30

private abbrev cell310 : AngleCell :=
  childLL cell31

private abbrev cell311 : AngleCell :=
  childLH cell31

private abbrev cell312 : AngleCell :=
  childHL cell31

private abbrev cell313 : AngleCell :=
  childHH cell31

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

private abbrev cell0000 : AngleCell :=
  childLL cell000

private abbrev cell0001 : AngleCell :=
  childLH cell000

private abbrev cell0002 : AngleCell :=
  childHL cell000

private abbrev cell0003 : AngleCell :=
  childHH cell000

private abbrev cell0020 : AngleCell :=
  childLL cell002

private abbrev cell0021 : AngleCell :=
  childLH cell002

private abbrev cell0022 : AngleCell :=
  childHL cell002

private abbrev cell0023 : AngleCell :=
  childHH cell002

private abbrev cell0200 : AngleCell :=
  childLL cell020

private abbrev cell0201 : AngleCell :=
  childLH cell020

private abbrev cell0202 : AngleCell :=
  childHL cell020

private abbrev cell0203 : AngleCell :=
  childHH cell020

private abbrev cell0210 : AngleCell :=
  childLL cell021

private abbrev cell0211 : AngleCell :=
  childLH cell021

private abbrev cell0212 : AngleCell :=
  childHL cell021

private abbrev cell0213 : AngleCell :=
  childHH cell021

private abbrev cell0220 : AngleCell :=
  childLL cell022

private abbrev cell0221 : AngleCell :=
  childLH cell022

private abbrev cell0222 : AngleCell :=
  childHL cell022

private abbrev cell0223 : AngleCell :=
  childHH cell022

private abbrev cell0230 : AngleCell :=
  childLL cell023

private abbrev cell0231 : AngleCell :=
  childLH cell023

private abbrev cell0232 : AngleCell :=
  childHL cell023

private abbrev cell0233 : AngleCell :=
  childHH cell023

private abbrev cell0320 : AngleCell :=
  childLL cell032

private abbrev cell0321 : AngleCell :=
  childLH cell032

private abbrev cell0322 : AngleCell :=
  childHL cell032

private abbrev cell0323 : AngleCell :=
  childHH cell032

private abbrev cell2000 : AngleCell :=
  childLL cell200

private abbrev cell2001 : AngleCell :=
  childLH cell200

private abbrev cell2002 : AngleCell :=
  childHL cell200

private abbrev cell2003 : AngleCell :=
  childHH cell200

private abbrev cell2010 : AngleCell :=
  childLL cell201

private abbrev cell2011 : AngleCell :=
  childLH cell201

private abbrev cell2012 : AngleCell :=
  childHL cell201

private abbrev cell2013 : AngleCell :=
  childHH cell201

private abbrev cell2020 : AngleCell :=
  childLL cell202

private abbrev cell2021 : AngleCell :=
  childLH cell202

private abbrev cell2022 : AngleCell :=
  childHL cell202

private abbrev cell2023 : AngleCell :=
  childHH cell202

private abbrev cell2030 : AngleCell :=
  childLL cell203

private abbrev cell2031 : AngleCell :=
  childLH cell203

private abbrev cell2032 : AngleCell :=
  childHL cell203

private abbrev cell2033 : AngleCell :=
  childHH cell203

private abbrev cell2100 : AngleCell :=
  childLL cell210

private abbrev cell2101 : AngleCell :=
  childLH cell210

private abbrev cell2102 : AngleCell :=
  childHL cell210

private abbrev cell2103 : AngleCell :=
  childHH cell210

private abbrev cell2120 : AngleCell :=
  childLL cell212

private abbrev cell2121 : AngleCell :=
  childLH cell212

private abbrev cell2122 : AngleCell :=
  childHL cell212

private abbrev cell2123 : AngleCell :=
  childHH cell212

private abbrev cell2130 : AngleCell :=
  childLL cell213

private abbrev cell2131 : AngleCell :=
  childLH cell213

private abbrev cell2132 : AngleCell :=
  childHL cell213

private abbrev cell2133 : AngleCell :=
  childHH cell213

private abbrev cell2200 : AngleCell :=
  childLL cell220

private abbrev cell2201 : AngleCell :=
  childLH cell220

private abbrev cell2202 : AngleCell :=
  childHL cell220

private abbrev cell2203 : AngleCell :=
  childHH cell220

private abbrev cell2210 : AngleCell :=
  childLL cell221

private abbrev cell2211 : AngleCell :=
  childLH cell221

private abbrev cell2212 : AngleCell :=
  childHL cell221

private abbrev cell2213 : AngleCell :=
  childHH cell221

private abbrev cell2220 : AngleCell :=
  childLL cell222

private abbrev cell2221 : AngleCell :=
  childLH cell222

private abbrev cell2222 : AngleCell :=
  childHL cell222

private abbrev cell2223 : AngleCell :=
  childHH cell222

private abbrev cell2230 : AngleCell :=
  childLL cell223

private abbrev cell2231 : AngleCell :=
  childLH cell223

private abbrev cell2232 : AngleCell :=
  childHL cell223

private abbrev cell2233 : AngleCell :=
  childHH cell223

private abbrev cell2300 : AngleCell :=
  childLL cell230

private abbrev cell2301 : AngleCell :=
  childLH cell230

private abbrev cell2302 : AngleCell :=
  childHL cell230

private abbrev cell2303 : AngleCell :=
  childHH cell230

private abbrev cell2310 : AngleCell :=
  childLL cell231

private abbrev cell2311 : AngleCell :=
  childLH cell231

private abbrev cell2312 : AngleCell :=
  childHL cell231

private abbrev cell2313 : AngleCell :=
  childHH cell231

private abbrev cell2320 : AngleCell :=
  childLL cell232

private abbrev cell2321 : AngleCell :=
  childLH cell232

private abbrev cell2322 : AngleCell :=
  childHL cell232

private abbrev cell2323 : AngleCell :=
  childHH cell232

private abbrev cell2330 : AngleCell :=
  childLL cell233

private abbrev cell2331 : AngleCell :=
  childLH cell233

private abbrev cell2332 : AngleCell :=
  childHL cell233

private abbrev cell2333 : AngleCell :=
  childHH cell233

private abbrev cell3200 : AngleCell :=
  childLL cell320

private abbrev cell3201 : AngleCell :=
  childLH cell320

private abbrev cell3202 : AngleCell :=
  childHL cell320

private abbrev cell3203 : AngleCell :=
  childHH cell320

private abbrev cell3220 : AngleCell :=
  childLL cell322

private abbrev cell3221 : AngleCell :=
  childLH cell322

private abbrev cell3222 : AngleCell :=
  childHL cell322

private abbrev cell3223 : AngleCell :=
  childHH cell322

private abbrev cell3230 : AngleCell :=
  childLL cell323

private abbrev cell3231 : AngleCell :=
  childLH cell323

private abbrev cell3232 : AngleCell :=
  childHL cell323

private abbrev cell3233 : AngleCell :=
  childHH cell323

private abbrev cell23200 : AngleCell :=
  childLL cell2320

private abbrev cell23201 : AngleCell :=
  childLH cell2320

private abbrev cell23202 : AngleCell :=
  childHL cell2320

private abbrev cell23203 : AngleCell :=
  childHH cell2320

private abbrev cell23220 : AngleCell :=
  childLL cell2322

private abbrev cell23221 : AngleCell :=
  childLH cell2322

private abbrev cell23222 : AngleCell :=
  childHL cell2322

private abbrev cell23223 : AngleCell :=
  childHH cell2322

private theorem checked23200 : adaptiveCoverCheck 8 cell23200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23200 (by decide +kernel)

private theorem checked23201 : adaptiveCoverCheck 8 cell23201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23201 (by decide +kernel)

private theorem checked23202 : adaptiveCoverCheck 8 cell23202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23202 (by decide +kernel)

private theorem checked23203 : adaptiveCoverCheck 8 cell23203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23203 (by decide +kernel)

private theorem checked23220 : adaptiveCoverCheck 8 cell23220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23220 (by decide +kernel)

private theorem checked23221 : adaptiveCoverCheck 8 cell23221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23221 (by decide +kernel)

private theorem checked23222 : adaptiveCoverCheck 8 cell23222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23222 (by decide +kernel)

private theorem checked23223 : adaptiveCoverCheck 8 cell23223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell23223 (by decide +kernel)

private theorem checked0000 : adaptiveCoverCheck 9 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 9 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 9 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 9 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0003 (by decide +kernel)

private theorem checked0020 : adaptiveCoverCheck 9 cell0020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0020 (by decide +kernel)

private theorem checked0021 : adaptiveCoverCheck 9 cell0021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0021 (by decide +kernel)

private theorem checked0022 : adaptiveCoverCheck 9 cell0022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0022 (by decide +kernel)

private theorem checked0023 : adaptiveCoverCheck 9 cell0023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0023 (by decide +kernel)

private theorem checked0200 : adaptiveCoverCheck 9 cell0200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0200 (by decide +kernel)

private theorem checked0201 : adaptiveCoverCheck 9 cell0201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0201 (by decide +kernel)

private theorem checked0202 : adaptiveCoverCheck 9 cell0202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0202 (by decide +kernel)

private theorem checked0203 : adaptiveCoverCheck 9 cell0203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0203 (by decide +kernel)

private theorem checked0210 : adaptiveCoverCheck 9 cell0210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0210 (by decide +kernel)

private theorem checked0211 : adaptiveCoverCheck 9 cell0211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0211 (by decide +kernel)

private theorem checked0212 : adaptiveCoverCheck 9 cell0212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0212 (by decide +kernel)

private theorem checked0213 : adaptiveCoverCheck 9 cell0213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0213 (by decide +kernel)

private theorem checked0220 : adaptiveCoverCheck 9 cell0220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0220 (by decide +kernel)

private theorem checked0221 : adaptiveCoverCheck 9 cell0221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0221 (by decide +kernel)

private theorem checked0222 : adaptiveCoverCheck 9 cell0222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0222 (by decide +kernel)

private theorem checked0223 : adaptiveCoverCheck 9 cell0223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0223 (by decide +kernel)

private theorem checked0230 : adaptiveCoverCheck 9 cell0230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0230 (by decide +kernel)

private theorem checked0231 : adaptiveCoverCheck 9 cell0231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0231 (by decide +kernel)

private theorem checked0232 : adaptiveCoverCheck 9 cell0232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0232 (by decide +kernel)

private theorem checked0233 : adaptiveCoverCheck 9 cell0233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0233 (by decide +kernel)

private theorem checked0320 : adaptiveCoverCheck 9 cell0320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0320 (by decide +kernel)

private theorem checked0321 : adaptiveCoverCheck 9 cell0321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0321 (by decide +kernel)

private theorem checked0322 : adaptiveCoverCheck 9 cell0322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0322 (by decide +kernel)

private theorem checked0323 : adaptiveCoverCheck 9 cell0323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell0323 (by decide +kernel)

private theorem checked2000 : adaptiveCoverCheck 9 cell2000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2000 (by decide +kernel)

private theorem checked2001 : adaptiveCoverCheck 9 cell2001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2001 (by decide +kernel)

private theorem checked2002 : adaptiveCoverCheck 9 cell2002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2002 (by decide +kernel)

private theorem checked2003 : adaptiveCoverCheck 9 cell2003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2003 (by decide +kernel)

private theorem checked2010 : adaptiveCoverCheck 9 cell2010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2010 (by decide +kernel)

private theorem checked2011 : adaptiveCoverCheck 9 cell2011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2011 (by decide +kernel)

private theorem checked2012 : adaptiveCoverCheck 9 cell2012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2012 (by decide +kernel)

private theorem checked2013 : adaptiveCoverCheck 9 cell2013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2013 (by decide +kernel)

private theorem checked2020 : adaptiveCoverCheck 9 cell2020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2020 (by decide +kernel)

private theorem checked2021 : adaptiveCoverCheck 9 cell2021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2021 (by decide +kernel)

private theorem checked2022 : adaptiveCoverCheck 9 cell2022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2022 (by decide +kernel)

private theorem checked2023 : adaptiveCoverCheck 9 cell2023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2023 (by decide +kernel)

private theorem checked2030 : adaptiveCoverCheck 9 cell2030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2030 (by decide +kernel)

private theorem checked2031 : adaptiveCoverCheck 9 cell2031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2031 (by decide +kernel)

private theorem checked2032 : adaptiveCoverCheck 9 cell2032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2032 (by decide +kernel)

private theorem checked2033 : adaptiveCoverCheck 9 cell2033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2033 (by decide +kernel)

private theorem checked2100 : adaptiveCoverCheck 9 cell2100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2100 (by decide +kernel)

private theorem checked2101 : adaptiveCoverCheck 9 cell2101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2101 (by decide +kernel)

private theorem checked2102 : adaptiveCoverCheck 9 cell2102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2102 (by decide +kernel)

private theorem checked2103 : adaptiveCoverCheck 9 cell2103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2103 (by decide +kernel)

private theorem checked2120 : adaptiveCoverCheck 9 cell2120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2120 (by decide +kernel)

private theorem checked2121 : adaptiveCoverCheck 9 cell2121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2121 (by decide +kernel)

private theorem checked2122 : adaptiveCoverCheck 9 cell2122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2122 (by decide +kernel)

private theorem checked2123 : adaptiveCoverCheck 9 cell2123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2123 (by decide +kernel)

private theorem checked2130 : adaptiveCoverCheck 9 cell2130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2130 (by decide +kernel)

private theorem checked2131 : adaptiveCoverCheck 9 cell2131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2131 (by decide +kernel)

private theorem checked2132 : adaptiveCoverCheck 9 cell2132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2132 (by decide +kernel)

private theorem checked2133 : adaptiveCoverCheck 9 cell2133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2133 (by decide +kernel)

private theorem checked2200 : adaptiveCoverCheck 9 cell2200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2200 (by decide +kernel)

private theorem checked2201 : adaptiveCoverCheck 9 cell2201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2201 (by decide +kernel)

private theorem checked2202 : adaptiveCoverCheck 9 cell2202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2202 (by decide +kernel)

private theorem checked2203 : adaptiveCoverCheck 9 cell2203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2203 (by decide +kernel)

private theorem checked2210 : adaptiveCoverCheck 9 cell2210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2210 (by decide +kernel)

private theorem checked2211 : adaptiveCoverCheck 9 cell2211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2211 (by decide +kernel)

private theorem checked2212 : adaptiveCoverCheck 9 cell2212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2212 (by decide +kernel)

private theorem checked2213 : adaptiveCoverCheck 9 cell2213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2213 (by decide +kernel)

private theorem checked2220 : adaptiveCoverCheck 9 cell2220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2220 (by decide +kernel)

private theorem checked2221 : adaptiveCoverCheck 9 cell2221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2221 (by decide +kernel)

private theorem checked2222 : adaptiveCoverCheck 9 cell2222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2222 (by decide +kernel)

private theorem checked2223 : adaptiveCoverCheck 9 cell2223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2223 (by decide +kernel)

private theorem checked2230 : adaptiveCoverCheck 9 cell2230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2230 (by decide +kernel)

private theorem checked2231 : adaptiveCoverCheck 9 cell2231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2231 (by decide +kernel)

private theorem checked2232 : adaptiveCoverCheck 9 cell2232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2232 (by decide +kernel)

private theorem checked2233 : adaptiveCoverCheck 9 cell2233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2233 (by decide +kernel)

private theorem checked2300 : adaptiveCoverCheck 9 cell2300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2300 (by decide +kernel)

private theorem checked2301 : adaptiveCoverCheck 9 cell2301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2301 (by decide +kernel)

private theorem checked2302 : adaptiveCoverCheck 9 cell2302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2302 (by decide +kernel)

private theorem checked2303 : adaptiveCoverCheck 9 cell2303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2303 (by decide +kernel)

private theorem checked2310 : adaptiveCoverCheck 9 cell2310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2310 (by decide +kernel)

private theorem checked2311 : adaptiveCoverCheck 9 cell2311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2311 (by decide +kernel)

private theorem checked2312 : adaptiveCoverCheck 9 cell2312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2312 (by decide +kernel)

private theorem checked2313 : adaptiveCoverCheck 9 cell2313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2313 (by decide +kernel)

private theorem checked2320 : adaptiveCoverCheck 9 cell2320 = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cell2320
    checked23200 checked23201 checked23202 checked23203

private theorem checked2321 : adaptiveCoverCheck 9 cell2321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2321 (by decide +kernel)

private theorem checked2322 : adaptiveCoverCheck 9 cell2322 = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cell2322
    checked23220 checked23221 checked23222 checked23223

private theorem checked2323 : adaptiveCoverCheck 9 cell2323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2323 (by decide +kernel)

private theorem checked2330 : adaptiveCoverCheck 9 cell2330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2330 (by decide +kernel)

private theorem checked2331 : adaptiveCoverCheck 9 cell2331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2331 (by decide +kernel)

private theorem checked2332 : adaptiveCoverCheck 9 cell2332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2332 (by decide +kernel)

private theorem checked2333 : adaptiveCoverCheck 9 cell2333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell2333 (by decide +kernel)

private theorem checked3200 : adaptiveCoverCheck 9 cell3200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3200 (by decide +kernel)

private theorem checked3201 : adaptiveCoverCheck 9 cell3201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3201 (by decide +kernel)

private theorem checked3202 : adaptiveCoverCheck 9 cell3202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3202 (by decide +kernel)

private theorem checked3203 : adaptiveCoverCheck 9 cell3203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3203 (by decide +kernel)

private theorem checked3220 : adaptiveCoverCheck 9 cell3220 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3220 (by decide +kernel)

private theorem checked3221 : adaptiveCoverCheck 9 cell3221 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3221 (by decide +kernel)

private theorem checked3222 : adaptiveCoverCheck 9 cell3222 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3222 (by decide +kernel)

private theorem checked3223 : adaptiveCoverCheck 9 cell3223 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3223 (by decide +kernel)

private theorem checked3230 : adaptiveCoverCheck 9 cell3230 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3230 (by decide +kernel)

private theorem checked3231 : adaptiveCoverCheck 9 cell3231 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3231 (by decide +kernel)

private theorem checked3232 : adaptiveCoverCheck 9 cell3232 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3232 (by decide +kernel)

private theorem checked3233 : adaptiveCoverCheck 9 cell3233 = true := by
  exact adaptiveCoverCheck_true_of_rejected 9 cell3233 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 10 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 10 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 10 cell002 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell002
    checked0020 checked0021 checked0022 checked0023

private theorem checked003 : adaptiveCoverCheck 10 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 10 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 10 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 10 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 10 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 10 cell020 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell020
    checked0200 checked0201 checked0202 checked0203

private theorem checked021 : adaptiveCoverCheck 10 cell021 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell021
    checked0210 checked0211 checked0212 checked0213

private theorem checked022 : adaptiveCoverCheck 10 cell022 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell022
    checked0220 checked0221 checked0222 checked0223

private theorem checked023 : adaptiveCoverCheck 10 cell023 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell023
    checked0230 checked0231 checked0232 checked0233

private theorem checked030 : adaptiveCoverCheck 10 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 10 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 10 cell032 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell032
    checked0320 checked0321 checked0322 checked0323

private theorem checked033 : adaptiveCoverCheck 10 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 10 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 10 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 10 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 10 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell103 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 10 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 10 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 10 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 10 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 10 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 10 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 10 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 10 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 10 cell200 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell200
    checked2000 checked2001 checked2002 checked2003

private theorem checked201 : adaptiveCoverCheck 10 cell201 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell201
    checked2010 checked2011 checked2012 checked2013

private theorem checked202 : adaptiveCoverCheck 10 cell202 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell202
    checked2020 checked2021 checked2022 checked2023

private theorem checked203 : adaptiveCoverCheck 10 cell203 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell203
    checked2030 checked2031 checked2032 checked2033

private theorem checked210 : adaptiveCoverCheck 10 cell210 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell210
    checked2100 checked2101 checked2102 checked2103

private theorem checked211 : adaptiveCoverCheck 10 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 10 cell212 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell212
    checked2120 checked2121 checked2122 checked2123

private theorem checked213 : adaptiveCoverCheck 10 cell213 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell213
    checked2130 checked2131 checked2132 checked2133

private theorem checked220 : adaptiveCoverCheck 10 cell220 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell220
    checked2200 checked2201 checked2202 checked2203

private theorem checked221 : adaptiveCoverCheck 10 cell221 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell221
    checked2210 checked2211 checked2212 checked2213

private theorem checked222 : adaptiveCoverCheck 10 cell222 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell222
    checked2220 checked2221 checked2222 checked2223

private theorem checked223 : adaptiveCoverCheck 10 cell223 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell223
    checked2230 checked2231 checked2232 checked2233

private theorem checked230 : adaptiveCoverCheck 10 cell230 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell230
    checked2300 checked2301 checked2302 checked2303

private theorem checked231 : adaptiveCoverCheck 10 cell231 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell231
    checked2310 checked2311 checked2312 checked2313

private theorem checked232 : adaptiveCoverCheck 10 cell232 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell232
    checked2320 checked2321 checked2322 checked2323

private theorem checked233 : adaptiveCoverCheck 10 cell233 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell233
    checked2330 checked2331 checked2332 checked2333

private theorem checked300 : adaptiveCoverCheck 10 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 10 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 10 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 10 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 10 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 10 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 10 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 10 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 10 cell320 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell320
    checked3200 checked3201 checked3202 checked3203

private theorem checked321 : adaptiveCoverCheck 10 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 10 cell322 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell322
    checked3220 checked3221 checked3222 checked3223

private theorem checked323 : adaptiveCoverCheck 10 cell323 = true := by
  exact adaptiveCoverCheck_succ_of_children 9 cell323
    checked3230 checked3231 checked3232 checked3233

private theorem checked330 : adaptiveCoverCheck 10 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 10 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 10 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 10 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 11 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 11 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 11 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 11 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 11 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 11 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 11 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 11 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 11 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 11 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 11 cell22 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell22
    checked220 checked221 checked222 checked223

private theorem checked23 : adaptiveCoverCheck 11 cell23 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell23
    checked230 checked231 checked232 checked233

private theorem checked30 : adaptiveCoverCheck 11 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 11 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 11 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 11 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 12 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 12 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 12 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 12 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 13 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 12 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee18e89e753

theorem e24PhiBelowKernelLH :
    adaptiveCoverCheck 13 (childLH e24PhiBelowRoot) = true := by
  exact CoverCertificatee18e89e753.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! E24 kernel child certificate: PhiBelow/LL, remaining depth 13. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE
namespace CoverCertificate4615b9c889

private abbrev cellRoot : AngleCell :=
  (childLL e24PhiBelowRoot)

private abbrev cell0 : AngleCell :=
  childLL cellRoot

private abbrev cell1 : AngleCell :=
  childLH cellRoot

private abbrev cell2 : AngleCell :=
  childHL cellRoot

private abbrev cell3 : AngleCell :=
  childHH cellRoot

private abbrev cell00 : AngleCell :=
  childLL cell0

private abbrev cell01 : AngleCell :=
  childLH cell0

private abbrev cell02 : AngleCell :=
  childHL cell0

private abbrev cell03 : AngleCell :=
  childHH cell0

private abbrev cell10 : AngleCell :=
  childLL cell1

private abbrev cell11 : AngleCell :=
  childLH cell1

private abbrev cell12 : AngleCell :=
  childHL cell1

private abbrev cell13 : AngleCell :=
  childHH cell1

private abbrev cell20 : AngleCell :=
  childLL cell2

private abbrev cell21 : AngleCell :=
  childLH cell2

private abbrev cell22 : AngleCell :=
  childHL cell2

private abbrev cell23 : AngleCell :=
  childHH cell2

private abbrev cell30 : AngleCell :=
  childLL cell3

private abbrev cell31 : AngleCell :=
  childLH cell3

private abbrev cell32 : AngleCell :=
  childHL cell3

private abbrev cell33 : AngleCell :=
  childHH cell3

private abbrev cell110 : AngleCell :=
  childLL cell11

private abbrev cell111 : AngleCell :=
  childLH cell11

private abbrev cell112 : AngleCell :=
  childHL cell11

private abbrev cell113 : AngleCell :=
  childHH cell11

private abbrev cell120 : AngleCell :=
  childLL cell12

private abbrev cell121 : AngleCell :=
  childLH cell12

private abbrev cell122 : AngleCell :=
  childHL cell12

private abbrev cell123 : AngleCell :=
  childHH cell12

private abbrev cell130 : AngleCell :=
  childLL cell13

private abbrev cell131 : AngleCell :=
  childLH cell13

private abbrev cell132 : AngleCell :=
  childHL cell13

private abbrev cell133 : AngleCell :=
  childHH cell13

private abbrev cell300 : AngleCell :=
  childLL cell30

private abbrev cell301 : AngleCell :=
  childLH cell30

private abbrev cell302 : AngleCell :=
  childHL cell30

private abbrev cell303 : AngleCell :=
  childHH cell30

private abbrev cell310 : AngleCell :=
  childLL cell31

private abbrev cell311 : AngleCell :=
  childLH cell31

private abbrev cell312 : AngleCell :=
  childHL cell31

private abbrev cell313 : AngleCell :=
  childHH cell31

private abbrev cell320 : AngleCell :=
  childLL cell32

private abbrev cell321 : AngleCell :=
  childLH cell32

private abbrev cell322 : AngleCell :=
  childHL cell32

private abbrev cell323 : AngleCell :=
  childHH cell32

private abbrev cell330 : AngleCell :=
  childLL cell33

private abbrev cell331 : AngleCell :=
  childLH cell33

private abbrev cell332 : AngleCell :=
  childHL cell33

private abbrev cell333 : AngleCell :=
  childHH cell33

private theorem checked110 : adaptiveCoverCheck 10 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 10 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 10 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 10 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 10 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 10 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 10 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 10 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 10 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 10 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 10 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 10 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell133 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 10 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 10 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 10 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 10 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 10 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 10 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 10 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 10 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell313 (by decide +kernel)

private theorem checked320 : adaptiveCoverCheck 10 cell320 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell320 (by decide +kernel)

private theorem checked321 : adaptiveCoverCheck 10 cell321 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell321 (by decide +kernel)

private theorem checked322 : adaptiveCoverCheck 10 cell322 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell322 (by decide +kernel)

private theorem checked323 : adaptiveCoverCheck 10 cell323 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell323 (by decide +kernel)

private theorem checked330 : adaptiveCoverCheck 10 cell330 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell330 (by decide +kernel)

private theorem checked331 : adaptiveCoverCheck 10 cell331 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell331 (by decide +kernel)

private theorem checked332 : adaptiveCoverCheck 10 cell332 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell332 (by decide +kernel)

private theorem checked333 : adaptiveCoverCheck 10 cell333 = true := by
  exact adaptiveCoverCheck_true_of_rejected 10 cell333 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 11 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 11 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 11 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 11 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 11 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 11 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 11 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 11 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 11 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 11 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 11 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 11 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 11 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 11 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 11 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 11 cell32 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell32
    checked320 checked321 checked322 checked323

private theorem checked33 : adaptiveCoverCheck 11 cell33 = true := by
  exact adaptiveCoverCheck_succ_of_children 10 cell33
    checked330 checked331 checked332 checked333

private theorem checked0 : adaptiveCoverCheck 12 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 12 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 12 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 12 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 11 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 13 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 12 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4615b9c889

theorem e24PhiBelowKernelLL :
    adaptiveCoverCheck 13 (childLL e24PhiBelowRoot) = true := by
  exact CoverCertificate4615b9c889.checkedRoot

end PartE
end GerverSofa

end

end

end

end

end

end
