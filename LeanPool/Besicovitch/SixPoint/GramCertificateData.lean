/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import LeanPool.Besicovitch.SixPoint.GramCertificateCore

/-!
# The thirty local Gram certificates

The two second-child radii both lie in `[barC - 1, 1]`.  Seven intervals cover that range, the
score is symmetric in the two sibling pairs, and the middle square is split once more, leaving
thirty ordered rectangles.  This file records one certificate for each and checks its arithmetic.

The tangent parameters, separation multipliers and factor entries were found numerically and are
stored as exact rationals with denominator `10000`; every inequality below is recomputed here.
-/

@[expose] public section

noncomputable section

namespace LeanPool.Besicovitch

/-- One local Gram certificate for each of the thirty radius rectangles. -/
def gramCertificates : Fin 30 → GramCertificate := ![
  -- `I0xI0`
  { pLower := 967/2500, pUpper := 1/2, wLower := 967/2500, wUpper := 1/2,
    alpha₀ := 1880 / 10000, alpha₁ := 3752 / 10000, alpha₂ := 1215 / 10000,
    alpha₃ := 1216 / 10000, alpha₄ := 1320 / 10000, alpha₅ := 1320 / 10000,
    etaP := 8111 / 10000, etaW := 8110 / 10000,
    factor := tenThousandthFactor ![
      ![-27, -6328, -8502, 6297, 8445],
      ![-8122, -5410, -6221, -5463, -6269],
      ![-15, -2916, 2178, 2918, -2168]] },
  -- `I0xI1`
  { pLower := 967/2500, pUpper := 1/2, wLower := 1/2, wUpper := 3/5,
    alpha₀ := 1883 / 10000, alpha₁ := 3370 / 10000, alpha₂ := 1216 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1219 / 10000, alpha₅ := 1323 / 10000,
    etaP := 8277 / 10000, etaW := 5910 / 10000,
    factor := tenThousandthFactor ![
      ![-4790, -8414, -10647, 1537, 2375],
      ![-6984, -255, 450, -7546, -8088],
      ![-390, -2835, 2364, 2762, -2019]] },
  -- `I0xI2`
  { pLower := 967/2500, pUpper := 1/2, wLower := 3/5, wUpper := 7/10,
    alpha₀ := 1884 / 10000, alpha₁ := 3152 / 10000, alpha₂ := 1217 / 10000,
    alpha₃ := 1221 / 10000, alpha₄ := 1164 / 10000, alpha₅ := 1330 / 10000,
    etaP := 8386 / 10000, etaW := 5005 / 10000,
    factor := tenThousandthFactor ![
      ![-5134, -8463, -10670, 1032, 1692],
      ![-6980, 352, 1216, -7344, -7267],
      ![-595, -2790, 2462, 2697, -1878]] },
  -- `I0xI3`
  { pLower := 967/2500, pUpper := 1/2, wLower := 7/10, wUpper := 3/4,
    alpha₀ := 1882 / 10000, alpha₁ := 3007 / 10000, alpha₂ := 1214 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1121 / 10000, alpha₅ := 1328 / 10000,
    etaP := 8437 / 10000, etaW := 4466 / 10000,
    factor := tenThousandthFactor ![
      ![-5242, -8482, -10649, 851, 1437],
      ![-7061, 592, 1522, -7166, -6736],
      ![-688, -2747, 2498, 2680, -1807]] },
  -- `I0xI4`
  { pLower := 967/2500, pUpper := 1/2, wLower := 3/4, wUpper := 4/5,
    alpha₀ := 1881 / 10000, alpha₁ := 2919 / 10000, alpha₂ := 1215 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1096 / 10000, alpha₅ := 1327 / 10000,
    etaP := 8482 / 10000, etaW := 4164 / 10000,
    factor := tenThousandthFactor ![
      ![-5283, -8499, -10648, 772, 1319],
      ![-7133, 704, 1670, -7056, -6421],
      ![-746, -2721, 2519, 2676, -1754]] },
  -- `I0xI5`
  { pLower := 967/2500, pUpper := 1/2, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1881 / 10000, alpha₁ := 2802 / 10000, alpha₂ := 1214 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1058 / 10000, alpha₅ := 1325 / 10000,
    etaP := 8560 / 10000, etaW := 3771 / 10000,
    factor := tenThousandthFactor ![
      ![-5319, -8527, -10663, 690, 1189],
      ![-7259, 829, 1842, -6900, -6000],
      ![-816, -2692, 2546, 2679, -1684]] },
  -- `I0xI6`
  { pLower := 967/2500, pUpper := 1/2, wLower := 9/10, wUpper := 1,
    alpha₀ := 1878 / 10000, alpha₁ := 2654 / 10000, alpha₂ := 1214 / 10000,
    alpha₃ := 1215 / 10000, alpha₄ := 1010 / 10000, alpha₅ := 1323 / 10000,
    etaP := 8668 / 10000, etaW := 3327 / 10000,
    factor := tenThousandthFactor ![
      ![-5339, -8568, -10685, 617, 1062],
      ![-7433, 950, 2017, -6708, -5503],
      ![-889, -2647, 2563, 2691, -1597]] },
  -- `I1xI1`
  { pLower := 1/2, pUpper := 3/5, wLower := 1/2, wUpper := 3/5,
    alpha₀ := 1880 / 10000, alpha₁ := 3028 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1228 / 10000, alpha₅ := 1226 / 10000,
    etaP := 6011 / 10000, etaW := 6021 / 10000,
    factor := tenThousandthFactor ![
      ![-8767, -4877, -4791, -4989, -4916],
      ![-80, -6070, -7028, 5985, 6939],
      ![-9, -2613, 2262, 2606, -2242]] },
  -- `I1xI2`
  { pLower := 1/2, pUpper := 3/5, wLower := 3/5, wUpper := 7/10,
    alpha₀ := 1883 / 10000, alpha₁ := 2844 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1220 / 10000, alpha₄ := 1168 / 10000, alpha₅ := 1228 / 10000,
    etaP := 6087 / 10000, etaW := 5081 / 10000,
    factor := tenThousandthFactor ![
      ![-7475, -7386, -7796, -987, -379],
      ![-4900, 2654, 3491, -7433, -7525],
      ![-189, -2529, 2363, 2530, -2171]] },
  -- `I1xI3`
  { pLower := 1/2, pUpper := 3/5, wLower := 7/10, wUpper := 3/4,
    alpha₀ := 1888 / 10000, alpha₁ := 2726 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1126 / 10000, alpha₅ := 1225 / 10000,
    etaP := 6131 / 10000, etaW := 4538 / 10000,
    factor := tenThousandthFactor ![
      ![-7399, -7449, -7856, -822, -203],
      ![-5234, 2589, 3414, -7263, -6948],
      ![-310, -2482, 2438, 2498, -2105]] },
  -- `I1xI4`
  { pLower := 1/2, pUpper := 3/5, wLower := 3/4, wUpper := 4/5,
    alpha₀ := 1883 / 10000, alpha₁ := 2647 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1101 / 10000, alpha₅ := 1225 / 10000,
    etaP := 6169 / 10000, etaW := 4234 / 10000,
    factor := tenThousandthFactor ![
      ![-7348, -7483, -7886, -746, -127],
      ![-5407, 2567, 3386, -7157, -6615],
      ![-374, -2440, 2463, 2476, -2058]] },
  -- `I1xI5`
  { pLower := 1/2, pUpper := 3/5, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1882 / 10000, alpha₁ := 2545 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1062 / 10000, alpha₅ := 1222 / 10000,
    etaP := 6214 / 10000, etaW := 3841 / 10000,
    factor := tenThousandthFactor ![
      ![-7332, -7503, -7905, -699, -80],
      ![-5599, 2592, 3415, -7008, -6172],
      ![-465, -2400, 2512, 2462, -1991]] },
  -- `I1xI6`
  { pLower := 1/2, pUpper := 3/5, wLower := 9/10, wUpper := 1,
    alpha₀ := 1880 / 10000, alpha₁ := 2426 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1216 / 10000, alpha₄ := 1015 / 10000, alpha₅ := 1219 / 10000,
    etaP := 6292 / 10000, etaW := 3396 / 10000,
    factor := tenThousandthFactor ![
      ![-7331, -7533, -7927, -658, -42],
      ![-5824, 2639, 3474, -6817, -5673],
      ![-556, -2341, 2544, 2465, -1922]] },
  -- `I2xI3`
  { pLower := 3/5, pUpper := 7/10, wLower := 7/10, wUpper := 3/4,
    alpha₀ := 1884 / 10000, alpha₁ := 2569 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1126 / 10000, alpha₅ := 1166 / 10000,
    etaP := 5183 / 10000, etaW := 4591 / 10000,
    factor := tenThousandthFactor ![
      ![-8941, -5867, -5484, -3194, -2519],
      ![-2173, 4811, 5251, -6632, -6515],
      ![-118, -2371, 2365, 2389, -2238]] },
  -- `I2xI4`
  { pLower := 3/5, pUpper := 7/10, wLower := 3/4, wUpper := 4/5,
    alpha₀ := 1884 / 10000, alpha₁ := 2500 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1100 / 10000, alpha₅ := 1165 / 10000,
    etaP := 5209 / 10000, etaW := 4285 / 10000,
    factor := tenThousandthFactor ![
      ![-8808, -6175, -5817, -2692, -1962],
      ![-2882, 4447, 4902, -6734, -6349],
      ![-189, -2333, 2410, 2364, -2195]] },
  -- `I2xI5`
  { pLower := 3/5, pUpper := 7/10, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1883 / 10000, alpha₁ := 2407 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1062 / 10000, alpha₅ := 1162 / 10000,
    etaP := 5254 / 10000, etaW := 3880 / 10000,
    factor := tenThousandthFactor ![
      ![-8676, -6415, -6069, -2254, -1483],
      ![-3526, 4155, 4618, -6727, -6021],
      ![-279, -2274, 2454, 2349, -2148]] },
  -- `I2xI6`
  { pLower := 3/5, pUpper := 7/10, wLower := 9/10, wUpper := 1,
    alpha₀ := 1881 / 10000, alpha₁ := 2296 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1215 / 10000, alpha₄ := 1015 / 10000, alpha₅ := 1156 / 10000,
    etaP := 5301 / 10000, etaW := 3441 / 10000,
    factor := tenThousandthFactor ![
      ![-8592, -6558, -6218, -1951, -1149],
      ![-4021, 3989, 4460, -6629, -5582],
      ![-383, -2213, 2514, 2336, -2071]] },
  -- `I3xI3`
  { pLower := 7/10, pUpper := 3/4, wLower := 7/10, wUpper := 3/4,
    alpha₀ := 1884 / 10000, alpha₁ := 2465 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1125 / 10000, alpha₅ := 1124 / 10000,
    etaP := 4632 / 10000, etaW := 4632 / 10000,
    factor := tenThousandthFactor ![
      ![-9301, -4545, -3859, -4544, -3859],
      ![0, -5841, -5846, 5841, 5846],
      ![0, -2317, 2315, 2318, -2316]] },
  -- `I3xI4`
  { pLower := 7/10, pUpper := 3/4, wLower := 3/4, wUpper := 4/5,
    alpha₀ := 1883 / 10000, alpha₁ := 2402 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1098 / 10000, alpha₅ := 1123 / 10000,
    etaP := 4657 / 10000, etaW := 4320 / 10000,
    factor := tenThousandthFactor ![
      ![-9317, -5051, -4368, -3918, -3133],
      ![-960, 5437, 5494, -6145, -5883],
      ![-73, -2272, 2360, 2294, -2280]] },
  -- `I3xI5`
  { pLower := 7/10, pUpper := 3/4, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1880 / 10000, alpha₁ := 2314 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1216 / 10000, alpha₄ := 1060 / 10000, alpha₅ := 1120 / 10000,
    etaP := 4694 / 10000, etaW := 3916 / 10000,
    factor := tenThousandthFactor ![
      ![-9262, -5488, -4808, -3293, -2427],
      ![-1905, 5038, 5140, -6324, -5727],
      ![-163, -2214, 2415, 2265, -2227]] },
  -- `I3xI6`
  { pLower := 7/10, pUpper := 3/4, wLower := 9/10, wUpper := 1,
    alpha₀ := 1880 / 10000, alpha₁ := 2211 / 10000, alpha₂ := 1217 / 10000,
    alpha₃ := 1213 / 10000, alpha₄ := 1012 / 10000, alpha₅ := 1113 / 10000,
    etaP := 4738 / 10000, etaW := 3471 / 10000,
    factor := tenThousandthFactor ![
      ![-9193, -5776, -5097, -2813, -1888],
      ![-2647, 4757, 4889, -6353, -5395],
      ![-273, -2145, 2480, 2253, -2163]] },
  -- `I4xI4`
  { pLower := 3/4, pUpper := 4/5, wLower := 3/4, wUpper := 4/5,
    alpha₀ := 1885 / 10000, alpha₁ := 2344 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1095 / 10000, alpha₅ := 1096 / 10000,
    etaP := 4341 / 10000, etaW := 4342 / 10000,
    factor := tenThousandthFactor ![
      ![-9433, -4451, -3646, -4452, -3646],
      ![1, 5797, 5595, -5797, -5594],
      ![0, -2250, 2331, 2249, -2331]] },
  -- `I4xI5`
  { pLower := 3/4, pUpper := 4/5, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1883 / 10000, alpha₁ := 2259 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1058 / 10000, alpha₅ := 1093 / 10000,
    etaP := 4376 / 10000, etaW := 3939 / 10000,
    factor := tenThousandthFactor ![
      ![-9464, -4949, -4127, -3808, -2895],
      ![-1007, 5418, 5273, -6059, -5515],
      ![-96, -2185, 2392, 2219, -2280]] },
  -- `I4xI6`
  { pLower := 3/4, pUpper := 4/5, wLower := 9/10, wUpper := 1,
    alpha₀ := 1880 / 10000, alpha₁ := 2159 / 10000, alpha₂ := 1218 / 10000,
    alpha₃ := 1215 / 10000, alpha₄ := 1012 / 10000, alpha₅ := 1087 / 10000,
    etaP := 4425 / 10000, etaW := 3487 / 10000,
    factor := tenThousandthFactor ![
      ![-9449, -5313, -4474, -3261, -2274],
      ![-1861, 5117, 5011, -6156, -5253],
      ![-200, -2105, 2448, 2200, -2222]] },
  -- `I5xI5`
  { pLower := 4/5, pUpper := 9/10, wLower := 4/5, wUpper := 9/10,
    alpha₀ := 1882 / 10000, alpha₁ := 2180 / 10000, alpha₂ := 1217 / 10000,
    alpha₃ := 1217 / 10000, alpha₄ := 1056 / 10000, alpha₅ := 1055 / 10000,
    etaP := 3970 / 10000, etaW := 3969 / 10000,
    factor := tenThousandthFactor ![
      ![-9605, -4327, -3370, -4324, -3368],
      ![-2, 5736, 5258, -5737, -5259],
      ![0, -2150, 2345, 2149, -2345]] },
  -- `I5xI6`
  { pLower := 4/5, pUpper := 9/10, wLower := 9/10, wUpper := 1,
    alpha₀ := 1881 / 10000, alpha₁ := 2086 / 10000, alpha₂ := 1217 / 10000,
    alpha₃ := 1214 / 10000, alpha₄ := 1008 / 10000, alpha₅ := 1049 / 10000,
    etaP := 4012 / 10000, etaW := 3517 / 10000,
    factor := tenThousandthFactor ![
      ![-9667, -4734, -3741, -3758, -2701],
      ![-905, 5453, 5025, -5906, -5061],
      ![-108, -2067, 2414, 2126, -2292]] },
  -- `I6xI6`
  { pLower := 9/10, pUpper := 1, wLower := 9/10, wUpper := 1,
    alpha₀ := 1880 / 10000, alpha₁ := 1999 / 10000, alpha₂ := 1216 / 10000,
    alpha₃ := 1216 / 10000, alpha₄ := 1003 / 10000, alpha₅ := 1003 / 10000,
    etaP := 3557 / 10000, etaW := 3558 / 10000,
    factor := tenThousandthFactor ![
      ![-9814, -4176, -3058, -4176, -3059],
      ![0, 5666, 4873, -5666, -4873],
      ![0, -2034, 2366, 2034, -2364]] },
  -- `I2aI2a`
  { pLower := 3/5, pUpper := 13/20, wLower := 3/5, wUpper := 13/20,
    alpha₀ := 1887 / 10000, alpha₁ := 2758 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1218 / 10000, alpha₄ := 1184 / 10000, alpha₅ := 1183 / 10000,
    etaP := 5348 / 10000, etaW := 5350 / 10000,
    factor := tenThousandthFactor ![
      ![-9010, -4741, -4351, -4780, -4399],
      ![-32, -5966, -6453, 5933, 6430],
      ![4, -2474, 2282, 2478, -2292]] },
  -- `I2aI2b`
  { pLower := 3/5, pUpper := 13/20, wLower := 13/20, wUpper := 7/10,
    alpha₀ := 1883 / 10000, alpha₁ := 2681 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1152 / 10000, alpha₅ := 1181 / 10000,
    etaP := 5378 / 10000, etaW := 4933 / 10000,
    factor := tenThousandthFactor ![
      ![-8827, -5954, -5696, -3245, -2657],
      ![-2139, 4784, 5350, -6732, -6858],
      ![-91, -2440, 2346, 2440, -2238]] },
  -- `I2bI2b`
  { pLower := 13/20, pUpper := 7/10, wLower := 13/20, wUpper := 7/10,
    alpha₀ := 1885 / 10000, alpha₁ := 2602 / 10000, alpha₂ := 1219 / 10000,
    alpha₃ := 1219 / 10000, alpha₄ := 1153 / 10000, alpha₅ := 1154 / 10000,
    etaP := 4960 / 10000, etaW := 4960 / 10000,
    factor := tenThousandthFactor ![
      ![-9165, -4649, -4101, -4641, -4094],
      ![-6, 5888, 6123, -5892, -6128],
      ![2, -2395, 2302, 2391, -2301]] }]

/-! ### Radius rectangles

The four box endpoints of each stored certificate, for the cover argument. -/

@[simp] theorem gramCertificates_pLower_0 :
    (gramCertificates 0).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_0 :
    (gramCertificates 0).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_0 :
    (gramCertificates 0).wLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_wUpper_0 :
    (gramCertificates 0).wUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_pLower_1 :
    (gramCertificates 1).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_1 :
    (gramCertificates 1).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_1 :
    (gramCertificates 1).wLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_wUpper_1 :
    (gramCertificates 1).wUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_pLower_2 :
    (gramCertificates 2).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_2 :
    (gramCertificates 2).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_2 :
    (gramCertificates 2).wLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_2 :
    (gramCertificates 2).wUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_pLower_3 :
    (gramCertificates 3).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_3 :
    (gramCertificates 3).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_3 :
    (gramCertificates 3).wLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_3 :
    (gramCertificates 3).wUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_pLower_4 :
    (gramCertificates 4).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_4 :
    (gramCertificates 4).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_4 :
    (gramCertificates 4).wLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_wUpper_4 :
    (gramCertificates 4).wUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_pLower_5 :
    (gramCertificates 5).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_5 :
    (gramCertificates 5).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_5 :
    (gramCertificates 5).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_5 :
    (gramCertificates 5).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_6 :
    (gramCertificates 6).pLower = 967 / 2500 := rfl

@[simp] theorem gramCertificates_pUpper_6 :
    (gramCertificates 6).pUpper = 1 / 2 := rfl

@[simp] theorem gramCertificates_wLower_6 :
    (gramCertificates 6).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_6 :
    (gramCertificates 6).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_7 :
    (gramCertificates 7).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_7 :
    (gramCertificates 7).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_7 :
    (gramCertificates 7).wLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_wUpper_7 :
    (gramCertificates 7).wUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_pLower_8 :
    (gramCertificates 8).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_8 :
    (gramCertificates 8).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_8 :
    (gramCertificates 8).wLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_8 :
    (gramCertificates 8).wUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_pLower_9 :
    (gramCertificates 9).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_9 :
    (gramCertificates 9).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_9 :
    (gramCertificates 9).wLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_9 :
    (gramCertificates 9).wUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_pLower_10 :
    (gramCertificates 10).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_10 :
    (gramCertificates 10).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_10 :
    (gramCertificates 10).wLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_wUpper_10 :
    (gramCertificates 10).wUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_pLower_11 :
    (gramCertificates 11).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_11 :
    (gramCertificates 11).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_11 :
    (gramCertificates 11).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_11 :
    (gramCertificates 11).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_12 :
    (gramCertificates 12).pLower = 1 / 2 := rfl

@[simp] theorem gramCertificates_pUpper_12 :
    (gramCertificates 12).pUpper = 3 / 5 := rfl

@[simp] theorem gramCertificates_wLower_12 :
    (gramCertificates 12).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_12 :
    (gramCertificates 12).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_13 :
    (gramCertificates 13).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_13 :
    (gramCertificates 13).pUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_wLower_13 :
    (gramCertificates 13).wLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_13 :
    (gramCertificates 13).wUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_pLower_14 :
    (gramCertificates 14).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_14 :
    (gramCertificates 14).pUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_wLower_14 :
    (gramCertificates 14).wLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_wUpper_14 :
    (gramCertificates 14).wUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_pLower_15 :
    (gramCertificates 15).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_15 :
    (gramCertificates 15).pUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_wLower_15 :
    (gramCertificates 15).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_15 :
    (gramCertificates 15).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_16 :
    (gramCertificates 16).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_16 :
    (gramCertificates 16).pUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_wLower_16 :
    (gramCertificates 16).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_16 :
    (gramCertificates 16).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_17 :
    (gramCertificates 17).pLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_pUpper_17 :
    (gramCertificates 17).pUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_wLower_17 :
    (gramCertificates 17).wLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_17 :
    (gramCertificates 17).wUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_pLower_18 :
    (gramCertificates 18).pLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_pUpper_18 :
    (gramCertificates 18).pUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_wLower_18 :
    (gramCertificates 18).wLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_wUpper_18 :
    (gramCertificates 18).wUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_pLower_19 :
    (gramCertificates 19).pLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_pUpper_19 :
    (gramCertificates 19).pUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_wLower_19 :
    (gramCertificates 19).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_19 :
    (gramCertificates 19).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_20 :
    (gramCertificates 20).pLower = 7 / 10 := rfl

@[simp] theorem gramCertificates_pUpper_20 :
    (gramCertificates 20).pUpper = 3 / 4 := rfl

@[simp] theorem gramCertificates_wLower_20 :
    (gramCertificates 20).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_20 :
    (gramCertificates 20).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_21 :
    (gramCertificates 21).pLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_pUpper_21 :
    (gramCertificates 21).pUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_wLower_21 :
    (gramCertificates 21).wLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_wUpper_21 :
    (gramCertificates 21).wUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_pLower_22 :
    (gramCertificates 22).pLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_pUpper_22 :
    (gramCertificates 22).pUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_wLower_22 :
    (gramCertificates 22).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_22 :
    (gramCertificates 22).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_23 :
    (gramCertificates 23).pLower = 3 / 4 := rfl

@[simp] theorem gramCertificates_pUpper_23 :
    (gramCertificates 23).pUpper = 4 / 5 := rfl

@[simp] theorem gramCertificates_wLower_23 :
    (gramCertificates 23).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_23 :
    (gramCertificates 23).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_24 :
    (gramCertificates 24).pLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_24 :
    (gramCertificates 24).pUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_wLower_24 :
    (gramCertificates 24).wLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_24 :
    (gramCertificates 24).wUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_pLower_25 :
    (gramCertificates 25).pLower = 4 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_25 :
    (gramCertificates 25).pUpper = 9 / 10 := rfl

@[simp] theorem gramCertificates_wLower_25 :
    (gramCertificates 25).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_25 :
    (gramCertificates 25).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_26 :
    (gramCertificates 26).pLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_pUpper_26 :
    (gramCertificates 26).pUpper = 1 := rfl

@[simp] theorem gramCertificates_wLower_26 :
    (gramCertificates 26).wLower = 9 / 10 := rfl

@[simp] theorem gramCertificates_wUpper_26 :
    (gramCertificates 26).wUpper = 1 := rfl

@[simp] theorem gramCertificates_pLower_27 :
    (gramCertificates 27).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_27 :
    (gramCertificates 27).pUpper = 13 / 20 := rfl

@[simp] theorem gramCertificates_wLower_27 :
    (gramCertificates 27).wLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_wUpper_27 :
    (gramCertificates 27).wUpper = 13 / 20 := rfl

@[simp] theorem gramCertificates_pLower_28 :
    (gramCertificates 28).pLower = 3 / 5 := rfl

@[simp] theorem gramCertificates_pUpper_28 :
    (gramCertificates 28).pUpper = 13 / 20 := rfl

@[simp] theorem gramCertificates_wLower_28 :
    (gramCertificates 28).wLower = 13 / 20 := rfl

@[simp] theorem gramCertificates_wUpper_28 :
    (gramCertificates 28).wUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_pLower_29 :
    (gramCertificates 29).pLower = 13 / 20 := rfl

@[simp] theorem gramCertificates_pUpper_29 :
    (gramCertificates 29).pUpper = 7 / 10 := rfl

@[simp] theorem gramCertificates_wLower_29 :
    (gramCertificates 29).wLower = 13 / 20 := rfl

@[simp] theorem gramCertificates_wUpper_29 :
    (gramCertificates 29).wUpper = 7 / 10 := rfl


/-- Arithmetic validation for certificate 0. -/
theorem gramCertificates_valid_0 (j : Fin 30) (hj : j = 0) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 1. -/
theorem gramCertificates_valid_1 (j : Fin 30) (hj : j = 1) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 2. -/
theorem gramCertificates_valid_2 (j : Fin 30) (hj : j = 2) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 3. -/
theorem gramCertificates_valid_3 (j : Fin 30) (hj : j = 3) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 4. -/
theorem gramCertificates_valid_4 (j : Fin 30) (hj : j = 4) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 5. -/
theorem gramCertificates_valid_5 (j : Fin 30) (hj : j = 5) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 6. -/
theorem gramCertificates_valid_6 (j : Fin 30) (hj : j = 6) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 7. -/
theorem gramCertificates_valid_7 (j : Fin 30) (hj : j = 7) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 8. -/
theorem gramCertificates_valid_8 (j : Fin 30) (hj : j = 8) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 9. -/
theorem gramCertificates_valid_9 (j : Fin 30) (hj : j = 9) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 10. -/
theorem gramCertificates_valid_10 (j : Fin 30) (hj : j = 10) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 11. -/
theorem gramCertificates_valid_11 (j : Fin 30) (hj : j = 11) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 12. -/
theorem gramCertificates_valid_12 (j : Fin 30) (hj : j = 12) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 13. -/
theorem gramCertificates_valid_13 (j : Fin 30) (hj : j = 13) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 14. -/
theorem gramCertificates_valid_14 (j : Fin 30) (hj : j = 14) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 15. -/
theorem gramCertificates_valid_15 (j : Fin 30) (hj : j = 15) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 16. -/
theorem gramCertificates_valid_16 (j : Fin 30) (hj : j = 16) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 17. -/
theorem gramCertificates_valid_17 (j : Fin 30) (hj : j = 17) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 18. -/
theorem gramCertificates_valid_18 (j : Fin 30) (hj : j = 18) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 19. -/
theorem gramCertificates_valid_19 (j : Fin 30) (hj : j = 19) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 20. -/
theorem gramCertificates_valid_20 (j : Fin 30) (hj : j = 20) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 21. -/
theorem gramCertificates_valid_21 (j : Fin 30) (hj : j = 21) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 22. -/
theorem gramCertificates_valid_22 (j : Fin 30) (hj : j = 22) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 23. -/
theorem gramCertificates_valid_23 (j : Fin 30) (hj : j = 23) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 24. -/
theorem gramCertificates_valid_24 (j : Fin 30) (hj : j = 24) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 25. -/
theorem gramCertificates_valid_25 (j : Fin 30) (hj : j = 25) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 26. -/
theorem gramCertificates_valid_26 (j : Fin 30) (hj : j = 26) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 27. -/
theorem gramCertificates_valid_27 (j : Fin 30) (hj : j = 27) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 28. -/
theorem gramCertificates_valid_28 (j : Fin 30) (hj : j = 28) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Arithmetic validation for certificate 29. -/
theorem gramCertificates_valid_29 (j : Fin 30) (hj : j = 29) : (gramCertificates j).Valid := by
  fin_cases j <;> cases hj
  all_goals norm_num [gramCertificates, GramCertificate.Valid, GramCertificate.upperBound,
      dualRadialBound, balance₀, balance₁, balance₂, balance₃, balance₄,
      diagonal₀, diagonal₁, diagonal₂, diagonal₃, diagonal₄, factorGram, factorRow,
      Matrix.vecMulVec, residual, targetOffDiagonal, positivePart, negativePart,
      redFirstLower, blueFirstLower, tenThousandthFactor, barC, gramLambda, gramMu,
      gramFirstPenalty, gramSecondPenalty, weightedFirstPenalty, weightedSecondPenalty,
      weightedConstantTerm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons]

/-- Every stored certificate satisfies its arithmetic side conditions. -/
theorem gramCertificates_valid (i : Fin 30) : (gramCertificates i).Valid := by
  fin_cases i
  · exact gramCertificates_valid_0 _ rfl
  · exact gramCertificates_valid_1 _ rfl
  · exact gramCertificates_valid_2 _ rfl
  · exact gramCertificates_valid_3 _ rfl
  · exact gramCertificates_valid_4 _ rfl
  · exact gramCertificates_valid_5 _ rfl
  · exact gramCertificates_valid_6 _ rfl
  · exact gramCertificates_valid_7 _ rfl
  · exact gramCertificates_valid_8 _ rfl
  · exact gramCertificates_valid_9 _ rfl
  · exact gramCertificates_valid_10 _ rfl
  · exact gramCertificates_valid_11 _ rfl
  · exact gramCertificates_valid_12 _ rfl
  · exact gramCertificates_valid_13 _ rfl
  · exact gramCertificates_valid_14 _ rfl
  · exact gramCertificates_valid_15 _ rfl
  · exact gramCertificates_valid_16 _ rfl
  · exact gramCertificates_valid_17 _ rfl
  · exact gramCertificates_valid_18 _ rfl
  · exact gramCertificates_valid_19 _ rfl
  · exact gramCertificates_valid_20 _ rfl
  · exact gramCertificates_valid_21 _ rfl
  · exact gramCertificates_valid_22 _ rfl
  · exact gramCertificates_valid_23 _ rfl
  · exact gramCertificates_valid_24 _ rfl
  · exact gramCertificates_valid_25 _ rfl
  · exact gramCertificates_valid_26 _ rfl
  · exact gramCertificates_valid_27 _ rfl
  · exact gramCertificates_valid_28 _ rfl
  · exact gramCertificates_valid_29 _ rfl

end LeanPool.Besicovitch
