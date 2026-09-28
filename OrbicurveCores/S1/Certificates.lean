/-
Copyright (c) 2026 The orbicurve-cores contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The orbicurve-cores contributors
-/
import OrbicurveCores.S1.Rational

/-!
# The four Belyi certificates

For each of the four curves `y² = f(x)` of [Sijs] Table 4 (up to isomorphism over `ℚ`) the
rational function `G = N / D` of `Blueprint.md` §2.3c, with its certificate `RatCert`. The
witnesses (quotients, Bézout coefficients) were computed by `scripts/s1_certificates.py`; here
every identity is checked by `ring`.
-/

open Polynomial

set_option linter.unusedSimpArgs false

namespace OrbicurveCores.S1

/-! ### Case I -/

/-- The cubic of case I. -/
noncomputable def fI : ℂ[X] :=
  (X ^ 3 + 44 * X ^ 2 - 16 * X)
/-- `H` for case I. -/
noncomputable def IH : ℂ[X] :=
  (X ^ 4 + 48 * X ^ 3 + 224 * X ^ 2 - 768 * X + 256)
/-- `K` for case I. -/
noncomputable def IK : ℂ[X] :=
  (X ^ 6 + 72 * X ^ 5 + 1200 * X ^ 4 + 19200 * X ^ 2 - 18432 * X + 4096)
/-- The denominator of `G` for case I. -/
noncomputable def ID : ℂ[X] :=
  (1024 * X ^ 7 + 45056 * X ^ 6 - 16384 * X ^ 5)
/-- The numerator of `G` for case I. -/
noncomputable def IN : ℂ[X] := -IH ^ 3
/-- The critical cofactor for case I. -/
noncomputable def IR : ℂ[X] :=
  (-5120 * X ^ 4)

theorem certI : RatCert fI IN ID IH IK IR (-1) where
  c_ne := by norm_num
  hN := by simp only [IN, map_neg, map_one]; ring
  hK := by simp only [IN, ID, IH, IK, map_neg, map_one]; ring
  hcrit := by
    simp only [IN, ID, IH, IK, IR, derivative_mul, derivative_pow,
      derivative_add, derivative_sub, derivative_neg, derivative_X, derivative_ofNat,
      map_natCast, Nat.cast_ofNat, map_ofNat]
    ring
  f_dvd_D := ⟨
    (1024 * X ^ 4), by simp only [ID, fI]; ring⟩
  D_dvd_f := ⟨
    (X ^ 11 + 220 * X ^ 10 + 19280 * X ^ 9 + 837760 * X ^ 8
      + 17813760 * X ^ 7 + 137995264 * X ^ 6 - 285020160 * X ^ 5
      + 214466560 * X ^ 4 - 78970880 * X ^ 3 + 14417920 * X ^ 2
      - 1048576 * X),
    1024, by norm_num, by
    simp only [ID, fI, map_ofNat, map_one]; ring⟩
  R_dvd_f := ⟨
    (-X ^ 14 - 264 * X ^ 13 - 28944 * X ^ 12 - 1682560 * X ^ 11
      - 54366720 * X ^ 10 - 908396544 * X ^ 9 - 5501751296 * X ^ 8
      + 14534344704 * X ^ 7 - 13917880320 * X ^ 6 + 6891765760 * X ^ 5
      - 1896873984 * X ^ 4 + 276824064 * X ^ 3 - 16777216 * X ^ 2),
    5120, by norm_num, by
    simp only [IR, fI, map_ofNat, map_one]; ring⟩
  H_cop := ⟨
    (117 * X ^ 2 + 5192 * X + 80),
    (-117 * X ^ 3 - 5660 * X ^ 2 - 28336 * X + 79232),
    20480, by norm_num, by
    simp only [IH, fI, map_ofNat, map_neg]; ring⟩
  K_cop := ⟨
    (-3813 * X ^ 2 - 169136 * X + 500),
    (3813 * X ^ 5 + 275900 * X ^ 4 + 4674300 * X ^ 3 + 1672400 * X ^ 2
      + 73812800 * X - 43874816),
    2048000, by norm_num, by
    simp only [IK, fI, map_ofNat, map_neg]; ring⟩
  H_sqf := ⟨
    (5 * X ^ 3 + 244 * X ^ 2 + 1328 * X - 2240),
    (-20 * X ^ 2 - 736 * X - 2880),
    983040, by norm_num, by
    simp only [IH, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  K_sqf := ⟨
    (102 * X ^ 5 + 7391 * X ^ 4 + 125808 * X ^ 3 + 58144 * X ^ 2
      + 1988352 * X - 958720),
    (-612 * X ^ 4 - 37002 * X ^ 3 - 506664 * X ^ 2 - 234336 * X - 4037760),
    1132462080, by norm_num, by
    simp only [IK, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  deg := by
    have hH : natDegree IH = 4 := by unfold IH; compute_degree!
    have h1 : natDegree ID ≤ 11 := by unfold ID; compute_degree; all_goals norm_num
    have h2 : natDegree IN = 12 := by
      rw [IN, natDegree_neg, natDegree_pow, hH]
    omega
  D_ne := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [ID, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_ofNat, eval_zero] at h1
    norm_num at h1

/-! ### Case II -/

/-- The cubic of case II. -/
noncomputable def fII : ℂ[X] :=
  (X ^ 3 - 4 * X ^ 2 - 384 * X - 2304)
/-- `H` for case II. -/
noncomputable def IIH : ℂ[X] :=
  (X ^ 4 - 384 * X ^ 2 - 3072 * X)
/-- `K` for case II. -/
noncomputable def IIK : ℂ[X] :=
  (X ^ 6 - 576 * X ^ 4 - 4608 * X ^ 3 + 55296 * X ^ 2 + 884736 * X
      + 3538944)
/-- The denominator of `G` for case II. -/
noncomputable def IID : ℂ[X] :=
  (4096 * X ^ 6 + 98304 * X ^ 5 - 983040 * X ^ 4 - 54525952 * X ^ 3
      - 679477248 * X ^ 2 - 3623878656 * X - 7247757312)
/-- The numerator of `G` for case II. -/
noncomputable def IIN : ℂ[X] := IIH ^ 3
/-- The critical cofactor for case II. -/
noncomputable def IIR : ℂ[X] :=
  (24576 * X ^ 3 + 688128 * X ^ 2 + 6291456 * X + 18874368)

theorem certII : RatCert fII IIN IID IIH IIK IIR (1) where
  c_ne := by norm_num
  hN := by simp only [IIN, map_neg, map_one]; ring
  hK := by simp only [IIN, IID, IIH, IIK, map_neg, map_one]; ring
  hcrit := by
    simp only [IIN, IID, IIH, IIK, IIR, derivative_mul, derivative_pow,
      derivative_add, derivative_sub, derivative_neg, derivative_X, derivative_ofNat,
      map_natCast, Nat.cast_ofNat, map_ofNat]
    ring
  f_dvd_D := ⟨
    (4096 * X ^ 3 + 114688 * X ^ 2 + 1048576 * X + 3145728), by simp only [IID, fII]; ring⟩
  D_dvd_f := ⟨
    (X ^ 12 - 48 * X ^ 11 - 672 * X ^ 10 + 48896 * X ^ 9 + 315648 * X ^ 8
      - 21454848 * X ^ 7 - 169869312 * X ^ 6 + 4459069440 * X ^ 5
      + 56566480896 * X ^ 4 - 220150628352 * X ^ 3
      - 7044820107264 * X ^ 2 - 42268920643584 * X - 84537841287168),
    4096, by norm_num, by
    simp only [IID, fII, map_ofNat, map_one]; ring⟩
  R_dvd_f := ⟨
    (X ^ 15 - 52 * X ^ 14 - 864 * X ^ 13 + 67712 * X ^ 12
      + 488704 * X ^ 11 - 39945216 * X ^ 10 - 317915136 * X ^ 9
      + 12649955328 * X ^ 8 + 153391988736 * X ^ 7
      - 1767320322048 * X ^ 6 - 38159442247680 * X ^ 5
      - 59880970911744 * X ^ 4 + 3296975810199552 * X ^ 3
      + 32800682419421184 * X ^ 2 + 129850124217090048 * X
      + 194775186325635072),
    24576, by norm_num, by
    simp only [IIR, fII, map_ofNat, map_one]; ring⟩
  H_cop := ⟨
    (X ^ 2 - 22 * X - 24),
    (-X ^ 3 + 18 * X ^ 2 + 96 * X - 384),
    884736, by norm_num, by
    simp only [IIH, fII, map_ofNat, map_neg]; ring⟩
  K_cop := ⟨
    (-21 * X ^ 2 + 308 * X + 4672),
    (21 * X ^ 5 - 224 * X ^ 4 - 9600 * X ^ 3 + 4608 * X ^ 2 + 1087488 * X
      + 7077888),
    226492416, by norm_num, by
    simp only [IIK, fII, map_ofNat, map_neg]; ring⟩
  H_sqf := ⟨
    (-X ^ 3 + 16 * X ^ 2 + 192 * X - 768),
    (4 * X ^ 2 - 64 * X),
    2359296, by norm_num, by
    simp only [IIH, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  K_sqf := ⟨
    (17 * X ^ 5 - 192 * X ^ 4 - 7680 * X ^ 3 + 9216 * X ^ 2 + 866304 * X
      + 5013504),
    (-102 * X ^ 4 + 1152 * X ^ 3 + 26496 * X ^ 2 - 69120 * X - 1216512),
    130459631616, by norm_num, by
    simp only [IIK, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  deg := by
    have hH : natDegree IIH = 4 := by unfold IIH; compute_degree!
    have h1 : natDegree IID ≤ 11 := by unfold IID; compute_degree; all_goals norm_num
    have h2 : natDegree IIN = 12 := by
      rw [IIN, natDegree_pow, hH]
    omega
  D_ne := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [IID, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_ofNat, eval_zero] at h1
    norm_num at h1

/-! ### Case III -/

/-- The cubic of case III. -/
noncomputable def fIII : ℂ[X] :=
  (X ^ 3 - 16 * X)
/-- `H` for case III. -/
noncomputable def IIIH : ℂ[X] :=
  (X ^ 4 + 224 * X ^ 2 + 256)
/-- `K` for case III. -/
noncomputable def IIIK : ℂ[X] :=
  (X ^ 6 - 528 * X ^ 4 - 8448 * X ^ 2 + 4096)
/-- The denominator of `G` for case III. -/
noncomputable def IIID : ℂ[X] :=
  (X ^ 10 - 64 * X ^ 8 + 1536 * X ^ 6 - 16384 * X ^ 4 + 65536 * X ^ 2)
/-- The numerator of `G` for case III. -/
noncomputable def IIIN : ℂ[X] := IIIH ^ 3
/-- The critical cofactor for case III. -/
noncomputable def IIIR : ℂ[X] :=
  (2 * X ^ 7 - 96 * X ^ 5 + 1536 * X ^ 3 - 8192 * X)

theorem certIII : RatCert fIII IIIN IIID IIIH IIIK IIIR (1) where
  c_ne := by norm_num
  hN := by simp only [IIIN, map_neg, map_one]; ring
  hK := by simp only [IIIN, IIID, IIIH, IIIK, map_neg, map_one]; ring
  hcrit := by
    simp only [IIIN, IIID, IIIH, IIIK, IIIR, derivative_mul, derivative_pow,
      derivative_add, derivative_sub, derivative_neg, derivative_X, derivative_ofNat,
      map_natCast, Nat.cast_ofNat, map_ofNat]
    ring
  f_dvd_D := ⟨
    (X ^ 7 - 48 * X ^ 5 + 768 * X ^ 3 - 4096 * X), by simp only [IIID, fIII]; ring⟩
  D_dvd_f := ⟨
    (X ^ 8 - 32 * X ^ 6 + 256 * X ^ 4),
    1, by norm_num, by
    simp only [IIID, fIII, map_ofNat, map_one]; ring⟩
  R_dvd_f := ⟨
    (X ^ 11 - 48 * X ^ 9 + 768 * X ^ 7 - 4096 * X ^ 5),
    2, by norm_num, by
    simp only [IIIR, fIII, map_ofNat, map_one]; ring⟩
  H_cop := ⟨
    (-15 * X ^ 2 + 256),
    (15 * X ^ 3 + 3344 * X),
    65536, by norm_num, by
    simp only [IIIH, fIII, map_ofNat, map_neg]; ring⟩
  K_cop := ⟨
    (-65 * X ^ 2 + 1024),
    (65 * X ^ 5 - 34304 * X ^ 3 - 557312 * X),
    4194304, by norm_num, by
    simp only [IIIK, fIII, map_ofNat, map_neg]; ring⟩
  H_sqf := ⟨
    (-7 * X ^ 3 - 1552 * X),
    (28 * X ^ 2 + 3072),
    786432, by norm_num, by
    simp only [IIIH, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  K_sqf := ⟨
    (187 * X ^ 5 - 98560 * X ^ 3 - 1673984 * X),
    (-1122 * X ^ 4 + 393888 * X ^ 2 + 3538944),
    14495514624, by norm_num, by
    simp only [IIIK, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  deg := by
    have hH : natDegree IIIH = 4 := by unfold IIIH; compute_degree!
    have h1 : natDegree IIID ≤ 11 := by unfold IIID; compute_degree; all_goals norm_num
    have h2 : natDegree IIIN = 12 := by
      rw [IIIN, natDegree_pow, hH]
    omega
  D_ne := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [IIID, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_ofNat, eval_zero] at h1
    norm_num at h1

/-! ### Case IV -/

/-- The cubic of case IV. -/
noncomputable def fIV : ℂ[X] :=
  (X ^ 3 - 1728)
/-- `H` for case IV. -/
noncomputable def IVH : ℂ[X] :=
  (X ^ 4 + 13824 * X)
/-- `K` for case IV. -/
noncomputable def IVK : ℂ[X] :=
  (X ^ 6 - 34560 * X ^ 3 - 23887872)
/-- The denominator of `G` for case IV. -/
noncomputable def IVD : ℂ[X] :=
  (64 * X ^ 9 - 331776 * X ^ 6 + 573308928 * X ^ 3 - 330225942528)
/-- The numerator of `G` for case IV. -/
noncomputable def IVN : ℂ[X] := IVH ^ 3
/-- The critical cofactor for case IV. -/
noncomputable def IVR : ℂ[X] :=
  (192 * X ^ 6 - 663552 * X ^ 3 + 573308928)

theorem certIV : RatCert fIV IVN IVD IVH IVK IVR (1) where
  c_ne := by norm_num
  hN := by simp only [IVN, map_neg, map_one]; ring
  hK := by simp only [IVN, IVD, IVH, IVK, map_neg, map_one]; ring
  hcrit := by
    simp only [IVN, IVD, IVH, IVK, IVR, derivative_mul, derivative_pow,
      derivative_add, derivative_sub, derivative_neg, derivative_X, derivative_ofNat,
      map_natCast, Nat.cast_ofNat, map_ofNat]
    ring
  f_dvd_D := ⟨
    (64 * X ^ 6 - 221184 * X ^ 3 + 191102976), by simp only [IVD, fIV]; ring⟩
  D_dvd_f := ⟨
    (X ^ 9 - 5184 * X ^ 6 + 8957952 * X ^ 3 - 5159780352),
    64, by norm_num, by
    simp only [IVD, fIV, map_ofNat, map_one]; ring⟩
  R_dvd_f := ⟨
    (X ^ 12 - 6912 * X ^ 9 + 17915904 * X ^ 6 - 20639121408 * X ^ 3
      + 8916100448256),
    192, by norm_num, by
    simp only [IVR, fIV, map_ofNat, map_one]; ring⟩
  H_cop := ⟨
    (X ^ 2),
    (-X ^ 3 - 15552),
    26873856, by norm_num, by
    simp only [IVH, fIV, map_ofNat, map_neg]; ring⟩
  K_cop := ⟨
    (-1),
    (X ^ 3 - 32832),
    80621568, by norm_num, by
    simp only [IVK, fIV, map_ofNat, map_neg]; ring⟩
  H_sqf := ⟨
    (X ^ 3 + 10368),
    (-4 * X ^ 2),
    143327232, by norm_num, by
    simp only [IVH, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  K_sqf := ⟨
    (-5 * X ^ 4 + 179712 * X),
    (30 * X ^ 3 - 559872),
    13374150672384, by norm_num, by
    simp only [IVK, derivative_mul, derivative_pow, derivative_add, derivative_sub,
      derivative_neg, derivative_X, derivative_ofNat, map_ofNat, map_neg,
      map_natCast, Nat.cast_ofNat]
    ring⟩
  deg := by
    have hH : natDegree IVH = 4 := by unfold IVH; compute_degree!
    have h1 : natDegree IVD ≤ 11 := by unfold IVD; compute_degree; all_goals norm_num
    have h2 : natDegree IVN = 12 := by
      rw [IVN, natDegree_pow, hH]
    omega
  D_ne := by
    intro h
    have h1 := congrArg (eval 1) h
    simp only [IVD, eval_mul, eval_pow, eval_add, eval_sub, eval_X, eval_ofNat, eval_zero] at h1
    norm_num at h1

end OrbicurveCores.S1
