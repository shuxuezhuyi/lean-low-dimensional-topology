module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Trace.HalfTurnTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.IntersectingHyperbolicProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The actual half-turn about a genuine hyperbolic midpoint exchanges its endpoints. -/
theorem pointHalfTurnSL_smul_eq_of_isHMidpoint {a b m : ℍ}
    (hm : IsHMidpoint a b m) : pointHalfTurnSL m • a = b := by
  by_cases hab : a = b
  · subst b
    have hma : m = a := by
      simpa only [closedHSegment_self, mem_singleton_iff] using hm.1
    subst m
    exact pointHalfTurnSL_fixed a
  obtain ⟨q, ha, hb, hi⟩ := exists_sl2_ordered_imaginary a b hab
  have htriangle : dist (q • a) (q • m) + dist (q • m) (q • b) =
      dist (q • a) (q • b) := by
    simpa only [dist_smul] using dist_triangle_eq_of_mem_closedHSegment hm.1
  have hmre : (q • m).re = 0 :=
    ((dist_triangle_eq_iff_vertical_between (ha.trans hb.symm) hi.le).mp
      htriangle).1.trans ha
  have hequidistant : dist (q • m) (q • a) = dist (q • m) (q • b) := by
    rw [dist_smul, dist_smul, dist_comm m a]
    exact hm.2
  have hnorm := (vertical_equidistant_iff ha hb (ne_of_lt hi) (q • m)).mp
    hequidistant
  have hsquare : (q • m).im ^ 2 = (q • a).im * (q • b).im := by
    have h := congrArg (fun r : ℝ => r ^ 2) hnorm
    rw [Real.sq_sqrt (mul_pos (q • a).im_pos (q • b).im_pos).le,
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h
    change (q • m).re * (q • m).re + (q • m).im * (q • m).im = _ at h
    rw [hmre] at h
    simpa only [zero_mul, zero_add, pow_two] using h
  have hcenter : metricProbe 0 (q • m).im (q • m).im_pos = q • m := by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hmre.symm
    · rfl
  have haxis : IsHalfTurnAt (axisHalfTurnSL (q • m).im (q • m).im_pos) (q • m) := by
    rw [← hcenter]
    exact axisHalfTurnSL_at _ _
  have hmobius := ((pointHalfTurnSL_at m).conjugate q).unique haxis
  have haction : (q * pointHalfTurnSL m * q⁻¹) • (q • a) =
      axisHalfTurnSL (q • m).im (q • m).im_pos • (q • a) := by
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [← realSLMobius_action (q * pointHalfTurnSL m * q⁻¹) (q • a),
      ← realSLMobius_action
        (axisHalfTurnSL (q • m).im (q • m).im_pos) (q • a), hmobius]
  have haComplex : ((q • a : ℍ) : ℂ) = ((q • a).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa only [UpperHalfPlane.coe_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using ha
    · simp only [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have hbComplex : ((q • b : ℍ) : ℂ) = ((q • b).im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa only [UpperHalfPlane.coe_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero] using hb
    · simp only [UpperHalfPlane.coe_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero]
  have hsquareComplex : ((q • m).im : ℂ) ^ 2 =
      ((q • a).im : ℂ) * ((q • b).im : ℂ) := by
    exact_mod_cast hsquare
  have hswap : axisHalfTurnSL (q • m).im (q • m).im_pos • (q • a) = q • b := by
    apply UpperHalfPlane.ext
    rw [axisHalfTurnSL_coe, haComplex, hbComplex]
    apply (div_eq_iff (mul_ne_zero
      (Complex.ofReal_ne_zero.mpr (q • a).im_ne_zero) Complex.I_ne_zero)).mpr
    rw [hsquareComplex]
    calc
      -(((q • a).im : ℂ) * ((q • b).im : ℂ)) =
          (((q • b).im : ℂ) * ((q • a).im : ℂ)) * Complex.I ^ 2 := by
        rw [Complex.I_sq]
        ring
      _ = (((q • b).im : ℂ) * Complex.I) *
          (((q • a).im : ℂ) * Complex.I) := by ring
  apply MulAction.injective q
  calc
    q • (pointHalfTurnSL m • a) = (q * pointHalfTurnSL m * q⁻¹) • (q • a) := by
      simp only [mul_smul, inv_smul_smul]
    _ = axisHalfTurnSL (q • m).im (q • m).im_pos • (q • a) := haction
    _ = q • b := hswap


private theorem midpoint_eq_left_of_eq {a b m : ℍ}
    (hm : IsHMidpoint a b m) (hab : a = b) : m = a := by
  have ham : dist a m = 0 := by
    calc
      dist a m = dist a b / 2 := hm.half_distance.1
      _ = 0 := by rw [hab, dist_self, zero_div]
  exact (dist_eq_zero.mp ham).symm

private theorem midpoint_mem_line (L : HalfPlaneLine) {a b m : ℍ}
    (ha : a ∈ L.carrier) (hb : b ∈ L.carrier) (hm : IsHMidpoint a b m) :
    m ∈ L.carrier := by
  by_cases hab : a = b
  · rw [midpoint_eq_left_of_eq hm hab]
    exact ha
  · exact L.closedHSegment_subset hab ha hb hm.1

private theorem midpoint_symm {a b m : ℍ} (hm : IsHMidpoint a b m) :
    IsHMidpoint b a m := by
  by_cases hab : a = b
  · simpa only [hab] using hm
  refine ⟨(closedHSegment_comm hab) ▸ hm.1, ?_⟩
  calc
    dist b m = dist m b := dist_comm _ _
    _ = dist a m := hm.2.symm
    _ = dist m a := dist_comm _ _

private theorem pointHalfTurnSL_displacement (m z : ℍ) :
    dist z (pointHalfTurnSL m • z) = 2 * dist m z := by
  have hm := pointHalfTurnSL_at m
  have h := elliptic_actual_angle_radial (pointHalfTurnSL m) hm.elliptic z
  change Real.sinh (dist z (pointHalfTurnSL m • z) / 2) = _ at h
  rw [hm.rotation_angle, hm.center_eq, Real.sin_pi_div_two, one_mul] at h
  have he := Real.sinh_injective h
  linarith

private theorem pointHalfTurnSL_product_geometry (m n : ℍ) (hmn : m ≠ n) :
    let f := pointHalfTurnSL n * pointHalfTurnSL m
    ∃ (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2),
      hTranslationLength (hSLIsometry f) = 2 * dist m n ∧
        m ∈ (hHyperbolicAxis f hf ht).carrier ∧
        n ∈ (hHyperbolicAxis f hf ht).carrier := by
  let f := pointHalfTurnSL n * pointHalfTurnSL m
  have htr : Matrix.trace f.val = -2 * Real.cosh (dist m n) := by
    dsimp only [f]
    rw [pointHalfTurnSL_pair_trace, dist_comm n m]
  have hc : 1 < Real.cosh (dist m n) :=
    Real.one_lt_cosh.mpr (ne_of_gt (dist_pos.mpr hmn))
  have ht : 4 < (Matrix.trace f.val) ^ 2 := by
    rw [htr]
    nlinarith [sq_nonneg (Real.cosh (dist m n) - 1)]
  have hf : realSLMobius f ≠ 1 := by
    intro he
    have h := hSL_trace_sq_of_projection_one f he
    linarith
  have hpos := hHyperbolic_translationLength_pos f hf ht
  have hcosh : Real.cosh (hTranslationLength (hSLIsometry f) / 2) =
      Real.cosh (dist m n) := by
    calc
      Real.cosh (hTranslationLength (hSLIsometry f) / 2) =
          |Matrix.trace f.val| / 2 := (hHyperbolic_translation_abs_trace f hf ht).symm
      _ = Real.cosh (dist m n) := by
        rw [htr, abs_of_neg (by nlinarith [Real.cosh_pos (dist m n)])]
        ring
  have hT : hTranslationLength (hSLIsometry f) = 2 * dist m n := by
    have h := Real.cosh_injOn (show 0 ≤ hTranslationLength (hSLIsometry f) / 2 by positivity)
      dist_nonneg hcosh
    linarith
  have hm : dist m (f • m) = 2 * dist m n := by
    dsimp only [f]
    rw [mul_smul, pointHalfTurnSL_fixed]
    simpa only [dist_comm n m] using pointHalfTurnSL_displacement n m
  have hn : dist n (f • n) = 2 * dist m n := by
    dsimp only [f]
    rw [mul_smul]
    calc
      dist n (pointHalfTurnSL n • (pointHalfTurnSL m • n)) =
          dist (pointHalfTurnSL n • n) (pointHalfTurnSL n • (pointHalfTurnSL m • n)) := by
        rw [pointHalfTurnSL_fixed]
      _ = dist n (pointHalfTurnSL m • n) :=
        (isometry_smul ℍ (pointHalfTurnSL n)).dist_eq _ _
      _ = 2 * dist m n := pointHalfTurnSL_displacement m n
  exact ⟨hf, ht, hT, (hHyperbolic_translation_minimum f hf ht m).mp (hm.trans hT.symm),
    (hHyperbolic_translation_minimum f hf ht n).mp (hn.trans hT.symm)⟩

private theorem strict_midpoint_bound_of_left_ne (L M : HalfPlaneLine)
    (hLM : Disjoint L.carrier M.carrier) {a b c d m n : ℍ}
    (ha : a ∈ L.carrier) (hb : b ∈ L.carrier)
    (hc : c ∈ M.carrier) (hd : d ∈ M.carrier)
    (hm : IsHMidpoint a b m) (hn : IsHMidpoint c d n) (hab : a ≠ b) :
    2 * dist m n < dist a c + dist b d := by
  have hmL := midpoint_mem_line L ha hb hm
  have hnM := midpoint_mem_line M hc hd hn
  have hmn : m ≠ n := by
    intro he
    exact Set.disjoint_left.mp hLM (he ▸ hmL) hnM
  let f := pointHalfTurnSL n * pointHalfTurnSL m
  obtain ⟨hf, ht, hT, hmA, hnA⟩ := pointHalfTurnSL_product_geometry m n hmn
  have ham : a ≠ m := by
    intro he
    have h := hm.half_distance.1
    have hazero : dist a m = 0 := dist_eq_zero.mpr he
    have hz : dist a b = 0 := by linarith
    exact hab (dist_eq_zero.mp hz)
  have haA : a ∉ (hHyperbolicAxis f hf ht).carrier := by
    intro haxis
    have he := L.eq_of_two_points (hHyperbolicAxis f hf ht) ham ha hmL haxis hmA
    have hnL : n ∈ L.carrier := by rw [he]; exact hnA
    exact Set.disjoint_left.mp hLM hnL hnM
  have hbound : hTranslationLength (hSLIsometry f) ≤ dist a (f • a) := by
    change sInf (range (fun z : ℍ => dist z (f • z))) ≤ _
    exact csInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact dist_nonneg⟩ ⟨a, rfl⟩
  have hstrict : hTranslationLength (hSLIsometry f) < dist a (f • a) := by
    apply lt_of_le_of_ne hbound
    intro he
    exact haA ((hHyperbolic_translation_minimum f hf ht a).mp he.symm)
  have hswapA := pointHalfTurnSL_smul_eq_of_isHMidpoint hm
  have hswapB := pointHalfTurnSL_smul_eq_of_isHMidpoint (midpoint_symm hn)
  have hdist : dist c (f • a) = dist d b := by
    dsimp only [f]
    calc
      dist c ((pointHalfTurnSL n * pointHalfTurnSL m) • a) =
          dist (pointHalfTurnSL n • d) (pointHalfTurnSL n • b) := by
        rw [mul_smul, hswapA, hswapB]
      _ = dist d b := (isometry_smul ℍ (pointHalfTurnSL n)).dist_eq _ _
  calc
    2 * dist m n = hTranslationLength (hSLIsometry f) := hT.symm
    _ < dist a (f • a) := hstrict
    _ ≤ dist a c + dist c (f • a) := dist_triangle _ _ _
    _ = dist a c + dist b d := by rw [hdist, dist_comm d b]

/-- Genuine hyperbolic midpoints on disjoint complete geodesics satisfy midpoint
convexity. Equality occurs exactly when both original endpoint pairs coincide.
Disjointness concerns interior carriers and includes asymptotic geodesics. -/
theorem disjoint_hLines_midpoint_distance (L M : HalfPlaneLine)
    (hLM : Disjoint L.carrier M.carrier) {a b c d m n : ℍ}
    (ha : a ∈ L.carrier) (hb : b ∈ L.carrier)
    (hc : c ∈ M.carrier) (hd : d ∈ M.carrier)
    (hm : IsHMidpoint a b m) (hn : IsHMidpoint c d n) :
    dist m n ≤ (dist a c + dist b d) / 2 ∧
      (dist m n = (dist a c + dist b d) / 2 ↔ a = b ∧ c = d) := by
  by_cases hab : a = b
  · by_cases hcd : c = d
    · subst b
      subst d
      have hma := midpoint_eq_left_of_eq hm rfl
      have hnc := midpoint_eq_left_of_eq hn rfl
      rw [hma, hnc]
      refine ⟨by linarith, ?_⟩
      constructor
      · intro _
        exact ⟨rfl, rfl⟩
      · intro _
        ring
    · have hs := strict_midpoint_bound_of_left_ne M L hLM.symm hc hd ha hb hn hm hcd
      have hstrict : 2 * dist m n < dist a c + dist b d := by
        simpa only [dist_comm n m, dist_comm c a, dist_comm d b] using hs
      refine ⟨by linarith, ?_⟩
      constructor
      · intro he
        exfalso
        linarith
      · rintro ⟨_, he⟩
        exact (hcd he).elim
  · have hstrict := strict_midpoint_bound_of_left_ne L M hLM ha hb hc hd hm hn hab
    refine ⟨by linarith, ?_⟩
    constructor
    · intro he
      exfalso
      linarith
    · rintro ⟨he, _⟩
      exact (hab he).elim

/-- The same full statement for arbitrary genuine complete hyperbolic-line sets. -/
theorem disjoint_isHLine_midpoint_distance {L M : Set ℍ}
    (hL : IsHalfPlaneHLine L) (hM : IsHalfPlaneHLine M) (hLM : Disjoint L M)
    {a b c d m n : ℍ} (ha : a ∈ L) (hb : b ∈ L) (hc : c ∈ M) (hd : d ∈ M)
    (hm : IsHMidpoint a b m) (hn : IsHMidpoint c d n) :
    dist m n ≤ (dist a c + dist b d) / 2 ∧
      (dist m n = (dist a c + dist b d) / 2 ↔ a = b ∧ c = d) := by
  obtain ⟨L, rfl⟩ := exists_halfPlaneLine_of_isHLine hL
  obtain ⟨M, rfl⟩ := exists_halfPlaneLine_of_isHLine hM
  exact disjoint_hLines_midpoint_distance L M hLM ha hb hc hd hm hn

end LowDimensionalTopology.Geometry.Hyperbolic
