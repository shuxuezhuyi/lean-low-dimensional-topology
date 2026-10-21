/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.LineBisectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaNormalized
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Euclidean

/-- The strict distance comparison of concentric geodesics has its literal radial sign. -/
theorem abs_radius_ratio_lt_iff (Q s t : ℝ) (hQ : 0 ≤ Q) (hs : 0 < s) (ht : s < t) :
    |Q-s^2|/s < |Q-t^2|/t ↔ Q < s*t := by
  have ht0 : 0 < t := hs.trans ht
  rw [div_lt_div_iff₀ hs ht0,←sq_lt_sq₀ (by positivity : 0 ≤ |Q-s^2| * t)
    (by positivity : 0 ≤ |Q-t^2| * s),mul_pow,mul_pow,sq_abs,sq_abs]
  have hcoef : 0 < t^2-s^2 := by nlinarith
  have hst : 0 < s*t := mul_pos hs ht0
  have he : (Q-s^2)^2*t^2-(Q-t^2)^2*s^2 = (t^2-s^2)*(Q^2-(s*t)^2) := by ring
  constructor
  · intro h
    have hp : (t^2-s^2)*(Q^2-(s*t)^2) < 0 := by rw [←he];linarith only [h]
    have hh : Q^2-(s*t)^2 < 0 := neg_of_mul_neg_right hp hcoef.le
    nlinarith
  · intro h
    have hh : Q^2-(s*t)^2 < 0 := by nlinarith
    have hp : (t^2-s^2)*(Q^2-(s*t)^2) < 0 := mul_neg_of_pos_of_neg hcoef hh
    rw [←he] at hp
    linarith only [hp]

/-- The side of a geodesic semicircle with smaller Euclidean radius is genuinely hyperbolically convex. -/
theorem hConvex_inside_real_circle (c r : ℝ) (hr : 0 < r) :
    HConvex {z : ℍ | ‖(z:ℂ)-(c:ℂ)‖ < r} := by
  let g := intervalNormalizer (c-r) (c+r) (by linarith)
  have hpos (z : ℍ) : 0 < (g • z).re ↔ ‖(z:ℂ)-(c:ℂ)‖ < r := by
    rw [intervalNormalizer_re_circle c r hr z]
    have hd := UpperHalfPlane.normSq_denom_pos g z.im_ne_zero
    rw [lt_div_iff₀ hd,zero_mul]
    constructor <;> intro h <;> nlinarith [norm_nonneg ((z:ℂ)-(c:ℂ))]
  have he : {z : ℍ | ‖(z:ℂ)-(c:ℂ)‖ < r} = (g • · : ℍ → ℍ) ⁻¹' {z : ℍ | 0 < z.re} := by
    ext z
    exact (hpos z).symm
  have hright : HConvex {z : ℍ | 0 < z.re} := by
    let m := metricProbe 1 1 zero_lt_one
    have hm : 0 < m.re := by norm_num [m,metricProbe]
    rw [←openHHalfPlane_vertical_gt 0 m hm]
    exact openHHalfPlane_hConvex _ _ hm.ne'
  rw [he]
  exact hright.isometry_preimage (realGL_isometry g)

/-- True concentric-axis distance comparison is the inside of the geometric-mean circle. -/
theorem concentric_pointDist_lt_iff (s t : ℝ) (hs : 0 < s) (ht : s < t) (z : ℍ) :
    (HalfPlaneLine.circle 0 s hs).pointDist z <
      (HalfPlaneLine.circle 0 t (hs.trans ht)).pointDist z ↔ ‖(z:ℂ)‖^2 < s*t := by
  rw [←Real.sinh_lt_sinh,circleLine_pointDist_sinh,circleLine_pointDist_sinh]
  simp only [Complex.ofReal_zero,sub_zero]
  have he (a b : ℝ) : a/(2*z.im*s) < b/(2*z.im*t) ↔ a/s < b/t := by
    have ea : a/(2*z.im*s) = (a/s)/(2*z.im) := by ring
    have eb : b/(2*z.im*t) = (b/t)/(2*z.im) := by ring
    rw [ea,eb,div_lt_div_iff_of_pos_right (by positivity : 0 < 2*z.im)]
  rw [he,abs_radius_ratio_lt_iff _ s t (sq_nonneg _) hs ht]

/-- The complementary strict comparison is the exterior of the same geometric-mean circle. -/
theorem concentric_pointDist_gt_iff (s t : ℝ) (hs : 0 < s) (ht : s < t) (z : ℍ) :
    (HalfPlaneLine.circle 0 t (hs.trans ht)).pointDist z <
      (HalfPlaneLine.circle 0 s hs).pointDist z ↔ s*t < ‖(z:ℂ)‖^2 := by
  have ht0 : 0 < t := hs.trans ht
  have heq := concentric_bisectorSet s t hs (hs.trans ht) (ne_of_lt ht)
  have hle := concentric_pointDist_lt_iff s t hs ht z
  have he : (HalfPlaneLine.circle 0 s hs).pointDist z =
      (HalfPlaneLine.circle 0 t (hs.trans ht)).pointDist z ↔ ‖(z:ℂ)‖^2 = s*t := by
    change z ∈ (HalfPlaneLine.circle 0 s hs).bisectorSet (HalfPlaneLine.circle 0 t (hs.trans ht)) ↔ _
    rw [heq]
    change ‖(z:ℂ)-(0:ℂ)‖=Real.sqrt (s*t) ↔ _
    rw [sub_zero,←sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity : 0 ≤ s*t)]
  constructor
  · intro h
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with hz | hz
    · exact h.ne' (he.mpr hz)
    · exact h.not_ge ((hle.mpr hz).le)
  · intro h
    by_contra hn
    rcases (le_of_not_gt hn).eq_or_lt with hh | hh
    · exact h.ne' (he.mp hh)
    · exact h.not_ge ((hle.mp hh).le)

/-- Every closer-to-one-line region for two genuine disjoint geodesics is hyperbolically convex. -/
theorem HalfPlaneLine.closer_line_hConvex (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
    HConvex {z : ℍ | L.pointDist z < M.pointDist z} := by
  obtain ⟨g,s,t,hs,ht,_hg,hst,hL,hM⟩ := L.exists_concentric_normalizer M hd
  have he : {z : ℍ | L.pointDist z < M.pointDist z} = (g • · : ℍ → ℍ) ⁻¹'
      {z : ℍ | (HalfPlaneLine.circle 0 s hs).pointDist z < (HalfPlaneLine.circle 0 t ht).pointDist z} := by
    ext z
    change L.pointDist z < M.pointDist z ↔ (HalfPlaneLine.circle 0 s hs).pointDist (g • z) < (HalfPlaneLine.circle 0 t
      ht).pointDist (g • z)
    rw [L.pointDist_isometry_image _ _ (realGL_isometry g) hL,
      M.pointDist_isometry_image _ _ (realGL_isometry g) hM]
  rw [he]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isometry_preimage (f := (g • · : ℍ →
    ℍ)) _ (realGL_isometry g)
  rcases lt_or_gt_of_ne hst with hst | hts
  · have hset : {z : ℍ | (HalfPlaneLine.circle 0 s hs).pointDist z <
        (HalfPlaneLine.circle 0 t ht).pointDist z} = {z : ℍ | ‖(z:ℂ)-(0:ℂ)‖ < Real.sqrt (s*t)} := by
      ext z
      change (HalfPlaneLine.circle 0 s hs).pointDist z < (HalfPlaneLine.circle 0 t
        ht).pointDist z ↔ ‖(z:ℂ)-(0:ℂ)‖ < Real.sqrt (s*t)
      rw [concentric_pointDist_lt_iff s t hs hst,sub_zero,
        ←sq_lt_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),Real.sq_sqrt (by positivity : 0 ≤ s*t)]
    rw [hset]
    exact hConvex_inside_real_circle 0 (Real.sqrt (s*t)) (Real.sqrt_pos.mpr (by positivity))
  · have hset : {z : ℍ | (HalfPlaneLine.circle 0 s hs).pointDist z <
        (HalfPlaneLine.circle 0 t ht).pointDist z} = {z : ℍ | Real.sqrt (t*s) < ‖(z:ℂ)-(0:ℂ)‖} := by
      ext z
      change (HalfPlaneLine.circle 0 s hs).pointDist z < (HalfPlaneLine.circle 0 t
        ht).pointDist z ↔ Real.sqrt (t*s) < ‖(z:ℂ)-(0:ℂ)‖
      rw [concentric_pointDist_gt_iff t s ht hts,sub_zero,
        ←sq_lt_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _),Real.sq_sqrt (by positivity : 0 ≤ t*s)]
    rw [hset]
    exact hConvex_outside_circle 0 (Real.sqrt (t*s)) (Real.sqrt_pos.mpr (by positivity))

/-- The strict closer-line region is an actual complement component of the actual equidistant geodesic. -/
theorem HalfPlaneLine.closer_line_eq_openHalfPlane (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (w : ℍ) (hw : L.pointDist w < M.pointDist w) :
    ∃ B : HalfPlaneLine, L.bisectorSet M = B.carrier ∧
      {z : ℍ | L.pointDist z < M.pointDist z} = openHHalfPlane B w := by
  obtain ⟨B,hB⟩ := L.bisector_disjoint M hd
  refine ⟨B,hB,?_⟩
  have hwN : w ∈ B.carrierᶜ := by
    rw [←hB]
    exact hw.ne
  let f : ℍ → ℝ := fun z => L.pointDist z-M.pointDist z
  have hf : Continuous f := (Metric.continuous_infDist_pt L.carrier).sub
    (Metric.continuous_infDist_pt M.carrier)
  apply Subset.antisymm
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.isPreconnected (HalfPlaneLine.closer_line_hConvex L
    M hd)).subset_connectedComponentIn hw
    intro z hz hzB
    rw [←hB] at hzB
    exact hz.ne hzB
  · intro z hz
    have hconn := (isPreconnected_connectedComponentIn (F := B.carrierᶜ) (x := w)).image f hf.continuousOn
    have hwI := mem_image_of_mem f (mem_connectedComponentIn hwN)
    have hzI := mem_image_of_mem f hz
    by_contra hn
    have hwf : f w < 0 := sub_neg.mpr hw
    have hzf : 0 ≤ f z := sub_nonneg.mpr (le_of_not_gt hn)
    obtain ⟨u,hu,he⟩ := hconn.ordConnected.out hwI hzI ⟨hwf.le,hzf⟩
    have huB : u ∈ B.carrier := by
      rw [←hB]
      exact sub_eq_zero.mp he
    exact connectedComponentIn_subset B.carrierᶜ w hu huB

/-- Actual closer-line comparison and its boundary have one common oriented affine Klein equation. -/
theorem HalfPlaneLine.closer_line_affine (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (w : ℍ) (hw : L.pointDist w < M.pointDist w) :
    ∃ a : ℂ, ∃ t : ℝ, a ≠ 0 ∧
      (∀ z : ℍ, L.pointDist z < M.pointDist z ↔ inner ℝ a (halfPlaneKleinCoordinate z) < t) ∧
      (∀ z : ℍ, L.pointDist z = M.pointDist z ↔ inner ℝ a (halfPlaneKleinCoordinate z) = t) := by
  obtain ⟨B,hB,hS⟩ := HalfPlaneLine.closer_line_eq_openHalfPlane L M hd w hw
  have hwB : w ∉ B.carrier := by rw [←hB];exact hw.ne
  have hBD (z : ℍ) : z ∈ B.carrier ↔ halfPlaneToDisc z ∈ B.toDiscLine.carrier := by
    rw [B.toDiscLine_carrier,B.discCarrier_eq_cayley_image]
    constructor
    · exact mem_image_of_mem _
    · rintro ⟨u,hu,he⟩
      exact cayleyHomeomorph.injective he ▸ hu
  have hwD : halfPlaneToDisc w ∉ B.toDiscLine.carrier := fun hh => hwB ((hBD w).mpr hh)
  have hnear (z : ℍ) : L.pointDist z < M.pointDist z ↔
      halfPlaneToDisc z ∈ openDiscHalfPlane B.toDiscLine (halfPlaneToDisc w) := by
    rw [←cayley_image_openHHalfPlane B w hwB,←hS]
    constructor
    · intro hz
      exact ⟨z,hz,rfl⟩
    · rintro ⟨u,hu,he⟩
      exact cayleyHomeomorph.injective he ▸ hu
  obtain ⟨a,t,ha,hEq⟩ := B.toDiscLine.exists_klein_linear_equation
  have heq (z : ℍ) : L.pointDist z = M.pointDist z ↔ inner ℝ a (halfPlaneKleinCoordinate z) = t := by
    change z ∈ L.bisectorSet M ↔ _
    rw [hB,hBD]
    exact hEq _
  have hne : inner ℝ a (kleinCoordinate (halfPlaneToDisc w)) ≠ t :=
    fun hh => hwD ((hEq _).mpr hh)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · refine ⟨a,t,ha,?_,heq⟩
    intro z
    rw [hnear,connectedComponentIn_discLine_lt B.toDiscLine a t hEq _ hlt]
    rfl
  · refine ⟨-a,-t,neg_ne_zero.mpr ha,?_,?_⟩
    · intro z
      have hh : L.pointDist z < M.pointDist z ↔ t < inner ℝ a (halfPlaneKleinCoordinate z) := by
        rw [hnear,connectedComponentIn_discLine_gt B.toDiscLine a t hEq _ hgt]
        rfl
      simpa only [inner_neg_left,neg_lt_neg_iff] using hh
    · intro z
      simpa only [inner_neg_left,neg_inj] using heq z

/-- Weak and strict true line-distance cuts use the same regular Klein affine functional. -/
theorem HalfPlaneLine.closer_line_affine_le (L M : HalfPlaneLine) (hd : L.HDisjoint M)
    (w : ℍ) (hw : L.pointDist w < M.pointDist w) :
    ∃ a : ℂ, ∃ t : ℝ, a ≠ 0 ∧
      (∀ z : ℍ, L.pointDist z < M.pointDist z ↔ inner ℝ a (halfPlaneKleinCoordinate z) < t) ∧
      (∀ z : ℍ, L.pointDist z ≤ M.pointDist z ↔ inner ℝ a (halfPlaneKleinCoordinate z) ≤ t) := by
  obtain ⟨a,t,ha,hlt,heq⟩ := HalfPlaneLine.closer_line_affine L M hd w hw
  refine ⟨a,t,ha,hlt,fun z => ?_⟩
  rw [le_iff_lt_or_eq,le_iff_lt_or_eq,hlt,heq]

end LowDimensionalTopology.Geometry.Hyperbolic
