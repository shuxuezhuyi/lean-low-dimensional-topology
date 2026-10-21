/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleAltitude
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicRayUniqueness
@[expose] public section
noncomputable section
open Set
open scoped Topology UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The finite vertex in the ideal-altitude counterexample. -/
def idealAltitudeVertex : ℍ := ⟨(1 + Complex.I) / 2, by norm_num⟩

/-- Radius of the actual orthogonal circle through the finite vertex. -/
def idealAltitudeRadius : ℝ := Real.sqrt (1 / 2)

/-- Its perpendicular foot on the complete imaginary axis. -/
def idealAltitudeFoot : ℍ :=
  ⟨(idealAltitudeRadius : ℂ) * Complex.I, by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    exact Real.sqrt_pos.mpr (by norm_num)⟩

/-- The actual perpendicular h-line used in the counterexample. -/
def idealAltitudePerpendicular : HalfPlaneLine :=
  .circle 0 idealAltitudeRadius (Real.sqrt_pos.mpr (by norm_num))

/-- The chosen radius is strictly between zero and one. -/
theorem idealAltitudeRadius_bounds : 0 < idealAltitudeRadius ∧ idealAltitudeRadius < 1 := by
  have hs : idealAltitudeRadius ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < idealAltitudeRadius := Real.sqrt_pos.mpr (by norm_num)
  constructor
  · exact hp
  · nlinarith

/-- The finite vertex lies on the actual orthogonal circle. -/
theorem idealAltitudeVertex_mem_perpendicular : idealAltitudeVertex ∈ idealAltitudePerpendicular.carrier := by
  apply norm_sub_real_eq_of_sq idealAltitudeRadius_bounds.1
  have hs : idealAltitudeRadius ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
  norm_num [idealAltitudeVertex, hs]

/-- The exhibited foot is genuinely orthogonal in the canonical Euclidean tangent definition. -/
theorem idealAltitudeFoot_orthogonal :
    (HalfPlaneLine.vertical 0).OrthogonalAt idealAltitudePerpendicular idealAltitudeFoot := by
  have hpL : idealAltitudeFoot ∈ (HalfPlaneLine.vertical 0).carrier := by
    change (((idealAltitudeRadius : ℂ) * Complex.I).re) = 0
    simp
  have hpM : idealAltitudeFoot ∈ idealAltitudePerpendicular.carrier := by
    apply norm_sub_real_eq_of_sq idealAltitudeRadius_bounds.1
    change (((idealAltitudeRadius : ℂ) * Complex.I).re - 0) ^ 2 +
      (((idealAltitudeRadius : ℂ) * Complex.I).im) ^ 2 = idealAltitudeRadius ^ 2
    simp
  apply ((HalfPlaneLine.vertical 0).orthogonalAt_iff_coefficients
    idealAltitudePerpendicular idealAltitudeFoot hpL hpM).mpr
  rfl

/-- The complete imaginary-axis parametrization gives the actual ray from i to infinity. -/
theorem idealAltitude_base_ray :
    hRay UpperHalfPlane.I ∞ = forwardHLineRay imaginaryAxisParam 0 := by
  apply hRay_eq_of_isHLineRay
  have hrange : range imaginaryAxisParam = (HalfPlaneLine.vertical 0).carrier := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      rfl
    · intro hz
      refine ⟨Real.log z.im, ?_⟩
      apply UpperHalfPlane.ext
      apply Complex.ext
      · exact hz.symm
      · exact Real.exp_log z.im_pos
  refine ⟨imaginaryAxisParam, ⟨imaginaryAxisParam_isometry, ?_⟩, 0, ?_, Or.inl rfl,
    imaginaryAxis_forwardRay_idealEndpoints 0⟩
  · rw [hrange]
    exact (HalfPlaneLine.vertical 0).isHLine
  · apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [imaginaryAxisParam]

/-- The actual foot lies below the finite end of the genuine ray from i to infinity. -/
theorem idealAltitudeFoot_not_mem_base_ray : idealAltitudeFoot ∉ hRay UpperHalfPlane.I ∞ := by
  rw [idealAltitude_base_ray]
  intro hp
  have hm : (idealAltitudeFoot : ℂ) ∈ ((↑) : ℍ → ℂ) '' forwardHLineRay imaginaryAxisParam 0 :=
    ⟨idealAltitudeFoot, hp, rfl⟩
  rw [imaginaryAxis_forwardRay_complex_image] at hm
  obtain ⟨y, hy, he⟩ := hm
  have him := congrArg Complex.im he
  have heq : y = idealAltitudeRadius := by simpa [idealAltitudeFoot] using him
  have hy' : 1 ≤ y := by simpa using hy
  exact (not_le_of_gt idealAltitudeRadius_bounds.2) (heq ▸ hy')

/-- The finite vertices together with the ideal endpoint are not on a common genuine h-line. -/
theorem idealAltitude_vertices_noncollinear :
    ¬∃ L : HalfPlaneLine, idealAltitudeVertex ∈ L.carrier ∧ UpperHalfPlane.I ∈ L.carrier ∧
      (∞ : OnePoint ℂ) ∈ L.idealEndpoints := by
  rintro ⟨L, ha, hi, hinf⟩
  have hi0 : UpperHalfPlane.I ∈ (HalfPlaneLine.vertical 0).carrier := by simp [HalfPlaneLine.carrier]
  have hiinf : (∞ : OnePoint ℂ) ∈ (HalfPlaneLine.vertical 0).idealEndpoints := by
    rw [vertical_idealEndpoints]
    simp
  have he : L = HalfPlaneLine.vertical 0 :=
    L.eq_of_shared_ideal_and_interior _ UpperHalfPlane.I hi hi0 ∞ hinf hiinf
  rw [he] at ha
  change (((1 + Complex.I) / 2 : ℂ).re) = 0 at ha
  norm_num at ha

/-- Every genuine isometric ray has unbounded distance from its finite initial point. -/
theorem IsHLineRay.dist_unbounded {z : ℍ} {a : OnePoint ℂ} {R : Set ℍ}
    (hR : IsHLineRay z a R) (B : ℝ) : ∃ p ∈ R, B < dist z p := by
  obtain ⟨γ, hγ, s, hs, hor, _⟩ := hR
  rcases hor with rfl | rfl
  · refine ⟨γ (s + |B| + 1), ⟨s + |B| + 1, ?_, rfl⟩, ?_⟩
    · change s ≤ s + |B| + 1
      linarith [abs_nonneg B]
    · rw [← hs, hγ.1.dist_eq, Real.dist_eq, abs_of_nonpos (by linarith [abs_nonneg B])]
      linarith [le_abs_self B]
  · refine ⟨γ (s - |B| - 1), ⟨s - |B| - 1, ?_, rfl⟩, ?_⟩
    · change s - |B| - 1 ≤ s
      linarith [abs_nonneg B]
    · rw [← hs, hγ.1.dist_eq, Real.dist_eq, abs_of_nonneg (by linarith [abs_nonneg B])]
      linarith [le_abs_self B]

/-- The actual two ideal-incident sides both have unbounded hyperbolic length. -/
theorem idealAltitude_ideal_sides_unbounded (B : ℝ) :
    (∃ p ∈ hRay UpperHalfPlane.I ∞, B < dist UpperHalfPlane.I p) ∧
      ∃ p ∈ hRay idealAltitudeVertex ∞, B < dist idealAltitudeVertex p := by
  have hi : (∞ : OnePoint ℂ) ∈ halfPlaneIdealBoundary := by
    rw [halfPlaneIdealBoundary_eq_real_infty]
    exact Or.inl rfl
  exact ⟨(isHLineRay_hRay UpperHalfPlane.I ∞ hi).dist_unbounded B,
    (isHLineRay_hRay idealAltitudeVertex ∞ hi).dist_unbounded B⟩

/-- The actual ideal triangle has a perpendicular foot outside its genuine ideal-incident side. -/
theorem idealAltitude_counterexample :
    idealAltitudeVertex ∈ idealAltitudePerpendicular.carrier ∧
      (HalfPlaneLine.vertical 0).OrthogonalAt idealAltitudePerpendicular idealAltitudeFoot ∧
        idealAltitudeFoot ∉ hRay UpperHalfPlane.I ∞ ∧
          ¬∃ L : HalfPlaneLine, idealAltitudeVertex ∈ L.carrier ∧ UpperHalfPlane.I ∈ L.carrier ∧
            (∞ : OnePoint ℂ) ∈ L.idealEndpoints :=
  ⟨idealAltitudeVertex_mem_perpendicular, idealAltitudeFoot_orthogonal,
    idealAltitudeFoot_not_mem_base_ray, idealAltitude_vertices_noncollinear⟩

end LowDimensionalTopology.Geometry.Hyperbolic
