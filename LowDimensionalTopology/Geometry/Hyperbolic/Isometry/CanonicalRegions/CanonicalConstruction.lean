/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.GeodesicRays
public import Mathlib.Algebra.QuadraticDiscriminant
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine ideal-to-ideal geodesic has two distinct ideal ends. -/
theorem idealHSegment_self_empty (p : Mobius.ExtendedComplex) : idealHSegment p p = ∅ := by
  ext z
  constructor
  · rintro ⟨L,hL,_hz⟩
    have hc := L.ncard_idealEndpoints
    simp [hL] at hc
  · intro h
    exact h.elim

/-- The geodesic between a real ideal point and infinity is the actual vertical line. -/
theorem idealHSegment_real_infty (p : ℝ) (z : ℍ) :
    z ∈ idealHSegment ((p : ℂ) : Mobius.ExtendedComplex) ∞ ↔ z.re=p := by
  rw [idealHSegment_eq_carrier (.vertical p) _ _ (vertical_idealEndpoints p)]
  rfl

theorem idealHSegment_comm (p q : Mobius.ExtendedComplex) : idealHSegment p q = idealHSegment q p := by
  ext z
  simp only [idealHSegment,Set.pair_comm]

/-- The literal semicircle equation for two real ideal endpoints, including the empty equal-endpoint case. -/
theorem idealHSegment_real_real (p q : ℝ) (z : ℍ) :
    z ∈ idealHSegment ((p : ℂ) : Mobius.ExtendedComplex) ((q : ℂ) : Mobius.ExtendedComplex) ↔
      (z.re-p)*(z.re-q)+z.im^2=0 := by
  have hordered (p q : ℝ) (hpq : p < q) :
      z ∈ idealHSegment ((p : ℂ) : Mobius.ExtendedComplex) ((q : ℂ) : Mobius.ExtendedComplex) ↔
        (z.re-p)*(z.re-q)+z.im^2=0 := by
    let c : ℝ := (p+q)/2
    let r : ℝ := (q-p)/2
    have hr : 0 < r := by dsimp [r]; linarith
    have hL : (HalfPlaneLine.circle c r hr).idealEndpoints =
        {((p : ℂ) : Mobius.ExtendedComplex),((q : ℂ) : Mobius.ExtendedComplex)} := by
      rw [circle_idealEndpoints]
      have hl : c-r=p := by dsimp [c,r]; ring
      have hu : c+r=q := by dsimp [c,r]; ring
      rw [hl,hu]
    rw [idealHSegment_eq_carrier (.circle c r hr) _ _ hL]
    change ‖(z : ℂ)-(c : ℂ)‖=r ↔ _
    rw [← sq_eq_sq₀ (norm_nonneg _) hr.le,← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      sub_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
    dsimp [c,r]
    constructor <;> intro h <;> nlinarith [h]
  rcases lt_trichotomy p q with hpq | rfl | hqp
  · exact hordered p q hpq
  · rw [idealHSegment_self_empty]
    simp only [Set.notMem_empty,false_iff]
    nlinarith [sq_nonneg (z.re-p),sq_pos_of_pos z.im_pos]
  · rw [idealHSegment_comm]
    simpa only [mul_comm] using hordered q p hqp

/-- A homogeneous real quadratic has a projective real root exactly when its discriminant is nonnegative. -/
theorem projective_quadratic_root_iff (a b c : ℝ) :
    (a=0 ∨ ∃ p : ℝ, a*p^2+b*p+c=0) ↔ 0 ≤ b^2-4*a*c := by
  by_cases ha : a=0
  · simpa [ha] using (iff_true_intro (sq_nonneg b)).symm
  · constructor
    · rintro (h | ⟨p,hp⟩)
      · exact (ha h).elim
      · have he : b^2-4*a*c=(2*a*p+b)^2 := by linear_combination -4*a*hp
        rw [he]
        positivity
    · intro hd
      right
      have hs : discrim a b c=Real.sqrt (b^2-4*a*c)*Real.sqrt (b^2-4*a*c) := by
        rw [Real.mul_self_sqrt hd]
        rfl
      obtain ⟨p,hp⟩ := exists_quadratic_eq_zero ha ⟨_,hs⟩
      exact ⟨p,by simpa only [pow_two] using hp⟩

/-- The real projective equation for an ideal point whose image-geodesic passes through z. -/
def hCanonicalEndpointPolynomial (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) (p : ℝ) : ℝ :=
  (A 0 0-A 1 0*z.re)*p^2 +
    (A 1 0*(z.re^2+z.im^2)-(A 0 0+A 1 1)*z.re+A 0 1)*p +
    (A 1 1*(z.re^2+z.im^2)-A 0 1*z.re)

/-- The endpoint discriminant is exactly the previously verified canonical-region quadratic. -/
theorem hCanonicalEndpointPolynomial_discriminant (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (A 1 0*(z.re^2+z.im^2)-(A 0 0+A 1 1)*z.re+A 0 1)^2-
      4*(A 0 0-A 1 0*z.re)*(A 1 1*(z.re^2+z.im^2)-A 0 1*z.re) =
        hCanonicalQuadratic A z^2-4*z.im^2 := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  unfold hCanonicalQuadratic
  linear_combination -4*z.im^2*hd

/-- The real special-linear boundary action, including every actual finite pole. -/
theorem realSLMobius_real_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (p : ℝ) :
    (realSLMobius A).val ((p : ℂ) : Mobius.ExtendedComplex) =
      if A 1 0*p+A 1 1=0 then ∞ else ((((A 0 0*p+A 0 1)/(A 1 0*p+A 1 1) : ℝ) : ℂ) : Mobius.ExtendedComplex) := by
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Mobius.fractionalLinear_coe]
  change (if (A 1 0 : ℂ)*(p : ℂ)+A 1 1=0 then ∞ else
    ((((A 0 0 : ℂ)*(p : ℂ)+A 0 1)/((A 1 0 : ℂ)*(p : ℂ)+A 1 1) : ℂ) : Mobius.ExtendedComplex)) = _
  have hden : (A 1 0 : ℂ)*(p : ℂ)+A 1 1 = ((A 1 0*p+A 1 1 : ℝ) : ℂ) := by push_cast; rfl
  rw [hden]
  simp only [Complex.ofReal_eq_zero]
  split_ifs
  · rfl
  · push_cast
    rfl

/-- The actual image of the ideal point infinity under a real special-linear matrix. -/
theorem realSLMobius_real_infty (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (realSLMobius A).val ∞ = if A 1 0=0 then ∞ else (((A 0 0/A 1 0 : ℝ) : ℂ) : Mobius.ExtendedComplex) := by
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,Mobius.fractionalLinear_infty]
  change (if (A 1 0 : ℂ)=0 then ∞ else (((A 0 0 : ℂ)/(A 1 0 : ℂ) : ℂ) : Mobius.ExtendedComplex)) = _
  simp only [Complex.ofReal_eq_zero]
  split_ifs
  · rfl
  · push_cast
    rfl

/-- The real finite endpoint equation is the actual ideal-to-image geodesic incidence relation. -/
theorem hCanonicalEndpointPolynomial_geodesic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (z : ℍ) (p : ℝ) :
    z ∈ idealHSegment ((p : ℂ) : Mobius.ExtendedComplex) ((realSLMobius A).val ((p : ℂ) : Mobius.ExtendedComplex)) ↔
      hCanonicalEndpointPolynomial A z p=0 := by
  rw [realSLMobius_real_apply]
  by_cases hd : A 1 0*p+A 1 1=0
  · rw [ite_eq_left hd,idealHSegment_real_infty]
    have hn : A 0 0*p+A 0 1 ≠ 0 := by
      intro hn
      have hdet := A.det_coe
      rw [Matrix.det_fin_two] at hdet
      have he : (A 0 0*p+A 0 1)*A 1 0-(A 1 0*p+A 1 1)*A 0 0 = -1 := by nlinarith [hdet]
      rw [hn,hd] at he
      norm_num at he
    have hpoly : hCanonicalEndpointPolynomial A z p=(A 0 0*p+A 0 1)*(p-z.re) := by
      unfold hCanonicalEndpointPolynomial
      linear_combination (z.re^2+z.im^2-p*z.re)*hd
    rw [hpoly,mul_eq_zero]
    simp only [hn,false_or]
    constructor <;> intro h <;> linarith
  · rw [ite_eq_right hd,idealHSegment_real_real]
    have hpoly : hCanonicalEndpointPolynomial A z p=(A 1 0*p+A 1 1)*
        ((z.re-p)*(z.re-(A 0 0*p+A 0 1)/(A 1 0*p+A 1 1))+z.im^2) := by
      unfold hCanonicalEndpointPolynomial
      field_simp [hd]
      ring
    rw [hpoly,mul_eq_zero]
    simp only [hd,false_or]

/-- The homogeneous infinite-endpoint equation is the genuine vertical geodesic incidence relation. -/
theorem hCanonicalEndpointPolynomial_infty (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    z ∈ idealHSegment ∞ ((realSLMobius A).val ∞) ↔ A 0 0-A 1 0*z.re=0 := by
  rw [realSLMobius_real_infty]
  by_cases hc : A 1 0=0
  · rw [ite_eq_left hc,idealHSegment_self_empty]
    have ha : A 0 0 ≠ 0 := by
      intro ha
      have hd := A.det_coe
      rw [Matrix.det_fin_two,ha,hc] at hd
      norm_num at hd
    simp [hc,ha]
  · rw [ite_eq_right hc,idealHSegment_comm,idealHSegment_real_infty]
    rw [eq_div_iff hc]
    constructor <;> intro h <;> nlinarith [h]

/-- The actual family of h-lines joining every ideal point to its actual image. -/
def hBoundaryImageGeodesicUnion (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Set ℍ :=
  {z | ∃ p : Mobius.ExtendedComplex, p ∈ halfPlaneIdealBoundary ∧ z ∈ idealHSegment p ((realSLMobius A).val p)}

/-- Fixed ideal endpoints contribute no geodesic; the family is exactly its distinct-endpoint subfamily. -/
theorem hBoundaryImageGeodesicUnion_nonfixed (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    z ∈ hBoundaryImageGeodesicUnion A ↔
      ∃ p : Mobius.ExtendedComplex, p ∈ halfPlaneIdealBoundary ∧ p ≠ (realSLMobius A).val p ∧
        z ∈ idealHSegment p ((realSLMobius A).val p) := by
  constructor
  · rintro ⟨p,hp,hz⟩
    refine ⟨p,hp,?_,hz⟩
    intro he
    rw [← he,idealHSegment_self_empty] at hz
    exact hz.elim
  · rintro ⟨p,hp,_hne,hz⟩
    exact ⟨p,hp,hz⟩

/-- The full finite-and-infinite projective equation for the actual family of boundary-image geodesics. -/
theorem hBoundaryImageGeodesicUnion_projective (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    z ∈ hBoundaryImageGeodesicUnion A ↔
      A 0 0-A 1 0*z.re=0 ∨ ∃ p : ℝ, hCanonicalEndpointPolynomial A z p=0 := by
  constructor
  · rintro ⟨p,hp,hz⟩
    rw [halfPlaneIdealBoundary_eq_real_infty] at hp
    rcases hp with rfl | ⟨p,rfl⟩
    · exact Or.inl ((hCanonicalEndpointPolynomial_infty A z).mp hz)
    · exact Or.inr ⟨p,(hCanonicalEndpointPolynomial_geodesic A z p).mp hz⟩
  · rintro (hz | ⟨p,hp⟩)
    · exact ⟨∞,by simp [halfPlaneIdealBoundary],(hCanonicalEndpointPolynomial_infty A z).mpr hz⟩
    · refine ⟨((p : ℂ) : Mobius.ExtendedComplex),?_,(hCanonicalEndpointPolynomial_geodesic A z p).mpr hp⟩
      exact (coe_mem_halfPlaneIdealBoundary (p : ℂ)).mpr (by simp)

/-- Genuine incidence with the boundary-image geodesic family is exactly a nonnegative real discriminant. -/
theorem hBoundaryImageGeodesicUnion_quadratic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    z ∈ hBoundaryImageGeodesicUnion A ↔ 0 ≤ hCanonicalQuadratic A z^2-4*z.im^2 := by
  rw [hBoundaryImageGeodesicUnion_projective]
  have h := projective_quadratic_root_iff
    (A 0 0-A 1 0*z.re)
    (A 1 0*(z.re^2+z.im^2)-(A 0 0+A 1 1)*z.re+A 0 1)
    (A 1 1*(z.re^2+z.im^2)-A 0 1*z.re)
  rw [hCanonicalEndpointPolynomial_discriminant A z] at h
  exact h

/-- The source geometric construction: the canonical region is the complement of the actual ideal-image geodesics. -/
theorem hCanonicalRegion_geometric_construction (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : Matrix.trace A.val ≠ 0) : hCanonicalRegion A = (hBoundaryImageGeodesicUnion A)ᶜ := by
  ext z
  rw [hCanonicalRegion_mem_quadratic A ht,Set.mem_compl_iff,hBoundaryImageGeodesicUnion_quadratic,not_le]
  constructor
  · intro h
    have hs := (sq_lt_sq₀ (abs_nonneg (hCanonicalQuadratic A z)) (by positivity : 0 ≤ 2*z.im)).mpr h
    rw [sq_abs] at hs
    nlinarith
  · intro h
    apply (sq_lt_sq₀ (abs_nonneg (hCanonicalQuadratic A z)) (by positivity : 0 ≤ 2*z.im)).mp
    rw [sq_abs]
    nlinarith

/-- The geometric construction with exactly the source nonidentity and non-half-turn assumptions. -/
theorem hCanonicalRegion_geometric_construction_of_order_ne_two
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A ≠ 1)
    (horder : orderOf (realSLMobius A) ≠ 2) :
    hCanonicalRegion A = (hBoundaryImageGeodesicUnion A)ᶜ := by
  apply hCanonicalRegion_geometric_construction
  intro ht
  exact horder ((realSLMobius_order_two_iff_trace_zero A hA).mpr ht)

end LowDimensionalTopology.Geometry.Hyperbolic
