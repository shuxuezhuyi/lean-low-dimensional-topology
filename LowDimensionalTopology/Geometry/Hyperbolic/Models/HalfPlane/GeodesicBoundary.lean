/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Tactic

/-!
# Actual ideal endpoints, collinearity, and rays
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius

noncomputable section

/-- The actual embedding in the extended complex plane used in the source compactification. -/
def extendedHalfPlanePoint (z : ℍ) : OnePoint ℂ := ((z : ℂ) : OnePoint ℂ)

/-- Ideal ends are actual compactified closure points on the actual ideal boundary. -/
def HalfPlaneLine.idealEndpoints (L : HalfPlaneLine) : Set (OnePoint ℂ) :=
  closure (extendedHalfPlanePoint '' L.carrier) ∩ halfPlaneIdealBoundary

/-- A family is h-collinear when its actual points lie in one genuine h-line. -/
def HCollinear {ι : Type*} (p : ι → ℍ) : Prop :=
  ∃ L : HalfPlaneLine, ∀ i, p i ∈ L.carrier

/-- Finite points of the extended closure are exactly the ordinary Euclidean closure. -/
theorem onePoint_coe_preimage_closure_image (S : Set ℂ) :
    ((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (((↑) : ℂ → OnePoint ℂ) '' S) = closure S := by
  rw [OnePoint.isOpenMap_coe.preimage_closure_eq_closure_preimage OnePoint.continuous_coe,
    preimage_image_eq _ OnePoint.coe_injective]

/-- The actual imaginary-axis embedding of the real parameter line is Euclidean isometric. -/
theorem imaginaryEuclideanAxis_isometry : Isometry (fun t : ℝ => (t : ℂ) * Complex.I) := by
  apply Isometry.of_dist_eq
  intro s t
  rw [Complex.dist_eq, ← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs, Real.dist_eq]

/-- The finite complex image of the whole hyperbolic imaginary axis. -/
theorem imaginaryAxisParam_complex_range :
    range (fun t : ℝ => (imaginaryAxisParam t : ℂ)) =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Ioi 0 := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨Real.exp t, Real.exp_pos t, ?_⟩
    exact (imaginaryAxisParam_coe t).symm
  · rintro ⟨y, hy, rfl⟩
    refine ⟨Real.log y, ?_⟩
    change (imaginaryAxisParam (Real.log y) : ℂ) = (y : ℂ) * Complex.I
    rw [imaginaryAxisParam_coe, Real.exp_log hy]

/-- The Euclidean closure of the positive imaginary axis includes its finite zero endpoint. -/
theorem closure_imaginaryAxisParam_complex_range :
    closure (range (fun t : ℝ => (imaginaryAxisParam t : ℂ))) =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Ici 0 := by
  rw [imaginaryAxisParam_complex_range,
    imaginaryEuclideanAxis_isometry.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      imaginaryEuclideanAxis_isometry.continuous, closure_Ioi]

/-- The actual extended imaginary-axis trace, independent of an auxiliary Euclidean coordinate. -/
def extendedImaginaryAxis : Set (OnePoint ℂ) :=
  range (fun t : ℝ => extendedHalfPlanePoint (imaginaryAxisParam t))

/-- Exactly zero and infinity are the ideal endpoints of the full imaginary h-line. -/
theorem imaginaryAxis_idealEndpoints :
    closure extendedImaginaryAxis ∩ halfPlaneIdealBoundary = {((0 : ℂ) : OnePoint ℂ), ∞} := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    have hinfty : (∞ : OnePoint ℂ) ∈ closure extendedImaginaryAxis :=
      mem_closure_of_tendsto imaginaryAxisParam_tendsto_infty
        (Eventually.of_forall (fun t => mem_range_self t))
    simp [halfPlaneIdealBoundary, hinfty]
  | coe z =>
    have hcoerange : extendedImaginaryAxis = ((↑) : ℂ → OnePoint ℂ) ''
        range (fun t : ℝ => (imaginaryAxisParam t : ℂ)) := by
      ext q
      simp only [extendedImaginaryAxis, mem_range, mem_image, extendedHalfPlanePoint]
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨_, ⟨t, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩; exact ⟨t, rfl⟩
    have hclosure : ((z : ℂ) : OnePoint ℂ) ∈ closure extendedImaginaryAxis ↔
        z ∈ (fun y : ℝ => (y : ℂ) * Complex.I) '' Ici 0 := by
      rw [hcoerange, ← closure_imaginaryAxisParam_complex_range]
      exact Set.ext_iff.mp (onePoint_coe_preimage_closure_image _) z
    rw [mem_inter_iff, hclosure]
    simp only [halfPlaneIdealBoundary, mem_insert_iff, OnePoint.coe_ne_infty, false_or,
      OnePoint.coe_eq_coe, mem_image, mem_singleton_iff, or_false]
    constructor
    · rintro ⟨⟨y, hy, hzy⟩, v, hv, hvz⟩
      subst v
      change z.im = 0 at hv
      have him := congrArg Complex.im hzy
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, hv] at him
      have hz0 : z = 0 := by rw [← hzy, him]; simp
      exact hz0
    · rintro rfl
      exact ⟨⟨0, le_rfl, by simp⟩, 0, rfl, rfl⟩

/-- Every real invertible matrix preserves the actual ideal boundary in both directions. -/
theorem realMobiusMatrix_preimage_boundary (g : GL (Fin 2) ℝ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ⁻¹' halfPlaneIdealBoundary = halfPlaneIdealBoundary := by
  ext p
  constructor
  · intro hp
    have h := realMobiusMatrix_maps_boundary g⁻¹ hp
    simpa only [realMobiusMatrix_inv, Mobius.fractionalLinear_inv_apply] using h
  · intro hp
    exact realMobiusMatrix_maps_boundary g hp

/-- The compactified point trace is transported by the actual extended real Mobius homeomorphism. -/
theorem normalizerGeodesic_extended_image (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    extendedHalfPlanePoint '' range (normalizerGeodesic g) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) '' extendedImaginaryAxis := by
  ext p
  constructor
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    refine ⟨extendedHalfPlanePoint (imaginaryAxisParam t), mem_range_self t, ?_⟩
    exact (normalizerGeodesic_extended g hg t).symm
  · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
    exact ⟨normalizerGeodesic g t, mem_range_self t, normalizerGeodesic_extended g hg t⟩

/-- The ideal ends of the actual complete h-line are exactly its two genuine compactified limits. -/
theorem normalizerGeodesic_idealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) :
    closure (extendedHalfPlanePoint '' range (normalizerGeodesic g)) ∩ halfPlaneIdealBoundary =
      {Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ),
        Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞} := by
  rw [normalizerGeodesic_extended_image g hg]
  change closure (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹) '' extendedImaginaryAxis) ∩ _ = _
  rw [← Homeomorph.image_closure]
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) '' closure extendedImaginaryAxis) ∩ _ = _
  rw [← image_inter_preimage, realMobiusMatrix_preimage_boundary,
    imaginaryAxis_idealEndpoints, image_insert_eq, image_singleton]

/-- Every actual Euclidean half-plane h-line has precisely two distinct genuine ideal ends,
realized by the actual limits of a complete unit-speed parametrization. -/
theorem HalfPlaneLine.exists_idealEndpoints_pair (L : HalfPlaneLine) :
    ∃ (a b : OnePoint ℂ) (γ : ℝ → ℍ), a ≠ b ∧ a ∈ halfPlaneIdealBoundary ∧
      b ∈ halfPlaneIdealBoundary ∧ L.idealEndpoints = {a, b} ∧
      Isometry γ ∧ range γ = L.carrier ∧
      Tendsto (fun t => extendedHalfPlanePoint (γ t)) atBot (𝓝 a) ∧
      Tendsto (fun t => extendedHalfPlanePoint (γ t)) atTop (𝓝 b) := by
  obtain ⟨g, hg, hL⟩ := L.exists_normalizer
  let a := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ)
  let b := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞
  have hγ : range (normalizerGeodesic g) = L.carrier := by
    rw [range_normalizerGeodesic, ← hL]
  refine ⟨a, b, normalizerGeodesic g, ?_, realMobiusMatrix_real_mem_boundary g⁻¹ 0,
    realMobiusMatrix_infty_mem_boundary g⁻¹, ?_, normalizerGeodesic_isometry g hg, hγ,
    normalizerGeodesic_tendsto_first g hg, normalizerGeodesic_tendsto_last g hg⟩
  · intro he
    have hinj := (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹)).injective he
    exact (OnePoint.coe_ne_infty (0 : ℂ)) hinj
  · change closure (extendedHalfPlanePoint '' L.carrier) ∩ halfPlaneIdealBoundary = _
    rw [← hγ]
    exact normalizerGeodesic_idealEndpoints g hg

/-- The two-endedness assertion is an exact finite cardinality statement. -/
theorem HalfPlaneLine.ncard_idealEndpoints (L : HalfPlaneLine) : L.idealEndpoints.ncard = 2 := by
  obtain ⟨a, b, _, hab, _, _, hends, _⟩ := L.exists_idealEndpoints_pair
  rw [hends]
  exact Set.ncard_pair hab

theorem HalfPlaneLine.idealEndpoints_eq_of_normalizer (L : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hL : L.carrier = {z : ℍ | (g • z).re = 0}) :
    L.idealEndpoints = {Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ),
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞} := by
  have hγ : range (normalizerGeodesic g) = L.carrier := by
    rw [range_normalizerGeodesic, ← hL]
  change closure (extendedHalfPlanePoint '' L.carrier) ∩ halfPlaneIdealBoundary = _
  rw [← hγ]
  exact normalizerGeodesic_idealEndpoints g hg

/-- The actual boundary images determine the two compactified ends without computing a matrix inverse. -/
theorem HalfPlaneLine.idealEndpoints_eq_of_normalizer_images (L : HalfPlaneLine)
    (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (hL : L.carrier = {z : ℍ | (g • z).re = 0}) (a b : OnePoint ℂ)
    (ha : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a = ((0 : ℂ) : OnePoint ℂ))
    (hb : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b = ∞) : L.idealEndpoints = {a, b} := by
  have hzero : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ) = a := by
    rw [realMobiusMatrix_inv, ← ha, Mobius.fractionalLinear_inv_apply]
  have hinfty : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞ = b := by
    rw [realMobiusMatrix_inv, ← hb, Mobius.fractionalLinear_inv_apply]
  rw [L.idealEndpoints_eq_of_normalizer g hg hL, hzero, hinfty]

/-- The actual affine translation, directly as a real invertible matrix. -/
def horizontalAxisNormalizer (x : ℝ) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, -x; 0, 1] (by simp [Matrix.det_fin_two])

theorem horizontalAxisNormalizer_pos (x : ℝ) : 0 < (horizontalAxisNormalizer x).val.det := by
  simp [horizontalAxisNormalizer, Matrix.det_fin_two]

theorem horizontalAxisNormalizer_re (x : ℝ) (z : ℍ) :
    (horizontalAxisNormalizer x • z).re = z.re - x := by
  change ((horizontalAxisNormalizer x • z : ℍ) : ℂ).re = _
  rw [UpperHalfPlane.coe_smul_of_det_pos (by simpa using horizontalAxisNormalizer_pos x)]
  simp [horizontalAxisNormalizer, UpperHalfPlane.num, UpperHalfPlane.denom, sub_eq_add_neg]

theorem horizontalNormalizer_boundary (x r : ℝ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix (horizontalAxisNormalizer x))
      ((r : ℂ) : OnePoint ℂ) = (((r - x : ℝ) : ℂ) : OnePoint ℂ) := by
  rw [Mobius.fractionalLinear_coe]
  simp [complexifiedRealMobiusMatrix, horizontalAxisNormalizer, sub_eq_add_neg]

theorem horizontalNormalizer_boundary_infty (x : ℝ) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix (horizontalAxisNormalizer x))
      ∞ = ∞ := by
  rw [Mobius.fractionalLinear_infty]
  simp [complexifiedRealMobiusMatrix, horizontalAxisNormalizer]

theorem intervalNormalizer_boundary_left (a b : ℝ) (hab : a < b) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix (intervalNormalizer a b hab)) ((a : ℂ) : OnePoint ℂ) =
      ((0 : ℂ) : OnePoint ℂ) := by
  have hd : -(a : ℂ) + b ≠ 0 := by
    rw [← Complex.ofReal_neg, ← Complex.ofReal_add]
    exact_mod_cast (show -a + b ≠ 0 by linarith)
  rw [Mobius.fractionalLinear_coe]
  simp [complexifiedRealMobiusMatrix, intervalNormalizer, hd]

theorem intervalNormalizer_boundary_right (a b : ℝ) (hab : a < b) :
    Mobius.fractionalLinear (complexifiedRealMobiusMatrix (intervalNormalizer a b hab)) ((b : ℂ) : OnePoint ℂ) = ∞ := by
  rw [Mobius.fractionalLinear_coe]
  simp [complexifiedRealMobiusMatrix, intervalNormalizer]

/-- The actual vertical h-line has its finite real foot and infinity as its two ideal ends. -/
theorem vertical_idealEndpoints (x : ℝ) :
    (HalfPlaneLine.vertical x).idealEndpoints = {((x : ℂ) : OnePoint ℂ), ∞} := by
  apply (HalfPlaneLine.vertical x).idealEndpoints_eq_of_normalizer_images
    (horizontalAxisNormalizer x) (horizontalAxisNormalizer_pos x)
  · ext z
    change z.re = x ↔ (horizontalAxisNormalizer x • z).re = 0
    rw [horizontalAxisNormalizer_re]
    exact sub_eq_zero.symm
  · simpa only [sub_self, Complex.ofReal_zero] using horizontalNormalizer_boundary x x
  · exact horizontalNormalizer_boundary_infty x

/-- A real-centred semicircle has exactly its two actual real Euclidean endpoints. -/
theorem circle_idealEndpoints (c r : ℝ) (hr : 0 < r) :
    (HalfPlaneLine.circle c r hr).idealEndpoints =
      {(((c - r : ℝ) : ℂ) : OnePoint ℂ), (((c + r : ℝ) : ℂ) : OnePoint ℂ)} := by
  apply (HalfPlaneLine.circle c r hr).idealEndpoints_eq_of_normalizer_images
    (intervalNormalizer (c - r) (c + r) (by linarith)) (intervalNormalizer_pos _ _ _)
  · ext z
    exact (intervalNormalizer_circle_re_zero_iff c r hr z).symm
  · exact intervalNormalizer_boundary_left _ _ _
  · exact intervalNormalizer_boundary_right _ _ _

theorem realOnePoint_injective : Function.Injective (fun x : ℝ => ((x : ℂ) : OnePoint ℂ)) :=
  OnePoint.coe_injective.comp Complex.ofReal_injective

/-- Two genuine h-lines with the same two actual ideal ends are equal. -/
theorem HalfPlaneLine.idealEndpoints_injective : Function.Injective HalfPlaneLine.idealEndpoints := by
  intro L M heq
  cases L with
  | vertical x =>
    cases M with
    | vertical y =>
      rw [vertical_idealEndpoints, vertical_idealEndpoints, pair_eq_pair_iff] at heq
      rcases heq with ⟨hxy, _⟩ | ⟨hbad, _⟩
      · exact congrArg HalfPlaneLine.vertical (realOnePoint_injective hxy)
      · exact (OnePoint.coe_ne_infty (x : ℂ) hbad).elim
    | circle c r hr =>
      rw [vertical_idealEndpoints, circle_idealEndpoints, pair_eq_pair_iff] at heq
      rcases heq with ⟨_, hbad⟩ | ⟨_, hbad⟩
      · exact (OnePoint.coe_ne_infty ((c + r : ℝ) : ℂ) hbad.symm).elim
      · exact (OnePoint.coe_ne_infty ((c - r : ℝ) : ℂ) hbad.symm).elim
  | circle c r hr =>
    cases M with
    | vertical x =>
      rw [circle_idealEndpoints, vertical_idealEndpoints, pair_eq_pair_iff] at heq
      rcases heq with ⟨_, hbad⟩ | ⟨hbad, _⟩
      · exact (OnePoint.coe_ne_infty ((c + r : ℝ) : ℂ) hbad).elim
      · exact (OnePoint.coe_ne_infty ((c - r : ℝ) : ℂ) hbad).elim
    | circle d s hs =>
      rw [circle_idealEndpoints, circle_idealEndpoints, pair_eq_pair_iff] at heq
      rcases heq with ⟨hl, hu⟩ | ⟨hl, hu⟩
      · have hl' := realOnePoint_injective hl
        have hu' := realOnePoint_injective hu
        have hc : c = d := by linarith
        have hrs : r = s := by linarith
        subst d
        congr 1
      · have hl' := realOnePoint_injective hl
        have hu' := realOnePoint_injective hu
        exfalso
        linarith

/-- A vertical h-line and any h-line sharing an interior point and an ideal end coincide. -/
theorem vertical_eq_of_shared_ideal_and_interior (x : ℝ) (M : HalfPlaneLine) (z : ℍ)
    (hz : z ∈ (HalfPlaneLine.vertical x).carrier) (hzM : z ∈ M.carrier)
    (p : OnePoint ℂ) (hp : p ∈ (HalfPlaneLine.vertical x).idealEndpoints)
    (hpM : p ∈ M.idealEndpoints) : HalfPlaneLine.vertical x = M := by
  cases M with
  | vertical y =>
    change z.re = x at hz
    change z.re = y at hzM
    exact congrArg HalfPlaneLine.vertical (hz.symm.trans hzM)
  | circle c r hr =>
    rw [vertical_idealEndpoints] at hp
    simp only [mem_insert_iff, mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · rw [circle_idealEndpoints] at hpM
      have hboundary : x = c - r ∨ x = c + r := by
        simpa only [mem_insert_iff, mem_singleton_iff, realOnePoint_injective.eq_iff] using hpM
      have hnorm := norm_sub_real_eq_radius_sq hzM
      change z.re = x at hz
      rcases hboundary with h | h <;> rw [hz, h] at hnorm <;>
        exfalso <;> nlinarith [sq_pos_of_pos z.im_pos]
    · rw [circle_idealEndpoints] at hpM
      simp only [mem_insert_iff, mem_singleton_iff] at hpM
      rcases hpM with h | h
      · exact (OnePoint.coe_ne_infty ((c - r : ℝ) : ℂ) h.symm).elim
      · exact (OnePoint.coe_ne_infty ((c + r : ℝ) : ℂ) h.symm).elim

/-- A real boundary point and an actual common interior point determine a real-centred semicircle. -/
theorem circle_eq_of_shared_real_boundary_and_interior (c r d s : ℝ) (hr : 0 < r) (hs : 0 < s)
    (z : ℍ) (hzL : z ∈ (HalfPlaneLine.circle c r hr).carrier)
    (hzM : z ∈ (HalfPlaneLine.circle d s hs).carrier)
    (a : ℝ) (haL : (a - c) ^ 2 = r ^ 2) (haM : (a - d) ^ 2 = s ^ 2) :
    HalfPlaneLine.circle c r hr = HalfPlaneLine.circle d s hs := by
  have hnL := norm_sub_real_eq_radius_sq hzL
  have hnM := norm_sub_real_eq_radius_sq hzM
  by_cases hcd : c = d
  · subst d
    have hrs : r = s := by nlinarith
    congr 1
  · have hprod : (c - d) * (z.re - a) = 0 := by nlinarith
    have hre : z.re = a := sub_eq_zero.mp
      ((mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hcd))
    rw [hre] at hnL
    exfalso
    nlinarith [sq_pos_of_pos z.im_pos]

/-- Two genuine h-lines sharing an interior point and an ideal end are the same line. -/
theorem HalfPlaneLine.eq_of_shared_ideal_and_interior (L M : HalfPlaneLine) (z : ℍ)
    (hzL : z ∈ L.carrier) (hzM : z ∈ M.carrier) (p : OnePoint ℂ)
    (hpL : p ∈ L.idealEndpoints) (hpM : p ∈ M.idealEndpoints) : L = M := by
  cases L with
  | vertical x => exact vertical_eq_of_shared_ideal_and_interior x M z hzL hzM p hpL hpM
  | circle c r hr =>
    cases M with
    | vertical x => exact (vertical_eq_of_shared_ideal_and_interior x
        (.circle c r hr) z hzM hzL p hpM hpL).symm
    | circle d s hs =>
      have hcase (a : ℝ) (hp : p = ((a : ℂ) : OnePoint ℂ)) (ha : (a - c) ^ 2 = r ^ 2) :
          HalfPlaneLine.circle c r hr = HalfPlaneLine.circle d s hs := by
        rw [hp, circle_idealEndpoints] at hpM
        have hboundary : a = d - s ∨ a = d + s := by
          simpa only [mem_insert_iff, mem_singleton_iff, realOnePoint_injective.eq_iff] using hpM
        apply circle_eq_of_shared_real_boundary_and_interior c r d s hr hs z hzL hzM a ha
        rcases hboundary with h | h <;> rw [h] <;> ring
      rw [circle_idealEndpoints] at hpL
      simp only [mem_insert_iff, mem_singleton_iff] at hpL
      rcases hpL with h | h
      · exact hcase (c - r) h (by ring)
      · exact hcase (c + r) h (by ring)

theorem pair_eq_of_two_mem_ne {X : Type*} {a b p q : X}
    (hp : p ∈ ({a, b} : Set X)) (hq : q ∈ ({a, b} : Set X)) (hpq : p ≠ q) :
    ({a, b} : Set X) = {p, q} := by
  simp only [mem_insert_iff, mem_singleton_iff] at hp hq
  rw [pair_eq_pair_iff]
  aesop

/-- Distinct actual h-lines share at most one ideal endpoint. -/
theorem HalfPlaneLine.idealEndpoints_inter_subsingleton (L M : HalfPlaneLine) (hne : L ≠ M) :
    (L.idealEndpoints ∩ M.idealEndpoints).Subsingleton := by
  intro p hp q hq
  by_contra hpq
  obtain ⟨a, b, _, _, _, _, hL, _⟩ := L.exists_idealEndpoints_pair
  obtain ⟨c, d, _, _, _, _, hM, _⟩ := M.exists_idealEndpoints_pair
  have hL' : L.idealEndpoints = {p, q} := hL.trans
    (pair_eq_of_two_mem_ne (hL ▸ hp.1) (hL ▸ hq.1) hpq)
  have hM' : M.idealEndpoints = {p, q} := hM.trans
    (pair_eq_of_two_mem_ne (hM ▸ hp.2) (hM ▸ hq.2) hpq)
  exact hne (HalfPlaneLine.idealEndpoints_injective (hL'.trans hM'.symm))

/-- parallel h-lines have precisely one common ideal end. -/
def HalfPlaneLine.Parallel (L M : HalfPlaneLine) : Prop :=
  L ≠ M ∧ ∃ p : OnePoint ℂ, L.idealEndpoints ∩ M.idealEndpoints = {p}

/-- intersecting h-lines meet in the model and have no common ideal end. -/
def HalfPlaneLine.Intersecting (L M : HalfPlaneLine) : Prop :=
  L ≠ M ∧ Disjoint L.idealEndpoints M.idealEndpoints ∧ (L.carrier ∩ M.carrier).Nonempty

/-- disjoint h-lines have neither an interior nor an ideal endpoint in common. -/
def HalfPlaneLine.HDisjoint (L M : HalfPlaneLine) : Prop :=
  L ≠ M ∧ Disjoint L.idealEndpoints M.idealEndpoints ∧ Disjoint L.carrier M.carrier

/-- Every distinct pair belongs to at least one of the three actual source classes. -/
theorem HalfPlaneLine.classification (L M : HalfPlaneLine) (hne : L ≠ M) :
    L.Parallel M ∨ L.Intersecting M ∨ L.HDisjoint M := by
  by_cases hends : (L.idealEndpoints ∩ M.idealEndpoints).Nonempty
  · obtain ⟨p, hp⟩ := hends
    refine Or.inl ⟨hne, p, Set.eq_singleton_iff_unique_mem.mpr ⟨hp, ?_⟩⟩
    intro q hq
    exact L.idealEndpoints_inter_subsingleton M hne hq hp
  · have hd : Disjoint L.idealEndpoints M.idealEndpoints :=
      Set.disjoint_left.mpr (fun p hpL hpM => hends ⟨p, hpL, hpM⟩)
    by_cases hmeet : (L.carrier ∩ M.carrier).Nonempty
    · exact Or.inr (Or.inl ⟨hne, hd, hmeet⟩)
    · exact Or.inr (Or.inr ⟨hne, hd,
        Set.disjoint_left.mpr (fun z hzL hzM => hmeet ⟨z, hzL, hzM⟩)⟩)

/-- For distinct genuine h-lines, an interior intersection automatically excludes common ideal ends. -/
theorem HalfPlaneLine.intersecting_iff (L M : HalfPlaneLine) (hne : L ≠ M) :
    L.Intersecting M ↔ (L.carrier ∩ M.carrier).Nonempty := by
  constructor
  · exact fun h => h.2.2
  · intro hz
    obtain ⟨z, hzL, hzM⟩ := hz
    refine ⟨hne, Set.disjoint_left.mpr ?_, ⟨z, hzL, hzM⟩⟩
    intro p hpL hpM
    exact hne (L.eq_of_shared_ideal_and_interior M z hzL hzM p hpL hpM)

/-- Parallel h-lines cannot intersect inside the model. -/
theorem HalfPlaneLine.Parallel.disjoint_carriers {L M : HalfPlaneLine} (h : L.Parallel M) :
    Disjoint L.carrier M.carrier := by
  obtain ⟨hne, p, hp⟩ := h
  have hp' : p ∈ L.idealEndpoints ∩ M.idealEndpoints := hp.symm ▸ mem_singleton p
  apply Set.disjoint_left.mpr
  intro z hzL hzM
  exact hne (L.eq_of_shared_ideal_and_interior M z hzL hzM p hp'.1 hp'.2)

/-- The three source alternatives are mutually exclusive as well as exhaustive. -/
theorem HalfPlaneLine.classification_exclusive (L M : HalfPlaneLine) (hne : L ≠ M) :
    (L.Parallel M ∨ L.Intersecting M ∨ L.HDisjoint M) ∧
      ¬(L.Parallel M ∧ L.Intersecting M) ∧ ¬(L.Parallel M ∧ L.HDisjoint M) ∧
      ¬(L.Intersecting M ∧ L.HDisjoint M) := by
  refine ⟨L.classification M hne, ?_, ?_, ?_⟩
  · rintro ⟨hp, hi⟩
    obtain ⟨p, he⟩ := hp.2
    have hm : p ∈ L.idealEndpoints ∩ M.idealEndpoints := he.symm ▸ mem_singleton p
    exact Set.disjoint_left.mp hi.2.1 hm.1 hm.2
  · rintro ⟨hp, hd⟩
    obtain ⟨p, he⟩ := hp.2
    have hm : p ∈ L.idealEndpoints ∩ M.idealEndpoints := he.symm ▸ mem_singleton p
    exact Set.disjoint_left.mp hd.2.1 hm.1 hm.2
  · rintro ⟨hi, hd⟩
    obtain ⟨z, hzL, hzM⟩ := hi.2.2
    exact Set.disjoint_left.mp hd.2.2 hzL hzM

/-- The actual Cayley image set of an h-line, without presuming the pending native disc carrier adapter. -/
def cayleyHLineCarrier (L : HalfPlaneLine) : Set 𝔻 := halfPlaneToDisc '' L.carrier

def extendedDiscPoint (z : 𝔻) : OnePoint ℂ := ((z : ℂ) : OnePoint ℂ)

/-- The actual compactified ideal endpoint set of the actual Cayley image trace. -/
def cayleyHLineIdealEndpoints (L : HalfPlaneLine) : Set (OnePoint ℂ) :=
  closure (extendedDiscPoint '' cayleyHLineCarrier L) ∩ extendedDiscIdealBoundary

theorem extendedDiscPoint_cayleyHLine_image (L : HalfPlaneLine) :
    extendedDiscPoint '' cayleyHLineCarrier L = extendedCayley ''
      (extendedHalfPlanePoint '' L.carrier) := by
  rw [cayleyHLineCarrier, image_image, image_image]
  apply Set.image_congr
  intro z _
  exact (extendedCayley_halfPlane z).symm

theorem extendedCayley_preimage_idealBoundary :
    extendedCayley ⁻¹' extendedDiscIdealBoundary = halfPlaneIdealBoundary := by
  ext p
  exact (idealBoundary_cayley_iff p).symm

/-- Cayley transports actual compactified endpoint sets, not just two designated boundary labels. -/
theorem cayleyHLineIdealEndpoints_eq_image (L : HalfPlaneLine) :
    cayleyHLineIdealEndpoints L = extendedCayley '' L.idealEndpoints := by
  rw [cayleyHLineIdealEndpoints, extendedDiscPoint_cayleyHLine_image, ← extendedCayley.image_closure,
    ← image_inter_preimage, extendedCayley_preimage_idealBoundary]
  rfl

theorem ncard_cayleyHLineIdealEndpoints (L : HalfPlaneLine) :
    (cayleyHLineIdealEndpoints L).ncard = 2 := by
  obtain ⟨a, b, _, hab, _, _, he, _⟩ := L.exists_idealEndpoints_pair
  rw [cayleyHLineIdealEndpoints_eq_image, he, image_insert_eq, image_singleton]
  exact Set.ncard_pair (extendedCayley.injective.ne hab)

end

end LowDimensionalTopology.Geometry.Hyperbolic
