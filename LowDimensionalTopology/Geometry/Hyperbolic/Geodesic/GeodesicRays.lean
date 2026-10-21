/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicBoundary
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicOrthogonality
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

/-!
# Actual rays toward ideal endpoints
-/

@[expose] public section

open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius

/-- The actual closed forward half-line trace of a complete unit-speed h-line. -/
def forwardHLineRay (γ : ℝ → ℍ) (s : ℝ) : Set ℍ := γ '' Ici s

/-- The actual closed backward half-line trace. -/
def backwardHLineRay (γ : ℝ → ℍ) (s : ℝ) : Set ℍ := γ '' Iic s

theorem hLineRay_union (γ : ℝ → ℍ) (s : ℝ) :
    backwardHLineRay γ s ∪ forwardHLineRay γ s = range γ := by
  rw [backwardHLineRay, forwardHLineRay, ← image_union, Iic_union_Ici, image_univ]

theorem hLineRay_inter {γ : ℝ → ℍ} (hγ : Isometry γ) (s : ℝ) :
    backwardHLineRay γ s ∩ forwardHLineRay γ s = {γ s} := by
  rw [backwardHLineRay, forwardHLineRay, ← image_inter hγ.injective]
  have he : Iic s ∩ Ici s = ({s} : Set ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ici, mem_singleton_iff]
    exact le_antisymm_iff.symm
  rw [he, image_singleton]

theorem forwardHLineRay_isClosed {γ : ℝ → ℍ} (hγ : Isometry γ) (s : ℝ) :
    IsClosed (forwardHLineRay γ s) :=
  hγ.isClosedEmbedding.isClosedMap (Ici s) isClosed_Ici

theorem backwardHLineRay_isClosed {γ : ℝ → ℍ} (hγ : Isometry γ) (s : ℝ) :
    IsClosed (backwardHLineRay γ s) :=
  hγ.isClosedEmbedding.isClosedMap (Iic s) isClosed_Iic

/-- The actual finite Euclidean forward trace is a closed imaginary ray away from zero. -/
theorem imaginaryAxis_forwardRay_complex_image (s : ℝ) :
    ((↑) : ℍ → ℂ) '' forwardHLineRay imaginaryAxisParam s =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Ici (Real.exp s) := by
  rw [forwardHLineRay, image_image, ← Real.image_exp_Ici, image_image]
  apply Set.image_congr
  intro t _
  exact imaginaryAxisParam_coe t

/-- The actual finite Euclidean backward trace is the bounded positive imaginary interval. -/
theorem imaginaryAxis_backwardRay_complex_image (s : ℝ) :
    ((↑) : ℍ → ℂ) '' backwardHLineRay imaginaryAxisParam s =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Ioc 0 (Real.exp s) := by
  rw [backwardHLineRay, image_image, ← Real.image_exp_Iic, image_image]
  apply Set.image_congr
  intro t _
  exact imaginaryAxisParam_coe t

/-- Actual ideal boundary accumulation points of a genuine model trace. -/
def hTraceIdealEndpoints (S : Set ℍ) : Set (OnePoint ℂ) :=
  closure (extendedHalfPlanePoint '' S) ∩ halfPlaneIdealBoundary

theorem extendedHalfPlanePoint_image (S : Set ℍ) :
    extendedHalfPlanePoint '' S = ((↑) : ℂ → OnePoint ℂ) '' (((↑) : ℍ → ℂ) '' S) := by
  rw [image_image]
  rfl

/-- Finite ideal endpoints are detected by the ordinary Euclidean closure of the actual trace. -/
theorem hTraceIdealEndpoints_finite_iff (S : Set ℍ) (z : ℂ) :
    ((z : ℂ) : OnePoint ℂ) ∈ hTraceIdealEndpoints S ↔
      z ∈ closure (((↑) : ℍ → ℂ) '' S) ∧ z.im = 0 := by
  rw [hTraceIdealEndpoints, extendedHalfPlanePoint_image, mem_inter_iff, coe_mem_halfPlaneIdealBoundary]
  change (z ∈ ((↑) : ℂ → OnePoint ℂ) ⁻¹' closure (((↑) : ℂ → OnePoint ℂ) ''
    (((↑) : ℍ → ℂ) '' S)) ∧ z.im = 0) ↔ _
  rw [onePoint_coe_preimage_closure_image]

/-- Compact ordinary closure prevents an artificial new infinity accumulation point. -/
theorem onePoint_closure_image_of_compact_closure (S : Set ℂ) (hS : IsCompact (closure S)) :
    closure (((↑) : ℂ → OnePoint ℂ) '' S) = ((↑) : ℂ → OnePoint ℂ) '' closure S := by
  apply subset_antisymm
  · exact closure_minimal (image_mono subset_closure) (hS.image OnePoint.continuous_coe).isClosed
  · exact image_closure_subset_closure_image OnePoint.continuous_coe

theorem closure_imaginaryAxis_forwardRay_complex_image (s : ℝ) :
    closure (((↑) : ℍ → ℂ) '' forwardHLineRay imaginaryAxisParam s) =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Ici (Real.exp s) := by
  rw [imaginaryAxis_forwardRay_complex_image,
    imaginaryEuclideanAxis_isometry.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      imaginaryEuclideanAxis_isometry.continuous, isClosed_Ici.closure_eq]

theorem closure_imaginaryAxis_backwardRay_complex_image (s : ℝ) :
    closure (((↑) : ℍ → ℂ) '' backwardHLineRay imaginaryAxisParam s) =
      (fun y : ℝ => (y : ℂ) * Complex.I) '' Icc 0 (Real.exp s) := by
  rw [imaginaryAxis_backwardRay_complex_image,
    imaginaryEuclideanAxis_isometry.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
      imaginaryEuclideanAxis_isometry.continuous, closure_Ioc (ne_of_lt (Real.exp_pos s))]

/-- The actual forward half-line has only the infinity ideal end. -/
theorem imaginaryAxis_forwardRay_idealEndpoints (s : ℝ) :
    hTraceIdealEndpoints (forwardHLineRay imaginaryAxisParam s) = {∞} := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    have hinfty : (∞ : OnePoint ℂ) ∈ closure
        (extendedHalfPlanePoint '' forwardHLineRay imaginaryAxisParam s) :=
      mem_closure_of_tendsto imaginaryAxisParam_tendsto_infty
        ((eventually_ge_atTop s).mono (fun t ht =>
          ⟨imaginaryAxisParam t, ⟨t, ht, rfl⟩, rfl⟩))
    simp [hTraceIdealEndpoints, halfPlaneIdealBoundary, hinfty]
  | coe z =>
    rw [hTraceIdealEndpoints_finite_iff, closure_imaginaryAxis_forwardRay_complex_image]
    simp only [mem_singleton_iff, OnePoint.coe_ne_infty, iff_false]
    rintro ⟨⟨y, hy, he⟩, hz⟩
    have him := congrArg Complex.im he
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, hz] at him
    change Real.exp s ≤ y at hy
    linarith [Real.exp_pos s]

/-- The actual bounded backward half-line has only the zero ideal end. -/
theorem imaginaryAxis_backwardRay_idealEndpoints (s : ℝ) :
    hTraceIdealEndpoints (backwardHLineRay imaginaryAxisParam s) = {((0 : ℂ) : OnePoint ℂ)} := by
  ext p
  induction p using OnePoint.rec with
  | infty =>
    have hcompact : IsCompact (closure (((↑) : ℍ → ℂ) '' backwardHLineRay imaginaryAxisParam s)) := by
      rw [closure_imaginaryAxis_backwardRay_complex_image]
      exact isCompact_Icc.image imaginaryEuclideanAxis_isometry.continuous
    have hinfty : (∞ : OnePoint ℂ) ∉ closure
        (extendedHalfPlanePoint '' backwardHLineRay imaginaryAxisParam s) := by
      rw [extendedHalfPlanePoint_image, onePoint_closure_image_of_compact_closure _ hcompact]
      rintro ⟨z, _, hz⟩
      exact OnePoint.coe_ne_infty z hz
    simp [hTraceIdealEndpoints, hinfty]
  | coe z =>
    rw [hTraceIdealEndpoints_finite_iff, closure_imaginaryAxis_backwardRay_complex_image]
    simp only [mem_singleton_iff, OnePoint.coe_eq_coe]
    constructor
    · rintro ⟨⟨y, _, he⟩, hz⟩
      have him := congrArg Complex.im he
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, hz] at him
      rw [← he, him]
      simp
    · rintro rfl
      exact ⟨⟨0, ⟨le_rfl, (Real.exp_pos s).le⟩, by simp⟩, rfl⟩

/-- Real Mobius normalization transports the actual compactified trace of every parameter subset. -/
theorem normalizerGeodesic_extended_image_set (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (T : Set ℝ) :
    extendedHalfPlanePoint '' (normalizerGeodesic g '' T) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) '' (extendedHalfPlanePoint '' (imaginaryAxisParam ''
        T)) := by
  rw [image_image, image_image, image_image]
  apply Set.image_congr
  intro t _
  exact normalizerGeodesic_extended g hg t

/-- Every trace subset has its actual ideal accumulation set transported, including half-lines. -/
theorem normalizerGeodesic_traceIdealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det)
    (T : Set ℝ) :
    hTraceIdealEndpoints (normalizerGeodesic g '' T) =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) '' hTraceIdealEndpoints (imaginaryAxisParam '' T) := by
  rw [hTraceIdealEndpoints, normalizerGeodesic_extended_image_set g hg]
  change closure (Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹) '' _) ∩ _ = _
  rw [← Homeomorph.image_closure]
  change (Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) '' closure _) ∩ _ = _
  rw [← image_inter_preimage, realMobiusMatrix_preimage_boundary]
  rfl

/-- The forward half-line of the actual normalized geodesic approaches exactly its last ideal end. -/
theorem normalizerGeodesic_forwardRay_idealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (s : ℝ) :
    hTraceIdealEndpoints (forwardHLineRay (normalizerGeodesic g) s) =
      {Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞} := by
  rw [forwardHLineRay, normalizerGeodesic_traceIdealEndpoints g hg]
  change _ '' hTraceIdealEndpoints (forwardHLineRay imaginaryAxisParam s) = _
  rw [imaginaryAxis_forwardRay_idealEndpoints, image_singleton]

/-- The backward half-line approaches exactly the first ideal end. -/
theorem normalizerGeodesic_backwardRay_idealEndpoints (g : GL (Fin 2) ℝ) (hg : 0 < g.val.det) (s : ℝ) :
    hTraceIdealEndpoints (backwardHLineRay (normalizerGeodesic g) s) =
      {Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ)} := by
  rw [backwardHLineRay, normalizerGeodesic_traceIdealEndpoints g hg]
  change _ '' hTraceIdealEndpoints (backwardHLineRay imaginaryAxisParam s) = _
  rw [imaginaryAxis_backwardRay_idealEndpoints, image_singleton]

/-- A ray towards an ideal endpoint is an actual isometric half-line, with exactly that actual
compactified boundary accumulation point. The two allowed chart orientations are explicit. -/
def IsHLineRay (z : ℍ) (a : OnePoint ℂ) (R : Set ℍ) : Prop :=
  ∃ (γ : ℝ → ℍ), IsHGeodesicParam γ ∧ ∃ s : ℝ, γ s = z ∧
    (R = forwardHLineRay γ s ∨ R = backwardHLineRay γ s) ∧ hTraceIdealEndpoints R = {a}

/-- Every point of a genuine h-line has the two genuine rays toward its two actual ideal ends. -/
theorem HalfPlaneLine.exists_rays_at (L : HalfPlaneLine) (z : ℍ) (hz : z ∈ L.carrier) :
    ∃ (a b : OnePoint ℂ) (γ : ℝ → ℍ) (s : ℝ), a ≠ b ∧ L.idealEndpoints = {a, b} ∧
      IsHGeodesicParam γ ∧ range γ = L.carrier ∧ γ s = z ∧
      IsHLineRay z a (backwardHLineRay γ s) ∧ IsHLineRay z b (forwardHLineRay γ s) ∧
      backwardHLineRay γ s ∪ forwardHLineRay γ s = L.carrier ∧
      backwardHLineRay γ s ∩ forwardHLineRay γ s = {z} := by
  obtain ⟨g, hg, hL⟩ := L.exists_normalizer
  have hz0 : (g • z).re = 0 := by rw [hL] at hz; exact hz
  let a := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ((0 : ℂ) : OnePoint ℂ)
  let b := Mobius.fractionalLinear (complexifiedRealMobiusMatrix g⁻¹) ∞
  let γ := normalizerGeodesic g
  let s := Real.log (g • z).im
  have hγ : IsHGeodesicParam γ :=
    ⟨normalizerGeodesic_isometry g hg, normalizerGeodesic_isHLine g hg⟩
  have hs : γ s = z := normalizerGeodesic_parameter g z hz0
  have hrange : range γ = L.carrier := by rw [range_normalizerGeodesic, ← hL]
  refine ⟨a, b, γ, s, ?_, L.idealEndpoints_eq_of_normalizer g hg hL, hγ, hrange, hs,
    ⟨γ, hγ, s, hs, Or.inr rfl, normalizerGeodesic_backwardRay_idealEndpoints g hg s⟩,
    ⟨γ, hγ, s, hs, Or.inl rfl, normalizerGeodesic_forwardRay_idealEndpoints g hg s⟩, ?_, ?_⟩
  · intro he
    exact OnePoint.coe_ne_infty (0 : ℂ)
      ((Mobius.fractionalLinearHomeomorph (complexifiedRealMobiusMatrix g⁻¹)).injective he)
  · rw [hLineRay_union, hrange]
  · rw [hLineRay_inter hγ.1, hs]

/-- For every prescribed ideal end of an actual h-line there is a genuine ray from every line point. -/
theorem HalfPlaneLine.exists_ray_to_idealEndpoint (L : HalfPlaneLine) (z : ℍ)
    (hz : z ∈ L.carrier) (a : OnePoint ℂ) (ha : a ∈ L.idealEndpoints) :
    ∃ R : Set ℍ, IsHLineRay z a R ∧ R ⊆ L.carrier := by
  obtain ⟨b, c, γ, s, _, he, hγ, hrange, _, hb, hc, _, _⟩ := L.exists_rays_at z hz
  rw [he] at ha
  simp only [mem_insert_iff, mem_singleton_iff] at ha
  rcases ha with rfl | rfl
  · exact ⟨backwardHLineRay γ s, hb, (image_mono (subset_univ _)).trans (by rw [image_univ, hrange])⟩
  · exact ⟨forwardHLineRay γ s, hc, (image_mono (subset_univ _)).trans (by rw [image_univ, hrange])⟩

/-- Any two distinct actual ideal boundary points are the two ends of an actual h-line. -/
theorem exists_halfPlaneLine_of_idealEndpoints (a b : OnePoint ℂ)
    (ha : a ∈ halfPlaneIdealBoundary) (hb : b ∈ halfPlaneIdealBoundary) (hab : a ≠ b) :
    ∃ L : HalfPlaneLine, L.idealEndpoints = {a, b} := by
  rw [halfPlaneIdealBoundary_eq_real_infty] at ha hb
  rcases ha with rfl | ⟨a, rfl⟩
  · rcases hb with rfl | ⟨b, rfl⟩
    · exact (hab rfl).elim
    · exact ⟨.vertical b, (vertical_idealEndpoints b).trans (Set.pair_comm _ _)⟩
  · rcases hb with rfl | ⟨b, rfl⟩
    · exact ⟨.vertical a, vertical_idealEndpoints a⟩
    · have hne : a ≠ b := fun h => hab (congrArg (fun r : ℝ => ((r : ℂ) : OnePoint ℂ)) h)
      by_cases hlt : a < b
      · refine ⟨.circle ((a + b) / 2) ((b - a) / 2) (by linarith), ?_⟩
        rw [circle_idealEndpoints]
        have hl : (a + b) / 2 - (b - a) / 2 = a := by ring
        have hu : (a + b) / 2 + (b - a) / 2 = b := by ring
        rw [hl, hu]
      · have hgt : b < a := lt_of_le_of_ne (not_lt.mp hlt) hne.symm
        refine ⟨.circle ((a + b) / 2) ((a - b) / 2) (by linarith), ?_⟩
        rw [circle_idealEndpoints]
        have hl : (a + b) / 2 - (a - b) / 2 = b := by ring
        have hu : (a + b) / 2 + (a - b) / 2 = a := by ring
        rw [hl, hu, Set.pair_comm]

/-- The complete h-line between two distinct ideal endpoints is unique. -/
theorem existsUnique_halfPlaneLine_of_idealEndpoints (a b : OnePoint ℂ)
    (ha : a ∈ halfPlaneIdealBoundary) (hb : b ∈ halfPlaneIdealBoundary) (hab : a ≠ b) :
    ∃! L : HalfPlaneLine, L.idealEndpoints = {a, b} := by
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_idealEndpoints a b ha hb hab
  exact ⟨L, hL, fun M hM => HalfPlaneLine.idealEndpoints_injective (hM.trans hL.symm)⟩

/-- The segment whose two endpoints are ideal is the actual complete h-line trace. -/
def idealHSegment (a b : OnePoint ℂ) : Set ℍ :=
  {z | ∃ L : HalfPlaneLine, L.idealEndpoints = {a, b} ∧ z ∈ L.carrier}

theorem idealHSegment_eq_carrier (L : HalfPlaneLine) (a b : OnePoint ℂ)
    (hL : L.idealEndpoints = {a, b}) : idealHSegment a b = L.carrier := by
  ext z
  constructor
  · rintro ⟨M, hM, hz⟩
    have he : M = L := HalfPlaneLine.idealEndpoints_injective (hM.trans hL.symm)
    exact he ▸ hz
  · intro hz
    exact ⟨L, hL, hz⟩

/-- Any interior point and any actual ideal endpoint lie on a genuine common h-line. -/
theorem exists_halfPlaneLine_through_point_and_idealEndpoint (z : ℍ) (a : OnePoint ℂ)
    (ha : a ∈ halfPlaneIdealBoundary) :
    ∃ L : HalfPlaneLine, z ∈ L.carrier ∧ a ∈ L.idealEndpoints := by
  rw [halfPlaneIdealBoundary_eq_real_infty] at ha
  rcases ha with rfl | ⟨a, rfl⟩
  · refine ⟨.vertical z.re, rfl, ?_⟩
    rw [vertical_idealEndpoints]
    exact mem_insert_of_mem _ (mem_singleton ∞)
  · by_cases hza : z.re = a
    · refine ⟨.vertical a, hza, ?_⟩
      rw [vertical_idealEndpoints]
      exact mem_insert _ _
    · let c := (z.re ^ 2 + z.im ^ 2 - a ^ 2) / (2 * (z.re - a))
      let r := ‖(z : ℂ) - (c : ℂ)‖
      have hr : 0 < r := norm_sub_real_pos c z
      have hden : 2 * (z.re - a) ≠ 0 := mul_ne_zero (by norm_num) (sub_ne_zero.mpr hza)
      have hc : 2 * c * (z.re - a) = z.re ^ 2 + z.im ^ 2 - a ^ 2 := by
        have he : c * (2 * (z.re - a)) = z.re ^ 2 + z.im ^ 2 - a ^ 2 := div_mul_cancel₀ _ hden
        nlinarith
      have hnorm := norm_sub_real_eq_radius_sq (show ‖(z : ℂ) - (c : ℂ)‖ = r from rfl)
      have haeq : (a - c) ^ 2 = r ^ 2 := by nlinarith
      refine ⟨.circle c r hr, rfl, ?_⟩
      rw [circle_idealEndpoints]
      have hfactor : (a - c - r) * (a - c + r) = 0 := by nlinarith
      rcases mul_eq_zero.mp hfactor with h | h
      · have he : a = c + r := by linarith
        rw [he]
        exact mem_insert_of_mem _ (mem_singleton _)
      · have he : a = c - r := by linarith
        rw [he]
        exact mem_insert _ _

/-- No arbitrary incidence hypothesis is added: this interior/ideal-end h-line is unique. -/
theorem existsUnique_halfPlaneLine_through_point_and_idealEndpoint (z : ℍ) (a : OnePoint ℂ)
    (ha : a ∈ halfPlaneIdealBoundary) :
    ∃! L : HalfPlaneLine, z ∈ L.carrier ∧ a ∈ L.idealEndpoints := by
  obtain ⟨L, hz, haL⟩ := exists_halfPlaneLine_through_point_and_idealEndpoint z a ha
  exact ⟨L, ⟨hz, haL⟩, fun M hM => M.eq_of_shared_ideal_and_interior L z hM.1 hz a hM.2 haL⟩

/-- A genuine isometric ray exists from every actual model point toward every actual ideal point. -/
theorem exists_hLineRay (z : ℍ) (a : OnePoint ℂ) (ha : a ∈ halfPlaneIdealBoundary) :
    ∃ R : Set ℍ, IsHLineRay z a R := by
  obtain ⟨L, hz, haL⟩ := exists_halfPlaneLine_through_point_and_idealEndpoint z a ha
  obtain ⟨R, hR, _⟩ := L.exists_ray_to_idealEndpoint z hz a haL
  exact ⟨R, hR⟩

end

end LowDimensionalTopology.Geometry.Hyperbolic
