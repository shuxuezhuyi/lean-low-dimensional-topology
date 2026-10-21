/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisSeparation
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine real-SL conjugation preserves the entire actual half-plane Fuchsian data. -/
theorem HalfPlaneFuchsianGroup.realSLConjugateData
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (q : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H) := by
  let E := P.asFuchsianDisc.nielsenConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  have hE : E.carrier = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := realSLMobius_image_openHalfPlane q
  refine ⟨?_, E.discrete⟩
  intro g
  have hg := E.image_eq g
  rwa [hE] at hg

/-- The actual one-half collar estimate for an arbitrary original simple hyperbolic
axis and every distinct translate in a genuine half-plane Fuchsian group. -/
theorem HalfPlaneFuchsianGroup.simple_hyperbolic_axis_collar
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠
      1)
    (htA : 4 < (Matrix.trace A.val)^2) (hs : IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A))
    (F : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F ∈
      H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA ≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
        htA).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)) :
    (1 : ℝ) / 2 ≤ Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2) * Real.sinh
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)) / 2) := by
  have hAH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨q, t, ht, he⟩ := realSLMobius_hyperbolic_positive_log_normal_form A hAH
  let D := hLogDilationSL t
  let C := q * F * q⁻¹
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  have PK : HalfPlaneFuchsianGroup K := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.realSLConjugateData P q
  have hQH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q * A * q⁻¹)) := by
    simpa only [map_mul, map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hAH
  have hDH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D) := he ▸ hQH
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D ≠ 1 := hDH.1.1
  have htD : 4 < (Matrix.trace
    D.val)^2 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff D hD).mp hDH
  have hA' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q * A *
    q⁻¹) ≠ 1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A q hA
  have htA' : 4 < (Matrix.trace (q * A * q⁻¹).val)^2 := by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hAD := hHyperbolicAxis_eq_of_realSLMobius_eq (q * A * q⁻¹) D hA' hD htA' htD he
  have hDaxis := hLogDilationSL_hyperbolic_axis t ht hD htD
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M := L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F)
  have hImageA : (q • · : ℍ → ℍ) '' L.carrier = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [← hDaxis, ← hAD, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA htA,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hImageM : (q • · : ℍ → ℍ) '' M.carrier = (logDilationAxisImage t hD htD C).carrier := by
    have hCI : (logDilationAxisImage t hD htD C).carrier =
        (C • · : ℍ → ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
      dsimp only [logDilationAxisImage]
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation D C hD htD,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier, hDaxis]
      rfl
    rw [hCI, ← hImageA]
    dsimp only [M]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier, image_image, image_image]
    congr 1
    funext z
    change q • (F • z) = (q * F * q⁻¹) • (q • z)
    rw [mul_smul, mul_smul, inv_smul_smul]
  have hneC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ logDilationAxisImage t hD htD C := by
    intro heC
    apply hne
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    apply (Set.image_injective.mpr (MulAction.injective q))
    rw [hImageA, hImageM, heC]
  have hsQ : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q * A * q⁻¹)) := by
    simpa only [map_mul, map_inv] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hs
  have hsD : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D) := he ▸ hsQ
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ K := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q * F * q⁻¹) ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
    rw [map_mul, map_mul, map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F, hF, rfl⟩
  have hTDA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry D) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) := by
    rw [← hSLIsometry_eq_of_realSLMobius_eq _ _ he,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation]
  have hSinhA : Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2) = Real.sinh t := by
    rw [← hTDA]
    exact hLogDilationSL_sinh_half_translation t ht hD htD
  have hdist := L.lineDist_isometry_image M (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
    (logDilationAxisImage t hD htD C) (q • ·) (isometry_smul ℍ q) hImageA hImageM
  have hc := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_logDilation_axis_collar PK t ht hD htD hsD C hCm hneC
  change (1 : ℝ) / 2 ≤ Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2) * Real.sinh (L.lineDist M / 2)
  rw [hSinhA]
  simpa only [hdist] using hc

end LowDimensionalTopology.Geometry.Fuchsian
