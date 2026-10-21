module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ModularTriangleExample
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleCongruence
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TwoIdealTriangles
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.FullDisplacementDetermination
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertExistence
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Native conjugacy takes the genuine reflection to the reflection in the image geodesic. -/
theorem native_reflection_realGL_conjugate
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (g : GL (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g)⁻¹ =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (L.realGLMap g) := by
  apply IsometryEquiv.ext
  intro z
  exact L.reflection_realGL_conjugation g z

theorem native_subgroupConjugate_closure (e : ℍ ≃ᵢ ℍ) (S : Set (ℍ ≃ᵢ ℍ)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (Subgroup.closure S) =
      Subgroup.closure ((fun f => e*f*e⁻¹) '' S) := by
  unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [MonoidHom.map_closure]
  rfl

theorem triangle_reflectionGroup_conjugate_of_side_images
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (g : GL (Fin 2) ℝ) (A B C : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (hA : T.sideLineA.realGLMap g = A) (hB : T.sideLineB.realGLMap g = B)
    (hC : T.sideLineC.realGLMap g = C) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g) (triangleReflectionGroup T) =
      Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry B,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry C} := by
  unfold triangleReflectionGroup triangleReflectionSides
  rw [native_subgroupConjugate_closure]
  simp only [image_insert_eq, image_singleton, native_reflection_realGL_conjugate, hA, hB, hC]

/-- The original three-reflection subgroup in a unit-semicircle normalization. -/
def normalizedIdealTriangleGroup (x y : ℝ) : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical x),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical y),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 (by norm_num))}

theorem normalizedIdealTriangleGroup_swap (x y : ℝ) :
    normalizedIdealTriangleGroup x y = normalizedIdealTriangleGroup y x := by
  unfold normalizedIdealTriangleGroup
  congr 1
  ext f
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

theorem native_subgroupConjugate_compose (e f : ℍ ≃ᵢ ℍ) (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate f H) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (e*f) H := by
  unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
  rw [Subgroup.map_map]
  congr 1

theorem native_axis_conjugate_vertical (x : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0) * _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical x) *
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹ =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical (-x)) := by
  rw [halfPlaneLineReflectionIsometry_inv]
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection x (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z)) : ℂ) =
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (-x) z : ℂ)
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe, map_sub, Complex.conj_ofReal,
    Complex.conj_conj]
  push_cast
  ring

theorem native_axis_conjugate_unitCircle :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0) *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 (by norm_num)) *
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹ =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 (by norm_num)) := by
  rw [halfPlaneLineReflectionIsometry_inv]
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 (by norm_num) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 z)) : ℂ) =
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 (by norm_num) z : ℂ)
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]

theorem normalizedIdealTriangleGroup_axis_conjugate (x y : ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0))
      (normalizedIdealTriangleGroup x y) = normalizedIdealTriangleGroup (-x) (-y) := by
  unfold normalizedIdealTriangleGroup
  rw [native_subgroupConjugate_closure]
  simp only [image_insert_eq, image_singleton, native_axis_conjugate_vertical,
    native_axis_conjugate_unitCircle]

/-- An actual ideal triangle has a genuine normalization, including both other vertices
and the actual measured-angle equations. -/
theorem ideal_triangle_group_normalization (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hc : T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) :
    ∃ (g : GL (Fin 2) ℝ) (a b : ℂ),
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ 0 ≤ a.im ∧ 0 ≤ b.im ∧ a.re ≠ b.re ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g) (triangleReflectionGroup T) =
        normalizedIdealTriangleGroup a.re b.re ∧
      Real.cos T.alpha = (if a.re < b.re then -a.re else a.re) ∧
      Real.cos T.beta = (if b.re < a.re then -b.re else b.re) := by
  have hci : ‖(T.toDiscTriangle.c : ℂ)‖ = 1 :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr hc
  obtain ⟨g, hg, hpEnd, hline⟩ := T.toDiscTriangle.exists_ideal_vertex_area_normalizer hci
  obtain ⟨a, b, hna, hnb, hia, hib, hne, ha, hb, hA, hB⟩ :=
    T.toDiscTriangle.normalized_sides_and_vertices hci g hg hpEnd hline
  have heA : T.sideLineA.realGLMap g = .vertical b.re := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hA
  have heB : T.sideLineB.realGLMap g = .vertical a.re := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hB
  have heC : T.sideLineC.realGLMap g = .circle 0 1 (by norm_num) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact hline
  refine ⟨g, a, b, hna, hnb, hia, hib, hne, ?_, ?_, ?_⟩
  · exact (triangle_reflectionGroup_conjugate_of_side_images T g _ _ _ heA heB heC).trans
      (normalizedIdealTriangleGroup_swap b.re a.re)
  · exact T.toDiscTriangle.alpha_cos_normalized hci g hg hline hpEnd a b hna hnb hne ha hb
  · exact T.toDiscTriangle.beta_cos_normalized hci g hg hline hpEnd a b hna hnb hne ha hb

/-- All actual ideal triangles with specified first two angles have the same actual
normalized side-reflection subgroup, with either global orientation allowed. -/
theorem ideal_triangle_group_canonical (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hc : T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) :
    ∃ e : ℍ ≃ᵢ ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T) =
      normalizedIdealTriangleGroup (-Real.cos T.alpha) (Real.cos T.beta) := by
  obtain ⟨g, a, b, _, _, _, _, hne, hG, hα, hβ⟩ := ideal_triangle_group_normalization T hc
  by_cases hab : a.re < b.re
  · rw [ite_eq_left hab] at hα
    rw [ite_eq_right (not_lt.mpr hab.le)] at hβ
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g, ?_⟩
    simpa only [hα, hβ, neg_neg] using hG
  · have hba : b.re < a.re := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hne)
    rw [ite_eq_right hab] at hα
    rw [ite_eq_left hba] at hβ
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0) * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g, ?_⟩
    rw [← native_subgroupConjugate_compose, hG, normalizedIdealTriangleGroup_axis_conjugate]
    rw [hα, hβ]

theorem native_subgroupConjugate_one (H : Subgroup (ℍ ≃ᵢ ℍ)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate 1 H = H := by
  ext f
  simp [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff]

theorem native_subgroup_conjugacy_of_common_normalization (H K J : Subgroup (ℍ ≃ᵢ ℍ))
    (e f : ℍ ≃ᵢ ℍ) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e H = J)
    (hf : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate f K = J) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (f⁻¹*e) H = K := by
  rw [← native_subgroupConjugate_compose, he, ← hf, native_subgroupConjugate_compose,
    inv_mul_cancel, native_subgroupConjugate_one]

/-- The full equal-angle conjugacy result for all triangles with a corresponding ideal vertex. -/
theorem ideal_equal_angle_reflectionGroups_conjugate
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hcT : T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hcS : S.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) :
    ∃ e : ℍ ≃ᵢ ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T) =
      triangleReflectionGroup S := by
  obtain ⟨e, he⟩ := ideal_triangle_group_canonical T hcT
  obtain ⟨f, hf⟩ := ideal_triangle_group_canonical S hcS
  rw [hα, hβ] at he
  exact ⟨f⁻¹*e, native_subgroup_conjugacy_of_common_normalization _ _ _ e f he hf⟩

theorem finite_closedTriangle_sideA (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    T.toClosedHTriangle.sideLineA = T.sideLineA := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ T.b_ne_c
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineA.toHalfPlane.closedCarrier_mem_interior_iff T.b).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineA.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.b_mem_sideLineA)
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineA.toHalfPlane.closedCarrier_mem_interior_iff T.c).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineA.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.c_mem_sideLineA)
  · exact T.rayBC.start_mem_support
  · exact T.rayBC.subset_support T.c_mem_rayBC

theorem finite_closedTriangle_sideB (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    T.toClosedHTriangle.sideLineB = T.sideLineB := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ T.c_ne_a
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineB.toHalfPlane.closedCarrier_mem_interior_iff T.c).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineB.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.c_mem_sideLineB)
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineB.toHalfPlane.closedCarrier_mem_interior_iff T.a).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineB.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.a_mem_sideLineB)
  · exact T.rayCA.start_mem_support
  · exact T.rayCA.subset_support T.a_mem_rayCA

theorem finite_closedTriangle_sideC (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) :
    T.toClosedHTriangle.sideLineC = T.sideLineC := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ T.a_ne_b
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff T.a).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineC.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.a_mem_sideLineC)
  · exact (T.toClosedHTriangle.toDiscTriangle.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff T.b).mp
      ((T.toClosedHTriangle.toDiscTriangle.sideLineC.closedCarrier_cayley_mem _).mp
        T.toClosedHTriangle.toDiscTriangle.b_mem_sideLineC)
  · exact T.rayAB.start_mem_support
  · exact T.rayAB.subset_support T.b_mem_rayAB

theorem finite_triangle_image_sideA
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (g : GL (Fin 2) ℝ)
    (hb : g • T.b = S.b) (hc : g • T.c = S.c) :
    T.sideLineA.realGLMap g = S.sideLineA := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_image_line_of_corresponding_points g T.sideLineA S.sideLineA T.b_ne_c
    T.rayBC.start_mem_support (T.rayBC.subset_support T.c_mem_rayBC)
    (hb ▸ S.rayBC.start_mem_support) (hc ▸ S.rayBC.subset_support S.c_mem_rayBC)

theorem finite_triangle_image_sideB
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (g : GL (Fin 2) ℝ)
    (hc : g • T.c = S.c) (ha : g • T.a = S.a) :
    T.sideLineB.realGLMap g = S.sideLineB := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_image_line_of_corresponding_points g T.sideLineB S.sideLineB T.c_ne_a
    T.rayCA.start_mem_support (T.rayCA.subset_support T.a_mem_rayCA)
    (hc ▸ S.rayCA.start_mem_support) (ha ▸ S.rayCA.subset_support S.a_mem_rayCA)

theorem finite_triangle_image_sideC
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (g : GL (Fin 2) ℝ)
    (ha : g • T.a = S.a) (hb : g • T.b = S.b) :
    T.sideLineC.realGLMap g = S.sideLineC := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_image_line_of_corresponding_points g T.sideLineC S.sideLineC T.a_ne_b
    T.rayAB.start_mem_support (T.rayAB.subset_support T.b_mem_rayAB)
    (ha ▸ S.rayAB.start_mem_support) (hb ▸ S.rayAB.subset_support S.b_mem_rayAB)

/-- A vertex-carrying real isometry conjugates the actual full reflection subgroups. -/
theorem finite_triangle_reflectionGroup_conjugate
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (g : GL (Fin 2) ℝ)
    (ha : g • T.a = S.a) (hb : g • T.b = S.b) (hc : g • T.c = S.c) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g) (triangleReflectionGroup T.toClosedHTriangle) =
      triangleReflectionGroup S.toClosedHTriangle := by
  unfold triangleReflectionGroup triangleReflectionSides
  simp only [finite_closedTriangle_sideA, finite_closedTriangle_sideB, finite_closedTriangle_sideC]
  rw [native_subgroupConjugate_closure]
  simp only [image_insert_eq, image_singleton, native_reflection_realGL_conjugate,
    finite_triangle_image_sideA T S g hb hc, finite_triangle_image_sideB T S g hc ha,
    finite_triangle_image_sideC T S g ha hb]

/-- Equal actual angles suffice for actual subgroup conjugacy, with no discreteness hypothesis. -/
theorem finite_equal_angle_reflectionGroups_conjugate
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    ∃ e : ℍ ≃ᵢ ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T.toClosedHTriangle) =
      triangleReflectionGroup S.toClosedHTriangle := by
  obtain ⟨g, ha, hb, hc⟩ := T.exists_isometry_of_angles_eq S hα hβ hγ
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g, finite_triangle_reflectionGroup_conjugate T S g ha hb hc⟩

theorem closedHTriangle_toDiscTriangle_injective :
    Function.Injective _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.toDiscTriangle := by
  intro T S h
  have ha : T.a = S.a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.a h)
  have hb : T.b = S.b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.b h)
  have hc : T.c = S.c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.injective (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.c h)
  cases T
  cases S
  cases ha
  cases hb
  cases hc
  rfl

theorem finite_discTriangle_toHalfPlane_toDiscTriangle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle) :
    T.toHalfPlane.toDiscTriangle = T := by
  cases T with
  | mk a b c hn =>
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscTriangle.mk (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane c)) _ = _
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]

theorem positive_angle_closedTriangle_has_finite_model
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα : 0 < T.alpha) (hβ : 0 < T.beta) (hγ : 0 < T.gamma) :
    ∃ U : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle, U.toClosedHTriangle = T := by
  let V := T.toDiscTriangle.finiteTriangle
    (T.toDiscTriangle.alpha_pos_iff_finite.mp hα)
    (T.toDiscTriangle.cycle.alpha_pos_iff_finite.mp hβ)
    (T.toDiscTriangle.cycle.cycle.alpha_pos_iff_finite.mp hγ)
  refine ⟨V.toHalfPlane, closedHTriangle_toDiscTriangle_injective ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle.toClosedHTriangle_toDiscTriangle,
    finite_discTriangle_toHalfPlane_toDiscTriangle]
  exact T.toDiscTriangle.finiteTriangle_toClosedDiscTriangle _ _ _

theorem closed_triangle_gamma_zero_ideal
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hγ : T.gamma = 0) :
    T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mp
  exact T.toDiscTriangle.cycle.cycle.alpha_eq_zero_iff_ideal.mp hγ

theorem closedHTriangle_cycle_angles (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    T.cycle.alpha = T.beta ∧ T.cycle.beta = T.gamma ∧ T.cycle.gamma = T.alpha := by
  refine ⟨rfl, rfl, ?_⟩
  change T.toDiscTriangle.cycle.cycle.cycle.alpha = T.toDiscTriangle.alpha
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.cycle_three]

/-- The full actual equal-angle conjugacy theorem includes all finite and ideal vertices. -/
theorem equal_angle_triangle_reflectionGroups_conjugate
    (T S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hα : T.alpha = S.alpha) (hβ : T.beta = S.beta) (hγ : T.gamma = S.gamma) :
    ∃ e : ℍ ≃ᵢ ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T) =
      triangleReflectionGroup S := by
  by_cases hc : T.gamma = 0
  · exact ideal_equal_angle_reflectionGroups_conjugate T S
      (closed_triangle_gamma_zero_ideal T hc)
      (closed_triangle_gamma_zero_ideal S (hγ.symm.trans hc)) hα hβ
  by_cases ha : T.alpha = 0
  · obtain ⟨e, he⟩ := ideal_equal_angle_reflectionGroups_conjugate T.cycle S.cycle
      (closed_triangle_gamma_zero_ideal T.cycle ((closedHTriangle_cycle_angles T).2.2.trans ha))
      (closed_triangle_gamma_zero_ideal S.cycle
        ((closedHTriangle_cycle_angles S).2.2.trans (hα.symm.trans ha))) hβ hγ
    exact ⟨e, by simpa only [triangleReflectionGroup_cycle] using he⟩
  by_cases hb : T.beta = 0
  · have hT := closedHTriangle_cycle_angles T
    have hS := closedHTriangle_cycle_angles S
    have hT' := closedHTriangle_cycle_angles T.cycle
    have hS' := closedHTriangle_cycle_angles S.cycle
    obtain ⟨e, he⟩ := ideal_equal_angle_reflectionGroups_conjugate T.cycle.cycle S.cycle.cycle
      (closed_triangle_gamma_zero_ideal T.cycle.cycle (hT'.2.2.trans (hT.1.trans hb)))
      (closed_triangle_gamma_zero_ideal S.cycle.cycle
        (hS'.2.2.trans (hS.1.trans (hβ.symm.trans hb)))) hγ
      (hT'.2.1.trans (hT.2.2.trans (hα.trans (hS.2.2.symm.trans hS'.2.1.symm))))
    exact ⟨e, by simpa only [triangleReflectionGroup_cycle] using he⟩
  have hpα : 0 < T.alpha := lt_of_le_of_ne T.toDiscTriangle.alpha_mem_Ico.1 (Ne.symm ha)
  have hpβ : 0 < T.beta := lt_of_le_of_ne T.toDiscTriangle.cycle.alpha_mem_Ico.1 (Ne.symm hb)
  have hpγ : 0 < T.gamma := lt_of_le_of_ne T.toDiscTriangle.cycle.cycle.alpha_mem_Ico.1 (Ne.symm hc)
  obtain ⟨U, hU⟩ := positive_angle_closedTriangle_has_finite_model T hpα hpβ hpγ
  obtain ⟨V, hV⟩ := positive_angle_closedTriangle_has_finite_model S
    (hα ▸ hpα) (hβ ▸ hpβ) (hγ ▸ hpγ)
  have hUVα : U.alpha = V.alpha := U.closed_angles.1.symm.trans
    (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.alpha hU |>.trans (hα.trans
      ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.alpha hV).symm.trans V.closed_angles.1)))
  have hUVβ : U.beta = V.beta := U.closed_angles.2.1.symm.trans
    (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.beta hU |>.trans (hβ.trans
      ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.beta hV).symm.trans V.closed_angles.2.1)))
  have hUVγ : U.gamma = V.gamma := U.closed_angles.2.2.symm.trans
    (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.gamma hU |>.trans (hγ.trans
      ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.gamma hV).symm.trans V.closed_angles.2.2)))
  obtain ⟨e, he⟩ := finite_equal_angle_reflectionGroups_conjugate U V hUVα hUVβ hUVγ
  exact ⟨e, by simpa only [hU, hV] using he⟩

theorem triangle_reflection_type_angles_admissible (G : Subgroup (ℍ ≃ᵢ ℍ)) (α β γ : ℝ)
    (h : IsTriangleReflectionType G α β γ) :
    0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α+β+γ < Real.pi := by
  obtain ⟨T, rfl, rfl, rfl, _⟩ := h
  exact ⟨T.toDiscTriangle.alpha_mem_Ico.1, T.toDiscTriangle.cycle.alpha_mem_Ico.1,
    T.toDiscTriangle.cycle.cycle.alpha_mem_Ico.1, T.angle_sum_lt_pi⟩

theorem closed_vertical_point_re
    (x : ℝ)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (z : ℂ)
    (hp : p.val = (z : Mobius.ExtendedComplex))
    (hL : p ∈ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier) :
    z.re = x := by
  let L := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).toDiscLine
  have heL : L.toHalfPlane = .vertical x := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).toDiscLine_toHalfPlane
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_closedLine_point_vertical_re L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph p)
    ((L.closedCarrier_cayley_mem p).mpr (heL.symm ▸ hL)) 1 (by norm_num) x
  · rw [heL]
    simp
  · exact (closed_vertex_normalized_identity p).trans hp

theorem angle_pair_cosine_sum_pos (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α+β < Real.pi) : 0 < Real.cos α + Real.cos β := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi hα
    (show Real.pi-β ≤ Real.pi by linarith) (show α < Real.pi-β by linarith)
  rw [Real.cos_pi_sub] at h
  linarith only [h]

def prescribedIdealTriangleLeft (α : ℝ) (hα : α ∈ Icc (0 : ℝ) Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  ⟨((⟨-Real.cos α, Real.sin α⟩ : ℂ) : Mobius.ExtendedComplex),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_closedHalfPlaneSet _).mpr (Real.sin_nonneg_of_mem_Icc hα)⟩

def prescribedIdealTriangleRight (β : ℝ) (hβ : β ∈ Icc (0 : ℝ) Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  ⟨((⟨Real.cos β, Real.sin β⟩ : ℂ) : Mobius.ExtendedComplex),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_closedHalfPlaneSet _).mpr (Real.sin_nonneg_of_mem_Icc hβ)⟩

theorem angle_unit_complex_norm (α : ℝ) :
    ‖(⟨-Real.cos α, Real.sin α⟩ : ℂ)‖ = 1 ∧
      ‖(⟨Real.cos α, Real.sin α⟩ : ℂ)‖ = 1 := by
  constructor
  all_goals
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, one_pow]
    nlinarith only [Real.sin_sq_add_cos_sq α]

/-- Actual noncollinear triangle with an ideal vertex and both other angles prescribed. -/
def prescribedIdealHTriangle (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α+β < Real.pi) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := prescribedIdealTriangleLeft α ⟨hα, by linarith⟩
  b := prescribedIdealTriangleRight β ⟨hβ, by linarith⟩
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint
  noncollinear := by
    rintro ⟨L, ha, hb, hc⟩
    obtain ⟨x, rfl⟩ := L.eq_vertical_of_infty_ideal
      ((L.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
    have heA := closed_vertical_point_re x _ (⟨-Real.cos α, Real.sin α⟩ : ℂ) rfl ha
    have heB := closed_vertical_point_re x _ (⟨Real.cos β, Real.sin β⟩ : ℂ) rfl hb
    have hpos := angle_pair_cosine_sum_pos α β hα hβ hsum
    change -Real.cos α = x at heA
    change Real.cos β = x at heB
    linarith only [heA, heB, hpos]

theorem prescribedIdealHTriangle_circle (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α+β < Real.pi) :
    (prescribedIdealHTriangle α β hα hβ hsum).sideLineC = .circle 0 1 (by norm_num) := by
  let T := prescribedIdealHTriangle α β hα hβ hsum
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_closed_points _ _
    (show T.a ≠ T.b from fun h => T.toDiscTriangle.a_ne_b (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph h))
  · exact (T.toDiscTriangle.sideLineC.closedCarrier_cayley_mem _).mp T.toDiscTriangle.a_mem_sideLineC
  · exact (T.toDiscTriangle.sideLineC.closedCarrier_cayley_mem _).mp T.toDiscTriangle.b_mem_sideLineC
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle_closedCarrier_of_coe 0 1 (by norm_num) _
      (Real.sin_nonneg_of_mem_Icc ⟨hα, by linarith⟩)
      (by simpa only [Complex.ofReal_zero, sub_zero] using (angle_unit_complex_norm α).1)
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle_closedCarrier_of_coe 0 1 (by norm_num) _
      (Real.sin_nonneg_of_mem_Icc ⟨hβ, by linarith⟩)
      (by simpa only [Complex.ofReal_zero, sub_zero] using (angle_unit_complex_norm β).2)

theorem prescribedIdealHTriangle_angles (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α+β < Real.pi) :
    (prescribedIdealHTriangle α β hα hβ hsum).alpha = α ∧
      (prescribedIdealHTriangle α β hα hβ hsum).beta = β ∧
      (prescribedIdealHTriangle α β hα hβ hsum).gamma = 0 := by
  let T := prescribedIdealHTriangle α β hα hβ hsum
  let a : ℂ := ⟨-Real.cos α, Real.sin α⟩
  let b : ℂ := ⟨Real.cos β, Real.sin β⟩
  have hab : a.re < b.re := by
    have h := angle_pair_cosine_sum_pos α β hα hβ hsum
    change -Real.cos α < Real.cos β
    linarith only [h]
  have hci : ‖(T.toDiscTriangle.c : ℂ)‖ = 1 :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal
  have hline : ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' T.sideLineC.carrier =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num)).carrier := by
    rw [prescribedIdealHTriangle_circle]
    simp
  have hca := closedTriangle_unitCircle_corner_cosine T a b
    (angle_unit_complex_norm α).1 (angle_unit_complex_norm β).2 (ne_of_lt hab) rfl rfl rfl
    (prescribedIdealHTriangle_circle α β hα hβ hsum)
  have hcb := T.toDiscTriangle.beta_cos_normalized hci 1 (by norm_num) hline
    (closed_vertex_normalized_identity T.c)
    a b (angle_unit_complex_norm α).1 (angle_unit_complex_norm β).2 (ne_of_lt hab)
    (closed_vertex_normalized_identity T.a) (closed_vertex_normalized_identity T.b)
  rw [ite_eq_left hab] at hca
  rw [ite_eq_right (not_lt.mpr hab.le)] at hcb
  refine ⟨?_, ?_, T.toDiscTriangle.gamma_of_ideal hci⟩
  · apply Real.injOn_cos ⟨T.toDiscTriangle.alpha_mem_Ico.1, T.toDiscTriangle.alpha_mem_Ico.2.le⟩
      ⟨hα, by linarith⟩
    dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.alpha] at hca
    simpa only [a, Complex.re, neg_neg] using hca
  · apply Real.injOn_cos ⟨T.toDiscTriangle.cycle.alpha_mem_Ico.1,
      T.toDiscTriangle.cycle.alpha_mem_Ico.2.le⟩ ⟨hβ, by linarith⟩
    exact hcb

theorem exists_triangle_reflection_type_with_zero (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hsum : α+β < Real.pi) :
    ∃ G : Subgroup (ℍ ≃ᵢ ℍ), IsTriangleReflectionType G α β 0 := by
  let T := prescribedIdealHTriangle α β hα hβ hsum
  have h := prescribedIdealHTriangle_angles α β hα hβ hsum
  exact ⟨triangleReflectionGroup T, T, h.1, h.2.1, h.2.2, rfl⟩


theorem circle_intersection_height_identity (a d b x : ℝ)
    (hx : 2*(a-d)*x = b^2-1) :
    (a-d)^2*(1+2*a*x-x^2) = (a^2+1)*(d^2+b^2)-
      ((a^2+1)+(d^2+b^2)-(a-d)^2)^2/4 := by
  linear_combination -(-4*a^2+4*a*d+2*a*x+b^2-2*d*x-1)/4 * hx

theorem angle_triple_construction_inequalities (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α+β+γ < Real.pi) :
    0 < Real.sin α ∧ 0 < Real.sin β ∧ 0 < Real.sin γ ∧
      Real.sin α * Real.sin β < Real.cos γ + Real.cos α * Real.cos β ∧
      0 < Real.cos α * Real.sin β + Real.cos β * Real.sin α := by
  have haπ : α < Real.pi := by linarith
  have hbπ : β < Real.pi := by linarith
  have hgπ : γ < Real.pi := by linarith
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi hγ.le
    (show Real.pi-(α+β) ≤ Real.pi by linarith)
    (show γ < Real.pi-(α+β) by linarith)
  rw [Real.cos_pi_sub, Real.cos_add] at hcos
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hα haπ,
    Real.sin_pos_of_pos_of_lt_pi hβ hbπ, Real.sin_pos_of_pos_of_lt_pi hγ hgπ,
    by linarith only [hcos], ?_⟩
  have h := Real.sin_pos_of_pos_of_lt_pi (add_pos hα hβ)
    (show α+β < Real.pi by linarith)
  rw [Real.sin_add] at h
  linarith only [h]

/-- Positive real coordinates for the genuine two-circle intersection construction. -/
theorem angle_construction_circle_coordinates (A B C p q r : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hA : A^2+p^2 = 1) (hB : B^2+q^2 = 1) (hC : C^2+r^2 = 1)
    (hcos : p*q < C+A*B) (hsum : 0 < A*q+B*p) :
    ∃ b x y : ℝ, 1 < b ∧ 0 < x ∧ 0 < y ∧
      x^2+y^2-1 = 2*(A/p)*x ∧
      x^2+y^2-b^2 = -2*b*(B/q)*x ∧
      (b^2+1)/(2*b) = (C+A*B)/(p*q) := by
  let k := (C+A*B)/(p*q)
  have hpq : 0 < p*q := mul_pos hp hq
  have hk : 1 < k := (one_lt_div hpq).mpr hcos
  obtain ⟨b, hb, hbrel⟩ : ∃ b : ℝ, 1 < b ∧ b^2+1 = 2*b*k := by
    have hsqrt : (Real.sqrt (k^2-1))^2 = k^2-1 := Real.sq_sqrt (by nlinarith only [hk])
    refine ⟨k+Real.sqrt (k^2-1),
      lt_of_lt_of_le hk (le_add_of_nonneg_right (Real.sqrt_nonneg _)), ?_⟩
    nlinarith only [hsqrt]
  have hbpos : 0 < b := lt_trans zero_lt_one hb
  have hheight : (b^2+1)/(2*b) = k := by
    apply (div_eq_iff (by positivity)).mpr
    nlinarith only [hbrel]
  have hbk : (b^2+1)*(p*q) = 2*b*(C+A*B) := by
    rw [hbrel]
    dsimp only [k]
    field_simp
  have hcot : 0 < A/p+B/q := by
    have he : A/p+B/q = (A*q+B*p)/(p*q) := by field_simp
    rw [he]
    exact div_pos hsum hpq
  have hgram : 0 < A^2+B^2+2*A*B*C := by
    have he : (C+A*B)^2-(p*q)^2 = A^2+B^2+C^2+2*A*B*C-1 := by
      rw [mul_pow, show p^2 = 1-A^2 by linarith only [hA],
        show q^2 = 1-B^2 by linarith only [hB]]
      ring
    have hsq : 0 < (C+A*B)^2-(p*q)^2 := by nlinarith only [hcos, hpq]
    nlinarith only [he, hsq, hC, sq_pos_of_pos hr]
  let D := A/p+b*B/q
  let E := b*A/p+B/q
  have hDE : D*E = b*(A^2+B^2+2*A*B*C)/(p^2*q^2) := by
    dsimp only [D, E]
    field_simp [ne_of_gt hp, ne_of_gt hq]
    linear_combination A*B*hbk + b*A^2*hB + b*B^2*hA
  have hD : 0 < D := by
    by_cases hBpos : 0 ≤ B
    · have hpos : 0 ≤ (b-1)*B/q := div_nonneg (mul_nonneg (by linarith only [hb]) hBpos) hq.le
      have he : D = (A/p+B/q)+(b-1)*B/q := by dsimp only [D]; ring
      rw [he]
      exact add_pos_of_pos_of_nonneg hcot hpos
    · have hBneg : B < 0 := lt_of_not_ge hBpos
      have hApos : 0 < A := by nlinarith only [hsum, hp, hq, hBneg]
      have hE : 0 < E := by
        have hpos : 0 < (b-1)*A/p := div_pos (mul_pos (by linarith only [hb]) hApos) hp
        have he : E = (A/p+B/q)+(b-1)*A/p := by dsimp only [E]; ring
        rw [he]
        exact add_pos hcot hpos
      have hprod : 0 < D*E := by rw [hDE]; positivity
      nlinarith only [hE, hprod]
  let x := (b^2-1)/(2*D)
  have hx : 0 < x := div_pos (by nlinarith only [hb]) (by positivity)
  have hDx : 2*D*x = b^2-1 := by
    dsimp only [x]
    exact mul_div_cancel₀ _ (by positivity)
  let R := 1+2*(A/p)*x-x^2
  have hR : 0 < R := by
    have hdet : D^2*R = b^2*r^2/(p^2*q^2) := by
      let a := A/p
      let d := -b*B/q
      have heD : D = a-d := by dsimp only [D, a, d]; ring
      have hu : a^2+1 = 1/p^2 := by
        dsimp only [a]
        field_simp [ne_of_gt hp]
        nlinarith only [hA]
      have hv : d^2+b^2 = b^2/q^2 := by
        dsimp only [d]
        field_simp [ne_of_gt hq]
        nlinarith only [hB]
      have hn : (a^2+1)+(d^2+b^2)-(a-d)^2 = 2*b*C/(p*q) := by
        calc
          _ = 1+b^2-2*b*A*B/(p*q) := by dsimp only [a, d]; ring
          _ = _ := by
            field_simp [ne_of_gt hp, ne_of_gt hq]
            linear_combination hbk
      have hg := circle_intersection_height_identity a d b x (heD ▸ hDx)
      rw [hn, hu, hv] at hg
      calc
        D^2*R = (1/p^2)*(b^2/q^2)-(2*b*C/(p*q))^2/4 := by
          simpa only [heD, R, a] using hg
        _ = _ := by
          field_simp [ne_of_gt hp, ne_of_gt hq]
          nlinarith only [hC]
    have hprod : 0 < D^2*R := by rw [hdet]; positivity
    exact pos_of_mul_pos_right hprod (sq_nonneg D)
  let y := Real.sqrt R
  have hy : 0 < y := Real.sqrt_pos.mpr hR
  have hy2 : y^2 = R := Real.sq_sqrt hR.le
  refine ⟨b, x, y, hb, hx, hy, ?_, ?_, hheight⟩
  · dsimp only [R] at hy2
    linarith only [hy2]
  · dsimp only [R, D] at hy2 hDx
    linear_combination hy2+hDx

/-- Actual finite triangle used by the prescribed-angle construction. -/
def angleConstructedTriangle
    (b x y : ℝ)
    (hb : 1 < b)
    (hx : 0 < x)
    (hy : 0 < y) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle where
  a := UpperHalfPlane.I
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 b (lt_trans zero_lt_one hb)
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe x y hy
  noncollinear := by
    rintro ⟨L, hA, hB, hC⟩
    have hne : UpperHalfPlane.I ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 b (lt_trans zero_lt_one hb) := by
      intro he
      have hi := congrArg UpperHalfPlane.im he
      change 1 = b at hi
      linarith only [hb, hi]
    have hL : L = .vertical 0 := L.eq_of_two_points (.vertical 0) hne hA hB rfl rfl
    rw [hL] at hC
    change x = 0 at hC
    linarith only [hx, hC]

theorem complex_unit_vector_angle_cos (A p : ℝ) (hA : A^2+p^2 = 1) :
    Real.cos (InnerProductGeometry.angle Complex.I (⟨p,A⟩ : ℂ)) = A ∧
      Real.cos (InnerProductGeometry.angle (-Complex.I) (⟨p,-A⟩ : ℂ)) = A := by
  have hn₁ : ‖(⟨p,A⟩ : ℂ)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, one_pow]
    linarith only [hA]
  have hn₂ : ‖(⟨p,-A⟩ : ℂ)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, one_pow]
    linarith only [hA]
  constructor
  · rw [InnerProductGeometry.cos_angle, hn₁, Complex.norm_I, one_mul, div_one, Complex.inner]
    simp
  · rw [InnerProductGeometry.cos_angle, hn₂, norm_neg, Complex.norm_I, one_mul, div_one, Complex.inner]
    simp

theorem angleConstructedTriangle_cos_alpha (A p b x y : ℝ)
    (hp : 0 < p) (hA : A^2+p^2 = 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (hcircle : x^2+y^2-1 = 2*(A/p)*x) :
    Real.cos (angleConstructedTriangle b x y hb hx hy).alpha = A := by
  let T := angleConstructedTriangle b x y hb hx hy
  have hD₁ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.a T.b = (b^2-1) • Complex.I := by
    apply Complex.ext <;>
      simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection, T, angleConstructedTriangle,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe, -Complex.ofReal_pow]
  have hD₂ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.a T.c = (2*x/p) • (⟨p,A⟩ : ℂ) := by
    have hform : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.a T.c = (⟨2*x, x^2+y^2-1⟩ : ℂ) := by
      apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection, T, angleConstructedTriangle, _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    rw [hform]
    apply Complex.ext
    · simp only [Complex.smul_re, smul_eq_mul]
      field_simp
    · simp only [Complex.smul_im, smul_eq_mul]
      rw [hcircle]
      ring
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_eq_direction T.rayAB T.rayAC
    T.b_mem_rayAB T.a_ne_b.symm T.c_mem_rayAC T.c_ne_a
  change T.alpha = _ at he
  rw [he, hD₁, hD₂,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (show 0 < b^2-1 by nlinarith only [hb]),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (show 0 < 2*x/p by positivity)]
  exact (complex_unit_vector_angle_cos A p hA).1

theorem angleConstructedTriangle_cos_beta (B q b x y : ℝ)
    (hq : 0 < q) (hB : B^2+q^2 = 1) (hb : 1 < b) (hx : 0 < x) (hy : 0 < y)
    (hcircle : x^2+y^2-b^2 = -2*b*(B/q)*x) :
    Real.cos (angleConstructedTriangle b x y hb hx hy).beta = B := by
  let T := angleConstructedTriangle b x y hb hx hy
  have hD₁ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.b T.a = (b^2-1) • (-Complex.I) := by
    apply Complex.ext <;>
      simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection, T, angleConstructedTriangle,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe, -Complex.ofReal_pow]
  have hD₂ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.b T.c = (2*b*x/q) • (⟨q,-B⟩ : ℂ) := by
    have hform : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection T.b T.c = (⟨2*b*x, x^2+y^2-b^2⟩ : ℂ) := by
      apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hyperbolicDirection, T, angleConstructedTriangle, _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    rw [hform]
    apply Complex.ext
    · simp only [Complex.smul_re, smul_eq_mul]
      field_simp
    · simp only [Complex.smul_im, smul_eq_mul]
      rw [hcircle]
      ring
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_eq_direction T.rayBA T.rayBC
    T.a_mem_rayBA T.a_ne_b T.c_mem_rayBC T.b_ne_c.symm
  change T.beta = _ at he
  rw [he, hD₁, hD₂,
    InnerProductGeometry.angle_smul_left_of_pos _ _ (show 0 < b^2-1 by nlinarith only [hb]),
    InnerProductGeometry.angle_smul_right_of_pos _ _ (show 0 < 2*b*x/q by positivity)]
  exact (complex_unit_vector_angle_cos B q hB).2

theorem angleConstructedTriangle_cosh_lengthC (b x y : ℝ)
    (hb : 1 < b) (hx : 0 < x) (hy : 0 < y) :
    Real.cosh (angleConstructedTriangle b x y hb hx hy).lengthC = (b^2+1)/(2*b) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle.lengthC, UpperHalfPlane.cosh_dist']
  norm_num [angleConstructedTriangle, _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  ring

/-- Every strictly positive angle triple with sum less than pi is realized by
a genuine finite triangle, with its original tangent-measured angles. -/
theorem exists_finite_triangle_with_angles (α β γ : ℝ)
    (hα : 0 < α) (hβ : 0 < β) (hγ : 0 < γ) (hsum : α+β+γ < Real.pi) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle, T.alpha = α ∧ T.beta = β ∧ T.gamma = γ := by
  obtain ⟨hp, hq, hr, hcos, hsin⟩ := angle_triple_construction_inequalities α β γ hα hβ hγ hsum
  obtain ⟨b, x, y, hb, hx, hy, hAC, hBC, hheight⟩ := angle_construction_circle_coordinates
    (Real.cos α) (Real.cos β) (Real.cos γ) (Real.sin α) (Real.sin β) (Real.sin γ)
    hp hq hr (by nlinarith only [Real.sin_sq_add_cos_sq α])
    (by nlinarith only [Real.sin_sq_add_cos_sq β])
    (by nlinarith only [Real.sin_sq_add_cos_sq γ]) hcos hsin
  let T := angleConstructedTriangle b x y hb hx hy
  have hA : T.alpha = α := by
    apply Real.injOn_cos ⟨T.angles_mem_Ioo.1.1.le, T.angles_mem_Ioo.1.2.le⟩
      ⟨hα.le, by linarith⟩
    exact angleConstructedTriangle_cos_alpha _ _ _ _ _ hp
      (by nlinarith only [Real.sin_sq_add_cos_sq α]) hb hx hy hAC
  have hB : T.beta = β := by
    apply Real.injOn_cos ⟨T.angles_mem_Ioo.2.1.1.le, T.angles_mem_Ioo.2.1.2.le⟩
      ⟨hβ.le, by linarith⟩
    exact angleConstructedTriangle_cos_beta _ _ _ _ _ hq
      (by nlinarith only [Real.sin_sq_add_cos_sq β]) hb hx hy hBC
  refine ⟨T, hA, hB, ?_⟩
  apply Real.injOn_cos ⟨T.angles_mem_Ioo.2.2.1.le, T.angles_mem_Ioo.2.2.2.le⟩
    ⟨hγ.le, by linarith⟩
  have hRule := T.cosine_rule_II
  rw [hA, hB, angleConstructedTriangle_cosh_lengthC] at hRule
  have he := (div_left_inj' (ne_of_gt (mul_pos hp hq))).mp (hRule.symm.trans hheight)
  linarith only [he]

/-- The complete source angle-triple existence criterion, including any ideal vertices. -/
theorem triangle_reflection_type_exists_iff (α β γ : ℝ) :
    (∃ G : Subgroup (ℍ ≃ᵢ ℍ), IsTriangleReflectionType G α β γ) ↔
      0 ≤ α ∧ 0 ≤ β ∧ 0 ≤ γ ∧ α+β+γ < Real.pi := by
  constructor
  · rintro ⟨G, hG⟩
    exact triangle_reflection_type_angles_admissible G α β γ hG
  · rintro ⟨hα, hβ, hγ, hsum⟩
    by_cases hc : γ = 0
    · subst γ
      exact exists_triangle_reflection_type_with_zero α β hα hβ (by linarith only [hsum])
    by_cases ha : α = 0
    · subst α
      let T := prescribedIdealHTriangle β γ hβ hγ (by linarith only [hsum])
      have ht := prescribedIdealHTriangle_angles β γ hβ hγ (by linarith only [hsum])
      have hT := closedHTriangle_cycle_angles T
      have hT' := closedHTriangle_cycle_angles T.cycle
      exact ⟨triangleReflectionGroup T.cycle.cycle, T.cycle.cycle,
        hT'.1.trans (hT.2.1.trans ht.2.2),
        hT'.2.1.trans (hT.2.2.trans ht.1),
        hT'.2.2.trans (hT.1.trans ht.2.1), rfl⟩
    by_cases hb : β = 0
    · subst β
      let T := prescribedIdealHTriangle γ α hγ hα (by linarith only [hsum])
      have ht := prescribedIdealHTriangle_angles γ α hγ hα (by linarith only [hsum])
      have hT := closedHTriangle_cycle_angles T
      exact ⟨triangleReflectionGroup T.cycle, T.cycle,
        hT.1.trans ht.2.1, hT.2.1.trans ht.2.2, hT.2.2.trans ht.1, rfl⟩
    obtain ⟨T, hTα, hTβ, hTγ⟩ := exists_finite_triangle_with_angles α β γ
      (lt_of_le_of_ne hα (Ne.symm ha)) (lt_of_le_of_ne hβ (Ne.symm hb))
      (lt_of_le_of_ne hγ (Ne.symm hc)) hsum
    exact ⟨triangleReflectionGroup T.toClosedHTriangle, T.toClosedHTriangle,
      T.closed_angles.1.trans hTα, T.closed_angles.2.1.trans hTβ,
      T.closed_angles.2.2.trans hTγ, rfl⟩

/-- Same-type subgroups of the entire native isometry group are actually conjugate. -/
theorem IsTriangleReflectionType.groups_conjugate {G H : Subgroup (ℍ ≃ᵢ ℍ)} {α β γ : ℝ}
    (hG : IsTriangleReflectionType G α β γ) (hH : IsTriangleReflectionType H α β γ) :
    ∃ e : ℍ ≃ᵢ ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e G = H := by
  obtain ⟨T, rfl, rfl, rfl, rfl⟩ := hG
  obtain ⟨S, hα, hβ, hγ, rfl⟩ := hH
  exact equal_angle_triangle_reflectionGroups_conjugate T S hα.symm hβ.symm hγ.symm

/-- Exchange the first two physical vertices without changing the triangle's side lines. -/
def swapClosedTriangle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := T.b
  b := T.a
  c := T.c
  noncollinear := by
    rintro ⟨L, hb, ha, hc⟩
    exact T.noncollinear ⟨L, ha, hb, hc⟩

theorem swapClosedTriangle_angles (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (swapClosedTriangle T).alpha = T.beta ∧
      (swapClosedTriangle T).beta = T.alpha ∧ (swapClosedTriangle T).gamma = T.gamma := by
  exact ⟨T.toDiscTriangle.cycle.alpha_eq_of_swapped_neighbors
      (swapClosedTriangle T).toDiscTriangle rfl rfl rfl,
    T.toDiscTriangle.alpha_eq_of_swapped_neighbors
      (swapClosedTriangle T).toDiscTriangle.cycle rfl rfl rfl,
    T.toDiscTriangle.cycle.cycle.alpha_eq_of_swapped_neighbors
      (swapClosedTriangle T).toDiscTriangle.cycle.cycle rfl rfl rfl⟩

theorem swapClosedTriangle_sideA (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (swapClosedTriangle T).sideLineA = T.sideLineB := by
  exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.eq_of_two_closed_points _ _
    T.toDiscTriangle.c_ne_a.symm (swapClosedTriangle T).toDiscTriangle.b_mem_sideLineA
    (swapClosedTriangle T).toDiscTriangle.c_mem_sideLineA
    T.toDiscTriangle.a_mem_sideLineB T.toDiscTriangle.c_mem_sideLineB)

theorem swapClosedTriangle_sideB (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (swapClosedTriangle T).sideLineB = T.sideLineA := by
  exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.eq_of_two_closed_points _ _
    T.toDiscTriangle.b_ne_c.symm (swapClosedTriangle T).toDiscTriangle.c_mem_sideLineB
    (swapClosedTriangle T).toDiscTriangle.a_mem_sideLineB
    T.toDiscTriangle.c_mem_sideLineA T.toDiscTriangle.b_mem_sideLineA)

theorem swapClosedTriangle_sideC (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (swapClosedTriangle T).sideLineC = T.sideLineC := by
  exact congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.eq_of_two_closed_points _ _
    T.toDiscTriangle.a_ne_b.symm (swapClosedTriangle T).toDiscTriangle.a_mem_sideLineC
    (swapClosedTriangle T).toDiscTriangle.b_mem_sideLineC
    T.toDiscTriangle.b_mem_sideLineC T.toDiscTriangle.a_mem_sideLineC)

theorem triangleReflectionGroup_swap (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleReflectionGroup (swapClosedTriangle T) = triangleReflectionGroup T := by
  unfold triangleReflectionGroup triangleReflectionSides
  rw [swapClosedTriangle_sideA, swapClosedTriangle_sideB, swapClosedTriangle_sideC]
  congr 2
  ext L
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

theorem IsTriangleReflectionType.cycle {G : Subgroup (ℍ ≃ᵢ ℍ)} {α β γ : ℝ}
    (h : IsTriangleReflectionType G α β γ) : IsTriangleReflectionType G β γ α := by
  obtain ⟨T, hα, hβ, hγ, hG⟩ := h
  have hc := closedHTriangle_cycle_angles T
  exact ⟨T.cycle, hc.1.trans hβ, hc.2.1.trans hγ, hc.2.2.trans hα,
    hG.trans (triangleReflectionGroup_cycle T).symm⟩

theorem IsTriangleReflectionType.swap {G : Subgroup (ℍ ≃ᵢ ℍ)} {α β γ : ℝ}
    (h : IsTriangleReflectionType G α β γ) : IsTriangleReflectionType G β α γ := by
  obtain ⟨T, hα, hβ, hγ, hG⟩ := h
  have hs := swapClosedTriangle_angles T
  exact ⟨swapClosedTriangle T, hs.1.trans hβ, hs.2.1.trans hα, hs.2.2.trans hγ,
    hG.trans (triangleReflectionGroup_swap T).symm⟩

end LowDimensionalTopology.Geometry.Fuchsian
