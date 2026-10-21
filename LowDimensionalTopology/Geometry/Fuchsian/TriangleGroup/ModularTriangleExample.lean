module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionAngles
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenSharpness
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FundamentalDomain
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.LambertPolygonAdapters
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
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

/-- The original native conformal isometries, mapped to their genuine global Mobius maps. -/
def halfPlaneConformalMobiusHom : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup →* Mobius.complexMobiusGroup where
  toFun f := ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f.val).val, (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f.val).property,
    (halfPlane_native_conformal_iff f.val).mp f.property⟩
  map_one' := by
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (1 : ℍ ≃ᵢ ℍ)).val = (1 : Equiv.Perm Mobius.ExtendedComplex)
    exact congrArg Subtype.val (map_one _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension)
  map_mul' f g := by
    apply Subtype.ext
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (f.val * g.val)).val =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f.val).val * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension g.val).val
    exact congrArg Subtype.val (map_mul _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension f.val g.val)

theorem halfPlaneConformalMobiusHom_matrix (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    halfPlaneConformalMobiusHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalElement A) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := by
  apply Subtype.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)).val = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val
  exact congrArg Subtype.val (nativeHalfPlaneExtension_hSL A)

theorem halfPlaneConformalMobiusHom_isometry : Isometry halfPlaneConformalMobiusHom := by
  apply Isometry.of_dist_eq
  intro f g
  rfl

def modularAxisReflection : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 0)
def modularMiddleReflection : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical (1/2))
def modularRightReflection : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.vertical 1)
def modularCircleReflection : ℍ ≃ᵢ ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry (.circle 0 1 (by norm_num))

def modularReflectionGroupFirst : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure {modularMiddleReflection, modularCircleReflection, modularAxisReflection}

def modularReflectionGroupSecond : Subgroup (ℍ ≃ᵢ ℍ) :=
  Subgroup.closure {modularMiddleReflection, modularCircleReflection, modularRightReflection}

theorem modular_vertical_reflection_relation :
    modularAxisReflection * modularMiddleReflection =
      modularMiddleReflection * modularRightReflection := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (1/2) z) : ℂ) =
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (1/2) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection 1 z) : ℂ)
  simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe, map_sub, Complex.conj_ofReal,
    Complex.conj_conj]
  norm_num
  ring

theorem modular_reflection_groups_equal : modularReflectionGroupFirst = modularReflectionGroupSecond := by
  have hh : modularMiddleReflection * modularMiddleReflection = 1 := by
    simpa only [modularMiddleReflection, pow_two] using
      halfPlaneLineReflectionIsometry_sq (.vertical (1/2))
  have haxis : modularAxisReflection =
      (modularMiddleReflection * modularRightReflection) * modularMiddleReflection := by
    calc
      _ = (modularAxisReflection * modularMiddleReflection) * modularMiddleReflection := by
        rw [mul_assoc, hh, mul_one]
      _ = _ := congrArg (fun e : ℍ ≃ᵢ ℍ => e * modularMiddleReflection)
        modular_vertical_reflection_relation
  have hright : modularRightReflection =
      (modularMiddleReflection * modularAxisReflection) * modularMiddleReflection := by
    symm
    calc
      _ = modularMiddleReflection * (modularAxisReflection * modularMiddleReflection) := mul_assoc _ _ _
      _ = modularMiddleReflection * (modularMiddleReflection * modularRightReflection) := by
        rw [modular_vertical_reflection_relation]
      _ = _ := by rw [← mul_assoc, hh, one_mul]
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [haxis]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    simp only [mem_insert_iff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | rfl
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · rw [hright]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
        (Subgroup.subset_closure (by simp))

/-- The actual finite unit-circle intersection of the two displayed triangles. -/
def modularTriangleCorner : ℍ :=
  ⟨⟨1/2, Real.sqrt 3/2⟩, by positivity⟩

theorem modularTriangleCorner_norm : ‖(modularTriangleCorner : ℂ)‖ = 1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← Complex.normSq_eq_norm_sq]
  norm_num [modularTriangleCorner, Complex.normSq_apply]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]

def modularTriangleRealEndpoint : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel :=
  ⟨((1 : ℂ) : Mobius.ExtendedComplex), by simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet]⟩

theorem modularTriangleRealEndpoint_ideal :
    modularTriangleRealEndpoint.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary 1).mpr (by simp)

def modularTriangleFirst : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel modularTriangleCorner
  b := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel UpperHalfPlane.I
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint
  noncollinear := by
    rintro ⟨L, ha, hb, hc⟩
    obtain ⟨x, rfl⟩ := L.eq_vertical_of_infty_ideal
      ((L.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
    have ha' := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier_mem_interior_iff modularTriangleCorner).mp ha
    have hb' := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier_mem_interior_iff UpperHalfPlane.I).mp hb
    change (1/2 : ℝ) = x at ha'
    change (0 : ℝ) = x at hb'
    linarith

def modularTriangleSecond : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel modularTriangleCorner
  b := modularTriangleRealEndpoint
  c := _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint
  noncollinear := by
    rintro ⟨L, ha, hb, hc⟩
    obtain ⟨x, rfl⟩ := L.eq_vertical_of_infty_ideal
      ((L.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
    have ha' := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier_mem_interior_iff modularTriangleCorner).mp ha
    have hb' := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier_mem_ideal_iff _
      modularTriangleRealEndpoint_ideal).mp hb
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints] at hb'
    change ((1 : ℂ) : Mobius.ExtendedComplex) ∈ {((x : ℂ) : Mobius.ExtendedComplex), ∞} at hb'
    simp only [mem_insert_iff, mem_singleton_iff, OnePoint.coe_ne_infty, or_false] at hb'
    have hreal := congrArg Complex.re (OnePoint.coe_injective hb')
    norm_num at hreal
    change (1/2 : ℝ) = x at ha'
    linarith

theorem modularTriangleFirst_sideC :
    modularTriangleFirst.sideLineC = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num) := by
  let T := modularTriangleFirst.toDiscTriangle
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel modularTriangleCorner ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.a_mem_sideLineC
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel UpperHalfPlane.I ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.b_mem_sideLineC
  apply T.sideLineC.toHalfPlane.eq_of_two_points _
    (show modularTriangleCorner ≠ UpperHalfPlane.I from by
      intro h; have he := congrArg UpperHalfPlane.re h; norm_num [modularTriangleCorner] at he)
    ((T.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff _).mp ha)
    ((T.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff _).mp hb)
  · change ‖(modularTriangleCorner : ℂ) - (0 : ℂ)‖ = 1
    simpa only [sub_zero] using modularTriangleCorner_norm
  · change ‖(UpperHalfPlane.I : ℂ) - (0 : ℂ)‖ = 1
    norm_num

theorem modularTriangleSecond_sideC :
    modularTriangleSecond.sideLineC = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num) := by
  let T := modularTriangleSecond.toDiscTriangle
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel modularTriangleCorner ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.a_mem_sideLineC
  have hb : modularTriangleRealEndpoint ∈ T.sideLineC.toHalfPlane.closedCarrier :=
    (T.sideLineC.closedCarrier_cayley_mem _).mp T.b_mem_sideLineC
  apply T.sideLineC.toHalfPlane.eq_of_shared_ideal_and_interior _ modularTriangleCorner
    ((T.sideLineC.toHalfPlane.closedCarrier_mem_interior_iff _).mp ha) ?_
    ((1 : ℂ) : Mobius.ExtendedComplex)
    ((T.sideLineC.toHalfPlane.closedCarrier_mem_ideal_iff _ modularTriangleRealEndpoint_ideal).mp hb) ?_
  · change ‖(modularTriangleCorner : ℂ) - (0 : ℂ)‖ = 1
    simpa only [sub_zero] using modularTriangleCorner_norm
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circle_idealEndpoints]
    norm_num

theorem halfPlaneLine_eq_vertical_of_finite_infty
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine)
    (z : ℍ)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z ∈ L.closedCarrier)
    (hi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∈ L.closedCarrier) : L = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical z.re := by
  obtain ⟨x, rfl⟩ := L.eq_vertical_of_infty_ideal
    ((L.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hi)
  have hx : z.re = x := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical x).closedCarrier_mem_interior_iff z).mp hz
  rw [hx]

theorem modularTriangleFirst_sideA : modularTriangleFirst.sideLineA = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  let T := modularTriangleFirst.toDiscTriangle
  exact halfPlaneLine_eq_vertical_of_finite_infty _ UpperHalfPlane.I
    ((T.sideLineA.closedCarrier_cayley_mem _).mp T.b_mem_sideLineA)
    ((T.sideLineA.closedCarrier_cayley_mem _).mp T.c_mem_sideLineA)

theorem modularTriangleFirst_sideB : modularTriangleFirst.sideLineB = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (1/2) := by
  let T := modularTriangleFirst.toDiscTriangle
  exact halfPlaneLine_eq_vertical_of_finite_infty _ modularTriangleCorner
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB)
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB)

theorem modularTriangleSecond_sideB : modularTriangleSecond.sideLineB = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (1/2) := by
  let T := modularTriangleSecond.toDiscTriangle
  exact halfPlaneLine_eq_vertical_of_finite_infty _ modularTriangleCorner
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB)
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB)

theorem modularTriangleSecond_sideA : modularTriangleSecond.sideLineA = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 1 := by
  let T := modularTriangleSecond.toDiscTriangle
  have hb : modularTriangleRealEndpoint ∈ T.sideLineA.toHalfPlane.closedCarrier :=
    (T.sideLineA.closedCarrier_cayley_mem _).mp T.b_mem_sideLineA
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint ∈ T.sideLineA.toHalfPlane.closedCarrier :=
    (T.sideLineA.closedCarrier_cayley_mem _).mp T.c_mem_sideLineA
  obtain ⟨x, hx⟩ := T.sideLineA.toHalfPlane.eq_vertical_of_infty_ideal
    ((T.sideLineA.toHalfPlane.closedCarrier_mem_ideal_iff _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal).mp hc)
  have he := (T.sideLineA.toHalfPlane.closedCarrier_mem_ideal_iff _
    modularTriangleRealEndpoint_ideal).mp hb
  rw [hx, _root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints] at he
  change ((1 : ℂ) : Mobius.ExtendedComplex) ∈ {((x : ℂ) : Mobius.ExtendedComplex), ∞} at he
  simp only [mem_insert_iff, mem_singleton_iff, OnePoint.coe_ne_infty, or_false] at he
  have hr := congrArg Complex.re (OnePoint.coe_injective he)
  norm_num at hr
  change T.sideLineA.toHalfPlane = _
  rwa [← hr] at hx

theorem closed_vertex_normalized_identity (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) :
    _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix (1 : GL (Fin 2) ℝ))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph p))) = p.val := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm_apply_apply]
  simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexifiedRealMobiusMatrix,
    _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_one]

theorem closedTriangle_unitCircle_corner_cosine
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (a b : ℂ)
    (hna : ‖a‖ = 1) (hnb : ‖b‖ = 1) (hne : a.re ≠ b.re)
    (ha : T.a.val = (a : Mobius.ExtendedComplex))
    (hb : T.b.val = (b : Mobius.ExtendedComplex))
    (hc : T.c.val = ∞)
    (hside : T.sideLineC = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num)) :
    Real.cos T.alpha = if a.re < b.re then -a.re else a.re := by
  apply T.toDiscTriangle.alpha_cos_normalized
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr (by rw [hc]; simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary]))
    1 (by norm_num) ?_ ?_ a b hna hnb hne ?_ ?_
  · change ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' T.sideLineC.carrier = _
    rw [hside]
    simp
  · exact (closed_vertex_normalized_identity T.c).trans hc
  · exact (closed_vertex_normalized_identity T.a).trans ha
  · exact (closed_vertex_normalized_identity T.b).trans hb

theorem modularTriangleFirst_alpha : modularTriangleFirst.alpha = Real.pi/3 := by
  have he := closedTriangle_unitCircle_corner_cosine modularTriangleFirst
    (modularTriangleCorner : ℂ) (UpperHalfPlane.I : ℂ) modularTriangleCorner_norm (by norm_num)
    (by norm_num [modularTriangleCorner]) rfl rfl rfl modularTriangleFirst_sideC
  norm_num [modularTriangleCorner] at he
  apply Real.injOn_cos
    ⟨modularTriangleFirst.toDiscTriangle.alpha_mem_Ico.1,
      modularTriangleFirst.toDiscTriangle.alpha_mem_Ico.2.le⟩
    (show Real.pi/3 ∈ Icc (0 : ℝ) Real.pi from by constructor <;> linarith [Real.pi_pos])
  rwa [Real.cos_pi_div_three]

theorem modularTriangleSecond_alpha : modularTriangleSecond.alpha = 2*Real.pi/3 := by
  have he := closedTriangle_unitCircle_corner_cosine modularTriangleSecond
    (modularTriangleCorner : ℂ) 1 modularTriangleCorner_norm (by norm_num)
    (by norm_num [modularTriangleCorner]) rfl rfl rfl modularTriangleSecond_sideC
  norm_num [modularTriangleCorner] at he
  apply Real.injOn_cos
    ⟨modularTriangleSecond.toDiscTriangle.alpha_mem_Ico.1,
      modularTriangleSecond.toDiscTriangle.alpha_mem_Ico.2.le⟩
    (show 2*Real.pi/3 ∈ Icc (0 : ℝ) Real.pi from by constructor <;> linarith [Real.pi_pos])
  rw [show 2*Real.pi/3 = Real.pi - Real.pi/3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]
  exact he

theorem modularTriangleFirst_beta : modularTriangleFirst.beta = Real.pi/2 := by
  have ht := closedTriangle_reflection_trace_alpha modularTriangleFirst.toDiscTriangle.cycle
  change (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL modularTriangleFirst.sideLineC
    modularTriangleFirst.sideLineA).val)^2 = 4 * Real.cos modularTriangleFirst.beta^2 at ht
  rw [modularTriangleFirst_sideC, modularTriangleFirst_sideA] at ht
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix, _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
    Fin.sum_univ_two] at ht
  have hc : Real.cos modularTriangleFirst.beta = 0 := by nlinarith only [ht]
  apply Real.injOn_cos
    ⟨modularTriangleFirst.toDiscTriangle.cycle.alpha_mem_Ico.1,
      modularTriangleFirst.toDiscTriangle.cycle.alpha_mem_Ico.2.le⟩
    (show Real.pi/2 ∈ Icc (0 : ℝ) Real.pi from by constructor <;> linarith [Real.pi_pos])
  rwa [Real.cos_pi_div_two]

theorem modularTriangleFirst_gamma : modularTriangleFirst.gamma = 0 :=
  modularTriangleFirst.toDiscTriangle.gamma_of_ideal
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal)

theorem modularTriangleSecond_beta : modularTriangleSecond.beta = 0 :=
  modularTriangleSecond.toDiscTriangle.beta_of_ideal
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff modularTriangleRealEndpoint).mpr modularTriangleRealEndpoint_ideal)

theorem modularTriangleSecond_gamma : modularTriangleSecond.gamma = 0 :=
  modularTriangleSecond.toDiscTriangle.gamma_of_ideal
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal)

theorem modularTriangleFirst_group : triangleReflectionGroup modularTriangleFirst = modularReflectionGroupFirst := by
  change Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ''
    {modularTriangleFirst.sideLineA, modularTriangleFirst.sideLineB, modularTriangleFirst.sideLineC}) = _
  rw [modularTriangleFirst_sideA, modularTriangleFirst_sideB, modularTriangleFirst_sideC]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext f
  simp only [image_insert_eq, image_singleton, modularAxisReflection, modularMiddleReflection,
    modularCircleReflection, mem_insert_iff, mem_singleton_iff]
  tauto

theorem modularTriangleSecond_group : triangleReflectionGroup modularTriangleSecond = modularReflectionGroupSecond := by
  change Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ''
    {modularTriangleSecond.sideLineA, modularTriangleSecond.sideLineB, modularTriangleSecond.sideLineC}) = _
  rw [modularTriangleSecond_sideA, modularTriangleSecond_sideB, modularTriangleSecond_sideC]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext f
  simp only [image_insert_eq, image_singleton, modularRightReflection, modularMiddleReflection,
    modularCircleReflection, mem_insert_iff, mem_singleton_iff]
  tauto

theorem modular_reflection_group_two_triangle_types :
    IsTriangleReflectionType modularReflectionGroupFirst (Real.pi/3) (Real.pi/2) 0 ∧
      IsTriangleReflectionType modularReflectionGroupFirst (2*Real.pi/3) 0 0 := by
  constructor
  · exact ⟨modularTriangleFirst, modularTriangleFirst_alpha, modularTriangleFirst_beta,
      modularTriangleFirst_gamma, modularTriangleFirst_group.symm⟩
  · exact ⟨modularTriangleSecond, modularTriangleSecond_alpha, modularTriangleSecond_beta,
      modularTriangleSecond_gamma, modular_reflection_groups_equal.trans modularTriangleSecond_group.symm⟩

def nativeConformalSubgroupMobiusHom (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) : H →* Mobius.complexMobiusGroup :=
  halfPlaneConformalMobiusHom.comp (Subgroup.inclusion hH)

theorem nativeConformalSubgroupMobiusHom_isometry (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) : Isometry (nativeConformalSubgroupMobiusHom H hH) := by
  apply Isometry.of_dist_eq
  intro f g
  rfl

theorem nativeConformalSubgroupMobiusHom_matrix (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H) :
    nativeConformalSubgroupMobiusHom H hH ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hA⟩ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A := by
  exact halfPlaneConformalMobiusHom_matrix A

theorem native_conformal_subgroup_discrete_of_image (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hH : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (J : Subgroup Mobius.complexMobiusGroup)
    (hd : DiscreteTopology J)
    (hmem : ∀ f : H, nativeConformalSubgroupMobiusHom H hH f ∈ J) : DiscreteTopology H := by
  let F : H → J := fun f => ⟨nativeConformalSubgroupMobiusHom H hH f, hmem f⟩
  have hcont : Continuous F := by
    apply Continuous.subtype_mk
    exact (nativeConformalSubgroupMobiusHom_isometry H hH).continuous
  have hinj : Function.Injective F := by
    intro f g he
    exact (nativeConformalSubgroupMobiusHom_isometry H hH).injective
      (congrArg Subtype.val he)
  have : DiscreteTopology J := hd
  exact DiscreteTopology.of_continuous_injective hcont hinj

theorem triangle_conformal_image_le_of_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (J : Subgroup Mobius.complexMobiusGroup)
    (hfirst : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB) ∈ J)
    (hsecond : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB) ∈ J) :
    ∀ f : triangleConformalGroup T,
      nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right f ∈ J := by
  let H := triangleConformalGroup T
  let hH : H ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := inf_le_right
  let F := nativeConformalSubgroupMobiusHom H hH
  have hgen : H = trianglePairProductGroup T := triangleConformalGroup_eq_pairProductGroup T
  have hm : ∀ f (hf : f ∈ trianglePairProductGroup T), F ⟨f, hgen.symm ▸ hf⟩ ∈ J := by
    intro f hf
    change f ∈ Subgroup.closure _ at hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      simp only [mem_insert_iff, mem_singleton_iff] at hf
      rcases hf with rfl | rfl
      · have hn := reflectionProductSL_native T.sideLineA T.sideLineB
        have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA *
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB ∈ H :=
          hgen.symm ▸ Subgroup.subset_closure (Or.inl rfl)
        have he : (⟨_, ha⟩ : H) =
            ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB), hn ▸ ha⟩ :=
          Subtype.ext hn
        rw [he]
        exact (nativeConformalSubgroupMobiusHom_matrix H hH _ _).symm ▸ hfirst
      · have hn := reflectionProductSL_native T.sideLineC T.sideLineB
        have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC *
            _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB ∈ H :=
          hgen.symm ▸ Subgroup.subset_closure (Or.inr (mem_singleton _))
        have he : (⟨_, ha⟩ : H) =
            ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB), hn ▸ ha⟩ :=
          Subtype.ext hn
        rw [he]
        exact (nativeConformalSubgroupMobiusHom_matrix H hH _ _).symm ▸ hsecond
    | one =>
      change F 1 ∈ J
      rw [map_one]
      exact J.one_mem
    | mul x y hx hy ihx ihy =>
      have he : (⟨x*y, _⟩ : H) = (⟨x, hgen.symm ▸ hx⟩ : H) * ⟨y, hgen.symm ▸ hy⟩ := rfl
      rw [he, map_mul]
      exact J.mul_mem ihx ihy
    | inv x hx ih =>
      have he : (⟨x⁻¹, _⟩ : H) = (⟨x, hgen.symm ▸ hx⟩ : H)⁻¹ := rfl
      rw [he, map_inv]
      exact J.inv_mem ih
  intro f
  exact hm f.val (hgen ▸ f.property)

theorem triangle_conformal_discrete_of_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (J : Subgroup Mobius.complexMobiusGroup) (hd : DiscreteTopology J)
    (hfirst : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB) ∈ J)
    (hsecond : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB) ∈ J) :
    DiscreteTopology (triangleConformalGroup T) :=
  native_conformal_subgroup_discrete_of_image _ inf_le_right J hd
    (triangle_conformal_image_le_of_generators T J hfirst hsecond)

def modularInversionSL : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![0, -1; 1, 0], by norm_num⟩

theorem modularInversionSL_projection : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modularInversionSL = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom modularInversionSL) =
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [modularInversionSL, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversionLift,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem modularTranslationSL_projection : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation := by
  change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) = _
  rw [← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation_lift]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL, _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem modularNegativeTranslationSL_projection :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation⁻¹ := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1) * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL, Matrix.mul_apply, Fin.sum_univ_two]
  rw [(eq_inv_iff_mul_eq_one).mpr he, map_inv, modularTranslationSL_projection]

theorem modularTriangleFirst_generator_projections :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL modularTriangleFirst.sideLineA modularTriangleFirst.sideLineB) =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation⁻¹ ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL modularTriangleFirst.sideLineC modularTriangleFirst.sideLineB) =
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation⁻¹ := by
  rw [modularTriangleFirst_sideA, modularTriangleFirst_sideB, modularTriangleFirst_sideC]
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (.vertical 0) (.vertical (1/2)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL, Matrix.mul_apply, Fin.sum_univ_two]
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL (.circle 0 1 (by norm_num)) (.vertical (1/2)) =
      -(modularInversionSL * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionScale, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionMatrix,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflectionMatrix, _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflectionMatrix, modularInversionSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
        Matrix.SpecialLinearGroup.coe_neg, Matrix.mul_apply, Fin.sum_univ_two]
  rw [hA, hB, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg, map_mul, modularInversionSL_projection,
    modularNegativeTranslationSL_projection]
  exact ⟨rfl, rfl⟩

theorem modularTriangleFirst_conformal_discrete : DiscreteTopology (triangleConformalGroup modularTriangleFirst) := by
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup :=
    Subgroup.subset_closure (Or.inl rfl)
  have hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup :=
    Subgroup.subset_closure (Or.inr (mem_singleton _))
  apply triangle_conformal_discrete_of_generators modularTriangleFirst _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup_discrete
  · rw [modularTriangleFirst_generator_projections.1]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.inv_mem hT
  · rw [modularTriangleFirst_generator_projections.2]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.mul_mem hS (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.inv_mem hT)

theorem modularReflectionGroupFirst_discrete : DiscreteTopology modularReflectionGroupFirst := by
  rw [← modularTriangleFirst_group]
  exact (triangle_discrete_full_iff_conformal modularTriangleFirst).mpr modularTriangleFirst_conformal_discrete

theorem modularReflectionGroupSecond_discrete : DiscreteTopology modularReflectionGroupSecond := by
  rw [← modular_reflection_groups_equal]
  exact modularReflectionGroupFirst_discrete

def modularConformalMobiusImage : Subgroup Mobius.complexMobiusGroup :=
  (nativeConformalSubgroupMobiusHom (triangleConformalGroup modularTriangleFirst) inf_le_right).range

theorem modularConformalMobiusImage_eq : modularConformalMobiusImage = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  let H := triangleConformalGroup modularTriangleFirst
  let F := nativeConformalSubgroupMobiusHom H inf_le_right
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup :=
    Subgroup.subset_closure (Or.inl rfl)
  have hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup :=
    Subgroup.subset_closure (Or.inr (mem_singleton _))
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL modularTriangleFirst.sideLineA
      modularTriangleFirst.sideLineB) ∈ H := by
    change _ ∈ triangleConformalGroup modularTriangleFirst
    rw [← reflectionProductSL_native, triangleConformalGroup_eq_pairProductGroup]
    exact Subgroup.subset_closure (Or.inl rfl)
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL modularTriangleFirst.sideLineC
      modularTriangleFirst.sideLineB) ∈ H := by
    change _ ∈ triangleConformalGroup modularTriangleFirst
    rw [← reflectionProductSL_native, triangleConformalGroup_eq_pairProductGroup]
    exact Subgroup.subset_closure (Or.inr (mem_singleton _))
  have haRange : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation⁻¹ ∈ F.range := by
    refine ⟨⟨_, ha⟩, ?_⟩
    exact (nativeConformalSubgroupMobiusHom_matrix H inf_le_right _ ha).trans
      modularTriangleFirst_generator_projections.1
  have hbRange : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation⁻¹ ∈ F.range := by
    refine ⟨⟨_, hb⟩, ?_⟩
    exact (nativeConformalSubgroupMobiusHom_matrix H inf_le_right _ hb).trans
      modularTriangleFirst_generator_projections.2
  have htRange : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation ∈ F.range := by
    simpa only [inv_inv] using F.range.inv_mem haRange
  have hsRange : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion ∈ F.range := by
    have h := F.range.mul_mem hbRange htRange
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
  apply le_antisymm
  · rintro g ⟨f, rfl⟩
    exact triangle_conformal_image_le_of_generators modularTriangleFirst _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup
      (by rw [modularTriangleFirst_generator_projections.1]; exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.inv_mem hT)
      (by rw [modularTriangleFirst_generator_projections.2];
          exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.mul_mem hS (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup.inv_mem hT)) f
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases hg with rfl | hg
    · exact htRange
    · exact (mem_singleton_iff.mp hg).symm ▸ hsRange

theorem modularTriangle_area_ratio :
    MeasureTheory.volume modularTriangleSecond.interior =
      (2 : ENNReal) * MeasureTheory.volume modularTriangleFirst.interior := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.area_eq_angle_defect, _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.area_eq_angle_defect,
    modularTriangleFirst_alpha, modularTriangleFirst_beta, modularTriangleFirst_gamma,
    modularTriangleSecond_alpha, modularTriangleSecond_beta, modularTriangleSecond_gamma]
  have hfirst : Real.pi - Real.pi/3 - Real.pi/2 - 0 = Real.pi/6 := by ring
  have hsecond : Real.pi - 2*Real.pi/3 - 0 - 0 = 2*(Real.pi/6) := by ring
  rw [hfirst, hsecond, ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num)]
  norm_num

theorem modularTriangleSecond_interior_graph :
    modularTriangleSecond.interior =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun x => Real.sqrt (1-x^2)) (Ioo (1/2) 1) := by
  let T := modularTriangleSecond.toDiscTriangle
  have hc : ‖(T.c : ℂ)‖ = 1 :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal
  have he := T.normalized_interior_eq_graph hc 1 (by norm_num)
    (closed_vertex_normalized_identity modularTriangleSecond.c) ?_
    (modularTriangleCorner : ℂ) 1 modularTriangleCorner_norm (by norm_num)
    (by norm_num [modularTriangleCorner])
    (closed_vertex_normalized_identity modularTriangleSecond.a)
    (closed_vertex_normalized_identity modularTriangleSecond.b) ?_ ?_
  · change T.halfPlaneInterior = _
    simpa only [one_smul, image_id', modularTriangleCorner, Complex.one_re,
      min_eq_left (show (1/2 : ℝ) ≤ 1 by norm_num), max_eq_right (show (1/2 : ℝ) ≤ 1 by norm_num)] using he
  · change ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' modularTriangleSecond.sideLineC.carrier = _
    rw [modularTriangleSecond_sideC]
    simp
  · change ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' modularTriangleSecond.sideLineA.carrier = _
    rw [modularTriangleSecond_sideA]
    simp
  · change ((1 : GL (Fin 2) ℝ) • · : ℍ → ℍ) '' modularTriangleSecond.sideLineB.carrier = _
    rw [modularTriangleSecond_sideB]
    simp [modularTriangleCorner]

def modularTriangleOverlapPoint : ℍ := ⟨⟨3/4, 1⟩, by norm_num⟩
def modularTriangleOverlapImage : ℍ := ⟨⟨13/17, 16/17⟩, by norm_num⟩

theorem modularTriangle_overlap_points_inside :
    modularTriangleOverlapPoint ∈ modularTriangleSecond.interior ∧
      modularTriangleOverlapImage ∈ modularTriangleSecond.interior := by
  rw [modularTriangleSecond_interior_graph]
  constructor
  · change ((3/4 : ℝ) ∈ Ioo (1/2) 1) ∧ Real.sqrt (1-(3/4)^2) < 1
    constructor
    · norm_num
    · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
  · change ((13/17 : ℝ) ∈ Ioo (1/2) 1) ∧ Real.sqrt (1-(13/17)^2) < 16/17
    constructor
    · norm_num
    · exact (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)

theorem modularTriangle_overlap_action :
    (modularCircleReflection * modularMiddleReflection * modularCircleReflection)
      modularTriangleOverlapPoint = modularTriangleOverlapImage := by
  apply UpperHalfPlane.ext
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 (by norm_num)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (1/2) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 (by norm_num) modularTriangleOverlapPoint)) : ℂ) = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  apply Complex.ext <;>
    norm_num [modularTriangleOverlapPoint, modularTriangleOverlapImage, Complex.div_re,
      Complex.div_im, Complex.normSq_apply]

/-- The larger original triangle really fails the geometric orbit-selector domain condition. -/
theorem modularTriangleSecond_not_fundamentalDomain :
    ¬ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain modularReflectionGroupSecond ℍ MeasureTheory.volume
      modularTriangleSecond.interior := by
  intro hD
  have hC : modularCircleReflection ∈ modularReflectionGroupSecond := Subgroup.subset_closure (by simp)
  have hM : modularMiddleReflection ∈ modularReflectionGroupSecond := Subgroup.subset_closure (by simp)
  let g : modularReflectionGroupSecond :=
    ⟨modularCircleReflection * modularMiddleReflection * modularCircleReflection,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hC hM) hC⟩
  have hg : g • modularTriangleOverlapPoint = modularTriangleOverlapImage := modularTriangle_overlap_action
  have ho : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection modularReflectionGroupSecond ℍ modularTriangleOverlapPoint =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection modularReflectionGroupSecond ℍ modularTriangleOverlapImage := by
    rw [← hg]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul modularReflectionGroupSecond ℍ g modularTriangleOverlapPoint).symm
  have he := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem modularReflectionGroupSecond ℍ hD
    modularTriangle_overlap_points_inside.1 modularTriangle_overlap_points_inside.2 ho
  have hi := congrArg UpperHalfPlane.im he
  norm_num [modularTriangleOverlapPoint, modularTriangleOverlapImage] at hi

/-- The first physical triangle with the vertex labels in the displayed source order. -/
def modularBookTriangleFirst : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle where
  a := modularTriangleFirst.c
  b := modularTriangleFirst.b
  c := modularTriangleFirst.a
  noncollinear := by
    rintro ⟨L, hc, hb, ha⟩
    exact modularTriangleFirst.noncollinear ⟨L, ha, hb, hc⟩

theorem modularBookTriangleFirst_angles :
    modularBookTriangleFirst.alpha = 0 ∧ modularBookTriangleFirst.beta = Real.pi/2 ∧
      modularBookTriangleFirst.gamma = Real.pi/3 := by
  have hb := modularTriangleFirst.toDiscTriangle.cycle.alpha_eq_of_swapped_neighbors
    modularBookTriangleFirst.toDiscTriangle.cycle rfl rfl rfl
  have hc := modularTriangleFirst.toDiscTriangle.alpha_eq_of_swapped_neighbors
    modularBookTriangleFirst.toDiscTriangle.cycle.cycle rfl rfl rfl
  exact ⟨modularBookTriangleFirst.toDiscTriangle.alpha_of_ideal
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint).mpr _root_.LowDimensionalTopology.Geometry.Hyperbolic.twoIdealInfiniteEndpoint_ideal),
    hb.trans modularTriangleFirst_beta, hc.trans modularTriangleFirst_alpha⟩

theorem modularBookTriangleFirst_sideA :
    modularBookTriangleFirst.sideLineA = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 (by norm_num) := by
  let T := modularBookTriangleFirst.toDiscTriangle
  have hb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel UpperHalfPlane.I ∈ T.sideLineA.toHalfPlane.closedCarrier :=
    (T.sideLineA.closedCarrier_cayley_mem _).mp T.b_mem_sideLineA
  have hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel modularTriangleCorner ∈ T.sideLineA.toHalfPlane.closedCarrier :=
    (T.sideLineA.closedCarrier_cayley_mem _).mp T.c_mem_sideLineA
  apply T.sideLineA.toHalfPlane.eq_of_two_points _
    (show UpperHalfPlane.I ≠ modularTriangleCorner from by
      intro h; have he := congrArg UpperHalfPlane.re h; norm_num [modularTriangleCorner] at he)
    ((T.sideLineA.toHalfPlane.closedCarrier_mem_interior_iff _).mp hb)
    ((T.sideLineA.toHalfPlane.closedCarrier_mem_interior_iff _).mp hc)
  · change ‖(UpperHalfPlane.I : ℂ) - (0 : ℂ)‖ = 1
    norm_num
  · change ‖(modularTriangleCorner : ℂ) - (0 : ℂ)‖ = 1
    simpa only [sub_zero] using modularTriangleCorner_norm

theorem modularBookTriangleFirst_sideB :
    modularBookTriangleFirst.sideLineB = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (1/2) := by
  let T := modularBookTriangleFirst.toDiscTriangle
  exact halfPlaneLine_eq_vertical_of_finite_infty _ modularTriangleCorner
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.c_mem_sideLineB)
    ((T.sideLineB.closedCarrier_cayley_mem _).mp T.a_mem_sideLineB)

theorem modularBookTriangleFirst_sideC :
    modularBookTriangleFirst.sideLineC = _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  let T := modularBookTriangleFirst.toDiscTriangle
  exact halfPlaneLine_eq_vertical_of_finite_infty _ UpperHalfPlane.I
    ((T.sideLineC.closedCarrier_cayley_mem _).mp T.b_mem_sideLineC)
    ((T.sideLineC.closedCarrier_cayley_mem _).mp T.a_mem_sideLineC)

theorem modularBookTriangleFirst_group :
    triangleReflectionGroup modularBookTriangleFirst = modularReflectionGroupFirst := by
  change Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ''
    {modularBookTriangleFirst.sideLineA, modularBookTriangleFirst.sideLineB,
      modularBookTriangleFirst.sideLineC}) = _
  rw [modularBookTriangleFirst_sideA, modularBookTriangleFirst_sideB, modularBookTriangleFirst_sideC]
  change Subgroup.closure _ = Subgroup.closure _
  congr 1
  ext f
  simp only [image_insert_eq, image_singleton, modularAxisReflection, modularMiddleReflection,
    modularCircleReflection, mem_insert_iff, mem_singleton_iff]
  tauto

/-- In exactly the original ordered angle triples. -/
theorem modular_reflection_group_source_types :
    IsTriangleReflectionType modularReflectionGroupFirst 0 (Real.pi/2) (Real.pi/3) ∧
      IsTriangleReflectionType modularReflectionGroupFirst 0 0 (2*Real.pi/3) := by
  constructor
  · exact ⟨modularBookTriangleFirst, modularBookTriangleFirst_angles.1,
      modularBookTriangleFirst_angles.2.1, modularBookTriangleFirst_angles.2.2,
      modularBookTriangleFirst_group.symm⟩
  · exact ⟨modularTriangleSecond.cycle, modularTriangleSecond_beta, modularTriangleSecond_gamma,
      modularTriangleSecond_alpha, modular_reflection_groups_equal.trans
        ((triangleReflectionGroup_cycle modularTriangleSecond).trans modularTriangleSecond_group).symm⟩

/-- The actual projective boundary action of the full integral special-linear group. -/
def integralHalfPlaneMobiusHom : Matrix.SpecialLinearGroup
    (Fin 2) ℤ →* Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ))

theorem integralHalfPlaneMobiusHom_S :
    integralHalfPlaneMobiusHom ModularGroup.S = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessInversion := by
  rw [← modularInversionSL_projection]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralHalfPlaneMobiusHom, ModularGroup.S, modularInversionSL,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem integralHalfPlaneMobiusHom_T :
    integralHalfPlaneMobiusHom ModularGroup.T = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessTranslation := by
  rw [← modularTranslationSL_projection]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [integralHalfPlaneMobiusHom, ModularGroup.T, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem integralHalfPlaneMobiusHom_range : integralHalfPlaneMobiusHom.range = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenSharpnessGroup := by
  rw [← Subgroup.map_top, ← SpecialLinearGroup.SL2Z_generators, MonoidHom.map_closure]
  simp only [image_insert_eq, image_singleton, integralHalfPlaneMobiusHom_S, integralHalfPlaneMobiusHom_T]
  rw [pair_comm]
  rfl

/-- The conformal subgroup in the source example is the genuine projective modular group. -/
theorem modularConformalMobiusImage_eq_integral :
    modularConformalMobiusImage = integralHalfPlaneMobiusHom.range := by
  rw [modularConformalMobiusImage_eq, integralHalfPlaneMobiusHom_range]

end LowDimensionalTopology.Geometry.Fuchsian
