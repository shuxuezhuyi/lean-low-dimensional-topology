/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticUniversalDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTrianglePoincareData
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A parabolic product of specified actual mirrors forces the two original
mirrors to share exactly one ideal endpoint. -/
theorem parabolic_reflection_product_parallel
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (M N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (he : ∀ z : ℍ, C • z = M.reflection
      (N.reflection z)) :
    M.Parallel N := by
  have hne : M ≠ N := by
    intro hMN
    have hh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius 1 := by
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_of_native_action
      intro z
      rw [he, hMN, N.reflection_involutive]
      simp only [one_smul]
    exact hC.1 (by simpa only [map_one] using hh)
  have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflection_product_abs_trace M N C he
  have htrace := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff C hC.1).mp hC
  have habs : |Matrix.trace C.val| / 2 = 1 := by
    nlinarith only [htrace, abs_nonneg (Matrix.trace C.val), sq_abs (Matrix.trace C.val)]
  have hone : _root_.LowDimensionalTopology.Geometry.Inversive.inversiveProduct M.extendedCircle.realModel N.extendedCircle.realModel = 1 :=
    ht.trans habs
  rcases M.classification N hne with hp | hi | hd
  · exact hp
  · obtain ⟨z, hzM, hzN⟩ := hi.2.2
    exact False.elim (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parabolic_no_fixed C hC z (by
      rw [he, (N.reflection_fixed_iff z).mpr hzN, (M.reflection_fixed_iff z).mpr hzM]))
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cosh_lineDist M N hd] at hone
    exact False.elim ((ne_of_gt (Real.one_lt_cosh.mpr (ne_of_gt (M.lineDist_pos N hd)))) hone)

/-- The literal joining line and two mirror factors give a genuine one-ideal
triangle when the original elliptic product is parabolic. -/
theorem elliptic_pair_parabolic_product_triangle_vertices
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (L M N :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine),
      T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) ∧
      T.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)) ∧
      T.b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary ∧ T.b.val ∈ M.idealEndpoints ∧ T.b.val ∈ N.idealEndpoints ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∈ M.carrier ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∈ L.carrier ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ∈ L.carrier ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ∈ N.carrier ∧
      (∀ z : ℍ, A • z = M.reflection (L.reflection z)) ∧
      (∀ z : ℍ, B • z = L.reflection (N.reflection z)) := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨L, M, N, huL, hvL, huM, hvN, hLM, _hLN, hAeq, hBeq⟩ :=
    elliptic_pair_common_reflection_factors A B hA hB huv
  have hprod (z : ℍ) : (A * B) • z = M.reflection (N.reflection z) := by
    rw [mul_smul, congrFun hAeq, congrFun hBeq, Function.comp_apply, Function.comp_apply,
      L.reflection_involutive]
  obtain ⟨_hMN, p, hp⟩ := parabolic_reflection_product_parallel (A * B) hAB M N hprod
  have hpMN : p ∈ M.idealEndpoints ∩ N.idealEndpoints := hp.symm ▸ mem_singleton p
  have hpIdeal : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary := by
    obtain ⟨a, b, _γ, _hab, ha, hb, hends, _⟩ := M.exists_idealEndpoints_pair
    have hm := hpMN.1
    rw [hends, mem_insert_iff, mem_singleton_iff] at hm
    rcases hm with rfl | rfl
    · exact ha
    · exact hb
  have hpClosed : p ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet_eq_open_union_boundary]
    exact Or.inr hpIdeal
  let P : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel := ⟨p, hpClosed⟩
  let T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel v, P, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel u, by
    rintro ⟨K, hvK, hpK, huK⟩
    have hvK' : v ∈ K.carrier := (K.closedCarrier_mem_interior_iff v).mp hvK
    have huK' : u ∈ K.carrier := (K.closedCarrier_mem_interior_iff u).mp huK
    have hKL : K = L := K.eq_of_two_points L huv huK' hvK' huL hvL
    have hpL : p ∈ L.idealEndpoints := by
      have h := (K.closedCarrier_mem_ideal_iff P hpIdeal).mp hpK
      simpa only [hKL] using h
    exact hLM (L.eq_of_shared_ideal_and_interior M u huL huM p hpL hpMN.1)⟩
  exact ⟨T, L, M, N, rfl, rfl, hpIdeal, hpMN.1, hpMN.2, huM, huL, hvL, hvN,
    fun z => congrFun hAeq z, fun z => congrFun hBeq z⟩

/-- An actual finite corner, with the other two endpoints possibly ideal,
has its measured angle detected by the original mirror-product trace. -/
theorem closed_triangle_finite_corner_product_trace_square
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (z : ℍ) (hz : T.a =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : ∀ x : ℍ, A • x = T.sideLineB.reflection (T.sideLineC.reflection x)) :
    (Matrix.trace A.val)^2 = 4 * (Real.cos T.alpha)^2 := by
  let C := T.finiteCornerAtA z hz
  have hact : ∀ x : ℍ, A • x = C.rayAC.supportLine.reflection (C.rayAB.supportLine.reflection x) := by
    intro x
    rw [C.supportAC, C.supportAB]
    exact he x
  have hh := native_ray_reflection_product_trace_square A C.rayAC C.rayAB hact
  have hang : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure C.rayAC C.rayAB = T.alpha :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _
      _).trans (_root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangle_finiteCorner_angle T z hz)
  rwa [hang] at hh

/-- The entire original group, rather than only selected reflection factors,
is the actual conformal group of the constructed one-ideal triangle. -/
theorem elliptic_pair_parabolic_product_actual_triangle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,
      T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) ∧
      T.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)) ∧
      T.b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary ∧ T.beta = 0 ∧
      (Matrix.trace A.val)^2 = 4 * (Real.cos T.gamma)^2 ∧
      (Matrix.trace B.val)^2 = 4 * (Real.cos T.alpha)^2 ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T := by
  obtain ⟨T, L, M, N, ha, hc, hb, hbM, hbN, huM, huL, hvL, hvN, hAeq, hBeq⟩ :=
    elliptic_pair_parabolic_product_triangle_vertices A B hA hB huv hAB
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  have hmap (K : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel) (hz : z ∈ K.closedCarrier) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph z ∈ K.toDiscLine.closedCarrier := by
    rw [← K.cayley_image_closedCarrier]
    exact mem_image_of_mem _ hz
  have huMc : T.c ∈ M.closedCarrier := by
    rw [hc]
    exact (M.closedCarrier_mem_interior_iff u).mpr huM
  have huLc : T.c ∈ L.closedCarrier := by
    rw [hc]
    exact (L.closedCarrier_mem_interior_iff u).mpr huL
  have hvLc : T.a ∈ L.closedCarrier := by
    rw [ha]
    exact (L.closedCarrier_mem_interior_iff v).mpr hvL
  have hvNc : T.a ∈ N.closedCarrier := by
    rw [ha]
    exact (N.closedCarrier_mem_interior_iff v).mpr hvN
  have hpMc := (M.closedCarrier_mem_ideal_iff T.b hb).mpr hbM
  have hpNc := (N.closedCarrier_mem_ideal_iff T.b hb).mpr hbN
  have hTA : T.sideLineA = M := by
    have he : T.toDiscTriangle.sideLineA = M.toDiscLine :=
      T.toDiscTriangle.sideLineA.eq_of_two_closed_points M.toDiscLine T.toDiscTriangle.b_ne_c
        T.toDiscTriangle.b_mem_sideLineA T.toDiscTriangle.c_mem_sideLineA
        (hmap M T.b hpMc) (hmap M T.c huMc)
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.sideLineA,
      M.toDiscLine_toHalfPlane] using
      congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he
  have hTB : T.sideLineB = L := by
    have he : T.toDiscTriangle.sideLineB = L.toDiscLine :=
      T.toDiscTriangle.sideLineB.eq_of_two_closed_points L.toDiscLine T.toDiscTriangle.c_ne_a
        T.toDiscTriangle.c_mem_sideLineB T.toDiscTriangle.a_mem_sideLineB
        (hmap L T.c huLc) (hmap L T.a hvLc)
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.sideLineB,
      L.toDiscLine_toHalfPlane] using
      congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he
  have hTC : T.sideLineC = N := by
    have he : T.toDiscTriangle.sideLineC = N.toDiscLine :=
      T.toDiscTriangle.sideLineC.eq_of_two_closed_points N.toDiscLine T.toDiscTriangle.a_ne_b
        T.toDiscTriangle.a_mem_sideLineC T.toDiscTriangle.b_mem_sideLineC
        (hmap N T.a hvNc) (hmap N T.b hpNc)
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.sideLineC,
      N.toDiscLine_toHalfPlane] using
      congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane he
  have htrA := closed_triangle_finite_corner_product_trace_square T.cycle.cycle u hc A (by
    intro z
    change A • z = T.sideLineA.reflection (T.sideLineB.reflection z)
    rw [hTA, hTB]
    exact hAeq z)
  change (Matrix.trace A.val)^2 = 4 * (Real.cos T.gamma)^2 at htrA
  have htrB := closed_triangle_finite_corner_product_trace_square T v ha B (by
    intro z
    rw [hTB, hTC]
    exact hBeq z)
  have hAI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry M *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := IsometryEquiv.ext hAeq
  have hBI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N := IsometryEquiv.ext hBeq
  have hBinv : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    B)⁻¹ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := by
    rw [hBI, mul_inv_rev]
    exact congrArg₂ (· * ·) (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_inv N)
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_inv L)
  refine ⟨T, ha, hc, hb, ?_, htrA, htrB, ?_⟩
  · exact T.toDiscTriangle.beta_of_ideal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_ideal_norm
    T.b hb)
  · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup_eq_pairProductGroup]
    change Subgroup.closure _ = Subgroup.closure _
    rw [hTA, hTB, hTC]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry]
    rw [← hAI, ← hBinv]
    apply le_antisymm
    · apply (Subgroup.closure_le _).mpr
      rintro k (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact inv_inv (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) ▸
          (Subgroup.closure _).inv_mem (Subgroup.subset_closure (by simp))
    · apply (Subgroup.closure_le _).mpr
      rintro k (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · exact (Subgroup.closure _).inv_mem (Subgroup.subset_closure (by simp))

/-- The ideal-vertex limit of the second cosine rule is established directly
from the actual normalized unit-semicircle vertices. -/
theorem one_ideal_triangle_finite_side_cosh
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) (u v : ℍ)
    (ha : T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel u) (hb : T.b =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel v)
    (hc : T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) :
    Real.cosh (dist u v) = (1 + Real.cos T.alpha * Real.cos T.beta) /
      (Real.sin T.alpha * Real.sin T.beta) := by
  have hci : ‖(T.toDiscTriangle.c :
    ℂ)‖ = 1 := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr hc
  obtain ⟨g, hg, hpEnd, hline⟩ := T.toDiscTriangle.exists_ideal_vertex_area_normalizer hci
  obtain ⟨a, b, hna, hnb, hia, hib, hne, hga, hgb, _hA, _hB⟩ :=
    T.toDiscTriangle.normalized_sides_and_vertices hci g hg hpEnd hline
  have hua : T.toDiscTriangle.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.a = _
    rw [ha, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
  have hvb : T.toDiscTriangle.b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph T.b = _
    rw [hb, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_on_interior]
  have hgu : ((g • u : ℍ) : ℂ) = a := by
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_closed_finite_vertex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u) g hg a (by rwa [← hua])
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hh
  have hgv : ((g • v : ℍ) : ℂ) = b := by
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_closed_finite_vertex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v) g hg b (by rwa [← hvb])
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hh
  have hα := T.toDiscTriangle.alpha_cos_normalized hci g hg hline hpEnd a b hna hnb hne hga hgb
  have hβ := T.toDiscTriangle.beta_cos_normalized hci g hg hline hpEnd a b hna hnb hne hga hgb
  change Real.cos T.alpha = _ at hα
  change Real.cos T.beta = _ at hβ
  have hcosprod : Real.cos T.alpha * Real.cos T.beta = -a.re * b.re := by
    by_cases hab : a.re < b.re
    · rw [ite_eq_left hab] at hα
      rw [ite_eq_right (not_lt_of_ge hab.le)] at hβ
      rw [hα, hβ]
    · have hba : b.re < a.re := lt_of_le_of_ne (le_of_not_gt hab) hne.symm
      rw [ite_eq_right hab] at hα
      rw [ite_eq_left hba] at hβ
      rw [hα, hβ]
      ring
  have hcosαsq : (Real.cos T.alpha)^2 = a.re^2 := by
    rw [hα]
    split_ifs <;> ring
  have hcosβsq : (Real.cos T.beta)^2 = b.re^2 := by
    rw [hβ]
    split_ifs <;> ring
  have haNorm : a.re^2 + a.im^2 = 1 := by
    have hh := Complex.sq_norm a
    rw [hna, one_pow, Complex.normSq_apply] at hh
    linarith only [hh]
  have hbNorm : b.re^2 + b.im^2 = 1 := by
    have hh := Complex.sq_norm b
    rw [hnb, one_pow, Complex.normSq_apply] at hh
    linarith only [hh]
  have hsinα : Real.sin T.alpha = a.im := by
    apply (sq_eq_sq₀ (Real.sin_nonneg_of_mem_Icc
      ⟨T.toDiscTriangle.alpha_mem_Ico.1, T.toDiscTriangle.alpha_mem_Ico.2.le⟩) hia).mp
    change (Real.sin T.alpha)^2 = a.im^2
    nlinarith only [Real.sin_sq_add_cos_sq T.alpha, hcosαsq, haNorm]
  have hsinβ : Real.sin T.beta = b.im := by
    apply (sq_eq_sq₀ (Real.sin_nonneg_of_mem_Icc
      ⟨T.toDiscTriangle.cycle.alpha_mem_Ico.1, T.toDiscTriangle.cycle.alpha_mem_Ico.2.le⟩) hib).mp
    change (Real.sin T.beta)^2 = b.im^2
    nlinarith only [Real.sin_sq_add_cos_sq T.beta, hcosβsq, hbNorm]
  rw [← (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hGLIsometry g).isometry.dist_eq u v]
  change Real.cosh (dist (g • u : ℍ) (g • v : ℍ)) = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cosh_dist_norm]
  have hgre : (g • u : ℍ).re = a.re := congrArg Complex.re hgu
  have hgrv : (g • v : ℍ).re = b.re := congrArg Complex.re hgv
  have hgim : (g • u : ℍ).im = a.im := congrArg Complex.im hgu
  have hgiv : (g • v : ℍ).im = b.im := congrArg Complex.im hgv
  rw [hgu, hgv, hna, hnb, hgre, hgrv, hgim, hgiv, hcosprod, hsinα, hsinβ]
  ring

/-- Actual positive rotation angles select the acute finite corners of the
physical one-ideal triangle; supplementary corners are excluded by its cosine law. -/
theorem elliptic_pair_parabolic_product_positive_triangle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B)))
    (δ ε : ℝ) (hδ : δ ∈ Ioc 0 (Real.pi / 2)) (hε : ε ∈ Ioc 0 (Real.pi / 2))
    (hangleA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * δ)
    (hangleB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * ε) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle,
      T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) ∧
      T.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)) ∧
      T.b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary ∧ T.beta = 0 ∧ T.gamma = δ ∧ T.alpha = ε ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T := by
  obtain ⟨T, ha, hc, hb, hβ, htrA, htrB, hG⟩ :=
    elliptic_pair_parabolic_product_actual_triangle A B hA hB huv hAB
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  have hκ : T.gamma ∈ Ioo 0 Real.pi := by
    have hh := (T.cycle.cycle.finiteCornerAtA u hc).proper
    have hp := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos _ _ hh
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangle_finiteCorner_angle] at hp
    exact ⟨hp, T.toDiscTriangle.cycle.cycle.alpha_mem_Ico.2⟩
  have hη : T.alpha ∈ Ioo 0 Real.pi := by
    have hh := (T.finiteCornerAtA v ha).proper
    have hp := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos _ _ hh
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangle_finiteCorner_angle] at hp
    exact ⟨hp, T.toDiscTriangle.alpha_mem_Ico.2⟩
  have hκδ : (Real.cos T.gamma)^2 = (Real.cos δ)^2 := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    rw [hangleA, show 2 * δ / 2 = δ by ring] at hh
    nlinarith only [htrA, hh]
  have hηε : (Real.cos T.alpha)^2 = (Real.cos ε)^2 := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).2.2.2
    rw [hangleB, show 2 * ε / 2 = ε by ring] at hh
    nlinarith only [htrB, hh]
  have hsδ : Real.sin T.gamma = Real.sin δ := by
    have hpos := Real.sin_pos_of_pos_of_lt_pi hκ.1 hκ.2
    have hposδ := Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith only [hδ.2, Real.pi_pos])
    nlinarith only [Real.sin_sq_add_cos_sq T.gamma, Real.sin_sq_add_cos_sq δ, hκδ, hpos, hposδ]
  have hsε : Real.sin T.alpha = Real.sin ε := by
    have hpos := Real.sin_pos_of_pos_of_lt_pi hη.1 hη.2
    have hposε := Real.sin_pos_of_pos_of_lt_pi hε.1 (by linarith only [hε.2, Real.pi_pos])
    nlinarith only [Real.sin_sq_add_cos_sq T.alpha, Real.sin_sq_add_cos_sq ε, hηε, hpos, hposε]
  have hDgeo := one_ideal_triangle_finite_side_cosh T.cycle.cycle u v hc ha hb
  change Real.cosh (dist u v) = (1 + Real.cos T.gamma * Real.cos T.alpha) /
    (Real.sin T.gamma * Real.sin T.alpha) at hDgeo
  rw [hsδ, hsε] at hDgeo
  have hDorig := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_parabolic_iff A B hA hB
    huv).mp hAB
  rw [hangleA, hangleB, show 2 * δ / 2 = δ by ring,
    show 2 * ε / 2 = ε by ring] at hDorig
  change Real.cosh (dist u v) = _ at hDorig
  have hden : Real.sin δ * Real.sin ε ≠ 0 :=
    mul_ne_zero (Real.sin_pos_of_pos_of_lt_pi hδ.1 (by linarith only [hδ.2, Real.pi_pos])).ne'
      (Real.sin_pos_of_pos_of_lt_pi hε.1 (by linarith only [hε.2, Real.pi_pos])).ne'
  have hprod : Real.cos T.gamma * Real.cos T.alpha = Real.cos δ * Real.cos ε := by
    have hh := (div_left_inj' hden).mp (hDgeo.symm.trans hDorig)
    linarith only [hh]
  have hcδ : 0 ≤ Real.cos δ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hδ.1, Real.pi_pos]) hδ.2
  have hcε : 0 ≤ Real.cos ε := Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [hε.1, Real.pi_pos]) hε.2
  have hcs := _root_.LowDimensionalTopology.Geometry.Hyperbolic.triangle_cosines_nonneg_of_product_nonneg hκ hη
    (by linarith only [T.angle_sum_lt_pi, hβ]) (hprod ▸ mul_nonneg hcδ hcε)
  have hceκ : Real.cos T.gamma = Real.cos δ := by nlinarith only [hκδ, hcs.1, hcδ]
  have hceη : Real.cos T.alpha = Real.cos ε := by nlinarith only [hηε, hcs.2, hcε]
  have hγδ : T.gamma = δ := Real.strictAntiOn_cos.injOn ⟨hκ.1.le, hκ.2.le⟩
    ⟨hδ.1.le, by linarith only [hδ.2, Real.pi_pos]⟩ hceκ
  have hαε : T.alpha = ε := Real.strictAntiOn_cos.injOn ⟨hη.1.le, hη.2.le⟩
    ⟨hε.1.le, by linarith only [hε.2, Real.pi_pos]⟩ hceη
  exact ⟨T, ha, hc, hb, hβ, hγδ, hαε, hG⟩

open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic in
/-- The genuine parabolic boundary case is itself an integral one-ideal
triangle group, with no supplied integral-triangle or discreteness conclusion. -/
theorem positive_elliptic_parabolic_product_isMobiusTriangleGroup
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hlA : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hlB : HasLeastEllipticRotation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (haA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (haB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB = 2 * Real.pi / orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    IsMobiusTriangleGroup
      (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let p := orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  let q := orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
  have hp : 2 ≤ p := least_elliptic_realSL_order_two_le A hA hlA
  have hq : 2 ≤ q := least_elliptic_realSL_order_two_le B hB hlB
  have hhalf (n : ℕ) (hn : 2 ≤ n) : Real.pi / n ∈ Ioc 0 (Real.pi / 2) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith only [hnR]
    exact ⟨div_pos Real.pi_pos hn0, div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  obtain ⟨T, _ha, _hc, _hb, hβ, hγ, hα, hG⟩ :=
    elliptic_pair_parabolic_product_positive_triangle A B hA hB huv hAB
      (Real.pi / p) (Real.pi / q) (hhalf p hp) (hhalf q hq)
      (by rw [haA]; dsimp only [p]; ring) (by rw [haB]; dsimp only [q]; ring)
  have htri : IsTriangleGroup (triangleConformalGroup T) := by
    refine ⟨(q : ℕ∞), ⊤, (p : ℕ∞), by exact_mod_cast hq, by simp,
      by exact_mod_cast hp, T, ?_, ?_, ?_, rfl⟩
    · simpa only [triangleOrderAngle_nat] using hα
    · simpa only [triangleOrderAngle_top] using hβ
    · simpa only [triangleOrderAngle_nat] using hγ
  exact native_pair_isMobiusTriangleGroup A B (triangleConformalGroup T) inf_le_right hG htri

end LowDimensionalTopology.Geometry.Fuchsian
