/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.EllipticReflectionPencils
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleTypeGeometry
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The joining line of two genuine elliptic centers gives three genuine reflection
factors, with opposite positions of the common factor. -/
theorem elliptic_pair_common_reflection_factors
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) :
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    ∃ L M N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine, u ∈ L.carrier ∧ v ∈ L.carrier ∧
      u ∈ M.carrier ∧ v ∈ N.carrier ∧ L ≠ M ∧ L ≠ N ∧
      (A • · : ℍ → ℍ) = M.reflection ∘ L.reflection ∧
      (B • · : ℍ → ℍ) = L.reflection ∘ N.reflection := by
  obtain ⟨L, huL, hvL⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_halfPlaneLine_through _ _ huv
  obtain ⟨M, ⟨huM, hAeq⟩,
    _⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_elliptic_reflection_factor A hA L huL
  obtain ⟨N, ⟨hvN, hBeq⟩,
    _⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_elliptic_reflection_factor_right B hB L hvL
  refine ⟨L, M, N, huL, hvL, huM, hvN,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_elliptic_reflection_factors_ne A hA L M hAeq, ?_, hAeq, hBeq⟩
  intro he
  have hN := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_elliptic_reflection_factors_ne B hB N L hBeq
  exact hN he.symm

/-- An elliptic product of the specified actual reflections forces the original
geodesics to intersect in the native half-plane. -/
theorem elliptic_reflection_product_intersection
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C))
    (M N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (he : ∀ z : ℍ, C • z = M.reflection
      (N.reflection z)) :
    ∃ w : ℍ, w ∈ M.carrier ∧ w ∈ N.carrier := by
  have hne : M ≠ N := by
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_elliptic_reflection_factors_ne C hC N M (funext
      he)
    exact hh.symm
  have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflection_product_abs_trace M N C he
  have hsmall : _root_.LowDimensionalTopology.Geometry.Inversive.inversiveProduct M.extendedCircle.realModel N.extendedCircle.realModel < 1 := by
    rw [ht]
    have htrace := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC
    have habs := abs_nonneg (Matrix.trace C.val)
    nlinarith only [htrace, habs, sq_abs (Matrix.trace C.val)]
  rcases M.classification N hne with hp | hi | hd
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_one_of_parallel M N
    hp] at hsmall
    exact False.elim (lt_irrefl _ hsmall)
  · exact hi.2.2
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cosh_lineDist M N hd] at hsmall
    exact False.elim (not_lt_of_ge (Real.one_le_cosh _) hsmall)

theorem native_ray_reflection_product_trace_square
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) {w : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt w)
    (he : ∀ x : ℍ, A • x = R.supportLine.reflection (S.supportLine.reflection x)) :
    (Matrix.trace A.val)^2 = 4 * (Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S))^2 := by
  have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflection_product_abs_trace R.supportLine S.supportLine A he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product] at ht
  change |_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisPairing R.supportLine S.supportLine| = |Matrix.trace A.val| / 2 at ht
  have hsq := congrArg (fun x : ℝ => x^2) ht
  simp only [sq_abs, div_pow] at hsq
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisPairing_sq_eq_cos_angle R S] at hsq
  nlinarith only [hsq]


theorem elliptic_pair_actual_triangle_center_angles
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,
      T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ∧
      T.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
      T.b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (A *
        B) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (A * B) hAB.1).mp hAB) ∧
      (Matrix.trace A.val)^2 = 4 * (Real.cos T.gamma)^2 ∧
      (Matrix.trace B.val)^2 = 4 * (Real.cos T.alpha)^2 ∧
      (Matrix.trace (A * B).val)^2 = 4 * (Real.cos T.beta)^2 ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  obtain ⟨L, M, N, huL, hvL, huM, hvN, hLM, hLN, hAeq, hBeq⟩ :=
    elliptic_pair_common_reflection_factors A B hA hB huv
  have hprod (z : ℍ) : (A * B) • z = M.reflection (N.reflection z) := by
    rw [mul_smul, congrFun hAeq, congrFun hBeq, Function.comp_apply, Function.comp_apply,
      L.reflection_involutive]
  obtain ⟨w, hwM, hwN⟩ := elliptic_reflection_product_intersection (A * B) hAB M N hprod
  have hwu : w ≠ u := by
    intro hwu
    have huN : u ∈ N.carrier := by rwa [← hwu]
    have hNL := N.eq_of_two_points L huv huN hvN huL hvL
    exact hLN hNL.symm
  have hwv : w ≠ v := by
    intro hwv
    have hvM : v ∈ M.carrier := by rwa [← hwv]
    have hML := M.eq_of_two_points L huv huM hvM huL hvL
    exact hLM hML.symm
  let T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle := ⟨v, w, u, by
    rintro ⟨K, hvK, hwK, huK⟩
    have hKL := K.eq_of_two_points L huv huK hvK huL hvL
    have hwL : w ∈ L.carrier := hKL ▸ hwK
    exact hLM (L.eq_of_two_points M hwu.symm huL hwL huM hwM)⟩
  have hTA : T.toClosedHTriangle.sideLineA = M := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideA]
    exact T.sideLineA.eq_of_two_points M T.b_ne_c T.rayBC.start_mem_support
      (T.rayBC.subset_support T.c_mem_rayBC) hwM huM
  have hTB : T.toClosedHTriangle.sideLineB = L := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideB]
    exact T.sideLineB.eq_of_two_points L T.c_ne_a T.rayCA.start_mem_support
      (T.rayCA.subset_support T.a_mem_rayCA) huL hvL
  have hTC : T.toClosedHTriangle.sideLineC = N := by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideC]
    exact T.sideLineC.eq_of_two_points N T.a_ne_b T.rayAB.start_mem_support
      (T.rayAB.subset_support T.b_mem_rayAB) hvN hwN
  have hAI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry M *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := IsometryEquiv.ext (congrFun
        hAeq)
  have hBI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N := IsometryEquiv.ext (congrFun
        hBeq)
  have hBinv : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    B)⁻¹ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry N *
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L := by
    rw [hBI, mul_inv_rev]
    exact congrArg₂ (· * ·) (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_inv N)
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneLineReflectionIsometry_inv L)
  have hbCenter : T.b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter (A * B)
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (A * B) hAB.1).mp hAB) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff (A * B) _ w).mp
    rw [hprod, (N.reflection_fixed_iff w).mpr hwN, (M.reflection_fixed_iff w).mpr hwM]
  have htrA : (Matrix.trace A.val)^2 = 4 * (Real.cos T.gamma)^2 := by
    have hh := native_ray_reflection_product_trace_square A T.rayCB T.rayCA (by
      intro z
      rw [T.support_CB_eq, show T.rayCA.supportLine = T.sideLineB from rfl]
      rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideA T, ←
        _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideB T,
        hTA, hTB]
      exact congrFun hAeq z)
    have hang : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayCB T.rayCA = T.gamma := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    rwa [hang] at hh
  have htrB : (Matrix.trace B.val)^2 = 4 * (Real.cos T.alpha)^2 := by
    have hh := native_ray_reflection_product_trace_square B T.rayAC T.rayAB (by
      intro z
      rw [T.support_AC_eq, show T.rayAB.supportLine = T.sideLineC from rfl]
      rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideB T, ←
        _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideC T,
        hTB, hTC]
      exact congrFun hBeq z)
    have hang : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayAC T.rayAB = T.alpha := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    rwa [hang] at hh
  have htrAB : (Matrix.trace (A * B).val)^2 = 4 * (Real.cos T.beta)^2 := by
    have hh := native_ray_reflection_product_trace_square (A * B) T.rayBC T.rayBA (by
      intro z
      rw [show T.rayBC.supportLine = T.sideLineA from rfl, T.support_BA_eq]
      rw [← _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideA T, ←
        _root_.LowDimensionalTopology.Geometry.Fuchsian.finite_closedTriangle_sideC T,
        hTA, hTC]
      exact hprod z)
    have hang : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayBC T.rayBA = T.beta := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm _ _
    rwa [hang] at hh
  refine ⟨T, rfl, rfl, hbCenter, htrA, htrB, htrAB, ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup_eq_pairProductGroup]
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


theorem elliptic_pair_elliptic_product_actual_triangle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,
      T.a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ∧
      T.c = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle := by
  obtain ⟨T, ha, hc, _hb, _htA, _htB, _htAB, hG⟩ :=
    elliptic_pair_actual_triangle_center_angles A B hA hB huv hAB
  exact ⟨T, ha, hc, hG⟩

/-- The literal non-elementary generated pair needs no separate assumption on the
centers to construct its genuine geometric triangle when its product is elliptic. -/
theorem nonElementary_elliptic_pair_elliptic_product_actual_triangle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle := by
  have huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) := by
    intro he
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    apply hNE
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ u).mpr he]
  obtain ⟨T, _ha, _hc, hG⟩ := elliptic_pair_elliptic_product_actual_triangle A B hA hB huv hAB
  exact ⟨T, hG⟩

/-- Original Mobius discreteness transfers to the very same finite triangle model,
including its native subgroup topology. The missing reciprocal-angle classification
is deliberately not part of this conclusion. -/
theorem discrete_elliptic_pair_elliptic_product_actual_triangle
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    ∃ T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle,
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) =
        _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle ∧
      DiscreteTopology (_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle) := by
  obtain ⟨T, hG⟩ := nonElementary_elliptic_pair_elliptic_product_actual_triangle A B hA hB hNE hAB
  let H := _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T.toClosedHTriangle
  let J := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let F := _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom H inf_le_right
  have hGH : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ)) = H := hG
  have hm : ∀ f (hf : f ∈ Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B} : Set (ℍ ≃ᵢ ℍ))), F ⟨f, hGH ▸ hf⟩ ∈ J := by
    intro f hf
    induction hf using Subgroup.closure_induction with
    | mem f hf =>
      rcases hf with rfl | rfl
      · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
      · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom_matrix]
        exact Subgroup.subset_closure (by simp)
    | one =>
      change F 1 ∈ J
      rw [map_one]
      exact J.one_mem
    | mul x y hx hy ihx ihy =>
      have he : (⟨x * y, _⟩ : H) = (⟨x, hGH ▸ hx⟩ : H) * ⟨y, hGH ▸ hy⟩ := rfl
      rw [he, map_mul]
      exact J.mul_mem ihx ihy
    | inv x hx ih =>
      have he : (⟨x⁻¹, _⟩ : H) = (⟨x, hGH ▸ hx⟩ : H)⁻¹ := rfl
      rw [he, map_inv]
      exact J.inv_mem ih
  refine ⟨T, hG, _root_.LowDimensionalTopology.Geometry.Fuchsian.native_conformal_subgroup_discrete_of_image H
    inf_le_right J hd ?_⟩
  intro f
  exact hm f.val (hGH.symm ▸ f.property)

end LowDimensionalTopology.Geometry.Fuchsian
