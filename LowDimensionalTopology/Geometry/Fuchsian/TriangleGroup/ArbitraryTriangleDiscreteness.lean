/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticParabolicTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.NontriangleCanonicalRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.NonTriangleParabolicGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSignatureCharacterization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
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

/-- An actual parabolic and a product elliptic cannot share the common
boundary fixed point that elementarity would force. -/
theorem HalfPlaneFuchsianGroup.parabolic_elliptic_product_nonElementary
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H)
    (hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B))) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H := by
  intro hE
  obtain ⟨p,_hp,hall⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint H hE _ hAH hA
  have hpA := hall ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAH⟩
  have hABH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B) ∈ H := by rw [map_mul];exact H.mul_mem hAH hBH
  have hpAB := hall ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B),hABH⟩
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier _ hAB _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
    (P.preserves ⟨_,hABH⟩) hpAB)
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_fixed_mem_disc_frontier _ hA _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
      (P.preserves ⟨_,hAH⟩) hpA)

/-- The two genuine parabolic generators and an elliptic product have
commutator trace strictly below the exceptional-model threshold. -/
theorem two_parabolic_elliptic_product_commutator_lt_eighteen
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B))) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val < 18 := by
  have ha := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff A hA.1).mp hA
  have hb := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hB.1).mp hB
  have ht := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff (A*B) hAB.1).mp hAB
  have hp : (Matrix.trace A.val*Matrix.trace B.val)^2 = 16 := by
    rw [mul_pow,ha,hb]
    norm_num
  have hh : (Matrix.trace A.val*Matrix.trace B.val*Matrix.trace (A*B).val)^2 < 64 := by
    rw [mul_pow,hp]
    nlinarith only [ht]
  have hl : -(8:ℝ) < Matrix.trace A.val*Matrix.trace B.val*Matrix.trace (A*B).val := by
    nlinarith only [hh]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace,ha,hb]
  linarith only [ht,hl]

/-- The actual small-trace classification applies to the entire original
pair, with discreteness and its invariant half-plane supplied by the original group. -/
theorem HalfPlaneFuchsianGroup.two_parabolic_elliptic_product_isTriangle
    {H : Subgroup Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)))
    (hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)=H) :
    IsMobiusTriangleGroup H := by
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)) := by
    rw [hgen]
    exact P.discrete
  let Q := realSL_pair_halfPlaneData A B hd
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H := hgen ▸ Subgroup.subset_closure (by simp)
  have hNE := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.parabolic_elliptic_product_nonElementary P A B hAH hBH hA hAB
  have hs : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)).re < 18 := by
    rw [realSLMobius_commutatorTrace,Complex.ofReal_re]
    exact two_parabolic_elliptic_product_commutator_lt_eighteen A B hA hB hAB
  have ht := fuchsian_two_parabolic_small_trace_triangle _ _ Q.asFuchsianDisc hA hB
    (by rwa [hgen]) hs
  rwa [hgen] at ht

/-- The actual joining reflections cancel at the common side. -/
theorem triangle_adjacent_reflection_product (L M N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L M*_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL M N)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL L N) := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action
  intro z
  rw [mul_smul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,M.reflection_involutive]

/-- The faithful Mobius image is generated by the two actual consecutive
products; reversing the second stated generator does not change the group. -/
theorem triangle_mobius_group_adjacent_generators
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC)} : Set Mobius.complexMobiusGroup)=
      closedTriangleMobiusGroup T := by
  let A := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  let B := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC)=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)⁻¹ := by
    rw [←map_inv]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_ext_action
    intro z
    apply (MulAction.injective B)
    change B • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC • z)=B • (B⁻¹ • z)
    rw [smul_inv_smul]
    dsimp only [B]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,
      T.sideLineB.reflection_involutive,T.sideLineC.reflection_involutive]
  have hgen : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B}:Set (ℍ≃ᵢℍ))=
      triangleConformalGroup T := by
    rw [triangleConformalGroup_eq_pairProductGroup]
    simp only [A,B,trianglePairProductGroup,reflectionProductSL_native]
  rw [he,closure_pair_inverse_right]
  exact (native_pair_mobius_range_eq_closure A B _ inf_le_right hgen).symm

/-- Every original nonideal closed-model point is an actual native point. -/
theorem closedHalfPlanePoint_exists_native_of_not_ideal
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHalfPlaneModel)
    (hp : p.val ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) : ∃z:ℍ,p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel z := by
  have ho : p.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    have hh := (Set.ext_iff.mp _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedHalfPlaneSet_eq_open_union_boundary p.val).mp p.property
    exact hh.resolve_right hp
  obtain ⟨z,hz,he⟩ := ho
  exact ⟨⟨z,hz⟩,Subtype.ext he.symm⟩

/-- With two genuine finite vertices, the arbitrary triangle is classified
using its actual generators, not a supplied reciprocal-angle condition. -/
theorem discrete_triangle_two_finite_corners_isTriangle
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T))
    (ha:T.a.val ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hc:T.c.val ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) :
    IsMobiusTriangleGroup (closedTriangleMobiusGroup T) := by
  let : DiscreteTopology (triangleConformalGroup T) := hd
  let P := nativeConformalSubgroup_halfPlaneData (triangleConformalGroup T) inf_le_right
  let A := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  let B := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC
  have hcA : T.c∈T.sideLineA.closedCarrier :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineA
  have hcB : T.c∈T.sideLineB.closedCarrier :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineB
  have haB : T.a∈T.sideLineB.closedCarrier :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineB
  have haC : T.a∈T.sideLineC.closedCarrier :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineC
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) :=
    reflectionProductSL_common_finite_elliptic _ _ (triangle_sideLineAB_distinct T) T.c hc hcA hcB
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) :=
    reflectionProductSL_common_finite_elliptic _ _ (triangle_sideLineCB_distinct T).symm T.a ha haB haC
  obtain ⟨u,hu⟩ := closedHalfPlanePoint_exists_native_of_not_ideal T.c hc
  obtain ⟨v,hv⟩ := closedHalfPlanePoint_exists_native_of_not_ideal T.a ha
  have huf : A • u=u := by
    rw [hu] at hcA hcB
    have huA := (T.sideLineA.closedCarrier_mem_interior_iff u).mp hcA
    have huB := (T.sideLineB.closedCarrier_mem_interior_iff u).mp hcB
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,(T.sideLineB.reflection_fixed_iff u).mpr huB,
      (T.sideLineA.reflection_fixed_iff u).mpr huA]
  have hvf : B • v=v := by
    rw [hv] at haB haC
    have hvB := (T.sideLineB.closedCarrier_mem_interior_iff v).mp haB
    have hvC := (T.sideLineC.closedCarrier_mem_interior_iff v).mp haC
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action,(T.sideLineC.reflection_fixed_iff v).mpr hvC,
      (T.sideLineB.reflection_fixed_iff v).mpr hvB]
  have huv : u≠v := by
    intro he
    have hac : T.a=T.c := hv.trans ((congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToClosedModel he).symm.trans hu.symm)
    exact T.noncollinear ⟨T.sideLineA,hac ▸ hcA,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.b).mp T.toDiscTriangle.b_mem_sideLineA,hcA⟩
  have hcent : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) := by
    rw [←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mp huf,
      ←(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ v).mp hvf]
    exact huv
  have hgen := triangle_mobius_group_adjacent_generators T
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈closedTriangleMobiusGroup T := hgen ▸ Subgroup.subset_closure (by simp [A])
  have hBH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈closedTriangleMobiusGroup T := hgen ▸ Subgroup.subset_closure (by simp [B])
  have hprod : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)) ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)) := by
    rw [triangle_adjacent_reflection_product]
    apply reflectionProductSL_common_closed_vertex_type _ _ (triangle_sideLineCB_distinct T.cycle) T.b
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.b).mp T.toDiscTriangle.b_mem_sideLineA
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.b).mp T.toDiscTriangle.b_mem_sideLineC
  rcases hprod with hprod | hprod
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_forces_triangle P A B hA hB hAH hBH hprod hcent
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_parabolic_product_forces_triangle P A B hA hB hAH hBH hprod hcent

/-- The one-finite-corner case has two actual parabolic generators and
an actual elliptic product, so the proved small-trace whole-group models apply. -/
theorem discrete_triangle_two_ideal_corners_isTriangle
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T))
    (ha:T.a.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hc:T.c.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary)
    (hb:T.b.val ∉ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary) :
    IsMobiusTriangleGroup (closedTriangleMobiusGroup T) := by
  let : DiscreteTopology (triangleConformalGroup T) := hd
  let P := nativeConformalSubgroup_halfPlaneData (triangleConformalGroup T) inf_le_right
  let A := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB
  let B := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    apply reflectionProductSL_common_ideal_parabolic _ _ (triangle_sideLineAB_distinct T) T.c hc
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineA
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineB
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    apply reflectionProductSL_common_ideal_parabolic _ _ (triangle_sideLineCB_distinct T).symm T.a ha
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineB
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineC
  have hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)) := by
    rw [triangle_adjacent_reflection_product]
    apply reflectionProductSL_common_finite_elliptic _ _ (triangle_sideLineCB_distinct T.cycle) T.b hb
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.b).mp T.toDiscTriangle.b_mem_sideLineA
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.b).mp T.toDiscTriangle.b_mem_sideLineC
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.two_parabolic_elliptic_product_isTriangle P A B hA hB hAB
    (triangle_mobius_group_adjacent_generators T)

theorem closedTriangleMobiusGroup_cycle (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    closedTriangleMobiusGroup T.cycle=closedTriangleMobiusGroup T := by
  let F : {K:Subgroup (ℍ≃ᵢℍ) // K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup}→
      Subgroup Mobius.complexMobiusGroup := fun K=>(nativeConformalSubgroupMobiusHom K.val K.property).range
  have he : (⟨triangleConformalGroup T.cycle,inf_le_right⟩:
      {K:Subgroup (ℍ≃ᵢℍ) // K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup})=
      ⟨triangleConformalGroup T,inf_le_right⟩ :=
    Subtype.ext (triangleConformalGroup_cycle T)
  exact congrArg F he

/-- The actual finite and ideal cases exhaust every original closed
hyperbolic triangle, and force its entire discrete conformal group to be a triangle group. -/
theorem discrete_arbitrary_triangle_isMobiusTriangleGroup
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd:DiscreteTopology (triangleConformalGroup T)) :
    IsMobiusTriangleGroup (closedTriangleMobiusGroup T) := by
  have hdc : DiscreteTopology (triangleConformalGroup T.cycle) := by
    rwa [triangleConformalGroup_cycle]
  have hdcc : DiscreteTopology (triangleConformalGroup T.cycle.cycle) := by
    rwa [triangleConformalGroup_cycle]
  by_cases ha:T.a.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
  · by_cases hc:T.c.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    · by_cases hb:T.b.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
      · exact closedTriangleMobiusGroup_isMobiusTriangleGroup T
          (Or.inl (T.toDiscTriangle.alpha_of_ideal ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.a).mpr ha)))
          (Or.inl (T.toDiscTriangle.beta_of_ideal ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.b).mpr hb)))
          (Or.inl (T.toDiscTriangle.gamma_of_ideal ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr hc)))
      · exact discrete_triangle_two_ideal_corners_isTriangle T hd ha hc hb
    · by_cases hb:T.b.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
      · have h:=discrete_triangle_two_ideal_corners_isTriangle T.cycle hdc hb ha hc
        rwa [closedTriangleMobiusGroup_cycle] at h
      · have h:=discrete_triangle_two_finite_corners_isTriangle T.cycle.cycle hdcc hc hb
        rwa [closedTriangleMobiusGroup_cycle,closedTriangleMobiusGroup_cycle] at h
  · by_cases hc:T.c.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
    · by_cases hb:T.b.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary
      · have h:=discrete_triangle_two_ideal_corners_isTriangle T.cycle.cycle hdcc hc hb ha
        rwa [closedTriangleMobiusGroup_cycle,closedTriangleMobiusGroup_cycle] at h
      · have h:=discrete_triangle_two_finite_corners_isTriangle T.cycle hdc hb ha
        rwa [closedTriangleMobiusGroup_cycle] at h
    · exact discrete_triangle_two_finite_corners_isTriangle T hd ha hc

/-- The genuine Mobius triangle-group predicate implies discreteness,
by its literal integral-triangle model and actual conjugation. -/
theorem mobiusTriangleGroup_discrete {H:Subgroup Mobius.complexMobiusGroup}
    (ht:IsMobiusTriangleGroup H) : DiscreteTopology H := by
  obtain ⟨K,hK,⟨p,q,r,hT⟩,s,hs⟩:=ht
  let : DiscreteTopology K:=hT.discrete
  have hr:DiscreteTopology (nativeConformalSubgroupMobiusHom K hK).range :=
    native_conformal_subgroup_image_discrete K hK
  let : DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s H):=by rwa [hs]
  have hi:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete s⁻¹ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s H)
  change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s⁻¹ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s H)) at hi
  rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel] at hi

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/--
on the faithful original Mobius image of every actual
finite/ideal triangle, without prescribed rational or reciprocal angles.
-/
theorem triangleConformalGroup_discrete_iff_isMobiusTriangleGroup
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    DiscreteTopology (triangleConformalGroup T) ↔
      IsMobiusTriangleGroup (closedTriangleMobiusGroup T) := by
  constructor
  · exact discrete_arbitrary_triangle_isMobiusTriangleGroup T
  · intro ht
    let : DiscreteTopology (closedTriangleMobiusGroup T):=mobiusTriangleGroup_discrete ht
    have hm:Isometry (closedTriangleMobiusEquiv T) := Isometry.of_dist_eq (fun _ _=>rfl)
    exact hm.isEmbedding.discreteTopology

end LowDimensionalTopology.Geometry.Fuchsian
