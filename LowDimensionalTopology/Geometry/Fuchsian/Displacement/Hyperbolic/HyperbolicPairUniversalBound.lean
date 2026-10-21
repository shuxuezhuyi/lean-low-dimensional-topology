/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.HyperbolicDisplacementProducts
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnUniversalBound
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCollarSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicFuchsianModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The scalar form of the actual Jorgensen inequality gives the quarter
product bound without a simplicity or noncrossing-family condition. -/
theorem hyperbolicPair_jorgensen_quarter_scalar (x y C : ℝ)
    (hx : 0≤x) (hxy : x≤y) (hC : 1≤C)
    (hJ : 1≤4*x^2+4*x^2*y^2*(C^2-1)) :
    1/4≤x*y*(C+1)/2 := by
  have hy : 0≤y:=hx.trans hxy
  have hp : 0≤x*y:=mul_nonneg hx hy
  have hz : 0≤x*y*C:=mul_nonneg hp (by linarith only [hC])
  have hxx : x^2≤x*y:=by nlinarith only [mul_nonneg hx (sub_nonneg.mpr hxy)]
  by_cases hb : 1/2≤x*y
  · have hm:=mul_le_mul_of_nonneg_left hC hp
    nlinarith only [hb,hm]
  · have hlow : 0≤1/2-x*y:=by linarith only [lt_of_not_ge hb]
    have hs : (1/2-x*y)^2≤(x*y*C)^2:=by
      nlinarith only [hJ,hxx]
    have hlin:1/2-x*y≤x*y*C:=(sq_le_sq₀ hlow hz).mp hs
    nlinarith only [hlin]

/-- The original half-turn extension and its newly proved universal bound
control every genuinely crossing original hyperbolic pair. -/
theorem crossing_hyperbolic_pair_universal_product
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (u : ℍ) (huA : u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB : u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨T,_hTu,_hAp,_hBp,hLA,hLB,_hle,_hindex,hdK,_hNEK⟩:=
    crossingAxis_halfturn_triangle A B hA hB htA htB u huA huB hd hNE
  have hbound:=threeHalfTurn_triangle_trace_bound T (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
    T.a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c) hdK
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T _ _ _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c)] at hbound
  have hcos : Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=by linarith only [hbound]
  have hprod : 0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2):=by
    apply mul_nonneg <;> apply Real.sinh_nonneg_iff.mpr
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)]
    · linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)]
  have hinv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T≤
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2):=by
    rw [crossingAxis_halfturn_invariant T _ _ hLA hLB]
    exact mul_le_of_le_one_right hprod (Real.sin_le_one T.alpha)
  exact hcos.trans (hinv.trans (displacementP_translation_product_lower _ _))


/-- The original projective Jorgensen defect is the true real trace defect. -/
theorem realSL_jorgensen_trace_defect (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=
      |(Matrix.trace A.val)^2-4|+|Matrix.trace (A*B*A⁻¹*B⁻¹).val-2| := by
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,realSLMobius_commutatorTrace]
  norm_cast

/-- The actual trace of a disjoint-axis commutator is determined by the
true line separation and actual half-translation lengths. -/
theorem disjoint_hyperbolic_commutator_trace
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    Matrix.trace (A*B*A⁻¹*B⁻¹).val-2=
      4*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)^2*
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)^2*
        (Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))^2-1) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB
  have hL : ∀p∈L.idealEndpoints,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have hM : ∀p∈M.idealEndpoints,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints]
    exact fun _ h=>h
  have ha:=congrArg (fun x :
    ℝ=>x^2) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisSignedSine_abs_eq_sinh_translation A hA htA)
  have hb:=congrArg (fun x :
    ℝ=>x^2) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisSignedSine_abs_eq_sinh_translation B hB htB)
  rw [sq_abs] at ha hb
  have hp : |_root_.LowDimensionalTopology.Geometry.Hyperbolic.hAxisPairing L M|=Real.cosh (L.lineDist M):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_normal_product L M).symm.trans
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_inversiveProduct_eq_cosh_lineDist L M hd)
  have hps:=congrArg (fun x : ℝ=>x^2) hp
  rw [sq_abs] at hps
  have hc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace_axis_pairing A B L M hL hM
  rw [mul_pow,mul_pow,ha,hb,hps] at hc
  linear_combination 2*hc

/-- The actual trace gap is four times the true half-length sinh squared. -/
theorem hyperbolic_real_trace_gap (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA : 4<(Matrix.trace A.val)^2) :
    (Matrix.trace A.val)^2-4=4*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)^2 := by
  have ht:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_trace A hA htA
  have hs:=Real.cosh_sq_sub_sinh_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)
  nlinarith only [ht,hs]

/-- Any actual discrete non-elementary pair with disjoint axes satisfies a
quarter product bound. This uses Jorgensen directly, with no simplicity or
noncrossing-of-all-translates hypothesis. -/
theorem disjoint_hyperbolic_pair_product_quarter
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hdis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    1/4≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let x:=Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)
  let y:=Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)
  let C:=Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
  have hx : 0≤x:=Real.sinh_nonneg_iff.mpr (by linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)])
  have hy : 0≤y:=Real.sinh_nonneg_iff.mpr (by linarith only [translationLength_nonnegative (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)])
  have hC : 1≤C:=Real.one_le_cosh _
  have hComm : 0≤4*x^2*y^2*(C^2-1):=by
    have hh : 0≤C^2-1:=by nlinarith only [hC]
    positivity
  have htrA: (Matrix.trace A.val)^2-4=4*x^2:=hyperbolic_real_trace_gap A hA htA
  have htrB: (Matrix.trace B.val)^2-4=4*y^2:=hyperbolic_real_trace_gap B hB htB
  have htrC: Matrix.trace (A*B*A⁻¹*B⁻¹).val-2=4*x^2*y^2*(C^2-1):=
    disjoint_hyperbolic_commutator_trace A B hA hB htA htB hdis
  have hJA:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hd hNE
  rw [realSL_jorgensen_trace_defect,htrA,htrC,abs_of_nonneg (by positivity),
    abs_of_nonneg hComm] at hJA
  have hJB:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
    (by simpa only [Set.pair_comm] using hd) (by simpa only [Set.pair_comm] using hNE)
  rw [realSL_jorgensen_trace_defect,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_swap,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_inverse,htrB,htrC,
    abs_of_nonneg (by positivity),abs_of_nonneg hComm] at hJB
  have hq : 1/4≤x*y*(C+1)/2:=by
    rcases le_total x y with hxy|hyx
    · exact hyperbolicPair_jorgensen_quarter_scalar x y C hx hxy hC hJA
    · have hh:=hyperbolicPair_jorgensen_quarter_scalar y x C hy hyx hC
        (by nlinarith only [hJB])
      simpa only [mul_comm y x] using hh
  exact hq.trans (hyperbolic_displacementP_lineDist_lower A B hA hB htA htB)


/-- Actual discreteness removes asymptotic axes when the two true axes have
no common point; no family-wide noncrossing premise is required. -/
theorem hyperbolic_pair_hDisjoint_of_no_common_point
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hno : ¬∃u : ℍ,u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier ∧
      u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB
  have hne : L≠M:=by
    intro he
    obtain ⟨z,_w,hz,_hw,_hne⟩:=L.exists_two_points
    have hzM : z∈M.carrier := by simpa only [←he] using hz
    exact hno ⟨z,hz,hzM⟩
  refine ⟨hne,Set.disjoint_left.mpr ?_,Set.disjoint_left.mpr ?_⟩
  · intro p hpA hpB
    exact hne (discrete_realSL_hyperbolic_axes_eq_of_shared_endpoint
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) hd A B
      (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      hA hB htA htB p hpA hpB)
  · intro u huA huB
    exact hno ⟨u,huA,huB⟩

/--
on the genuine native hyperbolic plane. Disjoint original
axes use Jorgensen directly; crossing original axes use the actual discrete
three-half-turn extension and its universal sharp trace bound.
-/
theorem hyperbolic_pair_universal_displacementP
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  by_cases hcross : ∃u : ℍ,u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier ∧
      u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier
  · obtain ⟨u,huA,huB⟩:=hcross
    exact crossing_hyperbolic_pair_universal_product A B hA hB htA htB u huA huB hd hNE
  · have hdis:=hyperbolic_pair_hDisjoint_of_no_common_point A B hA hB htA htB hd hcross
    exact cos_three_pi_div_seven_lt_quarter.le.trans
      (disjoint_hyperbolic_pair_product_quarter A B hA hB htA htB hd hNE hdis)

/--
For the unchanged original Fuchsian disc and
unchanged original hyperbolic pair. All real lifts, the actual whole-pair
subgroup, and the whole-disc metric-infimum transport are constructed.
-/
theorem hyperbolic_pair_displacement_ge_cos_three_pi_div_seven
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D
      ⟨f,Subgroup.subset_closure (by simp)⟩ ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  let H:=Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let F : H:=⟨f,Subgroup.subset_closure (by simp)⟩
  let G : H:=⟨g,Subgroup.subset_closure (by simp)⟩
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D F hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D G hg
  let q:=D.halfPlaneNormalizer
  have hgroup : D.normalizedGroup=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=by
    change (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)).map (MulAut.conj q).toMonoidHom=_
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←M.projection,←N.projection]
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact D.normalizedGroup_discrete
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact hNE.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.displacementP D F G M N]
  exact hyperbolic_pair_universal_displacementP M.matrix N.matrix M.nontrivial N.nontrivial
    M.trace_gt N.trace_gt hd hNE'

end LowDimensionalTopology.Geometry.Fuchsian
