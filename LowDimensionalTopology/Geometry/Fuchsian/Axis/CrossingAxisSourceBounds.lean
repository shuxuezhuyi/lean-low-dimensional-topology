/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CrossingAxisConstraints
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnUniversalBound
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.NonsimpleHyperbolicDisplacement
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HyperbolicReflectionPencils
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.Classification
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSignatureProfile
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import Mathlib.GroupTheory.Coset.Card
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CrossingAxisHalfTurns
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.SmallLambdaTriangleReduction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped OnePoint Pointwise ENNReal UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The true three-center angle and the smaller angle of the unchanged
original crossing axes have exactly the same sine. -/
theorem crossingAxis_halfturn_triangle_angle_sine
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (hu:T.a=u)
    (hf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
      T.b)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a))
    (hg:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
      T.c)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a)) :
    Real.sin T.alpha=Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u) := by
  have hTa:T.a∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier:=hu ▸ huA
  have hTb:T.b∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier:=
    halfturn_factorization_partner_on_axis A hA htA T.a T.b hTa
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.b,hf⟩
  have hTc:T.c∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier:=
    halfturn_factorization_partner_on_axis B hB htB T.a T.c (hu ▸ huB)
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.c,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c,hg⟩
  have hL:T.rayAB.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA:=
    T.rayAB.supportLine.eq_of_two_points _ T.a_ne_b T.rayAB.start_mem_support
      (T.rayAB.subset_support T.b_mem_rayAB) hTa hTb
  have hM:T.rayAC.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB:=
    T.rayAC.supportLine.eq_of_two_points _ T.c_ne_a.symm T.rayAC.start_mem_support
      (T.rayAC.subset_support T.c_mem_rayAC) (hu ▸ huB) hTc
  rw [←hu,←hL,←hM,←T.rayAB.acuteAngle_eq_support T.rayAC,min_def]
  split_ifs <;> simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle.alpha,Real.sin_pi_sub]

/-- The universal source cosine bound includes the actual smaller crossing
angle and the actual displacement-infimum translation lengths. -/
theorem crossing_hyperbolic_universal_length_angle_bound
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.cos (3*Real.pi/7)≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u) := by
  obtain ⟨T,hu,hf,hg,hLA,hLB,_hle,_hindex,hdK,_hNEK⟩:=
    crossingAxis_halfturn_triangle A B hA hB htA htB u huA huB hd hne
  have hb:=threeHalfTurn_triangle_trace_bound T (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c) hdK
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T _ _ _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c)] at hb
  have hcos:Real.cos (3*Real.pi/7)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=by linarith only [hb]
  rw [crossingAxis_halfturn_invariant T _ _ hLA hLB,
    crossingAxis_halfturn_triangle_angle_sine A B hA hB htA htB u huA huB T hu hf hg] at hcos
  exact hcos


/-- The universal cosine bound for every original invariant disc, using the
original actual translation lengths and the original smaller tangent angle. -/
theorem fuchsian_crossing_universal_length_angle_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier) :
    Real.cos (3*Real.pi/7)≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D
      f/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*
        Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg
  let q:=D.halfPlaneNormalizer
  let G:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hGH:G≤H:=(Subgroup.closure_le H).mpr (by
    intro s hs
    rcases hs with rfl|rfl
    · exact f.property
    · exact g.property)
  have hdG:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G D.discrete hGH
  have hmap:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.generated_pair_conjugation D f g M N
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    let originalCrossingNoEllipticDiscrete:DiscreteTopology G:=hdG
    have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) at hh
    rwa [hmap] at hh
  have hneN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have hh:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) at hh
    rwa [hmap] at hh
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f
    M,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N]
  exact crossing_hyperbolic_universal_length_angle_bound M.matrix N.matrix M.nontrivial
    N.nontrivial M.trace_gt N.trace_gt (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxf)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxg) hdN hneN

/-- Distinct actual hyperbolic axes rule out every elementary discrete pair;
the second hyperbolic map could preserve the first axis only if it were its own. -/
theorem crossing_distinct_axes_pair_nonElementary
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  apply discrete_hyperbolic_axis_moving_pair_nonElementary _ hd A B
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hA htA
  intro he
  exact hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant B hB htB _ he)


/-- The final nonsimple-element conclusion follows from the actual crossing
axes of one original element and a genuine conjugate in its original group. -/
theorem HalfPlaneFuchsianGroup.nonsimple_translation_sinh_cosine
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hns:¬IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    Real.sqrt (Real.cos (3*Real.pi/7))≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨g,hgm,hne,x,hx,hgx⟩:=(not_isSimple_iff_crossing H
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAm hAH).mp hns
  obtain ⟨F,hF⟩:=mobius_preserves_halfPlane_exists_SL g (P.preserves ⟨g,hgm⟩)
  subst g
  have hneq:((F•·:ℍ→ℍ) '' L.carrier)≠L.carrier:=by
    intro he
    apply hne
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_image_realSL,he]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_hyperbolic_axis A hA htA] at hx hgx
  obtain ⟨u,hu,rfl⟩:=hx
  have hp:F•u∈L.carrier:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL] at hgx
    obtain ⟨v,hv,he⟩:=hgx
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective he) ▸ hv
  let C:=F*A*F⁻¹
  have hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A F hA
  have htC:4<(Matrix.trace C.val)^2:=by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hCaxis:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier=((F•·:ℍ→ℍ) '' L.carrier):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A F hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hpC:F•u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier:=by rw [hCaxis];exact mem_image_of_mem _ hu
  have hCm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H:=by
    simp only [C,map_mul,map_inv]
    exact H.mul_mem (H.mul_mem hgm hAm) (H.inv_mem hgm)
  let J:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hJH:J≤H:=(Subgroup.closure_le H).mpr (by rintro a (rfl|rfl);exact hAm;exact hCm)
  have hdJ:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup J:=discreteMobius_subgroup_of_le H J P.discrete hJH
  have hneqAC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC:=by
    intro he
    exact hneq (hCaxis.symm.trans (congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier
      he.symm))
  have hNEJ:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary J:=crossing_distinct_axes_pair_nonElementary A C hA hC htA htC hdJ hneqAC
  have hb:=crossing_hyperbolic_universal_length_angle_bound A C hA hC htA htC (F•u) hp hpC hdJ hNEJ
  have hTC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A):=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation A F
  rw [hTC] at hb
  have hs:0≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2):=
    Real.sinh_nonneg_iff.mpr (by linarith only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA])
  have hSq:Real.cos (3*Real.pi/7)≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)^2:=by
    apply hb.trans
    rw [pow_two]
    exact mul_le_of_le_one_right (mul_nonneg hs hs) (Real.sin_le_one _)
  have hc0:0≤Real.cos (3*Real.pi/7):=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) hs).mp
  rw [Real.sq_sqrt hc0]
  exact hSq

/-- The nonsimple bound uses the original actual translation-length infimum
on every original invariant disc and the unchanged original group. -/
theorem fuchsian_nonsimple_translation_sinh_cosine
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) (hns:¬IsSimple H f.val) :
    Real.sqrt (Real.cos (3*Real.pi/7))≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2) := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let q:=D.halfPlaneNormalizer
  have P:HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun u=>D.normalizedGroup_preserves_halfPlane u.val u.property,D.normalizedGroup_discrete⟩
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix∈D.normalizedGroup:=by
    rw [M.projection]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hnsN:¬IsSimple D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix):=by
    intro hs
    rw [M.projection] at hs
    exact hns ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation H f.val q).mp hs)
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f M]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nonsimple_translation_sinh_cosine P M.matrix hAm M.nontrivial M.trace_gt hnsN

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance crossingCompactSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance crossingCompactSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩
/-- Actual finite index gives the genuine subgroup fundamental-domain area
without assuming subgroup finite area in advance. -/
theorem crossing_finite_index_fundamentalDomain_area {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH :
      K≤H)
    [(K.subgroupOf H).FiniteIndex]
    (D₀ : Set (unitDiscSubgroupData P K hKH).domain.carrier) (D₁ : Set P.domain.carrier)
    (hD₀ : IsFuchsianFundamentalDomain (unitDiscSubgroupData P K hKH) D₀)
    (hD₁ : IsFuchsianFundamentalDomain P D₁) :
    (unitDiscSubgroupData P K hKH).area D₀ =
      ((K.subgroupOf H).index : ℝ≥0∞)*P.area D₁ := by
  let Q:=unitDiscSubgroupData P K hKH
  let _crossingIndexRestrictedAction : MulAction K P.domain.carrier :=
    inferInstanceAs (MulAction K Q.domain.carrier)
  obtain ⟨F₀,hF₀,hDF₀,hFC₀⟩:=hD₀.exists_fundamentalSet
  obtain ⟨F₁,hF₁,hDF₁,hFC₁⟩:=hD₁.exists_fundamentalSet
  have hm₀:=hD₀.nullMeasurableSet_between hDF₀ hFC₀
  have hm₁:=hD₁.nullMeasurableSet_between hDF₁ hFC₁
  have he₀ : P.area D₀=P.area F₀:=hD₀.area_between hDF₀ hFC₀
  have he₁:=hD₁.area_between hDF₁ hFC₁
  let e : K.subgroupOf H≃*K:=Subgroup.subgroupOfEquivOfLe hKH
  let E:=orbitQuotientEquivOfMulEquiv (X:=P.domain.carrier) e (by intro g x;rfl)
  have he (x y : P.domain.carrier) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf H) P.domain.carrier x=
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (K.subgroupOf
            H) P.domain.carrier y ↔
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Q.domain.carrier y :=
    E.injective.eq_iff.symm
  have hF₀' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet (K.subgroupOf H) P.domain.carrier F₀:=by
    intro x
    obtain ⟨y,hy,hu⟩:=hF₀ x
    exact ⟨y,⟨hy.1,(he y x).mpr hy.2⟩,fun z hz=>hu z ⟨hz.1,(he z x).mp hz.2⟩⟩
  have hA:=fuchsianFundamentalSet_finite_index_area P (K.subgroupOf H) hF₀' hm₀ hF₁ hm₁
  rwa [←he₀,←he₁] at hA


/-- Finite index in a true zero-cusp cofinite group constructs an actual
zero-cusp cofinite subgroup signature, with no supplied subgroup area or signature. -/
theorem crossing_unitDisc_finite_index_zero_cusp_signature {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH :
      K≤H)
    [(K.subgroupOf H).FiniteIndex] {g : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature P.asFuchsianDisc g orders 0) :
    ∃g₀ orders₀, HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH)
      g₀ orders₀ 0 := by
  let Q:=unitDiscSubgroupData P K hKH
  let _crossingCompactCompletion : CompactSpace (FuchsianCuspCompletion P.asFuchsianDisc):=hSig.compact
  obtain ⟨w₀,hw₀,_⟩:=exists_actual_dirichlet_horocycle_good_center Q
  obtain ⟨w₁,hw₁,_⟩:=exists_actual_dirichlet_horocycle_good_center P
  let D₀:=dirichletDomain Q w₀
  let D₁:=dirichletDomain P w₁
  have hD₀:=dirichletDomain_fundamental Q w₀ hw₀
  have hD₁:=dirichletDomain_fundamental P w₁ hw₁
  have ha₁ : P.area D₁≠⊤:=compact_cuspCompletion_unitDisc_fundamental_area_ne_top P hD₁
  have hAidx:=crossing_finite_index_fundamentalDomain_area P K hKH D₀ D₁ hD₀ hD₁
  have ha₀ : Q.area D₀≠⊤:=by
    rw [hAidx]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ha₁
  obtain ⟨s,_hb,hs,_hA⟩:=finite_area_unitDisc_signature_area Q D₀ hD₀ ha₀
  have hp:s.parabolicEnds=0:=by
    by_contra hn
    have hpos:=cofinite_subgroup_signature_cusp_pos P.asFuchsianDisc K hKH hs hSig
      (by omega : 0<s.parabolicEnds)
    omega
  rw [hp] at hs
  exact ⟨s.genus,s.ellipticOrders,hs⟩

/-- The same genuine finite-index inheritance on the original entire disc,
using the actual whole-group normalizer and transporting the actual signature back. -/
theorem crossing_finite_index_zero_cusp_signature {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K≤H)
    [(K.subgroupOf H).FiniteIndex] {g : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature D g orders 0) :
    ∃g₀ orders₀, HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) g₀ orders₀ 0 := by
  let q:=geometricDiscNormalizer D
  let P:=geometricDiscData D
  let K':=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K
  have hK'H:K'≤geometricDiscGroup D:=by
    intro f hf
    obtain ⟨k,hk,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      K f).mp hf
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨k,hKH hk,rfl⟩
  have hIndex : (K'.subgroupOf (geometricDiscGroup D)).index=(K.subgroupOf H).index:=
    Subgroup.relIndex_map_map_of_injective K H (MulAut.conj q).injective
  let _crossingCompactNormalizedIndex : (K'.subgroupOf (geometricDiscGroup D)).FiniteIndex:=
    (Subgroup.finiteIndex_iff).mpr (by rw [hIndex];exact Subgroup.FiniteIndex.index_ne_zero)
  have hSig' : HasCofiniteFuchsianSignature P.asFuchsianDisc g orders 0:=by
    rw [geometricDiscData_asFuchsianDisc]
    exact cofinite_signature_global_conjugation D q g 0 orders hSig
  obtain ⟨g₀,orders₀,h₀⟩:=crossing_unitDisc_finite_index_zero_cusp_signature P K' hK'H hSig'
  refine ⟨g₀,orders₀,?_⟩
  apply cofinite_signature_of_conjugate_group
    (fuchsianDiscRestrict P.asFuchsianDisc K' hK'H) (fuchsianDiscRestrict D K hKH)
    q⁻¹ ?_ ?_ g₀ 0 orders₀ h₀
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel q K
  · change q.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=D.carrier
    rw [←geometricDiscNormalizer_image D]
    exact q.val.symm_image_image D.carrier

/-- With zero actual cusp classes the all-cusp completion is precisely the
unchanged original quotient, so the original quotient itself is compact. -/
theorem HasCofiniteFuchsianSignature.zero_cusp_quotient_compact
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {D : FuchsianDisc H} {g : ℕ} {orders
      : List ℕ}
    (hSig : HasCofiniteFuchsianSignature D g orders 0) :
    CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain) := by
  let _crossingCompactCompletion : CompactSpace (FuchsianCuspCompletion D):=hSig.compact
  let _crossingCompactParabolicFinite : Finite (FuchsianCyclicConjugacyClasses D .parabolic):=
    hSig.parabolicClassesFinite
  let _crossingCompactNoCusps : IsEmpty (FuchsianCyclicConjugacyClasses D .parabolic):=
    Finite.card_eq_zero_iff.mp hSig.cuspCount.symm
  have hs:Function.Surjective (fuchsianCuspCompletionOld D):=by
    intro x
    rcases fuchsianCuspCompletion_old_or_cusp D x with hx|⟨c,_hc⟩
    · exact hx
    · exact isEmptyElim c
  apply isCompact_univ_iff.mp
  apply (fuchsianCuspCompletionOld_isOpenEmbedding D).isEmbedding.isCompact_iff.mpr
  rw [Set.image_univ,hs.range_eq]
  exact isCompact_univ

/-- Compactness of the unchanged original quotient passes to each genuine
finite-index subgroup in the source's zero-cusp cofinite setting. -/
theorem crossing_finite_index_zero_cusp_quotient_compact {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K≤H)
    [(K.subgroupOf H).FiniteIndex] {g : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature D g orders 0) :
    CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient (fuchsianDiscRestrict D K hKH).domain) := by
  obtain ⟨g₀,orders₀,h₀⟩:=crossing_finite_index_zero_cusp_signature D K hKH hSig
  exact h₀.zero_cusp_quotient_compact

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An actual compact orbit quotient of a locally compact action has an
actual compact set meeting every orbit. The construction uses a finite open cover. -/
theorem crossing_compact_quotient_compact_orbit_cover
    {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [LocallyCompactSpace X] [ContinuousConstSMul G X]
    [CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X)] :
    ∃C:Set X,IsCompact C ∧ ∀x:X,∃g:G,g•x∈C := by
  classical
  choose C hC hCx using (fun x:X=>exists_compact_mem_nhds x)
  let U:X→Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G
    X):=fun x=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X '' interior (C x)
  have hU:∀x,IsOpen (U x):=fun x=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_isOpenMap G X _ isOpen_interior
  have hcov:(univ:Set (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient G X))⊆⋃x,U x:=by
    intro q _
    obtain ⟨x,rfl⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_surjective G X q
    exact mem_iUnion.mpr ⟨x,x,mem_interior_iff_mem_nhds.mpr (hCx x),rfl⟩
  obtain ⟨s,hs⟩:=isCompact_univ.elim_finite_subcover U hU hcov
  refine ⟨⋃x∈s,C x,s.finite_toSet.isCompact_biUnion (fun x _=>hC x),?_⟩
  intro z
  obtain ⟨x,hxs,hw⟩:=mem_iUnion₂.mp (hs (mem_univ
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X z)))
  obtain ⟨w,hw,hwe⟩:=hw
  obtain ⟨g,hg⟩:=(Quotient.exact hwe : MulAction.orbitRel G X w z)
  refine ⟨g,mem_iUnion₂.mpr ⟨x,hxs,?_⟩⟩
  change g•z=w at hg
  rw [hg]
  exact interior_subset hw

/-- A genuine locally finite fundamental domain for a compact original
quotient has compact closure: only finitely many closed tiles meet a compact orbit cover. -/
theorem IsLocallyFiniteFuchsianDomain.compact_closure_of_compact_quotient
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD:IsLocallyFiniteFuchsianDomain P D)
    [CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.domain)] : IsCompact (closure D) := by
  classical
  obtain ⟨C,hC,hcover⟩:=crossing_compact_quotient_compact_orbit_cover (G:=H) (X:=P.domain.carrier)
  let I:={g:H|(fuchsianDomainTile P D g∩C).Nonempty}
  have hI:I.Finite:=hD.compact_hits_finite C hC
  let K:=⋃g∈I,(Homeomorph.smul g).symm '' C
  have hK:IsCompact K:=hI.isCompact_biUnion (fun g _=>hC.image (Homeomorph.smul g).symm.continuous)
  apply hK.of_isClosed_subset isClosed_closure
  intro z hz
  obtain ⟨g,hg⟩:=hcover z
  have hgI:g∈I:=⟨g•z,⟨z,hz,rfl⟩,hg⟩
  exact mem_iUnion₂.mpr ⟨g,hgI,g•z,hg,(Homeomorph.smul g).symm_apply_apply z⟩

/-- A compact original quotient possesses a genuine original Dirichlet
fundamental domain bounded in the actual hyperbolic half-plane coordinate. -/
theorem crossing_compact_quotient_bounded_fundamental_domain
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
    [CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient P.domain)] :
    ∃D:Set P.domain.carrier,IsFuchsianFundamentalDomain P D ∧
      Bornology.IsBounded (P.halfPlaneCoordinate '' D) := by
  obtain ⟨w,hw,_⟩:=exists_actual_dirichlet_horocycle_good_center P
  have hD:=dirichletDomain_locallyFinite P w hw
  have hC:=hD.compact_closure_of_compact_quotient
  refine ⟨dirichletDomain P w,hD.fundamental,?_⟩
  exact ((hC.image P.halfPlaneCoordinate.continuous).isBounded).subset (image_mono subset_closure)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The unchanged actual pair group has its genuine original half-plane action. -/
theorem crossing_pair_halfPlaneData (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    HalfPlaneFuchsianGroup (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  refine {discrete:=hd,preserves:=?_}
  intro g
  have hle:Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range:=by
    rw [Subgroup.closure_le]
    rintro x (rfl|rfl)
    · exact ⟨A,rfl⟩
    · exact ⟨B,rfl⟩
  obtain ⟨q,hq⟩:=hle g.property
  rw [←hq]
  exact realSLMobius_image_openHalfPlane q

/-- A subunit actual crossing product constructs a true zero-cusp cofinite
signature of the entire original pair group, through its actual index-one-or-two extension. -/
theorem crossing_subunit_actual_pair_signature
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall:Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u)<1) :
    ∃g orders,HasCofiniteFuchsianSignature (crossing_pair_halfPlaneData A B hd).asFuchsianDisc
      g orders 0 := by
  obtain ⟨T,hu,hf,hg,hLA,hLB,hle,hindex,hdK,hNEK⟩:=
    crossingAxis_halfturn_triangle A B hA hB htA htB u huA huB hd hne
  let P:=threeHalfTurn_real_halfPlaneData (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
    T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c) hdK
  have hlam:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T<1:=by
    rw [crossingAxis_halfturn_invariant T _ _ hLA hLB,
      crossingAxis_halfturn_triangle_angle_sine A B hA hB htA htB u huA huB T hu hf hg]
    exact hsmall
  have hs:∃n orders,HasCofiniteFuchsianSignature P.asFuchsianDisc n orders 0:=by
    have hc:=(threeHalfTurn_triangle_small_parameter_classification T _ _ _ P.asFuchsianDisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c) hNEK hlam).2
    rcases hc with ⟨q,_hq,hs⟩|⟨q,_hq,hs⟩|⟨q,_hq,hs⟩
    all_goals exact ⟨0,_,hs⟩
  obtain ⟨n,orders,hs⟩:=hs
  let H:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hindex':H.relIndex K=1 ∨ H.relIndex K=2:=hindex
  let _crossingSubunitActualIndex : (H.subgroupOf K).FiniteIndex:=
    (Subgroup.finiteIndex_iff).mpr (by
      change H.relIndex K≠0
      rcases hindex' with hi|hi
      · rw [hi];decide
      · rw [hi];decide)
  obtain ⟨g,orders₀,h₀⟩:=crossing_finite_index_zero_cusp_signature P.asFuchsianDisc H hle hs
  exact ⟨g,orders₀,h₀⟩

/-- Noncompactness of the entire actual original pair quotient forces the
unit lower bound for the actual crossing product. -/
theorem crossing_noncompact_quotient_length_angle_unit_bound
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hncompact:¬CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient
      (crossing_pair_halfPlaneData A B hd).asFuchsianDisc.domain)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      A)/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
      Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u) := by
  by_contra hnot
  obtain ⟨g,orders,hs⟩:=crossing_subunit_actual_pair_signature A B hA hB htA htB u huA huB hd hne
    (lt_of_not_ge hnot)
  exact hncompact hs.zero_cusp_quotient_compact

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The unchanged original invariant disc restricted to its actual generated pair group. -/
def crossingGeneratedPairDisc {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) :
    FuchsianDisc (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) :=
  fuchsianDiscRestrict D _ ((Subgroup.closure_le H).mpr (by
    rintro a (rfl|rfl)
    · exact f.property
    · exact g.property))

/-- A subunit original crossing product constructs the actual zero-cusp
signature of the full original generated pair, on its unchanged original disc. -/
theorem fuchsian_crossing_subunit_actual_pair_signature {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (hsmall:Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x)<1) :
    ∃g₀ orders,HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) g₀ orders 0 := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg
  let q:=D.halfPlaneNormalizer
  let G:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hGH:G≤H:=(Subgroup.closure_le H).mpr (by
    intro s hs
    rcases hs with rfl|rfl
    · exact f.property
    · exact g.property)
  have hdG:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G D.discrete hGH
  have hmap:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.generated_pair_conjugation D f g M N
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    let originalCrossingNoEllipticDiscrete:DiscreteTopology G:=hdG
    have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) at hh
    rwa [hmap] at hh
  have hneN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have hh:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) at hh
    rwa [hmap] at hh
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f
    M,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N] at hsmall
  obtain ⟨g₀,orders,hs⟩:=crossing_subunit_actual_pair_signature M.matrix N.matrix M.nontrivial
    N.nontrivial M.trace_gt N.trace_gt (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxf)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxg) hdN hneN hsmall
  refine ⟨g₀,orders,?_⟩
  apply cofinite_signature_of_conjugate_group (crossing_pair_halfPlaneData M.matrix N.matrix hdN).asFuchsianDisc
    (crossingGeneratedPairDisc D f g) q⁻¹ ?_ ?_ g₀ 0 orders hs
  · rw [←hmap,_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel]
  · change q.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier
    rw [←D.halfPlaneNormalizer_image]
    exact q.val.symm_image_image D.carrier

/-- The unit bound for noncompactness of the whole unchanged original pair quotient. -/
theorem fuchsian_crossing_noncompact_quotient_length_angle_unit_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (hncompact:¬CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient
      (crossingGeneratedPairDisc D f g).domain)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  by_contra hnot
  obtain ⟨g₀,orders,hs⟩:=fuchsian_crossing_subunit_actual_pair_signature D f g hf hg hne x hxf hxg
    (lt_of_not_ge hnot)
  exact hncompact hs.zero_cusp_quotient_compact

/-- Absence of every bounded genuine original fundamental domain forces
the unit bound. Boundedness is in the actual native hyperbolic coordinate. -/
theorem fuchsian_crossing_no_bounded_domain_length_angle_unit_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (hnb:let P:=geometricDiscData (crossingGeneratedPairDisc D f g); ∀F:Set P.domain.carrier,
      IsFuchsianFundamentalDomain P F→¬Bornology.IsBounded (P.halfPlaneCoordinate '' F)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  by_contra hnot
  obtain ⟨g₀,orders,hs⟩:=fuchsian_crossing_subunit_actual_pair_signature D f g hf hg hne x hxf hxg
    (lt_of_not_ge hnot)
  let E:=crossingGeneratedPairDisc D f g
  let P:=geometricDiscData E
  have hsP:HasCofiniteFuchsianSignature P.asFuchsianDisc g₀ orders 0:=by
    rw [geometricDiscData_asFuchsianDisc]
    exact cofinite_signature_global_conjugation E (geometricDiscNormalizer E) g₀ 0 orders hs
  let _crossingOriginalPairCompact : CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient
    P.domain):=
    hsP.zero_cusp_quotient_compact
  obtain ⟨F,hF,hb⟩:=crossing_compact_quotient_bounded_fundamental_domain P
  exact hnb F hF hb

/-- The unit bound for a genuine locally finite original fundamental domain
unbounded in its actual hyperbolic coordinate. Local finiteness is explicit. -/
theorem fuchsian_crossing_unbounded_locallyFinite_domain_length_angle_unit_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (F:Set (geometricDiscData (crossingGeneratedPairDisc D f g)).domain.carrier)
    (hF:IsLocallyFiniteFuchsianDomain (geometricDiscData (crossingGeneratedPairDisc D f g)) F)
    (hnb:¬Bornology.IsBounded ((geometricDiscData (crossingGeneratedPairDisc D f g)).halfPlaneCoordinate '' F)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  by_contra hnot
  obtain ⟨g₀,orders,hs⟩:=fuchsian_crossing_subunit_actual_pair_signature D f g hf hg hne x hxf hxg
    (lt_of_not_ge hnot)
  let E:=crossingGeneratedPairDisc D f g
  let P:=geometricDiscData E
  have hsP:HasCofiniteFuchsianSignature P.asFuchsianDisc g₀ orders 0:=by
    rw [geometricDiscData_asFuchsianDisc]
    exact cofinite_signature_global_conjugation E (geometricDiscNormalizer E) g₀ 0 orders hs
  let _crossingOriginalPairCompact : CompactSpace (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient
    P.domain):=
    hsP.zero_cusp_quotient_compact
  have hC:=hF.compact_closure_of_compact_quotient
  exact hnb (((hC.image P.halfPlaneCoordinate.continuous).isBounded).subset (image_mono subset_closure))

/-- The source's unbounded-domain branch for the actual genuine Dirichlet
fundamental domain, whose required local finiteness is proved internally. -/
theorem fuchsian_crossing_unbounded_dirichlet_length_angle_unit_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (w:(geometricDiscData (crossingGeneratedPairDisc D f g)).domain.carrier)
    (hw:IsDirichletCenter (geometricDiscData (crossingGeneratedPairDisc D f g)) w)
    (hnb:¬Bornology.IsBounded ((geometricDiscData (crossingGeneratedPairDisc D f g)).halfPlaneCoordinate ''
      dirichletDomain (geometricDiscData (crossingGeneratedPairDisc D f g)) w)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  exact fuchsian_crossing_unbounded_locallyFinite_domain_length_angle_unit_bound D f g hf hg hne x hxf hxg
    _ (dirichletDomain_locallyFinite _ w hw) hnb

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Each true subgroup elliptic order divides a true ambient elliptic order,
through the original common physical fixed point and its full stabilizer. -/
theorem fuchsian_subgroup_elliptic_order_dvd {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H)
    (c : FuchsianCyclicConjugacyClasses (fuchsianDiscRestrict D K hKH) .elliptic) :
    ∃ d : FuchsianCyclicConjugacyClasses D .elliptic,
      fuchsianEllipticClassOrder (fuchsianDiscRestrict D K hKH) c ∣
        fuchsianEllipticClassOrder D d := by
  induction c using Quotient.inductionOn with
  | _ L =>
    obtain ⟨hL, f, hfL, hf⟩ := L.property
    have hfH : f ∈ H := hKH (hL.1 hfL)
    obtain ⟨p, hp, _hu⟩ := elliptic_disc_existsUnique_fixed f hf D.isDisc
      (D.image_eq ⟨f, hfH⟩)
    let M : fuchsianMaximalCyclicSubgroups H .elliptic :=
      ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val,
        elliptic_stabilizer_isMaximalCyclic D f hfH hf p hp,
        f, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH,
          hp⟩, hf⟩
    have hLM : L.val ≤ M.val := by
      intro g hg
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val g).mpr
        ⟨hKH (hL.1 hg), cyclic_elliptic_disc_fixes D L.val (hL.1.trans hKH)
          hL.2.1 f hfL hf p hp g hg⟩
    let _triangleSupergroupEllipticFinite : Finite M.val := fuchsianMaximalElliptic_finite D M
    refine ⟨Quotient.mk _ M, ?_⟩
    change Nat.card L.val ∣ Nat.card M.val
    exact Subgroup.card_dvd_of_le hLM

/-- Actual signature entries inherit divisibility from the full physical
subgroup and ambient elliptic stabilizers. -/
theorem cofinite_subgroup_signature_elliptic_order_dvd {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H)
    {g₀ p₀ g₁ p₁ : ℕ} {orders₀ orders₁ : List ℕ}
    (h₀ : HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) g₀ orders₀ p₀)
    (h₁ : HasCofiniteFuchsianSignature D g₁ orders₁ p₁) (m : ℕ) (hm : m∈orders₀) :
    ∃n∈orders₁,m∣n := by
  obtain ⟨c,hc⟩:=h₀.mem_orders.mp hm
  obtain ⟨d,hd⟩:=fuchsian_subgroup_elliptic_order_dvd D K hKH c
  exact ⟨fuchsianEllipticClassOrder D d,h₁.mem_orders.mpr ⟨d,rfl⟩,by rwa [hc] at hd⟩

/-- A true subgroup of an actual (2,3,8) signature has only the actual
elliptic orders 2,3,4,8. This is a geometric signature consumer. -/
theorem cofinite_two_three_eight_subgroup_orders {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K≤H)
    {g p : ℕ} {orders : List ℕ}
    (h₀ : HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) g orders p)
    (h₁ : HasCofiniteFuchsianSignature D 0 [2,3,8] 0) :
    ∀m∈orders,m∈([2,3,4,8] : List ℕ) := by
  intro m hm
  have hm2:=h₀.orders_two_le hm
  obtain ⟨n,hn,hd⟩:=cofinite_subgroup_signature_elliptic_order_dvd D K hKH h₀ h₁ m hm
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
  rcases hn with rfl|rfl|rfl
  · have hb:=Nat.le_of_dvd (by decide : 0<2) hd
    have he:m=2:=by omega
    simp [he]
  · have hb:=Nat.le_of_dvd (by decide : 0<3) hd
    interval_cases m <;> norm_num at *
  · have hb:=Nat.le_of_dvd (by decide : 0<8) hd
    interval_cases m <;> norm_num at *

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The actual index-two area and the actual allowed divisor orders force
exactly the three original cone orders in the current (2,3,8) consumer. -/
theorem halfTurn_index_two_eight_signature_budget (g p:ℕ) (orders:List ℕ)
    (hOrders:∀m∈orders,m=2∨m=3∨m=4∨m=8)
    (hArea:2*(g:ℝ)-2+p+(orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=1/12) :
    g=0 ∧ p=0 ∧ orders.Perm [3,3,4] := by
  have weighted (l:List ℕ) (hl:∀m∈l,m=2∨m=3∨m=4∨m=8) :
      24*(l.map (fun m:ℕ=>1-1/(m:ℝ))).sum=
        12*(l.count 2:ℝ)+16*(l.count 3:ℝ)+18*(l.count 4:ℝ)+21*(l.count 8:ℝ) := by
    induction l with
    | nil=>norm_num
    | cons m tail ih=>
      have ht:∀n∈tail,n=2∨n=3∨n=4∨n=8:=fun n hn=>hl n (List.mem_cons_of_mem m hn)
      have hs:=ih ht
      rcases hl m (by simp) with rfl|rfl|rfl|rfl
      all_goals
        norm_num [List.count_cons] at hs ⊢
        linarith only [hs]
  have hWeights:=weighted orders hOrders
  have hReal:48*(g:ℝ)+24*p+12*(orders.count 2:ℝ)+16*(orders.count 3:ℝ)+
      18*(orders.count 4:ℝ)+21*(orders.count 8:ℝ)=50:=by
    linarith only [hArea,hWeights]
  have hNat:48*g+24*p+12*orders.count 2+16*orders.count 3+
      18*orders.count 4+21*orders.count 8=50:=by
    exact_mod_cast hReal
  have hCounts:g=0 ∧ p=0 ∧ orders.count 2=0 ∧ orders.count 3=2 ∧
      orders.count 4=1 ∧ orders.count 8=0:=by omega
  obtain ⟨hg,hp,h2,h3,h4,h8⟩:=hCounts
  have hsub:orders⊆[3,4]:=by
    intro m hm
    rcases hOrders m hm with he|he|he|he
    · subst m
      exact False.elim ((List.not_mem_of_count_eq_zero h2) hm)
    · simp [he]
    · simp [he]
    · subst m
      exact False.elim ((List.not_mem_of_count_eq_zero h8) hm)
  refine ⟨hg,hp,?_⟩
  simpa using (List.perm_replicate_append_replicate (l:=orders) (a:=3) (b:=4)
    (m:=2) (n:=1) (by norm_num)).mpr ⟨h3,h4,hsub⟩


end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance crossingIndexSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance crossingIndexSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩


/-- The genuine index-two subgroup of a genuine (2,3,8) group has the full
actual (3,3,4) signature. Area, finite area and all subgroup cone orders are derived. -/
theorem crossing_two_three_eight_index_two_actual_signature {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH :
      K≤H)
    (hIndex : (K.subgroupOf H).index=2)
    (hSig : HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,3,8] 0) :
    HasCofiniteFuchsianSignature (fuchsianDiscRestrict P.asFuchsianDisc K hKH) 0 [3,3,4] 0 := by
  let Q:=unitDiscSubgroupData P K hKH
  let _crossingEightFiniteIndex : (K.subgroupOf H).FiniteIndex:=
    (Subgroup.finiteIndex_iff).mpr (by omega)
  let _crossingEightCompletion : CompactSpace (FuchsianCuspCompletion P.asFuchsianDisc):=hSig.compact
  obtain ⟨w₀,hw₀,_⟩:=exists_actual_dirichlet_horocycle_good_center Q
  obtain ⟨w₁,hw₁,_⟩:=exists_actual_dirichlet_horocycle_good_center P
  let D₀:=dirichletDomain Q w₀
  let D₁:=dirichletDomain P w₁
  have hD₀:=dirichletDomain_fundamental Q w₀ hw₀
  have hD₁:=dirichletDomain_fundamental P w₁ hw₁
  have ha₁ : P.area D₁≠⊤:=compact_cuspCompletion_unitDisc_fundamental_area_ne_top P hD₁
  have hAidx:=crossing_finite_index_fundamentalDomain_area P K hKH D₀ D₁ hD₀ hD₁
  have ha₀ : Q.area D₀≠⊤:=by
    rw [hAidx,hIndex]
    exact ENNReal.mul_ne_top (by norm_num) ha₁
  obtain ⟨s,hb,hs,hA₀⟩:=finite_area_unitDisc_signature_area Q D₀ hD₀ ha₀
  have hOrders:=cofinite_two_three_eight_subgroup_orders P.asFuchsianDisc K hKH hs hSig
  have hD₁' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain P.asFuchsianDisc).carrier
      (geometricModelArea P.asFuchsianDisc) D₁:=by
    rw [geometricModelArea_asUnitDisc]
    exact hD₁
  have ha₁' : geometricModelArea P.asFuchsianDisc D₁≠⊤:=by
    rwa [geometricModelArea_asUnitDisc]
  have hA₁:=cofinite_signature_area_of_genus_le_one P.asFuchsianDisc D₁ hD₁' ha₁'
    0 0 [2,3,8] hSig (by decide)
  rw [geometricModelArea_asUnitDisc] at hA₁
  have hR:=congrArg ENNReal.toReal hAidx
  rw [ENNReal.toReal_mul,hIndex,ENNReal.toReal_natCast] at hR
  change (Q.area D₀).toReal=2*(P.area D₁).toReal at hR
  have hDef:s.deficit=1/12:=by
    norm_num at hA₁
    have hR':=hA₀.symm.trans (hR.trans (congrArg (fun x:ℝ=>2*x) hA₁))
    have he : (2*Real.pi)*s.deficit=(2*Real.pi)*(1/12):=by
      calc
        (2*Real.pi)*s.deficit=2*(2*Real.pi*(1/24)):=hR'
        _=(2*Real.pi)*(1/12):=by ring
    exact mul_left_cancel₀ (by positivity : (2*Real.pi:ℝ)≠0) he
  have hBudget : 2*(s.genus:ℝ)-2+s.parabolicEnds+
      (s.ellipticOrders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=1/12:=by
    simpa [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit,hb] using hDef
  have hOrders' : ∀m∈s.ellipticOrders,m=2∨m=3∨m=4∨m=8:=by
    intro m hm
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using hOrders m hm
  obtain ⟨hg,hp,hPerm⟩:=halfTurn_index_two_eight_signature_budget s.genus s.parabolicEnds
    s.ellipticOrders hOrders' hBudget
  rw [hg,hp] at hs
  exact hs.perm_orders hPerm.symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- In the actual even-word extension of three involutions, an odd-order
three-factor product forces equality of the entire original pair group. -/
theorem three_involutions_pair_eq_of_odd_product_order {Γ:Type*} [Group Γ]
    (a b c:Γ) (ha:a*a=1) (hb:b*b=1) (hc:c*c=1)
    (hodd:Odd (orderOf (c*b*a))) :
    Subgroup.closure ({b*a,c*a}:Set Γ)=Subgroup.closure ({a,b,c}:Set Γ) := by
  let H:=Subgroup.closure ({b*a,c*a}:Set Γ)
  let K:=Subgroup.closure ({a,b,c}:Set Γ)
  have hab:a*b∈H:=by
    have h:=H.inv_mem (Subgroup.subset_closure (by simp:b*a∈({b*a,c*a}:Set Γ)))
    simpa only [mul_inv_rev,inv_eq_of_mul_eq_one_left ha,inv_eq_of_mul_eq_one_left hb] using h
  have hca:c*a∈H:=Subgroup.subset_closure (by simp)
  have hSquare (x:Γ) (hx:x∈K):x^2∈H:=by
    rcases three_involutions_pair_cosets a b c ha hb hc x hx with he|ho
    · exact H.pow_mem he 2
    · have hxa:=three_involutions_pair_conjugation a b c ha hb hc (a*x) ho
      have hp:=H.mul_mem hxa ho
      have he:a*(a*x)*a*(a*x)=x^2:=by simp only [mul_assoc,←mul_assoc a a,ha,one_mul,pow_two]
      exact he ▸ hp
  let w:=c*b*a
  have hw:w∈K:=K.mul_mem (K.mul_mem (Subgroup.subset_closure (by simp))
    (Subgroup.subset_closure (by simp))) (Subgroup.subset_closure (by simp))
  obtain ⟨n,hn⟩:=hodd
  have hwp:w^(orderOf w+1)=w:=by rw [pow_add,pow_orderOf_eq_one,pow_one,one_mul]
  have hwm:w∈H:=by
    have he:2*(n+1)=orderOf w+1:=by dsimp only [w];omega
    have hh:=H.pow_mem (hSquare w hw) (n+1)
    rw [←pow_mul,he,hwp] at hh
    exact hh
  have hwa:w*a∈H:=by
    have he:w*a=(c*a)*(a*b):=by dsimp [w];simp only [mul_assoc,←mul_assoc a a,ha,one_mul,mul_one]
    exact he ▸ H.mul_mem hca hab
  have ham:a∈H:=by
    have hh:=H.mul_mem (H.inv_mem hwm) hwa
    simpa only [mul_assoc,inv_mul_cancel_left] using hh
  apply le_antisymm (three_involutions_pair_relIndex a b c ha hb hc).1
  apply (Subgroup.closure_le _).mpr
  intro x hx
  simp only [mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with he|he|he
  · exact he.symm ▸ ham
  · have hh:=H.mul_mem (Subgroup.subset_closure (by simp:b*a∈({b*a,c*a}:Set Γ))) ham
    have hbm:b∈H:=by simpa only [mul_assoc,ha,mul_one] using hh
    exact he.symm ▸ hbm
  · have hh:=H.mul_mem hca ham
    have hcm:c∈H:=by simpa only [mul_assoc,ha,mul_one] using hh
    exact he.symm ▸ hcm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual numerator-three cover area forces its actual degree and final cone order. -/
theorem crossing_three_numerator_area_forces_degree_three (q n N:ℕ)
    (hq:7≤q) (hqn:q≤n) (hN:3≤N)
    (hArea:2*(N:ℝ)*(1/6-1/(n:ℝ))=1-6/(q:ℝ)) : N=3 ∧ n=q := by
  have hq0:0<(q:ℝ):=by exact_mod_cast (show 0<q by omega)
  have hn0:0<(n:ℝ):=by exact_mod_cast (show 0<n by omega)
  have hqnR:(q:ℝ)≤n:=by exact_mod_cast hqn
  have hN3:(3:ℝ)≤N:=by exact_mod_cast hN
  have hn6:(6:ℝ)<n:=by exact_mod_cast (show 6<n by omega)
  have hd:0<1/6-1/(n:ℝ):=by
    have hh:1/(n:ℝ)<1/6:=(one_div_lt_one_div_of_lt (by norm_num : (0:ℝ)<6) hn6)
    linarith
  have hr:1/(n:ℝ)≤1/(q:ℝ):=one_div_le_one_div_of_le hq0 hqnR
  have hr':(n:ℝ)⁻¹≤(q:ℝ)⁻¹:=by simpa only [one_div] using hr
  have hArea':2*(N:ℝ)*(1/6-(n:ℝ)⁻¹)=1-6*(q:ℝ)⁻¹:=by
    simpa only [div_eq_mul_inv,one_mul] using hArea
  have hd':0<1/6-(n:ℝ)⁻¹:=by simpa only [one_div] using hd
  have hNle:(N:ℝ)≤3:=by
    have hh:2*(N:ℝ)*(1/6-(n:ℝ)⁻¹)≤6*(1/6-(n:ℝ)⁻¹):=by
      nlinarith only [hArea',hr']
    have hcoef:2*(N:ℝ)≤6:=le_of_mul_le_mul_right hh hd'
    linarith only [hcoef]
  have hNe:N=3:=by exact_mod_cast (le_antisymm hNle hN3)
  have hrEq:(n:ℝ)⁻¹=(q:ℝ)⁻¹:=by rw [hNe] at hArea';norm_num at hArea';nlinarith only [hArea']
  have hnq:(n:ℝ)=(q:ℝ):=inv_injective hrEq
  exact ⟨hNe,by exact_mod_cast hnq⟩

/-- A subhalf actual cosine forces the actual reduced rotation denominator
strictly below three times its actual numerator. -/
theorem crossing_subhalf_reduced_denominator (lam:ℝ) (hl0:0≤lam) (hl:lam<1/2)
    (p q:ℕ) (hp:0<p) (hpq:2*p<q)
    (hθ:Real.arccos lam=Real.pi*p/q) : q<3*p := by
  have hq0:0<(q:ℝ):=by exact_mod_cast (show 0<q by omega)
  have hArc:Real.pi/3<Real.arccos lam:=by
    have hh:=Real.arccos_lt_arccos (by linarith : -1≤lam) hl (by norm_num : (1/2:ℝ)≤1)
    rw [←Real.cos_pi_div_three,Real.arccos_cos (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at hh
    exact hh
  rw [hθ] at hArc
  have hi:Real.pi/3*(q:ℝ)<Real.pi*p:=(lt_div_iff₀ hq0).mp hArc
  have hreal:(q:ℝ)<3*p:=by nlinarith only [hi,Real.pi_pos]
  exact_mod_cast hreal

theorem crossing_halfTurnCanonical_subhalf_signature
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall:halfTurnQuadKleinB (t^2) (t^2/w.re)/Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-(halfTurnQuadKleinA
      (t^2) (t^2/w.re))^2)<1/2) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          F,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W}:Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    let P:=nativeConformalSubgroup_halfPlaneData H hConf
    (Odd (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F*G*W))) ∧
      ((∃n:ℕ,7≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,3,n] 0) ∨
       (∃n:ℕ,5≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,4,n] 0))) ∨
    (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (F*G*W))=8 ∧
      HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,3,8] 0) := by
  have hu0:=zero_lt_one.trans_le hu
  have ht:=hu.trans_lt hut
  have hb:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2:ℕ)≠0)) hc
  obtain ⟨p,q,hq,hp,hpq,_hcop,hθ⟩:=halfTurnCanonical_reduced u t hu0 ht w hw hn hc hd
  have hq3p:=crossing_subhalf_reduced_denominator _ hb.1.le hsmall p q hp hpq hθ
  have hp2:2≤p:=by omega
  obtain ⟨orders,hs,hlen,N,n,_hN,hDegree,hnmem,hdiv,hArea⟩:=
    halfTurnCanonical_nonprimitive_signature u t hu hut w hw hn hc hd p q hp2 hpq hq hθ
  have hn2:=hs.orders_two_le hnmem
  have hqn:q≤n:=Nat.le_of_dvd (by omega) hdiv
  have hClass:=halfTurn_nonprimitive_order_list_classification orders
    (fun _ hm=>hs.orders_two_le hm) hlen p q N n hp2 hpq hDegree hnmem hqn hArea
  rcases hClass with ⟨hp2,hPerm,hn7⟩|⟨hp3,hPerm,hn7⟩|⟨hp2,hPerm,hn5⟩
  · have hq5:q=5:=by omega
    exact Or.inl ⟨by rw [←hq,hq5];decide,Or.inl ⟨n,hn7,hs.perm_orders hPerm.symm⟩⟩
  · have hq78:q=7 ∨ q=8:=by omega
    have hA:2*(N:ℝ)*(1/6-1/(n:ℝ))=1-6/(q:ℝ):=by
      have he: (orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=
          (([2,3,n]:List ℕ).map (fun m:ℕ=>1-1/(m:ℝ))).sum:=
        (hPerm.map (fun m:ℕ=>1-1/(m:ℝ))).sum_eq
      rw [he,hp3] at hArea
      norm_num at hArea
      convert hArea using 1
      ring
    have hN3:3≤N:=by omega
    have hq7:7≤q:=by omega
    obtain ⟨_hN3,hnq⟩:=crossing_three_numerator_area_forces_degree_three q n N hq7 hqn hN3 hA
    rcases hq78 with hq7|hq8
    · exact Or.inl ⟨by rw [←hq,hq7];decide,Or.inl ⟨n,hn7,hs.perm_orders hPerm.symm⟩⟩
    · have hP:orders.Perm [2,3,8]:=by simpa only [hnq,hq8] using hPerm
      exact Or.inr ⟨by rw [←hq,hq8],hs.perm_orders hP.symm⟩
  · have hq5:q=5:=by omega
    exact Or.inl ⟨by rw [←hq,hq5];decide,Or.inr ⟨n,hn5,hs.perm_orders hPerm.symm⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- Equality of the actual whole groups preserves their original half-plane signature. -/
theorem crossing_halfPlane_signature_of_group_eq {H K:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (Q:HalfPlaneFuchsianGroup K) (hKH:K=H)
    {g p:ℕ} {orders:List ℕ} (hs:HasCofiniteFuchsianSignature P.asFuchsianDisc g orders p) :
    HasCofiniteFuchsianSignature Q.asFuchsianDisc g orders p := by
  subst K
  exact hs

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual subhalf triple has an odd product and one of the two source
triangle signatures, or the genuine product order eight and full (2,3,8) signature. -/
theorem crossing_subhalf_triple_signature_order (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (A B C:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A
      T.a) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B
      T.b) (hC:_root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T<1/2) :
    let D:=(threeHalfTurn_real_halfPlaneData A B C hd).asFuchsianDisc
    (Odd (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)) ∧
      ((∃n:ℕ,7≤n ∧ HasCofiniteFuchsianSignature D 0 [2,3,n] 0) ∨
       (∃n:ℕ,5≤n ∧ HasCofiniteFuchsianSignature D 0 [2,4,n] 0))) ∨
    (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=8 ∧
      HasCofiniteFuchsianSignature D 0 [2,3,8] 0) := by
  let D:=(threeHalfTurn_real_halfPlaneData A B C hd).asFuchsianDisc
  obtain ⟨r,u,t,hu,ht,w,hu1,hut,hw,hn,hG,hdisc,htrace,hord⟩:=
    halfTurn_actual_halfperiod_group_model T A B C hA hB hC hd
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  have htrT:|Matrix.trace (A*B*C).val|=2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC
  have hsmall':|Matrix.trace (U*V*W).val|<2:=by
    rw [htrace,htrT]
    linarith only [hsmall]
  change |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans
      ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|<2 at hsmall'
  rw [axisHalfTurns_point_triple_trace] at hsmall'
  have hratio:(u*t)/u-u/(u*t)=t-1/t:=by field_simp
  rw [hratio] at hsmall'
  have hscalar:=halfTurn_small_trace_compact_scalar t w.re w.im ht hw w.im_pos hn
    ((le_abs_self _).trans_lt hsmall')
  have hc:t^2+1<2*(t^2/w.re):=by
    have hh:t^2+1<(2*t^2)/w.re:=(lt_div_iff₀ hw).mpr hscalar
    simpa only [mul_div_assoc] using hh
  let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/Real.sqrt
    ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-(halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
  have hb:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2:ℕ)≠0)) hc
  have htr:|Matrix.trace (U*V*W).val|=2*lam:=by
    rw [halfTurnCanonical_trace u t hu ht w hw hn,abs_of_pos (mul_pos (by norm_num) hb.1)]
  have hlam:lam=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T:=by rw [htrace,htrT] at htr;linarith only [htr]
  have hhalf:lam<1/2:=by rwa [hlam]
  have hClass:=crossing_halfTurnCanonical_subhalf_signature u t hu1 hut w hw hn hc hdisc hhalf
  rcases hClass with ⟨hodd,hs⟩|⟨h8,hs⟩
  · refine Or.inl ⟨?_,?_⟩
    · have ho:Odd (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C))):=by rw [←hord];exact hodd
      simpa only [map_mul] using ho
    · rcases hs with ⟨n,hn7,hs⟩|⟨n,hn5,hs⟩
      · exact Or.inl ⟨n,hn7,threeHalfTurn_original_signature_of_native D U V W hdisc
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r) hG (realSLMobius_image_openHalfPlane
            r) 0 0 [2,3,n] hs⟩
      · exact Or.inr ⟨n,hn5,threeHalfTurn_original_signature_of_native D U V W hdisc
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r) hG (realSLMobius_image_openHalfPlane
            r) 0 0 [2,4,n] hs⟩
  · refine Or.inr ⟨?_,threeHalfTurn_original_signature_of_native D U V W hdisc
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r) hG (realSLMobius_image_openHalfPlane
        r) 0 0 [2,3,8] hs⟩
    have ho:orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C))=8:=by rw [←hord];exact h8
    simpa only [map_mul] using ho

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- A subhalf actual crossing product forces one of the complete actual
source exceptions for the original whole pair group. -/
theorem crossing_subhalf_actual_pair_signature
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall:Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u)<1/2) :
    let D:=(crossing_pair_halfPlaneData A B hd).asFuchsianDisc
    (∃n:ℕ,7≤n ∧ HasCofiniteFuchsianSignature D 0 [2,3,n] 0) ∨
    (∃n:ℕ,5≤n ∧ HasCofiniteFuchsianSignature D 0 [2,4,n] 0) ∨
      HasCofiniteFuchsianSignature D 0 [3,3,4] 0 := by
  obtain ⟨T,hu,hf,hg,hLA,hLB,hle,hindex,hdK,_hNEK⟩:=
    crossingAxis_halfturn_triangle A B hA hB htA htB u huA huB hd hne
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.a)
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b)
  let c:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c)
  let H:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let K:=Subgroup.closure ({a,b,c}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let P:=threeHalfTurn_real_halfPlaneData (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
    T.a) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.b)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL T.c) hdK
  let Q:=crossing_pair_halfPlaneData A B hd
  have hlam:_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T<1/2:=by
    rw [crossingAxis_halfturn_invariant T _ _ hLA hLB,
      crossingAxis_halfturn_triangle_angle_sine A B hA hB htA htB u huA huB T hu hf hg]
    exact hsmall
  have ha:a*a=1:=by
    have hh:=pow_orderOf_eq_one a
    have ho:orderOf a=2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.a).1
    rwa [ho,pow_two] at hh
  have hb:b*b=1:=by
    have hh:=pow_orderOf_eq_one b
    have ho:orderOf b=2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.b).1
    rwa [ho,pow_two] at hh
  have hc:c*c=1:=by
    have hh:=pow_orderOf_eq_one c
    have ho:orderOf c=2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c).1
    rwa [ho,pow_two] at hh
  have hClass:=crossing_subhalf_triple_signature_order T _ _ _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.a)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
      T.b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c) hdK hlam
  rcases hClass with ⟨hodd,hs⟩|⟨_h8,hs⟩
  · have hi:c*b*a=(a*b*c)⁻¹:=by
      simp only [mul_inv_rev,inv_eq_of_mul_eq_one_left ha,inv_eq_of_mul_eq_one_left hb,
        inv_eq_of_mul_eq_one_left hc,mul_assoc]
    have ho:Odd (orderOf (c*b*a)):=by rw [hi,orderOf_inv];exact hodd
    have hHK:H=K:=by
      have he:=three_involutions_pair_eq_of_odd_product_order a b c ha hb hc ho
      simpa only [a,b,c,←hf,←hg] using he
    rcases hs with ⟨n,hn,hs⟩|⟨n,hn,hs⟩
    · exact Or.inl ⟨n,hn,crossing_halfPlane_signature_of_group_eq P Q hHK hs⟩
    · exact Or.inr (Or.inl ⟨n,hn,crossing_halfPlane_signature_of_group_eq P Q hHK hs⟩)
  · rcases hindex with h1|h2
    · have hHK:H=K:=le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
      exact Or.inl ⟨8,by decide,crossing_halfPlane_signature_of_group_eq P Q hHK hs⟩
    · let J:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
      have hJP:J≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K:=Subgroup.map_mono hle
      have hJidx:(J.subgroupOf (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius K)).index=2:=by
        have he:=Subgroup.relIndex_map_map_of_injective (f:=(MulAut.conj
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).toMonoidHom) H K (MulAut.conj
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).injective
        exact he.trans h2
      have hsP:HasCofiniteFuchsianSignature P.cayleyData.asFuchsianDisc 0 [2,3,8] 0:=
        cofinite_signature_of_conjugate_group P.asFuchsianDisc P.cayleyData.asFuchsianDisc _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
          rfl cayleyMobius_image_openHalfPlane 0 0 [2,3,8] hs
      have hsJ:=crossing_two_three_eight_index_two_actual_signature P.cayleyData J hJP hJidx hsP
      right
      right
      apply cofinite_signature_of_conjugate_group
        (fuchsianDiscRestrict P.cayleyData.asFuchsianDisc J
          hJP) Q.asFuchsianDisc _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H) ?_ 0 0 [3,3,4] hsJ
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      rw [←cayleyMobius_image_openHalfPlane]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_image_image _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- A subhalf actual original crossing product forces the complete actual
source signature exception list for the unchanged whole original pair group. -/
theorem fuchsian_crossing_subhalf_actual_pair_signatures {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
    (hsmall:Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x)<1/2) :
    (∃n:ℕ,7≤n ∧ HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [2,3,n] 0) ∨
    (∃n:ℕ,5≤n ∧ HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [2,4,n] 0) ∨
      HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [3,3,4] 0 := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg
  let q:=D.halfPlaneNormalizer
  let G:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hGH:G≤H:=(Subgroup.closure_le H).mpr (by
    intro s hs
    rcases hs with rfl|rfl
    · exact f.property
    · exact g.property)
  have hdG:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G D.discrete hGH
  have hmap:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.generated_pair_conjugation D f g M N
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    let originalCrossingNoEllipticDiscrete:DiscreteTopology G:=hdG
    have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) at hh
    rwa [hmap] at hh
  have hneN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have hh:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) at hh
    rwa [hmap] at hh
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f
    M,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N] at hsmall
  have hTransfer {orders:List ℕ}
      (hs:HasCofiniteFuchsianSignature (crossing_pair_halfPlaneData M.matrix N.matrix hdN).asFuchsianDisc
        0 orders 0) : HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 orders 0:=by
    apply cofinite_signature_of_conjugate_group (crossing_pair_halfPlaneData M.matrix N.matrix hdN).asFuchsianDisc
      (crossingGeneratedPairDisc D f g) q⁻¹ ?_ ?_ 0 0 orders hs
    · rw [←hmap,_root_.LowDimensionalTopology.Geometry.Hyperbolic.subgroupConjugate_inv_cancel]
    · change q.val.symm '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=D.carrier
      rw [←D.halfPlaneNormalizer_image]
      exact q.val.symm_image_image D.carrier
  have hs:=crossing_subhalf_actual_pair_signature M.matrix N.matrix M.nontrivial N.nontrivial
    M.trace_gt N.trace_gt (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxf)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxg) hdN hneN hsmall
  rcases hs with ⟨n,hn,hs⟩|⟨n,hn,hs⟩|hs
  · exact Or.inl ⟨n,hn,hTransfer hs⟩
  · exact Or.inr (Or.inl ⟨n,hn,hTransfer hs⟩)
  · exact Or.inr (Or.inr (hTransfer hs))

/--
The original crossing product has the half lower bound,
except possibly for the three genuine actual whole-pair signature families.
-/
theorem fuchsian_crossing_half_length_angle_bound_or_actual_signatures {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier)
 :
    (1/2≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*Real.sinh
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*Real.sin
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x)) ∨
    (∃n:ℕ,7≤n ∧ HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [2,3,n] 0) ∨
    (∃n:ℕ,5≤n ∧ HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [2,4,n] 0) ∨
      HasCofiniteFuchsianSignature (crossingGeneratedPairDisc D f g) 0 [3,3,4] 0 := by
  by_cases hb:1/2≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D
    f/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D
    g/2)*Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x)
  · exact Or.inl hb
  · exact Or.inr (fuchsian_crossing_subhalf_actual_pair_signatures D f g hf hg hne x hxf hxg
      (lt_of_not_ge hb))

end LowDimensionalTopology.Geometry.Fuchsian
