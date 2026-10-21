/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.HyperbolicMaximumDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicProducts
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

/-- A genuine parabolic element has this maximum-displacement bound with every
non-elementary partner; both the elliptic and nonelliptic partner cases are proved. -/
theorem HalfPlaneFuchsianGroup.parabolic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  let K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH:K≤H:=(Subgroup.closure_le H).mpr (by rintro f (rfl|rfl);exact hAm;exact hBm)
  have hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup K:=discreteMobius_subgroup_of_le H K P.discrete hKH
  by_cases ht:(Matrix.trace B.val)^2<4
  · have hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1:=by
      apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_left_ne_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      simpa only [Set.pair_comm] using hne
    exact parabolic_elliptic_displacementM_sqrt_eighth A B hA ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB).mpr ht) hd hne
  · have hp:=parabolic_displacementP_quarter A B hA (le_of_not_gt ht) hd hne
    have hm:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le_M_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)
    apply (sq_le_sq₀ (show 0≤1/Real.sqrt 8 by positivity) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mp
    have he:(1/Real.sqrt (8:ℝ))^2=(1:ℝ)/8:=by norm_num [div_pow,Real.sq_sqrt]
    rw [he]
    linarith only [hp,hm]

/-- Every actual nonelliptic member has this bound with any genuine
non-elementary partner in the original half-plane Fuchsian group. -/
theorem HalfPlaneFuchsianGroup.nonelliptic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P:HalfPlaneFuchsianGroup H)
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  rcases hA with hp|hh
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.parabolic_displacementM_eighth P A B hAm hBm hp hne
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.hyperbolic_displacementM_eighth P A B hAm hBm hh hne

/-- The complete actual original-disc nonelliptic branch of the universal
maximum-displacement argument, with no type assumption on the partner. -/
theorem fuchsian_nonelliptic_displacementM_eighth
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/Real.sqrt 8≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g := by
  let A:=D.normalizedLift f
  let B:=D.normalizedLift g
  let q:=D.halfPlaneNormalizer
  have P:HalfPlaneFuchsianGroup D.normalizedGroup:=
    ⟨fun u=>D.normalizedGroup_preserves_halfPlane u.val u.property,D.normalizedGroup_discrete⟩
  have hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    rcases hf with hp|hh
    · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp
      hp)
    · exact Or.inr ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation f.val q).mpr hh)
  have hAm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hBm:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈D.normalizedGroup:=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,rfl⟩
  have hPair:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D f g]
    exact hne.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nonelliptic_displacementM_eighth P A B hAm hBm hA hPair

/-- The exact source universal constant is below the stronger nonelliptic bound. -/
theorem universal_displacement_constant_le_sqrt_eighth :
    Real.sqrt ((4*(Real.cos (Real.pi/7))^2-3)/(8*Real.cos (Real.pi/7)+7))≤1/Real.sqrt 8 := by
  let c:=Real.cos (Real.pi/7)
  have hc:0≤c:=(Real.cos_pos_of_mem_Ioo
    ⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩).le
  have hc1:c≤1:=Real.cos_le_one _
  have hd:0<8*c+7:=by positivity
  have hh:(4*c^2-3)/(8*c+7)≤(1:ℝ)/8:=by
    apply (div_le_iff₀ hd).mpr
    have hcc:=mul_nonneg hc (sub_nonneg.mpr hc1)
    nlinarith only [hcc,hc1]
  have hs:=Real.sqrt_le_sqrt hh
  rwa [Real.sqrt_div (by norm_num:(0:ℝ)≤1),Real.sqrt_one] at hs

/-- The exact universal source bound for the actual original-disc infimum is
fully proved whenever one specified member is nonelliptic. -/
theorem fuchsian_universal_displacement_bound_of_nonelliptic
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    Real.sqrt ((4*(Real.cos (Real.pi/7))^2-3)/(8*Real.cos (Real.pi/7)+7))≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g :=
  universal_displacement_constant_le_sqrt_eighth.trans
    (fuchsian_nonelliptic_displacementM_eighth D f g hf hne)

/-- The exact universal bound for every original pair except the remaining
two-elliptic case. Classification and the required symmetry are proved internally. -/
theorem fuchsian_universal_displacement_bound_of_not_two_elliptic
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc H) (f g:H)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnot:¬(_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)) :
    Real.sqrt ((4*(Real.cos (Real.pi/7))^2-3)/(8*Real.cos (Real.pi/7)+7))≤
      _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g := by
  have hclass (a b:H)
      (hN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({a.val,b.val}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
      (ha:¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic a.val) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic a.val ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic a.val:=by
    rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy a.val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_left_ne_one a.val b.val hN) with hp|hl|he
    · exact Or.inl hp
    · exact Or.inr ⟨hl,D.carrier,D.isDisc,D.image_eq a⟩
    · exact False.elim (ha he)
  by_cases hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val
  · have hg:¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val:=fun hg=>hnot ⟨hf,hg⟩
    have hN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({g.val,f.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
      simpa only [Set.pair_comm] using hne
    have hh:=fuchsian_universal_displacement_bound_of_nonelliptic D g f (hclass g f hN hg) hN
    have hcomm:_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D g f=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D f g:=by
      rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_comm]
    rwa [hcomm] at hh
  · exact fuchsian_universal_displacement_bound_of_nonelliptic D f g (hclass f g hne hf) hne

end LowDimensionalTopology.Geometry.Fuchsian
