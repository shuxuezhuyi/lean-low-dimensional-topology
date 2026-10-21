/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicTraceBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.NonTriangleParabolicGroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual trace-eighteen constraint gives the actual unit product
bound for any real parabolic/nonelliptic pair. Every normalizer and
pointwise bound is constructed, not supplied. -/
theorem parabolic_displacementP_of_commutator_trace (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (htB:4≤(Matrix.trace B.val)^2)
    (htrace:18≤Matrix.trace (A*B*A⁻¹*B⁻¹).val) :
    1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,_ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hT:18≤2+(t*(q*B*q⁻¹) 1 0)^2:=by
    rw [parabolic_normalization_commutator_trace A B q t hnorm,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace] at htrace
    exact htrace
  have hc:4≤|t*(q*B*q⁻¹) 1 0|:=by
    nlinarith [sq_abs (t*(q*B*q⁻¹) 1 0),abs_nonneg (t*(q*B*q⁻¹) 1 0)]
  have hprod:1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
    intro z
    have hp:=translation_displacement_product_lower t (q*B*q⁻¹)
      (by rwa [realSL_trace_conjugation]) z
    linarith only [hc,hp]
  have hnormI:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t):=by
    rcases hnorm with he|he
    · rw [he]
    · rw [he]
      apply IsometryEquiv.ext
      intro z
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_neg_smul _ z
  calc
    1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=hprod
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=by rw [hnormI]
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=by
      rw [hSLIsometry_conjugation A q,hSLIsometry_conjugation B
        q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_conjugation]

/-- The nontriangle parabolic-pair unit product bound holds for the
actual original group, original geometric disc, and infimum over every
original point. Neither a trace gap nor a normal form is assumed. -/
theorem fuchsian_nontriangle_parabolic_displacementP (f
  g:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt:¬IsMobiusTriangleGroup (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D
      ⟨f,Subgroup.subset_closure (by simp)⟩ ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  let F:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨f,Subgroup.subset_closure (by simp)⟩
  let G:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨g,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let q:=D.halfPlaneNormalizer
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hgN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hg
  have hcomm:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f g q,
      ←D.normalizedLift_spec F,←D.normalizedLift_spec G,realSLMobius_commutatorTrace]
  have h18:18≤Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    have hh:=fuchsian_two_parabolic_nontriangle_trace_ge_eighteen f g D hf hg hne hnt
    rw [hcomm] at hh
    simpa only [Complex.ofReal_re] using hh
  change 1≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D F G
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP_eq_native]
  apply parabolic_displacementP_of_commutator_trace A B hfN _ h18
  exact le_of_eq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hgN.1).mp hgN).symm

end LowDimensionalTopology.Geometry.Fuchsian
