/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleParabolicDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.OneParabolicHeckeModels
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleSharpness
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

/-- The actual trace-six gap gives the half-product bound for every
real parabolic/nonelliptic pair through its constructed real normalizer. -/
theorem parabolic_displacementP_half_of_trace_six (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (htB:4≤(Matrix.trace B.val)^2)
    (htrace:6≤Matrix.trace (A*B*A⁻¹*B⁻¹).val) :
    1/2≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
  obtain ⟨q,t,_ht,hnorm⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  have hT:6≤2+(t*(q*B*q⁻¹) 1 0)^2:=by
    rw [parabolic_normalization_commutator_trace A B q t hnorm,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_commutator_trace] at htrace
    exact htrace
  have hc:2≤|t*(q*B*q⁻¹) 1 0|:=by
    nlinarith [sq_abs (t*(q*B*q⁻¹) 1 0),abs_nonneg (t*(q*B*q⁻¹) 1 0)]
  have hprod:1/2≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=by
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
    1/2≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=hprod
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*A*q⁻¹)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (q*B*q⁻¹)):=by rw [hnormI]
    _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B):=by
      rw [hSLIsometry_conjugation A q,hSLIsometry_conjugation B
        q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_conjugation]


/-- The improved half-product bound for the actual original invariant
disc and whole nontriangle parabolic/hyperbolic pair. The trace-six
gap is derived from genuine whole Hecke classification. -/
theorem fuchsian_nontriangle_parabolic_hyperbolic_displacementP (f
  g:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D:FuchsianDisc (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      f) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt:¬IsMobiusTriangleGroup (Subgroup.closure ({f,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/2≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D
      ⟨f,Subgroup.subset_closure (by simp)⟩ ⟨g,Subgroup.subset_closure (by simp)⟩ := by
  let F:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨f,Subgroup.subset_closure (by simp)⟩
  let G:Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=⟨g,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let q:=D.halfPlaneNormalizer
  have hfN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp hf
  have hgN:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B):=by
    rw [D.normalizedLift_spec]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward g q hg
  have hcomm:_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f g=((Matrix.trace (A*B*A⁻¹*B⁻¹).val:ℝ):ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f g q,
      ←D.normalizedLift_spec F,←D.normalizedLift_spec G,realSLMobius_commutatorTrace]
  have h6:6≤Matrix.trace (A*B*A⁻¹*B⁻¹).val:=by
    have hh:=fuchsian_one_parabolic_nontriangle_trace_ge_six f g D hf hne hnt
    rw [hcomm] at hh
    simpa only [Complex.ofReal_re] using hh
  change 1/2≤_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP D F G
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementP_eq_native]
  exact parabolic_displacementP_half_of_trace_six A B hfN
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff B hgN.1.1).mp hgN).le h6


/-- The improved parabolic constant is sharp for literal original
generated pairs, with all genuine type, discreteness, non-elementary
and nontriangle hypotheses proved for the same entire group. -/
theorem nontriangle_parabolic_generated_pair_sharpness (ε:ℝ) (hε:0<ε) :
    ∃c:ℝ, _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      ¬IsMobiusTriangleGroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (schottkyParabolicSL c)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      1<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (schottkyParabolicSL c))<1+ε := by
  obtain ⟨c,hc,hNT,hNE,hlo,hhi⟩:=nontriangle_parabolic_sharpness ε hε
  exact ⟨c,quarterTranslation_parabolic,schottkyParabolicSL_parabolic c (by linarith only [hc]),
    schottkyParabolicGroup_discrete c hc,hNE,hNT,hlo,hhi⟩

/-- The improved half constant is sharp for literal original
parabolic/hyperbolic generated pairs; the actual product-generator
replacement is included through the proved whole-group equality. -/
theorem nontriangle_parabolic_hyperbolic_generated_pair_sharpness (ε:ℝ) (hε:0<ε) :
    ∃v:ℝ,∃hv:0<v,
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      ¬IsMobiusTriangleGroup (Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
              1),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)}:Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      1/2<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv))<1/2+ε := by
  obtain ⟨v,hv,hvu,hNT,hNE,hHyp,hlo,hhi⟩:=nontriangle_parabolic_hyperbolic_sharpness ε hε
  refine ⟨v,hv,quarterTranslation_parabolic,hHyp,?_,?_,?_,hlo,hhi⟩
  all_goals rw [halfTurnSchottkyProductSL_pair_group]
  · exact halfTurnSchottkyGroup_discrete v hv hvu
  · exact hNE
  · exact hNT

end LowDimensionalTopology.Geometry.Fuchsian
