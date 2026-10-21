module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped OnePoint Pointwise UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual primitiveness forces the entire endpoint-pair subgroup to be cyclic or a genuine two-coset half-turn extension. -/
theorem primitive_pair_stabilizer_normal_forms (H K : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hp : IsPrimitive H f) (hf0 : f.val (0:ℂ) =
      (0:ℂ))
    (hKH : K ≤ H) (hpair : K ≤ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer) (hfK
      : f ∈ K) :
    K = Subgroup.zpowers f ∨
      ∃ s : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, s ∈ K ∧ s.val (0:ℂ) = ∞ ∧ s.val ∞ = (0:ℂ) ∧
        s^2 = 1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic s ∧
        ∀ g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, g ∈ K ↔ ∃ n : ℤ, g = f^n ∨ g = f^n*s := by
  have hgen := hp.generates (0:ℂ) hf0
  have hpowK : Subgroup.zpowers f ≤ K := Subgroup.zpowers_le.mpr hfK
  have hfixed {g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (hg : g ∈ K) (hg0 : g.val (0:ℂ) =
    (0:ℂ)) :
      g ∈ Subgroup.zpowers f := by
    rw [hgen,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer]
    exact ⟨hKH hg,hg0⟩
  by_cases hKpow : K ≤ Subgroup.zpowers f
  · exact Or.inl (le_antisymm hKpow hpowK)
  · right
    obtain ⟨s,hsK,hsout⟩ := Set.not_subset.mp hKpow
    have hswap : s.val (0:ℂ) = ∞ ∧ s.val ∞ = (0:ℂ) := by
      rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨s,hpair
        hsK⟩ with hfix | hswap
      · exact (hsout (hfixed hsK hfix.1)).elim
      · exact hswap
    have hs2 : s^2 = 1 := by simpa only [pow_two] using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square s hswap.1 hswap.2
    have hsn : s ≠ 1 := by
      intro he
      have hh := hswap.1
      rw [he] at hh
      exact OnePoint.coe_ne_infty (0:ℂ) hh
    refine ⟨s,hsK,hswap.1,hswap.2,hs2,_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic s hsn
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2,by decide,hs2⟩),fun g => ?_⟩
    constructor
    · intro hg
      rcases _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_zeroInftyPair_cases ⟨g,hpair
        hg⟩ with hfix | hswapG
      · obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp (hfixed hg hfix.1)
        exact ⟨n,Or.inl hn.symm⟩
      · have hgs0 : (g*s).val (0:ℂ) = (0:ℂ) := by
          change g.val (s.val (0:ℂ)) = (0:ℂ)
          rw [hswap.1,hswapG.2]
        obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp (hfixed (K.mul_mem hg hsK) hgs0)
        refine ⟨n,Or.inr ?_⟩
        rw [hn,mul_assoc,←pow_two,hs2,mul_one]
    · rintro ⟨n,rfl | rfl⟩
      · exact K.zpow_mem hfK n
      · exact K.mul_mem (K.zpow_mem hfK n) hsK

/-- Every actual logarithmic dilation preserves the entire actual imaginary axis. -/
theorem stableAxisDilation_image_axis (l : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
  have hstep (t : ℝ) : (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation
    l).val (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph t).val =
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph (t+l)).val := by
    simpa only [zpow_one,Int.cast_one,one_mul] using _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation_zpow_param l t 1
  apply Subset.antisymm
  · rintro _ ⟨x,hx,rfl⟩
    obtain ⟨t,ht⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph.surjective ⟨x,hx⟩
    have ht' : (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph
      t).val=x := congrArg Subtype.val ht
    rw [←ht',hstep]
    exact (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph (t+l)).property
  · intro x hx
    obtain ⟨t,ht⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph.surjective ⟨x,hx⟩
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph
      (t-l)).val,(_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisParamHomeomorph _).property,?_⟩
    rw [hstep,sub_add_cancel]
    exact congrArg Subtype.val ht

/-- The original full axis stabilizer of a primitive normalized dilation keeps both cyclic and half-turn branches. -/
theorem HalfPlaneFuchsianGroup.primitive_dilation_axis_stabilizer {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) ∨
      ∃ s : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, s ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis ∧
        s.val (0:ℂ) = ∞ ∧ s.val ∞ = (0:ℂ) ∧ s^2 = 1 ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic s ∧
        ∀ g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, g ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis ↔
          ∃ n : ℤ, g = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*s := by
  apply primitive_pair_stabilizer_normal_forms H _ _ hp
  · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero _
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer_le H _
  · intro g hg
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxis_mobius_endpoints_preserved g (P.preserves
      ⟨g,hg.1⟩) hg.2
  · exact ⟨hp.mem,stableAxisDilation_image_axis l⟩

/-- Every actual axis-reversing element has a genuine positive-height half-turn center. -/
theorem imaginaryAxis_exchange_halfturn (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (haxis : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : f.val (0:ℂ) = ∞ ∧ f.val ∞ = (0:ℂ)) :
    ∃ r : ℝ, ∃ hr : 0 < r, f = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL r hr) := by
  have hz : (f*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal).val (0:ℂ) = (0:ℂ) := by
    change f.val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val (0:ℂ)) = (0:ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_zero,hswap.2]
  have hi : (f*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal).val ∞ = ∞ := by
    change f.val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val ∞) = ∞
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty,hswap.1]
  obtain ⟨a,ha⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_fix_zero_infty_eq_scaling _ hz hi
  have heF : f = _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal := by
    rw [←ha,mul_assoc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mul_self,mul_one]
  have hI : ((Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := by
    refine ⟨0,?_⟩
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe]
  have hFI : f.val ((Complex.I:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := haxis ▸ mem_image_of_mem _ hI
  obtain ⟨t,ht⟩ := hFI
  rw [heF,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul_reciprocal_coe a Complex.I
    Complex.I_ne_zero] at ht
  have ht' : (Real.exp t:ℂ)*Complex.I = (a:ℂ)/Complex.I := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint,_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_coe] using OnePoint.coe_injective ht
  have hac : (a:ℂ) = -(Real.exp t:ℂ) := by
    have hh := congrArg (fun z : ℂ => z*Complex.I) ht'
    rw [div_mul_cancel₀ _ Complex.I_ne_zero,mul_assoc,Complex.I_mul_I,mul_neg_one] at hh
    exact hh.symm
  let r := Real.sqrt (Real.exp t)
  have hr : 0 < r := Real.sqrt_pos.mpr (Real.exp_pos t)
  have har : (a:ℂ) = -(r:ℂ)^2 := by
    rw [hac]
    congr 1
    exact_mod_cast (Real.sq_sqrt (Real.exp_pos t).le).symm
  refine ⟨r,hr,?_⟩
  apply mobius_ext_on_halfPlane
  intro z
  rw [heF,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul_reciprocal_coe a z z.ne_zero,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe,har]

/-- The original subgroup action and its half-turn formula agree at every native point. -/
theorem HalfPlaneFuchsianGroup.axis_exchange_coe {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : H)
    (haxis : g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : g.val.val (0:ℂ) = ∞ ∧ g.val.val ∞ = (0:ℂ)) :
    letI := P.nativeAction
    ∃ r : ℝ, ∃ _hr : 0 < r, ∀ z : ℍ, ((g • z : ℍ):ℂ) = -(r:ℂ)^2/(z:ℂ) := by
  let nativeExchangeFormulaAction := P.nativeAction
  obtain ⟨r,hr,he⟩ := imaginaryAxis_exchange_halfturn g.val haxis hswap
  exact ⟨r,hr,fun z => by rw [P.nativeAction_realSL g _ he.symm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe]⟩

/-- Axis reversal exchanges the two actual sides of the axis; it is never discarded by a no-elliptic assumption. -/
theorem HalfPlaneFuchsianGroup.axis_exchange_re_sign {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : H)
    (haxis : g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : g.val.val (0:ℂ) = ∞ ∧ g.val.val ∞ = (0:ℂ)) (z : ℍ) :
    letI := P.nativeAction
    0 < (g • z).re ↔ z.re < 0 := by
  let nativeExchangeSignAction := P.nativeAction
  obtain ⟨r,hr,he⟩ := P.axis_exchange_coe g haxis hswap
  have hre : (g • z).re = -r^2*z.re/Complex.normSq (z:ℂ) := by
    change (((g • z : ℍ):ℂ).re) = _
    rw [he,←Complex.ofReal_pow,←Complex.ofReal_neg,Complex.div_re]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,zero_div,add_zero,UpperHalfPlane.coe_re]
  rw [hre,lt_div_iff₀ (Complex.normSq_pos.mpr z.ne_zero),zero_mul]
  constructor <;> intro h <;> nlinarith [sq_pos_of_pos hr]

end LowDimensionalTopology.Geometry.Fuchsian
