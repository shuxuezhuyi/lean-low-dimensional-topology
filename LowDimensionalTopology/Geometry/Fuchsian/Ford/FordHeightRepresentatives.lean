/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordRegions
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HalfPlaneH3
public import Mathlib.Data.Set.Finite.Lemmas
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem unitTranslation_nonaffine_pair_nonElementary (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  rw [realSLMobius_unitTranslation]
  let L:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
        1,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  intro he
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈L:=Subgroup.subset_closure (by simp)
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈L:=Subgroup.subset_closure (by simp)
  obtain ⟨p,hp,hall⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint L he _ hT
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 1).mpr (by norm_num))
  have heq : ∞=p:=(hp ∞).mp (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)
  exact hc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp (by simpa only [←heq] using hall ⟨_,hA⟩))

theorem discrete_unitTranslation_nonaffine_coefficient (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hc : A 1 0≠0) :
    1≤|A 1 0| := by
  have hle : Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
          1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤H:=
    (Subgroup.closure_le H).mpr (by
      intro f hf
      rcases hf with rfl|hf
      · rwa [realSLMobius_unitTranslation]
      · simpa only [Set.mem_singleton_iff] using hf ▸ hA)
  have hb:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.one_le_jorgensenDefect_of_discrete_nonElementary _ _ (discreteMobius_subgroup_of_le H _ hd hle)
    (unitTranslation_nonaffine_pair_nonElementary A hc)
  change 1≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map
      Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)))
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (Matrix.SpecialLinearGroup.map
      Complex.ofRealHom A)) at hb
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenDefect_representatives] at hb
  have hTlift : Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)=
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDiscTranslationLift := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [hTlift,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenMatrixDefect_parabolic] at hb
  change 1≤‖(A 1 0:ℂ)‖^2 at hb
  rw [Complex.norm_real,Real.norm_eq_abs] at hb
  nlinarith [abs_nonneg (A 1 0)]

theorem discrete_unitTranslation_orbit_height_bound (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (z : ℍ) :
    (A•z).im≤max z.im (1/z.im) := by
  rw [realSL_im_action]
  by_cases hc : A 1 0=0
  · have h:=discrete_unitTranslation_affine_denominator H hd hT A hA hc
    have hs : Complex.normSq (realSLDenominator A z)=1:=by
      change Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))=1
      simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.normSq_ofReal]
      nlinarith [sq_abs (A 1 1)]
    rw [hs,div_one]
    exact le_max_left _ _
  · have hb:=discrete_unitTranslation_nonaffine_coefficient H hd hT A hA hc
    have hs : z.im^2≤Complex.normSq (realSLDenominator A z):=by
      change z.im^2≤Complex.normSq ((A 1 0:ℂ)*(z:ℂ)+(A 1 1:ℂ))
      rw [Complex.normSq_apply]
      simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.add_im,Complex.mul_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,
        zero_mul,sub_zero,add_zero]
      have hc2 : 1≤(A 1 0)^2:=by nlinarith [sq_abs (A 1 0)]
      nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im),
        sq_nonneg (A 1 0*z.re+A 1 1)]
    have hs0 : 0<Complex.normSq (realSLDenominator A z):=lt_of_lt_of_le (sq_pos_of_pos z.im_pos) hs
    apply le_trans _ (le_max_right z.im (1/z.im))
    apply (div_le_div_iff₀ hs0 z.im_pos).mpr
    nlinarith [hs]

/-- The actual native orbit under all determinant-one lifts of the original group. -/
def realFordOrbit (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z : ℍ) : Set ℍ :=
  {w | ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H ∧
    A•z=w}

theorem realFordOrbit_compact_inter_finite (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (z : ℍ) (K : Set ℍ) (hK : IsCompact
      K) :
    (K∩realFordOrbit H z).Finite := by
  have hf:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_isDiscontinuous_H3 H
    hd).finite_inter_orbit (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
    (hK.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous)
  have hi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' (K∩realFordOrbit H z)).Finite:=hf.subset (by
    rintro _ ⟨w,⟨hwK,A,hA,he⟩,rfl⟩
    refine ⟨mem_image_of_mem _ hwK,⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,?_⟩⟩
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed w
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,he])
  exact hi.of_finite_image _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_injective.injOn


theorem halfPlane_rectangle_isCompact (L U : ℝ) (hL : 0<L) :
    IsCompact {w : ℍ | 0≤w.re ∧ w.re≤1 ∧ L≤w.im ∧ w.im≤U} := by
  let Q:=(2+U^2)/(2*L)
  let R:=Real.arcosh (max 1 Q)
  have hclosed : IsClosed {w : ℍ | 0≤w.re ∧ w.re≤1 ∧ L≤w.im ∧ w.im≤U}:=
    (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
      ((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
        ((isClosed_le continuous_const UpperHalfPlane.continuous_im).inter
          (isClosed_le UpperHalfPlane.continuous_im continuous_const)))
  apply (isCompact_closedBall UpperHalfPlane.I R).of_isClosed_subset hclosed
  intro w hw
  rw [Metric.mem_closedBall]
  have hc : Real.cosh (dist w UpperHalfPlane.I)≤Q:=by
    rw [UpperHalfPlane.cosh_dist']
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,sub_zero,one_pow,mul_one]
    have hnum : w.re^2+w.im^2+1≤2+U^2:=by
      have hy:=mul_self_le_mul_self w.im_pos.le hw.2.2.2
      nlinarith [mul_nonneg hw.1 (sub_nonneg.mpr hw.2.1),hy]
    apply (div_le_iff₀ (by positivity : 0<2*w.im)).mpr
    have hQ : 0<Q:=div_pos (by positivity) (by positivity)
    have he : Q*(2*L)=2+U^2:=by dsimp [Q];field_simp
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hw.2.2.1)]
  have hR : Real.cosh R=max 1 Q:=Real.cosh_arcosh (le_max_left _ _)
  have hm : Real.cosh (dist w UpperHalfPlane.I)≤Real.cosh R:=by
    rw [hR]
    exact hc.trans (le_max_right _ _)
  have ha:=Real.cosh_le_cosh.mp hm
  have hR0 : 0≤R:=Real.arcosh_nonneg (le_max_left _ _)
  simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hR0] using ha

theorem unitTranslation_integer_mem (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (n : ℤ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ))∈H := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)^n:=by rw [hTranslationSL_zpow];simp
  rw [he,map_zpow,realSLMobius_unitTranslation]
  exact H.zpow_mem hT n

theorem translation_into_closed_unit_strip (z : ℍ) : ∃n : ℤ,
    0≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
      (n:ℝ)•z).re ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z).re≤1 ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z).im=z.im := by
  have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL ((-Int.floor z.re:ℤ):ℝ)•z).re=z.re-Int.floor z.re:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL _•z:ℍ):ℂ).re=_
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp only [Complex.add_re,Complex.ofReal_re,Int.cast_neg]
    change z.re+ -(Int.floor z.re:ℝ)=z.re- (Int.floor z.re:ℝ)
    ring
  refine ⟨-Int.floor z.re,?_,?_,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_im _ _⟩
  · rw [he]
    linarith [Int.floor_le z.re]
  · rw [he]
    linarith [Int.lt_floor_add_one z.re]

/-- A maximum-height representative is obtained from the actual discrete orbit,
without any assumed Ford fundamental-domain or reduction property. -/
theorem exists_ford_maximal_orbit_point (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧ z.im≤(B•z).im ∧
      ∀A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H → (A•(B•z)).im≤(B•z).im := by
  let U:=max z.im (1/z.im)
  let K:={w : ℍ | 0≤w.re ∧ w.re≤1 ∧ z.im≤w.im ∧ w.im≤U}
  have hK : IsCompact K:=halfPlane_rectangle_isCompact _ _ z.im_pos
  have hF : (K∩realFordOrbit H z).Finite:=realFordOrbit_compact_inter_finite H hd z K hK
  obtain ⟨n,hn0,hn1,hnim⟩:=translation_into_closed_unit_strip z
  have hTm:=unitTranslation_integer_mem H hT n
  have hnonempty : (K∩realFordOrbit H z).Nonempty:=by
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z,⟨hn0,hn1,?_,?_⟩,?_⟩
    · rw [hnim]
    · rw [hnim]
      exact le_max_left _ _
    · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ),hTm,rfl⟩
  obtain ⟨w,hw,hmax⟩:=Set.exists_max_image (K∩realFordOrbit H z) (fun w=>w.im) hF hnonempty
  obtain ⟨B,hB,heB⟩:=hw.2
  have hwz : z.im≤w.im:=hw.1.2.2.1
  refine ⟨B,hB,by rwa [heB],?_⟩
  intro A hA
  rw [heB]
  by_contra hnot
  have hbig : w.im<(A•w).im:=lt_of_not_ge hnot
  obtain ⟨m,hm0,hm1,hmim⟩:=translation_into_closed_unit_strip (A•w)
  let C:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (m:ℝ)*A*B
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈H:=by
    dsimp only [C]
    rw [map_mul,map_mul]
    exact H.mul_mem (H.mul_mem (unitTranslation_integer_mem H hT m) hA) hB
  have heC : C•z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (m:ℝ)•(A•w):=by simp only [C,mul_smul,heB]
  have hupper : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (m:ℝ)•(A•w)).im≤U:=by
    rw [←heC]
    exact discrete_unitTranslation_orbit_height_bound H hd hT C hC z
  have hmK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (m:ℝ)•(A•w)∈K:=by
    exact ⟨hm0,hm1,by rw [hmim];exact hwz.trans hbig.le,hupper⟩
  have hmF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (m:ℝ)•(A•w)∈K∩realFordOrbit H z:=
    ⟨hmK,C,hC,heC⟩
  have hmax':=hmax _ hmF
  rw [hmim] at hmax'
  exact (not_lt_of_ge hmax') hbig

/-- The actual maximum-height representative lies in the literal common Ford exterior. -/
theorem exists_ford_exterior_orbit_representative (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧
      z.im≤(B•z).im ∧ B•z∈mobiusFordExterior H := by
  obtain ⟨B,hB,hheight,hmax⟩:=exists_ford_maximal_orbit_point H hd hT z
  refine ⟨B,hB,hheight,?_⟩
  intro A
  let w:=B•z
  have he:=realSL_im_action A.val w
  have hn : Complex.normSq (realSLDenominator A.val w)≠0:=by
    intro h0
    rw [h0,div_zero] at he
    exact (ne_of_gt (A.val•w).im_pos) he
  have hp : 0<Complex.normSq (realSLDenominator A.val w):=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hn)
  have hh:=hmax A.val A.property
  change (A.val•w).im≤w.im at hh
  rw [he] at hh
  have hs : 1≤Complex.normSq (realSLDenominator A.val w):=by
    have hm:=(div_le_iff₀ hp).mp hh
    nlinarith [w.im_pos]
  rw [Complex.normSq_eq_norm_sq] at hs
  change 1≤‖realSLDenominator A.val w‖
  nlinarith [norm_nonneg (realSLDenominator A.val w)]

theorem exists_ford_circle_orbit_representative (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧
      z.im≤(B•z).im ∧ B•z∈mobiusFordCircleExterior H := by
  rw [mobiusFordCircleExterior_eq H hd hT]
  exact exists_ford_exterior_orbit_representative H hd hT z

end LowDimensionalTopology.Geometry.Fuchsian
