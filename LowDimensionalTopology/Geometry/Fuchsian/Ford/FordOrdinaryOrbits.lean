/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordHeightRepresentatives
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusOrbitLimits
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- A genuine open sphere neighborhood disjoint from every nonidentity translate. -/
def HasSeparatingMobiusNeighborhood (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (ξ :
  _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : Prop :=
  ∃U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsOpen U ∧ ξ∈U ∧
    ∀g : H,g≠1→Disjoint ((fun x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>g • x) '' U) U

theorem separatingMobiusNeighborhood_of_discontinuous (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hD : IsOpen D)
    (hinv : ∀g : H,∀x∈D,g • x∈D) (hd : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      D)
    (ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hξ : ξ∈D) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    HasSeparatingMobiusNeighborhood H ξ := by
  obtain ⟨q,r,_hr,_hq,hN,hξN,_hcl,_hrot,hsep⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_roundDisc H D hD hinv hd ξ hξ
  refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r,hN.isOpen,hξN,?_⟩
  intro g hg
  apply (hsep g).2
  intro hf
  exact hg (hfree g hf)

theorem separatingMobiusNeighborhood_of_ordinary (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (ξ :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hξ : ξ∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H) (hfree : ∀g : H,g • ξ=ξ→g=1) :
    HasSeparatingMobiusNeighborhood H ξ :=
  separatingMobiusNeighborhood_of_discontinuous H _ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet_isOpen H)
    (fun g _ hx=>_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet_invariant H g
      hx) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_ordinary_discontinuous H hH hd) ξ hξ hfree

theorem separating_orbit_inter_subsingleton (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hU : ∀g : H,g≠1→Disjoint ((fun x : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>g • x) '' U) U)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : (MulAction.orbit H z∩U).Subsingleton := by
  rintro _ ⟨⟨g,rfl⟩,hg⟩ _ ⟨⟨h,rfl⟩,hh⟩
  by_cases he : h=g
  · rw [he]
  · have hn : h*g⁻¹≠1:=by
      intro heq
      apply he
      exact eq_of_mul_inv_eq_one heq
    exact False.elim (Set.disjoint_left.mp (hU (h*g⁻¹) hn)
      ⟨g • z,hg,by simp only [mul_smul,inv_smul_smul]⟩ hh)

theorem realFordOrbit_extended {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {z w : ℍ}
    (hw : w∈realFordOrbit H z) : ((w : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit H ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨A,hA,rfl⟩:=hw
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,?_⟩
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z

/-- Separation at infinity bounds the actual finite orbit, with no parabolic translation hypothesis. -/
theorem realFordOrbit_bounded_of_separating_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hsep : HasSeparatingMobiusNeighborhood H ∞) (z : ℍ) :
    Bornology.IsBounded (((↑) : ℍ→ℂ) '' realFordOrbit H z) := by
  obtain ⟨U,hU,hinf,hsepU⟩:=hsep
  obtain ⟨K,⟨_hKclosed,hKcompact⟩,hKU⟩:=OnePoint.hasBasis_nhds_infty.mem_iff.mp (hU.mem_nhds hinf)
  let O:=((↑) : ℍ→ℂ) '' realFordOrbit H z
  let S:=O∩{w : ℂ | (w : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈U}
  have hS : S.Subsingleton:=by
    intro x hx y hy
    apply OnePoint.coe_injective
    apply separating_orbit_inter_subsingleton H U hsepU ((z : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · obtain ⟨u,hu,rfl⟩:=hx.1
      exact ⟨realFordOrbit_extended hu,hx.2⟩
    · obtain ⟨u,hu,rfl⟩:=hy.1
      exact ⟨realFordOrbit_extended hu,hy.2⟩
  apply (hKcompact.isBounded.union hS.finite.isBounded).subset
  intro w hw
  by_cases hwK : w∈K
  · exact Or.inl hwK
  · exact Or.inr ⟨hw,hKU (Or.inl ⟨w,hwK,rfl⟩)⟩

/-- A genuine Euclidean bounded slab away from the real axis is hyperbolically compact. -/
theorem halfPlane_norm_slab_isCompact (R L : ℝ) (hL : 0<L) :
    IsCompact {w : ℍ | ‖(w : ℂ)‖≤R ∧ L≤w.im} := by
  let Q:=(R^2+1)/(2*L)
  let r:=Real.arcosh (max 1 Q)
  have hclosed₁ : IsClosed {w : ℍ | ‖(w : ℂ)‖≤R}:=
    isClosed_le (by fun_prop) continuous_const
  have hclosed : IsClosed {w : ℍ | ‖(w : ℂ)‖≤R ∧ L≤w.im}:=
    hclosed₁.inter (isClosed_le continuous_const UpperHalfPlane.continuous_im)
  apply (isCompact_closedBall UpperHalfPlane.I r).of_isClosed_subset hclosed
  intro w hw
  rw [Metric.mem_closedBall]
  have hnorm : w.re^2+w.im^2=‖(w : ℂ)‖^2:=by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    change w.re^2+w.im^2=w.re*w.re+w.im*w.im
    ring
  have hnum : w.re^2+w.im^2+1≤R^2+1:=by
    rw [hnorm]
    nlinarith [norm_nonneg (w : ℂ),hw.1]
  have hc : Real.cosh (dist w UpperHalfPlane.I)≤Q:=by
    rw [UpperHalfPlane.cosh_dist']
    simp only [UpperHalfPlane.I_re,UpperHalfPlane.I_im,sub_zero,one_pow,mul_one]
    apply (div_le_iff₀ (by positivity : 0<2*w.im)).mpr
    have hQ : 0<Q:=div_pos (by positivity) (by positivity)
    have he : Q*(2*L)=R^2+1:=by dsimp [Q];field_simp
    nlinarith [mul_nonneg hQ.le (sub_nonneg.mpr hw.2)]
  have hr : Real.cosh r=max 1 Q:=Real.cosh_arcosh (le_max_left _ _)
  have hm : Real.cosh (dist w UpperHalfPlane.I)≤Real.cosh r:=by
    rw [hr]
    exact hc.trans (le_max_right _ _)
  have ha:=Real.cosh_le_cosh.mp hm
  have hr0 : 0≤r:=Real.arcosh_nonneg (le_max_left _ _)
  simpa only [abs_of_nonneg dist_nonneg,abs_of_nonneg hr0] using ha

/-- Actual maximum-height representatives for the ordinary-infinity branch, without a unit translation. -/
theorem exists_ford_maximal_of_separating_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧ z.im≤(B • z).im ∧
      ∀A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H→(A • (B • z)).im≤(B • z).im := by
  obtain ⟨R,_hR,hR⟩:=(realFordOrbit_bounded_of_separating_infty H hsep z).exists_pos_norm_le
  let K:={w : ℍ | ‖(w : ℂ)‖≤R ∧ z.im≤w.im}
  have hK : IsCompact K:=halfPlane_norm_slab_isCompact R z.im z.im_pos
  have hF : (K∩realFordOrbit H z).Finite:=realFordOrbit_compact_inter_finite H hd z K hK
  have hzO : z∈realFordOrbit H z:=⟨1,by rw [map_one];exact H.one_mem,one_smul _ _⟩
  have hnonempty : (K∩realFordOrbit H z).Nonempty:=⟨z,⟨hR _ (mem_image_of_mem _ hzO),le_rfl⟩,hzO⟩
  obtain ⟨w,hw,hmax⟩:=Set.exists_max_image (K∩realFordOrbit H z) (fun w=>w.im) hF hnonempty
  obtain ⟨B,hB,heB⟩:=hw.2
  refine ⟨B,hB,by rw [heB];exact hw.1.2,?_⟩
  intro A hA
  rw [heB]
  by_contra hn
  have hbig : w.im<(A • w).im:=lt_of_not_ge hn
  have hAO : A • w∈realFordOrbit H z:=by
    refine ⟨A*B,?_,?_⟩
    · rw [map_mul]
      exact H.mul_mem hA hB
    · rw [mul_smul,heB]
  have hAK : A • w∈K:=⟨hR _ (mem_image_of_mem _ hAO),hw.1.2.trans hbig.le⟩
  exact (not_lt_of_ge (hmax _ ⟨hAK,hAO⟩)) hbig


theorem HasSeparatingMobiusNeighborhood.stabilizer_trivial {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {ξ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hsep : HasSeparatingMobiusNeighborhood H ξ) (g
      : H)
    (hfix : g • ξ=ξ) : g=1 := by
  obtain ⟨U,_hU,hξ,hsepU⟩:=hsep
  by_contra hg
  exact Set.disjoint_left.mp (hsepU g hg) ⟨ξ,hξ,hfix⟩ hξ

theorem separating_infty_affine_identity (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hsep : HasSeparatingMobiusNeighborhood H ∞)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈H) (hc : A 1 0=0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=1 := by
  have he : (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩ : H)=1:=
    hsep.stabilizer_trivial _ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mpr
      hc)
  exact congrArg Subtype.val he

theorem realSL_im_le_iff_denominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (A • z).im≤z.im ↔ 1≤‖realSLDenominator A z‖ := by
  refine ⟨?_,realSL_im_le_of_denominator A z⟩
  intro hle
  have he:=realSL_im_action A z
  have hn : Complex.normSq (realSLDenominator A z)≠0:=by
    intro h0
    rw [h0,div_zero] at he
    exact (ne_of_gt (A • z).im_pos) he
  have hp : 0<Complex.normSq (realSLDenominator A z):=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hn)
  rw [he] at hle
  have hm:=(div_le_iff₀ hp).mp hle
  have hs : 1≤Complex.normSq (realSLDenominator A z):=by nlinarith [z.im_pos]
  rw [Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (realSLDenominator A z)]

/-- The ordinary-infinity hypotheses omit every nonidentity affine element, without using a translation. -/
theorem mobiusFordCircleExterior_eq_of_separating_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hsep : HasSeparatingMobiusNeighborhood H ∞) :
    mobiusFordCircleExterior H=mobiusFordExterior H := by
  ext z
  constructor
  · intro hz A
    by_cases hc : A.val 1 0=0
    · have he:=separating_infty_affine_identity H hsep A.val A.property hc
      have hfix : A.val • z=z:=by
        apply UpperHalfPlane.coe_injective
        apply OnePoint.coe_injective
        rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A.val z,he]
        rfl
      exact (realSL_im_le_iff_denominator A.val z).mp (by rw [hfix])
    · exact (realSLDenominator_ge_one_iff_circle_exterior A.val hc z).mpr (hz A.val A.property hc)
  · intro hz A hA hc
    exact (realSLDenominator_ge_one_iff_circle_exterior A hc z).mp (hz ⟨A,hA⟩)

theorem exists_ford_exterior_of_separating_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧ z.im≤(B • z).im ∧
      B • z∈mobiusFordCircleExterior H := by
  obtain ⟨B,hB,hheight,hmax⟩:=exists_ford_maximal_of_separating_infty H hd hsep z
  refine ⟨B,hB,hheight,?_⟩
  rw [mobiusFordCircleExterior_eq_of_separating_infty H hsep]
  intro A
  exact (realSL_im_le_iff_denominator A.val (B • z)).mp (hmax A.val A.property)

/-- The non-elementary ordinary-set instance retains precisely the ordinary/free infinity convention. -/
theorem exists_ford_exterior_of_ordinary_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hd :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H)
    (hinf : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H)
    (hfree : ∀g : H,g • (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞→g=1) (z : ℍ) :
    ∃B : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈H ∧ z.im≤(B • z).im ∧
      B • z∈mobiusFordCircleExterior H :=
  exists_ford_exterior_of_separating_infty H hd
    (separatingMobiusNeighborhood_of_ordinary H hH hd ∞ hinf hfree) z

end
end LowDimensionalTopology.Geometry.Fuchsian
