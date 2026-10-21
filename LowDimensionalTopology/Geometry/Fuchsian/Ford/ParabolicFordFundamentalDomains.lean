/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordHeightRepresentatives
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CosetFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Topology MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane MatrixGroups Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal closed unit-strip Ford region for the original sphere group. -/
def parabolicFordClosedStrip (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ:=
  {z | 0≤z.re ∧ z.re≤1 ∧ z∈mobiusFordExterior H}

/-- Its actual topological interior, without presupposing a domain theorem. -/
def parabolicFordDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ:=
  interior (parabolicFordClosedStrip H)

theorem parabolicFordClosedStrip_isClosed (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    IsClosed (parabolicFordClosedStrip H) := by
  have he : parabolicFordClosedStrip H={z : ℍ | 0≤z.re}∩{z : ℍ | z.re≤1}∩mobiusFordExterior H:=by
    ext z;simp only [parabolicFordClosedStrip,mem_ofPred_eq,mem_inter_iff,and_assoc]
  rw [he]
  exact ((isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
    (isClosed_le UpperHalfPlane.continuous_re continuous_const)).inter (fordExterior_isClosed _)

theorem parabolicFord_hConvex_re_le (c : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | z.re≤c} := by
  intro x hx y hy z hz
  change x.re≤c at hx
  change y.re≤c at hy
  by_contra hnot
  have hc : c<z.re:=lt_of_not_ge hnot
  have hh:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hReCutLt_hConvex ((c+z.re)/2)) x (by change x.re<(c+z.re)/2;linarith only [hx,hc])
    y (by change y.re<(c+z.re)/2;linarith only [hy,hc]) hz
  change z.re<(c+z.re)/2 at hh
  linarith only [hh,hc]

theorem parabolicFord_hConvex_re_ge (c : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | c≤z.re} := by
  have hgt (a : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | a<z.re}:=by
    let m:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (a+1) 1 zero_lt_one
    have hm : a<m.re:=by change a<a+1;linarith
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_vertical_gt a m hm]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_hConvex _ _ (ne_of_gt hm)
  intro x hx y hy z hz
  change c≤x.re at hx
  change c≤y.re at hy
  by_contra hnot
  have hc : z.re<c:=lt_of_not_ge hnot
  have hh:=(hgt ((c+z.re)/2)) x (by change (c+z.re)/2<x.re;linarith only [hx,hc])
    y (by change (c+z.re)/2<y.re;linarith only [hy,hc]) hz
  change (c+z.re)/2<z.re at hh
  linarith only [hh,hc]

/-- Every genuine closed isometric-circle exterior is hyperbolically convex. -/
theorem parabolicFord_denominator_ge_hConvex (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 1≤‖realSLDenominator A z‖} := by
  have habs : 0 < |A 1 0|:=abs_pos.mpr hc
  have hlevel (r : ℝ) (hr : 0<r) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | r<‖realSLDenominator A z‖}:=by
    have he : {z : ℍ | r<‖realSLDenominator A z‖}=
        {z : ℍ | r/ |A 1 0|<‖(z:ℂ)-((-A 1 1/A 1 0:ℝ):ℂ)‖}:=by
      ext z
      change (r<‖realSLDenominator A z‖) ↔ r/ |A 1 0|<‖(z:ℂ)-((-A 1 1/A 1 0:ℝ):ℂ)‖
      rw [realSLDenominator_norm_factor A hc,div_lt_iff₀ habs]
      simp only [mul_comm]
    rw [he]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_outside_circle _ _ (div_pos hr habs)
  intro x hx y hy z hz
  change 1≤‖realSLDenominator A x‖ at hx
  change 1≤‖realSLDenominator A y‖ at hy
  by_contra hnot
  have hn : ‖realSLDenominator A z‖<1:=lt_of_not_ge hnot
  let r:=(‖realSLDenominator A z‖+1)/2
  have hr : 0<r:=by dsimp [r];positivity
  have hh:=(hlevel r hr) x (by change r<‖realSLDenominator A x‖;dsimp [r];linarith only [hx,hn])
    y (by change r<‖realSLDenominator A y‖;dsimp [r];linarith only [hy,hn]) hz
  change r<‖realSLDenominator A z‖ at hh
  dsimp only [r] at hh
  linarith only [hh,hn]

theorem parabolicFordExterior_hConvex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (mobiusFordExterior H) := by
  intro x hx y hy z hz A
  by_cases hc : A.val 1 0=0
  · have he:=discrete_unitTranslation_affine_denominator H hd hT A.val A.property hc
    change 1≤‖(A.val 1 0:ℂ)*(z:ℂ)+(A.val 1 1:ℂ)‖
    simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.norm_real,Real.norm_eq_abs,he,le_refl]
  · exact parabolicFord_denominator_ge_hConvex A.val hc x (hx A) y (hy A) hz

theorem parabolicFordClosedStrip_hConvex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (parabolicFordClosedStrip H) := by
  intro x hx y hy z hz
  exact ⟨parabolicFord_hConvex_re_ge 0 x hx.1 y hy.1 hz,
    parabolicFord_hConvex_re_le 1 x hx.2.1 y hy.2.1 hz,
    parabolicFordExterior_hConvex H hd hT x hx.2.2 y hy.2.2 hz⟩

theorem parabolicFordDomain_hConvex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      1∈H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (parabolicFordDomain H):=
  (parabolicFordClosedStrip_hConvex H hd hT).interior

/-- The true Shimizu coefficient bound puts the whole high horoball in
 the literal common Ford exterior. -/
theorem parabolicFord_high_im_exterior (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (z : ℍ) (hz : 1≤z.im) : z∈mobiusFordExterior H := by
  intro A
  by_cases hc : A.val 1 0=0
  · have he:=discrete_unitTranslation_affine_denominator H hd hT A.val A.property hc
    change 1≤‖(A.val 1 0:ℂ)*(z:ℂ)+(A.val 1 1:ℂ)‖
    simp only [hc,Complex.ofReal_zero,zero_mul,zero_add,Complex.norm_real,Real.norm_eq_abs,he,le_refl]
  · have hb:=discrete_unitTranslation_nonaffine_coefficient H hd hT A.val A.property hc
    have him : |(realSLDenominator A.val z).im|=|A.val 1 0| *z.im:=by
      change |((A.val 1 0:ℂ)*(z:ℂ)+(A.val 1 1:ℂ)).im|=|A.val 1 0| *z.im
      simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,UpperHalfPlane.coe_im,
        Complex.ofReal_im,zero_mul,add_zero,abs_mul,abs_of_pos z.im_pos]
    calc
      1≤|A.val 1 0| *z.im:=by nlinarith only [hb,hz]
      _=|(realSLDenominator A.val z).im|:=him.symm
      _≤‖realSLDenominator A.val z‖:=Complex.abs_im_le_norm _

theorem parabolicFord_high_open_strip_subset (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    {z : ℍ | 0<z.re ∧ z.re<1 ∧ 1<z.im}⊆parabolicFordDomain H := by
  apply interior_maximal _
    ((isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
      ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
      (isOpen_lt continuous_const UpperHalfPlane.continuous_im)))
  intro z hz
  exact ⟨hz.1.le,hz.2.1.le,parabolicFord_high_im_exterior H hd hT z hz.2.2.le⟩

theorem parabolicFordDomain_nonempty (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    (parabolicFordDomain H).Nonempty := by
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (1/2) 2 (by norm_num)
  exact ⟨z,parabolicFord_high_open_strip_subset H hd hT (by change (0:ℝ)<1/2 ∧ 1/2<1 ∧ 1<2;norm_num)⟩

/-- Regularity of a genuine convex region is inherited from the actual
 open Klein chart and finite-dimensional convex-set topology. -/
theorem parabolicFord_closure_interior_of_hConvex {S : Set ℍ} (hS :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S)
    (hc : IsClosed S) (hn : (interior S).Nonempty) : closure (interior S)=S := by
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
  have hf : Topology.IsOpenEmbedding f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate
  have hK : Convex ℝ (f '' S):=by
    change Convex ℝ ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) '' S)
    rw [←Set.image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hS)
  have hpre : f ⁻¹' interior (f '' S)=interior S:=by
    rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
      Set.preimage_image_eq _ hf.injective]
  have hInt : f '' interior S=interior (f '' S):=by
    rw [←hpre,Set.image_preimage_eq_inter_range]
    apply Set.inter_eq_left.mpr
    rintro y hy
    obtain ⟨x,_hx,rfl⟩:=interior_subset hy
    exact ⟨x,rfl⟩
  have hnK : (interior (f '' S)).Nonempty:=by rw [←hInt];exact hn.image f
  rw [hf.isEmbedding.closure_eq_preimage_closure_image,hInt,
    hK.closure_interior_eq_closure_of_nonempty_interior hnK,
    ←hf.isEmbedding.closure_eq_preimage_closure_image,hc.closure_eq]

theorem closure_parabolicFordDomain (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    closure (parabolicFordDomain H)=parabolicFordClosedStrip H :=
  parabolicFord_closure_interior_of_hConvex (parabolicFordClosedStrip_hConvex H hd hT)
    (parabolicFordClosedStrip_isClosed H) (parabolicFordDomain_nonempty H hd hT)

theorem parabolicFordDomain_isConnected (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    IsConnected (parabolicFordDomain H) :=
  ⟨parabolicFordDomain_nonempty H hd hT,(parabolicFordDomain_hConvex H hd hT).isPreconnected⟩

theorem parabolicFord_hConvex_frontier_volume_zero {S : Set ℍ} (hS :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) :
    volume (frontier S)=0 := by
  have hh:=coset_discHConvex_frontier_area_zero ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hS)
  have hfront : frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ''
    S)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' frontier S:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_frontier S).symm
  rw [hfront] at hh
  have hM : MeasurableSet (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' frontier S):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isClosedMap _ isClosed_frontier).measurableSet
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' frontier S) hM,Set.image_image] at hh
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,Set.image_id'] using hh

theorem parabolicFordDomain_frontier_volume_zero (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    volume (frontier (parabolicFordDomain H))=0 :=
  parabolicFord_hConvex_frontier_volume_zero (parabolicFordDomain_hConvex H hd hT)

theorem parabolicFord_im_le_iff_denominator (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (A•z).im≤z.im ↔ 1≤‖realSLDenominator A z‖ := by
  have hp : 0<Complex.normSq (realSLDenominator A z):=
    UpperHalfPlane.normSq_denom_pos (Matrix.SpecialLinearGroup.mapGL ℝ A) z.im_ne_zero
  rw [realSL_im_action,div_le_iff₀ hp,Complex.normSq_eq_norm_sq]
  constructor
  · intro hh
    by_contra hn
    have hn' : ‖realSLDenominator A z‖<1:=lt_of_not_ge hn
    have hs : ‖realSLDenominator A z‖^2<1:=by nlinarith [norm_nonneg (realSLDenominator A z)]
    nlinarith [mul_pos z.im_pos (sub_pos.mpr hs)]
  · intro hn
    have hs : 1≤‖realSLDenominator A z‖^2:=by nlinarith only [hn]
    nlinarith [mul_nonneg z.im_pos.le (sub_nonneg.mpr hs)]

/-- Integer translates of maximal-height orbit representatives remain
 in exactly the same literal common exterior. -/
theorem parabolicFordExterior_integer_translate (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z : ℍ) (hz :
      z∈mobiusFordExterior H) (n : ℤ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z∈mobiusFordExterior H := by
  intro A
  apply (parabolicFord_im_le_iff_denominator A.val _).mp
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ))∈H:=by
    rw [map_mul]
    exact H.mul_mem A.property (unitTranslation_integer_mem H hT n)
  have ht:=realSL_im_le_of_denominator (A.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    (n:ℝ)) z (hz ⟨_,hB⟩)
  rw [mul_smul] at ht
  have him : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z).im=z.im:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z:ℍ):ℂ).im=z.im
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    simp
  rwa [him]

/-- Every original orbit reaches the literal closed unit-strip region. -/
theorem parabolicFordClosedStrip_orbit_representative {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (z
      : ℍ) :
    letI:=P.nativeAction
    ∃g : H,g•z∈parabolicFordClosedStrip H := by
  let parabolicFordOriginalAction:=P.nativeAction
  obtain ⟨B,hB,_hheight,hBext⟩:=exists_ford_exterior_orbit_representative H P.discrete hT z
  obtain ⟨n,hn0,hn1,_hnim⟩:=translation_into_closed_unit_strip (B•z)
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)*B
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)*B)∈H
    rw [map_mul]
    exact H.mul_mem (unitTranslation_integer_mem H hT n) hB
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,?_⟩
  rw [P.nativeAction_realSL _ A rfl]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)*B)•z∈parabolicFordClosedStrip H
  rw [mul_smul]
  exact ⟨hn0,hn1,parabolicFordExterior_integer_translate H hT (B•z) hBext n⟩

theorem parabolicFord_denominator_isOpenMap (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : IsOpenMap (fun z : ℍ=>‖realSLDenominator A z‖) := by
  let c:=-A 1 1/A 1 0
  let t:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-c)
  have hh:=((Homeomorph.mulLeft₀ |A 1 0| (abs_pos.mpr hc).ne').isOpenMap.comp
    (UpperHalfPlane.isOpenMap_norm.comp (Homeomorph.smul t).isOpenMap))
  change IsOpenMap (fun z : ℍ=>|A 1 0| *‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL
    (-c)•z:ℍ):ℂ)‖) at hh
  have he : (fun z : ℍ=>|A 1 0| *‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-c)•z:ℍ):ℂ)‖)=
      (fun z : ℍ=>‖realSLDenominator A z‖):=by
    funext z
    rw [realSLDenominator_norm_factor A hc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    congr 2
    dsimp only [c]
    push_cast
    ring
  rwa [he] at hh

/-- The true interior points lie strictly between the two strip edges
 and strictly outside every genuine non-affine isometric circle. -/
theorem parabolicFordDomain_strict_constraints (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (z : ℍ) (hz : z∈parabolicFordDomain H) :
    0<z.re ∧ z.re<1 ∧ ∀A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H → A 1 0≠0 → 1<‖realSLDenominator A z‖ := by
  have hlo : z∈interior (UpperHalfPlane.re ⁻¹' Ici (0:ℝ)):=
    interior_mono (fun x hx=>(hx : x∈parabolicFordClosedStrip H).1) hz
  have hhi : z∈interior (UpperHalfPlane.re ⁻¹' Iic (1:ℝ)):=
    interior_mono (fun x hx=>(hx : x∈parabolicFordClosedStrip H).2.1) hz
  rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
    interior_Ici] at hlo
  rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
    interior_Iic] at hhi
  refine ⟨hlo,hhi,?_⟩
  intro A hA hc
  have hsub : parabolicFordClosedStrip H⊆(fun w : ℍ=>‖realSLDenominator A w‖) ⁻¹' Ici (1:ℝ):=by
    intro w hw
    exact hw.2.2 ⟨A,hA⟩
  have hm:=interior_mono hsub hz
  rw [←(parabolicFord_denominator_isOpenMap A hc).preimage_interior_eq_interior_preimage
    (realSLDenominator_norm_continuous A),interior_Ici] at hm
  exact hm

/-- The primitive full infinity stabilizer, rather than mere membership
 of the unit translation, supplies the actual orbit uniqueness. -/
theorem parabolicFordDomain_orbit_unique {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H)
    (hstab : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1))
    (x y : ℍ) (hx : x∈parabolicFordDomain H) (hy : y∈parabolicFordDomain H) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ y → x=y := by
  let parabolicFordOriginalAction:=P.nativeAction
  intro hxy
  obtain ⟨g,hgy⟩:=(Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
  change g•y=x at hgy
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hAct : A•y=x:=by rwa [←P.nativeAction_realSL g A hA y]
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ g.property
  by_cases hc : A 1 0=0
  · have hfix : g.val.val (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞:=by rw [←hA];simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,hc]
    have hmem : g.val∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=by
      rw [←hstab]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞
        _).mpr ⟨g.property,hfix⟩
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hmem
    have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ))=g.val:=by
      have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)^n:=by rw [hTranslationSL_zpow];simp
      rw [he,map_zpow,realSLMobius_unitTranslation,hn]
    have hTr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•y=x:=by rw [←P.nativeAction_realSL g _ hp y];exact hgy
    have hRe : x.re=y.re+n:=by
      rw [←hTr]
      change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•y:ℍ):ℂ).re=_
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
      simp
    have hX:=parabolicFordDomain_strict_constraints H x hx
    have hY:=parabolicFordDomain_strict_constraints H y hy
    have hnlo : (-1:ℝ)<n:=by linarith only [hRe,hX.1,hY.2.1]
    have hnhi : (n:ℝ)<1:=by linarith only [hRe,hY.1,hX.2.1]
    have hn0 : n=0:=by
      have hl : (-1:ℤ)<n:=by exact_mod_cast hnlo
      have hr : n<1:=by exact_mod_cast hnhi
      omega
    have hg1 : g=1:=by apply Subtype.ext;rw [←hn,hn0,zpow_zero];rfl
    simpa only [hg1,one_smul] using hgy.symm
  · have hnorm:=(parabolicFordDomain_strict_constraints H y hy).2.2 A hAH hc
    have hlt : x.im<y.im:=by rw [←hAct];exact (realSL_im_lt_iff_denominator A y).mpr hnorm
    have hAi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹∈H:=by rw [map_inv];exact H.inv_mem hAH
    have hle:=realSL_im_le_of_denominator A⁻¹ x ((interior_subset hx).2.2 ⟨A⁻¹,hAi⟩)
    have hback : A⁻¹•x=y:=by rw [←hAct,inv_smul_smul]
    rw [hback] at hle
    exact (not_lt_of_ge hle hlt).elim

theorem parabolicFordDomain_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ (closure (parabolicFordDomain H)) := by
  let parabolicFordOriginalAction:=P.nativeAction
  intro z
  obtain ⟨g,hg⟩:=parabolicFordClosedStrip_orbit_representative P hT z
  exact ⟨g,by rwa [closure_parabolicFordDomain H P.discrete hT]⟩

/-- The corrected primitive-parabolic unit-strip theorem: the actual
 interior of the literal original Ford strip is a genuine fundamental
 domain, using the full infinity stabilizer and the true density area. -/
theorem parabolicFordDomain_fundamental {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hstab : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (parabolicFordDomain H) := by
  let parabolicFordOriginalAction:=P.nativeAction
  refine ⟨isOpen_interior,parabolicFordDomain_isConnected H P.discrete hT,?_,
    parabolicFordDomain_frontier_volume_zero H P.discrete hT⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (parabolicFordDomain_closure_meetsEveryOrbit P hT)
    (fun x hx y hy hxy=>parabolicFordDomain_orbit_unique P hstab x y hx hy hxy)

/-- The source primitive-element hypothesis supplies the complete
 stabilizer condition; membership of a nonprimitive translation cannot
 silently stand in its place. -/
theorem primitive_unitTranslation_Ford_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (parabolicFordDomain H) := by
  exact parabolicFordDomain_fundamental P hprim.1
    (hprim.generates ∞ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)).symm

/-- Compact sets meet only finitely many genuine closed Ford-strip
 tiles. The primitive case needs no separating neighborhood at infinity. -/
theorem parabolicFordClosedStrip_compact_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (K : Set ℍ) (hK : IsCompact K) :
    letI:=P.nativeAction
    {g : H | (g • parabolicFordClosedStrip H ∩ K).Nonempty}.Finite := by
  let parabolicFordOriginalAction:=P.nativeAction
  by_cases hn : K.Nonempty
  · obtain ⟨l,hl,hmin⟩:=hK.exists_isMinOn hn UpperHalfPlane.continuous_im.continuousOn
    obtain ⟨u,hu,hmax⟩:=hK.exists_isMaxOn hn UpperHalfPlane.continuous_im.continuousOn
    let U:=max u.im (1/l.im)
    let R:={z : ℍ | 0≤z.re ∧ z.re≤1 ∧ l.im≤z.im ∧ z.im≤U}
    have hR : IsCompact R:=halfPlane_rectangle_isCompact l.im U l.im_pos
    let Q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' K∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' R
    have hQ : IsCompact Q:=(hK.image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous).union (hR.image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous)
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_isDiscontinuous_H3 H P.discrete Q
      hQ).subset
    intro g hg
    obtain ⟨z,hzg,hzK⟩:=hg
    obtain ⟨v,hv,hvz⟩:=hzg
    change g•v=z at hvz
    obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
    have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ g.property
    have hAz : A•v=z:=by rw [←P.nativeAction_realSL g A hA v];exact hvz
    have hdown : z.im≤v.im:=by
      rw [←hAz]
      exact realSL_im_le_of_denominator A v (hv.2.2 ⟨A,hAH⟩)
    have hAi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹∈H:=by rw [map_inv];exact H.inv_mem hAH
    have hback : A⁻¹•z=v:=by rw [←hAz,inv_smul_smul]
    have hupper:=discrete_unitTranslation_orbit_height_bound H P.discrete hT A⁻¹ hAi z
    rw [hback] at hupper
    have hRmax : max z.im (1/z.im)≤U:=by
      apply max_le
      · exact (hmax hzK).trans (le_max_left _ _)
      · exact (one_div_le_one_div_of_le l.im_pos (hmin hzK)).trans (le_max_right _ _)
    have hvR : v∈R:=⟨hv.1,hv.2.1,(hmin hzK).trans hdown,hupper.trans hRmax⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed
      z,⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed v,Or.inr ⟨v,hvR,rfl⟩,?_⟩,
      Or.inl ⟨z,hzK,rfl⟩⟩
    change g.val•_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed v=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z
    rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,hAz]
  · have he : K=∅:=not_nonempty_iff_eq_empty.mp hn
    simp only [he,Set.inter_empty,Set.not_nonempty_empty,Set.ofPred_false,Set.finite_empty]

theorem parabolicFordClosedStrip_locallyFinite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    letI:=P.nativeAction
    LocallyFinite (fun g : H=>g • parabolicFordClosedStrip H) := by
  let parabolicFordOriginalAction:=P.nativeAction
  intro x
  obtain ⟨K,hK,hxK⟩:=exists_compact_mem_nhds x
  exact ⟨K,hxK,parabolicFordClosedStrip_compact_hits_finite P hT K hK⟩

/-- The literal strict-circle exterior cut by the original open unit strip. -/
def parabolicFordStrictStrip (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ:=
  {z | 0<z.re ∧ z.re<1 ∧ z∈strictFordRegion H}

theorem parabolicFordDomain_subset_strictStrip (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    parabolicFordDomain H⊆parabolicFordStrictStrip H := by
  intro z hz
  exact parabolicFordDomain_strict_constraints H z hz

/-- A strictly exterior strip point belongs to exactly its identity closed
 tile; the affine branch uses the entire primitive stabilizer. -/
theorem parabolicFordStrictStrip_closed_tile_unique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H)
    (hstab : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1))
    (z : ℍ) (hz : z∈parabolicFordStrictStrip H) (g : H) :
    letI:=P.nativeAction
    z∈g • parabolicFordClosedStrip H → g=1 := by
  let parabolicFordOriginalAction:=P.nativeAction
  rintro ⟨u,hu,hgu⟩
  change g•u=z at hgu
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g⁻¹.val (P.preserves g⁻¹)
  have hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hA.symm ▸ g⁻¹.property
  have hAz : A•z=u:=by
    rw [←P.nativeAction_realSL g⁻¹ A hA z,←hgu,inv_smul_smul]
  by_cases hc : A 1 0=0
  · have hfix : g⁻¹.val.val (∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞:=by rw [←hA];simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,hc]
    have hmem : g⁻¹.val∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1):=by
      rw [←hstab]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞
        _).mpr ⟨g⁻¹.property,hfix⟩
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp hmem
    have hp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ))=g⁻¹.val:=by
      have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)^n:=by rw [hTranslationSL_zpow];simp
      rw [he,map_zpow,realSLMobius_unitTranslation,hn]
    have hTr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z=u:=by
      rw [←P.nativeAction_realSL g⁻¹ _ hp z,←hgu,inv_smul_smul]
    have hRe : u.re=z.re+n:=by
      rw [←hTr]
      change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•z:ℍ):ℂ).re=_
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
      simp
    have hnlo : (-1:ℝ)<n:=by linarith only [hRe,hu.1,hz.2.1]
    have hnhi : (n:ℝ)<1:=by linarith only [hRe,hz.1,hu.2.1]
    have hn0 : n=0:=by
      have hl : (-1:ℤ)<n:=by exact_mod_cast hnlo
      have hr : n<1:=by exact_mod_cast hnhi
      omega
    apply inv_eq_one.mp
    apply Subtype.ext
    rw [←hn,hn0,zpow_zero]
    rfl
  · have hnorm:=hz.2.2 A hAH hc
    have hlt : u.im<z.im:=by rw [←hAz];exact (realSL_im_lt_iff_denominator A z).mpr hnorm
    have hAi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹∈H:=by rw [map_inv];exact H.inv_mem hAH
    have hle:=realSL_im_le_of_denominator A⁻¹ u (hu.2.2 ⟨A⁻¹,hAi⟩)
    have hback : A⁻¹•u=z:=by rw [←hAz,inv_smul_smul]
    rw [hback] at hle
    exact (not_lt_of_ge hle hlt).elim

/-- The actual primitive Ford strip agrees with its literal strict-circle
 definition. Local finiteness and true closed-tile coverage prove the
 difficult infinite-intersection openness implication. -/
theorem parabolicFordDomain_eq_strictStrip {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (hstab : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞=Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    parabolicFordDomain H=parabolicFordStrictStrip H := by
  let parabolicFordOriginalAction:=P.nativeAction
  let parabolicFordNativeContinuous : ContinuousConstSMul H ℍ:=⟨fun g=>(P.nativeHom g).continuous⟩
  apply Set.Subset.antisymm (parabolicFordDomain_subset_strictStrip H)
  intro z hz
  have hLF:=parabolicFordClosedStrip_locallyFinite P hT
  have hC (g : H) : IsClosed (g • parabolicFordClosedStrip H):=
    (Homeomorph.smul g).isClosedMap _ (parabolicFordClosedStrip_isClosed H)
  have hN:=hLF.iInter_compl_mem_nhds hC z
  apply mem_interior_iff_mem_nhds.mpr
  apply mem_of_superset hN
  intro y hy
  obtain ⟨g,hgyS⟩:=parabolicFordClosedStrip_orbit_representative P hT y
  have hgy : y∈g⁻¹ • parabolicFordClosedStrip H:=⟨g•y,hgyS,inv_smul_smul g y⟩
  by_cases hg : g⁻¹=1
  · simpa only [hg,one_smul] using hgy
  · have hzg : z∉g⁻¹ • parabolicFordClosedStrip H:=by
      intro hzi
      exact hg (parabolicFordStrictStrip_closed_tile_unique P hstab z hz g⁻¹ hzi)
    exact ((mem_iInter₂.mp hy g⁻¹ hzg) hgy).elim

/-- The pre-existing literal Ford-domain definition and the genuine
 closed-strip-interior construction are exactly the same point set. -/
theorem parabolicFordDomain_eq_mobiusFordDomain (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    parabolicFordDomain H=mobiusFordDomain H 0 := by
  have he : parabolicFordClosedStrip H=mobiusFordExterior H∩UpperHalfPlane.re ⁻¹' Icc (0:ℝ) 1:=by
    ext z
    simp only [parabolicFordClosedStrip,mem_ofPred_eq,mem_inter_iff,mem_preimage,mem_Icc,and_comm,and_assoc]
  rw [parabolicFordDomain,he,interior_inter,
    ←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
    interior_Icc]
  change interior (mobiusFordExterior H)∩{z : ℍ | 0<z.re ∧ z.re<1}=_
  simp only [mobiusFordDomain,fordDomain,zero_add]
  rfl

theorem parabolicFordDomain_compact_hits_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) (K
      : Set ℍ) (hK : IsCompact K) :
    letI:=P.nativeAction
    {g : H | (g • closure (parabolicFordDomain H)∩K).Nonempty}.Finite := by
  let parabolicFordOriginalAction:=P.nativeAction
  rw [closure_parabolicFordDomain H P.discrete hT]
  exact parabolicFordClosedStrip_compact_hits_finite P hT K hK

theorem primitive_unitTranslation_strictFord_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (parabolicFordStrictStrip H) := by
  rw [←parabolicFordDomain_eq_strictStrip P hprim.mem (hprim.generates ∞
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)).symm]
  exact primitive_unitTranslation_Ford_fundamental P hprim

theorem parabolicFord_high_closed_strip_subset (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    {z : ℍ | 0≤z.re ∧ z.re≤1 ∧ 1≤z.im}⊆closure (parabolicFordDomain H) := by
  rw [closure_parabolicFordDomain H hd hT]
  intro z hz
  exact ⟨hz.1,hz.2.1,parabolicFord_high_im_exterior H hd hT z hz.2.2⟩

end LowDimensionalTopology.Geometry.Fuchsian
