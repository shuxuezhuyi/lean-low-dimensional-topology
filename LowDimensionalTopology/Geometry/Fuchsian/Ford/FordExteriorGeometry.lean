/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordOrdinaryOrbits
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The genuine ordinary-infinity bound is uniform over every compact family of base points. -/
theorem realFordOrbit_uniform_bound (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hsep : HasSeparatingMobiusNeighborhood H ∞) (K : Set ℍ) (hK : IsCompact K) :
    ∃R : ℝ,0<R ∧ ∀A : Matrix.SpecialLinearGroup (Fin
      2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H→
      ∀z∈K,‖((A • z : ℍ) : ℂ)‖≤R := by
  obtain ⟨R,hRpos,hR⟩:=(realFordOrbit_bounded_of_separating_infty H hsep UpperHalfPlane.I).exists_pos_norm_le
  obtain ⟨B,hB⟩:=hK.isBounded.subset_closedBall UpperHalfPlane.I
  refine ⟨R*Real.exp B,mul_pos hRpos (Real.exp_pos _),?_⟩
  intro A hA z hz
  have hbase : ‖((A • UpperHalfPlane.I : ℍ) : ℂ)‖≤R:=
    hR _ (mem_image_of_mem _ (show A • UpperHalfPlane.I∈realFordOrbit H UpperHalfPlane.I from ⟨A,hA,rfl⟩))
  have hbaseIm : (A • UpperHalfPlane.I).im≤R:=Complex.im_le_norm _ |>.trans hbase
  have hc:=UpperHalfPlane.dist_coe_le (A • z) (A • UpperHalfPlane.I)
  have hdist : dist (A • z) (A • UpperHalfPlane.I)=dist z UpperHalfPlane.I:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry (Matrix.SpecialLinearGroup.mapGL ℝ
      A)).dist_eq z UpperHalfPlane.I
  rw [hdist] at hc
  have hex : Real.exp (dist z UpperHalfPlane.I)≤Real.exp B:=Real.exp_le_exp.mpr (hB hz)
  have hex0 : 0≤Real.exp (dist z UpperHalfPlane.I)-1:=sub_nonneg.mpr (Real.one_le_exp_iff.mpr dist_nonneg)
  have hm:=mul_le_mul_of_nonneg_right hbaseIm hex0
  have hmR:=mul_le_mul_of_nonneg_left hex hRpos.le
  have ht:=dist_triangle ((A • z : ℍ) : ℂ) ((A • UpperHalfPlane.I : ℍ) : ℂ) 0
  rw [dist_zero_right,dist_zero_right] at ht
  linarith

/-- Labels of true non-affine circles meeting a compact set, indexed by the original Mobius group. -/
def fordCircleLabels (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (K : Set
  ℍ) : Set H :=
  {g | ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g.val ∧
    A 1 0≠0 ∧
    ∃z∈K,‖realSLDenominator A z‖=1}

theorem fordCircleLabels_finite (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞)
    (K : Set ℍ) (hK : IsCompact K) : (fordCircleLabels H K).Finite := by
  by_cases hne : K.Nonempty
  · obtain ⟨p,hp,hmin⟩:=hK.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
    obtain ⟨R,_hR,hbound⟩:=realFordOrbit_uniform_bound H hsep K hK
    let J:={w : ℍ | ‖(w : ℂ)‖≤R ∧ p.im≤w.im}
    have hJ : IsCompact J:=halfPlane_norm_slab_isCompact R p.im p.im_pos
    let Q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' K∪_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed '' J
    have hQ : IsCompact Q:=(hK.image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous).union (hJ.image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous)
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteMobius_isDiscontinuous_H3 H hd Q hQ).subset
    intro g hg
    obtain ⟨A,hAg,_hc,z,hz,hden⟩:=hg
    have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H:=hAg ▸ g.property
    have him : (A • z).im=z.im:=by
      rw [realSL_im_action,Complex.normSq_eq_norm_sq,hden,one_pow,div_one]
    have hzJ : A • z∈J:=⟨hbound A hA z hz,by rw [him];exact hmin hz⟩
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed (A •
      z),⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z,Or.inl ⟨z,hz,rfl⟩,?_⟩,
      Or.inr ⟨A • z,hzJ,rfl⟩⟩
    change g.val • _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed (A • z)
    rw [←hAg,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL]
  · have he : K=∅:=not_nonempty_iff_eq_empty.mp hne
    have hlabels : fordCircleLabels H K=∅:=by
      ext g
      simp [fordCircleLabels,he]
    rw [hlabels]
    exact finite_empty


theorem realSLDenominator_norm_eq_of_mobius_eq {A B : Matrix.SpecialLinearGroup (Fin 2) ℝ}
    (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (z : ℍ) :
    ‖realSLDenominator A z‖=‖realSLDenominator B z‖ := by
  have hz : A • z=B • z:=by
    apply UpperHalfPlane.coe_injective
    apply OnePoint.coe_injective
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A
      z,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action B z,he]
  have him:=congrArg UpperHalfPlane.im hz
  rw [realSL_im_action,realSL_im_action] at him
  have hA : Complex.normSq (realSLDenominator A z)≠0:=
    UpperHalfPlane.normSq_denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ A) z.im_ne_zero
  have hB : Complex.normSq (realSLDenominator B z)≠0:=
    UpperHalfPlane.normSq_denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ B) z.im_ne_zero
  have heq:=(div_eq_div_iff hA hB).mp him
  have hs : Complex.normSq (realSLDenominator A z)=Complex.normSq (realSLDenominator B z):=
    (mul_left_cancel₀ z.im_ne_zero heq).symm
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq] at hs
  nlinarith [norm_nonneg (realSLDenominator A z),norm_nonneg (realSLDenominator B z)]

/-- The labels are the actual original transformations which possess a non-affine real lift. -/
abbrev FordCircleIndex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :=
  {g : H // ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    A=g.val ∧ A 1 0≠0}

def fordLabelLift {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (g : FordCircleIndex
  H) : Matrix.SpecialLinearGroup (Fin 2) ℝ:=
  g.property.choose

theorem fordLabelLift_projection {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (g :
  FordCircleIndex H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (fordLabelLift g)=g.val.val:=g.property.choose_spec.1

theorem fordLabelLift_nonaffine {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (g :
  FordCircleIndex H) :
    fordLabelLift g 1 0≠0:=g.property.choose_spec.2

/-- The literal strict common exterior, with no vertical-strip convention. -/
def strictFordRegion (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Set ℍ :=
  {z | ∀A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H→A 1
    0≠0→1<‖realSLDenominator A z‖}

theorem strictFordRegion_mem_iff_index (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (z : ℍ) :
    z∈strictFordRegion H ↔ ∀g : FordCircleIndex H,1<‖realSLDenominator (fordLabelLift g) z‖ := by
  constructor
  · intro hz g
    exact hz _ (fordLabelLift_projection g ▸ g.val.property) (fordLabelLift_nonaffine g)
  · intro hz A hA hc
    let g : FordCircleIndex H:=⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,⟨A,rfl,hc⟩⟩
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (fordLabelLift
      g)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A:=fordLabelLift_projection g
    rw [←realSLDenominator_norm_eq_of_mobius_eq he z]
    exact hz g

theorem fordLabel_compact_hits_finite (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞)
    (K : Set ℍ) (hK : IsCompact K) :
    {g : FordCircleIndex H | ∃z∈K,‖realSLDenominator (fordLabelLift g) z‖=1}.Finite := by
  have hf : {g : FordCircleIndex H | g.val∈fordCircleLabels H K}.Finite:=
    (fordCircleLabels_finite H hd hsep K hK).preimage Subtype.val_injective.injOn
  apply hf.subset
  intro g hg
  exact ⟨fordLabelLift g,fordLabelLift_projection g,fordLabelLift_nonaffine g,hg⟩

theorem realSLDenominator_norm_continuous (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Continuous (fun z : ℍ=>‖realSLDenominator A z‖) := by
  unfold realSLDenominator UpperHalfPlane.denom
  fun_prop

/-- Local finiteness of the actual circle labels proves openness of their strict common exterior. -/
theorem strictFordRegion_isOpen (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) :
    IsOpen (strictFordRegion H) := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  let K:=Metric.closedBall x 1
  let J:={g : FordCircleIndex H | ∃z∈K,‖realSLDenominator (fordLabelLift g) z‖=1}
  have hJ : J.Finite:=fordLabel_compact_hits_finite H hd hsep K (isCompact_closedBall _ _)
  have hN : (⋂g∈J,{z : ℍ | 1<‖realSLDenominator (fordLabelLift g) z‖})∈𝓝 x:=by
    apply (biInter_mem hJ).mpr
    intro g _hg
    exact (isOpen_lt continuous_const (realSLDenominator_norm_continuous _)).mem_nhds
      ((strictFordRegion_mem_iff_index H x).mp hx g)
  apply mem_of_superset (inter_mem (Metric.closedBall_mem_nhds x (by norm_num : (0:ℝ)<1)) hN)
  intro z hz
  apply (strictFordRegion_mem_iff_index H z).mpr
  intro g
  by_cases hg : g∈J
  · exact mem_iInter₂.mp hz.2 g hg
  · by_contra hle
    have hpre := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_metric_closedBall x 1).isPreconnected.image
      (fun u : ℍ=>‖realSLDenominator (fordLabelLift g) u‖)
      (realSLDenominator_norm_continuous _).continuousOn
    have hzI:=mem_image_of_mem (fun u : ℍ=>‖realSLDenominator (fordLabelLift g) u‖) hz.1
    have hxI:=mem_image_of_mem (fun u : ℍ=>‖realSLDenominator (fordLabelLift g) u‖)
      (Metric.mem_closedBall_self (x:=x) (by norm_num : (0:ℝ)≤1))
    obtain ⟨u,hu,he⟩:=hpre.ordConnected.out hzI hxI
      (show (1:ℝ)∈Icc ‖realSLDenominator (fordLabelLift g) z‖ ‖realSLDenominator (fordLabelLift g) x‖ from
        ⟨le_of_not_gt hle,((strictFordRegion_mem_iff_index H x).mp hx g).le⟩)
    exact hg ⟨u,hu,he⟩


def fordCircleMirror (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1
  0≠0) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (-A 1 1/A 1 0) (1/|A 1 0|) (div_pos zero_lt_one
    (abs_pos.mpr hc))

theorem realSLDenominator_norm_factor (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) (z : ℍ) :
    ‖realSLDenominator A z‖=|A 1 0| *‖(z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)‖ := by
  have hcC : (A 1 0 : ℂ)≠0:=Complex.ofReal_ne_zero.mpr hc
  have he : realSLDenominator A z=(A 1 0 : ℂ)*((z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)):=by
    change (A 1 0 : ℂ)*(z : ℂ)+(A 1 1 : ℂ)=_
    push_cast
    field_simp
    ring
  rw [he,norm_mul,Complex.norm_real,Real.norm_eq_abs]

theorem fordCircleMirror_carrier (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hc : A 1 0≠0) :
    (fordCircleMirror A hc).carrier={z | ‖realSLDenominator A z‖=1} := by
  ext z
  change ‖(z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)‖=1/|A 1 0| ↔ ‖realSLDenominator A z‖=1
  rw [realSLDenominator_norm_factor A hc,eq_div_iff (abs_pos.mpr hc).ne']
  rw [mul_comm]

theorem realSLDenominator_strict_circle (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hc : A 1 0≠0) : {z : ℍ | 1<‖realSLDenominator A z‖}=
      {z : ℍ | 1/|A 1 0|<‖(z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)‖} := by
  ext z
  change (1<‖realSLDenominator A z‖) ↔ (1/|A 1 0|<‖(z : ℂ)-((-A 1 1/A 1 0 : ℝ) : ℂ)‖)
  rw [realSLDenominator_norm_factor A hc,div_lt_iff₀ (abs_pos.mpr hc)]
  rw [mul_comm]

theorem strictFordRegion_hConvex (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (strictFordRegion H) := by
  have he : strictFordRegion H=⋂A : Matrix.SpecialLinearGroup (Fin
    2) ℝ,⋂_hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H,
      ⋂hc : A 1 0≠0,{z : ℍ | 1<‖realSLDenominator A z‖}:=by ext z; simp [strictFordRegion]
  rw [he]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter
  intro A
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter
  intro _hA
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.iInter
  intro hc
  rw [realSLDenominator_strict_circle A hc]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_outside_circle _ _ (div_pos zero_lt_one (abs_pos.mpr
    hc))

theorem realSLDenominator_normSq (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    Complex.normSq (realSLDenominator A z)=(A 1 0*z.re+A 1 1)^2+(A 1 0*z.im)^2 := by
  change Complex.normSq ((A 1 0 : ℂ)*(z : ℂ)+(A 1 1 : ℂ))=_
  simp only [Complex.normSq_apply,Complex.add_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.add_im,Complex.mul_im,
    add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring


/-- Raising a finite point along its actual vertical geodesic. -/
def fordRaise (w : ℍ) (t : ℝ) : ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe w.re (w.im*Real.exp
  t) (mul_pos w.im_pos (Real.exp_pos _))

theorem fordRaise_zero (w : ℍ) : fordRaise w 0=w := by
  apply UpperHalfPlane.ext
  apply Complex.ext
  · rfl
  · change w.im*Real.exp 0=w.im
    rw [Real.exp_zero,mul_one]

theorem fordRaise_continuous (w : ℍ) : Continuous (fordRaise w) := by
  apply UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun t : ℝ=>(⟨w.re,w.im*Real.exp t⟩ : ℂ))
  have he : (fun t : ℝ=>(⟨w.re,w.im*Real.exp t⟩ : ℂ))=
      (fun t : ℝ=>(w.re : ℂ)+((w.im*Real.exp t : ℝ) : ℂ)*Complex.I):=by
    funext t
    apply Complex.ext
    · simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
      ring
    · simp only [Complex.add_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
      ring
  rw [he]
  fun_prop

theorem fordRaise_im_gt (w : ℍ) {t : ℝ} (ht : 0<t) : w.im<(fordRaise w t).im := by
  change w.im<w.im*Real.exp t
  have he:=Real.one_lt_exp_iff.mpr ht
  nlinarith [w.im_pos]

theorem fordRaise_mem_strict (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (w : ℍ)
    (hw : w∈mobiusFordCircleExterior H) {t : ℝ} (ht : 0<t) : fordRaise w t∈strictFordRegion H := by
  intro A hA hc
  have hweak : 1≤‖realSLDenominator A w‖:=(realSLDenominator_ge_one_iff_circle_exterior A hc w).mpr (hw A hA hc)
  have hweakSq : 1≤Complex.normSq (realSLDenominator A w):=by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith only [hweak]
  have hy:=fordRaise_im_gt w ht
  have hys : 0<(fordRaise w t).im^2-w.im^2:=by nlinarith [w.im_pos]
  have hcs : 0<(A 1 0)^2:=sq_pos_of_ne_zero hc
  have he : Complex.normSq (realSLDenominator A (fordRaise w t))-Complex.normSq (realSLDenominator A w)=
      (A 1 0)^2*((fordRaise w t).im^2-w.im^2):=by
    rw [realSLDenominator_normSq,realSLDenominator_normSq]
    change (A 1 0*w.re+A 1 1)^2+(A 1 0*(w.im*Real.exp t))^2-
      ((A 1 0*w.re+A 1 1)^2+(A 1 0*w.im)^2)=
        (A 1 0)^2*((w.im*Real.exp t)^2-w.im^2)
    ring
  have hsq : 1<Complex.normSq (realSLDenominator A (fordRaise w t)):=by
    have hp:=mul_pos hcs hys
    linarith
  rw [Complex.normSq_eq_norm_sq] at hsq
  nlinarith [norm_nonneg (realSLDenominator A (fordRaise w t))]

theorem closure_strictFordRegion_subset (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    closure (strictFordRegion H)⊆mobiusFordCircleExterior H := by
  intro w hw A hA hc
  apply (realSLDenominator_ge_one_iff_circle_exterior A hc w).mp
  have hsub : strictFordRegion H⊆{z : ℍ | 1≤‖realSLDenominator A z‖}:=fun z hz=>(hz A hA hc).le
  exact closure_minimal hsub (isClosed_le continuous_const (realSLDenominator_norm_continuous A)) hw

/-- The true closure is the literal closed circle exterior; vertical rays supply the missing boundary points. -/
theorem closure_strictFordRegion (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    closure (strictFordRegion H)=mobiusFordCircleExterior H := by
  apply Subset.antisymm (closure_strictFordRegion_subset H)
  intro w hw
  have ht : Tendsto (fordRaise w) (𝓝[>] (0:ℝ)) (𝓝 w):=by
    have hc : Tendsto (fordRaise w) (𝓝 (0:ℝ)) (𝓝 (fordRaise w 0)):=
      (fordRaise_continuous w).continuousAt.tendsto
    simpa only [fordRaise_zero] using hc.mono_left (nhdsWithin_le_nhds (s:=Ioi (0:ℝ)))
  apply mem_closure_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact fordRaise_mem_strict H w hw ht

theorem strictFordRegion_nonempty (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) :
    (strictFordRegion H).Nonempty := by
  obtain ⟨B,_hB,_hheight,hBext⟩:=exists_ford_exterior_of_separating_infty H hd hsep UpperHalfPlane.I
  exact ⟨fordRaise (B • UpperHalfPlane.I) 1,fordRaise_mem_strict H _ hBext (by norm_num)⟩

theorem strictFordRegion_isConnected (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) :
    IsConnected (strictFordRegion H) :=
  ⟨strictFordRegion_nonempty H hd hsep,(strictFordRegion_hConvex H).isPreconnected⟩

theorem strictFordRegion_frontier_subset (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) :
    frontier (strictFordRegion H)⊆⋃g : FordCircleIndex H,(fordCircleMirror (fordLabelLift g) (fordLabelLift_nonaffine g)).carrier := by
  intro w hw
  have hweak:=closure_strictFordRegion_subset H (frontier_subset_closure hw)
  have hn : w∉strictFordRegion H:=by simpa only [(strictFordRegion_isOpen H hd hsep).interior_eq] using hw.2
  have hex : ∃g : FordCircleIndex H,¬1<‖realSLDenominator (fordLabelLift g) w‖:=by
    by_contra he
    push Not at he
    exact hn ((strictFordRegion_mem_iff_index H w).mpr he)
  obtain ⟨g,hg⟩:=hex
  refine mem_iUnion.mpr ⟨g,?_⟩
  rw [fordCircleMirror_carrier]
  change ‖realSLDenominator (fordLabelLift g) w‖=1
  have hle : 1≤‖realSLDenominator (fordLabelLift g) w‖:=
    (realSLDenominator_ge_one_iff_circle_exterior _ (fordLabelLift_nonaffine g) w).mpr
      (hweak _ (fordLabelLift_projection g ▸ g.val.property) (fordLabelLift_nonaffine g))
  exact le_antisymm (le_of_not_gt hg) hle

/-- The actual frontier is null for the genuine hyperbolic density measure. -/
theorem strictFordRegion_frontier_volume_zero (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hsep :
      HasSeparatingMobiusNeighborhood H ∞) :
    volume (frontier (strictFordRegion H))=0 := by
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H hd
  exact measure_mono_null (strictFordRegion_frontier_subset H hd hsep)
    (measure_iUnion_null (fun g : FordCircleIndex H=>(fordCircleMirror (fordLabelLift g) (fordLabelLift_nonaffine
      g)).volume_zero))

end
end LowDimensionalTopology.Geometry.Fuchsian
