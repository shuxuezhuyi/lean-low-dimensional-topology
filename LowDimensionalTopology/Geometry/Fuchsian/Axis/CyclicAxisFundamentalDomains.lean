module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.AxisDistanceHalfPlanes
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.StableSets
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped OnePoint Pointwise UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The source's actual annular half-plane strip, before any fundamental-domain conclusion. -/
def dilationAxisAnnulus (l : ℝ) : Set ℍ := {z | 1 < ‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖ < Real.exp l}

/-- Every actual power has its literal positive real dilation formula at every finite point. -/
theorem stableAxisDilation_zpow_coe (l : ℝ) (n : ℤ) (z : ℂ) :
    (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n).val z = (((Real.exp ((n:ℝ)*l):ℝ):ℂ)*z:ℂ) := by
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom _ ^ n).val _ = _
  rw [←map_zpow]
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling ((Units.mk0 ((Real.exp l:ℝ):ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero l)))^n)).val z = _
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
  simp only [Units.val_zpow_eq_zpow_val,Units.val_mk0]
  apply OnePoint.coe_injective
  congr 1
  rw [Complex.ofReal_exp,Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_intCast,Complex.exp_int_mul]

theorem HalfPlaneFuchsianGroup.dilation_element_coe {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (g : H) (n : ℤ) (he : g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n) (z : ℍ) :
    letI := P.nativeAction
    ((g • z : ℍ):ℂ) = (Real.exp ((n:ℝ)*l):ℂ)*(z:ℂ) := by
  let nativeDilationFormulaAction := P.nativeAction
  apply OnePoint.coe_injective
  change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g • z) = _
  rw [←P.nativeAction_boundary,he]
  exact stableAxisDilation_zpow_coe l n (z:ℂ)

theorem HalfPlaneFuchsianGroup.dilation_element_logNorm {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (g : H) (n : ℤ) (he : g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n) (z : ℍ) :
    letI := P.nativeAction
    Real.log ‖((g • z : ℍ):ℂ)‖ = (n:ℝ)*l+Real.log ‖(z:ℂ)‖ := by
  let nativeDilationLogAction := P.nativeAction
  rw [P.dilation_element_coe l g n he z,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),Real.log_mul (Real.exp_ne_zero _) (norm_ne_zero_iff.mpr z.ne_zero),Real.log_exp]

/-- The literal annulus is hyperbolically convex, with both real-centred boundary geodesics retained. -/
theorem dilationAxisAnnulus_hConvex (l : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (dilationAxisAnnulus l) := by
  intro x hx y hy z hz
  have hout := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_outside_circle 0 1 zero_lt_one x (by simpa using hx.1) y (by simpa using hy.1) hz
  have hin := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_inside_real_circle 0 (Real.exp l) (Real.exp_pos
    l)
    x (by simpa using hx.2) y (by simpa using hy.2) hz
  exact ⟨by simpa using hout,by simpa using hin⟩

theorem dilationAxisAnnulus_isOpen (l : ℝ) : IsOpen (dilationAxisAnnulus l) :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_coe.norm).inter
    (isOpen_lt UpperHalfPlane.continuous_coe.norm continuous_const)

/-- The full genuine closure is exactly the source closed annulus; this is derived from Mathlib's actual open norm map. -/
theorem closure_dilationAxisAnnulus (l : ℝ) (hl : 0 < l) :
    closure (dilationAxisAnnulus l) = {z : ℍ | 1 ≤ ‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖ ≤ Real.exp l} := by
  have hexp : 1 < Real.exp l := Real.one_lt_exp_iff.mpr hl
  change closure ((fun z : ℍ => ‖(z:ℂ)‖) ⁻¹' Ioo 1 (Real.exp l)) = _
  rw [←UpperHalfPlane.isOpenMap_norm.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_coe.norm,
    closure_Ioo hexp.ne]
  rfl

/-- The actual radial fundamental strip in logarithmic norm coordinates. -/
theorem mem_dilationAxisAnnulus_iff (l : ℝ) (z : ℍ) :
    z ∈ dilationAxisAnnulus l ↔ 0 < Real.log ‖(z:ℂ)‖ ∧ Real.log ‖(z:ℂ)‖ < l := by
  rw [Real.log_pos_iff (norm_nonneg _),Real.log_lt_iff_lt_exp (norm_pos_iff.mpr z.ne_zero)]
  rfl

/-- The actual logarithmic strip is nonempty for every positive dilation length. -/
theorem dilationAxisAnnulus_nonempty (l : ℝ) (hl : 0 < l) : (dilationAxisAnnulus l).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (l/2),?_⟩
  rw [mem_dilationAxisAnnulus_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_norm,Real.log_exp]
  constructor <;> linarith

/-- Every actual cyclic dilation orbit meets the literal closed annulus. -/
theorem HalfPlaneFuchsianGroup.dilationAnnulus_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l)
    (hH : H = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ (closure (dilationAxisAnnulus l)) := by
  let nativeAnnulusCoverAction := P.nativeAction
  intro z
  let n : ℤ := ⌊Real.log ‖(z:ℂ)‖/l⌋
  have hg : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^(-n) ∈ H := by
    rw [hH]
    exact (Subgroup.zpowers _).zpow_mem (Subgroup.mem_zpowers _) (-n)
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^(-n),hg⟩
  have he := P.dilation_element_logNorm l g (-n) rfl z
  have hr0 : 0 ≤ Real.log ‖((g • z : ℍ):ℂ)‖ := by
    rw [he]
    have hh := Int.sub_floor_div_mul_nonneg (Real.log ‖(z:ℂ)‖) hl
    push_cast
    dsimp [n]
    linarith
  have hr1 : Real.log ‖((g • z : ℍ):ℂ)‖ < l := by
    rw [he]
    have hh := Int.sub_floor_div_mul_lt (Real.log ‖(z:ℂ)‖) hl
    push_cast
    dsimp [n]
    linarith
  refine ⟨g,?_⟩
  rw [closure_dilationAxisAnnulus l hl]
  have hpos : 0 < ‖((g • z : ℍ):ℂ)‖ := norm_pos_iff.mpr (g • z).ne_zero
  constructor
  · calc
      1 = Real.exp 0 := Real.exp_zero.symm
      _ ≤ Real.exp (Real.log ‖((g • z : ℍ):ℂ)‖) := Real.exp_le_exp.mpr hr0
      _ = _ := Real.exp_log hpos
  · calc
      ‖((g • z : ℍ):ℂ)‖ = Real.exp (Real.log ‖((g • z : ℍ):ℂ)‖) := (Real.exp_log hpos).symm
      _ ≤ Real.exp l := Real.exp_le_exp.mpr hr1.le

/-- No two distinct interior points of the literal annulus are identified by the actual cyclic group. -/
theorem HalfPlaneFuchsianGroup.dilationAnnulus_orbit_unique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l)
    (hH : H = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    ∀ x ∈ dilationAxisAnnulus l, ∀ y ∈ dilationAxisAnnulus l,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ x = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ y → x = y := by
  let nativeAnnulusUniqueAction := P.nativeAction
  intro x hx y hy hxy
  obtain ⟨g,hgy⟩ := (Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
  change g • y = x at hgy
  have hgmem : g.val ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l) := by rw [←hH];exact g.property
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hgmem
  have he := P.dilation_element_logNorm l g n hn.symm y
  rw [hgy] at he
  have hxlog := (mem_dilationAxisAnnulus_iff l x).mp hx
  have hylog := (mem_dilationAxisAnnulus_iff l y).mp hy
  have hnlt : (n:ℝ) < 1 := by
    by_contra hnge
    have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnge)) hl.le
    nlinarith
  have hngt : (-1:ℝ) < (n:ℝ) := by
    by_contra hnle
    have hh := mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnle)) hl.le
    nlinarith
  have hnltZ : n < 1 := by exact_mod_cast hnlt
  have hngtZ : -1 < n := by exact_mod_cast hngt
  have hn0 : n = 0 := by omega
  have hg1 : g = 1 := Subtype.ext (by rw [←hn,hn0,zpow_zero];rfl)
  simpa only [hg1,one_smul] using hgy.symm

/-- The cyclic case of the actual axis-stabilizer strip is a genuine original-group hyperbolic-area fundamental domain. -/
theorem HalfPlaneFuchsianGroup.dilationAnnulus_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l)
    (hH : H = Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (dilationAxisAnnulus l) := by
  let nativeAnnulusFundamentalAction := P.nativeAction
  refine ⟨dilationAxisAnnulus_isOpen l,
    ⟨dilationAxisAnnulus_nonempty l hl,(dilationAxisAnnulus_hConvex l).isPreconnected⟩,?_,
    parabolicFord_hConvex_frontier_volume_zero (dilationAxisAnnulus_hConvex l)⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (P.dilationAnnulus_closure_meetsEveryOrbit l hl hH) (P.dilationAnnulus_orbit_unique l hl hH)

/-- Open convex planar regions with a common point have the exact closure-intersection property. -/
theorem convex_open_closure_inter {U V : Set ℂ} (hU : Convex ℝ U) (hV : Convex ℝ V)
    (hoU : IsOpen U) (hoV : IsOpen V) (hne : (U ∩ V).Nonempty) :
    closure (U ∩ V) = closure U ∩ closure V := by
  have hUI : (interior U).Nonempty := by
    rw [hoU.interior_eq]
    exact hne.mono inter_subset_left
  have hVI : (interior V).Nonempty := by
    rw [hoV.interior_eq]
    exact hne.mono inter_subset_right
  have hInt : interior (closure U ∩ closure V) = U ∩ V := by
    rw [interior_inter,hU.interior_closure_eq_interior_of_nonempty_interior hUI,
      hV.interior_closure_eq_interior_of_nonempty_interior hVI,hoU.interior_eq,hoV.interior_eq]
  have hc := (hU.closure.inter hV.closure).closure_interior_eq_closure_of_nonempty_interior
    (hInt.symm ▸ hne)
  rw [hInt,(isClosed_closure.inter isClosed_closure).closure_eq] at hc
  exact hc

/-- Genuine native Klein coordinates transport the actual closure in the open half-plane model. -/
theorem halfPlaneKlein_image_closure (S : Set ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' closure S = closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' S) ∩ Metric.ball (0:ℂ) 1 := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.closure_eq_preimage_closure_image S,
    image_preimage_eq_inter_range,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate]

/-- Genuine open hyperbolically convex regions sharing an interior point have the exact native closure intersection. -/
theorem hConvex_open_closure_inter {U V : Set ℍ} (hU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex U) (hV
  : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex V)
    (hoU : IsOpen U) (hoV : IsOpen V) (hne : (U ∩ V).Nonempty) :
    closure (U ∩ V) = closure U ∩ closure V := by
  have hUK : Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' U) := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex U).mp hU)
    simpa only [image_image,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate] using hh
  have hVK : Convex ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' V) := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex
      _).mp ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex V).mp hV)
    simpa only [image_image,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate] using hh
  have hoUK := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isOpenMap U hoU
  have hoVK := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isOpenMap V hoV
  have hneK : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' U ∩ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' V).Nonempty := by
    obtain ⟨z,hzU,hzV⟩ := hne
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z,mem_image_of_mem _
      hzU,mem_image_of_mem _ hzV⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective.image_injective
  rw [halfPlaneKlein_image_closure,Set.image_inter
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective,
    convex_open_closure_inter hUK hVK hoUK hoVK hneK,
    Set.image_inter _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective,halfPlaneKlein_image_closure,halfPlaneKlein_image_closure]
  ext z
  simp only [mem_inter_iff]
  tauto

end LowDimensionalTopology.Geometry.Fuchsian
