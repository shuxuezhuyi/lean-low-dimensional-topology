module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.NativeAxisStabilizers
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.CyclicAxisFundamentalDomains
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

/-- The second source strip keeps the entire half-turn extension, by choosing one side of the axis. -/
def dihedralAxisRightAnnulus (l : ℝ) : Set ℍ := dilationAxisAnnulus l ∩ {z : ℍ | 0 < z.re}

theorem axis_rightHalfPlane_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z : ℍ | 0 < z.re} := by
  let m := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 1 1 zero_lt_one
  have hm : 0 < m.re := by norm_num [m,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_vertical_gt 0 m hm]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHHalfPlane_hConvex _ _ hm.ne'

theorem dihedralAxisRightAnnulus_hConvex (l : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (dihedralAxisRightAnnulus l) := by
  intro x hx y hy z hz
  exact ⟨dilationAxisAnnulus_hConvex l x hx.1 y hy.1 hz,axis_rightHalfPlane_hConvex x hx.2 y hy.2 hz⟩

theorem dihedralAxisRightAnnulus_isOpen (l : ℝ) : IsOpen (dihedralAxisRightAnnulus l) :=
  (dilationAxisAnnulus_isOpen l).inter (isOpen_lt continuous_const UpperHalfPlane.continuous_re)

theorem closure_axis_rightHalfPlane : closure {z : ℍ | 0 < z.re} = {z : ℍ | 0 ≤ z.re} := by
  change closure (UpperHalfPlane.re ⁻¹' Ioi 0) = _
  rw [←UpperHalfPlane.isOpenMap_re.preimage_closure_eq_closure_preimage UpperHalfPlane.continuous_re,closure_Ioi]
  rfl

theorem dihedralAxisRightAnnulus_nonempty (l : ℝ) (hl : 0 < l) : (dihedralAxisRightAnnulus l).Nonempty := by
  let w := _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam (l/2)
  have hwD : w ∈ dilationAxisAnnulus l := by
    rw [mem_dilationAxisAnnulus_iff]
    simp only [w,_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_norm,Real.log_exp]
    constructor <;> linarith
  have hwR : w ∈ closure {z : ℍ | 0 < z.re} := by
    rw [closure_axis_rightHalfPlane]
    change 0 ≤ w.re
    simp [w,_root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam]
  have hh := (mem_closure_iff_nhds.mp hwR) (dilationAxisAnnulus l) ((dilationAxisAnnulus_isOpen l).mem_nhds hwD)
  exact hh

theorem closure_dihedralAxisRightAnnulus (l : ℝ) (hl : 0 < l) :
    closure (dihedralAxisRightAnnulus l) = {z : ℍ | 1 ≤ ‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖ ≤ Real.exp l ∧ 0 ≤ z.re} := by
  rw [dihedralAxisRightAnnulus,hConvex_open_closure_inter (dilationAxisAnnulus_hConvex l)
    axis_rightHalfPlane_hConvex (dilationAxisAnnulus_isOpen l)
    (isOpen_lt continuous_const UpperHalfPlane.continuous_re) (dihedralAxisRightAnnulus_nonempty l hl),
    closure_dilationAxisAnnulus l hl,closure_axis_rightHalfPlane]
  ext z
  simp only [mem_inter_iff,mem_ofPred_eq,and_assoc]

/-- The weak literal annulus is precisely the weak real logarithmic strip. -/
theorem mem_closure_dilationAxisAnnulus_iff (l : ℝ) (hl : 0 < l) (z : ℍ) :
    z ∈ closure (dilationAxisAnnulus l) ↔ 0 ≤ Real.log ‖(z:ℂ)‖ ∧ Real.log ‖(z:ℂ)‖ ≤ l := by
  rw [closure_dilationAxisAnnulus l hl,Real.log_nonneg_iff (norm_pos_iff.mpr z.ne_zero),
    Real.log_le_iff_le_exp (norm_pos_iff.mpr z.ne_zero)]
  rfl

/-- The literal positive radial subgroup alone supplies closed-annulus representatives inside any larger original group. -/
theorem HalfPlaneFuchsianGroup.dilationAnnulus_zpow_cover {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H) (z : ℍ) :
    letI := P.nativeAction
    ∃ n : ℤ, (⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩ : H) • z ∈ closure (dilationAxisAnnulus l) := by
  let nativeDihedralRadialAction := P.nativeAction
  let n : ℤ := -⌊Real.log ‖(z:ℂ)‖/l⌋
  let g : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩
  refine ⟨n,?_⟩
  rw [mem_closure_dilationAxisAnnulus_iff l hl]
  change 0 ≤ Real.log ‖((g • z : ℍ):ℂ)‖ ∧ Real.log ‖((g • z : ℍ):ℂ)‖ ≤ l
  rw [P.dilation_element_logNorm l g n rfl z]
  have h0 := Int.sub_floor_div_mul_nonneg (Real.log ‖(z:ℂ)‖) hl
  have h1 := Int.sub_floor_div_mul_lt (Real.log ‖(z:ℂ)‖) hl
  dsimp [n]
  push_cast
  constructor <;> linarith

/-- Positive dilation preserves the exact sign of the native real coordinate. -/
theorem HalfPlaneFuchsianGroup.dilation_element_re {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (g : H) (n : ℤ) (he : g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n) (z : ℍ) :
    letI := P.nativeAction
    (g • z).re = Real.exp ((n:ℝ)*l)*z.re := by
  let nativeDihedralReAction := P.nativeAction
  change (((g • z : ℍ):ℂ).re) = _
  rw [P.dilation_element_coe l g n he z,Complex.mul_re]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,UpperHalfPlane.coe_re]

/-- A positive dilation power cannot identify two different points in the actual open annulus. -/
theorem HalfPlaneFuchsianGroup.dilation_power_interior_unique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (g : H) (n : ℤ)
    (he : g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n) {x y : ℍ}
    (hx : x ∈ dilationAxisAnnulus l) (hy : y ∈ dilationAxisAnnulus l)
    (hxy : letI := P.nativeAction; g • y = x) : x = y := by
  let nativeDihedralUniquePowerAction := P.nativeAction
  have hlog := P.dilation_element_logNorm l g n he y
  rw [hxy] at hlog
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
  have hg1 : g = 1 := Subtype.ext (by rw [he,hn0,zpow_zero];rfl)
  simpa only [hg1,one_smul] using hxy.symm

/-- The actual half-turn extension covers the half-plane by the closed right annulus. -/
theorem HalfPlaneFuchsianGroup.dihedralAnnulus_closure_meetsEveryOrbit {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (s : H) (haxis : s.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : s.val.val (0:ℂ) = ∞ ∧ s.val.val ∞ = (0:ℂ)) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit H ℍ (closure (dihedralAxisRightAnnulus l)) := by
  let nativeDihedralCoverAction := P.nativeAction
  have hcover {u : ℍ} (hu : 0 ≤ u.re) : ∃ g : H, g • u ∈ closure (dihedralAxisRightAnnulus l) := by
    obtain ⟨n,hn⟩ := P.dilationAnnulus_zpow_cover l hl hfH u
    let a : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩
    have hnr : 0 ≤ (a • u).re := by
      rw [P.dilation_element_re l a n rfl u]
      exact mul_nonneg (Real.exp_pos _).le hu
    refine ⟨a,?_⟩
    rw [closure_dihedralAxisRightAnnulus l hl]
    have hh : 1 ≤ ‖((a • u : ℍ):ℂ)‖ ∧ ‖((a • u : ℍ):ℂ)‖ ≤ Real.exp l := by
      change a • u ∈ closure (dilationAxisAnnulus l) at hn
      rw [closure_dilationAxisAnnulus l hl] at hn
      exact hn
    exact ⟨hh.1,hh.2,hnr⟩
  intro z
  by_cases hz : 0 ≤ z.re
  · exact hcover hz
  · have hspos : 0 < (s • z).re := (P.axis_exchange_re_sign s haxis hswap z).mpr (lt_of_not_ge hz)
    obtain ⟨a,ha⟩ := hcover hspos.le
    exact ⟨a*s,by simpa only [mul_smul] using ha⟩

/-- Both actual normal-form families give uniqueness inside the genuine right annulus. -/
theorem HalfPlaneFuchsianGroup.dihedralAnnulus_orbit_unique {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (s : H) (haxis : s.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : s.val.val (0:ℂ) = ∞ ∧ s.val.val ∞ = (0:ℂ)) (hs2 : s.val^2 = 1)
    (hform : ∀ g : H, ∃ n : ℤ, g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*s.val) :
    letI := P.nativeAction
    ∀ x ∈ dihedralAxisRightAnnulus l, ∀ y ∈ dihedralAxisRightAnnulus l,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ x = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ y → x = y := by
  let nativeDihedralOrbitUniqueAction := P.nativeAction
  intro x hx y hy hxy
  obtain ⟨g,hgy⟩ := (Quotient.exact hxy : MulAction.orbitRel H ℍ x y)
  change g • y = x at hgy
  obtain ⟨n,hpower | hswapPower⟩ := hform g
  · exact P.dilation_power_interior_unique l hl g n hpower hx.1 hy.1 hgy
  · let a : H := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n,H.zpow_mem hfH n⟩
    have hg : g = a*s := Subtype.ext hswapPower
    have hss : s*s = 1 := by
      apply Subtype.ext
      change s.val*s.val = 1
      simpa only [pow_two] using hs2
    have hspos : 0 < (s • (s • y)).re := by
      rw [←mul_smul,hss,one_smul]
      exact hy.2
    have hsneg : (s • y).re < 0 := (P.axis_exchange_re_sign s haxis hswap (s • y)).mp hspos
    have hxneg : x.re < 0 := by
      rw [←hgy,hg,mul_smul,P.dilation_element_re l a n rfl]
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hsneg
    exact (hxneg.not_ge hx.2.le).elim

/-- The complete two-family original axis-stabilizer action has the literal source right-annulus fundamental domain. -/
theorem HalfPlaneFuchsianGroup.dihedralAnnulus_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hfH :
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ H)
    (s : H) (haxis : s.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)
    (hswap : s.val.val (0:ℂ) = ∞ ∧ s.val.val ∞ = (0:ℂ)) (hs2 : s.val^2 = 1)
    (hform : ∀ g : H, ∃ n : ℤ, g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g.val =
      _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*s.val) :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume (dihedralAxisRightAnnulus l) := by
  let nativeDihedralFundamentalAction := P.nativeAction
  refine ⟨dihedralAxisRightAnnulus_isOpen l,
    ⟨dihedralAxisRightAnnulus_nonempty l hl,(dihedralAxisRightAnnulus_hConvex l).isPreconnected⟩,?_,
    parabolicFord_hConvex_frontier_volume_zero (dihedralAxisRightAnnulus_hConvex l)⟩
  exact exists_fundamentalSet_between _ _ subset_closure
    (P.dihedralAnnulus_closure_meetsEveryOrbit l hl hfH s haxis hswap)
    (P.dihedralAnnulus_orbit_unique l hl hfH s haxis hswap hs2 hform)

/-- The full original imaginary-axis stabilizer acts in the same native model with inherited genuine discreteness. -/
theorem HalfPlaneFuchsianGroup.axisStabilizerData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup
      H) : HalfPlaneFuchsianGroup (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) where
  preserves g := P.preserves ⟨g.val,g.property.1⟩
  discrete := by
    let nativeAxisFullOriginalDiscrete : DiscreteTopology H := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.subgroup_discrete (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer_le H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis)

/-- Both source strips are derived for the actual full stabilizer of a primitive dilation, without assuming its normal form or a fundamental domain. -/
theorem HalfPlaneFuchsianGroup.primitive_dilation_axis_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (l : ℝ) (hl : 0 < l) (hp : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l)) :
    letI := P.axisStabilizerData.nativeAction
    ∃ D : Set ℍ, _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) ℍ volume D ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex D ∧ (D = dilationAxisAnnulus l ∨ D = dihedralAxisRightAnnulus l) := by
  let N := P.axisStabilizerData
  let nativeAxisFullFundamentalAction := N.nativeAction
  have hfK : _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis :=
    ⟨hp.mem,stableAxisDilation_image_axis l⟩
  rcases P.primitive_dilation_axis_stabilizer l hp with hcyclic | ⟨s,hsK,_hs0,_hsi,hs2,_hsE,hform⟩
  · exact ⟨dilationAxisAnnulus l,N.dilationAnnulus_fundamental l hl hcyclic,
      dilationAxisAnnulus_hConvex l,Or.inl rfl⟩
  · let sK : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := ⟨s,hsK⟩
    have hsaxis : sK.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis := hsK.2
    have hswap : sK.val.val (0:ℂ) = ∞ ∧ sK.val.val ∞ = (0:ℂ) := ⟨_hs0,_hsi⟩
    have hword (g : _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedImaginaryAxis) :
        ∃ n : ℤ, g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n ∨ g.val = _root_.LowDimensionalTopology.Geometry.Surfaces.stableAxisDilation l^n*sK.val :=
      (hform g.val).mp g.property
    exact ⟨dihedralAxisRightAnnulus l,N.dihedralAnnulus_fundamental l hl hfK sK hsaxis hswap hs2 hword,
      dihedralAxisRightAnnulus_hConvex l,Or.inr rfl⟩

end LowDimensionalTopology.Geometry.Fuchsian
