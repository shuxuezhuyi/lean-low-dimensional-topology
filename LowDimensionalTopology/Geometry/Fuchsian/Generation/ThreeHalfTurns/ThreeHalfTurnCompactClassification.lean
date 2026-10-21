/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnCovering
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.SmallLambdaTriangleReduction
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeDihedralChambers
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.FiniteCanonicalPolygonPoincare
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.RegularPolygon.RegularPolygonCycles
public import Mathlib.Algebra.Group.Subgroup.Finite
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
public import Mathlib.Topology.Connected.Clopen
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCompactDevelopment
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.HalfTurnExceptionalTriples
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSignatureProfile
/-!
# Compact three-half-turn groups

Concrete quadrilateral and pentagon supports supply the native side pairings.
Base and summit cycles establish local tessellation, stabilizer orders and the
actual finite-area signatures. Normalization then transports the small-parameter
classification to the original three-center action.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false
set_option maxHeartbeats 1200000
open Set Filter Topology MeasureTheory InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine open support polygon satisfies precisely the four strict
Klein inequalities of the concrete half-turn side-circle quadrilateral. -/
theorem halfTurnTrapezoid_interior_iff (a b s : ℝ) (ha : 0<a) (ha1 : a<1)
    (hs : 0<s) (hs1 : s<1) (hd : 0<a-b*s) (htop : s^2+(b*s-a)^2<1) (z : 𝔻) :
    z∈(halfTurnTrapezoidSupportData a b s ha ha1 hs hs1 hd htop).toDiscPolygon.interior ↔
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z).im<0 ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z).re<s ∧
        b*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z).re-(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z).im<a ∧ 0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z).re := by
  change z∈(halfTurnTrapezoidSupportData a b s ha ha1 hs hs1 hd htop).toCenteredData.toDiscPolygon.interior ↔_
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.CenteredDiscPolygonSupportData.toDiscPolygon_interior]
  change (∀i : Fin 4,inner ℝ (halfTurnTrapezoidUnitNormal b i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)<
    halfTurnTrapezoidUnitOffset a b s i) ↔_
  have he (i : Fin 4) : inner ℝ (halfTurnTrapezoidUnitNormal b i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)<
      halfTurnTrapezoidUnitOffset a b s i ↔
      inner ℝ (halfTurnTrapezoidRawNormals b i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z)<halfTurnTrapezoidRawOffsets a s i:=by
    rw [←sub_neg,halfTurnTrapezoid_unit_evaluate]
    rw [div_lt_iff₀ (norm_pos_iff.mpr (halfTurnTrapezoid_raw_normal_ne_zero b i)),zero_mul]
    exact sub_neg
  simp_rw [he]
  rw [Fin.forall_fin_succ]
  simp only [Fin.forall_fin_succ]
  norm_num [halfTurnTrapezoidRawNormals,halfTurnTrapezoidRawOffsets,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,mul_comm]

/-- The original native open polygon is exactly the strict radial/circular
region; its openness is derived from its actual Jordan support model. -/
theorem halfTurnQuadCanonical_native_interior (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) (z : ℍ) :
    z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
      (halfTurnQuadCanonical_finite k c hk hc)).interior ↔
      1<‖(z : ℂ)‖ ∧ ‖(z : ℂ)‖<k ∧ 0<z.re ∧
        0<z.re^2+z.im^2-2*c*z.re+k := by
  have hk0 : 0<k:=by linarith only [hk]
  have hc0 : 0<c:=by linarith only [hk,hc]
  have hN : 0<z.re^2+z.im^2+1:=by positivity
  have hkden : 0<k^2+1:=by positivity
  have hn : ‖(z : ℂ)‖^2=z.re^2+z.im^2:=by
    rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two]
  have haxis : (-2*z.re)/(z.re^2+z.im^2+1)<0 ↔ 0<z.re:=by
    rw [div_lt_iff₀ hN,zero_mul]
    constructor <;> intro hh <;> linarith only [hh]
  have hrad0 : 0<(z.re^2+z.im^2-1)/(z.re^2+z.im^2+1) ↔ 1<‖(z : ℂ)‖:=by
    rw [lt_div_iff₀ hN]
    constructor
    · intro hh
      have hh' : 1<‖(z : ℂ)‖^2:=by nlinarith only [hh,hn]
      nlinarith only [hh',norm_nonneg (z : ℂ)]
    · intro hh
      nlinarith only [hh,hn]
  have hrad1 : (z.re^2+z.im^2-1)/(z.re^2+z.im^2+1)<halfTurnQuadKleinS k ↔
      ‖(z : ℂ)‖<k:=by
    rw [halfTurnQuadKleinS,div_lt_div_iff₀ hN hkden]
    constructor
    · intro hh
      have hh' : ‖(z : ℂ)‖^2<k^2:=by nlinarith only [hh,hn]
      nlinarith only [hh',norm_nonneg (z : ℂ),hk0]
    · intro hh
      have hh' : ‖(z : ℂ)‖^2<k^2:=sq_lt_sq₀ (norm_nonneg _) hk0.le |>.mpr hh
      nlinarith only [hh',hn]
  have hcircle : halfTurnQuadKleinB k c*((z.re^2+z.im^2-1)/(z.re^2+z.im^2+1))-
      (-2*z.re)/(z.re^2+z.im^2+1)<halfTurnQuadKleinA k c ↔
      0<z.re^2+z.im^2-2*c*z.re+k:=by
    rw [←sub_pos]
    have he : halfTurnQuadKleinA k c-
        (halfTurnQuadKleinB k c*((z.re^2+z.im^2-1)/(z.re^2+z.im^2+1))-
          (-2*z.re)/(z.re^2+z.im^2+1))=
        (z.re^2+z.im^2-2*c*z.re+k)/(c*(z.re^2+z.im^2+1)):=by
      rw [halfTurnQuadKleinA,halfTurnQuadKleinB]
      field_simp
      ring
    rw [he,lt_div_iff₀ (mul_pos hc0 hN),zero_mul]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z∈(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon.interior ↔_
  dsimp only [halfTurnQuadCanonicalSupport]
  rw [halfTurnTrapezoid_interior_iff]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).im<0 ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).re<halfTurnQuadKleinS k ∧
    halfTurnQuadKleinB k c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).re-(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).im<halfTurnQuadKleinA k c ∧
    0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z).re ↔_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
  change (-2*z.re)/(z.re^2+z.im^2+1)<0 ∧
    (z.re^2+z.im^2-1)/(z.re^2+z.im^2+1)<halfTurnQuadKleinS k ∧
    halfTurnQuadKleinB k c*((z.re^2+z.im^2-1)/(z.re^2+z.im^2+1))-
      (-2*z.re)/(z.re^2+z.im^2+1)<halfTurnQuadKleinA k c ∧
    0<(z.re^2+z.im^2-1)/(z.re^2+z.im^2+1) ↔_
  rw [haxis,hrad0,hrad1,hcircle]
  tauto

/-- At the actual lower axis endpoint, all inequalities except the two
incident geodesic inequalities hold on a full native neighborhood. -/
theorem halfTurnQuadCanonical_lower_axis_germs (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    ∀ᶠz : ℍ in 𝓝 UpperHalfPlane.I,
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔0≤z.re ∧1≤‖(z : ℂ)‖) ∧
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔0<z.re ∧1<‖(z : ℂ)‖) := by
  have hnorm : Continuous (fun z : ℍ=>‖(z : ℂ)‖):=continuous_norm.comp UpperHalfPlane.continuous_coe
  have hpoly : Continuous (fun z : ℍ=>z.re^2+z.im^2-2*c*z.re+k):=by fun_prop
  have hnormI : ‖(UpperHalfPlane.I : ℂ)‖<k:=by simpa using hk
  have hpolyI : 0<UpperHalfPlane.I.re^2+UpperHalfPlane.I.im^2-2*c*UpperHalfPlane.I.re+k:=by
    norm_num
    linarith only [hk]
  filter_upwards [(isOpen_lt hnorm continuous_const).mem_nhds hnormI,
    (isOpen_lt continuous_const hpoly).mem_nhds hpolyI] with z hzk hp
  have hclosed := (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff
    (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon (halfTurnQuadCanonical_finite k c hk hc) z).trans
      (halfTurnQuadCanonical_native_closedCarrier k c hk hc z)
  have hopen:=halfTurnQuadCanonical_native_interior k c hk hc z
  have hzk0:=hzk.le
  have hp0:=hp.le
  constructor
  · exact hclosed.trans (by tauto)
  · exact hopen.trans (by tauto)

/-- At any genuine straight axis point, only the original axis support is
active; all other region inequalities hold in a full native neighborhood. -/
theorem halfTurnQuadCanonical_straight_axis_germs (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) (x : ℍ) (hxr : x.re=0)
    (hlo : 1<‖(x : ℂ)‖) (hhi : ‖(x : ℂ)‖<k) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    ∀ᶠz : ℍ in 𝓝 x,
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔0≤z.re) ∧
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔0<z.re) := by
  have hnorm : Continuous (fun z : ℍ=>‖(z : ℂ)‖):=UpperHalfPlane.continuous_coe.norm
  have hpoly : Continuous (fun z : ℍ=>z.re^2+z.im^2-2*c*z.re+k):=by fun_prop
  have hpolyX : 0<x.re^2+x.im^2-2*c*x.re+k:=by
    rw [hxr]
    nlinarith only [sq_nonneg x.im,hk]
  filter_upwards [(isOpen_lt continuous_const hnorm).mem_nhds hlo,
    (isOpen_lt hnorm continuous_const).mem_nhds hhi,
    (isOpen_lt continuous_const hpoly).mem_nhds hpolyX] with z hzlo hzhi hp
  have hclosed := (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff
    (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon (halfTurnQuadCanonical_finite k c hk hc) z).trans
      (halfTurnQuadCanonical_native_closedCarrier k c hk hc z)
  have hopen:=halfTurnQuadCanonical_native_interior k c hk hc z
  have hl:=hzlo.le
  have hh:=hzhi.le
  have hp0:=hp.le
  exact ⟨hclosed.trans (by tauto),hopen.trans (by tauto)⟩

/-- At the original upper axis endpoint the two genuine active supports are
the axis and outer semicircle. -/
theorem halfTurnQuadCanonical_upper_axis_germs (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) (x : ℍ) (hxr : x.re=0) (hxnorm : ‖(x : ℂ)‖=k) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    ∀ᶠz : ℍ in 𝓝 x,
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔0≤z.re ∧‖(z : ℂ)‖≤k) ∧
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔0<z.re ∧‖(z : ℂ)‖<k) := by
  have hnorm : Continuous (fun z : ℍ=>‖(z : ℂ)‖):=UpperHalfPlane.continuous_coe.norm
  have hpoly : Continuous (fun z : ℍ=>z.re^2+z.im^2-2*c*z.re+k):=by fun_prop
  have hpolyX : 0<x.re^2+x.im^2-2*c*x.re+k:=by
    rw [hxr]
    nlinarith only [sq_nonneg x.im,hk]
  have hlo : 1<‖(x : ℂ)‖:=hxnorm.symm ▸ hk
  filter_upwards [(isOpen_lt continuous_const hnorm).mem_nhds hlo,
    (isOpen_lt continuous_const hpoly).mem_nhds hpolyX] with z hzlo hp
  have hclosed := (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff
    (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon (halfTurnQuadCanonical_finite k c hk hc) z).trans
      (halfTurnQuadCanonical_native_closedCarrier k c hk hc z)
  have hopen:=halfTurnQuadCanonical_native_interior k c hk hc z
  have hl:=hzlo.le
  have hp0:=hp.le
  exact ⟨hclosed.trans (by tauto),hopen.trans (by tauto)⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Actual native axis inversion reverses both weak and strict real-coordinate signs. -/
theorem halfTurnPrimitiveBase_axis_sign (u : ℝ) (hu : 0<u) (z : ℍ) :
    (0≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu•z).re ↔ z.re≤0) ∧
      (0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu•z).re ↔ z.re<0) := by
  have hn : 0<Complex.normSq (z : ℂ):=Complex.normSq_pos.mpr z.ne_zero
  have hu2 : 0<u^2:=sq_pos_of_pos hu
  rw [sideOpposition_axis_halfturn_real]
  constructor
  · rw [le_div_iff₀ hn,zero_mul]
    constructor <;> intro h <;> nlinarith only [h,hu2]
  · rw [lt_div_iff₀ hn,zero_mul]
    constructor <;> intro h <;> nlinarith only [h,hu2]

/-- The exact radial norm of every actual native axis half-turn. -/
theorem halfTurnPrimitiveBase_axis_norm (u : ℝ) (hu : 0<u) (z : ℍ) :
    ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu•z : ℍ) : ℂ)‖=u^2/‖(z : ℂ)‖ := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe,norm_div,norm_neg,norm_pow,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hu]

/-- Pulling the actual upper-corner supports back by dilation gives the
right-hand inner unit sector, for weak and strict inequalities alike. -/
theorem halfTurnPrimitiveBase_dilation_supports (k : ℝ) (hk : 0<k) (z : ℍ) :
    (0≤(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk•z).re ∧
      ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk•z : ℍ) : ℂ)‖≤k ↔ 0≤z.re ∧ ‖(z : ℂ)‖≤1) ∧
    (0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk•z).re ∧
      ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk•z : ℍ) : ℂ)‖<k ↔ 0<z.re ∧ ‖(z : ℂ)‖<1) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,sideOpposition_dilation_norm]
  have hr0 : (0≤k*z.re)↔0≤z.re:=mul_nonneg_iff_of_pos_left hk
  have hr1 : (0<k*z.re)↔0<z.re:=mul_pos_iff_of_pos_left hk
  have hn0 : k*‖(z : ℂ)‖≤k ↔ ‖(z : ℂ)‖≤1:=by
    simpa only [mul_one] using (mul_le_mul_iff_right₀ hk : k*‖(z : ℂ)‖≤k*1 ↔ ‖(z : ℂ)‖≤1)
  have hn1 : k*‖(z : ℂ)‖<k ↔ ‖(z : ℂ)‖<1:=by
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ hk : k*‖(z : ℂ)‖<k*1 ↔ ‖(z : ℂ)‖<1)
  exact ⟨and_congr hr0 hn0,and_congr hr1 hn1⟩

/-- The three actual copy labels at the original five-side lower axis vertex. -/
def halfTurnPrimitiveThreeBaseMaps (u t : ℝ) (hu : 0<u) (ht : 0<t) : Fin 3→(ℍ≃ᵢℍ):=
  ![1,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht)))⁻¹]

/-- The four actual copy labels at the original four-side lower axis vertex. -/
def halfTurnPrimitiveFourBaseMaps (t : ℝ) (ht : 0<t) : Fin 4→(ℍ≃ᵢℍ):=
  ![1,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t ht),_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht)))⁻¹]

/-- All three literal copied polygons have their actual weak and strict base
germs; no fan, ball cover or local tessellation premise is used. -/
theorem halfTurnPrimitive_three_base_germs (u t c : ℝ) (hu : 1<u) (hut : u<t)
    (hc : t^2+1<2*c) :
    let hk:=one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let E:=halfTurnPrimitiveThreeBaseMaps u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))
    ∀ᶠz : ℍ in 𝓝 UpperHalfPlane.I,∀i : Fin 3,
      (z∈E i '' P.carrier ↔ ![0≤z.re ∧ 1≤‖(z : ℂ)‖,z.re≤0,0≤z.re ∧ ‖(z : ℂ)‖≤1] i) ∧
      (z∈E i '' P.interior ↔ ![0<z.re ∧ 1<‖(z : ℂ)‖,z.re<0,0<z.re ∧ ‖(z : ℂ)‖<1] i) := by
  let hu0:=zero_lt_one.trans hu
  let ht:=hu.trans hut
  let ht0:=zero_lt_one.trans ht
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu0)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos ht0))
  let x:=F UpperHalfPlane.I
  let y:=D UpperHalfPlane.I
  have hxre : x.re=0:=(axisHalfTurn_zero_re_coordinates u hu0 UpperHalfPlane.I (by simp)).1
  have hxnorm : ‖(x : ℂ)‖=u^2:=by
    change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu0•UpperHalfPlane.I : ℍ) : ℂ)‖=u^2
    rw [halfTurnPrimitiveBase_axis_norm,UpperHalfPlane.coe_I,Complex.norm_I,div_one]
  have hxlo : 1<‖(x : ℂ)‖:=by rw [hxnorm];nlinarith only [hu]
  have hxhi : ‖(x : ℂ)‖<t^2:=by
    rw [hxnorm]
    exact (sq_lt_sq₀ hu0.le ht0.le).mpr hut
  have hyre : y.re=0:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _•UpperHalfPlane.I).re=0
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,UpperHalfPlane.I_re,mul_zero]
  have hynorm : ‖(y : ℂ)‖=t^2:=by
    change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _•UpperHalfPlane.I : ℍ) : ℂ)‖=t^2
    rw [sideOpposition_dilation_norm,UpperHalfPlane.coe_I,Complex.norm_I,mul_one]
  have h0:=halfTurnQuadCanonical_lower_axis_germs (t^2) c hk hc
  have h1:=(F.continuous.continuousAt.tendsto).eventually
    (halfTurnQuadCanonical_straight_axis_germs (t^2) c hk hc x hxre hxlo hxhi)
  have h2:=(D.continuous.continuousAt.tendsto).eventually
    (halfTurnQuadCanonical_upper_axis_germs (t^2) c hk hc y hyre hynorm)
  have himage (f : ℍ≃ᵢℍ) (S : Set ℍ) (z : ℍ) : z∈f '' S ↔ f⁻¹ z∈S:=
    Set.mem_image_equiv (f:=f.toEquiv)
  filter_upwards [h0,h1,h2] with z hz0 hz1 hz2
  intro i
  fin_cases i
  · change (z∈(1 : ℍ≃ᵢℍ) '' P.carrier ↔ 0≤z.re ∧ 1≤‖(z : ℂ)‖) ∧
      (z∈(1 : ℍ≃ᵢℍ) '' P.interior ↔ 0<z.re ∧ 1<‖(z : ℂ)‖)
    rw [himage,himage]
    exact hz0
  · change (z∈F '' P.carrier ↔ z.re≤0) ∧ (z∈F '' P.interior ↔ z.re<0)
    rw [himage,himage,show F⁻¹=F from halfTurnNative_axis_inverse u hu0]
    have hs:=halfTurnPrimitiveBase_axis_sign u hu0 z
    exact ⟨hz1.1.trans hs.1,hz1.2.trans hs.2⟩
  · change (z∈(D⁻¹ : ℍ≃ᵢℍ) '' P.carrier ↔ 0≤z.re ∧ ‖(z : ℂ)‖≤1) ∧
      (z∈(D⁻¹ : ℍ≃ᵢℍ) '' P.interior ↔ 0<z.re ∧ ‖(z : ℂ)‖<1)
    rw [himage,himage,inv_inv]
    have hs:=halfTurnPrimitiveBase_dilation_supports (t^2) (sq_pos_of_pos ht0) z
    exact ⟨hz2.1.trans hs.1,hz2.2.trans hs.2⟩


/-- The four actual copied quadrilaterals have the original radial/axis
corner germs, including both opposite quarter sectors. -/
theorem halfTurnPrimitive_four_base_germs (t c : ℝ) (ht : 1<t)
    (hc : t^2+1<2*c) :
    let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let E:=halfTurnPrimitiveFourBaseMaps t (zero_lt_one.trans ht)
    ∀ᶠz : ℍ in 𝓝 UpperHalfPlane.I,∀i : Fin 4,
      (z∈E i '' P.carrier ↔
        ![0≤z.re ∧ 1≤‖(z : ℂ)‖,z.re≤0 ∧ 1≤‖(z : ℂ)‖,
          z.re≤0 ∧ ‖(z : ℂ)‖≤1,0≤z.re ∧ ‖(z : ℂ)‖≤1] i) ∧
      (z∈E i '' P.interior ↔
        ![0<z.re ∧ 1<‖(z : ℂ)‖,z.re<0 ∧ 1<‖(z : ℂ)‖,
          z.re<0 ∧ ‖(z : ℂ)‖<1,0<z.re ∧ ‖(z : ℂ)‖<1] i) := by
  let ht0:=zero_lt_one.trans ht
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let hk0:=sq_pos_of_pos ht0
  let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t ht0)
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) hk0)
  let x:=G UpperHalfPlane.I
  let y:=D UpperHalfPlane.I
  have hxre : x.re=0:=(axisHalfTurn_zero_re_coordinates t ht0 UpperHalfPlane.I (by simp)).1
  have hxnorm : ‖(x : ℂ)‖=t^2:=by
    change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t ht0•UpperHalfPlane.I : ℍ) : ℂ)‖=t^2
    rw [halfTurnPrimitiveBase_axis_norm,UpperHalfPlane.coe_I,Complex.norm_I,div_one]
  have hyre : y.re=0:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) hk0•UpperHalfPlane.I).re=0
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,UpperHalfPlane.I_re,mul_zero]
  have hynorm : ‖(y : ℂ)‖=t^2:=by
    change ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) hk0•UpperHalfPlane.I : ℍ) : ℂ)‖=t^2
    rw [sideOpposition_dilation_norm,UpperHalfPlane.coe_I,Complex.norm_I,mul_one]
  have hFI : F UpperHalfPlane.I=UpperHalfPlane.I:=by
    have hf:=axisHalfTurn_zero_re_coordinates 1 zero_lt_one UpperHalfPlane.I (by simp)
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•UpperHalfPlane.I).re=UpperHalfPlane.I.re
      rw [UpperHalfPlane.I_re]
      exact hf.1
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•UpperHalfPlane.I).im=UpperHalfPlane.I.im
      simpa only [UpperHalfPlane.I_im,one_pow,div_one] using hf.2
  have h0:=halfTurnQuadCanonical_lower_axis_germs (t^2) c hk hc
  have h1:=(G.continuous.continuousAt.tendsto).eventually
    (halfTurnQuadCanonical_upper_axis_germs (t^2) c hk hc x hxre hxnorm)
  have hFT : Tendsto F (𝓝 UpperHalfPlane.I) (𝓝 UpperHalfPlane.I):=by
    have hh : Tendsto F (𝓝 UpperHalfPlane.I) (𝓝 (F UpperHalfPlane.I)):=F.continuous.continuousAt
    rw [hFI] at hh
    exact hh
  have h2:=hFT.eventually h0
  have h3:=(D.continuous.continuousAt.tendsto).eventually
    (halfTurnQuadCanonical_upper_axis_germs (t^2) c hk hc y hyre hynorm)
  have himage (f : ℍ≃ᵢℍ) (S : Set ℍ) (z : ℍ) : z∈f '' S ↔ f⁻¹ z∈S:=
    Set.mem_image_equiv (f:=f.toEquiv)
  filter_upwards [h0,h1,h2,h3] with z hz0 hz1 hz2 hz3
  intro i
  have hn : 0<‖(z : ℂ)‖:=norm_pos_iff.mpr z.ne_zero
  fin_cases i
  · change (z∈(1 : ℍ≃ᵢℍ) '' P.carrier ↔ 0≤z.re ∧ 1≤‖(z : ℂ)‖) ∧
      (z∈(1 : ℍ≃ᵢℍ) '' P.interior ↔ 0<z.re ∧ 1<‖(z : ℂ)‖)
    rw [himage,himage]
    exact hz0
  · change (z∈G '' P.carrier ↔ z.re≤0 ∧ 1≤‖(z : ℂ)‖) ∧
      (z∈G '' P.interior ↔ z.re<0 ∧ 1<‖(z : ℂ)‖)
    rw [himage,himage,show G⁻¹=G from halfTurnNative_axis_inverse t ht0]
    have hs:=halfTurnPrimitiveBase_axis_sign t ht0 z
    have hn0 : ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t ht0•z : ℍ) : ℂ)‖≤t^2 ↔ 1≤‖(z : ℂ)‖:=by
      rw [halfTurnPrimitiveBase_axis_norm,div_le_iff₀ hn]
      simpa only [mul_one] using
        (mul_le_mul_iff_right₀ hk0 : t^2*1≤t^2*‖(z : ℂ)‖ ↔ 1≤‖(z : ℂ)‖)
    have hn1 : ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t ht0•z : ℍ) : ℂ)‖<t^2 ↔ 1<‖(z : ℂ)‖:=by
      rw [halfTurnPrimitiveBase_axis_norm,div_lt_iff₀ hn]
      simpa only [mul_one] using
        (mul_lt_mul_iff_right₀ hk0 : t^2*1<t^2*‖(z : ℂ)‖ ↔ 1<‖(z : ℂ)‖)
    exact ⟨hz1.1.trans (and_congr hs.1 hn0),hz1.2.trans (and_congr hs.2 hn1)⟩
  · change (z∈F '' P.carrier ↔ z.re≤0 ∧ ‖(z : ℂ)‖≤1) ∧
      (z∈F '' P.interior ↔ z.re<0 ∧ ‖(z : ℂ)‖<1)
    rw [himage,himage,show F⁻¹=F from halfTurnNative_axis_inverse 1 zero_lt_one]
    have hs:=halfTurnPrimitiveBase_axis_sign 1 zero_lt_one z
    have hn0 : 1≤‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z : ℍ) : ℂ)‖ ↔ ‖(z : ℂ)‖≤1:=by
      rw [halfTurnPrimitiveBase_axis_norm,one_pow,le_div_iff₀ hn,one_mul]
    have hn1 : 1<‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z : ℍ) : ℂ)‖ ↔ ‖(z : ℂ)‖<1:=by
      rw [halfTurnPrimitiveBase_axis_norm,one_pow,lt_div_iff₀ hn,one_mul]
    exact ⟨hz2.1.trans (and_congr hs.1 hn0),hz2.2.trans (and_congr hs.2 hn1)⟩
  · change (z∈(D⁻¹ : ℍ≃ᵢℍ) '' P.carrier ↔ 0≤z.re ∧ ‖(z : ℂ)‖≤1) ∧
      (z∈(D⁻¹ : ℍ≃ᵢℍ) '' P.interior ↔ 0<z.re ∧ ‖(z : ℂ)‖<1)
    rw [himage,himage,inv_inv]
    have hs:=halfTurnPrimitiveBase_dilation_supports (t^2) hk0 z
    exact ⟨hz3.1.trans hs.1,hz3.2.trans hs.2⟩

/-- Three actual base copies cover a full native ball and have pairwise
disjoint open-polygon pieces. Their geometry is derived from the true source polygon. -/
theorem halfTurnPrimitive_three_base_fan (u t c : ℝ) (hu : 1<u) (hut : u<t)
    (hc : t^2+1<2*c) :
    let hk:=one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let E:=halfTurnPrimitiveThreeBaseMaps u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))
    ∃r : ℝ,0<r ∧
      (⋃i : Fin 3,Metric.ball UpperHalfPlane.I r ∩ E i '' P.carrier)=Metric.ball UpperHalfPlane.I r ∧
      Pairwise (fun i j : Fin 3=>Disjoint
        (Metric.ball UpperHalfPlane.I r ∩ E i '' P.interior)
        (Metric.ball UpperHalfPlane.I r ∩ E j '' P.interior)) := by
  let hk:=one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let E:=halfTurnPrimitiveThreeBaseMaps u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))
  obtain ⟨r,hr,hBall⟩:=Metric.eventually_nhds_iff_ball.mp
    (halfTurnPrimitive_three_base_germs u t c hu hut hc)
  refine ⟨r,hr,?_,?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩:=mem_iUnion.mp hz
      exact hi.1
    · intro hz
      by_cases hre : 0≤z.re
      · by_cases hnorm : 1≤‖(z : ℂ)‖
        · exact mem_iUnion.mpr ⟨0,hz,(hBall z hz 0).1.mpr ⟨hre,hnorm⟩⟩
        · exact mem_iUnion.mpr ⟨2,hz,(hBall z hz 2).1.mpr ⟨hre,(lt_of_not_ge hnorm).le⟩⟩
      · exact mem_iUnion.mpr ⟨1,hz,(hBall z hz 1).1.mpr (lt_of_not_ge hre).le⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    have hiG:=(hBall z hi.1 i).2.mp hi.2
    have hjG:=(hBall z hj.1 j).2.mp hj.2
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    all_goals norm_num at hiG hjG
    all_goals (try rcases hiG with ⟨hi0,hi1⟩)
    all_goals (try rcases hjG with ⟨hj0,hj1⟩)
    all_goals linarith

/-- Four actual quarter-sector copies cover a full native ball at the genuine
lower axis vertex and their actual open polygon parts do not overlap. -/
theorem halfTurnPrimitive_four_base_fan (t c : ℝ) (ht : 1<t)
    (hc : t^2+1<2*c) :
    let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let E:=halfTurnPrimitiveFourBaseMaps t (zero_lt_one.trans ht)
    ∃r : ℝ,0<r ∧
      (⋃i : Fin 4,Metric.ball UpperHalfPlane.I r ∩ E i '' P.carrier)=Metric.ball UpperHalfPlane.I r ∧
      Pairwise (fun i j : Fin 4=>Disjoint
        (Metric.ball UpperHalfPlane.I r ∩ E i '' P.interior)
        (Metric.ball UpperHalfPlane.I r ∩ E j '' P.interior)) := by
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) c hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let E:=halfTurnPrimitiveFourBaseMaps t (zero_lt_one.trans ht)
  obtain ⟨r,hr,hBall⟩:=Metric.eventually_nhds_iff_ball.mp
    (halfTurnPrimitive_four_base_germs t c ht hc)
  refine ⟨r,hr,?_,?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨i,hi⟩:=mem_iUnion.mp hz
      exact hi.1
    · intro hz
      by_cases hre : 0≤z.re
      · by_cases hnorm : 1≤‖(z : ℂ)‖
        · exact mem_iUnion.mpr ⟨0,hz,(hBall z hz 0).1.mpr ⟨hre,hnorm⟩⟩
        · exact mem_iUnion.mpr ⟨3,hz,(hBall z hz 3).1.mpr ⟨hre,(lt_of_not_ge hnorm).le⟩⟩
      · by_cases hnorm : 1≤‖(z : ℂ)‖
        · exact mem_iUnion.mpr ⟨1,hz,(hBall z hz 1).1.mpr ⟨(lt_of_not_ge hre).le,hnorm⟩⟩
        · exact mem_iUnion.mpr ⟨2,hz,(hBall z hz 2).1.mpr ⟨(lt_of_not_ge hre).le,(lt_of_not_ge hnorm).le⟩⟩
  · intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    have hiG:=(hBall z hi.1 i).2.mp hi.2
    have hjG:=(hBall z hj.1 j).2.mp hj.2
    fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
    all_goals norm_num at hiG hjG
    all_goals rcases hiG with ⟨hi0,hi1⟩
    all_goals rcases hjG with ⟨hj0,hj1⟩
    all_goals linarith

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Actual endpoint transport and the actual paired incoming side determine
the complete canonical lifted flag step, including its genuine group label. -/
theorem halfTurnWalk_step_of_endpoint {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (i j : Fin m)
    (hv : S.element (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf j)
    (hs : S.paired (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf ((finRotate m).symm j)) (g : S.Generated) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (g,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
      (g*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i))⁻¹,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf j) := by
  let hV:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S
  let a:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i
  have hindex : (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a).val.1=j:=by
    apply _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap_vertex Q hf S hV a).trans hv
  have hside : (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a).val.2=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf ((finRotate m).symm j):=hs
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    apply Prod.ext
    · exact hindex
    · change _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherSide Q hf
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a).val.1
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCrossFlagMap Q hf S hV a).val.2=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf j
      rw [hindex,hside]
      have hne : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf ((finRotate m).symm j)≠_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf j:=
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf).injective.ne (Q.prev_ne_self j)
      simp only [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertexOtherSide,hne,ite_false]

/-- The literal positive-axis coordinate is recovered from its actual Klein coordinate. -/
theorem halfTurnWalk_axis_vertex (z : ℍ) (r : ℝ) (hr : 0<r)
    (hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z=(((r^2-1)/(r^2+1) : ℝ) : ℂ)) :
    z.re=0 ∧ z.im=r := by
  have hre : z.re=0:=(nativeSideCoordinates_im_zero z).mp (by simpa only [Complex.ofReal_im] using congrArg Complex.im hz)
  have hn : ‖(z : ℂ)‖=r:=(nativeSideCoordinates_re_eq_radius r hr z).mp (by simpa only [Complex.ofReal_re] using congrArg Complex.re hz)
  exact ⟨hre,(nativeSideCoordinates_axis_norm z hre).symm.trans hn⟩

/-- The genuine two axis vertices of the original quadrilateral. -/
theorem halfTurnWalk_four_axis_vertices (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0).re=0 ∧ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0).im=1 ∧
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).re=0 ∧ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).im=k := by
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  have h0:=halfTurnWalk_axis_vertex (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0) 1 zero_lt_one (by
    simpa [kleinSubdivisionVertices4] using halfTurnFour_native_vertex_coordinate k c hk hc 0)
  have h1:=halfTurnWalk_axis_vertex (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1) k (zero_lt_one.trans hk) (by
    simpa [kleinSubdivisionVertices4] using halfTurnFour_native_vertex_coordinate k c hk hc 1)
  exact ⟨h0.1,h0.2,h1.1,h1.2⟩

/-- The actual axis-pairing map sends the lower axis endpoint to the upper endpoint. -/
theorem halfTurnWalk_four_axis_image (t : ℝ) (ht : 1<t) (w : ℍ)
    (hc : t^2+1<2*(t^2/w.re)) :
    let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1 := by
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  have hv:=halfTurnWalk_four_axis_vertices (t^2) (t^2/w.re) hk hc
  have hh:=axisHalfTurn_zero_re_coordinates t (zero_lt_one.trans ht) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0) hv.1
  apply UpperHalfPlane.ext
  apply Complex.ext
  · exact hh.1.trans hv.2.2.1.symm
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t _•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0).im=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).im
    rw [hh.2,hv.2.1,hv.2.2.2,div_one]

/-- Actual dilation identifies the original two axis endpoints. -/
theorem halfTurnWalk_four_axis_dilation (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk)) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1 := by
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  have hv:=halfTurnWalk_four_axis_vertices k c hk hc
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k _•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0).re=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).re
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,hv.1,hv.2.2.1,mul_zero]
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k _•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0).im=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).im
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im,hv.2.1,hv.2.2.2,mul_one]

/-- Actual four-side endpoint transport in the original canonical cyclic order. -/
theorem halfTurnWalk_four_endpoint (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) (i : Fin 4) :
    let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
    halfTurnFour_element t ht w i (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (![1,0,3,2] i) := by
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  have hD:=halfTurnWalk_four_axis_dilation (t^2) (t^2/w.re) hk hc
  have hSummit:=halfTurnFour_summit_dilation (t^2) (t^2/w.re) hk hc w hw hn rfl
  have hW : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2:=
    (halfTurnFour_summit_halfturn (t^2) (t^2/w.re) hk hc w hw hn rfl).trans hSummit
  fin_cases i
  · exact halfTurnWalk_four_axis_image t ht w hc
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _))⁻¹ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0
    rw [←hD]
    exact IsometryEquiv.inv_apply_self _ _
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
    rw [←hW]
    exact sideOpposition_point_halfturn_involutive w _
  · exact hSummit


/-- The actual quadrilateral walk crosses each original outgoing side and
retains the actual generated-group label. -/
theorem halfTurnWalk_four_step (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) :
    let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
    let S:=halfTurnFour_pairing t ht w hw hn hc
    ∀i : Fin 4,∀g : S.Generated,
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (g,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
        (g*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i))⁻¹,
          _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (![1,0,3,2] i)) := by
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  let S:=halfTurnFour_pairing t ht w hw hn hc
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  dsimp only
  intro i g
  apply halfTurnWalk_step_of_endpoint Q hf S i (![1,0,3,2] i)
  · rw [halfTurnFour_pairing_element_index]
    exact halfTurnWalk_four_endpoint t ht w hw hn hc i
  · change e ((Equiv.swap (1 : Fin 4) 3) (e.symm (e i)))=
      e ((finRotate 4).symm (![1,0,3,2] i))
    rw [e.symm_apply_apply]
    apply congrArg e
    fin_cases i <;> decide

/-- The refined five vertices have their literal native Klein coordinates. -/
theorem halfTurnWalk_five_native_coordinate (u t c : ℝ) (hu : 1<u) (hut : u<t)
    (hc : t^2+1<2*c) (i : Fin 5) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnFiveDiscPolygon u t c hu hut hc)
      (halfTurnFiveDiscPolygon_finite u t c hu hut hc) i)=
      kleinSubdivisionVertices5 (halfTurnQuadKleinA (t^2) c) (halfTurnQuadKleinB (t^2) c)
        (halfTurnQuadKleinR (u^2)) (halfTurnQuadKleinS (t^2)) i := by
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate]
  have h:=halfTurnFive_band_parameters u t hu hut
  exact halfTurnQuadRefined_coordinate (t^2) c (u^2) h.1 hc h.2.1 h.2.2 i

/-- Subdivision retains every genuine old vertex at its original physical point. -/
theorem halfTurnWalk_five_four_vertex (u t c : ℝ) (hu : 1<u) (hut : u<t)
    (hc : t^2+1<2*c) (i : Fin 4) :
    let hk:=one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnFiveDiscPolygon u t c hu hut hc)
      (halfTurnFiveDiscPolygon_finite u t c hu hut hc) (![0,2,3,4] i)=
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnQuadCanonicalSupport (t^2) c hk hc).toDiscPolygon
        (halfTurnQuadCanonical_finite (t^2) c hk hc) i := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective
  rw [halfTurnWalk_five_native_coordinate,halfTurnFour_native_vertex_coordinate]
  fin_cases i <;> simp [kleinSubdivisionVertices5,kleinSubdivisionVertices4,
    halfTurnQuadKleinA,halfTurnQuadKleinB,halfTurnQuadKleinS]

/-- The subdivision vertex has the actual source axis height u squared. -/
theorem halfTurnWalk_five_middle_axis_vertex (u t c : ℝ) (hu : 1<u) (hut : u<t)
    (hc : t^2+1<2*c) :
    let v:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex (halfTurnFiveDiscPolygon u t c hu hut hc)
      (halfTurnFiveDiscPolygon_finite u t c hu hut hc) 1
    v.re=0 ∧ v.im=u^2 := by
  apply halfTurnWalk_axis_vertex _ (u^2) (sq_pos_of_pos (zero_lt_one.trans hu))
  simpa [kleinSubdivisionVertices5,halfTurnQuadKleinR] using
    halfTurnWalk_five_native_coordinate u t c hu hut hc 1

/-- Genuine five-side endpoint transport, with no supplied vertex-map property. -/
theorem halfTurnWalk_five_endpoint (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) (i : Fin 5) :
    let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
    let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
    halfTurnFiveElement u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)) w i
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (![1,2,0,4,3] i) := by
  let ht:=hu.trans hut
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
  let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
  let Q₄:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf₄:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  have h0 : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0:=
    halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 0
  have h2 : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 1:=
    halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 1
  have h3 : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 2:=
    halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 2
  have h4 : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 4=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3:=
    halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 3
  have hv:=halfTurnWalk_four_axis_vertices (t^2) (t^2/w.re) hk hc
  have hmid:=halfTurnWalk_five_middle_axis_vertex u t (t^2/w.re) hu hut hc
  fin_cases i
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u _) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1
    rw [h0]
    have hh:=axisHalfTurn_zero_re_coordinates u (zero_lt_one.trans hu) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0) hv.1
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hh.1.trans hmid.1.symm
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u _•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0).im=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).im
      rw [hh.2,hv.2.1,hmid.2,div_one]
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) _) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2
    rw [h2]
    have hh:=axisHalfTurn_zero_re_coordinates (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans ht))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1) hmid.1
    apply UpperHalfPlane.ext
    apply Complex.ext
    · exact hh.1.trans hv.2.2.1.symm
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) _•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 1).im=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 1).im
      rw [hh.2,hmid.2,hv.2.2.2]
      field_simp
  · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _))⁻¹ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0
    rw [h2,h0]
    exact halfTurnWalk_four_endpoint t ht w hw hn hc 1
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 4
    rw [h3,h4]
    exact halfTurnWalk_four_endpoint t ht w hw hn hc 2
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 4)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
    rw [h4,h3]
    exact halfTurnWalk_four_endpoint t ht w hw hn hc 3

/-- The actual five-side canonical flag step has its literal endpoint and
copy-label transition, including the genuine straight subdivision vertex. -/
theorem halfTurnWalk_five_step (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) :
    let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
    let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
    let S:=halfTurnFivePairing u t hu hut w hw hn hc
    ∀i : Fin 5,∀g : S.Generated,
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (g,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=
        (g*(S.generator (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf i))⁻¹,
          _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf (![1,2,0,4,3] i)) := by
  let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
  let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
  let S:=halfTurnFivePairing u t hu hut w hw hn hc
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  dsimp only
  intro i g
  apply halfTurnWalk_step_of_endpoint Q hf S i (![1,2,0,4,3] i)
  · rw [halfTurnFivePairing_element_index]
    exact halfTurnWalk_five_endpoint u t hu hut w hw hn hc i
  · rw [halfTurnFivePairing_paired_index]
    apply congrArg e
    fin_cases i <;> decide


/-- The exact alternating two-flag walk retains every actual copy label. -/
theorem halfTurnWalk_alternating_iterates {G F : Type*} [Group G]
    (e : G×F≃G×F) (a b : F) (X Y : G)
    (ha : ∀g,e (g,a)=(g*X,b)) (hb : ∀g,e (g,b)=(g*Y,a)) :
    ∀m : ℕ,∀g : G,
      (e^[2*m]) (g,a)=(g*(X*Y)^m,a) ∧
      (e^[2*m+1]) (g,a)=(g*(X*Y)^m*X,b) := by
  intro m
  induction m with
  | zero=>
    intro g
    constructor
    · simp
    · simpa using ha g
  | succ m ih=>
    intro g
    have he : (e^[2*(m+1)]) (g,a)=(g*(X*Y)^(m+1),a):=by
      rw [show 2*(m+1)=(2*m+1)+1 by omega,Function.iterate_succ_apply',(ih g).2,hb]
      simp only [pow_succ,mul_assoc]
    refine ⟨he,?_⟩
    rw [Function.iterate_succ_apply',he,ha]

/-- The exact true product order closes both orientations of an alternating vertex walk. -/
theorem halfTurnWalk_alternating_period {G F : Type*} [Group G]
    (e : G×F≃G×F) (a b : F) (X Y : G)
    (ha : ∀g,e (g,a)=(g*X,b)) (hb : ∀g,e (g,b)=(g*Y,a)) (g : G) :
    (e^[2*orderOf (X*Y)]) (g,a)=(g,a) ∧
      (e^[2*orderOf (X*Y)]) (g,b)=(g,b) := by
  constructor
  · simpa only [pow_orderOf_eq_one,mul_one] using
      (halfTurnWalk_alternating_iterates e a b X Y ha hb (orderOf (X*Y)) g).1
  · have hrev : (Y*X)^orderOf (X*Y)=1:=by
      rw [show Y*X=X⁻¹*(X*Y)*(X⁻¹)⁻¹ by group,conj_pow,pow_orderOf_eq_one]
      group
    simpa only [hrev,mul_one] using
      (halfTurnWalk_alternating_iterates e b a Y X hb ha (orderOf (X*Y)) g).1

/-- Three literal transitions with their actual identity word close the original lifted state. -/
theorem halfTurnWalk_three_period {G F : Type*} [Group G]
    (e : G×F≃G×F) (a b c : F) (X Y Z : G)
    (ha : ∀g,e (g,a)=(g*X,b)) (hb : ∀g,e (g,b)=(g*Y,c))
    (hc : ∀g,e (g,c)=(g*Z,a)) (hword : X*Y*Z=1) (g : G) :
    (e^[3]) (g,a)=(g,a) := by
  change e (e (e (g,a)))=(g,a)
  rw [ha,hb,hc]
  simpa only [mul_assoc,mul_one] using congrArg (fun x : G=>(g*x,a)) hword

/-- The actual summit cycle word is the actual canonical triple action. -/
theorem halfTurnWalk_summit_native_word (u t : ℝ) (hu : 0<u) (ht : 1<t) (w : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans ht))))⁻¹*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) := by
  rw [←halfTurnNative_axis_product u t hu (zero_lt_one.trans ht),mul_inv_rev,
    halfTurnNative_axis_inverse,halfTurnNative_axis_inverse]
  apply IsometryEquiv.ext
  intro x
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) _•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w•x))=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)•x
  simp only [mul_smul]

section FourWalks
variable (t : ℝ) (ht : 1<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
local notation "S₄" => halfTurnFour_pairing t ht w hw hn hc
local notation "e₄" => finitePolygonSideEquiv Q₄ hf₄
local notation "f₄" => finitePolygonOutgoingFlag Q₄ hf₄
local notation "σ₄" => finitePolygonCanonicalVertexStep Q₄ hf₄ S₄
local notation "d₄" => (S₄).generator (e₄ 3)
local notation "v₄" => (S₄).generator (e₄ 2)
local notation "a₄" => d₄⁻¹*v₄

theorem halfTurnWalk_four_third_inverse : v₄⁻¹=v₄ := by
  apply Subtype.ext
  change ((S₄).element (e₄ 2))⁻¹=(S₄).element (e₄ 2)
  rw [halfTurnFour_pairing_element_index]
  exact halfTurnNative_point_inverse w

/-- The literal four-side summit word in the unchanged actual generated subgroup. -/
theorem halfTurnWalk_four_summit_word :
    (a₄).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) := by
  change ((S₄).element (e₄ 3))⁻¹*(S₄).element (e₄ 2)=_
  rw [halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans ht))))⁻¹*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)=_
  simpa only [one_mul] using halfTurnWalk_summit_native_word 1 t zero_lt_one ht w

/-- Even and odd actual quadrilateral summit flags, with their exact copy words. -/
theorem halfTurnWalk_four_summit_iterates (m : ℕ) (g : (S₄).Generated) :
    (σ₄^[2*m]) (g,f₄ 3)=(g*a₄^m,f₄ 3) ∧
      (σ₄^[2*m+1]) (g,f₄ 3)=(g*a₄^m*d₄⁻¹,f₄ 2) := by
  apply halfTurnWalk_alternating_iterates σ₄ (f₄ 3) (f₄ 2) d₄⁻¹ v₄
  · intro g
    exact halfTurnWalk_four_step t ht w hw hn hc 3 g
  · intro g
    rw [←halfTurnWalk_four_third_inverse t ht w hw hn hc]
    exact halfTurnWalk_four_step t ht w hw hn hc 2 g

/-- The true original triple order closes both actual quadrilateral summit flags. -/
theorem halfTurnWalk_four_summit_period (q : ℕ)
    (hq : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) (g : (S₄).Generated) :
    (σ₄^[2*q]) (g,f₄ 3)=(g,f₄ 3) ∧ (σ₄^[2*q]) (g,f₄ 2)=(g,f₄ 2) := by
  have ho : orderOf a₄=q:=by
    calc
      orderOf a₄=orderOf (a₄).val:=(orderOf_injective (S₄).Generated.subtype Subtype.val_injective _).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _):=by rw [halfTurnWalk_four_summit_word]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _):=hSLIsometry_orderOf_eq_realSLMobius _
      _=q:=hq
  rw [←ho]
  apply halfTurnWalk_alternating_period σ₄ (f₄ 3) (f₄ 2) d₄⁻¹ v₄
  · intro g
    exact halfTurnWalk_four_step t ht w hw hn hc 3 g
  · intro g
    rw [←halfTurnWalk_four_third_inverse t ht w hw hn hc]
    exact halfTurnWalk_four_step t ht w hw hn hc 2 g

/-- The four-step axis cycle has actual identity word. -/
theorem halfTurnWalk_four_base_word :
    (((S₄).generator (e₄ 0))⁻¹*((S₄).generator (e₄ 1))⁻¹)^2=1 := by
  apply Subtype.ext
  change (((S₄).element (e₄ 0))⁻¹*((S₄).element (e₄ 1))⁻¹)^2=1
  rw [halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)))⁻¹*
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans ht))))⁻¹)⁻¹)^2=1
  rw [inv_inv,halfTurnNative_axis_inverse,halfTurnFour_dilation_product t ht]
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht))=1:=by
    exact inv_eq_iff_mul_eq_one.mp (halfTurnNative_axis_inverse t (zero_lt_one.trans ht))
  rw [←mul_assoc,hG,one_mul,pow_two]
  exact inv_eq_iff_mul_eq_one.mp (halfTurnNative_axis_inverse 1 zero_lt_one)

/-- Both original axis flags close after the true four-corner base cycle. -/
theorem halfTurnWalk_four_base_period (i : Fin 2) (g : (S₄).Generated) :
    (σ₄^[4]) (g,f₄ (i.castLE (by decide : 2≤4)))=(g,f₄ (i.castLE (by decide : 2≤4))) := by
  let X:=((S₄).generator (e₄ 0))⁻¹
  let Y:=((S₄).generator (e₄ 1))⁻¹
  have h0 (g : (S₄).Generated) : σ₄ (g,f₄ 0)=(g*X,f₄ 1):=
    halfTurnWalk_four_step t ht w hw hn hc 0 g
  have h1 (g : (S₄).Generated) : σ₄ (g,f₄ 1)=(g*Y,f₄ 0):=
    halfTurnWalk_four_step t ht w hw hn hc 1 g
  have hxy : (X*Y)^2=1:=halfTurnWalk_four_base_word t ht w hw hn hc
  fin_cases i
  · have hh:=(halfTurnWalk_alternating_iterates σ₄ (f₄ 0) (f₄ 1) X Y h0 h1 2 g).1
    rw [hxy,mul_one] at hh
    exact hh
  · have hyx : (Y*X)^2=1:=by
      rw [show Y*X=X⁻¹*(X*Y)*(X⁻¹)⁻¹ by group,conj_pow,hxy]
      group
    have hh:=(halfTurnWalk_alternating_iterates σ₄ (f₄ 1) (f₄ 0) Y X h1 h0 2 g).1
    rw [hyx,mul_one] at hh
    exact hh
end FourWalks

section FiveWalks
variable (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₅" => halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
local notation "hf₅" => halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
local notation "S₅" => halfTurnFivePairing u t hu hut w hw hn hc
local notation "e₅" => finitePolygonSideEquiv Q₅ hf₅
local notation "f₅" => finitePolygonOutgoingFlag Q₅ hf₅
local notation "σ₅" => finitePolygonCanonicalVertexStep Q₅ hf₅ S₅
local notation "d₅" => (S₅).generator (e₅ 4)
local notation "v₅" => (S₅).generator (e₅ 3)
local notation "a₅" => d₅⁻¹*v₅

theorem halfTurnWalk_five_third_inverse : v₅⁻¹=v₅ := by
  apply Subtype.ext
  change ((S₅).element (e₅ 3))⁻¹=(S₅).element (e₅ 3)
  rw [halfTurnFivePairing_element_index]
  exact halfTurnNative_point_inverse w

/-- The five-side summit word is the actual unchanged original triple. -/
theorem halfTurnWalk_five_summit_word :
    (a₅).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) := by
  change ((S₅).element (e₅ 4))⁻¹*(S₅).element (e₅ 3)=_
  rw [halfTurnFivePairing_element_index,halfTurnFivePairing_element_index]
  exact halfTurnWalk_summit_native_word u t (zero_lt_one.trans hu) (hu.trans hut) w

/-- Actual even and odd summit flags for the five-side canonical walk. -/
theorem halfTurnWalk_five_summit_iterates (m : ℕ) (g : (S₅).Generated) :
    (σ₅^[2*m]) (g,f₅ 4)=(g*a₅^m,f₅ 4) ∧
      (σ₅^[2*m+1]) (g,f₅ 4)=(g*a₅^m*d₅⁻¹,f₅ 3) := by
  apply halfTurnWalk_alternating_iterates σ₅ (f₅ 4) (f₅ 3) d₅⁻¹ v₅
  · intro g
    exact halfTurnWalk_five_step u t hu hut w hw hn hc 4 g
  · intro g
    rw [←halfTurnWalk_five_third_inverse u t hu hut w hw hn hc]
    exact halfTurnWalk_five_step u t hu hut w hw hn hc 3 g

/-- The genuine triple order closes both original five-side summit flags. -/
theorem halfTurnWalk_five_summit_period (q : ℕ)
    (hq : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) (g : (S₅).Generated) :
    (σ₅^[2*q]) (g,f₅ 4)=(g,f₅ 4) ∧ (σ₅^[2*q]) (g,f₅ 3)=(g,f₅ 3) := by
  have ho : orderOf a₅=q:=by
    calc
      orderOf a₅=orderOf (a₅).val:=(orderOf_injective (S₅).Generated.subtype Subtype.val_injective _).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _):=by rw [halfTurnWalk_five_summit_word]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _):=hSLIsometry_orderOf_eq_realSLMobius _
      _=q:=hq
  rw [←ho]
  apply halfTurnWalk_alternating_period σ₅ (f₅ 4) (f₅ 3) d₅⁻¹ v₅
  · intro g
    exact halfTurnWalk_five_step u t hu hut w hw hn hc 4 g
  · intro g
    rw [←halfTurnWalk_five_third_inverse u t hu hut w hw hn hc]
    exact halfTurnWalk_five_step u t hu hut w hw hn hc 3 g

/-- The three actual base transitions have the literal identity word. -/
theorem halfTurnWalk_five_base_word :
    ((S₅).generator (e₅ 0))⁻¹*((S₅).generator (e₅ 1))⁻¹*((S₅).generator (e₅ 2))⁻¹=1 := by
  apply Subtype.ext
  change ((S₅).element (e₅ 0))⁻¹*((S₅).element (e₅ 1))⁻¹*((S₅).element (e₅ 2))⁻¹=1
  rw [halfTurnFivePairing_element_index,halfTurnFivePairing_element_index,halfTurnFivePairing_element_index]
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u _))⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) _))⁻¹*
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _))⁻¹)⁻¹=1
  rw [inv_inv,halfTurnNative_axis_inverse,halfTurnNative_axis_inverse]
  have hfg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu))*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))))=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans (hu.trans hut)))))⁻¹:=by
    rw [←halfTurnNative_axis_product u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)),
      mul_inv_rev,halfTurnNative_axis_inverse,halfTurnNative_axis_inverse]
  rw [hfg]
  exact inv_mul_cancel _

/-- Every true base flag closes after its three original quarter/straight/quarter corners. -/
theorem halfTurnWalk_five_base_period (i : Fin 3) (g : (S₅).Generated) :
    (σ₅^[3]) (g,f₅ (i.castLE (by decide : 3≤5)))=(g,f₅ (i.castLE (by decide : 3≤5))) := by
  let X:=((S₅).generator (e₅ 0))⁻¹
  let Y:=((S₅).generator (e₅ 1))⁻¹
  let Z:=((S₅).generator (e₅ 2))⁻¹
  have h0 (g : (S₅).Generated) : σ₅ (g,f₅ 0)=(g*X,f₅ 1):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 0 g
  have h1 (g : (S₅).Generated) : σ₅ (g,f₅ 1)=(g*Y,f₅ 2):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 1 g
  have h2 (g : (S₅).Generated) : σ₅ (g,f₅ 2)=(g*Z,f₅ 0):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 2 g
  have hxyz : X*Y*Z=1:=halfTurnWalk_five_base_word u t hu hut w hw hn hc
  fin_cases i
  · exact halfTurnWalk_three_period σ₅ (f₅ 0) (f₅ 1) (f₅ 2) X Y Z h0 h1 h2 hxyz g
  · have hyzx : Y*Z*X=1:=by
      calc
        Y*Z*X=X⁻¹*(X*Y*Z)*X:=by group
        _=1:=by rw [hxyz];group
    exact halfTurnWalk_three_period σ₅ (f₅ 1) (f₅ 2) (f₅ 0) Y Z X h1 h2 h0 hyzx g
  · have hzxy : Z*X*Y=1:=by
      calc
        Z*X*Y=Z*(X*Y*Z)*Z⁻¹:=by group
        _=1:=by rw [hxyz];group
    exact halfTurnWalk_three_period σ₅ (f₅ 2) (f₅ 0) (f₅ 1) Z X Y h2 h0 h1 hzxy g
end FiveWalks

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Actual canonical flag motion commutes with literal original copy translation. -/
theorem halfTurnBaseCycle_step_left {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (h : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S (h*a.1,a.2)=
      (h*(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S a).1,
        (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S a).2) := by
  apply Prod.ext
  · change (h*a.1)*(S.generator a.2.val.2)⁻¹=h*(a.1*(S.generator a.2.val.2)⁻¹)
    exact mul_assoc _ _ _
  · rfl

/-- Every literal canonical iterate retains the same original left copy translation. -/
theorem halfTurnBaseCycle_iterate_left {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (h : S.Generated) (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (n : ℕ) :
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n]) (h*a.1,a.2)=
      (h*(((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n]) a).1,
        (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n]) a).2) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',ih,halfTurnBaseCycle_step_left]

/-- Canonical side crossing preserves the actual developed native point at every iterate. -/
theorem halfTurnBaseCycle_iterate_evaluation {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (n : ℕ) :
    S.copyEvaluation (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n]) a))=
      S.copyEvaluation (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a) := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    rw [Function.iterate_succ_apply']
    have hs:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNaturalVertexStep_side_step Q hf S
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S)
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n]) a)
    exact (S.step_evaluation (Or.inr hs)).symm.trans ih

/-- Actual isometry images identify both literal copied ball pieces with
cuts of the unchanged copied closed and open native polygon. -/
theorem halfTurnBaseCycle_piece_ball {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (a : S.Copy) (r : ℝ) :
    S.vertexCyclePiece a r=Metric.ball (S.copyEvaluation a) r ∩ a.1.val ''
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ∧
    S.vertexCycleInteriorPiece a r=Metric.ball (S.copyEvaluation a) r ∩ a.1.val ''
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior := by
  constructor
  · change a.1.val '' ((_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ∩ Metric.ball a.2.val r)=_
    rw [Set.image_inter a.1.val.injective,a.1.val.image_ball]
    exact Set.inter_comm _ _
  · change a.1.val '' ((_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ∩ Metric.ball a.2.val r)=_
    rw [Set.image_inter a.1.val.injective,a.1.val.image_ball]
    exact Set.inter_comm _ _

/-- Actual copy translation sends the two literal kinds of ball piece by the same physical isometry. -/
theorem halfTurnBaseCycle_piece_left {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (h : S.Generated) (a : S.Copy) (r : ℝ) :
    S.vertexCyclePiece (h*a.1,a.2) r=h.val '' S.vertexCyclePiece a r ∧
      S.vertexCycleInteriorPiece (h*a.1,a.2) r=h.val '' S.vertexCycleInteriorPiece a r := by
  constructor <;> change (fun z : ℍ=>h.val (a.1.val z)) '' _=h.val '' (a.1.val '' _)
  all_goals rw [Set.image_image]

/-- An actual finite canonical period gives the literal cyclic reindexing of every shifted iterate. -/
theorem halfTurnBaseCycle_rotate_iterate {A : Type*} (e : A≃A) (a : A) (n : ℕ)
    (hclose : (e^[n+1]) a=a) (s : ℕ) (i : Fin (n+1)) :
    (e^[s]) ((e^[i.val]) a)=(e^[(((finRotate (n+1))^s) i).val]) a := by
  induction s with
  | zero=>simp
  | succ s ih=>
    rw [Function.iterate_succ_apply',ih]
    simpa only [pow_succ',Equiv.Perm.coe_mul,Function.comp_apply] using
      _root_.LowDimensionalTopology.Geometry.Polygon.equiv_iterate_finRotate_of_period e a n hclose (((finRotate (n+1))^s) i)

/-- A proved actual base fan transports to any actual canonical cyclic starting
flag by its literal copy label; no new covering or disjointness premise is added. -/
theorem halfTurnBaseCycle_recenter {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (f₀ f₁ : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonVertexFlag Q hf) (n : ℕ) (r : ℝ)
    (hclose : ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n+1]) (1,f₀)=(1,f₀))
    (hcover : (⋃j : Fin (n+1),S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f₀))) r)=
        Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₀.val.1) r)
    (hdisj : Pairwise (fun i j : Fin (n+1)=>Disjoint
      (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
        (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[i.val]) (1,f₀))) r)
      (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
        (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f₀))) r)))
    (s : ℕ) (h : S.Generated)
    (hstate : ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[s]) (1,f₀)=(h,f₁)) :
    (⋃j : Fin (n+1),S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f₁))) r)=
        Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₁.val.1) r ∧
    Pairwise (fun i j : Fin (n+1)=>Disjoint
      (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
        (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[i.val]) (1,f₁))) r)
      (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
        (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,f₁))) r)) := by
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S
  let a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S:=(1,f₀)
  let φ : Fin (n+1)≃Fin (n+1):=(finRotate (n+1))^s
  let C (j : Fin (n+1)):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((e^[j.val]) a)
  let C₁ (j : Fin (n+1)):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S ((e^[j.val]) (1,f₁))
  have hstart : (1,f₁)=(h⁻¹*((e^[s]) a).1,((e^[s]) a).2):=by
    rw [hstate]
    simp
  have hnew (j : Fin (n+1)) : (e^[j.val]) (1,f₁)=
      (h⁻¹*((e^[(φ j).val]) a).1,((e^[(φ j).val]) a).2):=by
    rw [hstart,halfTurnBaseCycle_iterate_left]
    have he : (e^[j.val]) ((e^[s]) a)=(e^[s]) ((e^[j.val]) a):=by
      rw [←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm]
    rw [he,halfTurnBaseCycle_rotate_iterate e a n hclose s j]
  have hcopy (j : Fin (n+1)) : C₁ j=(h⁻¹*(C (φ j)).1,(C (φ j)).2):=by
    dsimp only [C₁]
    rw [hnew]
    rfl
  have hp (j : Fin (n+1)) :
      S.vertexCyclePiece (C₁ j) r=(h⁻¹).val '' S.vertexCyclePiece (C (φ j)) r ∧
      S.vertexCycleInteriorPiece (C₁ j) r=(h⁻¹).val '' S.vertexCycleInteriorPiece (C (φ j)) r:=by
    rw [hcopy]
    exact halfTurnBaseCycle_piece_left Q hf S h⁻¹ (C (φ j)) r
  have heval : h • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₁.val.1=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₀.val.1:=by
    have hh:=halfTurnBaseCycle_iterate_evaluation Q hf S a s
    rw [hstate] at hh
    change h • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₁.val.1=(1 : S.Generated) • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₀.val.1 at hh
    simpa only [one_smul] using hh
  have hcenter : (h⁻¹).val (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₀.val.1)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₁.val.1:=by
    change h⁻¹ • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₀.val.1=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf f₁.val.1
    rw [←heval,inv_smul_smul]
  constructor
  · change (⋃j,S.vertexCyclePiece (C₁ j) r)=_
    simp_rw [fun j=>(hp j).1]
    rw [←Set.image_iUnion]
    have hu : (⋃j,S.vertexCyclePiece (C (φ j)) r)=⋃j,S.vertexCyclePiece (C j) r:=by
      ext z
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j,hj⟩
        exact ⟨φ j,hj⟩
      · rintro ⟨j,hj⟩
        obtain ⟨i,rfl⟩:=φ.surjective j
        exact ⟨i,hj⟩
    rw [hu,hcover,(h⁻¹).val.image_ball,hcenter]
  · intro i j hij
    change Disjoint (S.vertexCycleInteriorPiece (C₁ i) r) (S.vertexCycleInteriorPiece (C₁ j) r)
    rw [(hp i).2,(hp j).2]
    exact Set.disjoint_image_of_injective (h⁻¹).val.injective (hdisj (φ.injective.ne hij))


/-- The exact original canonical-cycle subclauses at one indexed finite vertex. -/
def HalfTurnBaseCycleAt {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (i : Fin m) (n : ℕ) (r : ℝ) : Prop :=
  ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n+1])
    (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i)=(1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i) ∧
  (⋃j : Fin (n+1),S.vertexCyclePiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
    (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r)=
      Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) r ∧
  Pairwise (fun j k : Fin (n+1)=>Disjoint
    (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r)
    (S.vertexCycleInteriorPiece (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[k.val]) (1,_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonOutgoingFlag Q hf i))) r))

section FourBaseCycles
variable (t : ℝ) (ht : 1<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
local notation "P₄" => finiteDiscPoincarePolygon Q₄ hf₄
local notation "S₄" => halfTurnFour_pairing t ht w hw hn hc
local notation "e₄" => finitePolygonSideEquiv Q₄ hf₄
local notation "f₄" => finitePolygonOutgoingFlag Q₄ hf₄
local notation "σ₄" => finitePolygonCanonicalVertexStep Q₄ hf₄ S₄
local notation "E₄" => halfTurnPrimitiveFourBaseMaps t (zero_lt_one.trans ht)

/-- The actual four canonical base copy labels are exactly 1,G,F1,D inverse. -/
theorem halfTurnBaseCycle_four_origin_labels (j : Fin 4) :
    (((σ₄^[j.val]) (1,f₄ 0)).1).val=E₄ j := by
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht))
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one)
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans ht)))
  have hG2 : G*G=1:=inv_eq_iff_mul_eq_one.mp (halfTurnNative_axis_inverse t (zero_lt_one.trans ht))
  have hD : D=G*F:=halfTurnFour_dilation_product t ht
  have hGD : G*D=F:=by
    rw [hD,←mul_assoc,hG2,one_mul]
  have h0 (g : (S₄).Generated) : σ₄ (g,f₄ 0)=(g*((S₄).generator (e₄ 0))⁻¹,f₄ 1):=
    halfTurnWalk_four_step t ht w hw hn hc 0 g
  have h1 (g : (S₄).Generated) : σ₄ (g,f₄ 1)=(g*((S₄).generator (e₄ 1))⁻¹,f₄ 0):=
    halfTurnWalk_four_step t ht w hw hn hc 1 g
  fin_cases j
  · rfl
  · change (σ₄ (1,f₄ 0)).1.val=G
    rw [halfTurnWalk_four_step t ht w hw hn hc 0]
    change ((S₄).element (e₄ 0))⁻¹=G
    rw [halfTurnFour_pairing_element_index]
    exact halfTurnNative_axis_inverse t (zero_lt_one.trans ht)
  · change (σ₄ (σ₄ (1,f₄ 0))).1.val=F
    rw [h0,h1]
    change ((S₄).element (e₄ 0))⁻¹*((S₄).element (e₄ 1))⁻¹=F
    rw [halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
    change G⁻¹*(D⁻¹)⁻¹=F
    rw [inv_inv,show G⁻¹=G from halfTurnNative_axis_inverse t (zero_lt_one.trans ht)]
    exact hGD
  · change (σ₄ (σ₄ (σ₄ (1,f₄ 0)))).1.val=D⁻¹
    rw [h0,h1,h0]
    change (((S₄).element (e₄ 0))⁻¹*((S₄).element (e₄ 1))⁻¹)*((S₄).element (e₄ 0))⁻¹=D⁻¹
    rw [halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
    change (G⁻¹*(D⁻¹)⁻¹)*G⁻¹=D⁻¹
    rw [inv_inv,show G⁻¹=G from halfTurnNative_axis_inverse t (zero_lt_one.trans ht),hGD]
    change F*G=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _))⁻¹
    rw [halfTurnFour_dilation_product t ht,mul_inv_rev,halfTurnNative_axis_inverse,halfTurnNative_axis_inverse]

/-- The actual canonical four-step origin cycle has a full native ball fan. -/
theorem halfTurnBaseCycle_four_origin :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₄ hf₄ S₄ 0 3 r := by
  have hv : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0=UpperHalfPlane.I:=by
    have hh:=halfTurnWalk_four_axis_vertices (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0).re=UpperHalfPlane.I.re
      rw [hh.1,UpperHalfPlane.I_re]
    · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0).im=UpperHalfPlane.I.im
      rw [hh.2.1,UpperHalfPlane.I_im]
  let C (j : Fin 4):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ ((σ₄^[j.val]) (1,f₄ 0))
  have hp (j : Fin 4) (r : ℝ) :
      (S₄).vertexCyclePiece (C j) r=Metric.ball UpperHalfPlane.I r ∩ E₄ j '' (P₄).carrier ∧
      (S₄).vertexCycleInteriorPiece (C j) r=Metric.ball UpperHalfPlane.I r ∩ E₄ j '' (P₄).interior:=by
    have he : (S₄).copyEvaluation (C j)=UpperHalfPlane.I:=by
      have hh:=halfTurnBaseCycle_iterate_evaluation Q₄ hf₄ S₄ (1,f₄ 0) j.val
      change (S₄).copyEvaluation (C j)=(1 : (S₄).Generated) • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0 at hh
      rw [one_smul,hv] at hh
      exact hh
    have hh:=halfTurnBaseCycle_piece_ball Q₄ hf₄ S₄ (C j) r
    rw [he] at hh
    change _=(_∩(((σ₄^[j.val]) (1,f₄ 0)).1).val '' (P₄).carrier) ∧
      _=(_∩(((σ₄^[j.val]) (1,f₄ 0)).1).val '' (P₄).interior) at hh
    rw [halfTurnBaseCycle_four_origin_labels] at hh
    exact hh
  obtain ⟨r,hr,hcover,hdisj⟩:=halfTurnPrimitive_four_base_fan t (t^2/w.re) ht hc
  refine ⟨r,hr,halfTurnWalk_four_base_period t ht w hw hn hc 0 1,?_,?_⟩
  · change (⋃j : Fin 4,(S₄).vertexCyclePiece (C j) r)=_
    have he : (⋃j : Fin 4,(S₄).vertexCyclePiece (C j) r)=
        ⋃j : Fin 4,Metric.ball UpperHalfPlane.I r ∩ E₄ j '' (P₄).carrier:=by
      apply iUnion_congr
      intro j
      exact (hp j r).1
    rw [he,hv]
    exact hcover
  · intro i j hij
    change Disjoint ((S₄).vertexCycleInteriorPiece (C i) r) ((S₄).vertexCycleInteriorPiece (C j) r)
    rw [(hp i r).2,(hp j r).2]
    exact hdisj hij

/-- Both genuine quadrilateral base vertices satisfy the original complete
canonical-cycle clauses, with true word closure and actual ball pieces. -/
theorem halfTurnBaseCycle_four_all (i : Fin 2) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₄ hf₄ S₄ (i.castLE (by decide : 2≤4)) 3 r := by
  obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_four_origin t ht w hw hn hc
  refine ⟨r,hr,?_⟩
  fin_cases i
  · exact hAt
  · change HalfTurnBaseCycleAt Q₄ hf₄ S₄ 1 3 r
    let h:=((S₄).generator (e₄ 0))⁻¹
    have hs : (σ₄^[1]) (1,f₄ 0)=(h,f₄ 1):=by
      change σ₄ (1,f₄ 0)=(h,f₄ 1)
      rw [halfTurnWalk_four_step t ht w hw hn hc 0]
      simp only [one_mul]
      rfl
    refine ⟨halfTurnWalk_four_base_period t ht w hw hn hc 1 1,?_⟩
    exact halfTurnBaseCycle_recenter Q₄ hf₄ S₄ (f₄ 0) (f₄ 1) 3 r
      hAt.1 hAt.2.1 hAt.2.2 1 h hs
end FourBaseCycles


section FiveBaseCycles
variable (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₅" => halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
local notation "hf₅" => halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
local notation "P₅" => finiteDiscPoincarePolygon Q₅ hf₅
local notation "S₅" => halfTurnFivePairing u t hu hut w hw hn hc
local notation "e₅" => finitePolygonSideEquiv Q₅ hf₅
local notation "f₅" => finitePolygonOutgoingFlag Q₅ hf₅
local notation "σ₅" => finitePolygonCanonicalVertexStep Q₅ hf₅ S₅
local notation "E₅" => halfTurnPrimitiveThreeBaseMaps u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) hc
local notation "P₄" => finiteDiscPoincarePolygon Q₄ hf₄

/-- The three actual five-side canonical base labels are 1,F,D inverse. -/
theorem halfTurnBaseCycle_five_origin_labels (j : Fin 3) :
    (((σ₅^[j.val]) (1,f₅ 0)).1).val=E₅ j := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu))
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t)
    (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))))
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans (hu.trans hut))))
  have hFG : F*G=D⁻¹:=by
    change F*G=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) _))⁻¹
    rw [←halfTurnNative_axis_product u t (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)),
      mul_inv_rev,halfTurnNative_axis_inverse,halfTurnNative_axis_inverse]
  have h0 (g : (S₅).Generated) : σ₅ (g,f₅ 0)=(g*((S₅).generator (e₅ 0))⁻¹,f₅ 1):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 0 g
  have h1 (g : (S₅).Generated) : σ₅ (g,f₅ 1)=(g*((S₅).generator (e₅ 1))⁻¹,f₅ 2):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 1 g
  fin_cases j
  · rfl
  · change (σ₅ (1,f₅ 0)).1.val=F
    rw [h0]
    change ((S₅).element (e₅ 0))⁻¹=F
    rw [halfTurnFivePairing_element_index]
    exact halfTurnNative_axis_inverse u (zero_lt_one.trans hu)
  · change (σ₅ (σ₅ (1,f₅ 0))).1.val=D⁻¹
    rw [h0,h1]
    change ((S₅).element (e₅ 0))⁻¹*((S₅).element (e₅ 1))⁻¹=D⁻¹
    rw [halfTurnFivePairing_element_index,halfTurnFivePairing_element_index]
    change F⁻¹*G⁻¹=D⁻¹
    rw [show F⁻¹=F from halfTurnNative_axis_inverse u (zero_lt_one.trans hu),
      show G⁻¹=G from halfTurnNative_axis_inverse (u*t)
        (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))]
    exact hFG

/-- The genuine three-step canonical base cycle has the proved actual ball fan,
with the unchanged physical closed and open polygon after axis subdivision. -/
theorem halfTurnBaseCycle_five_origin :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₅ hf₅ S₅ 0 2 r := by
  have hb:=halfTurnFive_band_parameters u t hu hut
  have hI : (P₅).interior=(P₄).interior:=
    halfTurnQuadRefined_native_interior (t^2) (t^2/w.re) (u^2) hb.1 hc hb.2.1 hb.2.2
  have hC : (P₅).carrier=(P₄).carrier:=by
    calc
      (P₅).carrier=closure (P₅).interior:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₅ hf₅
      _=closure (P₄).interior:=congrArg closure hI
      _=(P₄).carrier:=(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₄ hf₄).symm
  have hv : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 0=UpperHalfPlane.I:=by
    have h0 : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 0=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0:=
      halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 0
    have ha:=halfTurnWalk_four_axis_vertices (t^2) (t^2/w.re)
      (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) hc
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 0).re=UpperHalfPlane.I.re
      rw [h0,ha.1,UpperHalfPlane.I_re]
    · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 0).im=UpperHalfPlane.I.im
      rw [h0,ha.2.1,UpperHalfPlane.I_im]
  let C (j : Fin 3):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₅ hf₅ S₅ ((σ₅^[j.val]) (1,f₅ 0))
  have hp (j : Fin 3) (r : ℝ) :
      (S₅).vertexCyclePiece (C j) r=Metric.ball UpperHalfPlane.I r ∩ E₅ j '' (P₄).carrier ∧
      (S₅).vertexCycleInteriorPiece (C j) r=Metric.ball UpperHalfPlane.I r ∩ E₅ j '' (P₄).interior:=by
    have he : (S₅).copyEvaluation (C j)=UpperHalfPlane.I:=by
      have hh:=halfTurnBaseCycle_iterate_evaluation Q₅ hf₅ S₅ (1,f₅ 0) j.val
      change (S₅).copyEvaluation (C j)=(1 : (S₅).Generated) • _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 0 at hh
      rw [one_smul,hv] at hh
      exact hh
    have hh:=halfTurnBaseCycle_piece_ball Q₅ hf₅ S₅ (C j) r
    rw [he] at hh
    change _=(_∩(((σ₅^[j.val]) (1,f₅ 0)).1).val '' (P₅).carrier) ∧
      _=(_∩(((σ₅^[j.val]) (1,f₅ 0)).1).val '' (P₅).interior) at hh
    rw [halfTurnBaseCycle_five_origin_labels,hC,hI] at hh
    exact hh
  obtain ⟨r,hr,hcover,hdisj⟩:=halfTurnPrimitive_three_base_fan u t (t^2/w.re) hu hut hc
  refine ⟨r,hr,halfTurnWalk_five_base_period u t hu hut w hw hn hc 0 1,?_,?_⟩
  · change (⋃j : Fin 3,(S₅).vertexCyclePiece (C j) r)=_
    have he : (⋃j : Fin 3,(S₅).vertexCyclePiece (C j) r)=
        ⋃j : Fin 3,Metric.ball UpperHalfPlane.I r ∩ E₅ j '' (P₄).carrier:=by
      apply iUnion_congr
      intro j
      exact (hp j r).1
    rw [he,hv]
    exact hcover
  · intro i j hij
    change Disjoint ((S₅).vertexCycleInteriorPiece (C i) r) ((S₅).vertexCycleInteriorPiece (C j) r)
    rw [(hp i r).2,(hp j r).2]
    exact hdisj hij

/-- All three actual five-side base vertices satisfy the original canonical
cycle clauses, including the genuine straight axis subdivision vertex. -/
theorem halfTurnBaseCycle_five_all (i : Fin 3) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₅ hf₅ S₅ (i.castLE (by decide : 3≤5)) 2 r := by
  obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_five_origin u t hu hut w hw hn hc
  refine ⟨r,hr,?_⟩
  have h0 (g : (S₅).Generated) : σ₅ (g,f₅ 0)=(g*((S₅).generator (e₅ 0))⁻¹,f₅ 1):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 0 g
  have h1 (g : (S₅).Generated) : σ₅ (g,f₅ 1)=(g*((S₅).generator (e₅ 1))⁻¹,f₅ 2):=
    halfTurnWalk_five_step u t hu hut w hw hn hc 1 g
  fin_cases i
  · exact hAt
  · change HalfTurnBaseCycleAt Q₅ hf₅ S₅ 1 2 r
    let h:=((S₅).generator (e₅ 0))⁻¹
    have hs : (σ₅^[1]) (1,f₅ 0)=(h,f₅ 1):=by
      change σ₅ (1,f₅ 0)=(h,f₅ 1)
      rw [h0]
      simp only [one_mul]
      rfl
    refine ⟨halfTurnWalk_five_base_period u t hu hut w hw hn hc 1 1,?_⟩
    exact halfTurnBaseCycle_recenter Q₅ hf₅ S₅ (f₅ 0) (f₅ 1) 2 r
      hAt.1 hAt.2.1 hAt.2.2 1 h hs
  · change HalfTurnBaseCycleAt Q₅ hf₅ S₅ 2 2 r
    let h:=((S₅).generator (e₅ 0))⁻¹*((S₅).generator (e₅ 1))⁻¹
    have hs : (σ₅^[2]) (1,f₅ 0)=(h,f₅ 2):=by
      change σ₅ (σ₅ (1,f₅ 0))=(h,f₅ 2)
      rw [h0,h1]
      simp only [one_mul]
      rfl
    refine ⟨halfTurnWalk_five_base_period u t hu hut w hw hn hc 2 1,?_⟩
    exact halfTurnBaseCycle_recenter Q₅ hf₅ S₅ (f₅ 0) (f₅ 2) 2 r
      hAt.1 hAt.2.1 hAt.2.2 2 h hs
end FiveBaseCycles

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
open scoped ComplexConjugate

/-- The actual unit mirror has the literal reciprocal radial coordinates. -/
theorem halfTurnSummit_unit_mirror_coordinates (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re=z.re/(z.re^2+z.im^2) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).im=z.im/(z.re^2+z.im^2) ∧
    ‖(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z : ℂ)‖=1/‖(z : ℂ)‖ := by
  refine ⟨?_,?_,?_⟩
  · simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_re,sub_zero,zero_add,one_pow,one_mul]
  · simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_im,sub_zero,one_pow,one_mul]
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
    simp only [Complex.ofReal_zero,Complex.ofReal_one,one_pow,zero_add,sub_zero,
      norm_div,norm_one,Complex.norm_conj]

/-- The actual inverse radial copy and the unit-mirror copy of the closed
quadrilateral coincide, including all original boundary points. -/
theorem halfTurnSummit_radial_mirror_closed_membership (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) (z : ℍ) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk) • z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier := by
  dsimp only
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  have hC (x : ℍ) : x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔
      1≤‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖≤k ∧ 0≤x.re ∧0≤x.re^2+x.im^2-2*c*x.re+k:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff Q hf x).trans
      (halfTurnQuadCanonical_native_closedCarrier k c hk hc x)
  have hk0:0<k:=zero_lt_one.trans hk
  have hN : 0<z.re^2+z.im^2:=by nlinarith only [sq_pos_of_pos z.im_pos,sq_nonneg z.re]
  have hr : 0<‖(z : ℂ)‖:=norm_pos_iff.mpr z.ne_zero
  have hR:=halfTurnSummit_unit_mirror_coordinates z
  have hpolyD : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).re^2+(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).im^2-
      2*c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).re+k=
      k*(k*(z.re^2+z.im^2)-2*c*z.re+1):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im]
    ring
  have hpolyR : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re^2+(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).im^2-
      2*c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re+k=
      (k*(z.re^2+z.im^2)-2*c*z.re+1)/(z.re^2+z.im^2):=by
    rw [hR.1,hR.2.1]
    field_simp
    ring
  rw [hC,hC,hpolyD,hpolyR,sideOpposition_dilation_norm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,hR.1,hR.2.2]
  have hnlo : 1≤1/‖(z : ℂ)‖ ↔ ‖(z : ℂ)‖≤1:=by
    rw [le_div_iff₀ hr,one_mul]
  have hnhi : 1/‖(z : ℂ)‖≤k ↔1≤k*‖(z : ℂ)‖:=by rw [div_le_iff₀ hr]
  rw [hnlo,hnhi,show k*‖(z : ℂ)‖≤k ↔ ‖(z : ℂ)‖≤1 by
    simpa only [mul_one] using (mul_le_mul_iff_right₀ hk0 : k*‖(z : ℂ)‖≤k*1 ↔ ‖(z : ℂ)‖≤1)]
  rw [mul_nonneg_iff_of_pos_left hk0,mul_nonneg_iff_of_pos_left hk0,
    le_div_iff₀ hN,le_div_iff₀ hN,zero_mul]
  tauto

/-- The corresponding original open copies coincide as well; this retains
strict inequalities needed for genuine disjoint open vertex pieces. -/
theorem halfTurnSummit_radial_mirror_open_membership (k c : ℝ) (hk : 1<k)
    (hc : k+1<2*c) (z : ℍ) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk) • z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior := by
  dsimp only
  have hk0:0<k:=zero_lt_one.trans hk
  have hN : 0<z.re^2+z.im^2:=by nlinarith only [sq_pos_of_pos z.im_pos,sq_nonneg z.re]
  have hr : 0<‖(z : ℂ)‖:=norm_pos_iff.mpr z.ne_zero
  have hR:=halfTurnSummit_unit_mirror_coordinates z
  have hpolyD : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).re^2+(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).im^2-
      2*c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • z).re+k=
      k*(k*(z.re^2+z.im^2)-2*c*z.re+1):=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im]
    ring
  have hpolyR : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re^2+(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).im^2-
      2*c*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re+k=
      (k*(z.re^2+z.im^2)-2*c*z.re+1)/(z.re^2+z.im^2):=by
    rw [hR.1,hR.2.1]
    field_simp
    ring
  rw [halfTurnQuadCanonical_native_interior,halfTurnQuadCanonical_native_interior,
    hpolyD,hpolyR,sideOpposition_dilation_norm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,hR.1,hR.2.2]
  have hnlo : 1<1/‖(z : ℂ)‖ ↔ ‖(z : ℂ)‖<1:=by rw [lt_div_iff₀ hr,one_mul]
  have hnhi : 1/‖(z : ℂ)‖<k ↔1<k*‖(z : ℂ)‖:=by rw [div_lt_iff₀ hr]
  rw [hnlo,hnhi,show k*‖(z : ℂ)‖<k ↔ ‖(z : ℂ)‖<1 by
    simpa only [mul_one] using (mul_lt_mul_iff_right₀ hk0 : k*‖(z : ℂ)‖<k*1 ↔ ‖(z : ℂ)‖<1)]
  rw [mul_pos_iff_of_pos_left hk0,mul_pos_iff_of_pos_left hk0,
    div_pos_iff_of_pos_right hN,div_pos_iff_of_pos_right hN]
  tauto

end LowDimensionalTopology.Geometry.Fuchsian

open scoped ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal third mirror is an actual positive-radius semicircle. -/
theorem halfTurnSummit_radius_pos (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    0<c^2-k := by
  have hc0:0<c:=by linarith only [hk,hc]
  nlinarith only [hc,hc0,hk,sq_nonneg (k-1)]

/-- The actual lower support of the original polygon is the genuine unit mirror. -/
theorem halfTurnSummit_unit_support (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon 3=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one := by
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let x:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let y:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate 4 3)
  have hx: x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q 3:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf 3
  have hy: y∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q 3:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf 3
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _ ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf).ne (by decide : (3 : Fin 4)≠finRotate 4 3))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q 3 hx) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q 3 hy)
  · have hh:=(halfTurnFour_side_coordinates k c hk hc 3 x).mp hx
    change ‖(x : ℂ)-(0 : ℂ)‖=1
    simpa only [sub_zero] using hh.1
  · have hh:=(halfTurnFour_side_coordinates k c hk hc 3 y).mp hy
    change ‖(y : ℂ)-(0 : ℂ)‖=1
    simpa only [sub_zero] using hh.1

/-- The actual third support is the real-centered circle defined by its
literal expanded equation, with its radius proved positive. -/
theorem halfTurnSummit_third_support (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon 2=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c (Real.sqrt (c^2-k)) (Real.sqrt_pos.mpr (halfTurnSummit_radius_pos k c hk hc)) := by
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let x:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 2
  let y:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf (finRotate 4 2)
  have hx: x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q 2:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf 2
  have hy: y∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q 2:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_right_mem Q hf 2
  have hm (z : ℍ) (hz:z∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q 2) :
      z∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c (Real.sqrt (c^2-k)) (Real.sqrt_pos.mpr (halfTurnSummit_radius_pos k c hk hc))).carrier := by
    have hh:=(halfTurnFour_side_coordinates k c hk hc 2 z).mp hz
    change ‖(z : ℂ)-(c : ℂ)‖=Real.sqrt (c^2-k)
    apply (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt (halfTurnSummit_radius_pos k c hk hc).le,←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,
      UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero]
    nlinarith only [hh.2.2.2]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.eq_of_two_points _ _
    ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_injective Q hf).ne (by decide : (2 : Fin 4)≠finRotate 4 2))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q 2 hx) (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q 2 hy) (hm x hx) (hm y hy)

/-- The actual canonical product is the product of the two actual summit
mirrors, in the order compatible with the original flag walk. -/
theorem halfTurnSummit_product_mirrors (k : ℝ) (hk : 1<k) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=k) (hc : k+1<2*(k/w.re)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (k/w.re)
        (Real.sqrt ((k/w.re)^2-k)) (Real.sqrt_pos.mpr (halfTurnSummit_radius_pos k (k/w.re) hk hc)))=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk)))⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w) := by
  let c:=k/w.re
  have hk0:0<k:=zero_lt_one.trans hk
  have hc0:0<c:=div_pos hk0 hw
  have hr : (Real.sqrt (c^2-k) : ℂ)^2=(c : ℂ)^2-k:=by
    exact_mod_cast Real.sq_sqrt (halfTurnSummit_radius_pos k c hk hc).le
  apply IsometryEquiv.ext
  intro z
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0)).injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0 • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection c (Real.sqrt (c^2-k)) _ z))=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0))
        (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k hk0))⁻¹) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)) z))
  rw [IsometryEquiv.apply_inv_self]
  apply UpperHalfPlane.ext
  change _=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w • z : ℍ) : ℂ)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe,pointHalfTurnSL_fractional_coe,hn]
  simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_add,one_pow,sub_zero,
    map_add,map_sub,map_div₀,map_pow,Complex.conj_conj,Complex.conj_ofReal]
  rw [hr]
  have hz : (z : ℂ)-(w.re : ℂ)≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.sub_im,UpperHalfPlane.coe_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact z.im_ne_zero hi
  have hcz : (c : ℂ)*(z : ℂ)-(k : ℂ)≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
      UpperHalfPlane.coe_im,zero_mul,add_zero,sub_zero,Complex.zero_im] at hi
    exact (mul_pos hc0 z.im_pos).ne' hi
  have hzc : (z : ℂ)-(c : ℂ)≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.sub_im,UpperHalfPlane.coe_im,Complex.ofReal_im,sub_zero,Complex.zero_im] at hi
    exact z.im_ne_zero hi
  have he : (c : ℂ)+((c : ℂ)^2-(k : ℂ))/((z : ℂ)-(c : ℂ))=
      ((c : ℂ)*(z : ℂ)-(k : ℂ))/((z : ℂ)-(c : ℂ)):=by
    field_simp [hzc]
    ring
  rw [he,one_div_div]
  field_simp [hz,hcz]
  dsimp only [c]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hw.ne',Complex.ofReal_ne_zero.mpr hk0.ne']

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
local instance halfTurnSummitIndexDiscMetric : MetricSpace 𝔻:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric

/-- Words in two actual involutive mirrors alternate between a power of
their product and such a power followed by the first mirror. -/
theorem halfTurnSummit_mirror_word {G : Type*} [Group G] (a b : G)
    (ha : a⁻¹=a) (hb : b⁻¹=b) (g : G) (hg : g∈Subgroup.closure ({a,b} : Set G)) :
    ∃k : ℤ,g=(a*b)^k ∨ g=(a*b)^k*a := by
  let A:=a*b
  have haa:a*a=1:=by simpa only [ha] using inv_mul_cancel a
  have hsem:SemiconjBy a A A⁻¹:=by
    change a*(a*b)=(a*b)⁻¹*a
    calc
      a*(a*b)=(a*a)*b:=(mul_assoc a a b).symm
      _=b:=by rw [haa,one_mul]
      _=(a*b)⁻¹*a:=by simp only [mul_inv_rev,ha,hb,mul_assoc,haa,mul_one]
  have hcomm (k : ℤ) : a*A^k=A^(-k)*a:=by
    have hh:=hsem.zpow_right k
    change a*A^k=(A⁻¹)^k*a at hh
    simpa only [inv_zpow',zpow_neg] using hh
  induction hg using Subgroup.closure_induction with
  | mem g hg=>
    rcases hg with rfl|rfl
    · exact ⟨0,Or.inr (by simp)⟩
    · refine ⟨-1,Or.inr ?_⟩
      simp only [zpow_neg_one,mul_inv_rev,ha,hb,mul_assoc,haa,mul_one]
  | one=>exact ⟨0,Or.inl (by simp)⟩
  | mul x y _ _ hx hy=>
    obtain ⟨k,hk|hk⟩:=hx <;> obtain ⟨l,hl|hl⟩:=hy
    · exact ⟨k+l,Or.inl (by rw [hk,hl,zpow_add])⟩
    · exact ⟨k+l,Or.inr (by rw [hk,hl,zpow_add,mul_assoc])⟩
    · refine ⟨k-l,Or.inr ?_⟩
      rw [hk,hl,mul_assoc,hcomm,←mul_assoc,←zpow_add]
      congr 1
    · refine ⟨k-l,Or.inl ?_⟩
      rw [hk,hl,mul_assoc,←mul_assoc a _ a,hcomm,mul_assoc _ a a,haa,mul_one,←zpow_add]
      congr 1
  | inv x _ hx=>
    obtain ⟨k,hk|hk⟩:=hx
    · exact ⟨-k,Or.inl (by rw [hk,zpow_neg])⟩
    · refine ⟨k,Or.inr ?_⟩
      rw [hk,mul_inv_rev,ha,←zpow_neg,hcomm,neg_neg]

/-- Genuine finite product order reduces the actual alternating words to a
finite list; no injectivity or geometric tiling is assumed. -/
theorem halfTurnSummit_mirror_finite_words {G : Type*} [Group G] (a b : G)
    (ha : a⁻¹=a) (hb : b⁻¹=b) (q : ℕ) (hq : 0<q) (horder : orderOf (a*b)=q)
    (g : G) (hg : g∈Subgroup.closure ({a,b} : Set G)) :
    ∃i : Fin q,∃s : Bool,g=(a*b)^i.val*(if s then a else 1) := by
  classical
  obtain ⟨k,hk⟩:=halfTurnSummit_mirror_word a b ha hb g hg
  have hfin:IsOfFinOrder (a*b):=orderOf_pos_iff.mp (horder ▸ hq)
  have hm:(a*b)^k∈Subgroup.zpowers (a*b):=⟨k,rfl⟩
  obtain ⟨i,hi,he⟩:=Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hm)
  have hiq : i<q:=by simpa only [Finset.mem_range,horder] using hi
  refine ⟨⟨i,hiq⟩,?_⟩
  rcases hk with hk|hk
  · exact ⟨false,by simpa only [Bool.false_eq_true,ite_false,mul_one] using hk.trans he.symm⟩
  · exact ⟨true,by simpa only [ite_true,he] using hk⟩

/-- Restriction of a genuine planar linear isometry to the actual open disc
is faithful, by scaling each test vector into that disc. -/
theorem halfTurnSummit_discOrthogonal_injective : Function.Injective _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalHom := by
  intro L M he
  apply LinearIsometryEquiv.ext
  intro z
  let t:ℝ:=(‖z‖+1)⁻¹
  have ht:0<t:=inv_pos.mpr (by positivity)
  have hw:‖t • z‖<1:=by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp only [t]
    rw [inv_mul_lt_iff₀ (by positivity : 0<‖z‖+1)]
    linarith
  let w:𝔻:=Complex.UnitDisc.mk (t • z) hw
  have hh:=congrArg (fun f : 𝔻≃ᵢ𝔻=>(f w : ℂ)) he
  change L (t • z)=M (t • z) at hh
  rw [map_smul,map_smul] at hh
  have hh':=congrArg (fun v : ℂ=>t⁻¹ • v) hh
  simpa only [inv_smul_smul₀ ht.ne'] using hh'

/-- The actual native two-mirror group has exactly twice the true reciprocal
angle denominator, by the faithful original angular chart. -/
theorem halfTurnSummit_mirror_group_card {p : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne : R.supportLine≠S.supportLine) (q : ℕ) (hq : 2≤q)
    (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/(q : ℝ)) :
    Nat.card (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ)))=2*q := by
  obtain ⟨e,_he0,_hCone,hGroup,_hPair⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_group_chart R S hne q hq hangle
  have hc:=Subgroup.card_map_of_injective (K:=Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ)))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_injective e)
  rw [hGroup] at hc
  rw [←hc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralGroup,Subgroup.card_map_of_injective halfTurnSummit_discOrthogonal_injective,
    _root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarDihedralGroup_card q (by omega)]

/-- The literal alternating two-mirror words enumerate the whole actual
finite mirror group bijectively; faithfulness follows from its proved size. -/
def halfTurnSummit_mirrorIndexEquiv {p : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne : R.supportLine≠S.supportLine) (q : ℕ) (hq : 2≤q)
    (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/(q : ℝ))
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine)=q) :
    (Fin q×Bool)≃Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ)) := by
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine
  let H:=Subgroup.closure ({a,b} : Set (ℍ≃ᵢℍ))
  have ha:a∈H:=Subgroup.subset_closure (by simp)
  have hb:b∈H:=Subgroup.subset_closure (by simp)
  let f : (Fin q×Bool)→H:=fun v=>⟨(a*b)^v.1.val*(if v.2 then a else 1),
    H.mul_mem (H.pow_mem (H.mul_mem ha hb) _) (by split;exact ha;exact H.one_mem)⟩
  have hf:Function.Surjective f:=by
    rintro ⟨g,hg⟩
    obtain ⟨i,s,he⟩:=halfTurnSummit_mirror_finite_words a b (by rfl) (by rfl) q (by omega) horder g hg
    exact ⟨(i,s),Subtype.ext he.symm⟩
  apply Equiv.ofBijective f
  apply (Nat.bijective_iff_surjective_and_card f).mpr
  refine ⟨hf,?_⟩
  have hc:=halfTurnSummit_mirror_group_card R S hne q hq hangle
  change Nat.card (Fin q×Bool)=Nat.card H
  rw [hc,Nat.card_prod]
  simp [Nat.mul_comm]

theorem halfTurnSummit_mirrorIndexEquiv_val {p : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne : R.supportLine≠S.supportLine) (q : ℕ) (hq : 2≤q)
    (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/(q : ℝ))
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine)=q) (v : Fin q×Bool) :
    (halfTurnSummit_mirrorIndexEquiv R S hne q hq hangle horder v).val=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine)^v.1.val*
        (if v.2 then _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine else 1) := rfl

/-- The actual alternating mirror words give a true full-ball fan with
pairwise disjoint open angular pieces, in the physical native plane. -/
theorem halfTurnSummit_mirror_ball_fan {p : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p)
    (hne : R.supportLine≠S.supportLine) (q : ℕ) (hq : 2≤q)
    (hangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/(q : ℝ))
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine)=q) (r : ℝ) :
    let eI:=halfTurnSummit_mirrorIndexEquiv R S hne q hq hangle horder
    let C:=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
    (⋃v : Fin q×Bool,(eI v).val '' (C∩Metric.ball p r))=Metric.ball p r ∧
      Pairwise (fun v w : Fin q×Bool=>Disjoint
        ((eI v).val '' interior C) ((eI w).val '' interior C)) := by
  let eI:=halfTurnSummit_mirrorIndexEquiv R S hne q hq hangle horder
  let C:=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
  let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ))
  obtain ⟨e,he0,hCone,hGroup,_hPair⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_group_chart R S hne q hq hangle
  have hMember (g : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e g.val∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralGroup q:=by
    rw [←hGroup]
    exact ⟨g.val,g.property,rfl⟩
  have hFix (g : H) : g.val p=p:=by
    obtain ⟨i,b,hg⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralGroup_normal_form q (by omega) _ (hMember g)
    apply e.injective
    calc
      e (g.val p)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation e g.val (e p):=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply e g.val p).symm
      _=0:=by rw [hg,he0];exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discOrthogonalMap_zero _
      _=e p:=he0.symm
  have hClosed : C=e.toHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralChamber q:=Set.ext hCone
  have hOpen : interior C=e.toHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralOpenChamber q:=by
    rw [hClosed,←e.toHomeomorph.preimage_interior]
    change e.toHomeomorph ⁻¹' interior {z : 𝔻 | (z : ℂ)∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationClosedPlaneSector (2*q)}=_
    rw [regular_sector_interior (2*q) (by omega)]
    rfl
  constructor
  · ext z
    constructor
    · intro hz
      obtain ⟨v,x,⟨_hx,hxr⟩,rfl⟩:=mem_iUnion.mp hz
      change dist ((eI v).val x) p<r
      have hd:=((eI v).val).dist_eq x p
      have hd' : dist ((eI v).val x) p=dist x p:=by simpa only [hFix (eI v)] using hd
      exact hd'.trans_lt hxr
    · intro hz
      obtain ⟨g,hg,x,hx,hxr,hxz⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.triangleVertex_closed_angle_ball_cover R S hne q hq hangle r z hz
      let v:=eI.symm ⟨g,hg⟩
      have hv:(eI v).val=g:=congrArg Subtype.val (eI.apply_symm_apply ⟨g,hg⟩)
      exact mem_iUnion.mpr ⟨v,x,⟨hx,hxr⟩,by
        change (eI v).val x=z
        rw [hv]
        exact hxz⟩
  · intro v w hvw
    apply disjoint_left.mpr
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    obtain ⟨i,b,hv⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralGroup_normal_form q (by omega) _ (hMember (eI v))
    obtain ⟨j,c,hw⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralGroup_normal_form q (by omega) _ (hMember (eI w))
    have hij:(i,b)≠(j,c):=by
      intro he
      apply hvw
      apply eI.injective
      apply Subtype.ext
      apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_injective e
      rw [hv,hw]
      exact congrArg (fun a : Fin q×Bool=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralAction q a.1 a.2) he
    apply disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedral_open_chamber_disjoint q (by omega) hij)
    · refine ⟨e x,?_,?_⟩
      · change x∈e.toHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralOpenChamber q
        rw [←hOpen]
        exact hx
      · rw [←hv,_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply,hxz]
    · refine ⟨e y,?_,?_⟩
      · change y∈e.toHomeomorph ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discDihedralOpenChamber q
        rw [←hOpen]
        exact hy
      · rw [←hw,_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeDiscConjugation_apply,hyz]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The inside of the actual closed canonical quadrilateral is its original
open polygon, including in the presence of subsequent marked subdivisions. -/
theorem halfTurnSummit_quad_carrier_interior (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    interior (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier=(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior := by
  dsimp only
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  have he:=((halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon_isConvex).interior_closure_eq_of_isOpen
    Q.interior_isOpen Q.interior_isConnected.nonempty
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier]
  change interior (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_closure,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.preimage_interior,he]

/-- The genuine closed and open quadrilateral have the two actual incident
mirror-cone germs at the lower physical summit. -/
theorem halfTurnSummit_quad_cone_germs (k c : ℝ) (hk : 1<k) (hc : k+1<2*c)
    (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos (halfTurnQuadKleinB k c/Real.sqrt ((halfTurnQuadKleinB k c)^2+1-
      (halfTurnQuadKleinA k c)^2))=Real.pi/q) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
    let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3
    let S:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3
    ∃r : ℝ,0<r ∧ ∀z : ℍ,dist z p<r →
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)) ∧
      (z∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior ↔z∈interior (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S))) := by
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3
  let C:=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
  have hb:=halfTurnQuadCanonical_angles k c hk hc
  have hAngle : Q.angle 3=Real.pi/q:=hb.2.2.2.2.2.trans hθ
  have hProper : Q.angle 3≠Real.pi:=by
    rw [hAngle]
    exact (div_lt_self Real.pi_pos (by exact_mod_cast (show 1<q by omega))).ne
  obtain ⟨r,hr,hG⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_closed_angle_germ Q
    (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon_isConvex hf 3 hProper
  have hClosed : ∀ᶠz in 𝓝 p,z∈P.carrier ↔z∈C:=by
    filter_upwards [Metric.ball_mem_nhds p hr] with z hz
    have hh:=hG z hz
    change z∈P.carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
    change z∈P.carrier ↔z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior S R) at hh
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior_comm S R] at hh
    exact hh
  have hOpen : ∀ᶠz in 𝓝 p,z∈P.interior ↔z∈interior C:=by
    have hh:=regular_interior_germ_of_germ hClosed
    filter_upwards [hh] with z hz
    change z∈interior P.carrier ↔_ at hz
    rw [halfTurnSummit_quad_carrier_interior] at hz
    exact hz
  exact Metric.eventually_nhds_iff_ball.mp (hClosed.and hOpen)

/-- A genuine isometry fixing the physical vertex transports actual closed
and open membership germs at that same vertex. -/
theorem halfTurnSummit_image_germ (p : ℍ) (g : ℍ≃ᵢℍ) (hg : g p=p)
    (A B : Set ℍ) (h : ∀ᶠz in 𝓝 p,z∈A ↔z∈B) :
    ∀ᶠz in 𝓝 p,z∈g '' A ↔z∈g '' B := by
  have hgi:g.symm p=p:=by
    apply g.injective
    rw [g.apply_symm_apply,hg]
  have ht : Tendsto g.symm (𝓝 p) (𝓝 p):=by
    simpa only [hgi] using g.symm.continuous.tendsto p
  filter_upwards [ht.eventually h] with z hz
  have hm (C : Set ℍ) : z∈g '' C ↔g.symm z∈C:=by
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [g.symm_apply_apply] using hx
    · intro hx
      exact ⟨g.symm z,hx,g.apply_symm_apply z⟩
  exact (hm A).trans (hz.trans (hm B).symm)

/-- Every actual word in the two physical incident mirrors fixes their
common physical vertex. -/
theorem halfTurnSummit_mirror_fixed {p : ℍ} (R S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt p) (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ))) : g p=p := by
  have hle : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine} : Set (ℍ≃ᵢℍ))≤
      MulAction.stabilizer (ℍ≃ᵢℍ) p:=by
    apply (Subgroup.closure_le _).mpr
    rintro a (rfl|rfl)
    · change R.supportLine.reflection p=p
      exact (R.supportLine.reflection_fixed_iff p).mpr R.start_mem_support
    · change S.supportLine.reflection p=p
      exact (S.supportLine.reflection_fixed_iff p).mpr S.start_mem_support
  exact hle hg

/-- The proved two-mirror angular fan transfers to the actual finite
quadrilateral, through its actual closed and open membership germs. -/
theorem halfTurnSummit_quad_mirror_fan (k c : ℝ) (hk : 1<k) (hc : k+1<2*c)
    (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos (halfTurnQuadKleinB k c/Real.sqrt ((halfTurnQuadKleinB k c)^2+1-
      (halfTurnQuadKleinA k c)^2))=Real.pi/q)
    (horder : let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
      let hf:=halfTurnQuadCanonical_finite k c hk hc
      orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3).supportLine*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3).supportLine)=q) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
    let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3
    let S:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3
    ∃hne : R.supportLine≠S.supportLine,
      ∃ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/q,
      let eI:=halfTurnSummit_mirrorIndexEquiv R S hne q hq ha horder
      ∃r : ℝ,0<r ∧
        (⋃v : Fin q×Bool,Metric.ball p r∩((eI v).val '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier))=Metric.ball p r ∧
        Pairwise (fun v w : Fin q×Bool=>Disjoint
          (Metric.ball p r∩((eI v).val '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior))
          (Metric.ball p r∩((eI w).val '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior))) := by
  dsimp only
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3
  let C:=closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior R S)
  have hAngle:Q.angle 3=Real.pi/q:=(halfTurnQuadCanonical_angles k c hk hc).2.2.2.2.2.trans hθ
  have hProper:Q.angle 3≠Real.pi:=by
    rw [hAngle]
    exact (div_lt_self Real.pi_pos (by exact_mod_cast (show 1<q by omega))).ne
  have hne:R.supportLine≠S.supportLine:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_rays_proper Q hf 3 hProper).symm
  have ha:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S=Real.pi/q:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_comm R S]
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_vertex_angle Q (halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon_isConvex
      hf 3 hProper).trans hAngle
  let eI:=halfTurnSummit_mirrorIndexEquiv R S hne q hq ha horder
  obtain ⟨r₀,hr₀,hg⟩:=halfTurnSummit_quad_cone_germs k c hk hc q hq hθ
  have hC:∀ᶠz in 𝓝 p,z∈P.carrier ↔z∈C:=by
    filter_upwards [Metric.ball_mem_nhds p hr₀] with z hz
    exact (hg z hz).1
  have hO:∀ᶠz in 𝓝 p,z∈P.interior ↔z∈interior C:=by
    filter_upwards [Metric.ball_mem_nhds p hr₀] with z hz
    exact (hg z hz).2
  have hFix (v : Fin q×Bool) : (eI v).val p=p:=halfTurnSummit_mirror_fixed R S _ (eI v).property
  have hFam:∀ᶠz in 𝓝 p,∀v : Fin q×Bool,
      (z∈(eI v).val '' P.carrier ↔z∈(eI v).val '' C) ∧
      (z∈(eI v).val '' P.interior ↔z∈(eI v).val '' interior C):=by
    apply eventually_all.mpr
    intro v
    exact (halfTurnSummit_image_germ p (eI v).val (hFix v) _ _ hC).and
      (halfTurnSummit_image_germ p (eI v).val (hFix v) _ _ hO)
  obtain ⟨r,hr,hB⟩:=Metric.eventually_nhds_iff_ball.mp hFam
  have hFan:=halfTurnSummit_mirror_ball_fan R S hne q hq ha horder r
  have hCut (v : Fin q×Bool) : (eI v).val '' (C∩Metric.ball p r)=
      Metric.ball p r∩((eI v).val '' C):=by
    rw [image_inter (eI v).val.injective,(eI v).val.image_ball,hFix v,inter_comm]
  refine ⟨hne,ha,r,hr,?_,?_⟩
  · ext z
    constructor
    · intro hz
      obtain ⟨v,hv⟩:=mem_iUnion.mp hz
      exact hv.1
    · intro hz
      have hz' : z∈⋃v : Fin q×Bool,(eI v).val '' (C∩Metric.ball p r):=hFan.1.symm ▸ hz
      obtain ⟨v,hv⟩:=mem_iUnion.mp hz'
      change z∈(eI v).val '' (C∩Metric.ball p r) at hv
      rw [hCut] at hv
      exact mem_iUnion.mpr ⟨v,hz,(hB z hz v).1.mpr hv.2⟩
  · intro v w hvw
    apply disjoint_left.mpr
    intro z hz hw
    exact disjoint_left.mp (hFan.2 hvw) ((hB z hz.1 v).2.mp hz.2) ((hB z hw.1 w).2.mp hw.2)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The actual inverse-dilation and unit-mirror copies of the original
closed and open quadrilateral agree as full physical subsets. -/
theorem halfTurnSummit_radial_mirror_copies (k c : ℝ) (hk : 1<k) (hc : k+1<2*c) :
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk))
    let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one)
    (D⁻¹ : ℍ≃ᵢℍ) '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier=R '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ∧
    (D⁻¹ : ℍ≃ᵢℍ) '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior=R '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior := by
  dsimp only
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk))
  let R:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one)
  have hR (z : ℍ) : R (R z)=z:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one).reflection_involutive z
  have h (C : Set ℍ) (hm : ∀z : ℍ,D z∈C ↔R z∈C) : (D⁻¹ : ℍ≃ᵢℍ) '' C=R '' C:=by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hx':D (D⁻¹ x)∈C:=by simpa only [D.apply_inv_self] using hx
      exact ⟨R (D⁻¹ x),(hm _).mp hx',hR _⟩
    · rintro ⟨x,hx,rfl⟩
      have hx':R (R x)∈C:=by simpa only [hR] using hx
      exact ⟨D (R x),(hm _).mpr hx',D.inv_apply_self _⟩
  exact ⟨h _ (halfTurnSummit_radial_mirror_closed_membership k c hk hc),
    h _ (halfTurnSummit_radial_mirror_open_membership k c hk hc)⟩

/-- The actual even and odd flag-walk copies fill a native summit ball with
disjoint open pieces whenever the true summit angle is primitive. -/
theorem halfTurnSummit_actual_summit_image_fan (k : ℝ) (hk : 1<k) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=k) (hc : k+1<2*(k/w.re))
    (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos (halfTurnQuadKleinB k (k/w.re)/Real.sqrt ((halfTurnQuadKleinB k (k/w.re))^2+1-
      (halfTurnQuadKleinA k (k/w.re))^2))=Real.pi/q)
    (horder : orderOf ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk)))⁻¹*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    let c:=k/w.re
    let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite k c hk hc
    let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
    let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk))
    let A:=D⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)
    let E : Fin q×Bool→(ℍ≃ᵢℍ):=fun v=>A^v.1.val*(if v.2 then D⁻¹ else 1)
    ∃r : ℝ,0<r ∧
      (⋃v : Fin q×Bool,Metric.ball p r∩(E v '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier))=Metric.ball p r ∧
      Pairwise (fun v a : Fin q×Bool=>Disjoint
        (Metric.ball p r∩(E v '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior))
        (Metric.ball p r∩(E a '' (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).interior))) := by
  dsimp only
  let c:=k/w.re
  let Q:=(halfTurnQuadCanonicalSupport k c hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite k c hk hc
  let p:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let R:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay Q hf 3
  let S:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay Q hf 3
  let a:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine
  let D:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL k (zero_lt_one.trans hk))
  let A:=D⁻¹*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)
  let E : Fin q×Bool→(ℍ≃ᵢℍ):=fun v=>A^v.1.val*(if v.2 then D⁻¹ else 1)
  let unit:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one)
  have hR : R.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle 0 1 zero_lt_one:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNextRay_support Q hf 3).trans (halfTurnSummit_unit_support k c hk hc)
  have hS : S.supportLine=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle c (Real.sqrt (c^2-k))
      (Real.sqrt_pos.mpr (halfTurnSummit_radius_pos k c hk hc)):=by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPrevRay_support,show (finRotate 4).symm 3=(2 : Fin 4) by decide]
    exact halfTurnSummit_third_support k c hk hc
  have hProduct:a*b=A:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry R.supportLine*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry S.supportLine=A
    rw [hR,hS]
    exact halfTurnSummit_product_mirrors k hk w hw hn hc
  have horder' : orderOf (a*b)=q:=by rw [hProduct];exact horder
  obtain ⟨hne,ha,r,hr,hCov,hDisj⟩:=halfTurnSummit_quad_mirror_fan k c hk hc q hq hθ horder'
  let eI:=halfTurnSummit_mirrorIndexEquiv R S hne q hq ha horder'
  have hCopy:=halfTurnSummit_radial_mirror_copies k c hk hc
  have hMul (g h : ℍ≃ᵢℍ) (C : Set ℍ) : (g*h) '' C=g '' (h '' C):=by rw [image_image];rfl
  have hImage (C : Set ℍ) (hC : (D⁻¹ : ℍ≃ᵢℍ) '' C=unit '' C) (v : Fin q×Bool) :
      (eI v).val '' C=E v '' C:=by
    rw [halfTurnSummit_mirrorIndexEquiv_val]
    change ((a*b)^v.1.val*(if v.2 then a else 1)) '' C=E v '' C
    rw [hProduct]
    rcases v with ⟨i,s⟩
    cases s
    · rfl
    · change (A^i.val*a) '' C=(A^i.val*D⁻¹) '' C
      rw [hMul,hMul]
      have he:a=unit:=congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry hR
      rw [he,←hC]
  refine ⟨r,hr,?_,?_⟩
  · change (⋃v : Fin q×Bool,Metric.ball p r∩(E v '' P.carrier))=Metric.ball p r
    have hc' : (⋃v : Fin q×Bool,Metric.ball p r∩((eI v).val '' P.carrier))=Metric.ball p r:=hCov
    have heSets : (⋃v : Fin q×Bool,Metric.ball p r∩((eI v).val '' P.carrier))=
        (⋃v : Fin q×Bool,Metric.ball p r∩(E v '' P.carrier)):=by
      apply iUnion_congr
      intro v
      rw [hImage P.carrier hCopy.1 v]
    exact heSets.symm.trans hc'
  · change Pairwise (fun v a : Fin q×Bool=>Disjoint
      (Metric.ball p r∩(E v '' P.interior)) (Metric.ball p r∩(E a '' P.interior)))
    intro i j hij
    rw [←hImage P.interior hCopy.2 i,←hImage P.interior hCopy.2 j]
    exact hDisj hij

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual mirror indices in the literal even/odd order of the canonical summit walk. -/
def halfTurnSummitCycleIndex (q : ℕ) : Fin q×Bool≃Fin (2*q) :=
  ((Equiv.prodCongr (Equiv.refl (Fin q)) finTwoEquiv.symm).trans finProdFinEquiv).trans
    (finCongr (Nat.mul_comm q 2))

theorem halfTurnSummitCycleIndex_val (q : ℕ) (v : Fin q×Bool) :
    (halfTurnSummitCycleIndex q v).val=2*v.1.val+(if v.2 then 1 else 0) := by
  rcases v with ⟨i,b⟩
  cases b <;> simp [halfTurnSummitCycleIndex,finProdFinEquiv,finTwoEquiv,Nat.add_comm]

section FourSummitCycles
variable (t : ℝ) (ht : 1<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
local notation "P₄" => finiteDiscPoincarePolygon Q₄ hf₄
local notation "S₄" => halfTurnFour_pairing t ht w hw hn hc
local notation "e₄" => finitePolygonSideEquiv Q₄ hf₄
local notation "f₄" => finitePolygonOutgoingFlag Q₄ hf₄
local notation "σ₄" => finitePolygonCanonicalVertexStep Q₄ hf₄ S₄
local notation "d₄" => (S₄).generator (e₄ 3)
local notation "v₄" => (S₄).generator (e₄ 2)
local notation "a₄" => d₄⁻¹*v₄
local notation "D₄" => hSLIsometry (verticalDilationSL (t^2) (sq_pos_of_pos (zero_lt_one.trans ht)))
local notation "A₄" => D₄⁻¹*hSLIsometry (pointHalfTurnSL w)
local notation "E₄" => (fun v : Fin _×Bool=>A₄^v.1.val*(if v.2 then D₄⁻¹ else 1))

/-- The actual canonical summit labels are the genuine mirror-fan labels in even/odd order. -/
theorem halfTurnSummitCycle_four_labels (q : ℕ) (v : Fin q×Bool) :
    (((σ₄^[(halfTurnSummitCycleIndex q v).val]) (1,f₄ 3)).1).val=E₄ v := by
  have hd : (d₄).val=D₄ := by
    change (S₄).element (e₄ 3)=D₄
    rw [halfTurnFour_pairing_element_index]
    rfl
  have ha : (a₄).val=A₄ := by
    change ((S₄).element (e₄ 3))⁻¹*(S₄).element (e₄ 2)=A₄
    rw [halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
    rfl
  rcases v with ⟨i,b⟩
  cases b
  · rw [halfTurnSummitCycleIndex_val]
    simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Subgroup.coe_mul,Subgroup.coe_one,
      Subgroup.coe_pow,one_mul,ha,mul_one] using
      congrArg (fun a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q₄ hf₄ S₄=>a.1.val)
        (halfTurnWalk_four_summit_iterates t ht w hw hn hc i.val 1).1
  · rw [halfTurnSummitCycleIndex_val]
    simpa only [ite_true,Subgroup.coe_mul,Subgroup.coe_one,Subgroup.coe_pow,Subgroup.coe_inv,
      one_mul,ha,hd] using
      congrArg (fun a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q₄ hf₄ S₄=>a.1.val)
        (halfTurnWalk_four_summit_iterates t ht w hw hn hc i.val 1).2

/-- The genuine primitive summit fan is the literal natural canonical vertex cycle. -/
theorem halfTurnSummitCycle_four_origin (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₄ hf₄ S₄ 3 (2*q-1) r := by
  have hangle : Real.arccos (halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2))=Real.pi/q := by
    rw [halfTurnQuadCanonical_cosine_trace t w.re w.im ht hw w.im_pos hn]
    exact hθ
  have hnative : orderOf A₄=q := by
    rw [halfTurnWalk_summit_native_word 1 t zero_lt_one ht w,
      hSLIsometry_orderOf_eq_realSLMobius]
    simpa only [one_mul] using horder
  obtain ⟨r,hr,hcover,hdisj⟩ := halfTurnSummit_actual_summit_image_fan (t^2)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) w hw hn hc q hq hangle hnative
  let e:=halfTurnSummitCycleIndex q
  let C (j : Fin (2*q)):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ ((σ₄^[j.val]) (1,f₄ 3))
  have hp (j : Fin (2*q)) :
      (S₄).vertexCyclePiece (C j) r=Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩
        E₄ (e.symm j) '' (P₄).carrier ∧
      (S₄).vertexCycleInteriorPiece (C j) r=Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩
        E₄ (e.symm j) '' (P₄).interior := by
    have he : (S₄).copyEvaluation (C j)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3 := by
      have hh:=halfTurnBaseCycle_iterate_evaluation Q₄ hf₄ S₄ (1,f₄ 3) j.val
      change (S₄).copyEvaluation (C j)=(1 : (S₄).Generated)•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3 at hh
      simpa only [one_smul] using hh
    have hl : (((σ₄^[j.val]) (1,f₄ 3)).1).val=E₄ (e.symm j) := by
      have hh:=halfTurnSummitCycle_four_labels t ht w hw hn hc q (e.symm j)
      rw [e.apply_symm_apply] at hh
      exact hh
    have hh:=halfTurnBaseCycle_piece_ball Q₄ hf₄ S₄ (C j) r
    rw [he] at hh
    change _=(_∩(((σ₄^[j.val]) (1,f₄ 3)).1).val '' (P₄).carrier) ∧
      _=(_∩(((σ₄^[j.val]) (1,f₄ 3)).1).val '' (P₄).interior) at hh
    rw [hl] at hh
    exact hh
  refine ⟨r,hr,?_⟩
  have hlen : 2*q-1+1=2*q := by omega
  rw [HalfTurnBaseCycleAt,hlen]
  refine ⟨(halfTurnWalk_four_summit_period t ht w hw hn hc q horder 1).1,?_,?_⟩
  · change (⋃j : Fin (2*q),(S₄).vertexCyclePiece (C j) r)=_
    simp_rw [fun j=>(hp j).1]
    exact (e.symm.surjective.iUnion_comp (fun v : Fin q×Bool=>
      Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩E₄ v '' (P₄).carrier)).trans hcover
  · intro i j hij
    change Disjoint ((S₄).vertexCycleInteriorPiece (C i) r) ((S₄).vertexCycleInteriorPiece (C j) r)
    rw [(hp i).2,(hp j).2]
    exact hdisj (e.symm.injective.ne hij)

/-- Both original quadrilateral summit directions satisfy the complete actual cycle clauses. -/
theorem halfTurnSummitCycle_four_all (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) (i : Fin 2) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₄ hf₄ S₄ (![2,3] i) (2*q-1) r := by
  obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_four_origin t ht w hw hn hc q hq hθ horder
  refine ⟨r,hr,?_⟩
  fin_cases i
  · change HalfTurnBaseCycleAt Q₄ hf₄ S₄ 2 (2*q-1) r
    have hs : (σ₄^[1]) (1,f₄ 3)=(d₄⁻¹,f₄ 2) := by
      change σ₄ (1,f₄ 3)=(d₄⁻¹,f₄ 2)
      rw [halfTurnWalk_four_step t ht w hw hn hc 3]
      simp only [one_mul]
      rfl
    have hlen : 2*q-1+1=2*q := by omega
    refine ⟨?_,?_⟩
    · rw [hlen]
      exact (halfTurnWalk_four_summit_period t ht w hw hn hc q horder 1).2
    · exact halfTurnBaseCycle_recenter Q₄ hf₄ S₄ (f₄ 3) (f₄ 2) (2*q-1) r
        hAt.1 hAt.2.1 hAt.2.2 1 d₄⁻¹ hs
  · exact hAt

/-- All actual quadrilateral canonical vertex cycles follow from the true primitive angle and word order. -/
theorem halfTurnPrimitive_four_cycles (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonCanonicalCycleConditions Q₄ hf₄ S₄ := by
  intro i
  fin_cases i
  · obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_four_all t ht w hw hn hc 0
    exact ⟨3,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_four_all t ht w hw hn hc 1
    exact ⟨3,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_four_all t ht w hw hn hc q hq hθ horder 0
    exact ⟨2*q-1,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_four_all t ht w hw hn hc q hq hθ horder 1
    exact ⟨2*q-1,r,hr,hAt⟩

/-- The proved original side neighborhoods and complete primitive cycles give all of actual local tessellation. -/
theorem halfTurnPrimitive_four_local_tessellation (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    (S₄).FiniteFiberLocalTessellationCondition := by
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q₄ hf₄ S₄
    (halfTurnFour_opposite t ht w hw hn hc)
    (halfTurnPrimitive_four_cycles t ht w hw hn hc q hq hθ horder)

/-- The genuine primitive four-side polygon is an actual fundamental domain for its whole generated group. -/
theorem halfTurnPrimitive_four_poincare (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    DiscreteTopology (S₄).Generated ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (S₄).Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₄).interior) := by
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_poincare Q₄ hf₄ S₄
    (halfTurnFour_opposite t ht w hw hn hc)
    (halfTurnPrimitive_four_cycles t ht w hw hn hc q hq hθ horder)

end FourSummitCycles

section FiveSummitCycles
variable (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₅" => halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
local notation "hf₅" => halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
local notation "P₅" => finiteDiscPoincarePolygon Q₅ hf₅
local notation "S₅" => halfTurnFivePairing u t hu hut w hw hn hc
local notation "e₅" => finitePolygonSideEquiv Q₅ hf₅
local notation "f₅" => finitePolygonOutgoingFlag Q₅ hf₅
local notation "σ₅" => finitePolygonCanonicalVertexStep Q₅ hf₅ S₅
local notation "d₅" => (S₅).generator (e₅ 4)
local notation "v₅" => (S₅).generator (e₅ 3)
local notation "a₅" => d₅⁻¹*v₅
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) hc
local notation "P₄" => finiteDiscPoincarePolygon Q₄ hf₄
local notation "D₅" => hSLIsometry (verticalDilationSL (t^2)
  (sq_pos_of_pos (zero_lt_one.trans (hu.trans hut))))
local notation "A₅" => D₅⁻¹*hSLIsometry (pointHalfTurnSL w)
local notation "E₅" => (fun v : Fin _×Bool=>A₅^v.1.val*(if v.2 then D₅⁻¹ else 1))

/-- Axis subdivision retains the original even/odd native summit-copy labels. -/
theorem halfTurnSummitCycle_five_labels (q : ℕ) (v : Fin q×Bool) :
    (((σ₅^[(halfTurnSummitCycleIndex q v).val]) (1,f₅ 4)).1).val=E₅ v := by
  have hd : (d₅).val=D₅ := by
    change (S₅).element (e₅ 4)=D₅
    rw [halfTurnFivePairing_element_index]
    rfl
  have ha : (a₅).val=A₅ := by
    change ((S₅).element (e₅ 4))⁻¹*(S₅).element (e₅ 3)=A₅
    rw [halfTurnFivePairing_element_index,halfTurnFivePairing_element_index]
    rfl
  rcases v with ⟨i,b⟩
  cases b
  · rw [halfTurnSummitCycleIndex_val]
    simpa only [Bool.false_eq_true,ite_false,Nat.add_zero,Subgroup.coe_mul,Subgroup.coe_one,
      Subgroup.coe_pow,one_mul,ha,mul_one] using
      congrArg (fun a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q₅ hf₅ S₅=>a.1.val)
        (halfTurnWalk_five_summit_iterates u t hu hut w hw hn hc i.val 1).1
  · rw [halfTurnSummitCycleIndex_val]
    simpa only [ite_true,Subgroup.coe_mul,Subgroup.coe_one,Subgroup.coe_pow,Subgroup.coe_inv,
      one_mul,ha,hd] using
      congrArg (fun a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q₅ hf₅ S₅=>a.1.val)
        (halfTurnWalk_five_summit_iterates u t hu hut w hw hn hc i.val 1).2

/-- The unchanged physical summit fan supplies the refined polygon's true canonical ball pieces. -/
theorem halfTurnSummitCycle_five_origin (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₅ hf₅ S₅ 4 (2*q-1) r := by
  have hb:=halfTurnFive_band_parameters u t hu hut
  have hI : (P₅).interior=(P₄).interior :=
    halfTurnQuadRefined_native_interior (t^2) (t^2/w.re) (u^2) hb.1 hc hb.2.1 hb.2.2
  have hC : (P₅).carrier=(P₄).carrier := by
    calc
      (P₅).carrier=closure (P₅).interior:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₅ hf₅
      _=closure (P₄).interior:=congrArg closure hI
      _=(P₄).carrier:=(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q₄ hf₄).symm
  have hv : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 4=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3 :=
    halfTurnWalk_five_four_vertex u t (t^2/w.re) hu hut hc 3
  have hangle : Real.arccos (halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2))=Real.pi/q := by
    rw [halfTurnQuadCanonical_cosine_trace t w.re w.im (hu.trans hut) hw w.im_pos hn]
    exact hθ
  have hnative : orderOf A₅=q := by
    rw [halfTurnWalk_summit_native_word u t (zero_lt_one.trans hu) (hu.trans hut) w,
      hSLIsometry_orderOf_eq_realSLMobius]
    exact horder
  obtain ⟨r,hr,hcover,hdisj⟩ := halfTurnSummit_actual_summit_image_fan (t^2)
    (one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)) w hw hn hc q hq hangle hnative
  let e:=halfTurnSummitCycleIndex q
  let C (j : Fin (2*q)):=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₅ hf₅ S₅ ((σ₅^[j.val]) (1,f₅ 4))
  have hp (j : Fin (2*q)) :
      (S₅).vertexCyclePiece (C j) r=Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩
        E₅ (e.symm j) '' (P₄).carrier ∧
      (S₅).vertexCycleInteriorPiece (C j) r=Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩
        E₅ (e.symm j) '' (P₄).interior := by
    have he : (S₅).copyEvaluation (C j)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3 := by
      have hh:=halfTurnBaseCycle_iterate_evaluation Q₅ hf₅ S₅ (1,f₅ 4) j.val
      change (S₅).copyEvaluation (C j)=(1 : (S₅).Generated)•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₅ hf₅ 4 at hh
      rw [one_smul,hv] at hh
      exact hh
    have hl : (((σ₅^[j.val]) (1,f₅ 4)).1).val=E₅ (e.symm j) := by
      have hh:=halfTurnSummitCycle_five_labels u t hu hut w hw hn hc q (e.symm j)
      rw [e.apply_symm_apply] at hh
      exact hh
    have hh:=halfTurnBaseCycle_piece_ball Q₅ hf₅ S₅ (C j) r
    rw [he] at hh
    change _=(_∩(((σ₅^[j.val]) (1,f₅ 4)).1).val '' (P₅).carrier) ∧
      _=(_∩(((σ₅^[j.val]) (1,f₅ 4)).1).val '' (P₅).interior) at hh
    rw [hl,hC,hI] at hh
    exact hh
  refine ⟨r,hr,?_⟩
  have hlen : 2*q-1+1=2*q := by omega
  rw [HalfTurnBaseCycleAt,hlen]
  refine ⟨(halfTurnWalk_five_summit_period u t hu hut w hw hn hc q horder 1).1,?_,?_⟩
  · change (⋃j : Fin (2*q),(S₅).vertexCyclePiece (C j) r)=_
    simp_rw [fun j=>(hp j).1]
    rw [hv]
    exact (e.symm.surjective.iUnion_comp (fun v : Fin q×Bool=>
      Metric.ball (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3) r∩E₅ v '' (P₄).carrier)).trans hcover
  · intro i j hij
    change Disjoint ((S₅).vertexCycleInteriorPiece (C i) r) ((S₅).vertexCycleInteriorPiece (C j) r)
    rw [(hp i).2,(hp j).2]
    exact hdisj (e.symm.injective.ne hij)

/-- Both refined summit vertices inherit the literal primitive canonical cycles. -/
theorem halfTurnSummitCycle_five_all (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) (i : Fin 2) :
    ∃r : ℝ,0<r ∧ HalfTurnBaseCycleAt Q₅ hf₅ S₅ (![3,4] i) (2*q-1) r := by
  obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_five_origin u t hu hut w hw hn hc q hq hθ horder
  refine ⟨r,hr,?_⟩
  fin_cases i
  · change HalfTurnBaseCycleAt Q₅ hf₅ S₅ 3 (2*q-1) r
    have hs : (σ₅^[1]) (1,f₅ 4)=(d₅⁻¹,f₅ 3) := by
      change σ₅ (1,f₅ 4)=(d₅⁻¹,f₅ 3)
      rw [halfTurnWalk_five_step u t hu hut w hw hn hc 4]
      simp only [one_mul]
      rfl
    have hlen : 2*q-1+1=2*q := by omega
    refine ⟨?_,?_⟩
    · rw [hlen]
      exact (halfTurnWalk_five_summit_period u t hu hut w hw hn hc q horder 1).2
    · exact halfTurnBaseCycle_recenter Q₅ hf₅ S₅ (f₅ 4) (f₅ 3) (2*q-1) r
        hAt.1 hAt.2.1 hAt.2.2 1 d₅⁻¹ hs
  · exact hAt

/-- Every original vertex of the genuine primitive five-side polygon satisfies its complete natural cycle. -/
theorem halfTurnPrimitive_five_cycles (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonCanonicalCycleConditions Q₅ hf₅ S₅ := by
  intro i
  fin_cases i
  · obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_five_all u t hu hut w hw hn hc 0
    exact ⟨2,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_five_all u t hu hut w hw hn hc 1
    exact ⟨2,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnBaseCycle_five_all u t hu hut w hw hn hc 2
    exact ⟨2,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_five_all u t hu hut w hw hn hc q hq hθ horder 0
    exact ⟨2*q-1,r,hr,hAt⟩
  · obtain ⟨r,hr,hAt⟩:=halfTurnSummitCycle_five_all u t hu hut w hw hn hc q hq hθ horder 1
    exact ⟨2*q-1,r,hr,hAt⟩

/-- The literal five-side neighborhoods and the complete primitive cycles imply actual local tessellation. -/
theorem halfTurnPrimitive_five_local_tessellation (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    (S₅).FiniteFiberLocalTessellationCondition := by
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_local_tessellation Q₅ hf₅ S₅
    (halfTurnFivePairing_opposition_index u t hu hut w hw hn hc)
    (halfTurnPrimitive_five_cycles u t hu hut w hw hn hc q hq hθ horder)

/-- The actual primitive five-side polygon is a fundamental domain for the unchanged entire three-half-turn group. -/
theorem halfTurnPrimitive_five_poincare (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    DiscreteTopology (S₅).Generated ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (S₅).Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₅).interior) := by
  exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygon_canonical_cycles_poincare Q₅ hf₅ S₅
    (halfTurnFivePairing_opposition_index u t hu hut w hw hn hc)
    (halfTurnPrimitive_five_cycles u t hu hut w hw hn hc q hq hθ horder)

end FiveSummitCycles
end LowDimensionalTopology.Geometry.Fuchsian



namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Compact genuine polygon geometry and actual local tessellation make the original evaluation injective. -/
theorem halfTurnCone_compact_evaluation_injective {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (hA6 : S.FiniteFiberLocalTessellationCondition) : Function.Injective S.evaluation := by
  exact (hA6.covering_homeomorph_of_compact S
    (S.native_metric_assumptions (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isOpen Q hf)
      (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_interior_isConnected Q hf))
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier Q hf).le
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf)).2.injective

/-- The complete development fiber at a fixed self-side center contains only
the two literal copies, so it detects every element of the whole generated group. -/
theorem halfTurnCone_unique_side_copy {X Γ : Type*} [Group Γ] [MulAction Γ X]
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
    (heval : Function.Injective S.evaluation) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hu : ∀t : P.Side,x.val∈t.val→t=s)
    (hpair : S.paired s=s) (hfix : S.generator s•x.val=x.val)
    (g : S.Generated) (q : P.Point) (hg : g•q.val=x.val) :
    q=x ∧ (g=1 ∨ g=(S.generator s)⁻¹) := by
  have hv : ∀t : P.Side,(S.sideMateCopy (1,x) s hx).2.val∈t.val→t=S.paired s := by
    intro t ht
    change S.generator s•x.val∈t.val at ht
    rw [hfix] at ht
    rw [hpair]
    exact hu t ht
  have hp : S.project (g,q)=S.project (1,x) := by
    apply heval
    change g•q.val=(1 : S.Generated)•x.val
    simpa only [one_smul] using hg
  have hc : (g,q)∈({(1,x),S.sideMateCopy (1,x) s hx} : Set S.Copy) := by
    rw [←S.project_fiber_eq_side_pair (1,x) s hx hu hv]
    exact hp
  simp only [mem_insert_iff,mem_singleton_iff] at hc
  rcases hc with hc | hc
  · exact ⟨congrArg Prod.snd hc,Or.inl (congrArg Prod.fst hc)⟩
  · constructor
    · apply Subtype.ext
      have hh := congrArg (fun a : S.Copy=>a.2.val) hc
      change q.val=S.generator s•x.val at hh
      exact hh.trans hfix
    · right
      have hh := congrArg Prod.fst hc
      change g=1*(S.generator s)⁻¹ at hh
      simpa only [one_mul] using hh

/-- A fixed unique self-side center has its exact stabilizer in the whole generated group. -/
theorem halfTurnCone_self_side_stabilizer {X Γ : Type*} [Group Γ] [MulAction Γ X]
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
    (heval : Function.Injective S.evaluation) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hu : ∀t : P.Side,x.val∈t.val→t=s)
    (hpair : S.paired s=s) (hfix : S.generator s•x.val=x.val) :
    (MulAction.stabilizer S.Generated x.val : Set S.Generated)={1,(S.generator s)⁻¹} := by
  ext g
  change g•x.val=x.val ↔ g=1 ∨ g=(S.generator s)⁻¹
  constructor
  · intro hg
    exact (halfTurnCone_unique_side_copy S heval x s hx hu hpair hfix g x hg).2
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact inv_smul_eq_iff.mpr hfix.symm

/-- A genuine nonidentity fixed self-side generator gives actual stabilizer order two. -/
theorem halfTurnCone_self_side_stabilizer_card {X Γ : Type*} [Group Γ] [MulAction Γ X]
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
    (heval : Function.Injective S.evaluation) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hu : ∀t : P.Side,x.val∈t.val→t=s)
    (hpair : S.paired s=s) (hfix : S.generator s•x.val=x.val)
    (hne : S.generator s≠1) : Nat.card (MulAction.stabilizer S.Generated x.val)=2 := by
  classical
  let a : MulAction.stabilizer S.Generated x.val :=
    ⟨(S.generator s)⁻¹,inv_smul_eq_iff.mpr hfix.symm⟩
  apply (Nat.card_eq_two_iff' (1 : MulAction.stabilizer S.Generated x.val)).mpr
  refine ⟨a,?_,?_⟩
  · intro he
    have hh : (S.generator s)⁻¹=1 := congrArg Subtype.val he
    exact hne (inv_eq_one.mp hh)
  · intro k hk
    apply Subtype.ext
    rcases (halfTurnCone_unique_side_copy S heval x s hx hu hpair hfix k.val x k.property).2 with he | he
    · exact False.elim (hk (Subtype.ext he))
    · exact he

/-- The original closed polygon contains exactly one point from such a center's whole orbit. -/
theorem halfTurnCone_self_side_carrier_orbit {X Γ : Type*} [Group Γ] [MulAction Γ X]
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)
    (heval : Function.Injective S.evaluation) (x : P.Point) (s : P.Side)
    (hx : x.val∈s.val) (hu : ∀t : P.Side,x.val∈t.val→t=s)
    (hpair : S.paired s=s) (hfix : S.generator s•x.val=x.val)
    (q : X) (hq : q∈P.carrier) (g : S.Generated) (hg : g•q=x.val) : q=x.val := by
  exact congrArg Subtype.val
    (halfTurnCone_unique_side_copy S heval x s hx hu hpair hfix g ⟨q,hq⟩ hg).1

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The three unchanged physical half-turn centers of the actual refined chamber. -/
def halfTurnPrimitive_five_centers (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ) : Fin 3→ℍ :=
  ![_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 u (zero_lt_one.trans hu),
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut))),w]

/-- Each original center lies on precisely its own genuine self-paired side;
this is proved from the literal original geodesic equations. -/
theorem halfTurnPrimitive_five_center_side_iff (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (i : Fin 3) (j : Fin 5) :
    halfTurnPrimitive_five_centers u t hu hut w i ∈
      _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide (halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc) j ↔
      j=(![0,1,3] : Fin 3→Fin 5) i := by
  have hu0 : 0<u := zero_lt_one.trans hu
  have ht : 1<t := hu.trans hut
  have ht0 : 0<t := zero_lt_one.trans ht
  have hu2 : u<u^2 := by nlinarith only [hu]
  have hutlo : u^2<u*t := by simpa only [pow_two] using mul_lt_mul_of_pos_left hut hu0
  have huthi : u*t<t^2 := by nlinarith only [hut,ht0]
  have ht2 : t<t^2 := by nlinarith only [ht]
  have hunit : 1<u*t := lt_trans hu (lt_mul_of_one_lt_right hu0 ht)
  have hukt : u<t^2 := hut.trans ht2
  have hnormu : ‖(⟨0,u⟩ : ℂ)‖=u :=
    nativeSideCoordinates_axis_norm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 u hu0) rfl
  have hnormut : ‖(⟨0,u*t⟩ : ℂ)‖=u*t :=
    nativeSideCoordinates_axis_norm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (u*t) (mul_pos hu0 ht0)) rfl
  have hnormw : ‖(w : ℂ)‖=t := by
    have hh : ‖(w : ℂ)‖^2=t^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simpa only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two] using hn
    nlinarith only [hh,norm_nonneg (w : ℂ),ht0]
  have hpoly : w.re^2+w.im^2-2*(t^2/w.re)*w.re+t^2=0 := by
    rw [hn]
    field_simp
    ring
  rw [halfTurnFiveDiscPolygon_side]
  clear hn hc
  fin_cases i <;> fin_cases j <;>
    dsimp only [halfTurnPrimitive_five_centers,halfTurnFiveLiteralSide,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four,
      Fin.reduceFinMk] <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] <;> (repeat' constructor) <;> intros <;>
    nlinarith [sq_nonneg u,sq_nonneg (u*t)]

/-- Every genuine self-side generator fixes its unchanged physical half-turn center. -/
theorem halfTurnPrimitive_five_center_fixed (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (i : Fin 3) :
    let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
    let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
    let S:=halfTurnFivePairing u t hu hut w hw hn hc
    let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf ((![0,1,3] : Fin 3→Fin 5) i)
    S.element s (halfTurnPrimitive_five_centers u t hu hut w i)=
      halfTurnPrimitive_five_centers u t hu hut w i ∧ orderOf (S.element s)=2 := by
  dsimp only
  rw [halfTurnFivePairing_element_index]
  fin_cases i
  · constructor
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at u (zero_lt_one.trans hu)).2
    · exact (hSLIsometry_orderOf_eq_realSLMobius _).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at u (zero_lt_one.trans hu)).1
  · constructor
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (u*t)
        (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))).2
    · exact (hSLIsometry_orderOf_eq_realSLMobius _).trans
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))).1
  · constructor
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w).2
    · exact (hSLIsometry_orderOf_eq_realSLMobius _).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w).1

/-- The actual three original centers remain three different physical points. -/
theorem halfTurnPrimitive_five_centers_injective (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) : Function.Injective (halfTurnPrimitive_five_centers u t hu hut w) := by
  intro i j he
  have hre:=congrArg UpperHalfPlane.re he
  have him:=congrArg UpperHalfPlane.im he
  have hu0 : 0<u:=zero_lt_one.trans hu
  have ht : 1<t:=hu.trans hut
  have hut' : u<u*t:=lt_mul_of_one_lt_right hu0 ht
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTurnPrimitive_five_centers,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hre him ⊢ <;> linarith

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The original three centers have order-two stabilizers in the whole actual
pairing group, and their actual chamber representatives are orbit-unique. -/
theorem halfTurnPrimitive_five_center_whole_group (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hA6 : (halfTurnFivePairing u t hu hut w hw hn hc).FiniteFiberLocalTessellationCondition)
    (i : Fin 3) :
    let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
    let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let S:=halfTurnFivePairing u t hu hut w hw hn hc
    let z:=halfTurnPrimitive_five_centers u t hu hut w i
    Nat.card (MulAction.stabilizer S.Generated z)=2 ∧
      z∈P.carrier ∧ ∀(g : S.Generated)(p : P.Point),g•p.val=z→p.val=z := by
  let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
  let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFivePairing u t hu hut w hw hn hc
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let z:=halfTurnPrimitive_five_centers u t hu hut w i
  let j:=(![0,1,3] : Fin 3→Fin 5) i
  let s:=e j
  have hz : z∈s.val := (halfTurnPrimitive_five_center_side_iff u t hu hut w hw hn hc i j).mpr rfl
  let x : P.Point:=⟨z,P.side_subset_carrier s hz⟩
  have huSide : ∀v : P.Side,z∈v.val→v=s := by
    intro v hv
    obtain ⟨k,rfl⟩:=e.surjective v
    have hk : k=j := (halfTurnPrimitive_five_center_side_iff u t hu hut w hw hn hc i k).mp hv
    exact congrArg e hk
  have hp : S.paired s=s := by
    have hh:=halfTurnFivePairing_paired_index u t hu hut w hw hn hc j
    change S.paired s=e (Equiv.swap 2 4 j) at hh
    rw [hh]
    congr 1
    fin_cases i <;> norm_num [j,Equiv.swap_apply_def]
  have hd:=halfTurnPrimitive_five_center_fixed u t hu hut w hw hn hc i
  have hfix : S.generator s•z=z := hd.1
  have hnGen : S.generator s≠1 := by
    intro he
    have hh : S.element s=1 := congrArg Subtype.val he
    have ho : orderOf (S.element s)=2 := hd.2
    rw [hh,orderOf_one] at ho
    norm_num at ho
  have hEval:=halfTurnCone_compact_evaluation_injective Q hf S hA6
  refine ⟨halfTurnCone_self_side_stabilizer_card S hEval x s hz huSide hp hfix hnGen,
    x.property,?_⟩
  intro g p hgp
  exact congrArg Subtype.val (halfTurnCone_unique_side_copy S hEval x s hz huSide hp hfix g p hgp).1

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Different unchanged half-turn centers represent different actual
whole-group orbits in the primitive refined chamber. -/
theorem halfTurnPrimitive_five_center_orbits (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hA6 : (halfTurnFivePairing u t hu hut w hw hn hc).FiniteFiberLocalTessellationCondition)
    (i j : Fin 3) (g : (halfTurnFivePairing u t hu hut w hw hn hc).Generated)
    (hg : g•halfTurnPrimitive_five_centers u t hu hut w i=
      halfTurnPrimitive_five_centers u t hu hut w j) : i=j := by
  let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
  let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFivePairing u t hu hut w hw hn hc
  have hi:=halfTurnPrimitive_five_center_whole_group u t hu hut w hw hn hc hA6 i
  have hj:=halfTurnPrimitive_five_center_whole_group u t hu hut w hw hn hc hA6 j
  let x : P.Point:=⟨halfTurnPrimitive_five_centers u t hu hut w i,hi.2.1⟩
  exact halfTurnPrimitive_five_centers_injective u t hu hut w hw (hj.2.2 g x hg)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Actual physical elliptic points in different whole-group orbits give
different actual maximal elliptic conjugacy classes of the unchanged boundary group. -/
theorem halfTurnNative_elliptic_classes_card_lower
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (m : ℕ) (z : Fin m→ℍ)
    (hfix : ∀i,∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (nativeCovolume_groupEquiv H hConf f).val ∧ f•z i=z i)
    (horbit : ∀(i j : Fin m)(f : H),f•z i=z j→i=j)
    [Finite (FuchsianCyclicConjugacyClasses
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc .elliptic)] :
    m≤Nat.card (FuchsianCyclicConjugacyClasses
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc .elliptic) := by
  let e:=nativeCovolume_groupEquiv H hConf
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let D:=P.asFuchsianDisc
  have hp (i : Fin m) : _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z i)∈fuchsianCyclicFixedPoints D .elliptic := by
    obtain ⟨f,hf,hfz⟩:=hfix i
    refine ⟨?_,(e f).val,(e f).property,hf,?_⟩
    · intro _
      change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z i)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
      exact mem_range_self _
    · change (nativeConformalSubgroupMobiusHom H hConf f).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z i))=_
      rw [nativeConformalSubgroupMobiusHom_action]
      exact congrArg _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint hfz
  let p (i : Fin m) : fuchsianCyclicFixedPoints D .elliptic:=⟨_,hp i⟩
  let c (i : Fin m) : FuchsianCyclicConjugacyClasses D .elliptic:=
    Quotient.mk _ (fuchsianCyclicPointStabilizer D .elliptic (p i))
  have hi : Function.Injective c := by
    intro i j hij
    have hrel:=Quotient.exact hij
    change MulAction.orbitRel (nativeConformalSubgroupMobiusHom H hConf).range
      (fuchsianCyclicFixedPoints D .elliptic)
      ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm
        (fuchsianCyclicPointStabilizer D .elliptic (p i)))
      ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm
        (fuchsianCyclicPointStabilizer D .elliptic (p j))) at hrel
    change MulAction.orbitRel _ _
      ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm
        ((fuchsianCyclicPointStabilizerEquiv D .elliptic) (p i)))
      ((fuchsianCyclicPointStabilizerEquiv D .elliptic).symm
        ((fuchsianCyclicPointStabilizerEquiv D .elliptic) (p j))) at hrel
    simp only [Equiv.symm_apply_apply,MulAction.orbitRel_apply,MulAction.mem_orbit_iff] at hrel
    obtain ⟨g,hg⟩:=hrel
    obtain ⟨f,rfl⟩:=e.surjective g
    apply Eq.symm
    apply (horbit j i f)
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    have hh:=congrArg Subtype.val hg
    change (nativeConformalSubgroupMobiusHom H hConf f).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z j))=
      _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (z i) at hh
    exact (nativeConformalSubgroupMobiusHom_action H hConf f (z j)).symm.trans hh
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective c hi

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- A true order-two whole-group stabilizer cannot be in the orbit of a point
fixed by a genuine element whose actual order is at least three. -/
theorem halfTurnCone_not_same_orbit_of_order {G X : Type*} [Group G] [MulAction G X]
    (x z : X) (hcard : Nat.card (MulAction.stabilizer G x)=2)
    (a : G) (ha : 3≤orderOf a) (haz : a•z=z) (g : G) : g•x≠z := by
  intro hgx
  let : Finite (MulAction.stabilizer G x):=Nat.finite_of_card_ne_zero (by rw [hcard];decide)
  let b : MulAction.stabilizer G x:=⟨g⁻¹*a*g,by
    change (g⁻¹*a*g)•x=x
    rw [mul_smul,mul_smul,hgx,haz,←hgx,inv_smul_smul]⟩
  have hconj : orderOf (g⁻¹*a*g)=orderOf a := by
    have hs : SemiconjBy g (g⁻¹*a*g) a := by
      change g*(g⁻¹*a*g)=a*g
      group
    exact hs.orderOf_eq
  have ho : orderOf b=orderOf a :=
    (orderOf_injective (MulAction.stabilizer G x).subtype Subtype.val_injective b).symm.trans hconj
  have hd:=orderOf_dvd_natCard b
  rw [hcard,ho] at hd
  have hle : orderOf a≤2:=Nat.le_of_dvd (by decide) hd
  omega

/-- Three orbit-distinct actual order-two centers and a genuine higher-order
summit give four different whole-group point orbits. -/
theorem halfTurnCone_three_centers_summit_orbits {G X : Type*} [Group G] [MulAction G X]
    (x : Fin 3→X) (hcard : ∀i,Nat.card (MulAction.stabilizer G (x i))=2)
    (hcenters : ∀(i j : Fin 3)(g : G),g•x i=x j→i=j)
    (z : X) (a : G) (ha : 3≤orderOf a) (haz : a•z=z) :
    ∀(i j : Fin 4)(g : G),g•(Fin.lastCases z x : Fin 4→X) i=(Fin.lastCases z x : Fin 4→X) j→i=j := by
  intro i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · intro j
    refine Fin.lastCases ?_ (fun j=>?_) j
    · intro _ _
      rfl
    · intro g hg
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at hg
      have hg' : g•z=x j:=hg
      exact False.elim ((halfTurnCone_not_same_orbit_of_order (x j) z (hcard j) a ha haz g⁻¹)
        (inv_smul_eq_iff.mpr hg'.symm))
  · intro j
    refine Fin.lastCases ?_ (fun j=>?_) j
    · intro g hg
      simp only [Fin.lastCases_last,Fin.lastCases_castSucc] at hg
      exact False.elim ((halfTurnCone_not_same_orbit_of_order (x i) z (hcard i) a ha haz g) hg)
    · intro g hg
      simp only [Fin.lastCases_castSucc] at hg
      exact congrArg Fin.castSucc (hcenters i j g hg)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic

/-- One specified actual cone order strengthens the elementary half-counting estimate. -/
theorem halfTurn_primitive_order_list_classification (g : ℕ) (orders : List ℕ)
    (h2 : ∀m∈orders,2≤m) (hlen : 4≤orders.length) (q n : ℕ)
    (hq : 3≤q) (hn : n∈orders) (hqn : q≤n)
    (hArea : 2*(g : ℝ)-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      1/2-1/(q : ℝ)) :
    g=0 ∧ orders.Perm [2,2,2,q] := by
  have hq0 : 0<(q : ℝ) := by exact_mod_cast (show 0<q by omega)
  have hn0 : 0<(n : ℝ) := lt_of_lt_of_le hq0 (by exact_mod_cast hqn)
  have hrec : 1/(n : ℝ)≤1/(q : ℝ) :=
    one_div_le_one_div_of_le hq0 (by exact_mod_cast hqn)
  have hm := halfTurn_marked_cone_sum_lower orders h2 n hn
  have hlenR : (4 : ℝ)≤orders.length := by exact_mod_cast hlen
  have hg0 : 0≤(g : ℝ) := Nat.cast_nonneg _
  have hg : g=0 := by
    have hgR : (g : ℝ)=0 := by linarith only [hm,hrec,hlenR,hg0,hArea]
    exact_mod_cast hgR
  have hl4 : orders.length=4 := by
    have hlR : (orders.length : ℝ)=4 := by
      rw [hg] at hArea
      norm_num only [Nat.cast_zero,mul_zero,zero_sub] at hArea
      linarith only [hm,hrec,hlenR,hArea]
    exact_mod_cast hlR
  have hnq : n=q := by
    have hrec' : 1/(q : ℝ)≤1/(n : ℝ) := by
      rw [hg] at hArea
      norm_num only [Nat.cast_zero,mul_zero,zero_sub] at hArea
      rw [hl4] at hm
      norm_num only [Nat.cast_ofNat] at hm
      linarith only [hm,hArea]
    have hle : (n : ℝ)≤q := (one_div_le_one_div hq0 hn0).mp hrec'
    exact Nat.le_antisymm (by exact_mod_cast hle) hqn
  subst n
  have herase : (orders.erase q).length=3 := by
    rw [List.length_erase_of_mem hn,hl4]
  obtain ⟨a,b,c,he⟩ := List.length_eq_three.mp herase
  have hp : (q::[a,b,c]).Perm orders := by
    simpa only [he] using (List.perm_cons_erase hn).symm
  have habc (m : ℕ) (hm : m∈[a,b,c]) : 2≤m :=
    h2 m (hp.mem_iff.mp (List.mem_cons_of_mem q hm))
  have ha := habc a (by simp)
  have hb := habc b (by simp)
  have hc := habc c (by simp)
  have hs : (1-1/(a : ℝ))+(1-1/(b : ℝ))+(1-1/(c : ℝ))=3/2 := by
    rw [hg,←(hp.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq] at hArea
    norm_num only [Nat.cast_zero,mul_zero,zero_sub,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil] at hArea
    linarith only [hArea]
  have hwa := (signature_elliptic_weight_bounds a ha).1
  have hwb := (signature_elliptic_weight_bounds b hb).1
  have hwc := (signature_elliptic_weight_bounds c hc).1
  have order_two (m : ℕ) (hm : 2≤m) (hw : 1-1/(m : ℝ)=1/2) : m=2 := by
    have hm0 : 0<(m : ℝ) := by exact_mod_cast (show 0<m by omega)
    have hmul := congrArg (fun x : ℝ=>x*m) hw
    field_simp at hmul
    have hm2 : (m : ℝ)=2 := by nlinarith only [hmul,hm0]
    exact_mod_cast hm2
  have hae : a=2 := order_two a ha (by linarith only [hs,hwa,hwb,hwc])
  have hbe : b=2 := order_two b hb (by linarith only [hs,hwa,hwb,hwc])
  have hce : c=2 := order_two c hc (by linarith only [hs,hwa,hwb,hwc])
  refine ⟨hg,?_⟩
  have hp' : [q,2,2,2].Perm orders := by simpa only [hae,hbe,hce] using hp
  exact hp'.symm.trans (by simpa using (List.perm_append_comm (l₁:=[q]) (l₂:=[2,2,2])))

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A literal original native geometric fundamental domain has its actual
covolume, through the faithful unchanged boundary action and null fixed sets. -/
theorem halfTurnNative_covolume_of_fundamental
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (F : Set ℍ)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume F) :
    MeasureTheory.covolume H ℍ volume=volume F := by
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let nativeCovolumeActualAction:=P.nativeAction
  let e:=nativeCovolume_groupEquiv H hConf
  have he (g : (nativeConformalSubgroupMobiusHom H hConf).range) (z : ℍ) :
      g•z=e.symm g•z := by
    have hh:=nativeCovolume_groupEquiv_action H hConf (e.symm g) z
    rw [e.apply_symm_apply] at hh
    exact hh
  have hF' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (nativeConformalSubgroupMobiusHom H hConf).range ℍ volume F := by
    have ht:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm (Homeomorph.refl ℍ) he hF
    simpa using ht
  have hMF:=native_geometric_fundamental_measureDomain P F hF'
  let : Countable H:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeDiscreteIsometrySubgroup_countable H
  let : ContinuousConstSMul H ℍ:=⟨fun g=>g.val.continuous⟩
  exact (nativeCovolume_measureDomain_transport H hConf F hMF).covolume_eq_volume volume

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Set MeasureTheory
open scoped UpperHalfPlane

/-- Faithfulness of the actual native boundary action makes every genuine
nontrivial finite-order native transformation an actual elliptic Mobius map. -/
theorem halfTurnNative_elliptic_of_order
    (H : Subgroup (ℍ≃ᵢℍ)) (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (a : H) (q : ℕ) (hq : 2≤q) (ha : orderOf a=q) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (nativeCovolume_groupEquiv H hConf a).val := by
  let f:=nativeConformalSubgroupMobiusHom H hConf
  have ho : orderOf (f a)=q :=
    (orderOf_injective f (nativeConformalSubgroupMobiusHom_isometry H hConf).injective a).trans ha
  have hn : f a≠1 := by
    intro he
    rw [he,orderOf_one] at ho
    omega
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic (f a) hn
    (orderOf_pos_iff.mp (by rw [ho];omega))

/-- The actual compact primitive chamber, its actual three distinct order-two
centers, and its genuine product order determine the original cofinite signature.
Every input is geometric or a genuine group fact; the signature is constructed. -/
theorem halfTurnPrimitive_native_signature
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H]
    (hConf : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (F C : Set ℍ)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume F) (hC : IsCompact C)
    (hcover : ∀z : ℍ,∃g : H,g•z∈C)
    (q : ℕ) (hq : 3≤q)
    (hArea : (volume F).toReal=Real.pi-2*Real.pi/q)
    (centers : Fin 3→ℍ)
    (hcenters : ∀i,∃f : H,orderOf f=2 ∧ f•centers i=centers i)
    (hcard : ∀i,Nat.card (MulAction.stabilizer H (centers i))=2)
    (horbit : ∀(i j : Fin 3)(g : H),g•centers i=centers j→i=j)
    (a : H) (ha : orderOf a=q) (v : ℍ) (hav : a•v=v) :
    HasCofiniteFuchsianSignature
      (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc 0 [2,2,2,q] 0 := by
  let P:=nativeConformalSubgroup_halfPlaneData H hConf
  let e:=nativeCovolume_groupEquiv H hConf
  obtain ⟨g,orders,hSig,hCov,_hPos,_hFin,_hReal⟩:=
    compactSignature_native_compact_cover H hConf C hC hcover
  let : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=hSig.ellipticClassesFinite
  have hfixFour : ∀i : Fin 4,∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (e f).val ∧
      f•(Fin.lastCases v centers : Fin 4→ℍ) i=(Fin.lastCases v centers : Fin 4→ℍ) i := by
    intro i
    refine Fin.lastCases ?_ (fun i=>?_) i
    · refine ⟨a,halfTurnNative_elliptic_of_order H hConf a q (by omega) ha,?_⟩
      simpa only [Fin.lastCases_last] using hav
    · obtain ⟨f,hf,hfx⟩:=hcenters i
      refine ⟨f,halfTurnNative_elliptic_of_order H hConf f 2 (by decide) hf,?_⟩
      simpa only [Fin.lastCases_castSucc] using hfx
  have hFour:=halfTurnNative_elliptic_classes_card_lower H hConf 4
    (Fin.lastCases v centers : Fin 4→ℍ) hfixFour
    (halfTurnCone_three_centers_summit_orbits centers hcard horbit v a (by rw [ha];exact hq) hav)
  have hlen : 4≤orders.length := by rwa [hSig.orders_length]
  have hEllipse:=halfTurnNative_elliptic_of_order H hConf a q (by omega) ha
  obtain ⟨n,hnmem,hdiv⟩:=elliptic_order_dvd_signature_entry P.asFuchsianDisc (e a) hEllipse hSig
  have heOrder : orderOf (e a)=q := (orderOf_injective e.toMonoidHom e.injective a).trans ha
  rw [heOrder] at hdiv
  have hqn : q≤n:=Nat.le_of_dvd (by have hh:=hSig.orders_two_le hnmem;omega) hdiv
  have hPhysical : (MeasureTheory.covolume H ℍ volume).toReal=Real.pi-2*Real.pi/q :=
    (congrArg ENNReal.toReal (halfTurnNative_covolume_of_fundamental H hConf F hF)).trans hArea
  have hScalar : 2*(g : ℝ)-2+(orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      1/2-1/(q : ℝ) := by
    rw [hCov] at hPhysical
    have hscale : (2*Real.pi)*(1/2-1/(q : ℝ))=Real.pi-2*Real.pi/q := by ring
    rw [←hscale] at hPhysical
    exact (mul_left_cancel₀ (show (2*Real.pi : ℝ)≠0 by positivity)) hPhysical
  obtain ⟨hg,horders⟩:=halfTurn_primitive_order_list_classification g orders
    (fun _ hm=>hSig.orders_two_le hm) hlen q n hq hnmem hqn hScalar
  subst g
  exact hSig.perm_orders horders.symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Set MeasureTheory
open scoped UpperHalfPlane

/-- The unchanged five-side generators are genuinely conformal. -/
theorem halfTurnPrimitive_five_group_conformal
    (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) :
    (halfTurnFivePairing u t hu hut w hw hn hc).Generated≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  rw [halfTurnFivePairing_generated]
  exact threeHalfTurn_native_group_conformal _ _ _

/-- The actual primitive refined chamber has the full original four-cone
signature; its fundamental domain, cone classes and area are all proved. -/
theorem halfTurnPrimitive_five_signature
    (u t : ℝ) (hu : 1<u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (q : ℕ) (hq : 3≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu)
        (zero_lt_one.trans (hu.trans hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    let S:=halfTurnFivePairing u t hu hut w hw hn hc
    letI:=(halfTurnPrimitive_five_poincare u t hu hut w hw hn hc q (by omega) hθ horder).1
    let hConf:=halfTurnPrimitive_five_group_conformal u t hu hut w hw hn hc
    HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData S.Generated hConf).asFuchsianDisc
      0 [2,2,2,q] 0 := by
  let Q:=halfTurnFiveDiscPolygon u t (t^2/w.re) hu hut hc
  let hf:=halfTurnFiveDiscPolygon_finite u t (t^2/w.re) hu hut hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFivePairing u t hu hut w hw hn hc
  let H:=S.Generated
  let hd:DiscreteTopology H:=
    (halfTurnPrimitive_five_poincare u t hu hut w hw hn hc q (by omega) hθ horder).1
  let hConf:=halfTurnPrimitive_five_group_conformal u t hu hut w hw hn hc
  have hA6:=halfTurnPrimitive_five_local_tessellation u t hu hut w hw hn hc q (by omega) hθ horder
  have hFD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume P.interior:=
    (halfTurnPrimitive_five_poincare u t hu hut w hw hn hc q (by omega) hθ horder).2
  let centers:=halfTurnPrimitive_five_centers u t hu hut w
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans hu)
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans hu) (zero_lt_one.trans (hu.trans hut)))
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  let K:=F*G*W
  let a : H:=S.generator (e 0)*S.generator (e 1)*S.generator (e 3)
  have hprod : a.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K := by
    change S.element (e 0)*S.element (e 1)*S.element (e 3)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K
    rw [halfTurnFivePairing_element_index,halfTurnFivePairing_element_index,halfTurnFivePairing_element_index]
    apply IsometryEquiv.ext
    intro z
    change F•(G•(W•z))=(F*G*W)•z
    simp only [mul_smul]
  have ha : orderOf a=q := by
    calc
      orderOf a=orderOf a.val:=(orderOf_injective H.subtype Subtype.val_injective a).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K):=by rw [hprod]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K):=hSLIsometry_orderOf_eq_realSLMobius K
      _=q:=horder
  let hk:=one_lt_pow₀ (hu.trans hut) (by decide : (2 : ℕ)≠0)
  let Q₄:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf₄:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  let v:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 3
  have hav : a•v=v := by
    change a.val v=v
    rw [hprod]
    have hh:=halfTurnCanonical_product_fixes_summit u t (zero_lt_one.trans hu) (hu.trans hut) w hw hn hc
    change F•(G•(W•v))=v at hh
    change (F*G*W)•v=v
    simpa only [mul_smul] using hh
  have hcenters : ∀i,∃f : H,orderOf f=2 ∧ f•centers i=centers i := by
    intro i
    let s:=e ((![0,1,3] : Fin 3→Fin 5) i)
    let f : H:=S.generator s
    have hdata:=halfTurnPrimitive_five_center_fixed u t hu hut w hw hn hc i
    refine ⟨f,?_,hdata.1⟩
    exact (orderOf_injective H.subtype Subtype.val_injective f).symm.trans hdata.2
  have hcard : ∀i,Nat.card (MulAction.stabilizer H (centers i))=2 := fun i=>
    (halfTurnPrimitive_five_center_whole_group u t hu hut w hw hn hc hA6 i).1
  have horbit : ∀(i j : Fin 3)(g : H),g•centers i=centers j→i=j :=
    halfTurnPrimitive_five_center_orbits u t hu hut w hw hn hc hA6
  have hArea : (volume P.interior).toReal=Real.pi-2*Real.pi/q := by
    have hb:=halfTurnFive_band_parameters u t hu hut
    have hQA : Q.area=volume P.interior:=Q.area_eq_halfPlane_volume
    rw [←hQA]
    change (halfTurnQuadRefined (t^2) (t^2/w.re) (u^2) hb.1 hc hb.2.1 hb.2.2).area.toReal=_
    rw [halfTurnQuadRefined_area,halfTurnQuadCanonical_area,
      halfTurnQuadCanonical_cosine_trace t w.re w.im (hu.trans hut) hw w.im_pos hn,hθ]
    ring
  exact halfTurnPrimitive_native_signature H hConf P.interior P.carrier hFD
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf) (halfTurnFivePairing_orbit_cover u t hu hut w hw hn hc)
    q hq hArea centers hcenters hcard horbit a ha v hav

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A genuine closed canonical vertex walk contains every original copy
with the same physical evaluation, once actual evaluation injectivity is proved. -/
theorem halfTurnCone_periodic_vertex_copy {m : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf))
    (heval : Function.Injective S.evaluation)
    (a : _root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S) (n : ℕ)
    (hclose : ((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[n+1]) a=a)
    (b : S.Copy)
    (hb : S.copyEvaluation b=S.copyEvaluation (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a)) :
    ∃i : Fin (n+1),_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S
      (((_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonCanonicalVertexStep Q hf S)^[i.val]) a)=b := by
  let hV:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPairing_preserves_vertices Q hf S
  let σ:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNaturalVertexStep Q hf S hV
  let U : Set (_root_.LowDimensionalTopology.Geometry.Polygon.FinitePolygonFlagState Q hf S):=range (fun i : Fin (n+1)=>(σ^[i.val]) a)
  have hclose' : (σ^[n+1]) a=a := hclose
  obtain ⟨hnext,hprev⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.equiv_periodic_range_invariant σ a n hclose'
  have hs : ∀c∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S '' U,∀d : S.Copy,S.Step c d→
      d∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S '' U := by
    rintro c ⟨v,hv,rfl⟩ d hd
    rcases hd with he|⟨s,hvs,hy,hg⟩
    · exact he ▸ mem_image_of_mem _ hv
    · have hmate:=S.sideMateCopy_eq_of_side_step _ d s hvs hy hg
      rw [←hmate]
      exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonNaturalVertexStep_incidence_closed Q hf S hV U hnext hprev v hv s hvs
  have hbase : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S '' U :=
    mem_image_of_mem _ ⟨0,rfl⟩
  have hp : S.project b=S.project (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S a) := heval hb
  obtain ⟨v,⟨i,rfl⟩,he⟩:=S.project_fiber_subset_of_step_closed
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q hf S '' U) _ hbase hs hp
  exact ⟨i,he⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section FourBaseStabilizer
variable (t : ℝ) (ht : 1<t) (w : ℍ) (hw : 0<w.re)
  (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
local notation "Q₄" => (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
local notation "hf₄" => halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
  (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
local notation "P₄" => finiteDiscPoincarePolygon Q₄ hf₄
local notation "S₄" => halfTurnFour_pairing t ht w hw hn hc
local notation "e₄" => finitePolygonSideEquiv Q₄ hf₄
local notation "f₄" => finitePolygonOutgoingFlag Q₄ hf₄
local notation "σ₄" => finitePolygonCanonicalVertexStep Q₄ hf₄ S₄
local notation "K₄" => metricProbe 0 (t^2) (sq_pos_of_pos (zero_lt_one.trans ht))

/-- The first half-turn is the actual second label of the unchanged base cycle,
and therefore belongs to the whole original generated subgroup. -/
def halfTurnFourBase_firstHalfTurn : (S₄).Generated := ((σ₄^[2]) (1,f₄ 0)).1

theorem halfTurnFourBase_firstHalfTurn_coe :
    (halfTurnFourBase_firstHalfTurn t ht w hw hn hc).val=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one) := by
  exact halfTurnBaseCycle_four_origin_labels t ht w hw hn hc 2

/-- The two actual base vertices are exactly the two original axis endpoints. -/
theorem halfTurnFourBase_axis_vertices :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0=UpperHalfPlane.I ∧ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 1=K₄ := by
  have h:=halfTurnWalk_four_axis_vertices (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
  constructor
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h.1
    · exact h.2.1
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · exact h.2.2.1
    · exact h.2.2.2

/-- The four literal copies alternate between the original two base vertices. -/
theorem halfTurnFourBase_cycle_points (j : Fin 4) :
    (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ ((σ₄^[j.val]) (1,f₄ 0))).2.val=
      ![UpperHalfPlane.I,K₄,UpperHalfPlane.I,K₄] j := by
  let X:=((S₄).generator (e₄ 0))⁻¹
  let Y:=((S₄).generator (e₄ 1))⁻¹
  have h0 (g : (S₄).Generated) : σ₄ (g,f₄ 0)=(g*X,f₄ 1) :=
    halfTurnWalk_four_step t ht w hw hn hc 0 g
  have h1 (g : (S₄).Generated) : σ₄ (g,f₄ 1)=(g*Y,f₄ 0) :=
    halfTurnWalk_four_step t ht w hw hn hc 1 g
  have hv:=halfTurnFourBase_axis_vertices t ht w hc
  fin_cases j
  · exact hv.1
  · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ (σ₄ (1,f₄ 0))).2.val=K₄
    rw [h0]
    exact hv.2
  · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ (σ₄ (σ₄ (1,f₄ 0)))).2.val=UpperHalfPlane.I
    rw [h0,h1]
    exact hv.1
  · change (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ (σ₄ (σ₄ (σ₄ (1,f₄ 0))))).2.val=K₄
    rw [h0,h1,h0]
    exact hv.2

/-- Actual evaluation injectivity and the true four-copy base cycle determine
every element of the entire generated group fixing the first center. -/
theorem halfTurnFourBase_stabilizer
    (heval : Function.Injective (S₄).evaluation) :
    (MulAction.stabilizer (S₄).Generated UpperHalfPlane.I : Set (S₄).Generated)=
      {1,halfTurnFourBase_firstHalfTurn t ht w hw hn hc} := by
  let F:=halfTurnFourBase_firstHalfTurn t ht w hw hn hc
  have hv:=halfTurnFourBase_axis_vertices t ht w hc
  have hI : UpperHalfPlane.I∈(P₄).carrier := by
    rw [←hv.1]
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q₄ hf₄ 0).property
  have hF : F•UpperHalfPlane.I=UpperHalfPlane.I := by
    change F.val UpperHalfPlane.I=UpperHalfPlane.I
    rw [halfTurnFourBase_firstHalfTurn_coe]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 zero_lt_one).2
  ext g
  change g•UpperHalfPlane.I=UpperHalfPlane.I ↔ g=1 ∨ g=F
  constructor
  · intro hg
    have hb : (S₄).copyEvaluation (g,⟨UpperHalfPlane.I,hI⟩)=
        (S₄).copyEvaluation (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ (1,f₄ 0)) := by
      change g•UpperHalfPlane.I=(1 : (S₄).Generated)•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0
      rw [one_smul,hv.1]
      exact hg
    obtain ⟨j,hj⟩:=halfTurnCone_periodic_vertex_copy Q₄ hf₄ S₄ heval (1,f₄ 0) 3
      (halfTurnWalk_four_base_period t ht w hw hn hc 0 1) (g,⟨UpperHalfPlane.I,hI⟩) hb
    have hp:=congrArg (fun a : (S₄).Copy=>a.2.val) hj
    rw [halfTurnFourBase_cycle_points] at hp
    fin_cases j
    · left
      exact (congrArg Prod.fst hj).symm
    · have hi:=congrArg UpperHalfPlane.im hp
      change t^2=1 at hi
      nlinarith only [ht,hi]
    · right
      exact (congrArg Prod.fst hj).symm
    · have hi:=congrArg UpperHalfPlane.im hp
      change t^2=1 at hi
      nlinarith only [ht,hi]
  · rintro (rfl | rfl)
    · exact one_smul _ _
    · exact hF

/-- The actual base-vertex center has true stabilizer order two. -/
theorem halfTurnFourBase_stabilizer_card
    (heval : Function.Injective (S₄).evaluation) :
    Nat.card (MulAction.stabilizer (S₄).Generated UpperHalfPlane.I)=2 := by
  classical
  let F:=halfTurnFourBase_firstHalfTurn t ht w hw hn hc
  have hF : F•UpperHalfPlane.I=UpperHalfPlane.I := by
    change F.val UpperHalfPlane.I=UpperHalfPlane.I
    rw [halfTurnFourBase_firstHalfTurn_coe]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 zero_lt_one).2
  have hne : F≠1 := by
    intro he
    have hh:=congrArg Subtype.val he
    change (halfTurnFourBase_firstHalfTurn t ht w hw hn hc).val=1 at hh
    rw [halfTurnFourBase_firstHalfTurn_coe] at hh
    have ho:=hSLIsometry_orderOf_eq_realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one)
    rw [hh,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 zero_lt_one).1,orderOf_one] at ho
    norm_num at ho
  let a : MulAction.stabilizer (S₄).Generated UpperHalfPlane.I:=⟨F,hF⟩
  apply (Nat.card_eq_two_iff' (1 : MulAction.stabilizer (S₄).Generated UpperHalfPlane.I)).mpr
  refine ⟨a,?_,?_⟩
  · intro he
    exact hne (congrArg Subtype.val he)
  · intro k hk
    apply Subtype.ext
    have hm : k.val∈({1,F} : Set (S₄).Generated) := by
      rw [←halfTurnFourBase_stabilizer t ht w hw hn hc heval]
      exact k.property
    simp only [mem_insert_iff,mem_singleton_iff] at hm
    rcases hm with he | he
    · exact False.elim (hk (Subtype.ext he))
    · exact he

/-- The actual whole orbit of the base center meets the original closed polygon
exactly at its two original axis endpoints. -/
theorem halfTurnFourBase_carrier_orbit
    (heval : Function.Injective (S₄).evaluation) :
    (P₄).carrier∩MulAction.orbit (S₄).Generated UpperHalfPlane.I={UpperHalfPlane.I,K₄} := by
  have hv:=halfTurnFourBase_axis_vertices t ht w hc
  have hI : UpperHalfPlane.I∈(P₄).carrier := by
    rw [←hv.1]
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q₄ hf₄ 0).property
  have hK : K₄∈(P₄).carrier := by
    rw [←hv.2]
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q₄ hf₄ 1).property
  ext z
  constructor
  · rintro ⟨hz,⟨g,hg⟩⟩
    have hb : (S₄).copyEvaluation (g⁻¹,⟨z,hz⟩)=
        (S₄).copyEvaluation (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonFlagStateCopy Q₄ hf₄ S₄ (1,f₄ 0)) := by
      change g⁻¹•z=(1 : (S₄).Generated)•_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q₄ hf₄ 0
      rw [one_smul,hv.1,←hg,inv_smul_smul]
    obtain ⟨j,hj⟩:=halfTurnCone_periodic_vertex_copy Q₄ hf₄ S₄ heval (1,f₄ 0) 3
      (halfTurnWalk_four_base_period t ht w hw hn hc 0 1) (g⁻¹,⟨z,hz⟩) hb
    have hp:=congrArg (fun a : (S₄).Copy=>a.2.val) hj
    rw [halfTurnFourBase_cycle_points] at hp
    fin_cases j
    · exact Or.inl hp.symm
    · exact Or.inr hp.symm
    · exact Or.inl hp.symm
    · exact Or.inr hp.symm
  · rintro (rfl | rfl)
    · exact ⟨hI,1,one_smul _ _⟩
    · refine ⟨hK,(S₄).generator (e₄ 0),?_⟩
      change (S₄).element (e₄ 0) UpperHalfPlane.I=K₄
      rw [halfTurnFour_pairing_element_index]
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)) UpperHalfPlane.I=K₄
      rw [←hv.1,←hv.2]
      exact halfTurnWalk_four_axis_image t ht w hc

/-- The genuine primitive polygon supplies evaluation injectivity internally,
so the base-vertex half-turn has its exact whole-group stabilizer and full closed-polygon orbit. -/
theorem halfTurnPrimitive_four_base_center (q : ℕ) (hq : 2≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    (MulAction.stabilizer (S₄).Generated UpperHalfPlane.I : Set (S₄).Generated)=
        {1,halfTurnFourBase_firstHalfTurn t ht w hw hn hc} ∧
      Nat.card (MulAction.stabilizer (S₄).Generated UpperHalfPlane.I)=2 ∧
      (P₄).carrier∩MulAction.orbit (S₄).Generated UpperHalfPlane.I={UpperHalfPlane.I,K₄} := by
  have heval:=halfTurnCone_compact_evaluation_injective Q₄ hf₄ S₄
    (halfTurnPrimitive_four_local_tessellation t ht w hw hn hc q hq hθ horder)
  exact ⟨halfTurnFourBase_stabilizer t ht w hw hn hc heval,
    halfTurnFourBase_stabilizer_card t ht w hw hn hc heval,
    halfTurnFourBase_carrier_orbit t ht w hw hn hc heval⟩

end FourBaseStabilizer
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The three actual unchanged half-turn centers of the four-side chamber. -/
def halfTurnPrimitive_four_centers (t : ℝ) (ht : 1<t) (w : ℍ) : Fin 3→ℍ :=
  ![UpperHalfPlane.I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t (zero_lt_one.trans ht),w]

/-- The genuine self-side centers, keeping the base vertex separate. -/
def halfTurnPrimitive_four_self_centers (t : ℝ) (ht : 1<t) (w : ℍ) : Fin 2→ℍ :=
  ![_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t (zero_lt_one.trans ht),w]

/-- The two actual self-side centers each lie on exactly one original side. -/
theorem halfTurnPrimitive_four_self_side_iff (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (i : Fin 2) (j : Fin 4) :
    halfTurnPrimitive_four_self_centers t ht w i∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide
      (halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
        (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon j ↔
      j=(![0,2] : Fin 2→Fin 4) i := by
  have ht0 : 0<t:=zero_lt_one.trans ht
  have ht2 : t<t^2:=by nlinarith only [ht]
  have hnormt : ‖(⟨0,t⟩ : ℂ)‖=t :=
    nativeSideCoordinates_axis_norm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 t ht0) rfl
  have hnormw : ‖(w : ℂ)‖=t := by
    have hh : ‖(w : ℂ)‖^2=t^2 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_apply]
      simpa only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two] using hn
    nlinarith only [hh,norm_nonneg (w : ℂ),ht0]
  have hpoly : w.re^2+w.im^2-2*(t^2/w.re)*w.re+t^2=0 := by
    rw [hn]
    field_simp
    ring
  rw [halfTurnFour_side_coordinates]
  clear hn hc
  fin_cases i <;> fin_cases j <;>
    dsimp only [halfTurnPrimitive_four_self_centers,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,Fin.reduceFinMk] <;>
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] <;> (repeat' constructor) <;> intros <;>
    nlinarith [sq_nonneg t]

/-- The actual maps of the two unchanged self sides have their true order and fixed centers. -/
theorem halfTurnPrimitive_four_self_center_fixed (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) (i : Fin 2) :
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
    let S:=halfTurnFour_pairing t ht w hw hn hc
    let s:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf ((![0,2] : Fin 2→Fin 4) i)
    S.element s (halfTurnPrimitive_four_self_centers t ht w i)=
      halfTurnPrimitive_four_self_centers t ht w i ∧ orderOf (S.element s)=2 := by
  dsimp only
  rw [halfTurnFour_pairing_element_index]
  fin_cases i
  · exact ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at t (zero_lt_one.trans ht)).2,
      (hSLIsometry_orderOf_eq_realSLMobius _).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at t (zero_lt_one.trans ht)).1⟩
  · exact ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w).2,
      (hSLIsometry_orderOf_eq_realSLMobius _).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at w).1⟩

theorem halfTurnPrimitive_four_centers_injective (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) : Function.Injective (halfTurnPrimitive_four_centers t ht w) := by
  intro i j he
  have hre:=congrArg UpperHalfPlane.re he
  have him:=congrArg UpperHalfPlane.im he
  fin_cases i <;> fin_cases j <;>
    norm_num [halfTurnPrimitive_four_centers,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe] at hre him ⊢ <;> linarith

/-- The actual whole generated group has stabilizer order two at each true self-side
center, and its closed-chamber representative is orbit-unique. -/
theorem halfTurnPrimitive_four_self_center_whole_group (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hA6 : (halfTurnFour_pairing t ht w hw hn hc).FiniteFiberLocalTessellationCondition) (i : Fin 2) :
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let S:=halfTurnFour_pairing t ht w hw hn hc
    let z:=halfTurnPrimitive_four_self_centers t ht w i
    Nat.card (MulAction.stabilizer S.Generated z)=2 ∧
      z∈P.carrier ∧ ∀(g : S.Generated)(p : P.Point),g•p.val=z→p.val=z := by
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFour_pairing t ht w hw hn hc
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let z:=halfTurnPrimitive_four_self_centers t ht w i
  let j:=(![0,2] : Fin 2→Fin 4) i
  let s:=e j
  have hz : z∈s.val := (halfTurnPrimitive_four_self_side_iff t ht w hw hn hc i j).mpr rfl
  let x : P.Point:=⟨z,P.side_subset_carrier s hz⟩
  have huSide : ∀v : P.Side,z∈v.val→v=s := by
    intro v hv
    obtain ⟨k,rfl⟩:=e.surjective v
    have hk : k=j := (halfTurnPrimitive_four_self_side_iff t ht w hw hn hc i k).mp hv
    exact congrArg e hk
  have hp : S.paired s=s := by
    change e ((Equiv.swap (1 : Fin 4) 3) (e.symm (e j)))=e j
    rw [e.symm_apply_apply]
    apply congrArg e
    fin_cases i <;> norm_num [j,Equiv.swap_apply_def]
  have hd:=halfTurnPrimitive_four_self_center_fixed t ht w hw hn hc i
  have hfix : S.generator s•z=z := hd.1
  have hnGen : S.generator s≠1 := by
    intro he
    have hh : S.element s=1 := congrArg Subtype.val he
    have ho : orderOf (S.element s)=2 := hd.2
    rw [hh,orderOf_one] at ho
    norm_num at ho
  have hEval:=halfTurnCone_compact_evaluation_injective Q hf S hA6
  refine ⟨halfTurnCone_self_side_stabilizer_card S hEval x s hz huSide hp hfix hnGen,
    x.property,?_⟩
  intro g p hgp
  exact congrArg Subtype.val (halfTurnCone_unique_side_copy S hEval x s hz huSide hp hfix g p hgp).1

/--
The actual primitive four-side chamber has the three genuine order-two
centers in three different whole-group orbits; actual local tessellation is derived internally.
-/
theorem halfTurnPrimitive_four_centers_data (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (q : ℕ) (hq : 2≤q) (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
    let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
      (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
    let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
    let S:=halfTurnFour_pairing t ht w hw hn hc
    let Z:=halfTurnPrimitive_four_centers t ht w
    (∀i : Fin 3,Nat.card (MulAction.stabilizer S.Generated (Z i))=2 ∧ Z i∈P.carrier) ∧
      ∀(i j : Fin 3)(g : S.Generated),g•Z i=Z j→i=j := by
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFour_pairing t ht w hw hn hc
  let Z:=halfTurnPrimitive_four_centers t ht w
  have hA6:=halfTurnPrimitive_four_local_tessellation t ht w hw hn hc q hq hθ horder
  have hEval:=halfTurnCone_compact_evaluation_injective Q hf S hA6
  have hSide (i : Fin 2):=halfTurnPrimitive_four_self_center_whole_group t ht w hw hn hc hA6 i
  have hv:_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 0=UpperHalfPlane.I := (halfTurnFourBase_axis_vertices t ht w hc).1
  have hI : UpperHalfPlane.I∈P.carrier := by
    rw [←hv]
    exact (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonPoincareVertex Q hf 0).property
  have hData : ∀i : Fin 3,Nat.card (MulAction.stabilizer S.Generated (Z i))=2 ∧ Z i∈P.carrier := by
    intro i
    fin_cases i
    · exact ⟨halfTurnFourBase_stabilizer_card t ht w hw hn hc hEval,hI⟩
    · exact ⟨(hSide 0).1,(hSide 0).2.1⟩
    · exact ⟨(hSide 1).1,(hSide 1).2.1⟩
  refine ⟨hData,?_⟩
  intro i j g hg
  have hInj:=halfTurnPrimitive_four_centers_injective t ht w hw
  fin_cases j
  · fin_cases i
    · rfl
    · have hi : g⁻¹•UpperHalfPlane.I=Z 1 := inv_smul_eq_iff.mpr hg.symm
      exact (hInj (show Z 0=Z 1 from (hSide 0).2.2 g⁻¹ ⟨UpperHalfPlane.I,hI⟩ hi)).symm
    · have hi : g⁻¹•UpperHalfPlane.I=Z 2 := inv_smul_eq_iff.mpr hg.symm
      exact (hInj (show Z 0=Z 2 from (hSide 1).2.2 g⁻¹ ⟨UpperHalfPlane.I,hI⟩ hi)).symm
  · exact hInj ((hSide 0).2.2 g ⟨Z i,(hData i).2⟩ hg)
  · exact hInj ((hSide 1).2.2 g ⟨Z i,(hData i).2⟩ hg)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Set MeasureTheory
open scoped UpperHalfPlane

/-- The unchanged four-side generators are genuinely conformal. -/
theorem halfTurnPrimitive_four_group_conformal
    (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re)) :
    (halfTurnFour_pairing t ht w hw hn hc).Generated≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  rw [halfTurnFour_generated]
  exact threeHalfTurn_native_group_conformal _ _ _

/-- The actual primitive original quadrilateral has the full four-cone
signature, including its genuine order-two vertex center. -/
theorem halfTurnPrimitive_four_signature
    (t : ℝ) (ht : 1<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (q : ℕ) (hq : 3≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    let S:=halfTurnFour_pairing t ht w hw hn hc
    letI:=(halfTurnPrimitive_four_poincare t ht w hw hn hc q (by omega) hθ horder).1
    let hConf:=halfTurnPrimitive_four_group_conformal t ht w hw hn hc
    HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData S.Generated hConf).asFuchsianDisc
      0 [2,2,2,q] 0 := by
  let hk:=one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)
  let Q:=(halfTurnQuadCanonicalSupport (t^2) (t^2/w.re) hk hc).toDiscPolygon
  let hf:=halfTurnQuadCanonical_finite (t^2) (t^2/w.re) hk hc
  let P:=_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf
  let S:=halfTurnFour_pairing t ht w hw hn hc
  let H:=S.Generated
  let hd:DiscreteTopology H:=
    (halfTurnPrimitive_four_poincare t ht w hw hn hc q (by omega) hθ horder).1
  let hConf:=halfTurnPrimitive_four_group_conformal t ht w hw hn hc
  have hFD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume P.interior:=
    (halfTurnPrimitive_four_poincare t ht w hw hn hc q (by omega) hθ horder).2
  let centers:=halfTurnPrimitive_four_centers t ht w
  let e:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSideEquiv Q hf
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  let K:=F*G*W
  let f : H:=halfTurnFourBase_firstHalfTurn t ht w hw hn hc
  let a : H:=f*S.generator (e 0)*S.generator (e 2)
  have hfval : f.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F:=halfTurnFourBase_firstHalfTurn_coe t ht w hw hn hc
  have hprod : a.val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K := by
    change f.val*S.element (e 0)*S.element (e 2)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K
    rw [hfval,halfTurnFour_pairing_element_index,halfTurnFour_pairing_element_index]
    apply IsometryEquiv.ext
    intro z
    change F•(G•(W•z))=(F*G*W)•z
    simp only [mul_smul]
  have ha : orderOf a=q := by
    calc
      orderOf a=orderOf a.val:=(orderOf_injective H.subtype Subtype.val_injective a).symm
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry K):=by rw [hprod]
      _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius K):=hSLIsometry_orderOf_eq_realSLMobius K
      _=q:=horder
  let v:=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf 3
  have hav : a•v=v := by
    change a.val v=v
    rw [hprod]
    have hh:=halfTurnCanonical_product_fixes_summit 1 t zero_lt_one ht w hw hn hc
    have hh' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W) v=v := by
      simpa only [one_mul] using hh
    change F•(G•(W•v))=v at hh'
    change (F*G*W)•v=v
    simpa only [mul_smul] using hh'
  have hcenters : ∀i,∃b : H,orderOf b=2 ∧ b•centers i=centers i := by
    intro i
    fin_cases i
    · refine ⟨f,?_,?_⟩
      · calc
          orderOf f=orderOf f.val:=(orderOf_injective H.subtype Subtype.val_injective f).symm
          _=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F):=by rw [hfval]
          _=2:=(hSLIsometry_orderOf_eq_realSLMobius F).trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 zero_lt_one).1
      · change f.val UpperHalfPlane.I=UpperHalfPlane.I
        rw [hfval]
        exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 zero_lt_one).2
    · let b : H:=S.generator (e 0)
      have hdata:=halfTurnPrimitive_four_self_center_fixed t ht w hw hn hc 0
      exact ⟨b,(orderOf_injective H.subtype Subtype.val_injective b).symm.trans hdata.2,hdata.1⟩
    · let b : H:=S.generator (e 2)
      have hdata:=halfTurnPrimitive_four_self_center_fixed t ht w hw hn hc 1
      exact ⟨b,(orderOf_injective H.subtype Subtype.val_injective b).symm.trans hdata.2,hdata.1⟩
  have hdata:=halfTurnPrimitive_four_centers_data t ht w hw hn hc q (by omega) hθ horder
  have hArea : (volume P.interior).toReal=Real.pi-2*Real.pi/q := by
    have hQA : Q.area=volume P.interior:=Q.area_eq_halfPlane_volume
    rw [←hQA,halfTurnQuadCanonical_area,
      halfTurnQuadCanonical_cosine_trace t w.re w.im ht hw w.im_pos hn,hθ]
    ring
  exact halfTurnPrimitive_native_signature H hConf P.interior P.carrier hFD
    (_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_isCompact Q hf) (halfTurnFourPairing_orbit_cover t ht w hw hn hc)
    q hq hArea centers hcenters (fun i=>(hdata.1 i).1) hdata.2 a ha v hav

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Set MeasureTheory
open scoped UpperHalfPlane

/-- Equal actual native groups have the same faithful original boundary
signature; no abstract replacement action or assigned genus is introduced. -/
theorem halfTurnNative_signature_group_eq
    (H K : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] [DiscreteTopology K]
    (hH : H≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (hK : K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup)
    (hEq : H=K) {g p : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData H hH).asFuchsianDisc
      g orders p) :
    HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData K hK).asFuchsianDisc
      g orders p := by
  subst K
  exact hSig

/-- Every actual primitive compact canonical half-turn model has precisely
its genuine four-cone cofinite signature, including the boundary halfperiod case. -/
theorem halfTurnCanonical_primitive_signature
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (q : ℕ) (hq : 3≤q)
    (hθ : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q)
    (horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
        (zero_lt_one.trans (hu.trans_lt hut)))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc
      0 [2,2,2,q] 0 := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
  let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
  let : DiscreteTopology H:=threeHalfTurn_native_group_discrete_of_original F G W hd
  let hConf:=threeHalfTurn_native_group_conformal F G W
  change HasCofiniteFuchsianSignature (nativeConformalSubgroup_halfPlaneData H hConf).asFuchsianDisc
    0 [2,2,2,q] 0
  rcases eq_or_lt_of_le hu with he|he
  · subst u
    have ht : 1<t:=hut
    have ho : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one*
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL t (zero_lt_one.trans ht)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w))=q := by
      simpa only [one_mul] using horder
    let S:=halfTurnFour_pairing t ht w hw hn hc
    let : DiscreteTopology S.Generated:=
      (halfTurnPrimitive_four_poincare t ht w hw hn hc q (by omega) hθ ho).1
    let hSC:=halfTurnPrimitive_four_group_conformal t ht w hw hn hc
    have hEq : S.Generated=H := by
      simpa only [H,F,G,W,one_mul] using halfTurnFour_generated t ht w hw hn hc
    exact halfTurnNative_signature_group_eq S.Generated H hSC hConf hEq
      (halfTurnPrimitive_four_signature t ht w hw hn hc q hq hθ ho)
  · let S:=halfTurnFivePairing u t he hut w hw hn hc
    let : DiscreteTopology S.Generated:=
      (halfTurnPrimitive_five_poincare u t he hut w hw hn hc q (by omega) hθ horder).1
    let hSC:=halfTurnPrimitive_five_group_conformal u t he hut w hw hn hc
    have hEq : S.Generated=H := by
      exact halfTurnFivePairing_generated u t he hut w hw hn hc
    exact halfTurnNative_signature_group_eq S.Generated H hSC hConf hEq
      (halfTurnPrimitive_five_signature u t he hut w hw hn hc q hq hθ horder)

end LowDimensionalTopology.Geometry.Fuchsian




namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open Set MeasureTheory
open scoped UpperHalfPlane

/-- Every actual discrete compact canonical model has one of the original
four-cone or exceptional triangular signatures, with all group data derived. -/
theorem halfTurnCanonical_small_parameter_signatures
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)
    let G:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
      (zero_lt_one.trans (hu.trans_lt hut)))
    let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
    let H:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry F,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry G,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry W} : Set (ℍ≃ᵢℍ))
    letI:=threeHalfTurn_native_group_discrete_of_original F G W hd
    let hConf:=threeHalfTurn_native_group_conformal F G W
    let P:=nativeConformalSubgroup_halfPlaneData H hConf
    (∃q : ℕ,3≤q ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,2,2,q] 0) ∨
      (∃n : ℕ,7≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,3,n] 0) ∨
      (∃n : ℕ,5≤n ∧ HasCofiniteFuchsianSignature P.asFuchsianDisc 0 [2,4,n] 0) := by
  obtain ⟨p,q,hq,hp,hpq,_hcop,hθ⟩:=halfTurnCanonical_reduced u t
    (zero_lt_one.trans_le hu) (hu.trans_lt hut) w hw hn hc hd
  by_cases hp1 : p=1
  · have hq3 : 3≤q:=by omega
    left
    refine ⟨q,hq3,?_⟩
    have hθ' : Real.arccos ((t-1/t)*w.re/(2*w.im))=Real.pi/q := by
      rw [halfTurnQuadCanonical_cosine_trace t w.re w.im (hu.trans_lt hut) hw w.im_pos hn] at hθ
      simpa only [hp1,Nat.cast_one,mul_one] using hθ
    exact halfTurnCanonical_primitive_signature u t hu hut w hw hn hc hd q hq3 hθ' hq.symm
  · have hp2 : 2≤p:=by omega
    have h:=halfTurnCanonical_nonprimitive_order_classification u t hu hut w hw hn hc hd
      p q hp2 hpq hq hθ
    exact Or.inr h.2

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

theorem halfTurnCanonical_discrete_cosines
    (u t : ℝ) (hu : 1≤u) (hut : u<t) (w : ℍ)
    (hw : 0<w.re) (hn : w.re^2+w.im^2=t^2) (hc : t^2+1<2*(t^2/w.re))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u (zero_lt_one.trans_le hu)),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos (zero_lt_one.trans_le hu)
          (zero_lt_one.trans (hu.trans_lt hut)))),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
 :
    let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/
      Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
        (halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
    (∃q : ℕ,3≤q ∧ lam=Real.cos (Real.pi/q)) ∨
    (∃q : ℕ,5≤q ∧ lam=Real.cos (2*Real.pi/q)) ∨
    (∃q : ℕ,7≤q ∧ lam=Real.cos (3*Real.pi/q)) := by
  let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/
    Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
      (halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
  have ht:1<t:=hu.trans_lt hut
  obtain ⟨p,q,hq,hp,hpq,_hcop,hθ⟩:=
    halfTurnCanonical_reduced u t (zero_lt_one.trans_le hu) ht w hw hn hc hd
  have hbounds:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2 : ℕ)≠0)) hc
  have hlam:lam=Real.cos (Real.pi*p/q):=by
    rw [←hθ]
    exact (Real.cos_arccos (by linarith only [hbounds.1]) hbounds.2.1.le).symm
  rcases (show p=1 ∨ 2≤p by omega) with hp1|hp2
  · refine Or.inl ⟨q,by omega,?_⟩
    simpa only [hp1,Nat.cast_one,mul_one] using hlam
  · have hclass:=halfTurnCanonical_nonprimitive_order_classification u t hu hut w hw hn hc hd
      p q hp2 hpq hq hθ
    rcases hclass.1 with hp2|hp3
    · refine Or.inr (Or.inl ⟨q,by omega,?_⟩)
      simpa only [hp2,Nat.cast_ofNat,mul_comm Real.pi 2] using hlam
    · refine Or.inr (Or.inr ⟨q,by omega,?_⟩)
      simpa only [hp3,Nat.cast_ofNat,mul_comm Real.pi 3] using hlam

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The entire small-parameter classification for the unchanged original
three-half-turn group: all possible actual parameters and all genuine
cofinite signatures. Only the original discreteness and product trace
conditions enter; physical domains, product order and signatures are derived. -/
theorem threeHalfTurn_original_small_parameter_classification
    (f g h : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f,g,h} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : orderOf f=2) (hg : orderOf g=2) (hh : orderOf h=2)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f,g,h} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)<2) :
    ((∃q : ℕ,3≤q ∧ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2=Real.cos (Real.pi/q)) ∨
      (∃q : ℕ,5≤q ∧ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2=Real.cos (2*Real.pi/q)) ∨
      (∃q : ℕ,7≤q ∧ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2=Real.cos (3*Real.pi/q))) ∧
    ((∃q : ℕ,3≤q ∧ HasCofiniteFuchsianSignature D 0 [2,2,2,q] 0) ∨
      (∃n : ℕ,7≤n ∧ HasCofiniteFuchsianSignature D 0 [2,3,n] 0) ∨
      (∃n : ℕ,5≤n ∧ HasCofiniteFuchsianSignature D 0 [2,4,n] 0)) := by
  let F : Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
    ⟨f,Subgroup.subset_closure (by simp)⟩
  let G : Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
    ⟨g,Subgroup.subset_closure (by simp)⟩
  let K : Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
    ⟨h,Subgroup.subset_closure (by simp)⟩
  let A:=D.normalizedLift F
  let B:=D.normalizedLift G
  let C:=D.normalizedLift K
  let q₀:=D.halfPlaneNormalizer
  have hA : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq f).trans hf
  have hB : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq g).trans hg
  have hC : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=2:=by
    rw [D.normalizedLift_spec]
    exact ((MulAut.conj q₀).orderOf_eq h).trans hh
  have hgroup : D.normalizedGroup=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=by
    change (Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)).map
      (MulAut.conj q₀).toMonoidHom=_
    rw [MonoidHom.map_closure,Set.image_insert_eq,Set.image_insert_eq,Set.image_singleton]
    change Subgroup.closure {q₀*f*q₀⁻¹,q₀*g*q₀⁻¹,q₀*h*q₀⁻¹}=_
    rw [←D.normalizedLift_spec F,←D.normalizedLift_spec G,←D.normalizedLift_spec K]
  have hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact D.normalizedGroup_discrete
  have hNE' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    rw [←hgroup]
    exact hNE.conjugation q₀
  have hprod : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C)=q₀*(f*g*h)*q₀⁻¹:=by
    dsimp only [A,B,C]
    rw [map_mul,map_mul,D.normalizedLift_spec,D.normalizedLift_spec,D.normalizedLift_spec]
    change (q₀*f*q₀⁻¹)*(q₀*g*q₀⁻¹)*(q₀*h*q₀⁻¹)=q₀*(f*g*h)*q₀⁻¹
    group
  have habs : |Matrix.trace (A*B*C).val|=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h):=by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs,hprod,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation]
    rfl
  have _horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*C))=orderOf (f*g*h):=by
    rw [hprod]
    exact (MulAut.conj q₀).orderOf_eq (f*g*h)
  obtain ⟨T,hAt,hBt,hCt⟩:=threeHalfTurn_original_centers_triangle A B C hA hB hC hNE'
  obtain ⟨r,u,t,hu,ht,w,hu1,hut,hw,hn,hG,hdisc,htrace,hord⟩:=
    halfTurn_actual_halfperiod_group_model T A B C hAt hBt hCt hd
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu
  let V:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))
  let W:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w
  have htrace' : |Matrix.trace (U*V*W).val|=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h):=htrace.trans habs
  have _hord' : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (U*V*W))=orderOf (f*g*h):=hord.trans _horder
  have hsmall' : |Matrix.trace (U*V*W).val|<2:=by rwa [htrace']
  change |Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL u hu*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (u*t) (mul_pos hu (zero_lt_one.trans ht))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL w).val|<2 at hsmall'
  rw [axisHalfTurns_point_triple_trace] at hsmall'
  have hratio : (u*t)/u-u/(u*t)=t-1/t:=by field_simp
  rw [hratio] at hsmall'
  have hscalar:=halfTurn_small_trace_compact_scalar t w.re w.im ht hw w.im_pos hn
    ((le_abs_self _).trans_lt hsmall')
  have hc : t^2+1<2*(t^2/w.re):=by
    have hh' : t^2+1<(2*t^2)/w.re:=(lt_div_iff₀ hw).mpr hscalar
    simpa only [mul_div_assoc] using hh'
  let lam:=halfTurnQuadKleinB (t^2) (t^2/w.re)/
    Real.sqrt ((halfTurnQuadKleinB (t^2) (t^2/w.re))^2+1-
      (halfTurnQuadKleinA (t^2) (t^2/w.re))^2)
  have hb:=halfTurnQuadCanonical_angles (t^2) (t^2/w.re)
    (one_lt_pow₀ ht (by decide : (2:ℕ)≠0)) hc
  have htr : |Matrix.trace (U*V*W).val|=2*lam:=by
    rw [halfTurnCanonical_trace u t hu ht w hw hn,
      abs_of_pos (mul_pos (by norm_num) hb.1)]
  have hlam : lam=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (f*g*h)/2:=by linarith only [htr,htrace']
  let s:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀
  have hGs : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate s (Subgroup.closure ({f,g,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))=
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius U,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius V,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius W}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=by
    rw [show s=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀ by rfl,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose]
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r) D.normalizedGroup=_
    rw [hgroup]
    exact hG
  have hDs : s.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀).val) '' D.carrier=_
    rw [show (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r*q₀).val=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius r).val*q₀.val by rfl,
      Equiv.Perm.coe_mul,Function.comp_def,←Set.image_image,D.halfPlaneNormalizer_image,
      realSLMobius_image_openHalfPlane]
  constructor
  · have hcos:=halfTurnCanonical_discrete_cosines u t hu1 hut w hw hn hc hdisc
    rw [←hlam]
    exact hcos
  · have hclass:=halfTurnCanonical_small_parameter_signatures u t hu1 hut w hw hn hc hdisc
    rcases hclass with ⟨n,hn,hSig⟩|⟨n,hn,hSig⟩|⟨n,hn,hSig⟩
    · exact Or.inl ⟨n,hn,threeHalfTurn_original_signature_of_native D U V W
        hdisc s hGs hDs 0 0 [2,2,2,n] hSig⟩
    · exact Or.inr (Or.inl ⟨n,hn,threeHalfTurn_original_signature_of_native D U V W
        hdisc s hGs hDs 0 0 [2,3,n] hSig⟩)
    · exact Or.inr (Or.inr ⟨n,hn,threeHalfTurn_original_signature_of_native D U V W
        hdisc s hGs hDs 0 0 [2,4,n] hSig⟩)

/-- The same complete compact-branch conclusions for the source's genuine
three-center geometric invariant, on any original invariant disc of the
unchanged generated group. The trace parameter equality is proved. -/
theorem threeHalfTurn_triangle_small_parameter_classification
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (D : FuchsianDisc (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt A T.a) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt B T.b) (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt C T.c)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hsmall : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T<1) :
    ((∃q : ℕ,3≤q ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T=Real.cos (Real.pi/q)) ∨
      (∃q : ℕ,5≤q ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T=Real.cos (2*Real.pi/q)) ∨
      (∃q : ℕ,7≤q ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T=Real.cos (3*Real.pi/q))) ∧
    ((∃q : ℕ,3≤q ∧ HasCofiniteFuchsianSignature D 0 [2,2,2,q] 0) ∨
      (∃n : ℕ,7≤n ∧ HasCofiniteFuchsianSignature D 0 [2,3,n] 0) ∨
      (∃n : ℕ,5≤n ∧ HasCofiniteFuchsianSignature D 0 [2,4,n] 0)) := by
  have htr : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)=
      2*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T := by
    rw [←map_mul,←map_mul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_traceAbs]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurn_triple_abs_trace T A B C hA hB hC
  have hsmall' : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)<2 := by
    rw [htr]
    linarith only [hsmall]
  have hparam : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusTraceAbs (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)/2=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnTriangleInvariant T := by rw [htr];ring
  have h:=threeHalfTurn_original_small_parameter_classification
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) D hA.1 hB.1 hC.1 hNE hsmall'
  simpa only [hparam] using h

end LowDimensionalTopology.Geometry.Fuchsian
