/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeOrders
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ConvexFiniteRotationSectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups ComplexConjugate
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
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def heckeCornerCoordinate (v : ℍ) (z : ℍ) : ℂ :=
  ((z:ℂ)-(v:ℂ))/((z:ℂ)-conj (v:ℂ))

theorem heckeCornerCoordinate_denom_ne (v z : ℍ) :
    (z:ℂ)-conj (v:ℂ)≠0 := by
  intro he
  have h:=congrArg Complex.im (sub_eq_zero.mp he)
  simp only [Complex.conj_im] at h
  change z.im= -v.im at h
  linarith [z.im_pos,v.im_pos]

theorem heckeCornerCoordinate_continuous (v : ℍ) :
    Continuous (heckeCornerCoordinate v) := by
  unfold heckeCornerCoordinate
  exact (UpperHalfPlane.continuous_coe.sub continuous_const).div
    (UpperHalfPlane.continuous_coe.sub continuous_const) (heckeCornerCoordinate_denom_ne v)

theorem heckeCornerCoordinate_im (v z : ℍ) :
    (heckeCornerCoordinate v z).im =
      -2*v.im*(z.re-v.re)/Complex.normSq ((z:ℂ)-conj (v:ℂ)) := by
  simp only [heckeCornerCoordinate,Complex.div_im,Complex.sub_re,Complex.sub_im,
    Complex.conj_re,Complex.conj_im,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem heckeCornerCoordinate_rotated_im (v z : ℍ) (hv : ‖(v:ℂ)‖=1) :
    ((conj (v:ℂ)/(v:ℂ))*heckeCornerCoordinate v z).im =
      -2*v.im*(v.re*Complex.normSq (z:ℂ)-z.re)/Complex.normSq ((z:ℂ)-conj (v:ℂ)) := by
  have hvn : Complex.normSq (v:ℂ)=1:=by rw [Complex.normSq_eq_norm_sq,hv];norm_num
  have hvn' : v.re^2+v.im^2=1:=by simpa only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,pow_two] using hvn
  simp only [heckeCornerCoordinate,Complex.mul_im,Complex.div_re,Complex.div_im,
    Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.sub_im,hvn,div_one]
  have hd : Complex.normSq ((z:ℂ)-conj (v:ℂ))≠0:=by
    exact (Complex.normSq_pos.mpr (heckeCornerCoordinate_denom_ne v z)).ne'
  simp only [UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  field_simp
  simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  linear_combination (2*v.im*z.re)*hvn'

def heckePingPongSector (n : ℕ) (hn : 3≤n) : Set ℍ :=
  heckeCornerCoordinate (standardHeckeCorner n hn) ⁻¹' _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n

theorem heckePingPongSector_isOpen (n : ℕ) (hn : 3≤n) :
    IsOpen (heckePingPongSector n hn) :=
  (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector_isOpen n).preimage (heckeCornerCoordinate_continuous _)

theorem heckePingPongSector_contains_nonpositive (n : ℕ) (hn : 3≤n)
    (z : ℍ) (hz : z.re≤0) : z∈heckePingPongSector n hn := by
  let v:=standardHeckeCorner n hn
  have hθ : 0<Real.pi/(n:ℝ):=div_pos Real.pi_pos (by exact_mod_cast (show 0<n by omega))
  have hθlt : Real.pi/(n:ℝ)<Real.pi/2:=by
    apply (div_lt_iff₀ (by exact_mod_cast (show 0<n by omega))).mpr
    have hnr : (3:ℝ)≤n:=by exact_mod_cast hn
    nlinarith [Real.pi_pos]
  have ha : 0<v.re:=by
    change 0<Real.cos (Real.pi/(n:ℝ))
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos],hθlt⟩
  have hd : 0<Complex.normSq ((z:ℂ)-conj (v:ℂ)):=
    Complex.normSq_pos.mpr (heckeCornerCoordinate_denom_ne v z)
  change heckeCornerCoordinate v z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationPlaneSector_eq_halfPlanes n (by omega)]
  constructor
  · rw [heckeCornerCoordinate_im]
    exact div_pos (mul_pos_of_neg_of_neg (by linarith [v.im_pos]) (by linarith)) hd
  · have he : (Circle.exp (-_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n):ℂ)=conj (v:ℂ)/(v:ℂ) := by
      rw [standardHeckeCorner_multiplier n hn]
      change (Circle.exp (-_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n):ℂ)=((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:Circle)⁻¹:Circle)
      rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,Circle.exp_neg]
    rw [he,heckeCornerCoordinate_rotated_im v z (standardHeckeCorner_norm n hn)]
    apply div_neg_of_neg_of_pos _ hd
    have hz0 : (z:ℂ)≠0:=z.ne_zero
    have hzNorm : 0<Complex.normSq (z:ℂ):=Complex.normSq_pos.mpr hz0
    exact mul_neg_of_neg_of_pos (by linarith [v.im_pos]) (by nlinarith [mul_pos ha hzNorm])


theorem heckeCorner_re_pos (n : ℕ) (hn : 3≤n) : 0<(standardHeckeCorner n hn).re := by
  have hnr : (3:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : 0<(n:ℝ):=by positivity
  change 0<Real.cos (Real.pi/(n:ℝ))
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · linarith [div_pos Real.pi_pos hn0,Real.pi_pos]
  · apply (div_lt_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]

theorem heckeCornerCoordinate_sector_rotation (n : ℕ) (hn : 3≤n) :
    (Circle.exp (-_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n):ℂ)=
      conj (standardHeckeCorner n hn:ℂ)/(standardHeckeCorner n hn:ℂ) := by
  rw [standardHeckeCorner_multiplier n hn]
  change (Circle.exp (-_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod n):ℂ)=((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:Circle)⁻¹:Circle)
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator,Circle.exp_neg]

theorem heckePingPongSector_mem_iff (n : ℕ) (hn : 3≤n) (z : ℍ) :
    z∈heckePingPongSector n hn ↔
      z.re<(standardHeckeCorner n hn).re ∧
      z.re<(standardHeckeCorner n hn).re*Complex.normSq (z:ℂ) := by
  let v:=standardHeckeCorner n hn
  have hd : 0<Complex.normSq ((z:ℂ)-conj (v:ℂ)):=
    Complex.normSq_pos.mpr (heckeCornerCoordinate_denom_ne v z)
  change heckeCornerCoordinate v z∈_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPlaneSector n ↔ _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.finiteRotationPlaneSector_eq_halfPlanes n (by omega)]
  simp only [mem_ofPred_eq]
  rw [heckeCornerCoordinate_sector_rotation n hn,
    heckeCornerCoordinate_im,heckeCornerCoordinate_rotated_im v z (standardHeckeCorner_norm n hn)]
  constructor
  · rintro ⟨h1,h2⟩
    have h1':=(lt_div_iff₀ hd).mp h1
    have h2':=(div_lt_iff₀ hd).mp h2
    constructor
    · by_contra he
      have hsign:=mul_nonpos_of_nonpos_of_nonneg (show -2*v.im≤0 by linarith [v.im_pos])
        (sub_nonneg.mpr (le_of_not_gt he))
      linarith
    · by_contra he
      have hsign:=mul_nonneg_of_nonpos_of_nonpos (show -2*v.im≤0 by linarith [v.im_pos])
        (sub_nonpos.mpr (le_of_not_gt he))
      linarith
  · rintro ⟨h1,h2⟩
    constructor
    · exact div_pos (mul_pos_of_neg_of_neg (by linarith [v.im_pos])
        (sub_neg.mpr h1)) hd
    · exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by linarith [v.im_pos])
        (sub_pos.mpr h2)) hd

def heckePingPongGap (n : ℕ) (hn : 3≤n) : Set ℍ :=
  heckePingPongSector n hn∩{z | 0<z.re}

theorem heckePingPongGap_isOpen (n : ℕ) (hn : 3≤n) :
    IsOpen (heckePingPongGap n hn) :=
  (heckePingPongSector_isOpen n hn).inter (isOpen_lt continuous_const UpperHalfPlane.continuous_re)

theorem heckePingPongGap_nonempty (n : ℕ) (hn : 3≤n) :
    (heckePingPongGap n hn).Nonempty := by
  let a:=(standardHeckeCorner n hn).re
  have ha : 0<a:=heckeCorner_re_pos n hn
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (a/2) 1 (by norm_num)
  have hzre : z.re=a/2:=rfl
  have hzn : Complex.normSq (z:ℂ)=(a/2)^2+1:=by
    norm_num [z,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply,pow_two]
  refine ⟨z,?_,?_⟩
  · rw [heckePingPongSector_mem_iff,hzre,hzn]
    change a/2<a ∧ a/2<a*((a/2)^2+1)
    constructor
    · linarith
    · nlinarith [mul_nonneg ha.le (sq_nonneg (a/2))]
  · change 0<z.re
    rw [hzre]
    linarith

theorem heckeCornerCoordinate_product (n : ℕ) (hn : 3≤n) (z : ℍ) :
    heckeCornerCoordinate (standardHeckeCorner n hn) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n) z)=
      (_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)⁻¹*heckeCornerCoordinate (standardHeckeCorner n hn) z := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_center_cross_ratio (standardHeckeCornerSL n) (standardHeckeCorner n hn)
    (standardHeckeCornerSL_fixed n hn) z
  rw [standardHeckeCornerSL_denom,standardHeckeCorner_multiplier] at h
  exact h

theorem heckeCornerCoordinate_product_power (n : ℕ) (hn : 3≤n) (m : ℕ) (z : ℍ) :
    heckeCornerCoordinate (standardHeckeCorner n hn) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)^m) z)=
      ((_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationGenerator n:ℂ)⁻¹)^m*heckeCornerCoordinate (standardHeckeCorner n hn) z :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.coordinate_rotation_power _ _ _ (heckeCornerCoordinate_product n hn) m z

end LowDimensionalTopology.Geometry.Fuchsian
