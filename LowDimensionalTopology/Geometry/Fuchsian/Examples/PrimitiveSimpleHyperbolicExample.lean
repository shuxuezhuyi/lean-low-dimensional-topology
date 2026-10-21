/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenReassembly
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.HyperbolicSideNecessity
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisExample
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.FiniteAreaIdealBoundary
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.PingPong
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianPrimitives

/-!
# Infinitely many primitive simple hyperbolics in a finitely generated group

The explicit side transformations of an ideal quadrilateral generate the group.
Two Nielsen reassemblies give convex locally finite polygons for its twist words.
The resulting side pairings prove simplicity, an integer character proves
primitivity, and a strictly growing trace sequence distinguishes conjugacy classes.

The coordinate, reassembly and word calculations all refer to this same matrix
family and its original disc action.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual opposite-side transformation of the regular ideal quadrilateral. -/
def torusExampleFSL : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![3/Real.sqrt 2,1/Real.sqrt 2;1/Real.sqrt 2,1/Real.sqrt 2],by
    have hne : Real.sqrt (2:ℝ)≠0:=by positivity
    simp only [Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]⟩

/-- The other opposite-side transformation; the gluing is interlaced. -/
def torusExampleGSL : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![3/Real.sqrt 2,-(1/Real.sqrt 2);-(1/Real.sqrt 2),1/Real.sqrt 2],by
    have hne : Real.sqrt (2:ℝ)≠0:=by positivity
    simp only [Matrix.det_fin_two,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one]
    field_simp
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]⟩

/-- The full genuine generated subgroup, not an abstract word group. -/
def torusExampleGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        torusExampleFSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius torusExampleGSL}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem torusExampleGroup_finitelyGenerated : torusExampleGroup.FG := by
  apply (Subgroup.fg_iff _).mpr
  exact ⟨{_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
            torusExampleFSL,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius torusExampleGSL},rfl,Set.toFinite _⟩

theorem torusExampleFSL_coe (z : ℍ) :
    ((torusExampleFSL • z : ℍ):ℂ)=(3*(z:ℂ)+1)/((z:ℂ)+1) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply,torusExampleFSL,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]
  have hs : ((Real.sqrt (2:ℝ):ℂ))≠0:=by exact_mod_cast (show Real.sqrt (2:ℝ)≠0 by positivity)
  have hz : (z:ℂ)+1≠0:=by
    intro he
    have hi:=congrArg Complex.im he
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im,UpperHalfPlane.coe_im] at hi
    exact z.im_ne_zero hi
  field_simp [hs,hz]

theorem torusExampleGSL_coe (z : ℍ) :
    ((torusExampleGSL • z : ℍ):ℂ)=(3*(z:ℂ)-1)/(1-(z:ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Algebra.algebraMap_self_apply,torusExampleGSL,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,
    Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_one,Complex.ofReal_ofNat]
  have hs : ((Real.sqrt (2:ℝ):ℂ))≠0:=by exact_mod_cast (show Real.sqrt (2:ℝ)≠0 by positivity)
  rw [show -(1/((Real.sqrt (2:ℝ):ℂ)))*(z:ℂ)+1/((Real.sqrt (2:ℝ):ℂ))=
      (1-(z:ℂ))/((Real.sqrt (2:ℝ):ℂ)) by ring,
    show 3/((Real.sqrt (2:ℝ):ℂ))*(z:ℂ)+ -(1/((Real.sqrt (2:ℝ):ℂ)))=
      (3*(z:ℂ)-1)/((Real.sqrt (2:ℝ):ℂ)) by ring,
    div_div_div_cancel_right₀ hs]

theorem torusExampleFSL_center_image : torusExampleFSL • UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 2 1 (by norm_num) := by
  apply UpperHalfPlane.ext
  rw [torusExampleFSL_coe]
  norm_num [UpperHalfPlane.I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,Complex.ext_iff,Complex.normSq]

theorem torusExampleGSL_center_image : torusExampleGSL • UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 (by norm_num) := by
  apply UpperHalfPlane.ext
  rw [torusExampleGSL_coe]
  norm_num [UpperHalfPlane.I,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,Complex.ext_iff,Complex.normSq]


/-- The actual signed Euclidean circle expression for ideal endpoints on the real axis. -/
def torusCircleQ (a b : ℝ) (z : ℍ) : ℝ :=
  Complex.normSq (z:ℂ)-(a+b)*z.re+a*b

def torusRealF (a : ℝ) : ℝ := (3*a+1)/(a+1)

theorem torusExampleFSL_re (z : ℍ) :
    (torusExampleFSL • z).re=(3*Complex.normSq (z:ℂ)+4*z.re+1)/
      Complex.normSq ((z:ℂ)+1) := by
  change (((torusExampleFSL • z:ℍ):ℂ)).re=_
  rw [torusExampleFSL_coe,Complex.div_re]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem torusExampleFSL_normSq (z : ℍ) :
    Complex.normSq ((torusExampleFSL • z:ℍ):ℂ)=
      (9*Complex.normSq (z:ℂ)+6*z.re+1)/Complex.normSq ((z:ℂ)+1) := by
  rw [torusExampleFSL_coe,Complex.normSq_div]
  congr 1
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  ring

theorem torusExampleFSL_circle_transport (a b : ℝ) (ha : a≠-1) (hb : b≠-1) (z : ℍ) :
    torusCircleQ (torusRealF a) (torusRealF b) (torusExampleFSL • z)*
      ((a+1)*(b+1)*Complex.normSq ((z:ℂ)+1))=4*torusCircleQ a b z := by
  have ha' : a+1≠0:=by intro h;apply ha;linarith
  have hb' : b+1≠0:=by intro h;apply hb;linarith
  have hd : Complex.normSq ((z:ℂ)+1)≠0 := by
    intro he
    have hh:=congrArg Complex.im (Complex.normSq_eq_zero.mp he)
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im,UpperHalfPlane.coe_im] at hh
    exact z.im_ne_zero hh
  simp only [torusCircleQ,torusRealF,torusExampleFSL_re,torusExampleFSL_normSq]
  field_simp
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
    add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

local instance torusEvaluationAction {X : Type*} [MetricSpace X] : MulAction (X≃ᵢX) X where
  smul g x:=g x
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

/-- Powers of the actual side transformation remain in its attracting side region. -/
theorem torus_positive_power_region {X : Type*} [MetricSpace X]
    (f : X≃ᵢX) (U P Q : Set X) (hUQ : U⊆Q) (hPQ : P⊆Q)
    (hf : MapsTo f Q P) (n : ℕ) : MapsTo (fun x=>((f^(n+1)):X≃ᵢX) x) U P := by
  intro x hx
  induction n with
  | zero => simpa only [Nat.zero_add,pow_one] using hf (hUQ hx)
  | succ n ih =>
    rw [show n+1+1=1+(n+1) by omega,pow_add,pow_one]
    exact hf (hPQ ih)

/-- Real cyclic-side dynamics, including both signed powers, proves packing. -/
theorem torus_cyclic_sector_wandering {X : Type*} [MetricSpace X]
    (f : X≃ᵢX) (U P Q R S : Set X)
    (hUQ : U⊆Q) (hPQ : P⊆Q) (hf : MapsTo f Q P)
    (hUS : U⊆S) (hRS : R⊆S) (hfi : MapsTo (f⁻¹:X≃ᵢX) S R)
    (hPU : Disjoint P U) (hRU : Disjoint R U)
    (g : X≃ᵢX) (hg : g∈Subgroup.zpowers f) (hne : g≠1) : Disjoint (g • U) U := by
  obtain ⟨k,rfl⟩:=Subgroup.mem_zpowers_iff.mp hg
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hy
  cases k with
  | ofNat n =>
    cases n with
    | zero => exact hne (zpow_zero f)
    | succ n =>
      have hm:=torus_positive_power_region f U P Q hUQ hPQ hf n hx
      apply disjoint_left.mp hPU hm
      change (f^((n+1:ℕ):ℤ)) x∈U at hy
      simpa only [zpow_natCast] using hy
  | negSucc n =>
    have hm:=torus_positive_power_region f⁻¹ U R S hUS hRS hfi n hx
    apply disjoint_left.mp hRU hm
    change (f^Int.negSucc n) x∈U at hy
    simpa only [zpow_negSucc,inv_pow] using hy

/-- The circle expression before the genuine F-minus side controls its image
relative to the F-plus vertical side. -/
theorem torusExampleFSL_side_identity (z : ℍ) :
    ((torusExampleFSL • z).re-1)*Complex.normSq ((z:ℂ)+1)=
      2*torusCircleQ (-1) 0 z := by
  have hd : Complex.normSq ((z:ℂ)+1)≠0 := by
    intro he
    have hh:=congrArg Complex.im (Complex.normSq_eq_zero.mp he)
    simp only [Complex.add_im,Complex.one_im,add_zero,Complex.zero_im,UpperHalfPlane.coe_im] at hh
    exact z.im_ne_zero hh
  rw [torusExampleFSL_re]
  field_simp
  simp [torusCircleQ,Complex.normSq_apply]
  ring

/-- The analogous G-side formula retains the actual opposite pairing. -/
theorem torusExampleGSL_side_identity (z : ℍ) :
    ((torusExampleGSL • z).re+1)*Complex.normSq (1-(z:ℂ))=
      -2*torusCircleQ 0 1 z := by
  have hd : Complex.normSq (1-(z:ℂ))≠0 := by
    intro he
    have hh:=congrArg Complex.im (Complex.normSq_eq_zero.mp he)
    simp only [Complex.sub_im,Complex.one_im,zero_sub,Complex.zero_im,UpperHalfPlane.coe_im,neg_eq_zero] at hh
    exact z.im_ne_zero hh
  change ((((torusExampleGSL • z:ℍ):ℂ)).re+1)*_=_
  rw [torusExampleGSL_coe,Complex.div_re]
  simp [torusCircleQ,Complex.normSq_apply,Complex.mul_re,Complex.mul_im]
  field_simp
  ring

/-- The two actual factor strips bounded by the displayed geodesics. -/
def torusFSector : Set ℍ := {z|0<torusCircleQ (-1) 0 z ∧ z.re<1}

def torusGSector : Set ℍ := {z|0<torusCircleQ 0 1 z ∧ -1<z.re}

def torusInitialQuad : Set ℍ := torusFSector∩torusGSector

theorem torus_shift_normSq_pos (a : ℝ) (z : ℍ) :
    0<Complex.normSq ((z:ℂ)+(a:ℂ)) := by
  apply Complex.normSq_pos.mpr
  intro he
  have hi:=congrArg Complex.im he
  simp only [Complex.add_im,Complex.ofReal_im,add_zero,Complex.zero_im,UpperHalfPlane.coe_im] at hi
  exact z.im_ne_zero hi

theorem torusF_mapsTo_plus : MapsTo (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)
    {z : ℍ|0<torusCircleQ (-1) 0 z} {z : ℍ|1<z.re} := by
  intro z hz
  have hi:=torusExampleFSL_side_identity z
  have hd:=torus_shift_normSq_pos 1 z
  have he : 0<((torusExampleFSL • z).re-1)*Complex.normSq ((z:ℂ)+1) := by
    rw [hi]
    exact mul_pos (by norm_num) hz
  have hp:=(mul_pos_iff_of_pos_right hd).mp he
  change 1<(torusExampleFSL • z).re
  linarith

theorem torusF_inverse_mapsTo_minus : MapsTo ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
  torusExampleFSL)⁻¹:ℍ≃ᵢℍ)
    {z : ℍ|z.re<1} {z : ℍ|torusCircleQ (-1) 0 z<0} := by
  intro z hz
  let y:ℍ:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)⁻¹ z
  have hf : torusExampleFSL • y=z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL).apply_inv_self z
  have hi:=torusExampleFSL_side_identity y
  rw [hf] at hi
  have hd:=torus_shift_normSq_pos 1 y
  norm_num only [Complex.ofReal_one] at hd
  have he:=mul_neg_of_neg_of_pos (sub_neg.mpr hz) hd
  change torusCircleQ (-1) 0 y<0
  rw [hi] at he
  linarith

theorem torusG_mapsTo_plus : MapsTo (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL)
    {z : ℍ|0<torusCircleQ 0 1 z} {z : ℍ|z.re < -1} := by
  intro z hz
  change 0<torusCircleQ 0 1 z at hz
  have hi:=torusExampleGSL_side_identity z
  have hd : 0<Complex.normSq (1-(z:ℂ)) := by
    have hh:=torus_shift_normSq_pos (-1) z
    rw [show 1-(z:ℂ)= -((z:ℂ)+((-1:ℝ):ℂ)) by push_cast;ring,Complex.normSq_neg]
    exact hh
  have he : ((torusExampleGSL • z).re+1)*Complex.normSq (1-(z:ℂ))<0 := by
    rw [hi]
    nlinarith
  have hp : (torusExampleGSL • z).re+1<0 := by
    by_contra! hn
    exact (not_lt_of_ge (mul_nonneg hn hd.le)) he
  change (torusExampleGSL • z).re < -1
  linarith

theorem torusG_inverse_mapsTo_minus : MapsTo ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
  torusExampleGSL)⁻¹:ℍ≃ᵢℍ)
    {z : ℍ|-1<z.re} {z : ℍ|torusCircleQ 0 1 z<0} := by
  intro z hz
  change -1<z.re at hz
  let y:ℍ:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL)⁻¹ z
  have hf : torusExampleGSL • y=z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL).apply_inv_self z
  have hi:=torusExampleGSL_side_identity y
  rw [hf] at hi
  have hd : 0<Complex.normSq (1-(y:ℂ)) := by
    have hh:=torus_shift_normSq_pos (-1) y
    rw [show 1-(y:ℂ)= -((y:ℂ)+((-1:ℝ):ℂ)) by push_cast;ring,Complex.normSq_neg]
    exact hh
  have he:=mul_pos (by linarith : 0<z.re+1) hd
  change torusCircleQ 0 1 y<0
  rw [hi] at he
  linarith

theorem torusFSector_wandering (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)) (hne :
      g≠1) :
    Disjoint (g • torusFSector) torusFSector := by
  apply torus_cyclic_sector_wandering (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL) torusFSector
    {z : ℍ|1<z.re} {z : ℍ|0<torusCircleQ (-1) 0 z}
    {z : ℍ|torusCircleQ (-1) 0 z<0} {z : ℍ|z.re<1}
    (fun _ hz=>hz.1) _ torusF_mapsTo_plus (fun _ hz=>hz.2) _
    torusF_inverse_mapsTo_minus _ _ g hg hne
  · intro z hz
    change 1<z.re at hz
    change 0<torusCircleQ (-1) 0 z
    dsimp [torusCircleQ]
    nlinarith [Complex.normSq_nonneg (z:ℂ)]
  · intro z hz
    change z.re<1
    dsimp [torusCircleQ] at hz
    nlinarith [Complex.normSq_nonneg (z:ℂ)]
  · apply disjoint_left.mpr
    intro z hp hz
    exact (not_lt_of_ge hp.le) hz.2
  · apply disjoint_left.mpr
    intro z hp hz
    exact (not_lt_of_ge hp.le) hz.1

theorem torusGSector_wandering (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL)) (hne :
      g≠1) :
    Disjoint (g • torusGSector) torusGSector := by
  apply torus_cyclic_sector_wandering (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL) torusGSector
    {z : ℍ|z.re < -1} {z : ℍ|0<torusCircleQ 0 1 z}
    {z : ℍ|torusCircleQ 0 1 z<0} {z : ℍ|-1<z.re}
    (fun _ hz=>hz.1) _ torusG_mapsTo_plus (fun _ hz=>hz.2) _
    torusG_inverse_mapsTo_minus _ _ g hg hne
  · intro z hz
    change z.re < -1 at hz
    change 0<torusCircleQ 0 1 z
    dsimp [torusCircleQ]
    nlinarith [Complex.normSq_nonneg (z:ℂ)]
  · intro z hz
    change -1<z.re
    dsimp [torusCircleQ] at hz
    nlinarith [Complex.normSq_nonneg (z:ℂ)]
  · apply disjoint_left.mpr
    intro z hp hz
    exact (not_lt_of_ge hp.le) hz.2
  · apply disjoint_left.mpr
    intro z hp hz
    exact (not_lt_of_ge hp.le) hz.1

theorem torus_factor_sectors_cover : torusFSector∪torusGSector=univ := by
  apply eq_univ_of_forall
  intro z
  change (0<torusCircleQ (-1) 0 z ∧ z.re<1) ∨
    (0<torusCircleQ 0 1 z ∧ -1<z.re)
  have hy : 0<z.im^2:=sq_pos_of_pos z.im_pos
  dsimp [torusCircleQ]
  simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  by_cases hp : 1≤z.re
  · right
    have hm:=mul_nonneg (sub_nonneg.mpr hp) (by linarith : 0≤z.re)
    constructor <;> nlinarith
  · have hx : z.re<1:=not_le.mp hp
    by_cases hm : z.re≤-1
    · left
      have hh:=mul_nonneg_of_nonpos_of_nonpos (by linarith : z.re+1≤0) (by linarith : z.re≤0)
      exact ⟨by nlinarith,hx⟩
    · have hx' : -1<z.re:=not_le.mp hm
      by_cases hq : 0<z.re*z.re+z.im*z.im+z.re
      · exact Or.inl ⟨by nlinarith,hx⟩
      · right
        constructor <;> nlinarith [not_lt.mp hq,sq_nonneg z.re]

/-- The actual native group generated by precisely the two displayed side maps. -/
def torusNativeGroup : Subgroup (ℍ≃ᵢℍ) := Subgroup.closure
  ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      torusExampleFSL,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL}:Set (ℍ≃ᵢℍ))

theorem torusNativeGroup_le_cyclic_sup : torusNativeGroup≤
    Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL) := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl|rfl)
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL))
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL))

theorem torusNativeGroup_le_conformal : torusNativeGroup≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl|rfl)
  · exact ⟨torusExampleFSL,rfl⟩
  · exact ⟨torusExampleGSL,rfl⟩

theorem torusInitialQuad_wandering (g : ℍ≃ᵢℍ) (hg : g∈torusNativeGroup) (hne : g≠1) :
    Disjoint (g • torusInitialQuad) torusInitialQuad :=
  two_packing_domains_wandering
    (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)) (Subgroup.zpowers
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL))
    torusFSector torusGSector torusFSector_wandering torusGSector_wandering
    torus_factor_sectors_cover g (torusNativeGroup_le_cyclic_sup hg) hne

theorem torusCircleQ_continuous (a b : ℝ) : Continuous (torusCircleQ a b) := by
  unfold torusCircleQ
  fun_prop

theorem torusFSector_isOpen : IsOpen torusFSector :=
  (isOpen_lt continuous_const (torusCircleQ_continuous (-1) 0)).inter
    (isOpen_lt UpperHalfPlane.continuous_re continuous_const)

theorem torusGSector_isOpen : IsOpen torusGSector :=
  (isOpen_lt continuous_const (torusCircleQ_continuous 0 1)).inter
    (isOpen_lt continuous_const UpperHalfPlane.continuous_re)

theorem torusInitialQuad_isOpen : IsOpen torusInitialQuad :=
  torusFSector_isOpen.inter torusGSector_isOpen

theorem torusInitialQuad_center_mem : UpperHalfPlane.I∈torusInitialQuad := by
  have hr : UpperHalfPlane.I.re=0:=rfl
  have hn : Complex.normSq (UpperHalfPlane.I:ℂ)=1:=by norm_num [UpperHalfPlane.I,Complex.normSq_apply]
  change (0<torusCircleQ (-1) 0 UpperHalfPlane.I ∧ UpperHalfPlane.I.re<1) ∧
    (0<torusCircleQ 0 1 UpperHalfPlane.I ∧ -1<UpperHalfPlane.I.re)
  norm_num [torusCircleQ,hr,hn]

/-- Genuine open packing proves discreteness in the existing boundary-uniform topology. -/
theorem torusNativeGroup_discrete : DiscreteTopology torusNativeGroup := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open torusInitialQuad torusInitialQuad_isOpen
    ⟨UpperHalfPlane.I,torusInitialQuad_center_mem⟩
  intro g hg
  apply torusInitialQuad_wandering g.val g.property
  intro he
  exact hg (Subtype.ext he)

/-- The actual common half-plane action is properly discontinuous. -/
theorem torusNativeGroup_discontinuous : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous torusNativeGroup ℍ := by
  let : DiscreteTopology torusNativeGroup:=torusNativeGroup_discrete
  exact nativeConformalSubgroup_discontinuous _ torusNativeGroup_le_conformal

/-- The whole native generated group maps into exactly the original generated Mobius group. -/
theorem torusNativeGroup_original_image :
    (nativeConformalSubgroupMobiusHom torusNativeGroup torusNativeGroup_le_conformal).range=
      torusExampleGroup := by
  let M:=nativeConformalSubgroupMobiusHom torusNativeGroup torusNativeGroup_le_conformal
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL∈torusNativeGroup:=Subgroup.subset_closure (by left;rfl)
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL∈torusNativeGroup:=Subgroup.subset_closure (by right;rfl)
  have hMF : M ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL,hF⟩=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius torusExampleFSL :=
    nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  have hMG : M ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL,hG⟩=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius torusExampleGSL :=
    nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  apply le_antisymm
  · rintro f ⟨g,rfl⟩
    have hi (x : ℍ≃ᵢℍ) (hx : x∈torusNativeGroup) : M ⟨x,hx⟩∈torusExampleGroup := by
      change x∈Subgroup.closure _ at hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl|rfl
        · rw [hMF]
          exact Subgroup.subset_closure (by left;rfl)
        · rw [hMG]
          exact Subgroup.subset_closure (by right;rfl)
      | one =>
        change M (1:torusNativeGroup)∈torusExampleGroup
        rw [map_one]
        exact torusExampleGroup.one_mem
      | mul a b ha hb iha ihb =>
        change M (⟨a,ha⟩*⟨b,hb⟩)∈torusExampleGroup
        rw [map_mul]
        exact torusExampleGroup.mul_mem iha ihb
      | inv a ha iha =>
        change M (⟨a,ha⟩:torusNativeGroup)⁻¹∈torusExampleGroup
        rw [map_inv]
        exact torusExampleGroup.inv_mem iha
    exact hi g.val g.property
  · apply (Subgroup.closure_le _).mpr
    rintro f (rfl|rfl)
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL,hF⟩,hMF⟩
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL,hG⟩,hMG⟩

/-- The original finite generated matrix group has its actual invariant disc and actual discreteness. -/
theorem torusExampleData : HalfPlaneFuchsianGroup torusExampleGroup := by
  rw [←torusNativeGroup_original_image]
  let : DiscreteTopology torusNativeGroup:=torusNativeGroup_discrete
  exact nativeConformalSubgroup_halfPlaneData _ torusNativeGroup_le_conformal


def torusKleinCutRegion {ι : Type*} (n : ι→ℂ) (t : ι→ℝ) : Set ℍ :=
  {z|∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<t i}

def torusKleinClosedRegion {ι : Type*} (n : ι→ℂ) (t : ι→ℝ) : Set ℍ :=
  {z|∀i,inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t i}

theorem torusKleinCutRegion_image {ι : Type*} (n : ι→ℂ) (t : ι→ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' torusKleinCutRegion n t=
      {u : ℂ|∀i,inner ℝ (n i) u<t i}∩Metric.ball 0 1 := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate ⁻¹' {u : ℂ|∀i,inner ℝ (n i) u<t i}) = _
  rw [image_preimage_eq_inter_range,_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate]

theorem torusKleinCutRegion_isOpen {ι : Type*} [Finite ι] (n : ι→ℂ) (t : ι→ℝ) :
    IsOpen (torusKleinCutRegion n t) := by
  have he : torusKleinCutRegion n t=⋂i,{z : ℍ|inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<t i}:=by
    ext z;simp [torusKleinCutRegion]
  rw [he]
  exact isOpen_iInter_of_finite (fun i=>isOpen_lt
      ((innerSL ℝ (n i)).continuous.comp
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous)
      continuous_const)

theorem torusKleinCutRegion_hConvex {ι : Type*} (n : ι→ℂ) (t : ι→ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (torusKleinCutRegion n t) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mpr
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mpr
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' torusKleinCutRegion n t)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' torusKleinCutRegion n t := by rw [image_image];rfl
  rw [he,torusKleinCutRegion_image]
  have hf : {u : ℂ|∀i,inner ℝ (n i) u<t i}=⋂i,{u : ℂ|inner ℝ (n i) u<t i}:=by ext u;simp
  rw [hf]
  exact (convex_iInter (fun i=>convex_halfSpace_lt (innerSL ℝ (n i)).toLinearMap.isLinear (t i))).inter
    (convex_ball (0:ℂ) 1)

theorem torusKleinCutRegion_closure {ι : Type*} (n : ι→ℂ) (t : ι→ℝ)
    (w : ℍ) (hw : w∈torusKleinCutRegion n t) :
    closure (torusKleinCutRegion n t)=torusKleinClosedRegion n t := by
  have hc : IsClosed (torusKleinClosedRegion n t) := by
    have he : torusKleinClosedRegion n t=⋂i,{z : ℍ|inner ℝ (n i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤t i}:=by
      ext z;simp [torusKleinClosedRegion]
    rw [he]
    exact isClosed_iInter (fun i=>isClosed_le
      ((innerSL ℝ (n i)).continuous.comp
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous)
      continuous_const)
  apply subset_antisymm
  · exact closure_minimal (fun _ hz i=>(hz i).le) hc
  · intro z hz
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.isEmbedding.closure_eq_preimage_closure_image,
      torusKleinCutRegion_image]
    exact affine_cuts_ball_weak_mem_closure n t (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ mem_range_self w)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_halfPlaneKleinCoordinate ▸ mem_range_self z) hw hz

theorem torus_hConvex_regular {S : Set ℍ} (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) (ho :
  IsOpen S) (hn : S.Nonempty) :
    interior (closure S)=S := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective.image_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_interior,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.image_closure]
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex _).mp
    hS).interior_closure_eq_of_isOpen
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap _ ho) (hn.image
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc)

def torusInitialNormals : Fin 4→ℂ := ![⟨-1/2,1/2⟩,⟨1/2,-1/2⟩,⟨-1/2,-1/2⟩,⟨1/2,1/2⟩]
def torusInitialSlacks (z : ℍ) : Fin 4→ℝ :=
  ![torusCircleQ (-1) 0 z,1-z.re,torusCircleQ 0 1 z,1+z.re]

theorem torusInitial_klein_slack (z : ℍ) (i : Fin 4) :
    (1/2-inner ℝ (torusInitialNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z))*
      (Complex.normSq (z:ℂ)+1)=torusInitialSlacks z i := by
  have hd : z.re^2+z.im^2+1≠0:=ne_of_gt (by positivity)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit]
  fin_cases i <;> norm_num [torusInitialNormals,torusInitialSlacks,torusCircleQ,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im]
  all_goals field_simp [hd];ring

theorem torusInitial_slack_pos_iff (z : ℍ) (i : Fin 4) :
    0<torusInitialSlacks z i ↔ inner ℝ (torusInitialNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<1/2 := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←torusInitial_klein_slack,mul_pos_iff_of_pos_right hd,sub_pos]

theorem torusInitial_slack_nonneg_iff (z : ℍ) (i : Fin 4) :
    0≤torusInitialSlacks z i ↔ inner ℝ (torusInitialNormals i) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤1/2 := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←torusInitial_klein_slack,mul_nonneg_iff_of_pos_right hd,sub_nonneg]

theorem torusInitialQuad_klein :
    torusInitialQuad=torusKleinCutRegion torusInitialNormals (fun _=>1/2) := by
  ext z
  constructor
  · intro hz i
    apply (torusInitial_slack_pos_iff z i).mp
    rcases hz with ⟨⟨h₁,h₂⟩,⟨h₃,h₄⟩⟩
    fin_cases i <;> norm_num [torusInitialSlacks] <;> linarith
  · intro hz
    have h0:=(torusInitial_slack_pos_iff z 0).mpr (hz 0)
    have h1:=(torusInitial_slack_pos_iff z 1).mpr (hz 1)
    have h2:=(torusInitial_slack_pos_iff z 2).mpr (hz 2)
    have h3:=(torusInitial_slack_pos_iff z 3).mpr (hz 3)
    norm_num [torusInitialSlacks] at h0 h1 h2 h3
    exact ⟨⟨h0,by linarith⟩,⟨h2,by linarith⟩⟩

def torusInitialClosedQuad : Set ℍ :=
  {z|0≤torusCircleQ (-1) 0 z ∧ z.re≤1 ∧ 0≤torusCircleQ 0 1 z ∧ -1≤z.re}

theorem torusInitialClosedQuad_klein :
    torusInitialClosedQuad=torusKleinClosedRegion torusInitialNormals (fun _=>1/2) := by
  ext z
  constructor
  · intro hz i
    apply (torusInitial_slack_nonneg_iff z i).mp
    rcases hz with ⟨h₁,h₂,h₃,h₄⟩
    fin_cases i <;> norm_num [torusInitialSlacks] <;> linarith
  · intro hz
    have h0:=(torusInitial_slack_nonneg_iff z 0).mpr (hz 0)
    have h1:=(torusInitial_slack_nonneg_iff z 1).mpr (hz 1)
    have h2:=(torusInitial_slack_nonneg_iff z 2).mpr (hz 2)
    have h3:=(torusInitial_slack_nonneg_iff z 3).mpr (hz 3)
    norm_num [torusInitialSlacks] at h0 h1 h2 h3
    exact ⟨h0,by linarith,h2,by linarith⟩

theorem torusInitialQuad_closure : closure torusInitialQuad=torusInitialClosedQuad := by
  rw [torusInitialQuad_klein,torusInitialClosedQuad_klein]
  exact torusKleinCutRegion_closure _ _ UpperHalfPlane.I (torusInitialQuad_klein ▸ torusInitialQuad_center_mem)

theorem torusInitialQuad_hConvex : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex torusInitialQuad := by
  rw [torusInitialQuad_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem torusInitialQuad_isConnected : IsConnected torusInitialQuad :=
  ⟨⟨UpperHalfPlane.I,torusInitialQuad_center_mem⟩,torusInitialQuad_hConvex.isPreconnected⟩

theorem torusInitialQuad_regular : interior (closure torusInitialQuad)=torusInitialQuad :=
  torus_hConvex_regular torusInitialQuad_hConvex torusInitialQuad_isOpen torusInitialQuad_isConnected.nonempty

theorem torusExampleFSL_inverse_center_image :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)⁻¹ UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2/5) (1/5) (by norm_num) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL).injective
  rw [IsometryEquiv.apply_inv_self]
  symm
  change torusExampleFSL • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2/5) (1/5) _=UpperHalfPlane.I
  apply UpperHalfPlane.ext
  rw [torusExampleFSL_coe]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.I,Complex.ext_iff,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem torusExampleGSL_inverse_center_image :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL)⁻¹ UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (2/5) (1/5) (by norm_num) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL).injective
  rw [IsometryEquiv.apply_inv_self]
  symm
  change torusExampleGSL • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (2/5) (1/5) _=UpperHalfPlane.I
  apply UpperHalfPlane.ext
  rw [torusExampleGSL_coe]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,UpperHalfPlane.I,Complex.ext_iff,Complex.div_re,Complex.div_im,Complex.normSq_apply]

theorem torus_metricProbe_dist_le_iff (a b c d : ℝ) (hb : 0<b) (hd : 0<d) (z : ℍ) :
    dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe a b
      hb)≤dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe c d hd) ↔
      0≤b*(Complex.normSq (z:ℂ)-2*c*z.re+c^2+d^2)-
        d*(Complex.normSq (z:ℂ)-2*a*z.re+a^2+b^2) := by
  rw [←not_lt,metricProbe_dist_lt_iff c d a b hd hb]
  constructor
  · intro h
    by_contra! he
    apply h
    linarith
  · intro h hn
    linarith

/-- The four actual named orbit inequalities force every whole-group nearest
representative into the literal closed ideal quadrilateral. -/
theorem torusNativeClosedDirichlet_subset :
    nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I⊆torusInitialClosedQuad := by
  intro z hz
  have hF : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL∈torusNativeGroup:=Subgroup.subset_closure (by left;rfl)
  have hG : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL∈torusNativeGroup:=Subgroup.subset_closure (by right;rfl)
  have h₁:=hz ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL,hF⟩
  have h₂:=hz ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL)⁻¹,torusNativeGroup.inv_mem hF⟩
  have h₃:=hz ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL,hG⟩
  have h₄:=hz ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL)⁻¹,torusNativeGroup.inv_mem hG⟩
  change dist z UpperHalfPlane.I≤dist z (torusExampleFSL • UpperHalfPlane.I) at h₁
  change dist z UpperHalfPlane.I≤dist z ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL)⁻¹ UpperHalfPlane.I) at h₂
  change dist z UpperHalfPlane.I≤dist z (torusExampleGSL • UpperHalfPlane.I) at h₃
  change dist z UpperHalfPlane.I≤dist z ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleGSL)⁻¹ UpperHalfPlane.I) at h₄
  rw [torusExampleFSL_center_image] at h₁
  rw [torusExampleFSL_inverse_center_image] at h₂
  rw [torusExampleGSL_center_image] at h₃
  rw [torusExampleGSL_inverse_center_image] at h₄
  have hI : UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num):=rfl
  rw [hI,torus_metricProbe_dist_le_iff] at h₁ h₂ h₃ h₄
  norm_num at h₁ h₂ h₃ h₄
  change 0≤torusCircleQ (-1) 0 z ∧ z.re≤1 ∧ 0≤torusCircleQ 0 1 z ∧ -1≤z.re
  dsimp [torusCircleQ]
  constructor
  · nlinarith
  · constructor
    · nlinarith
    · constructor <;> nlinarith

/-- Actual compact-orbit minimization, not a Poincare-data assumption, covers
the whole upper half-plane by the true closed quadrilateral translates. -/
theorem torusInitialQuad_closure_meetsEveryOrbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit torusNativeGroup ℍ (closure torusInitialQuad) := by
  intro z
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit torusNativeGroup
    torusNativeGroup_discontinuous UpperHalfPlane.I z
  refine ⟨g,?_⟩
  rw [torusInitialQuad_closure]
  exact torusNativeClosedDirichlet_subset hg

def torusInitialFMinusLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.circle (-1/2) (1/2) (by norm_num)
def torusInitialGMinusLine : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine:=.circle (1/2) (1/2) (by norm_num)

theorem torusInitialFMinusLine_iff (z : ℍ) :
    z∈torusInitialFMinusLine.carrier ↔ torusCircleQ (-1) 0 z=0 := by
  rw [torusInitialFMinusLine,circle_carrier_iff_normSq]
  simp [torusCircleQ,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  constructor <;> intro h <;> nlinarith

theorem torusInitialGMinusLine_iff (z : ℍ) :
    z∈torusInitialGMinusLine.carrier ↔ torusCircleQ 0 1 z=0 := by
  rw [torusInitialGMinusLine,circle_carrier_iff_normSq]
  simp [torusCircleQ,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]
  constructor <;> intro h <;> nlinarith

theorem torusInitialQuad_frontier_subset : frontier torusInitialQuad⊆
    torusInitialFMinusLine.carrier∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 1).carrier∪
      torusInitialGMinusLine.carrier∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-1)).carrier := by
  intro z hz
  rw [torusInitialQuad_isOpen.frontier_eq,torusInitialQuad_closure] at hz
  obtain ⟨hcl,hnot⟩:=hz
  change 0≤torusCircleQ (-1) 0 z ∧ z.re≤1 ∧ 0≤torusCircleQ 0 1 z ∧ -1≤z.re at hcl
  by_cases hF : 0<torusCircleQ (-1) 0 z
  · by_cases hR : z.re<1
    · by_cases hG : 0<torusCircleQ 0 1 z
      · by_cases hL : -1<z.re
        · exact False.elim (hnot ⟨⟨hF,hR⟩,⟨hG,hL⟩⟩)
        · right
          change z.re = -1
          linarith
      · left;right
        exact (torusInitialGMinusLine_iff z).mpr (by linarith [hcl.2.2.1])
    · left;left;right
      change z.re=1
      linarith [hcl.2.1]
  · left;left;left
    exact (torusInitialFMinusLine_iff z).mpr (by linarith [hcl.1])

theorem torusInitialQuad_frontier_null : MeasureTheory.volume (frontier torusInitialQuad)=0 :=
  MeasureTheory.measure_mono_null torusInitialQuad_frontier_subset
    (MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null
        (MeasureTheory.measure_union_null torusInitialFMinusLine.volume_zero
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
            1).volume_zero) torusInitialGMinusLine.volume_zero)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (-1)).volume_zero)

/-- The literal regular ideal quadrilateral is a true fundamental domain for the
whole actual generated group; its cover and packing have both been proved. -/
theorem torusInitialQuad_fundamental :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume torusInitialQuad := by
  refine ⟨torusInitialQuad_isOpen,torusInitialQuad_isConnected,?_,torusInitialQuad_frontier_null⟩
  apply exists_fundamentalSet_between _ _ subset_closure torusInitialQuad_closure_meetsEveryOrbit
  intro x hx y hy hxy
  obtain ⟨g,hg⟩:=(Quotient.exact hxy : MulAction.orbitRel torusNativeGroup ℍ x y)
  change g.val y=x at hg
  by_cases he : g.val=1
  · rw [he] at hg
    exact hg.symm
  · exact False.elim (disjoint_left.mp (torusInitialQuad_wandering g.val g.property he) ⟨y,hy,hg⟩ hx)


/-- The actual open ideal triangle with three real, increasingly ordered endpoints. -/
def torusIdealTriangle (a b c : ℝ) : Set ℍ :=
  {z|0<torusCircleQ a b z ∧ 0<torusCircleQ b c z ∧ torusCircleQ a c z<0}

/-- The actual four open hyperbolic half-planes bounded by the four ideal chords. -/
def torusIdealQuad (a b c d : ℝ) : Set ℍ :=
  {z|0<torusCircleQ a b z ∧ 0<torusCircleQ b c z ∧
    0<torusCircleQ c d z ∧ torusCircleQ a d z<0}

theorem torusCircleQ_eq (a b : ℝ) (z : ℍ) :
    torusCircleQ a b z=(z.re-a)*(z.re-b)+z.im^2 := by
  simp only [torusCircleQ,Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem torusCircleQ_inside_re {a b : ℝ} (hab : a<b) (z : ℍ)
    (hz : torusCircleQ a b z<0) : a<z.re ∧ z.re<b := by
  rw [torusCircleQ_eq] at hz
  constructor
  · by_contra! hn
    have hm:=mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hn)
      (sub_nonpos.mpr (hn.trans hab.le))
    nlinarith [sq_nonneg z.im]
  · by_contra! hn
    have hm:=mul_nonneg (sub_nonneg.mpr (hab.le.trans hn)) (sub_nonneg.mpr hn)
    nlinarith [sq_nonneg z.im]

theorem torusIdealTriangle_subset_quad_first {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle a b c⊆torusIdealQuad a b c d := by
  rintro z ⟨h₁,h₂,h₃⟩
  obtain ⟨ha,hc⟩:=torusCircleQ_inside_re (hab.trans hbc) z h₃
  have hp:=mul_pos (sub_pos.mpr (hbc.trans hcd)) (sub_pos.mpr hc)
  have hq:=mul_pos (sub_pos.mpr hcd) (sub_pos.mpr ha)
  refine ⟨h₁,h₂,?_,?_⟩ <;> dsimp [torusCircleQ] at * <;> nlinarith

theorem torusIdealTriangle_subset_quad_second {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle a c d⊆torusIdealQuad a b c d := by
  rintro z ⟨h₁,h₂,h₃⟩
  obtain ⟨ha,_hd⟩:=torusCircleQ_inside_re (hab.trans (hbc.trans hcd)) z h₃
  have hp:=mul_pos (sub_pos.mpr hbc) (sub_pos.mpr ha)
  refine ⟨?_,?_,h₂,h₃⟩
  · dsimp [torusCircleQ] at *
    nlinarith
  · by_cases hc : z.re≤c
    · have hq:=mul_nonneg (sub_nonneg.mpr hab.le) (sub_nonneg.mpr hc)
      dsimp [torusCircleQ] at *
      nlinarith
    · have hq:=mul_pos (sub_pos.mpr (hbc.trans hcd)) (sub_pos.mpr (not_le.mp hc))
      dsimp [torusCircleQ] at *
      nlinarith

/-- A genuine diagonal cuts the actual quad into these two actual open triangles;
the only points omitted are points of that actual diagonal. -/
theorem torusIdealQuad_split_ac {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle a b c∪torusIdealTriangle a c d=
      torusIdealQuad a b c d∩{z|torusCircleQ a c z≠0} := by
  ext z
  constructor
  · rintro (hz|hz)
    · exact ⟨torusIdealTriangle_subset_quad_first hab hbc hcd hz,ne_of_lt hz.2.2⟩
    · exact ⟨torusIdealTriangle_subset_quad_second hab hbc hcd hz,ne_of_gt hz.1⟩
  · rintro ⟨h,hne⟩
    rcases lt_or_gt_of_ne hne with hdiag|hdiag
    · exact Or.inl ⟨h.1,h.2.1,hdiag⟩
    · exact Or.inr ⟨hdiag,h.2.2.1,h.2.2.2⟩

theorem torusIdealTriangle_subset_quad_third {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle a b d⊆torusIdealQuad a b c d := by
  rintro z ⟨h₁,h₂,h₃⟩
  obtain ⟨_ha,hd⟩:=torusCircleQ_inside_re (hab.trans (hbc.trans hcd)) z h₃
  have hp:=mul_pos (sub_pos.mpr hbc) (sub_pos.mpr hd)
  refine ⟨h₁,?_,?_,h₃⟩
  · by_cases hb : b≤z.re
    · have hq:=mul_nonneg (sub_nonneg.mpr hcd.le) (sub_nonneg.mpr hb)
      dsimp [torusCircleQ] at *
      nlinarith
    · have hq:=mul_pos (sub_pos.mpr (hab.trans hbc)) (sub_pos.mpr (not_le.mp hb))
      dsimp [torusCircleQ] at *
      nlinarith
  · dsimp [torusCircleQ] at *
    nlinarith

theorem torusIdealTriangle_subset_quad_fourth {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle b c d⊆torusIdealQuad a b c d := by
  rintro z ⟨h₁,h₂,h₃⟩
  obtain ⟨hb,hd⟩:=torusCircleQ_inside_re (hbc.trans hcd) z h₃
  have hp:=mul_pos (sub_pos.mpr (hab.trans (hbc.trans hcd))) (sub_pos.mpr hb)
  have hq:=mul_pos (sub_pos.mpr hab) (sub_pos.mpr hd)
  refine ⟨?_,h₁,h₂,?_⟩ <;> dsimp [torusCircleQ] at * <;> nlinarith

theorem torusIdealQuad_split_bd {a b c d : ℝ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) :
    torusIdealTriangle a b d∪torusIdealTriangle b c d=
      torusIdealQuad a b c d∩{z|torusCircleQ b d z≠0} := by
  ext z
  constructor
  · rintro (hz|hz)
    · exact ⟨torusIdealTriangle_subset_quad_third hab hbc hcd hz,ne_of_gt hz.2.1⟩
    · exact ⟨torusIdealTriangle_subset_quad_fourth hab hbc hcd hz,ne_of_lt hz.2.2⟩
  · rintro ⟨h,hne⟩
    rcases lt_or_gt_of_ne hne with hdiag|hdiag
    · exact Or.inr ⟨h.2.1,h.2.2.1,hdiag⟩
    · exact Or.inl ⟨h.1,hdiag,h.2.2.2⟩

def torusCircleNormal (a b : ℝ) : ℂ:=⟨(a*b-1)/2,-(a+b)/2⟩
def torusCircleThreshold (a b : ℝ) : ℝ:=(1+a*b)/2

theorem torusCircleQ_klein (a b : ℝ) (z : ℍ) :
    (torusCircleThreshold a b-inner ℝ (torusCircleNormal a b)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z))*
      (Complex.normSq (z:ℂ)+1)=torusCircleQ a b z := by
  have hd : z.re^2+z.im^2+1≠0:=ne_of_gt (by positivity)
  norm_num [torusCircleNormal,torusCircleThreshold,torusCircleQ,
    _root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,Complex.normSq_apply]
  field_simp [hd]
  ring

theorem torusCircleQ_klein_pos_iff (a b : ℝ) (z : ℍ) :
    0<torusCircleQ a b z ↔ inner ℝ (torusCircleNormal a
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<
      torusCircleThreshold a b := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←torusCircleQ_klein,mul_pos_iff_of_pos_right hd,sub_pos]

theorem torusCircleQ_klein_neg_iff (a b : ℝ) (z : ℍ) :
    torusCircleQ a b z<0 ↔ inner ℝ (-torusCircleNormal a
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<
      -torusCircleThreshold a b := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←torusCircleQ_klein,inner_neg_left]
  constructor
  · intro h
    have hp : torusCircleThreshold a b-inner ℝ (torusCircleNormal a b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<0 := by
      by_contra! hn
      exact (not_lt_of_ge (mul_nonneg hn hd.le)) h
    linarith
  · intro h
    apply mul_neg_of_neg_of_pos _ hd
    linarith

def torusQuadNormals (a b c d : ℝ) : Fin 4→ℂ:=
  ![torusCircleNormal a b,torusCircleNormal b c,torusCircleNormal c d,-torusCircleNormal a d]
def torusQuadThresholds (a b c d : ℝ) : Fin 4→ℝ:=
  ![torusCircleThreshold a b,torusCircleThreshold b c,torusCircleThreshold c d,-torusCircleThreshold a d]

theorem torusIdealQuad_klein (a b c d : ℝ) :
    torusIdealQuad a b c d=torusKleinCutRegion (torusQuadNormals a b c d) (torusQuadThresholds a b c d) := by
  ext z
  constructor
  · intro hz i
    rcases hz with ⟨h₁,h₂,h₃,h₄⟩
    fin_cases i
    · exact (torusCircleQ_klein_pos_iff a b z).mp h₁
    · exact (torusCircleQ_klein_pos_iff b c z).mp h₂
    · exact (torusCircleQ_klein_pos_iff c d z).mp h₃
    · exact (torusCircleQ_klein_neg_iff a d z).mp h₄
  · intro hz
    exact ⟨(torusCircleQ_klein_pos_iff a b z).mpr (hz 0),
      (torusCircleQ_klein_pos_iff b c z).mpr (hz 1),
      (torusCircleQ_klein_pos_iff c d z).mpr (hz 2),
      (torusCircleQ_klein_neg_iff a d z).mpr (hz 3)⟩

theorem torusIdealQuad_isOpen (a b c d : ℝ) : IsOpen (torusIdealQuad a b c d) := by
  rw [torusIdealQuad_klein]
  exact torusKleinCutRegion_isOpen _ _

theorem torusIdealQuad_hConvex (a b c d : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (torusIdealQuad a b c d) := by
  rw [torusIdealQuad_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem torusIdealTriangle_isOpen (a b c : ℝ) : IsOpen (torusIdealTriangle a b c) :=
  (isOpen_lt continuous_const (torusCircleQ_continuous a b)).inter
    ((isOpen_lt continuous_const (torusCircleQ_continuous b c)).inter
      (isOpen_lt (torusCircleQ_continuous a c) continuous_const))

theorem torusCircleQ_zero_carrier (a b : ℝ) (hab : a<b) :
    {z : ℍ|torusCircleQ a b z=0}=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle ((a+b)/2) ((b-a)/2) (by linarith)).carrier := by
  ext z
  rw [circle_carrier_iff_normSq]
  simp only [mem_ofPred_eq,torusCircleQ,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  constructor <;> intro h <;> nlinarith

theorem torusCircleQ_ne_zero_dense (a b : ℝ) (hab : a<b) :
    Dense {z : ℍ|torusCircleQ a b z≠0} := by
  have hE : interior {z : ℍ|torusCircleQ a b z=0}=∅ := by
    rw [torusCircleQ_zero_carrier a b hab]
    have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle ((a+b)/2) ((b-a)/2) (by linarith)).carrier=
        ((↑):ℍ→ℂ) ⁻¹' Metric.sphere (((a+b)/2:ℝ):ℂ) ((b-a)/2) := by
      ext z
      simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier]
    rw [he,←UpperHalfPlane.isOpenEmbedding_coe.isOpenMap.preimage_interior_eq_interior_preimage
      UpperHalfPlane.continuous_coe,interior_sphere',preimage_empty]
  exact (interior_eq_empty_iff_dense_compl).mp hE

theorem torus_open_cut_closure (U : Set ℍ) (hU : IsOpen U) (a b : ℝ) (hab : a<b) :
    closure (U∩{z|torusCircleQ a b z≠0})=closure U := by
  apply subset_antisymm (closure_mono inter_subset_left)
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply mem_closure_iff.mpr
  intro V hV hzV
  obtain ⟨x,hxS,hxV⟩:=(torusCircleQ_ne_zero_dense a b hab).exists_mem_open (hV.inter hU) ⟨z,hzV,hz⟩
  exact ⟨x,hxV.1,hxV.2,hxS⟩

theorem torusRealF_strictMono (a b : ℝ) (ha : -1<a) (hab : a<b) : torusRealF a<torusRealF b := by
  dsimp [torusRealF]
  rw [div_lt_div_iff₀ (by linarith : 0<a+1) (by linarith : 0<b+1)]
  nlinarith

theorem torusExampleFSL_circle_pos_iff (a b : ℝ) (ha : -1<a) (hb : -1<b) (z : ℍ) :
    0<torusCircleQ (torusRealF a) (torusRealF b) (torusExampleFSL • z) ↔
      0<torusCircleQ a b z := by
  have hden : 0<(a+1)*(b+1)*Complex.normSq ((z:ℂ)+1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  calc
    _ ↔ 0<torusCircleQ (torusRealF a) (torusRealF b) (torusExampleFSL • z)*
        ((a+1)*(b+1)*Complex.normSq ((z:ℂ)+1)) := (mul_pos_iff_of_pos_right hden).symm
    _ ↔ 0<4*torusCircleQ a b z := by rw [torusExampleFSL_circle_transport a b (ne_of_gt ha) (ne_of_gt hb)]
    _ ↔ _ := mul_pos_iff_of_pos_left (by norm_num : (0:ℝ)<4)

theorem torusExampleFSL_circle_neg_iff (a b : ℝ) (ha : -1<a) (hb : -1<b) (z : ℍ) :
    torusCircleQ (torusRealF a) (torusRealF b) (torusExampleFSL • z)<0 ↔
      torusCircleQ a b z<0 := by
  have hden : 0<(a+1)*(b+1)*Complex.normSq ((z:ℂ)+1) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  have he:=torusExampleFSL_circle_transport a b (ne_of_gt ha) (ne_of_gt hb) z
  constructor
  · intro h
    have hm:=mul_neg_of_neg_of_pos h hden
    rw [he] at hm
    linarith
  · intro h
    by_contra! hn
    have hm:=mul_nonneg hn hden.le
    rw [he] at hm
    linarith

/-- The exact actual F-image of a real-ended ideal triangle. -/
theorem torusExampleFSL_triangle_image (a b c : ℝ) (ha : -1<a) (hb : -1<b) (hc : -1<c) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) '' torusIdealTriangle a b c=
      torusIdealTriangle (torusRealF a) (torusRealF b) (torusRealF c) := by
  apply subset_antisymm
  · rintro _ ⟨z,⟨h₁,h₂,h₃⟩,rfl⟩
    exact ⟨(torusExampleFSL_circle_pos_iff a b ha hb z).mpr h₁,
      (torusExampleFSL_circle_pos_iff b c hb hc z).mpr h₂,
      (torusExampleFSL_circle_neg_iff a c ha hc z).mpr h₃⟩
  · intro z hz
    obtain ⟨w,he⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL).surjective z
    rw [←he] at hz
    refine ⟨w,?_,he⟩
    exact ⟨(torusExampleFSL_circle_pos_iff a b ha hb w).mp hz.1,
      (torusExampleFSL_circle_pos_iff b c hb hc w).mp hz.2.1,
      (torusExampleFSL_circle_neg_iff a c ha hc w).mp hz.2.2⟩

theorem torusCircleQ_klein_nonneg_iff (a b : ℝ) (z : ℍ) :
    0≤torusCircleQ a b z ↔ inner ℝ (torusCircleNormal a
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
      torusCircleThreshold a b := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←torusCircleQ_klein,mul_nonneg_iff_of_pos_right hd,sub_nonneg]

theorem torusCircleQ_klein_nonpos_iff (a b : ℝ) (z : ℍ) :
    torusCircleQ a b z≤0 ↔ inner ℝ (-torusCircleNormal a
      b) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)≤
      -torusCircleThreshold a b := by
  rw [←not_lt,torusCircleQ_klein_pos_iff,inner_neg_left]
  constructor <;> intro h <;> linarith

def torusClosedQuad (a b c d : ℝ) : Set ℍ :=
  {z|0≤torusCircleQ a b z ∧ 0≤torusCircleQ b c z ∧
    0≤torusCircleQ c d z ∧ torusCircleQ a d z≤0}

theorem torusClosedQuad_klein (a b c d : ℝ) :
    torusClosedQuad a b c d=torusKleinClosedRegion (torusQuadNormals a b c d) (torusQuadThresholds a b c d) := by
  ext z
  constructor
  · intro hz i
    rcases hz with ⟨h₁,h₂,h₃,h₄⟩
    fin_cases i
    · exact (torusCircleQ_klein_nonneg_iff a b z).mp h₁
    · exact (torusCircleQ_klein_nonneg_iff b c z).mp h₂
    · exact (torusCircleQ_klein_nonneg_iff c d z).mp h₃
    · exact (torusCircleQ_klein_nonpos_iff a d z).mp h₄
  · intro hz
    exact ⟨(torusCircleQ_klein_nonneg_iff a b z).mpr (hz 0),
      (torusCircleQ_klein_nonneg_iff b c z).mpr (hz 1),
      (torusCircleQ_klein_nonneg_iff c d z).mpr (hz 2),
      (torusCircleQ_klein_nonpos_iff a d z).mpr (hz 3)⟩

theorem torusIdealQuad_nonempty (a b : ℝ) (ha : 1<a) (hab : a<b) :
    (torusIdealQuad 0 1 a b).Nonempty := by
  have hb : 0<b:=by linarith
  let p:ℍ:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (1/2) (Real.sqrt b/2) (by positivity)
  have hs:=Real.sq_sqrt hb.le
  have hp:=mul_pos (by linarith : 0<a-1/2) (by linarith : 0<b-1/2)
  refine ⟨p,?_,?_,?_,?_⟩ <;>
    norm_num [torusIdealQuad,torusCircleQ,p,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply] <;> nlinarith

theorem torusIdealQuad_closure (a b : ℝ) (ha : 1<a) (hab : a<b) :
    closure (torusIdealQuad 0 1 a b)=torusClosedQuad 0 1 a b := by
  obtain ⟨w,hw⟩:=torusIdealQuad_nonempty a b ha hab
  rw [torusIdealQuad_klein,torusClosedQuad_klein]
  exact torusKleinCutRegion_closure _ _ w ((torusIdealQuad_klein 0 1 a b) ▸ hw)

theorem torusIdealQuad_isConnected (a b : ℝ) (ha : 1<a) (hab : a<b) :
    IsConnected (torusIdealQuad 0 1 a b) :=
  ⟨torusIdealQuad_nonempty a b ha hab,(torusIdealQuad_hConvex 0 1 a b).isPreconnected⟩

theorem torusIdealQuad_regular (a b : ℝ) (ha : 1<a) (hab : a<b) :
    interior (closure (torusIdealQuad 0 1 a b))=torusIdealQuad 0 1 a b :=
  torus_hConvex_regular (torusIdealQuad_hConvex 0 1 a b) (torusIdealQuad_isOpen 0 1 a b)
    (torusIdealQuad_nonempty a b ha hab)

theorem torusCircleQ_zero_null (a b : ℝ) (hab : a<b) :
    MeasureTheory.volume {z : ℍ|torusCircleQ a b z=0}=0 := by
  rw [torusCircleQ_zero_carrier a b hab]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.volume_zero _

theorem torusCircleQ_pos_frontier_null (a b : ℝ) (hab : a<b) :
    MeasureTheory.volume (frontier {z : ℍ|0<torusCircleQ a b z})=0 := by
  apply MeasureTheory.measure_mono_null (t:={z : ℍ|torusCircleQ a b z=0}) _ (torusCircleQ_zero_null a b hab)
  intro z hz
  exact (frontier_lt_subset_eq continuous_const (torusCircleQ_continuous a b) hz).symm

theorem torusCircleQ_neg_frontier_null (a b : ℝ) (hab : a<b) :
    MeasureTheory.volume (frontier {z : ℍ|torusCircleQ a b z<0})=0 :=
  MeasureTheory.measure_mono_null (frontier_lt_subset_eq (torusCircleQ_continuous a b) continuous_const)
    (torusCircleQ_zero_null a b hab)

theorem torus_null_frontier_inter (A B : Set ℍ)
    (hA : MeasureTheory.volume (frontier A)=0) (hB : MeasureTheory.volume (frontier B)=0) :
    MeasureTheory.volume (frontier (A∩B))=0 :=
  MeasureTheory.measure_mono_null (frontier_inter_subset A B)
    (MeasureTheory.measure_union_null (MeasureTheory.measure_mono_null inter_subset_left hA)
      (MeasureTheory.measure_mono_null inter_subset_right hB))

theorem torusIdealQuad_frontier_null (a b c d : ℝ) (hab : a<b) (hbc : b<c) (hcd : c<d) :
    MeasureTheory.volume (frontier (torusIdealQuad a b c d))=0 := by
  exact torus_null_frontier_inter _ _ (torusCircleQ_pos_frontier_null a b hab)
    (torus_null_frontier_inter _ _ (torusCircleQ_pos_frontier_null b c hbc)
      (torus_null_frontier_inter _ _ (torusCircleQ_pos_frontier_null c d hcd)
        (torusCircleQ_neg_frontier_null a d (hab.trans (hbc.trans hcd)))))

/-- The genuine Nielsen change preserves the actual whole-group fundamental
quadrilateral. Its new cover and packing are conclusions of the true two-piece move. -/
theorem torusIdealQuad_nielsen_move (a b : ℝ) (ha : 1<a) (hab : a<b) (hFb : torusRealF b=a)
    (hOld : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ
      MeasureTheory.volume (torusIdealQuad 0 1 a b))
    (hOldPack : ∀g∈torusNativeGroup,g≠1→
      Disjoint (g • torusIdealQuad 0 1 a b) (torusIdealQuad 0 1 a b)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume (torusIdealQuad 0 1 (torusRealF a) a) ∧
    ∀g∈torusNativeGroup,g≠1→
      Disjoint (g • torusIdealQuad 0 1 (torusRealF a) a) (torusIdealQuad 0 1 (torusRealF a) a) := by
  have hF0 : torusRealF 0=1:=by norm_num [torusRealF]
  have hFa : 1<torusRealF a:=by
    have h:=torusRealF_strictMono 0 a (by norm_num) (by linarith)
    rwa [hF0] at h
  have hFaa : torusRealF a<a:=by
    have h:=torusRealF_strictMono a b (by linarith) hab
    rwa [hFb] at h
  let A:=torusIdealTriangle 0 1 a
  let B:=torusIdealTriangle 0 a b
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL
  have hf : f∈torusNativeGroup:=Subgroup.subset_closure (by left;rfl)
  have hAD : A⊆torusIdealQuad 0 1 a b:=torusIdealTriangle_subset_quad_first (by norm_num) ha hab
  have hBD : B⊆torusIdealQuad 0 1 a b:=torusIdealTriangle_subset_quad_second (by norm_num) ha hab
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    rintro z hA hB
    exact (not_lt_of_ge hA.2.2.le) hB.1
  have hcut : closure (A∪B)=closure (torusIdealQuad 0 1 a b) := by
    change closure (torusIdealTriangle 0 1 a∪torusIdealTriangle 0 a b)=_
    rw [torusIdealQuad_split_ac (by norm_num : (0:ℝ)<1) ha hab]
    exact torus_open_cut_closure _ (torusIdealQuad_isOpen 0 1 a b) 0 a (by linarith)
  have hImage : f • B=torusIdealTriangle 1 (torusRealF a) a := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) '' torusIdealTriangle 0 a b=_
    rw [torusExampleFSL_triangle_image 0 a b (by norm_num) (by linarith) (by linarith),hF0,hFb]
  have hclosed : closure (A∪f • B)=closure (torusIdealQuad 0 1 (torusRealF a) a) := by
    rw [hImage]
    change closure (torusIdealTriangle 0 1 a∪torusIdealTriangle 1 (torusRealF a) a)=_
    rw [torusIdealQuad_split_bd (by norm_num : (0:ℝ)<1) hFa hFaa]
    exact torus_open_cut_closure _ (torusIdealQuad_isOpen 0 1 (torusRealF a) a) 1 a ha
  have hreg : interior (closure (A∪f • B))=torusIdealQuad 0 1 (torusRealF a) a := by
    rw [hclosed,torusIdealQuad_regular (torusRealF a) a hFa hFaa]
  have hconn : IsConnected (interior (closure (A∪f • B))) := by
    rw [hreg]
    exact torusIdealQuad_isConnected (torusRealF a) a hFa hFaa
  have hnull : MeasureTheory.volume (frontier (interior (closure (A∪f • B))))=0 := by
    rw [hreg]
    exact torusIdealQuad_frontier_null 0 1 (torusRealF a) a (by norm_num) hFa hFaa
  constructor
  · have h:=two_piece_reassembly_fundamentalDomain torusNativeGroup MeasureTheory.volume
      (torusIdealQuad 0 1 a b) A B hOld (torusIdealTriangle_isOpen 0 1 a)
      (torusIdealTriangle_isOpen 0 a b) hAD hBD hAB hcut hOldPack f hf hconn hnull
    rwa [hreg] at h
  · intro g hg hne
    have h:=two_piece_reassembly_regularized_wandering torusNativeGroup
      (torusIdealQuad 0 1 a b) A B (torusIdealTriangle_isOpen 0 1 a)
      (torusIdealTriangle_isOpen 0 a b) hAD hBD hAB hOldPack f hf g hg hne
    rwa [hreg] at h


def torusInfiniteTriangle (a b : ℝ) : Set ℍ :=
  {z|a<z.re ∧ z.re<b ∧ 0<torusCircleQ a b z}

def torusStripQuad (a b c : ℝ) : Set ℍ :=
  {z|a<z.re ∧ 0<torusCircleQ a b z ∧ 0<torusCircleQ b c z ∧ z.re<c}

def torusVerticalNormal (c : ℝ) : ℂ := ⟨c/2,-1/2⟩

theorem torusVertical_klein (c : ℝ) (z : ℍ) :
    (c/2-inner ℝ (torusVerticalNormal c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z))*
      (Complex.normSq (z:ℂ)+1)=c-z.re := by
  have hd : z.re^2+z.im^2+1≠0:=ne_of_gt (by positivity)
  norm_num [torusVerticalNormal,_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_explicit,Complex.normSq_apply]
  field_simp [hd]
  ring

theorem torusVertical_klein_lt (c : ℝ) (z : ℍ) :
    z.re<c ↔ inner ℝ (torusVerticalNormal c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)<c/2 := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [←sub_pos,←torusVertical_klein,mul_pos_iff_of_pos_right hd,sub_pos]

theorem torusVertical_klein_gt (c : ℝ) (z : ℍ) :
    c<z.re ↔ inner ℝ (-torusVerticalNormal c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z)< -c/2 := by
  have hd : 0<Complex.normSq (z:ℂ)+1:=by linarith [Complex.normSq_nonneg (z:ℂ)]
  rw [inner_neg_left]
  calc
    c<z.re ↔ c-z.re<0 := sub_neg.symm
    _ ↔ (c/2-inner ℝ (torusVerticalNormal c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z))*
      (Complex.normSq (z:ℂ)+1)<0 := by rw [torusVertical_klein]
    _ ↔ c/2-inner ℝ (torusVerticalNormal c) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate
      z)<0 :=
      by constructor
         · intro h
           by_contra! hn
           exact (not_lt_of_ge (mul_nonneg hn hd.le)) h
         · exact fun h=>mul_neg_of_neg_of_pos h hd
    _ ↔ _ := by constructor <;> intro h <;> linarith

def torusStripNormals (a b c : ℝ) : Fin 4→ℂ :=
  ![-torusVerticalNormal a,torusCircleNormal a b,torusCircleNormal b c,torusVerticalNormal c]
def torusStripThresholds (a b c : ℝ) : Fin 4→ℝ :=
  ![-a/2,torusCircleThreshold a b,torusCircleThreshold b c,c/2]

theorem torusStripQuad_klein (a b c : ℝ) :
    torusStripQuad a b c=torusKleinCutRegion (torusStripNormals a b c) (torusStripThresholds a b c) := by
  ext z
  constructor
  · rintro ⟨h₁,h₂,h₃,h₄⟩ i
    fin_cases i
    · exact (torusVertical_klein_gt a z).mp h₁
    · exact (torusCircleQ_klein_pos_iff a b z).mp h₂
    · exact (torusCircleQ_klein_pos_iff b c z).mp h₃
    · exact (torusVertical_klein_lt c z).mp h₄
  · intro h
    exact ⟨(torusVertical_klein_gt a z).mpr (h 0),
      (torusCircleQ_klein_pos_iff a b z).mpr (h 1),
      (torusCircleQ_klein_pos_iff b c z).mpr (h 2),
      (torusVertical_klein_lt c z).mpr (h 3)⟩

theorem torusStripQuad_isOpen (a b c : ℝ) : IsOpen (torusStripQuad a b c) := by
  rw [torusStripQuad_klein]
  exact torusKleinCutRegion_isOpen _ _

theorem torusStripQuad_hConvex (a b c : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (torusStripQuad a b c) := by
  rw [torusStripQuad_klein]
  exact torusKleinCutRegion_hConvex _ _

theorem torusStripQuad_nonempty (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    (torusStripQuad a b c).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe b 1 (by norm_num),?_,?_,?_,?_⟩

  · exact hab
  · rw [torusCircleQ_eq]
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  · rw [torusCircleQ_eq]
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  · exact hbc

theorem torusStripQuad_regular (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    interior (closure (torusStripQuad a b c))=torusStripQuad a b c :=
  torus_hConvex_regular (torusStripQuad_hConvex a b c) (torusStripQuad_isOpen a b c)
    (torusStripQuad_nonempty a b c hab hbc)

theorem torusStripQuad_isConnected (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    IsConnected (torusStripQuad a b c) :=
  ⟨torusStripQuad_nonempty a b c hab hbc,(torusStripQuad_hConvex a b c).isPreconnected⟩

theorem torusInfiniteTriangle_isOpen (a b : ℝ) : IsOpen (torusInfiniteTriangle a b) :=
  (isOpen_lt continuous_const UpperHalfPlane.continuous_re).inter
    ((isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
      (isOpen_lt continuous_const (torusCircleQ_continuous a b)))

theorem torusVertical_zero_null (a : ℝ) :
    MeasureTheory.volume {z : ℍ|z.re=a}=0 := by
  change MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical a).carrier=0
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.volume_zero _

theorem torusVertical_lt_frontier_null (a : ℝ) :
    MeasureTheory.volume (frontier {z : ℍ|z.re<a})=0 :=
  MeasureTheory.measure_mono_null (frontier_lt_subset_eq UpperHalfPlane.continuous_re continuous_const)
    (torusVertical_zero_null a)

theorem torusVertical_gt_frontier_null (a : ℝ) :
    MeasureTheory.volume (frontier {z : ℍ|a<z.re})=0 := by
  apply MeasureTheory.measure_mono_null (t:={z : ℍ|z.re=a}) _ (torusVertical_zero_null a)
  intro z hz
  exact (frontier_lt_subset_eq continuous_const UpperHalfPlane.continuous_re hz).symm

theorem torusStripQuad_frontier_null (a b c : ℝ) (hab : a<b) (hbc : b<c) :
    MeasureTheory.volume (frontier (torusStripQuad a b c))=0 :=
  torus_null_frontier_inter _ _ (torusVertical_gt_frontier_null a)
    (torus_null_frontier_inter _ _ (torusCircleQ_pos_frontier_null a b hab)
      (torus_null_frontier_inter _ _ (torusCircleQ_pos_frontier_null b c hbc)
        (torusVertical_lt_frontier_null c)))

theorem torusVertical_ne_dense (a : ℝ) : Dense {z : ℍ|z.re≠a} := by
  have h : interior {z : ℍ|z.re=a}=∅ := by
    change interior (UpperHalfPlane.re ⁻¹' ({a} : Set ℝ))=∅
    rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage
      UpperHalfPlane.continuous_re,interior_singleton,preimage_empty]
  exact interior_eq_empty_iff_dense_compl.mp h

theorem torus_open_vertical_cut_closure (U : Set ℍ) (hU : IsOpen U) (a : ℝ) :
    closure (U∩{z|z.re≠a})=closure U := by
  apply subset_antisymm (closure_mono inter_subset_left)
  apply closure_minimal _ isClosed_closure
  intro z hz
  apply mem_closure_iff.mpr
  intro V hV hzV
  obtain ⟨x,hxS,hxV⟩:=(torusVertical_ne_dense a).exists_mem_open (hV.inter hU) ⟨z,hzV,hz⟩
  exact ⟨x,hxV.1,hxV.2,hxS⟩

theorem torusInitialQuad_strip : torusInitialQuad=torusStripQuad (-1) 0 1 := by
  ext z
  simp only [torusInitialQuad,torusFSector,torusGSector,torusStripQuad,mem_inter_iff,mem_ofPred_eq]
  tauto

theorem torusStripQuad_split_vertical {a b c : ℝ} (hab : a<b) (hbc : b<c) :
    torusInfiniteTriangle a b∪torusInfiniteTriangle b c=
      torusStripQuad a b c∩{z|z.re≠b} := by
  ext z
  constructor
  · rintro (⟨h₁,h₂,h₃⟩|⟨h₁,h₂,h₃⟩)
    · have hq : 0<torusCircleQ b c z := by
        rw [torusCircleQ_eq]
        have hm:=mul_pos_of_neg_of_neg (sub_neg.mpr h₂) (sub_neg.mpr (h₂.trans hbc))
        nlinarith [sq_nonneg z.im]
      exact ⟨⟨h₁,h₃,hq,h₂.trans hbc⟩,ne_of_lt h₂⟩
    · have hq : 0<torusCircleQ a b z := by
        rw [torusCircleQ_eq]
        have hm:=mul_pos (sub_pos.mpr (hab.trans h₁)) (sub_pos.mpr h₁)
        nlinarith [sq_nonneg z.im]
      exact ⟨⟨hab.trans h₁,hq,h₃,h₂⟩,ne_of_gt h₁⟩
  · rintro ⟨h,hne⟩
    rcases lt_or_gt_of_ne hne with hb|hb
    · exact Or.inl ⟨h.1,hb,h.2.1⟩
    · exact Or.inr ⟨hb,h.2.2.2,h.2.2.1⟩

theorem torusStripQuad_split_circle {a b c : ℝ} (hab : a<b) (hbc : b<c) :
    torusIdealTriangle a b c∪torusInfiniteTriangle a c=
      torusStripQuad a b c∩{z|torusCircleQ a c z≠0} := by
  ext z
  constructor
  · rintro (h|h)
    · obtain ⟨ha,hc⟩:=torusCircleQ_inside_re (hab.trans hbc) z h.2.2
      exact ⟨⟨ha,h.1,h.2.1,hc⟩,ne_of_lt h.2.2⟩
    · change a<z.re ∧ z.re<c ∧ 0<torusCircleQ a c z at h
      have h₁ : 0<torusCircleQ a b z := by
        have hp:=mul_pos (sub_pos.mpr hbc) (sub_pos.mpr h.1)
        dsimp [torusCircleQ] at *
        nlinarith
      have h₂ : 0<torusCircleQ b c z := by
        have hp:=mul_pos (sub_pos.mpr hab) (sub_pos.mpr h.2.1)
        dsimp [torusCircleQ] at *
        nlinarith
      exact ⟨⟨h.1,h₁,h₂,h.2.1⟩,ne_of_gt h.2.2⟩
  · rintro ⟨h,hne⟩
    rcases lt_or_gt_of_ne hne with hq|hq
    · exact Or.inl ⟨h.2.1,h.2.2.1,hq⟩
    · exact Or.inr ⟨h.1,h.2.2.2,hq⟩

theorem torusExampleFSL_vertical_circle (a : ℝ) (ha : a≠ -1) (z : ℍ) :
    torusCircleQ (torusRealF a) 3 (torusExampleFSL • z)*
      ((a+1)*Complex.normSq ((z:ℂ)+1))= -4*(z.re-a) := by
  have hd : Complex.normSq ((z:ℂ)+1)≠0:=ne_of_gt
    (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  have ha' : a+1≠0:=by intro h;apply ha;linarith
  rw [torusCircleQ,torusExampleFSL_re,torusExampleFSL_normSq]
  dsimp [torusRealF]
  field_simp [hd,ha']
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
    add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem torusExampleFSL_vertical_circle_pos (a : ℝ) (ha : -1<a) (z : ℍ) :
    0<torusCircleQ (torusRealF a) 3 (torusExampleFSL • z) ↔ z.re<a := by
  have hd : 0<(a+1)*Complex.normSq ((z:ℂ)+1):=mul_pos (by linarith)
    (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  have he:=torusExampleFSL_vertical_circle a (ne_of_gt ha) z
  constructor
  · intro h
    have hp:=mul_pos h hd
    rw [he] at hp
    linarith
  · intro h
    by_contra! hn
    have hp:=mul_nonpos_of_nonpos_of_nonneg hn hd.le
    rw [he] at hp
    linarith

theorem torusExampleFSL_vertical_circle_neg (a : ℝ) (ha : -1<a) (z : ℍ) :
    torusCircleQ (torusRealF a) 3 (torusExampleFSL • z)<0 ↔ a<z.re := by
  have hd : 0<(a+1)*Complex.normSq ((z:ℂ)+1):=mul_pos (by linarith)
    (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  have he:=torusExampleFSL_vertical_circle a (ne_of_gt ha) z
  constructor
  · intro h
    have hp:=mul_neg_of_neg_of_pos h hd
    rw [he] at hp
    linarith
  · intro h
    by_contra! hn
    have hp:=mul_nonneg hn hd.le
    rw [he] at hp
    linarith

theorem torusExampleFSL_infinite_triangle_image (a b : ℝ) (ha : -1<a) (hb : -1<b) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) '' torusInfiniteTriangle a b=
      torusIdealTriangle (torusRealF a) (torusRealF b) 3 := by
  apply subset_antisymm
  · rintro _ ⟨z,⟨h₁,h₂,h₃⟩,rfl⟩
    exact ⟨(torusExampleFSL_circle_pos_iff a b ha hb z).mpr h₃,
      (torusExampleFSL_vertical_circle_pos b hb z).mpr h₂,
      (torusExampleFSL_vertical_circle_neg a ha z).mpr h₁⟩
  · intro z hz
    obtain ⟨w,he⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL).surjective z
    rw [←he] at hz
    exact ⟨w,⟨(torusExampleFSL_vertical_circle_neg a ha w).mp hz.2.2,
      (torusExampleFSL_vertical_circle_pos b hb w).mp hz.2.1,
      (torusExampleFSL_circle_pos_iff a b ha hb w).mp hz.1⟩,he⟩

theorem torusExampleFSL_re_three (z : ℍ) :
    ((torusExampleFSL • z).re-3)*Complex.normSq ((z:ℂ)+1)= -2*(z.re+1) := by
  have hd : Complex.normSq ((z:ℂ)+1)≠0:=ne_of_gt
    (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z)
  rw [torusExampleFSL_re]
  field_simp [hd]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,
    add_zero,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
  ring

theorem torusExampleFSL_left_infinite_triangle_image :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) '' torusInfiniteTriangle (-1) 0=torusInfiniteTriangle 1 3 := by
  have hF0 : torusRealF 0=1:=by norm_num [torusRealF]
  have hcrit (z : ℍ) :
      torusExampleFSL • z∈torusInfiniteTriangle 1 3 ↔ z∈torusInfiniteTriangle (-1) 0 := by
    have hd : 0<Complex.normSq ((z:ℂ)+1):=by
      simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 z
    have h₁:=torusExampleFSL_side_identity z
    have h₂:=torusExampleFSL_re_three z
    have h₃:=torusExampleFSL_vertical_circle_pos 0 (by norm_num) z
    rw [hF0] at h₃
    constructor
    · rintro ⟨hA,hB,hC⟩
      have hAp:=mul_pos (sub_pos.mpr hA) hd
      have hBp:=mul_neg_of_neg_of_pos (sub_neg.mpr hB) hd
      refine ⟨?_,h₃.mp hC,?_⟩ <;> nlinarith
    · rintro ⟨hA,hB,hC⟩
      have hAp : 0<((torusExampleFSL • z).re-1)*Complex.normSq ((z:ℂ)+1):=by nlinarith
      have hBp : ((torusExampleFSL • z).re-3)*Complex.normSq ((z:ℂ)+1)<0:=by nlinarith
      refine ⟨?_,?_,h₃.mpr hB⟩
      · exact sub_pos.mp ((mul_pos_iff_of_pos_right hd).mp hAp)
      · by_contra! hn
        have hp:=mul_nonneg (sub_nonneg.mpr hn) hd.le
        exact not_lt_of_ge hp hBp
  apply subset_antisymm
  · rintro _ ⟨z,hz,rfl⟩
    exact (hcrit z).mpr hz
  · intro z hz
    obtain ⟨w,he⟩:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL).surjective z
    refine ⟨w,(hcrit w).mp ?_,he⟩
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) w∈torusInfiniteTriangle 1 3
    rwa [he]

theorem torus_reassembly_to (D A B E : Set ℍ)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ
      MeasureTheory.volume D)
    (hA : IsOpen A) (hB : IsOpen B) (hAD : A⊆D) (hBD : B⊆D)
    (hAB : Disjoint A B) (hcut : closure (A∪B)=closure D)
    (hpack : ∀g∈torusNativeGroup,g≠1→Disjoint (g • D) D)
    (hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure E)
    (hreg : interior (closure E)=E) (hconn : IsConnected E)
    (hnull : MeasureTheory.volume (frontier E)=0) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume E ∧
      ∀g∈torusNativeGroup,g≠1→Disjoint (g • E) E := by
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL∈torusNativeGroup:=Subgroup.subset_closure (by left;rfl)
  have he : interior (closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B))=E:=by rw [hnew,hreg]
  have hc : IsConnected (interior (closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL) • B))):=he ▸ hconn
  have hn : MeasureTheory.volume (frontier (interior (closure
    (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B))))=0:=he ▸ hnull
  constructor
  · have h:=two_piece_reassembly_fundamentalDomain torusNativeGroup MeasureTheory.volume D A B
      hD hA hB hAD hBD hAB hcut hpack (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        torusExampleFSL) hf hc hn
    rwa [he] at h
  · intro g hg hne
    have h:=two_piece_reassembly_regularized_wandering torusNativeGroup D A B hA hB hAD hBD
      hAB hpack (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) hf g hg hne
    rwa [he] at h

theorem torus_first_nielsen_move :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume (torusStripQuad 0 1 3) ∧
      ∀g∈torusNativeGroup,g≠1→Disjoint (g • torusStripQuad 0 1 3) (torusStripQuad 0 1 3) := by
  let A:=torusInfiniteTriangle 0 1
  let B:=torusInfiniteTriangle (-1) 0
  have hcutset : A∪B=torusInitialQuad∩{z|z.re≠0}:=by
    rw [torusInitialQuad_strip]
    change torusInfiniteTriangle 0 1∪torusInfiniteTriangle (-1) 0=_
    rw [union_comm,torusStripQuad_split_vertical (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)]
  have hAD : A⊆torusInitialQuad:=by
    intro z hz
    have h : z∈A∪B:=Or.inl hz
    rw [hcutset] at h
    exact h.1
  have hBD : B⊆torusInitialQuad:=by
    intro z hz
    have h : z∈A∪B:=Or.inr hz
    rw [hcutset] at h
    exact h.1
  have hAB : Disjoint A B:=by
    apply disjoint_left.mpr
    rintro z ⟨hA,_⟩ ⟨_,hB,_⟩
    exact (not_lt_of_ge hA.le) hB
  have hcut : closure (A∪B)=closure torusInitialQuad:=by
    rw [hcutset]
    exact torus_open_vertical_cut_closure _ torusInitialQuad_isOpen 0
  have hImage : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    torusExampleFSL) • B=torusInfiniteTriangle 1 3:=
    torusExampleFSL_left_infinite_triangle_image
  have hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure (torusStripQuad 0 1 3):=by
    rw [hImage]
    change closure (torusInfiniteTriangle 0 1∪torusInfiniteTriangle 1 3)=_
    rw [torusStripQuad_split_vertical (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<3)]
    exact torus_open_vertical_cut_closure _ (torusStripQuad_isOpen 0 1 3) 1
  exact torus_reassembly_to torusInitialQuad A B (torusStripQuad 0 1 3) torusInitialQuad_fundamental
    (torusInfiniteTriangle_isOpen 0 1) (torusInfiniteTriangle_isOpen (-1) 0) hAD hBD hAB hcut
    torusInitialQuad_wandering hnew (torusStripQuad_regular 0 1 3 (by norm_num) (by norm_num))
    (torusStripQuad_isConnected 0 1 3 (by norm_num) (by norm_num))
    (torusStripQuad_frontier_null 0 1 3 (by norm_num) (by norm_num))

theorem torus_second_nielsen_move :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume (torusIdealQuad 0 1 (5/2) 3) ∧
      ∀g∈torusNativeGroup,g≠1→
        Disjoint (g • torusIdealQuad 0 1 (5/2) 3) (torusIdealQuad 0 1 (5/2) 3) := by
  let A:=torusIdealTriangle 0 1 3
  let B:=torusInfiniteTriangle 0 3
  have hcutset : A∪B=torusStripQuad 0 1 3∩{z|torusCircleQ 0 3 z≠0}:=
    torusStripQuad_split_circle (by norm_num) (by norm_num)
  have hAD : A⊆torusStripQuad 0 1 3:=by
    intro z hz
    have h : z∈A∪B:=Or.inl hz
    rw [hcutset] at h
    exact h.1
  have hBD : B⊆torusStripQuad 0 1 3:=by
    intro z hz
    have h : z∈A∪B:=Or.inr hz
    rw [hcutset] at h
    exact h.1
  have hAB : Disjoint A B:=by
    apply disjoint_left.mpr
    rintro z ⟨_,_,hA⟩ ⟨_,_,hB⟩
    exact (not_lt_of_ge hA.le) hB
  have hcut : closure (A∪B)=closure (torusStripQuad 0 1 3):=by
    rw [hcutset]
    exact torus_open_cut_closure _ (torusStripQuad_isOpen 0 1 3) 0 3 (by norm_num)
  have hImage : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B=torusIdealTriangle 1 (5/2) 3:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      torusExampleFSL) '' torusInfiniteTriangle 0 3=_
    rw [torusExampleFSL_infinite_triangle_image 0 3 (by norm_num) (by norm_num)]
    norm_num [torusRealF]
  have hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure (torusIdealQuad 0 1 (5/2) 3):=by
    rw [hImage]
    change closure (torusIdealTriangle 0 1 3∪torusIdealTriangle 1 (5/2) 3)=_
    rw [torusIdealQuad_split_bd (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<5/2) (by norm_num : (5:ℝ)/2<3)]
    exact torus_open_cut_closure _ (torusIdealQuad_isOpen 0 1 (5/2) 3) 1 3 (by norm_num)
  exact torus_reassembly_to (torusStripQuad 0 1 3) A B (torusIdealQuad 0 1 (5/2) 3)
    torus_first_nielsen_move.1 (torusIdealTriangle_isOpen 0 1 3) (torusInfiniteTriangle_isOpen 0 3)
    hAD hBD hAB hcut torus_first_nielsen_move.2 hnew
    (torusIdealQuad_regular (5/2) 3 (by norm_num) (by norm_num))
    (torusIdealQuad_isConnected (5/2) 3 (by norm_num) (by norm_num))
    (torusIdealQuad_frontier_null 0 1 (5/2) 3 (by norm_num) (by norm_num) (by norm_num))
/-- Packing and the genuine nearest representative force every point of the
actual open quadrilateral to satisfy all whole-group Dirichlet comparisons. -/
theorem torusInitialQuad_subset_nativeClosedDirichlet :
    torusInitialQuad ⊆ nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I := by
  intro z hz
  obtain ⟨g,hg⟩:=nativeClosedDirichlet_meets_orbit torusNativeGroup
    torusNativeGroup_discontinuous UpperHalfPlane.I z
  have hg1 : g=1 := by
    by_contra hn
    have hv : g.val≠1 := fun h=>hn (Subtype.ext h)
    have hop : IsOpen (g • torusInitialQuad) :=
      g.val.toHomeomorph.isOpenMap _ torusInitialQuad_isOpen
    have hd:=(torusInitialQuad_wandering g.val g.property hv).closure_right hop
    have hcl : g.val z∈closure torusInitialQuad := by
      rw [torusInitialQuad_closure]
      exact torusNativeClosedDirichlet_subset hg
    exact disjoint_left.mp hd ⟨z,hz,rfl⟩ hcl
  change g • z∈nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I at hg
  simpa only [hg1,one_smul] using hg

/-- The closed physical quadrilateral is the literal full-group closed Dirichlet set. -/
theorem torusInitialQuad_closure_eq_nativeClosedDirichlet :
    closure torusInitialQuad=nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I := by
  have hc : IsClosed (nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I) := by
    have he : nativeClosedDirichlet torusNativeGroup UpperHalfPlane.I=
        ⋂g : torusNativeGroup,{z : ℍ|dist z UpperHalfPlane.I≤dist z (g.val UpperHalfPlane.I)} := by
      ext z
      simp [nativeClosedDirichlet]
    rw [he]
    exact isClosed_iInter (fun _=>isClosed_le (by fun_prop) (by fun_prop))
  apply subset_antisymm (closure_minimal torusInitialQuad_subset_nativeClosedDirichlet hc)
  intro z hz
  rw [torusInitialQuad_closure]
  exact torusNativeClosedDirichlet_subset hz

/-- The actual quadrilateral closed tiles are locally finite for the entire
native group. Compact-orbit label finiteness is used, not presumed. -/
theorem torusInitialQuad_closed_tiles_locallyFinite :
    LocallyFinite (fun g : torusNativeGroup=>g • closure torusInitialQuad) := by
  intro x
  let R : ℝ:=dist x UpperHalfPlane.I+1
  have hp:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.isDiscontinuous_iff_properlyDiscontinuousSMul
    torusNativeGroup ℍ).mp
    torusNativeGroup_discontinuous
  have hf:=hp.finite_disjoint_inter_image (isCompact_singleton (x:=UpperHalfPlane.I))
    (isCompact_closedBall UpperHalfPlane.I (2*R))
  refine ⟨Metric.ball x 1,Metric.ball_mem_nhds x (by norm_num),hf.subset ?_⟩
  rintro g ⟨y,⟨u,hu,rfl⟩,hy⟩
  rw [torusInitialQuad_closure_eq_nativeClosedDirichlet] at hu
  have hcomp:=hu g⁻¹
  change dist u UpperHalfPlane.I≤dist u (g.val⁻¹ UpperHalfPlane.I) at hcomp
  have he : dist u (g.val⁻¹ UpperHalfPlane.I)=dist (g.val u) UpperHalfPlane.I := by
    have h:=(g.val).dist_eq u (g.val⁻¹ UpperHalfPlane.I)
    rw [IsometryEquiv.apply_inv_self] at h
    exact h.symm
  rw [he] at hcomp
  have hbound : dist (g.val UpperHalfPlane.I) UpperHalfPlane.I≤2*dist (g.val u) UpperHalfPlane.I := by
    have ht:=dist_triangle (g.val UpperHalfPlane.I) (g.val u) UpperHalfPlane.I
    rw [(g.val).dist_eq,dist_comm UpperHalfPlane.I u] at ht
    linarith
  have hyx : dist (g.val u) x<1:=hy
  have hyI : dist (g.val u) UpperHalfPlane.I<R := by
    have ht:=dist_triangle (g.val u) x UpperHalfPlane.I
    dsimp [R]
    linarith
  refine ⟨g.val UpperHalfPlane.I,⟨UpperHalfPlane.I,rfl,rfl⟩,?_⟩
  exact Metric.mem_closedBall.mpr (by linarith)


theorem torus_reassembly_closed_tiles_locallyFinite (D A B E : Set ℍ)
    (hAD : A⊆D) (hBD : B⊆D)
    (hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure E)
    (hLF : LocallyFinite (fun g : torusNativeGroup=>g • closure D)) :
    LocallyFinite (fun g : torusNativeGroup=>g • closure E) := by
  let f : torusNativeGroup:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL,Subgroup.subset_closure (by left;rfl)⟩
  have hsub : closure E⊆closure D∪f • closure D := by
    rw [←hnew,closure_union]
    apply union_subset_union (closure_mono hAD)
    change closure (f.val.toHomeomorph '' B)⊆f.val.toHomeomorph '' closure D
    rw [←f.val.toHomeomorph.image_closure]
    exact image_mono (closure_mono hBD)
  have hLF₂ : LocallyFinite (fun g : torusNativeGroup=>(g*f) • closure D):=
    hLF.comp_injective (fun _ _ h=>mul_right_cancel h)
  intro x
  obtain ⟨U,hU,hfinU⟩:=hLF x
  obtain ⟨V,hV,hfinV⟩:=hLF₂ x
  refine ⟨U∩V,Filter.inter_mem hU hV,(hfinU.union hfinV).subset ?_⟩
  rintro g ⟨y,⟨u,hu,rfl⟩,hyU,hyV⟩
  rcases hsub hu with huD|⟨v,hv,rfl⟩
  · exact Or.inl ⟨g • u,⟨u,huD,rfl⟩,hyU⟩
  · exact Or.inr ⟨g • (f • v),⟨v,hv,(mul_smul g f v).symm⟩,hyV⟩

theorem torus_first_nielsen_locallyFinite
    (hLF : LocallyFinite (fun g : torusNativeGroup=>g • closure torusInitialQuad)) :
    LocallyFinite (fun g : torusNativeGroup=>g • closure (torusStripQuad 0 1 3)) := by
  let A:=torusInfiniteTriangle 0 1
  let B:=torusInfiniteTriangle (-1) 0
  have hcutset : A∪B=torusInitialQuad∩{z|z.re≠0}:=by
    rw [torusInitialQuad_strip]
    change torusInfiniteTriangle 0 1∪torusInfiniteTriangle (-1) 0=_
    rw [union_comm,torusStripQuad_split_vertical (by norm_num : (-1:ℝ)<0) (by norm_num : (0:ℝ)<1)]
  have hAD : A⊆torusInitialQuad:=by
    intro z hz
    have h : z∈A∪B:=Or.inl hz
    rw [hcutset] at h
    exact h.1
  have hBD : B⊆torusInitialQuad:=by
    intro z hz
    have h : z∈A∪B:=Or.inr hz
    rw [hcutset] at h
    exact h.1
  have hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure (torusStripQuad 0 1 3):=by
    rw [show (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B=torusInfiniteTriangle 1
      3 from
      torusExampleFSL_left_infinite_triangle_image]
    change closure (torusInfiniteTriangle 0 1∪torusInfiniteTriangle 1 3)=_
    rw [torusStripQuad_split_vertical (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<3)]
    exact torus_open_vertical_cut_closure _ (torusStripQuad_isOpen 0 1 3) 1
  exact torus_reassembly_closed_tiles_locallyFinite torusInitialQuad A B _ hAD hBD hnew hLF

theorem torus_second_nielsen_locallyFinite
    (hLF : LocallyFinite (fun g : torusNativeGroup=>g • closure (torusStripQuad 0 1 3))) :
    LocallyFinite (fun g : torusNativeGroup=>g • closure (torusIdealQuad 0 1 (5/2) 3)) := by
  let A:=torusIdealTriangle 0 1 3
  let B:=torusInfiniteTriangle 0 3
  have hcutset : A∪B=torusStripQuad 0 1 3∩{z|torusCircleQ 0 3 z≠0}:=
    torusStripQuad_split_circle (by norm_num) (by norm_num)
  have hAD : A⊆torusStripQuad 0 1 3:=by
    intro z hz
    have h : z∈A∪B:=Or.inl hz
    rw [hcutset] at h
    exact h.1
  have hBD : B⊆torusStripQuad 0 1 3:=by
    intro z hz
    have h : z∈A∪B:=Or.inr hz
    rw [hcutset] at h
    exact h.1
  have hImage : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B=torusIdealTriangle 1 (5/2) 3:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      torusExampleFSL) '' torusInfiniteTriangle 0 3=_
    rw [torusExampleFSL_infinite_triangle_image 0 3 (by norm_num) (by norm_num)]
    norm_num [torusRealF]
  have hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure (torusIdealQuad 0 1 (5/2) 3):=by
    rw [hImage]
    change closure (torusIdealTriangle 0 1 3∪torusIdealTriangle 1 (5/2) 3)=_
    rw [torusIdealQuad_split_bd (by norm_num : (0:ℝ)<1) (by norm_num : (1:ℝ)<5/2) (by norm_num : (5:ℝ)/2<3)]
    exact torus_open_cut_closure _ (torusIdealQuad_isOpen 0 1 (5/2) 3) 1 3 (by norm_num)
  exact torus_reassembly_closed_tiles_locallyFinite (torusStripQuad 0 1 3) A B _ hAD hBD hnew hLF

theorem torus_nielsen_locallyFinite (a b : ℝ) (ha : 1<a) (hab : a<b) (hFb : torusRealF b=a)
    (hLF : LocallyFinite (fun g : torusNativeGroup=>g • closure (torusIdealQuad 0 1 a b))) :
    LocallyFinite (fun g : torusNativeGroup=>g • closure (torusIdealQuad 0 1 (torusRealF a) a)) := by
  have hF0 : torusRealF 0=1:=by norm_num [torusRealF]
  have hFa : 1<torusRealF a:=by
    have h:=torusRealF_strictMono 0 a (by norm_num) (by linarith)
    rwa [hF0] at h
  have hFaa : torusRealF a<a:=by
    have h:=torusRealF_strictMono a b (by linarith) hab
    rwa [hFb] at h
  let A:=torusIdealTriangle 0 1 a
  let B:=torusIdealTriangle 0 a b
  have hAD : A⊆torusIdealQuad 0 1 a b:=torusIdealTriangle_subset_quad_first (by norm_num) ha hab
  have hBD : B⊆torusIdealQuad 0 1 a b:=torusIdealTriangle_subset_quad_second (by norm_num) ha hab
  have hImage : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B=torusIdealTriangle 1 (torusRealF a) a := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) '' torusIdealTriangle 0 a b=_
    rw [torusExampleFSL_triangle_image 0 a b (by norm_num) (by linarith) (by linarith),hF0,hFb]
  have hnew : closure (A∪(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL) • B)=closure (torusIdealQuad 0 1 (torusRealF a) a) := by
    rw [hImage]
    change closure (torusIdealTriangle 0 1 a∪torusIdealTriangle 1 (torusRealF a) a)=_
    rw [torusIdealQuad_split_bd (by norm_num : (0:ℝ)<1) hFa hFaa]
    exact torus_open_cut_closure _ (torusIdealQuad_isOpen 0 1 (torusRealF a) a) 1 a ha
  exact torus_reassembly_closed_tiles_locallyFinite (torusIdealQuad 0 1 a b) A B _ hAD hBD hnew hLF

def torusNielsenEndpoints : ℕ→ℝ×ℝ
  | 0=>(5/2,3)
  | n+1=>(torusRealF (torusNielsenEndpoints n).1,(torusNielsenEndpoints n).1)

def torusNielsenQuad (n : ℕ) : Set ℍ :=
  torusIdealQuad 0 1 (torusNielsenEndpoints n).1 (torusNielsenEndpoints n).2

theorem torusNielsenEndpoints_order (n : ℕ) :
    1<(torusNielsenEndpoints n).1 ∧
      (torusNielsenEndpoints n).1<(torusNielsenEndpoints n).2 ∧
      torusRealF (torusNielsenEndpoints n).2=(torusNielsenEndpoints n).1 := by
  induction n with
  | zero => norm_num [torusNielsenEndpoints,torusRealF]
  | succ n ih =>
    change 1<torusRealF (torusNielsenEndpoints n).1 ∧
      torusRealF (torusNielsenEndpoints n).1<(torusNielsenEndpoints n).1 ∧ _
    have hF0 : torusRealF 0=1:=by norm_num [torusRealF]
    have h₁:=torusRealF_strictMono 0 (torusNielsenEndpoints n).1 (by norm_num) (by linarith [ih.1])
    have h₂:=torusRealF_strictMono (torusNielsenEndpoints n).1 (torusNielsenEndpoints n).2
      (by linarith [ih.1]) ih.2.1
    rw [hF0] at h₁
    rw [ih.2.2] at h₂
    exact ⟨h₁,h₂,rfl⟩

theorem torusNielsenQuad_fundamental_packing (n : ℕ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusNativeGroup ℍ MeasureTheory.volume (torusNielsenQuad n) ∧
      ∀g∈torusNativeGroup,g≠1→Disjoint (g • torusNielsenQuad n) (torusNielsenQuad n) := by
  induction n with
  | zero => exact torus_second_nielsen_move
  | succ n ih =>
    obtain ⟨h₁,h₂,h₃⟩:=torusNielsenEndpoints_order n
    exact torusIdealQuad_nielsen_move _ _ h₁ h₂ h₃ ih.1 ih.2

theorem torusNielsenQuad_closed_tiles_locallyFinite (n : ℕ) :
    LocallyFinite (fun g : torusNativeGroup=>g • closure (torusNielsenQuad n)) := by
  induction n with
  | zero =>
    exact torus_second_nielsen_locallyFinite
      (torus_first_nielsen_locallyFinite torusInitialQuad_closed_tiles_locallyFinite)
  | succ n ih =>
    obtain ⟨h₁,h₂,h₃⟩:=torusNielsenEndpoints_order n
    exact torus_nielsen_locallyFinite _ _ h₁ h₂ h₃ ih

theorem torusNielsenQuad_hConvex (n : ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (torusNielsenQuad
  n) :=
  torusIdealQuad_hConvex _ _ _ _

def torusNielsenWordSL (n : ℕ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  torusExampleFSL^(n+2)*torusExampleGSL

theorem torusNielsenWordSL_succ (n : ℕ) :
    torusNielsenWordSL (n+1)=torusExampleFSL*torusNielsenWordSL n := by
  simp only [torusNielsenWordSL,pow_succ',mul_assoc]

theorem torusCircleQ_zero_re (a b : ℝ) (hab : a<b) (z : ℍ)
    (hz : torusCircleQ a b z=0) : a<z.re ∧ z.re<b := by
  rw [torusCircleQ_eq] at hz
  have hy : 0<z.im^2:=sq_pos_of_pos z.im_pos
  constructor
  · by_contra! hn
    have hm:=mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hn)
      (sub_nonpos.mpr (hn.trans hab.le))
    nlinarith
  · by_contra! hn
    have hm:=mul_nonneg (sub_nonneg.mpr (hab.le.trans hn)) (sub_nonneg.mpr hn)
    nlinarith

theorem torusNielsenWordSL_side_zero (n : ℕ) (z : ℍ) :
    torusCircleQ (torusNielsenEndpoints n).1 (torusNielsenEndpoints n).2
      (torusNielsenWordSL n • z)=0 ↔ torusCircleQ 0 1 z=0 := by
  have hzero (r : ℝ) (u : ℍ) (hr : r≠ -1) :
      torusCircleQ (torusRealF r) 3 (torusExampleFSL • u)=0 ↔ u.re=r := by
    have he:=torusExampleFSL_vertical_circle r hr u
    have hd : (r+1)*Complex.normSq ((u:ℂ)+1)≠0:=
      mul_ne_zero (by intro h;apply hr;linarith)
        (ne_of_gt (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 u))
    constructor
    · intro h
      rw [h,zero_mul] at he
      linarith
    · intro h
      have hn : -4*(u.re-r)=0:=by rw [h];ring
      rw [hn] at he
      exact (mul_eq_zero.mp he).resolve_right hd
  induction n generalizing z with
  | zero =>
    change torusCircleQ (5/2) 3 ((torusExampleFSL^2*torusExampleGSL) • z)=0 ↔ _
    rw [mul_smul,pow_two,mul_smul]
    have he:=hzero 3 (torusExampleFSL • (torusExampleGSL • z)) (by norm_num)
    norm_num [torusRealF] at he
    rw [he]
    have hF:=torusExampleFSL_re_three (torusExampleGSL • z)
    have hG:=torusExampleGSL_side_identity z
    have hdF : Complex.normSq (((torusExampleGSL • z:ℍ):ℂ)+1)≠0:=
      ne_of_gt (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 (torusExampleGSL • z))
    have hdG : Complex.normSq (1-(z:ℂ))≠0:=by
      intro h
      have hi:=congrArg Complex.im (Complex.normSq_eq_zero.mp h)
      simp only [Complex.sub_im,Complex.one_im,Complex.zero_im,UpperHalfPlane.coe_im,zero_sub,neg_eq_zero] at hi
      exact z.im_ne_zero hi
    constructor
    · intro h
      rw [h,sub_self,zero_mul] at hF
      have hx : (torusExampleGSL • z).re+1=0:=by linarith
      rw [hx,zero_mul] at hG
      linarith
    · intro h
      rw [h,mul_zero] at hG
      have hx : (torusExampleGSL • z).re+1=0:=(mul_eq_zero.mp hG).resolve_right hdG
      rw [hx,mul_zero] at hF
      have hxF : (torusExampleFSL • (torusExampleGSL • z)).re-3=0:=
        (mul_eq_zero.mp hF).resolve_right hdF
      linarith
  | succ n ih =>
    obtain ⟨ha,hab,hFb⟩:=torusNielsenEndpoints_order n
    rw [torusNielsenWordSL_succ,mul_smul]
    change torusCircleQ (torusRealF (torusNielsenEndpoints n).1) (torusNielsenEndpoints n).1
      (torusExampleFSL • (torusNielsenWordSL n • z))=0 ↔ _
    have hp : 0<((torusNielsenEndpoints n).1+1)*((torusNielsenEndpoints n).2+1)*
        Complex.normSq (((torusNielsenWordSL n • z:ℍ):ℂ)+1):=
      mul_pos (mul_pos (by linarith) (by linarith))
        (by simpa only [Complex.ofReal_one] using torus_shift_normSq_pos 1 (torusNielsenWordSL n • z))
    have he:=torusExampleFSL_circle_transport _ _ (by linarith : (torusNielsenEndpoints n).1≠ -1)
      (by linarith : (torusNielsenEndpoints n).2≠ -1) (torusNielsenWordSL n • z)
    have hz : torusCircleQ (torusRealF (torusNielsenEndpoints n).1)
        (torusRealF (torusNielsenEndpoints n).2) (torusExampleFSL • (torusNielsenWordSL n • z))=0 ↔
        torusCircleQ (torusNielsenEndpoints n).1 (torusNielsenEndpoints n).2
          (torusNielsenWordSL n • z)=0 := by
      constructor
      · intro h
        rw [h,zero_mul] at he
        linarith
      · intro h
        rw [h,mul_zero] at he
        exact (mul_eq_zero.mp he).resolve_right (ne_of_gt hp)
    simpa only [hFb] using hz.trans (ih z)

theorem torusNielsenQuad_first_side_mem_closure (n : ℕ) (z : ℍ) (hz : torusCircleQ 0 1 z=0) :
    z∈closure (torusNielsenQuad n) := by
  obtain ⟨ha,hab,_⟩:=torusNielsenEndpoints_order n
  rw [torusNielsenQuad,torusIdealQuad_closure _ _ ha hab]
  obtain ⟨hx0,hx1⟩:=torusCircleQ_zero_re 0 1 (by norm_num) z hz
  have hp:=mul_pos (sub_pos.mpr (by linarith : 0<(torusNielsenEndpoints n).1-z.re))
    (sub_pos.mpr (by linarith : 0<(torusNielsenEndpoints n).2-z.re))
  have hq:=mul_pos (sub_pos.mpr (by linarith : 0<(torusNielsenEndpoints n).1-1))
    (sub_pos.mpr hx1)
  have hr:=mul_pos (sub_pos.mpr (by linarith : 0<(torusNielsenEndpoints n).2-1)) hx0
  refine ⟨hz.ge,?_,?_,?_⟩ <;> dsimp [torusCircleQ] at * <;> nlinarith [sq_nonneg z.im]

theorem torusNielsenQuad_last_side_mem_closure (n : ℕ) (z : ℍ)
    (hz : torusCircleQ (torusNielsenEndpoints n).1 (torusNielsenEndpoints n).2 z=0) :
    z∈closure (torusNielsenQuad n) := by
  obtain ⟨ha,hab,_⟩:=torusNielsenEndpoints_order n
  rw [torusNielsenQuad,torusIdealQuad_closure _ _ ha hab]
  obtain ⟨hxa,hxb⟩:=torusCircleQ_zero_re _ _ hab z hz
  have hp:=mul_pos (sub_pos.mpr (by linarith : 0<z.re-1))
    (sub_pos.mpr (by linarith : 0<z.re))
  have hq:=mul_pos (sub_pos.mpr (by linarith : 0<z.re-1)) (sub_pos.mpr hxa)
  have hr:=mul_pos (by linarith : 0<(torusNielsenEndpoints n).1) (sub_pos.mpr hxb)
  refine ⟨?_,?_,hz.ge,?_⟩ <;> dsimp [torusCircleQ] at * <;> nlinarith [sq_nonneg z.im]

theorem torusNielsenWordSL_nontrivial_closed_intersection (n : ℕ) :
    (closure (torusNielsenQuad n)∩
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusNielsenWordSL n)) '' closure (torusNielsenQuad n)).Nontrivial := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.circle (1/2) (1/2) (by norm_num)
  obtain ⟨z,w,hz,hw,hzw⟩:=L.exists_two_points
  have he : {u : ℍ|torusCircleQ 0 1 u=0}=L.carrier:=by
    convert torusCircleQ_zero_carrier 0 1 (by norm_num) using 1;norm_num [L]
  have hzq : torusCircleQ 0 1 z=0:=by rwa [←he] at hz
  have hwq : torusCircleQ 0 1 w=0:=by rwa [←he] at hw
  have hf (u : ℍ) (hu : torusCircleQ 0 1 u=0) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusNielsenWordSL n)) u∈closure (torusNielsenQuad
        n)∩
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusNielsenWordSL
          n)) '' closure (torusNielsenQuad n) :=
    ⟨torusNielsenQuad_last_side_mem_closure n _ ((torusNielsenWordSL_side_zero n u).mpr hu),
      ⟨u,torusNielsenQuad_first_side_mem_closure n u hu,rfl⟩⟩
  exact ⟨_,hf z hzq,_,hf w hwq,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusNielsenWordSL
    n)).injective.ne hzw⟩

theorem torusExampleFSL_cayleyHamilton :
    torusExampleFSL.val*torusExampleFSL.val=
      (2*Real.sqrt 2) • torusExampleFSL.val-1 := by
  have hs : Real.sqrt (2:ℝ)≠0:=by positivity
  have hsq:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [torusExampleFSL,Matrix.mul_apply,Fin.sum_univ_two,Matrix.smul_apply,
      Matrix.sub_apply,Matrix.one_apply]
  all_goals field_simp [hs];nlinarith

def torusTwistTrace (n : ℕ) : ℝ :=
  Matrix.trace (torusExampleFSL^n*torusExampleGSL).val

theorem torusTwistTrace_initial : torusTwistTrace 0=2*Real.sqrt 2 ∧ torusTwistTrace 1=4 := by
  have hs : Real.sqrt (2:ℝ)≠0:=by positivity
  have hsq:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  constructor <;> norm_num [torusTwistTrace,torusExampleFSL,torusExampleGSL,
    Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [hs];nlinarith

theorem torusTwistTrace_recurrence (n : ℕ) :
    torusTwistTrace (n+2)=(2*Real.sqrt 2)*torusTwistTrace (n+1)-torusTwistTrace n := by
  have he : (torusExampleFSL^(n+2)*torusExampleGSL).val=
      (2*Real.sqrt 2) • (torusExampleFSL^(n+1)*torusExampleGSL).val-
        (torusExampleFSL^n*torusExampleGSL).val := by
    rw [show n+2=2+n by omega,pow_add,pow_two,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul,torusExampleFSL_cayleyHamilton,sub_mul,
      smul_mul_assoc,one_mul,sub_mul,smul_mul_assoc]
    congr 1
    simp only [pow_succ',Matrix.SpecialLinearGroup.coe_mul]
  unfold torusTwistTrace
  rw [he,Matrix.trace_sub,Matrix.trace_smul]
  rfl

theorem torusTwistTrace_growing (n : ℕ) :
    2<torusTwistTrace n ∧ torusTwistTrace n<torusTwistTrace (n+1) := by
  have hs : 1<Real.sqrt (2:ℝ):=by
    have hsq:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hp:=Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hs₂ : Real.sqrt (2:ℝ)<2:=by
    have hsq:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hp:=Real.sqrt_nonneg (2:ℝ)
    nlinarith
  induction n with
  | zero => rw [torusTwistTrace_initial.1,torusTwistTrace_initial.2];constructor <;> linarith
  | succ n ih =>
    obtain ⟨h₁,h₂⟩:=ih
    have hstep : torusTwistTrace (n+1)<torusTwistTrace (n+2):=by
      rw [torusTwistTrace_recurrence]
      have hp:=mul_pos (by linarith : 0<2*Real.sqrt 2-2) (by linarith [h₁,h₂] : 0<torusTwistTrace (n+1))
      nlinarith
    exact ⟨h₁.trans h₂,hstep⟩

theorem torusTwistTrace_strictMono : StrictMono torusTwistTrace :=
  strictMono_nat_of_lt_succ (fun n=>(torusTwistTrace_growing n).2)

theorem torusNielsenWordSL_hyperbolic (n : ℕ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n)) := by
  have ht : 4<(Matrix.trace (torusNielsenWordSL n).val)^2:=by
    change 4<(torusTwistTrace (n+2))^2
    nlinarith [(torusTwistTrace_growing (n+2)).1]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSLMobius_ne_one_of_trace_sq_gt_four _ ht)).mpr ht

theorem torusNielsenWordSL_pairwise_nonconjugate :
    Pairwise (fun m n=>¬IsConj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL m))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n))) := by
  intro m n hmn hc
  obtain ⟨g,hg⟩:=isConj_iff.mp hc
  have hh:=congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace hg
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at hh
  have hsq : (torusTwistTrace (m+2))^2=(torusTwistTrace (n+2))^2:=Complex.ofReal_injective hh
  have hp:=(torusTwistTrace_growing (m+2)).1
  have hq:=(torusTwistTrace_growing (n+2)).1
  have he : torusTwistTrace (m+2)=torusTwistTrace (n+2):=by nlinarith
  have hi:=torusTwistTrace_strictMono.injective he
  exact hmn (by omega)
def torusPairSL (b : Bool) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  if b then torusExampleGSL else torusExampleFSL

def torusNativePair (b : Bool) : ℍ≃ᵢℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusPairSL b)

def torusNativePairElement (b : Bool) : torusNativeGroup :=
  ⟨torusNativePair b,by
    cases b <;>apply Subgroup.subset_closure <;>simp [torusNativePair,torusPairSL]⟩

def torusNativeFactorMap (b : Bool) : Multiplicative ℤ→*(ℍ≃ᵢℍ) :=
  zpowersHom _ (torusNativePair b)

def torusNativeFreeLift : Monoid.CoprodI (fun _ : Bool=>Multiplicative ℤ)→*(ℍ≃ᵢℍ) :=
  Monoid.CoprodI.lift torusNativeFactorMap

theorem torusPairSL_trace_squared (b : Bool) : (Matrix.trace (torusPairSL b).val)^2=8 := by
  have hs : (Real.sqrt (2:ℝ))^2=2:=Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt (2:ℝ)≠0:=by positivity
  have hv : (3/Real.sqrt (2:ℝ)+1/Real.sqrt (2:ℝ))^2=8 := by
    field_simp
    nlinarith
  cases b <;> simpa [torusPairSL,torusExampleFSL,torusExampleGSL,Matrix.trace,Fin.sum_univ_two] using hv

theorem torusPairSL_hyperbolic (b : Bool) : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusPairSL b)) := by
  have ht : 4<(Matrix.trace (torusPairSL b).val)^2:=by rw [torusPairSL_trace_squared];norm_num
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSLMobius_ne_one_of_trace_sq_gt_four _ ht)).mpr ht

theorem torusNativeFactorMap_ne_one (b : Bool) (n : Multiplicative ℤ) (hn : n≠1) :
    torusNativeFactorMap b n≠1 := by
  intro he
  let M:=nativeConformalSubgroupMobiusHom torusNativeGroup torusNativeGroup_le_conformal
  have hfull : (torusNativePairElement b)^n.toAdd=1 := by
    apply Subtype.ext
    exact he
  have hm:=congrArg M hfull
  have hpair : M (torusNativePairElement b)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusPairSL
    b) :=
    nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  rw [map_zpow,hpair,map_one] at hm
  have hi:=injective_zpow_iff_not_isOfFinOrder.mpr
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _
      (Or.inr (torusPairSL_hyperbolic b).1))
  have hz : n.toAdd=0:=hi (hm.trans (zpow_zero _).symm)
  exact hn (congrArg Multiplicative.ofAdd hz)

theorem torusNativeFreeLift_range : torusNativeFreeLift.range=torusNativeGroup := by
  rw [torusNativeFreeLift,Monoid.CoprodI.range_eq_iSup,iSup_bool_eq]
  change (zpowersHom _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleGSL)).range⊔
    (zpowersHom _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry torusExampleFSL)).range=_
  rw [Subgroup.range_zpowersHom,Subgroup.range_zpowersHom,sup_comm]
  rw [torusNativeGroup,Subgroup.zpowers_eq_closure,Subgroup.zpowers_eq_closure,
    ←Subgroup.closure_union]
  congr 1

theorem torusNativeFreeLift_injective : Function.Injective torusNativeFreeLift := by
  let R : Bool→Set ℍ:=fun b=>if b then torusGSectorᶜ else torusFSectorᶜ
  have hnon (b : Bool) : (R b).Nonempty := by
    cases b
    · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 2 1 (by norm_num),?_⟩
      change ¬(0<torusCircleQ (-1) 0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 2 1 _) ∧
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 2 1 _).re<1)
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    · refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 (by norm_num),?_⟩
      change ¬(0<torusCircleQ 0 1 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 _) ∧
        -1<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-2) 1 _).re)
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  have hdis : Disjoint torusFSectorᶜ torusGSectorᶜ := by
    apply disjoint_left.mpr
    intro z hF hG
    have hz : z∈torusFSector∪torusGSector:=torus_factor_sectors_cover ▸ mem_univ z
    exact hz.elim hF hG
  have hRdis : Pairwise (fun i j=>Disjoint (R i) (R j)) := by
    intro i j hij
    cases i <;>cases j
    · exact (hij rfl).elim
    · exact hdis
    · exact hdis.symm
    · exact (hij rfl).elim
  have hpp : Pairwise (fun i j=>∀n : Multiplicative ℤ,n≠1→torusNativeFactorMap i n • R j⊆R i) := by
    intro i j hij n hn
    cases i <;>cases j
    · exact (hij rfl).elim
    · rintro z ⟨u,hu,rfl⟩ hF
      have huF : u∈torusFSector := by
        have hu' : u∉torusGSector:=hu
        have hcov : u∈torusFSector∪torusGSector:=torus_factor_sectors_cover ▸ mem_univ u
        exact hcov.resolve_right hu'
      exact disjoint_left.mp (torusFSector_wandering _ ⟨n.toAdd,rfl⟩
        (torusNativeFactorMap_ne_one false n hn)) ⟨u,huF,rfl⟩ hF
    · rintro z ⟨u,hu,rfl⟩ hG
      have huG : u∈torusGSector := by
        have hu' : u∉torusFSector:=hu
        have hcov : u∈torusFSector∪torusGSector:=torus_factor_sectors_cover ▸ mem_univ u
        exact hcov.resolve_left hu'
      exact disjoint_left.mp (torusGSector_wandering _ ⟨n.toAdd,rfl⟩
        (torusNativeFactorMap_ne_one true n hn)) ⟨u,huG,rfl⟩ hG
    · exact (hij rfl).elim
  apply Monoid.CoprodI.lift_injective_of_ping_pong torusNativeFactorMap
    (Or.inr ⟨false,?_⟩) R hnon hRdis hpp
  change (3:Cardinal)≤Cardinal.mk ℤ
  rw [Cardinal.mk_int]
  exact Cardinal.ofNat_le_aleph0

def torusNativeOriginalEquiv : torusNativeGroup≃*torusExampleGroup :=
  (MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry torusNativeGroup
    torusNativeGroup_le_conformal).injective).trans
    (MulEquiv.subgroupCongr torusNativeGroup_original_image)

def torusExamplePairElement (b : Bool) : torusExampleGroup :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusPairSL b),by
    cases b <;>apply Subgroup.subset_closure <;>simp [torusPairSL]⟩

/-- A genuine character of the entire original Mobius group, descended through
faithfulness of its actual hyperbolic-plane action. -/
theorem torusExample_integer_character_exists :
    ∃χ : torusExampleGroup→*Multiplicative ℤ,
      ∀b : Bool,χ (torusExamplePairElement b)=if b then Multiplicative.ofAdd (1:ℤ) else 1 := by
  let e : Monoid.CoprodI (fun _ : Bool=>Multiplicative ℤ)≃*torusExampleGroup :=
    ((MonoidHom.ofInjective torusNativeFreeLift_injective).trans
      (MulEquiv.subgroupCongr torusNativeFreeLift_range)).trans torusNativeOriginalEquiv
  let ψ : Monoid.CoprodI (fun _ : Bool=>Multiplicative ℤ)→*Multiplicative ℤ :=
    Monoid.CoprodI.lift (fun b=>if b then MonoidHom.id _ else 1)
  let χ:=ψ.comp e.symm.toMonoidHom
  refine ⟨χ,?_⟩
  intro b
  have he : e (@Monoid.CoprodI.of Bool (fun _ : Bool=>Multiplicative ℤ) _ b
      (Multiplicative.ofAdd (1:ℤ)))=torusExamplePairElement b := by
    apply Subtype.ext
    change nativeConformalSubgroupMobiusHom torusNativeGroup torusNativeGroup_le_conformal
      ⟨torusNativeFreeLift (Monoid.CoprodI.of (Multiplicative.ofAdd (1:ℤ))),_⟩=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusPairSL b)
    simp only [torusNativeFreeLift,Monoid.CoprodI.lift_of,torusNativeFactorMap,zpowersHom_apply,
      show (Multiplicative.ofAdd (1:ℤ)).toAdd=(1:ℤ) from rfl,zpow_one]
    exact nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  rw [←he]
  change ψ (e.symm (e _))=_
  rw [e.symm_apply_apply]
  simp only [ψ,Monoid.CoprodI.lift_of]
  cases b <;>rfl

/-- In a genuine cyclic group, a value-one integer character proves that
an actual element generates the entire group. -/
theorem cyclic_zpowers_eq_top_of_int_character_one
    {G : Type*} [Group G] [IsCyclic G] (χ : G→*Multiplicative ℤ)
    (g : G) (hg : χ g=Multiplicative.ofAdd (1 : ℤ)) : Subgroup.zpowers g=⊤ := by
  obtain ⟨a,ha⟩ := exists_zpow_surjective G
  obtain ⟨n,hn⟩ := ha g
  let m : ℤ:=(χ a).toAdd
  have hnm : n*m=1 := by
    have hh:=congrArg Multiplicative.toAdd hg
    rw [←hn,map_zpow,toAdd_zpow] at hh
    change n • m=(1 : ℤ) at hh
    simpa [zsmul_eq_mul] using hh
  apply top_unique
  intro b _
  obtain ⟨k,hk⟩ := ha b
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨k*m,?_⟩
  rw [←hn,←hk,←zpow_mul]
  congr 1
  calc
    n*(k*m)=k*(n*m) := by ring
    _=k := by rw [hnm,mul_one]

/-- An actual integer character of value one proves original geometric
primitivity: each actual boundary fixed-point stabilizer is generated by the element. -/
theorem hyperbolic_primitive_of_int_character_one
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (χ : H→*Multiplicative ℤ) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hχ : χ f=Multiplicative.ofAdd (1 : ℤ)) : IsPrimitive H f.val := by
  apply (primitive_iff_of_hyperbolic hf).mpr
  refine ⟨f.property,?_⟩
  intro p hp
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p
  have hKH : K≤H:=fun g hg=>((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p
    g).mp hg).1
  let kf : K:=⟨f.val,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f.val).mpr
    ⟨f.property,hp⟩⟩
  let e : K→*H:=Subgroup.inclusion hKH
  let ψ : K→*Multiplicative ℤ:=χ.comp e
  have : IsCyclic K:=D.stabilizer_isCyclic p
  have hgen : Subgroup.zpowers kf=⊤ :=
    cyclic_zpowers_eq_top_of_int_character_one ψ kf hχ
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr kf.property
  · intro g hg
    have hmem : (⟨g,hg⟩ : K)∈Subgroup.zpowers kf := by rw [hgen];trivial
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩

/-- Every hyperbolic word with exactly one character-unit factor is genuinely
primitive, with no abstract free-word interpretation of primitivity. -/
theorem hyperbolic_twist_word_primitive_of_character
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (χ : H→*Multiplicative ℤ) (f g : H)
    (hfχ : χ f=1) (hgχ : χ g=Multiplicative.ofAdd (1 : ℤ)) (n : ℕ)
    (hhyper : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (f^n*g).val) : IsPrimitive H (f^n*g).val := by
  apply hyperbolic_primitive_of_int_character_one D χ (f^n*g) hhyper
  rw [map_mul,map_pow,hfχ,one_pow,one_mul,hgχ]


/-- The actual matrix word is primitive in the original entire Fuchsian group
whenever it is hyperbolic; the integer character is constructed, not assumed. -/
theorem torusExample_twist_primitive (n : ℕ)
    (hhyper : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusExampleFSL^n*torusExampleGSL))) :
    IsPrimitive torusExampleGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusExampleFSL^n*torusExampleGSL)) := by
  obtain ⟨χ,hχ⟩:=torusExample_integer_character_exists
  let f:=torusExamplePairElement false
  let g:=torusExamplePairElement true
  have hval : (f^n*g).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusExampleFSL^n*torusExampleGSL) := by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      torusExampleFSL)^n*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius torusExampleGSL=_
    rw [map_mul,map_pow]
  rw [←hval]
  apply hyperbolic_twist_word_primitive_of_character torusExampleData.asFuchsianDisc χ f g
  · exact hχ false
  · exact hχ true
  · simpa only [hval] using hhyper


theorem torusNativeOriginalEquiv_action (g : torusNativeGroup) (z : ℍ) :
    let :=torusExampleData.nativeAction
    torusNativeOriginalEquiv g • z=g.val z := by
  let :=torusExampleData.nativeAction
  apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
  rw [←torusExampleData.nativeAction_boundary]
  exact nativeConformalSubgroupMobiusHom_action torusNativeGroup torusNativeGroup_le_conformal g z

theorem torusNielsenQuad_original_fundamental (n : ℕ) :
    let :=torusExampleData.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain torusExampleGroup ℍ MeasureTheory.volume (torusNielsenQuad n) := by
  let :=torusExampleData.nativeAction
  have he (g : torusExampleGroup) (z : ℍ) :
      (Homeomorph.refl ℍ) (g • z)=torusNativeOriginalEquiv.symm g • (Homeomorph.refl ℍ) z := by
    change g • z=(torusNativeOriginalEquiv.symm g).val z
    have h:=torusNativeOriginalEquiv_action (torusNativeOriginalEquiv.symm g) z
    rwa [torusNativeOriginalEquiv.apply_symm_apply] at h
  simpa using _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage torusNativeOriginalEquiv.symm
    (Homeomorph.refl ℍ) he (torusNielsenQuad_fundamental_packing n).1

theorem torusNielsenQuad_original_compact_tiles (n : ℕ) :
    let :=torusExampleData.nativeAction
    ∀K : Set ℍ,IsCompact K→{g : torusExampleGroup|(g • closure (torusNielsenQuad n)∩K).Nonempty}.Finite := by
  let :=torusExampleData.nativeAction
  change ∀K : Set ℍ,IsCompact K→
    {g : torusExampleGroup|(g • closure (torusNielsenQuad n)∩K).Nonempty}.Finite
  intro K hK
  have hf:=((torusNielsenQuad_closed_tiles_locallyFinite n).finite_nonempty_inter_compact hK).image
    torusNativeOriginalEquiv
  apply hf.subset
  rintro g ⟨x,⟨z,hz,rfl⟩,hxK⟩
  refine ⟨torusNativeOriginalEquiv.symm g,⟨g • z,⟨z,hz,?_⟩,hxK⟩,
    torusNativeOriginalEquiv.apply_symm_apply g⟩
  have he:=torusNativeOriginalEquiv_action (torusNativeOriginalEquiv.symm g) z
  rw [torusNativeOriginalEquiv.apply_symm_apply] at he
  exact he.symm

theorem torusNielsenQuad_original_polygon (n : ℕ) :
    IsConvexFuchsianPolygon torusExampleData.cayleyData
      (torusExampleData.cayleyCoordinate '' torusNielsenQuad n) :=
  torusExampleData.cayley_polygon (torusNielsenQuad_original_fundamental n)
    (torusNielsenQuad_hConvex n) (torusNielsenQuad_original_compact_tiles n)

theorem torusNielsenWordSL_mem (n : ℕ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n)∈torusExampleGroup := by
  rw [torusNielsenWordSL,map_mul,map_pow]
  exact torusExampleGroup.mul_mem
    (torusExampleGroup.pow_mem (Subgroup.subset_closure (by left;rfl)) (n+2))
    (Subgroup.subset_closure (by right;rfl))

theorem torusNielsenWordSL_isSimple (n : ℕ) :
    IsSimple torusExampleGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n)) := by
  let :=torusExampleData.nativeAction
  let g : torusExampleGroup:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL
    n),torusNielsenWordSL_mem n⟩
  have hg : g≠1:=by
    intro h
    exact (torusNielsenWordSL_hyperbolic n).1.1 (congrArg Subtype.val h)
  have hn : (closure (torusNielsenQuad n)∩g • closure (torusNielsenQuad n)).Nontrivial:=by
    have he : g • closure (torusNielsenQuad n)=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (torusNielsenWordSL n)) '' closure (torusNielsenQuad n):=by
      apply image_congr
      intro z _
      exact torusExampleData.nativeAction_realSL g (torusNielsenWordSL n) rfl z
    rw [he]
    exact torusNielsenWordSL_nontrivial_closed_intersection n
  let hPoly:=torusNielsenQuad_original_polygon n
  let e:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius torusExampleGroup
  have heg : e g≠1:=fun h=>hg (e.injective (h.trans (map_one e).symm))
  have hn':=torusExampleData.cayley_intersection_nontrivial (torusNielsenQuad n) g hn
  let s : FuchsianPolygonSides torusExampleData.cayleyData
      (torusExampleData.cayleyCoordinate '' torusNielsenQuad n):=
    ⟨_,hPoly.side_of_nontrivial_intersection heg hn'⟩
  have hs : fuchsianSideElement hPoly s=e g:=
    ((hPoly.existsUnique_side_element s.property).choose_spec.2 (e g) ⟨heg,rfl⟩).symm
  have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hPoly s).val:=by
    rw [hs]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (torusNielsenWordSL_hyperbolic n)
  have hsimple:=hPoly.hyperbolic_side_isSimple s hh
  rw [hs] at hsimple
  have hback:=hsimple.conjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  have hgroup : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius torusExampleGroup)=torusExampleGroup:=by
    ext f
    constructor
    · rintro ⟨g,⟨h,hh,hg⟩,hf⟩
      have he : f=h:=by
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹=f at hf
        change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*h*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹=g at hg
        rw [←hf,←hg]
        group
      rwa [he]
    · intro hf
      refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹,⟨f,hf,rfl⟩,?_⟩
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)⁻¹=f
      group
  rw [hgroup] at hback
  convert hback using 1
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n)=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius
  group

theorem torusNielsenWordSL_isPrimitive (n : ℕ) :
    IsPrimitive torusExampleGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL
      n)) :=
  torusExample_twist_primitive (n+2) (torusNielsenWordSL_hyperbolic n)

def torusNielsenWord (n : ℕ) : torusExampleGroup :=
  ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (torusNielsenWordSL n),torusNielsenWordSL_mem n⟩

/--
existential assertion: the actual finitely generated
Fuchsian group has infinitely many mutually nonconjugate primitive simple
hyperbolic elements. Simplicity comes from actual convex fundamental polygons.
-/
theorem exists_fg_fuchsian_group_with_infinite_nonconjugate_primitive_simple_hyperbolics :
    ∃H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,H.FG ∧ Nonempty (FuchsianDisc H) ∧
      ∃u : ℕ→H,(∀n,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (u n).val ∧ IsPrimitive H (u n).val ∧
        IsSimple H (u n).val) ∧
        Pairwise (fun m n=>¬IsConj (u m) (u n)) := by
  refine ⟨torusExampleGroup,torusExampleGroup_finitelyGenerated,⟨torusExampleData.asFuchsianDisc⟩,
    torusNielsenWord,?_,?_⟩
  · intro n
    exact ⟨torusNielsenWordSL_hyperbolic n,torusNielsenWordSL_isPrimitive n,
      torusNielsenWordSL_isSimple n⟩
  · intro m n hmn hc
    obtain ⟨g,hg⟩:=isConj_iff.mp hc
    apply torusNielsenWordSL_pairwise_nonconjugate hmn
    apply isConj_iff.mpr
    refine ⟨g.val,?_⟩
    exact congrArg Subtype.val hg
end LowDimensionalTopology.Geometry.Fuchsian
