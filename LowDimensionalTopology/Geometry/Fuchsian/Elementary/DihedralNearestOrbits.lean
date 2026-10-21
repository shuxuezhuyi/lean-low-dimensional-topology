/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FourCycleGroupAlternatives
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The two distinct real roots of an actual quadratic give its exact
linear and constant coefficients. -/
theorem quadratic_distinct_roots_vieta (a b c x y : ℝ) (hxy : x≠y)
    (hx : a*x^2+b*x+c=0) (hy : a*y^2+b*y+c=0) :
    b= -a*(x+y) ∧ c=a*x*y := by
  have hprod : (x-y)*(a*(x+y)+b)=0:=by nlinarith only [hx,hy]
  have hlin : a*(x+y)+b=0:=(mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hxy)
  refine ⟨by linarith only [hlin],?_⟩
  linear_combination hx-x*hlin

/-- Two nearest geometric-lattice roots are consecutive. An omitted
intermediate exponent would lie strictly inside the genuine conic. -/
theorem geometric_quadratic_nearest_roots_adjacent (a b c d : ℝ)
    (ha : 0<a) (hd : 1<d) (m n : ℤ) (hmn : m<n)
    (hm : a*(d^m)^2+b*d^m+c=0) (hn : a*(d^n)^2+b*d^n+c=0)
    (hnear : ∀k : ℤ,0≤a*(d^k)^2+b*d^k+c) : n=m+1 := by
  have hxy : d^m≠d^n:=ne_of_lt (zpow_lt_zpow_right₀ hd hmn)
  obtain ⟨hb,hc⟩:=quadratic_distinct_roots_vieta a b c (d^m) (d^n) hxy hm hn
  by_contra hnot
  have hmid : m+1<n:=by omega
  have hleft : d^m<d^(m+1):=zpow_lt_zpow_right₀ hd (by omega)
  have hright : d^(m+1)<d^n:=zpow_lt_zpow_right₀ hd hmid
  have hneg : a*(d^(m+1)-d^m)*(d^(m+1)-d^n)<0:=
    mul_neg_of_pos_of_neg (mul_pos ha (sub_pos.mpr hleft)) (sub_neg.mpr hright)
  have hnonneg:=hnear (m+1)
  rw [hb,hc] at hnonneg
  nlinarith only [hneg,hnonneg]

/-- The exact Euclidean conic polynomial of the genuine hyperbolic
circle on one actual positive dilation ray. -/
def dihedralCirclePolynomial (w z : ℍ) (r t : ℝ) : ℝ:=
  (z.re^2+z.im^2)*t^2-2*(w.re*z.re+w.im*Real.cosh r*z.im)*t+(w.re^2+w.im^2)

theorem dihedralCirclePolynomial_identity (w z : ℍ) (r t : ℝ) (ht : 0<t) :
    dihedralCirclePolynomial w z r t=
      2*w.im*t*z.im*(Real.cosh (dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z))-Real.cosh r) := by
  have he:=halfPlane_sphere_coordinate_equation w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL
    t ht•z)
    (dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)) rfl
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im] at he
  dsimp only [dihedralCirclePolynomial]
  nlinarith only [he]

theorem dihedralCirclePolynomial_root (w z : ℍ) (r t : ℝ) (ht : 0<t)
    (hr : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)=r) : dihedralCirclePolynomial w z r t=0 := by
  rw [dihedralCirclePolynomial_identity w z r t ht,hr,sub_self,mul_zero]

theorem dihedralCirclePolynomial_nonneg (w z : ℍ) (r t : ℝ) (ht : 0<t)
    (hr : 0≤r) (hnear : r≤dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)) :
    0≤dihedralCirclePolynomial w z r t := by
  rw [dihedralCirclePolynomial_identity w z r t ht]
  have hc : Real.cosh r≤Real.cosh (dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)):=by
    rw [Real.cosh_le_cosh,abs_of_nonneg hr,abs_of_nonneg dist_nonneg]
    exact hnear
  exact mul_nonneg (by positivity) (sub_nonneg.mpr hc)

/-- The actual nearest-circle lattice points on a genuine hyperbolic
axis orbit are adjacent integer powers of its positive dilation generator. -/
theorem dilation_nearest_circle_exponents_adjacent (w z : ℍ) (r d : ℝ)
    (hd : 1<d) (hr : 0≤r) (m n : ℤ) (hmn : m<n)
    (hm : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^m) (zpow_pos (by linarith) _)•z)=r)
    (hn : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^n) (zpow_pos (by linarith) _)•z)=r)
    (hnear : ∀k : ℤ,r≤dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^k) (zpow_pos (by linarith) _)•z)) : n=m+1 := by
  apply geometric_quadratic_nearest_roots_adjacent (z.re^2+z.im^2)
    (-2*(w.re*z.re+w.im*Real.cosh r*z.im)) (w.re^2+w.im^2) d
    (by nlinarith only [sq_pos_of_pos z.im_pos,sq_nonneg z.re]) hd m n hmn
  · simpa only [dihedralCirclePolynomial,sub_eq_add_neg,neg_mul] using
      dihedralCirclePolynomial_root w z r (d^m) (zpow_pos (by linarith) _) hm
  · simpa only [dihedralCirclePolynomial,sub_eq_add_neg,neg_mul] using
      dihedralCirclePolynomial_root w z r (d^n) (zpow_pos (by linarith) _) hn
  · intro k
    simpa only [dihedralCirclePolynomial,sub_eq_add_neg,neg_mul] using
      dihedralCirclePolynomial_nonneg w z r (d^k) (zpow_pos (by linarith) _) hr (hnear k)

/-- The real and imaginary coordinates of the genuine axis involution. -/
theorem dihedralFlip_coordinates (z : ℍ) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z).re= -z.re/(z.re^2+z.im^2) ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z).im=z.im/(z.re^2+z.im^2) := by
  have h:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe 1 zero_lt_one z
  have hre:=congrArg Complex.re h
  have him:=congrArg Complex.im h
  constructor
  · simpa [Complex.div_re,Complex.normSq_apply,pow_two] using hre
  · simpa [Complex.div_im,Complex.normSq_apply,pow_two,neg_div] using him

/-- Four actual same-circle points from adjacent pairs on the two
geometric-lattice rays force the center onto the actual invariant axis. -/
theorem dihedral_adjacent_four_circle_center (w z : ℍ) (r d t s : ℝ)
    (hd : 1<d) (ht : 0<t) (hs : 0<s) (hz : z.re≠0)
    (h1 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)=r)
    (h2 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t) (mul_pos (by linarith) ht)•z)=r)
    (h3 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL s
      hs•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r)
    (h4 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*s) (mul_pos (by linarith) hs)•
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r) :
    w.re=0 ∧ w.im^2=d*t*s := by
  let N:=z.re^2+z.im^2
  have hN : 0<N:=by dsimp only [N];nlinarith only [sq_nonneg z.re,sq_pos_of_pos z.im_pos]
  have hd0 : 0<d:=by linarith only [hd]
  have htd : t≠d*t:=by nlinarith only [hd,ht]
  have hsd : s≠d*s:=by nlinarith only [hd,hs]
  have hq1:=dihedralCirclePolynomial_root w z r t ht h1
  have hq2:=dihedralCirclePolynomial_root w z r (d*t) (mul_pos hd0 ht) h2
  have hq3:=dihedralCirclePolynomial_root w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1
    zero_lt_one•z) r s hs h3
  have hq4:=dihedralCirclePolynomial_root w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1
    zero_lt_one•z) r (d*s) (mul_pos hd0 hs) h4
  dsimp only [dihedralCirclePolynomial] at hq1 hq2 hq3 hq4
  have hq1' : N*t^2+(-2*(w.re*z.re+w.im*Real.cosh r*z.im))*t+(w.re^2+w.im^2)=0:=by
    dsimp only [N];nlinarith only [hq1]
  have hq2' : N*(d*t)^2+(-2*(w.re*z.re+w.im*Real.cosh r*z.im))*(d*t)+(w.re^2+w.im^2)=0:=by
    dsimp only [N];nlinarith only [hq2]
  obtain ⟨hb1,hc1⟩:=quadratic_distinct_roots_vieta N _ _ t (d*t) htd hq1' hq2'
  rw [(dihedralFlip_coordinates z).1,(dihedralFlip_coordinates z).2] at hq3 hq4
  have hnorm : (-z.re/N)^2+(z.im/N)^2=1/N:=by
    field_simp [hN.ne']
    dsimp only [N]
  have hq3' : ((-z.re/N)^2+(z.im/N)^2)*s^2+
    (-2*(w.re*(-z.re/N)+w.im*Real.cosh r*(z.im/N)))*s+(w.re^2+w.im^2) =0:=by
    dsimp only [N];nlinarith only [hq3]
  have hq4' : ((-z.re/N)^2+(z.im/N)^2)*(d*s)^2+
    (-2*(w.re*(-z.re/N)+w.im*Real.cosh r*(z.im/N)))*(d*s)+(w.re^2+w.im^2) =0:=by
    dsimp only [N];nlinarith only [hq4]
  rw [hnorm] at hq3' hq4'
  obtain ⟨hb2,hc2⟩:=quadratic_distinct_roots_vieta (1/N) _ _ s (d*s) hsd hq3' hq4'
  have hsquare : (N*t)^2=s^2:=by
    apply mul_left_cancel₀ hd0.ne'
    calc
      d*(N*t)^2=N*(w.re^2+w.im^2):=by rw [hc1];ring
      _=d*s^2:=by rw [hc2];field_simp
  have hsN : s=N*t:=by
    nlinarith only [hsquare,hs,mul_pos hN ht]
  have hb2' : -2*(-w.re*z.re+w.im*Real.cosh r*z.im)= -(s+d*s):=by
    have hb:=congrArg (fun x : ℝ=>x*N) hb2
    field_simp [hN.ne'] at hb
    nlinarith only [hb]
  rw [hsN] at hb2'
  have hprod : w.re*z.re=0:=by nlinarith only [hb1,hb2']
  have hwre : w.re=0:=(mul_eq_zero.mp hprod).resolve_right hz
  refine ⟨hwre,?_⟩
  rw [hwre,zero_pow (by norm_num : 2≠0),zero_add] at hc1
  rw [hsN]
  linear_combination hc1

/-- The axis half-turn matrix is exactly the original negative reciprocal
on the full compactified plane, rather than only a coordinate candidate. -/
theorem dihedralFlip_realSL_projection :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one)=fuchsianDihedralFlip := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe,fuchsianDihedralFlip_coe z z.ne_zero]
  norm_num

/-- A center forced by the adjacent-ray circle equations is genuinely
fixed by the corresponding original nonidentity dihedral involution. -/
theorem dihedral_adjacent_four_circle_fixed (w z : ℍ) (r d t s : ℝ)
    (hd : 1<d) (ht : 0<t) (hs : 0<s) (hz : z.re≠0)
    (h1 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL t ht•z)=r)
    (h2 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t) (mul_pos (by linarith) ht)•z)=r)
    (h3 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL s
      hs•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r)
    (h4 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*s) (mul_pos (by linarith) hs)•
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r) :
    let F:=fuchsianPositiveDilation (d*t*s) (mul_pos (mul_pos (by linarith) ht) hs)*fuchsianDihedralFlip
    F.val (w:ℂ)=(w:ℂ) ∧ F≠1 := by
  have hk : 0<d*t*s:=mul_pos (mul_pos (by linarith) ht) hs
  obtain ⟨hw0,hws⟩:=dihedral_adjacent_four_circle_center w z r d t s hd ht hs hz h1 h2 h3 h4
  have hnative : _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t*s) hk•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•w)=w:=by
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t*s)
      hk•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•w)).re=w.re
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,(dihedralFlip_coordinates
        w).1,hw0,neg_zero,zero_div,mul_zero]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t*s)
      hk•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•w)).im=w.im
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im,(dihedralFlip_coordinates w).2,hw0,
        zero_pow (by norm_num : 2≠0),zero_add,←hws]
      field_simp
  dsimp only
  constructor
  · rw [←dihedralFlip_realSL_projection]
    change (fuchsianPositiveDilation (d*t*s) hk*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one)).val (w:ℂ)=_
    rw [show fuchsianPositiveDilation (d*t*s) hk=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d*t*s) hk) from
      (realSLMobius_verticalDilation (d*t*s)
        hk).symm,←map_mul,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,mul_smul,hnative]
  · intro he
    have hi:=congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val ∞) he
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (Units.mk0 ((d*t*s:ℝ):ℂ)
      (Complex.ofReal_ne_zero.mpr hk.ne'))).val
      ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val ∞))=∞ at hi
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero] at hi
    exact OnePoint.coe_ne_infty (0:ℂ) hi

/-- Two genuine adjacent nearest pairs, one on each original lattice ray,
produce a nonidentity element of the same canonical dihedral lattice fixing
the actual circle center. -/
theorem dihedral_four_lattice_circle_fixed (w z : ℍ) (r d : ℝ)
    (hd : 1<d) (hr : 0≤r) (hz : z.re≠0) (m n p q : ℤ)
    (hmn : m<n) (hpq : p<q)
    (h1 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^m) (zpow_pos (by linarith) _)•z)=r)
    (h2 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^n) (zpow_pos (by linarith) _)•z)=r)
    (h3 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^p) (zpow_pos (by linarith) _)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r)
    (h4 : dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^q) (zpow_pos (by linarith) _)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=r)
    (hnear1 : ∀k : ℤ,r≤dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^k) (zpow_pos (by linarith) _)•z))
    (hnear2 : ∀k : ℤ,r≤dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^k) (zpow_pos (by linarith) _)•
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))) :
    ∃k : ℤ, let F:=fuchsianPositiveDilation (d^k) (zpow_pos (by linarith) _)*fuchsianDihedralFlip
      F.val (w:ℂ)=(w:ℂ) ∧ F≠1 := by
  have hd0 : 0<d:=by linarith only [hd]
  have hn:=dilation_nearest_circle_exponents_adjacent w z r d hd hr m n hmn h1 h2 hnear1
  have hq:=dilation_nearest_circle_exponents_adjacent w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z)
    r d hd hr p q hpq h3 h4 hnear2
  have he (j : ℤ) : d^(j+1)=d*d^j:=by rw [zpow_add₀ hd0.ne',zpow_one,mul_comm]
  simp only [hn,he] at h2
  simp only [hq,he] at h4
  have hfixed:=dihedral_adjacent_four_circle_fixed w z r d (d^m) (d^p) hd
    (zpow_pos hd0 _) (zpow_pos hd0 _) hz h1 h2 h3 h4
  have hcoef : d*d^m*d^p=d^(m+p+1):=by
    rw [zpow_add₀ hd0.ne',zpow_add₀ hd0.ne',zpow_one]
    ring
  refine ⟨m+p+1,?_⟩
  simpa only [hcoef] using hfixed

/-- Actual points of the two-ray positive dihedral orbit in the native
half-plane; both branches are genuine real Möbius actions. -/
def dihedralLatticePoint (z : ℍ) (d : ℝ) (hd : 0<d) (n : ℤ) (b : Bool) : ℍ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^n) (zpow_pos hd n)•(if b then
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z else z)

/-- Each actual lattice ray has at most two points on a genuine metric circle. -/
theorem dihedralLatticePoint_circle_three (w z : ℍ) (d : ℝ) (hd : 0<d)
    (r : ℝ) (b : Bool) (m n k : ℤ)
    (hm : dist w (dihedralLatticePoint z d hd m b)=r)
    (hn : dist w (dihedralLatticePoint z d hd n b)=r)
    (hk : dist w (dihedralLatticePoint z d hd k b)=r) :
    dihedralLatticePoint z d hd m b=dihedralLatticePoint z d hd n b ∨
    dihedralLatticePoint z d hd m b=dihedralLatticePoint z d hd k b ∨
    dihedralLatticePoint z d hd n b=dihedralLatticePoint z d hd k b := by
  let v : ℍ:=if b then _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z else z
  have hRay (j : ℤ) : (dihedralLatticePoint z d hd j b).re=
      (v.re/v.im)*(dihedralLatticePoint z d hd j b).im:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^j)
      _•v).re=(v.re/v.im)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^j) _•v).im
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im]
    field_simp
  exact halfPlane_sphere_equal_slope_three w _ _ _ r (v.re/v.im) hm hn hk
    (hRay m) (hRay n) (hRay k)

/-- The finite Boolean partition used to extract the two genuine ray pairs. -/
theorem bool_four_three_or_two_pairs (b : Fin 4→Bool) :
    (∃i j k : Fin 4,i≠j ∧ i≠k ∧ j≠k ∧ b i=b j ∧ b i=b k) ∨
      ∃i j k l : Fin 4,i≠j ∧ k≠l ∧ b i=false ∧ b j=false ∧ b k=true ∧ b l=true := by
  have h : ∀b : Fin 4→Bool,
      (∃i j k : Fin 4,i≠j ∧ i≠k ∧ j≠k ∧ b i=b j ∧ b i=b k) ∨
        ∃i j k l : Fin 4,i≠j ∧ k≠l ∧ b i=false ∧ b j=false ∧ b k=true ∧ b l=true:=by decide
  exact h b

/-- Four distinct actual nearest lattice points on a true metric circle
force a nonidentity member of the same canonical group to fix its center.
The four points may be supplied in any order or ray pattern. -/
theorem dihedral_four_nearest_lattice_points_fixed (w z : ℍ) (d r : ℝ)
    (hd : 1<d) (hr : 0≤r) (hz : z.re≠0) (n : Fin 4→ℤ) (b : Fin 4→Bool)
    (hp : Function.Injective (fun i=>dihedralLatticePoint z d (by linarith) (n i) (b i)))
    (hc : ∀i,dist w (dihedralLatticePoint z d (by linarith) (n i) (b i))=r)
    (hnear : ∀k : ℤ,∀a : Bool,r≤dist w (dihedralLatticePoint z d (by linarith) k a)) :
    ∃k : ℤ, let F:=fuchsianPositiveDilation (d^k) (zpow_pos (by linarith) _)*fuchsianDihedralFlip
      F.val (w:ℂ)=(w:ℂ) ∧ F≠1 := by
  have hd0 : 0<d:=by linarith only [hd]
  rcases bool_four_three_or_two_pairs b with ⟨i,j,k,hij,hik,hjk,hbij,hbik⟩|
    ⟨i,j,k,l,hij,hkl,hi,hj,hk,hl⟩
  · have hh:=dihedralLatticePoint_circle_three w z d hd0 r (b i) (n i) (n j) (n k)
      (hc i) (by simpa only [hbij] using hc j) (by simpa only [hbik] using hc k)
    have hh' : dihedralLatticePoint z d hd0 (n i) (b i)=dihedralLatticePoint z d hd0 (n j) (b j) ∨
        dihedralLatticePoint z d hd0 (n i) (b i)=dihedralLatticePoint z d hd0 (n k) (b k) ∨
        dihedralLatticePoint z d hd0 (n j) (b j)=dihedralLatticePoint z d hd0 (n k) (b k):=by
      simpa only [←hbij,←hbik] using hh
    rcases hh' with he|he|he
    · exact (hij (hp he)).elim
    · exact (hik (hp he)).elim
    · exact (hjk (hp he)).elim
  · have hmn : n i≠n j:=by
      intro he
      apply hij
      apply hp
      simp only [dihedralLatticePoint,hi,hj,he]
    have hpq : n k≠n l:=by
      intro he
      apply hkl
      apply hp
      simp only [dihedralLatticePoint,hk,hl,he]
    have hmain (a0 a1 a2 a3 : Fin 4) (ha : b a0=false) (hb : b a1=false)
        (hc' : b a2=true) (he : b a3=true) (hab : n a0<n a1) (hce : n a2<n a3) :=
      dihedral_four_lattice_circle_fixed w z r d hd hr hz (n a0) (n a1) (n a2) (n a3) hab hce
        (by simpa [dihedralLatticePoint,ha] using hc a0)
        (by simpa [dihedralLatticePoint,hb] using hc a1)
        (by simpa [dihedralLatticePoint,hc'] using hc a2)
        (by simpa [dihedralLatticePoint,he] using hc a3)
        (by intro u;simpa [dihedralLatticePoint] using hnear u false)
        (by intro u;simpa [dihedralLatticePoint] using hnear u true)
    rcases lt_or_gt_of_ne hmn with hmn|hmn <;> rcases lt_or_gt_of_ne hpq with hpq|hpq
    · exact hmain i j k l hi hj hk hl hmn hpq
    · exact hmain i j l k hi hj hl hk hmn hpq
    · exact hmain j i k l hj hi hk hl hmn hpq
    · exact hmain j i l k hj hi hl hk hmn hpq

/-- The original negative reciprocal reverses every actual scaling. -/
theorem dihedralFlip_scaling_relation (a : ℂˣ) :
    fuchsianDihedralFlip*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a)⁻¹*fuchsianDihedralFlip := by
  rw [fuchsianDihedralFlip,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv,mul_assoc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mul_scaling,
    ←mul_assoc,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul,←mul_assoc,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul]
  rw [mul_comm (-1:ℂˣ) a⁻¹]

/-- The original negative reciprocal has genuine order two. -/
theorem dihedralFlip_square : fuchsianDihedralFlip*fuchsianDihedralFlip=1 := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_endpoint_exchange_square
  · change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val (0:ℂ))=∞
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_zero,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
  · change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal.val ∞)=(0:ℂ)
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_infty,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero]

/-- The two actual word families exhaust a group generated by a scaling
and an involution reversing it. -/
theorem dihedral_closure_mem_normal_form {G : Type*} [Group G] (S J : G)
    (hJ : J*J=1) (hrel : J*S=S⁻¹*J) (f : G)
    (hf : f∈Subgroup.closure ({S,J}:Set G)) : ∃n : ℤ,f=S^n ∨ f=S^n*J := by
  have hJi : J⁻¹=J:=inv_eq_of_mul_eq_one_left hJ
  have hconj : J*S*J⁻¹=S⁻¹:=by rw [hrel,mul_assoc,mul_inv_cancel,mul_one]
  have hmove (n : ℤ) : J*S^n=S^(-n)*J:=by
    have he:=map_zpow (MulAut.conj J) S n
    change J*S^n*J⁻¹=(J*S*J⁻¹)^n at he
    rw [hconj,inv_zpow,←zpow_neg] at he
    calc
      J*S^n=(J*S^n*J⁻¹)*J:=by group
      _=S^(-n)*J:=by rw [he]
  let K : Subgroup G:={
    carrier:={a | ∃n : ℤ,a=S^n ∨ a=S^n*J}
    one_mem':=⟨0,Or.inl (zpow_zero S).symm⟩
    mul_mem':=by
      intro a b ha hb
      rcases ha with ⟨m,rfl|rfl⟩ <;> rcases hb with ⟨n,rfl|rfl⟩
      · exact ⟨m+n,Or.inl (zpow_add S m n).symm⟩
      · exact ⟨m+n,Or.inr (by rw [←mul_assoc,←zpow_add])⟩
      · refine ⟨m-n,Or.inr ?_⟩
        rw [mul_assoc,hmove,←mul_assoc,←zpow_add]
        congr 2
      · refine ⟨m-n,Or.inl ?_⟩
        calc
          (S^m*J)*(S^n*J)=S^m*(J*S^n)*J:=by group
          _=(S^m*S^(-n))*(J*J):=by rw [hmove];group
          _=S^(m-n):=by rw [hJ,mul_one,←zpow_add];congr 1
    inv_mem':=by
      intro a ha
      rcases ha with ⟨n,rfl|rfl⟩
      · exact ⟨-n,Or.inl (zpow_neg S n).symm⟩
      · refine ⟨n,Or.inr ?_⟩
        rw [mul_inv_rev,hJi,←zpow_neg,hmove,neg_neg] }
  have hle : Subgroup.closure ({S,J}:Set G)≤K:=by
    apply (Subgroup.closure_le _).mpr
    intro a ha
    rcases ha with rfl|rfl
    · exact ⟨1,Or.inl (zpow_one _).symm⟩
    · exact ⟨0,Or.inr (by rw [zpow_zero,one_mul])⟩
  exact hle hf

/-- Positive real parameters intertwine every actual integer group power. -/
theorem fuchsianPositiveDilation_zpow (d : ℝ) (hd : 0<d) (k : ℤ) :
    fuchsianPositiveDilation (d^k) (zpow_pos hd k)=(fuchsianPositiveDilation d hd)^k := by
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom (Units.mk0 (((d^k:ℝ):ℂ))
    _)=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScalingHom (Units.mk0 (d:ℂ) _))^k
  rw [←map_zpow]
  congr 1
  apply Units.ext
  simp only [Units.val_mk0,Units.val_zpow_eq_zpow_val,Complex.ofReal_zpow]

/-- The canonical group uses the literal two original Möbius generators. -/
def canonicalDihedralGroup (d : ℝ) (hd :
  0<d) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  Subgroup.closure ({fuchsianPositiveDilation d hd,fuchsianDihedralFlip}:Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem canonicalDihedralGroup_mem_iff (d : ℝ) (hd : 0<d) (f :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    f∈canonicalDihedralGroup d hd ↔ ∃n : ℤ,
      f=fuchsianPositiveDilation (d^n) (zpow_pos hd n) ∨
      f=fuchsianPositiveDilation (d^n) (zpow_pos hd n)*fuchsianDihedralFlip := by
  constructor
  · intro hf
    have hrel : fuchsianDihedralFlip*fuchsianPositiveDilation d hd=
        (fuchsianPositiveDilation d hd)⁻¹*fuchsianDihedralFlip:=
      dihedralFlip_scaling_relation _
    obtain ⟨n,hn⟩:=dihedral_closure_mem_normal_form (fuchsianPositiveDilation d hd)
      fuchsianDihedralFlip dihedralFlip_square hrel f hf
    refine ⟨n,?_⟩
    rw [fuchsianPositiveDilation_zpow d hd n]
    exact hn
  · rintro ⟨n,rfl|rfl⟩
    · rw [fuchsianPositiveDilation_zpow d hd n]
      exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n
    · rw [fuchsianPositiveDilation_zpow d hd n]
      exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) n)
        (Subgroup.subset_closure (by simp))

/-- The actual compactified-plane orbit of the canonical group is exactly
the pair of genuine native half-plane lattice rays. -/
theorem canonicalDihedralGroup_orbit_iff (d : ℝ) (hd : 0<d) (z u : ℍ) :
    ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit (canonicalDihedralGroup d
      hd) ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔
      ∃n : ℤ, ∃b : Bool,u=dihedralLatticePoint z d hd n b := by
  have hproj (n : ℤ) : fuchsianPositiveDilation (d^n) (zpow_pos hd n)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (d^n) (zpow_pos hd n)):=
    (realSLMobius_verticalDilation _ _).symm
  constructor
  · rintro ⟨f,he⟩
    change f.val.val (z:ℂ)=(u:ℂ) at he
    obtain ⟨n,hf|hf⟩:=(canonicalDihedralGroup_mem_iff d hd f.val).mp f.property
    · refine ⟨n,false,?_⟩
      apply UpperHalfPlane.ext
      apply OnePoint.coe_injective
      rw [hf,hproj n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action] at he
      exact he.symm
    · refine ⟨n,true,?_⟩
      apply UpperHalfPlane.ext
      apply OnePoint.coe_injective
      rw [hf,hproj n,←dihedralFlip_realSL_projection,←map_mul,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,mul_smul] at he
      exact he.symm
  · rintro ⟨n,b,rfl⟩
    cases b
    · refine ⟨⟨fuchsianPositiveDilation (d^n) (zpow_pos hd n),
        (canonicalDihedralGroup_mem_iff d hd _).mpr ⟨n,Or.inl rfl⟩⟩,?_⟩
      change (fuchsianPositiveDilation (d^n) (zpow_pos hd n)).val (z:ℂ)=
        ((dihedralLatticePoint z d hd n false:ℍ):ℂ)
      rw [hproj n,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
      rfl
    · refine ⟨⟨fuchsianPositiveDilation (d^n) (zpow_pos hd n)*fuchsianDihedralFlip,
        (canonicalDihedralGroup_mem_iff d hd _).mpr ⟨n,Or.inr rfl⟩⟩,?_⟩
      change (fuchsianPositiveDilation (d^n) (zpow_pos hd n)*fuchsianDihedralFlip).val (z:ℂ)=
        ((dihedralLatticePoint z d hd n true:ℍ):ℂ)
      rw [hproj n,←dihedralFlip_realSL_projection,←map_mul,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,mul_smul]
      rfl

/-- The degenerate imaginary-axis orbit still cannot contribute three
 distinct points of a genuine metric circle. -/
theorem dihedralLatticePoint_axis_three (w z : ℍ) (d : ℝ) (hd : 0<d)
    (hz : z.re=0) (r : ℝ) (n : Fin 3→ℤ) (b : Fin 3→Bool)
    (hc : ∀i,dist w (dihedralLatticePoint z d hd (n i) (b i))=r) :
    dihedralLatticePoint z d hd (n 0) (b 0)=dihedralLatticePoint z d hd (n 1) (b 1) ∨
    dihedralLatticePoint z d hd (n 0) (b 0)=dihedralLatticePoint z d hd (n 2) (b 2) ∨
    dihedralLatticePoint z d hd (n 1) (b 1)=dihedralLatticePoint z d hd (n 2) (b 2) := by
  have hreal (i : Fin 3) : (dihedralLatticePoint z d hd (n i) (b i)).re=0:=by
    dsimp only [dihedralLatticePoint]
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re]
    cases h : b i
    · simp only [Bool.false_eq_true,ite_false,hz,mul_zero]
    · simp only [ite_true]
      rw [(dihedralFlip_coordinates z).1,hz,neg_zero,zero_div,mul_zero]
  exact halfPlane_sphere_equal_slope_three w _ _ _ r 0 (hc 0) (hc 1) (hc 2)
    (by simpa only [zero_mul] using hreal 0)
    (by simpa only [zero_mul] using hreal 1)
    (by simpa only [zero_mul] using hreal 2)

/-- Four distinct nearest orbit points force a true stabilizer even when
 the original point lies on the canonical axis. -/
theorem dihedral_four_nearest_lattice_points_fixed_unconditional (w z : ℍ) (d r : ℝ)
    (hd : 1<d) (hr : 0≤r) (n : Fin 4→ℤ) (b : Fin 4→Bool)
    (hp : Function.Injective (fun i=>dihedralLatticePoint z d (by linarith) (n i) (b i)))
    (hc : ∀i,dist w (dihedralLatticePoint z d (by linarith) (n i) (b i))=r)
    (hnear : ∀k : ℤ,∀a : Bool,r≤dist w (dihedralLatticePoint z d (by linarith) k a)) :
    ∃k : ℤ, let F:=fuchsianPositiveDilation (d^k) (zpow_pos (by linarith) _)*fuchsianDihedralFlip
      F.val (w:ℂ)=(w:ℂ) ∧ F≠1 := by
  by_cases hz : z.re=0
  · have hh:=dihedralLatticePoint_axis_three w z d (by linarith) hz r
      (fun i=>n i.castSucc) (fun i=>b i.castSucc) (fun i=>hc i.castSucc)
    rcases hh with hh|hh|hh
    · exact (by have he:=hp hh; norm_num at he : False).elim
    · exact (by have he:=hp hh; norm_num at he : False).elim
    · exact (by have he:=hp hh; norm_num at he : False).elim
  · exact dihedral_four_nearest_lattice_points_fixed w z d r hd hr hz n b hp hc hnear

/-- A free actual center has no four distinct nearest points from one
 original orbit of the canonical infinite dihedral group. -/
theorem canonicalDihedralGroup_no_four_nearest (d : ℝ) (hd : 1<d)
    (w z : ℍ) (r : ℝ) (hr : 0≤r) (p : Fin 4→ℍ) (hp : Function.Injective p)
    (hc : ∀i,dist w (p i)=r)
    (ho : ∀i,((p i:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈
      MulAction.orbit (canonicalDihedralGroup d (by linarith)) ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hnear : ∀u : ℍ,((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈
      MulAction.orbit (canonicalDihedralGroup d (by linarith)) ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) → r ≤ dist w u)
    (hfree : ∀f∈canonicalDihedralGroup d (by linarith),
      f.val ((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→f=1) : False := by
  have hd0 : 0<d:=by linarith only [hd]
  have hx : ∀i,∃n : ℤ,∃b : Bool,p i=dihedralLatticePoint z d hd0 n b:=by
    intro i
    exact (canonicalDihedralGroup_orbit_iff d hd0 z (p i)).mp (ho i)
  choose n b hnb using hx
  have hinj : Function.Injective (fun i=>dihedralLatticePoint z d hd0 (n i) (b i)):=by
    intro i j hij
    apply hp
    simpa only [←hnb] using hij
  obtain ⟨k,hfix,hne⟩:=dihedral_four_nearest_lattice_points_fixed_unconditional w z d r hd hr n b hinj
    (by intro i;simpa only [←hnb] using hc i)
    (by intro k a;exact hnear _ ((canonicalDihedralGroup_orbit_iff d hd0 z _).mpr ⟨k,a,rfl⟩))
  exact hne (hfree _ ((canonicalDihedralGroup_mem_iff d hd0 _).mpr ⟨k,Or.inr rfl⟩) hfix)

end LowDimensionalTopology.Geometry.Fuchsian
