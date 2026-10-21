/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralNearestOrbits
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- On a mirror pair with actual squared norm t, the genuine nearest
circle polynomial on the positive ray is an exact nonnegative square. -/
theorem mirror_dihedral_positive_polynomial (w z:ℍ) (t a:ℝ)
    (hwre:w.re= -z.re) (hwim:w.im=z.im) (hn:z.re^2+z.im^2=t) :
    dihedralCirclePolynomial w z (dist w z) a=t*(a-1)^2 := by
  have he:=halfPlane_sphere_coordinate_equation w z (dist w z) rfl
  rw [hwre,hwim] at he
  have hco:w.re*z.re+w.im*Real.cosh (dist w z)*z.im=t:=by
    rw [hwre,hwim]
    nlinarith only [he,hn]
  rw [dihedralCirclePolynomial,hco,hwre,hwim,neg_sq,hn]
  ring

/-- The opposite ray's exact polynomial has the two adjacent lattice
roots one and t squared; these are genuine native Mobius orbit points. -/
theorem mirror_dihedral_negative_polynomial (w z:ℍ) (t a:ℝ)
    (ht:0<t) (hwre:w.re= -z.re) (hwim:w.im=z.im)
    (hn:z.re^2+z.im^2=t) (hx:4*z.re^2=(t-1)^2) :
    dihedralCirclePolynomial w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z) (dist
      w z) a=
      (a-1)*(a-t^2)/t := by
  have he:=halfPlane_sphere_coordinate_equation w z (dist w z) rfl
  rw [hwre,hwim] at he
  have hcy:z.im^2*Real.cosh (dist w z)=t+z.re^2:=by nlinarith only [he,hn]
  obtain ⟨hre,him⟩:=dihedralFlip_coordinates z
  rw [dihedralCirclePolynomial,hwre,hwim,hre,him,hn,neg_sq]
  field_simp
  linear_combination (a^2+t^2)*hn-a*t*hx-2*a*t*hcy

/-- The exact small three-point circle is a genuine nearest circle
for every point of the entire original dihedral lattice. -/
theorem mirror_dihedral_lattice_nearest (w z:ℍ) (t:ℝ)
    (ht:1<t) (hwre:w.re= -z.re) (hwim:w.im=z.im)
    (hn:z.re^2+z.im^2=t) (hx:4*z.re^2=(t-1)^2) (k:ℤ) (b:Bool) :
    dist w z≤dist w (dihedralLatticePoint z (t^2) (by positivity) k b) := by
  have hd:1<t^2:=by nlinarith only [ht]
  let a:ℝ:=(t^2)^k
  have ha:0<a:=zpow_pos (by positivity) k
  have hpoly:0≤dihedralCirclePolynomial w (if b then _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1
    zero_lt_one•z else z)
      (dist w z) a:=by
    cases b
    · change 0≤dihedralCirclePolynomial w z (dist w z) a
      rw [mirror_dihedral_positive_polynomial w z t a hwre hwim hn]
      positivity
    · change 0≤dihedralCirclePolynomial w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1
      zero_lt_one•z) (dist w z) a
      rw [mirror_dihedral_negative_polynomial w z t a (by positivity) hwre hwim hn hx]
      apply div_nonneg _ (by positivity)
      by_cases hk:k≤0
      · have ha1:a≤1:=by simpa only [zpow_zero] using zpow_le_zpow_right₀ hd.le hk
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith only [ha1,hd])
      · have hk1:1≤k:=by omega
        have hda:t^2≤a:=by simpa only [zpow_one] using zpow_le_zpow_right₀ hd.le hk1
        exact mul_nonneg (by linarith only [hda,hd]) (by linarith only [hda])
  rw [dihedralCirclePolynomial_identity _ _ _ a ha] at hpoly
  have hcos:Real.cosh (dist w z)≤Real.cosh
      (dist w (dihedralLatticePoint z (t^2) (by positivity) k b)):=by
    have hp:0<2*w.im*a*(if b then _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z else z).im:=by positivity
    change 0≤2*w.im*a*(if b then _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z else
      z).im*
      (Real.cosh (dist w (dihedralLatticePoint z (t^2) (by positivity) k b))-Real.cosh (dist w z)) at hpoly
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hp).mp hpoly)
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_le_cosh.mp hcos

/-- The nearest circle contains exactly the three actual lattice
points with exponent labels false/zero and true/zero-or-one. -/
theorem mirror_dihedral_lattice_circle_iff (w z:ℍ) (t:ℝ)
    (ht:1<t) (hwre:w.re= -z.re) (hwim:w.im=z.im)
    (hn:z.re^2+z.im^2=t) (hx:4*z.re^2=(t-1)^2) (k:ℤ) (b:Bool) :
    dist w (dihedralLatticePoint z (t^2) (by positivity) k b)=dist w z ↔
      if b then k=0 ∨ k=1 else k=0 := by
  have hd:1<t^2:=by nlinarith only [ht]
  let a:ℝ:=(t^2)^k
  have ha:0<a:=zpow_pos (by positivity) k
  have hiff (v:ℍ):dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL a ha•v)=dist w z ↔
      dihedralCirclePolynomial w v (dist w z) a=0:=by
    constructor
    · exact dihedralCirclePolynomial_root w v (dist w z) a ha
    · intro hp
      rw [dihedralCirclePolynomial_identity w v (dist w z) a ha] at hp
      have hc:Real.cosh (dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL a ha•v))=Real.cosh (dist w z):=by
        have hco:2*w.im*a*v.im≠0:=by positivity
        exact sub_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left hco)
      exact Real.cosh_injOn dist_nonneg dist_nonneg hc
  have ha0:a=1 ↔ k=0:=by
    change (t^2)^k=1 ↔ k=0
    rw [←zpow_zero (t^2)]
    exact (zpow_right_injective₀ (by positivity:t^2>0) hd.ne').eq_iff
  have ha1:a=t^2 ↔ k=1:=by
    change (t^2)^k=t^2 ↔ k=1
    have he:(t^2)^k=(t^2)^(1:ℤ) ↔ k=1:=
      (zpow_right_injective₀ (by positivity:t^2>0) hd.ne').eq_iff
    simpa only [zpow_one] using he
  cases b
  · change dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL a ha•z)=dist w z ↔ k=0
    rw [hiff,mirror_dihedral_positive_polynomial w z t a hwre hwim hn]
    simpa only [mul_eq_zero,ne_of_gt (by positivity:0<t),false_or,sq_eq_zero_iff,
      sub_eq_zero] using ha0
  · change dist w (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL a
    ha•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z))=dist w z ↔ k=0 ∨ k=1
    rw [hiff,mirror_dihedral_negative_polynomial w z t a (by positivity) hwre hwim hn hx]
    have hp:(a-1)*(a-t^2)/t=0 ↔ a=1 ∨ a=t^2:=by
      simp only [div_eq_zero_iff,mul_eq_zero,sub_eq_zero,ne_of_gt (by positivity:0<t),or_false]
    rw [hp,ha0,ha1]

/-- The explicit tiny-dihedral family has positive actual height on
its whole original open parameter interval. -/
theorem tinyDihedral_height_sq_pos (t:ℝ) (ht:1<t) (htu:t<2) :
    0<t-((t-1)/2)^2 := by
  have hsq:((t-1)/2)^2<1/4:=by nlinarith only [ht,htu]
  linarith only [ht,hsq]

def tinyDihedralVertex (t:ℝ) (ht:1<t) (htu:t<2) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe ((t-1)/2) (Real.sqrt (t-((t-1)/2)^2))
    (Real.sqrt_pos.mpr (tinyDihedral_height_sq_pos t ht htu))

def tinyDihedralCenter (t:ℝ) (ht:1<t) (htu:t<2) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-((t-1)/2)) (Real.sqrt (t-((t-1)/2)^2))
    (Real.sqrt_pos.mpr (tinyDihedral_height_sq_pos t ht htu))

theorem tinyDihedralVertex_coordinate_identity (t:ℝ) (ht:1<t) (htu:t<2) :
    (tinyDihedralVertex t ht htu).re^2+(tinyDihedralVertex t ht htu).im^2=t ∧
      4*(tinyDihedralVertex t ht htu).re^2=(t-1)^2 := by
  constructor
  · change ((t-1)/2)^2+(Real.sqrt (t-((t-1)/2)^2))^2=t
    rw [Real.sq_sqrt (tinyDihedral_height_sq_pos t ht htu).le]
    ring
  · change 4*((t-1)/2)^2=(t-1)^2
    ring

/-- Every point of the literal whole dihedral group orbit is at
least as far from the constructed center as the distinguished vertex. -/
theorem tinyDihedral_nearest_orbit (t:ℝ) (ht:1<t) (htu:t<2) (u:ℍ)
    (hu:((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit
      (canonicalDihedralGroup (t^2) (by positivity)) (((tinyDihedralVertex t ht htu:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)≤
      dist (tinyDihedralCenter t ht htu) u := by
  obtain ⟨k,b,rfl⟩:=(canonicalDihedralGroup_orbit_iff (t^2) (by positivity)
    (tinyDihedralVertex t ht htu) u).mp hu
  exact mirror_dihedral_lattice_nearest (tinyDihedralCenter t ht htu)
    (tinyDihedralVertex t ht htu) t ht rfl rfl
    (tinyDihedralVertex_coordinate_identity t ht htu).1
    (tinyDihedralVertex_coordinate_identity t ht htu).2 k b

theorem tinyDihedral_dilation_one (z:ℍ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL 1 zero_lt_one•z=z := by
  apply UpperHalfPlane.ext
  apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re,_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im]

/-- The three actual representatives of the complete nearest circle. -/
def tinyDihedralCyclePoints (t:ℝ) (ht:1<t) (htu:t<2) : Fin 3→ℍ :=
  ![tinyDihedralVertex t ht htu,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•tinyDihedralVertex t ht htu,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (by positivity)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•tinyDihedralVertex t ht htu)]

theorem tinyDihedralCyclePoints_orbit (t:ℝ) (ht:1<t) (htu:t<2) (i:Fin 3) :
    (((tinyDihedralCyclePoints t ht htu
      i:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit
      (canonicalDihedralGroup (t^2) (by positivity)) (((tinyDihedralVertex t ht htu:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  apply (canonicalDihedralGroup_orbit_iff (t^2) (by positivity) _ _).mpr
  fin_cases i
  · refine ⟨0,false,?_⟩
    simp [tinyDihedralCyclePoints,dihedralLatticePoint,tinyDihedral_dilation_one]
  · refine ⟨0,true,?_⟩
    simp [tinyDihedralCyclePoints,dihedralLatticePoint,tinyDihedral_dilation_one]
  · exact ⟨1,true,by simp [tinyDihedralCyclePoints,dihedralLatticePoint]⟩

theorem tinyDihedralCyclePoints_circle (t:ℝ) (ht:1<t) (htu:t<2) (i:Fin 3) :
    dist (tinyDihedralCenter t ht htu) (tinyDihedralCyclePoints t ht htu i)=
      dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu) := by
  have hcircle (k:ℤ) (b:Bool):dist (tinyDihedralCenter t ht htu)
      (dihedralLatticePoint (tinyDihedralVertex t ht htu) (t^2) (by positivity) k b)=
      dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu) ↔
      if b then k=0 ∨ k=1 else k=0:=
    mirror_dihedral_lattice_circle_iff (tinyDihedralCenter t ht htu)
      (tinyDihedralVertex t ht htu) t ht rfl rfl
      (tinyDihedralVertex_coordinate_identity t ht htu).1
      (tinyDihedralVertex_coordinate_identity t ht htu).2 k b
  fin_cases i
  · rfl
  · change dist (tinyDihedralCenter t ht htu)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•tinyDihedralVertex t ht htu)=_
    have h:=(hcircle 0 true).mpr (Or.inl rfl)
    simpa only [dihedralLatticePoint,zpow_zero,ite_true,tinyDihedral_dilation_one] using h
  · change dist (tinyDihedralCenter t ht htu)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (by positivity)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•tinyDihedralVertex t ht htu))=_
    have h:=(hcircle 1 true).mpr (Or.inr rfl)
    simpa only [dihedralLatticePoint,zpow_one,ite_true] using h

theorem tinyDihedralCyclePoints_injective (t:ℝ) (ht:1<t) (htu:t<2) :
    Function.Injective (tinyDihedralCyclePoints t ht htu) := by
  let z:=tinyDihedralVertex t ht htu
  let j:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (by positivity)•j
  have hz:0<z.re:=by change 0<(t-1)/2;linarith only [ht]
  have hj:j.re<0:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 zero_lt_one•z).re<0
    rw [(dihedralFlip_coordinates z).1]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hz) (by positivity)
  have hu:u.re<0:=by
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (by positivity)•j).re<0
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_re]
    exact mul_neg_of_pos_of_neg (by positivity) hj
  have hzj:z≠j:=by
    intro he
    have h:=congrArg UpperHalfPlane.re he
    linarith only [hz,hj,h]
  have hzu:z≠u:=by
    intro he
    have h:=congrArg UpperHalfPlane.re he
    linarith only [hz,hu,h]
  have hju:j≠u:=by
    intro he
    have h:=congrArg UpperHalfPlane.im he
    change j.im=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL (t^2) (by positivity)•j).im at h
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalDilationSL_im] at h
    have hd:1<t^2:=by nlinarith only [ht]
    nlinarith only [h,mul_pos j.im_pos (sub_pos.mpr hd)]
  intro i k he
  fin_cases i <;> fin_cases k <;> first
    | rfl
    | exact False.elim (hzj he)
    | exact False.elim (hzj he.symm)
    | exact False.elim (hzu he)
    | exact False.elim (hzu he.symm)
    | exact False.elim (hju he)
    | exact False.elim (hju he.symm)

/-- The actual complete original dihedral orbit meets its genuine
nearest metric circle in precisely these three physical points. -/
theorem tinyDihedral_nearest_orbit_eq_range (t:ℝ) (ht:1<t) (htu:t<2) :
    {u:ℍ | ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit
      (canonicalDihedralGroup (t^2) (by positivity)) (((tinyDihedralVertex t ht htu:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      dist (tinyDihedralCenter t ht htu) u=
        dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)}=
      Set.range (tinyDihedralCyclePoints t ht htu) := by
  ext u
  constructor
  · rintro ⟨hu,he⟩
    obtain ⟨k,b,rfl⟩:=(canonicalDihedralGroup_orbit_iff (t^2) (by positivity)
      (tinyDihedralVertex t ht htu) u).mp hu
    have hk:if b then k=0 ∨ k=1 else k=0:=
      (mirror_dihedral_lattice_circle_iff (tinyDihedralCenter t ht htu)
        (tinyDihedralVertex t ht htu) t ht rfl rfl
        (tinyDihedralVertex_coordinate_identity t ht htu).1
        (tinyDihedralVertex_coordinate_identity t ht htu).2 k b).mp he
    cases b
    · change k=0 at hk
      subst k
      exact ⟨0,by simp [tinyDihedralCyclePoints,dihedralLatticePoint,tinyDihedral_dilation_one]⟩
    · change k=0 ∨ k=1 at hk
      rcases hk with rfl|rfl
      · exact ⟨1,by simp [tinyDihedralCyclePoints,dihedralLatticePoint,tinyDihedral_dilation_one]⟩
      · exact ⟨2,by simp [tinyDihedralCyclePoints,dihedralLatticePoint]⟩
  · rintro ⟨i,rfl⟩
    exact ⟨tinyDihedralCyclePoints_orbit t ht htu i,tinyDihedralCyclePoints_circle t ht htu i⟩

theorem tinyDihedral_nearest_orbit_card (t:ℝ) (ht:1<t) (htu:t<2) :
    {u:ℍ | ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit
      (canonicalDihedralGroup (t^2) (by positivity)) (((tinyDihedralVertex t ht htu:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      dist (tinyDihedralCenter t ht htu) u=
        dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)}.ncard=3 := by
  rw [tinyDihedral_nearest_orbit_eq_range,
    Set.ncard_range_of_injective (tinyDihedralCyclePoints_injective t ht htu)]
  simp

/-- Both physical points lie strictly in the actual annular packing
for the original dihedral group, rather than on a mirrored boundary. -/
theorem tinyDihedral_vertex_center_annulus (t:ℝ) (ht:1<t) (htu:t<2) :
    (1<‖(tinyDihedralVertex t ht htu:ℂ)‖ ∧ ‖(tinyDihedralVertex t ht htu:ℂ)‖<t) ∧
    (1<‖(tinyDihedralCenter t ht htu:ℂ)‖ ∧ ‖(tinyDihedralCenter t ht htu:ℂ)‖<t) := by
  have hV: (tinyDihedralVertex t ht htu).re^2+(tinyDihedralVertex t ht htu).im^2=t:=
    (tinyDihedralVertex_coordinate_identity t ht htu).1
  have hW:(tinyDihedralCenter t ht htu).re^2+(tinyDihedralCenter t ht htu).im^2=t:=by
    change (-((tinyDihedralVertex t ht htu).re))^2+(tinyDihedralVertex t ht htu).im^2=t
    simpa only [neg_sq] using hV
  have hnorm (v:ℍ) (hv:v.re^2+v.im^2=t):‖(v:ℂ)‖^2=t:=by
    rw [←Complex.normSq_eq_norm_sq]
    simpa only [Complex.normSq_apply,pow_two,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im] using hv
  have hnV:=hnorm _ hV
  have hnW:=hnorm _ hW
  have hb (r:ℝ) (hr:0≤r) (he:r^2=t):1<r ∧ r<t:=by
    have hsq:t<t^2:=by nlinarith only [ht]
    constructor <;> nlinarith only [hr,he,ht,hsq]
  exact ⟨hb _ (norm_nonneg _) hnV,hb _ (norm_nonneg _) hnW⟩

/-- The radius of the explicit genuine three-point nearest family
shrinks to zero as the original parameter tends to one. -/
theorem tinyDihedral_radius_arbitrarily_small (ε:ℝ) (hε:0<ε) :
    ∃t:ℝ,∃ht:1<t,∃htu:t<2,
      dist (tinyDihedralCenter t ht htu) (tinyDihedralVertex t ht htu)<ε := by
  let y:ℝ→ℝ:=fun t=>Real.sqrt (t-((t-1)/2)^2)
  have hy:ContinuousAt y 1:=by fun_prop
  have hpos:y 1>0:=by norm_num [y]
  have hY:∀ᶠt in 𝓝 (1:ℝ),0<y t:=hy.eventually (Ioi_mem_nhds hpos)
  let X:ℝ→ℂ:=fun t=>((t-1)/2:ℝ)+y t*Complex.I
  let W:ℝ→ℂ:=fun t=>(-((t-1)/2):ℝ)+y t*Complex.I
  have hX:ContinuousAt X 1:=by fun_prop
  have hW:ContinuousAt W 1:=by fun_prop
  have htend:Filter.Tendsto (fun t=>dist (UpperHalfPlane.ofComplex (W t))
      (UpperHalfPlane.ofComplex (X t))) (𝓝 (1:ℝ)) (𝓝 (0:ℝ)):=by
    have hx1:0<(X 1).im:=by norm_num [X,y]
    have hw1:0<(W 1).im:=by norm_num [W,y]
    have hxc:ContinuousAt (fun t=>UpperHalfPlane.ofComplex (X t)) 1:=
      (UpperHalfPlane.ofComplex.continuousAt (by
        simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨⟨X 1,hx1⟩,rfl⟩)).comp hX
    have hwc:ContinuousAt (fun t=>UpperHalfPlane.ofComplex (W t)) 1:=
      (UpperHalfPlane.ofComplex.continuousAt (by
        simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
          Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
        exact ⟨⟨W 1,hw1⟩,rfl⟩)).comp hW
    have hd:=hwc.dist hxc
    simpa only [X,W,sub_self,zero_div,neg_zero,Complex.ofReal_zero,zero_add,dist_self] using hd
  have he:∀ᶠt in 𝓝 (1:ℝ),dist (UpperHalfPlane.ofComplex (W t))
      (UpperHalfPlane.ofComplex (X t))<ε:=htend.eventually (Iio_mem_nhds hε)
  have hf:∀ᶠt in 𝓝[>] (1:ℝ),1<t ∧ t<2 ∧ 0<y t ∧
      dist (UpperHalfPlane.ofComplex (W t)) (UpperHalfPlane.ofComplex (X t))<ε:=by
    filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num: (1:ℝ)<2)),
      mem_nhdsWithin_of_mem_nhds hY,mem_nhdsWithin_of_mem_nhds he] with t ht htu hyt het
    exact ⟨ht,htu,hyt,het⟩
  obtain ⟨t,ht,htu,_hyt,het⟩:=hf.exists
  refine ⟨t,ht,htu,?_⟩
  have hw:UpperHalfPlane.ofComplex (W t)=tinyDihedralCenter t ht htu:=by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0<(W t).im by simpa [W,y] using _hyt)]
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [W,y,tinyDihedralCenter,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  have hx:UpperHalfPlane.ofComplex (X t)=tinyDihedralVertex t ht htu:=by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0<(X t).im by simpa [X,y] using _hyt)]
    apply UpperHalfPlane.ext
    apply Complex.ext <;> simp [X,y,tinyDihedralVertex,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  rwa [hw,hx] at het

end LowDimensionalTopology.Geometry.Fuchsian
