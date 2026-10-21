/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.NonEllipticMaximumDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.CollinearHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HorocyclicRegions
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveEllipticAngles
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.EllipticProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.AngleParallelism
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.AngularMeasure
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticCenterMinimum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.CommutatorGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairReflectionGroups
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleAngleSum
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticPairSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleDisplacementSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleIntegralDiscreteness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set InnerProductGeometry
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

def ellipticTriangleRatio (x y z : ℝ) : ℝ :=
  (x^2+y^2+z^2+2*x*y*z-1)/(2+2*z-(x-y)^2)

theorem ellipticTriangleRatio_denominator_pos {x y z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hz : 0≤z) :
    0<2+2*z-(x-y)^2 := by
  have hd : (x-y)^2≤1 := by
    nlinarith only [sq_nonneg (1-(x-y)),sq_nonneg (1+(x-y)),
      mul_nonneg (by linarith only [hx.1,hy.2] : 0≤1+(x-y))
        (by linarith only [hx.2,hy.1] : 0≤1-(x-y))]
  linarith only [hd,hz]

theorem ellipticTriangleRatio_swap (x y z : ℝ) :
    ellipticTriangleRatio x y z=ellipticTriangleRatio y x z := by
  unfold ellipticTriangleRatio
  congr 1 <;> ring

theorem ellipticTriangleRatio_mono_first {x X y z : ℝ}
    (hx : x∈Icc 0 1) (hX : X∈Icc 0 1) (hy : y∈Icc 0 1)
    (hz : z∈Icc 0 1) (hxX : x≤X) :
    ellipticTriangleRatio x y z≤ellipticTriangleRatio X y z := by
  unfold ellipticTriangleRatio
  apply (div_le_div_iff₀
    (ellipticTriangleRatio_denominator_pos hx hy hz.1)
    (ellipticTriangleRatio_denominator_pos hX hy hz.1)).mpr
  have hy2 : 0≤1-y^2 := by nlinarith only [hy.1,hy.2]
  have hx0:=hx.1
  have hX0:=hX.1
  have hy0:=hy.1
  have hz0:=hz.1
  have hdiff : 0≤X-x := sub_nonneg.mpr hxX
  have hprod : 0≤(X-x)*(z+1)*
      ((X+x)*(z+1)+2*y*(X*x+(1-y^2)+z)) := by positivity
  nlinarith only [hprod]

theorem ellipticTriangleRatio_mono_second {x y Y z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hY : Y∈Icc 0 1)
    (hz : z∈Icc 0 1) (hyY : y≤Y) :
    ellipticTriangleRatio x y z≤ellipticTriangleRatio x Y z := by
  rw [ellipticTriangleRatio_swap x y,ellipticTriangleRatio_swap x Y]
  exact ellipticTriangleRatio_mono_first hy hY hx hz hyY

theorem ellipticTriangleRatio_mono_third {x y z Z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1)
    (hz : z∈Icc 0 1) (hZ : Z∈Icc 0 1) (hzZ : z≤Z) :
    ellipticTriangleRatio x y z≤ellipticTriangleRatio x y Z := by
  unfold ellipticTriangleRatio
  apply (div_le_div_iff₀
    (ellipticTriangleRatio_denominator_pos hx hy hz.1)
    (ellipticTriangleRatio_denominator_pos hx hy hZ.1)).mpr
  have hx2 : 0≤1-x^2 := by nlinarith only [hx.1,hx.2]
  have hy2 : 0≤1-y^2 := by nlinarith only [hy.1,hy.2]
  have hx0:=hx.1
  have hy0:=hy.1
  have hz0:=hz.1
  have hZ0:=hZ.1
  have hdiff : 0≤Z-z := sub_nonneg.mpr hzZ
  have hprod : 0≤(Z-z)*
      (((z+x*y)+(Z+x*y))*((1-x^2)+(1-y^2))+
        2*(z+x*y)*(Z+x*y)+2*(1-x^2)*(1-y^2)) := by positivity
  nlinarith only [hprod]

theorem ellipticTriangleRatio_mono {x y z X Y Z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hz : z∈Icc 0 1)
    (hX : X∈Icc 0 1) (hY : Y∈Icc 0 1) (hZ : Z∈Icc 0 1)
    (hxX : x≤X) (hyY : y≤Y) (hzZ : z≤Z) :
    ellipticTriangleRatio x y z≤ellipticTriangleRatio X Y Z :=
  (ellipticTriangleRatio_mono_first hx hX hy hz hxX).trans
    ((ellipticTriangleRatio_mono_second hX hy hY hz hyY).trans
      (ellipticTriangleRatio_mono_third hX hY hz hZ hzZ))

def EllipticTriangleRatiosBoundedBelow (b x y z : ℝ) : Prop :=
  b≤ellipticTriangleRatio x y z ∧ b≤ellipticTriangleRatio x z y ∧
    b≤ellipticTriangleRatio y z x

theorem ellipticTriangleRatiosBoundedBelow_swap {b x y z : ℝ} :
    EllipticTriangleRatiosBoundedBelow b x y z ↔
      EllipticTriangleRatiosBoundedBelow b y x z := by
  simp only [EllipticTriangleRatiosBoundedBelow,ellipticTriangleRatio_swap y x]
  tauto

theorem ellipticTriangleRatiosBoundedBelow_cycle {b x y z : ℝ} :
    EllipticTriangleRatiosBoundedBelow b x y z ↔
      EllipticTriangleRatiosBoundedBelow b y z x := by
  simp only [EllipticTriangleRatiosBoundedBelow,ellipticTriangleRatio_swap z x,
    ellipticTriangleRatio_swap y x]
  tauto

theorem ellipticTriangleRatiosBoundedBelow_mono {b x y z X Y Z : ℝ}
    (h : EllipticTriangleRatiosBoundedBelow b x y z)
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hz : z∈Icc 0 1)
    (hX : X∈Icc 0 1) (hY : Y∈Icc 0 1) (hZ : Z∈Icc 0 1)
    (hxX : x≤X) (hyY : y≤Y) (hzZ : z≤Z) :
    EllipticTriangleRatiosBoundedBelow b X Y Z :=
  ⟨h.1.trans (ellipticTriangleRatio_mono hx hy hz hX hY hZ hxX hyY hzZ),
    h.2.1.trans (ellipticTriangleRatio_mono hx hz hy hX hZ hY hxX hzZ hyY),
    h.2.2.trans (ellipticTriangleRatio_mono hy hz hx hY hZ hX hyY hzZ hxX)⟩

theorem ellipticTriangleSharpSquare_le_one_div_thirty_two :
    (4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7)≤1/32 := by
  let c:=Real.cos (Real.pi/7)
  have hc6 : Real.sqrt 3/2≤c := by
    rw [←Real.cos_pi_div_six]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith only [Real.pi_pos]
  have hc8 : c≤Real.sqrt (2+Real.sqrt 2)/2 := by
    rw [←Real.cos_pi_div_eight]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith only [Real.pi_pos]
  have hs3:=Real.sq_sqrt (by norm_num : (0:ℝ)≤3)
  have hs2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs3n:=Real.sqrt_nonneg (3:ℝ)
  have hs2n:=Real.sqrt_nonneg (2:ℝ)
  have hlow : (6:ℝ)/7≤c := by nlinarith only [hc6,hs3,hs3n]
  have hs2u : Real.sqrt 2≤(10:ℝ)/7 := by nlinarith only [hs2,hs2n]
  have hroot:=Real.sq_sqrt (by positivity : (0:ℝ)≤2+Real.sqrt 2)
  have hc0 : 0≤c := by linarith only [hlow]
  have hc2 : c^2≤(6:ℝ)/7 := by
    nlinarith only [hc8,hc0,hroot,Real.sqrt_nonneg (2+Real.sqrt 2),hs2u]
  change (4*c^2-3)/(8*c+7)≤1/32
  apply (div_le_iff₀ (by positivity : 0<8*c+7)).mpr
  nlinarith only [hc2,hlow]

theorem ellipticTriangleSharpSquare_eq_two_three_seven :
    ellipticTriangleRatio 0 (1/2) (Real.cos (Real.pi/7))=
      (4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7) := by
  unfold ellipticTriangleRatio
  rw [show (0:ℝ)^2+(1/2)^2+Real.cos (Real.pi/7)^2+
      2*0*(1/2)*Real.cos (Real.pi/7)-1=(4*Real.cos (Real.pi/7)^2-3)/4 by ring,
    show (2:ℝ)+2*Real.cos (Real.pi/7)-(0-1/2)^2=
      (8*Real.cos (Real.pi/7)+7)/4 by ring]
  simp only [div_div_div_cancel_right₀ (by norm_num : (4:ℝ)≠0)]

theorem ellipticTriangleSharpSquare_two_three_seven :
    EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      0 (1/2) (Real.cos (Real.pi/7)) := by
  let c:=Real.cos (Real.pi/7)
  have hc : c∈Icc 0 1 :=
    ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      (by linarith only [Real.pi_pos])
      (by linarith only [Real.pi_pos]),Real.cos_le_one _⟩
  have hc6 : Real.cos (Real.pi/6)≤c := by
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith only [Real.pi_pos]
  have hc3 : (1:ℝ)/2≤c := by
    rw [←Real.cos_pi_div_three]
    apply Real.cos_le_cos_of_nonneg_of_le_pi <;> linarith only [Real.pi_pos]
  have hnum : 0≤c^2-3/4 := by
    have hh:=Real.sq_cos_pi_div_six
    have hp : 0≤Real.cos (Real.pi/6) := by rw [Real.cos_pi_div_six];positivity
    nlinarith only [hh,hc6,hp,hc.1]
  rw [←ellipticTriangleSharpSquare_eq_two_three_seven]
  refine ⟨le_rfl,?_,?_⟩
  · unfold ellipticTriangleRatio
    apply (div_le_div_iff₀
      (ellipticTriangleRatio_denominator_pos (by norm_num) (by norm_num) hc.1)
      (ellipticTriangleRatio_denominator_pos (by norm_num) hc (by norm_num))).mpr
    have hh : 0≤(c^2-3/4)*(c-1/2)*(c+5/2) := by
      exact mul_nonneg (mul_nonneg hnum (sub_nonneg.mpr hc3)) (by positivity)
    nlinarith only [hh]
  · unfold ellipticTriangleRatio
    apply (div_le_div_iff₀
      (ellipticTriangleRatio_denominator_pos (by norm_num) (by norm_num) hc.1)
      (ellipticTriangleRatio_denominator_pos (by norm_num) hc (by norm_num))).mpr
    have hh : 0≤(c^2-3/4)*(c+c^2) := mul_nonneg hnum (by positivity)
    nlinarith only [hh]

theorem ellipticTriangleRatio_ge_one_div_thirty_two {x y z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hz : z∈Icc 0 1)
    (hN : (1:ℝ)/8≤x^2+y^2+z^2+2*x*y*z-1) :
    1/32≤ellipticTriangleRatio x y z := by
  unfold ellipticTriangleRatio
  apply (le_div_iff₀ (ellipticTriangleRatio_denominator_pos hx hy hz.1)).mpr
  nlinarith only [hN,hz.2,sq_nonneg (x-y)]

theorem ellipticTriangleRatiosBoundedBelow_of_numerator {x y z : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (hz : z∈Icc 0 1)
    (hN : (1:ℝ)/8≤x^2+y^2+z^2+2*x*y*z-1) :
    EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7)) x y z := by
  refine ⟨ellipticTriangleSharpSquare_le_one_div_thirty_two.trans
    (ellipticTriangleRatio_ge_one_div_thirty_two hx hy hz hN),
    ellipticTriangleSharpSquare_le_one_div_thirty_two.trans
    (ellipticTriangleRatio_ge_one_div_thirty_two hx hz hy ?_),
    ellipticTriangleSharpSquare_le_one_div_thirty_two.trans
    (ellipticTriangleRatio_ge_one_div_thirty_two hy hz hx ?_)⟩ <;>
      nlinarith only [hN]

theorem ellipticTriangleSharpSquare_two_four_five :
    EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      0 (Real.cos (Real.pi/4)) (Real.cos (Real.pi/5)) := by
  have hs2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs5:=Real.sq_sqrt (by norm_num : (0:ℝ)≤5)
  have hs2n:=Real.sqrt_nonneg (2:ℝ)
  have hs5n:=Real.sqrt_nonneg (5:ℝ)
  have hs2u : Real.sqrt 2≤2 := by nlinarith only [hs2,hs2n]
  have hs5u : Real.sqrt 5≤3 := by nlinarith only [hs5,hs5n]
  apply ellipticTriangleRatiosBoundedBelow_of_numerator
    (by norm_num)
    (by rw [Real.cos_pi_div_four];constructor <;> linarith only [hs2n,hs2u])
    (by rw [Real.cos_pi_div_five];constructor <;> linarith only [hs5n,hs5u])
  rw [Real.cos_pi_div_four,Real.cos_pi_div_five]
  have hs5l : 2≤Real.sqrt 5 := by nlinarith only [hs5,hs5n]
  nlinarith only [hs2,hs5,hs5l]

theorem ellipticTriangleSharpSquare_three_three_four :
    EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      (1/2) (1/2) (Real.cos (Real.pi/4)) := by
  have hs2:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hs2n:=Real.sqrt_nonneg (2:ℝ)
  have hs2u : Real.sqrt 2≤2 := by nlinarith only [hs2,hs2n]
  apply ellipticTriangleRatiosBoundedBelow_of_numerator
    (by norm_num) (by norm_num)
    (by rw [Real.cos_pi_div_four];constructor <;> linarith only [hs2n,hs2u])
  rw [Real.cos_pi_div_four]
  have hs2l : 1≤Real.sqrt 2 := by nlinarith only [hs2,hs2n]
  nlinarith only [hs2,hs2l]

theorem triangleOrderAngle_nonneg_of_two_le {p : ℕ∞} (hp : 2≤p) :
    0≤Fuchsian.triangleOrderAngle p := by
  rcases eq_or_ne p ⊤ with rfl|hpt
  · rw [Fuchsian.triangleOrderAngle_top]
  · obtain ⟨n,rfl⟩:=ENat.ne_top_iff_exists.mp hpt
    rw [Fuchsian.triangleOrderAngle_nat]
    positivity

theorem triangleOrderAngle_antitone_of_two_le {p q : ℕ∞}
    (hp : 2≤p) (hpq : p≤q) : Fuchsian.triangleOrderAngle q≤Fuchsian.triangleOrderAngle p := by
  rcases eq_or_ne q ⊤ with rfl|hqt
  · rw [Fuchsian.triangleOrderAngle_top]
    exact triangleOrderAngle_nonneg_of_two_le hp
  · have hpt : p≠⊤ := by intro he;rw [he] at hpq;exact hqt (top_le_iff.mp hpq)
    obtain ⟨m,rfl⟩:=ENat.ne_top_iff_exists.mp hpt
    obtain ⟨n,rfl⟩:=ENat.ne_top_iff_exists.mp hqt
    have hm : 2≤m := ENat.natCast_le_natCast.mp hp
    have hmn : m≤n := ENat.natCast_le_natCast.mp hpq
    rw [Fuchsian.triangleOrderAngle_nat,Fuchsian.triangleOrderAngle_nat]
    exact div_le_div_of_nonneg_left Real.pi_pos.le
      (by exact_mod_cast (by omega : 0<m)) (by exact_mod_cast hmn)

theorem triangleOrderAngle_mem_Icc_of_two_le {p : ℕ∞} (hp : 2≤p) :
    Fuchsian.triangleOrderAngle p∈Icc 0 (Real.pi/2) := by
  refine ⟨triangleOrderAngle_nonneg_of_two_le hp,?_⟩
  have hh:=triangleOrderAngle_antitone_of_two_le (p:=2) (q:=p) le_rfl hp
  have h2 : Fuchsian.triangleOrderAngle (2:ℕ∞)=Real.pi/2 := by norm_num [Fuchsian.triangleOrderAngle]
  rw [h2] at hh
  exact hh

theorem triangleOrderCos_mem_Icc_of_two_le {p : ℕ∞} (hp : 2≤p) :
    Real.cos (Fuchsian.triangleOrderAngle p)∈Icc 0 1 :=
  ⟨Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    (by linarith only [(triangleOrderAngle_mem_Icc_of_two_le hp).1,Real.pi_pos])
    (triangleOrderAngle_mem_Icc_of_two_le hp).2,Real.cos_le_one _⟩

theorem triangleOrderCos_monotone_of_two_le {p q : ℕ∞}
    (hp : 2≤p) (hpq : p≤q) :
    Real.cos (Fuchsian.triangleOrderAngle p)≤Real.cos (Fuchsian.triangleOrderAngle q) := by
  apply Real.cos_le_cos_of_nonneg_of_le_pi
    (triangleOrderAngle_nonneg_of_two_le (hp.trans hpq))
    (by linarith only [(triangleOrderAngle_mem_Icc_of_two_le hp).2,Real.pi_pos])
    (triangleOrderAngle_antitone_of_two_le hp hpq)

theorem triangleOrder_eq_nat_or_succ_le (n : ℕ) (p : ℕ∞) (hp : (n:ℕ∞)≤p) :
    p=n ∨ ((n+1:ℕ):ℕ∞)≤p := by
  rcases eq_or_ne p ⊤ with rfl|hpt
  · exact Or.inr le_top
  · obtain ⟨m,rfl⟩:=ENat.ne_top_iff_exists.mp hpt
    have hm : n≤m := ENat.natCast_le_natCast.mp hp
    by_cases he : m=n
    · exact Or.inl (congrArg Nat.cast he)
    · exact Or.inr (ENat.natCast_le_natCast.mpr (by omega))

theorem triangleOrder_le_nat_of_lt_succ (n : ℕ) {p : ℕ∞}
    (hp : p<((n+1:ℕ):ℕ∞)) : p≤n := by
  have hpt : p≠⊤ := ne_top_of_lt hp
  obtain ⟨m,rfl⟩:=ENat.ne_top_iff_exists.mp hpt
  exact ENat.natCast_le_natCast.mpr (by
    have hm:=ENat.natCast_lt_natCast.mp hp
    omega)

theorem triangleOrder_minimal_hyperbolic_types {p q r : ℕ∞}
    (hp : 2≤p) (hpq : p≤q) (hqr : q≤r)
    (hs : Fuchsian.triangleOrderAngle p+Fuchsian.triangleOrderAngle q+Fuchsian.triangleOrderAngle r<Real.pi) :
    (p=2 ∧ q=3 ∧ 7≤r) ∨ (p=2 ∧ 4≤q ∧ 5≤r) ∨
      (3≤p ∧ 3≤q ∧ 4≤r) := by
  have hq:=hp.trans hpq
  have hr:=hq.trans hqr
  have h2 : Fuchsian.triangleOrderAngle ((2:ℕ):ℕ∞)=Real.pi/2 := by
    rw [Fuchsian.triangleOrderAngle_nat];norm_num
  have h3 : Fuchsian.triangleOrderAngle ((3:ℕ):ℕ∞)=Real.pi/3 := by
    rw [Fuchsian.triangleOrderAngle_nat];norm_num
  rcases triangleOrder_eq_nat_or_succ_le 2 p hp with hp2|hp3
  · subst p
    rcases triangleOrder_eq_nat_or_succ_le 2 q hq with hq2|hq3
    · subst q
      have ha:=triangleOrderAngle_nonneg_of_two_le hr
      rw [h2] at hs
      linarith only [ha,hs]
    · rcases triangleOrder_eq_nat_or_succ_le 3 q hq3 with hq3|hq4
      · subst q
        refine Or.inl ⟨rfl,rfl,?_⟩
        by_contra hn
        have hr6:=triangleOrder_le_nat_of_lt_succ 6 (lt_of_not_ge hn)
        have ha:=triangleOrderAngle_antitone_of_two_le hr hr6
        change Fuchsian.triangleOrderAngle ((6:ℕ):ℕ∞)≤Fuchsian.triangleOrderAngle r at ha
        rw [Fuchsian.triangleOrderAngle_nat] at ha
        rw [h2,h3] at hs
        norm_num only [Nat.cast_ofNat] at ha
        linarith only [ha,hs]
      · refine Or.inr (Or.inl ⟨rfl,hq4,?_⟩)
        by_contra hn
        have hr4:=triangleOrder_le_nat_of_lt_succ 4 (lt_of_not_ge hn)
        have hq4eq : q=4 := le_antisymm (hqr.trans hr4) hq4
        have hr4eq : r=4 := le_antisymm hr4 (hq4.trans hqr)
        subst q
        subst r
        norm_num [Fuchsian.triangleOrderAngle] at hs
        linarith only [hs]
  · refine Or.inr (Or.inr ⟨hp3,hp3.trans hpq,?_⟩)
    by_contra hn
    have hr3:=triangleOrder_le_nat_of_lt_succ 3 (lt_of_not_ge hn)
    have hp3eq : p=3 := le_antisymm ((hpq.trans hqr).trans hr3) hp3
    have hq3eq : q=3 := le_antisymm (hqr.trans hr3) (hp3.trans hpq)
    have hr3eq : r=3 := le_antisymm hr3 ((hp3.trans hpq).trans hqr)
    subst p
    subst q
    subst r
    norm_num [Fuchsian.triangleOrderAngle] at hs
    linarith only [hs]

theorem ellipticTriangleRatiosBoundedBelow_mono_orders
    {b : ℝ} {p q r P Q R : ℕ∞}
    (h : EllipticTriangleRatiosBoundedBelow b
      (Real.cos (Fuchsian.triangleOrderAngle p)) (Real.cos (Fuchsian.triangleOrderAngle q))
      (Real.cos (Fuchsian.triangleOrderAngle r)))
    (hp : 2≤p) (hq : 2≤q) (hr : 2≤r) (hpP : p≤P) (hqQ : q≤Q) (hrR : r≤R) :
    EllipticTriangleRatiosBoundedBelow b
      (Real.cos (Fuchsian.triangleOrderAngle P)) (Real.cos (Fuchsian.triangleOrderAngle Q))
      (Real.cos (Fuchsian.triangleOrderAngle R)) :=
  ellipticTriangleRatiosBoundedBelow_mono h
    (triangleOrderCos_mem_Icc_of_two_le hp) (triangleOrderCos_mem_Icc_of_two_le hq)
    (triangleOrderCos_mem_Icc_of_two_le hr)
    (triangleOrderCos_mem_Icc_of_two_le (hp.trans hpP))
    (triangleOrderCos_mem_Icc_of_two_le (hq.trans hqQ))
    (triangleOrderCos_mem_Icc_of_two_le (hr.trans hrR))
    (triangleOrderCos_monotone_of_two_le hp hpP)
    (triangleOrderCos_monotone_of_two_le hq hqQ)
    (triangleOrderCos_monotone_of_two_le hr hrR)

theorem ellipticTriangleRatiosBoundedBelow_sorted {p q r : ℕ∞}
    (hp : 2≤p) (hpq : p≤q) (hqr : q≤r)
    (hs : Fuchsian.triangleOrderAngle p+Fuchsian.triangleOrderAngle q+Fuchsian.triangleOrderAngle r<Real.pi) :
    EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      (Real.cos (Fuchsian.triangleOrderAngle p)) (Real.cos (Fuchsian.triangleOrderAngle q))
      (Real.cos (Fuchsian.triangleOrderAngle r)) := by
  have h237 : EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      (Real.cos (Fuchsian.triangleOrderAngle (2:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (3:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (7:ℕ∞))) := by
    simpa [Fuchsian.triangleOrderAngle,Real.cos_pi_div_two,Real.cos_pi_div_three] using
      ellipticTriangleSharpSquare_two_three_seven
  have h245 : EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      (Real.cos (Fuchsian.triangleOrderAngle (2:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (4:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (5:ℕ∞))) := by
    simpa [Fuchsian.triangleOrderAngle,Real.cos_pi_div_two] using
      ellipticTriangleSharpSquare_two_four_five
  have h334 : EllipticTriangleRatiosBoundedBelow
      ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))
      (Real.cos (Fuchsian.triangleOrderAngle (3:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (3:ℕ∞)))
      (Real.cos (Fuchsian.triangleOrderAngle (4:ℕ∞))) := by
    simpa [Fuchsian.triangleOrderAngle,Real.cos_pi_div_three] using
      ellipticTriangleSharpSquare_three_three_four
  rcases triangleOrder_minimal_hyperbolic_types hp hpq hqr hs with
    ⟨hp2,hq3,hr7⟩|⟨hp2,hq4,hr5⟩|⟨hp3,hq3,hr4⟩
  · exact ellipticTriangleRatiosBoundedBelow_mono_orders h237
      (by norm_num) (by norm_num) (by norm_num) hp2.ge hq3.ge hr7
  · exact ellipticTriangleRatiosBoundedBelow_mono_orders h245
      (by norm_num) (by norm_num) (by norm_num) hp2.ge hq4 hr5
  · exact ellipticTriangleRatiosBoundedBelow_mono_orders h334
      (by norm_num) (by norm_num) (by norm_num) hp3 hq3 hr4

theorem ellipticTriangleRatio_sharp_lower_bound (p q r : ℕ∞)
    (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (hs : Fuchsian.triangleOrderAngle p+Fuchsian.triangleOrderAngle q+Fuchsian.triangleOrderAngle r<Real.pi) :
    (4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7)≤
      ellipticTriangleRatio (Real.cos (Fuchsian.triangleOrderAngle p))
        (Real.cos (Fuchsian.triangleOrderAngle q)) (Real.cos (Fuchsian.triangleOrderAngle r)) := by
  rcases le_total p q with hpq|hqp
  · rcases le_total q r with hqr|hrq
    · exact (ellipticTriangleRatiosBoundedBelow_sorted hp hpq hqr hs).1
    · rcases le_total p r with hpr|hrp
      · exact (ellipticTriangleRatiosBoundedBelow_sorted hp hpr hrq
          (by linarith only [hs])).2.1
      · exact (ellipticTriangleRatiosBoundedBelow_sorted hr hrp hpq
          (by linarith only [hs])).2.2
  · rw [ellipticTriangleRatio_swap]
    rcases le_total p r with hpr|hrp
    · exact (ellipticTriangleRatiosBoundedBelow_sorted hq hqp hpr
        (by linarith only [hs])).1
    · rcases le_total q r with hqr|hrq
      · exact (ellipticTriangleRatiosBoundedBelow_sorted hq hqr hrp
          (by linarith only [hs])).2.1
      · exact (ellipticTriangleRatiosBoundedBelow_sorted hr hrq hqp
          (by linarith only [hs])).2.2

theorem ellipticNontriangleRatio_lower_bound {x y : ℝ}
    (hx : x∈Icc 0 1) (hy : y∈Icc 0 1) (h : 1/2≤x ∨ 1/2≤y) :
    1/15≤(x+y)^2/(4-(x-y)^2) := by
  have hd:=ellipticTriangleRatio_denominator_pos hx hy (z:=0) le_rfl
  apply (le_div_iff₀ (by linarith only [hd] : 0<4-(x-y)^2)).mpr
  have hxy : 0≤x*y := mul_nonneg hx.1 hy.1
  rcases h with h|h <;> nlinarith only [h,hx.1,hy.1,hxy,sq_nonneg x,sq_nonneg y]

theorem ellipticNontriangleRatio_order_lower_bound (p q : ℕ∞)
    (hp : 2≤p) (hq : 2≤q) (hne : ¬(p=2 ∧ q=2)) :
    1/15≤(Real.cos (Fuchsian.triangleOrderAngle p)+Real.cos (Fuchsian.triangleOrderAngle q))^2/
      (4-(Real.cos (Fuchsian.triangleOrderAngle p)-Real.cos (Fuchsian.triangleOrderAngle q))^2) := by
  apply ellipticNontriangleRatio_lower_bound
    (triangleOrderCos_mem_Icc_of_two_le hp) (triangleOrderCos_mem_Icc_of_two_le hq)
  have h3 : Real.cos (Fuchsian.triangleOrderAngle (3:ℕ∞))=(1:ℝ)/2 := by
    norm_num [Fuchsian.triangleOrderAngle,Real.cos_pi_div_three]
  rcases triangleOrder_eq_nat_or_succ_le 2 p hp with hp2|hp3
  · rcases triangleOrder_eq_nat_or_succ_le 2 q hq with hq2|hq3
    · exact (hne ⟨hp2,hq2⟩).elim
    · right
      rw [←h3]
      exact triangleOrderCos_monotone_of_two_le (by norm_num) hq3
  · left
    rw [←h3]
    exact triangleOrderCos_monotone_of_two_le (by norm_num) hp3

theorem ellipticNontriangleRatio_sqrt_order_lower_bound (p q : ℕ∞)
    (hp : 2≤p) (hq : 2≤q) (hne : ¬(p=2 ∧ q=2)) :
    1/Real.sqrt 15≤Real.sqrt
      ((Real.cos (Fuchsian.triangleOrderAngle p)+Real.cos (Fuchsian.triangleOrderAngle q))^2/
        (4-(Real.cos (Fuchsian.triangleOrderAngle p)-Real.cos (Fuchsian.triangleOrderAngle q))^2)) := by
  have hh:=Real.sqrt_le_sqrt (ellipticNontriangleRatio_order_lower_bound p q hp hq hne)
  rw [Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one] at hh
  exact hh

theorem ellipticTriangleRatio_sqrt_sharp_lower_bound (p q r : ℕ∞)
    (hp : 2≤p) (hq : 2≤q) (hr : 2≤r)
    (hs : Fuchsian.triangleOrderAngle p+Fuchsian.triangleOrderAngle q+Fuchsian.triangleOrderAngle r<Real.pi) :
    Real.sqrt ((4*Real.cos (Real.pi/7)^2-3)/(8*Real.cos (Real.pi/7)+7))≤
      Real.sqrt (ellipticTriangleRatio (Real.cos (Fuchsian.triangleOrderAngle p))
        (Real.cos (Fuchsian.triangleOrderAngle q)) (Real.cos (Fuchsian.triangleOrderAngle r))) :=
  Real.sqrt_le_sqrt (ellipticTriangleRatio_sharp_lower_bound p q r hp hq hr hs)

theorem elliptic_radial_ratio_mono (s t D E : ℝ) (hs : 0<s) (ht : 0<t)
    (hD : 0≤D) (hDE : D≤E) :
    (s*t)^2*(D^2-1)/(s^2+t^2+2*s*t*D)≤
      (s*t)^2*(E^2-1)/(s^2+t^2+2*s*t*E) := by
  have hE : 0≤E:=hD.trans hDE
  apply (div_le_div_iff₀ (by positivity : 0<s^2+t^2+2*s*t*D)
    (by positivity : 0<s^2+t^2+2*s*t*E)).mpr
  have hdiff : 0≤E-D:=sub_nonneg.mpr hDE
  have hprod : 0≤(s*t)^2*(E-D)*((E+D)*(s^2+t^2)+2*s*t*(D*E+1)) := by positivity
  nlinarith only [hprod]

theorem elliptic_radial_cosine_ratio (s t x y z : ℝ) (hs : 0<s) (ht : 0<t)
    (hsx : s^2+x^2=1) (hty : t^2+y^2=1) :
    (s*t)^2*(((x*y+z)/(s*t))^2-1)/
        (s^2+t^2+2*s*t*((x*y+z)/(s*t)))=ellipticTriangleRatio x y z := by
  let D:=(x*y+z)/(s*t)
  have hm : s*t*D=x*y+z:=mul_div_cancel₀ _ (mul_ne_zero hs.ne' ht.ne')
  have hs2 : s^2=1-x^2:=by linarith only [hsx]
  have ht2 : t^2=1-y^2:=by linarith only [hty]
  have hst : (s*t)^2=(1-x^2)*(1-y^2) := by rw [mul_pow,hs2,ht2]
  have hsq : (s*t)^2*D^2=(x*y+z)^2 := by
    have hh:=congrArg (fun a : ℝ=>a^2) hm
    nlinarith only [hh]
  have hnum : (s*t)^2*(D^2-1)=x^2+y^2+z^2+2*x*y*z-1 := by
    rw [mul_sub,mul_one,hsq,hst]
    ring
  have hden : s^2+t^2+2*s*t*D=2+2*z-(x-y)^2 := by
    nlinarith only [hsx,hty,hm]
  change (s*t)^2*(D^2-1)/(s^2+t^2+2*s*t*D)=_
  rw [hnum,hden]
  rfl

theorem elliptic_radial_cosine_ratio_lower (s t x y z D : ℝ)
    (hs : 0<s) (ht : 0<t) (hsx : s^2+x^2=1) (hty : t^2+y^2=1)
    (hx : 0≤x) (hy : 0≤y) (hz : 0≤z) (hD : (x*y+z)/(s*t)≤D) :
    ellipticTriangleRatio x y z≤(s*t)^2*(D^2-1)/(s^2+t^2+2*s*t*D) := by
  rw [←elliptic_radial_cosine_ratio s t x y z hs ht hsx hty]
  exact elliptic_radial_ratio_mono s t _ D hs ht (by positivity) hD

theorem elliptic_pair_order_cosine_ratio_lower
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A))
    (hB : Mobius.MobiusElliptic (realSLMobius B))
    (hp : 2≤orderOf (realSLMobius A)) (hq : 2≤orderOf (realSLMobius B))
    (z : ℝ) (hz : 0≤z)
    (hD : (Real.cos (Real.pi/orderOf (realSLMobius A))*
          Real.cos (Real.pi/orderOf (realSLMobius B))+z)/
        (Real.sin (Real.pi/orderOf (realSLMobius A))*Real.sin (Real.pi/orderOf (realSLMobius B)))≤
      Real.cosh (dist (hEllipticCenter A ((realSLMobius_elliptic_iff A hA.1).mp hA))
        (hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)))) :
    ellipticTriangleRatio (Real.cos (Real.pi/orderOf (realSLMobius A)))
      (Real.cos (Real.pi/orderOf (realSLMobius B))) z≤
      (displacementM (hSLIsometry A) (hSLIsometry B))^2 := by
  have hsin (n : ℕ) (hn : 2≤n) : 0<Real.sin (Real.pi/n) := by
    have hnR : (2:ℝ)≤n:=by exact_mod_cast hn
    have hn0 : (0:ℝ)<n:=by linarith only [hnR]
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hn0)
    exact (div_lt_iff₀ hn0).mpr (by nlinarith only [Real.pi_pos,hnR])
  have hcos (n : ℕ) (hn : 2≤n) : 0≤Real.cos (Real.pi/n) := by
    have hh:=triangleOrderCos_mem_Icc_of_two_le (p:=(n:ℕ∞)) (by exact_mod_cast hn)
    simpa only [Fuchsian.triangleOrderAngle_nat] using hh.1
  have he:=elliptic_radial_cosine_ratio_lower
    (Real.sin (Real.pi/orderOf (realSLMobius A)))
    (Real.sin (Real.pi/orderOf (realSLMobius B)))
    (Real.cos (Real.pi/orderOf (realSLMobius A)))
    (Real.cos (Real.pi/orderOf (realSLMobius B))) z _
    (hsin _ hp) (hsin _ hq) (Real.sin_sq_add_cos_sq _) (Real.sin_sq_add_cos_sq _)
    (hcos _ hp) (hcos _ hq) hz hD
  exact he.trans (Fuchsian.elliptic_pair_order_radial_ratio_lower A B hA hB hp hq)

end LowDimensionalTopology.Geometry.Hyperbolic
