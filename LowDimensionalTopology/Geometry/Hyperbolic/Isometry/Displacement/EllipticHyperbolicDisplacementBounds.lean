/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Hyperbolic.HyperbolicDisplacementProducts
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact scalar last step of the genuine elliptic/hyperbolic displacement argument. -/
theorem elliptic_hyperbolic_radial_max_eighth (S s a b:ℝ)
    (hS:0≤S) (hs:0≤s) (hs1:s≤1) (ha:0≤a) (hb:0≤b)
    (hsep:1/2≤S*s*Real.cosh (a+b)) :
    1/8≤(max (S*Real.cosh b) (s*Real.sinh a))^2 := by
  let m:=max (S*Real.cosh b) (s*Real.sinh a)
  let N:=s*Real.cosh a
  have hm0:0≤m:=le_max_of_le_left (mul_nonneg hS (Real.cosh_pos b).le)
  have hN0:0≤N:=mul_nonneg hs (Real.cosh_pos a).le
  have hmS:S*Real.cosh b≤m:=le_max_left _ _
  have hms:s*Real.sinh a≤m:=le_max_right _ _
  have hsa:0≤s*Real.sinh a:=mul_nonneg hs (Real.sinh_nonneg_iff.mpr ha)
  have hsb:S*Real.sinh b≤m:=(mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh b).le hS).trans hmS
  have hfirst:=mul_le_mul_of_nonneg_left hmS hN0
  have hsecond:=mul_le_mul hms hsb
    (mul_nonneg hS (Real.sinh_nonneg_iff.mpr hb)) hm0
  have hsum:1/2≤m*N+m^2:=by
    rw [Real.cosh_add] at hsep
    dsimp only [N] at hfirst ⊢
    nlinarith only [hsep,hfirst,hsecond]
  have hss:s^2≤1:=by nlinarith only [mul_nonneg hs (sub_nonneg.mpr hs1)]
  have hsq:(s*Real.sinh a)^2≤m^2:=(sq_le_sq₀ hsa hm0).mpr hms
  have hN:N^2≤1+m^2:=by
    have he:N^2-(s*Real.sinh a)^2=s^2:=by
      dsimp only [N]
      nlinarith only [Real.cosh_sq_sub_sinh_sq a]
    nlinarith only [he,hss,hsq]
  by_contra hnot
  have hsmall:m^2<1/8:=lt_of_not_ge hnot
  have hleft:(1/2-m^2)^2≤(m*N)^2:=
    (sq_le_sq₀ (by linarith only [hsmall]) (mul_nonneg hm0 hN0)).mpr (by linarith only [hsum])
  have hright:=mul_le_mul_of_nonneg_left hN (sq_nonneg m)
  nlinarith only [hleft,hright,hsmall]

/-- Actual point-to-line infima satisfy the usual metric triangle bound, using a genuine foot. -/
theorem halfPlaneLine_pointDist_le_dist_add (L:HalfPlaneLine) (u z:ℍ) :
    L.pointDist u≤dist u z+L.pointDist z := by
  have hh: L.pointDist u≤dist u (L.orthogonalFoot z):=
    Metric.infDist_le_dist_of_mem (L.orthogonalFoot_mem z)
  have ht:=dist_triangle u z (L.orthogonalFoot z)
  rw [←L.pointDist_eq_orthogonalFoot z] at ht
  exact hh.trans ht

/-- A separately established actual center-axis constraint gives the source numerical
bound for the true whole-plane maximum-displacement infimum. The constraint is explicit. -/
theorem elliptic_hyperbolic_displacementM_eighth_of_separation
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2)
    (hB:Mobius.MobiusElliptic (realSLMobius B))
    (hsep:1/2≤Real.sinh (hTranslationLength (hSLIsometry A)/2)*
      Real.sin (hEllipticRotationAngle B hB/2)*
      Real.cosh ((hHyperbolicAxis A hA htA).pointDist
        (hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)))) :
    1/Real.sqrt 8≤displacementM (hSLIsometry A) (hSLIsometry B) := by
  let L:=hHyperbolicAxis A hA htA
  let u:=hEllipticCenter B ((realSLMobius_elliptic_iff B hB.1).mp hB)
  let S:=Real.sinh (hTranslationLength (hSLIsometry A)/2)
  let s:=Real.sin (hEllipticRotationAngle B hB/2)
  have hS:0≤S:=Real.sinh_nonneg_iff.mpr (by linarith only [hHyperbolic_translationLength_pos A hA htA])
  have hs:0<s:=Real.sin_pos_of_pos_of_lt_pi (hElliptic_halfAngle_mem_Ioo B hB).1
    (hElliptic_halfAngle_mem_Ioo B hB).2
  apply (displacementM_lower_bound _ _ _).mpr
  intro z
  have hd:=halfPlaneLine_pointDist_le_dist_add L u z
  have hcos:Real.cosh (L.pointDist u)≤Real.cosh (dist u z+L.pointDist z):=by
    apply Real.cosh_le_cosh.mpr
    rwa [abs_of_nonneg (L.pointDist_nonneg u),
      abs_of_nonneg (add_nonneg dist_nonneg (L.pointDist_nonneg z))]
  have hsep':1/2≤S*s*Real.cosh (dist u z+L.pointDist z):=
    hsep.trans (mul_le_mul_of_nonneg_left hcos (mul_nonneg hS hs.le))
  have hbound:=elliptic_hyperbolic_radial_max_eighth S s (dist u z) (L.pointDist z)
    hS hs.le (Real.sin_le_one _) dist_nonneg (L.pointDist_nonneg z) hsep'
  have hg:hSinhDisplacement (hSLIsometry A) z=S*Real.cosh (L.pointDist z):=by
    change Real.sinh (dist z (A•z)/2)=_
    rw [hyperbolic_half_displacement A hA htA,mul_comm]
  have hh:hSinhDisplacement (hSLIsometry B) z=s*Real.sinh (dist u z):=
    elliptic_actual_angle_radial B hB z
  rw [hg,hh]
  apply (sq_le_sq₀ (show 0≤1/Real.sqrt 8 by positivity)
    (le_max_of_le_left (mul_nonneg hS (Real.cosh_pos _).le))).mp
  have he:(1/Real.sqrt (8:ℝ))^2=(1:ℝ)/8:=by norm_num [div_pow,Real.sq_sqrt]
  rwa [he]

end LowDimensionalTopology.Geometry.Hyperbolic
