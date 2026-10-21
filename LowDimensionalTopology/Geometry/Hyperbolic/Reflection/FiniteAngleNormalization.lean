/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.Angle.PositiveCone
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.AngleNormalForms
public import LowDimensionalTopology.Geometry.Euclidean.Reflection.FiniteDihedralGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.ProperSectorAngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.Pencils.NativeEllipticPencils
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology InnerProductGeometry
open scoped ComplexConjugate Complex.UnitDisc OnePoint NNReal
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Reflection in a genuine disc diameter is the literal planar anti-linear reflection. -/
theorem DiscLine.reflection_zero_linear (L : DiscLine) (h0 : (0:𝔻)∈L.carrier) :
    ∃u : Circle,∀z : 𝔻,(L.reflection z:ℂ)=(u:ℂ)*conj (z:ℂ) := by
  obtain ⟨a,ha,hL⟩:=(discEllipticPencil_zero_iff_diameter L).mp h0
  obtain ⟨r,hr,hfix,hact⟩:=L.exists_geometric_reflection
  let p:=Inversive.planeReflectionHomeomorph (Mobius.complexPlaneCoordinates a) 0
    ((Mobius.complexPlaneCoordinates.map_ne_zero_iff).mpr ha)
  have hp : Inversive.IsReflection p:=Inversive.planeReflection_isReflection _ _ _
  have hfix' : Function.fixedPoints (Mobius.euclideanToComplexHom r)=
      Function.fixedPoints (Mobius.euclideanToComplexHom p):=by
    rw [hfix,Mobius.complexLine_reflection a 0 ha,hL]
  have hre : Function.fixedPoints r=Function.fixedPoints p:=by
    rw [Mobius.complexReflection_fixedPoints,Mobius.complexReflection_fixedPoints] at hfix'
    ext x
    have hx:=Set.ext_iff.mp hfix' (Mobius.extendedComplexEuclideanHomeomorph.symm x)
    simpa only [mem_preimage,Homeomorph.apply_symm_apply] using hx
  have hrp : r=p:=Inversive.IsReflection.eq_of_fixedPoints hr hp hre
  let u : Circle:=⟨-(a/conj a),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_neg,norm_div,Complex.norm_conj]
    exact div_self (norm_ne_zero_iff.mpr ha)⟩
  refine ⟨u,?_⟩
  intro z
  have hactz:=hact z
  rw [hrp] at hactz
  have hcoef : Mobius.euclideanToComplexHom p ((z:ℂ):Mobius.ExtendedComplex)=
      (((u:ℂ)*conj (z:ℂ)):Mobius.ExtendedComplex):=by
    dsimp only [p]
    simp only [Mobius.euclideanToComplexHom_apply,Mobius.extendedComplexEuclideanHomeomorph_coe,
      Inversive.planeReflectionHomeomorph_apply,Inversive.planeReflection_coe,Mobius.complexEuclidean_symm_coe]
    rw [Mobius.ReflectionBridge.planeReflection_complex_formula a z 0 ha]
    simp only [mul_zero,Complex.ofReal_zero,zero_div,add_zero]
    rfl
  exact OnePoint.coe_injective (hactz.symm.trans hcoef)


/-- A genuine diameter reflection is the standard mirror determined by any nonzero point on it. -/
theorem DiscLine.reflection_zero_direction (L : DiscLine) (h0 : (0:𝔻)∈L.carrier)
    (z : 𝔻) (hzL : z∈L.carrier) (hz0 : (z:ℂ)≠0) :
    let v:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(z:ℂ),hz0⟩
    ∀w : 𝔻,(L.reflection w:ℂ)=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (v*v) true (w:ℂ) := by
  obtain ⟨u,hu⟩:=L.reflection_zero_linear h0
  let v:=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection ⟨(z:ℂ),hz0⟩
  have hr : 0<‖(z:ℂ)‖:=norm_pos_iff.mpr hz0
  have hrep : (‖(z:ℂ)‖:ℂ)*(v:ℂ)=(z:ℂ):=_root_.LowDimensionalTopology.Geometry.Euclidean.finiteSectorDirection_reconstruct ⟨(z:ℂ),hz0⟩
  have hfix : L.reflection z=z:=by
    apply discToHalfPlane_injective
    change discToHalfPlane (halfPlaneToDisc (L.toHalfPlane.reflection (discToHalfPlane z)))=discToHalfPlane z
    rw [discToHalfPlane_halfPlaneToDisc]
    exact (L.toHalfPlane.reflection_fixed_iff (discToHalfPlane z)).mpr ((L.mem_carrier z).mp hzL)
  have hfix' : (u:ℂ)*conj (z:ℂ)=(z:ℂ):=by rw [←hu,hfix]
  have hvfix : (u:ℂ)*conj (v:ℂ)=(v:ℂ):=by
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    calc
      (‖(z:ℂ)‖:ℂ)*((u:ℂ)*conj (v:ℂ))=(u:ℂ)*conj ((‖(z:ℂ)‖:ℂ)*(v:ℂ)):=by
        rw [map_mul,Complex.conj_ofReal]
        ring
      _=(‖(z:ℂ)‖:ℂ)*(v:ℂ):=by rw [hrep];exact hfix'
  have huc : u*v⁻¹=v:=Circle.ext (by
    simpa only [Circle.coe_mul,Circle.coe_inv_eq_conj] using hvfix)
  have hu' : u=v*v:=by
    calc u=(u*v⁻¹)*v:=by group
         _=v*v:=by rw [huc]
  change ∀w : 𝔻,(L.reflection
    w:ℂ)=_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap (v*v) true (w:ℂ)
  intro w
  rw [hu,hu',_root_.LowDimensionalTopology.Geometry.Euclidean.finitePlanarOrthogonalMap_apply]
  rfl



/-- The closure of an actual native hyperbolic angle is the literal standard cone
in a proved Cayley-and-rotation chart; its size is the original forward-ray angle. -/
theorem cayley_closed_sector_rotation_normal_form (R S : HRayAt UpperHalfPlane.I)
    (hne : R.supportLine≠S.supportLine) :
    ∃L : ℂ ≃ₗᵢ[ℝ] ℂ,∀z : 𝔻,
      z∈halfPlaneToDisc '' closure (properHAngleInterior R S) ↔
      L (z:ℂ)∈Submodule.span ℝ≥0 {(1:ℂ),(Circle.exp (hInteriorAngleMeasure R S):ℂ)} := by
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Euclidean.positive_cone_rotation_normal_form R.kleinDirection S.kleinDirection
    R.kleinDirection_ne_zero S.kleinDirection_ne_zero (hInteriorAngleMeasure R S)
    (hInteriorAngleMeasure_I_eq_klein_angle R S).symm (hInteriorAngleMeasure_lt_pi R S hne)
  refine ⟨L,?_⟩
  intro z
  rw [cayley_closure_properHAngleInterior_I R S hne]
  exact hL (z:ℂ)

end LowDimensionalTopology.Geometry.Hyperbolic
