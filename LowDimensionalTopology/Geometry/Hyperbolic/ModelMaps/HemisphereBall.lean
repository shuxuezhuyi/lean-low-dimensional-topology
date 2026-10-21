/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.RadialCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperboloidBall.Distance
public import LowDimensionalTopology.Geometry.Inversive.SphereOrthogonality
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein

/-!
# The actual upper hemisphere and its stereographic disc model
-/

@[expose] public section
open Set Filter
open scoped Topology OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
noncomputable section
variable {n : ℕ}

theorem northPlane_norm (x : Inversive.Euclidean (n+1)) :
    ‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x‖ = ‖x‖ := by
  rw [← Inversive.cartanPlaneLinearIsometry_apply]
  exact (Inversive.cartanPlaneLinearIsometry (Inversive.northPole n)).norm_map x

theorem northPlane_distance_sq (x : Inversive.Euclidean (n+1)) :
    ‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x - Inversive.northPole n‖ ^ 2 =
      ‖x‖ ^ 2 + 1 + 2 * x (Fin.last n) := by
  rw [norm_sub_sq_real,northPlane_norm,Inversive.norm_northPole,inner_northPole_right,northPlane_height]
  ring

theorem cayleyBallFinite_height (x : Inversive.Euclidean (n+1)) (hx : 0 < x (Fin.last n)) :
    cayleyBallFinite x (Fin.last n) = (‖x‖ ^ 2 - 1) / (‖x‖ ^ 2 + 1 + 2 * x (Fin.last n)) := by
  have hden : ‖x‖ ^ 2 + 1 + 2 * x (Fin.last n) ≠ 0 := by positivity
  rw [cayleyBallFinite,Inversive.inversion_formula,div_pow,Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    northPlane_distance_sq]
  simp only [PiLp.add_apply,PiLp.smul_apply,PiLp.sub_apply,smul_eq_mul,northPlane_height]
  have hn : Inversive.northPole n (Fin.last n) = 1 := by simp [Inversive.northPole]
  rw [hn]
  field_simp
  ring

theorem cayleyBallHomeomorph_hemisphere_iff (x : HyperbolicHalfSpace n) :
    ‖x.val‖ = 1 ↔ (cayleyBallHomeomorph n x).val (Fin.last n) = 0 := by
  have hx : 0 < x.val (Fin.last n) := x.property
  have hden : ‖x.val‖ ^ 2 + 1 + 2 * x.val (Fin.last n) ≠ 0 := by positivity
  rw [cayleyBallHomeomorph_val,finiteEuclideanPart_cayleyBall _ (positiveHeight_ne_cayleyPole _ hx),
    cayleyBallFinite_height _ hx,div_eq_zero_iff]
  simp only [hden,or_false]
  constructor
  · intro h
    rw [h]
    norm_num
  · intro h
    have hn := norm_nonneg x.val
    nlinarith


/-- The true upper unit hemisphere inside the actual upper-half-space model. -/
abbrev UpperHemisphere (n : ℕ) := {x : HyperbolicHalfSpace n // ‖x.val‖ = 1}

/-- The true equatorial section of the actual Poincaré ball. -/
abbrev EquatorialBall (n : ℕ) := {x : unitBallDomain (n+1) // x.val (Fin.last n) = 0}

def equatorialBallHomeomorph (n : ℕ) : unitBallDomain n ≃ₜ EquatorialBall n where
  toFun x := ⟨⟨Inversive.equatorialEmbedding n x.val,by
    change Inversive.equatorialEmbedding n x.val ∈ Metric.ball (0 : Inversive.Euclidean (n+1)) 1
    rw [Metric.mem_ball,dist_zero_right,(Inversive.equatorialEmbedding n).norm_map]
    exact unitBallDomain_norm_lt x⟩,Inversive.equatorialEmbedding_last x.val⟩
  invFun x := ⟨verticalProjection n x.val.val,by
    change verticalProjection n x.val.val ∈ Metric.ball (0 : Inversive.Euclidean n) 1
    rw [Metric.mem_ball,dist_zero_right]
    have hn := verticalProjection_norm_sq x.val.val
    rw [x.property] at hn
    have hb := unitBallDomain_norm_lt x.val
    nlinarith [norm_nonneg x.val.val,norm_nonneg (verticalProjection n x.val.val)]⟩
  left_inv x := Subtype.ext (verticalProjection_equatorial x.val)
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    have he := equatorial_projection_decomposition x.val.val
    simpa only [x.property,zero_smul,add_zero] using he
  continuous_toFun := (((Inversive.equatorialEmbedding n).continuous.comp continuous_subtype_val).subtype_mk
    _).subtype_mk _
  continuous_invFun := (((verticalProjection n).continuous_of_finiteDimensional.comp
    (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _)

theorem cayleyBallHomeomorph_image_hemisphere (n : ℕ) :
    cayleyBallHomeomorph n '' {x : HyperbolicHalfSpace n | ‖x.val‖ = 1} =
      {x : unitBallDomain (n+1) | x.val (Fin.last n) = 0} := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (cayleyBallHomeomorph_hemisphere_iff x).mp hx
  · intro hy
    refine ⟨(cayleyBallHomeomorph n).symm y,?_,(cayleyBallHomeomorph n).apply_symm_apply y⟩
    apply (cayleyBallHomeomorph_hemisphere_iff _).mpr
    rwa [(cayleyBallHomeomorph n).apply_symm_apply]

def hemisphereEquatorialHomeomorph (n : ℕ) : UpperHemisphere n ≃ₜ EquatorialBall n :=
  ((cayleyBallHomeomorph n).image {x : HyperbolicHalfSpace n | ‖x.val‖ = 1}).trans
    (Homeomorph.setCongr (cayleyBallHomeomorph_image_hemisphere n))

/--
This is the geometric actual reflection followed by stereographic inversion,
restricted to the actual upper hemisphere and written in equatorial coordinates.
-/
def hemisphereDiscHomeomorph (n : ℕ) : UpperHemisphere n ≃ₜ unitBallDomain n :=
  (hemisphereEquatorialHomeomorph n).trans (equatorialBallHomeomorph n).symm

theorem hemisphereDiscHomeomorph_cayley (x : UpperHemisphere n) :
    Inversive.equatorialEmbedding n (hemisphereDiscHomeomorph n x).val =
      (cayleyBallHomeomorph n x.val).val := by
  have he := (equatorialBallHomeomorph n).apply_symm_apply (hemisphereEquatorialHomeomorph n x)
  exact congrArg (fun y : EquatorialBall n => y.val.val) he

theorem equatorialBall_pathDist (x y : unitBallDomain n) :
    (ballDensity (n+1)).pathDist (equatorialBallHomeomorph n x).val
      (equatorialBallHomeomorph n y).val = (ballDensity n).pathDist x y := by
  apply Real.cosh_strictMonoOn.injOn
    (show 0 ≤ (ballDensity (n+1)).pathDist _ _ from ENNReal.toReal_nonneg)
    (show 0 ≤ (ballDensity n).pathDist _ _ from ENNReal.toReal_nonneg)
  rw [ballDensity_pathDist_cosh,ballDensity_pathDist_cosh]
  change 1 + 2 * Inversive.ballDistanceRatio (Inversive.equatorialEmbedding n x.val) (Inversive.equatorialEmbedding n
    y.val) = _
  simp only [Inversive.ballDistanceRatio,(Inversive.equatorialEmbedding n).norm_map,(Inversive.equatorialEmbedding
    n).isometry.dist_eq]

theorem hemisphereDiscHomeomorph_pathDist (x y : UpperHemisphere n) :
    (ballDensity n).pathDist (hemisphereDiscHomeomorph n x) (hemisphereDiscHomeomorph n y) =
      halfSpacePathDist x.val y.val := by
  rw [← equatorialBall_pathDist]
  have hx : (equatorialBallHomeomorph n (hemisphereDiscHomeomorph n x)).val =
      cayleyBallHomeomorph n x.val := Subtype.ext (hemisphereDiscHomeomorph_cayley x)
  have hy : (equatorialBallHomeomorph n (hemisphereDiscHomeomorph n y)).val =
      cayleyBallHomeomorph n y.val := Subtype.ext (hemisphereDiscHomeomorph_cayley y)
  rw [hx,hy]
  exact cayleyBallHomeomorph_pathDist x.val y.val


/-- The actual real Euclidean two-ball is the native complex unit disc. -/
def euclideanBallComplexDiscHomeomorph : unitBallDomain 2 ≃ₜ 𝔻 where
  toFun x := Complex.UnitDisc.mk (Complex.orthonormalBasisOneI.repr.symm x.val) (by
    rw [Complex.orthonormalBasisOneI.repr.symm.norm_map]
    exact unitBallDomain_norm_lt x)
  invFun z := ⟨Complex.orthonormalBasisOneI.repr (z : ℂ),by
    change Complex.orthonormalBasisOneI.repr (z : ℂ) ∈ Metric.ball (0 : Inversive.Euclidean 2) 1
    rw [Metric.mem_ball,dist_zero_right,Complex.orthonormalBasisOneI.repr.norm_map]
    exact z.norm_lt_one⟩
  left_inv x := Subtype.ext (Complex.orthonormalBasisOneI.repr.apply_symm_apply x.val)
  right_inv z := Complex.UnitDisc.coe_injective (Complex.orthonormalBasisOneI.repr.symm_apply_apply (z : ℂ))
  continuous_toFun := by
    apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
    exact Complex.orthonormalBasisOneI.repr.symm.continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact Complex.orthonormalBasisOneI.repr.continuous.comp Complex.UnitDisc.continuous_coe

theorem euclideanBallComplexDiscHomeomorph_pathDist (x y : unitBallDomain 2) :
    discPathDist (euclideanBallComplexDiscHomeomorph x) (euclideanBallComplexDiscHomeomorph y) =
      (ballDensity 2).pathDist x y := by
  apply Real.cosh_strictMonoOn.injOn
    (show 0 ≤ discPathDist _ _ by rw [discPathDist_eq_halfPlane]; exact dist_nonneg)
    (show 0 ≤ (ballDensity 2).pathDist _ _ from ENNReal.toReal_nonneg)
  rw [disc_cosh_distance,ballDensity_pathDist_cosh]
  change 1 + 2 * ‖Complex.orthonormalBasisOneI.repr.symm x.val -
    Complex.orthonormalBasisOneI.repr.symm y.val‖ ^ 2 /
      ((1 - ‖Complex.orthonormalBasisOneI.repr.symm x.val‖ ^ 2) *
        (1 - ‖Complex.orthonormalBasisOneI.repr.symm y.val‖ ^ 2)) = _
  rw [← Complex.orthonormalBasisOneI.repr.symm.map_sub,
    Complex.orthonormalBasisOneI.repr.symm.norm_map,
    Complex.orthonormalBasisOneI.repr.symm.norm_map,
    Complex.orthonormalBasisOneI.repr.symm.norm_map,Inversive.ballDistanceRatio,dist_eq_norm]
  ring

/-- The geometric actual H³ hemisphere mapped onto the native complex Poincaré disc. -/
def upperHemisphereComplexDiscHomeomorph : UpperHemisphere 2 ≃ₜ 𝔻 :=
  (hemisphereDiscHomeomorph 2).trans euclideanBallComplexDiscHomeomorph

theorem upperHemisphereComplexDiscHomeomorph_pathDist (x y : UpperHemisphere 2) :
    discPathDist (upperHemisphereComplexDiscHomeomorph x) (upperHemisphereComplexDiscHomeomorph y) =
      halfSpacePathDist x.val y.val := by
  change discPathDist (euclideanBallComplexDiscHomeomorph (hemisphereDiscHomeomorph 2 x))
    (euclideanBallComplexDiscHomeomorph (hemisphereDiscHomeomorph 2 y)) = _
  exact (euclideanBallComplexDiscHomeomorph_pathDist _ _).trans (hemisphereDiscHomeomorph_pathDist x y)

theorem hemisphere_actual_cayley_conformal (x : HyperbolicHalfSpace n) :
    ConformalAt (Inversive.finiteEuclideanPart (cayleyBall n)) x.val := by
  have hx : x.val ≠ -Inversive.northPole n := positiveHeight_ne_cayleyPole x.val x.property
  have hreg : cayleyBall n (x.val : Inversive.ExtendedEuclidean (n+1)) ≠ ∞ := by
    rw [cayleyBall_coe _ hx]
    exact OnePoint.coe_ne_infty _
  exact Inversive.generalMobius_conformalAt (cayleyBall_mem_generalMobiusGroup n) hreg


/--
The very same ambient sphere-reflection map preserves actual Euclidean normal
orthogonality. Thus the restricted sphere-plane identification retains the geometric
orthogonal generalized-sphere incidences.
-/
theorem hemisphere_cayley_preserves_sphere_orthogonality (S T : Inversive.GeneralizedSphere 3)
    (hST : Inversive.GeneralizedSpheresOrthogonal S T) :
    Inversive.GeneralizedSpheresOrthogonal
      (Inversive.generalizedSphereImage (cayleyBall 2) (cayleyBall_mem_generalMobiusGroup 2) S)
      (Inversive.generalizedSphereImage (cayleyBall 2) (cayleyBall_mem_generalMobiusGroup 2) T) :=
  Inversive.GeneralizedSpheresOrthogonal.image (by norm_num : 2 ≤ 3) S T hST
    (cayleyBall 2) (cayleyBall_mem_generalMobiusGroup 2)


theorem hemisphereDiscHomeomorph_inverse_stereographic (x : unitBallDomain n) :
    ((hemisphereDiscHomeomorph n).symm x).val.val =
      Inversive.planeReflectionFinite (Inversive.northPole n) 0
        (Inversive.stereographicHomeomorph n (x.val : Inversive.ExtendedEuclidean n)).val := by
  let q := (Inversive.stereographicHomeomorph n (x.val : Inversive.ExtendedEuclidean n)).val
  have hs : stereographicInversion n (Inversive.equatorialEmbedding n x.val : Inversive.ExtendedEuclidean (n+1)) =
      (q : Inversive.ExtendedEuclidean (n+1)) := stereographicInversion_equatorial (x.val : Inversive.ExtendedEuclidean
        n)
  have hinv : stereographicInversion n (q : Inversive.ExtendedEuclidean (n+1)) =
      (Inversive.equatorialEmbedding n x.val : Inversive.ExtendedEuclidean (n+1)) := by
    rw [← hs]
    change Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2)
      (Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2) (Inversive.equatorialEmbedding n x.val :
        Inversive.ExtendedEuclidean (n+1))) = _
    exact Inversive.sphereInversion_involutive (Inversive.northPole n) (Real.sqrt_pos.mpr
      (by norm_num : (0 : ℝ) < 2)).ne' _
  have hr : cayleyBall n (Inversive.planeReflectionFinite (Inversive.northPole n) 0 q : Inversive.ExtendedEuclidean
    (n+1)) =
      (Inversive.equatorialEmbedding n x.val : Inversive.ExtendedEuclidean (n+1)) := by
    change stereographicInversion n
      (Inversive.planeReflection (Inversive.northPole n) 0 (Inversive.planeReflectionFinite (Inversive.northPole n) 0
        q)) = _
    rw [Inversive.planeReflection_coe,Inversive.planeReflectionFinite_involutive _ _ (northPole_ne_zero n)]
    exact hinv
  have hc := hemisphereDiscHomeomorph_cayley ((hemisphereDiscHomeomorph n).symm x)
  rw [(hemisphereDiscHomeomorph n).apply_symm_apply] at hc
  have hl : cayleyBall n (((hemisphereDiscHomeomorph n).symm x).val.val : Inversive.ExtendedEuclidean (n+1)) =
      (Inversive.equatorialEmbedding n x.val : Inversive.ExtendedEuclidean (n+1)) := by
    rw [← cayleyBallHomeomorph_coe]
    exact congrArg (fun z : Inversive.Euclidean (n+1) => (z : Inversive.ExtendedEuclidean (n+1))) hc.symm
  apply OnePoint.coe_injective
  apply (cayleyBall n).injective
  exact hl.trans hr.symm

theorem hemisphere_vertical_projection_eq_klein (x : unitBallDomain n) :
    verticalProjection n ((hemisphereDiscHomeomorph n).symm x).val.val = kleinRadialMap x.val := by
  rw [hemisphereDiscHomeomorph_inverse_stereographic,kleinRadialMap_eq_vertical_reflected_stereographic]

end
end LowDimensionalTopology.Geometry.Hyperbolic
