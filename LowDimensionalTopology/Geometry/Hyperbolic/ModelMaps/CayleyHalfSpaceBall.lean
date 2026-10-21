/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Ball.PathMetric
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.PathMetric
/-!
# The Cayley map in every finite dimension

The map is the specified north-pole sphere inversion after reflection in the
equatorial plane. Its restriction to the equator is the calibrated
stereographic homeomorphism. A direct norm identity identifies its image of
the positive half-space with the actual open unit ball.

The native half-space and ball homeomorphism has the correct positive
Euclidean derivative scale. Weighted tangent covariance therefore proves
transport of both density path metrics, including their ordinary distances.
The extension includes the pole and infinity; finite formulas exclude only
the relevant pole.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint Manifold Bundle
open Filter EuclideanGeometry Set Bundle
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

theorem northPole_ne_zero (n : ℕ) : Inversive.northPole n ≠ 0 := by
  intro h
  have hn := Inversive.norm_northPole n
  rw [h,norm_zero] at hn
  norm_num at hn

theorem inner_northPole_right (x : Inversive.Euclidean (n+1)) :
    inner ℝ x (Inversive.northPole n) = x (Fin.last n) := by
  simp [Inversive.northPole,EuclideanSpace.inner_single_right]

theorem northPlane_finite_formula (x : Inversive.Euclidean (n+1)) :
    Inversive.planeReflectionFinite (Inversive.northPole n) 0 x = x-(2*x (Fin.last n)) • Inversive.northPole n := by
  unfold Inversive.planeReflectionFinite
  rw [inner_northPole_right,Inversive.norm_northPole,one_pow,sub_zero,div_one]

theorem northPlane_height (x : Inversive.Euclidean (n+1)) :
    Inversive.planeReflectionFinite (Inversive.northPole n) 0 x (Fin.last n) = -x (Fin.last n) := by
  rw [northPlane_finite_formula]
  simp [Inversive.northPole]
  ring

theorem northPlane_negNorth :
    Inversive.planeReflectionFinite (Inversive.northPole n) 0 (-Inversive.northPole n) = Inversive.northPole n := by
  rw [northPlane_finite_formula]
  have hn : (-Inversive.northPole n) (Fin.last n) = -1 := by simp [Inversive.northPole]
  rw [hn]
  module

def stereographicInversion (n : ℕ) : Inversive.ExtendedHomeomorph (n+1) :=
  Inversive.sphereInversionHomeomorph (Inversive.northPole n) (Real.sqrt 2) (Real.sqrt_pos.mpr (by norm_num)).ne'

theorem equatorial_ne_northPole (x : Inversive.Euclidean
  n) : Inversive.equatorialEmbedding n x ≠ Inversive.northPole n := by
  intro h
  have hh := congrArg (fun y : Inversive.Euclidean (n+1) ↦ y (Fin.last n)) h
  simp [Inversive.northPole] at hh

theorem norm_equatorial_sub_north_sq (x : Inversive.Euclidean n) :
    ‖Inversive.equatorialEmbedding n x-Inversive.northPole n‖^2 = ‖x‖^2+1 := by
  rw [norm_sub_sq_real,(Inversive.equatorialEmbedding n).norm_map,Inversive.norm_northPole,
    Inversive.inner_equatorialEmbedding_northPole]
  ring

theorem stereographicInversion_equatorial (z : Inversive.ExtendedEuclidean n) :
    stereographicInversion n (Inversive.extendedEquatorialEmbedding n z) =
      ((Inversive.stereographicHomeomorph n z).val : Inversive.ExtendedEuclidean (n+1)) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [Inversive.extendedEquatorialEmbedding_infty,Inversive.stereographicHomeomorph_infty]
    change Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2) ∞ = (Inversive.northPole n :
      Inversive.ExtendedEuclidean (n+1))
    exact Inversive.sphereInversion_infty _ _
  | coe x =>
    rw [Inversive.extendedEquatorialEmbedding_coe]
    change Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2) (Inversive.equatorialEmbedding n x :
      Inversive.Euclidean (n+1)) = _
    rw [Inversive.sphereInversion_coe _ _ (equatorial_ne_northPole x),Inversive.stereographicHomeomorph_coe]
    apply congrArg OnePoint.some
    rw [Inversive.inversion_formula,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),norm_equatorial_sub_north_sq]
    match_scalars <;> field_simp
    ring

/-- The genuine extended-space Cayley map used. -/
def cayleyBall (n : ℕ) : Inversive.ExtendedHomeomorph (n+1) :=
  stereographicInversion n * Inversive.planeReflectionHomeomorph (Inversive.northPole n) 0 (northPole_ne_zero n)

def cayleyBallFinite (x : Inversive.Euclidean (n+1)) : Inversive.Euclidean (n+1) :=
  inversion (Inversive.northPole n) (Real.sqrt 2) (Inversive.planeReflectionFinite (Inversive.northPole n) 0 x)

theorem cayleyBall_mem_generalMobiusGroup (n : ℕ) : cayleyBall n ∈ Inversive.generalMobiusGroup (n+1) :=
  (Inversive.generalMobiusGroup (n+1)).mul_mem
    (Inversive.sphereInversion_isReflection (Inversive.northPole n) (Real.sqrt 2) (Real.sqrt_pos.mpr
      (by norm_num))).mem_generalMobiusGroup
    (Inversive.planeReflection_isReflection (Inversive.northPole n) 0 (northPole_ne_zero n)).mem_generalMobiusGroup

theorem cayleyBall_infty (n : ℕ) : cayleyBall n ∞ = (Inversive.northPole n : Inversive.ExtendedEuclidean (n+1)) := rfl

theorem cayleyBall_negNorth (n : ℕ) : cayleyBall n (-Inversive.northPole n : Inversive.Euclidean (n+1)) = ∞ := by
  change Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2)
    (Inversive.planeReflection (Inversive.northPole n) 0 (-Inversive.northPole n : Inversive.Euclidean (n+1))) = ∞
  rw [Inversive.planeReflection_coe,northPlane_negNorth,Inversive.sphereInversion_center]

theorem northPlane_ne_north {x : Inversive.Euclidean (n+1)} (hx : x ≠ -Inversive.northPole n) :
    Inversive.planeReflectionFinite (Inversive.northPole n) 0 x ≠ Inversive.northPole n := by
  intro he
  exact hx ((Inversive.planeReflectionFinite_involutive (Inversive.northPole n) 0 (northPole_ne_zero n)).injective
    (he.trans northPlane_negNorth.symm))

theorem cayleyBall_coe (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    cayleyBall n (x : Inversive.ExtendedEuclidean (n+1)) =
      (cayleyBallFinite x : Inversive.ExtendedEuclidean (n+1)) := by
  change Inversive.sphereInversion (Inversive.northPole n) (Real.sqrt 2)
    (Inversive.planeReflection (Inversive.northPole n) 0 (x : Inversive.ExtendedEuclidean (n+1))) = _
  rw [Inversive.planeReflection_coe,Inversive.sphereInversion_coe _ _ (northPlane_ne_north hx)]
  rfl

/-- The finite norm identity for the Cayley map. -/
theorem stereographicInversion_norm_sq (y : Inversive.Euclidean (n+1)) (hy : y ≠ Inversive.northPole n) :
    ‖inversion (Inversive.northPole n) (Real.sqrt 2) y‖^2 =
      1+4*y (Fin.last n)/‖y-Inversive.northPole n‖^2 := by
  have hD : ‖y-Inversive.northPole n‖^2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))
  rw [Inversive.inversion_formula,div_pow,Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),norm_add_sq_real,
    norm_smul,real_inner_smul_right,mul_pow,Real.norm_eq_abs,sq_abs,inner_sub_right,
    real_inner_self_eq_norm_sq,Inversive.norm_northPole,one_pow,real_inner_comm y (Inversive.northPole
      n),inner_northPole_right]
  field_simp [hD]
  ring

theorem cayleyBallFinite_norm_gap (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    1-‖cayleyBallFinite x‖^2 =
      4*x (Fin.last n)/‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x-Inversive.northPole n‖^2 := by
  rw [cayleyBallFinite,stereographicInversion_norm_sq _ (northPlane_ne_north hx),northPlane_height]
  ring
theorem stereographicInversion_image_equator :
    stereographicInversion n '' Set.range (Inversive.extendedEquatorialEmbedding n) =
      (Inversive.extendedUnitSphere : Set (Inversive.ExtendedEuclidean (n+1))) := by
  ext z
  constructor
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    rw [stereographicInversion_equatorial]
    exact ⟨(Inversive.stereographicHomeomorph n w).val,(Inversive.stereographicHomeomorph n w).property,rfl⟩
  · rintro ⟨x,hx,rfl⟩
    let y : Metric.sphere (0 : Inversive.Euclidean (n+1)) 1 := ⟨x,hx⟩
    refine ⟨Inversive.extendedEquatorialEmbedding n ((Inversive.stereographicHomeomorph n).symm y),
      ⟨(Inversive.stereographicHomeomorph n).symm y,rfl⟩,?_⟩
    rw [stereographicInversion_equatorial,(Inversive.stereographicHomeomorph n).apply_symm_apply]

theorem positiveHeight_ne_cayleyPole (x : Inversive.Euclidean (n+1)) (hx : 0 < x (Fin.last n)) :
    x ≠ -Inversive.northPole n := by
  intro he
  rw [he] at hx
  norm_num [Inversive.northPole] at hx

theorem cayleyBallFinite_maps_positive (x : Inversive.Euclidean (n+1)) (hx : 0 < x (Fin.last n)) :
    ‖cayleyBallFinite x‖ < 1 := by
  have hxp := positiveHeight_ne_cayleyPole x hx
  have hD : 0 < ‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x-Inversive.northPole n‖^2 :=
    sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (northPlane_ne_north hxp)))
  have hgap := cayleyBallFinite_norm_gap x hxp
  have hp : 0 < 4*x (Fin.last n)/‖Inversive.planeReflectionFinite (Inversive.northPole
    n) 0 x-Inversive.northPole n‖^2 :=
    div_pos (mul_pos (by norm_num) hx) hD
  nlinarith [norm_nonneg (cayleyBallFinite x)]

theorem cayleyBall_image_upperHalfSpace :
    cayleyBall n '' poincareHalfSpaceSet n 1 =
      (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean (n+1))) := by
  apply Set.Subset.antisymm
  · rintro z ⟨w,hw,rfl⟩
    induction w using OnePoint.rec with
    | infty => exact False.elim (poincareHalfSpaceSet_infty (n := n) 1 hw)
    | coe x =>
      have hx : 0 < x (Fin.last n) := by simpa only [poincareHalfSpaceSet_coe,one_mul] using hw
      rw [cayleyBall_coe x (positiveHeight_ne_cayleyPole x hx)]
      exact ⟨cayleyBallFinite x,by simpa only [Metric.mem_ball,dist_zero_right] using
        cayleyBallFinite_maps_positive x hx,rfl⟩
  · rintro z ⟨b,hb,rfl⟩
    have hbNorm : ‖b‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hb
    obtain ⟨z,hz⟩ := (cayleyBall n).surjective (b : Inversive.ExtendedEuclidean (n+1))
    induction z using OnePoint.rec with
    | infty =>
      rw [cayleyBall_infty] at hz
      have hh := congrArg norm (OnePoint.coe_injective hz)
      rw [Inversive.norm_northPole] at hh
      linarith
    | coe x =>
      have hxp : x ≠ -Inversive.northPole n := by
        intro he
        rw [he,cayleyBall_negNorth] at hz
        exact OnePoint.coe_ne_infty b hz.symm
      have hfinite : cayleyBallFinite x = b := OnePoint.coe_injective ((cayleyBall_coe x hxp).symm.trans hz)
      have hgap := cayleyBallFinite_norm_gap x hxp
      rw [hfinite] at hgap
      have hD : 0 < ‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x-Inversive.northPole n‖^2 :=
        sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (northPlane_ne_north hxp)))
      have hx : 0 < x (Fin.last n) := by
        have hpos : 0 < 4*x (Fin.last n)/‖Inversive.planeReflectionFinite (Inversive.northPole
          n) 0 x-Inversive.northPole n‖^2 := by
          rw [← hgap]
          nlinarith [norm_nonneg b]
        have hnum : 0 < 4*x (Fin.last n) := (div_pos_iff_of_pos_right hD).mp hpos
        nlinarith
      exact ⟨(x : Inversive.ExtendedEuclidean (n+1)),by
        simpa only [poincareHalfSpaceSet_coe,one_mul] using hx,hz⟩

theorem finiteEuclideanPart_cayleyBall (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    Inversive.finiteEuclideanPart (cayleyBall n) x = cayleyBallFinite x := by
  rw [Inversive.finiteEuclideanPart,cayleyBall_coe x hx]
  rfl

def cayleyBallScale (x : Inversive.Euclidean (n+1)) : ℝ :=
  2/‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x-Inversive.northPole n‖^2

theorem cayleyBallScale_pos (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    0 < cayleyBallScale x := by
  exact div_pos (by norm_num) (sq_pos_of_ne_zero
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (northPlane_ne_north hx))))

theorem cayleyBallFinite_dist (x y : Inversive.Euclidean (n+1))
    (hx : x ≠ -Inversive.northPole n) (hy : y ≠ -Inversive.northPole n) :
    dist (cayleyBallFinite x) (cayleyBallFinite y) =
      2/(dist (Inversive.planeReflectionFinite (Inversive.northPole n) 0 x) (Inversive.northPole n)*
        dist (Inversive.planeReflectionFinite (Inversive.northPole n) 0 y) (Inversive.northPole n))*dist x y := by
  rw [cayleyBallFinite,cayleyBallFinite,
    Inversive.sphereInversion_dist (Real.sqrt 2) (northPlane_ne_north hx) (northPlane_ne_north hy),
    Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  rw [← Inversive.cartanPlaneLinearIsometry_apply,← Inversive.cartanPlaneLinearIsometry_apply,
    (Inversive.cartanPlaneLinearIsometry (Inversive.northPole n)).isometry.dist_eq]

theorem cayleyBall_scale_limit (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    Tendsto (fun y : Inversive.Euclidean (n+1) ↦
      dist (Inversive.finiteEuclideanPart (cayleyBall n) y) (Inversive.finiteEuclideanPart (cayleyBall n) x)/dist y x)
      (𝓝[≠] x) (𝓝 (cayleyBallScale x)) := by
  let P := Inversive.cartanPlaneLinearIsometry (Inversive.northPole n)
  have hxN : dist (P x) (Inversive.northPole n) ≠ 0 :=
    dist_ne_zero.mpr (by dsimp only [P]; rw [Inversive.cartanPlaneLinearIsometry_apply]; exact northPlane_ne_north hx)
  have hdistCont : ContinuousAt (fun y : Inversive.Euclidean (n+1) ↦ dist (P y) (Inversive.northPole n)) x :=
    P.continuous.continuousAt.dist continuousAt_const
  have hcont : ContinuousAt (fun y : Inversive.Euclidean (n+1) ↦
      2/(dist (P y) (Inversive.northPole n)*dist (P x) (Inversive.northPole n))) x :=
    continuousAt_const.div (hdistCont.mul continuousAt_const) (mul_ne_zero hxN hxN)
  have hval : 2/(dist (P x) (Inversive.northPole n)*dist (P x) (Inversive.northPole n)) = cayleyBallScale x := by
    rw [cayleyBallScale,← pow_two,dist_eq_norm]
    dsimp only [P]
    rw [Inversive.cartanPlaneLinearIsometry_apply]
  have hlim := hcont.tendsto
  rw [hval] at hlim
  apply (hlim.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [(eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds,self_mem_nhdsWithin] with y hy hyx
  rw [finiteEuclideanPart_cayleyBall y hy,finiteEuclideanPart_cayleyBall x hx,
    cayleyBallFinite_dist y x hy hx,mul_div_cancel_right₀ _ (dist_ne_zero.mpr hyx)]
  dsimp only [P]
  rw [Inversive.cartanPlaneLinearIsometry_apply,Inversive.cartanPlaneLinearIsometry_apply]

theorem cayleyBall_hasFDerivAt_positive_isometry (x : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    ∃ O : Inversive.Euclidean (n+1) ≃ₗᵢ[ℝ] Inversive.Euclidean (n+1),
      HasFDerivAt (Inversive.finiteEuclideanPart (cayleyBall n))
        (cayleyBallScale x • (O : Inversive.Euclidean (n+1) →L[ℝ] Inversive.Euclidean (n+1))) x := by
  have hreg : cayleyBall n (x : Inversive.ExtendedEuclidean (n+1)) ≠ ∞ := by
    rw [cayleyBall_coe x hx]
    exact OnePoint.coe_ne_infty _
  obtain ⟨μ,hμ,O,hderiv⟩ := Auxiliary.Analysis.conformalAt_iff_positive_isometry.mp
    (Inversive.generalMobius_conformalAt (cayleyBall_mem_generalMobiusGroup n) hreg)
  have hlim := Auxiliary.Analysis.conformal_norm_ratio_tendsto hμ O hderiv
  simp only [← dist_eq_norm] at hlim
  have hμeq := tendsto_nhds_unique hlim (cayleyBall_scale_limit x hx)
  exact ⟨O,hμeq ▸ hderiv⟩

theorem cayleyBall_fderiv_norm (x v : Inversive.Euclidean (n+1)) (hx : x ≠ -Inversive.northPole n) :
    ‖fderiv ℝ (Inversive.finiteEuclideanPart (cayleyBall n)) x v‖ = cayleyBallScale x*‖v‖ := by
  obtain ⟨O,hO⟩ := cayleyBall_hasFDerivAt_positive_isometry x hx
  exact Inversive.hasFDerivAt_positive_isometry_norm (cayleyBallScale_pos x hx) O hO v

theorem cayleyBall_density_covariance (x v : Inversive.Euclidean (n+1)) (hx : 0 < x (Fin.last n)) :
    2/(1-‖Inversive.finiteEuclideanPart (cayleyBall n) x‖^2) *
      ‖fderiv ℝ (Inversive.finiteEuclideanPart (cayleyBall n)) x v‖ = (1/x (Fin.last n))*‖v‖ := by
  have hp := positiveHeight_ne_cayleyPole x hx
  rw [cayleyBall_fderiv_norm x v hp,finiteEuclideanPart_cayleyBall x hp,
    cayleyBallFinite_norm_gap x hp,cayleyBallScale]
  have hD : ‖Inversive.planeReflectionFinite (Inversive.northPole n) 0 x-Inversive.northPole n‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr (northPlane_ne_north hp))
  field_simp [hD,hx.ne']
  ring

/-- Restriction of the actual extended Cayley map to the two native model domains. -/
def cayleyBallHomeomorph (n : ℕ) : HyperbolicHalfSpace n ≃ₜ unitBallDomain (n+1) :=
  (halfSpaceExtendedHomeomorph n).trans
    (((cayleyBall n).image (poincareHalfSpaceSet n 1)).trans
      ((Homeomorph.setCongr cayleyBall_image_upperHalfSpace).trans (ballExtendedHomeomorph (n+1)).symm))

theorem cayleyBallHomeomorph_coe (x : HyperbolicHalfSpace n) :
    ((cayleyBallHomeomorph n x).val : Inversive.ExtendedEuclidean (n+1)) = cayleyBall n x.val := by
  exact ballExtendedHomeomorph_symm_apply _

theorem cayleyBallHomeomorph_val (x : HyperbolicHalfSpace n) :
    (cayleyBallHomeomorph n x).val = Inversive.finiteEuclideanPart (cayleyBall n) x.val := by
  have hp := positiveHeight_ne_cayleyPole x.val (show 0 < x.val (Fin.last n) from x.property)
  have hreg : cayleyBall n (x.val : Inversive.ExtendedEuclidean (n+1)) ≠ ∞ := by
    rw [cayleyBall_coe x.val hp]
    exact OnePoint.coe_ne_infty _
  have he := cayleyBallHomeomorph_coe x
  rw [← Inversive.coe_finiteEuclideanPart (cayleyBall n) hreg] at he
  exact OnePoint.coe_injective he

theorem cayleyBallHomeomorph_writtenInExtChart_eventuallyEq (x : HyperbolicHalfSpace n) :
    writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) x (cayleyBallHomeomorph n) =ᶠ[𝓝
      x.val]
      Inversive.finiteEuclideanPart (cayleyBall n) := by
  filter_upwards [(upperHalfSpaceDomain n).isOpen.mem_nhds x.property] with z hz
  let y : HyperbolicHalfSpace n := ⟨z,hz⟩
  have hy := Auxiliary.Analysis.openDomain_chart_symm_apply x y
  change (cayleyBallHomeomorph n ((chartAt (Inversive.Euclidean (n+1)) x).symm z)).val =
    Inversive.finiteEuclideanPart (cayleyBall n) z
  rw [hy,cayleyBallHomeomorph_val]

theorem cayleyBallHomeomorph_mdifferentiable (n : ℕ) :
    MDifferentiable 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) (cayleyBallHomeomorph n) := by
  intro x
  rw [mdifferentiableAt_iff]
  refine ⟨(cayleyBallHomeomorph n).continuous.continuousAt,?_⟩
  have hp := positiveHeight_ne_cayleyPole x.val (show 0 < x.val (Fin.last n) from x.property)
  obtain ⟨_,hO⟩ := cayleyBall_hasFDerivAt_positive_isometry x.val hp
  have hh := hO.differentiableAt.congr_of_eventuallyEq
    (cayleyBallHomeomorph_writtenInExtChart_eventuallyEq x)
  change DifferentiableWithinAt ℝ
    (writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) x (cayleyBallHomeomorph
      n)) _ x.val
  exact hh.differentiableWithinAt

theorem cayleyBallHomeomorph_mfderiv_apply (x : HyperbolicHalfSpace n)
    (v : TangentSpace 𝓘(ℝ,Inversive.Euclidean (n+1)) x) :
    (tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) (cayleyBallHomeomorph n x))
      (mfderiv 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) (cayleyBallHomeomorph n) x v) =
    fderiv ℝ (Inversive.finiteEuclideanPart (cayleyBall n)) x.val
      ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v) := by
  have hmd := cayleyBallHomeomorph_mdifferentiable n x
  simp only [mfderiv,hmd,ite_true,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  simp only [mfld_simps]
  change fderivWithin ℝ
    (writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) x (cayleyBallHomeomorph n))
    Set.univ x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v) =
      fderiv ℝ (Inversive.finiteEuclideanPart (cayleyBall n)) x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean
        (n+1)) x) v)
  rw [fderivWithin_univ]
  exact congrArg (fun A : Inversive.Euclidean (n+1) →L[ℝ] Inversive.Euclidean (n+1) ↦
    A ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v))
    (cayleyBallHomeomorph_writtenInExtChart_eventuallyEq x).fderiv_eq

theorem cayleyBallHomeomorph_tangent_covariance (x : HyperbolicHalfSpace n)
    (v : TangentSpace 𝓘(ℝ,Inversive.Euclidean (n+1)) x) :
    ballDensity (n+1) (cayleyBallHomeomorph n x) *
      ‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) (cayleyBallHomeomorph n x))
        (mfderiv 𝓘(ℝ,Inversive.Euclidean (n+1)) 𝓘(ℝ,Inversive.Euclidean (n+1)) (cayleyBallHomeomorph n) x v)‖ =
      halfSpaceDensity n x * ‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v‖ := by
  rw [cayleyBallHomeomorph_mfderiv_apply]
  change 2/(1-‖(cayleyBallHomeomorph n x).val‖^2) *
    ‖fderiv ℝ (Inversive.finiteEuclideanPart (cayleyBall n)) x.val
      ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v)‖ =
    (1/x.val (Fin.last n))*‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v‖
  rw [cayleyBallHomeomorph_val]
  exact cayleyBall_density_covariance x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean (n+1)) x) v) x.property

theorem cayleyBallHomeomorph_pathEDist (x y : HyperbolicHalfSpace n) :
    (ballDensity (n+1)).pathEDist (cayleyBallHomeomorph n x) (cayleyBallHomeomorph n y) =
      halfSpacePathEDist x y :=
  Auxiliary.Analysis.Density.pathEDist_equiv (cayleyBallHomeomorph n).toEquiv
    (cayleyBallHomeomorph_mdifferentiable n) cayleyBallHomeomorph_tangent_covariance x y

theorem cayleyBallHomeomorph_pathDist (x y : HyperbolicHalfSpace n) :
    (ballDensity (n+1)).pathDist (cayleyBallHomeomorph n x) (cayleyBallHomeomorph n y) =
      halfSpacePathDist x y :=
  congrArg ENNReal.toReal (cayleyBallHomeomorph_pathEDist x y)

theorem cayleyBallHomeomorph_isometry (n : ℕ) :
    @Isometry (HyperbolicHalfSpace n) (unitBallDomain (n+1))
      (halfSpaceDensity n).eMetricSpace.toPseudoEMetricSpace
      (ballDensity (n+1)).eMetricSpace.toPseudoEMetricSpace (cayleyBallHomeomorph n) :=
  Auxiliary.Analysis.Density.isometry_equiv (cayleyBallHomeomorph n).toEquiv
    (cayleyBallHomeomorph_mdifferentiable n) cayleyBallHomeomorph_tangent_covariance

end LowDimensionalTopology.Geometry.Hyperbolic
